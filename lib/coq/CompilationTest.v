Set Implicit Arguments.

From CFML Require Import Semantics LibSepFmap.
Import LibListNotation.

Add Rec LoadPath "../../../CompCert" as compcert.
Add Rec LoadPath "../../../CompCert/flocq" as Flocq.
From compcert Require Coqlib Maps Integers Floats Values AST Ctypes Clight.
From compcert Require Import Maps Errors SimplExpr.

(** CFML types *)

(* Definition program := list toplevel_fundef
   fundef := {name, rettype, list (var*type), trm}

   Clight.program -> main : "main" 
   
   Definition tr_program (p : program) : mon Clight.program

  Definition gather_vars (t : trm_r) : list (ident*type)
   Definition gather_temps (t : trm_r) : list (ident*type)

   Definition tr_trm_stmt (E : env_var) (t: trm_r) : mon Clight.statement
   Definition tr_trm_expr (E : env_var) (t: trm_r) : mon Clight.expr

   Definiton env_var := Ptree.t var_descr

   Inductive var_descr :=
    | var_stack
    | var_heap
    | var_const  


   Definition trm_get_var_heap_inv (E : env_var) (t : trm) :
                                       option (ident*type) :=
      match t with
      | trm_app trm_get (trm_var x :: nil) =>
                       match Ptree.get E x with
                       | Some (var_heap) => Some x
                       | _ => None
      | _ => None

 *)
  

Section CFML_TYPES.

Inductive type : Type :=
| type_long : type
| type_double : type
| type_ref : type -> type.


Variant var_descr : Type :=
  | stack : var_descr
  | heap : var_descr
  | const : var_descr.

Global Instance Inhab_var_descr_type : Inhab (var_descr * type).
Proof using. apply (Inhab_of_val (stack,type_long)). Qed.

(* Redefiniton of LibSepBind.bind to be typed, and with var descr *)
Inductive binding : Type :=
| binding_anon : binding
| binding_var : var -> type -> var_descr -> binding.

Definition numtype := type.

Variant prim : Type :=
  | val_ptr_add : prim
  | val_add : numtype -> prim
  (* | val_cast : numtype -> numtype -> prim
      (en pratique, juste besoin de (val_cast type_long type_double))*)
  | val_lt : numtype -> prim
  | val_ref : prim
  | val_get : prim
  | val_set : prim
  | val_free : prim
  | val_alloc : prim
  | val_dealloc : prim.


Definition is_binop (op : prim) : bool :=
  match op with
  | val_add _
  | val_lt _
    => true
  | _ => false
  end.
    

Inductive val : Type :=
| val_uninitialized : val
| val_unit : val
| val_bool : bool -> val
| val_int : int -> val
| val_loc : loc -> val
| val_prim : prim -> val
| val_header : nat -> val
                     
with trm : Type :=
| trm_val : val -> trm
| trm_var : var -> trm
| trm_apps : trm -> list trm -> trm
| trm_let : binding -> trm -> trm -> trm
| trm_while : trm -> trm -> trm
| trm_ite : trm -> trm -> trm -> trm.


Definition trm_seq (t1 t2 : trm) : trm :=
  trm_let binding_anon t1 t2.

  
Definition env_var := PTree.t (var_descr*type).

Definition env_var_join (E1 E2 : env_var) : env_var :=
  PTree.fold (fun t k elt => PTree.set k elt t) E1 E2.

(* Definition env_var := fmap var (var_descr*type). *)

Record fundef : Type :=
  mkfundef {
      name: var;
      rettype: type;
      params: list (var * AST.ident * type);
      vars: env_var;
      temps: env_var;
      body: trm
  }.


(* The choice is made here that function paramenters are temporaries (const in cfml),
   do not reside in memory, and thus their address cannot be referenced. This choice
   corresponds to the semantic [function_entry2] of Clight. (read Clight.v:547,713)*)

Definition program := list fundef.

End CFML_TYPES.


(* utility for var-ident translation *)
Local Open Scope error_monad_scope.

Fixpoint find_var (x : var) (l : list (var*AST.ident)) : res AST.ident :=
match l with
| nil => Error (msg "find_var: Variable not declared")
| (v,i)::l' =>
    if (var_eq x v) then OK i
    else do rl' <- find_var x l'; OK rl'
end.

Close Scope error_monad_scope.
(* Freshness monad *)


Declare Scope genident_monad_scope.
Section State_Monad.
  Import AST Coqlib.
  Local Open Scope string_scope.
  Local Open Scope list_scope.
  


  Record generator : Type :=
    mkgenerator {
        gen_next: ident;
        gen_trail: list (var*ident);
      }.


  Definition initial_generator (x : unit) : generator :=
    mkgenerator 1%positive nil.

  Inductive result (A: Type) (g: generator) : Type :=
  | Err: Errors.errmsg -> result A g
  | Res: A -> forall (g': generator), Ple (gen_next g) (gen_next g') -> result A g.


  #[global] Arguments Err [A g].
  #[global] Arguments Res [A g].

  
  Definition mon (A: Type) := forall (g: generator), result A g.
  
  Definition ret {A: Type} (x: A) : mon A :=
    fun g => Res x g (Ple_refl (gen_next g)).
  
  Definition error {A: Type} (msg: Errors.errmsg) : mon A :=
    fun g => Err msg.
  
  Definition bind {A B: Type} (x: mon A) (f: A -> mon B) : mon B :=
    fun g =>
      match x g with
      | Err msg => Err msg
      | Res a g' i =>
          match f a g' with
          | Err msg => Err msg
          | Res b g'' i' => Res b g'' (Ple_trans _ _ _ i i')
          end
      end.
  
  Definition bind2 {A B C: Type} (x: mon (A * B))
    (f: A -> B -> mon C) : mon C :=
    bind x (fun p => f (fst p) (snd p)).
  
  Definition gensym (x: var): mon ident :=
    fun (g: generator) =>
      Res (gen_next g)
        (mkgenerator
           (Pos.succ (gen_next g))
           ((x, gen_next g) :: (gen_trail g)))
        (Ple_succ (gen_next g)).


End State_Monad.


Notation "'do' X <- A ; B" :=
  (bind A (fun X => B))
    (at level 200, X ident, A at level 100, B at level 200)
    : genident_monad_scope.
Notation "'do' ( X , Y ) <- A ; B" :=
  (bind2 A (fun X Y => B))
    (at level 200, X ident, Y ident, A at level 100, B at level 200)
    : genident_monad_scope.


Local Open Scope genident_monad_scope.

Fixpoint st_mmap (A B: Type) (f: A -> mon B) (l: list A) {struct l} : mon (list B) :=
  match l with
  | nil => ret nil
  | hd :: tl =>
      do hd' <- f hd;
      do tl' <- st_mmap f tl;
      ret (hd' :: tl')
  end.

Fixpoint st_mfold (A B : Type) (f : B -> A -> mon B) (init : B) (l : list A) {struct l}
  : mon B :=
  match l with
  | nil => ret init
  | hd :: tl =>
      do carry <- f init hd;
      do cont <- st_mfold f carry tl;
      ret cont
  end.


  

  (** ** int * (const) p = malloc ?     ->  w: *p = v;    r: *p     + free(p);
    cfml   => let p = val_alloc(1) in 
           w=> (set p v)
           r=> (get p)
           free=> (free p)

    clight =>
           decla d'un `type * p` au début, puis
              Sbuiltin (Some p) malloc [sizeof(int)];
           w=> Sassign (Ederef (Evar p)) v
           r=> Ederef (Evar p)
           free=> Sbuiltin None free (Evar p)
   *)

  (** ** int x;         ->   w:   x = v;    r: x   
    cfml   => let p (décoration : stack allocated) = valloc(1) in
           ... pareil

    clight => ramener au début de la déclaration de la fonction
              compile_fun => analyse prog, sort liste des variabels
           w=> Sassign (Evar x) v
           r=> Evar x
   *)

  (** ** tempvar = v;
        => Sset tempvar v / let tempvar = v
        => clight : decla d'un `register void *$42;` au début
                      -> pour tout appel de fonction du coup
   *)

Coercion val_prim : prim >-> val.
Coercion val_loc : loc >-> val.
Coercion trm_var : var >-> trm.
Coercion trm_val : val >-> trm.

Definition state : Type := fmap loc val.

Implicit Types v : val.
Implicit Type l : loc.
Implicit Types t : trm.
Implicit Types s : state.
Implicit Types op : prim.
Implicit Types P : state -> trm -> Prop.

Inductive combiner :=
  | combiner_nil : trm -> trm -> combiner
  | combiner_cons : combiner -> trm -> combiner.

Coercion combiner_nil : trm >-> Funclass.
Coercion combiner_cons : combiner >-> Funclass.

Fixpoint combiner_to_trm (c:combiner) : trm :=
  match c with
  | combiner_nil t1 t2 => trm_apps t1 (t2::nil)
  | combiner_cons c1 t2 =>
      match combiner_to_trm c1 with
      | trm_apps t1 ts => trm_apps t1 (List.app ts (t2::nil))
      | t1 => trm_apps t1 (t2::nil)
      end
  end.

Coercion combiner_to_trm : combiner >-> trm.

Reserved Notation "t '/' s '-->' P"
  (at level 40, s at level 30).

Global Instance Inhab_val : Inhab val.
Proof using. apply (Inhab_of_val val_unit). Qed.


Inductive cfml_step : state -> trm -> (state->trm->Prop) -> Prop :=
| cfml_step_val : forall v s P,
    P s (trm_val v) ->
    (trm_val v) / s --> P
| cfml_step_seq : forall v1 t2 s P,
    P s t2 ->
    (trm_seq (trm_val v1) t2) / s --> P
| cfml_step_seq_l : forall t1 t2 s P P1,
    t1 / s --> P1 ->
    (forall t1' s', P1 s' t1' -> (trm_seq t1' t2) / s' --> P) ->
    (trm_seq t1 t2) / s --> P
| cfml_step_ref : forall v s P,
      (forall l, ~Fmap.indom s l ->
            l <> null ->
            P (Fmap.update s l v) (val_loc l)) ->
      (exists l, ~Fmap.indom s l /\ l <> null) ->
       (val_ref v)/ s --> P
| cfml_step_get : forall s l P,
    Fmap.indom s l ->
    P s (Fmap.read s l) ->
    (val_get l) / s --> P
| cfml_step_set : forall s l v P,
    Fmap.indom s l ->
    P (Fmap.update s l v) val_unit ->
    (val_set l v) / s --> P
| cfml_step_free : forall s l P,
    Fmap.indom s l ->
    P (Fmap.remove s l) val_unit ->
    (val_free l) / s --> P
| cfml_step_ptr_add : forall l l' n s P,
    (l':nat) = (l:nat) + n :> int ->
    P s (val_loc l') ->
    (val_ptr_add l (val_int n)) / s --> P
| cfml_step_alloc : forall n sa P,
    (forall l k sb, sb = Fmap.conseq (LibList.make k val_uninitialized) l ->
               n = nat_to_Z k ->
               l <> null ->
               Fmap.disjoint sa sb ->
               P (sb \+ sa) (val_loc l)) ->
    (exists l k sb, sb = Fmap.conseq (LibList.make k val_uninitialized) l
               /\ n = nat_to_Z k
               /\ l <> null
               /\ Fmap.disjoint sa sb) ->
     (val_alloc (val_int n)) / sa --> P
| cfml_step_dealloc : forall (n:int) s l P,
    (forall vs sa sb, s = sb \+ sa ->
                 sb = Fmap.conseq vs l ->
                 n = LibList.length vs ->
                 Fmap.disjoint sa sb ->
                 P sa val_unit) ->
    (exists vs sa sb, s = sb \+ sa
                 /\ sb = Fmap.conseq vs l
                 /\ n = LibList.length vs
                 /\ Fmap.disjoint sa sb) ->
    (val_dealloc (val_int n) l) / s --> P

where "t / s --> P" := (cfml_step s t P).
(* TODO à compléter *)

(** Preprocessing *)

(* assumptions: no vars bound in args of funcall, as bound term in a
   let binding, or in control flow check expressions  : ie,
   NO:
   - let x = (let y = 3 in y) in ..
   - if (let x = True in x) then ..
   - while (let x = True in x) do ..
   - f (let x = 3 in x)
 *)

Section Preprocessing.

  Local Open Scope genident_monad_scope.

  (* Assumption: no shadowing *)
  Fixpoint get_var_defs (t : trm) : mon env_var :=
    match t with
    | trm_val v => ret (PTree.empty (var_descr*type))
    | trm_var x => ret (PTree.empty (var_descr*type))

    | trm_let (binding_var v ty stack) t1 tk =>
        do i <- gensym v;
        do dtk <- get_var_defs tk;
        ret (PTree.set i (stack, ty) dtk)
    | trm_let (binding_var v ty heap) t1 tk =>
        do i <- gensym v;
        do dtk <- get_var_defs tk;
        ret (PTree.set i (heap, ty) dtk)
    | trm_let (binding_var _ _ const) _ tk =>
        get_var_defs tk

    | trm_let binding_anon t1 t2 =>
        do dt1 <- get_var_defs t1;
        do dt2 <- get_var_defs t2;
        ret (env_var_join dt1 dt2)

    | trm_apps _ _ => ret (PTree.empty (var_descr*type))

    | trm_while _ t => get_var_defs t
            
    | trm_ite _ t1 t2 =>
        do dt1 <- get_var_defs t1;
        do dt2 <- get_var_defs t2;
        ret (env_var_join dt1 dt2)
    end.


  Fixpoint get_temp_defs (t : trm) : mon env_var :=
    match t with
    | trm_val v => ret (PTree.empty (var_descr*type))
    | trm_var x => ret (PTree.empty (var_descr*type))

    | trm_let (binding_var v ty const) t1 tk =>
        do i <- gensym v;
        do dtk <- get_temp_defs tk;
        ret (PTree.set i (const, ty) dtk)
    | trm_let (binding_var _ _ _) _ tk =>
        get_temp_defs tk

    | trm_let binding_anon t1 t2 =>
        do dt1 <- get_temp_defs t1;
        do dt2 <- get_temp_defs t2;
        ret (env_var_join dt1 dt2)

    | trm_apps _ _ => ret (PTree.empty (var_descr*type))

    | trm_while _ t => get_temp_defs t
            
    | trm_ite _ t1 t2 =>
        do dt1 <- get_temp_defs t1;
        do dt2 <- get_temp_defs t2;
        ret (env_var_join dt1 dt2)
    end.

End Preprocessing.


Local Open Scope genident_monad_scope.

Definition make_function (f_name : var) (ret_type : type)
  (params : list (var * type)) (body : trm) : res (fundef * list (var * AST.ident)) :=

  let aux f_name ret_type params body : mon fundef :=
    do vars <- get_var_defs body;
    do temps <- get_temp_defs body;
    do f_params <- st_mmap (fun '(x, ty) => do i <- gensym x;
                                        ret (x, i, ty)) params;
    (* do all_temps <- mfold (fun env '(x, ty) => *)
    (*                         do i <- gensym x; *)
    (*                         ret (PTree.set i (const, ty) env)) temps params; *)
    ret (mkfundef f_name ret_type f_params vars (* all_temps *)
           temps body)
  in
  match aux f_name ret_type params body (initial_generator tt) with
  | Err msg => Error msg
  | Res f g i => OK (f, g.(gen_trail))
  end.



(** CompCert types *)



(* Fmap.update --> assign_loc *)

(** ** Important!! *)
(** Allocation of function-local variables.
  [alloc_variables e1 m1 vars e2 m2] allocates one memory block
  for each variable declared in [vars], and associates the variable
  name with this block.  [e1] and [m1] are the initial local environment
  and memory state.  [e2] and [m2] are the final local environment
  and memory state.

  (in [[../../../CompCert/cfrontend/Clight.v:223]])

  -> meaning each loc can be mapped to a block, at least for refs
 *)


(** Compilation *)

(* Definition program := list toplevel_fundef
   fundef := {name, rettype, list (var*type), trm}

   Clight.program -> main : "main" 
   
   Definition tr_program (p : program) : mon Clight.program

   Definition gather_vars (t : trm_r) : list (ident*type)
   Definition gather_temps (t : trm_r) : list (ident*type)

   Definition tr_trm_stmt (E : env_var) (t: trm_r) : mon Clight.statement
   Definition tr_trm_expr (E : env_var) (t: trm_r) : mon Clight.expr

   Definiton env_var := Ptree.t var_descr

   Inductive var_descr :=
    | var_stack
    | var_heap
    | var_const  


   Definition trm_get_var_heap_inv (E : env_var) (t : trm) :
                                       option (ident*type) :=
      match t with
      | trm_app trm_get (trm_var x :: nil) =>
                       match Ptree.get E x with
                       | Some (var_heap) => Some x
                       | _ => None
      | _ => None

 *)




Notation "[[ ta1 , .. , tan ]]" := (Ctypes.Tcons ta1 .. (Ctypes.Tcons tan Ctypes.Tnil) ..).

Notation "[| st1 ;; .. ;; stn1 ;; stn |]" := (Clight.Ssequence st1 .. (Clight.Ssequence stn1 stn) ..).


Module cc_types.
(** Clight types notations *)
Definition long := (Ctypes.Tlong Ctypes.Signed Ctypes.noattr).
Definition double := (Ctypes.Tfloat Ctypes.F64 Ctypes.noattr).
Definition pointer (ty : Ctypes.type):= (Ctypes.Tpointer ty Ctypes.noattr).

End cc_types.

Section Compil.


(** CFML to CompCert conversions *)

Coercion tr_int64 (n : int) : Integers.Int64.int :=
  Integers.Ptrofs.to_int64 (Integers.Ptrofs.repr n).


Fixpoint tr_types (ty : type) : Ctypes.type :=
  match ty with
  | type_long => cc_types.long
  | type_double => cc_types.double
  | type_ref ty => cc_types.pointer (tr_types ty)
  end.


Coercion tr_types : type >-> Ctypes.type.



Definition tr_binop (op : prim) : res (Cop.binary_operation * Ctypes.type) :=
  match op with
  | val_add ty => OK (Cop.Oadd, tr_types ty)
  | val_lt ty => OK (Cop.Olt, tr_types ty)
  | _ => Error (msg "tr_binop: not a binop")
  end.


  
(* tr_type *)

(* Parameter var_to_ident : var -> AST.ident. *)
(* rajouter (option ident) dans le constructeur
   calcul de l'ident

+ Fixpoint set_type (E : map var type) (t : trm) : trm
rajouter type_unknown dans la grammaire
   *)

(* Axiom var_ident_bij : forall (v : var) (i : AST.ident), *)
(*     ident_to_var (var_to_ident v) = v *)
(*     /\ var_to_ident (ident_to_var i) = i. *)

(* Coercion var_to_ident : var >-> AST.ident. *)


(* Definition this_first_unused_ident (x : unit) : AST.ident := *)
(*   3%positive. *)

(* Definition this_initial_generator (x: unit) : generator := *)
(*   mkgenerator (this_first_unused_ident x) nil. *)

(* (* Definition mon2 := mon this_first_unused_ident. *) *)
(* Compute match (gensym cc_types.long) (this_initial_generator tt) with *)
(*         | Res tbody g i => OK (tbody, g, i) *)
(*         | Err msg => Error msg *)
(*         end. *)
  
(* mmap for the gensym monad *)


Local Open Scope error_monad_scope.

Fixpoint is_expr (t : trm) : bool :=
  match t with
  | trm_val _ => true
  | trm_var _ => true
  | trm_apps val_get _ => true
  | trm_apps (val_prim op) _ => is_binop op
  | _ => false
  end.

            



Fixpoint tr_trm_expr (E : env_var)
  (var_ids : list (var*AST.ident)) (t : trm) : res Clight.expr :=
  let aux := tr_trm_expr E var_ids in
  match t with
  (* longs *)
  | trm_val (val_int n) => OK (Clight.Econst_long n cc_types.long)
  (* get *)
  | trm_apps val_get ((trm_var x) :: nil) =>
      do i <- find_var x var_ids;
      match PTree.get i E with
      (* stack *)
      | Some (stack, ty) =>
          OK (Clight.Evar i ty)
      | Some (heap, (type_ref ty) as tystar) =>
          OK (Clight.Ederef (Clight.Evar i ty) tystar)
      | Some (heap, _) => Error (msg "tr_trm_expr: non-pointer heap allocated variable")
      | Some (const, _) => Error (msg "tr_trm_expr: trying to 'get' a const")
      | None => Error (msg "tr_trm_expr: variable not found in environment")
      end
  (* temp *)
  | trm_var x =>
      do i <- find_var x var_ids;
      match PTree.get i E with
      | Some (const, ty) =>
          OK (Clight.Etempvar i ty)
      | Some (heap, (type_ref ty) as tystar) =>
          OK (Clight.Evar i ty)
      | Some (heap, _) => Error (msg "tr_trm_expr: non-pointer heap allocated variable")
      | Some (stack, ty) =>
          OK (Clight.Eaddrof (Clight.Evar i ty) (type_ref ty))
      | None => Error (msg "tr_trm_expr: variable not found in environment")
      end
  (* binop *)
  | trm_apps (val_prim op) (t1 :: t2 :: nil) =>
      if is_binop op then
        do (cop, ty) <- tr_binop op;
        do en1 <- aux t1;
        do en2 <- aux t2;
        OK (Clight.Ebinop cop en1 en2 ty)
      else Error (msg "tr_trm_expr: not a binop application")
  | _ => Error (msg "tr_trm_expr: not a translatable expr")
  end.



Fixpoint tr_trm_stmt (E : env_var)
  (var_ids : list (var*AST.ident))
  (t : trm) : res (Clight.statement) :=

  let aux := tr_trm_stmt E var_ids in
  let auxe := tr_trm_expr E var_ids in
  match t with
  (* sequence: [let _ = t1 in t2] *)
  | trm_let binding_anon t1 t2 =>
      do st1 <- aux t1;
      do st2 <- aux t2;
      OK ([| st1 ;; st2 |])
  (* pattern for funcall, kinda *)
  (* | trm_let (binding_var x t const) (trm_apps (trm_var f) ts) tk => *)
  (*     do es <- mmap auxe ts; *)
  (*     do stk <- aux tk; *)
  (*     OK (Clight.Scall (Some (var_to_ident x)) (Clight.Evar f [funtype..]) es) *)
  (* [alloc]. Assumes fun call has already been transformed to assign *)
(*      to a temp *)
  | trm_let (binding_var x ty const)
      (trm_apps val_alloc [tn] ) tk =>
      do i <- find_var x var_ids;
      do en <- auxe tn;
      do stk <- aux tk;
      OK ([| Clight.Sbuiltin (Some i) AST.EF_malloc
                ([[cc_types.long]])
                (en :: nil) ;;
              stk |])

  (* [let x = e in tk] *)

  | trm_let (binding_var x ty d) t tk =>
      do i <- find_var x var_ids;
      do e <- auxe t;
      do stk <- aux tk;
      match d with
      | const =>
          OK ([| Clight.Sset i e ;; stk |])
      | heap =>
          match ty with
          | type_ref ty' =>
              OK ([| Clight.Sassign (Clight.Evar i ty) e ;;
                     stk |])
          | _ => Error (msg "tr_trm_stmt: heap variable not declared as a pointer")
          end
      | stack =>
          OK ([| Clight.Sassign (Clight.Evar i ty) e ;; stk |])
      end

  (* various forms of [x = v;] *)
  | trm_apps val_set [(trm_var x) ; tv] =>
      do ev <- auxe tv;
      do i <- find_var x var_ids;
      match PTree.get i E with
      (* alloc on stack *)
      | Some (stack, t) =>
          OK (Clight.Sassign (Clight.Evar i t) ev)
      (* alloc on heap *)
      | Some (heap, (type_ref t) as tstar) =>
          OK (Clight.Sassign (Clight.Ederef (Clight.Evar i tstar) t) ev)
      | Some (const, t) =>
          Error (msg "tr_trm_stmt: trying to set a const var")
      | _ => Error (msg "tr_trm_stmt: error while setting a variable")
      end
          
  (* [while]. Assumes condition is pure *)
  | trm_while te tb =>
      do e <- auxe te;
      do stb <- aux tb;
      OK (Clight.Swhile e stb)
  (* [if]. Assumes condition is pure *)
  | trm_ite te t1 t2 =>
      do e <- auxe te;
      do st1 <- aux t1;
      do st2 <- aux t2;
      OK (Clight.Sifthenelse e st1 st2)

  | t =>
      if is_expr t then
      match auxe t with
        | OK e => OK (Clight.Sreturn (Some e))
        | Error m =>
            Error (m ++ (msg "tr_trm_stmt: not a translatable statement"))
        end
      else Error (msg "tr_trm_stmt: expr expected")
  end.


Definition tr_function (f : fundef) (var_ids : list (var * AST.ident))
  : res Clight.function :=
  let env := fold_left (fun '(x,i,ty) env => PTree.set i (const, ty) env) (env_var_join f.(vars) f.(temps)) f.(params) in
  do sbody <- tr_trm_stmt env var_ids f.(body);
  do cparams <- mmap (fun '(x, i, ty) => OK (i, tr_types ty)) f.(params);
  do cvars <- mmap (fun '(i, (d, ty)) => OK (i, tr_types ty)) (PTree.elements f.(vars));
  do ctemps <- mmap (fun '(i, (d, ty)) => OK (i, tr_types ty)) (PTree.elements f.(temps));
  OK (Clight.mkfunction
        f.(rettype)
        AST.cc_default
        cparams
        cvars
        ctemps
        sbody).
     
               


Definition tr_program (p : program) : res Clight.program.
Admitted.

End Compil.

(* Custom Syntax (from SLF) *)
  

  
Declare Custom Entry trm.
Import LibListNotation.

Declare Scope type_scope.

Notation "'long'" := type_long (at level 0, only parsing) : type_scope.
Notation "'double'" := type_double (at level 0, only parsing) : type_scope.
Notation "ty 'ref'" :=
  (type_ref ty) (at level 0, only parsing) : type_scope.


Declare Scope trm_scope.

Notation "<{ e }>" :=
  e
  (at level 0, e custom trm at level 99) : trm_scope.

Notation "( x )" :=
  x
  (in custom trm, x at level 99) : trm_scope.

Notation "'begin' e 'end'" :=
  e
  (in custom trm, e custom trm at level 99, only parsing) : trm_scope.

Notation "{ x }" :=
  x
  (in custom trm, x constr) : trm_scope.

Notation "x" := x
  (in custom trm at level 0,
   x constr at level 0) : trm_scope.


Notation "t1 '(' t2 , .. , tn ')'" :=
  (trm_apps t1 (cons (t2 : trm) .. (cons (tn : trm) nil) .. ))
    (in custom trm at level 30,
        t2 custom trm at level 99,
        tn custom trm at level 99,
      format "t1 '[   ' '(' t2 ',' .. ',' tn ')' ']'") : trm_scope.

Notation "'if' t0 'then' t1 'else' t2" :=
  (trm_ite t0 t1 t2)
  (in custom trm at level 69,
   t0 custom trm at level 99,
   t1 custom trm at level 99,
   t2 custom trm at level 99,
   left associativity,
   format "'[v' '[' 'if'  t0  'then'  ']' '/' '['   t1 ']' '/' 'else' '/' '['   t2 ']' ']'") : trm_scope.

Notation "'while' t1 'do' t2 'done'" :=
  (trm_while t1 t2)
  (in custom trm at level 0,
   t1 custom trm at level 99,
   t2 custom trm at level 99,
   format "'[v' 'while'  t1  'do'  '/' '['   t2 ']' '/'  'done' ']'")
   : trm_scope.

Notation "t1 ';' t2" :=
  (trm_let binding_anon t1 t2)
  (in custom trm at level 68,
   t2 custom trm at level 99,
   right associativity,
   format "'[v' '[' t1 ']' ';' '/' '[' t2 ']' ']'") : trm_scope.

Notation "'let' '(' x ':' ty '|' desc ')' '=' t1 'in' t2" :=
  (trm_let (binding_var x ty desc) t1 t2)
  (in custom trm at level 69,
      x at level 0,
      ty at level 0,
      desc at level 0,
      t1 custom trm at level 100,
      t2 custom trm at level 100,
      right associativity,
      format "'[v' '[' 'let'  '(' x ':' ty '|' desc ')' '='  t1  'in' ']' '/' '[' t2 ']' ']'") : trm_scope.

Notation "()" :=
  (trm_val val_unit)
  (in custom trm at level 0) : trm_scope.

Notation "()" :=
  (val_unit)
  (at level 0) : val_scope.


Notation "'ref'" :=
  (trm_val (val_prim val_ref))
  (in custom trm at level 0) : trm_scope.


Notation "! t" :=
  (val_get t)
  (in custom trm at level 67,
   t custom trm at level 99) : trm_scope.

(* Notation "'free'" := *)
(*   (trm_val (val_prim val_free)) *)
(*   (in custom trm at level 0) : trm_scope. *)

Notation "'alloc'" :=
  (trm_val (val_prim val_alloc))
  (in custom trm at level 0) : trm_scope.

Notation "t1 := t2" :=
  (val_set t1 t2)
  (in custom trm at level 67) : trm_scope.

Notation "t1 + t2" :=
  ((val_add type_long) t1 t2)
  (in custom trm at level 58) : trm_scope.

Notation "t1 < t2" :=
  ((val_lt type_long) t1 t2)
    (in custom trm at level 60) : trm_scope.


Module CFMLSyntax.

  Open Scope type_scope.
  Open Scope trm_scope.
  Open Scope val_scope.
  Open Scope string_scope.

  Coercion string_to_var (x:string) : var := x.
  Coercion int_to_trm (n:int) : trm := (trm_val (val_int n)).

End CFMLSyntax.


Section Tests.
  Import NotationForVariables Clight AST Ctypes.
  Import LibListNotation.

  Local Open Scope genident_monad_scope.
  Local Open Scope error_monad_scope.
  Open Scope string.
  
  Example test_trm_expr : trm :=
    trm_val (val_int 3).

  Example test_trm_expr2 : trm :=
    trm_var 'x.

  Example test_trm_stmt : trm :=
    trm_let (binding_var 'x type_long const) (val_int 3)
      (trm_let (binding_var 'y (type_ref type_long) const) (val_int 42)
         (trm_var "arg")).
    

  Import CFMLSyntax.

  Example test_trm_syntax : trm :=
    <{ let ('x1 : long ref | const) = alloc(1) in
       let ('y1 : long ref | const) = alloc(1) in
       let ('z1 : long ref | const) = alloc(1) in
       let ('x : long ref | heap) = 'x1 in
       let ('y : long ref | heap) = 'y1 in
       let ('z : long ref | heap) = 'z1 in
       'x := 1;
       'y := 1;
       'z := 0;
       while (! 'x) < 'n do
         'z := (! 'y);
         'y := (! 'x) + (! 'y);
         'x := (! 'z)
       done;
       (!'y)    
      }>.

  Print test_trm_syntax.
  
  
  Open Scope positive.


  
  Compute match get_temp_defs test_trm_stmt (initial_generator tt) with
          | Err msg => Error msg
          | Res env g i => OK (PTree.elements env, g.(gen_trail))
          end.
  
  Compute (tr_trm_expr (PTree.empty (var_descr*CompilationTest.type)) nil test_trm_expr).
  

  Compute do (f, l) <- make_function "funct" type_long
                        [('n, type_long)] test_trm_syntax;
          do cf <- tr_function f l;
          OK (f, PTree.elements f.(temps), PTree.elements f.(vars), cf, l).
          
            
  

End Tests.

(* rel_state : cfml.state -> clight.state -> Prop

   tr_correct : forall t s g P,
               t / s --> P ->
               rel_state s g ->
               (tr_trm E t) / g -->+
                       (fun c' g' => exists t' s',
                                     P t' s' /\
                                     rel_state s' g')



      G / t / s --> P
       -> si t := let x = t1 in t2
                 (x,v1)::G / t2 / s' --> P

G := env * temp_env

rel_state G env s g :=
        g = g1 \+ g2,
        forall l, v ∈ s, (l, tr v) ∈ G 
        forall x,v ∈ G,
               ∃ l, env!x = Some l, g2 l = Some tr v

Props:
rel_state -> dom s c dom g
rel_state -> fresh l g -> fresh l s

(define eventually omni small for clight : soit par dessus la small, soit directeement -> puis prouver equiv avec small sous hyp que les fonctions externes sont deter)


   OU : arriver dans un small traditionel : soit en partant d'un omni-small, soit d'un smallstep traditionel.

   tr_subst_com


   tr_expr : forall t,
             is_expr t ->
             eval_expr (tr_trm E t) G g (tr_val (subst G t))

 *)

