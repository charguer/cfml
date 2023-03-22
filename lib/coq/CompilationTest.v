Set Implicit Arguments.

From CFML Require Import Semantics LibSepFmap.

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
  

(* Section CFML_TYPES. *)

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
Inductive bind : Type :=
| bind_anon : bind
| bind_var : var -> type -> var_descr -> bind.

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
| trm_let : bind -> trm -> trm -> trm
| trm_while : trm -> trm -> trm
| trm_ite : trm -> trm -> trm -> trm.


Definition trm_seq (t1 t2 : trm) : trm :=
  trm_let bind_anon t1 t2.


Module VARS <: EQUALITY_TYPE.
  Definition t := var.
  Definition eq := eq_var_dec.
End VARS.
  
Module var_maps := EMap VARS.

Definition empty := var_maps.init (@None (var_descr*type)).

Definition env_var := fmap var (var_descr*type).

Record fundef : Type :=
  mkfundef {
      name: var;
      rettype: type;
      params: list (var*type);
      vars: env_var;
      temps: env_var;
      body: trm
  }.


Definition program := list fundef.

(* End CFML_TYPES. *)


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

Fixpoint get_var_defs (t : trm) : env_var :=
  match t with
  | trm_val v => empty
  | trm_var x => empty
  | trm_let (bind_var v ty stack)  t1 tk =>
      update (get_var_defs tk) v (stack, ty)
  | trm_let (bind_var v ty heap) t1 tk =>
      update (get_var_defs tk) v (heap, ty)
  | trm_let (bind_var _ _ const)  _ tk => (get_var_defs tk)
  | trm_let bind_anon t1 t2 => (get_var_defs t1) \+ (get_var_defs t2)
  | trm_apps t ts => empty
  | trm_while _ t => get_var_defs t
  | trm_ite _ t1 t2 => (get_var_defs t1) \+ (get_var_defs t2)
  end.

Fixpoint get_temp_defs (t : trm) : env_var :=
  match t with
  | trm_val v => empty
  | trm_var x => empty
  | trm_let (bind_var v ty const)  t1 tk =>
      update (get_var_defs tk) v (const, ty)
  | trm_let (bind_var _ _ _)  _ tk => (get_temp_defs tk)
  | trm_let bind_anon t1 t2 => (get_temp_defs t1) \+ (get_temp_defs t2)
  | trm_apps t ts => empty
  | trm_while _ t => get_temp_defs t
  | trm_ite _ t1 t2 => (get_temp_defs t1) \+ (get_temp_defs t2)
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




Notation "<<<( ta1 , .. , tan )>>>" := (Ctypes.Tcons ta1 .. (Ctypes.Tcons tan Ctypes.Tnil) ..).

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
(* tr_type *)

Parameter var_to_ident : var -> AST.ident.
Parameter ident_to_var : AST.ident -> var.
(* rajouter (option ident) dans le constructeur
   calcul de l'ident
(St : monade d'état, avec op `fresh` qui incrémente le compteur de num de var)
   Fixpoint set_ident (E: map (var-> ident)) (t : trm) : St (trm)


+ Fixpoint set_type (E : map var type) (t : trm) : trm
rajouter type_unknown dans la grammaire
   *)

Axiom var_ident_bij : forall (v : var) (i : AST.ident),
    ident_to_var (var_to_ident v) = v
    /\ var_to_ident (ident_to_var i) = i.

Coercion var_to_ident : var >-> AST.ident.
(* Coercion ident_to_var : AST.ident >-> var. *)


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
(* Fixpoint mmap (A B: Type) (f: A -> mon B) (l: list A) {struct l} : mon (list B) := *)
(*   match l with *)
(*   | nil => ret nil *)
(*   | hd :: tl => *)
(*       do hd' <- f hd; *)
(*       do tl' <- mmap f tl; *)
(*       ret (hd' :: tl') *)
(*   end. *)


Local Open Scope error_monad_scope.

Fixpoint tr_trm_expr (E : env_var) (t : trm) : res Clight.expr :=
  let aux := tr_trm_expr E in
  match t with
  (* longs *)
  | trm_val (val_int n) => OK (Clight.Econst_long n cc_types.long)
  (* get *)
  | trm_apps val_get ((trm_var x) :: nil) =>
      match Fmap.read E x with
      (* stack *)
      | (stack, ty) =>
          OK (Clight.Evar x ty)
      | (heap, (type_ref ty) as tystar) =>
          OK (Clight.Ederef (Clight.Evar x ty) tystar)
      (* | (const, ty) => *)
      (*     OK  (Clight.Etempvar x ty) *)
      | _ => Error (msg "tr_trm_expr: error while reading variable")
      end
  (* temp *)
  | trm_var x =>
      match Fmap.read E x with
      | (const, ty) =>
          OK (Clight.Etempvar x ty)
      | _ => Error (msg "tr_trm_expr: trying to use an alloc'ed variable as is")
      end
  (* add :> longs *)
  | trm_apps (val_add type_long) (t1 :: t2 :: nil) =>
      do en1 <- aux t1;
      do en2 <- aux t2;
      OK (Clight.Ebinop Cop.Oadd en1 en2 cc_types.long)
  (* lt :> longs *)
  | trm_apps (val_lt type_long) (t1 :: t2 :: nil) =>
      do en1 <- aux t1;
      do en2 <- aux t2;
      OK (Clight.Ebinop Cop.Olt en1 en2 cc_types.long)
  | _ => Error (msg "tr_trm_expr: not a translatable expr")
  end.



Fixpoint tr_trm_stmt (E : env_var) (t : trm) : res (Clight.statement) :=
  let aux := tr_trm_stmt E in
  let auxe := tr_trm_expr E in
  match t with
  (* sequence: [let _ = t1 in t2] *)
  | trm_let bind_anon t1 t2 =>
      do st1 <- aux t1;
      do st2 <- aux t2;
      OK ([| st1 ;; st2 |])
  (* pattern for funcall, kinda *)
  (* | trm_let (bind_var x t const) (trm_apps (trm_var f) ts) tk => *)
  (*     do es <- mmap auxe ts; *)
  (*     do stk <- aux tk; *)
  (*     OK (Clight.Scall (Some (var_to_ident x)) (Clight.Evar f [funtype..]) es) *)
  (* [alloc]. Assumes fun call has already been transformed to assign
     to a temp *)
  | trm_let (bind_var x ty const)
      (trm_apps val_alloc (tn :: nil)) tk =>
      do en <- auxe tn;
      do stk <- aux tk;
      OK ([| Clight.Sbuiltin (Some (var_to_ident x)) AST.EF_malloc
                (<<<(cc_types.long)>>>)
                (en :: nil) ;;
              stk |])

  (* [let x = e in tk] *)

  | trm_let (bind_var x ty d) t tk =>
      do e <- auxe t;
      do stk <- aux tk;
      match d with
      | const =>
          OK ([| Clight.Sset x e ;; stk |])
      | heap =>
          OK ([| Clight.Sassign
                     (Clight.Ederef (Clight.Evar x (cc_types.pointer ty))
                        ty) e ;;
                   stk |])
      | stack =>
          OK ([| Clight.Sassign (Clight.Evar x ty) e ;; stk |])
      end

  (* various forms of [x = v;] *)
  | trm_apps val_set ((trm_var x) :: tv :: nil) =>
      do ev <- tr_trm_expr E tv;
      match (Fmap.read E x) with
      (* alloc on stack *)
      | (stack, t) =>
          OK (Clight.Sassign (Clight.Evar x t) ev)
      (* alloc on heap *)
      | (heap, (type_ref t) as tstar) =>
          OK (Clight.Sassign (Clight.Ederef (Clight.Evar x tstar) t) ev)
      | (const, t) =>
          Error (msg "tr_trm_stmt: trying to set a const var")
      | _ => Error (msg "tr_trm_stmt: error while setting a variable")
      end
          
  (* [while]. Assumes condition is pure *)
  | trm_while te tb =>
      do e <- tr_trm_expr E te;
      do stb <- aux tb;
      OK (Clight.Swhile e stb)
  (* [if]. Assumes condition is pure *)
  | trm_ite te t1 t2 =>
      do e <- tr_trm_expr E te;
      do st1 <- aux t1;
      do st2 <- aux t2;
      OK (Clight.Sifthenelse e st1 st2)

  | _ => match auxe t with
        | OK e => OK (Clight.Sreturn (Some e))
        | Error _ =>
            Error (msg "tr_trm_stmt: not a translatable statement")
        end
  end.


Definition tr_function (f : fundef) : res Clight.function.
Admitted.



Definition tr_program (p : program) : res Clight.program.
Admitted.


End Compil.


Section Tests.
  Import NotationForVariables.
  Example test_trm_expr : trm :=
    trm_val (val_int 3).

  Example test_trm_expr2 : trm :=
    trm_var 'x.

  Example test_trm_stmt : trm :=
    trm_let (bind_var 'x type_long const) (val_int 3)
      (trm_var 'x).
    
  Local Open Scope error_monad_scope.

  Set Debug "Cbv".

  
  Compute (tr_trm_expr empty test_trm_expr).
  
  Eval vm_compute in (If (3 = 5) then False else True).

  Eval vm_compute in (tr_trm_expr (single 'x (const, type_long)) test_trm_expr2).

  Compute (get_temp_defs test_trm_stmt).

  Compute tr_trm_stmt (get_temp_defs test_trm_stmt) test_trm_stmt.
  
  
  

End Tests.
