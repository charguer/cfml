(** * Compiling CFML_C down to Clight *)

Set Implicit Arguments.

From CFML Require Import Semantics LibSepFmap CFML_C Clight_omni.
Import LibListNotation.

From compcert Require Coqlib Maps Integers Floats Values AST Ctypes Clight.
From compcert Require Import Maps Errors SimplExpr.

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

  Definition gensym (x: var') : mon var' :=
    fun (g: generator) =>
      match find_var (fst x) g.(gen_trail) with
      | Error msg => Res (fst x, Some (gen_next g))
                      (mkgenerator
                         (Pos.succ (gen_next g))
                         ((fst x, gen_next g) :: (gen_trail g)))
                      (Ple_succ (gen_next g))
      | OK i => Res (fst x, Some i) g (Ple_refl g.(gen_next))
      end.



  (* execute [f] without affecting the trail of [g], and while still generating
     unique idents. *)
  Definition save_trail {A B : Type} (f : A -> mon B) (a : A) : mon B :=
    fun (g : generator) =>
      match f a g with
      | Err msg => Err msg
      | Res b g' i =>
          Res b (mkgenerator
                   (gen_next g')
                   (gen_trail g))
            i
      end.



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

Fixpoint st_mmap {A B: Type} (f: A -> mon B) (l: list A) : mon (list B) :=
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

Close Scope genident_monad_scope.

Local Open Scope error_monad_scope.

Fixpoint mfold (A B : Type) (f : B -> A -> res B) (init : B) (l : list A) {struct l}
  : res B :=
  match l with
  | nil => OK init
  | hd :: tl =>
      do carry <- f init hd;
      do cont <- mfold f carry tl;
      OK cont
  end.

Close Scope error_monad_scope.
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


  Fixpoint set_var_idents (t : trm) {struct t} : mon (trm) :=
    match t with
    | trm_val v => ret t
    | trm_var x =>
        do x' <- gensym x;
        ret (trm_var x')
    | trm_let (binding_var x ty d) t1 tk =>
        do t1' <- save_trail set_var_idents t1;
        do x' <- gensym x;
        do tk' <- set_var_idents tk;
        ret (trm_let (binding_var x' ty d) t1' tk')
    | trm_let binding_anon t1 tk =>
        do t1' <- save_trail set_var_idents t1;
        do tk' <- set_var_idents tk;
        ret (trm_let binding_anon t1' tk')
    | trm_apps t ts =>
        do t' <- save_trail set_var_idents t;
        (* inlinig fmap so that coq accepts the fixpoint*)
        do ts' <- (fix fp (l : list trm) :=
          match l with
          | [] => ret []
          | hd::tl => do hd' <- save_trail set_var_idents hd;
                    do tl' <- fp tl;
                    ret (hd'::tl')%list
          end) ts;
        ret (trm_apps t' ts')
    | trm_ite e t1 t2 =>
        do e' <- save_trail set_var_idents e;
        do t1' <- save_trail set_var_idents t1;
        do t2' <- save_trail set_var_idents t2;
        ret (trm_ite e' t1' t2')
    | trm_while e t =>
        do e' <- save_trail set_var_idents e;
        do t' <- save_trail set_var_idents t;
        ret (trm_while e' t')
    end.

  Local Open Scope error_monad_scope.

  Fixpoint get_var_defs (t : trm) : res env_var :=
    match t with
    | trm_val v => OK (PTree.empty (var_descr*type))
    | trm_var x => OK (PTree.empty (var_descr*type))

    | trm_let (binding_var x ty stack) t1 tk =>
        do i <- get_ident x;
        do dtk <- get_var_defs tk;
        OK (PTree.set i (stack, ty) dtk)
    | trm_let (binding_var x ty heap) t1 tk =>
        do i <- get_ident x;
        do dtk <- get_var_defs tk;
        OK (PTree.set i (heap, ty) dtk)
    | trm_let (binding_var _ _ const) _ tk =>
        get_var_defs tk

    | trm_let binding_anon t1 t2 =>
        do dt1 <- get_var_defs t1;
        do dt2 <- get_var_defs t2;
        OK (env_var_join dt1 dt2)

    | trm_apps _ _ => OK (PTree.empty (var_descr*type))

    | trm_while _ t => get_var_defs t

    | trm_ite _ t1 t2 =>
        do dt1 <- get_var_defs t1;
        do dt2 <- get_var_defs t2;
        OK (env_var_join dt1 dt2)
    end.


  Fixpoint get_temp_defs (t : trm) : res env_var :=
    match t with
    | trm_val v => OK (PTree.empty (var_descr*type))
    | trm_var x => OK (PTree.empty (var_descr*type))

    | trm_let (binding_var x ty const) t1 tk =>
        do i <- get_ident x;
        do dtk <- get_temp_defs tk;
        OK (PTree.set i (const, ty) dtk)
    | trm_let (binding_var _ _ _) _ tk =>
        get_temp_defs tk

    | trm_let binding_anon t1 t2 =>
        do dt1 <- get_temp_defs t1;
        do dt2 <- get_temp_defs t2;
        OK (env_var_join dt1 dt2)

    | trm_apps _ _ => OK (PTree.empty (var_descr*type))

    | trm_while _ t => get_temp_defs t

    | trm_ite _ t1 t2 =>
        do dt1 <- get_temp_defs t1;
        do dt2 <- get_temp_defs t2;
        OK (env_var_join dt1 dt2)
    end.

End Preprocessing.


Local Open Scope genident_monad_scope.
Delimit Scope error_monad_scope with error_scope.

Definition make_function (f_name : var) (ret_type : type)
  (params : list (var' * type)) (body : trm) : res (fundef) :=

  let aux (x:unit) :=
    do params' <- st_mmap (fun '(x, ty) =>
                          do x' <- gensym x;
                          ret (x', ty))
                 params;
    do body' <- set_var_idents body;
    ret (params', body')
  in
  match aux tt (initial_generator tt) with
  | Err msg => Error msg
  | Res (p, b) g i =>
      (do vars <- get_var_defs b;
       do temps <- get_temp_defs b;
       OK (mkfundef f_name ret_type p vars temps b))%error_scope
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

(* Clight.program -> main : "main"


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

Notation "[| st1 ;; .. ;; stn1 ;; stn |]" :=
  (Clight.Ssequence st1 .. (Clight.Ssequence stn1 stn) ..)
    (only parsing).


Module cc_types.
(** Clight types notations *)
  Import Ctypes.
  Definition long := (Tlong Signed noattr).
  Definition double := (Tfloat F64 noattr).
  Definition pointer (ty : type):= (Tpointer ty noattr).

  Fixpoint tr_types (ty : CFML_C.type) : Ctypes.type :=
    match ty with
    | type_long => cc_types.long
    | type_double => cc_types.double
    | type_ref ty => cc_types.pointer (tr_types ty)
    end.


  Coercion tr_types : CFML_C.type >-> Ctypes.type.

  Definition make_funtype (t_params : list CFML_C.type) (rettype : CFML_C.type) : type :=

    Tfunction (fold_right (fun ty tl => Tcons (tr_types ty) tl) Tnil t_params)
              rettype AST.cc_default.

End cc_types.

Section Compil.


(** CFML to CompCert conversions *)


  Import cc_types.


  Coercion tr_int64 (n : int) : Integers.Int64.int :=
    Integers.Ptrofs.to_int64 (Integers.Ptrofs.repr n).





  Definition tr_binop (op : prim) : res (Cop.binary_operation * Ctypes.type) :=
    match op with
    | val_add ty => OK (Cop.Oadd, tr_types ty)
    | val_ptr_add => OK (Cop.Oadd, cc_types.pointer cc_types.long)
    | val_lt ty => OK (Cop.Olt, tr_types ty)
    | _ => Error (msg "tr_binop: not a binop")
    end.



  Local Open Scope error_monad_scope.

  (** translate values (mostly for temporary environments) *)
  Definition tr_val (v : val) : Values.val :=
    match v with
    | val_uninitialized => Values.Vundef
    | val_loc O => Values.Vundef
    | val_loc l => Values.Vptr (Pos.of_nat l) Integers.Ptrofs.zero
    | val_int i => Values.Vlong i
    | val_unit => Values.Vlong 0
    | val_prim _ => Values.Vundef
    end.

  Parameter R_env : val_env -> Clight.env -> Clight.temp_env -> Prop.

  (** get values of consts from a [val_env] *)
  Definition tr_temp_env (G : val_env) : Clight.temp_env :=
    PTree.fold (fun g i '(v,d,ty) => match d with
                                  | const => PTree.set i (tr_val v) g
                                  | _ => g
                                  end)
               G (PTree.empty Values.val).

  Parameter R_mem : state -> Memory.mem -> Prop.

  Parameter R_cont : CFML_C.continuation -> Clight.cont -> Prop.

  (** ** Compiles pure expressions  *)

  Fixpoint tr_trm_expr (E : env_var) (t : trm) : res Clight.expr :=
    let aux := tr_trm_expr E in
    match t with
    (* longs *)
    | trm_val (val_int n) => OK (Clight.Econst_long n cc_types.long)
    (* get *)
    | trm_apps val_get [trm_var x] =>
        do i <- get_ident x;
        match PTree.get i E with
        (* stack *)
        | Some (stack, ty) =>
            OK (Clight.Evar i ty)
        | Some (heap, (type_ref ty) as tystar) =>
            OK (Clight.Ederef (Clight.Evar i tystar) ty)
        | Some (heap, _) => Error (msg "tr_trm_expr: non-pointer heap allocated variable")
        | Some (const, _) => Error (msg "tr_trm_expr: trying to 'get' a const")
        | None => Error (msg "tr_trm_expr: variable not found in environment")
        end
    (* temp *)
    | trm_var x =>
        do i <- get_ident x;
        match PTree.get i E with
        | Some (const, ty) =>
            OK (Clight.Etempvar i ty)
        | Some (heap, (type_ref ty) as tystar) =>
            OK (Clight.Evar i tystar)
        | Some (heap, _) => Error (msg "tr_trm_expr: non-pointer heap allocated variable")
        | Some (stack, ty) =>
            OK (Clight.Eaddrof (Clight.Evar i ty) (type_ref ty))
        | None => Error (msg "tr_trm_expr: variable not found in environment")
        end
    (* binop *)
    | trm_apps (val_prim op) [t1 ; t2] =>
        if is_binop op then
          do (cop, ty) <- tr_binop op;
          do en1 <- aux t1;
          do en2 <- aux t2;
          OK (Clight.Ebinop cop en1 en2 ty)
        else Error (msg "tr_trm_expr: not a binop application")
    | _ => Error (msg "tr_trm_expr: not a translatable expr")
    end.


  (** ** Compiles statements *)

  Fixpoint tr_trm_stmt (E : env_var) (fundecl_types : PTree.t ((list type) * type))
    (t : trm) : res (Clight.statement) :=

    let aux := tr_trm_stmt E fundecl_types in
    let auxe := tr_trm_expr E in
    match t with
    (* sequence: [let _ = t1 in t2] *)
    | trm_let binding_anon t1 t2 =>
        do st1 <- aux t1;
        do st2 <- aux t2;
        OK ([| st1 ;; st2 |])
    (* funcall *)
    | trm_let (binding_var x ty const) (trm_apps (trm_var f) ts) tk =>
        do es <- mmap auxe ts;
        do i__x <- get_ident x;
        do i__f <- get_ident f;
        do stk <- aux tk;
        match fundecl_types ! i__f with
        | Some (t_params, rettype) =>
            OK ([| Clight.Scall (Some i__x)
                     (Clight.Evar i__f (make_funtype t_params rettype)) es ;;
                   stk |])
        | None => Error (msg "tr_trm_stmt : call to an undeclared function")
        end
    (* [alloc]. Assumes fun call has already been transformed to assign *)
    (*      to a temp *)
    | trm_let (binding_var x ty const)
        (trm_apps val_alloc [tn] ) tk =>
        do i <- get_ident x;
        do en <- auxe tn;
        do stk <- aux tk;
        OK ([| Clight.Sbuiltin (Some i) AST.EF_malloc
                 ([[cc_types.long]])
                 (en :: nil) ;;
               stk |])

    (* [let x = e in tk] *)
    | trm_let (binding_var x ty d) (val_uninitialized) tk =>
        match d with
        | stack =>
            do stk <- aux tk;
            OK stk
        | _ =>
            Error (msg "tr_trm_stmt: only stack variabels can be declared as uninitialised")
        end

    | trm_let (binding_var x ty d) t tk =>
        do i <- get_ident x;
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
        do i <- get_ident x;
        match PTree.get i E with
        (* alloc on stack *)
        | Some (stack, ty) =>
            OK (Clight.Sassign (Clight.Evar i ty) ev)
        (* alloc on heap *)
        | Some (heap, (type_ref ty) as tystar) =>
            OK (Clight.Sassign (Clight.Ederef (Clight.Evar i tystar) ty) ev)
        | Some (const, ty) =>
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


  Definition tr_function (f : fundef)
    (fundecl_types : PTree.t ((list type) * type)) : res Clight.function :=
    do env <- mfold (fun env '(x, ty) =>
                      do i <- get_ident x;
                      OK (PTree.set i (const, ty) env))
               (env_var_join f.(vars) f.(temps)) f.(params);
    do sbody <- tr_trm_stmt env fundecl_types f.(body);
    do cparams <- mmap (fun '(x, ty) =>
                         do i <- get_ident x;
                         OK (i, tr_types ty))
                   f.(params);
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




Section Compil_correct.

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

(define eventually omni small for clight :
 soit par dessus la small, soit directement ->
 puis prouver equiv avec small sous hyp que les fonctions externes sont deter
)


   OU : arriver dans un small traditionel : soit en partant d'un omni-small, soit d'un smallstep traditionel.

   tr_subst_com


   tr_expr : forall t,
             is_expr t ->
             eval_expr (tr_trm E t) G g (tr_val (subst G t))

 *)




  (* probably not the best way to do that, temporary solution *)
  Definition val_env_and_env_var_match (G : val_env) (GV : env_var) : Prop :=
    PTree.fold (fun b i '(v, d, ty) => b /\ (PTree.get i GV = Some (d, ty))) G True.

  (** ** Correctness of pure expression translation *)

  (** If [e] is an expression, reduces to a value in environment [G]
      and memory state [s], and compiles to a Clight expression [ex],
      then so does [ex]. *)
  (* Lemma tr_expr_correct : forall (e : trm) (ex : Clight.expr) (G : env) (GV : env_var) *)
  (*                           s (v : val) (ge : Clight.genv), *)
  (*     is_expr e -> *)
  (*     env_and_env_var_match G GV -> *)
  (*     (* G / e / s -->e⋄ (fun s' G' v' => s' = s /\  G' = G /\ v' = v) -> *) *)
  (*     eventually_expr G s e (fun s' G' v' => s' = s /\ G' = G /\ v' = v)  -> *)
  (*     (tr_trm_expr GV e) = OK ex -> *)
  (*     Clight.eval_expr ge (tr_env G) (tr_temp_env G) *)
  (*       (tr_mem s) ex (tr_val v). *)
  (* Proof. *)
  (* Admitted. *)

  (** [R] is the bisim relation we will be using.
      [R t f G s st] *)
  Definition R (FT : CFML_C.funtypes_env) (E : env_var) (c : CFML_C.config)
    (st : Clight.state) : Prop :=
    let '(f, G, s, t, k) := c in
    match st with
    | (Clight.State fc sc kc Ec tEc mc) =>
        tr_function f FT = OK fc
        /\ tr_trm_stmt E FT t = OK sc
        /\ R_mem s mc
        /\ R_env G Ec tEc
        /\ R_cont k kc
    | _ => False
    end.

  (** ** Correctness of statement translation *)
  Definition stmt_pc_final (P : CFML_C.stmt_pc) : Prop :=
    forall f G s t k, P (f, G, s, t, k) ->
                 (exists v, t = trm_val v).


  Lemma tr_stmt_correct : forall (c : CFML_C.config) (P : CFML_C.stmt_pc) (E : env_var)
                            (F : fundef_env) (FT : PTree.t (list type * type))
                            (ge : Clight.genv) (st : Clight.state),
      stmt_pc_final P ->
      R FT E c st ->
      eventually F c P ->
      Clight_omni.eventually' ge st
        (fun st' => exists c', P c' /\ R FT E c' st').
  Proof.
  Admitted.


End Compil_correct.


Import Clight AST Ctypes.

Declare Scope stmt_scope.

Notation "n 'i'" :=
  ({| Integers.Int64.intval := n; Integers.Int64.intrange := _ |})
    (at level 0, only printing, n at level 99,
    format "n 'i'") : stmt_scope.

Notation "Tlong" :=
  (Tlong Signed _)
    (at level 20, only printing) : stmt_scope.

Notation "ty '*'" :=
  (Tpointer ty _)
    (at level 0, only printing, ty at level 20,
     format "ty '*'") : stmt_scope.

Notation "'⋆' ( v ) '#' ty" :=
  (Ederef v ty)
    (at level 31, only printing, format "'⋆' '(' v ')' '#' ty") : stmt_scope.

Notation "'_' v '#' ty" :=
  (Etempvar v ty)
    (at level 30, only printing,
    format "'_' v '#' ty") : stmt_scope.

Notation "v '#' ty" :=
  (Evar v ty)
    (at level 30, only printing,
      format "v '#' ty") : stmt_scope.

Notation "v '@long' " :=
  (Econst_long v _)
    (at level 30, only printing, format "v '@long'") : stmt_scope.


Notation "'_' v '<-' f '(' e1 ',' .. ',' en ')'" :=
  (Sbuiltin (@Some positive v) f _ (@cons expr e1 .. (@cons expr en nil) .. ))
    (only printing, at level 69,
        f, v at level 0, e1, en at level 32,
        format "'_' v  '<-'  f '(' '[' e1 ','  .. ','  en ']' ')'" ) : stmt_scope.

Notation "e1 ':=' e2" :=
  (Sassign e1 e2)
    (only printing, at level 69,
      format "e1  ':='  e2") : stmt_scope.

Notation "t1 ';' t2" :=
  (Ssequence t1 t2)
    (only printing, at level 70,
        (* t2 at level 99, *)
        right associativity,
        format "'[v' '[' t1 ']' ';' '/' '[' t2 ']' ']'") : stmt_scope.

Notation "e1 '<c' e2" :=
  (Ebinop Cop.Olt e1 e2 _)
    (only printing, at level 32, format "'[' e1 ']'  '<c'  '[' e2 ']'") : stmt_scope.

Notation "e1 '+c' e2" :=
  (Ebinop Cop.Oadd e1 e2 _)
    (only printing, at level 32,  format "'[' e1 ']'  '+c'  '[' e2 ']'") : stmt_scope.

Notation "'if' '(' e ')' '{' t1 '}' 'else' '{' t2 '}'" :=
  (Sifthenelse e t1 t2)
    (only printing, at level 69,
     format "'[v' 'if'  '(' e ')'  '{' '/    ' '[v' t1 ']' '/' '}'  'else'  '{' '/    ' '[v' t2 ']' '/' '}' ']'") : stmt_scope.

Notation "'while' '(1)' '{' t '}'" :=
  (Sloop t Sskip)
    (only printing, at level 69,
    format "'[v' 'while'  '(1)'  '{' '/    ' '[v' t ']' '/' '}' ']'") : stmt_scope.

Notation "'return' e ';'" :=
  (Sreturn (Some e))
    (only printing, at level 69,
    format "'return'  e ';'") : stmt_scope.

Notation "'return;'" :=
  (Sreturn None) : stmt_scope.

Module ClightSyntax.

  Open Scope stmt_scope.

End ClightSyntax.


Section Tests.
  Import NotationForVariables Clight AST Ctypes.
  (* Import LibListNotation. *)

  Local Open Scope positive.
  Local Open Scope nat.
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
         (trm_var ("arg",None))).


  Import CFMLSyntax.

  Example test_trm_syntax : trm :=
    <{ let ('x1 : long ref # const) = alloc(1) in
       let ('y1 : long ref # const) = alloc(1) in
       let ('z1 : long ref # const) = alloc(1) in
       let ('x : long ref # heap) = 'x1 in
       let ('y : long ref # heap) = 'y1 in
       let ('z : long ref # heap) = 'z1 in
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

  Example test_trm_syntax_stack : trm :=
    <{ let ('x : long # stack) = 1 in
       let ('y : long # stack) = 1 in
       let ('z : long # stack) = 0 in
       while !'x < 'n do
         'z := !'y;
         'y := !'x + !'y;
         'x := !'z
       done;
       !'y
      }>.

  Print test_trm_syntax_stack.

  Compute set_var_idents test_trm_syntax (initial_generator tt).

  Import ClightSyntax.

  Close Scope liblist_scope.


  Example clight_syntax :=
    Ssequence
      (Sbuiltin (Some 2%positive) EF_malloc
         (Tcons (Tlong Signed {| attr_volatile := false; attr_alignas := None |})
            Tnil)
         (cons
            (Econst_long
               {|
                 Integers.Int64.intval := 1;
                 Integers.Int64.intrange := Integers.Int64.Z_mod_modulus_range' 1
               |} (Tlong Signed {| attr_volatile := false; attr_alignas := None |}))
            nil))
      (Sbuiltin (Some 2%positive) EF_malloc
         (Tcons (Tlong Signed {| attr_volatile := false; attr_alignas := None |})
            Tnil)
         (cons
            (Econst_long
               {|
                 Integers.Int64.intval := 1;
                 Integers.Int64.intrange := Integers.Int64.Z_mod_modulus_range' 1
               |} (Tlong Signed {| attr_volatile := false; attr_alignas := None |}))
            nil)).

  Eval vm_compute in clight_syntax.

  Notation "'_' v '<-' f '(' e1 ',' .. ',' en ')'" :=
    (Sbuiltin (@Some positive v) f _ (@cons expr e1 .. (@cons expr en nil) .. ))
      (only printing, at level 69,
        f, v at level 0, e1, en at level 32,
        format "'_' v  '<-'  f '(' '[' e1 ','  .. ','  en ']' ')'" ) : stmt_scope.

  Example clight_expr_ts :=
    Evar 3%positive cc_types.long.
  Print clight_expr_ts.

  (* Open Scope positive. *)
  (* Compute match get_temp_defs test_trm_stmt (initial_generator tt) with *)
  (*         | Err msg => Error msg *)
  (*         | Res env g i => OK (PTree.elements env, g.(gen_trail)) *)
  (*         end. *)

  Compute (tr_trm_expr (PTree.empty (var_descr*CFML_C.type)) test_trm_expr).

  Open Scope positive.

  (* Unset Printing Notations. *)
  (* Set Printing Coercions. *)
  Eval compute in do f <- make_function "funct" type_long
                   [(('n : var'), type_long)] test_trm_syntax;
          do cf <- tr_function f (PTree.empty (list CFML_C.type * CFML_C.type));
          OK (f, PTree.elements f.(temps), PTree.elements f.(vars), cf
            ).

  (* Eval vm_compute in do f <- make_function "funct" type_long *)
  (*                  [(('n : var'), type_long)] test_trm_syntax_stack; *)
  (*         do cf <- tr_function f; *)
  (*         OK (f, PTree.elements f.(temps), PTree.elements f.(vars), cf *)
  (*           ). *)

End Tests.
