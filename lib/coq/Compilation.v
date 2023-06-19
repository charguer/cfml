(** * Compiling CFML_C down to Clight *)

Set Implicit Arguments.

From TLC Require Import LibList LibMap LibSet.
From CFML Require OmnibigMeta.
From CFML Require Import Semantics LibSepFmap CFML_C ClightInterface.
Import LibListNotation.

From compcert Require Coqlib Maps Integers Floats Values AST Ctypes Ctyping
  Clight ClightBigstep.
From compcert Require Import Maps Errors SimplExpr Globalenvs.

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
          | [] => ret ([])
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


  Notation ptr_ofs := Integers.Ptrofs.int.


  Notation sizeof ty := (Clight.Esizeof ty (Ctyping.size_t)).


  Lemma all_access_by_value :
    forall (ty : CFML_C.type), exists x, Ctypes.access_mode ty = Ctypes.By_value x.
  Proof using.
    intros. induction ty; cbn; eauto.
  Qed.

  Definition chunk_of_type (ty : Ctypes.type) :=
    (AST.chunk_of_type (Ctypes.typ_of_type ty)).

  Lemma access_mode_is_chunk_of_type : forall (ty : CFML_C.type),
      Ctypes.access_mode ty = Ctypes.By_value (chunk_of_type ty).
  Proof using.
    induction ty; unfold chunk_of_type; cbn; eauto.
  Qed.

End cc_types.


Section Compil.


(** CFML to CompCert conversions *)


  Import cc_types.


  Coercion tr_int64 (n : int) : Integers.Int64.int :=
    Integers.Ptrofs.to_int64 (Integers.Ptrofs.repr n).



  Notation e_mult e1 e2 ty := (Clight.Ebinop Cop.Omul e1 e2 ty).



  Definition tr_binop (op : prim) : res (Cop.binary_operation * Ctypes.type) :=
    match op with
    | val_add ty => OK (Cop.Oadd, tr_types ty)
    | val_ptr_add ty => OK (Cop.Oadd, tr_types ty)
    | val_lt ty => OK (Cop.Olt, tr_types ty)
    | _ => Error (msg "tr_binop: not a binop")
    end.



  Local Open Scope error_monad_scope.


  (** ** Compiles pure expressions  *)

  Fixpoint tr_trm_expr (E : env_var) (t : trm) : res Clight.expr :=
    let aux := tr_trm_expr E in
    match t with
    (* longs *)
    | trm_val (val_int n) => OK (Clight.Econst_long n cc_types.long)
    (* get *)
    | trm_apps val_get ([trm_var x]) =>
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
    | trm_apps (val_prim op) ([t1 ; t2]) =>
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
        (trm_apps (val_alloc ty') ([tn]) ) tk =>
        if CFML_C.eq_type_dec ty (type_ref ty') then
          do i <- get_ident x;
          do en <- auxe tn;
          do stk <- aux tk;
          OK ([| Clight.Sbuiltin (Some i) AST.EF_malloc
                   ([[Ctyping.size_t]])
                   ((e_mult en (sizeof ty') Ctyping.size_t) :: nil) ;;
                 stk |])
        else Error (msg "tr_trm_stmt: type mismatch in alloc")

    (* [let x = e in tk] *)
    | trm_let (binding_var x ty stack) (val_uninitialized) tk =>
            do stk <- aux tk;
            OK stk

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
    | trm_apps val_set ([(trm_var x) ; tv]) =>
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
        (* TODO: invariant, expr ici jamais à gauche d'une seq *)
        if is_expr t then
          match auxe t with
          | OK e => OK (Clight.Sreturn (Some e))
          | Error m =>
              Error (m ++ (msg "tr_trm_stmt: not a translatable statement"))
          end
        else Error (msg "tr_trm_stmt: expr expected")
    end.





  Definition tr_function (f : fundef)
    (fundecl_types : CFML_C.funtypes_env) : res Clight.function :=
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


Section PTree_rel.
  Variable A B: Type.

  Definition ptree_relate (P : A -> Prop) (R : A -> B -> Prop)
    (P1 : PTree.t A) (P2 : PTree.t B) : Prop :=
    forall (i : positive) (a : A),
      PTree.get i P1 = Some a ->
      P a ->
      exists (b : B), PTree.get i P2 = Some b /\ R a b.

  Lemma ptree_relate_add_out :
    forall P R P1 P1' P2 i a,
      ptree_relate P R P1 P2 ->
      ~(P a) ->
      PTree.set i a P1 = P1' ->
      ptree_relate P R P1' P2.
  Proof using.
    intros. subst. unfold ptree_relate in H |- *. intros.
    forwards *: PTree.gsspec i0 i a P1.
    destruct (Coqlib.peq i0 i); subst.
    - cuts :(a = a0); subst. contradiction. congruence.
    - applys* H. congruence.
  Qed.

  Lemma ptree_relate_add_in :
    forall P R P1 P1' P2 P2' i a b,
      ptree_relate P R P1 P2 ->
      P a ->
      R a b ->
      PTree.set i a P1 = P1' ->
      PTree.set i b P2 = P2' ->
      ptree_relate P R P1' P2'.
  Proof using.
    intros. subst. unfold ptree_relate in H |- *.
    intros.
    forwards *: PTree.gsspec i0 i a P1.
    forwards *: PTree.gsspec i0 i b P2.
    destruct (Coqlib.peq i0 i); subst.
    - asserts Ha:(a = a0). congruence. subst.
      exists b. splits*.
    - forwards * : H i0. congruence. setoid_rewrite H5.
      auto.
  Qed.


End PTree_rel.


Section Compil_correct.

  Import CFMLSyntax cc_types.
  Import CFML_C OmnibigMeta ClightInterface.

  Instance Inhab_pos_type : Inhab (positive * CFML_C.type).
  Proof using. apply (Inhab_of_val (1%positive, type_long)). Qed.

  Instance Inhab_ptr_ofs : Inhab (ptr_ofs).
  Proof using. apply (Inhab_of_val (Integers.Ptrofs.zero)). Qed.


  Definition map_loc_out_type : Type := CFML_C.type * Values.block * ptr_ofs.

  Instance Inhab_loc_map : Inhab map_loc_out_type.
  Proof using.
    apply (Inhab_of_val (type_long, 1%positive, Integers.Ptrofs.zero)).
  Qed.

  Definition map_loc := map loc map_loc_out_type.

  Coercion Integers.Ptrofs.intval : Integers.Ptrofs.int >-> Z.

  Definition wf_map_loc (M : map_loc) :=
    forall l l' (ty ty' : type) (b b' : Values.block) (ofs ofs' : ptr_ofs),
      l \indom M ->
      l' \indom M ->
      l <> l' ->
      M [l] = (ty, b, ofs) ->
      M [l'] = (ty', b', ofs') ->
      b <> b'
      \/ ofs + (Memdata.size_chunk (cc_types.chunk_of_type (tr_types ty))) <= ofs'
      \/ ofs' + (Memdata.size_chunk (cc_types.chunk_of_type (tr_types ty'))) <= ofs.


  Variable ge : Clight.genv.




  (* WIP verif type obligs *)
  Variant match_values
    (M : map_loc) :
    CFML_C.type -> CFML_C.val -> Values.val -> Prop :=
    | match_values_int : forall (n : int),
        match_values M type_long (val_int n) (Values.Vlong n)
    | match_values_float : forall (d : Floats.float),
        match_values M type_double (val_double d) (Values.Vfloat d)
    | match_values_loc : forall (l l' : loc) ty
                           (b : Values.block) (ofs : ptr_ofs),
        l \indom M ->
        M [l] = (ty, b, ofs) ->
        match_values M (type_ref ty) (val_loc l) (Values.Vptr b ofs).


  Lemma match_val_has_type : forall M ty vs vt,
      wf_map_loc M ->
      match_values M ty vs vt ->
      Values.Val.has_type vt (Ctypes.typ_of_type ty).
  Proof using.
    induction ty; intros; cbn; inversion H0; cbn; eauto.
    unfold AST.Tptr. destruct Archi.ptr64; eauto.
  Qed.



  Definition match_temp_env (G : val_env) (te : Clight.temp_env)
    (M : map_loc) : Prop :=
        forall i v ty,
          PTree.get i G = Some (v, const, ty) ->
          (exists vt, PTree.get i te = Some vt /\ match_values M ty v vt).

        (* -> PTree_relate P R p1 p2
         R : relat entre valeurs
         P : filtre

         Lems:
         ptree_relate_add_out (on ne vérifie pas P)
         ptree_relate_add_in (on fait les deux add)

Lemma ptree_relate_add :
ptree_relate P R p1 p2 ->
if (P x) then ()
ptree_relate P R (add x p1) p2'

         *)

        (* M [l] = ty,, -> typeof (m [l]) ty *)



  Definition match_static_env (G : val_env) (e : Clight.env)
    (M : map_loc) : Prop :=
    forall i l d ty,
      d = stack \/ d = heap ->    (* d <> const *)
      PTree.get i G = Some (val_loc l, d, ty) ->
      (exists b,
          (* l \indom M -> *)
          (* M [l] = (ty, b, Integers.Ptrofs.zero) *)
          match_values M (type_ref ty) l (Values.Vptr b (Integers.Ptrofs.zero))
          /\ PTree.get i e = Some (b, tr_types ty)).


  Definition match_mem_vals (s : CFML_C.state) (m : Memory.Mem.mem)
    (M : map_loc) : Prop :=
    forall l b (ty : CFML_C.type) (ofs : ptr_ofs),
      l \indom M ->
      M [l] = (ty, b, ofs) ->
      let chunk := cc_types.chunk_of_type ty in
      Fmap.indom s l
      /\ Memory.Mem.valid_access m chunk b ofs Memtype.Freeable
      /\ (exists vt, Memory.Mem.load chunk m b ofs = Some vt
               /\ match_values M ty (Fmap.read s l) vt).

  Definition wf_env_and_mem (G : val_env) (s : CFML_C.state) : Prop :=
    forall l d ty i,
      PTree.get i G = Some (val_loc l, d, ty) ->
      d = heap \/ d = stack -> (* (d <> const) *)
      Fmap.indom s l.

  Variant match_config_expr (E : env_var)
   (M : map_loc) :
    CFML_C.config ->
   (PTree.tree (Values.block * Ctypes.type) * PTree.tree Values.val * Memory.Mem.mem *
   Clight.expr) -> Prop :=
    | match_config_expr_intro : forall f' G s t k e te m a,

        tr_trm_expr E t = OK a ->

        match_temp_env G te M ->
        match_static_env G e M ->

        wf_map_loc M ->
        match_mem_vals s m M ->
        wf_env_and_mem G s ->

        match_config_expr E M (f', G, s, t, k) (e, te, m, a).



  Variant match_config (FT : CFML_C.funtypes_env) (E : env_var) :
    CFML_C.config -> ClightInterface.config -> Prop :=
    | match_config_intro : forall f' G s t k e te m st,

        forall (M : map_loc),

        tr_trm_stmt E FT t = OK st ->

        match_temp_env G te M ->
        match_static_env G e M ->

        wf_map_loc M ->
        match_mem_vals s m M ->
        wf_env_and_mem G s ->

        match_config FT E (f', G, s, t, k) (e, te, m, st).




  Variant match_outs (M : map_loc)
    : CFML_C.val -> ClightBigstep.outcome -> Prop :=
    | match_outs_normal :
      match_outs M val_unit ClightBigstep.Out_normal
    | match_outs_ret_none :
      match_outs M val_unit (ClightBigstep.Out_return None)
    | match_outs_ret_val : forall vs ty vt,
        match_values M ty vs vt ->
        match_outs M vs (ClightBigstep.Out_return (Some (vt, tr_types ty))).


  Variant match_final_states (FT : CFML_C.funtypes_env) (E : env_var)
    (e : Clight.env):
    CFML_C.final_config -> ClightInterface.final_config -> Prop :=
    | match_final_states_intro : forall f' G s v k te m out,

      forall (M : map_loc),

        match_temp_env G te M ->

        match_static_env G e M ->

        wf_map_loc M ->

        match_mem_vals s m M ->

        match_outs M v out ->

        match_final_states FT E e (f', G, s, v, k) (te, m, out).




  Lemma forward_expr (E : env_var)
    (M : map_loc) :
    forall '(f', G, s, te, k) env le m a Q ty,
      match_config_expr E M (f', G, s, te, k) (env, le, m, a) ->
      tr_types ty = Clight.typeof a ->
      cfml_omnibig_expr G s te Q ->
      exists v, Clight.eval_expr ge env le m a v /\
             (exists vs, Q vs /\ match_values M ty vs v).
  Proof.
  Admitted.

  (** ** Correctness of statement translation *)

  Lemma assign_correct : forall s s' m m' l b ofs M vs vt ty chunk,
      wf_map_loc M ->
      match_mem_vals s m M ->
      match_values M (type_ref ty) (val_loc l) (Values.Vptr b ofs) ->
      match_values M ty vs vt ->
      s' = Fmap.update s l vs ->
      Ctypes.access_mode ty = Ctypes.By_value chunk ->
      Memory.Mem.storev chunk m (Values.Vptr b ofs) vt = Some m' ->

      (* Clight.assign_loc (Clight.genv_cenv ge) ty m b ofs bf vt m' -> *)
      match_mem_vals s' m' M.
  Proof using.
    intros.
    unfold match_mem_vals in H0.
    constructors*;
    forwards *(Hdoml0&Haccess& vt0 & Hload&Hvalues):H0 l0 b0 ty0 ofs0.
    rewrites H3. unfold Fmap.update. applys* Fmap.indom_union_r.
    splits*.
    - eapply Memory.Mem.store_valid_access_1.
      cbn in H5. eapply H5. eapply Haccess.
    - inversion H1. subst.
        ecase (Nat.eq_dec l l0); intros.
        * subst. rewrite H7 in H13. inversion H13; subst.
          eexists. split.
          applys* Memory.Mem.load_store_same.
          cbn in H5. forwards *Hchunk: cc_types.access_mode_is_chunk_of_type ty.
          rewrite Hchunk in H4. inversion H4. subst.
          eapply H5. setoid_rewrite Fmap.read_union_l.
          setoid_rewrite Fmap.read_single.
          unfold chunk_of_type.
          rewrites* Values.Val.load_result_same.
          applys * match_val_has_type. apply Fmap.indom_single.
        * forwards *: H l l0. forwards *: Memory.Mem.load_store_other b b0.
          {
            branches * H3.
            forwards *Hchunk: cc_types.access_mode_is_chunk_of_type ty.
            rewrite Hchunk in H4. inversion H4. subst.
            eauto.
          }
          eexists. rewrites* H8. rewrite Hload.
          splits *. setoid_rewrite Fmap.read_union_r. eauto.
          rewrites * (Fmap.indom_single_eq l l0 vs).
  Qed.




  Lemma forward (F : CFML_C.fundef_env) (FT : funtypes_env) (E : env_var) :
    forall (c : CFML_C.config) e te m st (Q : big_pc),
      match_config FT E c (e, te, m, st) ->
      cfml_omnibig_stmt F c Q ->
      omni_exec_stmt ge (e, te, m, st)
        (fun ft => exists fs, Q fs /\ match_final_states FT E e fs ft).
  Proof.
    introv H Hred. gen e te m st.
    induction Hred; introv HR;
      inversion HR as [? ? ? ? ? ? ? ? ? ?
                         Hcomp Htenv Henv
                         Hloc Hmemvals Hmemenv]; subst.
    (* bind rule *)
    - admit.
    (* funcall *)
    - admit.
    (* let x (stack) = val_uninit in t *)
    - cbn in Hcomp. monadInv Hcomp. forwards*: IHHred. constructors *.
    (* let p (heap) = e in t *)
    - cbn in Hcomp. monadInv Hcomp.
      destruct ty; inversion EQ2.

      asserts Htyx0: (Clight.typeof x0 = tr_types (type_ref ty)).
      admit.

      set (Qi1 := (fun '(f', G', s', v', k') =>
                    f' = f
                    /\ k' = k
                    /\ G' = G
                    /\ v' = val_unit
                    /\ (exists l', Qe (val_loc l')
                             /\ s' = Fmap.update s l (val_loc l')))).
      set (Q1 := (fun ft => exists fs, Qi1 fs /\ match_final_states FT E e0 fs ft)).

      forwards *(b&Hmatch&Hie0): Henv.
      forwards *(vt & Heval_e & vs & HQevs & Hmatchvsvt):
        forward_expr E M (f, G, s, e, k) e0 te. constructors*.
      inverts keep Hmatch.
      forwards *(Hldom & Hperm & v & Hload & Hmatchvals): Hmemvals l b.
      forwards *(m2 & Hstore):Memory.Mem.valid_access_store.
      { applys Memory.Mem.valid_access_implies. apply Hperm. constructor. }
      asserts *Hsemcast:(Cop.sem_cast vt (Clight.typeof x0)
                        (Clight.typeof (Clight.Evar i (pointer ty))) m = Some vt).
      { rewrite Htyx0. simpl. eapply Cop.cast_val_casted.
        inverts * Hmatchvsvt.
        applys * Cop.val_casted_ptr_ptr.
      }
      forwards * : (>> omni_exec_Sseq_1 Q1).
      constructors*.
      + constructors*.
      + cbn. eapply Clight.assign_loc_value. reflexivity.
        cbn. eapply Hstore.
      + unfold Q1, Qi1. forwards *(lvs&Hlvs): H3 vs.
        exists (f, G, Fmap.update s l lvs, (), k).
        splits*. splits*. exists lvs; intuition congruence.
        constructors*.
        eapply assign_correct. eauto.
        eauto. apply Hmatch. eapply Hmatchvsvt. congruence.
        cbn. eauto. eauto.
        constructors*.
      + intros. (* destruct (H3 vs HQevs) as (lve & ?); subst. *)
        inversion H6 as (?&?&?). destruct x2 as ((((f'&G')&s')&t')&k').
        unfold Qi1 in H8. destruct H8 as (?&?&?&?&?); subst.
        destruct H15 as (lv'&HQelv'&Hs').
        apply H5 with lv'; eauto.
        inversion H9. subst. constructors*.
        unfold wf_env_and_mem. intros.
        unfold wf_env_and_mem in Hmemenv.
        forwards * : Hmemenv l0 d ty0 H7 H8.
        unfold Fmap.update. applys* Fmap.indom_union_r.



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

  Compute (tr_trm_expr (PTree.empty (var_descr*CFML_C.type))
             (trm_apps val_ptr_add [trm_val (val_loc 3); trm_val (val_int 5)])).
             (* test_trm_expr). *)

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
