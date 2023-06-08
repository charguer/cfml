(** * Compiling CFML_C down to Clight *)

Set Implicit Arguments.

From CFML Require OmnibigMeta.
From CFML Require Import Semantics LibSepFmap CFML_C ClightInterface.
Import LibListNotation.

From compcert Require Coqlib Maps Integers Floats Values AST Ctypes Clight ClightBigstep.
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


  Notation ptr_ofs := Integers.Ptrofs.int.

End cc_types.


Section Compil.


(** CFML to CompCert conversions *)


  Import cc_types.


  Coercion tr_int64 (n : int) : Integers.Int64.int :=
    Integers.Ptrofs.to_int64 (Integers.Ptrofs.repr n).





  Definition tr_binop (op : prim) : res (Cop.binary_operation * Ctypes.type) :=
    match op with
    | val_add ty => OK (Cop.Oadd, tr_types ty)
    | val_ptr_add ty => OK (Cop.Oadd, tr_types ty)
    | val_lt ty => OK (Cop.Olt, tr_types ty)
    | _ => Error (msg "tr_binop: not a binop")
    end.



  Local Open Scope error_monad_scope.

  (* FIXME: not as easy to relate CFML locations and CompCert blocks *)
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

  Definition R_env (G : val_env)
    (c_e : Clight.env) (c_te : Clight.temp_env) : Prop :=
    forall (i : AST.ident), exists v d ty,
      PTree.get i G = Some (v, d, ty) ->
      match d with
      | heap
      | stack =>
          exists (b : Values.block),
          PTree.get i c_e = Some (b, tr_types ty)
          /\ tr_val v = Values.Vptr b Integers.Ptrofs.zero
      | const => PTree.get i c_te = Some (tr_val v)
      end.


  Definition tr_env (G : val_env) : res (Clight.env * Clight.temp_env) :=
    PTree.fold (fun res i '(v, d, ty) =>
                  match res with
                  | OK (e, ge) =>
                      match d with
                      | stack
                      | heap =>
                          match tr_val v with
                          | Values.Vptr b ofs =>
                              OK ((PTree.set i (b, tr_types ty) e), ge)
                          | _ => Error (msg "tr_env: ill defined values")
                          end
                      | const => OK (e, PTree.set i (tr_val v) ge)
                      end
                  | Error msg => Error msg
                  end) G (OK (PTree.empty (Values.block * Ctypes.type), PTree.empty Values.val)).


  (* FIXME *)
  Lemma tr_env_set_stack_or_heap :
    forall (G : val_env) (i : AST.ident) (v : val) (ty : type) (d : var_descr)
      (e : Clight.env) (te : Clight.temp_env) (b : Values.block) ofs,
      (d = stack \/ d = heap) ->
      tr_env G = OK (e, te) ->
      tr_val v = Values.Vptr b ofs ->
      tr_env (PTree.set i (v, d, ty) G) = OK (PTree.set i (b, tr_types ty) e, te).
  Admitted.

  Lemma tr_env_set_const :
    forall (G : val_env) (i : AST.ident) (v : val) (ty : type)
      (e : Clight.env) (te : Clight.temp_env),
      tr_env G = OK (e, te) ->
      tr_env (PTree.set i (v, const, ty) G) = OK (e, PTree.set i (tr_val v) te).
  Admitted.

  Definition compile_init_mem (s : CFML_C.state) : res Memory.mem.
    Admitted.

  Parameter R_mem : CFML_C.state -> Memory.mem -> Prop.

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
        (trm_apps (val_alloc ty') [tn] ) tk =>
        if CFML_C.eq_type_dec ty ty' then
          do i <- get_ident x;
          do en <- auxe tn;
          do stk <- aux tk;
          OK ([| Clight.Sbuiltin (Some i) AST.EF_malloc
                   ([[tr_types ty]])
                   (en :: nil) ;;
                 stk |])
        else Error (msg "tr_trm_stmt: type mismatch in alloc")

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






  Definition compile_config (FT : CFML_C.funtypes_env) (E : env_var)
    (c : CFML_C.config) : res ClightInterface.config :=
    let '(f, G, s, t, k) := c in
    do (e, te) <- tr_env G;
    do m <- compile_init_mem s;
    do stmt <- tr_trm_stmt E FT t;
    OK (e, te, m, stmt).



  Definition tr_program (p : program) : res Clight.program.
  Admitted.

End Compil.




Section Compil_correct.

  Import CFMLSyntax.

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

(*   Inductive match_commands (G : env_var) (F : funtypes_env) : *)
(*     CFML_C.trm -> CFML_C.call_stack -> Clight.statement -> Clight.cont -> Prop := *)
(* (* (t :CFML_C.trm) (cs : CFML_C.call_stack) *) *)
(* (*     (s : Clight.statement) (k : Clight.cont) : Prop := *) *)

(*   | match_commands_top : forall t cs s, *)
(*       cs = Ctop -> *)
(*       tr_trm_stmt G F t = OK s -> *)
(*       match_commands G F t cs s Clight.Kstop *)

(*   | match_commands_seq : forall t s cs s' k' t1 t2, *)
(*       t = <{t1 ; t2}> -> *)
(*       tr_trm_stmt G F t1 = OK s -> *)
(*       match_commands G F t2 cs s' k' -> *)
(*       match_commands G F t cs s (Clight.Kseq s' k') *)

(*   | match_commands_call_assign : forall t cs s x i ty fc e te k' f E cs' t1 t2, *)
(*       cs = Ccall f E cs' -> *)
(*       tr_function f F = OK fc -> *)
(*       R_env E e te -> *)
(*       t = <{let ({(x, Some i)} : ty#const) = t1 in t2}> -> *)
(*       tr_trm_stmt G F t1 = OK s -> *)
(*       match_commands G F t2 cs' Clight.Sskip k' -> *)
(*       match_commands G F t cs s (Clight.Kcall (Some i) fc e te k') *)

(*   | match_commands_call_anon : forall t cs s fc e te k' f E cs' t1 t2, *)
(*       cs = Ccall f E cs' -> *)
(*       tr_function f F = OK fc -> *)
(*       R_env E e te -> *)
(*       t = trm_let binding_anon t1 t2 -> *)
(*       tr_trm_stmt G F t1 = OK s -> *)
(*       match_commands G F t2 cs' Clight.Sskip k' -> *)
(*       match_commands G F t cs s (Clight.Kcall None fc e te k'). *)


  Definition config_final (c : CFML_C.config) : Prop :=
    let '(f, G, s, t, k) := c in
    k = Ctop /\ exists v, t = trm_val v.

  Import cc_types.

  (* WIP *)
  Variant match_values : CFML_C.val -> Values.val -> Prop :=
    | match_values_int : forall (n : int),
        match_values (val_int n) (Values.Vlong n).

  (* Variant match_env : CFML_C.val_env -> Clight.env -> Clight.temp_env -> Prop := *)
  (*   | match_env_intro : forall G e te (f : loc -> Values.block), *)
  (*       (forall i v ty, *)
  (*           PTree.get i G = Some (v, const, ty) -> *)
  (*           (exists vt, PTree.get i te = Some vt /\ match_values v vt) *)
  (*       ) -> *)
  (*       (forall i l ty d, *)
  (*           d = stack \/ d = heap -> *)
  (*           PTree.get i G = Some (val_loc l, d, ty) -> *)
  (*           (exists b, f l = b /\ PTree.get i e = Some (b, tr_types ty)) *)
  (*       ) -> *)
  (*       match_env G e te. *)

  Coercion Integers.Ptrofs.intval : Integers.Ptrofs.int >-> Z.

  (* Variant match_memories (s : CFML_C.state) (m : Memory.mem) : Prop := *)
  (*   | match_memories_intro : *)
  (*     forall (ll : list (loc * nat)) *)
  (*       (lb : list (Values.block * ptr_ofs * ptr_ofs)) *)
  (*       (f : loc * nat -> Values.block * ptr_ofs * ptr_ofs), *)

  (*       List.map f ll = lb -> *)

  (*       (forall l, (exists n, List.In (l, n) ll) <-> Fmap.indom s l) -> *)

  (*       (forall l n b ofsl ofsh, List.In (l, n) ll -> *)
  (*                           f (l, n) = (b, ofsl, ofsh) -> *)
  (*                           n = ofsh - ofsl :> int) -> *)

  (*       (forall l n n' l' b ofsl ofsh vt, List.In (l, n) ll -> *)
  (*                 n' < n -> *)
  (*                 (l' : nat) = (l : nat) + n' :> int -> *)
  (*                 f (l, n) = (b, ofsl, ofsh) -> *)
  (*                 Fmap.indom s l' *)
  (*                 /\ (exists chunk, Memory.Mem.load chunk m b (ofsl + n') = Some vt) *)
  (*                 /\ match_values (Fmap.read s l') vt) -> *)
  (*       match_memories s m. *)

  Variant match_config_expr (E : env_var) :
    CFML_C.config ->
   (PTree.tree (Values.block * Ctypes.type) * PTree.tree Values.val * Memory.Mem.mem *
   Clight.expr) -> Prop :=
    | match_config_expr_intro : forall f' G s t k e te m a,


      forall (ll : list (loc * positive * CFML_C.type))
        (lb : list (Values.block * ptr_ofs))
        (f : loc -> Values.block * ptr_ofs),

        tr_trm_expr E t = OK a ->

        (* match_env G e te -> *)
        (forall i v ty,
            PTree.get i G = Some (v, const, ty) ->
            (exists vt, PTree.get i te = Some vt /\ match_values v vt)
        ) ->
        (forall i l ty d,
            d = stack \/ d = heap ->
            PTree.get i G = Some (val_loc l, d, ty) ->
            (exists b n ofsl, List.In (l, n, ty) ll
                              /\ f l = (b, ofsl)
                              /\ PTree.get i e = Some (b, tr_types ty))
        ) ->

        (* match_memories s m -> *)
        List.map (fun '(l, n, ty) => f l) ll = lb ->

        (* (forall l, (exists n, List.In (l, n) ll) <-> Fmap.indom s l) -> *)

        (* (forall l n b ofsl ofsh, List.In (l, n) ll -> *)
        (*                     f (l, n) = (b, ofsl, ofsh) -> *)
        (*                     Pos.to_nat n = ofsh - ofsl + 1 :> int) -> *)

        (forall l n (n' : nat) (l' : loc) b ofsl vt ty, List.In (l, n, ty) ll ->
                  (n' < Pos.to_nat n)%nat ->
                  (l' : nat) = (l : nat) + n' :> int ->
                  f l = (b, ofsl) ->
                  let chunk := (AST.chunk_of_type (Ctypes.typ_of_type ty)) in
                  Fmap.indom s l'
                  /\ Memory.Mem.valid_access m chunk b (ofsl+n') Memtype.Writable
                  /\ (Memory.Mem.load chunk m b (ofsl + n') = Some vt)
                  /\ match_values (Fmap.read s l') vt) ->

        (* env and memory ok *)

        (forall l d ty, (exists i, PTree.get i G = Some (val_loc l, d, ty)) ->
                        d = heap \/ d = stack ->
                        Fmap.indom s l) ->

        match_config_expr E (f', G, s, t, k) (e, te, m, a).

  Variant match_config (FT : CFML_C.funtypes_env) (E : env_var) :
    CFML_C.config -> ClightInterface.config -> Prop :=
    | match_config_intro : forall f' G s t k e te m st,

      forall (ll : list (loc * positive * CFML_C.type))
        (lb : list (Values.block * ptr_ofs))
        (f : loc -> Values.block * ptr_ofs),

        tr_trm_stmt E FT t = OK st ->

        (* match_env G e te -> *)
        (forall i v ty,
            PTree.get i G = Some (v, const, ty) ->
            (exists vt, PTree.get i te = Some vt /\ match_values v vt)
        ) ->
        (forall i l ty d,
            d = stack \/ d = heap ->
            PTree.get i G = Some (val_loc l, d, ty) ->
            (exists b n ofs, List.In (l, n, ty) ll
                      /\ f l = (b, ofs)
                      /\ e ! i = Some (b, tr_types ty))
        ) ->

        (* match_memories s m -> *)
        List.map (fun '(l, n, ty) => f l) ll = lb ->

        (* (forall l, (exists n, List.In (l, n) ll) <-> Fmap.indom s l) -> *)

        (* (forall l n b ofsl ofsh, List.In (l, n) ll -> *)
        (*                     f (l, ty) = (b, ofsl, ofsh) -> *)
        (*                     Pos.to_nat n = ofsh - ofsl + 1 :> int) -> *)

        (forall l n (n' : nat) ty (l' : loc) b ofsl vt, List.In (l, n, ty) ll ->
                  (n' < Pos.to_nat n)%nat ->
                  (l' : nat) = (l : nat) + n' :> int ->
                  f l = (b, ofsl) ->
                  let chunk := (AST.chunk_of_type (Ctypes.typ_of_type ty)) in
                  Fmap.indom s l'
                  /\ Memory.Mem.valid_access m chunk b (ofsl+n') Memtype.Writable
                  /\ Memory.Mem.load chunk
                      m b (ofsl + n') = Some vt
                  /\ match_values (Fmap.read s l') vt) ->

        (* env and memory ok *)

        (forall l d ty, (exists i, PTree.get i G = Some (val_loc l, d, ty)) ->
                        d = heap \/ d = stack ->
                        Fmap.indom s l) ->

        match_config FT E (f', G, s, t, k) (e, te, m, st).

  Variant match_outs : CFML_C.val -> ClightBigstep.outcome -> Prop :=
    | match_outs_normal :
      match_outs val_unit ClightBigstep.Out_normal
    | match_outs_ret_none :
      match_outs val_unit (ClightBigstep.Out_return None)
    | match_outs_ret_val : forall vs ty vt,
        match_values vs vt ->
        match_outs vs (ClightBigstep.Out_return (Some (vt, ty))).

  Definition match_final_env (G : CFML_C.val_env) (te : Clight.temp_env) : Prop :=
    forall (i : AST.ident), exists (vs : val) (ty : type) (vt : Values.val),
      (G ! i = Some (vs, const, ty) <-> te ! i = Some vt)
      /\ match_values vs vt.



  Variant match_final_states (FT : CFML_C.funtypes_env) (E : env_var) :
    CFML_C.final_config -> ClightInterface.final_config -> Prop :=
    | match_final_states_intro : forall f' G s v k te m out,

      forall (ll : list (loc * positive * CFML_C.type))
        (lb : list (Values.block * ptr_ofs))
        (f : loc -> Values.block * ptr_ofs),

        (* match_final_env G te *)

        (forall (i : AST.ident) (vs : val) (ty : type) (vt : Values.val),
            G ! i = Some (vs, const, ty) ->
            match_values vs vt ->
            te ! i = Some vt) ->

        (* /\ match_memories s m *)

        List.map (fun '(l, n, ty) => f l) ll = lb ->
        (* (forall l, (exists n, List.In (l, n) ll) <-> Fmap.indom s l) -> *)

        (* (forall l n b ofsl ofsh, List.In (l, n) ll -> *)
        (*                     f (l, n) = (b, ofsl, ofsh) -> *)
        (*                     Pos.to_nat n = ofsh - ofsl + 1 :> int) -> *)

        (forall l n (n' : nat) ty (l' : loc) b ofsl vt, List.In (l, n, ty) ll ->
                  (n' < Pos.to_nat n)%nat ->
                  (l' : nat) = (l : nat) + n' :> int ->
                  f l = (b, ofsl) ->
                  let chunk := (AST.chunk_of_type (Ctypes.typ_of_type ty)) in
                  Fmap.indom s l'
                  /\ Memory.Mem.valid_access m chunk b (ofsl+n') Memtype.Writable
                  /\ Memory.Mem.load chunk
                      m b (ofsl + n') = Some vt
                  /\ match_values (Fmap.read s l') vt) ->

        match_outs v out ->
        match_final_states FT E (f', G, s, v, k) (te, m, out).


  Import CFML_C OmnibigMeta ClightInterface.

  Lemma forward_expr (E : env_var) (ge : Clight.genv) :
    forall '(f, G, s, te, k) env le m a Q,
      match_config_expr E (f, G, s, te, k) (env, le, m, a) ->
      cfml_omnibig_expr G s te Q ->
      exists v, Clight.eval_expr ge env le m a v.
  Proof.
  Admitted.


  Lemma forward (F : CFML_C.fundef_env) (FT : funtypes_env) (E : env_var) (ge : Clight.genv) : forall (c : CFML_C.config) (cc : ClightInterface.config) (Q : big_pc),
      match_config FT E c cc ->
      cfml_omnibig_stmt F c Q ->
      omni_exec_stmt ge cc (fun ft => exists fs, Q fs /\ match_final_states FT E fs ft).
  Proof.
    introv H Hred. generalize dependent cc.
    induction Hred; introv HR; inversion HR as [? ? ? ? ? ? ? ? ? ? ? fmem
                                                  Hcomp Htenv Henv
                                                  Hfmem Hmemvals Hmemenv]; subst.
    (* bind rule *)
    - admit.
    (* funcall *)
    - admit.
    (* let x (stack) = val_uninit in t *)
    - cbn in Hcomp. monadInv Hcomp. forwards*: IHHred. constructors *.
    (* let p (heap) = e in t *)
    - cbn in Hcomp. destruct e; try solve [inversion Hcomp].
      + destruct v; try solve [inversion Hcomp].
        inversion H2. forwards *: evalctx_expr_not_val C t0 (val_int z).
        forwards *: H3 (val_int z) H5. destruct H7 as (l'&[=]&_).
      + rename v into x'. monadInv Hcomp. destruct ty; inversion EQ2.
        set (Q1 := (fun fc => ClightInterface.exec_stmt'
                             ge (e0, te, m,
                               (Clight.Sassign (Clight.Evar i (pointer ty)) x0))
                             fc)).
        (* set (Q1 := (fun '(le', m', out) => *)
        (*              let a1 := Clight.Evar i (pointer ty) in *)
        (*              let a2 := x0 in *)
        (*              forall loc ofs bf v0 v2, *)
        (*                Clight.eval_lvalue ge e0 te m a1 loc ofs bf -> *)
        (*                Clight.eval_expr ge e0 te m a2 v2 -> *)
        (*                Cop.sem_cast v2 (Clight.typeof a2) (Clight.typeof a1) m = Some v0 -> *)
        (*                Clight.assign_loc (Clight.genv_cenv ge) (Clight.typeof a1) m loc ofs bf v0 m' *)
        (*                /\ le' = te *)
        (*                /\ out = ClightBigstep.Out_normal *)
        (*           )). *)
        applys * (>> omni_exec_Sseq_1 Q1).
        * forwards *Hi_in_e: Henv i l (type_ref ty) heap H.
          destruct (Hi_in_e) as (b & n & ofsl & ofsh & Hi_fmem & Hi).
          forwards *Htr_expr: forward_expr E ge (f, G, s, trm_var x', k) e0 te.
          { constructors *.  } destruct Htr_expr as (v & Hevalx0).
          constructors *.
          ** constructor. eapply Hi. (* lvalue *)
          ** admit.              (* sem_cast *)
          ** cbn.                (* assign_loc *)
             (* apply Hmemdom in H0. destruct H0 as [n Hln]. *)
             forwards *: Hmemvals. eapply Pos2Nat.is_pos.
             apply Zplus_0_r_reverse. destruct H4 as (_ & Hperm & Hload & Hmatch).
             eapply Clight.assign_loc_value. reflexivity.
             cbn. forwards *: Memory.Mem.valid_access_store Hperm.
          ** cbn. auto. constructors *. constructor. eapply Hi.



  (* Lemma forward (F : CFML_C.fundef_env) (FT : funtypes_env) (E : env_var) (ge : Clight.genv) : forall (c : CFML_C.config) (cc : ClightInterface.config) (Q : big_pc), *)
  (*     compile_config FT E c = OK cc -> *)
  (*     cfml_omnibig_stmt F c Q -> *)
  (*     ClightInterface.terminates ge cc *)
  (*     /\ (forall fc, ClightInterface.exec_stmt' ge cc fc -> *)
  (*              lift_R (match_final_states FT E) Q fc). *)
  (* Proof. *)
  (*   introv Hcomp Hred. generalize dependent cc. *)
  (*   induction Hred; introv Hcomp. *)
  (*   - admit.                    (* MDR les contextes on verra plus tard *) *)
  (*   - admit.                    (* idem pour les apps *) *)
  (*   - forwards*: IHHred. simpl in Hcomp. simpl. *)
  (*     monadInv Hcomp. monadInv EQ0. rewrite EQ, EQ1, EQ2. auto. *)
  (*   - destruct d; simpl in Hcomp. *)
  (*     + destruct v; try contradiction; cbn in *; monadInv Hcomp. *)
  (*       monadInv EQ0. *)
  (*       rewrites * (>> tr_env_set_stack_or_heap x0 x1) in IHHred. *)




  (*       set (cc' := (do (e, te) <- tr_env (PTree.set i (val_int z, stack, ty) G); *)
  (*                    do m <- compile_init_mem s; do stmt <- tr_trm_stmt E FT t; OK (e, te, m, stmt))%error_scope). *)
  (*       rewrite (tr_env_set_stack_or_heap G i) in cc'. *)
  (*       rewrite EQ1 in cc'. EQ2 in cc'. *)
  (*       forwards*: IHHred cc'.  *)

  (** ** Correctness of statement translation *)
  (* Definition stmt_pc_final (P : CFML_C.stmt_pc) : Prop := *)
  (*   forall c, P c -> config_final c. *)


  (* Lemma tr_stmt_correct : forall (c : CFML_C.config) (P : CFML_C.stmt_pc) (E : env_var) *)
  (*                           (F : fundef_env) (FT : PTree.t (list type * type)) *)
  (*                           (ge : Clight.genv) (st : Clight.state), *)
  (*     R FT E c st -> *)
  (*     cfml_omnistep F c P -> *)
  (*     Clight_omni.eventually' ge st *)
  (*       (fun st' => exists c', P c' /\ R FT E c' st'). *)
  (* Proof. *)
  (*   introv HR Hred. unfold config in *. generalize dependent c. *)
  (*   destruct c as [f G s t cs]. *)


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
