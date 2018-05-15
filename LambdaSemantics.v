(**

This file describes the syntax and semantics of a lambda calculus
with mutable heap. The language includes recursive functions, and a
couple of primitive functions. Records and arrays operations are
encoded using pointer arithmetics, and using the [alloc] operation
which allocates at once a requested number of consecutive memory cells.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From TLC Require Export LibString LibList LibCore.
From Sep Require Export Fmap TLCbuffer.
Open Scope string_scope.


(* ********************************************************************** *)
(* * Source language syntax *)

(* ---------------------------------------------------------------------- *)
(** Representation of variables *)

Definition var := string.

Inductive bind : Type :=
  | bind_anon : bind
  | bind_var : var -> bind.

Definition eq_var_dec := String.string_dec.

Definition var_eq (s1:var) (s2:var) : bool :=
  if eq_var_dec s1 s2 then true else false.

Lemma var_eq_spec : forall s1 s2,
  var_eq s1 s2 = isTrue (s1 = s2).
Proof using.
  intros. unfold var_eq. case_if; rew_bool_eq~.
Qed.

Global Opaque var.


(* ---------------------------------------------------------------------- *)
(** Representation of locations and fields *)

Definition loc := nat.

Definition null : loc := 0%nat.

Definition field := nat.

Global Opaque field loc.


(* ---------------------------------------------------------------------- *)
(** Syntax of the source language *)

Inductive prim : Type :=
  | val_ref : prim
  | val_get : prim
  | val_set : prim
  | val_alloc : prim
  | val_eq : prim
  | val_sub : prim
  | val_add : prim
  | val_ptr_add : prim.

Inductive val : Type :=
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_prim : prim -> val
  | val_fix : bind -> bind -> trm -> val

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fix : bind -> bind -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm
  | trm_let : bind -> trm -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_while : trm -> trm -> trm
  | trm_for : var -> trm -> trm -> trm -> trm.

(** The type of values is inhabited *)

Global Instance Inhab_val : Inhab val.
Proof using. apply (Inhab_of_val val_unit). Qed.

(** Encoded constructs *)

Notation "'trm_seq' t1 t2" := (trm_let bind_anon t1 t2)
  (at level 69, t1 at level 0, t2 at level 0).

Notation "'trm_fun' x t1" := (trm_fix bind_anon x t1)
  (at level 69, x at level 0, t1 at level 0).

Notation "'val_fun' x t1" := (val_fix bind_anon x t1)
  (at level 69, x at level 0, t1 at level 0).


(* ---------------------------------------------------------------------- *)
(** Coercions *)

Coercion val_prim : prim >-> val.
Coercion val_bool : bool >-> val.
Coercion val_int : Z >-> val.
Coercion val_loc : loc >-> val.
Coercion trm_val : val >-> trm.
Coercion trm_var : var >-> trm.
Coercion trm_app : trm >-> Funclass.
Coercion bind_var : var >-> bind.


(* ********************************************************************** *)
(* * Source language semantics *)

(* ---------------------------------------------------------------------- *)
(** Definition of contexts *)

(** [ctx] describes a list of bindings *)

Definition ctx : Type :=
  list (var * val).

(** [ctx_empty] describes the empty context *)

Definition ctx_empty : ctx :=
  nil.

(** [ctx_add z v E] is defined as:
    - [E] if [z] is the anonymous binder
    - [E] extended with the pair [(x,v)] if [z] is a variable [x]. *)

Definition ctx_add (z:bind) (v:val) (E:ctx) : ctx :=
  match z with
  | bind_anon => E
  | bind_var x => (x,v)::E
  end.

(** [ctx_one z v] is a shorthand for [ctx_add z v ctx_empty] *)

Definition ctx_one (z:bind) (v:val) : ctx :=
  ctx_add z v ctx_empty.

(** [ctx_two z1 v1 z2 v2] is a shorthand for
    [ctx_add z1 v1 (ctx_add z2 v2 ctx_empty)]. *)

Definition ctx_two (z1:bind) (v1:val) (z2:bind) (v2:val) : ctx :=
  ctx_add z1 v1 (ctx_add z2 v2 ctx_empty).

(** [ctx_rem x E] removes all bindings on [x] stored in [E] *)

Fixpoint ctx_rem_var (x:var) (E:ctx) : ctx :=
  match E with
  | nil => nil
  | (y,v)::E' =>
      let E'' := ctx_rem_var x E' in
      if var_eq x y then E'' else (y,v)::E''
  end.

Fixpoint ctx_rem (z:bind) (E:ctx) : ctx :=
  match z with
  | bind_anon => E
  | bind_var x => ctx_rem_var x E
  end.

(** [ctx_lookup x E] returns
    - [None] if [x] is not bound in [E]
    - [Some v] if [x] is bound to [v] in [E]. *)

Fixpoint ctx_lookup (x:var) (E:ctx) : option val :=
  match E with
  | nil => None
  | (y,v)::E' => if var_eq x y
                   then Some v
                   else ctx_lookup x E'
  end.

(** [ctx_fresh x E] asserts that [x] is not bound in [E] *)

Definition ctx_fresh (x:var) (E:ctx) : Prop :=
  ctx_lookup x E = None.


(* ---------------------------------------------------------------------- *)
(** Definition of capture-avoiding substitution *)

(** [subst E t] substitutes all the bindings from [E] inside [t] *)

Fixpoint subst (E:ctx) (t:trm) : trm :=
  let aux := subst E in
  match t with
  | trm_val v => trm_val v
  | trm_var x => match ctx_lookup x E with
                 | None => t
                 | Some v => v
                 end
  | trm_fix f z t1 => trm_fix f z (subst (ctx_rem z (ctx_rem f E)) t1)
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  | trm_let z t1 t2 => trm_let z (aux t1) (subst (ctx_rem z E) t2)
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_while t1 t2 => trm_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 => trm_for x (aux t1) (aux t2) (subst (ctx_rem x E) t3)
  end.

(** [subst1 z v t] replaces occurences of binder [z] with [v] in [t]. *)

Definition subst1 (z:bind) (v:val) (t:trm) :=
  subst (ctx_one z v) t.

Definition subst2 (z1:bind) (v1:val) (z2:bind) (v2:val) (t:trm) :=
  subst (ctx_two z1 v1 z2 v2) t.


(* ---------------------------------------------------------------------- *)
(** Big-step evaluation *)

Implicit Types t : trm.
Implicit Types v : val.
Implicit Types l : loc.
Implicit Types i : field.
Implicit Types b : bool.
Implicit Types n : int.
Implicit Types x : var.
Implicit Types z : bind.

Definition state := fmap loc val.

Section Red.

Local Open Scope fmap_scope.

Inductive red : state -> trm -> state -> val -> Prop :=
  (* Core constructs *)
  | red_val : forall m v,
      red m v m v
  | red_fix : forall m f x t1,
      red m (trm_fix f x t1) m (val_fix f x t1)
  | red_if : forall m1 m2 m3 b r t0 t1 t2,
      red m1 t0 m2 (val_bool b) ->
      red m2 (if b then t1 else t2) m3 r ->
      red m1 (trm_if t0 t1 t2) m3 r
  | red_let : forall m1 m2 m3 z t1 t2 v1 r,
      red m1 t1 m2 v1 ->
      red m2 (subst1 z v1 t2) m3 r ->
      red m1 (trm_let z t1 t2) m3 r
  | red_app : forall m1 m2 m3 m4 t1 t2 f z t3 v1 v2 r,
      red m1 t1 m2 v1 ->
      red m2 t2 m3 v2 ->
      v1 = val_fix f z t3 ->
      red m3 (subst2 f v1 z v2 t3) m4 r ->
      red m1 (trm_app t1 t2) m4 r
  | red_while : forall m1 m2 t1 t2 r,
      red m1 (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) m2 r ->
      red m1 (trm_while t1 t2) m2 r
  | red_for_arg : forall m1 m2 m3 m4 v1 v2 x t1 t2 t3 r,
      (* LATER: add [not_is_val t1 \/ not_is_val t2] *)
      red m1 t1 m2 v1 ->
      red m2 t2 m3 v2 ->
      red m3 (trm_for x v1 v2 t3) m4 r ->
      red m1 (trm_for x t1 t2 t3) m4 r
  | red_for : forall m1 m2 (x:var) n1 n2 t3 r,
      red m1 (
        If (n1 <= n2)
          then (trm_seq (subst1 x n1 t3) (trm_for x (n1+1) n2 t3))
          else val_unit) m2 r ->
      red m1 (trm_for x n1 n2 t3) m2 r

  (* Primitive operations on the heap *)
  | red_ref : forall ma mb v l,
      mb = (fmap_single l v) ->
      l <> null ->
      \# ma mb ->
      red ma (val_ref v) (mb \+ ma) (val_loc l)
  | red_get : forall m l v,
      fmap_data m l = Some v ->
      red m (val_get (val_loc l)) m v
  | red_set : forall m m' l v,
      m' = fmap_update m l v ->
      red m (val_set (val_loc l) v) m' val_unit
  | red_alloc : forall k n ma mb l,
      mb = fmap_conseq l k val_unit ->
      n = nat_to_Z k ->
      l <> null ->
      \# ma mb ->
      red ma (val_alloc (val_int n)) (mb \+ ma) (val_loc l)
  (* Other primitive operations *)
  | red_add : forall m n1 n2 n',
      n' = n1 + n2 ->
      red m (val_add (val_int n1) (val_int n2)) m (val_int n')
  | red_sub : forall m n1 n2 n',
      n' = n1 - n2 ->
      red m (val_sub (val_int n1) (val_int n2)) m (val_int n')
  | red_ptr_add : forall l' m l n,
      (l':nat) = (l:nat) + n :> int ->
      red m (val_ptr_add (val_loc l) (val_int n)) m (val_loc l')
  | red_eq : forall m v1 v2,
      red m (val_eq v1 v2) m (val_bool (isTrue (v1 = v2))).

  (* Remark: alternative for red_for rules.
    | red_for : forall m1 m2 m3 m4 v1 v2 x t1 t2 t3 r,
        red m1 (
          (trm_seq (trm_let x n1 t3) (trm_for x (n1+1) n2 t3))
          val_unit) m2 r ->
        red m1 (trm_for x n1 n2 t3) m2 r

  Definition trm_is_val (t:trm) : Prop :=
  match t with
  | trm_val v => True
  | _ => False
  end.

  *)

End Red.


(* ---------------------------------------------------------------------- *)
(** Reintroduce contexts *)

Lemma nil_eq_ctx_empty : 
  @nil (prod var val) = ctx_empty.
Proof using. auto. Qed.

Lemma cons_eq_ctx_add : forall x v (E:ctx),
  (x,v)::E = ctx_add x v E.
Proof using. auto. Qed.

Hint Rewrite nil_eq_ctx_empty cons_eq_ctx_add : rew_ctx.

Tactic Notation "rew_ctx" := 
  autorewrite with rew_ctx.
Tactic Notation "rew_ctx" "in" hyp(H) := 
  autorewrite with rew_ctx in H.
Tactic Notation "rew_ctx" "in" "*" := 
  autorewrite with rew_ctx in *.


(* ---------------------------------------------------------------------- *)
(** Properties of operations on contexts  *)

Lemma ctx_fresh_inv : forall (x1 x2:var) v E,
  ctx_fresh x1 (ctx_add x2 v E) ->
  x1 <> x2 /\ ctx_fresh x1 E.
Proof using. 
  introv M. unfolds ctx_fresh. simpls.
  rewrite var_eq_spec in *. case_if~.
Qed.

(** [ctx_rem x ctx_empty] *)

Lemma ctx_rem_empty : forall z,
  ctx_rem z ctx_empty = ctx_empty.
Proof using. intros. destruct z as [|x]; auto. Qed.

(** Result of removing a variable from a context. *)
(* -- TODO: rename and check useful *)

Lemma ctx_rem_add_same : forall z v E,
  ctx_rem z (ctx_add z v E) = ctx_rem z E.
Proof using.
  intros. destruct z as [|x].
  { auto. }
  { simpl. rewrite var_eq_spec. case_if~. }
Qed.

Lemma ctx_rem_add_neq : forall z1 z2 v E,
  z1 <> z2 ->
  ctx_rem z1 (ctx_add z2 v E) = ctx_add z2 v (ctx_rem z1 E).
Proof using.
  intros. destruct z2 as [|x2]. 
  { auto. }
  { destruct z1 as [|x1]. 
    { auto. }
    { simpl. rewrite var_eq_spec. case_if~. } }
Qed.

(** Removing a variable that does not occur in a context changes nothing. *)

Lemma ctx_rem_fresh : forall x E,
  ctx_fresh x E ->
  ctx_rem x E = E.
Proof using.
  introv M. unfold ctx_rem. induction E as [|(y,v) E'].
  { auto. }
  { simpls. lets (N1&N2): ctx_fresh_inv (rm M).
    rewrite var_eq_spec in *. case_if. rewrite~ IHE'. }
Qed.

(** [subst] with [ctx_empty] changes nothing. *)

Lemma subst_ctx_empty : forall t,
  subst ctx_empty t = t.
Proof using.
  intros. induction t; simpl; 
   try solve [ repeat rewrite ctx_rem_empty; fequals* ].
Qed.

(** [subst1 z v t] when [z] is anonymous returns [t] unchanged. *)

Lemma subst1_anon : forall v t,
  subst1 bind_anon v t = t.
Proof using.
  intros. unfold subst1, ctx_one, ctx_add. rewrite~ subst_ctx_empty.
Qed.

Lemma ctx_rem_rem_neq : forall z1 z2 E,
  ctx_rem z1 (ctx_rem z2 E) = ctx_rem z2 (ctx_rem z1 E).
Proof using. (*

  introv M. unfold ctx_rem. induction E as [|(y,v) E'].
  { auto. }
  { simpls. lets (N1&N2): ctx_fresh_inv (rm M).
    rewrite var_eq_spec in *. case_if. rewrite~ IHE'. }
*) admit.
Qed.

(** [subst] can be combuted  by iteratively substituting its bindings. *)

Lemma subst_ctx_add : forall z v E t,
  subst (ctx_add z v E) t = subst E (subst1 z v t).
Proof using.
  intros. destruct z as [|x].
  { simpl. rewrite~ subst1_anon. }
  { unfold subst1. simpl. rew_ctx. gen E. 
    induction t; intros; simpl; try solve [ fequals* ].
    { rewrite var_eq_spec. case_if~. }
    { rew_ctx. fequals. tests: (b = x).
      { repeat rewrite ctx_rem_add_same. fequals.
        rewrite ctx_rem_empty, subst_ctx_empty. auto. }
      { rewrite~ ctx_rem_add_neq. tests: (b0 = x).
        { rewrite ctx_rem_add_same. fequals.
          rewrite ctx_rem_rem_neq. rewrite ctx_rem_add_same.
          rewrite ctx_rem_empty, subst_ctx_empty. auto. }
        { do 3 rewrite~ ctx_rem_add_neq. do 2 rewrite ctx_rem_empty.
          rewrite~ IHt. } } }
  { rew_ctx. fequals. tests: (b = x).
    { do 2 rewrite ctx_rem_add_same. fequals. rewrite~ subst_ctx_empty. }
    { do 2 (rewrite~ ctx_rem_add_neq). rewrite ctx_rem_empty. rewrite~ IHt2. } }
  { skip. (* todo *) } }
Qed.

Lemma subst1_subst_ctx_rem_same : forall E x v t,
    subst1 x v (subst (ctx_rem x E) t)
  = subst E (subst1 x v t).
Proof using.
  intros. rewrite <- subst_ctx_add.
(* 
  intros E. induction E as [|(y,w) E']; simpl; intros.
  { auto. }
  { rewrite var_eq_spec. case_if.
    { subst. rewrite IHE'. rewrite~ subst_subst_same. }
    { simpl. rewrite IHE'. rewrite~ subst_subst_neq. } }
Qed.
*)
Admitted.

Lemma subst1_subst : forall x v E t,
  ctx_fresh x E ->
  subst1 x v (subst E t) = subst E (subst1 x v t).
Proof using.
  introv M. rewrite <- (@subst1_subst_ctx_rem_same E x v t).
  fequals. rewrite~ ctx_rem_fresh.
Qed.


(*

  (** Substituting for [E] without [x] then substituting for [x]
      is equivalent to substituting for [x] then for [E]
      (even if [x] is bound in [E]). *)


  (** Substitutions for two distinct variables commute. *)

  Lemma subst1_subst1_neq : forall x1 x2 v1 v2 t,
    x1 <> x2 ->
    subst1 x2 v2 (subst1 x1 v1 t) = subst1 x1 v1 (subst1 x2 v2 t).
  Proof using.
    introv N. induction t; simpl; try solve [ fequals;
    repeat case_if; simpl; repeat case_if; auto ].
    repeat case_if; simpl; repeat case_if~.
    { false. destruct v; destruct x1; destruct x2; false. simpls.
      rewrite name_eq_spec in *. rew_bool_eq in *. false. }
  Qed. (* LATER: simplify *)

  (** Substituting for a variable that has just been substituted
      does not further modify the term. *)

  Lemma subst_subst_same : forall x v1 v2 t,
    subst1 x v2 (subst1 x v1 t) = subst1 x v1 t.
  Proof using.
    intros. induction t; simpl; try solve [ fequals;
    repeat case_if; simpl; repeat case_if; auto ].
  Qed.
*)

(* ---------------------------------------------------------------------- *)
(* ** Derived rules *)

Lemma red_fun : forall m x t1,
  red m (trm_fun x t1) m (val_fun x t1).
Proof using. intros. apply red_fix. Qed.

Lemma red_seq : forall m1 m2 m3 t1 t2 r1 r,
  red m1 t1 m2 r1 ->
  red m2 t2 m3 r ->
  red m1 (trm_seq t1 t2) m3 r.
Proof using. introv M1 M2. applys* red_let. rewrite* subst1_anon. Qed.

Lemma red_ptr_add_nat : forall m l (f : nat),
  red m (val_ptr_add (val_loc l) (val_int f)) m (val_loc (l+f)%nat).
Proof using. intros. applys* red_ptr_add. math. Qed.

Lemma red_if_bool : forall m1 m2 b r t1 t2,
  red m1 (if b then t1 else t2) m2 r ->
  red m1 (trm_if b t1 t2) m2 r.
Proof using. introv M1. applys* red_if. applys red_val. Qed.

Lemma red_for_le : forall m1 m2 m3 x n1 n2 t3 r,
  n1 <= n2 ->
  red m1 (subst1 x n1 t3) m2 val_unit ->
  red m2 (trm_for x (n1+1) n2 t3) m3 r ->
  red m1 (trm_for x n1 n2 t3) m3 r.
Proof using.
  introv N M1 M2. applys red_for. case_if.
  { applys red_seq. applys M1. applys M2. }
  { false; math. }
Qed.

Lemma red_for_gt : forall m x n1 n2 t3,
  n1 > n2 ->
  red m (trm_for x n1 n2 t3) m val_unit.
Proof using.
  introv N. applys red_for. case_if.
  { false; math. }
  { applys red_val. }
Qed.




(* ********************************************************************** *)
(* * Notation for terms *)

(* ---------------------------------------------------------------------- *)
(** Notation for program variables *)

Notation "''a'" := ("a":var) : var_scope.
Notation "''b'" := ("b":var) : var_scope.
Notation "''c'" := ("c":var) : var_scope.
Notation "''d'" := ("d":var) : var_scope.
Notation "''e'" := ("e":var) : var_scope.
Notation "''f'" := ("f":var) : var_scope.
Notation "''g'" := ("g":var) : var_scope.
Notation "''h'" := ("h":var) : var_scope.
Notation "''i'" := ("i":var) : var_scope.
Notation "''j'" := ("j":var) : var_scope.
Notation "''k'" := ("k":var) : var_scope.
Notation "''l'" := ("l":var) : var_scope.
Notation "''m'" := ("m":var) : var_scope.
Notation "''n'" := ("n":var) : var_scope.
Notation "''o'" := ("o":var) : var_scope.
Notation "''p'" := ("p":var) : var_scope.
Notation "''q'" := ("q":var) : var_scope.
Notation "''r'" := ("r":var) : var_scope.
Notation "''s'" := ("s":var) : var_scope.
Notation "''t'" := ("t":var) : var_scope.
Notation "''u'" := ("u":var) : var_scope.
Notation "''v'" := ("v":var) : var_scope.
Notation "''w'" := ("w":var) : var_scope.
Notation "''x'" := ("x":var) : var_scope.
Notation "''y'" := ("y":var) : var_scope.
Notation "''z'" := ("z":var) : var_scope.

Notation "''a1'" := ("a1":var) : var_scope.
Notation "''b1'" := ("b1":var) : var_scope.
Notation "''c1'" := ("c1":var) : var_scope.
Notation "''d1'" := ("d1":var) : var_scope.
Notation "''e1'" := ("e1":var) : var_scope.
Notation "''f1'" := ("f1":var) : var_scope.
Notation "''g1'" := ("g1":var) : var_scope.
Notation "''h1'" := ("h1":var) : var_scope.
Notation "''i1'" := ("i1":var) : var_scope.
Notation "''j1'" := ("j1":var) : var_scope.
Notation "''k1'" := ("k1":var) : var_scope.
Notation "''l1'" := ("l1":var) : var_scope.
Notation "''m1'" := ("m1":var) : var_scope.
Notation "''n1'" := ("n1":var) : var_scope.
Notation "''o1'" := ("o1":var) : var_scope.
Notation "''p1'" := ("p1":var) : var_scope.
Notation "''q1'" := ("q1":var) : var_scope.
Notation "''r1'" := ("r1":var) : var_scope.
Notation "''s1'" := ("s1":var) : var_scope.
Notation "''t1'" := ("t1":var) : var_scope.
Notation "''u1'" := ("u1":var) : var_scope.
Notation "''v1'" := ("v1":var) : var_scope.
Notation "''w1'" := ("w1":var) : var_scope.
Notation "''x1'" := ("x1":var) : var_scope.
Notation "''y1'" := ("y1":var) : var_scope.
Notation "''z1'" := ("z1":var) : var_scope.

Notation "''a2'" := ("a2":var) : var_scope.
Notation "''b2'" := ("b2":var) : var_scope.
Notation "''c2'" := ("c2":var) : var_scope.
Notation "''d2'" := ("d2":var) : var_scope.
Notation "''e2'" := ("e2":var) : var_scope.
Notation "''f2'" := ("f2":var) : var_scope.
Notation "''g2'" := ("g2":var) : var_scope.
Notation "''h2'" := ("h2":var) : var_scope.
Notation "''i2'" := ("i2":var) : var_scope.
Notation "''j2'" := ("j2":var) : var_scope.
Notation "''k2'" := ("k2":var) : var_scope.
Notation "''l2'" := ("l2":var) : var_scope.
Notation "''m2'" := ("m2":var) : var_scope.
Notation "''n2'" := ("n2":var) : var_scope.
Notation "''o2'" := ("o2":var) : var_scope.
Notation "''p2'" := ("p2":var) : var_scope.
Notation "''q2'" := ("q2":var) : var_scope.
Notation "''r2'" := ("r2":var) : var_scope.
Notation "''s2'" := ("s2":var) : var_scope.
Notation "''t2'" := ("t2":var) : var_scope.
Notation "''u2'" := ("u2":var) : var_scope.
Notation "''v2'" := ("v2":var) : var_scope.
Notation "''w2'" := ("w2":var) : var_scope.
Notation "''x2'" := ("x2":var) : var_scope.
Notation "''y2'" := ("y2":var) : var_scope.
Notation "''z2'" := ("z2":var) : var_scope.

Notation "''a3'" := ("a3":var) : var_scope.
Notation "''b3'" := ("b3":var) : var_scope.
Notation "''c3'" := ("c3":var) : var_scope.
Notation "''d3'" := ("d3":var) : var_scope.
Notation "''e3'" := ("e3":var) : var_scope.
Notation "''f3'" := ("f3":var) : var_scope.
Notation "''g3'" := ("g3":var) : var_scope.
Notation "''h3'" := ("h3":var) : var_scope.
Notation "''i3'" := ("i3":var) : var_scope.
Notation "''j3'" := ("j3":var) : var_scope.
Notation "''k3'" := ("k3":var) : var_scope.
Notation "''l3'" := ("l3":var) : var_scope.
Notation "''m3'" := ("m3":var) : var_scope.
Notation "''n3'" := ("n3":var) : var_scope.
Notation "''o3'" := ("o3":var) : var_scope.
Notation "''p3'" := ("p3":var) : var_scope.
Notation "''q3'" := ("q3":var) : var_scope.
Notation "''r3'" := ("r3":var) : var_scope.
Notation "''s3'" := ("s3":var) : var_scope.
Notation "''t3'" := ("t3":var) : var_scope.
Notation "''u3'" := ("u3":var) : var_scope.
Notation "''v3'" := ("v3":var) : var_scope.
Notation "''w3'" := ("w3":var) : var_scope.
Notation "''x3'" := ("x3":var) : var_scope.
Notation "''y3'" := ("y3":var) : var_scope.
Notation "''z3'" := ("z3":var) : var_scope.

Open Scope var_scope.

(* Note: for variable names with several letters, add your own definition *)


(* ---------------------------------------------------------------------- *)
(** Notation for concrete programs *)

(* TODO: rename some x into z *)

Notation "'()" := val_unit : trm_scope.

Notation "'If_' t0 'Then' t1 'Else' t2" :=
  (trm_if t0 t1 t2)
  (at level 69, t0 at level 0) : trm_scope.

Notation "'If_' t0 'Then' t1 'End'" :=
  (trm_if t0 t1 val_unit)
  (at level 69, t0 at level 0) : trm_scope.

Notation "'Let' x ':=' t1 'in' t2" :=
  (trm_let x t1 t2)
  (at level 69, x at level 0, right associativity,
  format "'[v' '[' 'Let'  x  ':='  t1  'in' ']'  '/'  '[' t2 ']' ']'") : trm_scope.

Notation "'Let' 'Rec' f x ':=' t1 'in' t2" :=
  (trm_let f (trm_fix f x t1) t2)
  (at level 69, f at level 0, x at level 0, right associativity,
  format "'[v' '[' 'Let'  'Rec'  f  x  ':='  t1  'in' ']'  '/'  '[' t2 ']' ']'") : trm_scope.

Notation "t1 ;;; t2" :=
  (trm_seq t1 t2)
  (at level 68, right associativity, only parsing,
   format "'[v' '[' t1 ']'  ;;;  '/'  '[' t2 ']' ']'") : trm_scope.

Notation "'Fix' f x ':=' t" :=
  (trm_fix f x t)
  (at level 69, f at level 0, x at level 0) : trm_scope.

Notation "'Fix' f x1 x2 ':=' t" :=
  (trm_fix f x1 (trm_fun x2 t))
  (at level 69, f at level 0, x1 at level 0, x2 at level 0) : trm_scope.

Notation "'Fix' f x1 x2 x3 ':=' t" :=
  (trm_fix f x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, f at level 0, x1 at level 0, x2 at level 0, x3 at level 0) : trm_scope.

Notation "'ValFix' f x ':=' t" :=
  (val_fix f x t)
  (at level 69, f at level 0, x at level 0) : trm_scope.

Notation "'ValFix' f x1 x2 ':=' t" :=
  (val_fix f x1 (trm_fun x2 t))
  (at level 69, f at level 0, x1 at level 0, x2 at level 0) : trm_scope.

Notation "'ValFix' f x1 x2 x3 ':=' t" :=
  (val_fix f x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, f at level 0, x1 at level 0, x2 at level 0, x3 at level 0) : trm_scope.

Notation "'Fun' x1 ':=' t" :=
  (trm_fun x1 t)
  (at level 69, x1 at level 0) : trm_scope.

Notation "'Fun' x1 x2 ':=' t" :=
  (trm_fun x1 (trm_fun x2 t))
  (at level 69, x1 at level 0, x2 at level 0) : trm_scope.

Notation "'Fun' x1 x2 x3 ':=' t" :=
  (trm_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, x1 at level 0, x2 at level 0, x3 at level 0) : trm_scope.

Notation "'Fun' x1 ':=' t" :=
  (trm_fun x1 t)
  (at level 69, x1 at level 0) : trm_scope.

Notation "'Fun' x1 x2 ':=' t" :=
  (trm_fun x1 (trm_fun x2 t))
  (at level 69, x1 at level 0, x2 at level 0) : trm_scope.

Notation "'Fun' x1 x2 x3 ':=' t" :=
  (trm_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, x1 at level 0, x2 at level 0, x3 at level 0) : trm_scope.

Notation "'ValFun' x1 ':=' t" :=
  (val_fun x1 t)
  (at level 69, x1 at level 0) : trm_scope.

Notation "'ValFun' x1 x2 ':=' t" :=
  (val_fun x1 (trm_fun x2 t))
  (at level 69, x1 at level 0, x2 at level 0) : trm_scope.

Notation "'ValFun' x1 x2 x3 ':=' t" :=
  (val_fun x1 (trm_fun x2 (trm_fun x3 t)))
  (at level 69, x1 at level 0, x2 at level 0, x3 at level 0) : trm_scope.

Notation "'LetFun' f x1 ':=' t1 'in' t2" :=
  (trm_let f (trm_fun x1 t1) t2)
  (at level 69, f at level 0, x1 at level 0) : trm_scope.

Notation "'LetFun' f x1 x2 ':=' t1 'in' t2" :=
  (trm_let f (trm_fun x1 (trm_fun x2 t1)) t2)
  (at level 69, f at level 0, x1 at level 0, x2 at level 0) : trm_scope.

Notation "'LetFun' f x1 x2 x3 ':=' t1 'in' t2" :=
  (trm_let f (trm_fun x1 (trm_fun x2 (trm_fun x3 t1))) t2)
  (at level 69, f at level 0, x1 at level 0, x2 at level 0, x3 at level 0) : trm_scope.

Notation "'LetFix' f x1 ':=' t1 'in' t2" :=
  (trm_let f (trm_fix f x1 t1) t2)
  (at level 69, f at level 0, x1 at level 0) : trm_scope.

Notation "'LetFix' f x1 x2 ':=' t1 'in' t2" :=
  (trm_let f (trm_fix f x1 (trm_fun x2 t1)) t2)
  (at level 69, f at level 0, x1 at level 0, x2 at level 0) : trm_scope.

Notation "'LetFix' f x1 x2 x3 ':=' t1 'in' t2" :=
  (trm_let f (trm_fix f x1 (trm_fun x2 (trm_fun x3 t1))) t2)
  (at level 69, f at level 0, x1 at level 0, x2 at level 0, x3 at level 0) : trm_scope.

Notation "'While' t1 'Do' t2 'Done'" :=
  (trm_while t1 t2)
  (at level 69, t2 at level 68,
   format "'[v' 'While'  t1  'Do'  '/' '[' t2 ']' '/'  'Done' ']'")
   : trm_scope.

Notation "'For' x ':=' t1 'To' t2 'Do' t3 'Done'" :=
  (trm_for x t1 t2 t3)
  (at level 69, x at level 0, (* t1 at level 0, t2 at level 0, *)
   format "'[v' 'For'  x  ':='  t1  'To'  t2  'Do'  '/' '[' t3 ']' '/'  'Done' ']'")
  : trm_scope.

Notation "'ref t" :=
  (val_ref t)
  (at level 67) : trm_scope.

Notation "'! t" :=
  (val_get t)
  (at level 67) : trm_scope.

Notation "t1 ':= t2" :=
  (val_set t1 t2)
  (at level 67) : trm_scope.

Notation "t1 '+ t2" :=
  (val_add t1 t2)
  (at level 69) : trm_scope.

Notation "t1 '- t2" :=
  (val_sub t1 t2)
  (at level 69) : trm_scope.

Notation "t1 '= t2" :=
  (val_eq t1 t2)
  (at level 69) : trm_scope.




(* ********************************************************************** *)
(* * More on substitutions *)


(* ---------------------------------------------------------------------- *)
(** Distinct variables *)

(** [vars] is the type of a list of variables *)

Definition vars : Type := list var.

(** [var_fresh y xs] asserts that [y] does not belong to the list [xs] *)

Fixpoint var_fresh (y:var) (xs:vars) : bool :=
  match xs with
  | nil => true
  | x::xs' => if var_eq x y then false else var_fresh y xs'
  end.

(** [var_distinct xs] asserts that [xs] consists of a list of distinct variables. *)

Fixpoint var_distinct (xs:vars) : bool :=
  match xs with
  | nil => true
  | x::xs' => var_fresh x xs' && var_distinct xs'
  end.


(* ---------------------------------------------------------------------- *)
(** N-ary substitution *)

(** Shorthand [vars], [vals] and [trms] for lists of items. *)

Definition vals : Type := list val.
Definition trms : Type := list trm.

(** [substn xs vs t] is a shorthand for [substs (List.combine xs vs) t].
    It substitutes the values [vs] for the corresponding variables in [xs].
    This operation is only specified when [length xs = length vs]. *)

Definition substn (xs:vars) (vs:vals) (t:trm) : trm :=
  subst (LibList.combine xs vs) t.

(** Distribution of [substn] on [nil] and [cons] lists *)

Lemma substn_nil : forall t,
  substn nil nil t = t.
Proof using. intros. unfold substn. simpl. rew_ctx. apply subst_ctx_empty. Qed.

Lemma substn_cons : forall x xs v vs t,
  substn (x::xs) (v::vs) t = substn xs vs (subst1 x v t).
Proof using. intros. unfold substn. simpl. rew_ctx. rewrite~ subst_ctx_add. Qed.

(** Auxiliary results for freshness of bindings w.r.t. combine *)

Lemma ctx_fresh_combine : forall x ys vs,
  var_fresh x ys ->
  length ys = length vs ->
  ctx_fresh x (LibList.combine ys vs).
Proof using.
  intros x ys. unfold ctx_fresh.
  induction ys as [|y ys']; simpl; intros [|v vs] M L;
   rew_list in *; try solve [ false; math ].
  { auto. }
  { simpl. rewrite var_eq_spec in *. do 2 case_if. rewrite~ IHys'. }
Qed.

(* Permutation lemma for substitution and n-ary substitution *)

Lemma subst_substn : forall x v ys ws t,
  var_fresh x ys ->
  length ys = length ws ->
  subst1 x v (substn ys ws t) = substn ys ws (subst1 x v t).
Proof using.
  introv M L. unfold substn. rewrite~ subst1_subst.
  applys~ ctx_fresh_combine.
Qed.


(* ********************************************************************** *)
(* * N-ary functions and applications *)

(** [trm_apps t ts] denotes a n-ary application of [t] to the
    arguments from the list [ts].

    [trm_funs xs t] denotes a n-ary function with arguments [xs]
    and body [t].

    [trm_fixs f xs t] denotes a n-ary recursive function [f]
    with arguments [xs] and body [t].

  The tactic [rew_nary] can be used to convert terms in the goal
  to using the nary constructs wherever possible.

  The operation [substn xs vs t] substitutes the variables [xs]
  with the values [vs] inside the term [t].
*)


(* ---------------------------------------------------------------------- *)
(** Coercions from values to terms *)

Coercion vals_to_trms (vs:vals) : trms :=
  List.map trm_val vs.

(** Tactic [rew_vals_to_trms] to fold the coercion where possible *)

Lemma vals_to_trms_fold_start : forall v,
  (trm_val v)::nil = vals_to_trms (v::nil).
Proof using. auto. Qed.

Lemma vals_to_trms_fold_next : forall v vs,
  (trm_val v)::(vals_to_trms vs) = vals_to_trms (v::vs).
Proof using. auto. Qed.

Hint Rewrite vals_to_trms_fold_start vals_to_trms_fold_next
  : rew_vals_to_trms.

Tactic Notation "rew_vals_to_trms" :=
  autorewrite with rew_vals_to_trms.


(* ---------------------------------------------------------------------- *)
(** N-ary applications and N-ary functions *)

Fixpoint trm_apps (tf:trm) (ts:trms) : trm :=
  match ts with
  | nil => tf
  | t::ts' => trm_apps (trm_app tf t) ts'
  end.

Fixpoint trm_fixs (f:bind) (xs:vars) (t:trm) : trm :=
  match xs with
  | nil => t
  | x::xs' => trm_fix f x (trm_fixs bind_anon xs' t)
  end.

Definition val_fixs (f:bind) (xs:vars) (t:trm) : val :=
  match xs with
  | nil => arbitrary
  | x::xs' => val_fix f x (trm_fixs bind_anon xs' t)
  end.

Notation "'trm_funs' xs t1" := (trm_fixs bind_anon xs t1)
  (at level 69, xs at level 0, t1 at level 0).

Notation "'val_funs' xs t1" := (val_fixs bind_anon xs t1)
  (at level 69, xs at level 0, t1 at level 0).


(* ---------------------------------------------------------------------- *)
(** Nonempty list of distinct variables *)

Definition var_funs (n:nat) (xs:vars) : Prop :=
     var_distinct xs
  /\ length xs = n
  /\ xs <> nil.

(** Computable version of the above definition
    LATER use TLC exec *)

Definition var_funs_exec (n:nat) (xs:vars) : bool :=
     nat_compare n (List.length xs)
  && is_not_nil xs
  && var_distinct xs.

Lemma var_funs_exec_eq : forall (n:nat) xs,
  var_funs_exec n xs = isTrue (var_funs n xs).
Proof using.
  intros. unfold var_funs_exec, var_funs.
  rewrite nat_compare_eq.
  rewrite is_not_nil_eq.
  rewrite List_length_eq.
  extens. rew_istrue. iff*.
Qed.

Definition var_fixs (f:var) (n:nat) (xs:vars) : Prop :=
     var_distinct (f::xs)
  /\ length xs = n
  /\ xs <> nil.

Definition var_fixs_exec (f:var) (n:nat) (xs:vars) : bool :=
     nat_compare n (List.length xs)
  && is_not_nil xs
  && var_distinct (f::xs).

Lemma var_fixs_exec_eq : forall f (n:nat) xs,
  var_fixs_exec f n xs = isTrue (var_fixs f n xs).
Proof using.
  intros. unfold var_fixs_exec, var_fixs.
  rewrite nat_compare_eq.
  rewrite is_not_nil_eq.
  rewrite List_length_eq.
  extens. rew_istrue. iff*.
Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of n-ary functions *)

Lemma red_funs : forall m xs t,
  xs <> nil ->
  red m (trm_funs xs t) m (val_funs xs t).
Proof using.
  introv N. destruct xs as [|x xs']. { false. }
  simpl. applys red_fun.
Qed.

Lemma subst_trm_funs : forall y w xs t,
  var_fresh y xs ->
  subst1 y w (trm_funs xs t) = trm_funs xs (subst1 y w t).
Proof using.
  introv N. unfold subst1. induction xs as [|x xs']; simpls; fequals.
  { rewrite var_eq_spec in *. case_if. rewrite~ <- IHxs'. }
Qed.

Lemma red_app_funs_val_ind : forall xs vs m1 m2 tf t r,
  red m1 tf m1 (val_funs xs t) ->
  red m1 (substn xs vs t) m2 r ->
  var_funs (length vs) xs ->
  red m1 (trm_apps tf vs) m2 r.
Proof using.
  hint red_val.
  intros xs. induction xs as [|x xs']; introv R M (N&L&P).
  { false. } clear P.
  { destruct vs as [|v vs']; rew_list in *. { false; math. }
    simpls. tests C: (xs' = nil).
    { rew_list in *. asserts: (vs' = nil).
      { applys length_zero_inv. math. } subst vs'. clear L.
      simpls. applys* red_app. }
    { rew_istrue in N. destruct N as [F N'].
      unfold substn in M. simpl combine in M. rew_ctx in M. 
      rewrite subst_ctx_add in M. applys~ IHxs' M. applys* red_app.
      { rewrite~ subst_trm_funs. applys~ red_funs. } { splits~. } } }
Qed.

Lemma red_app_funs_val : forall xs vs m1 m2 vf t r,
  vf = val_funs xs t ->
  red m1 (substn xs vs t) m2 r ->
  var_funs (length vs) xs ->
  red m1 (trm_apps vf vs) m2 r.
Proof using.
  introv R M N. applys* red_app_funs_val_ind.
  { subst. apply~ red_val. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of n-ary functions *)

Lemma red_fixs : forall m f xs t,
  xs <> nil ->
  red m (trm_fixs f xs t) m (val_fixs f xs t).
Proof using.
  introv N. destruct xs as [|x xs']. { false. }
  simpl. applys red_fix.
Qed.

Lemma subst_trm_fixs : forall y w f xs t,
  var_fresh y (f::xs) ->
  subst1 y w (trm_fixs f xs t) = trm_fixs f xs (subst1 y w t).
Proof using.
  introv N. destruct xs as [|x xs'].
  { auto. }
  { unfold subst1. simpls. repeat rewrite var_eq_spec in *.
    do 2 case_if in N. simpl. rewrite var_eq_spec. case_if~.
    fequals. 
    forwards K: subst_trm_funs N. unfold subst1, ctx_one in K.
    simpls. rewrite~ K. }
Qed.  (* LATER: simplify *) 

(* LATER
Lemma red_app_fixs_val : forall xs vs m1 m2 vf (f:var) t r,
  vf = val_fixs f xs t ->
  red m1 (subst1 f vf (substn xs vs t)) m2 r ->
  var_fixs f (length vs) xs ->
  red m1 (trm_apps vf vs) m2 r.
Proof using.
  introv E M (N&L&P). destruct xs as [|x xs']. { false. }
  { destruct vs as [|v vs']; rew_list in *. { false; math. } clear P.
    simpls. case_if*. rew_istrue in *. destruct N as (N1&N2&N3).
    tests C':(xs' = nil).
    { rew_list in *. asserts: (vs' = nil).
      { applys length_zero_inv. math. } subst vs'. clear L.
      simpls. applys* red_app. }
    { applys~ red_app_funs_val_ind.
      { applys* red_app_fix. do 2 rewrite~ subst_trm_funs. applys~ red_funs. }
      { rewrite~ subst_substn in M. { rewrite~ substn_cons in M.
        rewrite~ subst_subst_neq. } { simpl. case_if~. } }
      { splits*. } } }
Qed.
*)

(* ---------------------------------------------------------------------- *)
(** Folding of n-ary functions *)

Lemma trm_apps_fold_start : forall t1 t2,
  trm_app t1 t2 = trm_apps t1 (t2::nil).
Proof using. auto. Qed.

Lemma trm_apps_fold_next : forall t1 t2 t3s,
  trm_apps (trm_app t1 t2) t3s = trm_apps t1 (t2::t3s).
Proof using. auto. Qed.

Lemma trm_apps_fold_concat : forall t1 t2s t3s,
  trm_apps (trm_apps t1 t2s) t3s = trm_apps t1 (List.app t2s t3s).
Proof using.
  intros. gen t1; induction t2s; intros. { auto. }
  { rewrite <- trm_apps_fold_next. simpl. congruence. }
Qed.

Lemma trm_funs_fold_start : forall x t,
  trm_fun x t = trm_funs (x::nil) t.
Proof using. auto. Qed.

Lemma trm_funs_fold_next : forall x xs t,
  trm_funs (x::nil) (trm_funs xs t) = trm_funs (x::xs) t.
Proof using. auto. Qed.

Lemma trm_fixs_fold_start : forall f x t,
  trm_fix f x t = trm_fixs f (x::nil) t.
Proof using. auto. Qed.

(* subsumed by iteration of trm_funs_fold_next *)
Lemma trm_funs_fold_app : forall xs ys t,
  trm_funs xs (trm_funs ys t) = trm_funs (List.app xs ys) t.
Proof using.
  intros. induction xs. { auto. } { simpl. congruence. }
Qed.

(* for innermost first rewriting strategy
Lemma trm_fixs_fold_next : forall f x xs t,
  trm_fixs f (x::nil) (trm_funs xs t) = trm_fixs f (x::xs) t.
Proof using. auto. Qed.
*)

Lemma trm_fixs_fold_app : forall f x xs ys t,
  trm_fixs f (x::xs) (trm_funs ys t) = trm_fixs f (x :: List.app xs ys) t.
Proof using. intros. simpl. rewrite~ trm_funs_fold_app. Qed.

Lemma val_funs_fold_start : forall x t,
  val_fun x t = val_funs (x::nil) t.
Proof using. auto. Qed.

Lemma val_funs_fold_app : forall x xs ys t,
  val_funs (x::xs) (trm_funs ys t) = val_funs (List.app (x::xs) ys) t.
Proof using. intros. simpl. rewrite~ trm_funs_fold_app. Qed.

Lemma val_funs_fold_app' : forall x xs ys t,
  val_funs (List.app (x::nil) xs) (trm_funs ys t) = val_funs (List.app (x::xs) ys) t.
Proof using. intros. simpl. rewrite~ trm_funs_fold_app. Qed.

Lemma val_fixs_fold_start : forall f x t,
  val_fix f x t = val_fixs f (x::nil) t.
Proof using. auto. Qed.

Lemma val_fixs_fold_app : forall f x xs ys t,
  val_fixs f (x::xs) (trm_funs ys t) = val_fixs f (List.app (x::xs) ys) t.
Proof using. intros. simpl. rewrite~ trm_funs_fold_app. Qed.

Lemma val_fixs_fold_app' : forall f x xs ys t,
  val_fixs f (List.app (x::nil) xs) (trm_funs ys t) = val_fixs f (List.app (x::xs) ys) t.
Proof using. intros. simpl. rewrite~ trm_funs_fold_app. Qed.

Hint Rewrite
  trm_apps_fold_start trm_apps_fold_next trm_apps_fold_concat
  trm_funs_fold_start trm_funs_fold_next
  trm_fixs_fold_start trm_fixs_fold_app
  val_funs_fold_start val_funs_fold_app val_funs_fold_app'
  val_fixs_fold_start val_fixs_fold_app val_fixs_fold_app' : rew_nary.

Tactic Notation "rew_nary" :=
  autorewrite with rew_nary; simpl List.app.
Tactic Notation "rew_nary" "in" hyp(H) :=
  autorewrite with rew_nary in H; simpl List.app in H.
Tactic Notation "rew_nary" "in" "*" :=
  autorewrite with rew_nary in *; simpl List.app in *.
  (* rewrite_strat (any (innermost (hints rew_nary))).
     => way too slow! *)

(* todo fix

Lemma rew_nary_demo_1 : forall (f x y z:var) t1 t2 t,
  val_fix f x (trm_fun y (trm_fun z (f t1 x y t2))) = t.
Proof using. intros. rew_nary. Abort.

Lemma rew_nary_demo_2 : forall f x y t,
  val_fun f (trm_fun x (trm_fun y (x y))) = t.
Proof using. intros. rew_nary. Abort.
*)


(* ---------------------------------------------------------------------- *)
(* ** Sequence of consecutive variables *)

(** [nat_to_var n] converts [nat] values into distinct
    [name] values.
    Warning: the current implementation is inefficient. *)

Definition dummy_char := Ascii.ascii_of_nat 0%nat.

Fixpoint nat_to_var (n:nat) : var :=
  match n with
  | O => String.EmptyString
  | S n' => String.String dummy_char (nat_to_var n')
  end.

Lemma injective_nat_to_var : injective nat_to_var.
Proof using.
  intros n. induction n as [|n']; intros m E; destruct m as [|m']; tryfalse.
  { auto. }
  { inverts E. fequals~. }
Qed.

(** [var_seq i n] generates a list of variables [x1;x2;..;xn]
    with [x1=i] and [xn=i+n-1]. Such lists are useful for
    generic programming. *)

Fixpoint var_seq (start:nat) (nb:nat) : vars :=
  match nb with
  | O => nil
  | S nb' => (nat_to_var start) :: var_seq (S start) nb'
  end.

Section Var_seq.
Implicit Types start nb : nat.

Lemma var_fresh_var_seq_lt : forall (x:nat) start nb,
  (x < start)%nat ->
  var_fresh (nat_to_var x) (var_seq start nb).
Proof using.
  intros. gen start. induction nb; intros.
  { auto. }
  { simpl. rewrite var_eq_spec. case_if.
    { lets: injective_nat_to_var C. math. }
    { applys IHnb. math. } }
Qed.

Lemma var_fresh_var_seq_ge : forall (x:nat) start nb,
  (x >= start+nb)%nat ->
  var_fresh (nat_to_var x) (var_seq start nb).
Proof using.
  intros. gen start. induction nb; intros.
  { auto. }
  { simpl. rewrite var_eq_spec. case_if.
    { lets: injective_nat_to_var C. math. }
    { applys IHnb. math. } }
Qed.

Lemma var_distinct_var_seq : forall start nb,
  var_distinct (var_seq start nb).
Proof using.
  intros. gen start. induction nb; intros.
  { auto. }
  { simpl. rew_istrue. split.
    { applys var_fresh_var_seq_lt. math. }
    { auto. } }
Qed.

Lemma length_var_seq : forall start nb,
  length (var_seq start nb) = nb.
Proof using.
  intros. gen start. induction nb; simpl; intros.
  { auto. } { rew_list. rewrite~ IHnb. }
Qed.

Lemma var_funs_var_seq : forall start nb,
  (nb > 0%nat)%nat ->
  var_funs nb (var_seq start nb).
Proof using.
  introv E. splits.
  { applys var_distinct_var_seq. }
  { applys length_var_seq. }
  { destruct nb. { false. math. } { simpl. auto_false. } }
Qed.

End Var_seq.



(* ********************************************************************** *)
(* * Tactics  *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [fmap_red] for proving [red] goals modulo
      equalities between states *)

Ltac fmap_red_base tt ::=
  match goal with H: red _ ?t _ _ |- red _ ?t _ _ =>
    applys_eq H 2 4; try fmap_eq end.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [var_neq] for proving two concrete variables distinct;
      also registered as hint for [auto] *)

Ltac var_neq :=
  match goal with |- ?x <> ?y :> var =>
    solve [ let E := fresh in
            destruct (eq_var_dec x y) as [E|E];
              [ false | apply E ] ] end.

Hint Extern 1 (?x <> ?y) => var_neq.
