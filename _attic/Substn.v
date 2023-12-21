
(** [ctx] is the type of bindings from variables to values *)

Definition ctx := Ctx.ctx val.

(** [subst E t] substitutes all the bindings from [E] inside [t] *)

Fixpoint subst (E:ctx) (t:trm) : trm :=
  let aux := subst E in
  match t with
  | trm_val v => trm_val v
  | trm_var x => match Ctx.lookup x E with
                 | None => t
                 | Some v => v
                 end
  | trm_fix f z t1 => trm_fix f z (subst (Ctx.rem z (Ctx.rem f E)) t1)
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  | trm_let z t1 t2 => trm_let z (aux t1) (subst (Ctx.rem z E) t2)
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_while t1 t2 => trm_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 => trm_for x (aux t1) (aux t2) (subst (Ctx.rem x E) t3)
  end.


(* ---------------------------------------------------------------------- *)
(** Special calls to [subst] on 1, 2, or n bindings. *)

(** [subst1 z v t] replaces occurences of binder [z] with [v] in [t]. *)

Definition subst1 (z:bind) (v:val) (t:trm) :=
  subst (Ctx.one z v) t.

(** [subst2 z1 v1 z2 v2 t] is similar. *)

Definition subst2 (z1:bind) (v1:val) (z2:bind) (v2:val) (t:trm) :=
   subst (Ctx.add z1 v1 (Ctx.one z2 v2)) t.

(** [substn xs vs t] is a shorthand for [substs (List.combine xs vs) t].
    It substitutes the values [vs] for the corresponding variables in [xs].
    This operation is only specified when [length xs = length vs]. *)

Definition substn (xs:vars) (vs:vals) (t:trm) : trm :=
  subst (LibList.combine xs vs) t.

(* ---------------------------------------------------------------------- *)
(** Lemmas about substitution *)

(** [subst] with [empty] changes nothing. *)

Lemma subst_empty : forall t,
  subst Ctx.empty t = t.
Proof using.
  intros. induction t; simpl;
   try solve [ repeat rewrite Ctx.rem_empty; fequals* ].
Qed.

(** [subst1 z v t]  returns [t] unchanged when [z] is anonymous. *)

Lemma subst1_anon : forall v t,
  subst1 bind_anon v t = t.
Proof using.
  intros. unfold subst1, Ctx.one, Ctx.add. rewrite~ subst_empty.
Qed.

(** [subst] can be combuted by iteratively substituting its bindings. *)

Lemma subst_cons : forall x v E t,
  subst ((x,v)::E) t = subst E (subst1 x v t).
Proof using.
  intros. unfold subst1. simpl. rew_ctx. gen E.
    induction t; intros; simpl; try solve [ fequals* ].
    { rewrite var_eq_spec. case_if~. }
    { rew_ctx. fequals. tests: (b = x).
      { repeat rewrite Ctx.rem_add_same. fequals.
        rewrite Ctx.rem_empty, subst_empty. auto. }
      { repeat rewrites~ (>> Ctx.rem_add_neq b). rewrite Ctx.rem_empty.
        tests: (b0 = x).
        { repeat rewrite Ctx.rem_add_same.
          rewrite Ctx.rem_empty. rewrite~ subst_empty. }
        { repeat rewrite~ Ctx.rem_add_neq. rewrite Ctx.rem_empty.
          rewrite~ IHt. } } }
  { rew_ctx. fequals. tests: (b = x).
    { do 2 rewrite Ctx.rem_add_same. fequals. rewrite~ subst_empty. }
    { do 2 (rewrite~ Ctx.rem_add_neq). rewrite Ctx.rem_empty. rewrite~ IHt2. } }
  { admit. (* todo for loops *) }
Qed.

(** Lifting of the above lemma to handle the substitution of binders. *)

Lemma subst_add : forall z v E t,
  subst (Ctx.add z v E) t = subst E (subst1 z v t).
Proof using.
  intros. destruct z as [|x].
  { simpl. rewrite~ subst1_anon. }
  { applys~ subst_cons. }
Qed.

(** Reformulation of the definition of [subst2] *)

Lemma subst2_eq_subst1_subst1 : forall x1 x2 v1 v2 t,
  subst2 x1 v1 x2 v2 t = subst1 x2 v2 (subst1 x1 v1 t).
Proof using. intros. unfold subst2. rewrite~ subst_add. Qed.

(** Distribution of [substn] on [nil] and [cons] lists *)

Lemma substn_nil : forall t,
  substn nil nil t = t.
Proof using. intros. unfold substn. simpl. rew_ctx. apply subst_empty. Qed.

Lemma substn_cons : forall x xs v vs t,
  substn (x::xs) (v::vs) t = substn xs vs (subst1 x v t).
Proof using.
  intros. unfold substn. rewrite combine_cons. rewrite~ subst_cons.
Qed.




Lemma rem_rem_same : forall z (E:ctx),
  Ctx.rem z (Ctx.rem z E) = Ctx.rem z E.
Proof using. Admitted.

Lemma rem_rem_swap : forall z1 z2 (E:ctx),
  Ctx.rem z1 (Ctx.rem z2 E) = Ctx.rem z2 (Ctx.rem z1 E).
Proof using. Admitted.



Lemma subst1_subst_rem_neq : forall x v E t,
  subst1 x v (subst (Ctx.rem x E) t) =
  subst (Ctx.add x v E) t.
Proof using. Opaque Ctx.add Ctx.rem.
  intros. destruct x as [|x].
  { simpl. rewrite~ subst1_anon. }
  { unfold subst1, Ctx.one. gen E. induction t; intros; simpl; try solve [fequals].
    { skip. }
    { fequals. skip. }
    { fequals. tests: (b = x).
      { repeat rewrite Ctx.rem_add_same. rewrite rem_rem_same.
        rewrite Ctx.rem_empty. rewrite subst_empty. auto. }
      { repeat rewrite~ Ctx.rem_add_neq. rewrite Ctx.rem_empty.
        rewrite <- IHt2. rewrite~ rem_rem_swap. } }
    { fequals. rewrite rem_rem_swap. admit. }
Admitted.



(*
(** Substitutions for two distinct variables commute. *)

Lemma subst1_subst1_neq : forall (x1 x2:var) v1 v2 t,
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


Lemma subst1_subst_rem_same : forall E z v t,
    subst1 z v (subst (rem z E) t)
  = subst E (subst1 z v t).
Proof using.
  intros. rewrite <- subst_add.

  intros E. induction E as [|(y,w) E']; simpl; intros.
  { auto. }
  { rewrite var_eq_spec. case_if.
    { subst. rewrite IHE'. rewrite~ subst_subst_same. }
    { simpl. rewrite IHE'. rewrite~ subst_subst_neq. } }
Qed.
)


Lemma subst1_subst_rem_same : forall E z v t,
    subst1 z v (subst (rem z E) t)
  = subst E (subst1 z v t).
Proof using.
  intros. rewrite <- subst_add.

  intros E. induction E as [|(y,w) E']; simpl; intros.
  { auto. }
  { rewrite var_eq_spec. case_if.
    { subst. rewrite IHE'. rewrite~ subst_subst_same. }
    { simpl. rewrite IHE'. rewrite~ subst_subst_neq. } }
Qed.

*)

===========================



(** Definition of variable clash *)

Definition var_clash (y:var) (z:bind) : bool :=
  match z with
  | bind_anon => false
  | bind_var x => var_eq x y
  end.

