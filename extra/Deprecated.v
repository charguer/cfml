(** Reformulation of the definition of [subst2] *)

Lemma subst2_eq_subst1_subst1 : forall x1 x2 v1 v2 t,
  subst2 x1 v1 x2 v2 t = subst1 x2 v2 (subst1 x1 v1 t).
Proof using. auto. Qed.

(** Reformulation of the definition of [isubst2] *)

Lemma isubst2_eq_isubst1_isubst1 : forall x1 x2 v1 v2 t,
  isubst2 x1 v1 x2 v2 t = isubst1 x2 v2 (isubst1 x1 v1 t).
Proof using.
  intros. unfold isubst2. rewrite~ isubst_add.
  rewrites (>> isubst1_eq_subst1 x1). auto.
Qed.

(** [isubst2] matches [subst2] *)

Lemma isubst2_eq_subst2 : forall z1 v1 z2 v2 t,
  isubst2 z1 v1 z2 v2 t = subst2 z1 v1 z2 v2 t.
Proof using.
  intros. rewrite isubst2_eq_isubst1_isubst1, subst2_eq_subst1_subst1.
  do 2 rewrite isubst1_eq_subst1. auto.
Qed.
(** [subst2] is a shorthand that iterates two calls to [subst1]. *)

Definition subst2 (z1:bind) (v1:val) (z2:bind) (v2:val) (t:trm) :=
   subst1 z2 v2 (subst1 z1 v1 t).

Lemma trm_size_isubst1 : forall t z v,
  trm_size (isubst1 z v t) = trm_size t.
Proof using. intros. applys trm_size_isubst. Qed.


(** [isubst2 z1 v1 z2 v2 t] is similar. *)

Definition isubst2 (z1:bind) (v1:val) (z2:bind) (v2:val) (t:trm) :=
   isubst (Ctx.add z1 v1 (Ctx.one z2 v2)) t.


(** [isubst1 z v t] replaces occurences of binder [z] with [v] in [t]. *)

Definition isubst1 (z:bind) (v:val) (t:trm) :=
  isubst (Ctx.one z v) t.

(** [isubst1] matches [subst1] *)

Lemma isubst1_eq_subst1 : forall z v t,
  isubst1 z v t = subst1 z v t.
Proof using.
  intros. unfold isubst1, Ctx.one.
  rewrite isubst_add, isubst_empty. auto.
Qed.

(** [isubst1 z v t] returns [t] unchanged when [z] is anonymous. *)

Lemma isubst1_anon : forall v t,
  isubst1 bind_anon v t = t.
Proof using.
  intros. unfold isubst1, Ctx.one, Ctx.add. rewrite~ isubst_empty.
Qed.

Ltac solve_measure_trm_size tt :=
  unfold measure in *; simpls; repeat rewrite trm_size_isubst1; math.

=================================


