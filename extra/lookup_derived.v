
(* ******************************************************* *)
(** ** Definition of context as list of bindings *)

(** This formalization of contexts leverages TLC definitions.
    For direct definitions, open file [SLFWPgen.v]. *)

Open Scope liblist_scope.

(** A context is an association list from variables to values. *)

Definition ctx : Type := list (var*val).

(** [rem x E] denotes the removal of bindings on [x] from [E]. *)

Definition rem : var -> ctx -> ctx := 
  @LibListAssocExec.rem var var_eq val.

(** [lookup x E] returns [Some v] if [x] is bound to a value [v],
    and [None] otherwise. *)

Definition lookup : var -> ctx -> option val := 
  @LibListAssocExec.get_opt var var_eq val.

(** [ctx_disjoint E1 E2] asserts that the two contexts have disjoint
    domains. *)

Definition ctx_disjoint (E1 E2:ctx) : Prop := 
  forall x v1 v2, lookup x E1 = Some v1 -> lookup x E2 = Some v2 -> False.

(** [ctx_equiv E1 E2] asserts that the two contexts bind same
    keys to same values. *)

Definition ctx_equiv (E1 E2:ctx) : Prop :=
  forall x, lookup x E1 = lookup x E2.

(** Basic properties of context operations follow. *)

Section CtxOps.

Lemma is_beq_var_eq :
  LibListAssocExec.is_beq var_eq.
Proof using. applys var_eq_spec. Qed.

Hint Resolve is_beq_var_eq.

Lemma ctx_equiv_eq :
  ctx_equiv = @LibListAssoc.equiv var val.
Proof using.
  intros. extens. intros E1 E2.
  unfold ctx_equiv, lookup, LibListAssoc.equiv. iff M.
  { intros x. specializes M x. do 2 rewrite~ LibListAssocExec.get_opt_eq in M. }
  { intros x. do 2 rewrite~ LibListAssocExec.get_opt_eq. }
Qed.

Lemma ctx_disjoint_eq :
  ctx_disjoint = @LibListAssoc.disjoint var val.
Proof using.
  intros. extens. intros E1 E2.
  unfold ctx_disjoint, lookup, LibListAssoc.disjoint. iff M; intros x v1 v2 K1 K2.
  { applys M; rewrite* LibListAssocExec.get_opt_eq. }
  { rewrite LibListAssocExec.get_opt_eq in K1, K2; auto. applys* M. }
Qed.

Lemma lookup_nil : forall y,
  lookup y (nil:ctx) = None.
Proof using.
  intros. unfold lookup. rewrite~ LibListAssocExec.get_opt_eq. 
Qed.

Lemma lookup_cons : forall x v E y,
  lookup y ((x,v)::E) = (If x = y then Some v else lookup y E).
Proof using.
  intros. unfold lookup. repeat rewrite~ LibListAssocExec.get_opt_eq.
Qed.

Lemma lookup_app : forall E1 E2 x,
  lookup x (E1 ++ E2) = match lookup x E1 with
                         | None => lookup x E2
                         | Some v => Some v
                         end.
Proof using. 
  intros. unfold lookup. repeat rewrite~ LibListAssocExec.get_opt_eq.
  applys~ LibListAssoc.get_opt_app.
Qed.

Lemma lookup_rem : forall x y E,
  lookup x (rem y E) = If x = y then None else lookup x E.
Proof using. 
  intros. unfold lookup, rem. repeat rewrite~ LibListAssocExec.get_opt_eq.
  repeat rewrite~ LibListAssocExec.rem_eq. applys~ LibListAssoc.get_opt_rem.
Qed.

Lemma rem_nil : forall y,
  rem y (nil:ctx) = nil.
Proof using.
  intros. unfold rem. rewrite~ LibListAssocExec.rem_eq.
Qed.

Lemma rem_cons : forall x v E y,
  rem y ((x,v)::E) = (If x = y then rem y E else (x,v) :: rem y E).
Proof using. 
  intros. unfold rem. repeat rewrite~ LibListAssocExec.rem_eq.
  rewrite~ LibListAssoc.rem_cons.
Qed.

Lemma rem_app : forall x E1 E2,
  rem x (E1 ++ E2) = rem x E1 ++ rem x E2.
Proof using. 
  intros. unfold rem. repeat rewrite~ LibListAssocExec.rem_eq.
  rewrite~ LibListAssoc.rem_app.
Qed.

Lemma ctx_equiv_rem : forall x E1 E2,
  ctx_equiv E1 E2 ->
  ctx_equiv (rem x E1) (rem x E2).
Proof using.
  introv M. rewrite ctx_equiv_eq in *. unfold rem.
  repeat rewrite~ LibListAssocExec.rem_eq.
  applys~ LibListAssoc.equiv_rem.
Qed.

Lemma ctx_disjoint_rem : forall x E1 E2,
  ctx_disjoint E1 E2 ->
  ctx_disjoint (rem x E1) (rem x E2).
Proof using.
  introv M. rewrite ctx_disjoint_eq in *. unfold rem.
  repeat rewrite~ LibListAssocExec.rem_eq.
  applys~ LibListAssoc.disjoint_rem.
Qed.

Lemma ctx_disjoint_equiv_app : forall E1 E2,
  ctx_disjoint E1 E2 ->
  ctx_equiv (E1 ++ E2) (E2 ++ E1).
Proof using.
  introv D. intros x. do 2 rewrite~ lookup_app. 
  case_eq (lookup x E1); case_eq (lookup x E2); auto.
  { intros v2 K2 v1 K1. false* D. }
Qed.

End CtxOps.

Hint Rewrite lookup_nil lookup_cons rem_nil rem_cons : rew_ctx.

Tactic Notation "rew_ctx" :=
   autorewrite with rew_ctx.
