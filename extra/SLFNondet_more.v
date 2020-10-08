
(** [ctx] defines the grammar of context. *)

Inductive ctx : Type :=
  | ctx_hole : ctx
  | ctx_seq1 : ctx -> trm -> ctx
  | ctx_let1 : var -> ctx -> trm -> ctx.

(* not needed in A-normal form
  | ctx_if1 : ctx -> trm -> trm -> ctx. *)

Implicit Types C : ctx.

(** [app_ctx C t] produces the term [C[t]], that is, it fills the
    hole of the context [C] with the term [t]. *)

Fixpoint app_ctx (C:ctx) (t:trm) : trm :=
  match C with
  | ctx_hole => t
  | ctx_seq1 C1 t2 => trm_seq (app_ctx C1 t) t2
  | ctx_let1 x C1 t2 => trm_let x (app_ctx C1 t) t2
 (* | ctx_if1 C1 t2 t3 => trm_if (app_ctx C1 t) t2 t3 *)
  end.

Definition trm_is_val (t:trm) : Prop :=
  match t with trm_val v => True | _ => False end.



  (* Rule for (strict) contexts *)
  | step_ctx : forall C s1 s2 t1 t1',
      C <> ctx_hole ->
      ~ trm_is_val t1 ->
      step s1 t1 s2 t1' ->
      step s1 (app_ctx C t1) s2 (app_ctx C t1')




Lemma step_val_inv : forall s v s' t',
  ~ step s v s' t'.
Proof using. introv R. inverts R. Qed.



(** The general pattern is captured by the following lemma.
    It applies to all terms that are not let-bindings, and that
    take a reduction step in the current state. *)

Lemma correct_step1 : forall s s' t t' Q,
  step s t s' t' ->
  (forall x t1 t2, t <> trm_let x t1 t2) ->
  correct s' t' Q ->
  correct s t Q.
Proof using.
  introv R N M. applys correct_step. introv R'.
  inverts R; inverts R'; subst; tryfalse;
  try solve [ match goal with H: ?ta = ?tb |- _ => inverts H end; auto ].
  skip.
  skip.
  skip.
  skip.
  skip.
sip
  false* N.
  inverts R.

try solve [ false N; eauto ]. false N.
Qed.

(*
Axiom correct_step1 : forall t' s' s t Q,
  (forall v, t <> trm_val v) ->
  (forall s'' t'', step s t s'' t'' -> s'' = s' /\ t'' = t') ->
  correct s' t' Q ->
  correct s t Q.

Lemma hoare_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  hoare (subst x v2 (subst f v1 t1)) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof using.
  introv E M. intros s K. applys correct_step1.
  { auto_false. }
  { introv R. inverts R; tryfalse.
     { false. destruct C; tryfalse. }
     { inverts TEMP. eauto. } }
  { applys M K. }
Qed.
*)




Lemma hoare_seq : forall t1 t2 H Q H1,
  hoare t1 H (fun r => H1) ->
  hoare t2 H1 Q ->
  hoare (trm_seq t1 t2) H Q.
Proof using.
(*
  introv M1 M2. intros s K. lets HC: (rm M1) (rm K).
  gen_eq Q1: (fun (_:val) => H1).
  gen_eq t1': t1.
  gen_eq s': s.
  induction HC; introv -> -> ->.
  { applys correct_step.
    introv R. inverts R; tryfalse.
    { destruct C; tryfalse. simpls. inverts H2.  (* destruct C; tryfalse. *)
      simpls. subst. false H4. hnfs*. }
    { subst. applys* M2. } }
  { rename t as t1. applys correct_step.
    introv R. inverts R; tryfalse.
    { destruct C; tryfalse. simpls. inverts H3.
      simpls. subst. false H4. hnfs*. }
   }
  { rename TEMP into E. inverts E. applys M K. }

  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval_seq R1 R2. }
Qed.

Lemma hoare_let : forall x t1 t2 H Q Q1,
  hoare t1 H Q1 ->
  (forall v, hoare (subst x v t2) (Q1 v) Q) ->
  hoare (trm_let x t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval_let R2. }
Qed.
*)
Admitted.


Lemma correct_ref : forall s v Q p,
  ~ (indom s p) ->
  Q p (update s p v) ->
  correct s (val_ref v) Q.
Proof using.
  introv N HQ. applys correct_step.
  { do 2 esplit. applys* step_ref. }
  { introv R. inverts R; tryfalse. applys* correct_val.
    unfold update. applys~ hstar_intro.
    { exists p. rewrite~ hstar_hpure_l. split~. { applys~ hsingle_intro. } }
    { applys* disjoint_single_of_not_indom. } }


Lemma hoare_ref : forall H v,
  hoare (val_ref v)
    H
    (fun r => (\exists p, \[r = val_loc p] \* p ~~> v) \* H).
Proof using.
  intros. intros s K.
  forwards~ (p&D&N): (Fmap.single_fresh 0%nat s v).
  applys correct_ref p.
  { intros N'. applys disjoint_inv_not_indom_both D N'. applys indom_single. }
  { unfold update. applys~ hstar_intro.
    { exists p. rewrite~ hstar_hpure_l. split~. { applys~ hsingle_intro. } } }
Qed.




(** Recall our previous big-step evaluation judgment. *)

Inductive eval : heap -> trm -> heap -> val -> Prop :=
  | eval_val : forall s v,
      eval s (trm_val v) s v
  | eval_fix : forall s f x t1,
      eval s (trm_fix f x t1) s (val_fix f x t1)
  | eval_app_fix : forall s1 s2 v1 v2 f x t1 v,
      v1 = val_fix f x t1 ->
      eval s1 (subst x v2 (subst f v1 t1)) s2 v ->
      eval s1 (trm_app v1 v2) s2 v
  | eval_let : forall s1 s2 s3 x t1 t2 v1 r,
      eval s1 t1 s2 v1 ->
      eval s2 (subst x v1 t2) s3 r ->
      eval s1 (trm_let x t1 t2) s3 r
  | eval_if : forall s1 s2 b v t1 t2,
      eval s1 (if b then t1 else t2) s2 v ->
      eval s1 (trm_if (val_bool b) t1 t2) s2 v
  | eval_add : forall s n1 n2,
       eval s (val_add (val_int n1) (val_int n2)) s (val_int (n1 + n2))
  | eval_ref : forall s v p,
      ~ Fmap.indom s p ->
      eval s (val_ref v) (Fmap.update s p v) (val_loc p)
  | eval_get : forall s p v,
      Fmap.indom s p ->
      v = Fmap.read s p ->
      eval s (val_get (val_loc p)) s v
  | eval_set : forall s p v,
      Fmap.indom s p ->
      eval s (val_set (val_loc p) v) (Fmap.update s p v) val_unit
  | eval_free : forall s p,
      Fmap.indom s p ->
      eval s (val_free (val_loc p)) (Fmap.remove s p) val_unit.

(** Recall our previous definition of Hoare triple, for deterministic
    languages. Let's rename it to [dhoare], within the scope of this
    file. *)

Definition dhoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=


(** Exercise: prove the equivalence of [hoare] and [dhoare],
    under the assumption [deterministic step]. *)

Lemma eval_of_step_and_eval : forall s1 s2 s3 t1 t2 v,
  step s1 t1 s2 t2 ->
  eval s2 t2 s3 v ->
  eval s1 t1 s3 v.
Admitted.


Lemma hoare_eq_dhoare_of_deterministic :
  deterministic step ->
  hoare = dhoare.
Proof using.
  introv HD. extens. intros t H Q.
  iff M; unfolds hoare, dhoare.
  { intros s K. specializes M K. clear K.
    induction M.
    { do 2 esplit. split. { applys eval_val. } { auto. } }
    { rename H0 into R'. destruct R' as (s'&t'&R').
      lets (s''&t''&HR&HQ): H2 R'. exists s'' t''. split~.
      applys* eval_of_step_and_eval. } }
  { intros s K. specializes M K. clear K.
    destruct M as (s'&v&HR&HQ). gen_eq v': v.
    induction HR; introv EQ; subst v.
    { applys* correct_val. }
    { applys* correct_fix. }
    { applys* correct_app_fix. }
    { applys* correct_let. skip. skip. }
    { applys* correct_if. } skip.
    { (* TODO: pb, allocation is not deterministic here.
 *)
Admitted.

(** Remark: technically, [hoare] always implies [dhoare], even for
    a non-deterministic language. Yet, the definition [dhoare] does
    not make much sense for a non-deterministic language, so we do
    not bother formally stating this more general implication. *)



(*
: [phoare t H Q] holds if, for any input state [s]
    satisfying the precondition [H], for any terminating evaluation
    of [t] in the state [s] reaching a value [v] in a state [s'],
    the postcondition [Q] holds of [v] and [s'].

    This definition applies regardless of whether the language is
    deterministic or not. It can be stated in big-step as well as
    in small-step presentation. Let's start with the big-step
    presentation. *)

Definition phoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s s' v, H s -> eval s t s' v -> Q v s'.


(** Exercise: prove the equivalence between the small-step and the
    big-step presentations of partial correctness Hoare triples,
    that is, the equivalence beteween [phoare] and [phoare']. *)

Lemma poare_eq_phoare' :
  phoare = phoare'.
Proof using. skip. Qed.






(* ################################################ *)
(** ** Deterministic languages *)

(** Let's forget about the details of our semantics defined by [step],
    and consider a general small-step semantics. *)

(** A semantics is deterministic iff there is at most one evaluation
    rule that applies to any given term. *)

(** The definition of [steps] may be simplified for a deterministic
    language, as shown below, yielding a predicate called [dsteps]. *)

Inductive dsteps : state->trm->(val->hprop)->Prop :=
  | dsteps_val : forall s v Q,
      Q v s ->
      dsteps s v Q
  | dsteps_step : forall s t s' t' Q,
      step s t s' t' ->
      dsteps s' t' Q ->
      dsteps s t Q.

(** Note: if we consider a language with deterministic allocation,
    then we could prove the equivalence between the judgment
    [hoare t H Q] from the file and the big-step-style definition from
    our previous chapters, that is,
    [forall s, H s -> exists s' v, eval s t s' v /\ Q v s'].
    This equivalence proof amounts, in particular, to establishing the
    equivalence between a small-step and a big-step semantics.
    It goes beyond the scope of the present chapter. *)



(** First, we prove an auxiliary results asserting that values can only evaluate
    to themselves with respect to the iterated reduction judgment [steps]. *)

Lemma steps_val_inv : forall s v s' t',
  steps s v s' t' ->
  s' = s /\ t' = v.
Proof using.
  introv M. inverts M as R1 R2. { auto. } { false. inverts R1. }
Qed.


