



(* ################################################ *)
(* ################################################ *)
(* DONT DELETE TODO : reasoning rule for while loops

Definition val_while (f x y u:var) (t1:trm) (t2:trm) : val :=
  (* let f x y u := fresh t1 t2 in *)
  val_fix f x (trm_let y t1 (trm_if (trm_var y) (trm_let u t1 (trm_app (trm_var f) val_unit)) val_unit)).

Lemma phoare_val : forall v H Q,
  H ==> Q v ->
  phoare (trm_val v) H Q.
Proof using. introv M. intros h K. applys* coevals_val. Qed.


Lemma subst_id : forall x v t,
  subst x v t = t.
Admitted.

(* todo: generalize H Q with a ghost param  *)
Lemma phoare_while : forall f x y u t1 t2 (C:val->hprop),
  let loop := trm_app (val_while f x y u t1 t2) val_unit in
  phoare t1 (\exists b, C b) (fun v => \exists b, \[v = val_bool b] \* C b) ->
  phoare t2 (C true) (fun v => \exists b, C b) ->
  phoare loop (\exists b, C b) (fun v => C false).
Proof using.
  introv M1 M2. cofix IH. applys phoare_app_fix. reflexivity.
  repeat rewrite subst_id. applys phoare_let.
  { applys M1. }
  { intros v. rewrite subst_id. skip (b&E'&E): (exists b, trm_var y = v /\ v = val_bool b).
    rewrite E'. subst v. applys phoare_if. clear E'. case_if.
    { applys phoare_let.
      { applys phoare_conseq M1. xsimpl. xsimpl. }
      { intros v. rewrite subst_id.
        skip_rewrite (trm_var f = val_while f x y u t1 t2).
        applys phoare_hexists. intros b'. applys phoare_hpure. intros Hb'. subst.
        applys phoare_conseq IH. xsimpl. xsimpl. } }
    { applys phoare_val. xsimpl. intros ? ->. xsimpl. } }
Qed.


*)
(* ################################################ *)
(* ################################################ *)
(* ################################################ *)
(* ################################################ *)
(* DONT DELETE TODO : proof of equivalence for bounded non determinism *)



Lemma sevals_eq_sevals'_of_bounded_determinism :
  ~ unbounded_nondeterminism ->
  sevals' = sevals.
Proof using.
  introv HD. extens. intros s t Q. iff M.
  { destruct M as (M&(nmax&B)). gen s t Q. induction nmax as [|nmax']; intros.
    { tests C: (exists v, t = trm_val v).
      { destruct C as (v&->). applys sevals_val. applys psevals'_val_inv M. }
      { lets (s2&t2&S0&M'): psevals'_not_val_inv M C.
        false B 1%nat. { math. } applys stepsn_step. applys S0. applys stepsn_refl. } }
    (* LATER: could factorize better the test on C? before the induction? *)
    { tests C: (exists v, t = trm_val v).
      { destruct C as (v&->). applys sevals_val. applys psevals'_val_inv M. }
      { lets (s2&t2&S0&M'): psevals'_not_val_inv M C.
        applys sevals_step. { exists. applys S0. } clears s2 t2.
        intros s' t' S. applys IHnmax'.
        { applys step_at_most_intro B S. }
        { applys pevals'_inv_step M S. } } } }
  { split.
    { introv R. gen M. induction R; intros.
      { inverts M as M1 M2.
        { left*. }
        { right. applys M1. } }
      { rename H into R1, R into R2. inverts M as M1 M2.
        { false. inverts R1. }
        { applys IHR. applys M2 R1. } } }
    { unfold bounded_exec. induction M.
      { exists 0%nat. introv N R.
        inverts R as S R'. { false. math. } inverts S. }
      { rename H1 into IH.
        asserts (nmax1&B1): (exists nmax1, forall s2 t2 n1,
          step s t s2 t2 ->
          t = val_repeat (val_int n1) ->
          n1 > 0 ->
          steps_at_most nmax1 s2 (val_repeat (val_int (n1-1)))).
        { tests C: (exists (n1:int), t = val_repeat n1 /\ (n1 > 0)).
          { destruct C as (n1&->&Hn1).
            forwards (nmax&B): IH. { applys* step_repeat_succ. }
            exists nmax. intros s2 t2 n0 R E Hn0. inverts E.
            asserts ->: (s2 = s). { inverts R as; try false_invert; auto. }
            applys B. }
          { exists 0%nat. intros. false* C. } }
        asserts (nmax2&B2): (exists nmax2, forall t1v s2 t1',
          step s t s2 (val_repeat t1') ->
          t = val_repeat t1v ->
          step s t1v s2 t1' ->
          steps_at_most nmax2 s2 (val_repeat t1')).
        { tests C: (exists t1 s2 t1', t = val_repeat t1 /\ step s t1 s2 t1').
           { destruct C as (t1&s2&t1'&->&S1).
             forwards (nmax&B): IH. { applys* step_repeat_ctx S1. }
             exists nmax. intros t1v s2v t1'v S E S1'. invert E; intros <-.
            (* INCOMPLETE PROOF REQUIRES showing finite branching for the subterm *) skip. }
           { exists 0%nat. intros. false* C. } }
        exists (S (nmax1 + nmax2)). (* it could be a max instead of a sum *)
        intros n s' t' Hn0 R.
        inverts R as. { false; math. } introv S R'. lets S': S.
        inverts S as.
        { false* stepsn_pos_val_inv. { math. } }
        { introv HD'. false* HD. }
        { false* stepsn_pos_val_inv. { math. } }
        { introv Hn. forwards* B: B1 S'. applys* B R'. { math. } }
        { introv R1. forwards* B: B2 S' R1. applys B R'. { math. } } } } }
Qed.











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




Qed.



(****Extra not needed*)


(** [sdiverge_let] is the counterpart of [seval_let]. *)

Lemma sdiverge_let : forall s1 s2 v1 x t1 t2,
  steps s1 t1 s2 (trm_val v1) ->
  sdiverge s2 (subst x v1 t2) ->
  sdiverge s1 (trm_let x t1 t2).
Proof using.
  introv M1 M2. gen_eq t1': (trm_val v1). gen v1.
  induction M1; intros; subst.
  { applys sdiverge_step. { applys step_let. } { applys M2. } }
  { rename H into R1. applys sdiverge_step.
    { applys step_let_ctx R1. }
    { applys* IHM1 M2. } }
Qed.

(** [sdiverge_let_ctx] is similar to [diverge_let_ctx], but
    expressed with respect to [sdiverge]. *)

Lemma sdiverge_let_ctx : forall s1 x t1 t2,
  sdiverge s1 t1 ->
  sdiverge s1 (trm_let x t1 t2).
Proof using.
  cofix IH. introv M. inverts M as R M1.
  applys sdiverge_step.
  { applys step_let_ctx R. }
  { applys IH M1. }
Qed.


Lemma diverge_of_step_and_diverge : forall s1 s2 t1 t2,
  step s1 t1 s2 t2 ->
  diverge s2 t2 ->
  diverge s1 t1.
Proof using.
(*
  introv M1 M2. gen s3 v. induction M1; intros.
  { inverts M2 as M3 M4. applys* eval_let. (* applys* IHM1. *) }
  { inverts M2. applys eval_fix. }
  { applys* eval_app_fix. }
  { applys* eval_if. }
  { applys* eval_let. applys eval_val. }
*)
skip.
Qed.




Lemma cosevals_of_coeval : forall s t Q,
  coevals s t Q ->
  cosevals s t Q.
Proof.
  cofix IH. introv M. inverts M.
  { applys* cosevals_val. }
  { applys* cosevals_step.
    { do 2 esplit. applys step_fix. }
    { introv S. inverts S. applys* cosevals_val. } }
  { applys* cosevals_step.
    { do 2 esplit. applys* step_app_fix. }
    { introv S. inverts S as E. inverts E. applys* IH. } }
  { rename H into M1, H0 into M2.
    applys cosevals_let.
    skip. (* PB GUARD *) skip. }
  { applys* cosevals_step.
    { do 2 esplit. applys* step_if. }
    { introv S. inverts S. applys* IH. } }
  { applys* cosevals_step.
    { do 2 esplit. applys* step_add. }
    { introv S. inverts S. applys* cosevals_val. } }
  { applys* cosevals_step.
    { do 2 esplit. applys* step_rand 0. math. }
    { introv S. inverts S; try false_invert. applys* cosevals_val. } }
  { applys* cosevals_step.
    { forwards~ (p&F): (exists_smallest_fresh s). lets (D&_): F.
      do 2 esplit. applys* step_ref. }
    { introv S. inverts S; try false_invert. applys* cosevals_val. } }
  { applys* cosevals_step.
    { do 2 esplit. applys* step_get. }
    { introv S. inverts S; try false_invert. applys* cosevals_val. } }
  { applys* cosevals_step.
    { do 2 esplit. applys* step_set. }
    { introv S. inverts S; try false_invert. applys* cosevals_val. } }
  { applys* cosevals_step.
    { do 2 esplit. applys* step_free. }
    { introv S. inverts S; try false_invert. applys* cosevals_val. } }
Qed.




(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * *)


CoInductive trace : Type :=
  | trace_return : val -> state -> trace
  | trace_step : trace -> trace.

Definition ret s v := (trace_return v s).

CoFixpoint trace_app (T1 T2:trace) : trace :=
  match T1 with
  | trace_return _ _ => T2
  | trace_step T1' => trace_step (trace_app T1' T2)
  end.

CoInductive trace_ends (v:val) (s:state) : trace->Prop :=
  | trace_ends_ter :
      trace_ends v s (trace_return v s)
  | trace_ends_step : forall T,
      trace_ends v s T ->
      trace_ends v s (trace_step T).


(** Deterministic *)

CoInductive post : trace->(val->hprop)->Prop :=
  | post_ter : forall Q v s,
      Q v s ->
      post (trace_return v s) Q
  | post_step : forall T Q,
      post T Q ->
      post (trace_step T) Q.

CoInductive teval : state -> trm -> trace -> Prop :=
  | teval_val : forall s v,
      teval s (trm_val v) (ret s v)
  | teval_fix : forall s f x t1,
      teval s (trm_fix f x t1) (ret s (val_fix f x t1))
  | teval_app_fix : forall s1 v1 v2 f x t1 T,
      v1 = val_fix f x t1 ->
      teval s1 (subst x v2 (subst f v1 t1)) T ->
      teval s1 (trm_app v1 v2) (trace_step T)
  | teval_let : forall s1 s2 s3 x t1 t2 v1 T1 T2,
      teval s1 t1 T1 ->
      (forall v1 s2, trace_ends v1 s2 T1 ->  (* at most one such v1, since deterministic *)
         teval s2 (subst x v1 t2) T2) ->
      teval s1 (trm_let x t1 t2) (trace_app T1 T2)
  | teval_if : forall s1 b t1 t2 T,
      teval s1 (if b then t1 else t2) T ->
      teval s1 (trm_if (val_bool b) t1 t2) (trace_step T)
  | teval_add : forall s n1 n2,
      teval s (val_add (val_int n1) (val_int n2)) (ret s (val_int (n1 + n2)))
  | teval_ref : forall s v p,
      smallest_fresh s p ->
      ~ Fmap.indom s p ->
      teval s (val_ref v) (ret (Fmap.update s p v) (val_loc p))
  | teval_get : forall s p,
      Fmap.indom s p ->
      teval s (val_get (val_loc p)) (ret s (Fmap.read s p))
  | teval_set : forall s p v,
      Fmap.indom s p ->
      teval s (val_set (val_loc p) v) (ret (Fmap.update s p v) val_unit)
  | teval_free : forall s p,
      Fmap.indom s p ->
      teval s (val_free (val_loc p)) (ret (Fmap.remove s p) val_unit).

Definition ptdhoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (s:state), H s -> exists T, teval s t T /\ post T Q.

(** Non-deterministic *)

Implicit Type K : trace->Prop.

(** [trace->Prop] is similar to [bool*((val*state)->Prop)],
    where bool indicates option to diverge,
    same as [(Div+(Ter of val*state)) -> Prop] *)

Definition tpost_step (K:trace->Prop) : trace->Prop :=
  fun (T:trace) => K (trace_step T).

Definition tpost_app (T:trace) (K:trace->Prop) : trace->Prop :=
  fun T' => K (trace_app T T').

CoInductive tevals : state -> trm -> (trace->Prop) -> Prop :=
  | tevals_val : forall s v K,
      K (trace_return v s) ->
      tevals s (trm_val v) K
  | tevals_fix : forall s f x t1 K,
      K (trace_return (val_fix f x t1) s) ->
      tevals s (trm_fix f x t1) K
  | tevals_app_fix : forall s1 v1 v2 f x t1 K,
      v1 = val_fix f x t1 ->
      tevals s1 (subst x v2 (subst f v1 t1)) K ->
      tevals s1 (trm_app v1 v2) (tpost_step K)
  | tevals_let : forall K1 s1 x t1 t2 K,
      tevals s1 t1 K1 ->
      (forall T1, K1 T1 ->
        forall v1 s2, trace_ends v1 s2 T1 ->
        tevals s2 (subst x v1 t2) (tpost_app T1 K)) ->
        (* (tpost_app T1 K) = (fun T2 => K (trace_app T1 T2))) *)
      tevals s1 (trm_let x t1 t2) K
  | tevals_if : forall s1 b t1 t2 K,
      tevals s1 (if b then t1 else t2) K ->
      tevals s1 (trm_if (val_bool b) t1 t2) (tpost_step K)
  | tevals_add : forall s n1 n2 K,
      K (trace_return (val_int (n1 + n2)) s) ->
      tevals s (val_add (val_int n1) (val_int n2)) K
  | tevals_rand : forall s n K,
      ~ deterministic ->
      n > 0 ->
      (forall n1, 0 <= n1 < n -> K (trace_return n1 s)) ->
      tevals s (val_rand (val_int n)) K
  | tevals_ref : forall s v K,
      (forall p, ~ Fmap.indom s p ->
         (deterministic -> smallest_fresh s p) ->
         K (trace_return (val_loc p) (Fmap.update s p v))) ->
      tevals s (val_ref v) K
  | tevals_get : forall s p K,
      Fmap.indom s p ->
      K (trace_return (Fmap.read s p) s) ->
      tevals s (val_get (val_loc p)) K
  | tevals_set : forall s p v K,
      Fmap.indom s p ->
      K (trace_return val_unit (Fmap.update s p v)) ->
      tevals s (val_set (val_loc p) v) K
  | tevals_free : forall s p K,
      Fmap.indom s p ->
      K (trace_return val_unit (Fmap.remove s p)) ->
      tevals s (val_free (val_loc p)) K.

Definition tpost_ter_or_div (Q:val->hprop) : trace->Prop :=
  fun T => forall v s, trace_ends v s T -> Q v s.

Definition pthoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (s:state), H s -> tevals s t (tpost_ter_or_div Q).


(** TODO:
    prove equivalence of pthoare with small-step partial correctness (pshoare based on psevals)
        tevals s t (tpost_ter_or_div Q) <-> psevals s t Q.
*)

(** Incorrect  equivalence:
        tevals s t (tpost_ter Q) <-> evals s t Q

where

Definition tpost_ter (Q:val->hprop) : trace->Prop :=
  fun T => exists v s, trace_ends v s T /\ Q v s.

Definition thoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (s:state), H s -> tevals s t (tpost_ter Q).

because tevals could relate any trace by coinduction...

*)



Lemma cosevals_let_inv : forall s1 x t1 t2 Q,
  cosevals s1 (trm_let x t1 t2) Q ->
  exists Q1, coevals s1 t1 Q1 (* TODO: pick using epsilon the largest such set, then inverts on that *)
          /\ (forall v1 s2, Q1 v1 s2 -> coevals s2 (subst x v1 t2) Q).
Proof using.
skip.
(*
  introv M. applys or_classic_l. intros N.
  gen s t1. cofix IH. intros.
  inverts M as S M'. inverts S as S'.
  { (* [t1] takes a step to [t1']. *)
    applys sdiverge_step S'. applys IH M'.
    { intros N'. applys N. destruct N' as (s'&v1&M1&M2). exists s' v1. split.
      { applys steps_step S' M1. } { applys M2. } } }
  { (* [t1] reaches a value [v1]: contradicts hypothesis [N] *)
    false N. exists s2 v1. split. { applys steps_refl. } { applys M'. } }
*)
Qed.

  (* TODO ALT { lets (Q1&M1&M2): cosevals_let_inv M. applys coevals_let M1 M2. } *)

  (* not used
Lemma coevals_of_step_and_coevals : forall s1 s2 t1 t2 Q,
  step s1 t1 s2 t2 ->
  coevals s2 t2 Q ->
  coevals s1 t1 Q.
Proof using.
  introv M1 M2. gen s3 v. induction M1; intros.
  { inverts M2 as M3 M4. applys* eval_let. (* applys* IHM1. *) }
  { inverts M2. applys eval_fix. }
  { applys* eval_app_fix. }
  { applys* eval_if. }
  { applys* eval_let. applys eval_val. }
  { inverts M2. applys* eval_add. }
  { inverts M2. applys* eval_rand. }
  { inverts M2. applys* eval_ref. }
  { inverts M2. applys* eval_get. }
  { inverts M2. applys* eval_set. }
  { inverts M2. applys* eval_free. }
skip.
Qed.
*)


(* TEMP
Lemma complete_cases : forall s t,
  (forall v, t <> trm_val v) ->
  (stuck s t) \/ (exists s' t', step s t s' t').
Proof using.
  skip.
Qed.
Lemma complete : forall s t,
  (exists v, t = trm_val v) \/ (exists s' t', step s t s' t').
Proof using.
  intros. tests C: (exists v, t = trm_val v).
  { left*. }
  { right.
*)



    In addition, also for the sake of simplifying the proofs, the semantics
    from [SLFCore] assumes a language in "strong" A-normal form, allowing
    for evaluation contexts to

    [let x = (let y = t1 in t2) in t3] needs to be rewritten as
    [let y = t1 in let x = t2 in t3], with alpha-renaming of [y]
    in case it occurs in [t3]. In that presentation, there is only
    one "context" rule, moreover evaluation context are not recursive.



(* ####################################################### *)
(** ** Definition of [exactevals] to Characterize Non-Deterministic Semantics *)

(** The judgment [evals s t Q] associates with a program configuration
    [(s,t)] an over-approximation of its possible output configurations,
    described by [Q].

    For the purpose of defining of Hoare triple, working with
    over-approximation is perfectly fine. In other contexts, however,
    it might be interesting to characterize exactly the set of output
    configurations.

    To that end, we define the predicate [exactevals s t Q], which relates
    a program configuration [(s,t)] with the smallest possible [Q] for which
    [evals s t Q] holds. As we formalize and prove next, this notion defines
    the set of output configurations is a non-ambiguous manner, and it is
     *)

Definition safes (s:state) (t:trm) : Prop :=
  evals s t (fun v s' => eval s t s' v).

(* definition smallestpost := (fun v s' => eval s t s' v) *)

(** This postcondition describes exactly the set of
    output configurations. *)

Definition exactevals (s:state) (t:trm) (Q:val->hprop) : Prop :=
  evals s t Q /\ (forall Q', evals s t Q' -> Q ===> Q').

(** By definition of [exactevals], if [exactevals s t Q] holds,
    then [Q] is smaller than any [Q'] for which [evals s t Q'] holds. *)

Lemma exactevals_inv_evals_smaller : forall s t Q Q',
  exactevals s t Q ->
  evals s t Q' ->
  Q ===> Q'.
Proof using. introv (M&W) M'. applys W M'. Qed.

(* EX1! (exactevals_unique) *)
(** Prove that [exactevals] associates each program to at most one
    postcondition. In other words, the "smallest" [Q] such that
    [evals s t Q], if it exists, is unique. *)

Lemma exactevals_unique : forall s t Q1 Q2,
  exactevals s t Q1 ->
  exactevals s t Q2 ->
  Q1 = Q2.
Proof using. (* ADMITTED *)
  introv (M1&W1) (M2&W2). applys qimpl_antisym.
  { applys W1 M2. }
  { applys W2 M1. }
Qed. (* /ADMITTED *)

(** [] *)

(** all satisfy Q implies one satisfy Q *)

(* EX2! (evals_inv_eval) *)
(** Assume [evals s t Q] holds, meaning that all executions
    produce output satisfying [Q]. Prove that if a particular
    execution produces a output value [v] in an output state [s'],
    in the sense that [eval s t s' v] holds, then [Q v s'] holds. *)

Lemma evals_inv_eval : forall s t v s' Q,
  evals s t Q ->
  eval s t s' v ->
  Q v s'.
Proof using. (* ADMITTED *)
  introv M R. gen v s'.
  induction M; intros; try solve [inverts* R; tryfalse].
  { inverts R as E; tryfalse. inverts TEMP0. (* TODO: rename *)
    applys* IHM. }
Qed. (* /ADMITTED *)

(** [] *)

(** A similar property holds for [exactevals], as an immediate corollary. *)

Lemma exactevals_inv_eval : forall s t v s' Q,
  exactevals s t Q ->
  eval s t s' v ->
  Q v s'.
Proof using. introv (M&W) R. applys evals_inv_eval M R. Qed.

(** "all correct st Q" implies all correct *)

(** We are now interested in proving that if [evals s t Q] holds for
    some [Q], then there exists a smallest [Q] for which [evals s t Q]
    holds. To establish this result, we need the following key lemma,
    which asserts that this smallest [Q] is witnessed by the set of
    results [(v,s')] to which the program may evaluate to, according
    to the evaluation relation [eval]; i.e., such that [eval s t s' v].
    holds. The proof is relatively direct, except for the case of the
    let-binding, whose proof requires to guess the appropriate
    intermediate invariant. *)

Lemma evals_inv_evals_eval : forall s t Q,
  evals s t Q ->
  safes s t.
Proof using.
  introv M. unfold safes. induction M.
  { applys evals_val. applys eval_val. }
  { applys evals_fix. applys eval_fix. }
  { applys* evals_app_fix. applys evals_conseq IHM.
    { intros v s' R. applys* eval_app_fix R. } }
  { rename IHM into IHM1, H0 into IHM2.
    applys evals_let (fun v1 s' => eval s t1 s' v1 /\ Q1 v1 s').
    { applys evals_conseq IHM1. { intros v1 s' R. split.
      { applys R. }
      { applys evals_inv_eval M R. } } }
    { intros v1 s2 (R1&K). applys evals_conseq. applys IHM2 K.
      { intros v s' R2. applys eval_let R1 R2. } } }
  { applys evals_if. applys evals_conseq IHM.
    { intros v s' R. applys eval_if R. } }
  { applys evals_add. applys eval_add. }
  { applys* evals_rand. intros n1 N1. applys* eval_rand. }
  { applys* evals_ref. intros p Hp HD. applys* eval_ref. }
  { applys* evals_get. applys* eval_get. }
  { applys* evals_set. applys* eval_set. }
  { applys* evals_free. applys* eval_free. }
Qed.

(* EX2! (exists_exactevals_of_evals) *)
(** This last lemma puts it all together.
    Assume [evals s t Q], meaning that all executions of the program
    [(s,t)] are safe and satisfy postcondition [Q]. Then, there exists
    a unique [Q'] that describes precisely the set of output configurations,
    in the sense that [exactevals s t Q'] holds. (Moreover, [Q'] is
    included in [Q], according to exactevals_inv_evals_smaller.) *)

Lemma exists_exactevals_of_evals : forall s t Q,
  evals s t Q ->
  exists! Q', exactevals s t Q'.
Proof using. (* ADMITTED *)
  introv M. sets Q': (fun v s' => eval s t s' v).
  asserts E: (exactevals s t Q').
  { split.
    { applys evals_inv_evals_eval M. }
    { intros Q'' M'. intros v s' R. applys evals_inv_eval M' R. } }
  exists Q'. split. { applys E. } { intros Q'' E'. applys exactevals_unique E' E. }
Qed. (* /ADMITTED *)


(** all correct implies exists one correct (because total correctness) *)


Lemma evals_inv_exists_eval : forall s t Q,
  evals s t Q ->
  exists s' v, eval s t s' v /\ Q v s'.
Proof using.
  introv M.  induction M.
  { exists. split*. applys eval_val. }
  { exists. split*. applys eval_fix. }
  { rename IHM into IHM1, M into M1.
    forwards (s'&v&R&HQ): IHM1.
    exists. split*. applys* eval_app_fix R. }
  { rename IHM into IHM1, H0 into IHM2, M into M1, H into M2.
    forwards (s1'&v1&R1&HQ1): IHM1.
    forwards (s'&v&R2&HQ2): IHM2 HQ1.
    exists. split*. applys eval_let R1 R2. }
  { forwards (s'&v&R1&HQ): IHM.
    exists. split*. applys* eval_if R1. }
  { exists. split*. applys* eval_add. }
  { rename H1 into N.
    exists. split*. applys* eval_rand 0. math. applys N. math. }
  { forwards~ (p&F): (exists_smallest_fresh s). lets (D&_): F.
    exists. split*. applys* eval_ref. }
  { exists. split*. applys* eval_get. }
  { exists. split*. applys* eval_set. }
  { exists. split*. applys* eval_free. }
Qed.


Lemma safes_inv_exists : forall s t,
  safes s t ->
  exists s' v, eval s t s' v.
Proof using.
  introv M. forwards (s'&v&R&_): evals_inv_exists_eval M.
  exists. applys* R.
Qed.


(** A corollary is that if the set of executions is singleton,
    then it matches the result of an execution. *)

Lemma evals_exactly_inv : forall s0 t0 v1 s1,
  evals s0 t0 (exactly v1 s1) ->
  (forall s2 v2, eval s0 t0 s2 v2 <-> (v2 = v1 /\ s2 = s1)).
Proof using.
  introv M. iff R (->&->).
  { applys evals_inv_eval M R. }
  { lets (s'&v&R'&(->&->)): evals_inv_exists_eval M. applys R'. }
Qed.








(* ####################################################### *)
(** ** Interpretation of [evals] for Deterministic Semantics *)

(** In this chapter, we introduced [evals] for characterizing
    the semantics of a non-deterministic language. We discussed
    the particular case of a deterministic program, satisfying
    [evals s t (exactly v s')].

    But what is the
    meaning of the [evals] predicate in the case of language that is
    deterministic? How does this predicate relate to the predicate [eval]?

    In this section, we prove that, for a deterministic language,
    [eval s t s' v] is equivalent to [evals s t Q], where [Q] is
    a "singleton precondition" introduced earlier: [exactly v s'],
    defined as [fun v0 s0 => v0 = v /\ s0 = s']. *)

(** Let us now investigate the proof of the equivalence relating
    [evals] and [eval]. The first direction, from [eval] to [evals],
    is relatively straightforward. *)

Lemma evals_exactly_of_eval_deterministic : forall s t s' v,
  deterministic ->
  eval s t s' v ->
  evals s t (exactly v s').
Proof using.
  hint exactly_intro.
  introv HD M. induction M; try solve [ constructors* ].
  { applys evals_let IHM1. intros ? ? (->&->). applys IHM2. }
  { applys evals_ref. intros p' D S.
    forwards* E: smallest_fresh_unique s p p'. subst*. }
Qed.

(** The other direction, from [eval] to [evals], is more challenging. *)

(* EX3? (eval_of_evals_deterministic) *)
(** Assume a deterministic language. Prove that [evals s t Q]
    implies that [(s,t)] evaluates to a final result [(s',v)]
    that satisfies [Q v s'].
    Hint: for the [val_ref] case, exploit [exists_smallest_fresh]. *)

Lemma eval_of_evals_deterministic : forall s t Q,
  deterministic ->
  evals s t Q ->
  exists v s', Q v s' /\ eval s t s' v.
Proof using. (* ADMITTED *)
  introv HD M. induction M;
    try solve [ do 2 esplit; split; [ eauto | constructors* ] ].
  (* Most cases are resolved by:
    { do 2 esplit; split; [ eauto | constructors* ]. } *)
  { destruct IHM as (v&s'&M1&M2).
    do 2 esplit; split; [ eauto | constructors* ]. }
  { destruct IHM as (v1&s''&K1&M1).
    rename H0 into IHM2. forwards (v&s'&K2&M2): IHM2 K1.
    exists v s'. split.
    { applys K2. }
    { applys eval_let M1 M2. } }
  { destruct IHM as (v&s'&M1&M2).
    do 2 esplit; split; [ eauto | constructors* ]. }
  { false HD. }
  { forwards~ (p&F): (exists_smallest_fresh s). lets (D&_): F.
    exists p (update s p v). split.
    { applys* H. } { applys* eval_ref. } }
Qed. (* /ADMITTED *)

(** [] *)

(** Combining the two results, we derive the desired equivalence. *)

Lemma eval_iff_evals_of_deterministic :
  deterministic ->
  forall s t s' v,
  eval s t s' v <-> evals s t (exactly v s').
Proof using.
  introv HD. intros. iff M.
  { applys* evals_exactly_of_eval_deterministic. }
  { forwards* (v''&s''&K&M'): eval_of_evals_deterministic M.
    destruct K as (->&->). applys M'. }
Qed.

---------------------


(* EX4! (progress) *)
(** Prove the progress property for [psevals]. *)

Lemma progress : forall s1 t1 Q,
  psevals s1 t1 Q ->
     (exists v1, t1 = trm_val v1 /\ Q v1 s1)
  \/ (exists s2 t2, step s1 t1 s2 t2 /\ psevals s2 t2 Q).
Proof using. (* ADMITTED *)
  introv M. forwards N: M s1 t1. { applys steps_refl. }
  destruct N as [(v1&E1&P1)|(s2&t2&R)].
  { left. exists* v1. }
  { right. exists s2 t2. split~. { applys* pevals_inv_step. } }
Qed. (* /ADMITTED *)

(* [] *)





Lemma sdiverges_of_sdiverges_and_step : forall s1 t1 s2 t2,
  sdiverges s1 t1 ->
  step s1 t1 s2 t2 ->
  sdiverges s2 t2.
Proof using.
  introv D M1. unfolds sdiverges. intros s3 t3 M2.
  applys D. { applys steps_step M1 M2. }
Qed.

Lemma cosevals_Empty_inv : forall s t,
  cosevals s t Empty ->
     (exists s' t', step s t s' t')
  /\ (forall s' t', step s t s' t' -> cosevals s' t' Empty).
Proof using.
  introv D. inverts D as.
  { intros K. false. (* if Empty':  unfolds Empty. false* hpure_inv K.*) }
  { auto. }
Qed.

Lemma sdiverges_iff_cosevals_Empty : forall s t,
      sdiverges s t
  <-> cosevals s t Empty.
Proof using.
  iff D.
  { gen s t. cofix IH. introv D.
    applys cosevals_step.
    { applys D. applys steps_refl. }
    { intros s2 t2 M1. applys IH.
      applys sdiverges_of_sdiverges_and_step D M1. } }
  { intros s2 t2 M. induction M.
    { lets (R&_): cosevals_Empty_inv D. applys R. }
    { rename H into M1, M into M2.
      lets (_&D'): cosevals_Empty_inv D.
      specializes D' M1. applys IHM D'. } }
Qed.

Lemma diverges_eq_sdiverges :
   diverges = sdiverges.
Proof using.
  extens. intros s t. unfold diverges.
  rewrite coevals_eq_cosevals.
  rewrite* <- sdiverges_iff_cosevals_Empty.
Qed.



(** proof of cosdiverges_eq_sdiverges *)

Lemma cosdiverges_inv_step : forall s1 t1 s2 t2,
  cosdiverges s1 t1 ->
  step s1 t1 s2 t2 ->
  cosdiverges s2 t2.
Proof using. introv M S. inverts M as M1 M2. applys M2 S. Qed.

Lemma sdiverges_inv_step : forall s1 t1 s2 t2,
  sdiverges s1 t1 ->
  step s1 t1 s2 t2 ->
  sdiverges s2 t2.
Proof using.
  introv M S. intros s3 t3 R. applys M. applys steps_step S R.
Qed.

Lemma cosdiverges_eq_sdiverges :
  cosdiverges = sdiverges.
Proof using.
  extens. intros s t. iff M.
  { introv R. gen M. induction R; intros.
    { inverts M as M1 M2. applys M1. }
    { rename H into S, R into R'.
      lets M': cosdiverges_inv_step M S. applys IHR M'. } }
  { gen s t. cofix IH. introv M. applys cosdiverges_step.
    { applys M s t. applys steps_refl. }
    { introv S. lets M': sdiverges_inv_step M S. applys IH M'. } }
Qed.


(* ####################################################### *)
(** ** Specialization to a Non-Deterministic Language *)

Module NondetTriples.

(** Let us set the flag [deterministic] to [False], so as to
    include the primitive operator [val_rand] in our language. *)

Parameter non_deterministic : ~ deterministic.

Hint Resolve non_deterministic.

(** With this non-deterministic setting, the evaluation rule for [val_rand n] is
    equivalent to the following statement, which indeed captures
    that the output value is between [0] inclusive and [n] exclusive. *)

Lemma eval_rand : forall s n n1,
  0 <= n1 < n ->
  eval s (val_rand (val_int n)) s (val_int n1).
Proof using. introv M. applys eval_rand M. applys non_deterministic. Qed.

(** With the non-deterministic setting for [SLFCore], the evaluation rule
    for [val_ref] is equivalent to the statement it had in the preivous
    chapters. *)

Lemma eval_ref : forall s v p,
  ~ Fmap.indom s p ->
  eval s (val_ref v) (Fmap.update s p v) (val_loc p).
Proof using. introv HD. applys* eval_ref. intros. false* non_deterministic. Qed.





(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Summary --> todo merge text ; make shorter summary *)

Module Summary.


(* ########################################################### *)
(** ** Total correctness **)

(* ########################################################### *)
(** *** Total correctness, big-step *)

(** Total correctness in big-step, for non-deterministic semantics.
    We rely on the inductive definition of [evals s t Q]. *)

Parameter evals : state -> trm -> (val->state->Prop) -> Prop.

Definition nhoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s, H s -> evals s t Q.

(** Total correctness in big-step, for deterministic semantics
    Simplified using the inductive definition of [eval s t s' v], which
    corresponds to [evals s t (fun s0 v0 => s0 = s' /\ v0 = v')],
    as proved in [SLFNondet]. *)

Parameter eval : state -> trm -> state -> val -> Prop.

Definition dhoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s, H s -> exists s' v, eval s t s' v /\ Q v s'.

(** Total correctness in big-step, for complete semantics.
    Nothing simpler than [evals]. If errors are part of the
    semantics, one may use the judgment:
    [evals s t (fun v s' => v <> val_error /\ Q v s')]. *)


(* ########################################################### *)
(** *** Total correctness, small-step *)

(** Total correctness in small-step, for non-deterministic semantics.
    We rely on the inductive definition of [sevals s t Q].
    The judgment [sevals s t Q] is proved equivalent to
    [evals s t Q] in lemma [sevals_eq_sevals] from [SLFNondet]. *)

Parameter step : state -> trm -> state -> trm -> Prop.

Inductive sevals : state->trm->(val->hprop)->Prop :=
  | sevals_val : forall s v Q,
      Q v s ->
      sevals s v Q
  | sevals_step : forall s t Q,
      (exists s' t', step s t s' t') ->
      (forall s' t', step s t s' t' -> sevals s' t' Q) ->
      sevals s t Q.

Definition shoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s, H s -> sevals s t Q.

(** Total correctness in small-step, for complete semantics.
    If the semantics is complete, progress is granted,
    and all we have to check is that programs don't terminate
    on an error. The judgment [csevals s t Q] is proved equivalent
    to [sevals s t Q] for complete semantics by lemma
    [csevals_eq_sevals_of_complete] in [SLFNondet]. *)

Parameter val_error : val. (* TODO *)

(* TODO do this proof : csevals_eq_sevals_of_complete *)

Inductive csevals : state->trm->(val->hprop)->Prop :=
  | csevals_val : forall s v Q,
      v <> val_error ->
      Q v s ->
      csevals s v Q
  | csevals_step : forall s t Q,
      (forall s' t', step s t s' t' -> csevals s' t' Q) ->
      csevals s t Q.

(** Total correctness in small-step, for deterministic semantics.
    There are two possibilities.
    The first possibility is a direct variant of [sevals],
    called [devals s t Q], proved equivalent in lemma
    [sevals_eq_devals_of_deterministic] from [SLFNondet]. *)

Inductive devals : state->trm->(val->hprop)->Prop :=
  | devals_val : forall s v Q,
      Q v s ->
      devals s v Q
  | devals_step : forall s t s' t' Q,
      step s t s' t' ->
      devals s' t' Q ->
      devals s t Q.

(** Total correctness in small-step, for deterministic semantics.
    The second possibility is to use the iterated small-step
    reduction relation [steps s t s' t']. The judgment
    [steps s t s' (trm_val v)] is equivalent to [eval s t s' v],
    as proved in lemma [eval_iff_steps] from [SLFCore].
    The judgment [dshoare] reformulates [dhoare] by replacing
    [eval] with [steps]. *)

Inductive steps : state -> trm -> state -> trm -> Prop :=
  | steps_refl : forall s t,
      steps s t s t
  | steps_step : forall s1 s2 s3 t1 t2 t3,
      step s1 t1 s2 t2 ->
      steps s2 t2 s3 t3 ->
      steps s1 t1 s3 t3.

Definition dshoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s, H s -> exists s' v, steps s t s' (trm_val v) /\ Q v s'.


(* ########################################################### *)
(** ** Partial correctness **)

(* ########################################################### *)
(** *** Partial correctness, big-step *)

(** Partial correctness in big-step, for non-deterministic semantics.
    We rely on the co-inductive counterpart of [evals], written
    [coevals s t Q]. *)

Parameter coevals : state -> trm -> (val->state->Prop) -> Prop.

Definition phoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s, H s -> coevals s t Q.

(** Divergence of all executions is characterized by the empty
    postcondition. *)

Definition Empty : val->state->Prop :=
  fun v s => False.

Definition diverges (s:state) (t:trm) : Prop :=
  coevals s t Empty.

(** Partial correctness in big-step, for complete semantics.
    If no terms are stuck, we may simply use the judgment [eval].
    See also [cpshoare]. *)

Definition cphoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s s' v, H s -> eval s t s' v -> (v <> val_error /\ Q v s').

(* TODO : this is the same as cpshoare, up to eval_iff_steps,
    cpshoare is related to coveals via psevals_eq_cosevals
    and cpshoare related to cosevals of complete. *)

(** Partial correctness in big-step, for deterministic semantics. *)

Definition dphoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s, H s -> (exists s' v, eval s t s' v /\ Q v s') \/ (diverge s t).

(* TODO TODO REMAINING: relate this to the small step version;
   or possibly directly to the big-step version, under hyp deterministic ?
   prove equivalence under deterministic hypothesis with the coevals case. *)

(*
Lemma dphoare_eq_phoare_of_deterministic :
    forall s, H s -> (exists s' v, eval s t s' v /\ Q v s') \/ (diverge s t).
=   forall s, H s -> (exists s' v, steps s t s' v /\ Q v s') \/ (sdiverge s t).

mq  (exists s' v, steps s t s' v /\ Q v s') \/ (sdiverge s t)
  = psevals s t Q

<=) by classic, suppose "not steps", prove sdiverge;
    apply psevals, destruct case, first one is contraction, done.
    (determinacy not needed)
=>) consider a path. cases termination or diverge:
    - case termination: the paths are identical, ends on termination
    - case diverges: applys hypothesis directly.

Definition sdiverges (s:state) (t:trm) : Prop :=
  forall s2 t2, steps s t s2 t2 ->
  exists s3 t3, step s2 t2 s3 t3.

Definition psevals (s1:state) (t1:trm) (Q:val->state->Prop) : Prop :=
  forall s2 t2, steps s1 t1 s2 t2 ->
       (exists v2, t2 = trm_val v2 /\ Q v2 s2)
    \/ (exists s3 t3, step s2 t2 s3 t3).
*)

(* ########################################################### *)
(** *** Partial correctness, small-step *)

(** Partial correctness in small-step, for non-deterministic semantics.
    First approach : use [steps] to express the fact that
    every execution prefix either reaches a value satisfying the
    postcondition, or reaches a term that is not stuck (i.e., whose
    execution can make progress). *)

Definition psevals (s1:state) (t1:trm) (Q:val->state->Prop) : Prop :=
  forall s2 t2, steps s1 t1 s2 t2 ->
       (exists v2, t2 = trm_val v2 /\ Q v2 s2)
    \/ (exists s3 t3, step s2 t2 s3 t3).

(** Partial correctness in small-step, for non-deterministic semantics.
    Second approach : use [cosevals], the coinductive counterpart
    of [sevals], to capture the same property without involving
    the transitive closure relation [steps]. The equivalence between
    the two approaches is captured by lemma [psevals_eq_cosevals]
    in [SLFPartial]. The second approach, namely [cosevals], is
    proved equivalent to the big-step characterizations of partial
    correctness, namely [coevals], by lemma [coevals_eq_cosevals]
    from [SLFPartial]. *)

CoInductive cosevals : state->trm->(val->hprop)->Prop :=
  | cosevals_val : forall s v Q,
      Q v s ->
      cosevals s v Q
  | cosevals_step : forall s t Q,
      (exists s' t', step s t s' t') ->
      (forall s' t', step s t s' t' -> cosevals s' t' Q) ->
      cosevals s t Q.

(** For both approaches, the definition of partial-correctness
    Hoare triples follows the same scheme as the big-step
    definition. *)

Definition pshoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s, H s -> psevals s t Q.

(** Partial correctness in small-step, for complete semantics.
    The judgment [cpshoare t H Q] is expressed in terms of [steps],
    in a similar way to [cphoare t H Q]. The judgment [cpshoare]
    is proved to be equivalent to [pshoare] under the assumption
    that the semantics is complete in lemma
    [cpshoare_eq_pshoare_of_complete], in [SLFPartial]. *)
    (* TODO: do this proof; lemma name won't be this one. *)

Definition cpshoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall s s' v, H s -> steps s t s' (trm_val v) -> (v <> val_error /\ Q v s').

(** Partial correctness in small-step, for deterministic semantics.
    Nothing simpler than [psevals]. *)

(** Divergence of all executions in small step is characterized
    by [sdiverges s t]: all execution prefixes can be extended.
    This characterization is proved equivalent to the big-step
    characterization via [coevals s t Empty], in lemma
    [diverges_eq_sdiverges] from [SLFPartial]. *)

Definition sdiverges (s:state) (t:trm) : Prop :=
  forall s2 t2, steps s t s2 t2 ->
  exists s3 t3, step s2 t2 s3 t3.

End Summary.




(** Here again, total correctness is a stronger property than partial
    correctness. A coinductive interpretation is always derivable from
    an inductive interpretation of a same set of derivation rules. *)

Lemma evalnpcos_of_evalns : forall s t Q,
  evalns s t Q ->
  evalnpcos s t Q.
Proof using. introv M. induction M; try solve [ constructors* ]. Qed.

(** It follows that [hoaren] is stronger than [hoarenpcos]. *)

Lemma hoarens_of_evalnpcos : forall t H Q,
  hoarens t H Q ->
  hoarenpcos t H Q.
Proof using.
  introv M. intros s K. specializes M (rm K). applys evalnpcos_of_evalns M.
Qed.
