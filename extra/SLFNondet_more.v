
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