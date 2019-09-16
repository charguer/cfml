(**

Separation Logic Foundations

Chapter: "WPsem".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Export SLFRules.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ####################################################### *)
(** * The chapter in a rush *)

(** This chapter introduces the notion of weakest precondition
    for Separation Logic triples. *)


(* ******************************************************* *)
(** ** Notion of weakest precondition *)

(** We next introduce a function [wp], called "weakest precondition".
    Given a term [t] and a postcondition [Q], this function computes
    a heap predicate [wp t Q] such that [triple t H Q] holds if and
    only if [wp t Q] is weaker than the precondition [H]. Formally: *)

Parameter wp : trm -> (val->hprop) -> hprop.

Parameter wp_equiv : forall t H Q,
  (triple t H Q) <-> (H ==> wp t Q).

(** The [wp t Q] is called "weakest precondition" for two reasons.
    First, because it is a "valid precondition" for the term [t]
    and the postcondition [Q]: *)

Lemma wp_pre : forall t Q,
  triple t (wp t Q) Q.
Proof using. intros. rewrite wp_equiv. applys himpl_refl. Qed.

(** Second, because it is the "weakest" of all valid preconditions
    for the term [t] and the postcondition [Q], in the sense that
    any other valid precondition [H] entails [wp t Q]. *)

Lemma wp_weakest : forall t H Q,
  triple t H Q ->
  H ==> wp t Q.
Proof using. introv M. rewrite <- wp_equiv. applys M. Qed.

(** As we prove further in this chapter, it is possible to
    define a function [wp] satisfying [wp_equiv]. Formally: *)

Definition wp_characterization (wp:trm->(val->hprop)->hprop) :=
  forall t H Q, (triple t H Q) <-> (H ==> wp t Q).

Parameter wp_characterization_exists : exists wp0,
  wp_characterization wp0.

(** In fact, there are several ways in which [wp] can be defined.
    It turns out that all possible definitions are equivalent.
    In other words, the property captured by [wp_characterization]
    defines a unique function. We next formally justify this fact. *)

Lemma wp_characterization_unique : forall wp1 wp2,
  wp_characterization wp1 ->
  wp_characterization wp2 ->
  wp1 = wp2.
Proof using.
  asserts L: (forall t Q wp1 wp2,
    wp_characterization wp1 ->
    wp_characterization wp2 ->
    wp1 t Q ==> wp2 t Q).
  { introv M1 M2. unfolds wp_characterization.
    rewrite <- M2. rewrite M1. applys himpl_refl. }
  introv M1 M2. applys fun_ext_2. intros t Q.
  applys himpl_antisym; applys L; auto.
Qed.

(** Thus, it really does not matter which definition of [wp] is
    considered. Thereafter, we only exploit the characterization lemma
    [wp_equiv], and never rely on the internal definition of [wp]. *)


(* ******************************************************* *)
(** ** Structural properties of weakest preconditions *)

(** It is interesting to observe how the structural rules
    can be applied on a judgment of the form [H ==> wp t Q].

    At this stage, we'll make three important observations.

    1. The extraction rules [triple_hexists] and [triple_hpure]
       are not needed in a wp-style presentation, because they
       are directly subsumed by basic lemmas on entailment.

    2. The combined consequence-frame-htop rule for [triple]
       has a counterpart for [wp]. This rule is, in effect,
       the unique structural rule that is needed for [wp].
       (All other structural rules are derivable from it.)

    3. The ramified-frame rule for [triple] also has a
       counterpart for [wp]. This ramified rule for [wp]
       will play a crucial rule in the construction of the function
       that computes weakest precondition in the next chapter. *)


(* ------------------------------------------------------- *)
(** *** 1. Extraction rules are no longer needed *)

(** Recall the extraction rule for existentials: *)

Parameter triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (\exists x, J x) Q.

(** Replacing [triple t H Q] with [H ==> wp t Q] yields: *)

Lemma triple_hexists_in_wp : forall t Q A (J:A->hprop),
  (forall x, (J x ==> wp t Q)) ->
  (\exists x, J x) ==> wp t Q.

(** This implication is just a special case of the lemma
    [himpl_hexists_l], which proves [(\exists x, J x) ==> H]
    from [forall x, (J x ==> H)]. *)

Proof using. introv M. applys himpl_hexists_l M. Qed.

(** In other words, in the [wp] presentation, we don't need
    a specific extraction rule for existentials, because the
    extraction rule for entailment already does the job. *)

(** Likewise for [triple_hpure], which enables extracting pure
    facts from precondition: the rule [himpl_hstar_hpure_l] may be
    used to prove [\[P] \* H1 ==> H2] from [\[P] -> H1 ==> H2]. *)


(* ------------------------------------------------------- *)
(** *** 2. Combined structural rule for [wp] *)

(** Recall the combined consequence-frame-htop rule for [triple]. *)

Parameter triple_conseq_frame_htop : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \Top ->
  triple t H Q.

(** Let us reformulate this rule using [wp]:

[[
    H1 ==> wp t Q1 ->
    H ==> H1 \* H2 ->
    Q1 \*+ H2 ===> Q \*+ \Top ->
    H ==> wp t Q.
]]

   The beove statement can be simplified by substituting [H]
   with [H1 \* H2], then substituting [H1] with [wp t Q1].
   We obtain:

[[
    Q1 \*+ H2 ===> Q \*+ \Top ->
    (wp t Q1) \* H2 ==> wp t Q.
]]
   After renaming [H2] into [H] and [Q] into [Q2], we arrive at
   the combined rule for [wp]:
*)

Lemma wp_conseq_frame_htop : forall t H Q1 Q2,
  Q1 \*+ H ===> Q2 \*+ \Top ->
  (wp t Q1) \* H ==> (wp t Q2).
Proof using.
  introv M. rewrite <- wp_equiv.
  applys triple_conseq_frame_htop (wp t Q1) M.
  { rewrite wp_equiv. xsimpl. } { xsimpl. }
Qed.

(** The above statement asserts that:

    1. [wp t Q1] can absorb any heap predicate [H] with which it
      is starred, changing it to [wp t (Q1 \*+ H)].

    2. [wp t Q1] can be weakened to [wp t Q2] when [Q1 ===> Q2].

    3. [wp t (Q1 \*+ H)] can be simplified to [wp t Q1] if one
      wants to discard [H] from the postcondition. *)

(** Further in this chapter, we present specializations of
    this rule, e.g., to invoke only the [frame] rule, or only the
    garbage collection rule. *)


(* ------------------------------------------------------- *)
(** *** 3. The ramified structural rule for [wp] *)

(** Consider the entailment [Q1 \*+ H ===> Q2 \*+ \Top]
    that appears in the combined rule [wp_conseq_frame_htop].

    This entailement can be rewritten using the magic wand as:
    [H ==> (Q1 \--* (Q2 \*+ \Top))].

    Thus, the conclusion [(wp t Q1) \* H ==> (wp t Q2)]
    can be reformulated as
    [(wp t Q1) \* (Q1 \--* (Q2 \*+ \Top)) ==> (wp t Q2)].

    The "ramified combined structural rule" for [wp], shown below,
    captures in a single line all the structural properties of [wp]. *)

Lemma wp_ramified : forall t Q1 Q2,
  (wp t Q1) \* (Q1 \--* Q2 \*+ \Top) ==> (wp t Q2).
Proof using. intros. applys wp_conseq_frame_htop. xsimpl. Qed.

(** The following specialization is useful to apply only frame. *)

Lemma wp_ramified_frame : forall t Q1 Q2,
  (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).
Proof using. intros. applys wp_conseq_frame_htop. xsimpl. Qed.

(** The following reformulation is handy to apply on any goal
    of the form [H ==> wp t Q]. *)

Lemma wp_ramified_trans : forall t H Q1 Q2,
  H ==> (wp t Q1) \* (Q1 \--* Q2 \*+ \Top) ->
  H ==> (wp t Q2).
Proof using. introv M. xchange M. applys wp_ramified. Qed.



(* ####################################################### *)
(** * Realization of [wp], and structural properties *)

(* ******************************************************* *)
(** ** Semantic definition of weakest precondition *)

(** The lemma [wp_equiv] asserts [(triple t H Q) <-> (H ==> wp t Q)].
    We have seen in the introduction of this chapter that [wp_equiv]
    defines a unique function [wp]. There remains to show that there
    actually exists at least one such function.

    Recall the definition of [wp_characterization].
[[
    Definition wp_characterization (wp:trm->(val->hprop)->hprop) :=
      forall t H Q, (triple t H Q) <-> (H ==> wp t Q).
]]
*)

(** In what follows, we'll give two possible definitions, a
    low-level one expressed as a function on heaps, and a high-level
    one expressed using only Separation Logic combinators.
    For both, we'll show that they satisfy [wp_characterization].

    Note that, by lemma [wp_characterization_unique], the two
    definitions that we consider are necessarily equivalent to
    each other. *)

(** The low-level definition of [wp t Q] is a predicate that
    characterizes a heap [h] if and only if [triple t (=h) Q]
    holds, where [=h] is a heap predicate that holds only of
    the heap [h]. *)

Definition wp_low (t:trm) (Q:val->hprop) : hprop :=
  fun (h:heap) => triple t (=h) Q.

Lemma wp_equiv_wp_low : wp_characterization wp_low.
  (** [forall t H Q, (triple t H Q) <-> (H ==> wp_low t Q)]. *)
Proof using.
  (** This proof is a bit technical, it is not required to follow it.
      It requires the lemma [triple_named_heap] established
      as exercise in an earlier chapter. *)
  unfold wp_low. iff M.
  { intros h K. applys triple_conseq M.
    { intros h' ->. applys K. }
    { applys qimpl_refl. } }
  { applys triple_named_heap. intros h K.
    applys triple_conseq (=h) Q.
    { specializes M K. applys M. }
    { intros ? ->. auto. }
    { applys qimpl_refl. } }
Qed.

(** The high-level definition of [wp t Q] is defined as
    the existence of a heap predicate [H] such that [H] holds
    of the current heap and the judgment [triple t H Q] holds. *)

Definition wp_high (t:trm) (Q:val->hprop) : hprop :=
  \exists (H:hprop), H \* \[triple t H Q].

(* EX3! (wp_equiv_wp_high) *)
(** Prove that this second definition of [wp] statisfies
    the characteristic property [wp_equiv]. *)

Lemma wp_equiv_wp_high : wp_characterization wp_high.
  (** [forall t H Q, (triple t H Q) <-> (H ==> wp_high t Q)]. *)
Proof using.
(* SOLUTION *)
  unfold wp_characterization, wp_high. iff M.
  { xsimpl H. apply M. }
  { applys triple_conseq Q M.
    { applys triple_hexists. intros H'.
      rewrite hstar_comm. applys triple_hpure.
      intros N. applys N. }
    { applys qimpl_refl. } }
(* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Specialized versions of the structural rule for [wp] *)

(** The combined structural rule for [wp] captures all the
    structural rules. We here discuss the formulation of
    specializations of this rule. The corresponding lemmas
    highlight interesting properties of the [wp] operator. *)

(** One important property of [wp] is its covariance, which
    corresponds to the rule of consequence for [wp]. It asserts
    that [wp t Q] is covariante in [Q], as we state and prove next. *)

Lemma wp_conseq : forall t Q1 Q2,
  Q1 ===> Q2 ->
  wp t Q1 ==> wp t Q2.
Proof using.
  introv M. lets N: wp_ramified t Q1 Q2. xchanges N. xchanges M.
Qed.

(** How can this rule simulate the rule of consequence, which also
    enables strenthening the precondition? The following lemma
    provides the answer: strenghtening of the precondition simply
    consists of invoking the transitivy property of entailment. *)

Lemma wp_conseq_pre : forall t H' H Q,
  H' ==> wp t Q ->
  H ==> H' ->
  H ==> wp t Q.
Proof using. introv M WH. applys himpl_trans WH. applys M. Qed.

(** More generally, the consequence rule for goals in [wp] form
    can be written in a form reminiscent of [triple_conseq]: *)

Lemma wp_conseq_trans : forall t H' Q' H Q,
  H' ==> wp t Q' ->
  H ==> H' ->
  Q' ===> Q ->
  H ==> wp t Q.
Proof using. introv M WH WQ. xchange WH. xchange M. applys wp_conseq WQ. Qed.

(** Thereafter, we present rules in the form of entailments between [wp],
    that is, [wp ... ==> wp ...], but keep in mind that this presentation
    is equivalent to the form: [forall H, H ==> wp ... -> H ==> wp ...]. *)

(** The frame rule for [wp] asserts that, given [(wp t Q) \* H],
    the [wp] may absorb [H] and yield [(wp t (Q \*+ H)]. *)

Lemma wp_frame : forall t H Q,
  (wp t Q) \* H ==> wp t (Q \*+ H).
Proof using.
  intros. rewrite <- wp_equiv.
  applys triple_frame. rewrite~ wp_equiv.
Qed.

(** The garbage collection in precondition for [wp] asserts that
    [wp] can absorb and discard any desired heap predicate [H]
    that sits next to it (i.e., that it is starred with). *)

Lemma wp_hany_pre : forall t H Q,
  (wp t Q) \* H ==> wp t Q.
Proof using.
  intros. rewrite <- wp_equiv.
  applys triple_hany_pre. rewrite~ wp_equiv.
Qed.

(** The garbage collection in postconditions for [wp] asserts
    that [wp] can absorb and discard any desired heap predicate
    [H] that appears in its postcondition. *)

Lemma wp_hany_post : forall t H Q ,
  wp t (Q \*+ H) ==> wp t Q.
Proof using.
  intros. rewrite <- wp_equiv.
  applys triple_hany_post. rewrite~ wp_equiv.
Qed.

(** Note, equivalently, the [H] from rules [wp_hany_pre] and
   [wp_hand_post] may be replaced with [\Top]. *)


(* ####################################################### *)
(** * Definition of [wp] directly in terms of [hoare] *)

(* ******************************************************* *)
(** ** Motivation for direct definitions for [wp] rules *)

(** In our construction, we have proved reasoning rules for
    [hoare], derived reasoning rules for [triple], then used
    the latter for proving the soundness of [wp].

    Yet, if our goal was only to prove properties [wp], we wouldn't
    need any result on [triple]. How would the reasoning rules be
    stated and proved if we were to directly state and prove [wp]
    properties from [hoare]? Let us investigate. *)

(** We assume [wp] to be defined [wp] to be defined directly in terms
    of [hoare], following the definition of [wp_high] from above. *)

Parameter wp_def : forall t Q,
  wp t Q = \exists H, H \* \[forall H', hoare t (H \* H') (Q \*+ H' \*+ \Top)].

(** We first establish the (most-general) structural rule for [wp],
    directly with respect to the [hoare] judgment. *)

Lemma wp_ramified' : forall t Q1 Q2,
  (wp t Q1) \* (Q1 \--* Q2 \*+ \Top) ==> (wp t Q2).
Proof using.
  intros. do 2 rewrite wp_def. xpull ;=> H M.
  xsimpl (H \* (Q1 \--* Q2 \*+ \Top)). intros H'.
  applys hoare_conseq M; xsimpl.
Qed.

(** We next establish [wp] reasoning rules for each term construct.

    To guide us towards the appropriate statements, we start from the
    rule for [triple], and reformulate it using the equivalence
    [triple t H Q <-> H ==> (wp t Q)]. *)


(* ******************************************************* *)
(** ** Weakest precondition for values and functions *)

(** First, consider a value [v]. Recall the rule [triple_val],
    which asserts that [H ==> Q v] is a sufficient condition for
    establishing [triple t (trm_val v) H Q]. *)

Parameter triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.

(** Equivalently, [H ==> Q v] is a sufficient condition to establish
    [H ==> wp (trm_val) Q]. Since this implication holds for any [H],
    it holds in particular for [H := Q v]. Thus, the entailement
    [Q v ==> wp (trm_val v) Q] holds. Let us formalize the statement,
    then prove it directly in terms of the [hoare] reasoning rule for
    values. *)

Lemma wp_val : forall v Q,
  Q v ==> wp (trm_val v) Q.
Proof using. intros. rewrite wp_def. xsimpl; intros H'. applys hoare_val. xsimpl. Qed.

(** Interestingly, we have not lost any expressive power: from [wp_val]
    one can recover [triple_val]. *)

Lemma triple_val_derived_from_wp_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using. introv M. rewrite wp_equiv. xchange M. applys wp_val. Qed.

(** The [wp] rules for [trm_fun] and [trm_fix] follow the exact same pattern. *)

Lemma wp_fun : forall x t Q,
  Q (val_fun x t) ==> wp (trm_fun x t) Q.
Proof using. intros. rewrite wp_def. xsimpl; intros H'. applys hoare_fun. xsimpl. Qed.

Lemma wp_fix : forall f x t Q,
  Q (val_fix f x t) ==> wp (trm_fix f x t) Q.
Proof using. intros. rewrite wp_def. xsimpl; intros H'. applys hoare_fix. xsimpl. Qed.


(* ******************************************************* *)
(** ** Weakest precondition for conditionals *)

(** Consider a term [triple_if b t1 t2]. Recall the reasoning rule. *)

Parameter triple_if_case : forall b t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if (val_bool b) t1 t2) H Q.

(** Replacing [triple] using [wp] entailements yields:

[[
    H ==> wp (if b then t1 else t2) Q ->
    H ==> wp (trm_if (val_bool b) t1 t2) Q.
]]
    which simplifies to:
[[
    wp (if b then t1 else t2) Q ==> wp (trm_if (val_bool b) t1 t2) Q.
]]
    This suggests.
*)

Lemma wp_if : forall b t1 t2 Q,
  wp (if b then t1 else t2) Q ==> wp (trm_if b t1 t2) Q.
Proof using.
  intros. repeat rewrite wp_def. xsimpl; intros H M H'.
  applys hoare_if_case. applys M.
Qed.

(** Equivalently, the rule may be stated with the conditional around
    the calls to [wp t1 Q] and [wp t2 Q]. *)

Lemma wp_if' : forall b t1 t2 Q,
  (if b then wp t1 Q else wp t2 Q) ==> wp (trm_if b t1 t2) Q.
Proof using. intros. applys himpl_trans wp_if. case_if~. Qed.

(** Once again, let us check that we have not lost expressive power.
    We prove [triple_if_case] only from [wp_if] and structural properties
    of [wp]. Observe the transitivity step. *)

Lemma triple_if_case_from_wp_if : forall b t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if (val_bool b) t1 t2) H Q.
Proof using.
  introv M. rewrite wp_equiv in *. xchange M.
  applys himpl_trans wp_if. auto.
Qed.


(* ******************************************************* *)
(** ** Weakest precondition for sequence and let-bindings *)

(** Consider a sequence [trm_seq t1 t2]. Recall the rule [triple_seq]. *)

Parameter triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.

(** Replacing [triple t H Q] with [H ==> wp t Q] throughout the rule gives:

[[
      H ==> (wp t1) (fun v => H1) ->
      H1 ==> (wp t2) Q ->
      H ==> wp (trm_seq t1 t2) Q.
]]
    This entailment holds for any [H] and [H1]. Let us specialize it to
    [H1 := (wp t2) Q] and [H := (wp t1) (fun v => (wp t2) Q)].
    This leads us to the wp-style reasoning rule for sequences.
    Again, we provide a direct proof from [hoare] triples. *)

Lemma wp_seq : forall t1 t2 Q,
  wp t1 (fun r => wp t2 Q) ==> wp (trm_seq t1 t2) Q.
Proof using.
  intros. rewrite wp_def. xsimpl. intros H' M1.
  rewrite wp_def. xsimpl. intros H''.
  applys hoare_seq. applys (rm M1). rewrite wp_def.
  repeat rewrite hstar_hexists. applys hoare_hexists; intros H'''.
  rewrite (hstar_comm H'''); repeat rewrite hstar_assoc.
  applys hoare_hpure; intros M2. applys hoare_conseq M2; xsimpl.
Qed.

(* EX2! (triple_seq_from_wp_seq) *)
(** Once again, let us check that we have not lost expressive power.
    Prove [triple_seq] only from [wp_seq] and structural properties
    of [wp]. *)

Lemma triple_seq_from_wp_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof using.
(* SOLUTION *)
  introv M1 M2. rewrite wp_equiv in *. xchange M1.
  applys himpl_trans wp_seq. applys wp_conseq. intros _. applys M2.
(* /SOLUTION *)
Qed.

(** The rule of [trm_let x t1 t2] is very similar, the main difference
    being the substitution on [t2]. *)

Lemma wp_let : forall x t1 t2 Q,
  wp t1 (fun v => wp (subst x v t2) Q) ==> wp (trm_let x t1 t2) Q.
Proof using.
  intros. rewrite wp_def. xsimpl. intros H' M1.
  rewrite wp_def. xsimpl. intros H''.
  applys hoare_let. applys (rm M1). intros v. simpl. rewrite wp_def.
  repeat rewrite hstar_hexists. applys hoare_hexists; intros H'''.
  rewrite (hstar_comm H'''); repeat rewrite hstar_assoc.
  applys hoare_hpure; intros M2. applys hoare_conseq M2; xsimpl.
Qed.


(* ******************************************************* *)
(** ** Weakest precondition for applications *)

(** Recall the rule [triple_app_fun]. *)

Parameter triple_app_fun : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.

(** The corresponding wp-style rule is stated and proved next. *)

Lemma wp_app_fun : forall x v1 v2 t1 Q,
  v1 = val_fun x t1 ->
  wp (subst x v2 t1) Q ==> wp (trm_app v1 v2) Q.
Proof using.
  introv EQ1. repeat rewrite wp_def. xsimpl. intros.
  applys* hoare_app_fun.
Qed.

(** Similarly, the weakest-precondition rule for recursive function
    is stated and proved next. *)

Lemma wp_app_fix : forall f x v1 v2 t1 Q,
  v1 = val_fix f x t1 ->
  wp (subst x v2 (subst f v1 t1)) Q ==> wp (trm_app v1 v2) Q.
Proof using.
  introv EQ1. repeat rewrite wp_def. xsimpl. intros.
  applys* hoare_app_fix.
Qed.


(* ####################################################### *)
(** * Bonus: Texan triples *)

(* ******************************************************* *)
(** ** Texan triples on a simple example *)

(** In this section, we show that specification triples can be presented
    in a different (yet equivalent) style using weakest preconditions. *)

(** Consider for example the specification triple for allocation. *)

Parameter triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists (l:loc), \[r = val_loc l] \* l ~~~> v).

(** This specification can be equivalently reformulated in the form: *)

Parameter wp_ref : forall Q v,
  \[] \* (\forall l, l ~~~> v \-* Q (val_loc l)) ==> wp (val_ref v) Q.

(** Above, we purposely left the empty heap predicate to the front to
    indicate where the precondition, if it were not empty, would go in
    the reformulation. *)

(** In what follows, we describe the chain of transformation that can take us
    from the triple form to the wp form, and establish the reciprocal.
    We then formalize the general pattern for translating a triple
    into a "texan triple" (i.e., the wp-based specification). *)

(** By replacing [triple t H Q] with [H ==> wp t Q], the specification
    gets reformulated as: *)

Lemma wp_ref_0 : forall v,
  \[] ==> wp (val_ref v) (fun r => \exists l, \[r = val_loc l] \* l ~~~> v).
Proof using. intros. rewrite <- wp_equiv. applys triple_ref. Qed.

(** The statement can be reformulated with the aim of making the RHS of the
    form [wp (val_ref v) Q] for an abstract [Q]. *)

Lemma wp_ref_1 : forall Q v,
  ((fun r => \exists l, \[r = val_loc l] \* l ~~~> v) \--* Q) ==> wp (val_ref v) Q.
Proof using. intros. xchange (wp_ref_0 v). applys wp_ramified_frame. Qed.

(** This statement can be further reformulated by quantifying [r] with a [\forall],
    which essentially amounts to unfolding the definition of [\--*]. *)

Lemma wp_ref_2 : forall Q v,
  (\forall r, (\exists l, \[r = val_loc l] \* l ~~~> v) \-* Q r) ==> wp (val_ref v) Q.
Proof using. intros. applys himpl_trans wp_ref_1. xsimpl. Qed.

(** The point is that now we may eliminate [r]: *)

Lemma wp_ref_3 : forall Q v,
  (\forall l, l ~~~> v \-* Q (val_loc l)) ==> wp (val_ref v) Q.
Proof using.
  intros. applys himpl_trans wp_ref_2.
  xsimpl. intros ? l ->. xchange (hforall_specialize l).
Qed.


(* ------------------------------------------------------- *)
(** *** 2. The general pattern *)

(** In practice, specification triples can (pretty much) all be casted
    in the form: [triple t H (fun r => exists x1 x2, \[r = v] \* H'].
    The value [v] may depend on the [xi].
    The heap predicate [H'] may depend on [r] and the [xi].
    The number of existentials [xi] may vary, possibly be zero.
    The equality \[r = v] may degenerate to \[r = r] if no pure fact
    is needed about [r].

    A triple of the above form may be reformulated as:
    [(\forall x1 x2, H \-* Q v) ==> wp t Q].

    We next formalize this result for the case of a single [xi] variable,
    making it explicit that [H] and [v] may depend on it. *)

Lemma texan_triple_equiv : forall t H A (Hof:val->A->hprop) (vof:A->val),
      (triple t H (fun r => \exists x, \[r = vof x] \* Hof r x))
  <-> (forall Q, H \* (\forall x, Hof (vof x) x \-* Q (vof x)) ==> wp t Q).
Proof using.
  intros. rewrite wp_equiv. iff M.
  { intros Q. xchange M. applys wp_ramified_trans.
    xsimpl. intros r x ->. xchanges (hforall_specialize x). }
  { applys himpl_trans M. xsimpl~. }
Qed.


(* ------------------------------------------------------- *)
(** *** 3. Exercise *)

(** Recall the function [incr] and its specification. *)

Parameter incr : val. (** Code omitted, may be found in [SLFHprop.v]. *)

Parameter triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1))).

(* EX2! (wp_incr) *)
(** State a Texan triple for [incr] as a lemma [wp_incr],
    then prove this lemma from [triple_incr].

    Hint: the proof is a bit easier by first turning the [wp] into a [triple]
    and then reasoning about triples, compared than working on the [wp] form. *)

(* SOLUTION *)
Lemma wp_incr : forall (p:loc) (n:int) Q,
  (p ~~~> n) \* (p ~~~> (n+1) \-* Q val_unit) ==> wp (trm_app incr p) Q.
Proof using.
  intros. rewrite <- wp_equiv. applys triple_conseq_frame.
  { applys triple_incr. } { xsimpl. } { xsimpl ;=> ? ->. auto. }
Qed.
(* /SOLUTION *)



(* ******************************************************* *)
(** ** Chapter's notes *)

(** Texan triples are used in Iris. *)

