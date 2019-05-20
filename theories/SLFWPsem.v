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

(** As prove further in this chapter, it is possible to 
    define a function [wp] satisfying [wp_equiv]. Formally: *)

Definition wp_characterization (wp:trm->(val->hprop)->hprop) :=
  forall t H Q, (triple t H Q) <-> (H ==> wp t Q).

Parameter wp_characterization_exists : exists wp0,
  wp_characterization wp0.

(** In fact, there are several ways in which [wp] can be defined.
    It turns out that all possible definitions are equivalent.
    In other words, [wp_equiv] defines a unique function.
    We next formally justify this fact. *)

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

    At this stage, we'll make four important observations.

    1. The extraction rules [triple_hexists] and [triple_hpure]
       are not needed in a wp-style presentation, because they
       are directly subsumed by basic lemmas on entailment.

    2. The predicate [wp t Q] is covariant in [Q], just the same
       way [triple t H Q] is covariant in [Q] (and contravariant 
       in [H]).

    3. The combined consequence-frame-htop rule for [triple]
       has a counterpart for [wp]. This rule is, in effect,
       the unique structural rule that is needed for [wp].
       (All other structural rules are derivable from it.)

    4. The ramified-frame rule for [triple] also has a
       counterpart for [wp]. This ramified rule for [wp]
       will play a crucial rule in the construction of
       our function that computes weakest precondition. *)

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
(** *** 2. Covariance of [wp] *)

(** If we have [triple t H Q1] and [Q1 ===> Q2], then, by the
    rule of consequence, we can derive [triple t H Q2]. 
    In other words, [triple t H Q] is covariant in [Q].

    In a similiar way [wp t Q] is covariant in [Q], as we state
    and prove next. *)

Lemma wp_conseq : forall t Q1 Q2,
  Q1 ===> Q2 ->
  wp t Q1 ==> wp t Q2.
Proof using.
  introv WQ.
  rewrite <- wp_equiv. (* same as [applys wp_weakest]. *)
  applys triple_conseq (wp t Q1) WQ.
  { rewrite wp_equiv. auto. (* same as [applys wp_pre]. *) }
  { applys himpl_refl. }
Qed.


(* ------------------------------------------------------- *)
(** *** 3. Combined structural rule for [wp] *)

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
  { rewrite wp_equiv. hsimpl. } { hsimpl. }
Qed.

(** Further in this chapter, we present specializations of
    this rule to invoke only the [frame] rule, or only the
    garbage collection rule. *)


(* ------------------------------------------------------- *)
(** *** 4. The ramified structural rule for [wp] *)

(** Consider the entailment  [Q1 \*+ H ===> Q2 \*+ \Top]
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
Proof using.
  intros. applys wp_conseq_frame_htop.
  hsimpl. (* exploiting [qwand_cancel] *)
Qed.

(** The following reformulation is handy to apply on any goal
    of the form [H ==> wp t Q]. *)

Lemma wp_ramified_trans : forall t H Q1 Q2,
  H ==> (wp t Q1) \* (Q1 \--* Q2 \*+ \Top) ->
  H ==> (wp t Q2).
Proof using. introv M. hchange M. applys wp_ramified. Qed.



(* ####################################################### *)
(** * Additional contents *)

(* ******************************************************* *)
(** ** Semantic definition of weakest precondition *)

(** We have seen that [wp_equiv] defines a unique function [wp].
    There remains to show that there actually exists at least
    one such function.

    In what follows, we'll give two possible definitions, a
    low-level one expressed as a function on heaps, and a high-level
    one expressed using only Separation Logic combinators.

    For both, we'll show that they satisfy [wp_equiv]. Thus, the
    two definitions must be equivalent ([wp_characterization_unique]). *)

(** We now present the low-level definition. *)

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

(** We now present the high-level definition. *)

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
  { hsimpl H. apply M. }
  { applys triple_conseq Q M.
    { applys triple_hexists. intros H'.
      rewrite hstar_comm. applys triple_hpure. 
      intros N. applys N. }
    { applys qimpl_refl. } }
(* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Frame rule and garbage rules for [wp] *)

(** The combined structural rule for [wp] captures all the
    structural rules. We here discuss the formulation of
    specializations of this rule. The corresponding lemmas
    highlight interesting properties of the [wp] operator. *)

(** Recall the [wp_conseq] rule. *)

Parameter wp_conseq' : forall t Q1 Q2,
  Q1 ===> Q2 ->
  wp t Q1 ==> wp t Q2.

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
    takes the form: *)

Lemma wp_conseq_trans : forall t H' Q' H Q,
  H' ==> wp t Q' ->
  H ==> H' ->
  Q' ===> Q ->
  H ==> wp t Q.
Proof using. introv M WH WQ. hchange WH. hchange M. applys wp_conseq WQ. Qed.

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




