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

(** In the previous chapter, we have introduced the notion of
    Separation Logic triple, written [triple t H Q].

    In this chapter, we introduce the notion of weakest precondition
    for Separation Logic triples, written [wp t Q].

    The intention is for [wp t Q] to be a heap predicate (of type [hprop])
    such that [H ==> wp t Q] if and only if [triple t H Q] holds.

    The benefits of introducing weakest preconditions is two-fold:

    - the use of [wp] greatly reduces the number of structural rules
      required, and reduces accordingly the number of different tactics
      required for carrying out proofs in practice.
    - the predicate [wp] will be used in the next chapter to enable a
      simpler set up of a "characteristic formula generator", the key
      ingredient of CFML's technology for carrying out proofs in practice.

    This chapter presents:

    - the notion of weakest precondition, as captured by [wp],
    - the reformulation of structural rules in [wp]-style,
    - the reformulation of reasoning rules in [wp]-style,
    - (optional) different possible definitions for [wp],
      and alternative ways to derive [wp]-style reasoning rules.

*)


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

(** There are several ways to define [wp]. It turns out that all
    definitions are provably equivalent. In other words, the
    equivalence [(triple t H Q) <-> (H ==> wp t Q)] characterizes
    a unique predicate [wp].

    The details of the possible direct definitions for [wp] are
    irrelevant to the main focus of this chapter, hence we postpone
    the related discussion to the appendix. *)


(* ******************************************************* *)
(** ** Structural rules in weakest-precondition style *)

(** We next discuss formulations of the frame rule and of the rule
    of consequence in weakest-precondition style. *)


(* ------------------------------------------------------- *)
(** *** The frame rule *)

(** The frame rule for [wp] asserts that [(wp t Q) \* H] entails
    [wp t (Q \*+ H)]. This statement can be read as follows:
    if you own both a piece of state satisfying [H] and a piece of state
    in which the execution of [t] produces [Q], then you own a piece
    of state in which the execution of [t] produces [Q \*+ H], that is,
    produces both [Q] and [H]. *)

Lemma wp_frame : forall t H Q,
  (wp t Q) \* H ==> wp t (Q \*+ H).

(** The lemma is proved by exploiting the frame rule for triples
    and the equivalence that characterizes [wp]. *)

Proof using.
  intros. rewrite <- wp_equiv.
  applys triple_frame. rewrite* wp_equiv.
Qed.

(** The connection with the frame is not be totally obvious.
    Recall the frame rule for triples.

[[
    triple t H1 Q ->
    triple t (H1 \* H) (Q \*+ H)
]]
    Let us replace the form [triple t H Q] with the form
    [H ==> wp t Q]. We obtain the following statement: *)

Lemma wp_frame_trans : forall t H1 Q H,
  H1 ==> wp t Q ->
  (H1 \* H) ==> wp t (Q \*+ H).

(** If we exploit transitivity to eliminate [H1], we obtain
    exactly [wp_frame]. *)

Proof using. introv M. xchange M. applys* wp_frame. Qed.


(* ------------------------------------------------------- *)
(** *** The rule of consequence *)

(** The rule of consequence for [wp] materializes as a covariance
    property: asserting that [wp t Q] is covariante in [Q].
    In other words, if one weakens [Q] then one weakens [wp t Q].
    Formally: *)

Lemma wp_conseq : forall t Q1 Q2,
  Q1 ===> Q2 ->
  wp t Q1 ==> wp t Q2.
Proof using.
  introv M. rewrite <- wp_equiv. applys* triple_conseq (wp t Q1) M. applys wp_pre.
Qed.

(** The connection with the rule of consequence is, again, not so obvious.
    Recall the rule of consequence.

[[
    triple t H1 Q1 ->
    H2 ==> H1 ->
    Q1 ===> Q2 ->
    triple t H2 Q2
]]
    Let us replace the form [triple t H Q] with the form [H ==> wp t Q].
    We obtain the following statement: *)

Lemma wp_conseq_trans : forall t H1 H2 Q1 Q2,
  H1 ==> wp t Q1 ->
  H2 ==> H1 ->
  Q1 ===> Q2 ->
  H2 ==> wp t Q2.

(** As we prove, this result is a corrolary [wp_conseq] and
    transitivity of entailement. *)

Proof using.
  introv M WH WQ. xchanges WH. xchanges M. applys wp_conseq WQ.
Qed.


(* ------------------------------------------------------- *)
(** *** The extraction rules *)

(** The extraction rules [triple_hpure] and [triple_hexists]
    have no specific counterpart with the [wp] presentation.
    Indeed, these extraction rules are already captured by
    the extraction rules for entailement.

    To see why, consider for example the rule [triple_hpure]. *)

Parameter triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.

(** Replacing the form [triple t H Q] with [H ==> wp t Q] yields: *)

Lemma triple_hpure_with_wp : forall t H Q (P:Prop),
  (P -> (H ==> wp t Q)) ->
  (\[P] \* H) ==> wp t Q.

(** The above implication is just a special case of the extraction
    lemma for pure facts on the left on an entailment, named
    [himpl_hstar_hpure_l], which asserts:
[[
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.
]]
    Indeed:
*)

Proof using. introv M. applys himpl_hstar_hpure_l M. Qed.

(** A similar reasoning applies to the extraction rule for existentials. *)


(* ******************************************************* *)
(** ** Reasoning rules for terms, in weakest-precondition style *)

(* ------------------------------------------------------- *)
(** *** Rule for values *)

(** Recall the rule [triple_val] which gives a reasoning rule for
    establishing a triple for a value [v]. *)

Parameter triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.

(** If we rewrite this rule in [wp] style, we obtain:
[[
    H ==> Q v ->
    H ==> wp (trm_val v) Q.
]]
    By exploiting transitivity of entailment, we can eliminate [H].
    We obtain the following statement, which reads as follows:
    if you own a state satisfying [Q v], then you own a state
    from which the evaluation of the value [v] satisfies the
    postcondition [Q].
*)

Lemma wp_val : forall v Q,
  Q v ==> wp (trm_val v) Q.
Proof using.
  intros. rewrite <- wp_equiv. applys* triple_val.
Qed.

(** Let us verify that while migrating to the [wp] presentation we have
    not lost any expressivity, by showing that from [wp_val] we are able
    to recover [triple_val]. *)

Lemma triple_val_derived_from_wp_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using. introv M. rewrite wp_equiv. xchange M. applys wp_val. Qed.


(* ------------------------------------------------------- *)
(** *** Rule for sequence *)

(** Recall the reasoning rule for a sequence [trm_seq t1 t2]. *)

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

    This leads us to the following statement, which reads as follows:
    if you own a state from which the evaluation of [t1]
    produces a state from which the evaluation of [t2]
    produces the postcondition [Q], then you own a state from
    which the evaluation of the sequence [t1;t2] produces [Q]. *)

Lemma wp_seq : forall t1 t2 Q,
  wp t1 (fun v => wp t2 Q) ==> wp (trm_seq t1 t2) Q.
Proof using.
  intros. rewrite <- wp_equiv. applys triple_seq.
  { rewrite* wp_equiv. }
  { rewrite* wp_equiv. }
Qed.

(* EX2? (triple_seq_from_wp_seq) *)
(** Check that [wp_seq] is just as expressive as [triple_seq],
    by proving that [triple_seq] is derivable from [wp_seqd]
    and from the structural rules for [wp] and/or the structural
    rules for [triple]. *)

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


(* ####################################################### *)
(** * Additional contents *)

(* ******************************************************* *)
(** ** Other reasoning rules for terms *)

(* ------------------------------------------------------- *)
(** *** Rule for functions *)

(** Recall the reasoning rule for a term [trm_fun x t1],
    which evaluates to the value [val_fun x t1]. *)

Parameter triple_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  triple (trm_fun x t1) H Q.

(** The rule for functions follow exactly the same pattern as for values. *)

Lemma wp_fun : forall x t Q,
  Q (val_fun x t) ==> wp (trm_fun x t) Q.
Proof using. intros. rewrite <- wp_equiv. applys* triple_fun. Qed.

(** A similar rule holds for the evaluation of a recursive function. *)

Lemma wp_fix : forall f x t Q,
  Q (val_fix f x t) ==> wp (trm_fix f x t) Q.
Proof using. intros. rewrite <- wp_equiv. applys* triple_fix. Qed.


(* ------------------------------------------------------- *)
(** *** Rule for conditionals *)

(** Recall the reasoning rule for a term [triple_if b t1 t2]. *)

Parameter triple_if_case : forall b t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if (val_bool b) t1 t2) H Q.

(** Replacing [triple] using [wp] entailements yields:

[[
    H ==> wp (if b then t1 else t2) Q ->
    H ==> wp (trm_if (val_bool b) t1 t2) Q.
]]
    which simplifies by transitivity to:
[[
    wp (if b then t1 else t2) Q ==> wp (trm_if (val_bool b) t1 t2) Q.
]]
*)

Lemma wp_if : forall b t1 t2 Q,
  wp (if b then t1 else t2) Q ==> wp (trm_if b t1 t2) Q.
Proof using.
  intros. rewrite <- wp_equiv. applys triple_if.
  { intros ->. rewrite* wp_equiv. }
  { intros ->. rewrite* wp_equiv. }
Qed.


(* ------------------------------------------------------- *)
(** *** Rule for let-bindings *)

(** Recall the reasoning rule for a term [trm_let x t1 t2]. *)

Parameter triple_let : forall x t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall v, triple (subst x v t2) (Q1 v) Q) ->
  triple (trm_let x t1 t2) H Q.

(** The rule of [trm_let x t1 t2] is very similar to that for
    [trm_seq], the only difference being the substitution. *)

Lemma wp_let : forall x t1 t2 Q,
  wp t1 (fun v => wp (subst x v t2) Q) ==> wp (trm_let x t1 t2) Q.
Proof using.
  intros. rewrite <- wp_equiv. applys triple_let.
  { rewrite* wp_equiv. }
  { intros v. rewrite* wp_equiv. }
Qed.


(* ------------------------------------------------------- *)
(** *** Rule for function applications *)

(** Recall the reasoning rule for an application [(val_fun x t1) v2]. *)

Parameter triple_app_fun : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.

(** The corresponding [wp] rule is stated and proved next. *)

Lemma wp_app_fun : forall x v1 v2 t1 Q,
  v1 = val_fun x t1 ->
  wp (subst x v2 t1) Q ==> wp (trm_app v1 v2) Q.
Proof using.
  introv EQ1. rewrite <- wp_equiv. applys* triple_app_fun.
  rewrite* wp_equiv.
Qed.

(** A similar rule holds for the application of a recursive function. *)


(* ####################################################### *)
(** * Bonus contents (optional reading) *)

(* ******************************************************* *)
(** ** A concrete definition for weakest precondition *)

Module WpHighLevel.

(** The lemma [wp_equiv] captures the characteristic property of [wp],
    that is, [(triple t H Q) <-> (H ==> wp t Q)].

    However, it does not give evidence that there exists a predicate [wp]
    satisfying this equivalence. We next present one possible definition.

    The idea is to define [wp t Q] as the predicate
    [\exists H, H \* \[triple t H Q]].  *)

Definition wp (t:trm) (Q:val->hprop) : hprop :=
  \exists (H:hprop), H \* \[triple t H Q].

(** As we argue next, the heap predicate [wp t Q] is entailed by
    any precondition [H'] that satisfies [triple t H' Q],
    and [wp t Q] is itself a valid precondition, in the sense that
    [triple t (wp t Q) Q].

    On the one hand, if [H'] is a valid precondition, i.e. such that
    [triple t H' Q] holds, then it is the case that
    [H' ==> \exists H, H \* \[triple t H Q]].
    Indeed, the entailment holds by instantiating [H] as [H'].

    On the other hand [\exists H, H \* \[triple t H Q]] is a valid
    precondition for [t] with postcondition [Q], that is:
    [triple t (\exists H, H \* \[triple t H Q]) Q]. To see why,
    apply the extraction rule for existentials gives:
    [forall H, triple t (H \* \[triple t H Q]) Q]
    then apply the extraction rule for pure facts gives:
    [forall H, (triple t H Q) -> (triple t H Q)], i.e., a tautology.

    The above reasoning is formalized next, through the proof
    that [wp_high] also statisfies the equivalence
    [triple t H Q <-> H ==> wp Q], which characterizes [wp]. *)

(* EX2! (wp_equiv_wp_high) *)
(** Prove that the definition [wp_high] statisfies the characteristic
    equivalence for weakest preconditions. *)

Lemma wp_equiv_wp : forall t H Q,
  (triple t H Q) <-> (H ==> wp t Q).
Proof using.
(* SOLUTION *)
  unfold wp. iff M.
  { xsimpl H. apply M. }
  { applys triple_conseq Q M.
    { applys triple_hexists. intros H'.
      rewrite hstar_comm. applys triple_hpure.
      intros N. applys N. }
    { applys qimpl_refl. } }
(* /SOLUTION *)
Qed.

(* TODO: problem, we give the same proof further in the file. *)

End WpHighLevel.


(* ******************************************************* *)
(** ** An alternative definition for weakest precondition *)

Module WpLowLevel.

(** The concrete definition for [wp] given above is expressed
    in terms of Separation Logic combinators. In constrast to
    this "high level" definition, there exists a more "low level"
    definition, expressed directly as a function over heaps.

    In that alternative definition, the heap predicate [wp t Q]
    is defined as a predicate that holds of a heap [h]
    if and only if the execution of [t] starting in exactly
    the heap [h]produces the post-condition [Q].

    Technically, [wp t Q] is defined as [fun h => triple t (=h) Q],
    where [=h] is a shorthand for [fun h' => (h' = h)].
    In other words, the precondition [=h] requires the input heap
    to be exactly [h]. *)

Definition wp (t:trm) (Q:val->hprop) : hprop :=
  fun (h:heap) => triple t (=h) Q.

(** One can prove that this definition of [wp] also statisfies the
    characteristic equivalence [triple t H Q <-> H ==> wp Q]. *)

Lemma wp_equiv_wp_low : forall t H Q,
  (triple t H Q) <-> (H ==> wp t Q).

(** The details of the proofs are given for the reference but are
    beyond the scope of this course. (The proof exploits the lemma
    [triple_named_heap] which was established as an exercise in the
    appendix of the chapter [SLFRules].) *)

Proof using. (* Warning: details beyond the scope of the proof. *)
  unfold wp. iff M.
  { intros h K. applys triple_conseq M.
    { intros h' ->. applys K. }
    { applys qimpl_refl. } }
  { applys triple_named_heap. intros h K.
    applys triple_conseq (=h) Q.
    { specializes M K. applys M. }
    { intros ? ->. auto. }
    { applys qimpl_refl. } }
Qed.

End WpLowLevel.


(* ******************************************************* *)
(** ** Equivalence between all definitions of [wp] *)

(** We next prove that the equivalence [(triple t H Q) <-> (H ==> wp t Q)]
    defines a unique predicate [wp]. In other words, all possible
    definitions of [wp] are equivalent to each another.
    Thus, it really does not matter which concrete definition
    of [wp] we consider: they are all equivalent.

    Concretely, assume two predicates [wp1] and [wp2] to both satisfy
    the caracteristic equivalence. We prove that they are equal. *)

Lemma wp_unique : forall wp1 wp2,
  (forall t H Q, (triple t H Q) <-> (H ==> wp1 t Q)) ->
  (forall t H Q, (triple t H Q) <-> (H ==> wp2 t Q)) ->
  wp1 = wp2.
Proof using.
  introv M1 M2. applys fun_ext_2. intros t Q. applys himpl_antisym.
  { rewrite <- M2. rewrite M1. auto. }
  { rewrite <- M1. rewrite M2. auto. }
Qed.


(* ******************************************************* *)
(** ** Extraction rule for existentials *)

(** Recall the extraction rule for existentials: *)

Parameter triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (\exists x, J x) Q.

(** Replacing [triple t H Q] with [H ==> wp t Q] yields the
    following lemma. Prove it. *)

(* EX1? (triple_hexists_in_wp) *)
(** Prove the extraction rule for existentials in [wp] style. *)

Lemma triple_hexists_in_wp : forall t Q A (J:A->hprop),
  (forall x, (J x ==> wp t Q)) ->
  (\exists x, J x) ==> wp t Q.

Proof using.
  (* SOLUTION *)
  introv M. applys himpl_hexists_l M.
  (* /SOLUTION *)
Qed.

(** In other words, in the [wp] presentation, we do not need
    a specific extraction rule for existentials, because the
    extraction rule for entailment already does the job. *)


(* ******************************************************* *)
(** ** Combined structural rule *)

(** Recall the combined consequence-frame rule for [triple]. *)

Parameter triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.

(** Let us reformulate this rule using [wp], replacing the
    form [triple t H Q] with the form [H ==> wp t Q]. *)

(* EX2! (wp_conseq_frame_trans) *)
(** Prove the combined structural rule in [wp] style.
    Hint: exploit [wp_conseq_trans] and [wp_frame]. *)

Lemma wp_conseq_frame_trans : forall t H H1 H2 Q1 Q,
  H1 ==> wp t Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  H ==> wp t Q.
Proof using.
  (* SOLUTION *)
  introv M WH WQ. xchanges WH. xchange M.
  applys wp_conseq_trans WQ. applys himpl_refl.
  applys wp_frame.
  (* /SOLUTION *)
Qed.

(** The combined structural rule for [wp] can actually be stated
    in a more concise way, as follows. *)

(* EX2! (wp_conseq_frame) *)
(** Prove the concise version of the combined structural rule
    in [wp] style. (Many proofs are possible.) *)

Lemma wp_conseq_frame : forall t H Q1 Q2,
  Q1 \*+ H ===> Q2 ->
  (wp t Q1) \* H ==> (wp t Q2).
Proof using.
  (* SOLUTION *)
  dup 3.
  { (* Proof using [wp_conseq_frame_trans] *)
    introv M. applys* wp_conseq_frame_trans M. }
  { (* Proof using [wp_frame] and [wp_conseq_trans] *)
    introv M. applys* wp_conseq_trans M. applys* wp_frame. }
  { (* Proof using [triple_conseq_frame] *)
    introv M. rewrite <- wp_equiv.
    applys triple_conseq_frame (wp t Q1) M.
    { rewrite wp_equiv. xsimpl. } { xsimpl. } }
  (* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Alternative statement of the rule for conditionals *)

(** We have established the following rule for reasoning
    about conditionals using [wp]. *)

Parameter wp_if' : forall b t1 t2 Q,
  wp (if b then t1 else t2) Q ==> wp (trm_if b t1 t2) Q.

(** Equivalently, the rule may be stated with the conditional around
    the calls to [wp t1 Q] and [wp t2 Q]. *)

(* EX1? (wp_if'') *)
(** Prove the alternative statement of rule [wp_if],
    either from [wp_if] or directly from [triple_if]*)

Lemma wp_if'' : forall b t1 t2 Q,
  (if b then (wp t1 Q) else (wp t2 Q)) ==> wp (trm_if b t1 t2) Q.
Proof using.
  (* SOLUTION *)
  dup.
  { (* Proof from [wp_if] *)
    intros. applys himpl_trans wp_if. case_if~. }
  { (* Proof from [triple_if] *)
     intros. rewrite <- wp_equiv. applys triple_if.
     { intros ->. rewrite* wp_equiv. }
     { intros ->. rewrite* wp_equiv. } }
  (* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Definition of [wp] directly from [hoare] *)

(** Let's step back on our construction so far.

    1. We defined Hoare triples ([hoare]) with respect to the big-step
       judgment ([eval]).

    2. We defined Separation Logic triples ([triple]) in terms of
       Hoare triples ([hoare]), through the definition:
       \[forall H', hoare t (H \* H') (Q \*+ H')].

    3. We defined Separation Logic weakest-preconditions ([wp]) in terms
       of Separation Logic triples ([triple]).

    Through the construction, we established in terms reasoning rules
    for Hoare triples ([hoare]), then for Separation Logic triples
    ([triple]), then for weakest-preconditions ([wp]).

    One natural question to raise is whether there is a more direct
    route to deriving reasoning rules for weakest preconditions.
    In other words, can we obtain the same end result through simpler
    proofs. *)

(** The notion of Hoare triple is a key abstraction that enables conduction
    further proofs without manipulating heaps (of type [heap]) explicitly.
    Experiments suggest that it is always beneficial to introduce the
    Hoare logic layer.

    Thus, the only question that remains is whether it would have some
    interest to derive the reasoning rules for weakest preconditions ([wp])
    directly from the the reasoning rules for Hoare triples ([hoare]),
    that is, to bypass the reasoning rules for Separation Logic triples ([triple]).

    In what follows, we show that if one cares only for [wp]-style rules,
    the route to deriving them straight from [hoare]-style rules is indeed
    quite short. *)

(** Remark: it is technically possible to bypass even the definition of
    [triple] and specify all functions directly using the predicate [wp],
    however, using [triple] leads to better readability of specifications,
    thus it seems preferable to continue using that specification style.
    (See discussion in chapter [SLFWand], appendix on "Texan triples".) *)

Module WpFromHoare.

(** Recall the definition of [triple] in terms of [hoare].

[[
    Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
      forall (H':hprop), hoare t (H \* H') (Q \*+ H').
]]

    In what follows, we conduct the proofs by assuming a concrete definition
    for [wp], namely [wp_high], which lends itself better to automated proofs. *)

Definition wp (t:trm) := fun (Q:val->hprop) =>
  \exists H, H \* \[triple t H Q].

(** First, we check the equivalence between [triple t H Q] and [H ==> wp t Q].
    This proof is the same as [wp_equiv_wp] from the module [WpHighLevel]
    given earlier in this chapter. *)

Lemma wp_equiv : forall t H Q,
  (triple t H Q) <-> (H ==> wp t Q).
Proof using.
  unfold wp. iff M.
  { xsimpl* H. }
  { applys* triple_conseq Q M.
    applys triple_hexists. intros H'.
    rewrite hstar_comm. applys* triple_hpure. }
Qed.

(** Second, we prove the consequence-frame rule associated with [wp].
    It is the only structural rule that is needed for weakest preconditions. *)

Lemma wp_conseq_frame : forall t H Q1 Q2,
  Q1 \*+ H ===> Q2 ->
  (wp t Q1) \* H ==> (wp t Q2).

(** The proof leverages the consequence rule for [hoare] triples,
    and the frame property comes from the [forall H'] quantification
    baked in the definition of [triple]. *)

Proof using.
  introv M. unfold wp. xpull. intros H' N. xsimpl (H' \* H).
  unfolds triple. intros H''. specializes N (H \* H'').
  applys hoare_conseq N. { xsimpl. } { xchange M. }
Qed.

(** Third and last, we establish reasoning rules for terms in [wp]-style
    directly from the corresponding rules for [hoare] triples.

    The proof details are beyond the scope of this course.
    The point here is to show that the proofs are fairly concise. *)

Lemma wp_val : forall v Q,
  Q v ==> wp (trm_val v) Q.
Proof using.
  intros. unfold wp. xsimpl. intros H'. applys hoare_val. xsimpl.
Qed.

Lemma wp_fun : forall x t Q,
  Q (val_fun x t) ==> wp (trm_fun x t) Q.
Proof using.
  intros. unfold wp. xsimpl. intros H'. applys hoare_fun. xsimpl.
Qed.

Lemma wp_fix : forall f x t Q,
  Q (val_fix f x t) ==> wp (trm_fix f x t) Q.
Proof using.
  intros. unfold wp. xsimpl. intros H'. applys hoare_fix. xsimpl.
Qed.

Lemma wp_if : forall b t1 t2 Q,
  wp (if b then t1 else t2) Q ==> wp (trm_if b t1 t2) Q.
Proof using.
  intros. unfold wp. xsimpl. intros H M H'.
  applys hoare_if_case. applys M.
Qed.

Lemma wp_seq : forall t1 t2 Q,
  wp t1 (fun v => wp t2 Q) ==> wp (trm_seq t1 t2) Q.
Proof using.
  intros. unfold wp. xsimpl. intros H' M1. intros H''. applys hoare_seq.
  { applys M1. }
  { repeat rewrite hstar_hexists. applys hoare_hexists; intros H'''.
    rewrite (hstar_comm H'''). repeat rewrite hstar_assoc.
    applys hoare_hpure. intros M2. applys hoare_conseq M2. xsimpl. xsimpl. }
Qed.

Lemma wp_let : forall x t1 t2 Q,
  wp t1 (fun v => wp (subst x v t2) Q) ==> wp (trm_let x t1 t2) Q.
Proof using.
  intros. unfold wp. xsimpl. intros H' M1. intros H''. applys hoare_let.
  { applys M1. }
  { intros v. simpl. repeat rewrite hstar_hexists.
    applys hoare_hexists. intros H'''.
    rewrite (hstar_comm H'''). repeat rewrite hstar_assoc.
    applys hoare_hpure. intros M2. applys hoare_conseq M2. xsimpl. xsimpl. }
Qed.

Lemma wp_app_fun : forall x v1 v2 t1 Q,
  v1 = val_fun x t1 ->
  wp (subst x v2 t1) Q ==> wp (trm_app v1 v2) Q.
Proof using.
  introv EQ1. unfold wp. xsimpl. intros H' M. intros H''. applys* hoare_app_fun.
Qed.

Lemma wp_app_fix : forall f x v1 v2 t1 Q,
  v1 = val_fix f x t1 ->
  wp (subst x v2 (subst f v1 t1)) Q ==> wp (trm_app v1 v2) Q.
Proof using.
  introv EQ1. unfold wp. xsimpl. intros H' M. intros H''. applys* hoare_app_fix.
Qed.

End WpFromHoare.

