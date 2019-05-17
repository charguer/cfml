
(**

Separation Logic Foundations

Chapter: "WP".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import SLFRules.
From TLC Require Import LibFix.

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
    for Separation Logic triples, and describes the construction
    of a function that effectively computes in Coq weakest
    preconditions. Using this function, we'll be able to carry
    out verification proofs using Separation Logic reasoning rules
    but without never needing to reason about program variables
    and substitutions. *)


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



(* ******************************************************* *)
(** ** Syntactic construction of a weakest precondition *)

(** To carry out practical verification proofs, we introduce
    a function [wpgen] that construct a weakest precondition
    heap predicate expressed in terms of the Separation Logic
    combinators, by induction on the structure of the program. *)

Module WpgenAmbition.

Parameter wpgen : trm -> (val->hprop) -> hprop.

(** Intuitively, we'd like the "syntactic" function [wpgen]
    to be provably equal to "semantic" function [wp].

    In practice, to establish correctness of a program,
    we only care for one direction of the implication: *)

Parameter wpgen_sound : forall t Q,
  wpgen t Q ==> wp t Q.

(** If we manage to define such a function [wpgen], then we could
    use [wpgen] to establish triples. *)

Lemma triple_of_wpgen : forall H t Q,
  H ==> wpgen t Q ->
  triple t H Q.
Proof using.
  introv M. rewrite wp_equiv. hchange M. applys wpgen_sound.
Qed.

(** The reciprocal implication from [wp] to [wpgen] would be
    interesting to have, as it would justify the completeness of [wpgen].
    Completeness would show that any Separation Logic proof can be carried 
    out using [wpgen]. Yet, it is not a priority to try to formalize this 
    result in Coq for now. *)

End WpgenAmbition.


(* ******************************************************* *)
(** ** Definition of formulae for terms *)


(* ------------------------------------------------------- *)
(** *** General structure *)

(** [wpgen t] is defined by recursion on [t], as a function
    that expects a postcondition [Q] and returns a [hprop].
    We call "formula" the result type of [wgpen t]: *)

Definition formula := (val->hprop) -> hprop.

(** The general shape of the definition of [wpgen] is a
    recursive function on [t], with recursive calls for
    the subterms. The auxiliary functions named [wpgen_val],
    [wpgen_if], etc... describe the body of [wpgen t] for
    each term construct that [t] could be.

[[
  Fixpoint wpgen (t:trm) : formula :=
    match t with
    | trm_val v => wpgen_val v
    | trm_seq t1 t2 => wpgen_seq (wpgen t1) (wpgen t2)
    | trm_if v0 t1 t2 => wpgen_if v0 (wpgen t1) (wpgen t2)
    | ...
    end.
]]

    In what follows, we present the definition of each of
    these auxiliary functions.
*)

(* ------------------------------------------------------- *)
(** *** Case of values *)

(** First, consider a value [v]. The formula [wpgen (trm_val v)]
    should be such that [H ==> wpgen (trm_val v) Q] entails
    [triple (trm_val v) H Q]. Recall rule [triple_val]. *)

Parameter triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.

(** [H ==> Q v] is a sufficient condition for [triple (trm_val v) H Q].
    Thus, we wish [H ==> wpgen (trm_val v) Q] to imply [H ==> Q v],
    for any [H]. To achieve this implication, it suffices to define
    [wpgen (trm_val v) Q] as [Q v].

    Recall that [wpgen_val v] describes the value of [wpgen (trm_val v)].
    Thus, [wpgen_val v] is a function that takes [Q] as argument,
    and returns the heap predicate [Q v]. *)

Definition wpgen_val (v:val) : formula := fun Q =>
  Q v.

(** Just to be sure, let us check the desired property. *)

Lemma triple_of_wpgen_val : forall v H Q,
  H ==> wpgen_val v Q ->
  triple (trm_val v) H Q.
Proof using.
  introv M. applys triple_val. unfolds wpgen_val. applys M.
Qed.

(** The pattern of the above lemma will be repeated for all terms.
    To capture this pattern, let us say that a formula [F] is sound
    for a term [t] iff [H ==> F Q] entails [triple t H Q]. *)

Definition formula_sound_for (t:trm) (F:formula) : Prop :=
  forall H Q, H ==> F Q -> triple t H Q.

(** We can reformulate the lemma above as: *)

Lemma wpgen_val_sound : forall v,
  formula_sound_for (trm_val v) (wpgen_val v).
Proof using. introv M. applys triple_of_wpgen_val M. Qed.

(** Remark: ultimately, what we'd like to show for [wpgen] is:
    [forall t, formula_sound_for t (wpgen t)]. *)


(* ------------------------------------------------------- *)
(** *** Case of functions *)

(** Recall the rule for functions. It is almost exactly like
    that for values, the only difference beeing that the
    conclusion in on [trm_fun x t1] and the premise on [val_fun x t1]. *)

Parameter triple_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  triple (trm_fun x t1) H Q.

(** To handle functions in [wpgen], we can reuse the definition
    of [wpgen_val], and simply adapt the statement of soundness
    as follows. *)

Lemma wpgen_fun_sound : forall x t,
  formula_sound_for (trm_fun x t) (wpgen_val (val_fun x t)).
Proof using. introv M. unfolds wpgen_val. applys triple_fun M. Qed.

(** Likewise for recursive functions. *)

Parameter triple_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triple (trm_fix f x t1) H Q.

Lemma wpgen_fix_sound : forall f x t,
  formula_sound_for (trm_fix f x t) (wpgen_val (val_fix f x t)).
Proof using. introv M. unfolds wpgen_val. applys triple_fix M. Qed.


(* ------------------------------------------------------- *)
(** *** Case of sequences *)

(** Second, consider a sequence [trm_seq t1 t2].
    The formula [wpgen (trm_seq t1 t2)] should be such that
    [H ==> [wpgen (trm_seq t1 t2)] Q] entails
    [triple (trm_seq t1 t2) H Q].

    Recall that [wpgen (trm_seq t1 t2)] evaluates to
    [wpgen_seq (wpgen t1) (wpgen t2)]. The definition of
    [wpgen_seq] can be derived from that of [triple_seq]. 
    Recall that rule. *)

Parameter triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun r => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.

(** By induction hypothesis on the subterms, a [triple] for 
    [t1] or [t2] is equivalent to a [wpgen] entailment. 
    Replacing [triple t H Q] with [H ==> wpgen t Q] throughout
    the rule [triple_seq] gives us: 

[[
      H ==> wpgen t1 (fun r => H1) ->
      H1 ==> wpgen t2 Q ->
      H ==> wpgen_seq (wpgen t1) (wpgen t2) Q.
]]

    From there, let [F1] denote [wpgen t1] and [F2] denote [wpgen t2].
    Moreover, let us substitute away [H1], by presuming that [wpgen]
    is covariant in its second argument (just like [wp] is).
    We obtain:

[[
      H => F1 (fun r => F2 Q) ->
      H => wpgen_seq F1 F2
]]

    which simplifies to [F1 (fun r => F2 Q) ==> wpgen_seq F1 F2].
    This leads us to the following definition of [wpgen_seq]. *)

Definition wpgen_seq (F1 F2:formula) : formula := fun Q =>
  F1 (fun X => F2 Q).

(** Again, let us verify that we obtain the desired implication
    for [trm_seq t1 t2], assuming that we have sound formulae
    for the two subterms. *)

Lemma wpgen_seq_sound : forall F1 F2 t1 t2,
  formula_sound_for t1 F1 ->
  formula_sound_for t2 F2 ->
  formula_sound_for (trm_seq t1 t2) (wpgen_seq F1 F2).
Proof using.
  introv S1 S2 M. unfolds wpgen_seq. applys triple_seq.
  { applys S1. applys M. }
  { applys S2. applys himpl_refl. }
Qed.


(* ------------------------------------------------------- *)
(** *** Case of let-bindings *)

(** Consider now the case of a let-binding [trm_let x t1 t2].
    Handling this construct is a bit more involved due to the
    binding of the variable [x] in [t2].

    The formula [wpgen (trm_let x t1 t2)] should be such that
    [H ==> [wpgen (trm_let x t1 t2)] Q] entails
    [triple (trm_let x t1 t2) H Q]. 

    Recall the rule [triple_let]. *)

Parameter triple_let : forall x t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall v, triple (subst x v t2) (Q1 v) Q) ->
  triple (trm_let x t1 t2) H Q.

(** Replacing triples using [wpgen] entailements yields:

[[
      H ==> wpgen t1 Q1 ->
      (forall v, (Q1 v) ==> wpgen (subst x v t2) Q) ->
      H ==> wpgen (trm_let x t1 t2) Q.
]]

   The second premise can be reformuled as an entailment
   between [Q1] and another postcondition, as follows:
   [Q1 ===> (fun v => wpgen (subst x v t2) Q)].

   From there, by covariante of [wpgen], we can replace [Q1]
   with [fun v => wpgen (subst x v t2) Q] into the first premise
   [H ==> wpgen t1 Q1]. We obtain the implication:

[[
      H ==> (wpgen t1) (fun v => wpgen (subst x v t2) Q) ->
      H ==> wpgen (trm_let x t1 t2) Q.
]]

  Let [F1] denote [wpgen t1] and let [F2of] denote
  [fun v => wpgen (subst x v t2)). In other words,
  [F2of v Q] denotes [wpgen (subst x v t2) Q].
  After eliminating [H], the implication above thus simplifies to:
    [F1 (fun v => F2of v Q) ==> wpgen (trm_let x t1 t2) Q].
  This discussion suggests the following definitions:

[[
    Fixpoint wpgen (t:trm) : formula :=
      match t with
      | trm_let x t1 t2 => wpgen_let (wpgen t1) (fun v => wpgen (subst x v t2))
      ...
      end.
]]
    where [wgen_let] is defined as:
*)

Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := fun Q =>
  F1 (fun v => F2of v Q).

(** The soundness result takes the following form.
    It assumes that [F1] is a sound formula for [t1] and that
    [F2of v] is a sound formula for [subst x v t2], for any [v]. *)

Lemma wpgen_let_sound : forall F1 F2of x t1 t2,
  formula_sound_for t1 F1 ->
  (forall v, formula_sound_for (subst x v t2) (F2of v)) ->
  formula_sound_for (trm_let x t1 t2) (wpgen_let F1 F2of).
Proof using.
  introv S1 S2 M. unfolds wpgen_let. applys triple_let.
  { applys S1. applys M. }
  { intros v. applys S2. applys himpl_refl. }
Qed.


(* ------------------------------------------------------- *)
(** *** Case of variables *)

(** What should be the weakest precondition of a free variable [x]?
    There is no reasoning rule of the form [triple (trm_var x) H Q].
    Indeed, if a program execution reaches a dandling free variable,
    then the program is stuck.

    Yet, the weakest precondition for a variable needs to be defined,
    somehow. If we really need to introduce a reasoning rule for free
    variables, it could be one with the premise [False]:
[[
              False
      ----------------------
      triple (trm_var x) H Q
]]

    To mimic [False -> triple x H Q] using [wpgen], we would like:
    [False -> H ==> wp x Q]. This implication is equivalent to
    [\[False] \* H ==> wp x Q], or just [\[False] ==> wp x Q].
    This discussion suggests to define [wp x] as the formula
    [fun Q => \False].  Let us name [wpgen_fail] this formula. *)

Definition wpgen_fail : formula := fun Q =>
  \[False].

(** The function [wpgen] will thus treat variables as follows:
[[
      Fixpoint wpgen (t:trm) : formula :=
        match t with
        | trm_var x => wpgen_fail
        ...
        end.
]]

    The formula [wpgen_fail] is a sound formula not just for
    a variable [x], but in fact for any term [t].
    Indeed, if [H ==> \[False]], then [triple t H Q] is always true. *)

Lemma wpgen_fail_sound : forall t,
  formula_sound_for t wpgen_fail.
Proof using.
  intros. introv M. unfolds wpgen_fail.
  applys triple_conseq Q M.
  { rewrite <- (hstar_hempty_r \[False]). applys triple_hpure.
    intros N. false. }
  { applys qimpl_refl. }
Qed.


(* ------------------------------------------------------- *)
(** *** Case of applications *)

(** What should be the weakest precondition for an application?
    Well, it depends on the function, and how this function was
    specified. Yet, when constructing the weakest precondition
    by induction on [t], we have no specification at hand.

    We would like to just postpone the reasoning on an application
    until we have established specifications for the function being
    applied. The way we implement the postponing is by defining
    [wpgen (trm_app t1 t2)] as [wp (trm_app t1 t2)]. In other words,
    we fall back to the semantic definition of [wp].

    We define:

[[
  Fixpoint wpgen (t:trm) : formula :=
    match t with
    | trm_app t1 t2 => wp t
    ...
    end.
]]

    "Obviously", [wp t] is always a sound formula for a term [t].
    Indeed, by definition of [wp], [H ==> wp t] implies [triple t H Q].
*)

Lemma wp_sound : forall t,
  formula_sound_for t (wp t).
Proof using. intros. introv M. rewrite wp_equiv. applys M. Qed.

(** Remark: recall that we consider terms in A-normal form, thus [t1]
    and [t2] are assumed to be variables at the point where [wgpen]
    reaches the application [trm_app t1 t2]. If [t1] and [t2] could
    be general terms, we would need to call [wpgen] recursively,
    essentially encoding [let x1 = t1 in let x2 = t2 in trm_app x1 x2]. *)


(* ------------------------------------------------------- *)
(** *** Case of conditionals *)

(** Consider a conditional in A-normal form: [trm_if v0 then t1 else t2],
    where [v0] denotes either a variable of a value. If [v0] is a variable,
    by the time the [wpgen] function reaches it, it should already have
    been substituted in by a value (recall the [subst] in the treatment
    of let-bindings). Thus, we may assume here [v0] to be a value.

    Moreover, in the expression [trm_if v0 then t1 else t2], if [v0] denotes
    anything else than a boolean value, then the term would be stuck.
    Thus, we may in fact assume that [exists b, v0 = val_bool b].

    Note, however, that the [wpgen] function could see a term of the form
    [trm_if v0 then t1 else t2] where [v0] denotes a Coq variable of type
    [val], for which there is not yet any fact available to assert that it
    is a boolean value. Thus, the [wpgen] function must not be restricted
    to handling only terms of the form [trm_if (val_bool b) then t1 else t2].

    Recall the reasoning rule for conditionals, more precisely the version
    expressed using a Coq if-then-else. *)

Parameter triple_if_case : forall b t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if (val_bool b) t1 t2) H Q.

(** Replacing triples using [wpgen] entailements yields:

[[
    H ==> wpgen (if b then t1 else t2) Q ->
    H ==> wpgen (trm_if (val_bool b) t1 t2) Q.
]]

    which simplifies to 

[[
    wpgen (if b then t1 else t2) Q ==> wpgen (trm_if (val_bool b) t1 t2) Q
]]

    We need to make appear [wpgen t1] and [wpgen t2] in the formula, so as
    to compute recursively the weakest preconditions for the subterm.
    To that end, we expand the Coq conditional as follows:

[[
    (if b then wpgen t1 Q else wpgen t2 Q) ==> wpgen (trm_if (val_bool b) t1 t2) Q
]]

    As explained earlier, we are actually seeking for a definition of
    [wpgen (trm_if v0 t1 t2) Q] and not just for [trm_if (val_bool b) t1 t2].
    We thus reformulate the above entailment as follows:

[[
        (\exists b, \[v0 = val_bool b]  (if b then wpgen t1 Q else wpgen t2 Q)
    ==> wpgen (trm_if v0 t1 t2) Q
]]

    This lattest entailment leads us the definition of [wpgen] for conditionals.
*)

Definition wpgen_if (v:val) (F1 F2:formula) : formula := fun Q =>
  \exists (b:bool), \[v = val_bool b] \* (if b then F1 Q else F2 Q).

(** With just a little work to extract the information captured in the
    [\exists (b:bool), \[v = val_bool b] ], we can prove [wpgen_if] 
    to be a sound formula for a conditional. *)

Lemma wpgen_if_sound : forall F1 F2 v0 t1 t2,
  formula_sound_for t1 F1 ->
  formula_sound_for t2 F2 ->
  formula_sound_for (trm_if v0 t1 t2) (wpgen_if v0 F1 F2).
Proof using.
  introv S1 S2 M. unfolds wpgen_if. 
  applys triple_conseq Q M; [|applys qimpl_refl].
  applys triple_hexists. intros b.
  applys triple_hpure. intros ->.
  applys triple_if_case. case_if.
  { applys S1. applys himpl_refl. }
  { applys S2. applys himpl_refl. }
Qed.


(* ------------------------------------------------------- *)
(** *** Turning the fixpoint into a structural function *)

(** We are almost ready to formally define our function [wpgen].
    There are two Coq-specific caveat on our way, however. 

    First, the definition of [wpgen] is not structurally recursive.
    Thus, we'll have to play some tricks to first define it as a functional,
    and then take the fixed point of this functional. The details of this
    fixed point construction are not essential for the moment; they are
    explained further in this chapter. In any case, we will shortly
    afterwards present an alternative definition to [wpgen] which is
    slightly more complex yet structurally recursive.

    Second, the definition of [wpgen] as a pattern matching on terms
    forces us to reveal our general grammar of terms. Indeed, Coq does
    not support notations in the grammar of patterns. We will put as
    comment the intended pattern, and write down the underlying pattern.
    (These patterns reveals the support for n-ary functions and applications,
    and the factorization between functions and recursive functions,
    and between [trm_seq] and [trm_let].) *)

Definition Wpgen wpgen (t:trm) : formula :=
  match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpgen_fail
  | (* [trm_fun x t1] *) 
    trm_fixs bind_anon (x::nil) t1 => wpgen_val (val_fun x t1)
  | (* [trm_fix f x t1] *)
    trm_fixs (bind_var f) (x::nil) t1 => wpgen_val (val_fix f x t1)
  | trm_if (trm_val v0) t1 t2 => wpgen_if v0 (wpgen t1) (wpgen t2)
  | (* [trm_seq t1 t2] *)
    trm_let bind_anon t1 t2 => wpgen_seq (wpgen t1) (wpgen t2)
  | trm_let (bind_var x) t1 t2 => wpgen_let (wpgen t1) (fun X => wpgen (subst x X t2))
  | (* [trm_app t1 t2] *)
    trm_apps t1 (t2::nil) => wp t
  | (* other terms are outside of the sub-language that we consider,
       so let us here pretend that they are no such terms. *)
    _ => wpgen_fail
  end.

Definition wpgen := FixFun Wpgen.

(** The fixed point equation, which enables unfolding the definition
    of [wpgen], is proved further in this file. *)

Parameter wpgen_fix : forall t, 
  wpgen t = Wpgen wpgen t.

(** We establish the soundness of [wpgen] by induction on [t].
    The induction principle that we wish to use is that associated
    with the sublanguage presented in [SLFRules], whose inductive
    definition comes with the following induction principle.

    Moreover, we tweak the induction hypothesis so that, in the case
    of a [trm_let x t1 t2], the induction principle applies not just
    to [t2], but to any subterm of the form [subst x v t2]. This
    generalized induction principle is justified by the fact that
    a substitution does not increase the size of a term (when the
    size of all values is considered to be one unit). Again, we
    prove this derived induction principle further in this file,
    but the details are orthogonal to the matter of the present chapter. *)

Parameter trm_induct : forall (P : trm -> Prop),
  (forall v, P (trm_val v)) ->
  (forall x, P (trm_var x)) ->
  (forall x t1 , P t1 -> P (trm_fun x t1)) ->
  (forall (f:var) x t1, P t1 -> P (trm_fix f x t1)) ->
  (forall t1, P t1 -> forall t2, P t2 -> P (trm_app t1 t2)) ->
  (forall t1, P t1 -> forall t2, P t2 -> P (trm_seq t1 t2)) ->
  (forall (x:var) t1, P t1 -> forall t2, (forall v, P (subst x v t2)) -> P (trm_let x t1 t2)) ->
  (forall v t1, P t1 -> forall t2, P t2 -> P (trm_if v t1 t2)) ->  
  (forall t, P t).

(** The soundness lemma asserts that [H ==> wpgen t Q] implies
    [triple t H Q]. Equivalently, it can be formulated as:
    [forall t, formula_sound_for t (wpgen t)]. The proof consists
    of invoking all the soundness lemmas which we have proved
    previously. *)

Theorem wpgen_sound : forall t,
  formula_sound_for t (wpgen t).
Proof using.
  intros. induction t using trm_induct; 
   rewrite wpgen_fix; simpl.
  { applys wpgen_val_sound. }
  { applys wpgen_fail_sound. }
  { applys wpgen_fun_sound. }
  { applys wpgen_fix_sound. }
  { applys wp_sound. }
  { applys wpgen_seq_sound. { applys IHt1. } { applys IHt2. } }
  { applys wpgen_let_sound. { applys IHt1. } { intros v. applys H. } }
  { applys wpgen_if_sound. { applys IHt1. } { applys IHt2. } }
Qed.

Corollary triple_of_wpgen : forall t H Q,
  H ==> wpgen t Q ->
  triple t H Q.
Proof using. introv M. applys wpgen_sound M. Qed.


(* ------------------------------------------------------- *)
(** *** Turning the fixpoint into a structural function *)

(** context 

Definition ctx : Type := list (var * val).

Check Ctx.empty : ctx.
Check Ctx.add : var -> val -> ctx -> ctx
Check Ctx.rem_var : var -> ctx -> ctx
Check Ctx.lookup : var -> ctx -> val

Check isubst : ctx -> trm -> trm.

Lemma isubst_empty : forall t,
  isubst Ctx.empty t = t.

Lemma isubst_add : forall x v E t,
  isubst (Ctx.add x v E) t = isubst E (subst x v t).

*)

Definition wpaux_var (E:ctx) (x:var) : formula :=
  match Ctx.lookup x E with
  | None => wpgen_fail
  | Some v => wpgen_val v
  end.


(* 
Import SyntaxAndSemantics. 
*)


Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpaux_var E x
  (* | trm_fun x t1 => trm_fun (isubst (Ctx.rem_var x E) t1)
  | trm_fix f x t1 => trm_fix (isubst (Ctx.rem_var x (Ctx.rem_var f E)) t1)  *)
  | trm_fixs f (x::nil) t1 => wpgen_val (val_fun x (isubst (Ctx.rem_var x E) t1))
  | trm_if t0 t1 t2 => wpgen_fail (* wpgen_if (wpgen t0) (wpgen t1) (wpgen t2) *)
  | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun X => wpgen (Ctx.add x X E) t2)
  (* | trm_app t1 t2 => wp (isubst E t) *)
  | trm_apps t1 (t2::nil) => wp (isubst E t)
  | _ => wpgen_fail
  end.


Lemma wpgen_sound_trm : forall E t,
  formula_sound_for (isubst E t) (wpgen E t).
Proof using.
  intros. gen E. induction t. introv M.
Abort.

Lemma triple_of_wpgen : forall t H Q,
  H ==> wpgen Ctx.empty t Q ->
  triple t H Q.
Abort.





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

(** Or, equivalently, the [H] from rules [wp_hany_pre] and 
   [wp_hand_post] may be replaced with [\Top]. *)




(* ******************************************************* *)
(** ** Semantic definition of weakest precondition *)


(*

Lemma flocal_elim : forall F H Q,
  H ==> wp t Q' \* (Q' \--* (Q \*+ \GC)) ->
  H ==> wp t Q.
Proof using. introv L M. lets N: (L Q). applys* himpl_trans N. Qed.





  prove1: 
    F Q ==> mklocal F Q
    (take Q1 = Q)

  prove 2:
    (mkflocal (mkflocal F)) Q := mkflocal F
    right-to-left : instance of (1)
    left-to-right: ...

    (mkflocal (mkflocal F)) Q
  = \exists Q1, mkflocal F Q1 \* (Q1 \--* (Q \*+ \GC))
  = \exists Q1, (\exists Q2, F Q2 \* (Q2 \--* (Q1 \*+ \GC))) \* (Q1 \--* (Q \*+ \GC))
  = \exists Q1 Q2, F Q2 \* (Q2 \--* (Q1 \*+ \GC) \* (Q1 \--* (Q \*+ \GC))
  = \exists Q1 Q2, F Q2 \* (Q2 \--* (Q1 \*+ \GC) \* ((Q1 \*+ \GC) \--* ((Q \*+ \GC) \*+ \GC))
  ==> \exists Q1 Q2, F Q2 \* (Q2 \--* (Q1 \*+ \GC) \* ((Q1 \*+ \GC) \--* (Q \*+ \GC \*+ \GC))
  = \exists Q1 Q2, F Q2 \* (Q2 \--* (Q \*+ \GC \*+ \GC))
  = \exists Q2, F Q2 \* (Q2 \--* (Q \*+ \GC))
  = mkflocal F


  mkflocal F Q := \exists Q1, F Q1 \* (Q1 \--* (Q \*+ \GC)).

  \exists Q1, F Q1 \* (Q1 \--* (Q \*+ \GC)) ==> F Q


  F Q1 \* (Q1 \--* (Q \*+ \GC)) ==> F Q



  wp t Q1 \* (Q1 \--* (Q \*+ \GC)) ==> wp t Q


  H ==> wp t Q1 \* (Q1 \--* (Q \*+ \GC)) ->
  H ==> wp t Q.


let H1 := wp t Q1
let H2 := (Q1 \--* (Q \*+ \GC)) 


  H ==> H1 \* H2 ->
  H1 ==> wp t Q1 ->
  Q1 \* H2 ==> Q \*+ \GC ->
  H ==> wp t Q.


  H ==> H1 \* H2 ->
  triple t H1 Q1 ->
  Q1 \* H2 ==> Q \*+ \GC ->
  triple t H Q


reciprocally, with 
   forall Q1,   wp t Q1 \* (Q1 \--* (Q \*+ \GC)) ==> wp t Q
we can simulate frame


  H ==> H1 \* H2 ->
  H1 ==> wp t Q1 ->
  Q1 \* H2 ==> Q \*+ \GC ->
  H ==> wp t Q.

exploit fact

  H ==> H1 \* H2 ->
  H1 ==> wp t Q1 ->
  Q1 \* H2 ==> Q \*+ \GC ->
  H ==> wp t Q1 \* (Q1 \--* (Q \*+ \GC))

suffices (hchange 1 and 2)

  H1 \* H2 ==> wp t Q1 \* (Q1 \--* (Q \*+ \GC))
  wp t Q1 \* H2 ==> wp t Q1 \* (Q1 \--* (Q \*+ \GC))
  H2 ==> (Q1 \--* (Q \*+ \GC))

done.




-------





Lemma wpgen_himpl_wp : forall t Q,
  wpgen t Q ==> wp t Q.

Definition wpgen_sound_for t := forall Q,
  wpgen t Q ==> wp t Q.

wpgen_sound_for (trm_val v)
wpgen_sound_for (trm_fun x t).
wpgen_sound_for (trm_fix f x t).
..



--------






Definition wpgen_fail : formula := mkflocal (fun Q =>
  \[False]).

Definition wpgen_val (v:val) : formula := mkflocal (fun Q =>
  Q v).

Definition wpaux_var (E:ctx) (x:var) : formula :=
  match Ctx.lookup x E with
  | None => wpgen_fail
  | Some v => wpgen_val v
  end.

Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := mkflocal (fun Q =>
  F1 (fun X => F2of X Q)).

Definition wpgen_seq (F1 F2:formula) : formula := mkflocal (fun Q =>
  F1 (fun X => F2 Q)).

Definition wpgen_app (t1:trm) (t2:trm) : formula := mkflocal (fun Q =>  
  wp (trm_app t1 t2) Q)

Definition wpgen_if_val (v:val) (F1 F2:formula) : formula := mkflocal (fun Q =>
  \exists (b:bool), \[v = val_bool b] \* (if b then F1 Q else F2 Q)).

Definition wpgen_if (F0 F1 F2:formula) : formula :=
  wpgen_let F0 (fun v => wpgen_if_val v F1 F2).

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  let aux := wpgen E in
  match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpaux_var E x
  | trm_fun x t1 => trm_fun (isubst (Ctx.rem x E) t1)
  | trm_fix f x t1 => trm_fix (isubst (Ctx.rem x (Ctx.rem f E)) t1))
  | trm_if t0 t1 t2 => wpgen_if (aux t0) (aux t1) (aux t2)
  | trm_let x t1 t2 => wpgen_let (aux t1) (fun X => wpgen (Ctx.add x X E) t2)
  | trm_app t1 t2 => wgpen_app (isubst E t1) (isubst E t2)
  end.







forward proof 
- with let
- lets
- subst all pb

reasoning on calls
- with = 2*x (app vs apps)
- with y st P x y

recursion
- call that does not fit coq


*)

