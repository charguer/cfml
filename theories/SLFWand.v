(**

Separation Logic Foundations

Chapter: "Wand".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import SLFDirect SLFExtra.

Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ####################################################### *)
(** * Chapter in a rush *)

(** This chapter introduces additional Separation Logic operators,
    most notably the "magic wand", written [H1 \-* H2].

    Magic wand does not only have a cool name, and it is not only
    a fascinating operator for logicians; it turns out that the
    magic wand is a key ingredient to streamlining the process of
    practical program verification in Separation Logic.

    In this chapter, we first introduce the new operators, then
    explain how they can be used to reformulate the frame rule
    and give a different presentation to Separation Logic triples. *)

Module WandDef.


(* ******************************************************* *)
(** ** Definition of the magic wand *)

(** At a high level, [H1 \* H2] describes the "addition" of a
    heap satisfying [H1] with a heap satisfying [H2].
    Think of it as [H1 + H2].

    As a counterpart to this addition operator, we introduce
    a subtraction operator, called "magic wand", and written [H1 \-* H2].
    Think of it as [ -H1 + H2]. Note however, that whereas a subtraction
    is defined for all arguments, for the magic wand operator it only makes
    sense to subtract [H1] from [H2] when the heap described by [H1]
    is a subset of the heap described by [H2]. In other words, [H1 \-* H2]
    specifies a heap that cannot possibly exist when [H1] is not somehow
    a subset of [H2].

    A heap [h] satisfies [H1 \-* H2] if and only if, when we augment
    it with a disjoint heap [h'] satisfying [H1], we recover [H2].
    Think of it as [(-H1 + H2) + H1] simplifying to [H2].

    The operator [hwand] can be defined as follows. *)

Definition hwand' (H1 H2:hprop) : hprop :=
  fun h => forall h', Fmap.disjoint h h' -> H1 h' -> H2 (h \u h').

(** Another possible definition of [H1 \-* H2] can be stated
    without refering to heaps at all, by reusing the basic
    Separation Logic operators that we have already introduced.
    [H1 \-* H2] denotes some heap, described as [H0], such
    that [H0] augmented with [H1] yields [H2].

    In the alternative definition of [hwand] shown below,
    the heap [H0] is existentially quantified using [\exists],
    and the entailment assertion is described as the pure heap
    predicate [\[ H0 \* H1 ==> H2 ]]. *)

Definition hwand (H1 H2:hprop) : hprop :=
  \exists H0, H0 \* \[ (H0 \* H1) ==> H2].

Notation "H1 \-* H2" := (hwand H1 H2) (at level 43, right associativity).

(** As we prove further in this file, we can prove that [hwand']
    defines the same operator as [hwand]. *)

Parameter hwand_eq_hwand' :
  hwand = hwand'.

(** In practice, we prefer using the definition [hwand] because its
    properties can be established with help of the tactic [xsimpl],
    conducting all the reasoning at the level of [hprop] and avoiding
   the need to work with explicit heaps (of type [heap]). *)


(* ******************************************************* *)
(** ** Characteristic property of the magic wand *)

(** The definition of [hwand] is not easy to make sense of at first.
    To better grasp its meaning, we detail introduction and
    elimination lemmas for it. *)

(** The operator [H1 \-* H2] is uniquely defined by the followig
    equivalence. In other words, any operator that satisfies this
    equivalence for all arguments is provably equal to the definition
    of [hwand] given above. (We proof this fact further in the chapter.) *)

Parameter hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 \-* H2) <-> (H0 \* H1 ==> H2).

(** The right-to-left direction is an introduction rule: it tells
    what needs to be proved to introduce a magic wand [H1 \-* H2]
    when starting from a state described by [H0]. What needs to
    be proved is that [H0], if augmented with [H1], yields [H2]. *)

Lemma himpl_hwand_r : forall H0 H1 H2,
  (H0 \* H1) ==> H2 ->
  H0 ==> (H1 \-* H2).
Proof using. introv M. applys hwand_equiv. applys M. Qed.

(** The left-to-right direction is an elimination rule: it tells
    what can be deduced from [H0 ==> (H1 \-* H2)]. What can be
    deduced is that if [H0] is augmented with [H1], then [H2]
    can be recovered. *)

Lemma himpl_hwand_r_inv : forall H0 H1 H2,
  H0 ==> (H1 \-* H2) ->
  (H0 \* H1) ==> H2.
Proof using. introv M. applys hwand_equiv. applys M. Qed.

(** This elimination rule can be equivalently reformulated in the
    following form, which makes it perhaps even clearer that
    [H1 \-* H2], when augmented with [H1], yields [H2].
    Think of it as [H1 + (-H1 + H2)] simplifying to [H2]. *)

Lemma hwand_cancel : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.
Proof using.
  intros. rewrite hstar_comm.
  applys himpl_hwand_r_inv. applys himpl_refl.
Qed.

Arguments hwand_cancel : clear implicits.


(* ******************************************************* *)
(** ** Magic wand for postconditions *)

(** For entailment, written [H1 ==> H2], we introduced its extension
    to postconditions, written [Q1 ===> Q2], and defined as
    [forall x, (Q1 x) ==> (Q2 x)].

    Likewise, for magic wand, written [H1 \-* H2], we introduce
    its extension to postconditions, written [Q1 \--* Q2], and
    defined (in first approximation) as [forall x, (Q1 x) \-* (Q2 x)].

    Like [H1 \-* H2], the expression [Q1 \--* Q2] should denote a heap
    predicate, of type [hprop]. Thus, writing [forall x, (Q1 x) \-* (Q2 x)]
    makes no sense, because [forall] applies to propositions of type [Prop],
    and not to heap predicates of type [hprop].

    In order to define [Q1 \--* Q2], we thus need to introduce the
    operation [\forall], which lifts the universal quantifier from
    [Prop] to [hprop]. In other words, [\forall] is to [forall]
    what [\exists] is to [exists].

    The definition of [\forall x, H], a notation for [hforall (fun x => H)],
    follows exactly the same pattern as that of [\exists x, H], with only
    the [exists] quantifier being replaced with a [forall] in the definition. *)

Definition hforall (A : Type) (J : A -> hprop) : hprop :=
  fun h => forall x, J x h.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : heap_scope.

(** We are now read to formally define [Q1 \--* Q2], a notation that stands
    for [qwand Q1 Q2], and which is defined as [\forall x, (Q1 x) \-* (Q2 x)]. *)

Definition qwand A (Q1 Q2:A->hprop) : hprop :=
  \forall x, (Q1 x) \-* (Q2 x).

Notation "Q1 \--* Q2" := (qwand Q1 Q2) (at level 43).

(** As a sanity check of our definition, let us prove that [Q1 \--* Q2]
    indeed entails [(Q1 x) \-* (Q2 x)] for any [x]. *)

Lemma qwand_specialize : forall A (x:A) (Q1 Q2:A->hprop),
  (Q1 \--* Q2) ==> (Q1 x \-* Q2 x).
Proof using. intros. unfold qwand. intros h K. applys K. Qed.

(** The operator [qwand] satisfies many properties similar to those
    of [hwand]. We state these properties further in the chapter.

    For now, we just state the two most important rules: the
    characterization rule, and the cancellation rule. *)

Lemma qwand_equiv : forall H Q1 Q2,
  H ==> (Q1 \--* Q2)  <->  (Q1 \*+ H) ===> Q2.
Proof using.
  intros. iff M.
  { intros x. xchange M. xchange (qwand_specialize x).
    xchange (hwand_cancel (Q1 x)). }
  { applys himpl_hforall_r. intros x. applys himpl_hwand_r.
    xchange (M x). }
Qed.

Lemma qwand_cancel : forall Q1 Q2,
  Q1 \*+ (Q1 \--* Q2) ===> Q2.
Proof using. intros. rewrite <- qwand_equiv. applys qimpl_refl. Qed.


(* ******************************************************* *)
(** ** Frame expressed with [hwand]: the ramified frame rule *)

(** Recall the consequence-frame rule *)

Parameter triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.

(** This rule suffers from practical issues, which we discuss in
    details further in this chapter. In short, the main problem is
    that one needs to either provide a value for, or to introduce a
    unification variable (evar) for [H2]. The problem would disappear
    if we make use of the magic wand to eliminate the need to quantify
    [H2] altogether.

    [Q1 \*+ H2 ===> Q] is equivalent to [H2 ==> (Q1 \--* Q)].
    By substituting away, we can merge the two entailments
    [H ==> H1 \* H2] and [H2 ==> (Q1 \--* Q)] into a single one:
    [H ==> H1 \* (Q1 \--* Q)].

    The resulting rule is called the "ramified frame rule". *)

Lemma triple_ramified_frame : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  triple t H Q.

(** As we prove next, the ramified frame rule has exactly the same
    expressive power as the consequence-frame rule.

    First, let us prove that it is derivable.
    To that end, we instantiate [H2] as [Q1 \--* Q]. *)

Proof using.
  introv M W. applys triple_conseq_frame (Q1 \--* Q) M.
  { applys W. } { applys qwand_cancel. }
Qed.

(** Reciprocally, we prove that consequence-frame is derivable from
    the ramified frame rule. *)

Lemma triple_conseq_frame' : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.
Proof using.
  introv M WH WQ. applys triple_ramified_frame M.
  xchange WH. xsimpl. rewrite qwand_equiv. applys WQ.
Qed.


(* ******************************************************* *)
(** ** Ramified frame rule in weakest-precondition style *)

(** The ramified-frame rule for [triple] also has a counterpart for [wp].
    In what follows, we present a concise rule, called [wp_ramified], that
    subsumes all other structural rules of Separation Logic. *)

(** Recall from chapter [SLFWPsem] the rule [wp_conseq_frame], which
    combines the consequence rule and the frame rule for [wp]. *)

Parameter wp_conseq_frame : forall t H Q1 Q2,
  Q1 \*+ H ===> Q2 ->
  (wp t Q1) \* H ==> (wp t Q2).

(** Let us reformulate this rule using a magic wand. The premise
    [Q1 \*+ H ===> Q2] can be rewriten as [H ==> (Q1 \--* Q2)].
    By replacing [H] with [Q1 \--* Q2] in the conclusion of
    [wp_conseq_frame], we obtain the ramified rule for [wp]. *)

Lemma wp_ramified : forall t Q1 Q2,
  (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).
Proof using. intros. applys wp_conseq_frame. applys qwand_cancel. Qed.

(* EX2! (wp_conseq_frame_of_wp_ramified) *)
(** Prove that [wp_conseq_frame] is derivable from [wp_ramified].
    To that end, prove the statement of [wp_conseq_frame] by using
    only [wp_ramified], the characteristic property of the magic
    wand [qwand_equiv], and properties of the entailment relation. *)

Lemma wp_conseq_frame_of_wp_ramified : forall t H Q1 Q2,
  Q1 \*+ H ===> Q2 ->
  (wp t Q1) \* H ==> (wp t Q2).
Proof using.
(* ADMITTED *)
  introv M. applys himpl_trans; [| applys wp_ramified Q1 ].
  apply himpl_frame_r. rewrite qwand_equiv. applys M.
Qed. (* /ADMITTED *)

(* [] *)

(** The following reformulation of [wp_ramified] is more practical
    to exploit in practice, because it applies to any goal of the
    form [H ==> wp t Q]. *)

Lemma wp_ramified_trans : forall t H Q1 Q2,
  H ==> (wp t Q1) \* (Q1 \--* Q2) ->
  H ==> (wp t Q2).
Proof using. introv M. xchange M. applys wp_ramified. Qed.

End WandDef.


(* ******************************************************* *)
(** ** Automation with [xsimpl] for [hwand] expressions *)

(** Throughout the rest of the chapter, we assume that the tactic [xsimpl]
    is extended with support for the magic wand. The definition of magic
    wand used is the same as the one defined abov (technically, it comes
    from [SepFunctor.v]). *)

Module XsimplDemo.

(** [xsimpl] is able to spot magic wand that cancel out.
    For example, [H2 \-* H3] can be simplified with [H2]
    to leave only [H3]. *)

Lemma xsimpl_demo_hwand_cancel : forall H1 H2 H3 H4 H5,
  H1 \* (H2 \-* H3) \* H4 \* H2 ==> H5.
Proof using. intros. xsimpl. Abort.

(** [xsimpl] is able to simplified uncurried magic wands
    of the form [(H1 \* H2 \* H3) \-* H4] against a fragment,
    e.g., [H2], leaving in this case [(H1 \* H3) \-* H4]. *)

Lemma xsimpl_demo_hwand_cancel_partial : forall H1 H2 H3 H4 H5 H6,
  ((H1 \* H2 \* H3) \-* H4) \* H5 \* H2 ==> H6.
Proof using. intros. xsimpl. Abort.

(** [xsimpl] automatically applies the [himpl_hwand_r] when
    the right-hand-side, after prior simplification, reduces
    to just a magic wand. In the example below, [H1] is first
    cancelled out from both sides, then [H3] is moved from
    the RHS to the LHS. *)

Lemma xsimpl_demo_himpl_hwand_r : forall H1 H2 H3 H4 H5,
  H1 \* H2 ==> H1 \* (H3 \-* (H4 \* H5)).
Proof using. intros. xsimpl. Abort.

(** [xsimpl] iterates the simplifications it is able to perform
    until it no obvious simplification remain. *)

Lemma xsimpl_demo_hwand_iter : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* ((H1 \* H3) \-* (H4 \-* H5)) \* H4 ==> ((H2 \-* H3) \-* H5).
Proof using. intros. xsimpl. Qed.

(** [xsimpl] is also able to deal with [qwand]. In particular,
    it can cancel out [Q1 \--* Q2] against [Q1 v], leaving [Q2 v]. *)

Lemma xsimpl_demo_qwand_cancel : forall A (v:A) (Q1 Q2:A->hprop) H1 H2,
  (Q1 \--* Q2) \* H1 \* (Q1 v) ==> H2.
Proof using. intros. xsimpl. Abort.

End XsimplDemo.


(* ####################################################### *)
(** * Additional contents *)

(* ******************************************************* *)
(** ** Evaluation of [wpgen] recursively in locally-defined functions *)

Module WPgenRec.
Implicit Types vx vf : val.

(** In the chapter [SLFWPgen], the definition of [wpgen t Q] considered
    does not recursive inside the body of functions that occur inside [t].
    Instead, it treats such locally-defined functions like values.
    In essence, the definition of [wpgen] considered was as follows.

[[
    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v      => Q v
      | trm_fun x t1   => Q (val_fun x t1)
      | trm_fix f x t1 => Q (val_fix f x t1)
      ...
      end.
]]

*)

(** Doing so is not a major limitation, because it is always possible
    for the user to manually invoke [wpgen] once again for each locally-
    defined function, during the verification proof.

    Yet, it is much more satisfying and practical to set up [wpgen] so
    that it recursively computes the weakest precondition of the
    local functions that it encounters during its evaluation. *)

(** In what follows, we show how such a version of [wpgen] can be set up
    with help of the magic wand operator. We begin with the case of
    non-recursive functions of the form [trm_fun x t1], then generalize
    the definition to the slightly more complex case of recursive functions
    of the form [trm_fix f x t1].

    The new definition of [wpgen] will take the following form, for
    well-suited definitions of [wpgen_fun] and [wpgen_fix] yet to be
    introduced. In the code snippet below, [vx] denotes a value to
    which the function may be applied, and [vf] denotes the value
    associated with the function itself, this value being used in particular
    in the case of recursive calls.

[[
    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct match t with
      ...
      | trm_fun x t1 => wpgen_fun (fun vx => wpgen ((x,vx)::E) t1)
      | trm_fix f x t1 => wpgen_fix (fun vf vx => wpgen ((f,vf)::(x,vx)::E) t1)
      ...
      end.
]]

*)


(* ------------------------------------------------------- *)
(** *** 1. Treatment of non-recursive functions *)

(** Our first task is to provide a definition for [wpgen (trm_fun x t1) Q],
    in terms of [wpgen t1].

    For now, let us assume the context [E] to be empty, and let us ignore
    the predicate [mkstruct].

    Let [vf] denote the function [val_fun x t1], which the term [trm_fun x t1]
    evaluates to. The heap predicate [wpgen (trm_fun x t1) Q] should
    assert that that the postcondition [Q] holds of the result value [vf],
    that is [Q vf] should hold.

    Rather than specifying that [vf] is equal to [val_fun x t1] as we were
    doing previously, we would like to specify that [vf] denotes a function
    whose body admits [wpgen t1] as weakest precondition. This information
    no longer exposes the syntax of the term [t1], and is neverthess sufficient
    for the user to carry out reasoning about the function [vf].

    To achieve this, we define the heap predicate [wpgen (trm_fun x t1) Q] to
    be of the form [\forall vf, \[P vf] \-* Q vf] for a carefully-crafed predicate
    [P] that we will detail afterwards.

    The universal quantification on [vf] is intended to hide away from the
    user the fact that [vf] actually denotes [val_fun x t1]. It would not be
    incorrect to replace [\forall vf, ...] with [let vf := val_fun x t1 in ...],
    yet we are purposely trying to abstract away from the syntax of [t1].

    In the heap predicate [\forall vf, \[P vf] \-* Q vf], the magic wand featuring
    a left-hand side of the form [\[P vf]] is intended to provide to the user the
    knowledge of the weakest precondition of the body [t1] of the function, in such
    a way that the user is able to derive the specification that he wishes to
    establish for the local function.

    In other words, the proposition [P vf] should enable the user establishing
    properties of applications of the form [trm_app vf vx], where [vf] denotes
    the function and [vx] denotes an argument to which the function is applied.

    To figure out the details of the statement of [P], it is useful to recall
    from [SLFWPgen] the statement of the lemma [triple_app_fun_from_wpgen]
    which we used for reasoning about top-level functions. Up to minor
    alpha-renaming, it is as shown below. It enables establishing a triple
    for an application [trm_app vf vx] with precondition [H'] and postcondition
    [Q'] from the premise [H' ==> wgen ((x,vx)::nil) t1 Q']. *)

Parameter triple_app_fun_from_wpgen : forall vf vx x t1 H' Q',
  vf = val_fun x t1 ->
  H' ==> wpgen ((x,vx)::nil) t1 Q' ->
  triple (trm_app vf vx) H' Q'.

(** It therefore makes sense, in our definition of the predicate
    [wpgen (trm_fun x t1) Q], which we said would take the form
    [\forall vf, \[P vf] \-* Q vf], to define [P vf] as:

[[
    forall vx H' Q', (H' ==> wpgen ((x,vx)::nil) t1 Q') ->
                     triple (trm_app vf vx) H' Q'
]]

*)

(** Overall, the definition of [wpgen E t] is as follows. (The occurence of
    [nil] is replaced with [E] to account for the case of a nonempty context.)

[[
  Fixpoint wpgen (E:ctx) (t:trm) : formula :=
    mkstruct match t with
    ...
    | trm_fun x t1 => fun Q =>
        let P vf :=
          (forall vx H' Q', (H' ==> wpgen ((x,vx)::E) t1 Q') ->
                            triple (trm_app vf vx) H' Q') in
        \forall vf, \[P vf] \-* Q vf
    ...
    end.
]]

*)

(** The actual definition of [wpgen] exploits an intermediate definition,
    called [wpgen_fun] and defined below.

[[
    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct match t with
      ...
      | trm_fun x t1 => wpgen_fun (fun vx => wpgen ((x,vx)::E) t1)
      ...
      end.
]]

*)

Definition wpgen_fun (Fof:val->formula) : formula := fun Q =>
  \forall vf,
      \[forall vx H' Q', (H' ==> Fof vx Q') -> triple (trm_app vf vx) H' Q']
  \-* Q vf.

(** The soundness lemma for this construct is as follows. *)

Lemma wpgen_fun_sound : forall x t1 Fof,
  (forall vx, formula_sound (subst x vx t1) (Fof vx)) ->
  formula_sound (trm_fun x t1) (wpgen_fun Fof).
Proof using.
  introv M. intros Q. unfolds wpgen_fun. applys himpl_hforall_l (val_fun x t1).
  xchange hwand_hpure_l_intro.
  { introv N. rewrite <- wp_equiv. applys himpl_trans_r.
    { applys* wp_app_fun. } { xchanges N. applys* M. } }
  { applys wp_fun. }
Qed.

(** When we carry out the proof of soundness for the presented of [wpgen]
    featuring [wpgen_fun], we obtain the following proof obligation.
    (This proof obligation appears in lemma [wpgen_sound] in file [SLFDirect.v].) *)

Lemma wpgen_fun_proof_obligation : forall E x t1,
  (forall E, formula_sound (isubst E t1) (wpgen E t1)) ->
  formula_sound (trm_fun x (isubst (rem x E) t1)) (wpgen_fun (fun v => wpgen ((x,v)::E) t1)).

(** The proof exploits the lemma [wpgen_fun_sound] that we just established,
    as well as a substitution lemma, the same as the one used to justify the
    soundness of the [wpgen] of a let-binding. *)

Proof using.
  introv IH. applys wpgen_fun_sound.
  { intros vx. rewrite <- isubst_rem. applys IH. }
Qed.

(** This completes our presentation of a version of [wpgen] that recursively
    processes the local definition of non-recursive functions. *)

(** Remark: the following variant of [wpgen_fun] enables deriving instances
    of [wp (trm_app vf vx)] rather than instances of [triple (trm_app vf vx)]. *)

Definition wpgen_fun' (Fof:val->formula) : formula := fun Q =>
  \forall vf, \[forall vx Q', Fof vx Q' ==> wp (trm_app vf vx) Q'] \-* Q vf.

(** This variant is completely equivalent to the previous version, and has the
    benefits that it is slightly more concise. It requires however a bit more
    effort for the use to exploit it. That said, when the manipulations of the
    formulae produced by [wpgen] are performed by x-tactic, then it does not
    make a difference to the end-user which variant of the definition is used. *)


(* ------------------------------------------------------- *)
(** *** 2. Treatment of recursive functions *)

(** The formula produced by [wpgen] for a recursive function [trm_fix f x t1]
    is almost the same as for a non-recursive function, the main difference being
    that we need to add a binding in the context to associated the name [f] of the
    recursive function with the value [vf] that corresponds to the recursive function.

    Here again, the heap predicate [wpgen (trm_fun x t1) Q] will be of the
    form [\forall vf, \[P vf] \-* Q vf].

    To figure out the details of the statement of [P], recall from [SLFWPgen]
    the statement of [triple_app_fix_from_wpgen], which is useful for reasoning
    about top-level recursive functions. Up to minor alpha-renaming, the lemma
    statement is as shown below. *)

Parameter triple_app_fix_from_wpgen : forall vf vx f x t1 H Q,
  vf = val_fix f x t1 ->
  H ==> wpgen ((f,vf)::(x,vx)::nil) t1 Q ->
  triple (trm_app vf vx) H Q.

(** It therefore makes sense to define [P vf] as:

[[
    forall vx H' Q', (H' ==> wpgen ((f,vf)::(x,vx)::nil) t1 Q') ->
                     triple (trm_app vf vx) H' Q'
]]

*)

(** We thus consider:

[[
    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct match t with
      | ..
      | trm_fun x t1 => wpgen_fix (fun vf v => wpgen ((f,vf)::(x,v)::E) t1)
      | ..
      end
]]

    with the definition of [wpgen_fix] as follows. *)

Definition wpgen_fix (Fof:val->val->formula) : formula := fun Q =>
  \forall vf,
    \[forall vx H' Q', (H' ==> Fof vf vx Q') -> triple (trm_app vf vx) H' Q']
  \-* Q vf.

(** The corresponding soundness lemma for this construct appears next. *)

Lemma wpgen_fix_sound : forall f x t1 Fof,
  (forall vf vx, formula_sound (subst x vx (subst f vf t1)) (Fof vf vx)) ->
  formula_sound (trm_fix f x t1) (wpgen_fix Fof).
Proof using.
  introv M. intros Q. unfolds wpgen_fix. applys himpl_hforall_l (val_fix f x t1).
  xchange hwand_hpure_l_intro.
  { introv N. rewrite <- wp_equiv. applys himpl_trans_r.
    { applys* wp_app_fix. } { xchange N. applys* M. } }
  { applys wp_fix. }
Qed.

(** The proof of soundness of [wpgen] involves the following proof obligation. *)

Lemma wpgen_fix_proof_obligation : forall E f x t1,
  (forall E, formula_sound (isubst E t1) (wpgen E t1)) ->
  formula_sound (trm_fix f x (isubst (rem x (rem f E)) t1))
                    (wpgen_fix (fun vf vx => wpgen ((f,vf)::(x,vx)::E) t1)).
Proof using.
  introv IH. applys wpgen_fix_sound.
  { intros vf vx. rewrite <- isubst_rem_2. applys IH. }
Qed.

(** Again, we refer to the proof of lemma [wpgen_sound] in file [SLFDirect]
    for the full proof of the definition of [wpgen] featuring [wpgen_fix]. *)

(** Remark: here again, an alternative, more concise definition is possible. *)

Definition wpgen_fix' (Fof:val->val->formula) : formula := fun Q =>
  \forall vf, \[forall vx Q', Fof vf vx Q' ==> wp (trm_app vf vx) Q'] \-* Q vf.

End WPgenRec.


(* ******************************************************* *)
(** ** Benefits of the ramified rule over the consequence-frame rule *)

Module WandBenefits.
Import WandDef.

(** Recall the consequence-frame rule *)

Parameter triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.

(** One practical caveat with this rule is that we must resolve [H2],
    which corresponds to the difference between [H] and [H1].
    In practice, providing [H2] explicitly is extremely tedious.
    The alternative is to leave [H2] as an evar, and count on the
    fact that the tactic [xsimpl], when applied to [H ==> H1 \* H2],
    will correctly instantiate [H2].

    This approach works, but is relatively fragile, as evars may get
    instantiated in undesired ways. Moreover, evars depend on the context
    at the time of their creation, and they must be instantiated with
    values from that context. Yet, for example, if [H] contains existential
    quantifiers at the moment of applying the consequence-frame rule,
    then extracting those quantifiers after the rule is applied makes
    it almost impossible to instantiate [H2] correctly.

    To illustrate the problem on a concrete example, recall the
    specification of [ref]. *)

Parameter triple_ref : forall (v:val),
  triple (val_ref v)
    \[]
    (fun r => \exists (l:loc), \[r = val_loc l] \* l ~~~> v).

(** Assume that wish to derive the following triple, which
    extends both the precondition and the postcondition with
    [\exists l' v', l' ~~~> v']. *)

Lemma triple_ref_with_nonempty_pre : forall (v:val),
  triple (val_ref v)
    (\exists l' v', l' ~~~> v')
    (fun r => \exists (l:loc), \[r = val_loc l] \* l ~~~> v \*
              \exists l' v', l' ~~~> v').
Proof using.
  intros. applys triple_conseq_frame.
  (* observe the evar [?H2] in second and third goals *)
  { applys triple_ref. }
  { (* here, [?H2] should be in theory instantiated with the RHS.
       but [xsimpl] strategy is to first extract the quantifiers
       from the LHS. After that, the instantiation of [H2] fails. *)
    xsimpl.
Abort.

(** Now, let us apply the ramified frame rule for the same goal. *)

Lemma triple_ref_with_nonempty_pre' : forall (v:val),
  triple (val_ref v)
    (\exists l' v', l' ~~~> v')
    (fun r => \exists (l:loc), \[r = val_loc l] \* l ~~~> v \*
              \exists l' v', l' ~~~> v').
Proof using.
  intros. applys triple_ramified_frame.
  { applys triple_ref. }
  { xsimpl. intros l' v'. rewrite qwand_equiv. xsimpl. auto. }
Qed.

(** For a further comparison between the consequence-frame rule
    and the ramified frame rule, consider the following example.

    Assume we want to frame the specification [triple_ref] with [l' ~~~> v'],
    that is, add this predicate to both the precondition and the postcondition.
    First, let's do it with the consequence-frame rule. *)

Lemma triple_ref_with_consequence_frame : forall (l':loc) (v':val) (v:val),
  triple (val_ref v)
    (l' ~~~> v')
    (fun r => \exists (l:loc), \[r = val_loc l] \* l ~~~> v \* l' ~~~> v').
Proof using.
  intros. applys triple_conseq_frame.
  (* observe the evar [?H2] in second and third goals *)
  { applys triple_ref. }
  { xsimpl. (* instantiates the evar [H2] *) }
  { xsimpl. auto. }
Qed.

(** Now, let's carry out the same proof using the ramified frame rule. *)

Lemma triple_ref_with_ramified_frame : forall (l':loc) (v':val) (v:val),
  triple (val_ref v)
    (l' ~~~> v')
    (fun r => \exists (l:loc), \[r = val_loc l] \* l ~~~> v \* l' ~~~> v').
Proof using.
  intros. applys triple_ramified_frame.
  { applys triple_ref. }
  { rewrite hstar_hempty_l. rewrite qwand_equiv.
    (* Remark: the first two steps above will be automatically
       carried out by [xsimpl], in subsequent chapters. *)
    (* Here, we read the same state as in the previous proof. *)
    xsimpl. auto. }
Qed.

(** Again, observe how we have been able to complete the same proof
    without involving any evar. *)

End WandBenefits.


(* ******************************************************* *)
(** ** Properties of [hwand] *)

Module WandProperties.
Import WandDef.

(** We next present the most important properties of [H1 \-* H2].
    The tactic [xsimpl] provides dedicated support for
    simplifying expressions involving magic wand. So,
    in most proofs, it is not required to manually manipulate
    the lemmas capturing properties of the magic wand.
    Nevertheless, there are a few situations where [xsimpl]
    won't automatically perform the desired manipulation.
    In such cases, the tactic [xchange] proves very useful.

    In what follows, [xsimpl] and [xchange] do not simplify
    expressions involving magic wands. *)

(* ------------------------------------------------------- *)
(** *** Structural properties of [hwand] *)

(** [H1 \-* H2] is covariant in [H2], and contravariant in [H1]
    (like an implication). *)

Lemma hwand_himpl : forall H1 H1' H2 H2',
  H1' ==> H1 ->
  H2 ==> H2' ->
  (H1 \-* H2) ==> (H1' \-* H2').
Proof using.
  introv M1 M2. applys himpl_hwand_r. xchange M1.
  xchange (hwand_cancel H1 H2). applys M2.
Qed.

(** Two predicates [H1 \-* H2] ans [H2 \-* H3] may simplify
    to [H1 \-* H3]. This simplification is reminiscent of the
    arithmetic operation [(-H1 + H2) + (-H2 + H3) = (-H1 + H3)]. *)

Lemma hwand_trans_elim : forall H1 H2 H3,
  (H1 \-* H2) \* (H2 \-* H3) ==> (H1 \-* H3).
Proof using.
  intros. applys himpl_hwand_r. xchange (hwand_cancel H1 H2).
Qed.

(** The predicate [H \-* H] holds of the empty heap.
    Intuitively [(-H + H)] can be replaced with zero. *)

Lemma himpl_hempty_hwand_same : forall H,
  \[] ==> (H \-* H).
Proof using. intros. apply himpl_hwand_r. xsimpl. Qed.


(* ------------------------------------------------------- *)
(** *** Tempting yet false properties for [hwand] *)

(** The reciprocal entailment to the elimination lemma,
    that is, [H2 ==> H1 \* (H1 \-* H2)] does not hold.

    As counter-example, consider [H2 = \[]] and [H1 = \[False]].
    We can prove that the empty heap does not satisfies
    [\[False] \* (\[False] \-* \[])]. *)

Lemma not_himpl_hwand_r_inv_reciprocal : exists H1 H2,
  ~ (H2 ==> H1 \* (H1 \-* H2)).
Proof using.
  exists \[False] \[]. intros N. forwards K: N (Fmap.empty:heap).
  applys hempty_intro. rewrite hstar_hpure in K. destruct K. auto.
Qed.

(** More generally, one has to be suspicious of any entailment
    that introduces wands out of nowhere.

    The entailment [hwand_trans_elim]:
    [(H1 \-* H2) \* (H2 \-* H3) ==> (H1 \-* H3)]
    is correct because, intuitively, the left-hand-side captures
    that [H1 <= H2] and that [H1 <= H3] (for some vaguely-defined
    notion of [<=]), from which one derive [H1 <= H3] and justify
    that the right-hand-side makes sense.

    On the contrary, the reciprocal entailment
    [(H1 \-* H3) ==> (H1 \-* H2) \* (H2 \-* H3)]
    is certainly false, because from [H1 <= H3] there is no way
    to justify [H1 <= H2] nor [H2 <= H3]. *)


(* ------------------------------------------------------- *)
(** *** Interaction of [hwand] with [hempty] and [hpure] *)

(** [\[] \-* H] is equivalent to [H]. *)

Lemma hwand_hempty_l : forall H,
  (\[] \-* H) = H.
Proof using.
  intros. unfold hwand. xsimpl.
  { intros H0 M. xchange M. }
  { xsimpl. }
Qed.

(** Assume that [\[P] \-* H] holds of a heap.
    To show that [H] holds of this same heap, it suffices
    ot justify that the proposition [P] is true. Formally: *)

Lemma hwand_hpure_l_intro : forall P H,
  P ->
  (\[P] \-* H) ==> H.
Proof using.
  introv HP. unfold hwand. xsimpl.
  intros H0 M. xchange M. applys HP.
Qed.
   (* Note: here is an alterntive proof w.r.t. [hwand]:
    introv HP. unfold hwand. intros h K.
    forwards M: K (Fmap.empty:heap).
    { apply Fmap.disjoint_empty_r. }
    { applys hpure_intro HP. }
    { rewrite Fmap.union_empty_r in M. applys M. } *)

(** [\[P] \-* H] can be proved of a heap if [H] can be proved
   of this heap under the assumption [P]. Formally: *)

Lemma hwand_hpure_r_intro : forall H1 H2 P,
  (P -> H1 ==> H2) ->
  H1 ==> (\[P] \-* H2).
Proof using. introv M. applys himpl_hwand_r. xsimpl. applys M. Qed.

(* EX1! (himpl_hwand_hpure_lr) *)
(** Prove that [\[P1 -> P2]] entails [\[P1] \-* \[P2]]. *)

Lemma himpl_hwand_hpure_lr : forall (P1 P2:Prop),
  \[P1 -> P2] ==> (\[P1] \-* \[P2]).
Proof using.
(* ADMITTED *)
  intros. unfold hwand. xpull. intros M.
  xsimpl \[P1->P2]. { applys M. } xsimpl. auto.
Qed. (* /ADMITTED *)

(** [] *)


(* ------------------------------------------------------- *)
(** *** Interaction of [hwand] with [hstar] *)

(** The heap predicates [(H1 \* H2) \-* H3] and [H1 \-* (H2 \-* H3)]
    and [H2 \-* (H1 \-* H3)] are all equivalent. Intuitively, they all
    describe the predicate [H3] with the missing pieces [H1] and [H2].

    The equivalence between the uncurried form [(H1 \* H2) \-* H3]
    and the curried form [H1 \-* (H2 \-* H3)] is formalized by the
    lemma shown below. The third form [H2 \-* (H1 \-* H3)] follows
    from the commutativity property [H1 \* H2 = H2 \* H1]. *)

Lemma hwand_curry_eq : forall H1 H2 H3,
  (H1 \* H2) \-* H3 = H1 \-* (H2 \-* H3).
Proof using.
  intros. applys himpl_antisym.
  { apply himpl_hwand_r. apply himpl_hwand_r.
    xchange (hwand_cancel (H1 \* H2) H3). }
  { apply himpl_hwand_r. xchange (hwand_cancel H1 (H2 \-* H3)).
    xchange (hwand_cancel H2 H3). }
Qed.

(** If a heap satisfies [H1 \-* H2] and another heap
    satisfies [H3], then their disjoint union satisfies
    [H1 \-* (H2 \* H3)]. In both views, if [H1] is provided,
    then both [H2] and [H3] can be obtained. *)

Lemma hstar_hwand : forall H1 H2 H3,
  (H1 \-* H2) \* H3 ==> H1 \-* (H2 \* H3).
Proof using.
  intros. applys himpl_hwand_r. xsimpl. xchange (hwand_cancel H1 H2).
Qed.

(** Remark: the reciprocal entailment is false. *)


(* ------------------------------------------------------- *)
(** *** Exercises on [hwand] *)

(* EX1! (himpl_hwand_hstar_same_r) *)
(** Prove that [H1] entails [H2 \-* (H2 \* H1)]. *)

Lemma himpl_hwand_hstar_same_r : forall H1 H2,
  H1 ==> (H2 \-* (H2 \* H1)).
Proof using.
(* ADMITTED *)
  intros. applys himpl_hwand_r. xsimpl.
Qed. (* /ADMITTED *)

(** [] *)

(* EX2! (hwand_cancel_part) *)
(** Prove that [H1 \* ((H1 \* H2) \-* H3)] simplifies to [H2 \-* H3]. *)

Lemma hwand_cancel_part : forall H1 H2 H3,
  H1 \* ((H1 \* H2) \-* H3) ==> (H2 \-* H3).
Proof using.
(* ADMITTED *)
  intros. applys himpl_hwand_r. xchange (hwand_cancel (H1 \* H2)).
Qed. (* /ADMITTED *)

(** [] *)


(* ******************************************************* *)
(** ** Properties of [hforall] *)

(** To prove that a heap satisfies [\forall x, J x], one must
    show that, for any [x], this heap satisfies [J x]. *)

Lemma himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (\forall x, J x).
Proof using. introv M. intros h K x. apply~ M. Qed.

(** Assuming a heap satisfies [\forall x, J x], one can derive
    that the same heap satisfies [J v] for any desired value [v]. *)

Lemma hforall_specialize : forall A (v:A) (J:A->hprop),
  (\forall x, J x) ==> (J v).
Proof using. intros. intros h K. apply* K. Qed.

(** The lemma above can equivalently be formulated in the following way. *)

Lemma himpl_hforall_l : forall A (v:A) (J:A->hprop) H,
  J v ==> H ->
  (\forall x, J x) ==> H.
Proof using. introv M. applys himpl_trans M. applys hforall_specialize. Qed.


(* ******************************************************* *)
(** ** Properties of [qwand] *)

(* ------------------------------------------------------- *)
(** *** Main properties of [qwand] *)

(** We first state the introduction and elimination lemmas
    analogous to [himpl_hwand_r], [himpl_hwand_r_inv], and [hwand_cancel]. *)

Lemma himpl_qwand_r : forall H Q1 Q2,
  (Q1 \*+ H) ===> Q2 ->
  H ==> (Q1 \--* Q2).
Proof using. introv M. rewrite* qwand_equiv. Qed.

Lemma himpl_qwand_r_inv : forall H Q1 Q2,
  H ==> (Q1 \--* Q2) ->
  (Q1 \*+ H) ===> Q2.
Proof using. introv M. rewrite* <- qwand_equiv. Qed.

(** Like [hwand], [qwand] is covariant in its second argument,
    and contravariant in its first argument. *)

Lemma qwand_himpl : forall Q1 Q1' Q2 Q2',
  Q1' ===> Q1 ->
  Q2 ===> Q2' ->
  (Q1 \--* Q2) ==> (Q1' \--* Q2').
Proof using.
  introv M1 M2. applys himpl_qwand_r. intros x.
  xchange (qwand_specialize x). applys himpl_hwand_r_inv.
  applys hwand_himpl. { applys M1. } { applys M2. }
Qed.

(** If a heap satisfies [Q1 \--* Q2] and another heap
    satisfies [H], then their disjoint union satisfies
    [Q1 \--* (Q2 \*+ H)]. In both views, if [Q1] is provided,
    then both [Q2] and [H] can be obtained. *)

Lemma hstar_qwand : forall Q1 Q2 H,
  (Q1 \--* Q2) \* H ==> Q1 \--* (Q2 \*+ H).
Proof using.
  intros. applys himpl_qwand_r. xchange (@qwand_cancel Q1).
Qed.


(* ------------------------------------------------------- *)
(** *** Exercices on [qwand] *)

(* EX1! (himpl_qwand_hstar_same_r) *)
(** Prove that [H] entails [Q \--* (Q \*+ H)]. *)

Lemma himpl_qwand_hstar_same_r : forall H Q,
  H ==> Q \--* (Q \*+ H).
Proof using.
(* ADMITTED *)
  intros. applys himpl_qwand_r. xsimpl.
Qed. (* /ADMITTED *)

(** [] *)

(* EX2! (qwand_cancel_part) *)
(** Prove that [H \* ((Q1 \*+ H) \--* Q2)] simplifies to [Q1 \--* Q2]. *)

Lemma qwand_cancel_part : forall H Q1 Q2,
  H \* ((Q1 \*+ H) \--* Q2) ==> (Q1 \--* Q2).
Proof using.
(* ADMITTED *)
  intros. applys himpl_qwand_r. intros x.
  xchange (qwand_specialize x).
  xchange (hwand_cancel (Q1 x \* H)).
Qed. (* /ADMITTED *)

(** [] *)


(* ******************************************************* *)
(** ** Equivalence between the definitions of magic wand *)

(** In what follows we prove the equivalence between the three
    characterizations of [hwand H1 H2] that we have presented:

    1. [fun h => forall h', Fmap.disjoint h h' -> H1 h' -> H2 (h \u h')]

    2. [\exists H0, H0 \* \[ (H0 \* H1) ==> H2]]

    3. [forall H0 H1 H2, (H0 ==> hwand H1 H2) <-> (H0 \* H1 ==> H2)].

    To prove the 3-way equivalence, we first prove the equivalence
    between (1) and (2), then prove the equivalence between (2) and (3).
*)

(** Let us first prove that [hwand] is equivalent to [hwand'],
    i.e., that (1) and (2) are equivalent definitions. *)

Lemma hwand_eq_hwand'_details :
  hwand = hwand'.
Proof using.
  apply pred_ext_3. intros H1 H2 h. unfold hwand, hwand'. iff M.
  { intros h1 D K1. destruct M as (H0&M).
    destruct M as (h0&h2&K0&K2&D'&U).
    lets (N&E): hpure_inv (rm K2). subst h h2.
    rewrite Fmap.union_empty_r in *.
    applys N. applys hstar_intro K0 K1 D. }
  { exists (=h). rewrite hstar_comm. rewrite hstar_hpure. split.
    { intros h3 K3. destruct K3 as (h1&h2&K1&K2&D&U).
      subst h1 h3. applys M D K2. }
    { auto. } }
Qed.

(** According to definition (3), an operator [op] is a magic wand
   if and only if, for any [H0], [H1], [H2], it satisfies the
   equivalence [(H0 ==> op H1 H2) <-> (H0 \* H1 ==> H2)]. Formally: *)

Definition hwand_characterization (op:hprop->hprop->hprop) :=
  forall H0 H1 H2, (H0 ==> op H1 H2) <-> (H0 \* H1 ==> H2).

(** We prove that an operator [op] satisfies [hwand_characterization]
    if and only if it is equal to [hwand]. *)

Lemma hwand_characterization_iff_eq_hwand : forall op,
  hwand_characterization op <-> op = hwand.
Proof using.
  iff Hop.
  { apply fun_ext_2. intros H1 H2.
    unfolds hwand_characterization, hwand. apply himpl_antisym.
    { lets (M&_): (Hop (op H1 H2) H1 H2). xsimpl (op H1 H2).
      applys M. applys himpl_refl. }
    { xsimpl. intros H0 M. rewrite Hop. applys M. } }
  { subst. unfolds hwand_characterization, hwand.
    intros H0 H1 H2. iff M. { xchange* M. } { xsimpl~ H0. } }
Qed.

(** Remark: the right-to-left direction was "too easy" to prove.
    It's because [xsimpl] is doing all the work for us.
    Here is a detailed proof not using [xsimpl]. *)

Lemma hwand_characterization_hwand_details : forall H0 H1 H2,
  (H0 ==> hwand H1 H2) <-> (H0 \* H1 ==> H2).
Proof using.
  intros. unfold hwand. iff M.
  { applys himpl_trans. applys himpl_frame_l M.
    rewrite hstar_hexists. applys himpl_hexists_l. intros H3.
    rewrite (hstar_comm H3). rewrite hstar_assoc.
    applys himpl_hstar_hpure_l. intros N. applys N. }
  { applys himpl_hexists_r H0. rewrite hstar_comm.
    applys himpl_hstar_hpure_r. applys M. applys himpl_refl. }
Qed.

End WandProperties.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Bonus contents (optional reading) *)

(* ******************************************************* *)
(** ** Texan triples *)

Module TexanTriples.

Implicit Types v : val.

(* ------------------------------------------------------- *)
(** *** 1. Example of Texan triples *)

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
Proof using. intros. rewrite wp_equiv. applys triple_ref. Qed.

(** The statement can be reformulated with the aim of making the RHS of the
    form [wp (val_ref v) Q] for an abstract [Q]. *)

Lemma wp_ref_1 : forall Q v,
  ((fun r => \exists l, \[r = val_loc l] \* l ~~~> v) \--* Q) ==> wp (val_ref v) Q.
Proof using. intros. xchange (wp_ref_0 v). applys wp_ramified. Qed.

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
  intros. rewrite <- wp_equiv. iff M.
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

(* ADMITTED *)
Lemma wp_incr : forall (p:loc) (n:int) Q,
  (p ~~~> n) \* (p ~~~> (n+1) \-* Q val_unit) ==> wp (trm_app incr p) Q.
Proof using.
  intros. rewrite wp_equiv. applys triple_conseq_frame.
  { applys triple_incr. } { xsimpl. } { xsimpl. intros ? ->. auto. }
Qed. (* /ADMITTED *)

(** [] *)

(** Remark: texan triples are used in Iris. *)

End TexanTriples.


(* ******************************************************* *)
(** ** Direct proof of [wp_ramified] directly from Hoare triples *)

Module WpFromHoare.
Import WandDef.

(** In the first part of this chapter, we proved the rule [wp_ramified]
    from the combined consequence-frame rule for triples.

    Recall from the last section of the chapter [SLFWPsem] that it can
    be interesting to define [wp]-style rules directly from the [hoare]
    rules, so as to bypass the statements and proofs of rules for triples.

    In that vein, let us establish the rule [wp_ramified] directly
    from the Hoare logic rules. *)

Lemma wp_ramified : forall t Q1 Q2,
  (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).
Proof using.
  intros. unfold wp. xpull. intros H M.
  xsimpl (H \* (Q1 \--* Q2)). intros H'.
  applys hoare_conseq M. { xsimpl. }
  intros r. xchange (qwand_specialize r). xsimpl.
  rewrite hstar_comm. applys hwand_cancel.
Qed.

End WpFromHoare.


(* ******************************************************* *)
(** ** Conjunction and disjunction operators on [hprop] *)

Module ConjDisj.
Import WandDef.

(* ------------------------------------------------------- *)
(** *** Definition of [hor] *)

(** For some advanced applications, it is useful to lift the
    disjunction operation [P1 \/ P2] from [Prop] to [hprop].

    The heap predicate [hor H1 H2] describes a heap that
    satisfies [H1] or [H2] (possibly both).

    An obvious definition for it is: *)

Definition hor' (H1 H2 : hprop) : hprop :=
  fun h => H1 h \/ H2 h.

(** An alternative definition leverages [\exists] to quantify
    over a boolean indicating whether [H1] or [H2] should hold.
    The benefits of this definition is that the proof of its
    properties can be established without manipulating heaps. *)

Definition hor (H1 H2 : hprop) : hprop :=
  \exists (b:bool), if b then H1 else H2.

(* EX2! (hor_eq_hor') *)
(** Prove the equivalence of the definitions [hor] and [hor']. *)

Lemma hor_eq_hor' :
  hor = hor'.
Proof using.
(* ADMITTED *)
  applys fun_ext_2. intros H1 H2. unfold hor, hor'. applys himpl_antisym.
  { xsimpl. intros b h K. destruct b. { left*. } { right*. } }
  { intros h K. destruct K. { exists* true. } { exists* false. } }
Qed. (* /ADMITTED *)

(** [] *)

(** The introduction and elimination rules for [hor] are as follows. *)

Lemma himpl_hor_r_r : forall H1 H2,
  H1 ==> hor H1 H2.
Proof using. intros. unfolds hor. exists* true. Qed.

Lemma himpl_hor_r_l : forall H1 H2,
  H2 ==> hor H1 H2.
Proof using. intros. unfolds hor. exists* false. Qed.

Lemma himpl_hor_l : forall H1 H2 H3,
  H1 ==> H3 ->
  H2 ==> H3 ->
  hor H1 H2 ==> H3.
Proof using.
  introv M1 M2. unfolds hor. applys himpl_hexists_l. intros b. case_if*.
Qed.

(** The operator [hor] is commutative. To establish this property, it is
    handy to exploit the following lemma, called [if_neg], which swaps the
    two branches of a conditional by negating the boolean condition. *)

Lemma if_neg : forall (b:bool) A (X Y:A),
  (if b then X else Y) = (if neg b then Y else X).
Proof using. intros. case_if*. Qed.

(* EX2! (hor_comm) *)
(** Prove that [hor] is a symmetric operator.
    Hint: exploit [hprop_op_comm] (from chapter [SLFHimpl]) and [if_neg]. *)

Lemma hor_comm : forall H1 H2,
  hor H1 H2 = hor H2 H1.
Proof using.
(* ADMITTED *)
  applys hprop_op_comm. intros. unfold hor.
  xpull. intros b. rewrite if_neg. xsimpl.
Qed. (* /ADMITTED *)

(** [] *)


(* ------------------------------------------------------- *)
(** *** Definition of [hand] *)

(** Likewise, we lift the conjunction operation [P1 /\ P2] from
    [Prop] to [hprop].

    The heap predicate [hand H1 H2], called the "non-separating
    conjunction", describes a heap that satisfies both [H1] and [H2]
    at the same time.

    An obvious definition for it is: *)

Definition hand' (H1 H2 : hprop) : hprop :=
  fun h => H1 h /\ H2 h.

(** An alternative definition leverages [\forall] to
    non-deterministically quantify over a boolean indicating
    whether [H1] or [H2] should hold. This the quantification
    is over all booleans, both must hold. *)

Definition hand (H1 H2 : hprop) : hprop :=
  \forall (b:bool), if b then H1 else H2.

(* EX2! (hand_eq_hand') *)
(** Prove the equivalence of the definitions [hand] and [hand']. *)

Lemma hand_eq_hand' :
  hand = hand'.
Proof using.
(* ADMITTED *)
  applys fun_ext_2. intros H1 H2. unfold hand, hand', hforall.
  applys himpl_antisym.
  { intros h N. split. { applys N true. } { applys N false. } }
  { intros h (K1&K2) b. case_if. { applys K1. } { applys K2. } }
Qed. (* /ADMITTED *)

(** [] *)

(** The introduction and elimination rules for [hand] are as follows. *)

Lemma himpl_hand_l_r : forall H1 H2,
  hand H1 H2 ==> H1.
Proof using. intros. unfolds hand. applys* himpl_hforall_l true. Qed.

Lemma himpl_hand_l_l : forall H1 H2,
  hand H1 H2 ==> H2.
Proof using. intros. unfolds hand. applys* himpl_hforall_l false. Qed.

Lemma himpl_hand_r : forall H1 H2 H3,
  H1 ==> H2 ->
  H1 ==> H3 ->
  H1 ==> hand H2 H3.
Proof using. introv M1 M2 Hh. intros b. case_if*. Qed.

(* EX1! (hand_comm) *)
(** Prove that [hand] is a symmetric operator. *)

Lemma hand_comm : forall H1 H2,
  hand H1 H2 = hand H2 H1.
Proof using.
(* ADMITTED *)
  applys hprop_op_comm. intros. unfold hand, hforall. intros h K b.
  rewrite if_neg. applys K.
Qed. (* /ADMITTED *)

(** [] *)

End ConjDisj.


(* ******************************************************* *)
(** ** Summary of all Separation Logic operators *)

Module SummaryHprop.

(** The core operators are defined as function over heaps. *)

  Definition hempty : hprop :=
    fun h => (h = Fmap.empty).

  Definition hpure (P:Prop) : hprop :=
    fun h => (h = Fmap.empty) /\ P.

  Definition hsingle (l:loc) (v:val) : hprop :=
    fun h => (h = Fmap.single l v).

  Definition hstar (H1 H2 : hprop) : hprop :=
    fun h => exists h1 h2, H1 h1
                                /\ H2 h2
                                /\ Fmap.disjoint h1 h2
                                /\ h = Fmap.union h1 h2.

  Definition hexists A (J:A->hprop) : hprop :=
    fun h => exists x, J x h.

  Definition hforall (A : Type) (J : A -> hprop) : hprop :=
    fun h => forall x, J x h.

(** The remaining operators can be defined either as function over
    heaps, or as derived definition expressed in terms of the core
    operators defined above. *)

(** Direct definition for the remaining operators. *)

Module ReaminingOperatorsDirect.

  Definition hwand (H1 H2:hprop) : hprop :=
    fun h => forall h', Fmap.disjoint h h' -> H1 h' -> H2 (h \u h').

  Definition qwand A (Q1 Q2:A->hprop) : hprop :=
    fun h => forall x h', Fmap.disjoint h h' -> Q1 x h' -> Q2 x (h \u h').

  Definition hor (H1 H2 : hprop) : hprop :=
    fun h => H1 h \/ H2 h.

  Definition hand (H1 H2 : hprop) : hprop :=
    fun h => H1 h /\ H2 h.

End ReaminingOperatorsDirect.

(** Alternative definitions for the same operators, expressed in terms
    of the core operators. *)

Module ReaminingOperatorsDerived.

  Definition hpure (P:Prop) : hprop :=
    \exists (p:P), \[].

  Definition hwand (H1 H2 : hprop) : hprop :=
    \exists H0, H0 \* \[ (H0 \* H1) ==> H2].

  Definition qwand A (Q1 Q2:A->hprop) : hprop :=
    \forall x, (Q1 x) \-* (Q2 x).

  Definition hand (H1 H2 : hprop) : hprop :=
    \forall (b:bool), if b then H1 else H2.

  Definition hor (H1 H2 : hprop) : hprop :=
    \exists (b:bool), if b then H1 else H2.

End ReaminingOperatorsDerived.

(** In pratice, it saves a lot of effort to use the derived definitions,
    because using derived definitions all the properties of these definitions
    can be established with the help of the [xsimpl] tactic, through reasoning
    taking place exclusively at the level of [hprop]. *)

End SummaryHprop.

