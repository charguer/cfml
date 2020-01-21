(**

Separation Logic Foundations

Chapter: "Affine".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require SLFRules.
From Sep Require Export SLFDirect.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Chapter in a rush *)

(** The Separation Logic framework that we have constructed is well-suited
    for a language with explicit deallocation, but cannot be used as such for
    a language equipped with a garbage collector. As we pointed out in the
    chapter [SLFBasic], there is no rule in Separation Logic that allows
    discarding a heap predicate from the precondition or the postcondition.

    In this chapter, we explain how to generalize the Separation Logic
    framework to support a "garbage collection rule", which one may invoke
    in the logic to discard predicates describing allocated data, thereby
    reflecting on the action of the garbage collector. The resulting
    framework is said to describe an "affine" logic, as opposed to a "linear"
    logic.

    This chapter is organized as follows:

    - first, we recall the example demonstrating the need for a new rule,
    - second, we present the statement of the "garbage collection rule",
    - third, we show how to refine the definition of Separation Logic
      triples, so as to accomodate the new rule.

    Although in the present course we consider a language for which it is
    desirable that any heap predicate can be discarded, we will present
    general definitions allowing to fine-tune which heap predicates can
    be discarded and which cannot be discarded by the user. We will argue
    why such a fine-tuning may be interesting. *)


(* ########################################################### *)
(** ** Motivation for the garbage collection rule *)

Module MotivatingExample.
Export DemoPrograms.

(** Let us recall the example of the function [succ_using_incr_attempt]
    from chapter [SLFBasic]. This function allocates a reference with
    contents [n], then increments that reference, and finally returning
    its contents, that is, [n+1]. Let us revisit this example, with
    this time the intention of establishing for it a postcondition that
    does not leak the existence of a left-over reference cell.

[[
    let succ_using_incr n =
      let p = ref n in
      incr p;
      !p
]]

*)

Definition succ_using_incr :=
  VFun 'n :=
    Let 'p := 'ref 'n in
    incr 'p ';
    '! 'p.

(** In the framework developed so far, the heap predicate describing the
    reference cell allocated by the function cannot be discarded by the
    user, because the code does not feature a deallocation operation.
    As a result, the user is forced to include in the postcondition the
    description of a left-over reference. *)

Lemma Triple_succ_using_incr : forall (n:int),
  TRIPLE (succ_using_incr n)
    PRE \[]
    POST (fun r => \[r = n+1] \* \exists p, (p ~~~> (n+1))).
Proof using.
  xwp. xapp. intros ? p ->. xapp. xapp. xsimpl. auto.
Qed.

(** If we try to prove a specification that does not mention the left-over
    reference, we get stuck with a proof obligation of the form 
    [p ~~~> (n+1) ==> \[]]. *)

Lemma Triple_succ_using_incr' : forall (n:int),
  TRIPLE (succ_using_incr n)
    PRE \[]
    POST (fun r => \[r = n+1]).
Proof using.
  xwp. xapp. intros ? p ->. xapp. xapp. xsimpl. { auto. } (* stuck here *)
Abort.

(** This situation is desirable in a programming language with explicit
    deallocation, because it ensures that the code written by the
    programmer is not missing any deallocation operation. However, it is
    ill-suited for a programming language equipped with a garbage collector
    that performs deallocation automatically.

    In this chapter, we present an "affine" version of Separation Logic,
    where the above function [succ_using_incr_attempt] admits the
    postcondition [fun r => \[r = n+1]], and needs not mention the
    left-over reference. *)

End MotivatingExample.


(* ########################################################### *)
(** ** Statement of the garbage collection rule *)

(** There are several ways to state a "garbage collection rule" and its
    corrolaries. We present them next. *)

(** The most direct presentation of the "garbage collection rule" allows
    one to freely discard any piece of state from the postcondition.

    More precisely, this rule, named [triple_hany_post], asserts that an
    arbitrary heap predicate [H'] can be dropped from the postcondition. *)

Parameter triple_hany_post : forall t H H' Q,
  triple t H (Q \*+ H') ->
  triple t H Q.

(** A symmetric rule, named [triple_hany_pre], asserts that an arbitrary
    heap predicate [H'] can be dropped from the precondition. *)

Parameter triple_hany_pre : forall t H H' Q,
  triple t H Q ->
  triple t (H \* H') Q.

(** The rule [triple_hany_pre] is derivable from [triple_hany_post], by
    a simple application of the frame rule. Reciprocally, [triple_hany_post]
    is derivable from [triple_hany_post], however the proof is more involved
    (it appears in the bonus section). *)

(** Let us show that, using the rule [triple_hany_post], we can derive
    the desired specification for the motivating example from the
    specification that mentions the left-over postcondition. *)

Module MotivatingExampleSolved.
Export MotivatingExample.

Lemma Triple_succ_using_incr' : forall (n:int),
  TRIPLE (succ_using_incr n)
    PRE \[]
    POST (fun r => \[r = n+1]).
Proof using.
  intros. applys triple_hany_post. applys Triple_succ_using_incr.
Qed.

End MotivatingExampleSolved.


(* ########################################################### *)
(** ** Fine-grained control on collectable predicates *)

(** As suggested in the introduction, it may be useful to constraint
    the garbage collection rule so that it can be used to discard
    only certain types of heap predicates, but not all. For example,
    even in a programming language featuring a garbage collector,
    it may be useful to ensure that every file handle opened eventually
    gets closed, or that every lock acquired eventually gets released.
    File handles and locks are example of resources that may be
    described in Separation Logic, yet should not be freely discarded.

    As another example, consider the extension of Separation Logic with
    "time credits", which are used for complexity analysis. In such a
    setting, it is desirable to throw away a positive number of credits
    to reflect for over-approximations, however it must be ruled out to
    throw away negative number of credits, as this would compromise
    the soundness of the framework. *)

(** To constraint the garbage collection rule and allow fine-tuning
    of which heap predicates may be thrown away, we introduce the notion
    of "affine predicates", captured by a judgment written [haffine H].
    The idea is that only predicates satisyfing [haffine] may get freely
    discarded. *)

Parameter haffine : hprop -> Prop.

Parameter triple_haffine_post : forall t H H' Q,
  haffine H' ->
  triple t H (Q \*+ H') ->
  triple t H Q.

(** The variant of the garbage collection rule that operates on the
    precondition is constrained in a similar way. *)

Parameter triple_haffine_pre : forall t H H' Q,
  haffine H' ->
  triple t H Q ->
  triple t (H \* H') Q.

(** The definition of [haffine] should be set up in such a way that
    this predicate distributes in the expected way on each of the
    Separation Logic operators, as captured by the following lemma. *)

Parameter haffine_hempty :
  haffine \[].

Parameter haffine_hpure : forall P,
  haffine \[P].

Parameter haffine_hstar : forall H1 H2,
  haffine H1 ->
  haffine H2 ->
  haffine (H1 \* H2).

Parameter haffine_hexists : forall A (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\exists x, (J x)).

Parameter haffine_hforall : forall A `{Inhab A} (J:A->hprop),
  (forall x, haffine (J x)) ->
  haffine (\forall x, (J x)).

(** In addition, [haffine] distributes on the heap predicate [\[P] \* H] 
    by providing the hypothesis [P], because if a heap [h] satifies 
    [\[P] \* H] then it must be the case that the proposition [P] is true. *)

Parameter haffine_hstar_hpure : forall P H,
  (P -> haffine H) ->
  haffine (\[P] \* H).

(** We will present further on a template for defining [haffine] in
    a way that guarantees by construction that all these properties
    indeed hold. *)


(* ########################################################### *)
(** ** The garbage collection heap predicate *)

(** We now introduce a new heap predicate that is very handy for
    describing "pieces of heap to be garbage collected". We will
    use it to reformulate the garbage collection rule is a more
    concise and more usable way.

    This heap predicate is named [hgc] and is written [\GC].
    We define it as "some heap predicate [H] that satisfies [haffine]",
    as formalized next. *)

Definition hgc : hprop :=
  \exists H, \[haffine H] \* H.

Notation "\GC" := (hgc).

(** Observe that the heap predicate [\GC] is itself affine.
    Indeed, [\GC] denotes some heap [H] such that [haffine H] holds.
    Thus, by essence, it denotes an affine heap predicate. *)

Lemma haffine_hgc :
  haffine \GC.
Proof using.
  applys haffine_hexists. intros H. applys haffine_hstar_hpure. auto.
Qed.

(** Using the predicate [\GC], we can reformulate the constrained
    garbage collection rule [triple_haffine_post] as follows. *)

Parameter triple_hgc_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.

(** Not only is this rule more concise, it also has the benefits
    that the piece of heap discarded, previously described by [H']
    no longer needs to be provided upfront at the moment of applying
    the rule. It may be provided later on in the reasoning, by
    instantiating the existential quantifier carried into the
    definition of the [\GC] predicate, a.k.a., [hgc]. *)

(** The process of exploiting the [\GC] to "absorb" affine heap predicates
    is captured by the following lemma, which asserts that a heap predicate [H]
    entails [\GC] whenever [H] is affine. *)

Lemma himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.
Proof using.
  introv M. unfold hgc. applys himpl_hexists_r H.
  applys* himpl_hstar_hpure_r.
Qed.

(** In particular, the empty heap predicate [\[]] entails [\GC], because the
    empty heap predicate is affine (recall lemma [haffine_hempty]). *)

Lemma hempty_himpl_hgc :
  \[] ==> \GC.
Proof using. applys himpl_hgc_r. applys haffine_hempty. Qed.

(** The tactic [xsimpl] is extended with specific support for the
    predicate [\GC]. In particular, [xsimpl] simplifies goals of the
    form [H ==> \GC] by turning them into [haffine H] using the above
    lemma. The tactic then tries to discharge [haffine H] by means that
    depend on the choice of the definition of [haffine]. *)


(* ########################################################### *)
(** ** Exploiting the garbage collection in proofs *)

(** In a verification proof, there are two ways to discard heap
    predicates that are no longer needed:

    - either by invoking [triple_haffine_pre] to remove a specific
      predicate from the current state, i.e., the precondition;
    - or by invoking [triple_htop_post] to add a [\GC] into the
      current postcondition and allow subsequent removal of any
      predicate that may be left-over in the final entailment
      justifying that the final state satisfies the postcondition.

    Eager removal of predicates from the current state is never
    necessary: one can be lazy and postpone the application of
    the garbage collection rule until the last step of reasoning.

    To that end, it suffices to anticipate, right from the beginning
    of the verification proof, the possibility of discarding heap
    predicates from the final state, when proving that it entails
    the postcondition. Concretely, it suffices to apply the rule
    [triple_htop_post] as very first step of the proof to extend
    the postcondition with a [\GC] predicate, which will be used
    to "capture" all the garbage left-over at the end of the proof.

    We implement this strategy once-and-forall by integrating directly
    the rule [triple_htop_post] into the tactic [xwp], which sets up
    the verification proof by computing the characteristic formula.
    To that end, we generalize the lemma [xwp_lemma], which the tactic
    [xwp] applies. Its original statement is as follows. *)

Parameter xwp_lemma : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.

(** Its generalized form extends the postcondition to which the formula
    computed by [wpgen] is applied from [Q] to [Q \*+ \GC], as shown below. *)

Lemma xwp_lemma' : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 (Q \*+ \GC) ->
  triple (trm_app v1 v2) H Q.
Proof using. introv E M. applys triple_hgc_post. applys* xwp_lemma. Qed.

(** Let us update the tactic [xwp] to exploit the above lemma. *)

Tactic Notation "xwp" :=
  intros; applys xwp_lemma';
  [ reflexivity | simpl; unfold wpgen_var; simpl ].

(** Using the updated version of [xwp], the proof of [succ_using_incr]
    in a fully-affine logic works out very smoothly, the left-over
    reference being automatically absorbed into the [\GC] predicate 
    by [xsimpl]. *)

Module MotivatingExampleWithTactic.
Export MotivatingExample.

(* Assume a fully-affine logic. *)

Parameter haffine_hany : forall (H:hprop),
  haffine H.

Lemma Triple_succ_using_incr : forall (n:int),
  TRIPLE (succ_using_incr n)
    PRE \[]
    POST (fun r => \[r = n+1]).
Proof using.
  xwp. xapp. intros ? r ->. xapp. xapp. xsimpl. { auto. }
  applys himpl_hgc_r. applys haffine_hany.
  (* We will show further how to automate the work from the last line. *)
Qed.

End MotivatingExampleWithTactic.


(* ########################################################### *)
(** ** Fully-affine and fully-linear instantiations *)

(** In the toy language that we consider, every predicate may be
    discarded, thus [haffine H] can be defined to be always true,
    using the following definition. In that case, [\GC] becomes
    equivalent to [htop], the predicate that holds of any heap. *)

Module FullyAffineLogic.

  Definition haffine (H:hprop) := 
    True.

  Lemma haffine_hany : forall (H:hprop), 
    haffine H.
  Proof using. unfold haffine. auto. Qed.

  Definition hgc : hprop :=
    \exists H, \[haffine H] \* H.

  Definition htop (h:heap) := True.

  Lemma hgc_eq_htop : hgc = htop.
  Proof using.
    unfold hgc, haffine, htop. applys himpl_antisym.
    { intros h M. auto. }
    { intros h M. applys hexists_intro (=h). rewrite hstar_hpure. auto. }
  Qed.

End FullyAffineLogic.

(** On the contrary, one can stick to a "linear" Separation Logic
    and enforce that no heap predicate can be discarded simply
    by definining [haffine] to only be satisfied by heap predicates
    that characterize the empty heap. In that case, [\GC] becomes
    equivalent to [\[]]. *)

Module FullyLinearLogic.

  Definition haffine (H:hprop) := 
    (H ==> \[]).

  Lemma haffine_hempty :
    haffine \[].
  Proof using. unfold haffine. auto. Qed.

  Definition hgc : hprop :=
    \exists H, \[haffine H] \* H.

  Lemma hgc_eq_hempty : hgc = hempty.
  Proof using.
    unfold hgc, haffine. applys himpl_antisym.
    { xpull. intros H M. auto. }
    { xsimpl \[]. auto. }
  Qed.

End FullyLinearLogic.

(** We'll come back later on in more details on these two extreme
    specializations of the [haffine] predicate. 

    In what follows, we purposely leave the definition of [haffine]
    abstract for the sake of generality. *)


(* ########################################################### *)
(** ** Refined definition of Separation Logic triples *)

Module NewTriples.

(** In what follows, we explain how to refine the notion of Separation
    Logic triple so as to accomodate the garbage collection rule.

    Recall the definition of triple for a linear logic.

[[
    Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
      forall (H':hprop), hoare t (H \* H') (Q \*+ H').
]]

    The garbage collection rule [triple_htop_post] asserts that
    postconditions may be freely extended with the [\GC] predicate.
    To support this rule, it suffices to modify the definition of
    [triple] to include the predicate [\GC] in the postcondition
    of the underlying Hoare triple, as follows. *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), hoare t (H \* H') (Q \*+ H' \*+ \GC).

(** Again, keep in mind that this definition of [triple] is strictly
    more general than the previous one. Indeed, as explained earlier on,
    by instantiating [haffine] as the predicate [fun (H:hprop) => \[]],
    the predicate [\GC] becomes equivalent to the empty predicate [\[]].
    In that case, [\GC] can be replaced with [\[]], which simplifies away;
    we thus recover exactly the previous definition of [triple]. *)

(** For the refined definition of [triple] using [\GC], one can prove that:

    - all the existing reasoning rules for linear triples remain sound;
    - the rule [triple_htop_post] is sound;
    - the rule [triple_haffine_hpost] and [triple_haffine_hpre] can
      be derived from [triple_htop_post] and the other structural rules.

    The proofs appear scattered through the remaining of this chapter.

    One fundamental property that appears necessary in many of the proof
    is the following lemma, which asserts that two occurences of [\GC]
    can always be collapsed into one. *)

Lemma hstar_hgc_hgc :
  \GC \* \GC = \GC.
Proof using.
  unfold hgc. applys himpl_antisym.
  { xpull. intros H1 K1 H2 K2. xsimpl (H1 \* H2). applys* haffine_hstar. }
  { xpull. intros H K. xsimpl H \[]. auto. applys haffine_hempty. }
Qed.

(** Let us establish the soundness of the garbage collection rule. *)

(* EX2! (triple_hgc_post') *)
(** Prove [triple_htop_post] with respect to the refined definition of
    [triple]. 
    Hint: exploit [hoare_conseq] then exploit [hstar_hgc_hgc] using 
    tactic [xchange]. *)

Lemma triple_hgc_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.
Proof using. (* ADMITTED *)
  introv M. unfold triple in *. intros H'.
  applys hoare_conseq M. { xsimpl. }
  { intros r. xchange hstar_hgc_hgc. xsimpl. }
Qed. (* /ADMITTED *)

(* [] *)

(** Let us update the soundness proof for the other structural rules. *)

(* [] *)

(* EX2? (triple_frame) *)
(** Prove the frame rule for the definition of [triple] that includes [\GC].
    Hint: unfold the definition of [triple] but not that of [hoare],
    then exploit lemma [hoare_conseq] and conclude using the tactic [xsimpl]. *)

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using. (* ADMITTED *)
  introv M. unfold triple in *. rename H' into H1. intros H2.
  applys hoare_conseq (M (H1 \* H2)). { xsimpl. } { xsimpl. }
Qed. (* /ADMITTED *)

(* [] *)

(* EX2? (triple_conseq) *)
(** Prove the frame rule for the definition of [triple] that includes [\GC].
    Hint: follow the same approach as in the proof of [triple_frame],
    and leverage the tactic [xchange] to conclude. *)

Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using. (* ADMITTED *)
  introv M WH WQ. unfold triple in *. rename H' into H1. intros H2.
  applys hoare_conseq (M H2). { xchange WH. } { xchanges WQ. }
Qed. (* /ADMITTED *)

(* [] *)

(** EX1? (triple_conseq_frame_hgc)
    Prove that combined structural rule, which extends 
    [triple_conseq_frame] with the garbage collection rule,
    replacing [Q1 \*+ H2 ===> Q] with [Q1 \*+ H2 ===> Q \*+ \GC].
    Hint: invoke [triple_conseq], [triple_frame] and [triple_hgc_post]
    in the appropriate order. *)

Lemma triple_conseq_frame_hgc : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \GC ->
  triple t H Q.
Proof using. (* ADMITTED *)
  introv M WH WQ. applys triple_hgc_post.
  applys triple_conseq WH WQ.
  applys triple_frame M.
Qed. (* /ADMITTED *)

(* [] *)

(** EX1? (triple_ramified_frame_hgc)
    Prove the following generalization of the ramified frame rule 
    that includes the garbage collection rule. 
    Hint: it is a corrolary of [triple_conseq_frame_hgc]. Take inspiration
    from the proof of [triple_ramified_frame] in chapter [SLFWand]. *)

Lemma triple_ramified_frame_hgc : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* (Q \*+ \GC)) ->
  triple t H Q.
Proof using. (* ADMITTED *)
  introv M W. applys triple_conseq_frame_hgc (Q1 \--* (Q \*+ \GC)) M.
  { applys W. } { applys qwand_cancel. }
Qed. (* /ADMITTED *)

(* [] *)

(** The extraction rules remain valid as well. *)

Lemma triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. unfolds triple. intros H'.
  rewrite hstar_assoc. applys* hoare_hpure.
Qed.

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (\exists x, J x) Q.
Proof using.
  introv M. unfolds triple. intros H'.
  rewrite hstar_hexists. applys* hoare_hexists.
Qed.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Additional contents *)

(* ########################################################### *)
(** ** Variants of the garbage collection rule *)

Module Export DerivedGCRules.

(** Recall the main garbage collection rule, namely [triple_hgc_post]. *)

Parameter triple_hgc_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.

(** Let us derive from it the rules [triple_haffine_post] and
    [triple_haffine_pre]. *)

(** EX1! (triple_haffine_post)
    Prove that [triple_haffine_post] is derivable from [triple_hgc_post].
    Hint: unfold the definition of [\GC] using [unfold hgc]. *)

Lemma triple_haffine_post : forall t H H' Q,
  haffine H' ->
  triple t H (Q \*+ H') ->
  triple t H Q.
Proof using. (* ADMITTED *)
  introv K M. applys triple_hgc_post. applys triple_conseq M.
  { xsimpl. } { xsimpl. applys himpl_hgc_r K. }
Qed. (* /ADMITTED *)

(* [] *)

(** EX1? (triple_hgc_post')
    Reciprocally, prove that [triple_hgc_post] is derivable from
    [triple_haffine_post]. *)

Lemma triple_hgc_post' : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.
Proof using. (* ADMITTED *)
  introv M. applys triple_haffine_post M. applys haffine_hgc.
Qed. (* /ADMITTED *)

(* [] *)

(** EX1? (triple_haffine_pre)
    Prove that [triple_haffine_pre] is derivable from [triple_hgc_post].
    Hint: exploit the other structural rules of Separation Logic. *)

Lemma triple_haffine_pre : forall t H H' Q,
  haffine H' ->
  triple t H Q ->
  triple t (H \* H') Q.
Proof using. (* ADMITTED *)
  introv K M. applys triple_haffine_post K. applys triple_frame M.
Qed. (* /ADMITTED *)

(* [] *)

End DerivedGCRules.


(* ########################################################### *)
(** ** Garbage collection rules in WP style *)

(** Let us update the definition of [wp] to use the new definition
    of [triple]. *)

Definition wp (t:trm) (Q:val->hprop) : hprop :=
  \exists (H:hprop), H \* \[triple t H Q].

(** Recall the characteristic equivalence of [wp]. *)

Lemma wp_equiv : forall t H Q,
  (H ==> wp t Q) <-> (triple t H Q).
Proof using.
  unfold wp. iff M.
  { applys* triple_conseq Q M.
    applys triple_hexists. intros H'.
    rewrite hstar_comm. applys* triple_hpure. }
  { xsimpl* H. }
Qed.

(** In weakest precondition style, the garbage collection rule [triple_hgc_post]
    translates into the entailment [wp t (Q \*+ \GC) ==> wp t Q]. *)

(** EX1? (wp_hgc_post)
    Prove the garbage collection in wp-style.
    Hint: exploit [wp_equiv] and [triple_hgc_post]. *)

Lemma wp_hgc_post : forall t H Q,
  wp t (Q \*+ \GC) ==> wp t Q.
Proof using. (* ADMITTED *)
  intros. rewrite wp_equiv.
  applys triple_hgc_post. rewrite* <- wp_equiv.
Qed. (* /ADMITTED *)

(* [] *)

(** Likewise, the wp-style presentation of the rule [triple_hgc_pre] takes the
    following form. *)

Lemma wp_hany_pre : forall t H Q,
  haffine H ->
  (wp t Q) \* H ==> wp t Q.
Proof using.
  introv K. rewrite wp_equiv. applys triple_haffine_pre.
  { applys K. } { rewrite* <- wp_equiv. }
Qed.

(** The revised presentation of the wp-style ramified frame rule includes an
    extra [\GC] predicate. This rule captures at once all the structural
    properties of Separation Logic, including the garbage collection rule. *)

Lemma wp_ramified : forall Q1 Q2 t,
  (wp t Q1) \* (Q1 \--* (Q2 \*+ \GC)) ==> (wp t Q2).

(** For a change, let us present below a direct proof for this lemma, 
    that is, not reusing the structural rules associated with triples. *)

Proof using.
  intros. unfold wp. xpull ;=> H M. 
  xsimpl (H \* (Q1 \--* Q2 \*+ \GC)).
  unfolds triple. intros H'.
  applys hoare_conseq (M ((Q1 \--* Q2 \*+ \GC) \* H')).
  { xsimpl. } { xchange hstar_hgc_hgc. xsimpl. }
Qed.


(* ########################################################### *)
(** ** Construction template for [haffine] *)

Module HaffineDef.

(** As explained when introducing the predicate [haffine], the definition of this
    predicate should, ideally, distribute in an intuitive manner over the operators
    of Separation Logic. For example, [haffine H1] and [haffine H2] should imply
    [haffine (H1 \* H2)].

    An easy way to obtain a well-behaved definition of [haffine] is to first define
    the notion of "affine heap", written [heap_affine h], and then derive the notion
    of "affine heap predicate", written [haffine H]. The latter is defined as the set
    of heap predicates that characterize only affine heaps, that is, the predicates
    [H] such that [forall h, H h -> heap_affine h].

    The notion of "affine heap" is characterize by the abstract predicate named
    [heap_affine], which is a predicate over heap representations. *)

Parameter heap_affine : heap -> Prop.

(** For example, for a fully-affine logic, we may define [fun (h:heap) => True],
    and for a fully-linear logic, we may define [fun (h:heap) => h = Fmap.empty]. *)

(** Let us assume that the definition of [heap_affine] is such that it holds of
    the empty heap and is stable by (disjoint) union of heaps. *)

Parameter heap_affine_empty :
  heap_affine Fmap.empty.

Parameter heap_affine_union : forall h1 h2,
  heap_affine h1 ->
  heap_affine h2 ->
  Fmap.disjoint h1 h2 ->
  heap_affine (Fmap.union h1 h2).

(** The notion of "affine heap predicate", as captured by [haffine H], holds of
    heap predicates that characterize only affine heaps, as formalized below. *)

Definition haffine (H:hprop) : Prop :=
  forall h, H h -> heap_affine h.

(** From the above definition and the two properties assumed of [heap_affine], 
    we can derive all the desired distribution rules. *)

Lemma haffine_hempty :
  haffine \[].
Proof using.
  introv K. lets E: hempty_inv K. subst. applys heap_affine_empty.
Qed.

Lemma haffine_hstar : forall H1 H2,
  haffine H1 ->
  haffine H2 ->
  haffine (H1 \* H2).
Proof using.
  introv M1 M2 K. lets (h1&h2&K1&K2&D&U): hstar_inv K.
  subst. applys* heap_affine_union.
Qed.

(** Let us extend the notion of affinity to postconditions. The predicate
    [haffine_post J] asserts that [haffine] holds of [J x] for any [x]. *)

Definition haffine_post (A:Type) (J:A->hprop) : Prop :=
  forall x, haffine (J x).

(** Recall the distribution rules over quantifiers.

[[
    Parameter haffine_hexists : forall A (J:A->hprop),
      (forall x, haffine (J x)) ->
      haffine (\exists x, (J x)).

    Parameter haffine_hforall : forall A `{Inhab A} (J:A->hprop),
      (forall x, haffine (J x)) ->
      haffine (\forall x, (J x)).
]]

  The can be reformulated in a more concise way using [haffine_post].
*)

Lemma haffine_hexists : forall A (J:A->hprop),
  haffine_post J ->
  haffine (hexists J).
Proof using. introv F1 (x&Hx). applys* F1. Qed.

Lemma haffine_hforall : forall A `{Inhab A} (J:A->hprop),
  haffine_post J ->
  haffine (hforall J).
Proof using. introv IA F1 Hx. lets N: hforall_inv Hx. applys* F1 arbitrary. Qed.

(** Two other facts are useful. First, pure heap predicates are affine. *)

Lemma haffine_hpure : forall P,
  haffine \[P].
Proof using.
  intros. intros h K. lets (HP&M): hpure_inv K. 
  subst. applys heap_affine_empty.
Qed.

(** Second, [haffine] distributes over [\[P] \* H] by providing the
    proposition [P] as hypothesis. *)

Lemma haffine_hstar_hpure : forall P H,
  (P -> haffine H) ->
  haffine (\[P] \* H).
Proof using.
  introv M. intros h K. rewrite hstar_hpure in K. applys* M.
Qed.

(** Consider a definition of [\GC] based on the definition of
    [haffine] derived from [heap_affine] as done above. *)

Section GCProp.

Definition hgc : hprop :=
  \exists H, \[haffine H] \* H.

Notation "\GC" := (hgc).

(** For this definition of [haffine], we can state introduction and
    elimination lemmas for [\GC] expressed in terms of [heap_affine]. *)

Lemma hgc_intro : forall h,
  heap_affine h ->
  \GC h.
Proof using.
  unfold hgc. intros h K. applys hexists_intro (=h).
  rewrite hstar_hpure. split. { introv ->. auto. } { auto. }
Qed.

(* EX2? (hgc_inv) *)
(** Prove the reciprocal elimination lemma for [\GC]. *)

Lemma hgc_inv : forall h,
  \GC h ->
  heap_affine h.
Proof using. (* ADMITTED *)
  unfold hgc. intros h M. lets (H&K): hexists_inv M.
  rewrite hstar_hpure in K. destruct K as (K&Hh).
  unfold haffine in K. applys K. auto.
Qed. (* /ADMITTED *)

(* [] *)

End GCProp.


(* ########################################################### *)
(** ** Definition of [haffine] for a fully-affine logic *)

Module FullyAffineHaffine.

(** To set up a fully-affine logic, we make all heaps satisfy [heap_affine]. *)

Definition heap_affine (h:heap) :=
  True.

(** It is trivial to check that [heap_affine] satisfies the required properties. *)

Lemma heap_affine_empty :
  heap_affine Fmap.empty.
Proof using. unfold heap_affine. auto. Qed.

Lemma heap_affine_union : forall h1 h2,
  heap_affine h1 ->
  heap_affine h2 ->
  Fmap.disjoint h1 h2 ->
  heap_affine (Fmap.union h1 h2).
Proof using. unfold heap_affine. auto. Qed.

(** The generic construction of [haffine] provides a predicate that holds
    of any heap predicate. *)

Definition haffine (H:hprop) : Prop :=
  forall h, H h -> heap_affine h.

Lemma haffine_hany : forall (H:hprop),
  haffine H.
Proof using. unfold haffine, heap_affine. auto. Qed.

(** This associated generic construction of [haffine] is equivalent to the direct
    definition of [haffine] as [fun (H:hprop) => True] presented earlier on. *)

Definition haffine' (H:hprop) := 
  True.

Lemma haffine_eq_haffine' : 
  haffine = haffine'.
Proof using. 
  apply pred_ext_1. intros H. unfold haffine, haffine', heap_affine. autos*.
Qed.

End FullyAffineHaffine.


(* ########################################################### *)
(** ** Definition of [haffine] for a fully-linear logic *)

Module FullyLinearHaffine.

(** To set up a fully-linear logic, we make only empty heaps satisfy 
    [heap_affine]. *)

Definition heap_affine (h:heap) :=
  h = Fmap.empty.

(** It is not hard to check that [heap_affine] satisfies the required properties. *)

Lemma heap_affine_empty :
  heap_affine Fmap.empty.
Proof using. unfold heap_affine. auto. Qed.

Lemma heap_affine_union : forall h1 h2,
  heap_affine h1 ->
  heap_affine h2 ->
  Fmap.disjoint h1 h2 ->
  heap_affine (Fmap.union h1 h2).
Proof using. 
  introv K1 K2 D. unfolds heap_affine. subst. rewrite* Fmap.union_empty_r.
Qed.

(** The associated generic construction of [haffine] provides a predicate that 
    holds only of the empty heap predicate. It is thus equivalent to the
    previously-presented definition of [haffine] for a fully-linear logic
    defined as [fun H => (H ==> \[])]. *)

Definition haffine (H:hprop) : Prop :=
  forall h, H h -> heap_affine h.

Definition haffine' (H:hprop) := 
  H ==> \[].

Lemma haffine_eq_haffine' : 
  haffine = haffine'.
Proof using. 
  apply pred_ext_1. intros H. unfold haffine, haffine', heap_affine. iff M.
  { intros h Hh. rewrite* M. applys hempty_intro. }
  { intros h K. lets N: M K. applys hempty_inv N. }
Qed.

End FullyLinearHaffine.

End HaffineDef.


(* ########################################################### *)
(** ** Proof of the reasoning rules for terms *)

Module TermRules.

(** The standard reasoning rules of Separation Logic can be derived for the
    revised notion of Separation Logic triple, the one which includes [\GC],
    following essentially the same proofs as for the original Separation
    Logic triples. The main difference is that one sometimes needs to invoke
    the lemma [hstar_hgc_hgc] for collapsing two [\GC] into a single one.

    In what follows, we present just one representative example of such proofs,
    namely the reasoning rule for sequences. *)

(** The rule for sequences follows a similar proof from that of lemma [triple_seq]
    in chapter [SLFRules]. Only we exploit [hstar_hgc_hgc] to collapse the two 
    [\GC] predicates associated with the two subterms into just one [\GC] predicate. *)

Lemma triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2. intros H'. unfolds triple.
  applys hoare_seq.
  { applys M1. }
  { applys hoare_conseq. { applys M2. } { xsimpl. } { xchanges hstar_hgc_hgc. } }
Qed.

End TermRules.


(* ########################################################### *)
(** ** Revised definition of [mkstruct] *)

(** Recall the definition [mkstruct], as stated in the file [SLFWand].

[[
    Definition mkstruct (F:formula) : formula :=
      fun Q => \exists Q', (F Q') \* (Q' \--* Q).
]]

    This definition can be generalized to handle not just the consequence
    and the frame rule, but also the garbage collection rule.

    To that end, we augment [mkstruct] with an additional [\GC], as follows. *)

Definition mkstruct (F:formula) : formula :=
  fun Q => \exists Q', F Q' \* (Q' \--* (Q \*+ \GC)).

(** Let us prove that this revised definition of [mkstruct] does sastisfy
    the [wp]-style statement of the garbage collection rule, which is stated
    in a way similar to [wp_hgc_post]. *)

Lemma mkstruct_hgc : forall Q F,
  mkstruct F (Q \*+ \GC) ==> mkstruct F Q.
Proof using.
  intros. unfold mkstruct. set (X := hgc) at 3. replace X with (\GC \* \GC).
  { xsimpl. } { subst X. apply hstar_hgc_hgc. }
Qed.

(** Besides, let us prove that the revised definition of [mkstruct] still
    satisfies the three required properties. 

    The proofs shown below exploit a version of [xsimpl] that handles the magic
    wand but provides no built-in support for the [\GC] predicate. *)

Lemma mkstruct_erase : forall F Q,
  F Q ==> mkstruct F Q.
Proof using.
  intros. unfold mkstruct. xsimpl Q. apply himpl_hgc_r. apply haffine_hempty.
Qed.

Lemma mkstruct_conseq : forall F Q1 Q2,
  Q1 ===> Q2 ->
  mkstruct F Q1 ==> mkstruct F Q2.
Proof using.
  introv WQ. unfold mkstruct. xpull. intros Q'. xsimpl Q'. xchange WQ.
Qed.

Lemma mkstruct_frame : forall F H Q,
  (mkstruct F Q) \* H ==> mkstruct F (Q \*+ H).
Proof using.
  intros. unfold mkstruct. xpull. intros Q'. xsimpl Q'.
Qed.

(** EX2? (mkstruct_haffine_post)
    Prove the reformulation of [triple_haffine_post] adapted to [mkstruct],
    for discarding an affine piece of postcondition. *)

Lemma mkstruct_haffine_post : forall H Q F,
  haffine H ->
  mkstruct F (Q \*+ H) ==> mkstruct F Q.
Proof using. (* ADMITTED *)
  introv K. applys himpl_trans. 2: { applys mkstruct_hgc. }
  applys mkstruct_conseq. xsimpl. applys himpl_hgc_r K.
Qed. (* /ADMITTED *)

(* [] *)

(** EX2? (mkstruct_haffine_pre)
    Prove the reformulation of [triple_haffine_pre] adapted to [mkstruct],
    for discarding an affine piece of postcondition. *)

Lemma mkstruct_haffine_pre : forall H Q F,
  haffine H ->
  (mkstruct F Q) \* H ==> mkstruct F Q.
Proof using. (* ADMITTED *)
  introv K. applys himpl_trans. { applys mkstruct_frame. }
  { applys mkstruct_haffine_post K. }
Qed. (* /ADMITTED *)

(* [] *)

End NewTriples.


(* ########################################################### *)
(** ** Tactic [xaffine], and behavior of [xsimpl] on [\GC] *)

Module XaffineXsimplTactics.
Import SLFDirect.

(** To present the tactics, let us import the definitions from [SLFDirect]
    but assume that the definition of [mkstruct] is like the one presented
    in this file, that is, including the [\GC] when defining [mkstruct F]
    as [fun Q => \exists Q', F Q' \* (Q' \--* (Q \*+ \GC)). 

    As argued above, with this definition, [mkstruct] satisfies the
    following garbage collection rule. *)

Parameter mkstruct_hgc : forall Q F,
  mkstruct F (Q \*+ \GC) ==> mkstruct F Q.

(** The tactic [xaffine] applys to a goal of the form [haffine H].
    The tactic simplifies the goal using all the distributivity rules
    associated with [haffine]. Ultimately, it invokes [eauto with haffine],
    which can leverage knowledge specific to the definition of [haffine]
    from the Separation Logic set up at hand. *)

Create HintDb haffine.

Tactic Notation "xaffine" :=
  repeat match goal with |- haffine ?H =>
    match H with
    | (hempty) => apply haffine_hempty
    | (hpure _) => apply haffine_hpure
    | (hstar _ _) => apply haffine_hstar
    | (hexists _) => apply haffine_hexists
    | (hforall _) => apply haffine_hforall
    | (hgc) => apply haffine_hgc
    | _ => eauto with haffine
    end
  end.

Lemma xaffine_demo : forall H1 H2 H3,
  haffine H1 ->
  haffine H3 ->
  haffine (H1 \* H2 \* H3).
Proof using. introv K1 KJ. xaffine. (* remains [haffine H2] *) Abort.

(** The tactic [xsimpl] is extended with support for simplifying goals
    of the form [H ==> \GC] into [haffine H], using lemma [himpl_hgc_r].
    In addition, [xsimpl] invokes the tactic [xaffine] to simplify
    [haffine H]. *)

Lemma xsimpl_demo_hgc_simpl : forall H1 H2,
  haffine H1 ->
  H1 \* H2 ==> H2 \* \GC.
Proof using. introv K1. xsimpl. (* clears the goal *) Abort.

(** Another feature of [xsimpl] is that it is able to collapse several
    occurences of [\GC] into one. *)

Lemma xsimpl_demo_hgc_collapse : forall H1 H2 H3,
  H1 \* H2 \* H3 ==> H3 \* \GC \* H2 \* \GC.
Proof using. intros. xsimpl. (* leaves only one [\GC] *) Abort.


(* ########################################################### *)
(** ** The garbage collection tactics *)

(** The tactic [xgc H] removes [H] from the precondition (i.e. from the
    current state), in the course of a proof exploiting a formula produced
    by [wpgen].

    More precisely, the tactic invokes the following variant of the rule
    [triple_haffine_pre], which allows to leverage [xsimpl] for computing
    the heap predicate [H2] that remains after a predicate [H1] is removed
    from a precondition [H], through the entailment [H ==> H1 \* H2]. *)

Lemma xgc_lemma: forall H1 H2 H F Q,
  haffine H1 ->
  H ==> H1 \* H2 ->
  H2 ==> mkstruct F Q ->
  H ==> mkstruct F Q.
Proof using.
  introv K WH M. xchange WH. xchange M. 
  applys himpl_trans mkstruct_frame. 
  applys himpl_trans mkstruct_hgc.
  applys mkstruct_conseq. xsimpl.
Qed.

Tactic Notation "xgc" constr(H) :=
  eapply (@xgc_lemma H); [ xaffine | xsimpl | ].

Lemma xgc_demo : forall H1 H2 H3 F Q,
  haffine H2 ->
  (H1 \* H2 \* H3) ==> mkstruct F Q.
Proof using. intros. xgc H2. (* clears [H2] *) Abort.

(** In what follows, let us assume to simplify the demos that all
    heap predicates are affine, i.e. that the logic is fully affine. *)

Parameter haffine_hany :
  forall (H:hprop), haffine H.

Hint Resolve haffine_hany : haffine.

(** The tactic [xgc_keep H] is a variant of [xgc] that enables to discard
    everything but [H] from the precondition.

    The implementation of the tactic leverages the same lemma [xgc_lemma],
    only providing [H2] instead of [H1]. *)

Tactic Notation "xgc_keep" constr(H) :=
  eapply (@xgc_lemma _ H); [ xaffine | xsimpl | ].

Lemma xgc_keep_demo : forall H1 H2 H3 F Q,
  (H1 \* H2 \* H3) ==> mkstruct F Q.
Proof using.
  intros. xgc_keep H2.
  (* [haffine H1] and [haffine H3] are discharged by the tactic [xaffine]
     which ultimately invokes the lemma [haffine_hany]. *)
Abort.

(** The tactic [xgc_post] simply extends the postcondition with a [\GC],
    to enable subsequent garbage collection in the final entailment. *)

Lemma xgc_post_lemma : forall H Q F,
  H ==> mkstruct F (Q \*+ \GC) ->
  H ==> mkstruct F Q.
Proof using. introv M. xchange M. applys mkstruct_hgc. Qed.

Tactic Notation "xgc_post" :=
  apply xgc_post_lemma.

Lemma xgc_keep_demo : forall H1 H2 H3 F Q,
  H1 ==> mkstruct F (Q \*+ H2 \*+ H3) ->
  H1 ==> mkstruct F Q.
Proof using.
  introv M. xgc_post. xchange M. applys mkstruct_conseq. xsimpl.
  (* Check out how the end proof fails without the call to [xgc_post]. *)
  (* Above, [haffine H1] and [haffine H3] are discharged using [haffine_hany]. *)
Abort.

End XaffineXsimplTactics.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Bonus contents (optional reading) *)


(* ########################################################### *)
(** ** Low-level definition of refined triples *)

Module LowLevel.
Import NewTriples HaffineDef.

(* TODO *)
Notation "\GC" := (hgc).

(** Consider the updated definition of [triple] introduced in this chapter. *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), hoare t (H \* H') (Q \*+ H' \*+ \GC).

(** In chapter [SLFHprop], we presented an alternative definition for
    Separation Logic triples, called [triple_lowlevel], expressed directly
    in terms of heaps.

[[
    Definition triple_lowlevel (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
      forall h1 h2,
      Fmap.disjoint h1 h2 ->
      H h1 ->
      exists h1' v,
           Fmap.disjoint h1' h2
        /\ eval (h1 \u h2) t (h1' \u h2) v
        /\ Q v h1'.
]]

    In what follows, we explain how to generalize this definition to match
    our revised definition of [triple], and obtain a direct definition 
    expressed in terms of heap, that does not depend on the definition of
    [hstar] nor that of [\GC].

    Let us aim instead for a direct definition, entirely expressed in terms
    of union of heaps. To that end, we need to introduce an additional piece of
    state to describe the piece of the final heap covered by the [\GC] predicate.

    We will need to describe the disjointness of the 3 pieces of heap that
    describe the final state. To that end, we exploit the auxiliary definition 
    [Fmap.disjoint_3 h1 h2 h3], which asserts that the three arguments denote
    pairwise disjoint heaps. It is defined in the module [Fmap] as follows.

[[ 
    Definition disjoint_3 (h1 h2 h3:heap) : Prop :=
         disjoint h1 h2
      /\ disjoint h2 h3
      /\ disjoint h1 h3.
]]

*)

(** We then formulate [triple_lowlevel] using a final state of the from
    [h1' \u h2 \u h3'] instead of just [h1' \u h2]. There, [h3'] denotes
    the piece of the final state covered by the [\GC] heap predicate.
    This piece of state is an affine heap, as captured by [heap_affine h3']. *)

Definition triple_lowlevel (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall h1 h2,
  Fmap.disjoint h1 h2 ->
  H h1 ->
  exists h1' h3' v,
       Fmap.disjoint_3 h1' h2 h3'
    /\ heap_affine h3'
    /\ eval (h1 \u h2) t (h1' \u h2 \u h3') v
    /\ Q v h1'.

(** One can prove the equivalence of [triple] and [triple_lowlevel]
    following a similar proof pattern as previously. The proof is a bit
    more technical and requires additional tactic support to deal with
    the tedious disjointness conditions, so we omit the details here. *)

Lemma triple_eq_triple_lowlevel : 
  triple = triple_lowlevel.
Proof using.
  applys pred_ext_3. intros t H Q.
  unfold triple, triple_lowlevel, hoare. iff M.
  { introv D P1.
    forwards~ (h'&v&R1&R2): M (=h2) (h1 \u h2). { apply~ hstar_intro. }
    destruct R2 as (h2'&h1''&N0&N1&N2&N3).
    destruct N0 as (h1'&h3'&T0&T1&T2&T3). subst.
    exists h1' h1'' v. splits~.
    { rew_disjoint. auto. }
    { applys hgc_inv N1. }
    { applys_eq~ R1 2 4. } }
  { introv (h1&h2&N1&N2&D&U).
    forwards~ (h1'&h3'&v&R1&R2&R3&R4): M h1 h2.
    exists (h1' \u h3' \u h2) v. splits~.
    { applys_eq~ R3 2 4. }
    { subst. rewrite hstar_assoc. apply~ hstar_intro.
      rewrite hstar_comm. applys~ hstar_intro. applys~ hgc_intro. } }
Qed.

End LowLevel.


(* ########################################################### *)
(** ** Pre and post rules *)

Module FromPreToPostGC.
Import SLFRules ProofsSameSemantics.

(** Let us prove that the rule [triple_hgc_post] is derivable from
    [triple_hgc_pre]. *)

Parameter triple_hgc_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \GC) Q.

Lemma triple_hgc_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.

(** The key idea of the proof is that a term [t] admits the same behavior
    as [let x = t in x]. Thus, to simulate garbage collection of a predicate
    from the postcondition of [t], one can invoke the garbage collection 
    rule on the precondition of the variable [x] that appears at the end
    of [let x = t in x]. 

    To formalize this idea, recall from [SLFRules] the lemma
    [trm_equiv_eta_expansion] which asserts the equivalence of
    [t] and [let x = t in x], and recall the lemma [triple_trm_equiv],
    which asserts that two equivalent terms satisfy the same triples. *)

Proof using.
  introv M. lets E: trm_equiv_eta_expansion t "x".
  applys triple_trm_equiv E. applys triple_let.
  { applys M. }
  { intros v. simpl. applys triple_hgc_pre. applys triple_val. auto. }
Qed.

End FromPreToPostGC.
