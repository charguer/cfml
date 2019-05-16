(**

Separation Logic Foundations

Chapter: "Himpl".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Export SLFHprop.
From Sep Require SepBase.

(** Implicit Types *)

Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ####################################################### *)
(** * The chapter in a rush *)

(* ******************************************************* *)
(** ** Definition of entailment *)

(** The "entailement relationship" [H1 ==> H2] asserts that any
    heap satisfying [H1] also satisfies [H2]. *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall (h:heap), H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55).

(** [H1 ==> H2] captures the fact that [H1] is a stronger precondition
    than [H2], in the sense that it is more restrictive. *)

(** As we show next, the entailment relation is reflexive, transitive,
    and antisymmetric. It thus forms an order relation.

    Remark: entailment on [hprop] satisfies these properties as a direct  
    consequence of the fact that implication on [Prop] satisfies all 
    these same properties. *)

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. intros h. hnf. auto. Qed.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using. introv M1 M2. intros h H1h. eauto. Qed.

(* EX1! (himpl_antisym) *)
(** Prove the antisymmetry of entailement result shown below
    using extensionatity for heap predicates, as captured by
    lemma [predicate_extensionality] or lemma [hprop_eq]. *)

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  H1 = H2.
Proof using.
(* SOLUTION *)
  introv M1 M2. applys hprop_eq.
  intros h. iff N.
  { applys M1. auto. }
  { applys M2. auto. }
(* /SOLUTION *)
Qed.

(** For example, [himpl_antisym] can be used to establish
    commutativity of separating conjunction: [(H1 \* H2) = (H2 \* H1)]
    by proving that each side entails the other:
    [(H1 \* H2) ==> (H2 \* H1)] and [(H2 \* H1) ==> (H1 \* H2)]. *)


(* ******************************************************* *)
(** ** Entailment for postconditions *)

(** Entailment applies to heap predicates, so they can be used to capture
    that a precondition is stronger than another one (i.e., that a 
    precondition entails another one). It is similarly interesting to 
    express that a postcondition is stronger than another one.

    For that purpose, we introduce [Q1 ===> Q2], which asserts that
    for any value [v], the heap predicate [Q1 v] entails [Q2 v]. 
 
    Equivalently, [Q1 ===> Q2] holds if for any value [v] and any heap [h],
    the proposition [Q1 v h] implies [Q2 v h]. *)

Definition qimpl (Q1 Q2:val->hprop) : Prop :=
  forall (v:val), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55).

Lemma qimpl_refl : forall Q,
  Q ===> Q.
Proof using. intros Q v. applys himpl_refl. Qed.

Lemma qimpl_trans : forall Q2 Q1 Q3,
  (Q1 ===> Q2) ->
  (Q2 ===> Q3) ->
  (Q1 ===> Q3).
Proof using. introv M1 M2. intros v. applys himpl_trans; eauto. Qed.

Lemma qimpl_antisym : forall Q1 Q2,
  (Q1 ===> Q2) ->
  (Q2 ===> Q1) ->
  (Q1 = Q2).
Proof using.
  introv M1 M2. apply functional_extensionality.
  intros v. applys himpl_antisym; eauto.
Qed.


(* ******************************************************* *)
(** ** Fundamental properties of Separation Logic operators *)

(** The fundamental properties of Separation Logic operators are
    described next. *)

(** (1) The star operator is associative. *)

Parameter hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).

(** (2) The star operator is commutative. *)

Parameter hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.

(** (3) The empty heap predicate is a neutral for the star.
    It is both a left and a right neutral, since star is commutative. *)

Parameter hstar_hempty_l : forall H,
  \[] \* H = H.

(** (4) Existentials can be "extruded" out of stars, that is:

      [(\exists x, H1) \* H2  =  \exists x, (H1 \* H2)].
      when [x] does not occur in [H2]. 

    The corresponding formal statement is as follows: *)

Parameter hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (J \*+ H).

(** (5) Star is "regular" with respect to entailment. *)

Parameter himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).

(** These properties are shared by essentially all variants of Separation
    Logic, and many generic results can be derived from these facts alone. *)

(** Remark: the star operator, together with the empty heap predicate,
    form a "commutative monoid structure". Moreover, the star is "regular"
    with respect to entailment and existentials. *)


(* ******************************************************* *)
(** ** Contradictions from absurd separating conjunctions *)

(** A heap predicate of the form [(l ~~~> v1) \* (l ~~~> v2)] 
    describes two "disjoint" cells that are both "at location [l]".
    This is absurd. The contraction is formally captured by
    the following entailment: *)

Lemma hstar_hsingle_same_loc : forall (l:loc) (v1 v2:val),
  (l ~~~> v1) \* (l ~~~> v2) ==> \[False].

(** The proof of this result exploits a result on finite maps.
    Essentially, the domain of a single singleton map that binds
    a location [l] to some value is the singleton set [\{l}], thus 
    such a singleton map cannot be disjoint from another singleton 
    map that binds the same location [l]. *)

Parameter fmap_disjoint_single_single_same_inv : forall (l:loc) (v1 v2:val),
  fmap_disjoint (fmap_single l v1) (fmap_single l v2) ->
  False.

(** Using this lemma, we can prove [hstar_hsingle_same_loc]
    by unfolding the definition of [hstar] to reveal the
    contradiction on the disjointness assumption. *)

Proof using.
  intros. unfold hsingle. intros h (h1&h2&E1&E2&D&E). false.
  subst. applys fmap_disjoint_single_single_same_inv D.
Qed.

(** More generally, a heap predicate of the form [H1 \* H1] 
    is generally suspicious in Separation Logic. 
    Such a predicate can only be satisfied if [H1] covers no
    memory cell, that is, if [H1] is a pure predicate of the
    form [\[P]] for some proposition [P]. *)


(* ******************************************************* *)
(** ** The [hsimpl] tactic *)

(** The Separation Logic setup that we will rely on in subsequent
    chapters includes a tactic called [hsimpl], to assist in the
    simplifications of entailment relations. 

    The working of [hsimpl] can be summarized as a 3-step process:

    1. extract pure facts and existential quantifiers from the LHS
    2. cancel out equal predicates occuring both in the LHS and RHS
    3. instantiate existential quantifiers (using either evars or
       user-provided hints) and generate subgoals for the pure facts
       occuring in the RHS. Moreover, eliminate any redundant [\Top].

    These three steps are detailed and illustrated next.

    The tactic [hpull] is a degraded version of [hsimpl] that only
    perform the first step. We will show examples where it is useful.
*)

Module Htactics.
Import SepBase.
Notation "'hprop''" := (SLFHprop.hprop).


(* ******************************************************* *)
(** *** [hsimpl] to extract pure facts and quantifiers in LHS *)

(** The first feature of [hsimpl] is its ability to extract the
    pure facts and the existential quantifiers from the left-hand
    side out into the Coq context. 

    For example, the proposition [P] appears in the LHS.
    After calling [hsimpl], it is turned into an hypothesis
    at the head of the goal, hypothesis that may subsequently
    be introduced. *)

Lemma hsimpl_demo_lhs_hpure : forall H1 H2 H3 H4 (n:int),
  H1 \* H2 \* \[n > 0] \* H3 ==> H4.
Proof using.
  intros. hsimpl. intros Hn.
  (* variant syntax: 
     intros. hsimpl ;=> HP
  *)
Abort.

(** In case the LHS includes a contradiction, the goal is discharged. *)

Lemma hsimpl_demo_lhs_hpure : forall H1 H2 H3 H4,
  H1 \* H2 \* \[False] \* H3 ==> H4.
Proof using.
  intros. hsimpl.
Qed.

(** Similarly, any existential quantifier from the LHS is turned
    into a universally-quantified variable outside of the entailment. *)

Lemma hsimpl_demo_lhs_hexists : forall H1 H2 H3 H4 (p:loc),
  H1 \* \exists (n:int), (p ~~~> n \* H2) \* H3 ==> H4.
Proof using.
  intros. hsimpl. intros n.
Abort.

(** The [hsimpl] or [hpull] tactic extracts at once everything it can, 
    as illustrated next. *)

Lemma hsimpl_demo_lhs_several : forall H1 H2 H3 H4 (p q:loc),
  H1 \* \exists (n:int), (p ~~~> n \* \[n > 0] \* H2) \* \[p <> q] \* H3 ==> H4.
Proof using.
  intros. hsimpl. intros n Hn Hp.
Abort.

(** This task is also performed by the simpler tactic [hpull]. *)

Lemma hpull_demo_lhs_several : forall H1 H2 H3 H4 (p q:loc),
  H1 \* \exists (n:int), (p ~~~> n \* \[n > 0] \* H2) \* \[p <> q] \* H3 ==> H4.
Proof using.
  intros. hpull. intros n Hn Hp.
Abort.


(* ******************************************************* *)
(** *** [hsimpl] to cancel out heap predicates from LHS and RHS *)

(** The second feature of [hsimpl] is its ability to cancel out
    similar heap predicates that occur on both sides of an entailment. 

    For example, [H2] occurs on both sides, so it can be cancelled out. *)

Lemma hsimpl_demo_cancel_one : forall H1 H2 H3 H4 H5 H6 H7,
  H1 \* H2 \* H3 \* H4 ==> H5 \* H6 \* H2 \* H7.
Proof using.
  intros. hsimpl.
Abort.

(** [hsimpl] actually cancels out all the heap predicates that it
    can spot to appear on both sides. Here, [H2], [H3], and [H4]. *)

Lemma hsimpl_demo_cancel_many : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 ==> H4 \* H3 \* H5 \* H2.
Proof using.
  intros. hsimpl.
Abort.

(** If all the pieces are cancelled out, then the goal is discharged. *)

Lemma hsimpl_demo_cancel_all : forall H1 H2 H3 H4,
  H1 \* H2 \* H3 \* H4 ==> H4 \* H3 \* H1 \* H2.
Proof using.
  intros. hsimpl.
Qed.


(* ******************************************************* *)
(** *** [hsimpl] to instantiate pure facts and quantifiers in RHS *)

(** The third feature of [hsimpl] is its ability to instantiate
    existential quantifiers, pure facts, and [\Top] in the RHS.

    Let us first illustrate how it deals with pure facts. *)

Lemma hsimpl_demo_rhs_hpure : forall H1 H2 H3 (n:int),
  H1 ==> H2 \* \[n > 0] \* H3.
Proof using.
  intros. hsimpl.
Abort.

(** In the face of a quantifier in the RHS, it introduces an evar. *)

Lemma hsimpl_demo_rhs_hexists : forall H1 H2 H3 H4 (p:loc),
  H1 ==> H2 \* \exists (n:int), (p ~~~> n \* H3) \* H4.
Proof using.
  intros. hsimpl. (* here, [p ~~~> n] becomes [p ~~~> ?x] *)
Abort.

(** The evar may often be subsequently instantiated as a result of
    a cancellation with a matching item from the LHS. For example: *)

Lemma hsimpl_demo_rhs_hexists_unify : forall H1 H2 H3 H4 (p:loc),
  H1 \* (p ~~~> 3) ==> H2 \* \exists (n:int), (p ~~~> n \* H3) \* H4.
Proof using.
  intros. hsimpl. (* [p ~~~> n] becomes [p ~~~> ?x], 
                     which then cancels out with [p ~~~> 3] *)
Abort.

(** The instantiation of [n] can be observed if there is another
    occurence of [n] in the entailment. For example: *)

Lemma hsimpl_demo_rhs_hexists_unify_view : forall H1 H2 H3 (p:loc),
  H1 \* (p ~~~> 3) ==> H2 \* \exists (n:int), (p ~~~> n \* \[n > 0]) \* H3.
Proof using.
  intros. hsimpl. (* [p ~~~> n] unifies with [p ~~~> 3], then [3 > 0] remains. *)
Abort.

(** In some cases, it may desirable to provide an explicit value
    to instantiate the existential quantifiers from the RHS.
    Such values may be passed as arguments to [hsimpl],
    using the syntax [hsimpl v1 .. vn] or [hsimpl (>> v1 .. vn)]. *)

Lemma hsimpl_demo_rhs_hints : forall H1 (p q:loc),
  H1 ==> \exists (n m:int), (p ~~~> n \* q ~~~> m).
Proof using.
  intros. hsimpl 3 4.
Abort.

(** It is possible to provide hint for only a subset of the quantifier,
    using the placeholder value [__] for arguments that should be instantiated
    using evars. *)

Lemma hsimpl_demo_rhs_hints_skip : forall H1 (p q:loc),
  H1 ==> \exists (n m:int), (p ~~~> n \* q ~~~> m).
Proof using.
  intros. hsimpl __ 4.
Abort.

(** Finally, [hsimpl] provides support for eliminating [\Top] on the RHS.
    First, if the RHS includes several occurences of [\Top], then they 
    are replaced with a single one. *)

Lemma hsimpl_demo_rhs_htop_compact : forall H1 H2 H3 H4,
  H1 \* H2 ==> H3 \* \Top \* H4 \* \Top.
Proof using.
  intros. hsimpl.
Abort.

(** Second, if after cancellations the RHS consists of exactly
   [\Top] and nothing else, then the goal is discharged. *)

Lemma hsimpl_demo_rhs_htop : forall H1 H2 H3,
  H1 \* H2 \* H3 ==> H3 \* \Top \* H2 \* \Top.
Proof using.
  intros. hsimpl.
Abort.


(* ******************************************************* *)
(** ** Example of entailment proofs using [hsimpl] *)

Lemma himpl_example_1 : forall (p:loc),
  p ~~~> 3 ==> \exists (n:int), p ~~~> n.
Proof using. hsimpl. Qed.

Lemma himpl_example_2 : forall (p q:loc),
  p ~~~> 3 \* q ~~~> 3 ==> \exists (n:int), p ~~~> n \* q ~~~> n.
Proof using. hsimpl. Qed.

Lemma himpl_example_3 : forall (p q:loc),
  p ~~~> 3 \* q ~~~> 3 ==> p ~~~> 3 \* \Top.
Proof using. hsimpl. Qed.

Lemma himpl_example_4 : forall (p:loc),
  \exists (n:int), p ~~~> n ==> \exists (m:int), p ~~~> (m + 1).
Proof using. 
  intros. (* observe that [hsimpl] here does not work well. *)
  hpull. intros n. hsimpl (n-1).
  replace (n-1+1) with n. { auto. } { math. }
  (* variant for the last line: 
  applys_eq himpl_refl 2. fequal. math. *)
Qed.

Lemma himpl_example_5 : forall (H:hprop),
  \[False] ==> H.
Proof using. hsimpl. Qed.

(** The tactic [hsimpl] also work on [===>]. In this case, it
    introduces a name for the result, and resolves the [==>] goal. *)

Lemma qimpl_example_1 : forall (Q1 Q2:val->hprop) (H2 H3:hprop),
  Q1 \*+ H2 ===> Q2 \*+ H2 \*+ H3.
Proof using. intros. hsimpl. intros r. Abort.



(* ******************************************************* *)
(** ** Identifying true and false entailments *)

(** For each entailment relation, indicate (without proof)
    whether it is true or false. Solutions appear further on. *)

(* WORKINCLASS *)

Section CaseStudies.
Implicit Types p q : loc.
Implicit Types n m : int.

Parameter case_study_1 : forall p q,
      p ~~~> 3 \* q ~~~> 4
  ==> q ~~~> 4 \* p ~~~> 3.

Parameter case_study_2 : forall p q,
      p ~~~> 3
  ==> q ~~~> 4 \* p ~~~> 3.

Parameter case_study_3 : forall p q,
      q ~~~> 4 \* p ~~~> 3
  ==> p ~~~> 4.

Parameter case_study_4 : forall p q,
      q ~~~> 4 \* p ~~~> 3
  ==> p ~~~> 3.

Parameter case_study_5 : forall p q,
      \[False] \* p ~~~> 3
  ==> p ~~~> 4 \* q ~~~> 4.

Parameter case_study_6 : forall p q,
      p ~~~> 3 \* q ~~~> 4
  ==> \[False].

Parameter case_study_7 : forall p,
      p ~~~> 3 \* p ~~~> 4
  ==> \[False].

Parameter case_study_8 : forall p,
      p ~~~> 3 \* p ~~~> 3
  ==> \[False].

Parameter case_study_9 : forall p,
      p ~~~> 3
  ==> \exists n, p ~~~> n.

Parameter case_study_10 : forall p,
      exists n, p ~~~> n
  ==> p ~~~> 3.

Parameter case_study_11 : forall p,
      \exists n, p ~~~> n \* \[n > 0] 
  ==> \exists n, \[n > 1] \* p ~~~> (n-1).

Parameter case_study_12 : forall p q,
      p ~~~> 3 \* q ~~~> 3
  ==> \exists n, p ~~~> n \* q ~~~> n.

Parameter case_study_13 : forall p n,
  p ~~~> n \* \[n > 0] \* \[n < 0] ==> p ~~~> n \* p ~~~> n.


(* /WORKINCLASS *)

(* SOLUTION *)
(**

1. true (commutativity)
2. false (one cell does not entail two cell)
3. false (one cell does not entail two cell)
4. false (one cell does not entail two cell)
   Note: [q ~~~> 4 \* p ~~~> 3 ==> p ~~~> 3 \* \Top] would be true.

5. true (\[False] entails anything)
6. false (a satisfiable heap predicate does not entail \[False])
7. true (a cell cannot be starred with itself)
8. true (a cell cannot be starred with itself)

9. true (instantiate [n] with [3])
10. false ([n] could be something else than [3])
   Note [\exists (u:unit), p ~~~> u ==> p ~~~> tt] would be true.

11. true (instantiate [n] in RHS with [n+1] for the [n] of the LHS)
12. true (instantiate [n] with [3])
13. true (equivalent to \[False] ==> \[False])

*)
(* /SOLUTION *)

Lemma case_study_1' : forall p q,
      p ~~~> 3 \* q ~~~> 4
  ==> q ~~~> 4 \* p ~~~> 3.
Proof using. hsimpl. Qed.

Lemma case_study_5' : forall p q,
      \[False] \* p ~~~> 3
  ==> p ~~~> 4 \* q ~~~> 4.
Proof using. hsimpl. Qed.

Lemma case_study_7' : forall p,
      p ~~~> 3 \* p ~~~> 4
  ==> \[False].
Proof using. intros. hchange (hstar_hsingle_same_loc p). Qed.

Lemma case_study_8' : forall p,
      p ~~~> 3 \* p ~~~> 3
  ==> \[False].
Proof using. intros. hchange (hstar_hsingle_same_loc p). Qed.

Lemma case_study_9' : forall p,
      p ~~~> 3
  ==> \exists n, p ~~~> n.
Proof using. hsimpl. Qed.

Lemma case_study_11' : forall p,
      \exists n, p ~~~> n \* \[n > 0] 
  ==> \exists n, \[n > 1] \* p ~~~> (n-1).
Proof using.
  intros. hpull ;=> n Hn. hsimpl (n+1).
  math. math_rewrite (n+1-1 = n). hsimpl.
Qed.

Lemma case_study_12' : forall p q,
      p ~~~> 3 \* q ~~~> 3
  ==> \exists n, p ~~~> n \* q ~~~> n.
Proof using. hsimpl. Qed.

Lemma case_study_13' : forall p n,
  p ~~~> n \* \[n > 0] \* \[n < 0] ==> p ~~~> n \* p ~~~> n.
Proof using. intros. hsimpl ;=> Hn1 Hn2. false. math. Qed.

End CaseStudies.


(* ******************************************************* *)
(** ** The [hchange] tactic *)

(** Assume an entailment goal of the form [H1 \* H2 \* H3 ==> H4].
    Assume an entailment assumption [M], say [H2 ==> H2'].
    Then [hchange M] turns the goal into [H1 \* H2' \* H3 ==> H4],
    effectively replacing [H2] with [H2'].

    In a sense, [hchange] is to entailment what [rewrite] is to equality. *)

Lemma hchange_demo_base : forall H1 H2 H2' H3 H4,
  H2 ==> H2' ->
  H1 \* H2 \* H3 ==> H4.
Proof using.
  introv M. hchange M. (* Note that freshly produced items appear to the front *)
Abort.

(** The tactic [hchange] can also take as argument equalities.
    Use [hchange M] to exploit the left-to-right direction
    and [hchange <- M] to exploit the right-to-left direction . *)

Lemma hchange_demo_eq : forall H1 H2 H3 H4 H5,
  H1 \* H3 = H5 ->
  H1 \* H2 \* H3 ==> H4.
Proof using.
  introv M. hchange M.
  hchange <- M.
Abort.

(** The tactic [hchange] is also able to instantiate lemmas if needed. *)

Lemma hchange_demo_inst : forall H1 (J J':int->hprop) H3 H4,
  (forall n, J n = J' (n+1)) ->
  H1 \* J 3 \* H3 ==> H4.
Proof using.
  introv M. hchange M.
  (* Note that freshly produced items appear to the front *)
Abort.

(** The tactic [hchanges M] is a shorthand for [hchange M; hsimpl]. *)

Lemma hchanges_demo_base : forall p H1 H2 H3,
  H1 \* H3 ==> p ~~~> 3 ->
  H1 \* H2 \* H3 ==> H2 \* \exists (n:int), p ~~~> n.
Proof using.
  introv M. dup.
  (* details: *)
  { hchange M. hsimpl. }
  (* shorthand: *)
  { hchanges M. }
Abort.

End Htactics.


(* ####################################################### *)
(** * Additional contents *)

(* ******************************************************* *)
(** ** Proofs for the Separation Algebra *)

(** We next show the details of the proofs establishing the
    commutative monoid structure with the frame property.

    Note that these results must be proved without help of
    the tactic [hsimpl], because the implementation of the
    tactic itself depends on these key lemmas. 

    To establish the properties, we need to exploit a few
    basic facts about finite maps; we will introduce them as
    we go along. *)

(* EX1! (himpl_frame_l) *)
(** The simplest result to derive is the frame lemma for entailment. *)

Lemma himpl_frame_l' : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof using. 
(* SOLUTION *)
  introv W (h1&h2&M1&M2&D&U). exists* h1 h2. 
(* /SOLUTION *)
Qed.

(* EX1! (himpl_frame_r) *)
(** State and prove a symmetric lemma to [himpl_frame_l] called [himpl_frame_r]
    to exploit an entailment on the right-hand-side of a star. *)

(* SOLUTION *)
Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof using. 
  introv W. rewrite (hstar_comm H1 H2). rewrite (hstar_comm H1 H2').
  applys himpl_frame_l. auto.
Qed.
(* /SOLUTION *)

(** The second simplest result is the extrusion property for existentials. *)

Lemma hstar_hexists' : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof using.
  intros. applys himpl_antisym.
  { intros h (h1&h2&M1&M2&D&U). destruct M1 as (x&M1). exists~ x h1 h2. }
  { intros h (x&M). destruct M as (h1&h2&M1&M2&D&U). exists h1 h2. splits~. exists~ x. }
Qed.

(** To prove commutativity of star, we need to exploit the fact that 
    the union of two finite maps with disjoint domains commutes. *)

Check fmap_union_comm_of_disjoint : forall h1 h2,
  fmap_disjoint h1 h2 ->
  h1 \u h2 = h2 \u h1.

Lemma hstar_comm' : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof using.
  asserts F: (forall H1 H2, H1 \* H2 ==> H2 \* H1).
  { intros. intros h (h1&h2&M1&M2&D&U). exists h2 h1.
    subst. splits~.
    { rewrite fmap_union_comm_of_disjoint; auto. } }
  intros. applys himpl_antisym. { applys F. } { applys F. }
Qed.

(** To prove that the empty heap predicate is a neutral for star,
    we need to exploit the fact that the union with an empty map
    is the identity. *)

Check fmap_union_empty_l : forall h, 
  fmap_empty \u h = h.

Lemma hstar_hempty_l' : forall H,
  \[] \* H = H.
Proof using.
  intros. applys himpl_antisym. 
  { intros h (h1&h2&M1&M2&D&U). hnf in M1. subst.
    rewrite @fmap_union_empty_l. auto. }
  { intros h M. exists (fmap_empty:heap) h. splits~.
    { hnf. auto. }
    { rewrite @fmap_union_empty_l. auto. } }
Qed.

(** The lemma showing that [\[]] is a left neutral can be derived
    from the previous result and commutativity. *)

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof using.
  intros. rewrite hstar_comm'. rewrite hstar_hempty_l'. auto.
Qed.

(** Associativity of star is the most tedious result to derive.
    We need to exploit the associativity of union on finite maps,
    as well as lemmas about the disjointness of a map with the
    result of the union of two maps. *)

Check fmap_union_assoc : forall h1 h2 h3,
  (h1 \u h2) \u h3 = h1 \u (h2 \u h3).

Check fmap_disjoint_union_eq_l : forall h1 h2 h3,
    fmap_disjoint (h2 \u h3) h1 
  = (fmap_disjoint h1 h2 /\ fmap_disjoint h1 h3).

Check fmap_disjoint_union_eq_r : forall h1 h2 h3,
   fmap_disjoint h1 (h2 \u h3) 
 = (fmap_disjoint h1 h2 /\ fmap_disjoint h1 h3).

(* EX2! (hstar_assoc) *)
(** Complete the right-to-left part of the proof below. *)

Lemma hstar_assoc' : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using.
  intros. applys himpl_antisym.
  { intros h (h'&h3&M1&M2&D&U). destruct M1 as (h1&h2&M3&M4&D'&U').
    subst h'. rewrite fmap_disjoint_union_eq_l in D.
    exists h1 (h2 \u h3). splits.
    { applys M3. }
    { exists* h2 h3. }
    { rewrite* @fmap_disjoint_union_eq_r. } 
    { rewrite* @fmap_union_assoc in U. } }
(* SOLUTION *)
  { intros h (h1&h'&M1&M2&D&U). destruct M2 as (h2&h3&M3&M4&D'&U').
    subst h'. rewrite fmap_disjoint_union_eq_r in D.
    exists (h1 \u h2) h3. splits.
    { exists* h1 h2. }
    { applys M4. }
    { rewrite* @fmap_disjoint_union_eq_l. } 
    { rewrite* @fmap_union_assoc. } }
(* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Proof of the consequence rule. *)

(** The rule of consequence in Separation Logic is similar
    to that in Hoared logic. *)

Lemma triple_conseq : forall t H Q H' Q',
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.

(** The shortest proof of [triple_conseq] goes through the low-level 
    interpretation of Separation Logic triples in terms of heaps.
    A more elegant proof is presented further. *)

Proof using.
  (* No need to follow through this low-level proof. *)
  introv M WH WQ. rewrite triple_iff_triple_lowlevel in *.
  intros h1 h2 D HH. forwards (v&h1'&h3'&D'&R&HQ): M D. applys WH HH.
  exists v h1' h3'. splits~. applys WQ HQ.
Qed.

(** However, it is simpler and more elegant to first establish
    the consequence rule for [Hoare_triple], then derive its
    generalization to the case of Separation Logic [triple]. *)

(* EX2! (Hoare_conseq) *)
(** Prove the consequence rule for Hoare triples. *)

Lemma Hoare_conseq : forall t H Q H' Q',
  Hoare_triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  Hoare_triple t H Q.
Proof using.
(* SOLUTION *)
  introv M WH WQ. unfold Hoare_triple.
  intros s Hs. forwards (s'&v&R&HQ): M s.
  { applys WH. auto. }
  { exists s' v. split. { apply R. } { applys WQ. auto. } }
  (* variant proof script:
      intros s Ps. lets Ps': WH Ps.
      lets M': M Ps'. destruct M' as (v&s'&R&HQ).
      exists v s'. splits~. applys WQ. auto. *)
(* /SOLUTION *)
Qed.

(* EX2! (rule_conseq) *)
(** Prove the consequence rule by leveraging the lemma [Hoare_conseq],
    rather than going through the definition of [triple_lowlevel]. 
    Hint: apply lemma [Hoare_conseq] with the appropriate arguments,
    and use lemma [applys himpl_frame_l] to prove the entailments. *)

Lemma rule_conseq'' : forall t H Q H' Q',
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
(* SOLUTION *)
  introv M WH WQ. unfold triple. intros H''.
  applys Hoare_conseq M. 
  { applys himpl_frame_l. applys WH. }
  { intros x. applys himpl_frame_l. applys himpl_frame_l. applys WQ. }
(* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Combined structural rules *)

(** The frame rule almost never applies to a goal in practice,
    because it requires the goal to be exactly in the form
    [triple t (H1 \* H2) (Q1 \*+ H2)].

    This limitation can be addressed by combining the frame rule
    with the rule of consequence, as follows. *)

Lemma triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.

(* EX1! (triple_conseq_frame) *)
(** Prove the combined consequence-frame rule. *)

Proof using.
(* SOLUTION *)
  introv M WH WQ. applys triple_conseq WH WQ.
  applys triple_frame M.
(* /SOLUTION *)
Qed.

(** The "combined structural rule" generalizes the rule above
    by also integrating the garbage collection rule. *)

Lemma triple_conseq_frame_htop : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \Top ->
  triple t H Q.

(* EX1! (himpl_frame_l) *)
(** Prove the combined structural rule. *)

Proof using.
(* SOLUTION *)
  introv M WH WQ. applys triple_htop_post.
  applys triple_conseq_frame M WH WQ.
(* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Structural rules for extracting existentials and pure facts *)

(** From an entailment [(\exists x, (J x) ==> H], it is useful
    to extract [x] into the context, and turn the goal into:
    [forall x, (J x ==> H)].

    Likewise, for a goal [triple t (\exists x, (J x)) Q], it is
    useful to extract [x] into the context, and turn the goal into:
    [forall x, triple t (J x) Q].

    The structural rule called [triple_hexists] captures this
    extraction of the existential quantifier. *)

Parameter triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.

(** Similarly, for a goal [triple t (\[P] \* H) Q], it is
    useful to extract [P] into the context, and turn the goal into:
    [P -> triple t H Q].

    The structural rule called [triple_hpure] captures this
    extraction of the existential quantifier. *)

Parameter triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.

(** To prove these two lemmas, we first establish corresponding
    results on [Hoare_triple], then derive them for [triple]. *)

Lemma Hoare_triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, Hoare_triple t (J x) Q) ->
  Hoare_triple t (hexists J) Q.
Proof using. introv M. intros h (x&Hh). applys M Hh. Qed.

Lemma triple_hexists' : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using.
  introv M. unfold triple. intros H'.
  rewrite hstar_hexists. applys Hoare_triple_hexists.
  intros v. applys M.
Qed.

Lemma Hoare_triple_hpure : forall t (P:Prop) H Q,
  (P -> Hoare_triple t H Q) ->
  Hoare_triple t (\[P] \* H) Q.
Proof using.
  introv M. intros h (h1&h2&M1&M2&D&U). destruct M1 as (M1&HP).
  subst. rewrite fmap_union_empty_l. applys M HP M2.
Qed.

Lemma triple_hpure' : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. unfold triple. intros H'.
  rewrite hstar_assoc. applys Hoare_triple_hpure.
  intros HP. applys M HP.
Qed.

(** Remark: recall that [\[P]] can be encoded as [\exists (p:P), \[]].
    One may exploit this equivalence to show that [Hoare_triple_hpure]
    is derivable from [Hoare_triple_hexists], as illustrated next. *)

Lemma triple_hpure_derived_from_triple_exists : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. rewrite hpure_eq_hexists_proof. (* TODO: fix display *)
  rewrite hstar_hexists. applys triple_hexists.
  rewrite hstar_hempty_l. apply M.
Qed.


(* ******************************************************* *)
(** ** Entailment lemmas for [\Top] *)

(* EX1! (himpl_htop_r) *)
(** Prove that any heap predicate entails [\Top] *)

Lemma himpl_htop_r : forall H,
  H ==> \Top.
Proof using. 
(* SOLUTION *)
  intros. intros h Hh.
  applys htop_intro. (* hnf; auto. *)
(* /SOLUTION *)
Qed.

(* EX2! (hstar_htop_htop) *)
(** Prove that [\Top \* \Top] is equivalent to [\Top] *)

Lemma hstar_htop_htop :
  \Top \* \Top = \Top.
Proof using.
(* SOLUTION *)
  applys himpl_antisym.
  { applys himpl_htop_r. }
  { rewrite <- hstar_hempty_l at 1. applys himpl_frame_l.
    applys himpl_htop_r. }
(* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Variants for the garbage collection rule *)

(** Recall the lemma [triple_htop_post]. *)

Parameter triple_htop_post : forall t H Q,
  triple t H (Q \*+ \Top) ->
  triple t H Q.

(* EX2! (triple_hany_post) *)
(** The following lemma provides an alternative presentation of the
    same result as [triple_htop_post]. Prove that it is derivable
    from [triple_htop_post] and [triple_conseq]. *)

Lemma triple_hany_post : forall t H H' Q,
  triple t H (Q \*+ H') ->
  triple t H Q.
Proof using.
(* SOLUTION *)
  introv M. applys* triple_htop_post. applys triple_conseq M.
  { applys himpl_refl. }
  { intros v. applys himpl_frame_r. applys himpl_htop_r. }
(* /SOLUTION *)
Qed. 

(** Reciprocally, [triple_htop_post] is trivially derivable from
    [triple_hany_post], simply by instantiating [H'] as [\Top]. *)

Lemma triple_htop_post_derived_from_triple_hany_post : forall t H Q,
  triple t H (Q \*+ \Top) ->
  triple t H Q.
Proof using. intros. applys triple_hany_post \Top. auto. Qed.

(** The reason we prefer [triple_htop_post] to [triple_hany_post]
    is that it does not require providing [H'] at the time of applying
    the rule. The instantiation is postponed through the introduction
    of [\Top], which is equivalent to [\exists H', H']. Delaying the 
    instantiation of [H'] using [\Top] rather than throught the
    introduction of an evar enables more robust proof scripts and
    tactic support. *)

(* EX2! (triple_htop_pre) *)
(** The rule [triple_htop_post] enables discarding pieces of
    heap from the postcondition. The symmetric rule [triple_htop_pre] 
    enables discarding pieces of heap from the precondition.

    Prove that it is derivable from [triple_htop_post] and
    [triple_frame] (and, optionally, [triple_conseq]). *)

Lemma triple_htop_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \Top) Q.
Proof using.
(* SOLUTION *)
  introv M. applys triple_htop_post. applys triple_frame. auto.
(* /SOLUTION *)
Qed.

(* EX2! (triple_htop_pre) *)
(** The rule [triple_hany_pre] is a variant of [triple_htop_pre].
    Prove that it is derivable. 
    You may exploit [triple_htop_pre], or [triple_hany_post],
    or [triple_htop_post], whichever you find simpler. *)

Lemma triple_hany_pre : forall t H H' Q,
  triple t H Q ->
  triple t (H \* H') Q.
Proof using. 
  dup 3.
  (* first proof, based on [triple_hany_post]: *)
  introv M. applys triple_hany_post. applys triple_frame. auto.
  (* second proof, based on [triple_htop_pre]: *)
  introv M. lets N: triple_htop_pre M. applys triple_conseq N.
  { applys himpl_frame_r. applys himpl_htop_r. }
  { applys qimpl_refl. }
  (* third proof, based on [triple_htop_post]: *)
  introv M. applys triple_htop_post.
  lets N: triple_frame H' M.
  applys triple_conseq N.
  { applys himpl_refl. }
  { intros v. applys himpl_frame_r. applys himpl_htop_r. }
Qed.

(** Here again, the reciprocal holds: [triple_hany_pre] is trivially
    derivable from [triple_htop_pre]. The variant of the rule that is
    most useful in practice is actually yet another presentation,
    which applies to any goal and enables specifying explicitly the
    piece of the precondition that one wishes to discard. *)

Lemma triple_hany_pre_trans : forall H1 H2 t H Q,
  triple t H1 Q ->
  H ==> H1 \* H2 ->
  triple t H Q.
Proof using.
  introv M WH. applys triple_conseq (H1 \* H2) Q.
  { applys triple_hany_pre. auto. }
  { applys WH. }
  { applys qimpl_refl. }
Qed.

(** Remark: the lemmas that enable discarding pieces of precondition
    (e.g., [triple_htop_pre]) are derivable from those that enable
    discarding pices of postconditions (e.g., [triple_htop_post]), 
    but not the other way around.

    Technical remark: the previous remark can be mitigated. If we expose 
    that [triple t H Q <-> triple t' H Q] holds whenever [t] and [t']
    are observationally equivalent (with respect to the semantics 
    defined by [eval]), and if we are able to prove that [let x = t in x]
    is observationally equivalent to [t] for some fresh variable x,
    then it is possible to prove that [triple_htop_post] is derivable
    from [triple_htop_pre]. (At a high-level, the postcondition of [t]
    can be viewed as the precondition of the [x] occuring in the 
    right-hand side of the term [let x = t in x].)  *)
