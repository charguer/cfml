
(*

(* ******************************************************* *)
(** *** [xpull] to extract from LHS *)

Lemma xpull_demo_lhs_several : forall H1 H2 H3 H4 (p q:loc),
  H1 \* \exists (n:int), (p ~~~> n \* \[n > 0] \* H2) \* \[p <> q] \* H3 ==> H4.
Proof using.
  intros. xpull. intros n Hn Hp.
Abort.


(* ******************************************************* *)
(** *** [xsimpl] to extract pure facts and quantifiers in LHS *)

(** The first feature of [xsimpl] is its ability to extract the
    pure facts and the existential quantifiers from the left-hand
    side out into the Coq context.

    For example, the proposition [P] appears in the LHS.
    After calling [xsimpl], it is turned into an hypothesis
    at the head of the goal, hypothesis that may subsequently
    be introduced. *)

Lemma xsimpl_demo_lhs_hpure : forall H1 H2 H3 H4 (n:int),
  H1 \* H2 \* \[n > 0] \* H3 ==> H4.
Proof using.
  intros. xsimpl. intros Hn.
  (* variant syntax:
     intros. xsimpl ;=> HP
  *)
Abort.

(** In case the LHS includes a contradiction, the goal is discharged. *)

Lemma xsimpl_demo_lhs_hpure : forall H1 H2 H3 H4,
  H1 \* H2 \* \[False] \* H3 ==> H4.
Proof using.
  intros. xsimpl.
Qed.

(** Similarly, any existential quantifier from the LHS is turned
    into a universally-quantified variable outside of the entailment. *)

Lemma xsimpl_demo_lhs_hexists : forall H1 H2 H3 H4 (p:loc),
  H1 \* \exists (n:int), (p ~~~> n \* H2) \* H3 ==> H4.
Proof using.
  intros. xsimpl. intros n.
Abort.

(** The [xsimpl] or [xpull] tactic extracts at once everything it can,
    as illustrated next. *)

Lemma xsimpl_demo_lhs_several : forall H1 H2 H3 H4 (p q:loc),
  H1 \* \exists (n:int), (p ~~~> n \* \[n > 0] \* H2) \* \[p <> q] \* H3 ==> H4.
Proof using.
  intros. xsimpl. intros n Hn Hp.
Abort.




(* ******************************************************* *)
(** *** [xsimpl] to cancel out heap predicates from LHS and RHS *)

(** The second feature of [xsimpl] is its ability to cancel out
    similar heap predicates that occur on both sides of an entailment.

    For example, [H2] occurs on both sides, so it can be cancelled out. *)

Lemma xsimpl_demo_cancel_one : forall H1 H2 H3 H4 H5 H6 H7,
  H1 \* H2 \* H3 \* H4 ==> H5 \* H6 \* H2 \* H7.
Proof using.
  intros. xsimpl.
Abort.

(** [xsimpl] actually cancels out all the heap predicates that it
    can spot to appear on both sides. Here, [H2], [H3], and [H4]. *)

Lemma xsimpl_demo_cancel_many : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 ==> H4 \* H3 \* H5 \* H2.
Proof using.
  intros. xsimpl.
Abort.

(** If all the pieces get cancelled out, then the goal is discharged. *)

Lemma xsimpl_demo_cancel_all : forall H1 H2 H3 H4,
  H1 \* H2 \* H3 \* H4 ==> H4 \* H3 \* H1 \* H2.
Proof using.
  intros. xsimpl.
Qed.


(* ******************************************************* *)
(** *** [xsimpl] to instantiate pure facts and quantifiers in RHS *)

(** The third feature of [xsimpl] is its ability to instantiate
    existential quantifiers, pure facts, and [\Top] in the RHS.

    Let us first illustrate how it deals with pure facts,
    by spawning subgoals. *)

Lemma xsimpl_demo_rhs_hpure : forall H1 H2 H3 (n:int),
  H1 ==> H2 \* \[n > 0] \* H3.
Proof using.
  intros. xsimpl.
Abort.

(** In the face of a quantifier in the RHS, the [xsimpl] tactic
    introduces an evar. *)

Lemma xsimpl_demo_rhs_hexists : forall H1 H2 H3 H4 (p:loc),
  H1 ==> H2 \* \exists (n:int), (p ~~~> n \* H3) \* H4.
Proof using.
  intros. xsimpl. (* here, [p ~~~> n] becomes [p ~~~> ?x] *)
Abort.

(** The evar often gets subsequently instantiated as a result of
    a cancellation with a matching item from the LHS. For example: *)

Lemma xsimpl_demo_rhs_hexists_unify : forall H1 H2 H3 H4 (p:loc),
  H1 \* (p ~~~> 3) ==> H2 \* \exists (n:int), (p ~~~> n \* H3) \* H4.
Proof using.
  intros. xsimpl. (* [p ~~~> n] becomes [p ~~~> ?x],
                     which then cancels out with [p ~~~> 3] *)
Abort.

(** The instantiation of the evar (e.g., [n]) can be observed if there
    is another occurence of the same variable in the entailment. For example: *)

Lemma xsimpl_demo_rhs_hexists_unify_view : forall H1 H2 H3 (p:loc),
  H1 \* (p ~~~> 3) ==> H2 \* \exists (n:int), (p ~~~> n \* \[n > 0]) \* H3.
Proof using.
  intros. xsimpl. (* [p ~~~> n] unifies with [p ~~~> 3], then [3 > 0] remains. *)
Abort.

(** In some cases, it may desirable to provide an explicit value
    to instantiate the existential quantifiers from the RHS.
    Such values may be passed as arguments to [xsimpl],
    using the syntax [xsimpl v1 .. vn] or [xsimpl (>> v1 .. vn)]. *)

Lemma xsimpl_demo_rhs_hints : forall H1 (p q:loc),
  H1 ==> \exists (n m:int), (p ~~~> n \* q ~~~> m).
Proof using.
  intros. xsimpl 3 4.
Abort.

(** It is possible to provide hint for only a subset of the quantifier,
    using the placeholder value [__] for arguments that should be instantiated
    using evars. *)

Lemma xsimpl_demo_rhs_hints_skip : forall H1 (p q:loc),
  H1 ==> \exists (n m:int), (p ~~~> n \* q ~~~> m).
Proof using.
  intros. xsimpl __ 4.
Abort.

(** Finally, [xsimpl] provides support for eliminating [\Top] on the RHS.
    First, if the RHS includes several occurences of [\Top], then they
    are replaced with a single one. *)

Lemma xsimpl_demo_rhs_htop_compact : forall H1 H2 H3 H4,
  H1 \* H2 ==> H3 \* \Top \* H4 \* \Top.
Proof using.
  intros. xsimpl.
Abort.

(** Second, if after cancellations the RHS consists of exactly
   [\Top] and nothing else, then the goal is discharged. *)

Lemma xsimpl_demo_rhs_htop : forall H1 H2 H3,
  H1 \* H2 \* H3 ==> H3 \* \Top \* H2 \* \Top.
Proof using.
  intros. xsimpl.
Abort.


(* ******************************************************* *)
(** ** Example of entailment proofs using [xsimpl] *)

Lemma himpl_example_1 : forall (p:loc),
  p ~~~> 3 ==> \exists (n:int), p ~~~> n.
Proof using. xsimpl. Qed.

Lemma himpl_example_2 : forall (p q:loc),
  p ~~~> 3 \* q ~~~> 3 ==> \exists (n:int), p ~~~> n \* q ~~~> n.
Proof using. xsimpl. Qed.

Lemma himpl_example_3 : forall (p q:loc),
  p ~~~> 3 \* q ~~~> 3 ==> p ~~~> 3 \* \Top.
Proof using. xsimpl. Qed.

Lemma himpl_example_4 : forall (p:loc),
  \exists (n:int), p ~~~> n ==> \exists (m:int), p ~~~> (m + 1).
Proof using.
  intros. (* observe that [xsimpl] here does not work well. *)
  xpull. intros n. xsimpl (n-1).
  replace (n-1+1) with n. { auto. } { math. }
  (* variant for the last line:
  applys_eq himpl_refl 2. fequal. math. *)
Qed.

Lemma himpl_example_5 : forall (H:hprop),
  \[False] ==> H.
Proof using. xsimpl. Qed.

(** The tactic [xsimpl] also work on [===>]. In this case, it
    introduces a name for the result, and resolves the [==>] goal. *)

Lemma qimpl_example_1 : forall (Q1 Q2:val->hprop) (H2 H3:hprop),
  Q1 \*+ H2 ===> Q2 \*+ H2 \*+ H3.
Proof using. intros. xsimpl. intros r. Abort.


(* ******************************************************* *)
(** ** The [xchange] tactic *)

(** Assume an entailment goal of the form [H1 \* H2 \* H3 ==> H4].
    Assume an entailment assumption [M], say [H2 ==> H2'].
    Then [xchange M] turns the goal into [H1 \* H2' \* H3 ==> H4],
    effectively replacing [H2] with [H2'].

    In a sense, [xchange] is to entailment what [rewrite] is to equality. *)

Lemma xchange_demo_base : forall H1 H2 H2' H3 H4,
  H2 ==> H2' ->
  H1 \* H2 \* H3 ==> H4.
Proof using.
  introv M. xchange M. (* Note that freshly produced items appear to the front *)
Abort.

(** The tactic [xchange] can also take as argument equalities.
    Use [xchange M] to exploit the left-to-right direction
    and [xchange <- M] to exploit the right-to-left direction . *)

Lemma xchange_demo_eq : forall H1 H2 H3 H4 H5,
  H1 \* H3 = H5 ->
  H1 \* H2 \* H3 ==> H4.
Proof using.
  introv M. xchange M.
  xchange <- M.
Abort.

(** The tactic [xchange] is also able to instantiate lemmas if needed. *)

Lemma xchange_demo_inst : forall H1 (J J':int->hprop) H3 H4,
  (forall n, J n = J' (n+1)) ->
  H1 \* J 3 \* H3 ==> H4.
Proof using.
  introv M. xchange M.
  (* Note that freshly produced items appear to the front *)
Abort.

(** The tactic [xchanges M] is a shorthand for [xchange M; xsimpl]. *)

Lemma xchanges_demo_base : forall p H1 H2 H3,
  H1 \* H3 ==> p ~~~> 3 ->
  H1 \* H2 \* H3 ==> H2 \* \exists (n:int), p ~~~> n.
Proof using.
  introv M. dup.
  (* details: *)
  { xchange M. xsimpl. }
  (* shorthand: *)
  { xchanges M. }
Abort.

End Htactics.
*)