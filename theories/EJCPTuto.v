(**

EJCP: tutorial using basic functions.
The tutorial continues with the files:
- ExampleStack
- ExampleList
- ExamplePairingHeap

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.

From Sep Require Import Example.




(* ####################################################### *)
(** * Entailment tactic *)

Module XsimplDemo.
Implicit Types p q : loc.

(* ******************************************************* *)
(** *** [xpull] to extract from LHS *)

Lemma xpull_demo_hpure : forall H1 H2 n,
  H1 \* \[n = 3] ==> H2.
Proof using.
  intros. xpull. intros Hn.
Abort.

Lemma xpull_demo_hpure_false : forall H1 H2,
  H1 \* \[False] ==> H2.
Proof using.
  intros. xpull. 
Abort.

Lemma xpull_demo_hexists : forall H1 H2 p,
  H1 \* \exists (n:int), (p ~~~> n) ==> H2.
Proof using.
  intros. xpull. intros n.
Abort.

Lemma xpull_demo_lhs_several : forall H1 H2 H3 H4 p q,
  H1 \* \exists (n:int), (p ~~~> n \* \[n > 0] \* H2) \* \[p <> q] \* H3 ==> H4.
Proof using.
  intros. xpull. intros n Hn Hp.
Abort.


(* ******************************************************* *)
(** *** [xsimpl] to cancel out heap predicates from LHS and RHS *)

(** For example, [H2] occurs on both sides, so it can be cancelled out. *)

Lemma xsimpl_demo_cancel_one : forall H1 H2 H3 H4 H5 H6 H7,
  H1 \* H2 \* H3 \* H4 ==> H5 \* H6 \* H2 \* H7.
Proof using.
  intros. xsimpl.
Abort.

(** [xsimpl] can cancel several predicates, here [H2], [H3], and [H4]. *)

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

(** [xsimpl] instantiates existential quantifiers, pure facts,
    and [\Top] in the RHS. *)

Lemma xsimpl_demo_rhs_hpure : forall H1 H2 H3 (n:int),
  H1 ==> H2 \* \[n > 0] \* H3.
Proof using.
  intros. xsimpl.
Abort.

(** For existentials, [xsimpl] introduces an evar. *)

Lemma xsimpl_demo_rhs_hexists : forall H1 H2 H3 H4 (p:loc),
  H1 ==> H2 \* \exists (n:int), (p ~~~> n \* H3) \* H4.
Proof using.
  intros. xsimpl. (* here, [p ~~~> n] becomes [p ~~~> ?x] *)
Abort.

(** The evar often gets subsequently instantiated during cancellation. *)

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

(** In some cases, it may desirable to provide an explicit instantiation,
    using the syntax [xsimpl v1 .. vn] or [xsimpl (>> v1 .. vn)]. *)

Lemma xsimpl_demo_rhs_hints : forall H1 (p q:loc),
  H1 ==> \exists (n m:int), (p ~~~> n \* q ~~~> m).
Proof using.
  intros. xsimpl 3 4.
Abort.

(** The placeholder value [__] can be used to skip an existential. *)

Lemma xsimpl_demo_rhs_hints_skip : forall H1 (p q:loc),
  H1 ==> \exists (n m:int), (p ~~~> n \* q ~~~> m).
Proof using.
  intros. xsimpl __ 4.
Abort.

(** [xsimpl] collapses the multiple occurences of [\Top].
    If the RHS consists of exactly [\Top] and nothing else, 
    then the goal is discharged. *)

Lemma xsimpl_demo_rhs_htop : forall H1 H2 H3,
  H1 \* H2 \* H3 ==> H3 \* \Top \* H2 \* \Top.
Proof using.
  intros. xsimpl.
Abort.

(** The tactic [xsimpl] also work on [===>]. *)

Lemma qimpl_example_1 : forall (Q1 Q2:val->hprop) (H2 H3:hprop),
  Q1 \*+ H2 ===> Q2 \*+ H2 \*+ H3.
Proof using. intros. xsimpl. intros r. Abort.


(* ******************************************************* *)
(** ** The [xchange] tactic *)

(** [xchange] is to entailment what [rewrite] is to equality. *)

(** Assume an entailment goal of the form [H1 \* H2 \* H3 ==> H4].
    Assume an entailment assumption [M], say [H2 ==> H2'].
    Then [xchange M] turns the goal into [H1 \* H2' \* H3 ==> H4],
    effectively replacing [H2] with [H2']. *)

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

End XsimplDemo.
