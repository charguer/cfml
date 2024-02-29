Set Implicit Arguments.
From CFML Require Import WPLib.
From CFML Require Import Stdlib.
From EXAMPLES Require Import MList_ml Queue_ml.
From EXAMPLES Require Import MList_proof.
From TLC Require Import LibListZ.
Import SpecMList.

Definition MQueue  A `{EA:Enc A} (L: list A) (q: loc) : hprop :=
  \exists (f r: loc) L1 L2, (q ~~~> `{ front' := f; rear' := r; size' := length L }) \*
                         (f ~> MList L1) \* (r ~> MList L2) \*
                         \[L1 = nil -> L2 = nil] \* \[L = L1 ++ rev L2].

Section Ops.

Context A {EA:Enc A}.
Implicit Types L : list A.

Lemma nil_rev_nil : forall A,
    (@nil A) = (@nil A) ++ rev (@nil A).
Proof using. auto. Qed.

Lemma Triple_create :
  SPEC (create tt)
    PRE \[]
    POST (fun q => MQueue (@nil A) q).
Proof using.
  xcf. xapp ;=> x1. xapp ;=> x2.
  xapp ;=> r. unfold MQueue.
  xsimpl*.
  { apply nil_rev_nil. }
  { do 2 xchanges <- MList_nil. }
Qed.

Lemma Triple_queue_is_empty : forall L q,
    SPEC (is_empty q)
      PRE (MQueue L q)
      POST (fun b => MQueue L q \* \[b = isTrue (L = nil)]).
Proof using.
  xcf. unfold MQueue. xpull*. intros.
  xapp. xvals*. split.
  { apply length_zero_inv. }
  { intros Hnil. rewrite Hnil. auto. }
Qed.

Lemma Triple_push : forall L (x: A) (q: loc),
    SPEC (push x q)
      PRE (MQueue L q)
      POST (fun (_:unit) => MQueue (L & x) q).
Proof using.
  xcf. xapp* Triple_queue_is_empty ;=>.
  destruct L as [|x' L'].
  { rewrite <- LibListExec.is_nil_eq in H.
    simpl in *. subst.
    xif; intros; tryfalse *.
    { xapp. intros.
      xapp. unfold MQueue. xpull* ;=>.
      xapp. xapp. xapp. xsimpl*.
      { auto_false*. }
      { rew_list*. f_equal.
        apply nil_eq_app_inv in H1.
        destruct H1. auto. } } }
  { cuts * G : (~ x' :: L' = nil).
    { apply isTrue_eq_false in G.
      subst. xif; intros; tryfalse *.
      unfold MQueue. xpull ;=>.
      xapp. xapp. xapp. xapp. xsimpl*.
      { rew_list*. math. }
      { intros. assert (x2 = nil) by auto.
        apply H0 in H2. subst.
        rew_list* in *. }
      { rewrite H1. rew_list*. } }
    { auto_false. } }
Qed.

Lemma Triple_pop : forall L q,
    L <> nil ->
    SPEC (pop q)
      PRE (MQueue L q)
      POST (fun x => \exists L', \[L = x :: L'] \* MQueue L' q).
Proof using.
  xcf. unfold MQueue. xpull* ;=>.
  xapp. xchange* (MList_eq x) ;=> f.
  xapp. xmatch.
  { xchange MList_contents_iff ;=>.
    destruct H2. cuts G : (x1 = nil); auto.
    cuts G2 : (x2 = nil); auto. subst.
    rew_list in *. contradiction. }
  { unfold MList_contents. destruct x1; xpull* ;=>.
    inversion H2; subst. xchange* (MList_eq x4) ;=>.
    xchange* <- (MList_eq x4). xapp. xif ;=>.
    { subst. xapp. xapp ;=>. xapp. xapp ;=>.
      xapp. xval. xapp. xapp. xval.
      xsimpl*; rew_list*; try math. }
    { xapp. xchange* <- MList_cons. xapp ;=>.
      { auto_false*. }
      { inversion H3; subst. xapp. xapp. xval.
        xsimpl*; rew_list*; try math. } } }
Qed.

Lemma Triple_transfer : forall L1 L2 (q1 q2: loc),
    SPEC (transfer q1 q2)
      PRE (MQueue L1 q1 \* MQueue L2 q2)
      POSTUNIT (MQueue (@nil A) q1 \* MQueue (L2 ++ L1) q2).
Proof using.
  intros. gen q1 q2 L2.
  induction_wf IH : list_sub L1.
  xcf. xapp Triple_queue_is_empty ;=>.
  destruct L1 as [| x' L1']; xif ;=>.
  { assert (@nil A = nil) by auto.
    apply isTrue_eq_true in H1. auto_false. }
  { xval. rew_list*. xsimpl*. }
  { xapp Triple_pop ;=>.
    { intros false; inversion false. }
    { xapp Triple_push. inversion H1; subst. xapp; try constructor.
      rew_list*. xsimpl*. } }
  { assert (~ x' :: L1'= nil).
    { intros false. inversion false. }
    { apply isTrue_eq_false in H1.
      rewrite H1 in H. subst. inversion H0. } }
Qed.

End Ops.
