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

Lemma Triple_is_empty : forall L q,
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
  xcf.
  xapp* Triple_is_empty ;=>.
  destruct L as [|x' L'].
  { Search (isTrue _).
    rewrite <- LibListExec.is_nil_eq in H.
    simpl in *. subst.
    xif; intros; tryfalse *.
    { xapp. intros.
      xapp. unfold MQueue. xpull* ;=>.
      xapp. xapp. xapp. xsimpl*.
      { intros false. inversion false. }
      { rew_list*. f_equal.
        apply nil_eq_app_inv in H1.
        destruct H1. auto. } } }
  { Search (_ :: _ = nil).
    cuts * G : (~ x' :: L' = nil).
    { Search isTrue _.
      apply isTrue_eq_false in G.
      subst. xif; intros; tryfalse *.
      unfold MQueue. xpull ;=>.
      xapp. xapp. xapp. xapp. xsimpl*.
      { rew_list*. math. }
      { intros. assert (x2 = nil) by auto.
        apply H0 in H2. subst.
        rew_list* in *. }
      { rewrite H1. rew_list*. } }
    { intros false. inversion false. } }
Qed.

End Ops.
