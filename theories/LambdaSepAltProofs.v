
Set Implicit Arguments.
From Sep Require LambdaSep LambdaSepLifted.
Generalizable Variables A.

(* ********************************************************************** *)
(* * Alternative proofs for LambdaSep *)

Module LambdaSepAlt.
Import LambdaSep.
Implicit Types P : Prop.

(* ---------------------------------------------------------------------- *)
(* ** Auxiliary lemma showing that reasoning rule for extracting
   pure propositions from preconditions is just a special case
   of the reasoning rule for extracting existentials from preconditions. *)

Lemma triple_hprop_from_hexists :
  forall (T:Type) (F:hprop->(T->hprop)->Prop),
  (forall (A:Type) (J:A->hprop) (Q:T->hprop),
    (forall x, F (J x) Q) ->
    F (hexists J) Q) ->
  (forall P H Q,
    (P -> F H Q) ->
    F (\[P] \* H) Q).
Proof using.
  introv M. introv N. rewrite hpure_eq_hexists_empty.
  rewrite hstar_hexists.
  applys M. rewrite~ hstar_hempty_l.
Qed.

Arguments triple_hprop_from_hexists [T].

Lemma triple_hwand_hpure_l_from_hexists_and_consequence :
  forall (T:Type) (F:hprop->(T->hprop)->Prop),
  (forall (A:Type) (J:A->hprop) (Q:T->hprop),
    (forall x, F (J x) Q) ->
    F (hexists J) Q) ->
  (forall H1 H2 (Q:T->hprop),
    F H1 Q ->
    H2 ==> H1 ->
    F H2 Q) ->
  (forall P H Q,
    P ->
    F H Q ->
    F (\[P] \-* H) Q).
Proof using.
  introv M W HP. introv N. rewrite hwand_eq_hexists_hstar_hpure.
  applys M. intros. applys* W. hpull. introv R. hchanges~ R.
Qed.

(* ---------------------------------------------------------------------- *)
(* ** Additional proofs for structural rules of LambdaSep's [hoare] triples *)

Lemma hoare_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, hoare t (J x) Q) ->
  hoare t (hexists J) Q.
Proof using. introv M (x&Hh). applys* M. Qed.

Lemma hoare_hforall : forall t (A:Type) (J:A->hprop) Q,
  (exists x, hoare t (J x) Q) ->
  hoare t (hforall J) Q.
Proof using. introv (x&M) Hh. applys* M. Qed.

Lemma hoare_hprop : forall t (P:Prop) H Q,
  (P -> hoare t H Q) ->
  hoare t (\[P] \* H) Q.
Proof using.
  introv M. applys~ triple_hprop_from_hexists.
  { applys* hoare_hexists. }
Qed.
(* Details:
  introv M (h1&h2&N1&N2&N3&N4).
  destruct (hpure_inv' N1). subst.
  rewrite heap_union_empty_l.
  applys* M.
*)

Lemma hoare_hwand_hpure_l : forall t (P:Prop) H Q,
  P ->
  hoare t H Q ->
  hoare t (\[P] \-* H) Q.
Proof using.
  introv HP M. applys~ triple_hwand_hpure_l_from_hexists_and_consequence.
  { applys* hoare_hexists. }
  { introv N W. applys* hoare_conseq. }
Qed.
(* Details:
  introv HP M. intros h (H1&(h1&h2&N1&N2&N3&N4)).
  lets (N2'&E): (hpure_inv' (rm N2)). subst.
  rewrite heap_union_empty_r.
  applys* M. applys N2'. hhsimpl~.
*)

(* ---------------------------------------------------------------------- *)
(* ** Alternative proofs for structural rules of LambdaSep's SL [triple] *)

Implicit Types H : hprop.
Implicit Types Q : val -> hprop.

Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
  introv M MH MQ. intros HF. applys hoare_conseq M.
  { hchanges MH. }
  { intros x. hchanges (MQ x). }
Qed.

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using.
  introv M. intros HF. rewrite hstar_hexists.
  applys hoare_hexists. intros. applys* M.
Qed.

Lemma triple_hforall : forall t A (J:A->hprop) Q,
  (exists x, triple t (J x) Q) ->
  triple t (hforall J) Q.
Proof using.
  introv (x&M). intros HF.
  forwards* N: hoare_hforall (fun x => J x \* HF).
  applys* hoare_conseq. applys hstar_hforall.
Qed.

(** corrolary *)
Lemma triple_hforall_for : forall A (x:A) t (J:A->hprop) Q,
  triple t (J x) Q ->
  triple t (hforall J) Q.
Proof using. intros. applys* triple_hforall. Qed.

Lemma triple_hprop : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. intros HF. rewrite hstar_assoc.
  applys hoare_hprop. intros. applys* M.
Qed.

Lemma triple_hwand_hpure_l : forall t (P:Prop) H Q,
  P ->
  triple t H Q ->
  triple t (\[P] \-* H) Q.
Proof using.
  introv HP M. intros HF.
  forwards* N: hoare_hwand_hpure_l P.
  applys* hoare_conseq. applys hstar_hwand.
Qed.

Lemma triple_hor : forall t H1 H2 Q,
  triple t H1 Q ->
  triple t H2 Q ->
  triple t (hor H1 H2) Q.
Proof using.
  introv M1 M2. unfold hor. applys triple_hexists.
  intros b. destruct* b.
Qed.

Lemma triple_hand_l : forall t H1 H2 Q,
  triple t H1 Q ->
  triple t (hand H1 H2) Q.
Proof using.
  introv M1. unfold hand. applys triple_hforall. exists* true.
Qed.

Lemma triple_hand_r : forall t H1 H2 Q,
  triple t H2 Q ->
  triple t (hand H1 H2) Q.
Proof using.
  introv M1. unfold hand. applys triple_hforall. exists* false.
Qed.

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using.
  introv M. intros HF.
  applys hoare_conseq (M (HF \* H')); hsimpl.
Qed.

Lemma triple_hgc_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.
Proof using.
  introv M. intros HF.
  applys hoare_conseq (M HF); hsimpl.
Qed.

Lemma triple_hgc_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \GC) Q.
Proof using.
  introv M. applys triple_hgc_post. applys~ triple_frame.
Qed.

Lemma triple_combined : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \GC ->
  triple t H Q.
Proof using.
  introv M WH WQ. applys triple_hgc_post. applys triple_conseq.
  { applys* triple_frame. } { eauto. } { eauto. }
Qed.

End LambdaSepAlt.


(* ********************************************************************** *)
(* * Alternative proofs for structural rules of LambdaSep's SL [triple] *)

Module LambdaSepLiftedAlt.
Import LambdaSep LambdaSepLifted.

Implicit Types H : hprop.

Hint Resolve Post_himpl.

Lemma Triple_conseq : forall t H' `{Enc A} (Q':A->hprop) H (Q:A->hprop),
  H ==> H' ->
  Triple t H' Q' ->
  Q' ===> Q ->
  Triple t H Q.
Proof using. introv MH M MQ. applys* triple_conseq MH. Qed.

Lemma Triple_hexists : forall t `{Enc A} B (J:B->hprop) (Q:A->hprop),
  (forall x, Triple t (J x) Q) ->
  Triple t (hexists J) Q.
Proof using. intros. applys~ triple_hexists. Qed.

Lemma Triple_hforall : forall t B (J:B->hprop) `{EA:Enc A} (Q:A->hprop),
  (exists x, Triple t (J x) Q) ->
  Triple t (hforall J) Q.
Proof using. unfold Triple. introv (x&M). applys* triple_hforall. Qed.

(** corrolary *)
Lemma Triple_hforall_for : forall B (x:B) t (J:B->hprop) `{EA:Enc A} (Q:A->hprop),
  Triple t (J x) Q ->
  Triple t (hforall J) Q.
Proof using. intros. applys* Triple_hforall. Qed.

Lemma Triple_hprop : forall t (P:Prop) `{Enc A} H (Q:A->hprop),
  (P -> Triple t H Q) ->
  Triple t (\[P] \* H) Q.
Proof using. intros. applys~ triple_hprop. Qed.

Lemma Triple_hwand_hpure_l : forall t (P:Prop) H `{EA:Enc A} (Q:A->hprop),
  P ->
  Triple t H Q ->
  Triple t (\[P] \-* H) Q.
Proof using. unfold Triple. introv M N. applys* triple_hwand_hpure_l. Qed.

Lemma Triple_frame : forall t `{Enc A} H (Q:A->hprop) H',
  Triple t H Q ->
  Triple t (H \* H') (Q \*+ H').
Proof using.
  introv M. unfold Triple. rewrite Post_star. applys* triple_frame.
Qed.

(*
Lemma Triple_ramified_frame_hgc : forall t `{Enc A} H H1 (Q1 Q:A->hprop),
  Triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q \*+ \GC) ->
  Triple t H Q.
Proof using. .. Qed.

Lemma Triple_ramified_frame : forall t `{Enc A} H H1 (Q1 Q:A->hprop),
  Triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  Triple t H Q.
Proof using. .. Qed.
*)

Lemma Triple_hor : forall t H1 H2 `{Enc A} (Q:A->hprop),
  Triple t H1 Q ->
  Triple t H2 Q ->
  Triple t (hor H1 H2) Q.
Proof using. introv M1 M2. applys* triple_hor. Qed.

Lemma triple_hand_l : forall t H1 H2 `{Enc A} (Q:A->hprop),
  Triple t H1 Q ->
  Triple t (hand H1 H2) Q.
Proof using. introv M1 M2. applys* triple_hand_l. Qed.

Lemma Triple_hand_r : forall t H1 H2 `{Enc A} (Q:A->hprop),
  Triple t H2 Q ->
  Triple t (hand H1 H2) Q.
Proof using. introv M1 M2. applys* triple_hand_r. Qed.

Lemma Triple_hgc_post : forall t `{Enc A} H (Q:A->hprop),
  Triple t H (Q \*+ \GC) ->
  Triple t H Q.
Proof using.
  introv M. unfolds Triple. rewrite Post_star in M. applys* triple_hgc_post.
Qed.

Lemma Triple_hgc_pre : forall t `{Enc A} H (Q:A->hprop),
  Triple t H Q ->
  Triple t (H \* \GC) Q.
Proof using. introv M. applys* triple_hgc_pre. Qed.

Lemma Triple_combined : forall t H1 H2 `{Enc A} (Q1 Q:A->hprop) H,
  Triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \GC ->
  Triple t H Q.
Proof using.
  introv M WH WQ. applys* triple_conseq_frame_hgc.
  do 2 rewrite <- Post_star. apply* Post_himpl.
Qed.

End LambdaSepLiftedAlt.