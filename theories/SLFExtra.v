(**

Separation Logic Foundations

Chapter: "Extra".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Export SLFDirect.

(** Implicit Types *)

Implicit Types n : int.
Implicit Types v w : val.
Implicit Types l : loc.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(** The type [heap], a.k.a. [state]. By convention, the "state"
    refers to the full memory state, while the "heap" potentially
    refers to only a fraction of the memory state. *)

Definition state : Type := heap.


(* ####################################################### *)
(** * Additional Hoare Triples *)

Section Hoare.

Lemma hoare_hforall : forall t (A:Type) (J:A->hprop) Q,
  (exists x, hoare t (J x) Q) ->
  hoare t (hforall J) Q.
Proof using. introv (x&M) Hh. applys M. applys* himpl_hforall_l. Qed.

Lemma hoare_hwand_hpure_l : forall t (P:Prop) H Q,
  P ->
  hoare t H Q ->
  hoare t (\[P] \-* H) Q.
Proof using.
  Transparent hwand.
  introv HP M. unfold hwand. applys hoare_hexists. intros H'.
  rewrite hstar_comm. applys hoare_hpure. intros N.
  applys hoare_conseq M. { hchange~ N. } { hsimpl. }
Qed.

End Hoare.


(* ####################################################### *)
(** * Separation Logic Triples *)


(* ******************************************************* *)
(** ** Structural rules *)

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

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using.
  introv M. intros HF.
  applys hoare_conseq (M (HF \* H')); hsimpl.
Qed.

Lemma triple_htop_post : forall t H Q,
  triple t H (Q \*+ \Top) ->
  triple t H Q.
Proof using.
  introv M. intros HF.
  applys hoare_conseq (M HF); hsimpl.
Qed.

Lemma triple_htop_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \Top) Q.
Proof using.
  introv M. applys triple_htop_post. applys~ triple_frame.
Qed.

Lemma triple_hany_pre : forall t H H' Q,
  triple t H Q ->
  triple t (H \* H') Q.
Proof using.
  introv M. applys triple_conseq.
  { applys* triple_htop_pre. }
  { hsimpl. } { hsimpl. }
Qed.

Lemma triple_hany_post : forall t H H' Q,
  triple t H (Q \*+ H') ->
  triple t H Q.
Proof using.
  introv M. applys triple_htop_post.
  applys triple_conseq M; hsimpl.
Qed.

Lemma triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.
Proof using.
  introv M WH WQ. applys triple_conseq WH WQ.
  applys triple_frame M.
Qed.

Lemma triple_conseq_frame_htop : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \Top ->
  triple t H Q.
Proof using.
  introv M WH WQ. applys triple_htop_post.
  applys triple_conseq_frame M WH WQ.
Qed.

Lemma triple_ramified_frame : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  triple t H Q.
Proof using.
  introv M W. applys triple_conseq_frame (Q1 \--* Q) M.
  { applys W. } { rewrite~ <- qwand_equiv. }
Qed.

Lemma triple_ramified_frame_htop : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* (Q \*+ \Top)) ->
  triple t H Q.
Proof using. 
  introv M W. applys triple_conseq_frame_htop (Q1 \--* Q \*+ \Top) M.
  { applys W. } { rewrite~ <- qwand_equiv. }
Qed.

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using.
  introv M. intros HF. rewrite hstar_hexists.
  applys hoare_hexists. intros. applys* M.
Qed.

Lemma triple_hforall : forall A (x:A) t (J:A->hprop) Q,
  triple t (J x) Q ->
  triple t (hforall J) Q.
Proof using.
  introv M. intros HF.
  forwards* N: hoare_hforall (fun x => J x \* HF).
  applys* hoare_conseq. applys himpl_trans. applys hstar_hforall.
  applys* himpl_hforall_l.
Qed.

Lemma triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. intros HF. rewrite hstar_assoc.
  applys hoare_hpure. intros. applys* M.
Qed.

Lemma triple_hwand_hpure_l : forall t (P:Prop) H Q,
  P ->
  triple t H Q ->
  triple t (\[P] \-* H) Q.
Proof using.
  introv HP M. intros HF. applys* hoare_conseq M.
  hsimpl. applys hwand_hpure_l_intro HP.
Qed.


(* ******************************************************* *)
(** ** Rules for terms *)

Lemma triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using.
  introv M. intros HF. applys hoare_val. { hchanges M. }
Qed.

Lemma triple_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  triple (trm_fun x t1) H Q.
Proof using.
  introv M. intros HF. applys~ hoare_fun. { hchanges M. }
Qed.

Lemma triple_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triple (trm_fix f x t1) H Q.
Proof using.
  introv M. intros HF. applys~ hoare_fix. { hchanges M. }
Qed.

Lemma triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF. applys hoare_seq.
  { applys M1. }
  { applys hoare_conseq M2; hsimpl. }
Qed.

Lemma triple_let : forall z t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall (X:val), triple (subst z X t2) (Q1 X) Q) ->
  triple (trm_let z t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF. applys hoare_let.
  { applys M1. }
  { intros v. applys hoare_conseq M2; hsimpl. }
Qed.

Lemma triple_if_case : forall (b:bool) t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros HF. applys hoare_if_case. applys M1.
Qed.

Lemma triple_app_fun : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
  unfold triple. introv E M1. intros H'.
  applys hoare_app_fun E. applys M1.
Qed.

Lemma triple_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  triple (subst x v2 (subst f v1 t1)) H Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
  unfold triple. introv E M1. intros H'.
  applys hoare_app_fix E. applys M1.
Qed.


(* ******************************************************* *)
(** ** Rules for primitives *)

Lemma triple_add : forall n1 n2,
  triple (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).
Proof using.
  intros. intros H'. applys hoare_conseq. 
  { applys hoare_add. } { hsimpl. } { hsimpl. auto. }
Qed.

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists l, \[r = val_loc l] \* l ~~~> v).
Proof using.
  intros. intros HF. applys hoare_conseq hoare_ref; hsimpl~.
Qed.

Lemma triple_get : forall v l,
  triple (val_get (val_loc l))
    (l ~~~> v)
    (fun x => \[x = v] \* (l ~~~> v)).
Proof using.
  intros. intros HF. applys hoare_conseq hoare_get; hsimpl~.
Qed.

Lemma triple_set : forall w l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => \[r = val_unit] \* l ~~~> w).
Proof using.
  intros. intros HF. applys hoare_conseq hoare_set; hsimpl~.
Qed.




(* ####################################################### *)
(* LATER

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

*)
