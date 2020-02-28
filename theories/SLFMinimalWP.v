
(* ########################################################### *)
(** ** Definition of [wp] and reasoning rules *)

(* ################################################ *)
(** *** Definition of the weakest-precondition judgment. *)

(** [wp] is defined on top of [hoare] triples. More precisely [wp t Q]
    is a heap predicate such that [H ==> wp t Q] if and
    only if [SL_triple t H Q], where [SL_triple t H Q]
    is defined as [forall H', hoare t (H \* H') (Q \*+ H')]. *)

Definition wp (t:trm) := fun (Q:val->hprop) =>
  \exists H, H \* \[forall H', hoare t (H \* H') (Q \*+ H')].


(* ################################################ *)
(** *** Structural rule for [wp]. *)

(** The ramified frame rule (with garbage collection) *)

Lemma wp_ramified : forall Q1 Q2 t,
  (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).
Proof using.
  intros. unfold wp. xpull. intros H M.
  xsimpl (H \* (Q1 \--* Q2)). intros H'.
  applys hoare_conseq M; xsimpl.
Qed.

Arguments wp_ramified : clear implicits.

(** Corollaries *)

Lemma wp_conseq : forall t Q1 Q2,
  Q1 ===> Q2 ->
  wp t Q1 ==> wp t Q2.
Proof using.
  introv M. applys himpl_trans_r (wp_ramified Q1 Q2). xsimpl. xchanges M.
Qed.

Lemma wp_frame : forall t H Q,
  (wp t Q) \* H ==> wp t (Q \*+ H).
Proof using. intros. applys himpl_trans_r wp_ramified. xsimpl. Qed.

Lemma wp_ramified_frame : forall t Q1 Q2,
  (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).
Proof using. intros. applys himpl_trans_r wp_ramified. xsimpl. Qed.

Lemma wp_ramified_trans : forall t H Q1 Q2,
  H ==> (wp t Q1) \* (Q1 \--* Q2) ->
  H ==> (wp t Q2).
Proof using. introv M. xchange M. applys wp_ramified. Qed.


(* ################################################ *)
(** *** Weakest-precondition style reasoning rules for terms. *)

Lemma wp_eval_like : forall t1 t2 Q,
  eval_like t1 t2 ->
  wp t1 Q ==> wp t2 Q.
Proof using.
  introv E. unfold wp. xpull. intros H M. xsimpl H.
  intros H'. applys hoare_eval_like E M.
Qed.

Lemma wp_val : forall v Q,
  Q v ==> wp (trm_val v) Q.
Proof using. intros. unfold wp. xsimpl; intros H'. applys hoare_val. xsimpl. Qed.

Lemma wp_fun : forall x t Q,
  Q (val_fun x t) ==> wp (trm_fun x t) Q.
Proof using. intros. unfold wp. xsimpl; intros H'. applys hoare_fun. xsimpl. Qed.

Lemma wp_fix : forall f x t Q,
  Q (val_fix f x t) ==> wp (trm_fix f x t) Q.
Proof using. intros. unfold wp. xsimpl; intros H'. applys hoare_fix. xsimpl. Qed.

Lemma wp_app_fun : forall x v1 v2 t1 Q,
  v1 = val_fun x t1 ->
  wp (subst x v2 t1) Q ==> wp (trm_app v1 v2) Q.
Proof using. introv EQ1. unfold wp. xsimpl; intros. applys* hoare_app_fun. Qed.
(* variant: introv EQ1. applys wp_eval_like. introv R. applys* eval_app_fun. *)

Lemma wp_app_fix : forall f x v1 v2 t1 Q,
  v1 = val_fix f x t1 ->
  wp (subst x v2 (subst f v1 t1)) Q ==> wp (trm_app v1 v2) Q.
Proof using. introv EQ1. unfold wp. xsimpl; intros. applys* hoare_app_fix. Qed.
(* variant: introv EQ1. applys wp_eval_like. introv R. applys* eval_app_fix. *)

Lemma wp_seq : forall t1 t2 Q,
  wp t1 (fun r => wp t2 Q) ==> wp (trm_seq t1 t2) Q.
Proof using.
  intros. unfold wp at 1. xsimpl. intros H' M1.
  unfold wp at 1. xsimpl. intros H''.
  applys hoare_seq. applys (rm M1). unfold wp.
  repeat rewrite hstar_hexists. applys hoare_hexists; intros H'''.
  rewrite (hstar_comm H'''); repeat rewrite hstar_assoc.
  applys hoare_hpure; intros M2. applys hoare_conseq M2; xsimpl.
Qed.

Lemma wp_let : forall x t1 t2 Q,
  wp t1 (fun v => wp (subst x v t2) Q) ==> wp (trm_let x t1 t2) Q.
Proof using.
  intros. unfold wp at 1. xsimpl. intros H' M1.
  unfold wp at 1. xsimpl. intros H''.
  applys hoare_let. applys (rm M1). intros v. simpl. unfold wp.
  repeat rewrite hstar_hexists. applys hoare_hexists; intros H'''.
  rewrite (hstar_comm H'''); rew_heap.
  applys hoare_hpure; intros M2. applys hoare_conseq M2; xsimpl.
Qed.

Lemma wp_if : forall b t1 t2 Q,
  wp (if b then t1 else t2) Q ==> wp (trm_if b t1 t2) Q.
Proof using.
  intros. repeat unfold wp. xsimpl; intros H M H'.
  applys hoare_if. applys M.
Qed.

Lemma wp_if_case : forall b t1 t2 Q,
  (if b then wp t1 Q else wp t2 Q) ==> wp (trm_if b t1 t2) Q.
Proof using. intros. applys himpl_trans wp_if. case_if~. Qed.


Lemma wp_equiv : forall t H Q,
  (H ==> wp t Q) <-> (triple t H Q).
Proof using.
  unfold wp, triple. iff M.
  { intros H'. applys hoare_conseq. 2:{ applys himpl_frame_l M. }
     { clear M. rewrite hstar_hexists. applys hoare_hexists. intros H''.
       rewrite (hstar_comm H''). rew_heap. applys hoare_hpure. intros N.
       applys N. }
     { auto. } }
  { xsimpl H. apply M. }
Qed.


