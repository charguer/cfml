
Set Implicit Arguments.
From Sep Require SepBase SepLifted.
Generalizable Variables A.

(* ********************************************************************** *)
(* * Alternative proofs for SepBase structural rules *)

Module SepBaseAltStruct.
Import SepBase.
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
(* ** Additional proofs for structural rules of SepBase's [hoare] triples *)

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
(* ** Alternative proofs for structural rules of SepBase's SL [triple] *)

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

End SepBaseAltStruct.


(* ********************************************************************** *)
(* * Alternative proofs for structural rules of SepBase's SL [triple] *)

Module SepLiftedAltStruct.
Import SepBase SepLifted.

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

End SepLiftedAltStruct.


(* ********************************************************************** *)
(* * Alternative proofs for SepBase term rules *)

Module SepBaseAltTerm.
Import SepBase.
Implicit Types P : Prop.
Implicit Types v w : val.
Implicit Types n : int.

(* ---------------------------------------------------------------------- *)
(* ** Definition of triples *)

(** This is a total-correctness definition of a triple, for a
  deterministic language. (Remark: our definition makes sense even though
  technically allocation picks fresh locations in a non-deterministic
  manner, because identity of locations do not influence program
  behaviors.)

  Below, the evaluation of [t] in state [h] terminates on value [v]
  in state [h'], when [h] satisfies the pre-condition [H] starred
  with a heap predicate [H'] describing the framed part, and where
  the final state [h'] satisfies the post-condition [Q] applied to the
  result value [v], starred with the framed part [H'], and starred
  with [\Top] to account for garbage collection.

  Remark: in a C-style language, [\Top] needs to be defined in a
  more restrictive way to enforce deallocation of malloc-ed blocks. *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) :=
  forall H' h,
  (H \* H') h ->
  exists h' v,
       red h t h' v
    /\ (Q v \* \Top \* H') h'.


(* ---------------------------------------------------------------------- *)
(* ** Triples satisfy the [local] predicate *)

(** This lemma is exploited indirectly by tactics such as [xapply],
  which perform application of lemmas modulo framing. *)


Lemma is_local_triple : forall t,
  is_local (triple t).
Proof using.
  skip.
(* TODO updated def...
  intros. applys pred_ext_2. intros H Q. iff M.
  { intros h Hh. forwards (h'&v&N1&N2): M \[] h. { hhsimpl. }
    exists H \[] Q. hhsimpl. splits~. hsimpl. }
  { intros H' h Hh. lets (h1&h2&N1&N2&N3&N4): Hh. hnf in M.
    lets (H1&H2&Q1&R): M N1. rewrite <-hstar_assoc, hstar_comm, hstar_hpure in R.
    lets ((R1&R2)&R3): R.
    forwards (h'&v&S1&S2): R1 (H2\*H') h.
    { subst h. rewrite <- hstar_assoc. exists~ h1 h2. }
    exists h' v. splits~. rewrite <- hstar_htop_htop.
    applys himpl_inv S2.
    hchange (R2 v). rew_heap.
    rewrite (hstar_comm_assoc \Top H'). hsimpl. }
*)
Qed.

(** Make tactic [xlocal] aware that triples are local *)

Ltac xlocal_base tt ::=
  try first [ applys is_local_local
            | applys is_local_triple ].


(* ---------------------------------------------------------------------- *)
(* ** Structural rules *)

(** Note: all these rules could be derived directly from the fact that
    [triple] satisfies [is_local], using lemmas from [SepFunctor] *)

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using.
  introv M. intros HF h N. rewrite hstar_hexists in N.
  destruct N as (x&N). applys* M.
Qed.

Lemma triple_hforall_exists : forall t (A:Type) (J:A->hprop) Q,
  (exists x, triple t (J x) Q) ->
  triple t (hforall J) Q.
Proof using.
  introv (x&M). intros HF h N. lets N': hstar_hforall (rm N) x.
  applys* M.
Qed.

Lemma triple_hprop : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. intros HF h N. rewrite hstar_assoc in N. rewrite hstar_hpure in N.
  destruct N as (x&N). applys* M.
Qed.

Lemma triple_hwand_hpure_l : forall t (P:Prop) H Q,
  P ->
  triple t H Q ->
  triple t (\[P] \-* H) Q.
Proof using.
  introv HP M. intros HF h N.
  lets N': hstar_hwand (rm N).
  lets U: (conj (rm HP) (rm N')). rewrite <- hstar_hpure in U.
  lets U': hwand_cancel (rm U).
  applys* M.
Qed.

Lemma triple_conseq : forall t H' Q' H Q,
  H ==> H' ->
  triple t H' Q' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
  introv MH M MQ. intros HF h N.
  forwards (h'&v&R&K): (rm M) HF h. { hhsimpl~. }
  exists h' v. splits~. { hhsimpl. hchanges (MQ v). }
Qed.

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using.
  introv M. intros HF h N. rewrite hstar_assoc in N.
  forwards (h'&v&R&K): (rm M) (H' \* HF) h. { hhsimpl~. }
  exists h' v. splits~. { hhsimpl~. }
Qed.

Lemma triple_htop_post : forall t H Q,
  triple t H (Q \*+ \Top) ->
  triple t H Q.
Proof using.
  introv M. intros HF h N. forwards* (h'&v&R&K): (rm M) HF h.
  exists h' v. splits~. { rewrite <- hstar_htop_htop. hhsimpl. }
Qed.

Lemma triple_htop_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \Top) Q.
Proof using.
  introv M. applys triple_htop_post. applys~ triple_frame.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Term rules *)

Lemma triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using.
  introv M. intros HF h N. exists h v. splits.
  { applys red_val. }
  { hhsimpl. hchanges M. }
Qed.

(*
Lemma triple_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  triple (trm_fun x t1) H Q.
Proof using.
  introv M. intros HF h N. exists___. splits.
  { applys red_fun. }
  { hhsimpl. hchanges M. }
Qed.
*)

Lemma triple_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triple (trm_fix f x t1) H Q.
Proof using.
  introv M. intros HF h N. exists___. splits.
  { applys red_fix. }
  { hhsimpl. hchanges M. }
Qed.


(* TODO: move to SepFunctor? *)
Lemma hprop_extract_hfalse : forall H1 H2 h,
  (H1 \* H2) h -> 
  H1 ==> \[False] ->
  False.
Proof using.
  introv M1 M2. lets: himpl_frame_l M2 M1. rewrite* hstar_hpure in H.
Qed.

Lemma triple_if : forall Q1 t0 t1 t2 H Q,
  triple t0 H Q1 ->
  (forall (b:bool), triple (if b then t1 else t2) (Q1 b) Q) ->
  (forall v, ~ is_val_bool v -> (Q1 v) ==> \[False]) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2 M3. intros HF h N.
  forwards* (h1'&v&R1&K1): (rm M1) HF h.
  tests C: (is_val_bool v).
  { destruct C as (b&E). subst. forwards* (h'&v'&R&K): (rm M2) h1'.
    exists h' v'. splits~.
    { applys* red_if_trm. }
    { rewrite <- hstar_htop_htop. rew_heap~. } }
  { false hprop_extract_hfalse K1. applys~ M3. }
Qed.

Lemma triple_if_bool : forall (b:bool) t1 t2 H Q,
  (b = true -> triple t1 H Q) ->
  (b = false -> triple t2 H Q) ->
  triple (trm_if b t1 t2) H Q.
Proof using.
  introv M1 M2. applys triple_if (fun r => \[r = val_bool b] \* H).
  { applys triple_val. hsimpl~. }
  { intros b'. applys~ triple_hprop. intros E. inverts E. case_if*. }
  { intros v' N. hpull. intros E. inverts~ E. false N. hnfs*. }
Qed.

Lemma triple_seq : forall t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall (X:val), triple t2 (Q1 X) Q) ->
  triple (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF h N.
  lets~ (h1'&v1&R1&K1): (rm M1) HF h.
  subst. forwards* (h2'&v2&R2&K2): (rm M2) (\Top \* HF) h1'.
  exists h2' v2. splits~.
  { applys~ red_seq R1 R2. }
  { rewrite <- hstar_htop_htop. hhsimpl. }
Qed.

Lemma triple_let : forall z t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall (X:val), triple (subst1 z X t2) (Q1 X) Q) ->
  triple (trm_let z t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF h N.
  lets~ (h1'&v1&R1&K1): (rm M1) HF h.
  forwards* (h2'&v2&R2&K2): (rm M2) (\Top \* HF) h1'.
  exists h2' v2. splits~.
  { applys~ red_let_trm R2. }
  { rewrite <- hstar_htop_htop. hhsimpl. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Rules for loops *)

Lemma triple_while_raw : forall t1 t2 H Q,
  triple (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) H Q ->
  triple (trm_while t1 t2) H Q.
Proof using.
  introv M. intros H' h Hf. forwards (h'&v&R&K): (rm M) Hf.
  exists h' v. splits~. { applys* red_while. }
Qed.

Lemma triple_while : forall t1 t2 H Q,
  (forall t,
     (forall H' Q', triple (trm_if t1 (trm_seq t2 t) val_unit) H' Q' ->
                    triple t H' Q') ->
    triple t H Q) ->
  triple (trm_while t1 t2) H Q.
Proof using.
  introv M. applys M. introv K. applys triple_while_raw. applys K.
Qed.

Lemma triple_while_inv : forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) t1 t2 H,
  let Q := (fun r => \exists Y, I false Y) in
  wf R ->
  (H ==> (\exists b X, I b X) \* \Top) -> (* LATER: replace \top with H' *)
  (forall t b X,
      (forall b' X', R X' X -> triple t (I b' X') Q) ->
      triple (trm_if t1 (trm_seq t2 t) val_unit) (I b X) Q) ->
  triple (trm_while t1 t2) H Q. (* LATER: allow for weakening on Q *)
Proof using.
  introv WR H0 HX. xchange (rm H0). xpull ;=> b0 X0.
  rewrite hstar_comm. applys triple_htop_pre. gen b0.
  induction_wf IH: WR X0. intros. applys triple_while_raw.
  applys HX. intros b' X' HR'. applys~ IH.
Qed.

Lemma triple_for_raw : forall (x:var) (n1 n2:int) t3 H (Q:val->hprop),
  triple (
    If (n1 <= n2)
      then (trm_seq (subst1 x n1 t3) (trm_for x (n1+1) n2 t3))
      else val_unit) H Q ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using.
  introv M. intros H' h Hf. forwards (h'&v&R&K): (rm M) Hf.
  exists h' v. splits~. { applys~ red_for. }
Qed.

(* LATER: simplify proof using triple_for_raw *)
Lemma triple_for_gt : forall x n1 n2 t3 H Q,
  n1 > n2 ->
  H ==> Q val_unit \* \Top ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using.
  introv N M. intros H' h Hf. exists h val_unit. splits~.
  { applys* red_for_gt. }
  { hhsimpl. hchanges~ M. }
Qed.

(* LATER: simplify proof using triple_for_raw *)
Lemma triple_for_le : forall Q1 (x:var) n1 n2 t3 H Q,
  n1 <= n2 ->
  triple (subst1 x n1 t3) H Q1 ->
  (forall v, triple (trm_for x (n1+1) n2 t3) (Q1 v) Q) ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using.
  introv N M1 M2. intros HF h Hf. forwards (h1'&v1&R1&K1): (rm M1) Hf.
  forwards* (h2'&v2&R2&K2): (rm M2) (\Top \* HF) h1'.
  exists h2' v2. splits~.
  { applys* red_for_le. }
  { rewrite <- hstar_htop_htop. hhsimpl. }
Qed.

(* LATER: simplify proof using triple_for_raw *)
Lemma triple_for : forall (x:var) (n1 n2:int) t3 H Q,
  (If (n1 <= n2) then
    (exists Q1,
      triple (subst1 x n1 t3) H Q1 /\
      (forall v, triple (trm_for x (n1+1) n2 t3) (Q1 v) Q))
  else
    (H ==> Q val_unit)) ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using.
  introv M. case_if.
  { destruct M. applys* triple_for_le. }
  { xapplys* triple_for_gt. { math. } hchanges* M. }
Qed.

(* LATER: simplify proof using triple_for_raw *)
Lemma triple_for_inv : forall (I:int->hprop) H' (x:var) n1 n2 t3 H Q,
  (n1 <= n2+1) ->
  (H ==> I n1 \* H') ->
  (forall i, n1 <= i <= n2 ->
     triple (subst1 x i t3) (I i) (fun r => I (i+1))) ->
  (I (n2+1) \* H' ==> Q val_unit \* \Top) ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using.
  introv N M1 M2 M3. xchange (rm M1). gen N M2.
  induction_wf IH: (wf_upto (n2+1)) n1; intros.
  asserts M4: (triple (trm_for x (n2 + 1)%I n2 t3) (I (n2+1) \* H') Q).
  { applys triple_for_gt. { math. }
    { hchanges M3. } }
  tests C: (n1 = n2+1).
  { xapplys M4. }
  { applys triple_for_le.
    { math. }
    { xapplys M2. { math. } }
    { simpl. xpull ;=> _. tests C': (n1 = n2).
      { xapplys M4. }
      { xapplys IH. { hnf; math. } { math. } { intros. applys M2. math. } } } }
Qed.

(** Rules for for-loop not in normal form  -- DEPRECATED?

Lemma triple_for_trm : forall (x:var) (t1 t2 t3:trm) H (Q:val->hprop) (Q1:val->hprop),
  triple t1 H Q1 ->
  (forall v1, exists Q2,
      triple t2 (Q1 v1) Q2
   /\ (forall v2, triple (trm_for x v1 v2 t3) (Q2 v2) Q)) ->
  triple (trm_for x t1 t2 t3) H Q.
Proof using.
  introv M1 M2. intros HF h Hf. forwards (h1'&v1&R1&K1): (rm M1) Hf.
  lets (Q2&M2'&M3): ((rm M2) v1).
  forwards* (h2'&v2&R2&K2): (rm M2') h1'.
  rewrite <- (hstar_assoc \Top \Top) in K2. rewrite hstar_htop_htop in K2.
  forwards* (h'&v'&R'&K'): ((rm M3) v2) h2'.
  exists h' v'. splits~.
  { applys* red_for_arg. }
  { rewrite <- hstar_htop_htop. rew_heap~. }
Qed.
*)

Definition is_val_int (v:val) :=
  exists n, v = val_int n.

(* full rule, too complex -- DEPRECATEDScheme new_scheme := Induction for _ Sort _
with _ := Induction for _ Sort _.

Lemma triple_for_trm_int : forall (x:var) (t1 t2 t3:trm) H (Q:val->hprop) (Q1:val->hprop),
  triple t1 H Q1 ->
  (forall v, ~ is_val_int v -> (Q1 v) ==> \[False]) ->
  (forall (n1:int), exists Q2,
      triple t2 (Q1 (val_int n1)) Q2
   /\ (forall v, ~ is_val_int v -> (Q2 v) ==> \[False])
   /\ (forall (n2:int), triple (trm_for x n1 n2 t3) (Q2 (val_int n2)) Q)) ->
  triple (trm_for x t1 t2 t3) H Q.
Proof using. (* might be simplified using triple_for_trm *)
  introv M1 nQ1 M2. intros HF h Hf. forwards (h1'&v1&R1&K1): (rm M1) Hf.
  tests C1: (is_val_int v1).
  { destruct C1 as (n1&E). subst. lets (Q2&M2'&nQ2&M3): ((rm M2) n1).
    forwards* (h2'&v2&R2&K2): (rm M2') h1'.
    rewrite <- (hstar_assoc \Top \Top) in K2. rewrite hstar_htop_htop in K2.
    tests C2: (is_val_int v2).
    { destruct C2 as (n2&E). subst.
      forwards* (h'&v'&R'&K'): ((rm M3) n2) h2'.
      exists h' v'. splits~.
      { applys* red_for_arg. }
      { rewrite <- hstar_htop_htop. rew_heap~. } }
    { specializes nQ2 C2.
      asserts Z: ((\[False] \* \Top \* HF) h2').
      { applys himpl_trans K2. hchange nQ2. hsimpl. hsimpl. }
      repeat rewrite hfalse_hstar_any in Z.
      lets: hpure_inv Z. false*. } } (* LATER: shorten *)
  { specializes nQ1 C1.
    asserts Z: ((\[False] \* \Top \* HF) h1').
    { applys himpl_trans K1. hchange nQ1. hsimpl. hsimpl. }
    repeat rewrite hfalse_hstar_any in Z.
    lets: hpure_inv Z. false*. } (* LATER: shorten *)
Qed.
 *)

(* ---------------------------------------------------------------------- *)
(** Primitive functions over the state *)

Section RulesStateOps.
Transparent hstar hsingle hfield hexists loc null.

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists l, \[r = val_loc l] \* l ~~~> v).
Proof using.
  intros. intros HF h N.
  forwards~ (l&Dl&Nl): (fmap_single_fresh null h v).
  sets h1': (fmap_single l v).
  exists (h1' \u h) (val_loc l). splits~.
  { applys~ red_ref. }
  { exists h1' h. split.
    { exists l. applys~ himpl_hstar_hpure_r. unfold h1'. hnfs~. }
    { splits~. hhsimpl~. } }
Qed.

Lemma triple_get : forall v l,
  triple (val_get (val_loc l))
    (l ~~~> v)
    (fun x => \[x = v] \* (l ~~~> v)).
Proof using.
  intros. intros HF h N. exists h v. splits~.
  { applys red_get. destruct N as (?&?&(?&?)&?&?&?).
    subst h. applys~ fmap_union_single_l_read. }
  { rew_heap. rewrite hstar_hpure. split~. hhsimpl~. }
Qed.

Lemma triple_set : forall w l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => \[r = val_unit] \* l ~~~> w).
Proof using.
  intros. intros HF h N. destruct N as (h1&h2&(N0&N1)&N2&N3&N4).
  hnf in N1. sets h1': (fmap_single l w).
  exists (h1' \u h2) val_unit. splits~.
  { applys red_set. subst h h1. applys~ fmap_union_single_to_update. }
  { rew_heap. rewrite hstar_hpure. split~. exists h1' h2. splits~.
    { hnfs~. }
    { hhsimpl~. }
    { subst h1. applys~ fmap_disjoint_single_set v. } }
Qed.

Lemma triple_set' : forall w l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => l ~~~> w).
Proof using. intros. xapplys* triple_set. Qed.


(* ---------------------------------------------------------------------- *)
(** Alloc function *)

Lemma triple_alloc : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (fun r => \exists l, \[r = val_loc l /\ l <> null] \* Alloc (abs n) l).
Proof using. (* Note: [abs n] currently does not compute in Coq. *)
  introv N Hh.
  forwards~ (l&Dl&Nl): (fmap_conseq_fresh null h (abs n) val_unit).
  sets h1': (fmap_conseq l (abs n) val_unit).
  exists (h1' \u h) (val_loc l). splits~.
  { applys (red_alloc (abs n)); eauto.
    rewrite~ abs_nonneg. }
  { exists h1' h. split.
    { exists l. applys~ himpl_hstar_hpure_r. applys~ Alloc_fmap_conseq. }
    { splits~. hhsimpl~. } }
Qed.

End RulesStateOps.


(* ---------------------------------------------------------------------- *)
(** Other primitive functions *)

Lemma triple_eq : forall v1 v2,
  triple (val_eq v1 v2)
    \[]
    (fun r => \[r = isTrue (v1 = v2)]).
Proof using.
  introv Hh. exists___. splits.
  { applys* red_binop. applys* redbinop_eq. }
  { hhsimpl~. }
Qed.

Lemma triple_add : forall n1 n2,
  triple (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).
Proof using.
  introv Hh. exists___. splits.
  { applys* red_binop. applys* redbinop_add. }
  { hhsimpl*. }
Qed.

Lemma triple_sub : forall n1 n2,
  triple (val_sub n1 n2)
    \[]
    (fun r => \[r = val_int (n1 - n2)]).
Proof using.
  introv Hh. exists___. splits.
  { applys* red_binop. applys* redbinop_sub. }
  { hhsimpl*. }
Qed.

(* DEPRECATED details

Lemma triple_ptr_add : forall l n,
  l + n >= 0 ->
  triple (val_ptr_add l n)
    \[]
    (fun r => \[r = val_loc (abs (l + n))]).
Proof using.
  introv N Hh. exists___. splits.
  { applys* red_binop. applys* redbinop_ptr_add (abs (l + n)). rewrite~ abs_nonneg. }
  { hhsimpl*. }
Qed.

Lemma triple_ptr_add_nat : forall l (f:nat),
  triple (val_ptr_add l f)
    \[]
    (fun r => \[r = val_loc (l+f)%nat]).
Proof using.
  intros. xapplys~ triple_ptr_add. { math. }
  { applys* red_binop. intros. subst. fequals.
    applys eq_nat_of_eq_int. rewrite abs_nonneg; math. }
Qed.

(** Alternative direct proof for [triple_ptr_add_nat] *)

Lemma triple_ptr_add_nat' : forall l (f:nat),
  triple (val_ptr_add l f)
    \[]
    (fun r => \[r = val_loc (l+f)%nat]).
Proof using.
  introv Hh. exists___. splits.
  { applys* red_binop. applys* redbinop_ptr_add_nat. }
  { hhsimpl*. }
Qed.


*)

(* ---------------------------------------------------------------------- *)
(* ** Practical additional rules *)

(** Combination of [triple_val] and [triple_htop_post] *)

Lemma triple_val_htop : forall v H Q,
  H ==> Q v \* \Top ->
  triple (trm_val v) H Q.
Proof using.
  introv M. applys triple_htop_post. applys~ triple_val.
Qed.

(** Combination of [triple_frame] and [triple_conseq] *)

Lemma triple_frame_consequence : forall H2 H1 Q1 t H Q,
  H ==> H1 \* H2 ->
  triple t H1 Q1 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.
Proof using.
  introv WH M WQ. applys triple_conseq WH WQ. applys triple_frame M.
Qed.

(** Combination of [triple_let] and [triple_val] *)

Lemma triple_let_val : forall z v1 t2 H Q,
  (forall (X:val), X = v1 -> triple (subst1 z X t2) H Q) ->
  triple (trm_let z (trm_val v1) t2) H Q.
Proof using.
  introv M. forwards~ M': (rm M).
  applys_eq~ (>> triple_let H (fun x => \[x = v1] \* H)) 2.
  { applys triple_val. hsimpl~. }
  { intros X. applys triple_hprop. intro_subst. applys M'. }
Qed.

(** A rule of conditionals with case analysis already done *)

Lemma triple_if' : forall Q1 t0 t1 t2 H Q,
  triple t0 H Q1 ->
  triple t1 (Q1 true) Q ->
  triple t2 (Q1 false) Q ->
  (forall v, ~ is_val_bool v -> (Q1 v) ==> \[False]) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2 M3 M4. applys* triple_if.
  { intros b. case_if*. }
Qed.

(** A direct proof for [triple_if_bool] *)

Lemma triple_if_bool' : forall v t1 t2 H Q,
  (v = true -> triple t1 H Q) ->
  (v = false -> triple t2 H Q) ->
  (is_val_bool v) ->
  triple (trm_if v t1 t2) H Q.
Proof using.
  introv M1 M2 (b&E). intros HF h N. subst v.
  destruct b.
  { forwards* (h'&v'&R&K): (rm M1) h.
    exists h' v'. splits~.
    { applys* red_if_bool. } }
  { forwards* (h'&v'&R&K): (rm M2) h.
    exists h' v'. splits~.
    { applys* red_if_bool. } }
Qed.

(** A rule for unary function application -- DEPRECATED

Lemma triple_app : forall (f:bind) x F V t1 H Q,
  F = (val_fix f x t1) ->
  triple (subst2 f F x V t1) H Q ->
  triple (trm_app F V) H Q.
Proof using.
  introv EF M. subst F. intros HF h N.
  lets~ (h'&v&R&K): (rm M) HF h.
  exists h' v. splits~. { hint red_val. applys~ red_app. }
Qed.

*)

End SepBaseAltTerm.
