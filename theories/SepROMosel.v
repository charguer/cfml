Set Implicit Arguments.
From Sep Require Import SepRO SepMosel.


Module ProofMode.


(* ********************************************************************** *)
(* * Exposing [heap_empty] to MoSel *)

Module SepROCoreHempty <: SepCoreHemptySig SepROCore.

Definition heap_empty := heap_empty.

Lemma hempty_eq : hempty = (fun h => h = heap_empty).
Proof using. auto. Qed.

End SepROCoreHempty.


(* ********************************************************************** *)
(* * Subset of the interface of SepLogicSetup that needs to be exposed to MoSel *)

Module SepROMosel := SepLogicMosel SepROCore SepROCoreHempty SepROSetup.
Export SepROMosel.ProofMode.

(* ---------------------------------------------------------------------- *)
(** Proof mode definitions for SepRO *)

Import iris.proofmode.coq_tactics.

(** Proper instances for normally, RO and ROFrame. *)

Instance normally_mono : Proper ((⊢) ==> (⊢)) normally.
Proof. intros ???. by apply normally_himpl. Qed.
Instance normally_mono_flip : Proper (flip (⊢) ==> flip (⊢)) normally.
Proof. intros ???. by apply normally_himpl. Qed.
Instance normally_ne : NonExpansive normally.
Proof. by intros ??? ->%leibniz_equiv_iff. Qed.
Instance normally_proper : Proper ((≡) ==> (≡)) normally.
Proof. apply ne_proper, _. Qed.

Instance RO_mono : Proper ((⊢) ==> (⊢)) RO.
Proof. intros ???. by apply RO_covariant. Qed.
Instance RO_mono_flip : Proper (flip (⊢) ==> flip (⊢)) RO.
Proof. intros ???. by apply RO_covariant. Qed.
Instance RO_ne : NonExpansive RO.
Proof. by intros ??? ->%leibniz_equiv_iff. Qed.
Instance RO_proper : Proper ((≡) ==> (≡)) RO.
Proof. apply ne_proper, _. Qed.

Instance ROFrame_mono : Proper ((⊢) ==> (⊢) ==> (⊢)) ROFrame.
Proof. intros ??????. by apply ROFrame_himpl. Qed.
Instance ROFrame_mono_flip : Proper (flip (⊢) ==> flip (⊢) ==> flip (⊢)) ROFrame.
Proof. intros ??????. by apply ROFrame_himpl. Qed.
Instance ROFrame_ne : NonExpansive2 ROFrame.
Proof. by intros ??? ->%leibniz_equiv_iff. Qed.
Instance ROFrame_proper : Proper ((≡) ==> (≡) ==> (≡)) ROFrame.
Proof. apply ne_proper_2, _. Qed.

(** Persistent and Affine instances. *)

Instance normally_persistent P : Persistent P → Persistent (normally P).
Proof.
  rewrite /Persistent /bi_persistently /= /hpersistently /normally=>HP h Hh.
  split; [by apply (HP h), Hh|done].
Qed.
Instance normally_affine P : Affine P → Affine (normally P).
Proof. rewrite /Affine=>->. by rewrite normally_hempty. Qed.

Instance RO_persistent P : Persistent P → Persistent (RO P).
Proof.
  rewrite /Persistent /bi_persistently /= /hpersistently /RO=>HP h [h' [Hh' _]].
  exists heap_empty. split; [by eapply HP|split; [done|]].
  by rewrite Fmap.union_empty_l.
Qed.
Instance RO_affine P : Affine P → Affine (RO P).
Proof. rewrite /Affine=>->. by rewrite RO_empty. Qed.

(** Into/From instances for RO, normally and ROFrame. *)

Instance normally_from_pure (P : hprop) (φ : Prop) :
  FromPure true P φ → FromPure true (normally P) φ.
Proof.
  rewrite /FromPure /= /bi_affinely=><-. by rewrite normally_hand_l normally_hempty.
Qed.
Instance normally_into_pure (P : hprop) (φ : Prop) :
  IntoPure P φ → IntoPure (normally P) φ.
Proof. by rewrite /IntoPure normally_erase=>->. Qed.
Instance normally_from_sep (P Q R : hprop) :
  FromSep P Q R → FromSep (normally P) (normally Q) (normally R).
Proof. by rewrite /FromSep /bi_sep /= -normally_hstar =><-. Qed.
Instance normally_into_sep (P Q R : hprop) :
  IntoSep P Q R → IntoSep (normally P) (normally Q) (normally R).
Proof. by rewrite /IntoSep /bi_sep /= -normally_hstar =><-. Qed.
Instance normally_from_exist {A} (P : hprop) (Φ : A → hprop) :
  FromExist P Φ → FromExist (normally P) (λ x, normally (Φ x)).
Proof. by rewrite /FromExist /bi_exist /= -normally_hexists=><-. Qed.
Instance normally_into_exist {A} (P : hprop) (Φ : A → hprop) :
  IntoExist P Φ → IntoExist (normally P) (λ x, normally (Φ x)).
Proof. by rewrite /IntoExist /bi_exist /= -normally_hexists=><-. Qed.
Instance normally_from_forall {A} `{Inhabited A} (P : hprop) (Φ : A → hprop) :
  FromForall P Φ → FromForall (normally P) (λ x, normally (Φ x)).
Proof.
  assert (Inhab A). { split. by exists inhabitant. }
  by rewrite /FromForall /bi_forall /= -normally_hforall=> <-.
Qed.
Instance normally_into_forall {A} (P : hprop) (Φ : A → hprop) :
  IntoForall P Φ → IntoForall (normally P) (λ x, normally (Φ x)).
Proof.
  rewrite /IntoForall=>->. apply bi.forall_intro=>?. f_equiv.
  apply bi.forall_elim.
Qed.
Instance from_assumption_normally p (P Q : hprop) :
  FromAssumption p P Q →
  KnownLFromAssumption p (normally P) Q.
Proof.
  by rewrite /KnownLFromAssumption /FromAssumption normally_erase=><-.
Qed.

Instance RO_from_pure (a : bool) (P : hprop) (φ : Prop) :
  FromPure true P φ → FromPure true (RO P) φ.
Proof. rewrite /FromPure /= -hpure_pure =><-. by rewrite RO_pure. Qed.
Instance RO_into_pure (P : hprop) (φ : Prop) :
  IntoPure P φ → IntoPure (RO P) φ.
Proof.
  rewrite /IntoPure /bi_pure /= /hpure_abs=>->.
  rewrite RO_star RO_pure. f_equiv. auto.
Qed.
Instance RO_into_sep (P Q R : hprop) :
  IntoSep P Q R → IntoSep (RO P) (RO Q) (RO R).
Proof. by rewrite /IntoSep /bi_sep /= -RO_star =><-. Qed.
Instance RO_from_exist {A} (P : hprop) (Φ : A → hprop) :
  FromExist P Φ → FromExist (RO P) (λ x, RO (Φ x)).
Proof. by rewrite /FromExist /bi_exist /= -RO_hexists=><-. Qed.
Instance RO_into_exist {A} (P : hprop) (Φ : A → hprop) :
  IntoExist P Φ → IntoExist (RO P) (λ x, RO (Φ x)).
Proof. by rewrite /IntoExist /bi_exist /= -RO_hexists=><-. Qed.
Instance RO_into_forall {A} (P : hprop) (Φ : A → hprop) :
  IntoForall P Φ → IntoForall (RO P) (λ x, RO (Φ x)).
Proof.
  rewrite /IntoForall=>->. apply bi.forall_intro=>?. f_equiv.
  apply bi.forall_elim.
Qed.

(* We do not wnad this instance to be picked by iCombine => low priority. *)
Instance ROFrame_from_sep (P Q : hprop) : FromSep (ROFrame P Q) P Q | 1000.
Proof. apply ROFrame_intro. Qed.
Instance ROFrame_from_and (P Q : hprop) :
  FromAnd (P ∗ Q) P Q → FromAnd (ROFrame P Q) P Q | 1000.
Proof. rewrite /FromAnd=>->. apply ROFrame_intro. Qed.

(** Setup iModIntro to work with normally. *)

Lemma modality_normally_mixin :
  modality_mixin normally MIEnvId
                 (MIEnvTransform (λ P Q : hprop, TCAnd (TCEq P Q) (Normal P))).
Proof.
  split; simpl.
  - by intros P h [-> ?].
  - by intros P Q [-> ?]; apply normally_intro.
  - by rewrite normally_hempty.
  - by intros P Q ?; f_equiv.
  - by intros P Q; rewrite normally_hstar.
Qed.
Definition modality_normally :=
  Modality _ modality_normally_mixin.
Instance from_modal_normally P :
  FromModal modality_normally (normally P) (normally P) P.
Proof. by rewrite /FromModal. Qed.
(* Low priority to force annotation. *)
Instance from_modal_abs_normally P :
  FromModal modality_normally (normally P) (<absorb> normally P) (<absorb> P) | 100.
Proof. by rewrite /FromModal /= /bi_absorbingly normally_hstar normally_erase. Qed.

(** Frame instances *)

Class MakeNormally (P Q : hprop) :=
  make_normally : normally P ⊣⊢ Q.
Arguments MakeNormally _%I _%I.
Hint Mode MakeNormally - - : typeclass_instances.
Instance make_normally_default P : MakeNormally P (normally P) | 100.
Proof. by unfold MakeNormally. Qed.
Instance make_normally_normal P : Normal P → MakeNormally P P.
Proof. unfold MakeNormally. apply normally_Normal_eq. Qed.

Instance frame_normally (p : bool) (P Q R R' : hprop) :
  Normal P → Frame false P Q R → MakeNormally R R' →
  Frame p P (normally Q) R'.
Proof.
  rewrite /Frame /MakeNormally /= bi.intuitionistically_if_elim =>? <- <-.
  rewrite {1}(@normally_intro P) normally_hstar //.
Qed.

(* Contrarilly to other MakeXXX classes, [MakeROFRame] uses an
   entailment instead of an equivalence, because the converse
   direction is surprisingly difficult to prove (even though they
   should hold, that is, no information is lost). *)
Class MakeROFrame (P Q R : hprop) :=
  make_ro_frame : R ⊢ ROFrame P Q.
Arguments MakeROFrame _%I _%I _%I.
Hint Mode MakeROFrame - - - : typeclass_instances.
Class KnownLMakeROFrame (P Q R : hprop) :=
  knownl_make_ro_frame :> MakeROFrame P Q R.
Arguments KnownLMakeROFrame _%I _%I _%I.
Hint Mode KnownLMakeROFrame ! - - : typeclass_instances.
Class KnownRMakeROFrame (P Q R : hprop) :=
  knownr_make_ro_frame :> MakeROFrame P Q R.
Arguments KnownRMakeROFrame _%I _%I _%I.
Hint Mode KnownRMakeROFrame ! - - : typeclass_instances.

Instance make_roframe_default (P Q : hprop) :
  MakeROFrame P Q (ROFrame P Q) | 100.
Proof. by rewrite /MakeROFrame. Qed.
Instance make_roframe_emp_l (P : hprop) :
  KnownLMakeROFrame emp P P.
Proof. rewrite /KnownLMakeROFrame /MakeROFrame. iIntros "H". by iSplitR. Qed.
Instance make_roframe_emp_r (P : hprop) :
  KnownRMakeROFrame P emp P.
Proof. rewrite /KnownRMakeROFrame /MakeROFrame. iIntros "H". by iSplitL. Qed.

Typeclasses Opaque ROFrame.

(* There is no support, in MoSel, for resources that would be
   duplicable but not persistent (like RO which is not affine). We
   workaround this restriction with this [DupFrameRO] that repeatedly
   tries to frame an RO permission in a goal. This [DupFrameRO] type
   class is called when trying to frame in the LHS of an [ROFrame]. *)
Class DupFrameRO (R P Q : hprop) := dup_frame_ro : RO R ∗ Q ⊢ P.
Arguments DupFrameRO _%I _%I _%I.
Hint Mode DupFrameRO ! ! - : typeclass_instances.
Instance dup_frame_ro_go (R P Q Q' : hprop) :
  Frame false (RO R) P Q' →
  TCOr (DupFrameRO R Q' Q) (TCEq Q' Q) →
  DupFrameRO R P Q.
Proof.
  rewrite /Frame /DupFrameRO=><- [<- /=|-> //].
  rewrite assoc. f_equiv. apply RO_duplicatable.
Qed.

Class FrameOrWand (R P Q : hprop) := frame_or_wand : R ∗ Q ⊢ P.
Arguments FrameOrWand _%I _%I _%I.
Hint Mode FrameOrWand ! - - : typeclass_instances.
Instance frame_or_wand_frame (R P Q : hprop) :
  Frame false R P Q → FrameOrWand R P Q | 0.
Proof. done. Qed.
Instance frame_or_wand_normally_wand (R P : hprop) :
  Normal R →
  FrameOrWand R (normally P) (normally (R -∗ P)%I) | 1.
Proof.
  unfold FrameOrWand. iIntros (?) "[? H] !>". rewrite normally_erase.
  by iApply "H".
Qed.
(* The following default instance will not be used if P is of the form
   [normally X]. *)
Lemma frame_or_wand_wand (R P : hprop) :
  FrameOrWand R P (R -∗ P).
Proof. unfold FrameOrWand. iIntros "[? H]". by iApply "H". Qed.
Hint Extern 1 (FrameOrWand _ ?P _) =>
  lazymatch P with
  | normally _ => fail
  | _ => simple eapply @frame_or_wand_wand
  end
: typeclass_instances.

(* We try all these framing schemes, in this order: *)
(* 1st step: if we are tying to frame an RO, we first see if it is
   needed on the LHS. If so, then we also make it available on the
   RHS. *)
Instance frame_roframe_ro_lr p (R P P' Q Q' S : hprop) :
  DupFrameRO R P P' → FrameOrWand (RO R) Q Q' →
  MakeROFrame P' Q' S → Frame p (RO R) (ROFrame P Q) S | 1.
Proof.
  rewrite /Frame /DupFrameRO /FrameOrWand /MakeROFrame
          bi.intuitionistically_if_elim=><- <- ->.
  assert (HR:=@RO_duplicatable R). unfold duplicatable in HR. rewrite {1}HR.
  by rewrite /bi_sep /= hstar_assoc ROFrame_frame_r ROFrame_frame_l.
Qed.

(* 2nd step: we try to frame on the LHS. *)
Instance frame_roframe_l p (R P P' Q S : hprop) :
  Frame p R P P' → MakeROFrame P' Q S → Frame p R (ROFrame P Q) S | 2.
Proof. rewrite /Frame /MakeROFrame=><- ->. apply ROFrame_frame_l. Qed.

(* 3rd step: we try to convert to a RO permission. *)
Instance frame_roframe_lr p (R P P' Q Q' S : hprop) :
  Normal R → DupFrameRO R P P' → FrameOrWand R Q Q' → MakeROFrame P' Q' S →
  Frame p R (ROFrame P Q) S | 3.
Proof.
  rewrite /DupFrameRO /FrameOrWand /MakeROFrame /Frame
    bi.intuitionistically_if_elim =>? <- <- ->. apply ROFrame_frame_lr, _.
Qed.

(* 4th step: we frame on the RHS *)
Instance frame_roframe_r p (R P Q Q' S : hprop) :
  Frame p R Q Q' → MakeROFrame P Q' S → Frame p R (ROFrame P Q) S | 4.
Proof.
  rewrite /DupFrameRO /FrameOrWand /MakeROFrame /Frame=><- ->. apply ROFrame_frame_r.
Qed.

(** A bit of automation for ROFrame and normally. *)
Hint Extern 2 (envs_entails _ (ROFrame _ _)) => progress iFrame : iFrame.
Hint Extern 2 (envs_entails _ (<absorb> ROFrame _ _)) => progress iFrame : iFrame.

Hint Extern 0 (envs_entails _ (ROFrame \[_] _)) => iSplitR.
Hint Extern 0 (envs_entails _ (ROFrame _ \[_])) => iSplitL.
Hint Extern 0 (envs_entails _ (ROFrame \[] _)) => iSplitR.
Hint Extern 0 (envs_entails _ (ROFrame _ \[])) => iSplitL.
Hint Extern 0 (envs_entails _ (ROFrame emp%I _)) => iSplitR.
Hint Extern 0 (envs_entails _ (ROFrame _ emp%I)) => iSplitL.

Hint Extern 0 (envs_entails _ (<absorb> ROFrame \[_] _)) => iSplitR.
Hint Extern 0 (envs_entails _ (<absorb> ROFrame _ \[_])) => iSplitL.
Hint Extern 0 (envs_entails _ (<absorb> ROFrame \[] _)) => iSplitR.
Hint Extern 0 (envs_entails _ (<absorb> ROFrame _ \[])) => iSplitL.
Hint Extern 0 (envs_entails _ (<absorb> ROFrame emp%I _)) => iSplitR.
Hint Extern 0 (envs_entails _ (<absorb> ROFrame _ emp%I)) => iSplitL.

Hint Extern 0 (envs_entails _ (normally _)) => iModIntro (normally _).
Hint Extern 0 (envs_entails _ (<absorb> normally _)) => iModIntro (normally _)%I.

(** [PrepareHProp] stuff. *)

Instance prepare_hprop_normally (P Q : hprop) :
  PrepareHProp P Q → PrepareHProp (normally P) (normally Q).
Proof. by unfold PrepareHProp=>->. Qed.

Instance prepare_hprop_ROFrame (P P' Q Q' : hprop) :
  PrepareHProp P P' → PrepareHProp Q Q' →
  PrepareHProp (ROFrame P Q) (ROFrame P' Q').
Proof. by rewrite /PrepareHProp=>-> ->. Qed.

(** Tactics *)

Lemma triple_ramified_frame_read_only_absorb : forall t H Q H' Q',
  triple t H' Q' ->
  H ==> (<absorb> ROFrame H' (normally (Q' \--* Q)))%I ->
  triple t H Q.
Proof using.
  intros t H Q H' Q' Ht HH. eapply triple_conseq; first last; [done| |].
  eapply triple_htop_pre, triple_ramified_frame_read_only;
    [eassumption|iIntros "?"; iAssumption].
  iIntros "H". by iDestruct (HH with "H") as ">$".
Qed.

Lemma triple_ramified_frame_read_only_absorb_locked : forall t H Q H' Q',
  triple t H' Q' ->
  H ==> (<absorb> ROFrame H' (normally (locked Q' \--* Q)))%I ->
  triple t H Q.
Proof using. unlock. apply triple_ramified_frame_read_only_absorb. Qed.

Ltac ram_apply lem :=
  lazymatch goal with
  | |- triple _ _ ?Q =>
    (is_evar Q; eapply triple_ramified_frame_read_only_absorb_locked) ||
    eapply triple_ramified_frame_read_only_absorb
  end; [eapply lem|iPrepare].

Lemma triple_let_ramified_frame_read_only_locked : forall z t1 t2 H1 H Q1 Q Q',
  triple t1 H1 Q1 ->
  H ==> ROFrame H1 (locked Q1 \--* Q') ->
  (forall (X:val), triple (subst1 z X t2) (Q' X) Q) ->
  triple (trm_let z t1 t2) H Q.
Proof using. unlock. apply triple_let_ramified_frame_read_only. Qed.

Ltac ram_apply_let lem :=
  eapply triple_let_ramified_frame_read_only_locked; [eapply lem|iPrepare|].

(* ********************************************************************** *)

End ProofMode.
