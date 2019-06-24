
Set Implicit Arguments.
From Sep Require Import SepBase SepMosel.


Module ProofMode.


(* ********************************************************************** *)
(* * Exposing [heap_empty] to MoSel *)

Module SepBasicCoreHempty <: SepCoreHemptySig SepBasicCore.

Definition heap_empty := heap_empty.

Lemma hempty_eq : hempty = (fun h => h = heap_empty).
Proof using. auto. Qed.

End SepBasicCoreHempty.


(* ********************************************************************** *)
(* * Subset of the interface of SepLogicSetup that needs to be exposed to MoSel *)

Module SepBasicMosel := SepLogicMosel SepBasicCore SepBasicCoreHempty SepBasicSetup.
Export SepBasicMosel.ProofMode.

Definition wp (t:trm) (Q:val->hprop) : hprop :=
  \exists H, H \* \[triple t H Q].

Lemma wp_equiv : forall t H Q,
  triple t H Q <-> (H ==> wp t Q).
Proof using.
  intros. unfold wp. iff M.
  { xsimpl. rew_heap~. }
  { applys~ triple_conseq (rm M). xtpull~. }
Qed.

Instance triple_as_valid t H Q : AsEmpValid (triple t H Q) (H -∗ wp t Q).
Proof. rewrite /AsEmpValid wp_equiv. apply as_emp_valid. Qed.

Instance frame_wp p t R Φ Ψ :
  (∀ v, Frame p R (Φ v) (Ψ v)) → Frame p R (wp t Φ) (wp t Ψ).
Proof.
  rewrite /Frame /wp=> HR. iIntros "[HR H]". iDestruct "H" as (H) "[HH %]".
  iExists (H ∗ □?p R)%I. iFrame. iPureIntro. eapply triple_frame_consequence=>//.
  iIntros (?) "[??]". iApply HR. iFrame.
Qed.

Instance wp_absorbing t Q : Absorbing (wp t Q).
Proof.
  apply wp_equiv. rewrite /bi_absorbingly -htop_True comm.
  apply triple_htop_pre. iIntros "$".
Qed.

(* ********************************************************************** *)

End ProofMode.
