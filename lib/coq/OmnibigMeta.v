(** * Meta-theory about Omni-big-step semantics *)

Set Implicit Arguments.

From TLC Require Import LibString LibList LibCore LibInt.

Section Omni_big_correction.

  Variable sTrm : Type.           (* source terms *)
  Variable sVal : Type.           (* source values *)
  Variable tTrm : Type.           (* target terms *)
  Variable tVal : Type.           (* target values *)

  Definition s_pc : Type := sVal -> Prop. (* postconditions *)
  Definition t_pc : Type := tVal -> Prop.


  Definition bigstep (trm : Type) (val : Type) :=
    trm -> val -> Prop : Type.

  Variable sOmniBig : bigstep sTrm s_pc.
  Variable sBig : bigstep sTrm sVal.
  Variable tOmniBig : bigstep tTrm t_pc.
  Variable tBig : bigstep tTrm tVal.

  Definition s_sp (t : sTrm) := fun v => sBig t v.
  Definition t_sp (t : tTrm) := fun v => tBig t v.

  Definition terminates {trm : Type} {val : Type} {exec : bigstep trm val}
    (t : trm) : Prop :=
    exists (v : val), exec t v.


  Definition post_not_empty : Prop :=
    forall (s : sTrm) (Q : s_pc),
      sOmniBig s Q ->
      exists v, Q v.

  Variable compile : sTrm -> tTrm.

  Variable R : sTrm -> tTrm -> Prop.

  Variable Rval : sVal -> tVal -> Prop.

  Definition lift_R (R : sVal -> tVal -> Prop)
    (Qs : s_pc) (Qt : t_pc) : Prop :=
    forall vt, Qt vt -> exists vs, Qs vs /\ R vs vt.


  Hypothesis forward : forall (src_t : sTrm) (tgt_t : tTrm) (Qs : s_pc),
      R src_t tgt_t ->
      sOmniBig src_t Qs ->
      exists Qt, tOmniBig tgt_t Qt /\ lift_R Rval Qs Qt.



  Hypothesis s_omnibig_iff_terminates_and_correct : forall t P,
      sOmniBig t P <-> @terminates _ _ sBig t /\ forall v, sBig t v -> P v.

  Hypothesis t_omnibig_iff_terminates_and_correct : forall t P,
      tOmniBig t P <-> @terminates _ _ tBig t /\ forall v, tBig t v -> P v.


  Lemma correction : forall (t_s : sTrm) (t_t : tTrm),
      R t_s t_t ->
      @terminates _ _ sBig t_s ->
      @terminates _ _ tBig t_t
      /\ forall vt, tBig t_t vt ->
              exists vs, Rval vs vt /\ sBig t_s vs.
  Proof using forward s_omnibig_iff_terminates_and_correct
    t_omnibig_iff_terminates_and_correct.
    introv HR Hterminates.
    setoid_rewrite s_omnibig_iff_terminates_and_correct in forward.
    setoid_rewrite t_omnibig_iff_terminates_and_correct in forward.
    forwards *Hforward: forward t_s t_t (s_sp t_s).
    firstorder.
  Qed.

End Omni_big_correction.
