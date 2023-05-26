(** * Meta-theory about Omni-big-step semantics *)

Set Implicit Arguments.

From TLC Require Import LibString LibList LibCore LibInt.

Section Omni_and_big_correction.

  Variable sTrm : Type.           (* source terms *)
  Variable sVal : Type.           (* source values *)
  Variable tTrm : Type.           (* target terms *)
  Variable tVal : Type.           (* target values *)

  Definition pc : Type := sVal -> Prop. (* postconditions *)

  Variable compile : sTrm -> tTrm.
  Variable comp_values : sVal -> tVal.
  Variable comp_values_inv : tVal -> sVal.

  Definition bigstep (trm : Type) (val : Type) :=
    trm -> val -> Prop : Type.

  Variable sOmniBig : bigstep sTrm pc.
  Variable sBig : bigstep sTrm sVal.
  Variable tBig : bigstep tTrm tVal.

  Definition sp (t : sTrm) := fun v => sBig t v.

  Definition terminates {trm : Type} {val : Type} {exec : bigstep trm val}
    (t : trm) : Prop :=
    exists (v : val), exec t v.


  Hypothesis forward : forall (t : sTrm) (P : pc),
      sOmniBig t P ->
      exists v, tBig (compile t) v /\ P (comp_values_inv v).

  Hypothesis omnibig_iff_terminates_and_correct : forall t P,
      sOmniBig t P <-> @terminates _ _ sBig t /\ forall v, sBig t v -> P v.

  Hypothesis tBig_deter : forall t v v',
      tBig t v -> tBig t v' -> v = v'.

  Lemma correction : forall (t : sTrm),
      @terminates _ _ sBig t ->
      @terminates _ _ tBig (compile t)
      /\ forall v, tBig (compile t) v ->
             exists P, sOmniBig t P /\ P (comp_values_inv v).
  Proof using forward omnibig_iff_terminates_and_correct tBig_deter.
    introv Hterm.
    specialize (@omnibig_iff_terminates_and_correct t (sp t)).
    simpl in omnibig_iff_terminates_and_correct.
    assert (sOmniBig t (sp t)). now apply omnibig_iff_terminates_and_correct.
    specialize (@forward t (sp t) H).
    destruct forward as (v'&HtBig&Hsp).
    split; try solve [firstorder].
    intros. exists (sp t). split; eauto.
    forwards* : tBig_deter (compile t) v v'. congruence.
  Qed.





End Omni_and_big_correction.
