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

  Variable Rval : sVal -> tVal -> Prop.

  (* Variable comp_values : sVal -> tVal. *)
  (* Variable comp_values_inv : tVal -> sVal. *)

  Definition bigstep (trm : Type) (val : Type) :=
    trm -> val -> Prop : Type.

  Variable sOmniBig : bigstep sTrm pc.
  Variable sBig : bigstep sTrm sVal.
  Variable tBig : bigstep tTrm tVal.

  Definition sp (t : sTrm) := fun v => sBig t v.

  Definition terminates {trm : Type} {val : Type} {exec : bigstep trm val}
    (t : trm) : Prop :=
    exists (v : val), exec t v.

  Definition lift_R (R : sVal -> tVal -> Prop) : ((sVal -> Prop) -> tVal -> Prop) :=
    fun P vt => exists vs, P vs /\ R vs vt.

  Hypothesis forward : forall (t : sTrm) (P : pc),
      sOmniBig t P ->
      @terminates _ _ tBig (compile t) /\
        (forall v, tBig (compile t) v -> lift_R Rval P v).


  Hypothesis omnibig_iff_terminates_and_correct : forall t P,
      sOmniBig t P <-> @terminates _ _ sBig t /\ forall v, sBig t v -> P v.

  (* Hypothesis tBig_deter : forall t v v', *)
  (*     tBig t v -> tBig t v' -> v = v'. *)

  Lemma correction : forall (t : sTrm),
      @terminates _ _ sBig t ->
      @terminates _ _ tBig (compile t)
      /\ forall vt, tBig (compile t) vt ->
              exists vs, Rval vs vt /\ sBig t vs.
      (* /\ forall v, tBig (compile t) v -> *)
      (*        exists P, sOmniBig t P /\ P (comp_values_inv v). *)
  Proof using forward omnibig_iff_terminates_and_correct.
    introv Hterm.
    specialize (@omnibig_iff_terminates_and_correct t (sp t)).
    (* simpl in omnibig_iff_terminates_and_correct. *)
    assert (sOmniBig t (sp t)). now apply omnibig_iff_terminates_and_correct.
    specialize (@forward t (sp t) H).
    destruct forward as (Htermcomp&Hcomps).
    unfold terminates in Htermcomp. destruct Htermcomp as (vt & Hvt).
    split. unfold terminates. exists vt. apply Hvt.
    intros. forwards * : Hcomps vt0 H0.
    unfold lift_R in H1.
    destruct H1 as (vs & Hvsinsp & HRv').
    exists vs. split. auto.
    apply Hvsinsp.
  Qed.




End Omni_and_big_correction.
