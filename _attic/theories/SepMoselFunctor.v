(** Requires:

   opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git
   opam update
   opam install coq-iris=branch.gen_proofmode.2018-05-29.0.9b14f90a

*)

(**
   This file contains an instantiation of the Generalized Proof Mode
   (extending Iris) for CFML.
*)

Set Implicit Arguments.
From TLC Require Export LibCore.
From Sep Require Export LibSepTLCbuffer LibSepFunctor.

From iris Require bi proofmode.tactics.
(* We undo the setup done by Stdpp. *)
Global Generalizable No Variables.
Global Obligation Tactic := Coq.Program.Tactics.program_simpl.


(* ********************************************************************** *)
(* * Extension to the core interface that needs to be exposed to MoSel *)

Module Type SepCoreHemptySig (SC : SepCore).
Import SC.

(** Implement a definition of heap_empty *)

Parameter heap_empty : heap.

(** Forces the definition of [hempty] to be the canonical one *)

Parameter hempty_eq :
  hempty = (fun h => h = heap_empty).

End SepCoreHemptySig.



(* ********************************************************************** *)
(* * Subset of the interface of SepLogicSetup that needs to be exposed to MoSel *)

Module Type SepSetupMoselSig (SC : SepCore).
Export SC.

Implicit Types h : heap.
Implicit Types H : hprop.
Implicit Types P : Prop.


(* ---------------------------------------------------------------------- *)
(* ** Definition of heap predicates *)

Definition hpure (P:Prop) : hprop :=
  hexists (fun (p:P) => hempty).

Definition hor (H1 H2 : hprop) : hprop :=
  hexists (fun (b:bool) => if b then H1 else H2).

Definition hand (H1 H2 : hprop) : hprop :=
  hforall (fun (b:bool) => if b then H1 else H2).

Definition hwand (H1 H2 : hprop) : hprop :=
  hexists (fun (H:hprop) => H \* (hpure (H \* H1 ==> H2))).

Definition qwand A (Q1 Q2:A->hprop) : hprop :=
  hforall (fun x => hwand (Q1 x) (Q2 x)).

Definition htop : hprop :=
  hexists (fun (H:hprop) => H).


(* ---------------------------------------------------------------------- *)
(* ** Some notation *)

Notation "'\exists' x1 , H" := (hexists (fun x1 => H))
  (at level 39, x1 ident, H at level 50) : heap_scope.
Notation "'\exists' x1 x2 , H" := (\exists x1, \exists x2, H)
  (at level 39, x1 ident, x2 ident, H at level 50) : heap_scope.
Notation "'\exists' x1 x2 x3 , H" := (\exists x1, \exists x2, \exists x3, H)
  (at level 39, x1 ident, x2 ident, x3 ident, H at level 50) : heap_scope.

Notation "\[ P ]" := (hpure P)
  (at level 0, P at level 99, format "\[ P ]") : heap_scope.

Notation "\Top" := (htop) : heap_scope.

Notation "H1 \-* H2" := (hwand H1 H2)
  (at level 43, right associativity) : heap_scope.

Notation "Q1 \--* Q2" := (qwand Q1 Q2)
  (at level 43) : heap_scope.


(* ---------------------------------------------------------------------- *)
(* ** Definition of [mklocal] *)

Notation "'~~' B" := (hprop->(B->hprop)->Prop)
  (at level 8, only parsing) : type_scope.

Definition mklocal B (F:~~B) : ~~B :=
  fun (H:hprop) (Q:B->hprop) =>
    H ==> \exists H1 H2 Q1,
       H1 \* H2 \* \[F H1 Q1 /\ Q1 \*+ H2 ===> Q \*+ \Top].

Definition local B (F:~~B) :=
  F = mklocal F.


(* ---------------------------------------------------------------------- *)
(* ** Properties *)

Parameter himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').

Parameter hstar_hpure : forall P H h,
  (\[P] \* H) h = (P /\ H h).

Parameter hpure_intro_hempty : forall P h,
  \[] h ->
  P ->
  \[P] h.

Parameter hpure_inv_hempty : forall P h,
  \[P] h ->
  P /\ \[] h.

Parameter htop_intro : forall h,
  \Top h.

Parameter himpl_htop_r : forall H H',
  H ==> H' ->
  H ==> H' \* \Top.

Global Opaque hempty hpure hstar hexists htop.


(* ---------------------------------------------------------------------- *)
(* ** Tactics *)

Ltac xpull_xtpull_iris_hook := idtac.

Ltac xlocal_core := idtac.

Parameter mklocal_ramified_frame : forall B (Q1:B->hprop) H1 F H Q,
  local F ->
  F H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  F H Q.

End SepSetupMoselSig.




(* ********************************************************************** *)
(* * Proof Mode *)


Module SepLogicMosel (SC : SepCore) (SCH: SepCoreHemptySig SC) (SS : SepSetupMoselSig SC).
Export SS SCH.


(* ********************************************************************** *)
(* * Instantiating Iris Proof Mode *)

Module ProofModeInstantiate.

Import iris.bi.bi iris.proofmode.coq_tactics.
Export iris.proofmode.tactics.

Canonical Structure hpropC := leibnizC hprop.

Definition hpersistently (H : hprop) : hprop :=
  fun _ => H heap_empty.

(* Proofmode's hpure has to be absorbing. So we redefine it here, and
   we add later by hand the necessary infrastructure for CFML's hpure. *)
Definition hpure_abs (φ : Prop) : hprop := \[φ] \* \Top.

Program Canonical Structure hpropI : bi :=
  Bi hprop _ _ (@himpl _) hempty hpure_abs hand hor
     (@pred_impl _) hforall hexists hstar hwand hpersistently _ _.
Next Obligation. apply discrete_ofe_mixin, _. Qed.
Next Obligation.
  Transparent hempty.
  split; [split|..].
  - intros ??; apply himpl_refl.
  - intros ???; apply himpl_trans.
  - intros. rewrite leibniz_equiv_iff. split=>?.
    + subst. auto.
    + apply himpl_antisym; naive_solver.
  - by intros ??? ->%LibAxioms.prop_ext.
  - solve_proper.
  - solve_proper.
  - solve_proper.
  - by intros ???? ->%fun_ext_1.
  - by intros ???? ->%fun_ext_1.
  - solve_proper.
  - solve_proper.
  - solve_proper.
  - intros ?????. rewrite /hpure_abs hstar_hpure.
    split; [done|apply htop_intro].
  - intros ??. rewrite /hpure_abs=>Hφ h Hh. apply Hφ.
    + rewrite /hpure_abs hstar_hpure in Hh. apply Hh.
    + rewrite hstar_hpure. split; [done|]. apply htop_intro.
  - rewrite /hpure_abs=>??? H. rewrite hstar_hpure.
    split; [|by apply htop_intro]. intros x. specialize (H x).
    rewrite hstar_hpure in H. apply H.
  - by intros ??? [? _].
  - by intros ??? [_ ?].
  - intros P Q R HQ HR ?. by split; [apply HQ|apply HR].
  - by left.
  - by right.
  - intros P Q R HP HQ ? [|]. by apply HP. by apply HQ.
  - intros P Q R H ???. apply H. by split.
  - intros P Q R H ? []. by apply H.
  - intros A P Ψ H ???. by apply H.
  - intros A Ψ a ? H. apply H.
  - by eexists.
  - intros A Φ Q H ? []. by eapply H.
  - intros ??????. eapply himpl_trans. by apply himpl_frame_r.
    rewrite (hstar_comm P Q') (hstar_comm Q Q'). by apply himpl_frame_r.
  - intros. by rewrite hstar_hempty_l.
  - intros. by rewrite hstar_hempty_l.
  - intros. by rewrite hstar_comm.
  - intros. by rewrite hstar_assoc.
  - intros P Q R H ??. exists P. rewrite hstar_comm hstar_hpure. auto.
  - intros P Q R H. eapply himpl_trans.
    { rewrite hstar_comm. by apply himpl_frame_r. }
    unfold hwand. rewrite hstar_comm hstar_hexists=>h [F HF].
    rewrite (hstar_comm F) hstar_assoc hstar_hpure in HF. destruct HF as [HR HF].
    by apply HR.
  - intros P Q H h. apply H.
  - auto.
  - unfold hpersistently. rewrite hempty_eq. intros h _. auto.
  - auto.
  - auto.
  - intros P Q h. replace (hpersistently P) with (\[P heap_empty] \* \Top).
    { rewrite hstar_assoc !hstar_hpure=>-[? _]. auto using htop_intro. }
    extens=>h'. rewrite hstar_hpure /hpersistently. naive_solver auto using htop_intro.
  - intros P Q h [HP HQ]. rewrite -(hstar_hempty_l Q) in HQ.
    eapply himpl_frame_l, HQ. rewrite hempty_eq. intros ? ->. apply HP.
Qed.

Lemma hpure_pure φ : \[φ] = bi_affinely ⌜φ⌝.
Proof.
  extens=>h. split.
  - split; [by eapply hpure_inv_hempty|by apply (himpl_htop_r (H:=\[φ]))].
  - intros [? Hφ]. apply hpure_intro_hempty; [done|].
    change ((\[φ] \* \Top%I) h) in Hφ. rewrite hstar_hpure in Hφ. naive_solver.
Qed.
Lemma htop_True : \Top = True%I.
Proof.
  extens=>h. split=>?.
  - rewrite /bi_pure /= /hpure_abs hstar_hpure. auto.
  - apply htop_intro.
Qed.
Opaque hpure_abs.

Ltac unfold_proofmode :=
  change (@bi_and hpropI) with hand;
  change (@bi_or hpropI) with hor;
  change (@bi_emp hpropI) with hempty;
  change (@bi_forall hpropI) with hforall;
  change (@bi_exist hpropI) with hexists;
  change (@bi_sep hpropI) with hstar;
  change (@bi_wand hpropI) with hwand.

End ProofModeInstantiate.



(* ********************************************************************** *)
(* * Tactics for better integration of Iris Proof Mode with CFML Iris *)

Module ProofMode.

Export ProofModeInstantiate.
Import iris.proofmode.coq_tactics. (* TODO: should it be Export? *)

(* We need to repeat all these hints appearing in proofmode/tactics.v,
   so that they state something about CFML connectives. [Hint Extern]
   patterns are not matched modulo canonical structure unification. *)

Hint Extern 0 (_ ==> _) => iStartProof.
Hint Extern 0 (envs_entails _ (hpure _)) => iPureIntro.
Hint Extern 0 (envs_entails _ (hempty)) => iEmpIntro.
Hint Extern 0 (envs_entails _ (hforall _)) => iIntros (?).
Hint Extern 0 (envs_entails _ (hwand _ _)) => iIntros "?".

Hint Extern 1 (envs_entails _ (hand _ _)) => iSplit.
Hint Extern 1 (envs_entails _ (hstar _ _)) => iSplit.
Hint Extern 1 (envs_entails _ (hexists _)) => iExists _.
Hint Extern 1 (envs_entails _ (hor _ _)) => iLeft.
Hint Extern 1 (envs_entails _ (hor _ _)) => iRight.

Hint Extern 2 (envs_entails _ (hstar _ _)) => progress iFrame : iFrame.

(* Specific instances for CFML. *)

Hint Extern 3 (envs_entails _ ?P) => is_evar P; iAccu.
Hint Extern 3 (envs_entails _ (?P _)) => is_evar P; iAccu.

Hint Extern 0 (envs_entails _ (\[_] \* _)) => iSplitR.
Hint Extern 0 (envs_entails _ (\[_] ∗ _)) => iSplitR.
Hint Extern 0 (envs_entails _ (_ \* \[_])) => iSplitL.
Hint Extern 0 (envs_entails _ (_ ∗ \[_])) => iSplitL.

Hint Extern 0 (envs_entails _ (\[] \* _)) => iSplitR.
Hint Extern 0 (envs_entails _ (\[] ∗ _)) => iSplitR.
Hint Extern 0 (envs_entails _ (_ \* \[])) => iSplitL.
Hint Extern 0 (envs_entails _ (_ ∗ \[])) => iSplitL.

(** * Specific Proofmode instances about hpure and htop. *)

Global Instance htop_absorbing : Absorbing \Top.
Proof. intros ??. apply htop_intro. Qed.
Global Instance htop_persistent : Persistent \Top.
Proof. intros ??. apply htop_intro. Qed.

Global Instance htop_into_pure : IntoPure \Top True.
Proof. unfold IntoPure. auto. Qed.
Global Instance htrop_from_pure a : FromPure a \Top True.
Proof. intros ??. apply htop_intro. Qed.

Global Instance hpure_affine φ : Affine \[φ].
Proof. rewrite hpure_pure. apply _. Qed.
Global Instance hpure_persistent φ : Persistent \[φ].
Proof. rewrite hpure_pure. apply _. Qed.

Global Instance hpure_into_pure φ : IntoPure \[φ] φ.
Proof. rewrite hpure_pure /IntoPure. by iDestruct 1 as "%". Qed.
Global Instance hpure_from_pure φ : FromPure true \[φ] φ.
Proof. by rewrite hpure_pure /FromPure /= /bi_affinely stdpp.base.comm. Qed.

Global Instance from_and_hpure φ ψ : FromAnd \[φ ∧ ψ] \[φ] \[ψ].
Proof. rewrite /FromAnd. auto. Qed.
Global Instance from_sep_hpure φ ψ : FromSep \[φ ∧ ψ] \[φ] \[ψ].
Proof. rewrite /FromSep. auto. Qed.
Global Instance into_and_hpure (p : bool) φ ψ : IntoAnd p \[φ ∧ ψ] \[φ] \[ψ].
Proof. rewrite /IntoAnd. f_equiv. auto. Qed.
Global Instance into_sep_hpure φ ψ : IntoSep \[φ ∧ ψ] \[φ] \[ψ].
Proof. rewrite /IntoSep. auto. Qed.
Global Instance from_or_hpure φ ψ : FromOr \[φ ∨ ψ] \[φ] \[ψ].
Proof. rewrite /FromOr. auto. Qed.
Global Instance into_or_hpure φ ψ : IntoOr \[φ ∨ ψ] \[φ] \[ψ].
Proof. rewrite /IntoOr. auto. Qed.
Global Instance from_exist_hpure {A} (φ : A → Prop) :
  FromExist \[∃ x : A, φ x] (λ a : A, \[φ a]).
Proof. rewrite /FromExist. auto. Qed.
Global Instance into_exist_hpure {A} (φ : A → Prop) :
  IntoExist \[∃ x : A, φ x] (λ a : A, \[φ a]).
Proof. rewrite /IntoExist. auto. Qed.
Global Instance from_forall_hpure {A : Type} `{Inhabited A} (φ : A → Prop) :
  FromForall \[∀ a : A, φ a] (λ a : A, \[φ a]).
Proof. rewrite /FromForall. auto. Qed.
Global Instance frame_here_hpure p (φ : Prop) Q :
   FromPure true Q φ → Frame p \[φ] Q emp.
Proof.
  rewrite /FromPure /Frame=><- /=. destruct p=>/=; iIntros "[% _] !%"; auto.
Qed.

(** [PrepareHProp] / [iPrepare] tactic. *)

Class PrepareHProp (P Q : hprop) := prepare_hprop_eq : P = Q.
Hint Mode PrepareHProp ! - : typeclass_instances.
Arguments PrepareHProp _%I _%I.

Instance prepare_hprop_default (P : hprop) : PrepareHProp P P | 100.
Proof. done. Qed.

(* In the case [P ∗ Q] is under a definition, we do not wnat ot apply
   this instance, because it would unfold the definition. Hence, we
   use [Hint Extern] that will apply only if the star match without a
   definition. *)
Lemma prepare_hprop_curry (P Q R S : hprop) :
  PrepareHProp (P -∗ Q -∗ R) S → PrepareHProp (P ∗ Q -∗ R) S.
Proof.
  rewrite /PrepareHProp=><-. apply leibniz_equiv. iSplit.
  - iIntros "H ? ?"; iApply "H"; iFrame.
  - iIntros "H [??]". by iApply ("H" with "[$]").
Qed.
Hint Extern 1 (PrepareHProp ((_ ∗ _) -∗ _) _) =>
  simple eapply prepare_hprop_curry : typeclass_instances.
Hint Extern 1 (PrepareHProp ((_ \* _) -∗ _) _) =>
  simple eapply prepare_hprop_curry : typeclass_instances.
Hint Extern 1 (PrepareHProp ((_ ∗ _)%I \-* _) _) =>
  simple eapply prepare_hprop_curry : typeclass_instances.
Hint Extern 1 (PrepareHProp ((_ \* _) \-* _) _) =>
  simple eapply prepare_hprop_curry : typeclass_instances.

Instance prepare_hprop_hempty_wand (P Q : hprop) :
  PrepareHProp P Q → PrepareHProp (\[] -∗ P) Q.
Proof.
  rewrite /PrepareHProp=><-. apply leibniz_equiv. iSplit; [|by iIntros "$ _"].
  iIntros "H". by iApply "H".
Qed.
Instance prepare_hprop_next (P Q R : hprop) :
  PrepareHProp P Q → PrepareHProp (R -∗ P) (R -∗ Q) | 10.
Proof. by rewrite /PrepareHProp=> ->. Qed.

Instance prepare_hprop_forall {A} (Φ Ψ : A → hprop) :
  (∀ x, PrepareHProp (Φ x) (Ψ x)) → PrepareHProp (∀ x, Φ x) (∀ x, Ψ x).
Proof. rewrite /PrepareHProp=> H. by setoid_rewrite H. Qed.

Instance prepare_hprop_hstar (P P' Q Q' : hprop) :
  PrepareHProp P P' → PrepareHProp Q Q' → PrepareHProp (P ∗ Q) (P' ∗ Q') | 10.
Proof. by rewrite /PrepareHProp=>-> ->. Qed.

Lemma prepare_hprop_hemp_hstar (P Q : hprop) :
  PrepareHProp P Q → PrepareHProp (\[] \* P) Q.
Proof. rewrite /PrepareHProp=>->. by rewrite left_id. Qed.
Hint Extern 1 (PrepareHProp (\[] \* _) _) =>
  simple apply prepare_hprop_hemp_hstar : typeclass_instances.
Hint Extern 1 (PrepareHProp (\[] ∗ _) _) =>
  simple apply prepare_hprop_hemp_hstar : typeclass_instances.
Hint Extern 1 (PrepareHProp (emp%I \* _)%I _) =>
  simple apply prepare_hprop_hemp_hstar : typeclass_instances.
Hint Extern 1 (PrepareHProp (emp ∗ _) _) =>
  simple apply prepare_hprop_hemp_hstar : typeclass_instances.

Lemma prepare_hprop_hstar_hemp (P Q : hprop) :
  PrepareHProp P Q → PrepareHProp (P \* \[]) Q.
Proof. rewrite /PrepareHProp=>->. by rewrite right_id. Qed.
Hint Extern 1 (PrepareHProp (_ \* \[]) _) =>
  simple apply prepare_hprop_hstar_hemp : typeclass_instances.
Hint Extern 1 (PrepareHProp (_ ∗ \[]) _) =>
  simple apply prepare_hprop_hstar_hemp : typeclass_instances.
Hint Extern 1 (PrepareHProp (_ \* emp%I)%I _) =>
  simple apply prepare_hprop_hstar_hemp : typeclass_instances.
Hint Extern 1 (PrepareHProp (_ ∗ emp) _) =>
  simple apply prepare_hprop_hstar_hemp : typeclass_instances.

Instance prepare_hprop_absorbingly (P Q : hprop) :
  PrepareHProp P Q → PrepareHProp (<absorb> P) (<absorb> Q).
Proof. by unfold PrepareHProp=>->. Qed.


Lemma tac_prepare Δ (P Q : hprop) :
  PrepareHProp P Q →
  envs_entails Δ Q →
  envs_entails Δ P.
Proof. by rewrite /PrepareHProp=>->. Qed.

Ltac iPrepare :=
  iStartProof;
  eapply tac_prepare; [apply _|cbv beta].



(* ProofMode's [iIntros] tend to move pure facts in Coq's context.
   While, in general, this is desirable, this is not what we want
   after having applied [mklocal_ramified_frame] because we would loose
   pure facts that will not be unified in [Q] when [Q] is an evar. As
   a result, we use a specific version of this lemma where Q1 is
   locked, and hence pure facts cannot escape.

   This specific version is only used when the postcondition is
   indeed an evar. *)
Lemma mklocal_ramified_frame_locked {B} : forall (Q1 : B → hprop) H1 F H Q,
  local F ->
  F H1 Q1 ->
  H ==> H1 \* (locked Q1 \--* Q) ->
  F H Q.
Proof using. unlock. apply mklocal_ramified_frame. Qed.

Ltac ram_apply lem :=
  lazymatch goal with
  | |- ?F _ ?Q =>
    (is_evar Q; eapply mklocal_ramified_frame_locked) ||
    eapply mklocal_ramified_frame
  end; [xlocal_core tt|eapply lem|iPrepare].


(** Fix for xpull/xtpull to unfold proof mode functions *)

Ltac xpull_xtpull_iris_hook tt ::=
  ProofModeInstantiate.unfold_proofmode.


End ProofMode.


End SepLogicMosel.
