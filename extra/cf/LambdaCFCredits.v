(**

This file formalizes characteristic formulae for
program verification using Separation Logic,
for the version that includes time credits.

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
From TLC Require Export LibFix.
From Sep Require Export SepBaseCredits.  (* MODIFIED FOR CREDITS *)
Open Scope heap_scope.

Implicit Types v w : val.

(* ********************************************************************** *)
(* * Type of a formula *)

(** A formula is a binary relation relating a precondition
    and a postcondition. *)

Definition formula := hprop -> (val -> hprop) -> Prop.

Global Instance Inhab_formula : Inhab formula.
Proof using. apply (Inhab_of_val (fun _ _ => True)). Qed.


(* ********************************************************************** *)
(* * Characteristic formula generator *)


(* ---------------------------------------------------------------------- *)
(* ** Definition of CF blocks *)

(** These auxiliary definitions give the characteristic formula
    associated with each term construct. *)

Definition cf_fail : formula := fun H Q =>
  False.

Definition cf_val (v:val) : formula := fun H Q =>
  (fun (x:val) => \[x = v] \* H)  ===> Q.

Definition cf_let (F1:formula) (F2of:val->formula) : formula := fun H Q =>
  exists Q1,
      F1 H Q1
   /\ (forall (X:val), (F2of X) (Q1 X) Q).

Definition cf_seq (F1 F2:formula) : formula :=
  cf_let F1 (fun _ => F2).

Definition cf_if_val (v:val) (F1 F2:formula) : formula := fun H Q =>
  exists (b:bool), (v = val_bool b)
                /\ (b = true -> F1 H Q)
                /\ (b = false -> F2 H Q).

Definition cf_if (F0 F1 F2 : formula) : formula :=
  cf_let F0 (fun v => local (cf_if_val v F1 F2)).

 (* MODIFIED FOR CREDITS *)
Definition Tick (F:formula) := fun H Q =>
  exists H', pay_one H H' /\ F H' Q.


(* ---------------------------------------------------------------------- *)
(* ** Definition of the CF generator *)

(** The CF generator is a recursive function, defined using the
    optimal fixed point combinator (from TLC). [cf_def] gives the
    function, and [cf] is then defined as the fixpoint of [cf_def].
    Subsequently, the fixed-point equation is established. *)

Definition cf_def cf (t:trm) :=
  match t with
  | trm_val v => local (cf_val v)
  | trm_var x => local (cf_fail) (* unbound variable *)
  | trm_fix f x t1 => local (cf_val (val_fix f x t1))
  | trm_if t0 t1 t2 => local (cf_if (cf t0) (cf t1) (cf t2))
  | trm_let x t1 t2 => local (cf_let (cf t1) (fun X => cf (subst1 x X t2)))
  | trm_app t1 t2 => local (triple t)
  | trm_while t1 t2 => local (cf_fail) (* unsupported *)
  | trm_for x t1 t2 t3 => local (cf_fail) (* unsupported *)
  end.

Definition cf := FixFun cf_def.

Ltac fixfun_auto := try solve [
  try fequals; auto; try apply fun_ext_1; auto ].

Lemma cf_unfold_iter : forall n t,
  cf t = func_iter n cf_def cf t.
Proof using.
  applys~ (FixFun_fix_iter (measure trm_size)). auto with wf.
  intros f1 f2 t IH. unfold cf_def.
  destruct t; fequals.
  { fequals~. }
  { fequals~. applys~ fun_ext_1. }
Qed.

Lemma cf_unfold : forall t,
  cf t = cf_def cf t.
Proof using. applys (cf_unfold_iter 1). Qed.


(* ********************************************************************** *)
(* * Soundness proof *)

(* ---------------------------------------------------------------------- *)
(* ** Soundness of the CF generator *)

Lemma is_local_cf : forall T,
  is_local (cf T).
Proof.
  intros. rewrite cf_unfold. destruct T; try apply is_local_local.
Qed.

Definition sound_for (t:trm) (F:formula) :=
  forall H Q, F H Q -> triple t H Q.

Lemma sound_for_local : forall t (F:formula),
  sound_for t F ->
  sound_for t (local F).
Proof using.
  unfold sound_for. introv SF. intros H Q M.
  rewrite is_local_triple. applys local_weaken M. applys SF.
Qed.

Lemma sound_for_cf : forall (t:trm),
  sound_for t (cf t).
Proof using.
  intros t. induction_wf: trm_size t.
  rewrite cf_unfold. destruct t; simpl;
   try (applys sound_for_local; intros H Q P).
  { unfolds in P. applys~ triple_val. hchanges~ P. }
  { false. }
  { unfolds in P. applys triple_fix. hchanges~ P. }
  { destruct P as (Q1&P1&P2). applys triple_if.
    { applys* IH. }
    { intros v. specializes P2 v. applys sound_for_local (rm P2).
      clears H Q Q1. intros H Q (b&P1'&P2'&P3'). inverts P1'.
      case_if; applys* IH. }
    { intros v N. specializes P2 v. applys local_false P2.
      intros H' Q' (b&E&S1&S2). subst. applys N. hnfs*. } }
  { destruct P as (Q1&P1&P2). applys triple_let Q1.
    { applys~ IH. }
    { intros X. applys~ IH. } }
  { applys P. }
  { false. }
  { false. }
Qed.

Theorem triple_of_cf : forall t H Q,
  cf t H Q ->
  triple t H Q.
Proof using. intros. applys* sound_for_cf. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Soundness of the CF of a function *)

Lemma triple_app_of_cf : forall F v (f:bind) x t H H' Q,
  F = val_fix f x t ->
  pay_one H H' ->
  cf (subst2 f F x v t) H' Q ->
  triple (F v) H Q.
Proof using.
  introv EF HP M. applys* triple_app_fix. applys* triple_of_cf.
Qed.


