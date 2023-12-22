Set Implicit Arguments.
From CFML Require Import LibSepGroup WPLibCredits Stdlib.
Open Scope cf_scope.
Open Scope record_scope.

From TLC Require Import LibListZ LibMap.

From CFML Require Import LibSepTLCbuffer.
Import IndexHints.

Require Import ListMisc.

Require Import Capacity_ml.


(* ******************************************************* *)
(** ** Definitions *)

Notation "'K'" := capacity.

Definition Wrap_up i := If i >= K then i - K else i.
Definition Wrap_down i := If i < 0 then i + K else i.

Definition IsFull A (c: list A) : Prop :=
	length c = K.

(* ******************************************************* *)
(** ** Lemma *)

Lemma capacity_spec :
  capacity > 0.
Proof. rewrite capacity_cf__; math. Qed.

Lemma NotFull_of_nil : forall A,
	~ IsFull (@nil A).
Proof.
	hint capacity_spec.
	intros. unfold IsFull. rew_list*.
Qed.


(* ******************************************************* *)
(** ** Hints *)

Hint Extern 1 (@le _ _ _ capacity) => hint capacity_spec; math.
Hint Extern 1 (@lt _ _ _ capacity) => hint capacity_spec; math.
Hint Extern 1 (@ge _ _ capacity _) => hint capacity_spec; math.
Hint Extern 1 (@gt _ _ capacity _) => hint capacity_spec; math.


(* ******************************************************* *)
(** ** Tactics *)

Tactic Notation "unwrap_up" :=
	unfold Wrap_up; repeat case_if*.
Tactic Notation "unwrap_up" "in" hyp(H) :=
	unfold Wrap_up in H; repeat case_if* in H.
Tactic Notation "unwrap_up" "in" "*" :=
	unfold Wrap_up in *; repeat case_if*.

Tactic Notation "unwrap_down" :=
	unfold Wrap_down; repeat case_if*.
Tactic Notation "unwrap_down" "in" hyp(H) :=
	unfold Wrap_down in H; repeat case_if* in H.
Tactic Notation "unwrap_down" "in" "*" :=
		unfold Wrap_down in *; repeat case_if*.


(* ******************************************************* *)
(** ** Specifications *)

Lemma wrap_up_spec : forall (n: int),
	SPEC (wrap_up n)
		PRE (\$1)
		POST (fun n' => \[n' = Wrap_up n]).
Proof.
	xcf. unfold Wrap_up.
	xif; intros C; case_if; xval*; xsimpl*.
Qed.

Hint Extern 1 (RegisterSpec wrap_up) => Provide wrap_up_spec.

Lemma wrap_down_spec : forall (n: int),
	SPEC (wrap_down n)
		PRE (\$1)
		POST (fun n' => \[n' = Wrap_down n]).
Proof.
	xcf. unfold Wrap_down.
	xif; intros C; case_if; xval*; xsimpl*.
Qed.

Hint Extern 1 (RegisterSpec wrap_down) => Provide wrap_down_spec.
