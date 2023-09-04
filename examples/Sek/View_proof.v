Set Implicit Arguments.
From CFML Require Import LibSepGroup WPLibCredits Stdlib.
From CFML Require Import WPRecord.
Open Scope cf_scope.
Open Scope record_scope.
(*From CFML Require Import WPDisplay WPRecord.
Open Scope cf_scope.
Open Scope record_scope.*)

From TLC Require Import LibListZ LibMap.

From CFML Require Import LibSepTLCbuffer.
Import IndexHints.

Require Import ListMisc.
Import LibListNotation.

From CFML Require Import Array_proof.
Import FarraySpec.

Require Import View_ml.


(* ******************************************************* *)
(** ** Definitions *)

Definition vswap (v: view_) : view_ :=
	match v with
	|	Front => Back
	|	Back => Front
	end.

Definition vcons A (v: view_) (x: A) (L: list A) : list A :=
	match v with
	|	Front => x :: L
	|	Back => L & x
	end.

Definition vapp A (v: view_) (L1 L2: list A) : list A :=
	match v with
	|	Front => L1 ++ L2
	|	Back => L2 ++ L1
	end.

Definition vindex (v: view_) : int :=
	match v with
	|	Front => 0
	|	Back => 1
	end.

Definition vsides A {IA: Inhab A} (v: view_) (L: list A) : A * A :=
	match v with
	|	Front => (L[0], L[1])
	|	Back => (L[1], L[0])
	end.

Definition vlist2 A (v: view_) (f b: A) : list A :=
	match v with
	|	Front => [f; b]
	|	Back => [b; f]
	end.


(* ******************************************************* *)
(** ** Lemmas *)

Lemma vswap_vswap : forall v,
	vswap (vswap v) = v.
Proof. intros. destruct v; auto. Qed.


Lemma length_vcons : forall A v (x: A) (L: list A),
	length (vcons v x L) = 1 + length L.
Proof. intros. destruct v; simpl; rew_list~. Qed.

Lemma length_vapp : forall A v (L1 L2: list A),
	length (vapp v L1 L2) = length L1 + length L2.
Proof. intros. destruct v; simpl; rew_list~. Qed.


Lemma vapp_assoc : forall A v (L1 L2 L3: list A),
	vapp v (vapp v L1 L2) L3 = vapp v L1 (vapp v L2 L3).
Proof. intros. destruct v; simpl; rew_list~. Qed.

Lemma vapp_swap : forall A v (L1 L2: list A),
	vapp (vswap v) L1 L2 = vapp v L2 L1.
Proof. intros. destruct v; auto. Qed.


Lemma vapp_vcons_l : forall A v (x: A) (L1 L2: list A),
	vapp v (vcons v x L1) L2 = vcons v x (vapp v L1 L2).
Proof. intros. destruct v; simpl; rew_list~. Qed.

Lemma vcons_vapp : forall A v (x: A) (L1 L2: list A),
	vcons v x (vapp v L1 L2) = vapp v (vcons v x L1) L2.
Proof. intros. destruct v; simpl; rew_list~. Qed.

Lemma vapp_vcons_r : forall A v (x: A) (L1 L2: list A),
	vapp v L1 (vcons v x L2) = vapp v (vcons (vswap v) x L1) L2.
Proof. intros. destruct v; simpl; rew_list~. Qed.

Lemma vapp_vcons_swap : forall A v (x: A) (L1 L2: list A),
	vapp v (vcons (vswap v) x L1) L2 = vapp v L1 (vcons v x L2).
Proof. intros. destruct v; simpl; rew_list~. Qed.


Lemma vapp_nil_l : forall A v (L: list A),
	vapp v nil L = L.
Proof. intros. destruct v; simpl; rew_list~. Qed.

Lemma vapp_nil_r : forall A v (L: list A),
	vapp v L nil = L.
Proof. intros. destruct v; simpl; rew_list~. Qed.

Lemma self_eq_vapp_l_inv : forall A v (L1 L2: list A),
	L1 = vapp v L1 L2 ->
	L2 = nil.
Proof.
	intros. destruct v; simpl in H.
	{ applys* self_eq_app_l_inv. }
	{ applys* self_eq_app_r_inv. }
Qed.

Lemma self_eq_app_r_inv : forall A v (L1 L2: list A),
	L2 = vapp v L1 L2 ->
	L1 = nil.
Proof. intros. rewrites <- vapp_swap in H. applys* self_eq_vapp_l_inv. Qed.


Lemma length_vlist2 : forall A (v: view_) (f b: A),
	length (vlist2 v f b) = 2.
Proof. unfold vlist2. intros A []; auto. Qed.

(* ******************************************************* *)
(** ** Hints *)

Hint Rewrite vswap_vswap : rew_list.
Hint Rewrite length_vcons length_vapp : rew_list.
Hint Rewrite vapp_assoc vapp_swap : rew_list.
Hint Rewrite vcons_vapp vapp_vcons_l vapp_vcons_swap vapp_vcons_r : rew_list.
Hint Rewrite vapp_nil_l vapp_nil_r self_eq_vapp_l_inv self_eq_app_r_inv : rew_list.
Hint Resolve length_vlist2.
Hint Rewrite length_vlist2 : rew_list.


(* ******************************************************* *)
(** ** Specifications *)

Lemma view_swap_spec : forall (v: view_),
	SPEC (view_swap v)
		PRE (\$1)
		POST \[= vswap v].
Proof. xcf. xpay. xmatch; xvals~. Qed.

Hint Extern 1 (RegisterSpec view_swap) => Provide view_swap_spec.

Lemma view_sides_spec_farray : forall A (IA: Inhab A) (v: view_) (a: array A) (L: list A),
	FArray L a ->
	length L >= 2 ->
	SPEC (view_sides v a)
		PRE (\$1)
		POST \[= vsides v L].
Proof.
   introv Ra HL. xcf. xpay. xmatch.
   { xapp*. autos~. xapp*. autos~. xvals~. }
   { xapp*. autos~. xapp*. autos~. xvals~. } (* TODO: auto_star does not include auto_tilde *)
Qed.

Hint Extern 1 (RegisterSpec view_sides) => Provide view_sides_spec_farray.
