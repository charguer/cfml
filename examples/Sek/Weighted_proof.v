Set Implicit Arguments.
From CFML Require Import LibSepGroup WPLib Stdlib.
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

Require Import Weighted_ml.



(* ******************************************************* *)
(** ** Definitions *)

Notation "'listW' A" := (list (weighted_ A)) (at level 69).
Notation "'Wlist' A" := (weighted_ (listW A)) (at level 69).

Definition list_of_listW A (LW: listW A) : list A :=
	LibList.map unweighted' LW.

Definition Wlist_of_listW A (L: listW A) : Wlist A :=
	weighted_make__ L (list_sum weight' L).


(* ******************************************************* *)
(** ** Lemmas *)

Instance weighted_inhab A : Inhab A -> Inhab (weighted_ A).
Proof using. intros. apply (Inhab_of_val (weighted_make__ arbitrary 0)). Qed.

Hint Resolve weighted_inhab.

Lemma Wlist_of_listW_eq : forall A (L: listW A),
	Wlist_of_listW L = weighted_make__ L (list_sum weight' L).
Proof. auto. Qed.

(* ******************************************************* *)
(** ** Spec *)

Lemma mk_weighted_spec : forall A (IA: Inhab A) (EA: Enc A) (uw: A) (w: int),
	SPEC (mk_weighted uw w)
		PRE \[]
		POST \[= weighted_make__ uw w].
Proof. xcf. xpay_skip. xvals~. Qed.

Hint Extern 1 (RegisterSpec mk_weighted) => Provide mk_weighted_spec.

Lemma dummy_weighted_spec : forall A (IA: Inhab A) (EA: Enc A) (uw: A),
	SPEC (dummy_weighted uw)
		PRE \[]
		POST \[= weighted_make__ uw 0].
Proof. xcf. xpay_skip. xapp~. xsimpl~. Qed.

Hint Extern 1 (RegisterSpec dummy_weighted) => Provide dummy_weighted_spec.

Lemma unweighted_spec : forall A (IA: Inhab A) (EA: Enc A) (x: weighted_ A),
	SPEC (unweighted x)
		PRE \[]
		POST \[= unweighted' x].
Proof. xcf. xpay_skip. xvals~. Qed.

Hint Extern 1 (RegisterSpec unweighted) => Provide unweighted_spec.

Lemma weight_spec : forall A (IA: Inhab A) (EA: Enc A) (x: weighted_ A),
	SPEC (weight x)
		PRE \[]
		POST \[= weight' x].
Proof. xcf~. xpay_skip. xvals~. Qed.

Hint Extern 1 (RegisterSpec weight) => Provide weight_spec.
