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

Require Import View_ml.
Require Import Owner_ml.
Require Import Weighted_ml.
Require Import SWChunk_ml.
Require Import Capacity_proof.
Require Import View_proof.
Require Import SWChunk_proof.




Lemma hfold_list2_vcons :
  forall [A B : Type] (v: view_) (f : A -> B -> hprop) (x1 : A) 
	(x2 : B) (l1 : list A) (l2 : list B),
  hfold_list2 f (vcons v x1 l1) (vcons v x2 l2) = f x1 x2 \* hfold_list2 f l1 l2.
Admitted.


(* ******************************************************* *)
(** ** Representation predicates *)

(* Cf MList_proof.v *)
Notation "'Whtype' A a" := (htype (weighted_ A) (weighted_ a)) (at level 69, A at level 0).

Definition SWChunkOf_MaybeOwned a A {IA: Inhab a} {EA: Enc A} (R: Whtype A a)
	(M: SWChunkMem a) (oo: option owner_) (L: Wlist A) (s: swchunk_ a) : hprop :=
	\exists l,
		s ~> SWChunk_MaybeOwned M oo l \*
		hfold_list2 R L l.

Lemma SWChunkOf_MaybeOwned_eq : forall a (s: swchunk_ a) A (IA: Inhab a) (EA: Enc A) (R: Whtype A a)
	(M: SWChunkMem a) (oo: option owner_) (L: Wlist A),
	s ~> SWChunkOf_MaybeOwned R M oo L = 
		\exists l,
			s ~> SWChunk_MaybeOwned M oo l \*
			hfold_list2 R L l.
Proof using. auto. Qed.

(* ******************************************************* *)
(** ** Specifications *)

Lemma swchunk_default_spec_of : forall a A (IA: Inhab a) (EA: Enc A) (R: Whtype A a)
	(M: SWChunkMem a) (oo: option owner_) (L: Wlist A) (c: swchunk_ a),
	SPEC (swchunk_default c)
		INV (c ~> SWChunkOf_MaybeOwned R M oo L)
		POST (fun (d: A) => \[]).
Admitted.

Hint Extern 1 (RegisterSpec swchunk_default) => Provide swchunk_default_spec_of.

Lemma swchunk_create_spec_of : forall a A (IA: Inhab a) (EA: Enc A) (R: Whtype A a)
	(M: SWChunkMem a) (d: a) (oo: option owner_),
	SPEC (swchunk_create d oo)
		MONO M
		PRE \[]
		POST (fun M' c => c ~> SWChunkOf_MaybeOwned R M' oo nil).
Admitted.

Hint Extern 1 (RegisterSpec swchunk_create) => Provide swchunk_create_spec_of.

Lemma swchunk_is_full_spec_of : forall a A (IA: Inhab a) (EA: Enc A) (R: Whtype A a)
	(M: SWChunkMem a) (oo: option owner_) (L: Wlist A) (c: swchunk_ a),
	SPEC (swchunk_is_full c)
		INV (c ~> SWChunkOf_MaybeOwned R M oo L)
		POST \[= IsFull L].
Proof using. skip. Qed.

Hint Extern 1 (RegisterSpec swchunk_is_full) => Provide swchunk_is_full_spec_of.

Lemma swchunk_push_spec_of : forall a A (IA: Inhab a) (EA: Enc A) (R: Whtype A a)
	(v: view_) (M: SWChunkMem a) (oo: option owner_) (L: Wlist A) (c: swchunk_ a) (X: weighted_ A) (x: weighted_ a),
	SPEC (swchunk_push v c x)
	MONO M
	PRE (c ~> SWChunkOf_MaybeOwned R M oo L \* R X x)
	POST (fun M' c' => c' ~> SWChunkOf_MaybeOwned R M' oo (vcons v X L)).
Proof using.
  xtriple. xchange SWChunkOf_MaybeOwned_eq ;=> l. xapp swchunk_push_spec ;=> c' M' HE.
	xchange <- hfold_list2_vcons v. xchanges~ <- SWChunkOf_MaybeOwned_eq. 
Qed.

Hint Extern 1 (RegisterSpec swchunk_push) => Provide swchunk_push_spec_of.
