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

Require Import Owner_ml.
Require Import View_ml.
Require Import Weighted_ml.
Require Import SChunk_ml.
Require Import SWChunk_ml.
Require Import Capacity_proof.
Require Import View_proof.
Require Import Weighted_proof.
Require Import SChunk_proof.



(* ******************************************************* *)
(** ** Representation predicates *)

Definition list_sum A (W: A -> int) (L: list A) : int :=
  LibList.fold_left (fun x acc => acc + W x) 0 L.

Notation "'SWChunkMem' A" := (SChunkMem (weighted_ A)) (at level 69).
Notation "'Wlist' A" := (list (weighted_ A)) (at level 69).

Record SWChunk_inv A (L: list (weighted_ A)) (w: int) : Prop :=
	mkSWChunk_inv {
		swcinv_pos : Forall (fun x => weight' x > 0) L;
		swcinv_sum : w = list_sum weight' L }.

Definition SWChunk_IsOwner A {IA: Inhab A} {EA: Enc A} (oo: option owner_) (s: swchunk_ A) : Prop :=
	SChunk_IsOwner oo (unweighted' s).

(* Definition SWChunk_Shared A {IA: Inhab A} {EA: Enc A} (M: WChunkMemory A) (L: Wlist A) (s: swchunk_ A) : Prop :=
	let '(c, w) := s in
	SChunk_Shared M L c /\
	SWChunk_inv L w.

Definition SWChunk_UniquelyOwned A {IA: Inhab A} {EA: Enc A} (L: Wlist A) (s: swchunk_ A) : hprop :=
	let '(c, w) := s in
	c ~> SChunk_UniquelyOwned L \*
	\[SWChunk_inv L w].

Definition SWChunk_MaybeOwned A {IA: Inhab A} {EA: Enc A}	(M: WChunkMemory A) (oo: option owner_) (L: Wlist A) (s: swchunk_ A) : hprop :=
	If SWChunk_IsOwner oo s then
		s ~> SWChunk_UniquelyOwned L
	else
		\[SWChunk_Shared M L s]. *)

Definition SWChunk_MaybeOwned A {IA: Inhab A} {EA: Enc A}	(M: SWChunkMem A) (oo: option owner_) (L: Wlist A) (s: swchunk_ A) : hprop :=
	let (c, w) := s in
	c ~> SChunk_MaybeOwned M oo L \*
	\[SWChunk_inv L w].

Lemma SWChunk_MaybeOwned_Mono : forall A {IA: Inhab A} {EA: Enc A}
	(M M': SWChunkMem A) (oo: option owner_) (L: Wlist A) (c: swchunk_ A),
	SChunkExtend M M' ->
	(c ~> SWChunk_MaybeOwned M oo L ==> c ~> SWChunk_MaybeOwned M' oo L).
Admitted.

(* ******************************************************* *)
(** ** Lemmas *)

Instance partial_swchunk_inhab A : Inhab A -> Inhab (partial_swchunk_ A).
Proof using. intros. apply (Inhab_of_val (MaybeOwned arbitrary arbitrary)). Qed.

Instance swchunk_inhab A : Inhab A -> Inhab (swchunk_ A).
Proof using. intros. apply weighted_inhab. apply~ partial_swchunk_inhab. Qed.

Hint Resolve partial_swchunk_inhab swchunk_inhab.


(* ******************************************************* *)
(** ** Specifications *)

Lemma swchunk_push_spec : forall A (IA: Inhab A) (EA: Enc A)
	(v: view_) (M: SWChunkMem A) (oo: option owner_) (L: Wlist A) (c: swchunk_ A) (x: weighted_ A),
	SPEC (swchunk_push v oo c x)
	MONO M
	PRE (c ~> SWChunk_MaybeOwned M oo L)
	POST (fun M' c' => c' ~> SWChunk_MaybeOwned M' oo (vcons v x L)).
Admitted.
