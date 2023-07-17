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
Require Import EChunk_ml.
Require Import PChunk_ml.
Require Import SChunk_ml.
Require Import Capacity_proof.
Require Import View_proof.
Require Import EChunkImpl_proof.
Require Import EChunk_proof.
Require Import PArray_proof.
Require Import PChunkImpl_proof.
Require Import PChunk_proof.



(* ******************************************************* *)
(** ** Representation predicates *)

Notation "'EChunkMap' A" := (map (echunk_ A) (list A)) (at level 69).

Record ChunkMemory (A: Type) : Type :=
	mk_ChunkMemory {
		cm_a : Memory A;
		cm_c : EChunkMap A }.

(* Definition IsMaybeOwner A {IA: Inhab A} {EA: Enc A} (oo: option owner_) (c: schunk_ A) : Prop :=
	match c with
	|	MaybeOwned ec o => oo = Some o
	|	Shared _ => oo = None
	end. *)

Definition SChunk_IsOwner A {IA: Inhab A} {EA: Enc A} (oo: option owner_) (c: schunk_ A) : Prop :=
	match c with
	|	MaybeOwned ec o => oo = Some o
	|	Shared _ => False
	end.

Definition SChunk_Shared A {IA: Inhab A} {EA: Enc A} (M: ChunkMemory A) (L: list A) (c: schunk_ A) : Prop :=
	match c with
	|	MaybeOwned ec _ => ec \indom (cm_c M) /\ (cm_c M)[ec] = L
	|	Shared pc => IsPChunk (cm_a M) L pc
	end.

Definition SChunk_UniquelyOwned A {IA: Inhab A} {EA: Enc A} (L: list A) (c: schunk_ A) : hprop :=
	match c with
	|	MaybeOwned ec _ => ec ~> EChunk L
	|	Shared _ => \[False]
	end.

Definition SChunk_MaybeOwned A {IA: Inhab A} {EA: Enc A} (M: ChunkMemory A) (oo: option owner_) (L: list A) (c: schunk_ A) : hprop :=
	If SChunk_IsOwner oo c then
		c ~> SChunk_UniquelyOwned L
	else
		\[SChunk_Shared M L c].

Definition CMSharedRepr A {IA: Inhab A} {EA: Enc A} (M: ChunkMemory A) : hprop :=
	SharedRepr (cm_a M) \*
	Group (EChunk (A := A)) (cm_c M).

Definition CMExtend A {IA: Inhab A} {EA: Enc A} (M M': ChunkMemory A) : Prop :=
	Extend (cm_a M) (cm_a M') /\
	(cm_c M) \c (cm_c M') /\
	forall sc L, SChunk_Shared M L sc ->
		SChunk_Shared M' L sc.


(* ******************************************************* *)
(** ** Lemmas *)

#[global]
Instance MonType_ChunkMemory A {IA: Inhab A} {EA: Enc A} :
	MonType (ChunkMemory A) := make_MonType (@CMSharedRepr A IA EA) (@CMExtend A IA EA).


(* ******************************************************* *)
(** ** Specs *)

Lemma schunk_match_id_spec : forall A (IA: Inhab A) (EA: Enc A) (M: ChunkMemory A) (oo: option owner_) (L: list A) (c: schunk_ A),
	SPEC (schunk_match_id oo c)
		MONO M
		PRE \[]
		INV (c ~> SChunk_MaybeOwned M oo L)
		POST (fun M' c' => c' ~> SChunk_MaybeOwned M' oo L).
Admitted.

Hint Extern 1 (RegisterSpec schunk_match_id) => Provide schunk_match_id_spec.

Lemma schunk_default_spec : forall A (IA: Inhab A) (EA: Enc A) (M: ChunkMemory A) (oo: option owner_) (L: list A) (c: schunk_ A),
	SPEC (schunk_default c)
		PRE \[]
		INV (c ~> SChunk_MaybeOwned M oo L)
		POST (fun (d: A) => \[]).
Admitted.

Hint Extern 1 (RegisterSpec schunk_default) => Provide schunk_default_spec.

Lemma schunk_is_empty_spec : forall A (IA: Inhab A) (EA: Enc A) (M: ChunkMemory A) (oo: option owner_) (L: list A) (c: schunk_ A),
	SPEC (schunk_is_empty c)
		PRE \[]
		INV (c ~> SChunk_MaybeOwned M oo L)
		POST \[= isTrue (L = nil)].
Admitted.

Hint Extern 1 (RegisterSpec schunk_is_empty) => Provide schunk_is_empty_spec.

Lemma schunk_is_full_spec : forall A (IA: Inhab A) (EA: Enc A) (M: ChunkMemory A) (oo: option owner_) (L: list A) (c: schunk_ A),
	SPEC (schunk_is_full c)
		PRE \[]
		INV (c ~> SChunk_MaybeOwned M oo L)
		POST \[= isTrue (IsFull L)].
Admitted.

Hint Extern 1 (RegisterSpec schunk_is_full) => Provide schunk_is_full_spec.
