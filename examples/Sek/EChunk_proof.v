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

Require Import View_ml.
Require Import EChunk_ml.
Require Import Capacity_proof.
Require Import View_proof.
Require Import EChunkImpl_proof.


(* ******************************************************* *)

(* echunk_default_spec *)

Lemma echunk_create_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (d: A),
  SPEC (echunk_create d)
    PRE (\$(K + 2))
    POST (fun c => c ~> EChunk (@nil A)).
Proof. xcf. xtriple. xapp. xsimpl~. Qed.

Hint Extern 1 (RegisterSpec echunk_create) => Provide echunk_create_spec.

Lemma echunk_is_empty_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (L: list A) (c: echunk_ A),
  SPEC (echunk_is_empty c)
    PRE (\$1 \* c ~> EChunk L)
    POST (fun b => c ~> EChunk L \* \[b = isTrue (L = nil)]).
Proof. xcf. xtriple. xapp. xsimpl~. Qed.

Hint Extern 1 (RegisterSpec echunk_is_empty) => Provide echunk_is_empty_spec.

Lemma echunk_is_full_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (L: list A) (c: echunk_ A),
  SPEC (echunk_is_full c)
    PRE (\$1 \* c ~> EChunk L)
    POST (fun b => c ~> EChunk L \* \[b = isTrue (IsFull L)]).
Proof. xcf. xtriple. xapp. xsimpl~. Qed.

Hint Extern 1 (RegisterSpec echunk_is_full) => Provide echunk_is_full_spec.

(* echunk_size_spec *)

Lemma echunk_peek_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (v: view_) (L: list A) (c: echunk_ A),
	L <> nil ->
	SPEC (echunk_peek v c)
		PRE (\$3)
		INV (c ~> EChunk L)
		POST (fun x => \exists L', \[L = vcons v x L']).
Proof. xcf. xpay. xmatch; xapp~ ;=> x L' ->; xsimpl~; fequals. Qed.

Hint Extern 1 (RegisterSpec echunk_peek) => Provide echunk_peek_spec.

Lemma echunk_pop_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (v: view_) (L: list A) (c: echunk_ A),
	L <> nil -> 
	SPEC (echunk_pop v c)
		PRE (\$3 \* c ~> EChunk L)
		POST (fun x => \exists L', c ~> EChunk L' \* \[L = vcons v x L']).
Proof. xcf. xpay. xmatch; xapp~ ;=> x L' ->; xsimpl~. Qed.

Hint Extern 1 (RegisterSpec echunk_pop) => Provide echunk_pop_spec.

Lemma echunk_push_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (v: view_) (c: echunk_ A) (x: A) (L: list A),
	~ (IsFull L) ->
	SPEC (echunk_push v c x)
		PRE (\$3 \* c ~> EChunk L)
		POSTUNIT (c ~> EChunk (vcons v x L)).
Proof. xcf. xpay. xmatch; xapp~; xsimpl~. Qed.

Hint Extern 1 (RegisterSpec echunk_push) => Provide echunk_push_spec.

Lemma echunk_get_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (c: echunk_ A) (L: list A) (i: int),
	index L i ->
	SPEC (echunk_get c i)
		PRE (\$2)
		INV (c ~> EChunk L)
		POST \[= L[i]].
Proof. xcf. xtriple. xapp~. xsimpl~. Qed.

Hint Extern 1 (RegisterSpec echunk_get) => Provide echunk_get_spec.

Lemma echunk_set_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (c: echunk_ A) (L: list A) (i: int) (x: A),
	index L i ->
	SPEC (echunk_set c i x)
		PRE (c ~> EChunk L \* \$2)
		POSTUNIT (c ~> EChunk (L[i := x])).
Proof. xcf. xtriple. xapp~. xsimpl~. Qed.

Hint Extern 1 (RegisterSpec echunk_set) => Provide echunk_set_spec.

Lemma echunk_copy_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (c: echunk_ A) (L: list A),
	SPEC (echunk_copy c)
		PRE (\$(K + 1))
		INV (c ~> EChunk L)
		POST (fun c' => c' ~> EChunk L).
Proof. xcf. xtriple. xapp. xsimpl~. Qed.

Hint Extern 1 (RegisterSpec echunk_copy) => Provide echunk_copy_spec.
