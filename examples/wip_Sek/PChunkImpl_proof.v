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

Require Import PChunkImpl_ml.
Require Import PArray_proof.
Require Import Capacity_proof.
Require Import EChunkImpl_proof.



(* Pourquoi je suis obligé de le remettre ?? *)
Instance MonType_PArrayMem A {IA: Inhab A} {EA: Enc A} :
	MonType (PArrayMem A) :=	make_MonType (PArrayMemory) (PArrayExtend).

Ltac xcf_pre tt ::=
	intros; match goal with |- TripleMon _ _ _ _ => unfold TripleMon | _ => idtac end.


(* ******************************************************* *)
(** ** Representation predicates *)

Record PChunkInv A {IA: Inhab A} (L: list A) (D: list A) (front: int) (size: int) (default: A) : Prop :=
	mkPChunk_inv {
		pchunk_in : forall (i: int), 0 <= i < size -> D[Wrap_up (front + i)] = L[i];
		pchunk_out : forall (i: int), size <= i < K -> D[Wrap_up (front + i)] = default;
		pchunk_length : length L = size;
		pchunk_capa : length D = K;
		pchunk_front : 0 <= front < K;
		pchunk_size : 0 <= size <= K }.

Definition IsPChunk A {IA: Inhab A} {EA: Enc A} (M: PArrayMem A) (L: list A) (c: pchunk_ A) : Prop :=
	let (data, front, size, default) := c in
	exists (D: list A),
		IsPArray M D data /\
		PChunkInv L D front size default.

Lemma IsPChunk_inv_IsPArray : forall A (IA: Inhab A) (EA: Enc A) (M: PArrayMem A) (c: pchunk_ A) (L: list A),
	IsPChunk M L c ->
	exists D, IsPArray M D (data' c).
Proof. unfold IsPChunk. intros. destruct c. simpl. destruct~ H as [D [Rdata I]]. Qed.

Lemma IsPChunk_inv_PChunkInv : forall A (IA: Inhab A) (EA: Enc A) (M: PArrayMem A) (c: pchunk_ A) (L: list A),
	IsPChunk M L c ->
	exists D, PChunkInv L D (front' c) (size' c) (default' c).
Proof. unfold IsPChunk. intros. destruct c. simpl. destruct~ H as [D [Rdata I]]. Qed.

Lemma IsPChunk_inv_length : forall A (IA: Inhab A) (EA: Enc A) (M: PArrayMem A) (c: pchunk_ A) (L: list A),
	IsPChunk M L c -> 0 <= length L <= K.
Proof.
	intros. forwards [D I]: IsPChunk_inv_PChunkInv H.
	forwards~: pchunk_size. forwards~: pchunk_length.
Qed.

Hint Resolve IsPChunk_inv_IsPArray IsPChunk_inv_PChunkInv IsPChunk_inv_length.

Definition IsHead A {IA: Inhab A} {EA: Enc A} (M: PArrayMem A) (c: pchunk_ A) : hprop :=
	IsHead M (data' c).

Definition access_cost A {IA: Inhab A} {EA: Enc A} (ishd: bool) (M: PArrayMem A) (c: pchunk_ A) : hprop :=
	if ishd then IsHead M c \* \$1 else \$(2 * K + 2).

Lemma access_cost_eq : forall A {IA: Inhab A} {EA: Enc A} (ishd: bool) (M: PArrayMem A) (c: pchunk_ A) (L D: list A),
	IsPArray M D (data' c) ->
		access_cost ishd M c =
		parray_rebase_and_get_array_cost ishd M (data' c) D.
Admitted.

Lemma rebase_cost_true : forall A {IA: Inhab A} {EA: Enc A} (M: PArrayMem A) (pa: PArray_ml.parray_ A) (L: list A),
	parray_rebase_and_get_array_cost true M pa L = PArray_proof.IsHead M pa \* \$1.
Admitted.

Lemma rebase_cost_false : forall A {IA: Inhab A} {EA: Enc A} (M: PArrayMem A) (pa: PArray_ml.parray_ A) (L: list A),
	parray_rebase_and_get_array_cost false M pa L = \$(length L + bound L + 2).
Admitted.

Hint Resolve access_cost_eq rebase_cost_true.


(*************************************************)
(** Specifications *)

Lemma pchunk_default_spec : forall A (IA: Inhab A) (EA: Enc A) (M: PArrayMem A) (L: list A) (c: pchunk_ A),
	IsPChunk M L c ->
	SPEC (pchunk_default c)
		PRE (\$1)
		POST \[= default' c].
Proof. unfolds IsPChunk. introv Rc. xcf. xvals~. Qed.

Hint Extern 1 (RegisterSpec pchunk_default) => Provide pchunk_default_spec.

Lemma pchunk_create_spec : forall A (IA: Inhab A) (EA: Enc A) (M: PArrayMem A) (a: A),
	SPEC (pchunk_create a)
		MONO M
		PRE (\$(K + 3))
		POST (fun M' c => \[IsPChunk M' nil c] \* IsHead M' c).
Proof.
	xcf. xapp~ ;=> data M' HM' Rdata _.
	xvals~.
	unfolds~ IsPChunk. exists (make K a). split~.
	{ constructors~; intros.
		{ math. }
		{ rew_listp~. unwrap_up. }
		{ rew_listp~. } }
Qed.

Hint Extern 1 (RegisterSpec pchunk_create) => Provide pchunk_create_spec.

Lemma pchunk_is_empty_spec : forall A (IA: Inhab A) (EA: Enc A) (M: PArrayMem A) (L: list A) (c: pchunk_ A),
	IsPChunk M L c ->
	SPEC (pchunk_is_empty c)
		PRE (\$1)
		POST (fun b => \[b = isTrue (L = nil)]).
Proof.
	introv Rc. xcf~. xpay. xvals~.
	forwards~ [D I]: IsPChunk_inv_PChunkInv. forwards~ EL: pchunk_length. rewrites <- EL.
	rewrite* length_zero_eq_eq_nil.
Qed.

Hint Extern 1 (RegisterSpec pchunk_is_empty) => Provide pchunk_is_empty_spec.

Lemma pchunk_is_full_spec : forall A (IA: Inhab A) (EA: Enc A) (M: PArrayMem A) (L: list A) (c: pchunk_ A),
	IsPChunk M L c ->
	SPEC (pchunk_is_full c)
		PRE (\$1)
		POST (fun b => \[b = isTrue (IsFull L)]).
Admitted.

Hint Extern 1 (RegisterSpec pchunk_is_full) => Provide pchunk_is_full_spec.

Lemma pchunk_peek_back_spec : forall A (IA: Inhab A) (EA: Enc A) (ishd: bool) (M: PArrayMem A) (L: list A) (c: pchunk_ A),
	IsPChunk M L c ->
	L <> nil ->
	SPEC (pchunk_peek_back c)
		PRE (\$5 \* access_cost ishd M c)
		INV (PArrayMemory M)
		POST (fun x => IsHead M c \* \exists L', \[L = L' & x]).
Admitted.

Hint Extern 1 (RegisterSpec pchunk_peek_back) => Provide pchunk_peek_back_spec.

Lemma pchunk_pop_back_spec : forall A (IA: Inhab A) (EA: Enc A) (ishd: bool) (M: PArrayMem A) (L: list A) (c: pchunk_ A),
	IsPChunk M L c ->
	L <> nil ->
	SPEC (pchunk_pop_back c)
		MONO M
		PRE (\$7 \* access_cost ishd M c)
		POST (fun M' '(c', x) => \exists L',
			IsHead M' c' \*
			\[IsPChunk M' L' c'] \*
			\[L = L' & x]).
Proof.
	introv Rc HL. xcf. xpay.
	lets (x & q & ->): list_neq_nil_inv_last L HL.
	xlets. xapp. destruct c; simpls. lets~ [D [Rdata [Iin Iout Ilen Icapa Ifront Isz]]]: Rc. rew_list in Ilen.
	unfold IsHead; simpl. rewrites~ (>> access_cost_eq D); simpl.
	xapp~; simpl.
	{ unwrap_up. }
	{	intros x' M' E -> _. xchange~ <- rebase_cost_true D. xapp~.
		{ unwrap_up. }
		{ intros pa M'' E' Rpa _. xlets. xvals~.
			unfold IsPChunk. exists. split~.
			{ constructors* ;=> i Hi.
				{ applys_eq* Iin; list_cases*.
					{ unwrap_up in C; false; math. }
					{ unwrap_up. } }
				{ list_cases*.
					{ applys_eq* Iout. unwrap_up in C. }
					{ unwrap_up. } } }
			{ fequals. fequals. forwards* H: Iin (size' - 1).
				rew_array in H. case_if~. false. math. } } }
Qed.

Hint Extern 1 (RegisterSpec pchunk_pop_back) => Provide pchunk_pop_back_spec.

Lemma pchunk_push_back_spec : forall A (IA: Inhab A) (EA: Enc A) (ishd: bool) (M: PArrayMem A) (c: pchunk_ A) (x: A) (L: list A),
	IsPChunk M L c ->
	~ (IsFull L) ->
	SPEC (pchunk_push_back c x)
		MONO M
		PRE (\$5 \* access_cost ishd M c)
		POST (fun M' c' => IsHead M' c' \* \[IsPChunk M' (L & x) c']).
Proof.
	introv Rc HL. unfolds IsFull. xcf. simpl. xpay.
	destruct c; simpls. lets~ [D [Rdata [Iin Iout Ilen Icapa Ifront Isz]]]: Rc.
	xapp. rewrites~ (>> access_cost_eq L D); simpl. xapp~.
	{ unwrap_up. }
	{ intros pa M' E Rpa _. xvals~. unfold IsPChunk. exists; split~.
		{ constructors* ;=> i Hi; list_cases*; unwrap_up in *; false; math. } }
Qed.

Hint Extern 1 (RegisterSpec pchunk_push_back) => Provide pchunk_push_back_spec.

Lemma pchunk_peek_front_spec : forall A (IA: Inhab A) (EA: Enc A) (ishd: bool) (M: PArrayMem A) (c: pchunk_ A) (L: list A),
	IsPChunk M L c ->
	L <> nil ->
	SPEC (pchunk_peek_front c)
		PRE (\$5 \* access_cost ishd M c)
		INV (PArrayMemory M)
		POST (fun x => IsHead M c \* \exists L', \[L = x :: L']).
Admitted.

Hint Extern 1 (RegisterSpec pchunk_peek_front) => Provide pchunk_peek_front_spec.

Lemma pchunk_pop_front_spec : forall A (IA: Inhab A) (EA: Enc A) (ishd: bool) (M: PArrayMem A) (c: pchunk_ A) (L: list A),
	IsPChunk M L c ->
	L <> nil ->
	SPEC (pchunk_pop_front c)
		MONO M
		PRE (\$11 \* access_cost ishd M c)
		POST (fun M' '(c', x) => \exists L',
			IsHead M' c' \*
			\[IsPChunk M' L' c'] \*
			\[L = x :: L']).
Admitted.

Hint Extern 1 (RegisterSpec pchunk_pop_front) => Provide pchunk_pop_front_spec.

Lemma pchunk_push_front_spec : forall A (IA: Inhab A) (EA: Enc A) (ishd: bool) (M: PArrayMem A) (c: pchunk_ A) (x: A) (L: list A),
	IsPChunk M L c ->
	~ (IsFull L) ->
	SPEC (pchunk_push_back c x)
		MONO M
		PRE (\$5 \* access_cost ishd M c)
		POST (fun M' c' => IsHead M' c' \* \[IsPChunk M' (x :: L) c']).
Admitted.

Hint Extern 1 (RegisterSpec pchunk_push_front) => Provide pchunk_push_front_spec.

Lemma pchunk_get_spec : forall A (IA: Inhab A) (EA: Enc A) (ishd: bool) (M: PArrayMem A) (c: pchunk_ A) (L: list A) (i: int),
	IsPChunk M L c ->
	index L i ->
	SPEC (pchunk_get c i)
		PRE (\$4 \* access_cost ishd M c)
		INV (PArrayMemory M)
		POST (fun x => IsHead M c \* \[x = L[i]]).
Admitted.

Hint Extern 1 (RegisterSpec pchunk_get) => Provide pchunk_get_spec.

Lemma pchunk_set_spec : forall A (IA: Inhab A) (EA: Enc A) (ishd: bool) (M: PArrayMem A) (c: pchunk_ A) (L: list A) (i: int) (x: A),
	IsPChunk M L c ->
	index L i ->
	SPEC (pchunk_set c i x)
		MONO M
		PRE (\$5 \* access_cost ishd M c)
		POST (fun M' c' => IsHead M' c' \* \[IsPChunk M' (L[i := x]) c']).
Proof.
	introv Rc Hi. xcf; simpl. xpay. xapp.
	destruct c; simpls. lets [D [Rdata [Iin Iout Ilen Icapa Ifront Isz]]]: Rc. xchange~ access_cost_eq; simpl. xapp~.
	{ rew_index in *. unwrap_up. }
	{ intros pa M' E Rpa _. xvals~.
		unfold IsPChunk. exists; split~.
		{ constructors* ;=> j Hj; list_cases*; unwrap_up in *; false; math. } }
Qed.

Hint Extern 1 (RegisterSpec pchunk_set) => Provide pchunk_set_spec.

Lemma pchunk_of_echunk_spec : forall A (IA: Inhab A) (EA: Enc A) (M: PArrayMem A) (ec: EChunkImpl_ml.echunk_ A) (L: list A),
	SPEC (pchunk_of_echunk ec)
		MONO M
		PRE (\$3 \* ec ~> EChunk L)
		POST (fun M' pc => IsHead M' pc \* \[IsPChunk M' L pc]).
Proof.
	xcf*. xpay. xapp ;=> [[[data front] size] default]. xpull ;=> D I. xmatch.
	xapp ;=> pa M' E Rpa _. xvals~.
	unfold IsPChunk. exists D. split~.
	destruct I. constructors~.
Qed.

Hint Extern 1 (RegisterSpec pchunk_of_echunk) => Provide pchunk_of_echunk_spec.
