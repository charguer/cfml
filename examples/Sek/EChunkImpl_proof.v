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

Require Import EChunkImpl_ml.
Require Import Capacity_proof.



(* Useful lemma *)
Lemma plus_minus : forall a b c,
	a + (b - c) = a + b - c.
Proof using. math. Qed.

#[global]
Hint Rewrite plus_minus: rew_maths.


Axiom Array_copy_spec : forall (A:Type) (EA:Enc A) (a:array A) (xs:list A),
  SPEC (Array_ml.copy a)
    PRE (\$(length xs))
    INV (a ~> Array xs)
    POST (fun a' => a' ~> Array xs).

Hint Extern 1 (RegisterSpec Array_ml.copy) => Provide Array_copy_spec.




(*************************************************)
(** EChunks *)

Record EChunk_inv A {IA: Inhab A} (L: list A) (D: list A) (front: int) (size: int) (default: A) : Prop :=
	mkEChunk_inv {
		echunk_in : forall (i: int), 0 <= i < size -> D[Wrap_up (front + i)] = L[i];
		echunk_out : forall (i: int), size <= i < K -> D[Wrap_up (front + i)] = default;
		echunk_length : length L = size;
		echunk_capa : length D = K;
		echunk_front : 0 <= front < K;
		echunk_size : 0 <= size <= K }.

Definition EChunk A {IA: Inhab A} {EA: Enc A} (L: list A) (c: echunk_ A) : hprop :=
  \exists (data: loc) (D: list A) (front: int) (size: int) (default: A),
  	c ~~~> `{ data' := data; front' := front; size' := size; default' := default }
 		\* data ~> Array D
  	\* \[EChunk_inv L D front size default].

Lemma haffine_Echunk : forall A (IA: Inhab A) (EA: Enc A) (L: list A) (c: echunk_ A),
    haffine (c ~> EChunk L).
Proof.
  intros.
  xunfold EChunk. (* Later : géré par xaffine *)
  xaffine.
Qed.

Lemma haffine_repr_Echunk : forall A (IA: Inhab A) (EA: Enc A),
    haffine_repr (@EChunk A IA EA).
Proof. intros. intros ? ?. apply haffine_Echunk. Qed.

Hint Resolve haffine_Echunk haffine_repr_Echunk : haffine.

Lemma EChunk_eq : forall c A {IA: Inhab A} {EA: Enc A} (L: list A),
  c ~> EChunk L =
  \exists (data: loc) (D: list A) (front: int) (size: int) (default: A),
    c ~~~> `{ data' := data; front' := front; size' := size; default' := default }
  	\* data ~> Array D
  	\* \[EChunk_inv L D front size default].
Proof. auto. Qed.

Hint Extern 1 (RegisterOpen EChunk) => Provide EChunk_eq.

Lemma echunk_inv_length : forall A (IA: Inhab A) (EA: Enc A) (c: echunk_ A) (L: list A),
  c ~> EChunk L ==+> \[0 <= length L <= K].
Proof.
  intros.
  xopen c. introv Hc. lets []: Hc.
  xclose* c. xsimpl*.
Qed.


(*************************************************)
(** Specifications *)

Lemma echunk_fields_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (L: list A) (c: echunk_ A),
	SPEC (echunk_fields c)
		PRE (\$1 \* c ~> EChunk L)
		POST (fun '(data, front, size, default) => \exists D,
			c ~~~> `{ data' := data; front' := front; size' := size; default' := default } \*
			data ~> Array D \*
			\[EChunk_inv L D front size default]).
Proof. xcf*. xpay. xopen c ;=> data D front size default I. xappn*. xvals*. Qed.

Hint Extern 1 (RegisterSpec echunk_fields) => Provide echunk_fields_spec.

Lemma echunk_of_fields_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (L D: list A) (a: array A) (f s: int) (d: A),
	EChunk_inv L D f s d ->
	SPEC (echunk_of_fields a f s d)
		PRE (a ~> Array D \* \$1)
		POST (fun c => c ~> EChunk L).
Proof. introv I. xcf. xpay. xapp ;=> c. xchanges~ <- EChunk_eq. Qed.

Hint Extern 1 (RegisterSpec echunk_of_fields) => Provide echunk_of_fields_spec.

(* echunk_default spec? *)

Lemma echunk_create_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (d: A),
  SPEC (echunk_create d)
    PRE (\$(K + 2))
    POST (fun c => c ~> EChunk (@nil A)).
Proof.
  xcf. xpay. xapp~ ;=> a L ->.
  xapp~; try xsimpl~.
  { constructors~; rew_listp~ ;=> i Hi.
    { false. math. }
    { rew_listp*. unwrap_up. } }
	{ forwards~: capacity_spec. }
Qed.

Hint Extern 1 (RegisterSpec echunk_create) => Provide echunk_create_spec.

Lemma echunk_is_empty_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (L: list A) (c: echunk_ A),
  SPEC (echunk_is_empty c)
    PRE (\$1 \* c ~> EChunk L)
    POST (fun b => c ~> EChunk L \* \[ b = isTrue (L = nil)]).
Proof.
  xcf*.
  xopen c; introv Inv. lets []: Inv.
  xpay. xapp.
  xclose* c. xvals*. subst*.
  now rewrite* length_zero_eq_eq_nil. (* now? *)
Qed.

Hint Extern 1 (RegisterSpec echunk_create) => Provide echunk_create_spec.

Lemma echunk_is_full_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (L: list A) (c: echunk_ A),
  SPEC (echunk_is_full c)
    PRE (\$1 \* c ~> EChunk L)
    POST (fun b => c ~> EChunk L \* \[b = isTrue (IsFull L)]).
Proof.
  xcf*.
	xopen c; introv Inv. lets []: Inv.
  xpay. xapp.
  xclose* c. xvals*.
Qed.

Hint Extern 1 (RegisterSpec echunk_is_full) => Provide echunk_is_full_spec.

Lemma echunk_peek_back_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (L: list A) (c: echunk_ A),
  L <> nil ->
  SPEC (echunk_peek_back c)
    PRE (\$2)
    INV (c ~> EChunk L)
    POST (fun x => \exists L', \[L = L' & x]).
Proof.	
  introv HL.
  xcf*.
	lets (x & q & ->): list_neq_nil_inv_last L HL.
	xopen* c. intros data D front size d Inv. lets [Iin Iout Ilen Icapa Ifront Isz]: Inv.
	xpay. xappn*.
	{ unwrap_up. }
	{ rew_list in *.
		xsimpl.
		{ fequals. fequals.
			forwards* E: Iin (size - 1). rew_array in E.
			case_if*; [rew_maths; auto | math]. }
		{ xclose* c. xsimpl. } }
Qed.

Hint Extern 1 (RegisterSpec echunk_peek_back) => Provide echunk_peek_back_spec.

Lemma echunk_pop_back_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (L: list A) (c: echunk_ A),
  L <> nil -> 
  SPEC (echunk_pop_back c)
    PRE (\$2 \* c ~> EChunk L)
    POST (fun x => \exists L', c ~> EChunk L' \* \[L = L' & x]).
Proof.
  introv HL.
  xcf*. xpay.
	lets (x & q & ->): list_neq_nil_inv_last L HL.
	xopen* c. intros data D front size d Inv. lets [Iin Iout Ilen Icapa Ifront Isz]: Inv. rew_list in *.
	xapp*. xlets. xappn*.
	{ unwrap_up. }
	{ unwrap_up. }
	{ xvals*.
		{ fequals. fequals.
			forwards* E: Iin (size - 1). rew_array in E. case_if*.
			{ false. math. } }
		{ xclose* c q.
			{ constructors* ;=> i Hi.
				{ applys_eq* Iin; list_cases*.
					{ false. unwrap_up in C. math. }
					{ unwrap_up. } }
				{ list_cases*.
					{ applys_eq Iout. unwrap_up in C. }
					{ unwrap_up. } } }
		{ xsimpl*. } } }
Qed.

Hint Extern 1 (RegisterSpec echunk_pop_back) => Provide echunk_pop_back_spec.

Lemma echunk_push_back_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (c: echunk_ A) (x: A) (L: list A),
  ~ (IsFull L) ->
  SPEC (echunk_push_back c x)
    PRE (\$2 \* c ~> EChunk L)
    POSTUNIT (c ~> EChunk (L & x)).
Proof.
  introv HL. unfolds IsFull.
  xcf*.
	xopen* c. intros data D front size d Inv. lets [Iin Iout Ilen Icapa Ifront Isz]: Inv.
  xpay. xappn*.
	{ unwrap_up. }
	{ xclose* c (L & x).
		(* Je ne suis pas sur de comprendre comment Coq fait fonctionner la preuve qui suit
			sans précisions supplémentaires, mais tant mieux *)
		{ constructors*; intros i Hi; list_cases*; unfolds* Wrap_up; false; unwrap_up. }
		{ xsimpl*. } }
Qed.

Hint Extern 1 (RegisterSpec echunk_push_back) => Provide echunk_push_back_spec.

Lemma echunk_peek_front_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (c: echunk_ A) (L: list A),
	L <> nil ->
	SPEC (echunk_peek_front c)
		PRE (\$1)
		INV (c ~> EChunk L)
		POST (fun x => \exists L', \[L = x :: L']).
Proof.
	introv HL.
	xcf*.
	lets (x & q & ->): list_neq_nil_inv_cons L HL.
	xopen* c. intros data D front size d Inv. lets [Iin Iout Ilen Icapa Ifront Isz]: Inv.
	xpay. xappn*. xclose* c (x :: q).
	{ constructors*; auto. }
	{ xsimpl*. fequals.
		forwards* E: (Iin 0). rew_list in E. rewrite <- E.
		fequals. unwrap_up. }
Qed.

Hint Extern 1 (RegisterSpec echunk_peek_front) => Provide echunk_peek_front_spec.

Lemma echunk_pop_front_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (c: echunk_ A) (L: list A),
	L <> nil ->
	SPEC (echunk_pop_front c)
		PRE (\$2 \* c ~> EChunk L)
		POST (fun x => \exists L', c ~> EChunk L' \* \[L = x :: L']).
Proof.
	introv HL.
	xcf*. xpay.
	lets (x & q & ->): list_neq_nil_inv_cons L HL.
	xopen* c. intros data D front start d Inv. lets [Iin Iout Ilen Icapa Ifront Isz]: Inv.
	xappn*. xvals.
	{ fequals. forwards* E: (Iin 0). rew_list in E. rewrite <- E. fequals. unwrap_up. }
	{ xclose* c q.
		{ rew_list in *. constructors*.
			{ intros i Hi.
				list_cases*.
				{ false. unwrap_up in C. math. }
				{ applys_eq* (Iin (1 + i)).
					{ fequals. unwrap_up. }
					{ rewrite read_cons_pos.
						{ fequals*. }
						{ math. } } }
				{ unwrap_up. } }
			{ intros i Hi.
				list_cases*.
				{ applys_eq* (Iout (1 + i)).
					{ fequals. unwrap_up. }
					{ unwrap_up in C. } } 
				{	unwrap_up. } }
			{ unwrap_up. } }
		{ xsimpl*. } }
Qed.

Hint Extern 1 (RegisterSpec echunk_pop_front) => Provide echunk_pop_front_spec.

Lemma echunk_push_front_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (c: echunk_ A) (x: A) (L: list A),
	~(IsFull L) ->
	SPEC (echunk_push_front c x)
		PRE (\$2 \* c ~> EChunk L)
		POSTUNIT (c ~> EChunk (x :: L)).
Proof.
	introv HL. unfolds IsFull.
	xcf*.
	xopen* c. intros data D front start d Inv. lets [Iin Iout Ilen Icapa Ifront Isz]: Inv.
	xpay. xappn*.
	{ unwrap_down. }
	{ xclose* c (x :: L).
		{ constructors*.
			{ intros i Hi.
				list_cases*. (* Factorisable ? *)
				{ false. unwrap_down in C0; unwrap_up in C0. }
				{ unwrap_down; unwrap_up. }
				{ false. unwrap_down in C0; unwrap_up in C0. }
				{ applys_eq* (Iin (i - 1)).
					fequals. unwrap_down; unwrap_up. }
				{ unwrap_down; unwrap_up. } }
			{ intros i Hi.
				list_cases*.
				{ false. unwrap_down in C; unwrap_up in C. }
				{ applys_eq* (Iout (i - 1)).
					fequals. unwrap_down; unwrap_up. }
				{ unwrap_down; unwrap_up. } }
			{ unwrap_down. } }
		{ xsimpl*. } }
Qed.

Hint Extern 1 (RegisterSpec echunk_push_front) => Provide echunk_push_front_spec.

Lemma echunk_get_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (c: echunk_ A) (L: list A) (i: int),
	index L i ->
	SPEC (echunk_get c i)
		PRE (\$2)
		INV (c ~> EChunk L)
		POST \[= L[i]].
Proof.
	introv Hi. rew_index in Hi. xcf. xpay.
	xopen c ;=> data D front size d I. lets [Iin Iout Ilen Icapa Ifront Isz]: I.
	xappn.
	{ unwrap_up. }
	{ xclose* c. xsimpl. forwards~: Iin i. }
Qed.

Hint Extern 1 (RegisterSpec echunk_get) => Provide echunk_get_spec.

Lemma echunk_set_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (c: echunk_ A) (L: list A) (i: int) (x: A),
	index L i ->
	SPEC (echunk_set c i x)
		PRE (c ~> EChunk L \* \$2)
		POSTUNIT (c ~> EChunk (L[i := x])).
Proof.
	introv Hi. rew_index in Hi. xcf. xpay.
	xopen c ;=> data D front size d I. lets [Iin Iout Ilen Icapa Ifront Isz]: I.
	xappn.
	{ unwrap_up. }
	{ xclose c; try xsimpl.
		constructors* ;=> j Hj; list_cases*; unwrap_up in *; false; math. }
Qed.

Hint Extern 1 (RegisterSpec echunk_set) => Provide echunk_set_spec.

Lemma echunk_copy_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (c: echunk_ A) (L: list A),
	SPEC (echunk_copy c)
		PRE (\$(K + 1))
		INV (c ~> EChunk L)
		POST (fun c' => c' ~> EChunk L).
Proof.
	xcf. xpay.
	xopen c ;=> data D front size d I.
	xapp. xapp ;=> a. xappn ;=> c'.
	xclose* c. xchanges~ <- EChunk_eq. forwards*: echunk_capa.
Qed.

Hint Extern 1 (RegisterSpec echunk_copy) => Provide echunk_copy_spec.

(* Axiom Array_copy_spec : forall (A:Type) (EA:Enc A) (a:array A) (xs:list A),
  SPEC (Array_ml.copy a)
    PRE (\$(length xs))
    INV (a ~> Array xs)
    POST (fun a' => a' ~> Array xs).

Hint Extern 1 (RegisterSpec Array_ml.copy) => Provide Array_copy_spec.

Lemma echunk_copy_spec : forall (A:Type) (IA:Inhab A) (EA:Enc A) (c:echunk_ A) (L:list A),
  SPEC (echunk_copy c)
    PRE (\$(1 + K))
    INV (c ~> EChunk L)
    POST (fun c' => c' ~> EChunk L).
Proof.
  intros.
  xcf. xpay_pre; xsimpl.
  xopen c; introv Inv.
  xappn. intros.
  xappn*. intros c'.
  xclose* c. xclose_repr* EChunk_eq c'.
  destruct Inv.
  xsimpl*.
Qed.

Hint Extern 1 (RegisterSpec echunk_copy) => Provide echunk_copy_spec. *)

(* À quoi sert ce truc ? *)
Global Instance Heapdata_echunk : forall A {IA} {EA}, Heapdata (@EChunk A IA EA).
Proof.
  intros.
  apply Heapdata_intro; intros x L1 L2.
  do 2 (xopen_repr EChunk_eq x; intros).
  xchange* (Heapdata_record x).
Qed.

Hint Resolve Heapdata_echunk : core.
