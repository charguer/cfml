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

Require Import EChunk_ml.




(* Useful lemma *)
Lemma plus_minus : forall a b c,
	a + (b - c) = a + b - c.
Proof using. math. Qed.

#[global]
Hint Rewrite plus_minus: rew_maths.




(*************************************************)
(** EChunks *)

Notation "'K'" := capacity.

Definition Wrap_up i := If i >= K then i - K else i.
Definition Wrap_down i := If i < 0 then i + K else i.

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

Definition IsFull A (c:list A) : Prop :=
  length c = K.

Lemma capacity_spec :
  capacity > 0.
Proof. rewrite capacity_cf__; math. Qed.

Lemma NotFull_of_nil : forall A,
  ~ IsFull (@nil A).
Proof.
  hint capacity_spec.
  intros. unfold IsFull. rew_list*.
Qed.

Hint Extern 1 (@le _ _ _ capacity) => hint capacity_spec; math.
Hint Extern 1 (@lt _ _ _ capacity) => hint capacity_spec; math.
Hint Extern 1 (@ge _ _ capacity _) => hint capacity_spec; math.
Hint Extern 1 (@gt _ _ capacity _) => hint capacity_spec; math.

(*************************************************)
(** Specifications *)

Lemma wrap_up_spec : forall (n: int),
	SPEC (wrap_up n)
		PRE (\$1)
		POST (fun n' => \[n' = Wrap_up n]).
Proof.
	xcf. unfold Wrap_up.
	xpay.
	xif; intros C; case_if; xval*; xsimpl*.
Qed.

Hint Extern 1 (RegisterSpec wrap_up) => Provide wrap_up_spec.

Lemma wrap_down_spec : forall (n: int),
	SPEC (wrap_down n)
		PRE (\$1)
		POST (fun n' => \[n' = Wrap_down n]).
Proof.
	xcf. unfold Wrap_down.
	xpay.
	xif; intros C; case_if; xval*; xsimpl*.
Qed.

Hint Extern 1 (RegisterSpec wrap_down) => Provide wrap_down_spec.

Tactic Notation "unwrap_up" :=
	unfold Wrap_up; repeat case_if*.
Tactic Notation "unwrap_up" "in" hyp(H) :=
	unfold Wrap_up in H; repeat case_if* in H.

Tactic Notation "unwrap_down" :=
	unfold Wrap_down; repeat case_if*.
Tactic Notation "unwrap_down" "in" hyp(H) :=
	unfold Wrap_down in H; repeat case_if* in H.

Lemma echunk_create_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (a: A),
  SPEC (echunk_create a)
    PRE (\$(K + 1))
    POST (fun c => c ~> EChunk (@nil A)).
Proof.
  xcf. xpay. xapp*. intros d L Hd.
  xapp*. intros r.
  xunfolds* EChunk.
  { constructors*; subst*; intros.
    { false. math. }
    { rew_listp*. unwrap_up. }
    { rew_listp*. } }
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
    PRE (\$4 \* c ~> EChunk L)
    POST (fun x => \exists L', c ~> EChunk L' \* \[L = L' & x]).
Proof.
  introv HL.
  xcf*.
	xpay. xapp*. intros x q E. subst.
	xopen* c. intros data D front size d Inv. lets [Iin Iout Ilen Icapa Ifront Isz]: Inv.
	xapp*. xlets. xappn*.
	{ unwrap_up. }
	{ rew_list in *.
		xvals*. xclose* c q.
		{ constructors*; intros i Hi.
			{ applys_eq* Iin; list_cases*.
				{ false. unwrap_up in C. math. }
				{ unwrap_up. } }
			{ list_cases*.
				{ applys_eq Iout. unwrap_up in C. }
				{ unwrap_up. } } }
		{ xsimpl*. } }
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
		PRE (\$3 \* c ~> EChunk L)
		POST (fun x => \exists L', c ~> EChunk L' \* \[L = x :: L']).
Proof.
	introv HL.
	xcf*.
	xpay. xapp*. intros x q E. subst.
	xopen* c. intros data D front start d Inv. lets [Iin Iout Ilen Icapa Ifront Isz]: Inv.
	xappn*. xval. xclose* c q.
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
	{ xsimpl*. }
Qed.

Hint Extern 1 (RegisterSpec echunk_pop_front) => Provide echunk_pop_front_spec.

Lemma echunp_push_front_spec : forall (A: Type) (IA: Inhab A) (EA: Enc A) (c: echunk_ A) (x: A) (L: list A),
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
