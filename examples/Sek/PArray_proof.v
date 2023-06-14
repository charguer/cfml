Set Implicit Arguments.
From CFML Require Import LibSepGroup WPLibCredits Stdlib Array_proof.
From TLC Require Import LibListZ LibMap.

From CFML Require Import LibSepTLCbuffer.
Import IndexHints.

Require Import ListMisc.
Require Import Mono.

Require Import PArray_ml.



(* Copy-paste of earlier definitions to work around a notation bug in Coq *)

Notation "<[ e ]>" :=
 e
 (at level 0, e custom wp at level 99) : wp_scope.

Notation "'Pay' F" :=
 ((*Wptag*) (Wpgen_pay F))
 (in custom wp at level 69, F at level 0) : wp_scope.

Notation "'Fail'" :=
 ((*Wptag*) (Wpgen_fail))
 (in custom wp at level 69) : wp_scope.

Notation "'Done'" :=
 ((*Wptag*) (Wpgen_done))
 (in custom wp at level 69) : wp_scope.

Notation "'Match' V F1" :=
 ((*Wptag*) (Wpgen_match V F1))
 (in custom wp at level 69,
  V custom wp at level 0,
  F1 custom wp at level 69,
  format "'[v' 'Match'  V  '/' '['   F1 ']' ']' " ) : wp_scope.

Notation "'Assert' F" :=
 ((*Wptag*) (Wpgen_assert F))
 (in custom wp at level 69,
  F custom wp at level 99) : wp_scope.

Notation "'Val' v" :=
 ((*Wptag*) (Wpgen_val v))
 (in custom wp at level 69) : wp_scope.

Notation "'Let' x ':=' F1 'in' F2" :=
 ((*Wptag*) (Wpgen_let_trm F1 (fun x => F2)))
 (in custom wp at level 69,
  x ident,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  right associativity,
 format "'[v' '[' 'Let'  x  ':='  F1  'in' ']' '/' '[' F2 ']' ']'") : wp_scope.

Notation "'LetVal' x ':=' V 'in' F1" :=
 ((*Wptag*) (Wpgen_let_val V (fun x => F1)))
 (in custom wp at level 69,
  x ident,
  V constr at level 69,
  F1 custom wp at level 99,
  right associativity,
 format "'[v' '[' 'LetVal'  x  ':='  V  'in' ']' '/' '[' F1 ']' ']'") : wp_scope.

Notation "'Alias' x ':=' V 'in' F1" :=
 ((*Wptag*) (Wpgen_alias (Wpgen_let_val V (fun x => F1))))
 (in custom wp at level 69,
  x ident,
  V constr at level 69,
  F1 custom wp at level 99,
  right associativity,
 format "'[v' '[' 'Alias'  x  ':='  V  'in' ']' '/' '[' F1 ']' ']'") : wp_scope.

Notation "'Seq' F1 ; F2" :=
 ((*Wptag*) (Wpgen_seq F1 F2))
 (in custom wp at level 68,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  right associativity,
  format "'[v' 'Seq'  '[' F1 ']'  ; '/' '[' F2 ']' ']'") : wp_scope.

Notation "'App' f x1 .. xn" :=
 ((*Wptag*) (Wpgen_app _ f (cons (Dyn x1) .. (cons (Dyn xn) nil) ..)))
  (in custom wp at level 68,
   f constr at level 0,
   x1 constr at level 0,
   xn constr at level 0) (* TODO: format *)
  : wp_scope.

(* TODO: why need both? *)
Notation "'App' f x1 x2 .. xn" :=
 ((*Wptag*) (Wpgen_app _ f (cons (Dyn x1) (cons (Dyn x2) .. (cons (Dyn xn) nil) ..))))
  (in custom wp at level 68,
   f constr at level 0,
   x1 constr at level 0,
   x2 constr at level 0,
   xn constr at level 0) (* TODO: format *)
  : wp_scope.

Notation "'If_' v 'Then' F1 'Else' F2" :=
 ((*Wptag*) (Wpgen_if v F1 F2))
 (in custom wp at level 69,
  v constr at level 69,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  left associativity,
  format "'[v' '[' 'If_'  v  'Then'  ']' '/' '['   F1 ']' '/' 'Else' '/' '['   F2 ']' ']'") : wp_scope.

Notation "'While' F1 'Do' F2 'Done'" :=
 ((*Wptag*) (Wpgen_while F1 F2))
 (in custom wp at level 68,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  format "'[v' '[' 'While'  F1  'Do'  ']' '/' '['   F2 ']' '/' 'Done' ']'") : wp_scope.

Notation "'For' i '=' n1 'To' n2 'Do' F1 'Done'" :=
 ((*Wptag*) (Wpgen_for_int n1 n2 (fun i => F1)))
 (in custom wp at level 68,
  i ident,
  n1 constr at level 69,
  n2 constr at level 69,
  F1 custom wp at level 99,
  format "'[v' '[' 'For'  i  '='  n1  'To'  n2  'Do'  ']' '/' '['   F1 ']' '/' 'Done' ']'") : wp_scope.

Notation "'For' i '=' n1 'Downto' n2 'Do' F1 'Done'" :=
 ((*Wptag*) (Wpgen_for_downto_int n1 n2 (fun i => F1)))
 (in custom wp at level 68,
  i ident,
  n1 constr at level 69,
  n2 constr at level 69,
  F1 custom wp at level 99,
  format "'[v' '[' 'For'  i  '='  n1  'Downto'  n2  'Do'  ']' '/' '['   F1 ']' '/' 'Done' ']'") : wp_scope.

Notation "'LetFun' f ':=' B1 'in' F1" :=
 ((*Wptag*) (Wpgen_let_fun (fun A EA Q => \forall f, \[B1] \-* (F1 A EA Q))))
 (in custom wp at level 69,
  f ident,
  B1 constr at level 69,
  F1 custom wp at level 99,
  right associativity,
  format "'[v' '[' 'LetFun'  f  ':=' '/' '['   B1 ']'  'in' ']' '/' '[' F1 ']' ']'" ) : wp_scope.


Ltac xcf_pre tt ::=
	intros; match goal with |- TripleMon _ _ _ _ => unfold TripleMon | _ => idtac end.



(*************************************************)
(** PArrays *)
Implicit Types p q: loc.

(* parray_desc *)
Inductive Desc A :=
  |	Desc_Base : list A -> Desc A 
  |	Desc_Diff : loc -> int -> A -> Desc A.

#[global]
Instance Desc_inhab A : Inhab A -> Inhab (Desc A).
Proof using. intros. apply (Inhab_of_val (Desc_Base nil)). Qed.

Hint Resolve Desc_inhab.

Definition PArray_Desc A {EA: Enc A} (D: Desc A) (d: parray_desc_ A) : hprop :=
	match d, D with
	|	PArray_Base a, Desc_Base L => a ~> Array L
	|	PArray_Diff p i x, Desc_Diff q j y => \[(p, i, x) = (q, j, y)]
	|	_, _ => \[False]
	end.

Lemma PArray_Desc_eq : forall A (EA: Enc A) (D: Desc A) (d: parray_desc_ A),
	d ~> PArray_Desc D =
	match d, D with
	|	PArray_Base a, Desc_Base L => a ~> Array L
	|	PArray_Diff p i x, Desc_Diff q j y => \[(p, i, x) = (q, j, y)]
	|	_, _ => \[False]
	end.
Proof using. auto. Qed.

Lemma PArray_Desc_eq_Base : forall A (EA: Enc A) (D: Desc A) (a: array A),
	PArray_Base a ~> PArray_Desc D = \exists L, \[D = Desc_Base L] \* a ~> Array L.
Proof using.
	intros. cases D; rewrite PArray_Desc_eq.
	{ xsimpl*. intros L E. injection E. auto. }
	{ xsimpl*. Unshelve. apply nil. (* Pourquoi il a besoin qu'on fasse ça ? *) }
Qed.

Lemma PArray_Desc_eq_Diff : forall A (EA: Enc A) (D: Desc A) p i x,
	PArray_Diff p i x ~> PArray_Desc D = \[D = Desc_Diff p i x].
Proof using.
	intros. cases D; rewrite PArray_Desc_eq.
	{	xsimpl*. }
	{ xsimpl*; intros H; injection H as E1 E2 E3; subst; auto. }
Qed.

Hint Extern 1 (RegisterOpen PArray_Desc) => Provide PArray_Desc_eq_Base PArray_Desc_eq_Diff PArray_Desc_eq.

Definition PArray A {EA: Enc A} (D: Desc A) (pa: parray_ A) : hprop :=
	\exists d, pa ~~~> `{ data' := d } \* d ~> PArray_Desc D.

Lemma PArray_eq : forall A (EA: Enc A) (D: Desc A) (pa: parray_ A),
	pa ~> PArray D =
	\exists d, pa ~~~> `{ data' := d } \* d ~> PArray_Desc D.
Proof using. auto. Qed.

Hint Extern 1 (RegisterOpen PArray) => Provide PArray_eq.

Global Instance Heapdata_PArray : forall A (EA: Enc A),
	Heapdata (PArray (A := A)).
Proof using.
	intros. apply Heapdata_intro. intros.
	xchange* PArray_eq. intros D2.
	xchange* PArray_eq. intros D1.
	xchange* Heapdata_record.
Qed.

Hint Resolve Heapdata_PArray.


Definition Memory A : Type := map (parray_ A) (Desc A).

Record Inv A {IA: Inhab A} {EA: Enc A} (M: Memory A) : Prop := {
	Inv_closure : forall p,
		p \indom M ->
		forall i v q, M[p] = Desc_Diff q i v ->
		q \indom M
}.

Inductive IsPArray A {IA: Inhab A} {EA: Enc A} (M: Memory A) : list A -> parray_ A -> Prop :=
|	IsPArray_Base : forall pa L,
		pa \indom M ->
		M[pa] = Desc_Base L ->
		IsPArray M L pa
|	IsPArray_Diff : forall pa pa' i x L L',
		pa \indom M ->
		M[pa] = Desc_Diff pa' i x ->
		IsPArray M L' pa' ->
		L = L'[i := x] ->
		IsPArray M L pa.

Lemma IsPArray_inv_indom : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
	IsPArray M L pa -> pa \indom M.
Proof using. intros. inversion H; auto. Qed.

Hint Resolve IsPArray_inv_indom.


Definition Shared {A} {IA: Inhab A} {EA: Enc A} (M: Memory A) : hprop :=
	Group (PArray (A := A)) M \* \[Inv M].


Definition Extend {A} {IA: Inhab A} {EA: Enc A} (M M': Memory A) : Prop :=
	(dom M) \c (dom M') /\ forall L p, IsPArray M L p -> IsPArray M' L p.

Lemma IsPArray_extend : forall A (IA: Inhab A) (EA: Enc A) (M M': Memory A) p L,
	Extend M M' -> IsPArray M L p -> IsPArray M' L p.
Proof. introv [_ H] Arr. auto. Qed.


Instance MonType_EChunkMap A {IA: Inhab A} {EA: Enc A} :
	MonType (Memory A) :=	make_MonType (Shared) (Extend).

(*************************************************)
(** Specifications *)

Lemma focus_shared : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
  IsPArray M L pa ->
  Shared M ==+> pa ~> PArray M[pa].
Proof using.
  skip.
Qed.

Lemma Extend_add_binding : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (D: Desc A),
	~(pa \indom M) ->
		Extend M (M[pa := D]).
Proof using.
	introv H. unfold Extend. split.
	{ rew_set. (* TODO : AC *) skip. }
	{ intros L p Rp. induction Rp.
		{ apply IsPArray_Base.
			{ false. skip. }
			{ skip. } }
		{ skip. } }
Qed.

Lemma parray_create_spec : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (sz: int) (d: A),
	sz >= 0 ->
	SPEC (parray_create sz d)
		MONO M
		PRE \[]
		POST (fun M' pa => \[IsPArray M' (make sz d) pa]).
Proof using.
	introv Hsz. xcf*. simpl.
	xpay_skip.
	xapp*. intros a L E. subst.
	xapp*. intros pa.

	xchange* <- PArray_Desc_eq_Base. (* TODO : faire fonctionner xclose ? *)
	xchange* <- PArray_eq.
	unfold Shared.
	xchange* (>> Group_add_fresh pa).
	{ apply Heapdata_PArray. }
	{
		(* Lemme Shared M ==+> Inv M. *)
		intros Inv. lets [Inv_closure]: Inv.
		intros Hnot_indom. xsimpl*.
		{ apply* Extend_add_binding. }
		{ constructors*.
			{ intros p Hindom i x q H.
				rewrites* read_update in H. case_if* in H.
				forwards* Clos: Inv_closure H.
				{ forwards* [|]: indom_update_inv Hindom; tryfalse. }
				{ rewrites* (>> indom_update_eq M). } } }
		{ apply IsPArray_Base.
			{ apply* indom_update_same. }
			{ rewrite* read_update_same. } } }
Qed.

Hint Extern 1 (RegisterSpec parray_create) => Provide parray_create_spec.

(* Lemma parray_length_spec : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
	IsPArray M L pa ->
	SPEC (parray_length pa)
		INV (Shared M)
		POST (fun sz => \[sz = length L]).
Admitted. *)

Lemma parray_base_copy_spec : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
	IsPArray M L pa ->
	SPEC (parray_base_copy pa)
		INV (Shared M)
		POST (fun a => a ~> Array L).
Proof using.
	introv Harr. induction Harr; xcf*; xpay_skip.
	{ xchange* (>> focus_shared M pa L).
		{ apply* IsPArray_Base. }
		{ xopen* pa. intros d. xapp*. xcase; cases M[pa].
			{ cases* M[pa]; auto. (* Spec de copy ? *) skip. }
			{ skip. } } }
	{ xchange* (>> focus_shared M pa L).
		{ apply* IsPArray_Diff. }
		{ xopen* pa. intros d. xapp*. xcase.
			{ (* Contradiction ? *) skip. }
			{ xcase.
				{ skip. }
				{ xdone. } } } }
Qed.

Hint Extern 1 (RegisterSpec parray_base_copy) => Provide parray_base_copy_spec.

Lemma parray_rebase_and_get_array_spec : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
	IsPArray M L pa ->
	SPEC (parray_rebase_and_get_array pa)
		INV (Shared M)
		POST (fun a => a ~> Array L \* \[M[pa] = Desc_Base L]).
Admitted.

Hint Extern 1 (RegisterSpec parray_rebase_and_get_array) => Provide parray_rebase_and_get_array_spec.

Lemma parray_get_spec : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A) (i: int),
	IsPArray M L pa ->
	index L i ->
	SPEC (parray_get pa i)
		PRE \[]
		INV (Shared M)
		POST \[= L[i]].
Proof using.
	introv Harr Hind. xcf*. xpay_skip.
	xapp*. intros a H. xapp*. xsimpl*.
Qed.

Hint Extern 1 (RegisterSpec parray_get) => Provide parray_get_spec.

Lemma parray_set_spec : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A) (i: int) (x: A),
	IsPArray M L pa ->
	index L i ->
	SPEC (parray_set pa i x)
		MONO M
		PRE \[]
		POST (fun M' q => \[IsPArray M' (L[i := x]) q]).
Proof using.
	introv Harr Hind. xcf*. simpl. xpay_skip.
	xchange* focus_shared. xopen* pa. intros D.
	xapp*. intros a H. subst.
	xapp*. intros q.
	xappn*. xval.
	xsimpl* M[q := Desc_Base L[i := x]].
	{ apply Extend_add_binding; skip. }
	{ apply IsPArray_Base.
		{ apply* indom_update_same. }
		{ rewrite* read_update_same. } }
	{ xsimpl. }
	(* Déplier le code de set ? *) skip.
Qed.

Hint Extern 1 (RegisterSpec parray_set) => Provide parray_set_spec.

Lemma parray_copy_spec : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
	IsPArray M L pa ->
	SPEC (parray_copy pa)
		MONO M
		PRE (\$1)
		POST (fun M' q => \[IsPArray M' L q]).
Admitted.

Hint Extern 1 (RegisterSpec parray_copy) => Provide parray_copy_spec.
