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

#[global]
Hint Rewrite @LibMap.dom_update : rew_map.

Hint Extern 1 (dom _ \c dom _) => rew_map; set_prove.
Hint Extern 1 (_ \in dom _) => rew_map; set_prove.
Hint Extern 1 (?x <> ?y :> loc) => 
	match goal with 
	| H1: ?x \in ?E, H2: ~ ?y \in ?E |- _ => intros ->; false 
	| H1: ~ ?x \in ?E, H2: ?y \in ?E |- _ => intros ->; false 
	end.

Lemma xsimpl_l_false : forall Nc Hla Hlw Hlt HR,
  Xsimpl (Nc, Hla, Hlw, (\[False] \* Hlt)) HR.
Proof using.
	intros. apply xsimpl_l_hpure. intros. false.
Qed.

Ltac xsimpl_step_l tt ::=
	match goal with |- Xsimpl ?HL ?HR =>
	match HL with
	| (?Nc, ?Hla, ?Hlw, (?H \* ?Hlt)) =>
		match H with
		| \[] => apply xsimpl_l_hempty
		| \[False] => apply xsimpl_l_false
		| \[?P] => apply xsimpl_l_hpure; intro
		| \$ ?n => apply xsimpl_l_hcredits
		| ?H1 \* ?H2 => rewrite (@hstar_assoc H1 H2)
		| hexists ?J => apply xsimpl_l_hexists; intro
		| ?H1 \-* ?H2 => apply xsimpl_l_acc_hwand
		| ?Q1 \--* ?Q2 => apply xsimpl_l_acc_hwand
		| _ => apply xsimpl_l_acc_other
		end
	| (?Nc, ?Hla, ((?H1 \-* ?H2) \* ?Hlw), \[]) =>
			match H1 with
			| \[] => apply xsimpl_l_cancel_hwand_hempty
			| \$ ?n => apply xsimpl_l_hwand_hcredits
			| (_ \* _) => xsimpl_hwand_hstars_l tt
			| _ => first [ xsimpl_pick_same H1; apply xsimpl_l_cancel_hwand
									 | apply xsimpl_l_keep_wand ]
			end
	| (?Nc, ?Hla, ((?Q1 \--* ?Q2) \* ?Hlw), \[]) =>
			first [ xsimpl_pick_applied Q1; eapply xsimpl_l_cancel_qwand
						| apply xsimpl_l_keep_wand ]
	end end.

Ltac set_prove2 := (* set_prove fails sometimes *)
	set_prove_setup false; intuition.


Parameter copy_spec : forall A `{EA:Enc A} (xs:list A) t,
  SPEC (Array_ml.copy t)
    INV (t ~> Array xs)
    POST (fun t' => t' ~> Array xs).

Hint Extern 1 (RegisterSpec Array_ml.copy) => Provide copy_spec.



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
	(PArray_Base a) ~> PArray_Desc D = \exists L, \[D = Desc_Base L] \* a ~> Array L.
Proof using.
	intros. destruct D; rewrite PArray_Desc_eq.
	{ xsimpl*. intros L E. inverts* E. }
	{ xsimpl*. }
Qed.

Lemma PArray_Desc_eq_Diff : forall A (EA: Enc A) (D: Desc A) p i x,
	(PArray_Diff p i x) ~> PArray_Desc D = \[D = Desc_Diff p i x].
Proof using.
	intros. destruct D; rewrite PArray_Desc_eq.
	{	xsimpl*. }
	{ xsimpl*; intros H; inverts* H. }
Qed.


Hint Extern 1 (RegisterOpen PArray_Desc) => Provide PArray_Desc_eq.


Definition PArray A {EA: Enc A} (D: Desc A) (pa: parray_ A) : hprop :=
	\exists d, pa ~~~> `{ data' := d } \* d ~> PArray_Desc D.

Lemma PArray_eq : forall A (pa: parray_ A) (EA: Enc A) (D: Desc A),
	pa ~> PArray D =
	\exists d, pa ~~~> `{ data' := d } \* d ~> PArray_Desc D.
Proof using. auto. Qed.

Lemma PArray_Base_close : forall A (EA: Enc A) (pa: parray_ A) (a: array A) (L: list A),
	pa ~~~> `{ data' := PArray_Base a } \* a ~> Array L ==> pa ~> PArray (Desc_Base L).
Proof using. intros. xchange* <- PArray_Desc_eq_Base. xchange* <- PArray_eq. Qed.


Hint Extern 1 (RegisterOpen PArray) => Provide PArray_eq.

Global Instance Heapdata_PArray : forall A (EA: Enc A),
	Heapdata (PArray (A := A)).
Proof using.
	intros. apply Heapdata_intro. intros.
	do 2 xchange* PArray_eq.
	xchange* Heapdata_record.
Qed.

Hint Resolve Heapdata_PArray.


Notation "'Memory' A" := (map (parray_ A) (Desc A)) (at level 69).

Inductive IsPArray A {IA: Inhab A} {EA: Enc A} (M: Memory A) : list A -> parray_ A -> Prop :=
	|	IsPArray_Base : forall pa L,
			pa \indom M ->
			M[pa] = Desc_Base L ->
			IsPArray M L pa
	|	IsPArray_Diff : forall pa' pa i x L' L,
			pa \indom M ->
			M[pa] = Desc_Diff pa' i x ->
			IsPArray M L' pa' ->
			index L' i ->
			L = L'[i := x] ->
			IsPArray M L pa.

Lemma IsPArray_inv_indom : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
	IsPArray M L pa ->
	pa \indom M.
Proof using. intros. inverts* H. Qed.

Hint Resolve IsPArray_inv_indom.

Section IsPArray_sized.

Inductive IsPArray_sized A {IA: Inhab A} {EA: Enc A} (M: Memory A) : list A -> parray_ A -> nat -> Prop :=
	|	IsPArray_Base_sized : forall pa L,
			pa \indom M ->
			M[pa] = Desc_Base L ->
			IsPArray_sized M L pa 0
	|	IsPArray_Diff_sized : forall pa' pa i x L' L n,
			pa \indom M ->
			M[pa] = Desc_Diff pa' i x ->
			IsPArray_sized M L' pa' n ->
			index L' i ->
			L = L'[i := x] ->
			IsPArray_sized M L pa (S n).

Hint Constructors IsPArray IsPArray_sized.

Lemma IsPArray_sized_of_unsized : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (L: list A) (pa: parray_ A),
	IsPArray M L pa -> exists n, IsPArray_sized M L pa n.
Proof using. introv H. induction* H. Qed.

Lemma IsPArray_unsized_of_sized : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (L: list A) (pa: parray_ A) (n: nat),
	IsPArray_sized M L pa n -> IsPArray M L pa.
Proof using. introv H. induction* H. Qed.

End IsPArray_sized.

Hint Resolve IsPArray_unsized_of_sized.


Record Inv A {IA: Inhab A} {EA: Enc A} (M: Memory A) : Prop := {
	Inv_closure : forall p i v q,
		p \indom M ->
		M[p] = Desc_Diff q i v ->
		q \indom M
}.

Definition Points_into {A} {IA: Inhab A} {EA: Enc A} (M: Memory A) (D: Desc A) : Prop :=
	match D with
	|	Desc_Base _ => True
	|	Desc_Diff q _ _ => q \indom M
	end.

Lemma Points_into_Base : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (L: list A),
	Points_into M (Desc_Base L).
Proof using. unfold Points_into. auto. Qed.

Lemma Points_into_eq_Diff : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) q i x,
	Points_into M (Desc_Diff q i x) = q \indom M.
Proof using. unfold Points_into. auto. Qed.

Hint Resolve Points_into_Base Points_into_eq_Diff.


Definition Shared {A} {IA: Inhab A} {EA: Enc A} (M: Memory A) : hprop :=
	Group (PArray (A := A)) M \* \[Inv M].

Lemma Shared_inv_Inv : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A),
	Shared M ==+> \[Inv M].
Proof using. unfold Shared. xsimpl*. Qed.

Lemma Shared_inv_focus : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
	IsPArray M L pa ->
	Shared M ==>
		\[Inv M] \*
		pa ~> PArray (M[pa]) \*
		\forall D,
			pa ~> PArray D \-*
			\[Points_into M D] \-*
			Shared (M[pa := D]).
Proof using.
	intros. unfold Shared. xchange* (>> Group_focus pa).
	intros Inv. xsimpl*; intros D.
	{ destruct D; intros C; constructors*; intros p i v q Hdom E.
		{ rewrites* read_update in E. case_if*.
			rew_map in *. forwards*: Inv_closure p; [set_prove2 | set_prove]. }
		{ rewrites* read_update in E. case_if*.
			{ inverts* E. }
			{ rew_map in *. forwards*: Inv_closure p; [set_prove2 | set_prove]. } } }
	{ xchange* (>> hforall_specialize D). }
Qed.

Lemma Shared_add_fresh_Base : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
	pa ~> PArray (Desc_Base L) \* Shared M ==> Shared (M[pa := Desc_Base L]) \* \[pa \notindom M].
Proof using.
	skip.
Qed.

Lemma Shared_add_fresh_Diff : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) q i x,
	pa ~> PArray (Desc_Diff q i x) \* \[q \indom M] \* Shared M ==> Shared (M[pa := Desc_Diff q i x]) \* \[pa \notindom M].
Proof using.
	skip.
Qed.


Definition Extend {A} {IA: Inhab A} {EA: Enc A} (M M': Memory A) : Prop :=
	(dom M) \c (dom M') /\ forall L p, IsPArray M L p -> IsPArray M' L p.

Lemma IsPArray_extend : forall A (IA: Inhab A) (EA: Enc A) (M M': Memory A) p L,
	Extend M M' -> IsPArray M L p -> IsPArray M' L p.
Proof using. introv [_ H] Arr. auto. Qed.

Lemma Extend_id : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A),
	Extend M M.
Proof using. unfold Extend. auto. Qed.

Lemma Extend_add_fresh : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (D: Desc A),
	~(pa \indom M) ->
		Extend M (M[pa := D]).
Proof using.
	introv H. unfold Extend. split*.
	{ intros L p Rp. induction Rp.
		{ applys* IsPArray_Base. rew_map*. }
		{ applys* IsPArray_Diff. rew_map*. } }
Qed.

Instance MonType_Memory A {IA: Inhab A} {EA: Enc A} :
	MonType (Memory A) :=	make_MonType (Shared) (Extend).

(*************************************************)
(** Specifications *)

(* Laisser tel quel *)
Lemma parray_create_spec : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (sz: int) (d: A),
	sz >= 0 ->
	SPEC (parray_create sz d)
		MONO M
		PRE \[]
		POST (fun M' pa => \[IsPArray M' (make sz d) pa]).
Proof using.
	introv Hsz. xcf*. simpl.
	xpay_skip.
	xapp*. intros a L ->.
	xapp*. intros pa.
	xchange* PArray_Base_close.
	xchanges* Shared_add_fresh_Base; intros Hpa.
	{ apply* Extend_add_fresh. }
	{ apply* IsPArray_Base. rew_map*. }
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
	introv Rpa. lets (n&Rpas): IsPArray_sized_of_unsized Rpa.
	gen pa L. induction_wf IH: wf_lt n.
	introv Rpa. xcf*. xpay_skip.
	xchange* Shared_inv_focus. intros Inv.
	xopen* pa. intros D. xapp*. xmatch.
	{ xchange* PArray_Desc_eq_Base. intros L' E.
		inverts* Rpas; tryfalse.
		rewrite E in H0. inverts* H0.
		xapp*. intros q. xsimpl*.
		xchange* PArray_Base_close.
		xchange* hforall_specialize.
		xchange* hwand_hpure_l.
		rewrites* <- E. rew_map*. xsimpl*. }
	{ xchange* PArray_Desc_eq_Diff. intros E.
		inverts Rpas; tryfalse.
		rewrite E in H0. inverts* H0.
		xchange* <- PArray_Desc_eq_Diff. xclose* pa.
		xchange* hforall_specialize.
		rewrites* E. rewrites* Points_into_eq_Diff.
		xchange* hwand_hpure_l.
		{ applys* Inv_closure Inv. }
		{ rewrites* <- E. rew_map*.
			xapp* IH; try math. intros a. xapp*. xval*. xsimpl*. } }
Qed.

Hint Extern 1 (RegisterSpec parray_base_copy) => Provide parray_base_copy_spec.

Lemma parray_rebase_and_get_array_spec : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
	IsPArray M L pa ->
	SPEC (parray_rebase_and_get_array pa)
		MONO M
		PRE \[]
		POST (fun M' a =>
			a ~> Array L \*
			\[IsPArray M' L pa] \*
			\[M'[pa] = Desc_Base L]).
Proof using.
	introv Rpa. xcf*. xpay_skip.
	xchange* Shared_inv_focus. intros Inv.
	xopen* pa. intros D. xapp*. xmatch.
	{ xval*.
		xchange* PArray_Desc_eq_Base.
		intros L' E.
		inverts* Rpa; tryfalse.
		rewrite E in H0. inverts* H0.
		xsimpl*.
		(* xchange* PArray_Base_close. *)
		xchange* (hforall_specialize (M[pa])).
		rewrites* E.
		xchange* hwand_hpure_l.
		rewrites* <- E. rew_map*.
		xsimpl*. }
Qed.

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
	skip.
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
