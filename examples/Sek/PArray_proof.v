Set Implicit Arguments.
From CFML Require Import LibSepGroup WPLibCredits Stdlib.
From CFML Require Import WPDisplay WPRecord.
Open Scope cf_scope.
Open Scope record_scope.

From TLC Require Import LibListZ LibMap.

From CFML Require Import LibSepTLCbuffer.
Import IndexHints.

Require Import ListMisc.

Require Import PArray_ml.


(*************************************************)
(** CFML additions *)

Ltac xcf_pre tt ::=
	intros; match goal with |- TripleMon _ _ _ _ => unfold TripleMon | _ => idtac end.

#[global]
Hint Rewrite @LibMap.dom_update : rew_map.

Ltac saturate_indom :=
	idtac.

Hint Extern 1 (dom _ \c dom _) => rew_map; set_prove.
Hint Extern 1 (_ \in dom _) => rew_map; saturate_indom; set_prove.
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

Ltac saturate_indom_step :=
	match goal with I: Inv ?M, H: ?M[?p] = Desc_Diff ?q ?i ?v |- _ =>
		let Hp := fresh in
		try (assert (Hp: p \indom M);
		[| generalize (@Inv_closure _ _ _ M I p i v q Hp H); intro]);
		clear H
	end.

Ltac saturate_indom ::=
	repeat saturate_indom_step.

Lemma indom_of_union_single_neq : forall A (IA: Inhab A) (EA: Enc A) (p q: parray_ A) (M: Memory A),
	p \in (dom M : set loc) \u '{q} ->
	q <> p ->
	p \in (dom M: set loc).
Admitted.

Hint Resolve indom_of_union_single_neq.

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
			rew_map in *.
			assert (Hp: p \indom M). { applys* indom_of_union_single_neq. }
			saturate_indom; set_prove. }
		{ rewrites* read_update in E. case_if*.
			{ inverts* E. }
			{ rew_map in *.
				assert (Hp: p \indom M). { applys* indom_of_union_single_neq. }
				saturate_indom; set_prove. } } }
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
	intros L p Rp. induction Rp.
	{ applys* IsPArray_Base. rew_map*. }
	{ applys* IsPArray_Diff. rew_map*. }
Qed.

Lemma Extend_contract : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
	IsPArray M L pa ->
	Extend M (M[pa := Desc_Base L]).
Admitted.

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
		{ rewrites* <- E. rew_map*.
			xapp* IH; try math. intros a. xapp*. xval*. xsimpl*. } }
Qed.

Hint Extern 1 (RegisterSpec parray_base_copy) => Provide parray_base_copy_spec.

Lemma parray_rebase_and_get_array_spec : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
	IsPArray M L pa ->
	SPEC (parray_rebase_and_get_array pa)
		PRE (Shared M)
		POST (fun a =>
			a ~> Array L \*
			\forall L', a ~> Array L' \-* (
				let M' := M[pa := Desc_Base L'] in
				Shared (M') \*
				\[IsPArray M' L' pa])).
Proof using.
	introv Rpa. xcf*. xpay_skip.
	xchange* Shared_inv_focus. intros Inv.
	xopen* pa. intros D. xapp*. skip.
Qed.

Hint Extern 1 (RegisterSpec parray_rebase_and_get_array) => Provide parray_rebase_and_get_array_spec.

Lemma parray_get_spec : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A) (i: int),
	IsPArray M L pa ->
	index L i ->
	SPEC (parray_get pa i)
		MONO M
		PRE \[]
		POST (fun M' x => \[x = L[i]]).
Proof using.
	introv Rpa Hind. xcf*. simpl. xpay_skip.
	xapp*. intros a. xapp*.
	xchange hforall_specialize. intros Rpa'. xsimpl*.
	unfold Extend. split*.
	intros L' p Rp.

	constructors*.
	rew_map in *. left. applys* IsPArray_inv_indom.
	rewrites* read_update. case_if*.
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
