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
Require Import Mono.

Require Import PArray_simple_ml.



(*************************************************)
(** CFML additions *)






Ltac xcf_pre tt ::=
	intros; match goal with |- TripleMon _ _ _ _ => unfold TripleMon | _ => idtac end.

#[global]
Hint Rewrite @LibMap.dom_update : rew_map.

Hint Rewrite update_same : rew_map.


Ltac set_prove_setup_custom tt :=
	idtac.

Ltac set_prove_setup use_classic ::=
  intros;
  rew_set_tactic tt;
  try set_specialize use_classic;
  rew_set_tactic tt;
  set_prove_setup_custom tt.




Hint Extern 1 (dom _ \c _) => rew_map; set_prove.
(*
Hint Extern 1 (_ \in dom _) => rew_map; saturate_indom; set_prove.
*)
(* match  (?x \indom ?E) *)
Hint Extern 1 (@is_in _ (set _) (in_inst _) ?x (@dom (map _ _) (set _) (dom_inst _ _) ?E)) =>
 rew_map; set_prove.

Hint Extern 1 (?x <> ?y :> loc) =>
	match goal with
	| H1: ?x \in ?E, H2: ~ ?y \in ?E |- _ => intros ->; false
	| H1: ~ ?x \in ?E, H2: ?y \in ?E |- _ => intros ->; false
	end.

Import HintArith.


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


Tactic Notation "tryifalse" :=
	try solve [intros; false].


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

Definition PArray_Desc A {IA: Inhab A} {EA: Enc A} (D: Desc A) (d: parray_desc_ A) : hprop :=
	match d, D with
	|	PArray_Base a, Desc_Base L => a ~> Array L
	|	PArray_Diff p i x, Desc_Diff q j y => \[(p, i, x) = (q, j, y)]
	|	_, _ => \[False]
	end.

Lemma PArray_Desc_eq : forall A (IA: Inhab A) (EA: Enc A) (D: Desc A) (d: parray_desc_ A),
	d ~> PArray_Desc D =
	match d, D with
	|	PArray_Base a, Desc_Base L => a ~> Array L
	|	PArray_Diff p i x, Desc_Diff q j y => \[(p, i, x) = (q, j, y)]
	|	_, _ => \[False]
	end.
Proof using. auto. Qed.

Lemma PArray_Desc_eq_Base : forall A (IA: Inhab A) (EA: Enc A) (D: Desc A) (a: array A),
	(PArray_Base a) ~> PArray_Desc D = \exists L, \[D = Desc_Base L] \* a ~> Array L.
Proof using.
	intros. destruct D; rewrite PArray_Desc_eq.
	{ xsimpl*. intros L E. inverts* E. }
	{ xsimpl*. }
Qed.

Lemma PArray_Desc_eq_Diff : forall A (IA: Inhab A) (EA: Enc A) (D: Desc A) p i x,
	(PArray_Diff p i x) ~> PArray_Desc D = \[D = Desc_Diff p i x].
Proof using.
	intros. destruct D; rewrite PArray_Desc_eq.
	{	xsimpl*. }
	{ xsimpl*; intros H; inverts* H. }
Qed.

Hint Extern 1 (RegisterOpen PArray_Desc) => Provide PArray_Desc_eq.

Lemma haffine_PArray_Desc : forall A (IA: Inhab A) (EA: Enc A) (D: Desc A) (d: parray_desc_ A),
    haffine (d ~> PArray_Desc D).
Proof using. intros. destruct D; destruct d; rewrite PArray_Desc_eq; xaffine. Qed.

Lemma haffine_repr_PArray_Desc : forall A (IA: Inhab A) (EA: Enc A),
    haffine_repr (@PArray_Desc A IA EA).
Proof using. intros. intros ? ?. apply haffine_PArray_Desc. Qed.

Hint Resolve haffine_PArray_Desc haffine_repr_PArray_Desc : haffine.


Definition PArray A {IA: Inhab A} {EA: Enc A} (D: Desc A) (pa: parray_ A) : hprop :=
	\exists d, pa ~~~> `{ data' := d } \* d ~> PArray_Desc D.

Lemma PArray_eq : forall A (IA: Inhab A) (EA: Enc A) (pa: parray_ A) (D: Desc A),
	pa ~> PArray D =
	\exists d, pa ~~~> `{ data' := d } \* d ~> PArray_Desc D.
Proof using. auto. Qed.

Lemma PArray_Base_close : forall A (IA: Inhab A) (EA: Enc A) (pa: parray_ A) (a: array A) (L: list A),
	pa ~~~> `{ data' := PArray_Base a } \* a ~> Array L ==> pa ~> PArray (Desc_Base L).
Proof using. intros. xchange* <- PArray_Desc_eq_Base. xchange* <- PArray_eq. Qed.

Lemma PArray_Diff_close : forall A (IA: Inhab A) (EA: Enc A) (pa: parray_ A) q i x,
	pa ~~~> `{ data' := PArray_Diff q i x } ==> pa ~> PArray (Desc_Diff q i x).
Proof using. intros. xchange* <- PArray_Desc_eq_Diff q i x. xchange* <- PArray_eq. Qed.

Hint Extern 1 (RegisterOpen PArray) => Provide PArray_eq.

Global Instance Heapdata_PArray : forall A (IA: Inhab A) (EA: Enc A),
	Heapdata (PArray (A := A)).
Proof using.
	intros. apply Heapdata_intro. intros.
	do 2 xchange* PArray_eq.
	xchange* Heapdata_record.
Qed.

Hint Resolve Heapdata_PArray.

Lemma haffine_PArray : forall A (IA: Inhab A) (EA: Enc A) (D: Desc A) (pa: parray_ A),
    haffine (pa ~> PArray D).
Proof using. intros. rewrite PArray_eq. xaffine. Qed.

Lemma haffine_repr_PArray : forall A (IA: Inhab A) (EA: Enc A),
    haffine_repr (@PArray A IA EA).
Proof using. intros. intros ? ?. apply haffine_PArray. Qed.

Hint Resolve haffine_PArray haffine_repr_PArray : haffine.


Notation "'Memory' A" := (map (parray_ A) (Desc A)) (at level 69).

Lemma Memory_eq_inv_Base : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L L': list A),
	M[pa] = Desc_Base L -> M[pa] = Desc_Base L' -> L = L'.
Proof using. introv EA E E'. rewrites* E in E'. inverts* E'. Qed.

Lemma Memory_eq_inv_Desc : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) q i x r j y,
	M[pa] = Desc_Diff q i x -> M[pa] = Desc_Diff r j y -> (q, i, x) = (r, j, y).
Proof using. introv EA E E'. rewrites* E in E'. inverts* E'. Qed.

Hint Resolve Memory_eq_inv_Base Memory_eq_inv_Desc.

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

Lemma IsPArray_inv_eq : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L L': list A),
	IsPArray M L pa ->
	IsPArray M L' pa ->
	L = L'.
Proof using.
	introv Rpa. gen L'.
	induction Rpa as [pa L H E | q pa i x L Lq Hq E Rq IH Hi EL]; intros L' Rpa'; inverts* Rpa' as; tryifalse.
	{ intros q' Hpa E' Rq' Hi0.
		forwards* Ediff: Memory_eq_inv_Desc pa E E'. inverts* Ediff.
		forwards*: IH. }
Qed.

Hint Resolve IsPArray_inv_eq.

Lemma IsPArray_inv_neq : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa pa': parray_ A) (L L': list A),
	IsPArray M L pa ->
	IsPArray M L' pa' ->
	L <> L' ->
	pa <> pa'.
Proof using. introv Rpa Rpa' HL <-. forwards*: IsPArray_inv_eq. Qed.

Hint Resolve IsPArray_inv_neq.

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


Lemma indom_of_union_single_neq : forall A (IA: Inhab A) (EA: Enc A) (p q: parray_ A) (M: Memory A),
	p \in (dom M : set loc) \u '{q} ->
	q <> p ->
	p \in (dom M : set loc).
Proof using. introv IA EA [ans | contra] Hneq; [auto | tryfalse]. Qed.

Lemma dom_of_union_single_eq : forall A (IA: Inhab A) (EA: Enc A) (p: parray_ A) (M: Memory A),
	p \in (dom M : set loc) -> dom M = dom M \u '{p}.
Proof using.
	intros. rewrite set_ext_eq. intros q. split.
	{ set_prove. }
	{ intros* [qdom | ->]; auto. }
Qed.

Hint Resolve indom_of_union_single_neq.
#[global]
Hint Rewrite dom_of_union_single_eq : rew_set.


Definition Points_into {A} {IA: Inhab A} {EA: Enc A} (R: set (parray_ A)) (D: Desc A) : Prop :=
	match D with
	|	Desc_Base _ => True
	|	Desc_Diff q _ _ => q \in R
	end.

Lemma Points_into_Base : forall A (IA: Inhab A) (EA: Enc A) (R: set (parray_ A)) (L: list A),
	Points_into R (Desc_Base L).
Proof using. unfold Points_into. auto. Qed.

Lemma Points_into_eq_Diff : forall A (IA: Inhab A) (EA: Enc A) (R: set (parray_ A)) q i x,
	Points_into R (Desc_Diff q i x) = q \in R.
Proof using. unfold Points_into. auto. Qed.

Lemma Points_into_subset : forall A (IA: Inhab A) (EA: Enc A) (R R': set (parray_ A)) (D: Desc A),
	R \c R' -> Points_into R D -> Points_into R' D.
Proof using. introv HR. destruct* D. applys* HR. Qed.

Hint Resolve Points_into_Base Points_into_eq_Diff Points_into_subset.


Definition Points_into_forall A {IA: Inhab A} {EA: Enc A} (R: set (parray_ A)) (M: Memory A) : Prop :=
	forall p, p \indom M -> Points_into R (M[p]).

Lemma Points_into_forall_eq : forall A (IA: Inhab A) (EA: Enc A) (R: set (parray_ A)) (M: Memory A),
	Points_into_forall R M = forall p, p \indom M -> Points_into R (M[p]).
Proof using. auto. Qed.

Lemma Points_into_forall_subset : forall A (IA: Inhab A) (EA: Enc A) (R R': set (parray_ A)) (M: Memory A),
	R \c R' -> Points_into_forall R M -> Points_into_forall R' M.
Proof using. introv HR. unfold Points_into_forall. intros H p Hp. applys* Points_into_subset. Qed.

Lemma Points_into_forall_update :
	forall A (IA: Inhab A) (EA: Enc A) (R: set (parray_ A)) (M: Memory A) (pa: parray_ A) (D: Desc A),
		Points_into_forall R M ->
		Points_into R D ->
		Points_into_forall R (M[pa := D]).
Proof using.
	introv Hforall H. rewrite Points_into_forall_eq. intros p Hp.
	rew_map in *. rewrites* read_update.
	case_if*. applys* Hforall. applys* indom_of_union_single_neq.
Qed.

Hint Resolve Points_into_forall_eq Points_into_forall_update.


Record Inv A {IA: Inhab A} {EA: Enc A} (M: Memory A) : Prop := {
	Inv_closure : Points_into_forall (dom M) M
}.

Lemma Inv_closure_inv : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (p: parray_ A),
	Inv M ->
	p \indom M ->
	Points_into (dom M) (M[p]).
Proof using. introv I Hp. applys* Inv_closure. Qed.

Hint Resolve Inv_closure Inv_closure_inv.


Definition Shared {A} {IA: Inhab A} {EA: Enc A} (M: Memory A) : hprop :=
	Group (PArray (A := A)) M \* \[Inv M].

Lemma Shared_eq : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A),
	Shared M = Group (PArray (A := A)) M \* \[Inv M].
Proof using. auto. Qed.

Lemma Shared_inv_Inv : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A),
	Shared M ==+> \[Inv M].
Proof using. unfold Shared. xsimpl*. Qed.

(* [saturate_indom tt] finds all hypotheses of the form [M[p] = Desc_Diff q i v]
   where [Inv M] is in the context, and produces [q \indom M].
   It leaves [p \indom M] as side-condition, which is expected to be provable. *)

Ltac saturate_indom_step tt :=
	match goal with I: Inv ?M, H: ?M[?p] = Desc_Diff ?q ?i ?v |- _ =>
		let Hp := fresh in
		try (assert (Hp: p \indom M);
		[ clear H (* important to clear to avoid auto to loop *)
    | generalize (@Inv_closure _ _ _ M I p i v q Hp H); intro]);
		clear H (* hypothesis [q \indom M] now part of the context *)
	end.

Ltac saturate_indom tt :=
	repeat (saturate_indom_step tt).

(*Ltac set_prove_setup_custom tt ::=
	saturate_indom tt.*)

Lemma Shared_inv_focus : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
	IsPArray M L pa ->
	Shared M ==>
		\[Inv M] \*
		pa ~> PArray (M[pa]) \*
		\forall D,
			pa ~> PArray D \-*
			\[Points_into (dom M) D] \-*
			Shared (M[pa := D]).
Proof using.
	intros. unfold Shared. xchange* Group_focus pa.
	forwards* Dpa: IsPArray_inv_indom.
	intros I. xsimpl*; intros D.
	{ constructors*.
		{ rewrites* Points_into_forall_eq. intros p Hdom.
			rew_map in *. rewrites* <- dom_of_union_single_eq in *.
			rewrites* read_update. case_if*. } }
	{ xchange* hforall_specialize D. }
Qed.

Lemma Shared_add_fresh_Base : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
  pa ~> PArray (Desc_Base L) \* Shared M
  ==> Shared (M[pa := Desc_Base L]) \* \[pa \notindom M].
Proof using.
	intros. unfold Shared. xchanges* Group_add_fresh.
	intros I Hpa. constructors*.
	{ applys* Points_into_forall_update.
		applys* Points_into_forall_subset (dom M). }
Qed.

Hint Resolve Shared_inv_Inv Shared_add_fresh_Base.


Definition Extend {A} {IA: Inhab A} {EA: Enc A} (M M': Memory A) : Prop :=
	(dom M) \c (dom M') /\ forall L p, IsPArray M L p -> IsPArray M' L p.

Lemma IsPArray_Extend : forall A (IA: Inhab A) (EA: Enc A) (M M': Memory A) p L,
	Extend M M' -> IsPArray M L p -> IsPArray M' L p.
Proof using. introv [_ H] Arr. auto. Qed.

Ltac set_specialize_hyps A x ::=
  repeat match goal with H: forall _:A, _ |- _ =>
    specializes H x
  end.

Lemma Extend_trans : forall A (IA: Inhab A) (EA: Enc A) (M1 M2 M3: Memory A),
	Extend M1 M2 -> Extend M2 M3 -> Extend M1 M3.
Proof using.
	unfold Extend. introv [Hdom1 Harr1] [Hdom2 Harr2]. split*.
Qed.

Lemma Extend_add_fresh : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (D: Desc A),
	~(pa \indom M) ->
	Extend M (M[pa := D]).
Proof using.
	introv H. unfold Extend. split*.
	intros L p Rp. induction Rp.
	{ applys* IsPArray_Base. rew_map*. }
	{ applys* IsPArray_Diff. rew_map*. }
Qed.

Lemma Extend_update_Base : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
	IsPArray M L pa ->
	Extend M (M[pa := Desc_Base L]).
Proof using.
	introv Rpa. unfold Extend.
	split*. intros Lq q Rq. induction Rq as [q Lq Hq E | p q i x Lp Lq Hq E Rp IH Hi EL].
	{ applys* IsPArray_Base. rewrites* read_update. case_if*.
		rewrite <- C in *.
		inverts* Rpa as; tryifalse. intros Hpa E'. rewrites* E in E'. }
	{ tests : (q = pa).
		{	applys* IsPArray_Base. rew_map*.
			forwards* Rpa': IsPArray_Diff p pa.
			fequals*. }
		{ applys* IsPArray_Diff. rew_map*. } }
Qed.

Lemma Extend_update_Diff : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A) q i x,
	index L i ->
	IsPArray M (L[i := x]) pa ->
	q \indom M ->
	q <> pa ->
	M[q] = Desc_Base L ->
	Extend M (M[pa := Desc_Diff q i x]).
Proof using.
	introv Hi Rpa Hq Hdiff Mq. unfold Extend.
	split*. intros Lp p Rp. induction Rp as [p Lp Hp E | r p j y Lr Lp Hp E Rr IH Hj EL].
	{	tests : (p = pa).
		{ applys* IsPArray_Diff q i x L.
			{ rew_map*. }
			{ applys* IsPArray_Base. rew_map*. }
			{ forwards*: IsPArray_Base. } }
		{ applys* IsPArray_Base. rew_map*. } }
	{ tests : (p = pa).
		{ applys* IsPArray_Diff q i x L.
			{ rew_map*. }
			{ applys* IsPArray_Base. rew_map*. }
			{ forwards*: IsPArray_Diff r pa. } }
		{ applys* IsPArray_Diff. rew_map*. } }
Qed.

Hint Resolve IsPArray_Extend Extend_trans Extend_add_fresh Extend_update_Base Extend_update_Diff.


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
	introv Hsz. xcf*. simpl. xpay_skip.
	xapp*. intros a L ->.
	xapp*. intros pa.
	xchange* PArray_Base_close.
	xchanges* Shared_add_fresh_Base; intros Hpa.
	apply* IsPArray_Base. rew_map*.
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
	introv Rpa. lets (n & Rpas): IsPArray_sized_of_unsized Rpa.
	gen pa L. induction_wf IH: wf_lt n.
	introv Rpa. xcf*. xpay_skip.
	xchange* Shared_inv_focus. intros I.
	xopen* pa. intros D. xapp*. xmatch.
	{ xchange* PArray_Desc_eq_Base. intros L' E.
		inverts* Rpas as; tryifalse. intros Hpa E'.
		rewrite E in E'. inverts* E'.
		xapp*. intros q. xsimpl*.
		xchange* PArray_Base_close.
		xchange* hforall_specialize.
		xchange* hwand_hpure_l.
		rewrites* <- E. rew_map*. xsimpl*. }
	{ xchange* PArray_Desc_eq_Diff. intros E.
		inverts Rpas as; tryifalse. intros q Hpa E' Rq Hi.
		rewrite E in E'. inverts* E'.
		xchange* <- PArray_Desc_eq_Diff. xclose* pa.
		xchange* hforall_specialize.
		rewrites* E. rewrites* Points_into_eq_Diff.
		xchange* hwand_hpure_l.
		{ applys* IsPArray_inv_indom. }
		{ rewrites* <- E. rew_map*.
			xapp* IH; try math. intros a. xapp*. xvals*. } }
Qed.

Hint Extern 1 (RegisterSpec parray_base_copy) => Provide parray_base_copy_spec.

Lemma parray_rebase_and_get_array_spec : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
	IsPArray M L pa ->
	SPEC (parray_rebase_and_get_array pa)
		PRE (Shared M)
		POST (fun a =>
			pa ~~~> `{ data' := (PArray_Base (B_ := A)) a } \*
			a ~> Array L \*
			Group (PArray (A := A)) (M \-- pa) \*
			\[Inv M]).
Proof using.
	introv Rpa. xcf*. xpay_skip.
	xchange* Shared_eq. intros I. xchange* Group_rem pa M.
	xopen* pa. intros D. xapp*. xmatch.
	{ xvals*. xchange* PArray_Desc_eq_Base. intros L' E'.
		xsimpl*. inverts Rpa as; tryifalse.
		intros Hpa E. rewrites* E in E'. inverts* E'. }
	{ xclose* pa. xchange* Group_add_again. rew_map*. xchange* <- Shared_eq.
		xapp*. intros a.
		xchange* Shared_eq. intros _. xchange* Group_rem pa M.
		xopen* pa. intros D. xapp*. xvals*. }
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
	xapp*. intros a Points. xapp*.
	xchange* PArray_Base_close.
	xchange* Group_add_again.
	xchanges* <- Shared_eq.
	constructors*.
	{ rew_map*. rewrites* <- dom_of_union_single_eq. }
Qed.

Hint Extern 1 (RegisterSpec parray_get) => Provide parray_get_spec.


Lemma set_in_remove_one_eq : forall A x y (E: set A),
	x \in (E \-- y) = (x \in E /\ x <> y).
Proof using. set_prove. Qed.

Hint Rewrite set_in_remove_one_eq : rew_set.

Hint Rewrite dom_remove : rew_map.

Lemma parray_set_spec : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A) (i: int) (x: A),
	IsPArray M L pa ->
	index L i ->
	SPEC (parray_set pa i x)
		MONO M
		PRE \[]
		POST (fun M' q => \[IsPArray M' (L[i := x]) q]).
Proof using.
	introv Rpa Hi. xcf*. simpl. xpay_skip.
	xapp*. intros a Points. xapp*. xapp*.
	xapp*. intros pb.
	xapp*. xval*.
	xchange* PArray_Diff_close. xchange* PArray_Base_close.
	xchange* (heapdata pa pb). intros Diff.
	xchange* Group_add_fresh. intros Hpb.
	rewrites* update_remove_one_neq.
	xchange* Group_add_again.
	{ forwards*: IsPArray_inv_indom. }
	{ assert (HMpb: Extend M (M[pb := Desc_Base L[i := x]])).
		{ applys* Extend_add_fresh.
			intros H. false Hpb. rew_map*.
			set_prove2.
			(* rew_map i *. set_prove_setup true.
			(* 3 lignes suivantes automatisable ? *)
			rewrites* (>> eq_union_single_remove_one (dom M)).
			intros* [|]; auto.
			rewrites* dom_remove in Hpb. *) }
		xchanges* <- Shared_eq.
		{ constructors*.
			{ rew_map*. applys* Points_into_forall_update.
				{ applys* Points_into_forall_update.
					applys* Points_into_forall_subset (dom M). }
				{ rewrites* Points_into_eq_Diff. set_prove. } } }
		{ applys* Extend_trans.
			applys* Extend_update_Diff pa (L[i := x]).
				{ applys* index_update. }
				{ rew_list. (* ne fait rien ? *) rewrites* update_update_same. rewrites* LibListZ.update_same. }
				{ rew_map*. } }
		{ applys* IsPArray_Base. rewrites* read_update_neq. rew_map*. } }
Qed.

Hint Extern 1 (RegisterSpec parray_set) => Provide parray_set_spec.

Lemma parray_copy_spec : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
	IsPArray M L pa ->
	SPEC (parray_copy pa)
		MONO M
		PRE \[]
		POST (fun M' q => \[IsPArray M' L q]).
Proof using.
	introv Rpa. xcf*. simpl. xpay_skip.
	xapp*. intros a. xapp*. intros q.
	xchange* PArray_Base_close.
	xchanges* Shared_add_fresh_Base; intros Hdom.
	{ applys* IsPArray_Base. rew_map*. }
Qed.

Hint Extern 1 (RegisterSpec parray_copy) => Provide parray_copy_spec.
