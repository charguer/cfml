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

Require Import PArray_ml.



(*************************************************)
(** CFML additions *)






Ltac xcf_pre tt ::=
	intros; match goal with |- TripleMon _ _ _ _ => unfold TripleMon | _ => idtac end.

#[global]
Hint Rewrite @LibMap.dom_update : rew_map.


Ltac math_0 ::=
	simpl.


Ltac set_prove_setup_custom tt :=
	idtac.

Ltac set_prove_setup use_classic ::=
  intros;
  rew_set_tactic tt;
  try set_specialize use_classic;
  rew_set_tactic tt;
  set_prove_setup_custom tt.



Hint Rewrite update_update_same LibListZ.update_same : rew_list.

Hint Rewrite update_same : rew_map.


Hint Extern 1 (dom _ \c _) => rew_map; set_prove.
(*
Hint Extern 1 (_ \in dom _) => rew_map; saturate_indom; set_prove.
*)
(* match  (?x \indom ?E) *)
Hint Extern 1 (@is_in _ (set _) (in_inst _) ?x (@dom (map _ _) (set _) (dom_inst _ _) ?E)) =>
 rew_map; set_prove.

Hint Extern 1 (?x <> ?y :> loc) =>  (* parray_ _ *)
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


Ltac set_specialize_hyps A x ::=
	repeat match goal with H: forall _:A, _ |- _ =>
		specializes H x
	end.


Tactic Notation "tryifalse" :=
	try solve [intros; false].


Parameter copy_spec : forall A `{EA:Enc A} (xs:list A) t,
  SPEC (Array_ml.copy t)
    INV (t ~> Array xs)
    POST (fun t' => t' ~> Array xs).

Hint Extern 1 (RegisterSpec Array_ml.copy) => Provide copy_spec.


Ltac rew_map_upd :=
	rewrites* read_update; case_if*.



(*************************************************)
(** PArrays *)

(* maximum length of a chain of diff, possibly depending on array size *)
Definition bound A (L: list A) : int := 
  length L.

Lemma bound_pos : forall A (L: list A),
	bound L >= 0.
Proof using. auto. Qed.

Lemma bound_update : forall A (L: list A) i x,
	index L i ->
	bound L[i := x] = bound L. (* swap *)
Proof using. unfold bound. intros. rew_list*. Qed.

Hint Resolve bound_pos bound_update.


(* parray_desc *)
Inductive Desc A :=
  |	Desc_Base : list A -> Desc A 
  |	Desc_Diff : parray_ A -> int -> A -> Desc A.

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

Lemma PArray_Desc_Diff_inv : forall A (IA: Inhab A) (EA: Enc A) (D: Desc A) p i x,
	(PArray_Diff p i x) ~> PArray_Desc D ==+> \[D = Desc_Diff p i x].
Proof using. intros. rewrites* PArray_Desc_eq_Diff. xsimpl*. Qed.

Hint Extern 1 (RegisterOpen PArray_Desc) => Provide PArray_Desc_eq.

Lemma haffine_PArray_Desc : forall A (IA: Inhab A) (EA: Enc A) (D: Desc A) (d: parray_desc_ A),
    haffine (d ~> PArray_Desc D).
Proof using. intros. destruct D; destruct d; rewrite PArray_Desc_eq; xaffine. Qed.

Lemma haffine_repr_PArray_Desc : forall A (IA: Inhab A) (EA: Enc A),
    haffine_repr (@PArray_Desc A IA EA).
Proof using. intros. intros ? ?. apply haffine_PArray_Desc. Qed.

Hint Resolve haffine_PArray_Desc haffine_repr_PArray_Desc : haffine.


Record PArray_Rec A : Type := make_pa_rec {
	desc : Desc A;
	maxdist : int }.

Instance PArray_Rec_inhab A : Inhab A -> Inhab (PArray_Rec A).
Proof using. intros. apply (Inhab_of_val {| desc := arbitrary; maxdist := 0 |}). Qed.

Hint Resolve PArray_Rec_inhab.

Lemma PArray_Rec_eq : forall A (rec: PArray_Rec A),
	rec = {| desc := desc rec; maxdist := maxdist rec |}.
Proof using. intros. destruct* rec. Qed.

Lemma PArray_Rec_eq_desc : forall A (D: Desc A) (md: int),
	desc {| desc := D; maxdist := md |} = D.
Proof using. auto. Qed.

Lemma PArray_Rec_eq_maxdist : forall A (D: Desc A) (md: int),
	maxdist {| desc := D; maxdist := md |} = md.
Proof using. auto. Qed.

Hint Resolve PArray_Rec_eq_desc PArray_Rec_eq_maxdist.
Hint Extern 1 (maxdist (make_pa_rec _ _) <= _) => simpl.

Definition PArray A {IA: Inhab A} {EA: Enc A} (rec: PArray_Rec A) (pa: parray_ A) : hprop :=
	\exists d, pa ~~~> `{ data' := d ; maxdist' := maxdist rec } \* d ~> PArray_Desc (desc rec).

Lemma PArray_eq : forall A (IA: Inhab A) (EA: Enc A) (pa: parray_ A) (rec: PArray_Rec A),
	pa ~> PArray rec =
	\exists d, pa ~~~> `{ data' := d ; maxdist' := maxdist rec } \* d ~> PArray_Desc (desc rec).
Proof using. auto. Qed.

Lemma PArray_Base_close : forall A (IA: Inhab A) (EA: Enc A) (pa: parray_ A) (a: array A) (md: int) (L: list A),
	pa ~~~> `{ data' := PArray_Base a; maxdist' := md } \* a ~> Array L ==>
	pa ~> PArray {| desc := Desc_Base L; maxdist := md |}.
Proof using.
	intros. xchange* <- PArray_Desc_eq_Base.
	xchange* <- PArray_eq {| desc := Desc_Base L; maxdist := md |}.
Qed.

Lemma PArray_Diff_close : forall A (IA: Inhab A) (EA: Enc A) (pa: parray_ A) (md: int) q i x,
	pa ~~~> `{ data' := PArray_Diff q i x; maxdist' := md } ==>
	pa ~> PArray {| desc := Desc_Diff q i x; maxdist := md |}.
Proof using.
	intros. xchange* <- PArray_Desc_eq_Diff q i x.
	xchange* <- PArray_eq {| desc := Desc_Diff q i x; maxdist := md |}.
Qed.

Hint Extern 1 (RegisterOpen PArray) => Provide PArray_eq.

Global Instance Heapdata_PArray : forall A (IA: Inhab A) (EA: Enc A),
	Heapdata (PArray (A := A)).
Proof using.
	intros. apply Heapdata_intro. intros.
	do 2 xchange* PArray_eq.
	xchange* Heapdata_record.
Qed.

Hint Resolve Heapdata_PArray.

Lemma haffine_PArray : forall A (IA: Inhab A) (EA: Enc A) (rec: PArray_Rec A) (pa: parray_ A),
    haffine (pa ~> PArray rec).
Proof using. intros. rewrite PArray_eq. xaffine. Qed.

Lemma haffine_repr_PArray : forall A (IA: Inhab A) (EA: Enc A),
    haffine_repr (@PArray A IA EA).
Proof using. intros. intros ? ?. apply haffine_PArray. Qed.

Hint Resolve haffine_PArray haffine_repr_PArray : haffine.


Notation "'Memory' A" := (map (parray_ A) (PArray_Rec A)) (at level 69).

Lemma Memory_eq_inv_Base : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L L': list A),
	desc (M[pa]) = Desc_Base L -> desc (M[pa]) = Desc_Base L' -> L = L'.
Proof using. introv EA E E'. rewrites* E in E'. inverts* E'. Qed.

Lemma Memory_eq_inv_Desc : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) q i x r j y,
	desc (M[pa]) = Desc_Diff q i x -> desc (M[pa]) = Desc_Diff r j y -> (q, i, x) = (r, j, y).
Proof using. introv EA E E'. rewrites* E in E'. inverts* E'. Qed.

Hint Resolve Memory_eq_inv_Base Memory_eq_inv_Desc.

Inductive IsPArray A {IA: Inhab A} {EA: Enc A} (M: Memory A) : list A -> parray_ A -> Prop :=
	|	IsPArray_Base : forall pa L,
			pa \indom M ->
			desc (M[pa]) = Desc_Base L ->
			maxdist (M[pa]) <= bound L ->
			IsPArray M L pa
	|	IsPArray_Diff : forall pa' pa i x L' L,
			pa \indom M ->
			desc (M[pa]) = Desc_Diff pa' i x ->
			IsPArray M L' pa' ->
			index L' i ->
			L = L'[i := x] ->
			maxdist (M[pa]) < maxdist (M[pa']) ->
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

Lemma IsPArray_inv_maxdist : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
	IsPArray M L pa ->
	maxdist (M[pa]) <= bound L.
Proof using.
	introv Rpa. induction Rpa as [| q pa i x L' L Hpa E Rq IH Hi EL Hdist]; auto.
	forwards* Elen: length_update L' i x.
Qed.

Hint Resolve IsPArray_inv_maxdist.

Section IsPArray_sized.

Inductive IsPArray_sized A {IA: Inhab A} {EA: Enc A} (M: Memory A) : list A -> parray_ A -> nat -> Prop :=
	|	IsPArray_Base_sized : forall pa L,
			pa \indom M ->
			desc (M[pa]) = Desc_Base L ->
			maxdist (M[pa]) <= bound L ->
			IsPArray_sized M L pa 0
	|	IsPArray_Diff_sized : forall pa' pa i x L' L n,
			pa \indom M ->
			desc (M[pa]) = Desc_Diff pa' i x ->
			IsPArray_sized M L' pa' n ->
			index L' i ->
			L = L'[i := x] ->
			maxdist (M[pa]) < maxdist (M[pa']) ->
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
	p \in (dom M : set (parray_ A)) \u '{q} ->
	q <> p ->
	p \in (dom M : set (parray_ A)).
Proof using. introv IA EA [ans | contra] Hneq; [auto | tryfalse]. Qed.

Lemma dom_of_union_single_eq : forall A (IA: Inhab A) (EA: Enc A) (p: parray_ A) (M: Memory A),
	p \in (dom M : set (parray_ A)) -> 
  dom M = dom M \u '{p}.
Proof using.
	intros. rewrite set_ext_eq. intros q. split.
	{ set_prove. }
	{ intros* [qdom | ->]; auto. }
Qed.

Hint Resolve indom_of_union_single_neq.
#[global]
Hint Rewrite dom_of_union_single_eq : rew_set.


Definition Points_into {A} {IA: Inhab A} {EA: Enc A} (R: set (parray_ A)) (rec: PArray_Rec A) : Prop :=
	match desc rec with
	|	Desc_Base _ => True
	|	Desc_Diff q _ _ => q \in R
	end.

Lemma Points_into_Base : forall A (IA: Inhab A) (EA: Enc A) (R: set (parray_ A)) (L: list A) (md: int),
	Points_into R {| desc := Desc_Base L; maxdist := md |}.
Proof using. unfold Points_into. intros. simpls*. Qed.

Lemma Points_into_of_eq_Base : forall A (IA: Inhab A) (EA: Enc A) (R: set (parray_ A)) (rec: PArray_Rec A) (L: list A),
	desc rec = Desc_Base L ->
	Points_into R rec.
Proof using. unfold Points_into. introv IA EA ->. auto. Qed.

Lemma Points_into_eq_Diff : forall A (IA: Inhab A) (EA: Enc A) (R: set (parray_ A)) q i x (md: int),
	Points_into R {| desc := Desc_Diff q i x; maxdist := md |} = q \in R.
Proof using. unfold Points_into. intros. simpls*. Qed.

Lemma Points_into_eq_of_eq_Diff : forall A (IA: Inhab A) (EA: Enc A) (R: set (parray_ A)) (rec: PArray_Rec A) q i x,
	desc rec = Desc_Diff q i x ->
	Points_into R rec = q \in R.
Proof using. unfold Points_into. introv IA EA ->. auto. Qed.

Lemma Points_into_subset : forall A (IA: Inhab A) (EA: Enc A) (R R': set (parray_ A)) (rec: PArray_Rec A),
	R \c R' -> Points_into R rec -> Points_into R' rec.
Proof using. introv HR. lets* [[L | q i x] md]: rec. applys* HR. Qed.

Hint Resolve Points_into_Base Points_into_of_eq_Base Points_into_eq_Diff Points_into_eq_of_eq_Diff Points_into_subset.


Definition Points_into_forall A {IA: Inhab A} {EA: Enc A} (R: set (parray_ A)) (M: Memory A) : Prop :=
	forall p, p \indom M -> Points_into R (M[p]).

Lemma Points_into_forall_eq : forall A (IA: Inhab A) (EA: Enc A) (R: set (parray_ A)) (M: Memory A),
	Points_into_forall R M = forall p, p \indom M -> Points_into R (M[p]).
Proof using. auto. Qed.

Lemma Points_into_forall_subset : forall A (IA: Inhab A) (EA: Enc A) (R R': set (parray_ A)) (M: Memory A),
	R \c R' -> Points_into_forall R M -> Points_into_forall R' M.
Proof using. introv HR. unfold Points_into_forall. intros H p Hp. applys* Points_into_subset. Qed.

Lemma Points_into_forall_update :
	forall A (IA: Inhab A) (EA: Enc A) (R: set (parray_ A)) (M: Memory A) (pa: parray_ A) (rec: PArray_Rec A),
		Points_into_forall R M ->
		Points_into R rec ->
		Points_into_forall R (M[pa := rec]).
Proof using.
	introv Hforall H. rewrite Points_into_forall_eq. intros p Hp.
	rew_map in *. rew_map_upd.
Qed.

Hint Resolve Points_into_forall_eq Points_into_forall_update.


Record Inv A {IA: Inhab A} {EA: Enc A} (M: Memory A) : Prop := {
	Inv_closure : Points_into_forall (dom M) M;
	Inv_dist_pos : forall pa, pa \indom M -> maxdist (M[pa]) >= 0
}.

Lemma Inv_closure_inv : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A),
	Inv M ->
	pa \indom M ->
	Points_into (dom M) (M[pa]).
Proof using. introv I Hpa. applys* Inv_closure. Qed.

Lemma Inv_dist_pos_inv : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A),
	Inv M ->
	pa \indom M ->
	maxdist (M[pa]) >= 0.
Proof using. introv I Hp. applys* Inv_dist_pos. Qed.

Hint Resolve Inv_closure Inv_closure_inv Inv_dist_pos Inv_dist_pos_inv.


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
		\forall rec,
			pa ~> PArray rec \-*
			\[Points_into (dom M) rec] \-*
			\[maxdist rec >= 0] \-*
			Shared (M[pa := rec]).
Proof using.
	intros. unfold Shared. xchange* Group_focus pa.
	forwards* Dpa: IsPArray_inv_indom.
	intros I. xsimpl*; intros rec.
	{ constructors*.
		{ rewrites* Points_into_forall_eq. intros p Hdom.
			rew_map in *. rewrites* <- dom_of_union_single_eq in *.
			rew_map_upd. }
		{ intros p Hp. rew_map in Hp. rew_map_upd. } }
	{ xchange* hforall_specialize rec. }
Qed.

Lemma Shared_add_fresh_Base : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (rec: PArray_Rec A) (L: list A),
  desc rec = Desc_Base L ->
	maxdist rec >= 0 ->
	pa ~> PArray rec \* Shared M 
  ==> Shared (M[pa := rec]) \* \[pa \notindom M].
Proof using.
	intros. unfold Shared. xchanges* Group_add_fresh.
	intros I Hpa. constructors*.
	{ applys* Points_into_forall_update.
		applys* Points_into_forall_subset (dom M). }
	{ intros p Hp. rew_map in Hp. rew_map_upd. }
Qed.

Hint Resolve Shared_inv_Inv Shared_add_fresh_Base.


Definition Extend {A} {IA: Inhab A} {EA: Enc A} (M M': Memory A) : Prop :=
	(dom M) \c (dom M') /\ forall L p, IsPArray M L p -> IsPArray M' L p.

Lemma IsPArray_Extend : forall A (IA: Inhab A) (EA: Enc A) (M M': Memory A) p L,
	Extend M M' -> IsPArray M L p -> IsPArray M' L p.
Proof using. introv [_ H] Arr. auto. Qed.

Lemma Extend_trans : forall A (IA: Inhab A) (EA: Enc A) (M1 M2 M3: Memory A),
	Extend M1 M2 -> Extend M2 M3 -> Extend M1 M3.
Proof using.
	unfold Extend. introv [Hdom1 Harr1] [Hdom2 Harr2]. split*.
Qed.

Lemma Extend_add_fresh : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (rec: PArray_Rec A),
	~(pa \indom M) ->
	Extend M (M[pa := rec]).
Proof using.
	introv H. unfold Extend. split*.
	intros L p Rp. induction Rp.
	{ applys* IsPArray_Base; rew_map*. }
	{ applys* IsPArray_Diff; rew_map*. forwards*: IsPArray_inv_indom M pa'. }
Qed.

Lemma Extend_update_Base : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (rec: PArray_Rec A) (L: list A),
	IsPArray M L pa ->
	desc rec = Desc_Base L ->
	maxdist (M[pa]) <= maxdist rec ->
	maxdist rec <= bound L ->
	Extend M (M[pa := rec]).
Proof using.
	introv Rpa HD Hlb Hub. unfold Extend.
	split*. intros Lq q Rq. induction Rq as [q Lq Hq E | p q i x Lp Lq Hq E Rp IH Hi EL].
	{ applys* IsPArray_Base; rewrites* read_update; case_if*;
		rewrite <- C in *;
		inverts* Rpa as; tryifalse; intros Hpa E' Hdist'; rewrites* E in E'.
		{ rewrites* HD. }
		{ inverts* E'. } }
	{ tests : (q = pa).
		{	applys* IsPArray_Base; rew_map*;
			forwards* Rpa': IsPArray_Diff p pa; forwards* EL': IsPArray_inv_eq M pa (Lp[i := x]) L. substs*. auto. }
		{ applys* IsPArray_Diff.
			{ rew_map*. }
			{ rewrites* (>> read_update p). case_if*; rew_map*. } } }
Qed.

Lemma Extend_update_Diff : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (rec: PArray_Rec A) (L: list A) q i x,
	index L i ->
	IsPArray M (L[i := x]) pa ->
	q <> pa ->
	desc (M[q]) = Desc_Base L ->
	IsPArray M L q ->
	desc rec = Desc_Diff q i x ->
	maxdist (M[pa]) <= maxdist rec ->
	maxdist rec < maxdist (M[q]) ->
	Extend M (M[pa := rec]).
Proof using.
	introv Hi Rpa Hdiff Mq Rq HD Hlb Hub. unfold Extend.
	split*. intros Lp p Rp. induction Rp as [p Lp Hp E | r p j y Lr Lp Hp E Rr IH Hj EL].
	{	tests : (p = pa).
		{ applys* IsPArray_Diff q i x L; rew_map*.
			{ applys* IsPArray_Base; rew_map*. rew_set. left*. }
			{ forwards*: IsPArray_Base. } }
		{ applys* IsPArray_Base; rew_map*. } }
	{ tests : (p = pa).
		{ applys* IsPArray_Diff q i x L; rew_map*.
			{ applys* IsPArray_Base; rew_map*. rew_set. left*. }
			{ forwards*: IsPArray_Diff r pa. } }
		{ applys* IsPArray_Diff.
			{ rew_map*. }
			{ rewrites* (>> read_update r). case_if*; rew_map*. } } }
Qed.

Hint Resolve IsPArray_Extend Extend_trans Extend_add_fresh Extend_update_Base Extend_update_Diff.


Instance MonType_Memory A {IA: Inhab A} {EA: Enc A} :
	MonType (Memory A) :=	make_MonType (Shared) (Extend).


Definition IsBase A {IA: Inhab A} {EA: Enc A} (M: Memory A) (pa: parray_ A) : Prop :=
	exists L, desc (M[pa]) = Desc_Base L.

Definition IsHead A {IA: Inhab A} {EA: Enc A} (M: Memory A) (pa: parray_ A) : hprop :=
	\[IsBase M pa] \* \$(maxdist (M[pa])).

Lemma IsHead_eq : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A),
	IsHead M pa =
	\[exists L, desc (M[pa]) = Desc_Base L] \* \$(maxdist (M[pa])).
Proof using. auto. Qed.

Lemma IsHead_eq_base : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
	desc (M[pa]) = Desc_Base L ->
	IsHead M pa = \$(maxdist (M[pa])).
Proof using. introv E. rewrites* IsHead_eq. xsimpl*. Qed.

Lemma IsHead_eq_diff : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) q i x,
	desc (M[pa]) = Desc_Diff q i x ->
	IsHead M pa = \[False].
Proof using. introv E. rewrites* IsHead_eq. xpull. intros [L contra]. false. Qed.

Hint Resolve IsHead_eq_base IsHead_eq_diff.

Lemma haffine_IsHead : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A),
	maxdist (M[pa]) >= 0 ->
	haffine (IsHead M pa).
Proof using. intros. rewrite IsHead_eq. xaffine*. Qed.

Hint Resolve haffine_IsHead : haffine.

	(*************************************************)
(** Specifications *)

Lemma dist_bound_spec : forall A (IA: Inhab A) (EA: Enc A) (a: array A) (L: list A),
	SPEC (dist_bound a)
		PRE (\$1)
		INV (a ~> Array L)
		POST \[= bound L].
Proof using. xcf*. xpay. xapp*. xsimpl*. Qed.

Hint Extern 1 (RegisterSpec dist_bound) => Provide dist_bound_spec.

Lemma parray_create_spec : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (sz: int) (d: A),
	sz >= 0 ->
	SPEC (parray_create sz d)
		MONO M
		PRE (\$(sz + 1))
		POST (fun M' pa => \[IsPArray M' (make sz d) pa] \* IsHead M' pa).
Proof using.
	introv Hsz. xcf*. simpl. xpay.
	xapp*. intros a L ->.
	xapp*. intros pa.
	xchange* PArray_Base_close.
	xchanges* Shared_add_fresh_Base (make sz d); intros Hpa.
	{ apply* IsPArray_Base; rew_map*. }
	{ rewrites* IsHead_eq. rew_map*. xsimpl*. }
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
		PRE (\$(length L + bound L - maxdist (M[pa]) + 1))
		INV (Shared M)
		POST (fun a => a ~> Array L).
Proof using.
	introv Rpa. lets (n & Rpas): IsPArray_sized_of_unsized Rpa.
	gen pa L. induction_wf IH: wf_lt n.
	introv Rpa. xcf*. xpay.
	xchange* Shared_inv_focus. intros I.
	xopen* pa. intros D. xapp*. xmatch.
	{ xchange* PArray_Desc_eq_Base. intros L' E.
		inverts* Rpas as; tryifalse. intros Hpa E' Hub.
		rewrite E in E'. inverts* E'.
		xapp*. intros q. xsimpl*.
		xchange* PArray_Base_close.
		xchange* hforall_specialize.
		do 2 xchange* hwand_hpure_l; simpls*. rewrites* <- E.
		rewrites* <- PArray_Rec_eq. rew_map*. xsimpl*. }
	{ xchange* PArray_Desc_eq_Diff. intros E.
		inverts Rpas as; tryifalse. intros q Hpa E' Rq Hi Hdist.
		rewrite E in E'. inverts* E'.
		xchange* <- PArray_Desc_eq_Diff. xclose* pa.
		xchange* hforall_specialize.
		do 2 xchange* hwand_hpure_l; simpls*. rew_map*.
		xapp* IH; try math. intros a. xapp*. xvals*. }
Qed.

Hint Extern 1 (RegisterSpec parray_base_copy) => Provide parray_base_copy_spec.

Definition parray_rebase_and_get_array_cost A {IA: Inhab A} {EA: Enc A}  (ishd: bool) (M: Memory A) (pa: parray_ A) (L: list A) : hprop := 
  if ishd then IsHead M pa \* \$1 else \$(length L + bound L + 2).

Lemma parray_rebase_and_get_array_spec : forall A (IA: Inhab A) (EA: Enc A) (ishd: bool) (M: Memory A) (pa: parray_ A) (L: list A),
	IsPArray M L pa ->
	SPEC (parray_rebase_and_get_array pa)
		PRE (Shared M \* parray_rebase_and_get_array_cost ishd M pa L)
		POST (fun a =>
			pa ~~~> `{ data' := (PArray_Base (B_ := A)) a; maxdist' := maxdist (M[pa]) } \*
			a ~> Array L \*
			Group (PArray (A := A)) (M \-- pa) \*
			\[Inv M] \*
			(if ishd then IsHead M pa else \$(maxdist (M[pa])))).
Proof using.
	introv Rpa. unfold parray_rebase_and_get_array_cost. xcf*. xpay.
	xchange* Shared_eq. intros I. xchange* Group_rem pa M.
	xopen* pa. intros D. xapp*. xmatch.
	{ xchange* PArray_Desc_eq_Base. intros L' E'.
		xvals*.
		{ inverts Rpa as; tryifalse.
			intros Hpa E Hdist. applys* Memory_eq_inv_Base. }
		{ case_if*; xsimpl*. forwards*: IsPArray_inv_maxdist. } }
	{	xchange* PArray_Desc_Diff_inv. intros E'.
		xclose* pa. xchange* Group_add_again. rew_map*. xchange* <- Shared_eq.
		xapp*. intros a.
		xchange* Shared_eq. intros _. xchange* Group_rem pa M.
		xopen* pa. intros D. xapp*. xvals*.
		case_if*.
		{ xchange* IsHead_eq_diff. }
		{ xsimpl*. } }
Qed.

Hint Extern 1 (RegisterSpec parray_rebase_and_get_array) => Provide parray_rebase_and_get_array_spec.

Lemma parray_get_spec : forall A (IA: Inhab A) (EA: Enc A) (ishd: bool) (M: Memory A) (pa: parray_ A) (L: list A) (i: int),
	IsPArray M L pa ->
	index L i ->
	SPEC (parray_get pa i)
		MONO M
		PRE (\$1 \* parray_rebase_and_get_array_cost ishd M pa L)
		POST (fun M' x => \[x = L[i]] \* IsHead M' pa).
Proof using.
	introv Rpa Hind. xcf*. simpl. xpay.
	xapp*. intros a I. xapp*.
	xchange* PArray_Base_close.
	xchange* Group_add_again.
	xchanges* <- Shared_eq.
	{ constructors*.
	  { rew_map*. rewrites* <- dom_of_union_single_eq. }
	  { intros p Hp. rew_map in Hp. rew_map_upd; applys* Inv_dist_pos_inv. } }
  { setoid_rewrite IsHead_eq_base at 2; rew_map*. case_if*.
		{	rewrites* IsHead_eq. xsimpl*. }
		{ xsimpl*. } }
Qed.

Hint Extern 1 (RegisterSpec parray_get) => Provide parray_get_spec.

Ltac xif_pre tt ::=
  xif_xmatch_pre tt;
  match xgoal_code_without_wptag tt with
	| (Wpgen_if ?cond _ _) =>
		match goal with
		|	H: cond = _ |- _ => rewrite H (* inline condition for case analysis *)
		|	_ => idtac
		end
  end.

Lemma parray_set_spec : forall A (IA: Inhab A) (EA: Enc A) (ishd: bool) (M: Memory A) (pa: parray_ A) (L: list A) (i: int) (x: A),
	IsPArray M L pa ->
	index L i ->
	SPEC (parray_set pa i x)
		MONO M
		PRE (\$3 \* parray_rebase_and_get_array_cost ishd M pa L)
		POST (fun M' q => \[IsPArray M' (L[i := x]) q] \* IsHead M' q).
Proof using.
	introv Rpa Hi. xcf*. simpl. xpay.
	xapp*. intros a I. xapp*. xapp*.
	xif; intros C.
	{ xapp*. intros b. xapp*. xapp*. intros pb.
		do 2 xchange* PArray_Base_close.
		xchange* Group_add_again pa.
		xchange* Group_add_fresh. intros Hpb.
		xchanges* <- Shared_eq.
		{ constructors*; rew_map*.
			{ do 2 applys* Points_into_forall_update.
				applys* Points_into_forall_subset (dom M). }
			{ intros p Hp. rew_map_upd; rew_map_upd. applys* Inv_dist_pos. set_prove2. } }
		{ applys* Extend_trans. applys* Extend_update_Base. }
		{ applys* IsPArray_Base; rew_map*. }
		{ setoid_rewrite IsHead_eq_base at 2; rew_map*. case_if*; xsimpl*. } }
	{ xapp*. xapp*. xapp*. xapp*. intros pb. xapp*. xval*.
		xchange* PArray_Diff_close. xchange* PArray_Base_close.
		xchange* (heapdata pa pb). intros Diff.
		xchange* Group_add_fresh. intros Hpb.
		rewrites* update_remove_one_neq.
		xchange* Group_add_again.
		{ forwards*: IsPArray_inv_indom pa. }
		{ assert (HMpb: Extend M (M[pb := {| desc := Desc_Base L[i := x]; maxdist := maxdist (M[pa]) + 1 |}])).
			{ applys* Extend_add_fresh.
				(* 3 lignes suivantes automatisable ? *)
				rewrites* (>> eq_union_single_remove_one (dom M)).
				intros* [|]; auto.
				rewrites* dom_remove in Hpb. }
			xchanges* <- Shared_eq.
			{ constructors*; rew_map*.
				{ applys* Points_into_forall_update.
					{ applys* Points_into_forall_update.
						applys* Points_into_forall_subset (dom M). }
					{ rewrites* Points_into_eq_Diff. set_prove. } }
				{ intros p Hp. rew_map_upd.
					{ applys* Inv_dist_pos. }
					{ rew_map_upd.
						{ forwards*: Inv_dist_pos pa. }
						{ applys* Inv_dist_pos. set_prove2. } } } }
			{ applys* Extend_trans.
				applys* Extend_update_Diff pa (L[i := x]) i (L[i]); rew_map*.
					{ applys* index_update. }
					{ applys* IsPArray_Base; rew_map*. forwards*: IsPArray_inv_maxdist pa. } }
			{ applys* IsPArray_Base; rewrites* read_update_neq; rew_map*. forwards*: IsPArray_inv_maxdist pa. }
			{ setoid_rewrite IsHead_eq_base at 2; rewrites* read_update_neq; rew_map*. case_if*.
				{ rewrite IsHead_eq. xsimpl*. }
				{ xsimpl*. } } } }
Qed.

Hint Extern 1 (RegisterSpec parray_set) => Provide parray_set_spec.

Lemma parray_copy_spec : forall A (IA: Inhab A) (EA: Enc A) (M: Memory A) (pa: parray_ A) (L: list A),
	IsPArray M L pa ->
	SPEC (parray_copy pa)
		MONO M
		PRE (\$(length L + bound L + 2))
		POST (fun M' q => \[IsPArray M' L q] \* IsHead M' q).
Proof using.
	introv Rpa. xcf*. simpl. xpay.
	xchange* Shared_inv_Inv. intros I. (* Needed later *)
	xapp*. intros a. xapp*. intros q.
	xchange* PArray_Base_close.
	xchanges* Shared_add_fresh_Base L; intros Hdom.
	{ applys* IsPArray_Base; rew_map*. }
	{ rewrites* IsHead_eq. rew_map*. xsimpl*. }
Qed.

Hint Extern 1 (RegisterSpec parray_copy) => Provide parray_copy_spec.
