Set Implicit Arguments.
From CFML Require Import LibSepGroup WPLib Stdlib.
From CFML Require Import WPRecord.
Open Scope cf_scope.
Open Scope record_scope.
(*From CFML Require Import WPDisplay WPRecord.
Open Scope cf_scope.
Open Scope record_scope.*)

From TLC Require Import LibListZ LibMap.
Import LibListNotation.

From CFML Require Import LibSepTLCbuffer.
Import IndexHints.

Require Import ListMisc.

From CFML Require Import Array_proof.

Require Import Capacity_ml.
Require Import Weighted_ml.
Require Import View_ml.
Require Import Owner_ml.
Require Import SWChunk_ml.
Require Import SWSek_ml.
Require Import Capacity_proof.
Require Import Weighted_proof.
Require Import View_proof.
Require Import Owner_proof.
Require Import SChunk_proof.
Require Import SWChunk_proof.
Require Import SWChunkOf.



(* Copy from Common_proof.v in the ChunkedSeq directory. *)
Lemma cons_eq_last_inv : forall A x1 (x2:A) l1 l2, 
  x1::l1 = l2&x2 ->
  ((l1 = nil /\ l2 = nil /\ x1 = x2)  
  \/ (exists l2', l2 = x1::l2' /\ l1 = l2'&x2)).
Proof. introv E. destruct l2; rew_list in E; inverts* E. Qed.

Inductive ForallConseq (A:Type) (P:A->A->Prop) : list A -> Prop :=
  | ForallConseq_nil : 
     ForallConseq P nil
  | ForallConseq_one : forall x,
     ForallConseq P (x::nil) 
  | ForallConseq_next : forall x y L,
     P x y -> ForallConseq P (y::L) -> ForallConseq P (x::y::L).

Section ForallConseqLemmas.
Hint Constructors ForallConseq.

Lemma ForallConseq_last : forall A (P:A->A->Prop) x y L,
  P y x -> ForallConseq P (L&y) -> ForallConseq P (L&y&x).
Proof.
  introv Pyx H. induction L; rew_list in *.
	constructors~.
  inverts H as.
    intros E. false* nil_eq_last_inv.
    introv M1 M2 M3. lets [ (?&?&?) | (?&?&?)]: (>> cons_eq_last_inv M3).
    subst. rew_list. auto.
    subst. rew_list. auto.
Qed.

Lemma ForallConseq_last_inv : forall A (P:A->A->Prop) x y L,
  ForallConseq P (L&x&y) ->
  P x y /\ ForallConseq P (L&x).
Proof.
  introv M. induction L; rew_list in *.
  inverts~ M.
  inverts M as.
    intros E. false. forwards* (?&?): nil_eq_app_inv E. false.
    introv M1 M2 E. destruct L.
      rew_list in E. inverts E. inverts M2. rew_list. splits~.
      rew_list in E. inverts E. rew_list in *.
       forwards (?&?): IHL M2. splits~.
Qed.


Lemma ForallConseq_concat : forall A (P:A->A->Prop) x y L1 L2,
  P x y -> ForallConseq P (L1&x) -> ForallConseq P (y::L2) -> 
  ForallConseq P (L1&x ++ y::L2).
Proof.
  introv Pyx H1 H2. sets_eq L0: (L1 & x). gen L1.
  induction H1; intros; rew_list in *.
  false* nil_eq_last_inv.
  destruct L1; rew_list in *; inverts EQL0.
    constructors~.
    false* nil_eq_last_inv.
  destruct L1; rew_list in *; inverts EQL0. forwards*: IHForallConseq.
Qed.

Lemma ForallConseq_cons_fuse : forall A (P:A->A->Prop) y z L,
  (forall a, P y a -> P z a) ->
  ForallConseq P (y :: L) ->
  ForallConseq P (z :: L).
Proof.
  introv Pza H1. inverts H1; constructors~.
Qed.

Lemma ForallConseq_concat_fuse : forall A (P:A->A->Prop) x y z L1 L2,
  (forall a, P a x -> P a z) -> (forall a, P y a -> P z a) ->
  ForallConseq P (L1&x) -> ForallConseq P (y::L2) -> 
  ForallConseq P (L1&z ++ L2).
Proof.
  introv Paz Pza H1 H2. sets_eq L0: (L1 & x). gen L1.
  induction H1; intros; rew_list in *.
  false* nil_eq_last_inv.
  destruct L1; rew_list in *.
		forwards~: ForallConseq_cons_fuse. 
    inverts EQL0. false* last_eq_nil_inv.
  destruct L1; rew_list in *; inverts EQL0.
		forwards*: IHForallConseq.
    destruct L1; rew_list in *; inverts H4; constructors~.
Qed.
  
Lemma ForallConseq_cons_inv : forall A (P:A->A->Prop) x L,
  ForallConseq P (x::L) -> ForallConseq P L.
Proof. introv M. inverts M as C M. auto. inverts M as C M. auto. auto. Qed.

Lemma ForallConseq_cons2_inv : forall A (P:A->A->Prop) x y L,
  ForallConseq P (x::y::L) -> P x y /\ ForallConseq P L.
Proof. introv M. inverts M as C M. splits~. inverts M as C M. auto. auto. Qed.

End ForallConseqLemmas.



(* ******************************************************* *)
(** ** Representation predicates *)

Inductive SekMem (A: Type) :=
|	SM_Empty : SekMem A
|	SM_Level : SWChunkMem A -> SekMem (partial_swchunk_ A) -> SekMem A.

Arguments SM_Empty {A}.
Arguments SM_Level {A}.

Fixpoint SekMemory A {IA: Inhab A} (M: SekMem A) : hprop :=
	match M with
	|	SM_Empty => \[]
	|	SM_Level SWCM M' => SChunkMemory SWCM \* SekMemory M'
	end.

Lemma SekMemory_eq : forall A (IA: Inhab A) (M: SekMem A),
	SekMemory M =
		match M with
		|	SM_Empty => \[]
		|	SM_Level SWCM M' => SChunkMemory SWCM \* SekMemory M'
		end.
Proof. intros. induction* M. Qed.

Lemma SekMemory_eq_level : forall A (IA: Inhab A) (SWCM: SWChunkMem A) (M': SekMem (partial_swchunk_ A)),
	SekMemory (SM_Level SWCM M') =
		SChunkMemory SWCM \* SekMemory M'.
Proof. auto. Qed.

Hint Resolve SekMemory_eq SekMemory_eq_level.

Fixpoint SekExtend A {IA: Inhab A} (M1 M2: SekMem A) : Prop :=
	match M1, M2 with
	|	SM_Empty, _ => True
	|	SM_Level SWCM1 M1', SM_Level SWCM2 M2' => SChunkExtend SWCM1 SWCM2 /\ SekExtend M1' M2'
	|	_, _ => False
	end.

Lemma SekExtend_eq : forall A (IA: Inhab A) (M1 M2: SekMem A),
	SekExtend M1 M2 =
		match M1, M2 with
		|	SM_Empty, _ => True
		|	SM_Level SWCM1 M1', SM_Level SWCM2 M2' => SChunkExtend SWCM1 SWCM2 /\ SekExtend M1' M2'
		|	_, _ => False
		end.
Proof. intros. induction* M1. Qed.

Lemma SekExtend_eq_level : forall A (IA: Inhab A) (SWCM1 SWCM2: SWChunkMem A) (M1' M2': SekMem (partial_swchunk_ A)),
	SekExtend (SM_Level SWCM1 M1') (SM_Level SWCM2 M2') =
	(SChunkExtend SWCM1 SWCM2 /\ SekExtend M1' M2').
Proof. auto. Qed.

Lemma SekExtend_refl : forall A (IA: Inhab A) (M: SekMem A),
	SekExtend M M.
Admitted.

Lemma SekExtend_trans : forall A (IA: Inhab A) (M2 M1 M3: SekMem A),
	SekExtend M1 M2 ->
	SekExtend M2 M3 ->
	SekExtend M1 M3.
Admitted.

Hint Resolve SekExtend_trans.

#[global]
Instance MonType_SekMem A {IA: Inhab A} {EA: Enc A} :
	MonType (SekMem A) := make_MonType (SekMemory (A := A)) (SekExtend (A := A)).



Definition SWSek_vconcat A (v: view_) (Lf Lb: listW A) (LLm: listW (listW A)) : listW A :=
	vapp v Lf (vapp v (concat (list_of_listW LLm)) Lb).

Lemma SWSek_vconcat_eq : forall A (v: view_) (Lf Lb: listW A) (LLm: listW (listW A)),
	SWSek_vconcat v Lf Lb LLm = vapp v Lf (vapp v (concat (list_of_listW LLm)) Lb).
Proof. auto. Qed.

Lemma SWSek_vconcat_absorb_left : forall A (v: view_) (Lf Lb: listW A) (LLm: listW (listW A)),
	SWSek_vconcat v Lf Lb LLm = SWSek_vconcat v nil Lb (vcons v (Wlist_of_listW Lf) LLm).
Admitted.


Definition SWSek_middle_full A (LLm: listW (listW A)) : Prop :=
	ForallConseq (fun c1 c2 => length c1 + length c2 > K) (list_of_listW LLm).


Lemma SWSek_middle_full_vcons_full : forall A (v: view_) (L: listW A) (LLm: listW (listW A)),
	IsFull L ->
	SWSek_middle_full LLm ->
	SWSek_middle_full (vcons v (Wlist_of_listW L) LLm).
Admitted.


Record SWSek_inv_gen (pf pb: bool) (v: view_) A (L Lf Lb: listW A) (LLm : listW (listW A)) (w: int) : Prop :=
	mkSWSek_inv {
		swsinv_concat : L = SWSek_vconcat v Lf Lb LLm;
		swsinv_full : SWSek_middle_full LLm;
		swsinv_weight : w = list_sum weight' L;
		swsinv_popf : pf -> LLm <> nil -> Lf <> nil;
		swsinv_popb : pb -> LLm <> nil -> Lb <> nil }.
	
(* Definition SWSek_inv :=
	SWSek_inv_gen true true Front. *)

Notation "'RChunkType' A a" := (listW A -> swchunk_ a -> hprop) (at level 69, A at level 0).
Notation "'WRChunkType' A a" := (Wlist A -> swchunk_ a -> hprop) (at level 69, A at level 0).

Definition WRChunk_of_RChunk a A (RChunk: RChunkType A a) : WRChunkType A a :=
	fun L c =>
		c ~> RChunk (unweighted' L) \*
		\[weight' L = weight' c]. (* = list_sum weight' L *)

Lemma RChunk_lift : forall a A (RChunk: RChunkType A a) (X: listW A) (x: swchunk_ a),
	x ~> RChunk X ==>
		x ~> (WRChunk_of_RChunk RChunk) (weighted_make__ X (weight' x)).
Proof. xunfold WRChunk_of_RChunk. xsimpl~. Qed.

Fixpoint depth a (s: swsek_ a) : int :=
	match s with
	|	SWSek_Empty _ => 0
	|	SWSek_Level _ s' _ => 1 + depth s'
	end.

Definition SWSekOf_Level (pf pb: bool) (v: view_) a A {IA: Inhab a} {EA: Enc a} (RChunk: RChunkType A a)
	(L: listW A) (sides: loc) (LLm: listW (listW A)) (w: int) : hprop :=
	\exists f b Lf Lb,
		\[FArray (vlist2 v f b) sides] \*
		f ~> RChunk Lf \*
		b ~> RChunk Lb \*
		\[SWSek_inv_gen pf pb v L Lf Lb LLm w].

Lemma SWSekOf_Level_eq : forall (pf pb: bool) (v: view_) a A (IA: Inhab a) (EA: Enc a) (RChunk: RChunkType A a)
	(L: listW A) (sides: loc) (LLm: listW (listW A)) (w: int),
	SWSekOf_Level pf pb v RChunk L sides LLm w =
		\exists f b Lf Lb,
			\[FArray (vlist2 v f b) sides] \*
			f ~> RChunk Lf \*
			b ~> RChunk Lb \*
			\[SWSek_inv_gen pf pb v L Lf Lb LLm w].
Proof using. auto. Qed.

Definition SWSekOf_IsEmpty a (s: swsek_ a) : Prop :=
	exists d, s = SWSek_Empty d.

Definition SWSekOf_collapsed (cl: bool) a A {IA: Inhab a} {EA: Enc a}
	(L: listW A) (m: swsek_ (partial_swchunk_ a)) : Prop :=
	cl ->
	L = nil ->
	SWSekOf_IsEmpty m.

Fixpoint SWSekOf a A {IA: Inhab a} {EA: Enc a} (R: Whtype A a)
	(M: SekMem a) (oo: option owner_) (L: listW A) (s: swsek_ a) : hprop :=
	match s with
	|	SWSek_Empty _ => \[L = nil]
	|	SWSek_Level sides m w => \exists LLm SWCM M',
			let RChunk := SWChunkOf_MaybeOwned R SWCM oo in
			\[M = SM_Level SWCM M'] \*
			SWSekOf_Level true true Front RChunk L sides LLm w \*
			\[SWSekOf_collapsed true L m] \*
			m ~> SWSekOf (WRChunk_of_RChunk RChunk) M' oo LLm
	end.

Definition SWSekOf_mid a A {IA: Inhab a} {EA: Enc a} (RChunk: RChunkType A a)
	(M': SekMem (partial_swchunk_ a)) (oo: option owner_) (LLm: listW (listW A)) (m: swsek_ (partial_swchunk_ a)) : hprop :=
	m ~> SWSekOf (WRChunk_of_RChunk RChunk) M' oo LLm.

Lemma SWSekOf_mid_eq : forall a A (IA: Inhab a) (EA: Enc a) (RChunk: RChunkType A a)
	(M': SekMem (partial_swchunk_ a)) (oo: option owner_) (LLm: listW (listW A)) (m: swsek_ (partial_swchunk_ a)),
	m ~> SWSekOf_mid RChunk M' oo LLm = m ~> SWSekOf (WRChunk_of_RChunk RChunk) M' oo LLm.
Proof. auto. Qed.

Lemma SWSekOf_eq : forall a A (IA: Inhab a) (EA: Enc a) (R: Whtype A a)
	(M: SekMem a) (oo: option owner_) (L: listW A) (s: swsek_ a),
	s ~> SWSekOf R M oo L =
		match s with
		|	SWSek_Empty _ => \[L = nil]
		|	SWSek_Level sides m w => \exists LLm SWCM M',
				let RChunk := SWChunkOf_MaybeOwned R SWCM oo in
				\[M = SM_Level SWCM M'] \*
				SWSekOf_Level true true Front RChunk L sides LLm w \*
				\[SWSekOf_collapsed true L m] \*
				m ~> SWSekOf_mid RChunk M' oo LLm
		end.
Proof using. intros. gen M L. induction* s. Qed.

Lemma SWSekOf_eq_empty : forall a A (IA: Inhab a) (EA: Enc a) (R: Whtype A a)
	(M: SekMem a) (oo: option owner_) (L: listW A) (d: a),
	SWSek_Empty d ~> SWSekOf R M oo L =
		\[L = nil].
Proof using. auto. Qed.

Lemma SWSekOf_eq_level : forall a A (IA: Inhab a) (EA: Enc a) (R: Whtype A a)
	(M: SekMem a) (oo: option owner_) (L: listW A) (sides: array a) (m: swsek_ (partial_swchunk_ a)) (w: int),
	SWSek_Level sides m w ~> SWSekOf R M oo L =
		\exists LLm SWCM M',
			let RChunk := SWChunkOf_MaybeOwned R SWCM oo in
			\[M = SM_Level SWCM M'] \*
			SWSekOf_Level true true Front RChunk L sides LLm w \*
			\[SWSekOf_collapsed true L m] \*
			m ~> SWSekOf_mid RChunk M' oo LLm.
Proof using. auto. Qed.

Hint Extern 1 (RegisterOpen SWSekOf) => Provide SWSekOf_eq_empty SWSekOf_eq_level.

Lemma SWSekOf_mid_Mono : forall a A (IA: Inhab a) (EA: Enc a) (R: Whtype A a)
	(SWCM1 SWCM2: SWChunkMem a) (M': SekMem (partial_swchunk_ a))
	(oo: option owner_) (LLm: listW (listW A)) (m: swsek_ (partial_swchunk_ a)),
	let RChunk1 := SWChunkOf_MaybeOwned R SWCM1 oo in
	let RChunk2 := SWChunkOf_MaybeOwned R SWCM2 oo in
	SChunkExtend SWCM1 SWCM2 ->
	(m ~> SWSekOf_mid RChunk1 M' oo LLm ==> m ~> SWSekOf_mid RChunk2 M' oo LLm).
Admitted.

Lemma SWSekOf_Mono : forall a A {IA: Inhab a} {EA: Enc a} (R: Whtype A a)
	(M1 M2: SekMem a) (oo: option owner_) (L: listW A) (s: swsek_ a),
	SekExtend M1 M2 ->
	(s ~> SWSekOf R M1 oo L ==> s ~> SWSekOf R M2 oo L).
Admitted.



(* ******************************************************* *)
(** ** Specs *)

Lemma mk_swsek_weight_invariant_spec_of : forall a A (IA: Inhab a) (EA: Enc a) (R: Whtype A a)
	SWCM Ml (v: view_) (oo: option owner_) (f b: swchunk_ a) (mid: swsek_ (partial_swchunk_ a))
	(Lf Lb: listW A) (LLm: listW (listW A)),
		SWSek_middle_full LLm ->
		let M := SM_Level SWCM Ml in
		let RChunk := SWChunkOf_MaybeOwned R SWCM oo in
		SPEC (mk_swsek_weight_invariant v oo f mid b)
		MONO M
		PRE (f ~> RChunk Lf \*
					b ~> RChunk Lb \*
					mid ~> SWSekOf_mid RChunk Ml oo LLm)
		POST (fun M' s' => s' ~> SWSekOf R M' oo (SWSek_vconcat v Lf Lb LLm)).
Admitted.

Hint Extern 1 (RegisterSpec mk_swsek_weight_invariant) => Provide mk_swsek_weight_invariant_spec_of.

Lemma read_1 : forall A (IA: Inhab A) (f b: A),
	[f; b][1] = b.
Proof. intros. rew_array. case_if. case_if~. math. Qed.

Hint Rewrite read_1 : rew_list.



(* Hint Extern 1 (RegisterSpec swchunk_create) =>
	match goal with R: Whtype _ _ |- _ => Provide (@swchunk_create_spec_of _ _ _ _ R) end. *)

Ltac xspec_registered f ::=
	ltac_database_get database_spec f;
	try match goal with |- ?S -> _ =>
		match S with context[Whtype _ _] =>
			match goal with R: Whtype _ _ |- _ =>
				let H := fresh in
				intros H;
				specializes H R;
				revert H
			end
		end
	end.

Definition one_if (P: Prop) : int :=
	If P then 1 else 0.

(* Ltac xsimpl_use_credits tt ::=
	constr:(false). *)

Lemma swsek_push_spec_of : forall a A (IA: Inhab a) (EA: Enc a) (R: Whtype A a)
	(M: SekMem a) (v: view_) (oo: option owner_) (L: listW A) (s: swsek_ a) (X: weighted_ A) (x: weighted_ a),
	v = Front ->
	SPEC (swsek_push v oo s x)
		MONO M
		PRE (s ~> SWSekOf R M oo L \* x ~> R X)
		POST (fun M' s' => s' ~> SWSekOf R M' oo (vcons v X L)).
Proof using.
	introv ->.
	sets_eq n: (depth s). gen a A IA EA R M L X x s. induction_wf IH: (downto 0) n; hide IH.
	introv Eqn. xcf. xpay_skip. xmatch.
	{ xlet. xapp. skip. (* base case, not so interesting *) }
	{ xchanges SWSekOf_eq_level ;=> LLm SWCM M' -> Cl. xchange SWSekOf_Level_eq ;=> f b Lf Lb Hsides Ig.
		xapp*. xmatch. rew_list. xapp.
		xlet (fun '(f1, mid1) =>
			\exists SWCM1 M1' Lf1 LLm1,
			let M := SM_Level SWCM M' in
			let M1 := SM_Level SWCM1 M1' in
			\[SekExtend M M1] \*
			let RChunk := SWChunkOf_MaybeOwned R SWCM1 oo in
			\$(-1) \*
			f1 ~> RChunk Lf1 \*
			b ~> RChunk Lb \*
			\[~ IsFull Lf1] \*
			\[SWSek_middle_full LLm1] \*
			\[L = SWSek_vconcat Front Lf1 Lb LLm1] \*
			mid1 ~> SWSekOf_mid RChunk M1' oo LLm1 \*
			SekMemory M1 \*
			x ~> R X).
		{ simpl. lets [Iconcat Ifull Iweight Ipf Ipb]: Ig. xif ;=> cond.
			{ xchange SWChunkOf_MaybeOwned_inv_Inv f ;=> I_f.
				xapp ;=> d. xapp; simpl ;=> f' SWCM1 HE.
				(* pourquoi ça marche pas tout de suite? *)
				do 2 xchange~ SWChunkOf_MaybeOwned_Mono. xchange~ SWSekOf_mid_Mono.
				xchange RChunk_lift f. xchange* SWSekOf_mid_eq. sets_eq n': (depth mid). xapp~; simpl.
				{ split.
					{ skip. } (* lemmas: depth >= 0*)
					{ subst n n'. math. } }
				{ intros mid' M1' HE1. xval. xsimpl~ (Wlist_of_listW Lf :: LLm).
					{ apply capacity_spec. }
					{ applys~ SWSek_middle_full_vcons_full Front. }
					{ subst L. rewrite* SWSek_vconcat_absorb_left. }
					{ xchanges <- SWSekOf_mid_eq. fequals. unfold Wlist_of_listW. fequals. applys~ swcinv_sum. } } }
			{ xvals~. split*.
				{ apply SChunkExtend_refl. }
				{ apply SekExtend_refl. } } }
	destruct x5__ as [f1 mid1]. xpull. xpull ;=> SCWM1 M1' Lf1 LLm1 HE HLF1 HLLm1 EqL. xmatch.
	xchange SekMemory_eq. xapp; simpl ;=> f2 SWCM' HE1.
	xchange <- SekMemory_eq_level. xchange~ SWChunkOf_MaybeOwned_Mono. xchange~ SWSekOf_mid_Mono.
	xapp~; simpl ;=> s' M2 HE2. xsimpl.
	{ destruct HE as [HE HES]. destruct~ M2 as [| SWCM2 M2']. destruct HE2 as [HE2 HES2]. split~. }
	{ rew_list. fequals~. }
	{ skip. (* credits... *) } }
Qed.
