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



(* ******************************************************* *)
(** ** Representation predicates *)

(* Inductive SekMemory (A: Type) {IA: Inhab A} {EA: Enc A} :=
	|	BottomMemory : WChunkMemory A -> SekMemory
	|	LevelMemory : WChunkMemory A -> SekMemory (A := partial_swchunk_ A) -> SekMemory. *)

Inductive SekMem (A: Type) {IA: Inhab A} {EA: Enc A} :=
|	SM_Empty : SekMem
|	SM_Level : SWChunkMem A -> SekMem (A := partial_swchunk_ A) -> SekMem.



Definition List_of_Wlist A (WL: Wlist A) : list A :=
	LibList.map unweighted' WL.

Record SWSek_inv_gen (popf popb: bool) A (L Lf Lb: Wlist A) (LLm : Wlist (Wlist A)) (w: int) : Prop :=
	mkSWSek_inv {
		swsinv_concat : L = Lf ++ concat (List_of_Wlist LLm) ++ Lb;
		swsinv_full : ForallConseq (fun c1 c2 => length c1 + length c2 > K) (List_of_Wlist LLm);
		swsinv_weight : w = list_sum weight' L;
		swsinv_popf : popf -> LLm <> nil -> Lf <> nil;
		swsinv_popb : popb -> LLm <> nil -> Lb <> nil }.
	
Definition SWSek_inv :=
	SWSek_inv_gen true true.

Definition WRChunk_of_RChunk a A (RChunk: Wlist A -> swchunk_ a -> hprop) : weighted_ (Wlist A) -> swchunk_ a -> hprop :=
	fun L c =>
		c ~> RChunk (unweighted' L) \*
		\[weight' L = weight' c]. (* = list_sum weight' L *)

Fixpoint SWSekOf a A {IA: Inhab a} {EA: Enc A} (R: Whtype A a)
	(M: SekMem (A := a)) (oo: option owner_) (L: Wlist A) (s: swsek_ a) : hprop :=
	let (sides, mid, w) := s in
	\exists f b Lf Lb LLm SWCM M',
		let RChunk := SWChunkOf_MaybeOwned R SWCM oo in
		\[M = SM_Level SWCM M'] \*
		sides ~> Array ([f; b]) \*
		f ~> RChunk Lf \*
		b ~> RChunk Lb \*
		\[SWSek_inv L Lf Lb LLm w] \*
		match mid with
		|	None => \[LLm = nil]
		|	Some m => m ~> SWSekOf (WRChunk_of_RChunk RChunk) M' oo LLm
		end.
