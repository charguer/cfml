Set Implicit Arguments.
From CFML Require Import WPLib Stdlib LibSepGroup Array_proof.
From TLC Require Import LibList LibListZ LibMap.

From CFML Require Import LibSepTLCbuffer.
Import IndexHints.

Require Import Mono.

Require Import ListMisc.

Require Import Id_ml Id_proof.

Require Import EChunk_ml EChunk_proof.

Require Export Preserve.

(***************************************)
(** EChunkMap *)

(* A type for a map linking echunks to their content *)
Notation EChunkMap A := (map (echunk_ A) (list A)).

(* Shared M asserts that M is effectievly a bag of echunks. *)
Definition EChunkGroup {A} {IA:Inhab A} {EA:Enc A} : EChunkMap A -> hprop :=
  Group (EChunk (A:=A)).

Lemma EChunkGroup_empty : forall A (IA:Inhab A) (EA:Enc A),
  \[] ==> EChunkGroup (\{} : EChunkMap A).
Proof.
  intros.
  xunfold (EChunkGroup (A:=A)).
  xunfold Group. rewrite fold_empty.
  xsimpl*. unfold finite.
  rewrite dom_empty. eauto with finite.
Qed.

Global Instance MonType_EChunkMap (A:Type) {IA:Inhab A} {EA:Enc A}
 : MonType (EChunkMap A) :=
  make_MonType (EChunkGroup (A:=A)) (Preserve (B:=A)).

(***************************************)
(** The actual Memory type *)

Record Memory (A:Type) : Type :=
  mk_m {
      echunks : EChunkMap A;
      ids : Idents
    }.

Definition empty {A:Type} :=
  @mk_m A \{} \{}.

Global Instance BagEmpty_memory A : BagEmpty (Memory A) :=
  { empty := @empty A }.

Definition union (A:Type) (M1 M2:Memory A) :=
  mk_m (echunks M1 \u echunks M2) (ids M1 \u ids M2).

Global Instance BagUnion_memory A : BagUnion (Memory A) :=
  { union := @union A }.

Definition disjoint (A:Type) (M1 M2:Memory A) :=
  (echunks M1 \# echunks M2) /\ (ids M1 \# ids M2).

Global Instance BagDisjoint_memory A : BagDisjoint (Memory A) :=
  { disjoint := @disjoint A }.

Global Instance Disjoint_sym_memory A : @Disjoint_sym _ (BagDisjoint_memory A).
Proof.
  constructor.
  introv (?&?).
  constructor.
  { rewrite disjoint_eq_disjoint_dom in *. eapply disjoint_sym; eauto. }
  { rewrite disjoint_eq_disjoint_dom in *. eapply disjoint_sym; eauto. }
Qed.

(***************************************)
(** The Extend pre-order *)

Definition Extend {A} {IA:Inhab A} {EA:Enc A} (M M':Memory A) : Prop :=
  Preserve (echunks M) (echunks M') /\ (dom (ids M)) \c (dom (ids M')).

Lemma Extend_refl : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A),
  Extend M M.
Proof.
  split*.
  { eauto with preserve. }
  { apply incl_refl. }
Qed.

Lemma Extend_trans : forall A (IA:Inhab A) (EA:Enc A) (M1 M2 M3:Memory A),
  Extend M1 M2 ->
  Extend M2 M3 ->
  Extend M1 M3.
Proof.
  intros ? ? ? ? ? ? [] [].
  split*.
  { eauto with preserve. }
  { eapply incl_trans; typeclass. }
Qed.

Lemma Extend_union_l : forall A (IA:Inhab A) (EA:Enc A) (M1 M2:Memory A),
  M1 \# M2 ->
  Extend M1 (M1 \u M2).
Proof.
  introv (D&?).
  rewrite disjoint_eq_disjoint_dom in D.
  constructor*; simpl.
  { constructor.
    { rewrite dom_union. rew_set. jauto. }
    { rewrites* (>> union_read_l i).
      eauto with suffix. } }
  { rewrite dom_union. rew_set. firstorder. }
Qed.

Lemma Extend_union_r : forall A (IA:Inhab A) (EA:Enc A) (M1 M2:Memory A),
  M1 \# M2 ->
  Extend M1 (M2 \u M1).
Proof.
  introv (D&?).
  rewrite disjoint_eq_disjoint_dom in D.
  constructor*; simpl.
  { constructor.
    { rewrite dom_union. rew_set. jauto. }
    { apply disjoint_sym in D.
      rewrites* (>> union_read_r i).
      eauto with suffix. } }
  { rewrite dom_union. rew_set. firstorder. }
Qed.

Lemma Extend_from_Preserve : forall A (IA:Inhab A) (EA:Enc A) (E1 E2: EChunkMap A) (I:Idents),
  Preserve E1 E2 ->
  Extend (mk_m E1 I) (mk_m E2 I).
Proof.
  intros.
  constructor*.
  apply incl_refl.
Qed.

Lemma Extend_from_Incl : forall A (IA:Inhab A) (EA:Enc A) (E:EChunkMap A) (I1 I2:Idents),
  dom I1 \c dom I2 ->
  Extend (mk_m E I1) (mk_m E I2).
Proof.
  intros.
  constructor*.
  eauto with preserve.
Qed.

Lemma Extend_empty : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A),
  Extend \{} M.
Proof.
  intros. destruct M.
  split; simpl.
  { eauto with preserve. }
  { rewrite dom_empty. apply empty_incl. }
Qed.

Create HintDb extend.
Hint Resolve
     Extend_trans
     Extend_union_l Extend_union_r
     Extend_from_Preserve Extend_from_Incl
     Extend_empty
     disjoint_sym : extend.

Lemma union_empty_eq_empty : forall A (IA:Inhab A) (EA:Enc A) (M1 M2:Memory A),
  @empty A \u @empty A = \{}.
Proof.
  intros. destruct M1,M2.
  typeclass.
Qed.

(**************************************)
(** The Shared predicate *)

Definition Shared {A} {IA:Inhab A} {EA:Enc A} (M:Memory A) : hprop :=
  EChunkGroup (echunks M) \* RefGroup (ids M).

Lemma haffine_Shared : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A),
  haffine (Shared M).
Proof. intros. unfold Shared. xaffine. Qed.

Hint Resolve haffine_Shared : haffine.

Lemma Shared_eq : forall A (IA:Inhab A) (EA:Enc A) (M:Memory A),
  Shared M = EChunkGroup (echunks M) \* RefGroup (ids M).
Proof. auto. Qed.

Global Instance MonType_Memory {A} {IA:Inhab A} {EA:Enc A} : MonType (Memory A) :=
  make_MonType Shared Extend.

Lemma Shared_empty : forall A (IA:Inhab A) (EA:Enc A),
  \[] ==> Shared (@empty A).
Proof.
  intros.
  xchange* EChunkGroup_empty. xchange RefGroup_empty.
  unfold Shared. xsimpl*.
Qed.

Lemma Shared_union : forall A (IA:Inhab A) (EA:Enc A) (M1 M2:Memory A),
  Shared M1 \* Shared M2 ==> Shared (M1 \u M2).
Proof.
  intros.
  simpl. unfold Shared,union. simpl.
  xchange* (>> Group_join (echunks M1)). intros.
  xchange* (>> Group_join (ids M1)). typeclass. typeclass.
  intros. xsimpl*.
Qed.

Lemma Shared_disjoint : forall A (IA:Inhab A) (EA:Enc A) (M1 M2:Memory A),
  Shared M1 \* Shared M2 ==+> \[M1 \# M2].
Proof.
  intros.
  simpl. unfold Shared, disjoint. simpl.
  xchange* (>> Group_star_disjoint (echunks M1)). intros.
  xchange* (>> Group_star_disjoint (ids M1)). typeclass. typeclass. intros.
  xsimpl*.
Qed.

Lemma Shared_union_himpl : forall A (IA:Inhab A) (EA:Enc A) (M1 M2:Memory A),
  Shared M1 \* Shared M2 ==> \exists M, Shared M \* \[Extend M1 M /\ Extend M2 M].
Proof.
  intros.
  xchange Shared_disjoint. intros.
  xchange Shared_union. xsimpl*.
  split; eauto with extend.
  applys Extend_union_l. now apply disjoint_sym.
Qed.
