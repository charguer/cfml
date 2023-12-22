Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From CFML Require Import Stdlib.Array_proof.
From TLC Require Import LibList LibListSub.
From TLC Require Import LibListZ LibMap.

Require Import ListMisc.

(***************************************)
(** Maps *)

Lemma read_single : forall (a A:Type) (IA:Inhab A) (i:a) (x:A),
    (i \:= x)[i] = x.
Proof.
  intros.
  rewrite <- union_empty_l.
  rewrite <- update_eq_union_single.
  rew_map*.
Qed.

Hint Rewrite dom_single read_single
     read_update_same : rew_map.

Ltac rew_maps_core tt := rew_map; rew_set.

Tactic Notation "rew_maps" :=
  rew_maps_core tt.
Tactic Notation "rew_maps" "*"  :=
  rew_maps; auto_star.

(***************************************)
(** Preserve *)

(* NB: Preserve could be more general *)
Definition Preserve (A B:Type) {IB:Inhab B} (M M':map A (list B)) : Prop :=
  forall (i:A),
    i \indom M ->
    (i \indom M') /\ Suffix M[i] M'[i].

Lemma Preserve_refl : forall (A B:Type) {IB:Inhab B} (M:map A (list B)),
    Preserve M M.
Proof.
  intros. intros i Hi.
  split*. apply Suffix_refl.
Qed.

Lemma Preserve_trans : forall (A B:Type) {IB:Inhab B} (M1 M2 M3:map A (list B)),
  Preserve M1 M2 ->
  Preserve M2 M3 ->
  Preserve M1 M3.
Proof.
  introv H12 H23. intros i Hi.
  destructs* (H12 i).
  destructs* (H23 i).
  eauto with suffix.
Qed.

Lemma Preserve_add_fresh : forall (A B:Type) {IB:Inhab B} (M:map A (list B)) (j:A) (x:list B),
  j \notindom M ->
  Preserve M M[j:=x].
Proof.
  introv Hj. intros i Hi.
  split; rew_map*.
  { eauto with suffix. }
  { intros ->. unfolds in Hj. auto. }
Qed.

Lemma Preserve_existing : forall (A B:Type) {IB:Inhab B} (M:map A (list B)) (j:A) (xs:list B),
  j \indom M ->
  Suffix M[j] xs ->
  Preserve M M[j:=xs].
Proof.
  introv Hj Hp.
  intros i Hi.
  split.
  { rew_map*. }
  { rewrite read_update.
    case_if as E.
    { rewrite* <- E. }
    { rew_map*. eauto with suffix. } }
Qed.

Lemma Preserve_empty : forall (A B:Type) {IB:Inhab B} (M:map A (list B)),
    Preserve \{} M.
Proof.
  intros. intros j Hj.
  rewrite dom_empty in Hj.
  now apply in_empty in Hj.
Qed.

Lemma Preserve_union_l : forall (A B:Type) {IB:Inhab B} (M1 M2:map A (list B)),
    M1 \# M2 ->
    Preserve M1 (M1 \u M2).
Proof.
  intros. intros j Hj.
  split.
  { rewrite dom_union.
    now eapply in_union_l. }
  { erewrite <- union_read_l; try easy.
    eauto with suffix. }
Qed.

Lemma Preserve_union_r : forall (A B:Type) {IB:Inhab B} (M1 M2:map A (list B)),
    M1 \# M2 ->
    Preserve M2 (M1 \u M2).
Proof.
  intros. intros j Hj.
  split.
  { rewrite dom_union.
    now eapply in_union_r. }
  { erewrite <- union_read_r; try easy.
    eauto with suffix. }
Qed.

Create HintDb preserve.
Hint Resolve Preserve_refl Preserve_trans
     Preserve_add_fresh Preserve_existing
     Preserve_empty
     Preserve_union_l Preserve_union_r : preserve.
