(**

This file presents a modernized, simplified proof for
"Separation Logic with Temporary Read-Only Permissions",
as described in the ESOP'17 paper by Arthur Charguéraud
and François Pottier.

Compared with the original proof, this one builds SL triples
on top of Hoare triples, using the technique of the baked-in
frame rule, here adapted to the needs of read-only permissions.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Export Semantics LibSepFunctor.
From Sep Require Import LibSepFmap.
Module Fmap := LibSepFmap.
Import NotationForFmapDisjoint.
Open Scope fmap_scope.
Arguments exist [A] [P].
Generalizable Variables A B.


(* ********************************************************************** *)
(* * FMap buffer --- now in TLC *)

Section FmapProp.
Variables (A B : Type).
Implicit Types h : fmap A B.
Implicit Types x : A.
Implicit Types v : B.


Axiom indom_filter_eq : forall (IB:Inhab B) (f:A->B->Prop) h x,
  indom (Fmap.filter f h) x = (indom h x /\ f x (read h x)).

Axiom filter_swap : forall (IB:Inhab B) (f1 f2:A->B->Prop) h,
  Fmap.filter f1 (Fmap.filter f2 h) = Fmap.filter f2 (Fmap.filter f1 h).


Lemma filter_all : forall (IB:Inhab B) (f:A->B->Prop) h,
  (forall x, indom h x -> f x (Fmap.read h x)) ->
  Fmap.filter f h = h.
Admitted.

Lemma filter_none : forall (IB:Inhab B) (f:A->B->Prop) h,
  (forall x, indom h x -> ~ f x (Fmap.read h x)) ->
  Fmap.filter f h = Fmap.empty.
Admitted.

Lemma filter_read : forall (IB:Inhab B) (f:A->B->Prop) h x,
  f x (Fmap.read h x) ->
  Fmap.read (Fmap.filter f h) x = Fmap.read h x.
Admitted.

Lemma indom_filter_inv : forall (IB:Inhab B) (f:A->B->Prop) h x,
  indom (Fmap.filter f h) x ->
     indom h x
  /\ f x (read h x)
  /\ read (Fmap.filter f h) x = read h x.
Proof using.
  introv D. erewrite indom_filter_eq in D. splits*. applys* filter_read.
Qed.

Lemma filter_empty: forall {IB:Inhab B} (f:A->B->Prop),
  Fmap.filter f Fmap.empty = Fmap.empty.
Proof using .
  intros. applys filter_none. intros x K.
  rewrite* indom_empty_eq in K.
Qed.

Lemma filter_single : forall (IB:Inhab B) (f:A->B->Prop) x y,
    Fmap.filter f (Fmap.single x y)
  = If f x y then (Fmap.single x y) else Fmap.empty.
Proof using.
  intros. case_if.
  { applys filter_all. intros k K. rewrite indom_single_eq in K.
    subst. rewrite* read_single. }
  { applys filter_none. intros k K. rewrite indom_single_eq in K.
    subst. rewrite* read_single. }
Qed.

Axiom filter_union : forall (IB:Inhab B) (f:A->B->Prop) h1 h2,
  Fmap.filter f (Fmap.union h1 h2) = Fmap.union (Fmap.filter f h1) (Fmap.filter f h2).

Axiom filter_partition : forall (IB:Inhab B) (f1 f2:A->B->Prop) h h1 h2,
  (forall x y, indom h x -> y = Fmap.read h x -> f1 x y -> f2 x y -> False) ->
  h1 = Fmap.filter f1 h ->
  h2 = Fmap.filter f2 h ->
  h = Fmap.union h1 h2 /\ Fmap.disjoint h1 h2.

Axiom filter_idempotent : forall (IB:Inhab B) (f:A->B->Prop) h,
  Fmap.filter f (Fmap.filter f h) = Fmap.filter f h.

  (* todo: provable by extensionality, but simpler direct proof. *)
(*  intros. applys extensionality.
  { intros. repeat erewrite indom_filter_eq. split. } *)


Lemma filter_incompatible : forall (IB:Inhab B) (f1 f2:A->B->Prop) h,
  (forall x y, indom h x -> y = Fmap.read h x -> f1 x y -> f2 x y -> False) ->
  Fmap.filter f1 (Fmap.filter f2 h) = Fmap.empty.
Proof using.
  introv M. applys* indom_empty_iff_empty.
  intros x K. do 2 erewrite indom_filter_eq in K.
  destruct K as ((Ix&K1)&K2). rewrite* filter_read in K2.
Qed.

Axiom indom_map : forall (IB:Inhab B) C (f:A->B->C) h x,
  indom (map_ f h) x = indom h x.

Axiom read_map : forall (IB:Inhab B) C (IB:Inhab C) (f:A->B->C) h x,
  indom h x ->
  read (map_ f h) x = f x (read h x).

Axiom map_empty : forall (IB:Inhab B) C (f:A->B->C),
  map_ f (@Fmap.empty A B) = Fmap.empty.

Axiom map_single : forall (IB:Inhab B) C (f:A->B->C) x y,
  map_ f (single x y) = single x (f x y).

Axiom map_union : forall (IB:Inhab B) C (f:A->B->C) h1 h2,
  map_ f (union h1 h2) = union (map_ f h1) (map_ f h2).

Axiom map_id : forall (IB:Inhab B) (f:A->B->B) h,
  (forall x y, indom h x -> y = read h x -> f x y = y) ->
  map_ f h = h.
(* Proof using. extensionality. Qed. *)

End FmapProp.

Hint Rewrite filter_empty filter_single filter_union : rew_fmap.

Hint Rewrite indom_map : rew_fmap.

Hint Rewrite map_empty map_single map_union : rew_fmap.

Lemma not_indom_of_indom_disjoint : forall A B (h1 h2:fmap A B) x,
  indom h1 x ->
  disjoint h1 h2 ->
  ~ indom h2 x.
Proof using.
  introv M1 D M2. rewrite* disjoint_eq_not_indom_both in D.
Qed.

Lemma read_union_cases : forall A B {IB:Inhab B} (h1 h2:fmap A B) x,
  read (union h1 h2) x = (If indom h1 x then read h1 x else read h2 x).
Proof using.
  Transparent Fmap.map_union.
  intros. unfold read, union, Fmap.map_union, indom, map_indom. simpl.
  case_eq (fmap_data h1 x); intros; repeat case_if; auto_false.
Qed.


(* ---------------------------------------------------------------------- *)

Tactic Notation "rew_fmap" :=
  autorewrite with rew_fmap.
Tactic Notation "rew_fmap" "in" hyp(H) :=
  autorewrite with rew_fmap in H.
Tactic Notation "rew_fmap" "in" "*" :=
  autorewrite with rew_fmap in *.

Tactic Notation "rew_fmap" "~" :=
  rew_fmap; auto_tilde.
Tactic Notation "rew_fmap" "~" "in" hyp(H) :=
  rew_fmap in H; auto_tilde.
Tactic Notation "rew_fmap" "~" "in" "*" :=
  rew_fmap in *; auto_tilde.

Tactic Notation "rew_fmap" "*" :=
  rew_fmap; auto_star.
Tactic Notation "rew_fmap" "*" "in" hyp(H) :=
  rew_fmap in H; auto_star.
Tactic Notation "rew_fmap" "*" "in" "*" :=
  rew_fmap in *; auto_star.

(* ---------------------------------------------------------------------- *)

Lemma agree_eq_indom_both_read_same : forall A B (IB:Inhab B) (h1 h2:fmap A B),
  agree h1 h2 = (forall x, indom h1 x -> indom h2 x -> read h1 x = read h2 x).
Proof using.
  extens. iff M.
  { introv M1 M2. specializes M x. unfolds indom, map_indom, read.
    destruct (fmap_data h1 x) as [y1|]; tryfalse.
    destruct (fmap_data h2 x) as [y2|]; tryfalse. applys* M. }
  { intros x y1 y2 M1 M2. specializes M x. unfolds indom, map_indom, read.
    destruct (fmap_data h1 x) as [y1'|]; tryfalse. inverts M1.
    destruct (fmap_data h2 x) as [y2'|]; tryfalse. inverts M2.
    applys M; auto_false. }
Qed.

Lemma agree_inv_read_same : forall A B (IB:Inhab B) (h1 h2:fmap A B) x,
  agree h1 h2 ->
  indom h1 x ->
  indom h2 x ->
  read h1 x = read h2 x.
Proof using.
  introv G D1 D2. erewrite agree_eq_indom_both_read_same in G. autos*.
Qed. (* TODO: erewrites *)


Lemma disjoint_filter : forall A B (IB:Inhab B) (f1:A->B->Prop) h1 h2,
  disjoint h1 h2 ->
  disjoint h1 (filter f1 h2).
Proof using.
  introv IB D. rewrite disjoint_eq_not_indom_both in *.
  intros x M1 M2. erewrite (@indom_filter_eq A B IB) in M2. false*.
Qed. (* TODO: erewrites *)

Lemma agree_filter : forall A B (IB:Inhab B) (f1:A->B->Prop) h1 h2,
  agree h1 h2 ->
  agree h1 (filter f1 h2).
Proof using.
  introv IB D. erewrite agree_eq_indom_both_read_same in *.
  intros x D1 D2. lets (Dx&Px&Ex): indom_filter_inv D2.
  rewrite Ex. applys* D.
Qed.



(* ********************************************************************** *)
(* * Core of the logic *)

Module Export SepROCore <: SepCore.

Implicit Types l : loc.
Implicit Types v : val.
Implicit Types p : loc.


(* ---------------------------------------------------------------------- *)
(** Heaps *)

Declare Scope heap_scope.

(** Definition of access modes: read-write or read-only *)

Inductive mode :=
  | mode_rw : mode
  | mode_ro : mode.

Notation "'rw'" := (mode_rw).
Notation "'ro'" := (mode_ro).

Global Instance mode_inhab : Inhab mode.
Proof using. applys Inhab_of_val mode_rw. Qed.

Global Instance val_mode_inhab : Inhab (val*mode)%type.
Proof using. typeclass. Qed.

Hint Resolve val_mode_inhab.

Implicit Types m : mode.

(** Representation of heaps as states with locations tagged by a mode *)

Definition heap : Type := fmap loc (val*mode)%type.

(** projions of the rw or ro part of a heap *)

Definition proj (m:mode) (h:heap) : heap :=
  Fmap.filter (fun l '(v,m') => m = m') h.

Notation "h '^' m" := (proj m h) : heap_scope.

(* Notation with higher priority *)

Notation "h '^rw'" := (proj mode_rw h)
  (at level 9, format "h '^rw'") : heap_scope.
Notation "h '^ro'" := (proj mode_ro h)
  (at level 9, format "h '^ro'") : heap_scope.

Open Scope heap_scope.

(** State of heap *)

Coercion heap_state (h : heap) : state :=
  Fmap.map_ (fun l '(v,m) => v) h.

(** Empty *)

Definition heap_empty : heap :=
  Fmap.empty.

Lemma heap_empty_eq :
  heap_empty = Fmap.empty.
Proof using. auto. Qed.

Hint Rewrite heap_empty_eq : rew_fmap.

Global Instance heap_inhab : Inhab heap.
Proof using. applys Inhab_of_val heap_empty. Qed.

(** Starable heaps: heaps that, on the intersection of their domains,
    associate locations to equal values, in read-only mode. *)

Definition heap_compat (h1 h2 : heap) : Prop :=
     Fmap.disjoint_3 (h1^rw) (h2^rw) (h1^ro \+ h2^ro)
  /\ Fmap.agree (h1^ro) (h2^ro).

(** Union of heaps.
    The operation [h1 \u h2] is partial. When the arguments are
    not compatible, it returns an unspecified result.
    We implement it using a classical logic test, so as to avoid
    dependently-typed programming. *)

Definition heap_union (h1 h2 : heap) : heap :=
  If (heap_compat h1 h2) then (h1 \+ h2) else arbitrary.

Declare Scope heap_union_scope.

Notation "h1 \u h2" := (heap_union h1 h2)
   (at level 37, right associativity) : heap_union_scope.

Local Open Scope heap_union_scope.

(** Affinity is customizable. Only rw permissions may be considered
    affine. RO permissions may be freely discarded by other means. *)

Parameter heap_affine : heap -> Prop. (* (h:heap) := True.*)

Parameter heap_affine_onlyrw : forall h,
  heap_affine h ->
  h^ro = Fmap.empty.

Parameter heap_affine_empty :
  heap_affine heap_empty.

Parameter heap_affine_union : forall h1 h2,
  heap_affine h1 ->
  heap_affine h2 ->
  heap_compat h1 h2 ->
  heap_affine (heap_union h1 h2).

Parameter heap_affine_union_inv : forall h1 h2,
  heap_affine (heap_union h1 h2) ->
  heap_affine h1 /\ heap_affine h2.


(* ---------------------------------------------------------------------- *)
(* ** Hprop *)

(** A heap predicate, type [hprop] is a predicate over such heaps. *)

Definition hprop := heap -> Prop.


(* ---------------------------------------------------------------------- *)
(* ** Entailment *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall (h:heap), H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55) : heap_scope.

Local Open Scope heap_scope.

Definition qimpl A (Q1 Q2:A->hprop) : Prop :=
  forall (v:A), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55) : heap_scope.

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. introv M. auto. Qed.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using. introv M1 M2. intros h H1h. eauto. Qed.

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  (H1 = H2).
Proof using. introv M1 M2. applys pred_ext_1. intros h. iff*. Qed.


(* ---------------------------------------------------------------------- *)
(** Operators *)

(** Affinity is defined in the standard way *)

Definition haffine (H : hprop) : Prop :=
  forall h, H h -> heap_affine h.

(** Heap predicates *)

Definition hempty : hprop :=
  fun h => h = heap_empty.

Program Definition hstar (H1 H2 : hprop) : hprop :=
  fun h => exists h1 h2,
               H1 h1
            /\ H2 h2
            /\ heap_compat h1 h2
            /\ h = h1 \u h2.

Definition hexists A (J:A->hprop) : hprop :=
  fun h => exists x, J x h.

Definition hforall (A : Type) (J : A -> hprop) : hprop :=
  fun h => forall x, J x h.

(** Notation *)

Notation "\[]" := (hempty)
    (at level 0) : heap_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : heap_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : heap_scope.


(* ---------------------------------------------------------------------- *)
(* ** Tactic for automation *)

Hint Extern 1 (\# _ _) => fmap_disjoint_pre tt.
Hint Extern 1 (\# _ _ _) => fmap_disjoint_pre tt.

Tactic Notation "rew_heap" :=
  autorewrite with rew_heap.
Tactic Notation "rew_heap" "in" hyp(H) :=
  autorewrite with rew_heap in H.
Tactic Notation "rew_heap" "in" "*" :=
  autorewrite with rew_heap in *.

Tactic Notation "rew_heap" "~" :=
  rew_heap; auto_tilde.
Tactic Notation "rew_heap" "~" "in" hyp(H) :=
  rew_heap in H; auto_tilde.
Tactic Notation "rew_heap" "~" "in" "*" :=
  rew_heap in *; auto_tilde.

Tactic Notation "rew_heap" "*" :=
  rew_heap; auto_star.
Tactic Notation "rew_heap" "*" "in" hyp(H) :=
  rew_heap in H; auto_star.
Tactic Notation "rew_heap" "*" "in" "*" :=
  rew_heap in *; auto_star.

Hint Rewrite union_assoc union_empty_l union_empty_r : rew_heap.


(* ---------------------------------------------------------------------- *)

Lemma disjoint_proj : forall h1 h2 m1 m2,
  disjoint h1 h2 ->
  disjoint (proj m1 h1) (proj m2 h2).
Proof using.
  autos* disjoint_filter disjoint_sym. (* TODO: slow *)
Qed.

Lemma agree_proj : forall h1 h2 m1 m2,
  agree h1 h2 ->
  agree (proj m1 h1) (proj m2 h2).
Proof using.
  introv D. autos* agree_filter agree_sym. (* TODO: slow *)
Qed.

(* TODO: would one sided versions of these lemmas be sufficient? helpful? *)

(* ---------------------------------------------------------------------- *)

Lemma disjoint_components : forall h,
  disjoint (h^rw) (h^ro).
Proof using.
  intros. forwards* (E&D): filter_partition h (h^rw) (h^ro).
  { intros x (v,m) _ _ K1 K2. false. }
Qed.

Lemma heap_compat_of_disjoint : forall h1 h2,
  disjoint h1 h2 ->
  heap_compat h1 h2.
Proof using.
  introv D. lets E1: disjoint_components h1.
  lets E2: disjoint_components h2. split.
  { splits; rew_disjoint; try splits;
    try solve [ assumption | applys* disjoint_proj ]. }
  { applys agree_of_disjoint. applys* disjoint_proj. }
Qed.

Lemma heap_fmap_components : forall h,
  h = (h^rw) \+ (h^ro) /\ disjoint (h^rw) (h^ro).
Proof using.
  intros. lets D: disjoint_components h.
  forwards* (E&D'): filter_partition h (h^rw) (h^ro).
  { intros x (v,m) _ _ K1 K2. false. }
Qed.

Lemma heap_union_eq_of_compat : forall h1 h2,
  heap_compat h1 h2 ->
  h1 \u h2 = h1 \+ h2.
Proof using. introv D. unfold heap_union. case_if*. Qed.

Hint Rewrite heap_union_eq_of_compat : rew_fmap.

Lemma heap_components : forall h,
  h = (h^rw) \u (h^ro) /\ disjoint (h^rw) (h^ro).
Proof using.
  intros. lets (E&D): heap_fmap_components h.
  rewrite* heap_union_eq_of_compat. applys* heap_compat_of_disjoint.
Qed.

Lemma disjoint_of_disjoint_components : forall h1 h2,
  disjoint h1 (h2^rw) ->
  disjoint h1 (h2^ro) ->
  disjoint h1 h2.
Proof using.
  introv M1 M2. forwards (E&D): heap_components h2.
  lets D': heap_compat_of_disjoint D.
  rewrite E. rewrite* heap_union_eq_of_compat.
Qed.

Lemma disjoint_heap_state : forall h1 h2,
  disjoint h1 h2 ->
  disjoint (heap_state h1) (heap_state h2).
Proof using.
  introv D. unfolds heap_state. rewrite disjoint_eq_not_indom_both in *.
  intros x D1 D2. rew_fmap* in *.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [proj] *)

(* Corollary *)
Lemma heap_compat_components : forall h,
  heap_compat (h^rw) (h^ro).
Proof using. intros. applys heap_compat_of_disjoint. applys disjoint_components. Qed.

Lemma proj_empty : forall m,
  (heap_empty^m) = empty.
Proof using.
  intros. unfold proj, heap_empty. rewrite* filter_empty.
Qed.

Hint Rewrite proj_empty : rew_heap.

Lemma proj_idempotent : forall h m,
  (h^m)^m = h^m.
Proof using.
  intros. unfold proj. applys* filter_idempotent.
Qed.

Lemma proj_proj_neq : forall h m1 m2,
  m1 <> m2 ->
  (h^m1)^m2 = heap_empty.
Proof using.
  intros. unfold proj. applys filter_incompatible.
  { intros x y D K M1 M2. destruct y as (v&m'). false. }
Qed.

(* Corollary for autorewrite *)
Lemma proj_ro_proj_rw : forall h,
  (h^rw)^ro = heap_empty.
Proof using. intros. applys* proj_proj_neq. auto_false. Qed.

(* Corollary for autorewrite *)
Lemma proj_rw_proj_ro : forall h,
  (h^ro)^rw = heap_empty.
Proof using. intros. applys* proj_proj_neq. auto_false. Qed.

Hint Rewrite proj_idempotent proj_ro_proj_rw proj_rw_proj_ro : rew_fmap rew_heap.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [heap_compat] *)

Lemma heap_compat_def : forall h1 h2,
    heap_compat h1 h2
  = (  Fmap.disjoint_3 (h1^rw) (h2^rw) (h1^ro \+ h2^ro)
    /\ Fmap.agree (h1^ro) (h2^ro)).
Proof using. auto. Qed.

Hint Rewrite heap_compat_def : rew_disjoint.

Lemma heap_compat_sym : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat h2 h1.
Proof using. introv (M1&M2). split~. applys* agree_sym. Qed.

Hint Resolve heap_compat_sym.

Lemma heap_compat_sym_eq : forall h1 h2 : heap,
   heap_compat h1 h2 = heap_compat h2 h1.
Proof using. intros. extens. autos* heap_compat_sym. Qed.

Lemma heap_compat_empty_l : forall h,
  heap_compat heap_empty h.
Proof using.
  intros. (* lets: disjoint_components h. *)
  unfold heap_empty. split; simpl.
  { rew_heap. rew_fmap. splits*. applys disjoint_components. }
  { rew_heap. apply Fmap.agree_empty_l. (* TODO: hints *) }
Qed.

Lemma heap_compat_empty_r : forall h,
  heap_compat h heap_empty.
Proof using.
  hint heap_compat_sym, heap_compat_empty_l. auto.
Qed. (* Not needed? *)

Hint Resolve heap_compat_empty_l heap_compat_empty_r.

Lemma heap_compat_refl_of_rw_empty : forall h,
  h^rw = Fmap.empty ->
  heap_compat h h.
Proof using.
  introv M. split.
  { rewrite M. auto. }
  { apply Fmap.agree_refl. } (* TODO: hint *)
Qed.


(* ---------------------------------------------------------------------- *)
(* ** More properties of [heap_compat] and [proj] *)

(* More generally, compat is preserved by subset. *)
Lemma heap_compat_proj_r : forall m h1 h2,
  heap_compat h1 h2 ->
  heap_compat h1 (proj m h2).
Proof using.
  hint agree_empty_r.
  introv (D&G). destruct m; split; rew_fmap; auto.
Qed.

Lemma heap_compat_proj_l : forall m h1 h2,
  heap_compat h1 h2 ->
  heap_compat (proj m h1) (h2).
Proof using.
  introv D. autos* heap_compat_proj_r heap_compat_sym.
Qed.

Lemma heap_compat_proj : forall h1 h2 m1 m2,
  heap_compat h1 h2 ->
  heap_compat (h1^m1) (h2^m2).
Proof using.
  introv D. autos* heap_compat_proj_r heap_compat_sym.
Qed.

Hint Resolve heap_compat_proj_r heap_compat_proj_l.

Lemma proj_fmap_union : forall m h1 h2,
  (h1 \+ h2)^m = (h1^m) \+ (h2^m).
Proof using.
  intros. unfold proj. rewrite* filter_union.
Qed.

Hint Rewrite proj_fmap_union : rew_fmap.

Lemma proj_union : forall m h1 h2,
  heap_compat h1 h2 ->
  (h1 \u h2)^m = (h1^m) \u (h2^m).
Proof using. introv D. rew_fmap*. Qed.

Hint Rewrite proj_union : rew_heap.

Lemma heap_compat_union_l : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h1 h3 ->
  heap_compat h2 h3 ->
  heap_compat (h1 \u h2) h3.
Proof using.
  introv D (D2&G2) (D3&G3).
  lets (E1&R1): heap_fmap_components h1.
  lets (E2&R2): heap_fmap_components h2.
  lets (E3&R3): heap_fmap_components h3.
  split.
  { rew_fmap*. (* TODO: slow *) }
  { rew_fmap*. applys~ Fmap.agree_union_l. }
Qed.

Lemma heap_compat_union_r : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h1 h3 ->
  heap_compat h2 h3 ->
  heap_compat h1 (h2 \u h3).
Proof using. hint heap_compat_sym, heap_compat_union_l. autos*. Qed.


(* ---------------------------------------------------------------------- *)
(* ** More properties of [heap_union] *)

Lemma heap_union_comm : forall h1 h2,
  heap_compat h1 h2 ->
  h1 \u h2 = h2 \u h1.
Proof using.
  introv D. rew_fmap*. applys extensionality.
  { intros x. extens. do 2 rewrite* indom_union_eq. }
  { intros x Dx.
    lets (E1&R1): heap_fmap_components h1.
    lets (E2&R2): heap_fmap_components h2.
    destruct D as (D&G).
    rewrite E1,E2 in Dx |- *.
    repeat rewrite Fmap.union_assoc in *.
    repeat rewrite* indom_union_eq in Dx.
    repeat rewrite read_union_cases.
    case_if as C1; try case_if as C2; try case_if as C3; try case_if as C4; auto.
    { false* not_indom_of_indom_disjoint C1 C2. }
    { false* not_indom_of_indom_disjoint C1 C3. }
    { false* not_indom_of_indom_disjoint C2 C3. }
    { applys* agree_inv_read_same. }
    { false*. (* contradicts Dx *) } }
Qed.

Lemma heap_union_assoc : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h2 h3 ->
  heap_compat h1 h3 ->
  (h1 \u h2) \u h3 = h1 \u (h2 \u h3).
Proof using.
  hint heap_compat_union_l. introv D1 D2 D3. rew_fmap*.
Qed.

Lemma heap_union_empty_l : forall h,
  heap_empty \u h = h.
Proof using. intros. rew_fmap*. Qed.

(* Corollary for autorewrite *)
Lemma heap_union_empty_r : forall h,
  h \u heap_empty = h.
Proof using. intros. rew_fmap*. Qed.

Hint Rewrite heap_union_empty_l heap_union_empty_r heap_union_assoc : rew_heap.

Lemma heap_fmap_union_state : forall h1 h2,
  heap_state (h1 \+ h2) = heap_state h1 \+ heap_state h2.
Proof using. intros. unfold heap_state. rew_fmap*. Qed.

Hint Rewrite heap_fmap_union_state : rew_fmap.

Lemma heap_state_single : forall p v m,
  heap_state (single p (v, m)) = single p v.
Proof using. intros. unfold heap_state. rew_fmap*. Qed.

Hint Rewrite heap_state_single : rew_fmap.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [toro] *)

(** [toro h] defines the read-only heap associated with [h],
    i.e. covering the same memory cells, but with all tagged
    as read-only. *)

Definition toro (h:heap) : heap :=
  Fmap.map_ (fun l '(v,m) => (v,mode_ro)) h.

Lemma indom_toro : forall h,
  indom (toro h) = indom h.
Proof using. intros. extens. intros x. unfold toro. rew_fmap*. Qed.

Lemma proj_rw_toro : forall h,
  (toro h)^rw = Fmap.empty.
Proof using.
  intros. unfold toro, proj.
  match goal with |- context [map_ ?f _] => set (F:=f) end.
  applys filter_none.
  intros x K N. rew_fmap* in K.
  erewrite read_map in N; auto. unfold F in N.
  destruct (read h x) as (v,m). false.
Qed. (* TODO: simplify *)

Lemma proj_ro_toro : forall h,
  (toro h)^ro = (toro h).
Proof using.
  intros. unfold toro, proj.
  match goal with |- context [map_ ?f _] => set (F:=f) end.
  applys filter_all. intros x K. rew_fmap* in K.
  erewrite read_map; auto. unfold F.
  destruct (read h x) as (v,m). auto.
Qed. (* TODO: simplify *)

Lemma toro_proj_ro : forall h,
  toro (h^ro) = h^ro.
Proof using.
  intros. unfold toro. applys map_id. intros x (v,m) D Ey.
  unfold proj in *.
  match type of D with context [filter ?f _] => set (F:=f) in * end.
  lets (Dd&Px&E): indom_filter_inv D.
  unfold F in Px. destruct (read h x) as (v',m'). subst. congruence.
Qed. (* TODO: simplify *)

Lemma toro_idempotent : forall h,
  toro (toro h) = toro h.
Proof using.
  intros. unfold toro. applys map_id. intros x (v,m) D Ey.
  unfold proj in *.
  match type of D with context [map_ ?f _] => set (F:=f) in * end.
  rew_fmap* in D. erewrite read_map in Ey; auto.
  unfolds F. destruct (read h x) as (v', m'). congruence.
Qed. (* TODO: simplify *)

Hint Rewrite indom_toro proj_rw_toro proj_ro_toro : rew_heap rew_fmap.

Lemma heap_state_toro : forall h,
  heap_state (toro h) = heap_state h.
Proof using.
  intros h. unfold heap_state, toro. applys extensionality.
  { intros x. rew_fmap*. }
  { intros x K. lets K': K. rewrite indom_map in K';[|typeclass].
    erewrite read_map; auto. rewrite indom_map in K';[|typeclass].
    do 2 (erewrite read_map; auto). destruct (read h x) as (v&m). auto. }
Qed. (* TODO: simplify *)

Hint Rewrite heap_state_toro : rew_fmap.

Lemma toro_empty :
  toro heap_empty = heap_empty.
Proof using.
  intros. unfold toro. rewrite* map_empty.
Qed.

Hint Rewrite toro_empty : rew_heap.

Lemma toro_fmap_union : forall h1 h2,
  toro (h1 \+ h2) = (toro h1) \+ (toro h2).
Proof using.
  intros. unfold toro. rewrite* map_union.
Qed.

Hint Rewrite toro_fmap_union : rew_fmap.

Lemma disjoint_toro_eq : forall h1 h2,
  disjoint h1 (toro h2) = disjoint h1 h2.
Proof using.
  extens. do 2 rewrite disjoint_eq_not_indom_both in *.
  rewrite* indom_toro.
Qed.

(* Note: needed only for the next lemma, for which a simpler
   proof might exist. *)
Lemma toro_decompose : forall h,
  toro h = (toro h^rw) \+ h^ro.
Proof using.
  intros. lets (E&D): heap_fmap_components h.
  rewrite E at 1. rewrite toro_fmap_union. rewrite* toro_proj_ro.
Qed.

Lemma heap_compat_toro_r : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat h1 (toro h2).
Proof using.
  introv (M1&M2). split.
  { rew_heap. splits; [auto|auto|].
    { rew_disjoint. split; [auto|].
      { rewrite disjoint_toro_eq. applys* disjoint_of_disjoint_components. } } }
  { rew_heap. rewrite toro_decompose. applys agree_union_r; [|auto].
    { applys agree_of_disjoint. rewrite* disjoint_toro_eq. } }
Qed.

Lemma heap_compat_toro_l : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat (toro h1) h2.
Proof using. autos* heap_compat_sym heap_compat_toro_r. Qed.

(** corollary *)
Lemma heap_compat_toro : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat (toro h1) (toro h2).
Proof using.
  introv M. autos* heap_compat_sym heap_compat_toro_r.
Qed.

(** corollary of heap_compat_refl_of_rw_empty *)
Lemma heap_compat_refl_toro : forall h,
  heap_compat (toro h) (toro h).
Proof using.
  intros. applys heap_compat_refl_of_rw_empty. rew_heap*.
Qed.

Lemma toro_union : forall h1 h2,
  heap_compat h1 h2 ->
  toro (h1 \u h2) = (toro h1) \u (toro h2).
Proof using.
  introv D. lets: heap_compat_toro D.
  do 2 rewrite* heap_union_eq_of_compat.
  rewrite* toro_fmap_union.
Qed.

Hint Rewrite toro_union : rew_heap.


(* ---------------------------------------------------------------------- *)
(* ** More properties of [heap_compat] *)

Lemma heap_compat_union_l_inv_l : forall h1 h2 h3,
  heap_compat (h1 \u h2) h3 ->
  heap_compat h1 h2 ->
  heap_compat h2 h3.
Proof using.
  hint heap_compat_proj.
  introv M1 M2. lets (D1&G1): M1. lets (D2&G2): M2.
  rew_fmap* in *. splits.
  { auto. } (* TODO: slow *)
  { forwards*: Fmap.agree_union_l_inv G1 G2. }
Qed.

Lemma heap_compat_union_l_inv_r : forall h1 h2 h3,
  heap_compat (h1 \u h2) h3 ->
  heap_compat h1 h2 ->
  heap_compat h1 h3.
Proof using.
  introv M1 M2. rewrite* heap_union_comm in M1.
  applys* heap_compat_union_l_inv_l.
Qed.

Lemma heap_compat_union_l_inv : forall h1 h2 h3,
  heap_compat (h1 \u h2) h3 ->
  heap_compat h1 h2 ->
  heap_compat h1 h3 /\ heap_compat h2 h3.
Proof using.
  autos* heap_compat_union_l_inv_l heap_compat_union_l_inv_r. (* TODO: slow *)
Qed.

Lemma heap_compat_union_r_inv : forall h1 h2 h3,
  heap_compat h1 (h2 \u h3) ->
  heap_compat h2 h3 ->
  heap_compat h1 h2 /\ heap_compat h1 h3.
Proof using.
  introv M1 M2. repeat rewrite (heap_compat_sym_eq h1) in *.
  applys* heap_compat_union_l_inv.
Qed.

Lemma disjoint_of_compat_ro_empty_l : forall h1 h2,
  heap_compat h1 h2 ->
  h1^ro = Fmap.empty ->
  disjoint h1 h2.
Proof using.
  introv D E. lets (E1&D1): (heap_components h1).
  lets (E2&D2): (heap_components h2).
  rewrite E1 in D. lets D1': heap_compat_of_disjoint D1.
  forwards (C1&C2): heap_compat_union_l_inv D; [auto|].
  rewrite E1,E2,E. rew_heap. lets (C1'&_): C1. rew_heap in C1'.
  rew_fmap; [|auto]. auto. applys* heap_compat_of_disjoint.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of empty *)

Lemma hempty_intro :
  \[] heap_empty.
Proof using. hnfs~. Qed.

Lemma hempty_inv : forall h,
  \[] h ->
  h = heap_empty.
Proof using. introv M. auto. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Core properties *)

Section Properties.
Implicit Types H : hprop.

Hint Resolve hempty_intro
  heap_compat_empty_l heap_compat_empty_r
  heap_union_empty_l heap_union_empty_r.

Lemma hexists_intro : forall A (J:A->hprop) x h,
  J x h ->
  (hexists J) h.
Proof using. introv M. exists~ x. Qed.

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  heap_compat h1 h2 ->
  (H1 \* H2) (h1 \u h2).
Proof using. intros. exists~ h1 h2. Qed.

Lemma hstar_hempty_l : forall H,
  hempty \* H = H.
Proof using.
  intros. applys pred_ext_1. intros h.
  iff (h1&h2&M1&M2&D&->) M.
  { rewrite (hempty_inv M1). rew_heap*. }
  { exists~ heap_empty h. }
Qed.

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof using.
  hint heap_union_comm, Fmap.agree_sym.
  intros. unfold hstar. extens. intros h.
  iff (h1&h2&M1&M2&D&U).
  { exists h2 h1. subst~. }
  { exists h2 h1. subst~. }
Qed.

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using.
  hint heap_compat_union_r, heap_compat_union_l, hstar_intro.
  intros. extens. intros h. split.
  { intros (h'&h3&(h1&h2&M2&P1&P2&->)&M3&M1&->).
    lets~ (M1a&M1b): heap_compat_union_l_inv M1.
    exists* h1 (h2 \u h3). rew_heap*. }
  { intros (h1&h'&P1&(h2&h3&M2&P2&P3&->)&M1&->).
    lets~ (M1a&M1b): heap_compat_union_r_inv M1.
    exists* (h1 \u h2) h3. rew_heap*. }
Qed.

Lemma hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof using.
  hint hexists_intro.
  intros. applys pred_ext_1. intros h. iff M.
  { destruct M as (h1&h2&(x&M1)&M2&D&U). exists* x h1 h2. }
  { destruct M as (x&(h1&h2&M1&M2&D&U)). exists* h1 h2. }
Qed.

Lemma hstar_hforall : forall H A (J:A->hprop),
  (hforall J) \* H ==> hforall (J \*+ H).
Proof using.
  intros. intros h M. destruct M as (h1&h2&M1&M2&D&U).
  intros x. exists~ h1 h2.
Qed.

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof using. introv W (h1&h2&?). exists* h1 h2. Qed.

Lemma haffine_hempty :
  haffine \[].
Proof using.
  introv K. rewrite (hempty_inv K). applys heap_affine_empty.
Qed.

Lemma haffine_hstar : forall H1 H2,
  haffine H1 ->
  haffine H2 ->
  haffine (H1 \* H2).
Proof using.
  introv M1 M2 (h1&h2&K1&K2&D&->). applys* heap_affine_union.
Qed.

End Properties.

End SepROCore.


(* ********************************************************************** *)
(* * Derived properties of the logic *)

(** Here, we instantiate the functors to obtained derived definitions,
  lemmas, notation, and tactics. *)

Module Export SepROSetup := SepSetup SepROCore.
Export SepROCore.

Local Open Scope heap_union_scope.

Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ---------------------------------------------------------------------- *)
(* ** Auxiliary lemmas *)

Section Aux.

Lemma hpure_inv : forall P h,
  \[P] h ->
  P /\ h = heap_empty.
Proof using.
  introv M. lets (HP&N): hpure_inv_hempty M. rewrite* (hempty_inv N).
Qed.

Lemma hpure_intro : forall P,
  P ->
  \[P] heap_empty.
Proof using. introv M. applys~ hpure_intro_hempty. applys hempty_intro. Qed.

End Aux.

Global Opaque heap_affine.


(* ---------------------------------------------------------------------- *)
(* ** Singleton heap *)

Definition hsingle (l:loc) (v:val) : hprop :=
  fun h => h = Fmap.single l (v, mode_rw)
           /\ l <> null.

(* equivalent to:  h^rw = Fmap.single l v /\ h^ro = Fmap.empty /\ l <> null. *)

Notation "l '~~~>' v" := (hsingle l v)
  (at level 32, no associativity) : heap_scope.
(* TODO: use only one arrow *)
Notation "l '~~>' v" := (hsingle l v)
  (at level 32, no associativity) : heap_scope.

Lemma hsingle_intro : forall l v,
  l <> null ->
  (l ~~~> v) (Fmap.single l (v,mode_rw)).
Proof using. intros. split~. Qed.

Lemma hsingle_inv : forall h l v,
  (l ~~~> v) h ->
  h = Fmap.single l (v,mode_rw) /\ (l <> null).
Proof using. auto. Qed.

Lemma proj_single : forall l v m1 m2,
  proj m1 (Fmap.single l (v, m2)) =
  If m1 = m2 then Fmap.single l (v, m2) else Fmap.empty.
Proof using. intros. unfold proj. rew_fmap*. Qed.

(* Corollary for autorewrite *)
Lemma single_rw : forall l v,
  ((Fmap.single l (v, mode_rw))^rw) = Fmap.single l (v, mode_rw).
Proof using. intros. rewrite proj_single. case_if*. Qed.

(* Corollary for autorewrite *)
Lemma single_ro : forall l v,
  ((Fmap.single l (v, mode_rw))^ro) = Fmap.empty.
Proof using. intros. rewrite proj_single. case_if*. Qed.

Hint Rewrite single_rw single_ro : rew_fmap.

Lemma hstar_hsingle_same_loc : forall (l:loc) (v1 v2:val),
  (l ~~~> v1) \* (l ~~~> v2) ==> \[False].
Proof using.
  intros. intros h (h1&h2&(E1&N1)&(E2&N2)&(D&A)&E). subst. false.
  rew_fmap in D. applys* Fmap.disjoint_single_single_same_inv D.
Qed.

Arguments hstar_hsingle_same_loc : clear implicits.

Global Opaque hsingle.

(* ** Configure [hcancel] to make it aware of [hsingle] *)

(* not needed? *)
Ltac xsimpl_hook H ::=
  match H with
  | hsingle _ _ => xsimpl_cancel_same H
  end.

Global Opaque hsingle.


(* ---------------------------------------------------------------------- *)
(* ** Compatibility with singleton heaps *)
(* TODO: simplify this section *)

Lemma disjoint_of_compat_single : forall p v h1 h2,
  heap_compat h1 h2 ->
  h1 = (single p (v, rw)) ->
  forall w,
  disjoint (single p w) (heap_state h2).
Proof using.
  introv D ->. intros.
  forwards D': disjoint_of_compat_ro_empty_l D. { rew_fmap*. }
  lets D'': disjoint_heap_state (rm D'). rew_fmap in D''.
  rewrite disjoint_eq_not_indom_both in *.
  intros x. specializes D'' x. rewrite indom_single_eq in *. autos*.
Qed.

Lemma heap_compat_single_set : forall p v w h1 h2,
  heap_compat h1 h2 ->
  h1 = (single p (v, rw)) ->
  heap_compat (single p (w, rw)) h2.
Proof using.
  introv (D&G) ->. unfolds. rew_fmap in *. split~.
  destruct D as (D1&D2&D3). splits; [|auto|].
  { rewrite disjoint_eq_not_indom_both in *.
    intros x. specializes D1 x. rewrite indom_single_eq in *. autos*. }
  { rewrite disjoint_eq_not_indom_both in *.
    intros x. specializes D3 x. rewrite indom_single_eq in *. autos*. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Definitions of [duplicatable] *)

Definition duplicatable (H:hprop) : Prop :=
  H ==> H \* H.


(* ---------------------------------------------------------------------- *)
(* ** Definitions and properties of [onlyrw] *)

Definition onlyrw (H:hprop) : Prop :=
  forall h, H h -> h^ro = Fmap.empty.

Definition onlyrw_post A (Q:A->hprop) : Prop :=
  forall x, onlyrw (Q x).

Lemma onlyrw_ro : forall H h,
  onlyrw H ->
  H h ->
  h^ro = Fmap.empty.
Proof using. introv N K. applys* N. Qed.

Lemma onlyrw_rw : forall H h,
  onlyrw H ->
  H h ->
  h^rw = h.
Proof using.
  introv N K. specializes N (rm K).
  forwards (E&_): heap_components h.
  rewrite N in E. rew_fmap* in E.
Qed.

Lemma onlyrw_of_haffine : forall H,
  haffine H ->
  onlyrw H.
Proof using.
  introv M. intros h K. rewrite haffine_eq in M.
  specializes M K. applys* heap_affine_onlyrw.
Qed.

Lemma onlyrw_hempty :
  onlyrw \[].
Proof using.
  Transparent hempty hpure.
  introv M. unfolds hempty, hpure. subst. rew_heap*.
Qed.

Lemma onlyrw_hpure : forall P,
  onlyrw \[P].
Proof using.
  Transparent hpure.
  introv (p&M). unfolds hempty. subst. rew_heap*.
Qed.

Lemma onlyrw_hgc :
  onlyrw \GC.
Proof using.
  introv (H&M). rewrite hstar_hpure_l in M. destruct M as (F&R).
  applys* heap_affine_onlyrw. rewrite haffine_eq in F. applys* F.
Qed.

Lemma onlyrw_hempty' : (* simpler proof *)
  onlyrw \[].
Proof using.
  intros. rewrite hempty_eq_hpure_true. applys~ onlyrw_hpure.
Qed.

Lemma onlyrw_hsingle : forall l v,
  onlyrw (hsingle l v).
Proof using.
  Transparent hsingle.
  introv (E&N). subst h. rew_fmap*.
Qed.

Lemma onlyrw_hstar : forall H1 H2,
  onlyrw H1 ->
  onlyrw H2 ->
  onlyrw (H1 \* H2).
Proof using.
  introv N1 N2 (h1&h2&P1&P2&M1&->). rew_heap*.
  rewrites (>> N1 P1). rewrites (>> N2 P2). rew_heap*.
Qed.

Lemma onlyrw_hexists : forall A (J:A->hprop),
  onlyrw_post J ->
  onlyrw (hexists J).
Proof using. introv M (x&N). rewrites~ (>> M N). Qed.

Hint Resolve onlyrw_hempty onlyrw_hstar onlyrw_hgc : onlyrw.

(* Remaining lemmas are not needed for the soundness proof,
   but may be needed by clients. *)

Lemma onlyrw_hforall_inhab : forall `{Inhab A} (J:A->hprop),
  onlyrw_post J ->
  onlyrw (hforall J).
Proof using.
  introv IA M N. lets M': M (arbitrary (A:=A)). lets N': N (arbitrary (A:=A)).
  applys M' N'.
Qed.

Lemma onlyrw_hforall : forall A (x:A) (J:A->hprop),
  onlyrw (J x) ->
  onlyrw (hforall J).
Proof using. introv M N. applys M N. Qed.

Lemma onlyrw_hor : forall H1 H2,
  onlyrw H1 ->
  onlyrw H2 ->
  onlyrw (hor H1 H2).
Proof using. introv M1 M2. applys onlyrw_hexists. intros b. case_if*. Qed.

Lemma onlyrw_hand_l : forall H1 H2,
  onlyrw H1 ->
  onlyrw (hand H1 H2).
Proof using. introv M1. applys* onlyrw_hforall true. Qed.

Lemma onlyrw_hand_r : forall H1 H2,
  onlyrw H2 ->
  onlyrw (hand H1 H2).
Proof using. introv M1. applys* onlyrw_hforall false. Qed.

Lemma onlyrw_himpl : forall H1 H2,
  onlyrw H2 ->
  (H1 ==> H2) ->
  onlyrw H1.
Proof using. introv HS HI M. lets: HI M. applys* HS. Qed.

(* Note: onlyrw_hwand is not true *)

Lemma onlyrw_hpure_star_hpure : forall (P:Prop) H,
  (P -> onlyrw H) ->
  onlyrw (\[P] \* H).
Proof using.
  introv N (h1&h2&P1&P2&M1&->). rew_heap*.
  lets (MP&ME): hpure_inv P1. rewrites (rm ME).
  rew_heap. rewrites~ (>> N P2).
Qed.


(* ---------------------------------------------------------------------- *)
(* ** onlyro *)

Definition onlyro (H:hprop) : Prop :=
  forall h, H h -> h^rw = Fmap.empty.

Definition onlyro_post A (Q:A->hprop) : Prop :=
  forall x, onlyro (Q x).

Lemma onlyro_rw : forall H h,
  onlyro H ->
  H h ->
  h^rw = Fmap.empty.
Proof using. introv N K. applys* N. Qed.

Lemma onlyro_hempty :
  onlyro hempty.
Proof using.
  introv M. unfolds hempty, hpure. subst. rew_heap*.
Qed.

Lemma onlyro_hstar : forall H1 H2,
  onlyro H1 ->
  onlyro H2 ->
  onlyro (H1 \* H2).
Proof using.
  introv N1 N2 (h1&h2&P1&P2&M1&EQ). subst. rew_heap*.
  rewrite* N1. rewrite* N2. rew_heap*.
Qed.

Hint Resolve onlyro_hstar onlyro_hempty : onlyro.

(* Remaining lemmas are not needed for the soundness proof,
   but may be needed by clients. *)
(* TODO: maybe try to factorize proofs/statements with onlyrw? *)

Lemma onlyro_hexists : forall A (J:A->hprop),
  onlyro_post J ->
  onlyro (hexists J).
Proof using. introv M (x&N). rewrites~ (>> M N). Qed.

Lemma onlyro_hforall_inhab : forall `{Inhab A} (J:A->hprop),
  onlyro_post J ->
  onlyro (hforall J).
Proof using.
  introv IA M N. lets M': M (arbitrary (A:=A)). lets N': N (arbitrary (A:=A)).
  applys M' N'.
Qed.

Lemma onlyro_hforall : forall A (x:A) (J:A->hprop),
  onlyro (J x) ->
  onlyro (hforall J).
Proof using. introv M N. applys M N. Qed.

Lemma onlyro_hor : forall H1 H2,
  onlyro H1 ->
  onlyro H2 ->
  onlyro (hor H1 H2).
Proof using. introv M1 M2. applys onlyro_hexists. intros b. case_if*. Qed.

Lemma onlyro_hand_l : forall H1 H2,
  onlyro H1 ->
  onlyro (hand H1 H2).
Proof using. introv M1. applys* onlyro_hforall true. Qed.

Lemma onlyro_hand_r : forall H1 H2,
  onlyro H2 ->
  onlyro (hand H1 H2).
Proof using. introv M1. applys* onlyro_hforall false. Qed.

Lemma onlyro_himpl : forall H1 H2,
  onlyro H2 ->
  (H1 ==> H2) ->
  onlyro H1.
Proof using. introv HS HI M. lets: HI M. applys* HS. Qed.


(* ---------------------------------------------------------------------- *)

Lemma union_same : forall h,
  union h h = h.
Proof using.
  intros. applys extensionality.
  { intros x. extens. rewrite* indom_union_eq. }
  { intros x Dx. rewrite* indom_union_eq in Dx. rewrite* read_union_l. }
Qed.

Hint Rewrite union_same : fmap.

(* ---------------------------------------------------------------------- *)
(* ** Definitions and properties of [RO] *)

Section RO.

Definition RO (H:hprop) : hprop :=
  fun h => exists h', H h' /\ h = toro h'.

Lemma toro_pred : forall (H:hprop) h,
  H h ->
  RO H (toro h).
Proof using.
  introv N. exists h. split~.
Qed.

Lemma RO_heap_empty : forall (H:hprop),
  H heap_empty ->
  RO H heap_empty.
Proof using. introv N. exists heap_empty. rew_heap*. Qed.

Hint Resolve toro_pred RO_heap_empty.

Lemma RO_duplicatable : forall H,
  duplicatable (RO H).
Proof using.
  intros H h M. lets (h'&M1&M2): M. subst.
  lets D: heap_compat_refl_toro h'. do 2 esplit. splits*.
  rewrite* heap_union_eq_of_compat. rewrite* union_same.
Qed.

Lemma RO_covariant : forall H1 H2,
  H1 ==> H2 ->
  (RO H1) ==> (RO H2).
Proof using.
  introv M. intros h (h'&M1&->). auto.
Qed.

Lemma RO_RO : forall H,
  RO (RO H) = RO H.
Proof using.
  hint toro_idempotent.
  intros. apply pred_ext_1. intros h. unfolds RO.
  iff (h'&(h''&M1'&->)&->) (h'&M1&->).
  { exists* h''. }
  { exists* (toro h'). }
Qed.

Lemma RO_hempty :
  RO \[] = \[].
Proof using.
  intros. apply pred_ext_1. intros h.
  unfold hempty. iff (h'&->&->) ->; rew_heap*.
Qed.

Lemma RO_pure : forall P,
  RO \[P] = \[P].
Proof using.
  hint hpure_intro.
  intros. apply pred_ext_1. intros h.
  iff (h'&(M1p&M2)&->) (MP&M1).
  { lets ->: hempty_inv M2. rew_heap*. }
  { lets ->: hempty_inv M1. auto. }
Qed.

(* Alternative proof *)
Lemma RO_hempty' :
  RO \[] = \[].
Proof using.
  intros. rewrite hempty_eq_hpure_true. rewrite~ RO_pure.
Qed.

Lemma RO_hexists : forall A (J:A->hprop),
    RO (hexists J)
  = \exists x, RO (J x).
Proof using.
  hint hexists_intro.
  intros. apply pred_ext_1. intros h.
  iff (h'&(x&M1)&->) (x&(h'&M1&->)); autos*.
Qed.

Lemma RO_if : forall (b:bool) H1 H2,
    RO (if b then H1 else H2)
  = (if b then RO H1 else RO H2).
Proof using. intros. destruct* b. Qed.

Lemma RO_or : forall H1 H2,
     RO (hor H1 H2)
  ==> hor (RO H1) (RO H2).
Proof using.
  intros. unfolds hor. rewrite RO_hexists.
  applys himpl_hexists. intros b. destruct* b.
Qed.

Lemma RO_hstar : forall H1 H2,
  RO (H1 \* H2) ==> (RO H1 \* RO H2).
Proof using.
  hint hstar_intro.
  intros. intros h (h'&(h1&h2&N1&P1&P2&->)&->).
  lets C: heap_compat_toro P2.
  exists (toro h1) (toro h2). rew_heap*.
Qed.

Arguments RO_hstar : clear implicits.

Lemma onlyro_RO : forall H,
  onlyro (RO H).
Proof using.
  introv (h'&K&E). subst. rew_heap*.
Qed.

End RO.


(* ********************************************************************** *)
(* * Elimination lemmas useful to simplify proofs *)

Lemma onlyrw_rw_elim : forall H h,
  onlyrw H ->
  H h ->
  H (h^rw).
Proof using. introv N K. rewrites* (>> onlyrw_rw K). Qed.

Lemma onlyrw_onlyro_rw_elim : forall HF HR h,
  onlyrw HF ->
  onlyro HR ->
  (HF \* HR) h ->
  HF (h^rw).
Proof using.
  introv NF NR (h1&h2&K1&K2&D&->). rew_heap*.
  rewrites* (>> onlyro_rw K2).
  rewrites* (>> onlyrw_rw K1).
  rew_heap*.
Qed.


(* ********************************************************************** *)
(* isframe *)

Definition isframe (HI HO:hprop) : Prop :=
  exists HR, onlyrw HO /\ onlyro HR /\ HI = HO \* HR.

Lemma isframe_rw_elim : forall HI HO h,
  isframe HI HO ->
  HI h ->
  HO (h^rw).
Proof using.
  introv (R&NF&NR&->) M. applys* onlyrw_onlyro_rw_elim.
Qed.

Lemma isframe_hempty :
  isframe \[] \[].
Proof using.
  exists \[]. splits*.
  { auto with onlyrw. }
  { auto with onlyro. }
  { subst. xsimpl. }
Qed.

Lemma isframe_onlyrw : forall HI HO H,
  isframe HI HO ->
  onlyrw H ->
  isframe (HI \* H) (HO \* H).
Proof using.
  introv (HR&NF&NR&E) N.
  exists HR. splits*.
  { auto with onlyrw. }
  { subst. xsimpl. }
Qed.

Lemma isframe_onlyro : forall HI HO H,
  isframe HI HO ->
  onlyro H ->
  isframe (HI \* H) HO.
Proof using.
  introv (HR&NF&NR&E) N.
  exists (HR \* H). splits*.
  { auto with onlyro. }
  { subst. xsimpl. }
Qed.

Lemma onlyrw_of_isframe : forall HI HO,
  isframe HI HO ->
  onlyrw HO.
Proof using. introv (R&NF&NR&E) M. auto. Qed.


(* ********************************************************************** *)
(* * Reasoning rules, high-level proofs *)

Implicit Types p : loc.
Implicit Types v : val.


(* ---------------------------------------------------------------------- *)
(* ** Definition of Hoare triples in a logic with read-only predicates *)

Definition hoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall h, H h -> exists h' v, eval (heap_state h) t (heap_state h') v
                             /\ Q v (h'^rw)
                             /\ h'^ro = h^ro.

Lemma hoare_conseq : forall t H' Q' H Q,
  hoare t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoare t H Q.
Proof using.
  introv M MH MQ HF. forwards (h'&v&R&K&S): M h.
  { applys* MH. }
  exists h' v. splits~. { applys MQ K. }
Qed.

Lemma hoare_frame_read_only : forall t H1 Q1 H2,
  hoare t (H1 \* RO H2) Q1 ->
  onlyrw H2 ->
  hoare t (H1 \* H2) (Q1 \*+ H2).
Proof using.
  hint heap_compat_toro_r, heap_compat_proj_l,
    heap_compat_proj_r, heap_compat_union_r.
  hint heap_compat_proj, heap_compat_of_disjoint.
  introv M N. intros ? (h1&h2&P1&P2&R1&->).
  forwards (h'&v&R&L&S): M (h1 \u toro h2).
  { exists h1 (toro h2). splits~. { applys* toro_pred. } }
  (* Adding facts *)
  lets (Eh'&Dh'): heap_fmap_components h'.
  rewrite S in Dh'.
  asserts C': (heap_compat h'^rw (h1^ro \u h2)).
  { rew_fmap in Dh';[|auto]. applys heap_compat_of_disjoint. rew_fmap; [|auto].
    rewrite disjoint_union_eq_r.
    rewrite <- (disjoint_toro_eq _ h2). auto. }
  (* Rest of the proof *)
  rewrite Eh' in R. rewrite S in R. rew_heap~ in R.
  exists (h'^rw \u h1^ro \u h2) v. splits.
  { rew_fmap~. rew_fmap~ in R. }
  { forwards~ (G1&G2): heap_compat_union_r_inv C'. rew_heap*.
    rewrites~ (@onlyrw_rw H2 h2). applys* hstar_intro. }
  { rew_heap*. }
Qed.

Lemma hoare_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, hoare t (J x) Q) ->
  hoare t (hexists J) Q.
Proof using. introv M. intros h (x&Hh). applys M Hh. Qed.

Lemma hoare_hpure : forall t (P:Prop) H Q,
  (P -> hoare t H Q) ->
  hoare t (\[P] \* H) Q.
Proof using.
  introv M. intros h (h1&h2&(HP&M1)&M2&D&->).
  lets ->: hempty_inv M1. rew_heap*.
Qed.


(* ########################################################### *)
(** ** Reasoning rules for terms, for Hoare triples. *)

Lemma hoare_val : forall HI HO v,
  isframe HI HO ->
  hoare (trm_val v) HI (fun r => \[r = v] \* HO).
Proof using.
  introv HF. intros h K. exists h v. splits~.
  { applys eval_val. }
  { rewrite hstar_hpure_l. split~. applys* isframe_rw_elim. }
Qed.

Lemma hoare_fix : forall HI HO f x t1,
  isframe HI HO ->
  hoare (trm_fix f x t1) HI (fun r => \[r = (val_fix f x t1)] \* HO).
Proof using.
  introv HF. intros h K. exists h (val_fix f x t1). splits~.
  { applys eval_fix. }
  { rewrite hstar_hpure_l. split~. applys* isframe_rw_elim. }
Qed.

Lemma hoare_app_fix : forall v1 v2 (f:var) x t1 H Q,
  v1 = val_fix f x t1 ->
  f <> x ->
  hoare (subst x v2 (subst f v1 t1)) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof using.
  introv E D M. intros s K0. forwards (s'&v&R1&K1&E1): (rm M) K0.
  exists s' v. splits~. { applys* eval_app E R1. auto_false. }
Qed.

(* Note: the order of the heap predicates is carefully
   chosen so as to simplify the proof. *)
Lemma hoare_let : forall x t1 t2 H1 H2 Q1 Q HI HO,
  isframe HI HO ->
  hoare t1 (RO H2 \* HI \* H1) (Q1 \*+ HO) ->
  (forall v H3, onlyro H3 -> hoare (subst x v t2) (Q1 v \* HO \* H2 \* H3) (Q \*+ HO)) ->
  hoare (trm_let x t1 t2) (H2 \* HI \* H1) (Q \*+ HO).
Proof using.
  introv HF M1 M2. intros h K.
  destruct K as (h2&hr&P1&P2&D1&U1).
  destruct P2 as (hI&h1&PI&PO&D2&U2).
  rewrite U2 in D1. lets (D3&D4): heap_compat_union_r_inv D1 D2.
  forwards (h1'&v1&R1&K1&E1): (rm M1) (toro h2 \u hI \u h1).
  { applys* hstar_intro.
    { applys* toro_pred. }
    { applys* hstar_intro. }
    { applys* heap_compat_union_r; applys* heap_compat_toro_l. } }
  (* Adding compatibility facts *)
  lets: disjoint_components h1'. rewrite E1 in H.
    rew_fmap in H; [|auto|auto].
  2: { applys heap_compat_toro_l. auto. }
  rewrite disjoint_union_eq_r in H. destruct H as (H&H').
    rewrite disjoint_toro_eq in H.
  lets Hs: H. lets: heap_compat_of_disjoint Hs.
  lets (X&Y): heap_fmap_components h2.
    rewrite X in H. rewrite disjoint_union_eq_r in H,H'.
  asserts: (heap_compat h1'^rw (hI^ro \u h1^ro)).
  { applys heap_compat_union_r.
        { applys* heap_compat_of_disjoint. }
        { applys* heap_compat_of_disjoint. }
        { applys* heap_compat_proj. } }
  asserts: (heap_compat h2 (hI^ro \u h1^ro)).
  { applys heap_compat_union_r.
        { applys* heap_compat_proj_r. }
        { applys* heap_compat_proj_r. }
        { applys* heap_compat_proj. } }
  asserts: (heap_compat h1'^rw (h2 \u hI^ro \u h1^ro)).
   { applys* heap_compat_union_r. }
  (* Remaining of the proof *)
  forwards (h2'&v2&R2&K2&E2): (rm M2) v1 (= hI^ro \u h1^ro) (h1'^rw \u h2 \u hI^ro \u h1^ro).
  { intros ? ->. rew_heap*. }
  { rewrite <- hstar_assoc. applys* hstar_intro.
    { applys* hstar_intro. } }
  lets D1': heap_compat_toro_l D1.
  lets D1'': D1'. rew_fmap* in D1''. (* TODO: cleanup *)
  exists h2' v2. splits*.
  { applys eval_let_trm (heap_state h1').
    { applys_eq R1. subst h hr. rew_fmap*. }
    { applys_eq R2. lets (E1'&_): heap_fmap_components h1'.
      rewrite E1' at 1. rewrite E1. rew_fmap*. } }
  { rewrite E2. rewrite U1,U2. rew_fmap*. }
Qed.

Lemma hoare_if : forall (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros h Hh. forwards* (h1'&v1&R1&K1&E1): (rm M1).
  exists h1' v1. splits*. { applys* eval_if. }
Qed.

Lemma hoare_ref : forall HI HO v,
  isframe HI HO ->
  hoare (val_ref v)
    (HI)
    (fun r => (\exists p, \[r = val_loc p] \* p ~~> v) \* HO).
Proof using.
  hint hsingle_intro.
  introv NF. intros s1 K0.
  forwards~ (p&D&N): (Fmap.single_fresh 0%nat s1 (v,mode_rw)).
  lets D': disjoint_heap_state D. rew_fmap* in D'.
  lets D'': heap_compat_of_disjoint D.
  exists (heap_union (Fmap.single p (v,mode_rw)) s1) (val_loc p). splits.
  { rew_fmap*. applys~ eval_ref_sep. }
  { rew_heap*. applys~ hstar_intro.
    { rew_fmap. exists p. rewrite~ hstar_hpure_l. }
    { applys* isframe_rw_elim. } }
  { rew_fmap*. }
Qed.

Lemma hoare_get_ro : forall HI HO v p,
  isframe HI HO ->
  hoare (val_get p)
    (RO (p ~~> v) \* HI)
    (fun r => \[r = v] \* HO).
Proof using.
  introv NH. intros s (s1&s2&P1&P2&D&U).
  destruct P1 as (h'&K'&E). lets (->&N): hsingle_inv K'.
  exists s v. splits.
  { rew_fmap* in *. applys* eval_get_sep (heap_state s1) (heap_state s2);
    subst s s1; rew_fmap*. }
  { rewrite~ hstar_hpure_l. split~. subst s s1. rew_heap*.
    applys* isframe_rw_elim. }
  { auto. }
Qed.

Lemma hoare_set : forall HI HO w p v,
  isframe HI HO ->
  hoare (val_set (val_loc p) v)
    ((p ~~> w) \* HI)
    (fun r => \[r = val_unit] \* (p ~~> v) \* HO).
Proof using.
  introv NH. intros s1 K0.
  destruct K0 as (h1&h2&P1&P2&D&U). lets (K&N): hsingle_inv P1.
  forwards D': disjoint_of_compat_single D K w.
  lets: heap_compat_single_set w D.
  exists (heap_union (single p (v,mode_rw)) h2) val_unit. splits.
  { subst h1. applys* eval_set_sep (single p w) (single p v) (heap_state h2);
    subst; rew_fmap*. }
  { rewrite hstar_hpure_l. split~.
    { rew_heap*. applys* hstar_intro.
      { rew_fmap. applys* hsingle_intro. } { applys* isframe_rw_elim. } } }
  { subst. rew_fmap*. }
Qed.

Lemma hoare_free : forall HI HO p v,
  isframe HI HO ->
  hoare (val_free (val_loc p))
    ((p ~~> v) \* HI)
    (fun r => \[r = val_unit] \* HO).
Proof using.
  introv NH. intros s1 K0.
  destruct K0 as (h1&h2&P1&P2&D&U). lets (K&N): hsingle_inv P1.
  forwards D': disjoint_of_compat_single D K v.
  exists h2 val_unit. splits.
  { subst h1. applys* eval_free_sep; subst; rew_fmap*. }
  { rewrite hstar_hpure_l. split~. applys* isframe_rw_elim. }
  { subst. rew_fmap*. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Definition of SL triples in a logic with read-only predicates *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall HI HO, isframe HI HO ->
  hoare t (H \* HI) (Q \*+ HO \*+ \GC).

(** Equivalent definition *)

Definition triple' (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall HF HR, onlyrw HF -> onlyro HR ->
    hoare t (H \* HF \* HR) (Q \*+ HF \*+ \GC).

Lemma triple_eq_triple' : triple = triple'.
Proof using.
  extens. intros t H Q. iff M.
  { intros HF HR NF NR. lets HFa: isframe_onlyrw isframe_hempty NF.
    lets HFb: isframe_onlyro (rm HFa) NR. rew_heap in *. applys M HFb. }
  { intros HI HO (HR&NF&NR&E). subst HI. applys* M. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** SL rules structural *)

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using.
  introv M. intros HI HO FR. rewrite hstar_hexists.
  applys hoare_hexists. intros. applys* M.
Qed.

Lemma triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. intros HI HO FR. rewrite hstar_assoc.
  applys hoare_hpure. intros. applys* M.
Qed.
(* Note: [triple_hpure] can also be proved from [triple_hexists] *)

Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
  introv M MH MQ. intros HI HO FR. applys* hoare_conseq M.
  { xchanges MH. }
  { intros x. xchanges (MQ x). }
Qed.

Lemma triple_frame_onlyrw : forall t H1 Q1 H2,
  triple t H1 Q1 ->
  onlyrw H2 ->
  triple t (H1 \* H2) (Q1 \*+ H2).
Proof using.
  introv M N. intros HI HO HF.
  forwards~ HF': isframe_onlyrw H2 HF.
  forwards~ K: M HF'.
  applys hoare_conseq K; xsimpl.
Qed.

Lemma triple_frame_onlyro : forall t H1 Q1 H2,
  triple t H1 Q1 ->
  onlyro H2 ->
  triple t (H1 \* H2) Q1.
Proof using.
  introv M N. intros HI HO HF.
  forwards~ HF': isframe_onlyro H2 HF.
  forwards~ K: M HF'.
  applys hoare_conseq K; xsimpl.
Qed.

Lemma triple_conseq_frame : forall H Q t H1 Q1 H2,
  triple t H1 Q1 ->
  H ==> (H1 \* H2) ->
  (Q1 \*+ H2) ===> Q ->
  onlyrw H2 ->
  triple t H Q.
Proof using.
  introv M WH WQ N. applys triple_conseq WH WQ.
  applys* triple_frame_onlyrw.
Qed.

Lemma triple_frame_read_only : forall t H1 Q1 H2,
  triple t (H1 \* RO H2) Q1 ->
  onlyrw H2 ->
  triple t (H1 \* H2) (Q1 \*+ H2).
Proof using.
  introv M N. intros HI HO HF. specializes M HF.
  rewrite hstar_comm in M. rewrite <- hstar_assoc in M.
  forwards~ K: hoare_frame_read_only M.
  applys hoare_conseq K. { xsimpl. } { xsimpl. }
Qed.

Lemma triple_hgc_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.
Proof using.
  introv M. intros HI HO HF. applys* hoare_conseq M. { xsimpl. }
Qed.

Lemma triple_haffine_post : forall H' t H Q,
  triple t H (Q \*+ H') ->
  haffine H' ->
  triple t H Q.
Proof using.
  introv M F. applys triple_hgc_post. applys triple_conseq M; xsimpl.
Qed.

Lemma triple_hro_pre : forall t H H' Q,
  triple t H Q ->
  triple t (H \* RO H') Q.
Proof using.
  introv M. applys* triple_frame_onlyro. applys onlyro_RO.
Qed.

Lemma triple_haffine_pre : forall t H H' Q,
  triple t H Q ->
  haffine H' ->
  triple t (H \* H') Q.
Proof using.
  introv M F. applys~ triple_haffine_post H'.
  applys* triple_frame_onlyrw M.
  applys* onlyrw_of_haffine.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** SL rules for terms *)

Lemma triple_of_hoare : forall t H Q,
  (forall HI HO, isframe HI HO ->
     exists Q', hoare t (H \* HI) Q' /\ Q' ===> Q \*+ HO \*+ \GC) ->
  triple t H Q.
Proof using.
  introv M. intros HI HO HF. forwards* (Q'&R&W): M HF. applys* hoare_conseq R.
Qed.

Lemma triple_val : forall v,
  triple (trm_val v) \[] (fun r => \[r = v]).
Proof using.
  intros. intros HI HO HF. rew_heap.
  applys hoare_conseq.
  { applys* hoare_val. }
  { xsimpl. }
  { xsimpl*. }
Qed.

Lemma triple_val_framed : forall v H Q,
  H ==> Q v ->
  onlyrw H ->
  triple (trm_val v) H Q.
Proof using.
  introv M N. applys triple_conseq_frame N.
  { applys triple_val. }
  { xsimpl. }
  { xchanges M. intros ? ->. xsimpl*. }
Qed.

Lemma triple_fix : forall f x t1,
  triple (trm_fix f x t1) \[] (fun r => \[r = (val_fix f x t1)]).
Proof using.
  intros. intros HI HO HF. rew_heap.
  applys hoare_conseq.
  { applys* hoare_fix. }
  { xsimpl. }
  { xsimpl*. }
Qed.

Lemma triple_fix_framed : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  onlyrw H ->
  triple (trm_fix f x t1) H Q.
Proof using.
  introv M N. applys triple_conseq_frame N.
  { applys triple_fix. }
  { xsimpl. }
  { xchanges M. intros ? ->. xsimpl*. }
Qed.

Lemma triple_let : forall (z:var) t1 t2 H1 H2 Q Q1,
  triple t1 (H1 \* RO H2) Q1 ->
  (forall v, triple (subst1 z v t2) (Q1 v \* H2) Q) ->
  triple (trm_let z t1 t2) (H1 \* H2) Q.
Proof using.
  introv M1 M2.
  applys triple_of_hoare. intros HI HO HF.
  unfolds in M1.
  esplit. split.
  { applys hoare_conseq.
    { applys hoare_let H1 H2 (Q1 \*+ \GC) (Q \*+ \GC) HF.
      { applys hoare_conseq.
        { applys M1 HF. } { xsimpl. } { xsimpl. } }
      { intros v H3 N3. lets NO: onlyrw_of_isframe HF.
        forwards* HFa: isframe_onlyrw (HO \* \GC) isframe_hempty.
        { auto with onlyrw. }
        forwards* HFb: isframe_onlyro H3 (rm HFa). rew_heap in HFb.
        applys hoare_conseq.
        { applys M2 HFb. } { xsimpl. }
        { xsimpl. } } }
    { xsimpl. }
    { xsimpl. } }
  { xsimpl. }
Qed.

Lemma triple_if : forall (b:bool) t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros HI HO HF. applys hoare_if. applys~ M1.
Qed.

Lemma triple_app_fix : forall (f:var) F x X t1 H Q,
  F = val_fix f x t1 ->
  f <> x ->
  triple (subst2 f F x X t1) H Q ->
  triple (trm_app F X) H Q.
Proof using.
  introv EF N M. intros HI HO HF. applys* hoare_app_fix EF N.
Qed.

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists l, \[r = val_loc l] \* l ~~~> v).
Proof using.
  intros. applys~ triple_of_hoare.
  intros HI HO HF. esplit. split.
  { rew_heap. applys* hoare_ref HF. } { xsimpl*. }
Qed.

Lemma triple_get_ro : forall v l,
  triple (val_get (val_loc l))
    (RO (l ~~~> v))
    (fun x => \[x = v]).
Proof using.
  intros. applys triple_of_hoare. intros HI HO HF.
  esplit; split. { applys* hoare_get_ro. } { xsimpl*. }
Qed.

Lemma triple_set : forall (w:val) l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => \[r = val_unit] \* l ~~~> w).
Proof using.
  intros. applys triple_of_hoare. intros HI HO HF.
  esplit; split. { applys* hoare_set. } { xsimpl*. }
Qed.

Lemma triple_set' : forall (w:val) l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => l ~~~> w).
Proof using.
  intros. applys triple_conseq.
  { applys* triple_set. } { xsimpl*. } { xsimpl*. }
Qed.

Lemma triple_free : forall l v,
  triple (val_free (val_loc l))
    (l ~~~> v)
    (fun r => \[r = val_unit]).
Proof using.
  intros. applys triple_of_hoare. intros HI HO HF.
  esplit; split. { applys* hoare_free. } { xsimpl*. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Extra *)

Lemma decomposition : forall H,
  H ==> (\exists H1 H2, \[onlyrw H1] \* \[onlyro H2] \* (H1 \* H2)).
Proof using.
  intros H h K. forwards (->&_): (heap_components h).
  exists (= h^rw) (= h^ro). do 2 rewrite hstar_hpure. splits.
  { intros ? ->. rew_heap*. }
  { intros ? ->. rew_heap*. }
  { applys* hstar_intro. applys heap_compat_of_disjoint. applys disjoint_components. }
Qed.

Lemma hoare_let' : forall x t1 t2 H1 H2 Q1 Q HI HO,
  isframe HI HO ->
  hoare t1 (H1 \* RO H2 \* HI) (Q1 \*+ HO) ->
  (forall v H3, onlyro H3 -> hoare (subst x v t2) (Q1 v \* HO \* H2 \* H3) (Q \*+ HO)) ->
  hoare (trm_let x t1 t2) (H1 \* H2 \* HI) (Q \*+ HO).
Proof using.
  introv HF M1 M2. rewrite hstar_comm_assoc in M1. rewrite (hstar_comm H1) in M1.
  rewrite (hstar_comm H1). rewrite hstar_assoc. applys* hoare_let.
Qed.

Lemma hoare_named_heap : forall t H Q,
  (forall h, H h -> hoare t (= h) Q) ->
  hoare t H Q.
Proof using. introv M. intros h Hh. applys* M. Qed.
