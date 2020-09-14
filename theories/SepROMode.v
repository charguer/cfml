(**

This file formalizes "Separation Logic with Temporary
Read-Only Permissions", as described in the ESOP'17
paper by Arthur Charguéraud and François Pottier.

This file contains:
- a definition of heaps as pairs of states,
- an instantiation of the functor from the file SepFunctor.v,
- a definition of triples,
- statement and proofs of SL reasoning rules.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Export Semantics SepFunctor. 
From Sep Require Import Fmap.
Import NotationForFmapDisjoint.
Open Scope fmap_scope.
Arguments exist [A] [P].


Generalizable Variables A B.


Hint Mode Inhab + : typeclass_instances.

(* TODO:

Module FMaps.
Section Map.
Transparent Fmap.map.
(* TODO: this function only maps values, we'd need another function to map keys as well *)

Program Definition map_ A B1 B2 `{Inhab B1} `{Inhab B2} (f:A->B1->B2) (M:fmap A B1) : fmap A B2 :=
  Fmap.make (fun (x:A) => match Fmap.read M x with
    | None => None
    | Some y => Some (f x y)
    end) _.
(*
Transparent update (*update_inst*) bag_update_as_union_single single_bind single_bind_inst LibMap.union_inst LibContainer.union.
*)
Lemma map_update : forall A `{Inhab B1} `{Inhab B2} (f:A->B1->B2) (M:Fmap.map A B1) x y,
  map_ f (Fmap.update M x y) = Fmap.update (map_ f M) x (f x y).
Proof using.
  intros. extens. intros a. unfold map_. simpl. unfold bag_update_as_union_single.
  unfold single_bind. simpl. unfold single_bind_impl. unfold LibContainer.union. simpl.
  unfold LibMap.union_impl.
  case_if; subst. autos*. destruct* (M a). (* TODO: cleanup *)
Qed.

Transparent dom dom_inst.

Lemma dom_map : forall A `{Inhab B1} `{Inhab B2} (f:A->B1->B2) (M:map A B1),
  dom (map_ f M) = dom M.
Proof using.
  intros. unfold map_. simpl. unfold dom_impl.
  fequal. extens. intros x. destruct (M x); auto_false.
Qed.

Transparent read LibMap.read_inst.

Lemma read_map : forall A `{Inhab B1} `{Inhab B2} (f:A->B1->B2) (M:map A B1) (x:A),
  x \indom M ->
  (map_ f M)[x] = f x (M[x]).
Proof using.
  introv Hx. unfold map_. simpl. unfold read, LibMap.read_inst. unfold LibMap.read_impl.
  unfold dom, LibMap.dom_inst, dom_impl in Hx. rewrite in_set_st_eq in Hx.
  destruct (M x); auto_false.
Qed.

Axiom extens : forall A `{Inhab B} (M1 M2:map A B),
  dom M1 = dom M2 ->
  (forall (x:A), x \indom M1 -> M1[x] = M2[x]) ->
  M1 = M2.

End Map.

Section Filter.
Transparent map.

Definition filter A `{Inhab B} (f:A->B->Prop) (M:map A B) : map A B :=
  fun (x:A) => match M x with
    | None => None
    | Some y => If f x y then Some y else None
    end.

Transparent update bag_update_as_union_single single_bind single_bind_inst LibMap.union_inst LibContainer.union.

Transparent dom dom_inst.

Lemma dom_filter : forall A `{Inhab B} (f:A->B->Prop) (M:map A B),
  dom (filter f M) \c dom M.
Proof using.
Admitted.

Transparent read LibMap.read_inst.

Lemma read_filter : forall A `{Inhab B} (f:A->B->Prop) (M:map A B) x,
  x \indom M ->
  f x (M[x]) ->
  (filter f M)[x] = M[x].
Proof using.
Admitted.

End Filter.

End FMaps.
*)



Section FmapProp.
Variables (A B : Type).
Implicit Types h : fmap A B.
Implicit Types x : A.
Implicit Types v : B.


Axiom indom_single_eq : forall x1 x2 v,
  indom (single x1 v) x2 = (x1 = x2).

Axiom indom_empty_eq : forall (IB:Inhab B) x,
  indom (@Fmap.empty A B) x = False.

Axiom indom_empty_iff_empty : forall (IB:Inhab B) h,
  (forall x, ~ indom h x) -> h = Fmap.empty.

Axiom indom_union_eq : forall (IB:Inhab B) h1 h2 x,
  indom (Fmap.union h1 h2) x = (indom h1 x \/ indom h2 x).

Axiom extensionality : forall (IB:Inhab B) h1 h2,
  (forall x, indom h1 x = indom h2 x) ->
  (forall x, indom h1 x -> Fmap.read h1 x = Fmap.read h2 x) ->
  h1 = h2.

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

(** Projections of the rw or ro part of a heap *)

Definition filter_mode (m:mode) (h:heap) : heap :=
  Fmap.filter (fun l '(v,m') => m = m') h.

Notation "h '^' m" := (filter_mode m h) : heap_scope.

(* Notation with higher priority *)

Notation "h '^rw'" := (filter_mode mode_rw h)
  (at level 9, format "h '^rw'") : heap_scope.
Notation "h '^ro'" := (filter_mode mode_ro h)
  (at level 9, format "h '^ro'") : heap_scope.


Open Scope heap_scope.

(** State of heap *)

Coercion heap_state (h : heap) : state :=
  Fmap.map_ (fun l '(v,m) => v) h.

(** Empty *)

Definition heap_empty : heap :=
  Fmap.empty.

Global Instance heap_inhab : Inhab heap.
Proof using. applys Inhab_of_val heap_empty. Qed.

(** Starable heaps: heaps that, on the intersection of their domains,
    associate locations to equal values, in read-only mode. *)

Definition heap_compat (h1 h2 : heap) : Prop :=
     Fmap.disjoint_3 (h1^rw) (h2^rw) (h1^ro \+ h2^ro)
  /\ Fmap.agree (h1^ro) (h2^ro).

(*
Definition heap_compat_alternative (h1 h2 : heap) : Prop :=
  forall l, indom h1 l -> indom h2 l ->
  let '(v1,m1) = h1[l] in
  let '(v2,m2) = h2[l] in
  v1 = v2 /\ m1 = m2 /\ m1 = mode_ro.
*)

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

(** Affinity is customizable; note that read-only permissions are
    not to be considered affine. *)

Parameter heap_affine : heap -> Prop. (* (h:heap) := True.*)

(*
Parameter heap_affine_ro : forall h,
  h^rw = Fmap.empty -> (* equivalent to [h^ro = h] *)
  heap_affine h.
*)

Parameter heap_affine_Normal : forall h,
  heap_affine h ->
  h^ro = Fmap.empty.

Parameter heap_affine_empty :
  heap_affine Fmap.empty.

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

(*
Lemma haffine_any : forall H,
  haffine H.                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          
Proof using. introv M. hnfs*. Qed.
*)

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

(* Hint Extern 1 (_ = _ :> heap) => fmap_eq. LATER *)

Tactic Notation "fmap_disjoint_pre" :=
  subst; rew_disjoint; jauto_set.

Hint Extern 1 (\# _ _) => fmap_disjoint_pre.
Hint Extern 1 (\# _ _ _) => fmap_disjoint_pre.

Hint Resolve Fmap.agree_sym.

(* LATER: move to TLC; (this cannot be put in TLCbuffer) *)
(* TODO: check whether still necessary *)
Ltac fequal_base ::=
  let go := f_equal_fixed; [ fequal_base | ] in
  match goal with
  | |- exist _ _ = exist _ _ => apply exist_eq_exist
  | |- (_,_,_) = (_,_,_) => go
  | |- (_,_,_,_) = (_,_,_,_) => go
  | |- (_,_,_,_,_) = (_,_,_,_,_) => go
  | |- (_,_,_,_,_,_) = (_,_,_,_,_,_) => go
  | |- _ => f_equal_fixed
  end.




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
(* TODO: remove tilde *)

Tactic Notation "rew_heap" "*" :=
  rew_heap; auto_tilde.
Tactic Notation "rew_heap" "*" "in" hyp(H) :=
  rew_heap in H; auto_tilde.
Tactic Notation "rew_heap" "*" "in" "*" :=
  rew_heap in *; auto_tilde.

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


(* ---------------------------------------------------------------------- *)

Lemma disjoint_filter_mode : forall h1 h2 m1 m2,
  disjoint h1 h2 ->
  disjoint (filter_mode m1 h1) (filter_mode m2 h2).
Proof using.
  introv D. autos* disjoint_filter disjoint_sym. (* TODO: slow *)
Qed.

Lemma agree_filter_mode : forall h1 h2 m1 m2,
  agree h1 h2 ->
  agree (filter_mode m1 h1) (filter_mode m2 h2).
Proof using.
  introv D. autos* agree_filter agree_sym. (* TODO: slow *)
Qed.

(* ---------------------------------------------------------------------- *)

Lemma heap_disjoint_components : forall h,
  disjoint (h^rw) (h^ro).
Proof using. 
  intros. forwards* (E&D): filter_partition h (h^rw) (h^ro).
  { intros x (v,m) _ _ K1 K2. false. }
Qed.


Lemma heap_compat_of_disjoint : forall h1 h2,
  disjoint h1 h2 ->
  heap_compat h1 h2.
Proof using.
  introv D. lets E1: heap_disjoint_components h1.
  lets E2: heap_disjoint_components h2. split.
  { splits; rew_disjoint; try splits; 
    try solve [ assumption | applys* disjoint_filter_mode ]. }
  { applys agree_of_disjoint. applys* disjoint_filter_mode. }
Qed.

Lemma heap_eq_disjoint_map_union_rw_ro : forall h,
  h = (h^rw) \+ (h^ro) /\ disjoint (h^rw) (h^ro).
Proof using. 
  intros. lets D: heap_disjoint_components h.
  forwards* (E&D'): filter_partition h (h^rw) (h^ro).
  { intros x (v,m) _ _ K1 K2. false. }
Qed.

Lemma heap_union_eq_of_compat : forall h1 h2,
  heap_compat h1 h2 ->
  h1 \u h2 = h1 \+ h2.
Proof using. introv D. unfold heap_union. case_if*. Qed.

Lemma heap_eq_disjoint_union_rw_ro : forall h,
  h = (h^rw) \u (h^ro) /\ disjoint (h^rw) (h^ro).
Proof using. 
  intros. lets (E&D): heap_eq_disjoint_map_union_rw_ro h.
  rewrite* heap_union_eq_of_compat. applys* heap_compat_of_disjoint.
Qed.

(* Corrolary *)
Lemma heap_eq_union_rw_ro : forall h,
  h = (h^rw) \u (h^ro).
Proof using. intros. applys heap_eq_disjoint_union_rw_ro. Qed.




(* ---------------------------------------------------------------------- *)
(* ** Properties of [filter_mode] *)

(* Corrolary *)
Lemma heap_compat_components : forall h,
  heap_compat (h^rw) (h^ro).
Proof using. intros. applys heap_compat_of_disjoint. applys heap_disjoint_components. Qed.

Lemma filter_mode_heap_empty : forall m,
  (heap_empty^m) = empty.
Proof using.
  intros. unfold filter_mode, heap_empty. rewrite* filter_empty.
Qed.

Hint Rewrite filter_mode_heap_empty : rew_heap.


Lemma filter_modes_eq : forall h m,
  (h^m)^m = h^m.
Proof using.
  intros. unfold filter_mode. applys* filter_idempotent.
Qed.

Lemma filter_modes_neq : forall h m1 m2,
  m1 <> m2 ->
  (h^m1)^m2 = Fmap.empty.
Proof using.
  intros. unfold filter_mode. applys filter_incompatible.
  { intros x y D K M1 M2. destruct y as (v&m'). false. }
Qed.

(* Corollary for autorewrite *)
Lemma filter_modes_rw_ro : forall h,
  (h^rw)^ro = Fmap.empty.
Proof using. intros. applys* filter_modes_neq. auto_false. Qed.

(* Corollary for autorewrite *)
Lemma filter_modes_ro_rw : forall h,
  (h^ro)^rw = Fmap.empty.
Proof using. intros. applys* filter_modes_neq. auto_false. Qed.

Hint Rewrite filter_modes_eq filter_modes_rw_ro filter_modes_ro_rw : rew_heap.

Lemma filter_modes_swap : forall h m1 m2,
  (h^m1)^m2 = (h^m2)^m1.
Proof using.
  intros. unfold filter_mode. applys* filter_swap. 
Qed.

(* for automation *)
Lemma disjoint_filter_modes_swap : forall h1 h2 m11 m12 m21 m22,
  disjoint (h1^m11) (h2^m21) ->
  disjoint ((h1^m12)^m11) ((h2^m22)^m21).
Proof using.
  introv D. rewrite (filter_modes_swap h1), (filter_modes_swap h2).
  applys* disjoint_filter_mode.
Qed. 


(* ---------------------------------------------------------------------- *)
(* ** Equalities on heaps *)

Lemma heap_eq : forall h1 h2,
  h1^rw = h2^rw ->
  h1^ro = h2^ro ->
  h1 = h2.
Proof using. 
  introv M1 M2. forwards E1: heap_eq_union_rw_ro h1.
  forwards E2: heap_eq_union_rw_ro h2. congruence.
Qed.

(* TODO: check what's actually needed *)
Lemma heap_eq_forward : forall h1 h2,
  h1 = h2 ->
  h1^rw = h2^rw /\ h1^ro = h2^ro.
Proof using. intros. subst*. Qed.



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
Proof using. introv (M1&M2). split~. Qed.

Hint Resolve heap_compat_sym.

Lemma heap_compat_empty_l : forall h,
  heap_compat heap_empty h.
Proof using.
  intros. (* lets: heap_disjoint_components h. *)
  unfold heap_empty. split; simpl.
  { rew_heap. rew_fmap. splits*. applys heap_disjoint_components. }
  { rew_heap. apply Fmap.agree_empty_l. (* TODO: hints *) }
Qed.

Lemma heap_compat_empty_r : forall h,
  heap_compat h heap_empty.
Proof using.
  hint heap_compat_sym, heap_compat_empty_l. auto.
Qed. (* Not needed? *)

Lemma heap_compat_refl_if_ro : forall h,
  h^rw = Fmap.empty ->
  heap_compat h h.
Proof using.
  introv M. split. 
  { rewrite M. auto. }
  { apply Fmap.agree_refl. } (* TODO: hint *)
Qed.

(* ---------------------------------------------------------------------- *)
(* ** More properties of [heap_compat] and [filter_mode] *)

(* more generally, compat preserved by subset *)
Lemma heap_compat_filter_mode_r : forall m h1 h2,
  heap_compat h1 h2 ->
  heap_compat h1 (filter_mode m h2).
Proof using.
  introv (D&G). split.
  { do 2 rewrites (>> filter_modes_swap m). rew_disjoint.
    hint disjoint_filter. splits*. } (* TODO: slow *)
  { rewrite filter_modes_swap. applys* agree_filter. } 
Qed.

Lemma heap_compat_filter_mode : forall h1 h2 m1 m2,
  heap_compat h1 h2 ->
  heap_compat (h1^m1) (h2^m2).
Proof using.
  introv D. autos* heap_compat_filter_mode_r heap_compat_sym.
Qed.

Lemma filter_mode_fmap_union : forall m h1 h2,
  (h1 \+ h2)^m = (h1^m) \+ (h2^m).
Proof using.
  intros. unfold filter_mode. rewrite* filter_union.
Qed.

Lemma filter_mode_union : forall m h1 h2,
  heap_compat h1 h2 ->
  (h1 \u h2)^m = (h1^m) \u (h2^m).
Proof using.
  introv D. do 2 rewrite* heap_union_eq_of_compat.
  { applys* filter_mode_fmap_union. }
  { applys* heap_compat_filter_mode. } 
Qed.

Hint Rewrite filter_mode_union : rew_heap.

Lemma heap_compat_union_l : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h1 h3 ->
  heap_compat h2 h3 ->
  heap_compat (h1 \u h2) h3.
Proof using. 
  introv D (D2&G2) (D3&G3).
  lets (E1&R1): heap_eq_disjoint_map_union_rw_ro h1.
  lets (E2&R2): heap_eq_disjoint_map_union_rw_ro h2.
  lets (E3&R3): heap_eq_disjoint_map_union_rw_ro h3.
  split. 
  { rewrite heap_union_eq_of_compat; trivial. (* TODO: slow *)
    do 2 rewrite filter_mode_fmap_union. splits*. }
  { rewrite* heap_union_eq_of_compat.
    rewrite filter_mode_fmap_union.
    applys~ Fmap.agree_union_l. }
Qed.

Lemma heap_compat_union_r : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h1 h3 ->
  heap_compat h2 h3 ->
  heap_compat h1 (h2 \u h3).
Proof using. hint heap_compat_sym, heap_compat_union_l. autos*. Qed.


(* ---------------------------------------------------------------------- *)
(* ** More properties of [heap_union] *)

Lemma not_indom_of_indom_disjoint : forall A B (h1 h2:fmap A B) x,
  indom h1 x ->
  disjoint h1 h2 ->
  ~ indom h2 x.
Proof using.
  introv M1 D M2. rewrite* disjoint_eq_not_indom_both in D.
Qed.

Lemma read_union_cases : forall A B {IB:Inhab B} (h1 h2:fmap A B) x,
  read (union h1 h2) x = If indom h1 x then read h1 x else read h2 x.
Proof using.
  Transparent Fmap.map_union.
  intros. unfold read, union, Fmap.map_union, indom, map_indom. simpl.
  case_eq (fmap_data h1 x); intros; repeat case_if; auto_false. 
Qed.

Lemma heap_union_comm : forall h1 h2,
  heap_compat h1 h2 ->
  h1 \u h2 = h2 \u h1.
Proof using.
  introv D. do 2 (rewrite* heap_union_eq_of_compat).
  applys extensionality.
  { intros x. extens. do 2 rewrite* indom_union_eq. }
  { intros x Dx.
    lets (E1&R1): heap_eq_disjoint_map_union_rw_ro h1.
    lets (E2&R2): heap_eq_disjoint_map_union_rw_ro h2.
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

(* needed? *)
Hint Resolve heap_union_comm.

Lemma heap_union_assoc : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h2 h3 ->
  heap_compat h1 h3 ->
  (h1 \u h2) \u h3 = h1 \u (h2 \u h3).
Proof using.
  hint heap_compat_union_l.
  introv D1 D2 D3. repeat rewrite* heap_union_eq_of_compat.
  rewrite* Fmap.union_assoc.
Qed.

Lemma heap_union_empty_l : forall h,
  heap_empty \u h = h.
Proof using.
  intros. rewrite* heap_union_eq_of_compat.
  { rewrite* Fmap.union_empty_l. }
  { applys heap_compat_empty_l. }
Qed.

(* needed? *)
Lemma heap_union_empty_r : forall h,
  h \u heap_empty = h.
Proof using.
  intros. auto. rewrite heap_union_comm. 
  { apply* heap_union_empty_l. }
  { applys heap_compat_empty_r. } 
Qed.

Lemma heap_union_state : forall h1 h2,
  heap_compat h1 h2 ->
  heap_state (h1 \u h2) = heap_state h1 \+ heap_state h2.
Proof using.
  introv D. rewrite* heap_union_eq_of_compat.   
  unfold heap_state. rewrite* map_union.
Qed.

(* useful? heap_state_fmap_union *)


Hint Rewrite heap_union_state : rew_fmap.

Lemma heap_state_single : forall p v m,
  heap_state (single p (v, m)) = single p v.
Proof using.
  intros. unfold heap_state. rewrite* map_single.
Qed.

Hint Rewrite heap_state_single heap_union_state : rew_heap.

Hint Rewrite heap_union_empty_l heap_union_empty_r : rew_heap.






(* ---------------------------------------------------------------------- *)
(* ** Properties  *)

Lemma heap_state_components : forall h,
  heap_state h = heap_state (h^rw) \+ heap_state (h^ro).
Proof using. 
  intros. rewrite (heap_eq_union_rw_ro h) at 1.
  rewrite* heap_union_state. applys* heap_compat_components.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [to_ro] *)

(** [to_ro h] defines the read-only heap associated with [h],
    i.e. covering the same memory cells, but with all tagged
    as read-only. *)

Definition to_ro (h:heap) : heap :=
  Fmap.map_ (fun l '(v,m) => (v,mode_ro)) h.


Lemma indom_to_ro : forall h,
  indom (to_ro h) = indom h.
Proof using.
  intros. extens. intros x. unfold to_ro. rewrite* indom_map.
Qed.

Lemma to_ro_rw : forall h,
  (to_ro h)^rw = Fmap.empty.
Proof using. 
  intros. unfold to_ro, filter_mode.
  match goal with |- context [map_ ?f _] => set (F:=f) end.
  applys filter_none.
  intros x K N. rewrite indom_map in K; [|typeclass].
  erewrite read_map in N; auto. unfold F in N.
  destruct (read h x) as (v,m). false.
Qed. (* TODO: simplify *)

Lemma to_ro_ro : forall h,
  (to_ro h)^ro = (to_ro h).
Proof using. 
  intros. unfold to_ro, filter_mode.
  match goal with |- context [map_ ?f _] => set (F:=f) end.
  applys filter_all.
  intros x K. rewrite indom_map in K; [|typeclass].
  erewrite read_map; auto. unfold F.
  destruct (read h x) as (v,m). auto.
Qed. (* TODO: simplify *)

Lemma to_ro_on_ro : forall h,
  to_ro (h^ro) = h^ro.
Proof using. 
  intros. unfold to_ro. applys map_id. intros x (v,m) D Ey.
  unfold filter_mode in *.  
  match type of D with context [filter ?f _] => set (F:=f) in * end.
  lets (Dd&Px&E): indom_filter_inv D. 
  unfold F in Px. destruct (read h x) as (v',m'). subst. congruence.
Qed. (* TODO: simplify *)


Lemma to_ro_idempotent : forall h,
  to_ro (to_ro h) = to_ro h.
Proof using. 
  intros. unfold to_ro. applys map_id. intros x (v,m) D Ey.
  unfold filter_mode in *.  
  match type of D with context [map_ ?f _] => set (F:=f) in * end.
  rewrite* indom_map in D. erewrite read_map in Ey; auto.
  unfolds F. destruct (read h x) as (v', m'). congruence.
Qed. (* TODO: simplify *)


Lemma to_ro_state : forall h,
  heap_state (to_ro h) = heap_state h.
Proof using.
  intros h. unfold heap_state, to_ro. applys extensionality.
  { intros x. repeat (rewrite indom_map;[|typeclass]). auto. }
  { intros x K. lets K': K. rewrite indom_map in K';[|typeclass].
    erewrite read_map; auto. rewrite indom_map in K';[|typeclass].
    do 2 (erewrite read_map; auto). destruct (read h x) as (v&m). auto. }
Qed. (* TODO: simplify *)

Hint Rewrite to_ro_rw to_ro_ro to_ro_state : rew_heap.

Lemma to_ro_empty : 
  to_ro heap_empty = heap_empty.
Proof using. 
  intros. unfold to_ro. rewrite* map_empty.
Qed.

Lemma to_ro_fmap_union : forall h1 h2,
  to_ro (h1 \+ h2) = (to_ro h1) \+ (to_ro h2).
Proof using. 
  intros. unfold to_ro. rewrite* map_union.
Qed.

Lemma to_ro_decompose : forall h,
  to_ro h = (to_ro h^rw) \+ h^ro.
Proof using. 
  intros. lets (E&D): heap_eq_disjoint_map_union_rw_ro h.
  rewrite E at 1. rewrite to_ro_fmap_union. rewrite* to_ro_on_ro.
Qed.

Lemma disjoint_to_ro : forall h1 h2,
  disjoint h1 h2 ->
  disjoint h1 (to_ro h2).
Proof using.
  introv M. rewrite disjoint_eq_not_indom_both in *.
  intros x R1 R2. rewrite indom_to_ro in R2. applys* M.
Qed.

Lemma disjoint_components : forall h1 h2,
  disjoint h1 (h2^rw) ->
  disjoint h1 (h2^ro) ->
  disjoint h1 h2.
Proof using.
  introv M1 M2. forwards (E&D): heap_eq_disjoint_union_rw_ro h2.
  lets D': heap_compat_of_disjoint D. 
  rewrite E. rewrite* heap_union_eq_of_compat.
Qed.

Lemma heap_compat_to_ro_r : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat h1 (to_ro h2).
Proof using.
  introv (M1&M2). split.
  { rew_heap. splits; [auto|auto|].
    { rew_disjoint. split; [auto|].
      { applys disjoint_to_ro. applys* disjoint_components. } } }
  { rew_heap. rewrite to_ro_decompose. applys agree_union_r; [|auto].
    { applys agree_of_disjoint. applys* disjoint_to_ro. } }
Qed.

(** corollary *)
Lemma heap_compat_ro_ro : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat (to_ro h1) (to_ro h2).
Proof using.
  introv M. autos* heap_compat_sym heap_compat_to_ro_r.
Qed.

(* not needed? *)
Lemma to_ro_union : forall h1 h2,
  heap_compat h1 h2 ->
  to_ro (h1 \u h2) = (to_ro h1) \u (to_ro h2).
Proof using. 
  introv D. lets: heap_compat_ro_ro D.
  do 2 rewrite* heap_union_eq_of_compat.
  rewrite* to_ro_fmap_union.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [heap_empty] *)

Lemma heap_empty_state : heap_state heap_empty = Fmap.empty.
Proof using.
  unfold heap_empty. unfold heap_state. rewrite map_empty; [|typeclass]. 
  auto.
Qed.

Hint Rewrite heap_empty_state : rew_heap.



(* ---------------------------------------------------------------------- *)
(* ** More properties of [heap_compat] *)

Lemma heap_compat_union_l_inv_l : forall h1 h2 h3,
  heap_compat (h1 \u h2) h3 ->
  heap_compat h1 h2 ->
  heap_compat h2 h3.
Admitted. (*
  introv M2 M1. lets (C1&D1): M1. lets (C2&D2): M2.
  rew_heap~ in C2.
  rew_heap~ in D2.
  forwards~ (N1&N2): Fmap.agree_union_l_inv C2.
Qed.*)

Lemma heap_compat_union_l_inv_r : forall h1 h2 h3,
  heap_compat (h1 \u h2) h3 ->
  heap_compat h1 h2 ->
  heap_compat h1 h3.
Admitted. (*
  introv M1 M2. rewrite heap_union_comm in M1.
  applys* heap_compat_union_l_inv_l.
Qed.*)

Lemma heap_compat_union_l_inv : forall h1 h2 h3,
  heap_compat (h1 \u h2) h3 ->
  heap_compat h1 h2 ->
  heap_compat h1 h3 /\ heap_compat h2 h3.
Admitted. (*
  hint heap_compat_union_l_inv_l, heap_compat_union_l_inv_r. autos*.
Qed.*)

Lemma heap_compat_union_r_inv : forall h1 h2 h3,
  heap_compat h1 (h2 \u h3) ->
  heap_compat h2 h3 ->
  heap_compat h1 h2 /\ heap_compat h1 h3.
Admitted. (*
  introv M1 M2. rewrite heap_union_comm in M1.
  lets M1': heap_compat_sym M1.
  forwards~ (N1&N2): heap_compat_union_l_inv M1'.
Qed.*)


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

Hint Resolve hempty_intro
  heap_compat_empty_l heap_compat_empty_r
  heap_union_empty_l heap_union_empty_r.

Lemma hstar_hempty_l : forall H,
  hempty \* H = H.
Proof using.
  intros. applys pred_ext_1. intros h.
  iff (h1&h2&M1&M2&D&U) M.
  { forwards E: hempty_inv M1. subst.
    rewrite~ heap_union_empty_l. }
  { exists~ heap_empty h. }
Qed.

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof using.
  intros. unfold hprop, hstar. extens. intros h.
  hint Fmap.agree_sym.
  iff (h1&h2&M1&M2&D&U).
  { exists h2 h1. subst. splits~. }
  { exists h2 h1. subst. splits~. }
Qed.

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using.
  intros. unfold hprop, hstar. extens. intros h. split.
  { intros (h'&h3&(h1&h2&M2&P1&P2&E1)&M3&M1&E2). subst h'.
    lets~ (M1a&M1b): heap_compat_union_l_inv M1.
    exists h1 (h2 \u h3). splits.
    { auto. }
    { exists h2 h3. splits*. }
    { applys* heap_compat_union_r. }
    { subst. applys~ heap_union_assoc. } }
  { intros (h1&h'&P1&(h2&h3&M2&P2&P3&E1)&M1&E2). subst h'.
    lets~ (M1a&M1b): heap_compat_union_r_inv M1.
    exists (h1 \u h2) h3. splits.
    { exists h1 h2. splits*. }
    { auto. }
    { applys* heap_compat_union_l. }
    { subst. symmetry. applys~ heap_union_assoc. } }
Qed.

Lemma hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof using.
  intros. applys pred_ext_1. intros h. iff M.
  { destruct M as (h1&h2&(x&M1)&M2&D&U). exists~ x h1 h2. }
  { destruct M as (x&(h1&h2&M1&M2&D&U)). exists h1 h2. splits~. exists~ x. }
Qed.

Lemma hstar_hforall : forall H A (J:A->hprop),
  (hforall J) \* H ==> hforall (J \*+ H).
Proof using.
  intros. intros h M. destruct M as (h1&h2&M1&M2&D&U). intros x. exists~ h1 h2.
Qed.

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof using. introv W (h1&h2&?). exists* h1 h2. Qed.

Lemma haffine_hempty :
  haffine \[].
Proof using.
  introv K. lets E: hempty_inv K. subst. applys heap_affine_empty.
Qed.

Lemma haffine_hstar : forall H1 H2,
  haffine H1 ->
  haffine H2 ->
  haffine (H1 \* H2).
Proof using.
  introv M1 M2 (h1&h2&K1&K2&D&U).
  subst. applys* heap_affine_union.
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
  introv M. lets (HP&N): hpure_inv_hempty M. lets E: hempty_inv N. auto.
Qed.

Lemma hpure_intro : forall P,
  P ->
  \[P] heap_empty.
Proof using. introv M. applys~ hpure_intro_hempty. applys hempty_intro. Qed.

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  heap_compat h1 h2 ->
  (H1 \* H2) (h1 \u h2).
Proof using. intros. exists~ h1 h2. Qed.
(* LATER: use in proofs *)

(*
Lemma hgc_intro : forall h,
  \GC h.
Proof using. intros. applys hgc_of_heap_affine. hnfs*. Qed.
*)

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

Notation "l '~~>' v" := (hsingle l v)
  (at level 32, no associativity) : heap_scope.

Lemma filter_mode_single : forall l v m1 m2,
  filter_mode m1 (Fmap.single l (v, m2)) = 
  If m1 = m2 then Fmap.single l (v, m2) else Fmap.empty.
Proof using.
  intros. unfold filter_mode. rewrite filter_single; try typeclass.
Qed.

(* Corollary for autorewrite *)
Lemma single_rw : forall l v,
  ((Fmap.single l (v, mode_rw))^rw) = Fmap.single l (v, mode_rw).
Proof using. intros. rewrite filter_mode_single. case_if*. Qed.

(* Corollary for autorewrite *)
Lemma single_ro : forall l v,
  ((Fmap.single l (v, mode_rw))^ro) = Fmap.empty.
Proof using. intros. rewrite filter_mode_single. case_if*. Qed.

Hint Rewrite single_rw single_ro : rew_heap.

Lemma hstar_hsingle_same_loc : forall (l:loc) (v1 v2:val),
  (l ~~~> v1) \* (l ~~~> v2) ==> \[False].
Proof using.
  intros. intros h (h1&h2&(E1&N1)&(E2&N2)&(D&A)&E). subst. false.
  rew_heap in D. applys* Fmap.disjoint_single_single_same_inv D.
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
(* ** Definitions of [duplicatable] *)

Definition duplicatable (H:hprop) : Prop :=
  H ==> H \* H.


(* ---------------------------------------------------------------------- *)
(* ** Definitions and properties of [normal] *)

Class Normal (H:hprop) : Prop :=
  normal_emp : forall h, H h -> h^ro = Fmap.empty.

Hint Mode Normal ! : typeclass_instances.

Lemma Normal_ro : forall H h,
  Normal H ->
  H h ->
  h^ro = Fmap.empty.
Proof using. introv N K. applys* N. Qed.

Lemma Normal_rw : forall H h,
  Normal H ->
  H h ->
  h^rw = h.
Proof using.
  introv N K. specializes N (rm K).
  forwards E: heap_eq_union_rw_ro h.
  rewrite N in E. rew_heap* in E.
Qed.

(* TODO: definition ? *)
Notation Normal_post Q := (forall x, Normal (Q x)).


Instance Normal_hempty :
  Normal \[].
Proof using.
  Transparent hempty hpure.
  introv M. unfolds hempty, hpure. subst. rew_heap*.
Qed.

Instance Normal_hpure : forall P,
  Normal \[P].
Proof using.
  Transparent hpure.
  introv (p&M). unfolds hempty. subst. rew_heap*.
Qed.

Lemma Normal_hgc :
  Normal \GC.
Proof using. 
  introv (H&M). rewrite hstar_hpure_l in M. destruct M as (F&R).
  applys* heap_affine_Normal. rewrite haffine_eq in F. applys* F.
Qed.

Lemma Normal_hempty' : (* simpler proof *)
  Normal \[].
Proof using.
  intros. rewrite hempty_eq_hpure_true. applys~ Normal_hpure.
Qed.

Instance Normal_hsingle : forall l v,
  Normal (hsingle l v).
Proof using.
  Transparent hsingle.
  introv (E&N). subst h. rew_heap*.
Qed.

Instance Normal_hstar : forall H1 H2,
  Normal H1 ->
  Normal H2 ->
  Normal (H1 \* H2).
Proof using.
  introv N1 N2 (h1&h2&P1&P2&M1&EQ).
  lets (_&E): heap_eq_forward EQ. simpls. rewrite E.
  rew_heap*. rewrites (>> N1 P1). rewrites (>> N2 P2). rew_heap*.
Qed.

Instance Normal_hexists : forall A (J:A->hprop),
  Normal_post J ->
  Normal (hexists J).
Proof using. introv M (x&N). rewrites~ (>> M N). Qed.

Instance Normal_hforall_inhab : forall `{Inhab A} (J:A->hprop),
  Normal_post J ->
  Normal (hforall J).
Proof using.
  introv IA M N. lets M': M (arbitrary (A:=A)). lets N': N (arbitrary (A:=A)).
  applys M' N'.
Qed.

Instance Normal_hforall : forall A (x:A) (J:A->hprop),
  Normal (J x) ->
  Normal (hforall J).
Proof using. introv M N. applys M N. Qed.

Instance Normal_hor : forall H1 H2,
  Normal H1 ->
  Normal H2 ->
  Normal (hor H1 H2).
Proof using. introv M1 M2. applys Normal_hexists. intros b. case_if*. Qed.

Instance Normal_hand_l : forall H1 H2,
  Normal H1 ->
  Normal (hand H1 H2).
Proof using. introv M1. applys* Normal_hforall true. Qed.

Instance Normal_hand_r : forall H1 H2,
  Normal H2 ->
  Normal (hand H1 H2).
Proof using. introv M1. applys* Normal_hforall false. Qed.

Lemma Normal_himpl : forall H1 H2,
  Normal H2 ->
  (H1 ==> H2) ->
  Normal H1.
Proof using. introv HS HI M. lets: HI M. applys* HS. Qed.

(* Note: Normal_hwand is not true *)

Lemma Normal_hpure_star_hpure : forall (P:Prop) H,
  (P -> Normal H) ->
  Normal (\[P] \* H).
Proof using.
  introv N (h1&h2&P1&P2&M1&EQ).
  lets (_&E): heap_eq_forward EQ. simpls. rewrite E.
  rew_heap*.
  lets (MP&ME): hpure_inv P1. rewrites (rm ME).
  rewrites~ (>> N P2). rew_heap*.
Qed.

Lemma Normal_of_haffine : forall H,
  haffine H ->
  Normal H.
Proof using. 
  introv M. intros h K. rewrite haffine_eq in M.
  specializes M K. applys* heap_affine_Normal.
Qed.

Hint Resolve Normal_hempty Normal_hstar Normal_hgc : Normal.



(* ---------------------------------------------------------------------- *)
(* *)

(* Dual of Normal *)

Class ReadOnly (H:hprop) : Prop :=
  read_only : forall h, H h -> h^rw = Fmap.empty.

Hint Mode Normal ! : typeclass_instances.

Lemma ReadOnly_rw : forall H h,
  ReadOnly H ->
  H h ->
  h^rw = Fmap.empty.
Proof using. introv N K. applys* N. Qed.

Instance ReadOnly_hempty :
  ReadOnly hempty.
Proof using.
  introv M. unfolds hempty, hpure. subst. rew_heap*.
Qed.

Instance ReadOnly_hstar : forall H1 H2,
  ReadOnly H1 ->
  ReadOnly H2 ->
  ReadOnly (H1 \* H2).
Proof using.
  introv N1 N2 (h1&h2&P1&P2&M1&EQ). subst. rew_heap*.
  rewrite* N1. rewrite* N2. rew_heap*.
Qed.

Hint Resolve ReadOnly_hstar ReadOnly_hempty : ReadOnly.



(* ---------------------------------------------------------------------- *)
(* ** Definitions and properties of [RO] *)

Definition RO (H:hprop) : hprop :=
  fun h => exists h', H h' /\ h = to_ro h'.

  (* equivalent to:
Definition RO' (H:hprop) : hprop :=
  \exists h', \[H h'] \* (= to_ro h').
 *)

Ltac heap_eq :=
  solve [ rew_heap; subst; auto ].

Lemma union_same : forall h,
  union h h = h.
Proof using.
  intros. applys extensionality.  
  { intros x. extens. rewrite* indom_union_eq. }
  { intros x Dx. rewrite* indom_union_eq in Dx. rewrite* read_union_l. } 
Qed.

Lemma heap_compat_refl_to_ro : forall h,
  heap_compat (to_ro h) (to_ro h).
Proof using.
  intros. applys heap_compat_refl_if_ro. rew_heap*.
Qed.

(* not needed *)
Lemma to_ro_duplicatable : forall h,
  duplicatable (= to_ro h).
Proof using.
  intros h. unfolds. intros h' E. subst.
  lets D: heap_compat_refl_to_ro h. do 2 esplit. splits*. 
  rewrite* heap_union_eq_of_compat. rewrite* union_same.
Qed.

Lemma RO_duplicatable : forall H,
  duplicatable (RO H).
Proof using.
  intros H h M. lets (h'&M1&M2): M. subst.
  lets D: heap_compat_refl_to_ro h'. do 2 esplit. splits*.
  rewrite* heap_union_eq_of_compat. rewrite* union_same.
Qed.

Lemma RO_covariant : forall H1 H2,
  H1 ==> H2 ->
  (RO H1) ==> (RO H2).
Proof using. 
  introv M. intros h (h'&M1&M2). exists~ h'.
Qed.

Lemma RO_RO : forall H,
  RO (RO H) = RO H.
Proof using. 
  intros. apply pred_ext_1. intros h. unfolds RO.
  iff (h'&(h''&M1'&M2')&M2) (h'&M1&M2).
  { exists h''. splits~. subst. rewrite* to_ro_idempotent. }
  { exists h. splits~.
    { exists h'. split~. }
    { subst. rewrite* to_ro_idempotent. } }
Qed.

Hint Rewrite to_ro_empty : rew_heap.

Lemma RO_empty :
  RO \[] = \[].
Proof using. 
  intros. apply pred_ext_1. intros h.
  unfold hempty. iff (h'&M1&M2) M1.
  { subst. rew_heap*. }
  { subst. exists heap_empty. rew_heap*. }
Qed.

Lemma RO_pure : forall P,
  RO \[P] = \[P].
Proof using.
  hint hpure_intro. intros. apply pred_ext_1. intros h.
  iff (h'&(M1p&M2)&M3) (MP&M1); unfolds hempty.
  { subst. rew_heap*. }
  { exists h. subst. rew_heap*. }
Qed.

Lemma RO_empty' : (* simpler proof *)
  RO \[] = \[].
Proof using.
  intros. rewrite hempty_eq_hpure_true. rewrite~ RO_pure.
Qed.

Lemma RO_hexists : forall A (J:A->hprop),
    RO (hexists J)
  = \exists x, RO (J x).
Proof using.
  intros. apply pred_ext_1. intros h.
  iff (h'&(x&M1)&M2) (x&(h'&M1&M2)).
  { exists x. exists* h'. }
  { exists h'. splits~. { exists~ x. } }
Qed. 

(* NOT NEEDED?
Lemma RO_if : forall (b:bool) H1 H2,
    RO (if b then H1 else H2)
  = (if b then RO H1 else RO H2).
Proof using. intros. destruct* b. Qed.
*)

Lemma RO_or : forall H1 H2,
     RO (hor H1 H2)
  ==> hor (RO H1) (RO H2).
Proof using. 
  intros. unfolds hor. rewrite RO_hexists.
  applys himpl_hexists. intros b. destruct* b.
Qed. 

Lemma RO_star : forall H1 H2,
  RO (H1 \* H2) ==> (RO H1 \* RO H2).
Proof using.
  intros. intros h (h'&(h1&h2&N1&P1&P2&N2)&M2).
  lets C: heap_compat_ro_ro P2.
  exists (to_ro h1) (to_ro h2). splits.
  { exists~ h1. }
  { exists~ h2. }
  { auto. }
  { subst. rewrite* to_ro_union. }
Qed.

Lemma to_ro_pred : forall (H:hprop) h,
  H h ->
  RO H (to_ro h).
Proof using.
  introv N. exists h. split~.
Qed.

Arguments RO_star : clear implicits.

(* needed?
Lemma RO_ro : forall h,
  RO (= (h^ro)) (h^ro).
Proof using.
  intros. exists h. split~.
Qed.
*)

Instance ReadOnly_RO : forall H,
  ReadOnly (RO H).
Proof using.
  introv (h'&K&E). subst. rew_heap*.
Qed.


(* ********************************************************************** *)
(* * Elim lemmas *)

Lemma Normal_rw_elim : forall H h, 
  Normal H -> 
  H h ->
  H (h^rw).
Proof using. introv N K. rewrites* (>> Normal_rw K). Qed.

Lemma Normal_ReadOnly_rw_elim : forall HF HR h, 
  Normal HF -> 
  ReadOnly HR ->
  (HF \* HR) h ->
  HF (h^rw).
Proof using.
  introv NF NR (h1&h2&K1&K2&D&->). rew_heap*.
  rewrites* (>> ReadOnly_rw K2).
  rewrites* (>> Normal_rw K1).
  rew_heap*.
Qed.


(* ********************************************************************** *)
(* Framed *)

Definition Framed HI HO :=
  exists HR, Normal HO /\ ReadOnly HR /\ HI = HO \* HR.

Lemma Framed_rw_elim : forall HI HO h, 
  Framed HI HO -> 
  HI h ->
  HO (h^rw).
Proof using.
  introv (R&NF&NR&->) M. applys* Normal_ReadOnly_rw_elim.
Qed.

Lemma Framed_hempty :
  Framed \[] \[].
Proof using.
  exists \[]. splits*. 
  { auto with Normal. }
  { auto with ReadOnly. }
  { subst. xsimpl. } 
Qed.

Lemma Framed_Normal : forall HI HO H,
  Framed HI HO ->
  Normal H ->
  Framed (HI \* H) (HO \* H).
Proof using.
  introv (HR&NF&NR&E) N.
  exists HR. splits*. 
  { auto with Normal. }
  { subst. xsimpl. } 
Qed.

Lemma Framed_ReadOnly : forall HI HO H,
  Framed HI HO ->
  ReadOnly H ->
  Framed (HI \* H) HO.
Proof using.
  introv (HR&NF&NR&E) N.
  exists (HR \* H). splits*. 
  { auto with ReadOnly. } 
  { subst. xsimpl. } 
Qed.



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

(* Not needed *)
Lemma hoare_named_heap : forall t H Q,
  (forall h, H h -> hoare t (= h) Q) ->
  hoare t H Q.
Proof using. introv M. intros h Hh. applys* M. Qed.

Lemma hoare_frame_read_only : forall t H1 Q1 H2,
  hoare t (H1 \* RO H2) Q1 ->
  Normal H2 ->
  hoare t (H1 \* H2) (Q1 \*+ H2).
Proof using.
  introv M N. intros h (h1&h2&P1&P2&R1&R2).
  forwards (h'&v&R&L&S): M (h1 \u to_ro h2).
  { exists h1 (to_ro h2). splits~. 
    { applys* to_ro_pred. }
    { applys* heap_compat_to_ro_r. } }
  rewrite (heap_eq_union_rw_ro h') in R.
  rewrite heap_union_state in R.
  rewrite heap_union_state in R.
  rewrite S in R.
  rew_heap in R. 
  exists (h'^rw \u h1^ro \u h2) v. splits.
  { subst h. rew_heap in *. applys_eq R. skip. skip. skip. skip. }
  { rew_heap. do 2 esplit. (* TODO: hstar intro *) splits*.
    (* normal -> rw is empty *)
    (* ro rw -> empty *)  skip . rew_heap. rewrites~ (@Normal_rw H2 h2). (* h2^ro is empty *) skip. skip. }
  { skip. }
  { skip. }
  { skip. }
  { skip. }
  { applys* heap_compat_to_ro_r. }
Qed. (* TODO *)

Lemma hoare_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, hoare t (J x) Q) ->
  hoare t (hexists J) Q.
Proof. introv M. intros h (x&Hh). applys M Hh. Qed.

Lemma hoare_hpure : forall t (P:Prop) H Q,
  (P -> hoare t H Q) ->
  hoare t (\[P] \* H) Q.
Proof.
  introv M. intros h (h1&h2&(HP&M1)&M2&D&U). hnf in M1. subst. rew_heap*.
  rew_fmap*.
Qed.


(* ########################################################### *)
(** ** Reasoning rules for terms, for Hoare triples. *)

Lemma hoare_val : forall HI HO v,
  Framed HI HO ->
  hoare (trm_val v) HI (fun r => \[r = v] \* HO).
Proof.
  introv HF. intros h K. exists h v. splits~.
  { applys eval_val. }
  { rewrite hstar_hpure_l. split~. applys* Framed_rw_elim. }
Qed.

Lemma hoare_fix : forall HI HO f x t1,
  Framed HI HO ->
  hoare (trm_fix f x t1) HI (fun r => \[r = (val_fix f x t1)] \* HO).
Proof.
  introv HF. intros h K. exists h (val_fix f x t1). splits~.
  { applys eval_fix. }
  { rewrite hstar_hpure_l. split~. applys* Framed_rw_elim. }
Qed.

Lemma hoare_app_fix : forall v1 v2 (f:var) x t1 H Q,
  v1 = val_fix f x t1 ->
  f <> x ->
  hoare (subst x v2 (subst f v1 t1)) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof.
  introv E D M. intros s K0. forwards (s'&v&R1&K1&E1): (rm M) K0.
  exists s' v. splits~. { applys* eval_app E R1. auto_false. }
Qed.

Hint Extern 1 (heap_compat _ _) => skip.
Hint Extern 1 (disjoint _ _) => skip.

Lemma hoare_let : forall x t1 t2 H1 H2 Q1 Q HI HO,
  Framed HI HO ->
  hoare t1 (H1 \* RO H2 \* HI) (Q1 \*+ HO) ->
  (forall v H3, ReadOnly H3 -> hoare (subst x v t2) (Q1 v \* HO \* H2 \* H3) (Q \*+ HO)) ->
  hoare (trm_let x t1 t2) (H1 \* H2 \* HI) (Q \*+ HO).
Proof.
  introv HF M1 M2. intros h K.
  destruct K as (h1&hr&P1&P2&D1&U1).
  destruct P2 as (h2&hI&PI&PO&D2&U2).
  forwards (h1'&v1&R1&K1&E1): (rm M1) (h1 \u to_ro h2 \u hI).
  { do 2 esplit. splits*. do 2 esplit. splits*. { applys* to_ro_pred. } }
  (* destruct K1 as (ha&hb&Pa&Pb&D3&U3).*)
  forwards (h2'&v2&R2&K2&E2): (rm M2) v1 (= hI^ro \u h1^ro) (h1'^rw \u h2 \u (h1^ro \u hI^ro) ).
  { intros ? ->. rew_heap*. }
  { rewrite <- hstar_assoc. do 2 esplit. (* TODO: tactic *) splits*.
    do 2 esplit. splits*. { fequal. rewrite* heap_union_comm. } }
  exists h2' v2. splits*.
  { applys eval_let_trm (heap_state h1').
    { applys_eq R1. subst h hr. rew_heap*. } 
    { applys_eq R2. rewrite (heap_state_components h1').
      rewrite E1. rew_heap*. fmap_eq*. } }
    { rewrite E2. rewrite U1,U2. rew_heap*.  (* same unions *)
      rewrite* <- heap_union_assoc. rewrites* (>> heap_union_comm (h2^ro)). 
      rewrite* heap_union_assoc. }
Qed.

Lemma hoare_if : forall (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.
Proof.
  introv M1. intros h Hh. forwards* (h1'&v1&R1&K1&E1): (rm M1).
  exists h1' v1. splits*. { applys* eval_if. }
Qed.

Lemma hoare_ref : forall HI HO v,
  Framed HI HO ->
  hoare (val_ref v)
    (HI)
    (fun r => (\exists p, \[r = val_loc p] \* p ~~> v) \* HO).
Proof using.
  introv NF. intros s1 K0.
  forwards~ (p&D&N): (Fmap.single_fresh 0%nat s1 (v,mode_rw)).
  exists (heap_union (Fmap.single p (v,mode_rw)) s1) (val_loc p). splits.
  { rew_heap*. applys~ eval_ref_sep. }
  { rew_heap*. applys~ hstar_intro.
    { exists p. rewrite~ hstar_hpure_l. split~. { split~. (* applys~ hsingle_intro. *) } }
    { applys* Framed_rw_elim. } }
  { rew_heap*. }
Qed.

Lemma hoare_get_ro : forall HI HO v p,
  Framed HI HO ->
  hoare (val_get p)
    (RO (p ~~> v) \* HI)
    (fun r => \[r = v] \* HO).
Proof using.
  introv NH. intros s (s1&s2&P1&P2&D&U).
  destruct P1 as (h'&(K&N)&E).
  exists s v. splits.
  { (*lets E1: hsingle_inv P1.*)
     subst s1.
     applys eval_get_sep (heap_state h') (heap_state s2). subst s. rew_heap*. 
     subst h'. rew_heap*. }
  { rewrite~ hstar_hpure_l. split~. subst s s1. rew_heap*.
    applys* Framed_rw_elim. }
  { auto. }
Qed.

Lemma hoare_set : forall HI HO w p v,
  Framed HI HO ->
  hoare (val_set (val_loc p) v)
    ((p ~~> w) \* HI)
    (fun r => \[r = val_unit] \* (p ~~> v) \* HO).
Proof using.
  introv NH. intros s1 K0.
  destruct K0 as (h1&h2&P1&P2&D&U).
  (* lets E1: hsingle_inv P1. *)
  destruct P1 as (K&N).
  exists (heap_union (single p (v,mode_rw)) h2) val_unit. splits.
  { subst h1. applys* eval_set_sep (single p w) (single p v) (heap_state h2).
    { subst. rew_heap*. }
    { rew_heap*. } } 
  { rewrite hstar_hpure_l. split~.
    { rew_heap*. exists __ (h2^rw). splits*. (* rewrites~ applys~ hstar_intro.*)
      { splits*. } { applys* Framed_rw_elim. } } }
  { subst. rew_heap*. }
Qed.

Lemma hoare_free : forall HI HO p v,
  Framed HI HO ->
  hoare (val_free (val_loc p))
    ((p ~~> v) \* HI)
    (fun r => \[r = val_unit] \* HO).
Proof using.
  introv NH. intros s1 K0.
  destruct K0 as (h1&h2&P1&P2&D&U).
  (* lets E1: hsingle_inv P1. *)
  destruct P1 as (K&N).
  exists h2 val_unit. splits.
  { subst h1. applys* eval_free_sep.   
    { subst. rew_heap*. } }
  { rewrite hstar_hpure_l. split~. applys* Framed_rw_elim. }
  { subst. rew_heap*. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Definition of SL triples in a logic with read-only predicates *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) :=
  forall HI HO, Framed HI HO ->
  hoare t (H \* HI) (Q \*+ HO \*+ \GC).

(** Equivalent definition *)

Definition triple' (t:trm) (H:hprop) (Q:val->hprop) :=
  forall HF HR, Normal HF -> ReadOnly HR ->
    hoare t (H \* HF \* HR) (Q \*+ HF \*+ \GC).

Lemma triple_eq_triple' : triple = triple'.
Proof using.
  extens. intros t H Q. iff M.
  { intros HF HR NF NR. lets HFa: Framed_Normal Framed_hempty NF.
    lets HFb: Framed_ReadOnly (rm HFa) NR. rew_heap in *. applys M HFb. }
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
Qed. (* Note: can also be proved from [triple_hexists] *)

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

Lemma triple_frame_Normal : forall t H1 Q1 H2,
  triple t H1 Q1 ->
  Normal H2 ->
  triple t (H1 \* H2) (Q1 \*+ H2).
Proof using.
  introv M N. intros HI HO HF.
  forwards~ HF': Framed_Normal H2 HF.
  forwards~ K: M HF'. 
  applys hoare_conseq K; xsimpl.
Qed.

Lemma triple_frame_ReadOnly : forall t H1 Q1 H2,
  triple t H1 Q1 ->
  ReadOnly H2 ->
  triple t (H1 \* H2) Q1.
Proof using.
  introv M N. intros HI HO HF.
  forwards~ HF': Framed_ReadOnly H2 HF.
  forwards~ K: M HF'. 
  applys hoare_conseq K; xsimpl.
Qed.

Lemma triple_conseq_frame : forall H Q t H1 Q1 H2,
  triple t H1 Q1 ->
  H ==> (H1 \* H2) ->
  (Q1 \*+ H2) ===> Q ->
  Normal H2 ->
  triple t H Q.
Proof using.
  introv M WH WQ N. applys triple_conseq WH WQ.
  applys* triple_frame_Normal.
Qed.

Lemma triple_frame_read_only : forall t H1 Q1 H2,
  triple t (H1 \* RO H2) Q1 ->
  Normal H2 ->
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
  introv M. applys* triple_frame_ReadOnly. applys ReadOnly_RO.
Qed.

Lemma triple_haffine_pre : forall t H H' Q,
  triple t H Q ->
  haffine H' ->
  triple t (H \* H') Q.
Proof using.
  introv M F. applys~ triple_haffine_post H'.
  applys* triple_frame_Normal M.
  applys* Normal_of_haffine.
Qed.



(* ---------------------------------------------------------------------- *)
(* ** SL rules for terms *)

Lemma triple_of_hoare : forall t H Q,
  (forall HI HO, Framed HI HO ->
     exists Q', hoare t (H \* HI) Q' /\ Q' ===> Q \*+ HO \*+ \GC) ->
  triple t H Q.
Proof using.
  introv M. intros HI HO HF. forwards* (Q'&R&W): M HF. applys* hoare_conseq R.
Qed.

Lemma triple_val : forall v,
  triple (trm_val v) \[] (fun r => \[r = v]).
Proof.
  intros. intros HI HO HF. rew_heap.
  applys hoare_conseq.
  { applys* hoare_val. }
  { xsimpl. }
  { xsimpl*. }
Qed.

Lemma triple_val_framed : forall v H Q,
  H ==> Q v ->
  Normal H ->
  triple (trm_val v) H Q.
Proof using.
  introv M N. applys triple_conseq_frame N.
  { applys triple_val. }
  { xsimpl. }
  { xchanges M. intros ? ->. xsimpl*. }
Qed.

Lemma triple_fix : forall f x t1,
  triple (trm_fix f x t1) \[] (fun r => \[r = (val_fix f x t1)]).
Proof.
  intros. intros HI HO HF. rew_heap.
  applys hoare_conseq.
  { applys* hoare_fix. }
  { xsimpl. }
  { xsimpl*. }
Qed.

Lemma triple_fix_framed : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  Normal H ->
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
      { intros v H3 N3. 
        lets (_&NO&_&_): HF. (* TODO: lemma *)
        forwards* HFa: Framed_Normal (HO \* \GC) Framed_hempty.
        { auto with Normal. }
        forwards* HFb: Framed_ReadOnly H3 (rm HFa). rew_heap in HFb.
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
  H ==> (\exists H1 H2, \[Normal H1] \* \[ReadOnly H2] \* (H1 \* H2)). 
Proof using.
  intros H h K. rewrite (heap_eq_union_rw_ro h).
  exists (= h^rw) (= h^ro). do 2 rewrite hstar_hpure. splits.
  { intros ? ->. rew_heap*. }
  { intros ? ->. rew_heap*. } 
  { do 2 esplit. splits*. }
Qed.

