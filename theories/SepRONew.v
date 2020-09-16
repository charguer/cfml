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
Generalizable Variable A.


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



(* ********************************************************************** *)
(* * Core of the logic *)

Module Export SepROCore <: SepCore.


(* ---------------------------------------------------------------------- *)
(** Heaps *)

Declare Scope heap_scope.

(** Representation of heaps as pairs *)

Definition heap : Type :=
  { h : (state*state)%type | let '(f,r) := h in Fmap.disjoint f r }.

(** Components *)

Definition part_rw (h:heap) : state :=
  match h with exist (f,r) _ => f end.

Definition part_ro (h:heap) : state :=
  match h with exist (f,r) _ => r end.

Notation "h '^^rw'" := (part_rw h)
   (at level 9, format "h '^^rw'") : heap_scope.

Notation "h '^^ro'" := (part_ro h)
   (at level 9, format "h '^^ro'") : heap_scope.

Open Scope heap_scope.

(** State of heap *)

Coercion heap_state (h : heap) : state :=
  (h^^rw \+ h^^ro).

(** Empty *)

Program Definition heap_empty : heap :=
  (Fmap.empty, Fmap.empty).

Global Instance heap_inhab : Inhab heap.
Proof using. applys Inhab_of_val heap_empty. Qed.

(** Starable heaps: disjoint owned heaps, agreeible read-only heaps *)

Definition heap_compat (h1 h2 : heap) : Prop :=
    Fmap.agree (h1^^ro) (h2^^ro)
 /\ (\# (h1^^rw) (h2^^rw) (h1^^ro \+ h2^^ro)).

(** Union of heaps.
    The operation [h1 \u h2] is partial. When the arguments are
    not compatible, it returns an unspecified result.
    We implement it using a classical logic test, so as to avoid
    dependently-typed programming. *)

Program Definition heap_union (h1 h2 : heap) : heap :=
  If (heap_compat h1 h2) then (h1^^rw \+ h2^^rw, h1^^ro \+ h2^^ro) else arbitrary.
Next Obligation.
  match goal with H: heap_compat _ _ |- _ => destruct H end. fmap_disjoint.
Qed.

Declare Scope heap_union_scope.

Notation "h1 \u h2" := (heap_union h1 h2)
   (at level 37, right associativity) : heap_union_scope.

Local Open Scope heap_union_scope.

(** Affinity is customizable. Only rw permissions may be considered
    affine. RO permissions may be freely discarded by other means. *)

Parameter heap_affine : heap -> Prop. (* (h:heap) := True.*)

Parameter heap_affine_onlyrw : forall h,
  heap_affine h ->
  h^^ro = Fmap.empty.

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

(* Hint Extern 1 (_ = _ :> heap) => fmap_eq. LATER *)

Tactic Notation "fmap_disjoint_pre" :=
  subst; rew_disjoint; jauto_set.

Hint Extern 1 (\# _ _) => fmap_disjoint_pre.
Hint Extern 1 (\# _ _ _) => fmap_disjoint_pre.

Hint Resolve Fmap.agree_sym.

(* LATER: move to TLC; (this cannot be put in TLCbuffer) *)
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

(* ---------------------------------------------------------------------- *)

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

Ltac heap_eq :=
  solve [ rew_heap; subst; auto ].
(* TODO: remove *)


(* ---------------------------------------------------------------------- *)
(* ** Equalities on [heap] *)

Lemma heap_state_def : forall h,
  heap_state h = (h^^rw \+ h^^ro).
Proof using. auto. Qed.

Hint Rewrite heap_state_def : rew_disjoint.

Lemma heap_disjoint_parts : forall h,
  \# (h^^rw) (h^^ro).
Proof using. intros ((f,r)&D). simple~. Qed.

Lemma heap_make : forall f r,
  Fmap.disjoint f r -> exists (h:heap), h^^rw = f /\ h^^ro = r.
Proof using. introv M. exists~ ((exist (f,r) M : heap)). Qed.

Lemma heap_eq : forall h1 h2,
  h1^^rw = h2^^rw ->
  h1^^ro = h2^^ro ->
  h1 = h2.
Proof using.
  intros ((f1,r1)&D1) ((f2,r2)&D2) M1 M2. simpls. subst. fequals.
Qed.

Lemma heap_eq_forward : forall h1 h2,
  h1 = h2 ->
  h1^^rw = h2^^rw /\ h1^^ro = h2^^ro.
Proof using. intros ((f1&r1)&D1) ((f2&r2)&D2) M. inverts~ M. Qed.

Ltac unstate := unfold heap_state; simpl.


(* ---------------------------------------------------------------------- *)
(* ** Auxiliary function [mkrw] *)

(** [mkrw s] defines the heap [(s,state_empty)], that is, the state
    [s] viewed with full permission. *)

Program Definition mkrw s : heap :=
  (s, Fmap.empty).

Lemma part_rw_mkrw : forall s,
  (mkrw s)^^rw = s.
Proof using. auto. Qed.

Lemma part_ro_mkrw : forall s,
  (mkrw s)^^ro = Fmap.empty.
Proof using. auto. Qed.

Lemma mkrw_part_rw_of_ro_empty : forall h,
  h^^ro = empty ->
  (mkrw h^^rw) = h.
Proof using. intros ((f,r),D) E. applys heap_eq; simpls*. Qed.

Hint Rewrite part_rw_mkrw part_ro_mkrw : rew_fmap.


(* ---------------------------------------------------------------------- *)
(* ** Auxiliary function [mkro] *)

(** [mkrw s] defines the heap [(state_empty,s)], that is, the state
    [s] viewed with read-only permission. *)

Program Definition mkro s : heap :=
  (Fmap.empty, s).

Lemma part_ro_mkro : forall s,
  (mkro s)^^ro = s.
Proof using. auto. Qed.

Lemma part_rw_mkro : forall s,
  (mkro s)^^rw = Fmap.empty.
Proof using. auto. Qed.

Lemma mkro_part_rw_of_rw_empty : forall h,
  h^^rw = empty ->
  (mkro h^^ro) = h.
Proof using. intros ((f,r),D) E. applys heap_eq; simpls*. Qed.

Hint Rewrite part_rw_mkro part_ro_mkro : rew_fmap.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [part] *)

Lemma parts_heap_union_of_compat : forall h1 h2,
  heap_compat h1 h2 ->
     (h1 \u h2)^^rw = h1^^rw \+ h2^^rw
  /\ (h1 \u h2)^^ro = h1^^ro \+ h2^^ro.
Proof using.
  introv D. unfold heap_union.
  destruct (classicT (heap_compat h1 h2)); auto_false.
Qed.

(* Corollary for autorewrite *)
Lemma part_rw_heap_union_of_compat : forall h1 h2,
  heap_compat h1 h2 ->
  (h1 \u h2)^^rw = h1^^rw \+ h2^^rw.
Proof using. introv D. forwards*: parts_heap_union_of_compat D. Qed.

(* Corollary for autorewrite *)
Lemma part_ro_heap_union_of_compat : forall h1 h2,
  heap_compat h1 h2 ->
  (h1 \u h2)^^ro = h1^^ro \+ h2^^ro.
Proof using. introv D. forwards*: parts_heap_union_of_compat D. Qed.

Hint Rewrite part_rw_heap_union_of_compat part_ro_heap_union_of_compat : rew_fmap.

(* ---------------------------------------------------------------------- *)
(* ** Projections *)

(** Components *)

Definition proj_rw (h:heap) : heap :=
  mkrw (h^^rw).

Definition proj_ro (h:heap) : heap :=
  mkro (h^^ro).

(* Equivalent definitions *)

Program Definition proj_rw' (h:heap) : heap :=
  match h with (f,r) => exist (f,Fmap.empty) _ end.

Program Definition proj_ro' (h:heap) : heap :=
  match h with (f,r) => exist (Fmap.empty,r) _ end.

Notation "h '^rw'" := (proj_rw h)
   (at level 9, format "h '^rw'") : heap_scope.

Notation "h '^ro'" := (proj_ro h)
   (at level 9, format "h '^ro'") : heap_scope.

(** Decomposition as union of projections *)

Lemma heap_compat_projs : forall h,
  heap_compat (h^rw) (h^ro).
Proof using. 
  hint agree_empty_l.
  intros ((f,r),D). split; simple*.
Qed.

Lemma heap_eq_union_projs : forall h,
  h = (h^rw) \u (h^ro).
Proof using.
  intros. lets C: heap_compat_projs h.
  applys heap_eq; rew_fmap*.
Qed.

Lemma heap_eq_projs : forall h1 h2,
  h1^rw = h2^rw ->
  h1^ro = h2^ro ->
  h1 = h2.
Proof using.
  introv M1 M2. applys heap_eq.
  { unfolds proj_rw, mkrw. inverts* M1. }
  { unfolds proj_ro, mkro. inverts* M2. }
Qed.

(* TODO: rename heap_eq into heap_eq_parts *)

(* not needed?
Lemma heap_state_projs : forall h,
  heap_state h = heap_state (h^rw) \+ heap_state (h^ro).
*)


(* ---------------------------------------------------------------------- *)
(* ** Properties of [proj] on [parts] *)

Lemma part_rw_proj_rw : forall h,
  (h^rw)^^rw = h^^rw.
Proof using. intros ((f,r),D). auto. Qed.

Lemma part_rw_proj_ro : forall h,
  (h^ro)^^rw = Fmap.empty.
Proof using. intros ((f,r),D). auto. Qed.

Lemma part_ro_proj_rw : forall h,
  (h^rw)^^ro = Fmap.empty.
Proof using. intros ((f,r),D). auto. Qed.

Lemma part_ro_proj_ro : forall h,
  (h^ro)^ro = h^ro.
Proof using. intros ((f,r),D). auto. Qed.

Hint Rewrite part_rw_proj_rw part_rw_proj_ro
             part_ro_proj_rw part_ro_proj_ro : rew_fmap.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [heap_compat] *)

Lemma heap_compat_def : forall h1 h2,
    heap_compat h1 h2
  =   ( (Fmap.agree h1^^ro h2^^ro)
    /\ (\# (h1^^rw) (h2^^rw) (h1^^ro \+ h2^^ro))).
Proof using. auto. Qed.
(*
Hint Rewrite heap_compat_def : rew_disjoint.
*)
Lemma heap_compat_sym : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat h2 h1.
Proof using. introv (M1&M2). split*. Qed.

Hint Resolve heap_compat_sym.

Lemma heap_compat_empty_l : forall h,
  heap_compat heap_empty h.
Proof using.
  hint agree_empty_l.
  intros. lets: heap_disjoint_parts h.
  unfold heap_empty. split; simple*.
Qed.

Lemma heap_compat_empty_r : forall h,
  heap_compat h heap_empty.
Proof using. autos* heap_compat_sym heap_compat_empty_l. Qed.

Hint Resolve heap_compat_empty_l heap_compat_empty_r.

(* TODO: optimize automation
Hint Extern 1 (disjoint _ _) => 
  jauto_set; rew_disjoint; assumption.
*)

Lemma heap_compat_union_l : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h1 h3 ->
  heap_compat h2 h3 ->
  heap_compat (h1 \u h2) h3.
Proof using.
  hint agree_union_l.
  introv M1 M2 M3. lets M1': M1.
  unfold heap_compat in M1, M2, M3.
  rew_disjoint. split; rew_fmap*.
Qed.

Lemma heap_compat_union_r : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h1 h3 ->
  heap_compat h2 h3 ->
  heap_compat h1 (h2 \u h3).
Proof using. hint heap_compat_sym, heap_compat_union_l. autos*. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [heap_compat] on [proj] *)

Lemma heap_compat_proj_ro_r : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat h1 (proj_ro h2).
Proof using.
  hint agree_empty_r.
  introv (D&G). split; rew_fmap; auto.
Qed.

Lemma heap_compat_proj_ro_l : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat (proj_ro h1) (h2).
Proof using.
  introv D. autos* heap_compat_proj_ro_r heap_compat_sym.
Qed.

Lemma heap_compat_proj_rw_r : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat h1 (proj_rw h2).
Proof using.
  hint agree_empty_r.
  introv (D&G). split; rew_fmap; auto.
Qed.

Lemma heap_compat_proj_rw_l : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat (proj_rw h1) (h2).
Proof using.
  introv D. autos* heap_compat_proj_rw_r heap_compat_sym.
Qed.

Hint Resolve heap_compat_proj_ro_r heap_compat_proj_ro_l.
Hint Resolve heap_compat_proj_rw_r heap_compat_proj_rw_l.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [proj] *)

Implicit Types h : heap.

(* Corollary
Lemma heap_compat_parts : forall h,
  heap_compat (h^rw) (h^ro).
Proof using. intros. applys heap_compat_of_disjoint. applys disjoint_parts. Qed.
 *)

Lemma proj_rw_empty :
  (heap_empty^rw) = heap_empty.
Proof using. applys* heap_eq. Qed.

Lemma proj_ro_empty :
  (heap_empty^ro) = heap_empty.
Proof using. applys* heap_eq. Qed.

Hint Rewrite proj_rw_empty proj_ro_empty : rew_heap.

Lemma proj_rw_idempotent : forall h,
  (h^rw)^rw = h^rw.
Proof using. intros. applys* heap_eq. Qed.

Lemma proj_ro_idempotent : forall h,
  (h^ro)^ro = h^ro.
Proof using. intros. applys* heap_eq. Qed.

Hint Rewrite proj_rw_idempotent proj_ro_idempotent : rew_fmap rew_heap.

Lemma proj_ro_proj_rw : forall h,
  (h^rw)^ro = heap_empty.
Proof using. intros. applys* heap_eq. Qed.

Lemma proj_rw_proj_ro : forall h,
  (h^ro)^rw = heap_empty.
Proof using. intros. applys* heap_eq. Qed.

Hint Rewrite proj_ro_proj_rw proj_rw_proj_ro : rew_fmap rew_heap.

(* Reformulation of [heap_affine_onlyrw] *) (* TODO: rename *)
Lemma heap_affine_onlyrw' : forall h,
  heap_affine h ->
  h^ro = heap_empty.
Proof using.
  introv M. lets E: heap_affine_onlyrw M.
  unfold proj_ro, mkro. rewrite E. applys* heap_eq.
Qed. (* TODO: higher level ?*)


Lemma proj_rw_mkrw : forall s,
  (mkrw s)^rw = mkrw s.
Proof using. intros. applys* heap_eq. Qed.

Lemma proj_ro_mkrw : forall s,
  (mkrw s)^ro = heap_empty.
Proof using. intros. applys* heap_eq. Qed.

Hint Rewrite proj_rw_mkrw proj_ro_mkrw : rew_heap.

Lemma proj_ro_mkro : forall s,
  (mkro s)^ro = mkro s.
Proof using. intros. applys* heap_eq. Qed.

Lemma proj_rw_mkro : forall s,
  (mkro s)^rw = heap_empty.
Proof using. intros. applys* heap_eq. Qed.

Hint Rewrite proj_rw_mkro proj_ro_mkro : rew_heap.

Lemma proj_rw_union : forall h1 h2,
  heap_compat h1 h2 ->
  (h1 \u h2)^rw = (h1^rw) \u (h2^rw).
Proof using.
  hint heap_compat_proj_rw_r.
  introv D. unfold proj_rw.
  applys* heap_eq; rew_fmap*.
Qed.

Lemma proj_ro_union : forall h1 h2,
  heap_compat h1 h2 ->
  (h1 \u h2)^ro = (h1^ro) \u (h2^ro).
Proof using.
  hint heap_compat_proj_ro_r.
  introv D. unfold proj_ro.
  applys* heap_eq; rew_fmap*.
Qed.

Hint Rewrite proj_rw_union proj_ro_union : rew_heap.


(* ---------------------------------------------------------------------- *)
(* ** Auxiliary function [toro] *)

(** [toro h] defines the read-only heap associated with [h],
    i.e. covering the same memory cells, but with all tagged
    as read-only. *)

Program Definition toro (h:heap) : heap :=
  (Fmap.empty, h^^rw \+ h^^ro).

Lemma part_rw_toro : forall h,
  (toro h)^^rw = Fmap.empty.
Proof using. auto. Qed.

Lemma part_ro_toro : forall h,
  (toro h)^^ro = h^^rw \+ h^^ro.
Proof using. auto. Qed.

Lemma proj_rw_toro : forall h,
  (toro h)^rw = heap_empty.
Proof using. auto. Qed.

Lemma proj_ro_toro : forall h,
  (toro h)^ro = (toro h).
Proof using. auto. Qed.

Lemma heap_state_toro : forall h,
  heap_state (toro h) = heap_state h.
Proof using.
  intros h. do 2 rewrite heap_state_def. rewrite part_rw_toro, part_ro_toro.
  fmap_eq.
Qed.

Hint Rewrite proj_rw_toro proj_ro_toro : rew_fmap rew_heap.
Hint Rewrite part_rw_toro part_ro_toro heap_state_toro : rew_fmap.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [heap_union] *)

(* not needed? *)
Lemma heap_union_def : forall h1 h2,
  heap_compat h1 h2 -> exists D,
  h1 \u h2 = exist (h1^^rw \+ h2^^rw, h1^^ro \+ h2^^ro) D.
Proof using.
  introv M. unfold heap_union.
  rewrite (classicT_l M). esplit. destruct~ M.
Qed.

(* not needed? *)
Lemma heap_union_spec : forall h1 h2,
  heap_compat h1 h2 ->
     (h1 \u h2)^^rw = h1^^rw \+ h2^^rw
  /\ (h1 \u h2)^^ro = h1^^ro \+ h2^^ro.
Proof using.
  introv M. lets (D&E): heap_union_def M. rewrite~ E.
Qed.

(* not needed? *)
Lemma heap_union_f : forall h1 h2,
  heap_compat h1 h2 ->
  (h1 \u h2)^^rw = h1^^rw \+ h2^^rw.
Proof using.
  introv D. unfold heap_union. rewrite (classicT_l D).
  destruct h1 as ((f1,r1)&D1). destruct h2 as ((f2,r2)&D2).
  unstate. fmap_eq.
Qed.

(* not needed? *)
Lemma heap_union_r : forall h1 h2,
  heap_compat h1 h2 ->
  (h1 \u h2)^^ro = h1^^ro \+ h2^^ro.
Proof using.
  introv D. unfold heap_union. rewrite (classicT_l D).
  destruct h1 as ((f1,r1)&D1). destruct h2 as ((f2,r2)&D2).
  unstate. fmap_eq.
Qed.

Hint Rewrite heap_union_f heap_union_r : rew_fmap.
(* TODO: rename *)

(* ---------------------------------------------------------------------- *)

Lemma heap_compat_refl_if_ro : forall h,
  h^^rw = Fmap.empty ->
  heap_compat h h.
Proof using.
  hint Fmap.agree_refl.
  introv M. unfolds. rewrite* M.
Qed.

Lemma heap_compat_toro_l : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat (toro h1) h2.
Proof using.
  introv (N1&N2). split; simpl.
  { applys~ Fmap.agree_union_l. applys~ Fmap.agree_of_disjoint. }
  { auto. } (* TODO: slow *)
Qed.

Lemma heap_compat_part_ro_toro : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat h1 (toro h2).
Proof using.
  hint heap_compat_toro_l, heap_compat_sym. autos*.
Qed.

Lemma heap_compat_toro : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat (toro h1) (toro h2).
Proof using.
  introv (M1&M2). split.
  { do 2 rewrite part_ro_toro.
    applys~ Fmap.agree_union_lr. }
  { do 2 rewrite part_rw_toro. auto. }
Qed.

Lemma heap_compat_inv_disjoint_part_rw : forall h1 h2,
  heap_compat h1 h2 ->
  disjoint (h1^^rw) (h2^^rw).
Proof using.
  introv M. unfolds heap_compat. auto.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [heap_state] *)

Lemma heap_state_eq : forall h,
  heap_state h = h^^rw \+ h^^ro.
Proof. auto. Qed.

Lemma heap_state_empty : heap_state heap_empty = Fmap.empty.
Proof. unfold heap_empty. unstate. fmap_eq. Qed.

Lemma heap_state_union : forall h1 h2,
  heap_compat h1 h2 ->
  heap_state (h1 \u h2) = heap_state h1 \+ heap_state h2.
Proof using.
  introv C. unfold heap_state. rew_fmap*. 
  unfolds heap_compat. fmap_eq.
Qed.

Hint Rewrite heap_state_empty heap_state_union : rew_fmap.


(* ---------------------------------------------------------------------- *)
(* ** More properties of [heap_union] *)

(* Note: below, the hypothesis is not needed, but it makes sense to have it *)
Lemma heap_union_comm : forall h1 h2,
  heap_compat h1 h2 ->
  h1 \u h2 = h2 \u h1.
Proof using.
  introv M1. lets M1': M1. unfold heap_compat in M1'.
  applys heap_eq; rew_fmap*.
  { fmap_eq. }
  { applys* Fmap.union_comm_of_agree. }
Qed.

Lemma heap_union_assoc : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h2 h3 ->
  heap_compat h1 h3 ->
  (h1 \u h2) \u h3 = h1 \u (h2 \u h3).
Proof using.
  hint heap_compat_union_l, heap_compat_union_r.
  introv M1 M2 M3. applys heap_eq; rew_fmap*.
Qed.

Lemma heap_union_empty_l : forall h,
  heap_empty \u h = h.
Proof using. intros h. applys heap_eq; rew_fmap*. Qed.

Lemma heap_union_empty_r : forall h,
  h \u heap_empty = h.
Proof using.
  intros. rewrite* heap_union_comm. apply* heap_union_empty_l.
Qed.

Hint Rewrite heap_union_empty_l heap_union_empty_r: rew_heap.



(* ---------------------------------------------------------------------- *)
(* ** More properties of [heap_compat] *)

Lemma heap_compat_union_l_inv_l : forall h1 h2 h3,
  heap_compat (h1 \u h2) h3 ->
  heap_compat h1 h2 ->
  heap_compat h2 h3.
Proof using.
  introv M2 M1. lets (C1&D1): M1. lets (C2&D2): M2.
  rew_fmap~ in *. forwards~ (N1&N2): Fmap.agree_union_l_inv C2.
  split*.
Qed.

Lemma heap_compat_union_l_inv_r : forall h1 h2 h3,
  heap_compat (h1 \u h2) h3 ->
  heap_compat h1 h2 ->
  heap_compat h1 h3.
Proof using.
  hint heap_compat_sym.
  introv M1 M2. rewrite* heap_union_comm in M1.
  applys* heap_compat_union_l_inv_l.
Qed.

Lemma heap_compat_union_l_inv : forall h1 h2 h3,
  heap_compat (h1 \u h2) h3 ->
  heap_compat h1 h2 ->
  heap_compat h1 h3 /\ heap_compat h2 h3.
Proof using.
  hint heap_compat_union_l_inv_l, heap_compat_union_l_inv_r. autos*.
Qed.

Lemma heap_compat_union_r_inv : forall h1 h2 h3,
  heap_compat h1 (h2 \u h3) ->
  heap_compat h2 h3 ->
  heap_compat h1 h2 /\ heap_compat h1 h3.
Proof using.
  introv M1 M2. rewrite* heap_union_comm in M1.
  lets M1': heap_compat_sym M1.
  forwards~ (N1&N2): heap_compat_union_l_inv M1'.
Qed.

Lemma heap_compat_mkrw_inv : forall s1 s2,
  heap_compat (mkrw s1) (mkrw s2) ->
  disjoint s1 s2.
Proof using. introv (A&D). rew_fmap* in *. Qed.


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

Implicit Type H : hprop.

Section Properties.

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
    exists* h1 (h2 \u h3). rewrite* heap_union_assoc. }
  { intros (h1&h'&P1&(h2&h3&M2&P2&P3&->)&M1&->).
    lets~ (M1a&M1b): heap_compat_union_r_inv M1.
    exists* (h1 \u h2) h3. rewrite* heap_union_assoc. }
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

End Aux.

Global Opaque heap_affine.


(* ---------------------------------------------------------------------- *)
(* ** Singleton heap *)

Definition hsingle (l:loc) (v:val) : hprop :=
  fun h =>    h = mkrw (Fmap.single l v)
           /\ l <> null.

Notation "l '~~~>' v" := (hsingle l v)
  (at level 32, no associativity) : heap_scope.

Lemma hstar_hsingle_same_loc : forall (l:loc) (v1 v2:val),
  (l ~~~> v1) \* (l ~~~> v2) ==> \[False].
Proof using.
  intros. intros h (h1&h2&(E1&N1)&(E2&N2)&C&E). subst. false.
  lets: heap_compat_mkrw_inv C.
  applys* Fmap.disjoint_single_single_same_inv l v1 v2.
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
(* ** Definitions and properties of [onlyrw] *)

Definition onlyrw (H:hprop) : Prop :=
  forall h, H h -> h^ro = heap_empty.

Definition onlyrw_post A (Q:A->hprop) : Prop :=
  forall x, onlyrw (Q x).

Lemma onlyrw_proj_ro : forall H h,
  onlyrw H ->
  H h ->
  h^ro = heap_empty.
Proof using. introv N K. applys* N. Qed.

Lemma onlyrw_proj_rw : forall H h,
  onlyrw H ->
  H h ->
  h^rw = h.
Proof using.
  introv N K. rewrite (heap_eq_union_projs h) at 2.
  rewrite* N. rew_heap*.
Qed.

Lemma onlyrw_of_haffine : forall H,
  haffine H ->
  onlyrw H.
Proof using.
  introv M. intros h K. rewrite haffine_eq in M.
  specializes M K. applys* heap_affine_onlyrw'.
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
  applys* heap_affine_onlyrw'. rewrite haffine_eq in F. applys* F.
Qed.

Lemma onlyrw_hempty' : (* simpler proof *)
  onlyrw \[].
Proof using.
  intros. rewrite hempty_eq_hpure_true. applys~ onlyrw_hpure.
Qed.

Lemma onlyrw_hsingle : forall l v,
  onlyrw (hsingle l v).
Proof using. introv (->&N). rew_heap. autos*. Qed.

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
  rewrites~ (>> N P2). rew_heap*.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** onlyro *)

Definition onlyro (H:hprop) : Prop :=
  forall h, H h -> h^rw = heap_empty.

Definition onlyro_post A (Q:A->hprop) : Prop :=
  forall x, onlyro (Q x).

Lemma onlyro_rw : forall H h,
  onlyro H ->
  H h ->
  h^rw = heap_empty.
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
(* ** RO *)

Section RO.

Definition RO (H:hprop) : hprop :=
  fun h => exists h', H h' /\ h = toro h'.

Lemma toro_pred : forall (H:hprop) h,
  H h ->
  RO H (toro h).
Proof using.
  introv N. exists h. split~.
Qed.

(* TODO: move *)
Lemma toro_empty :
  toro heap_empty = heap_empty.
Proof using. intros. applys heap_eq; rew_fmap*. Qed.

Hint Rewrite toro_empty : rew_heap.


Lemma RO_heap_empty : forall (H:hprop),
  H heap_empty ->
  RO H heap_empty.
Proof using. introv N. exists heap_empty. rew_heap*. Qed.

Hint Resolve toro_pred RO_heap_empty.

(* TODO: move *)
(** corollary of heap_compat_refl_of_rw_empty *)
Lemma heap_compat_refl_toro : forall h,
  heap_compat (toro h) (toro h).
Proof using. (* 
  intros. applys heap_compat_refl_of_rw_empty. rew_heap*.
Qed. TODO *)  Admitted.


Lemma RO_duplicatable : forall H,
  duplicatable (RO H).
Proof using.
  intros H h M. lets (h'&M1&M2): M. subst.
  lets D: heap_compat_refl_toro h'. do 2 esplit. splits*.
(* TODO: toro h' = toro h' \u toro h' *)
Admitted.

Lemma RO_covariant : forall H1 H2,
  H1 ==> H2 ->
  (RO H1) ==> (RO H2).
Proof using.
  introv M. intros h (h'&M1&->). auto.
Qed.


Axiom toro_idempotent : forall h,
  toro (toro h) = toro h.

Lemma RO_RO : forall H,
  RO (RO H) = RO H.
Proof using.
  hint toro_idempotent.
  intros. apply pred_ext_1. intros h. unfolds RO.
  iff (h'&(h''&M1'&->)&->) (h'&M1&->).
  { exists* h''. }
  { exists* (toro h'). }
Qed.

Lemma RO_empty :
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
Lemma RO_empty' :
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

Axiom toro_union : forall h1 h2,
  heap_compat h1 h2 ->
  toro (h1 \u h2) = (toro h1) \u (toro h2).

Hint Rewrite toro_union : rew_heap.

Lemma RO_star : forall H1 H2,
  RO (H1 \* H2) ==> (RO H1 \* RO H2).
Proof using.
  hint hstar_intro.
  intros. intros h (h'&(h1&h2&N1&P1&P2&->)&->).
  lets C: heap_compat_toro P2.
  exists (toro h1) (toro h2). rew_heap*.
Qed.

Arguments RO_star : clear implicits.

Lemma onlyro_RO : forall H,
  onlyro (RO H).
Proof using.
  introv (h'&K&E). subst. rew_heap*.
Qed.

End RO.



(* ********************************************************************** *)
(* * Elimination lemmas useful to simplify proofs *)

(* TODO: rename *)

(* TODO: change to h^rw *)

Lemma onlyrw_rw_elim : forall H h,
  onlyrw H ->
  H h ->
  H (mkrw (h^^rw)).
Proof using. introv N K. rewrite~ mkrw_part_rw_of_ro_empty. Qed.

Lemma onlyrw_onlyro_rw_elim : forall HF HR h,
  onlyrw HF ->
  onlyro HR ->
  (HF \* HR) h ->
  HF (mkrw (h^^rw)).
Proof using.
  introv NF NR (h1&h2&K1&K2&D&->). rew_heap*.
  rewrites* (>> onlyro_rw K2). rew_fmap.
  rewrite~ mkrw_part_rw_of_ro_empty.
Qed.


(* ********************************************************************** *)
(* isframe *)

Definition isframe (HI HO:hprop) : Prop :=
  exists HR, onlyrw HO /\ onlyro HR /\ HI = HO \* HR.

Lemma isframe_rw_elim : forall HI HO h,
  isframe HI HO ->
  HI h ->
  HO (mkrw (h^^rw)).
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

(* ---------------------------------------------------------------------- *)
(* ** Tactic [himpl_fold] *)

(** [himpl_fold] applies to a goal of the form [H1 h].
    It searches the context for an assumption of the from [H2 h],
    then replaces the goal with [H1 ==> H2].
    It also deletes the assumption [H2 h]. *)

Ltac himpl_fold_core tt :=
  match goal with N: ?H ?h |- _ ?h =>
    applys himpl_inv N; clear N end.

Tactic Notation "himpl_fold" := himpl_fold_core tt.
Tactic Notation "himpl_fold" "~" := himpl_fold; auto_tilde.
Tactic Notation "himpl_fold" "*" := himpl_fold; auto_star.

(* TODO: remove *)


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
(* ** Definition of Hoare triples in a logic with read-only predicates *)

Definition hoare (t:trm) (H:hprop) (Q:val->hprop) :=
  forall h, H h -> exists h' v, eval (heap_state h) t (heap_state h') v
                             /\ Q v (mkrw (h'^^rw))
                             /\ h'^^ro = h^^ro.


Lemma hoare_conseq : forall t H' Q' H Q,
  hoare t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoare t H Q.
Proof using.
  introv M MH MQ HF. forwards (h'&v&R&K&E): M h.
  { himpl_fold~. }
  exists h' v. splits~. { himpl_fold. auto. }
Qed.

Lemma hoare_frame_read_only : forall t H1 Q1 H2,
  hoare t (H1 \* RO H2) Q1 ->
  onlyrw H2 ->
  hoare t (H1 \* H2) (Q1 \*+ H2).
Proof using.
   hint heap_compat_part_ro_toro. (*, heap_compat_part_l,
    heap_compat_part_r, heap_compat_union_r.
  hint heap_compat_part, heap_compat_of_disjoint. *)
  introv M N. intros ? (h1&h2&P1&P2&R1&->).
  forwards (h'&v&R&L&S): M (h1 \u toro h2).
  { exists h1 (toro h2). splits~. { applys* toro_pred. } }
   (* rewrite Eh' in R. rewrite S in R. rew_heap~ in R.*)
  exists ((mkrw h'^^rw) \u (mkro h1^^ro) \u h2) v. splits.
  { applys_eq R. { rew_heap*. rew_fmap*. }
     { rewrite (heap_state_eq h'). rew_fmap*. 
(* TODO heap_compat (h1^^^ro) h2 *)
(* TODO
  asserts C': (heap_compat h'^^^rw h1^^^ro)-- trivial
          h'^^ro = (h1 \u toro h2)^^ro -> heap_compat (h'^^^rw) h2)).
  { rew_fmap in Dh';[|auto]. applys heap_compat_of_disjoint. rew_fmap; [|auto].
    rewrite disjoint_union_eq_r.
    rewrite <- (disjoint_toro_eq _ h2). auto. }
*)
(* TODO: heap_state (h^^^rw) *)
skip. skip. skip. } } (* TODO (h1 \u h2) ^^^rw = ... *)
(* TODO  (h1^^^ro)^^^rw *)
skip.
skip.
Qed.
  (* Adding facts
  lets (Eh'&Dh'): part_rwmap_parts h'.
  rewrite S in Dh'.
  asserts C': (heap_compat h'^^rw (h1^^ro \u h2)).
  { rew_fmap in Dh';[|auto]. applys heap_compat_of_disjoint. rew_fmap; [|auto].
    rewrite disjoint_union_eq_r.
    rewrite <- (disjoint_toro_eq _ h2). auto. }
 *)

(* TODO: rename part_rw, part_ro *)
(* TODO: notation for (mkrw h'^^rw) \u (mkro h1^^ro),
   ^^^rw and ^^^ro. *)


Lemma hoare_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, hoare t (J x) Q) ->
  hoare t (hexists J) Q.
Proof using. introv M. intros h (x&Hh). applys M Hh. Qed.

Lemma hoare_hpure : forall t (P:Prop) H Q,
  (P -> hoare t H Q) ->
  hoare t (\[P] \* H) Q.
Proof using.
  introv M. intros h (h1&h2&(HP&M1)&M2&D&->).
  lets ->: hempty_inv M1. rew_fmap*.
Qed.


(* ********************************************************************** *)
(** * Hoare rules for term constructs *)

Implicit Types v : val.

Lemma hoare_val : forall HI HO v,
  isframe HI HO ->
  hoare (trm_val v) HI (fun r => \[r = v] \* HO).
Proof using. (*
  introv HF. intros h K. exists h v. splits~.
  { applys eval_val. }
  { rewrite hstar_hpure_l. split~. applys* isframe_rw_elim. }
Qed. *) Admitted.

Lemma hoare_fix : forall HI HO f x t1,
  isframe HI HO ->
  hoare (trm_fix f x t1) HI (fun r => \[r = (val_fix f x t1)] \* HO).
Proof using. (*
  introv HF. intros h K. exists h (val_fix f x t1). splits~.
  { applys eval_fix. }
  { rewrite hstar_hpure_l. split~. applys* isframe_rw_elim. } 
Qed. *) Admitted.

Lemma hoare_app_fix : forall v1 v2 (f:var) x t1 H Q,
  v1 = val_fix f x t1 ->
  f <> x ->
  hoare (subst x v2 (subst f v1 t1)) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof using. (*
  introv E D M. intros s K0. forwards (s'&v&R1&K1&E1): (rm M) K0.
  exists s' v. splits~. { applys* eval_app E R1. auto_false. }
Qed. *) Admitted.

(* Note: the order of the heap predicates is carefully
   chosen so as to simplify the proof. *)
Lemma hoare_let : forall x t1 t2 H1 H2 Q1 Q HI HO,
  isframe HI HO ->
  hoare t1 (RO H2 \* HI \* H1) (Q1 \*+ HO) ->
  (forall v H3, onlyro H3 -> hoare (subst x v t2) (Q1 v \* HO \* H2 \* H3) (Q \*+ HO)) ->
  hoare (trm_let x t1 t2) (H2 \* HI \* H1) (Q \*+ HO).
Proof using. (*
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
  lets: disjoint_parts h1'. rewrite E1 in H.
    rew_fmap in H; [|auto|auto].
  2: { applys heap_compat_toro_l. auto. }
  rewrite disjoint_union_eq_r in H. destruct H as (H&H').
    rewrite disjoint_toro_eq in H.
  lets Hs: H. lets: heap_compat_of_disjoint Hs.
  lets (X&Y): heap_fmap_parts h2.
    rewrite X in H. rewrite disjoint_union_eq_r in H,H'.
  asserts: (heap_compat h1'^^rw (hI^^ro \u h1^^ro)).
  { applys heap_compat_union_r.
        { applys* heap_compat_of_disjoint. }
        { applys* heap_compat_of_disjoint. }
        { applys* heap_compat_part. } }
  asserts: (heap_compat h2 (hI^^ro \u h1^^ro)).
  { applys heap_compat_union_r.
        { applys* heap_compat_part_r. }
        { applys* heap_compat_part_r. }
        { applys* heap_compat_part. } }
  asserts: (heap_compat h1'^^rw (h2 \u hI^^ro \u h1^^ro)).
   { applys* heap_compat_union_r. }
  (* Remaining of the proof *)
  forwards (h2'&v2&R2&K2&E2): (rm M2) v1 (= hI^^ro \u h1^^ro) (h1'^^rw \u h2 \u hI^^ro \u h1^^ro).
  { intros ? ->. rew_heap*. }
  { rewrite <- hstar_assoc. applys* hstar_intro.
    { applys* hstar_intro. } }
  lets D1': heap_compat_toro_l D1.
  lets D1'': D1'. rew_fmap* in D1''. (* TODO: cleanup *)
  exists h2' v2. splits*.
  { applys eval_let_trm (heap_state h1').
    { applys_eq R1. subst h hr. rew_fmap*. }
    { applys_eq R2. lets (E1'&_): heap_fmap_parts h1'.
      rewrite E1' at 1. rewrite E1. rew_fmap*. } }
  { rewrite E2. rewrite U1,U2. rew_fmap*. }
Qed. *) Admitted.

Lemma hoare_if : forall (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.
Proof using. (*
  introv M1. intros h Hh. forwards* (h1'&v1&R1&K1&E1): (rm M1).
  exists h1' v1. splits*. { applys* eval_if. }
Qed. *) Admitted.

Notation "l '~~>' v" := (hsingle l v)
  (at level 32, no associativity) : heap_scope.


Lemma hoare_ref : forall HI HO v,
  isframe HI HO ->
  hoare (val_ref v)
    (HI)
    (fun r => (\exists p, \[r = val_loc p] \* p ~~> v) \* HO).
Proof using. (*
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
Qed. *) Admitted.

Implicit Types p : loc.

Lemma hoare_get_ro : forall HI HO v p,
  isframe HI HO ->
  hoare (val_get p)
    (RO (p ~~> v) \* HI)
    (fun r => \[r = v] \* HO).
Proof using. (*
  introv NH. intros s (s1&s2&P1&P2&D&U).
  destruct P1 as (h'&K'&E). lets (->&N): hsingle_inv K'.
  exists s v. splits.
  { rew_fmap* in *. applys* eval_get_sep (heap_state s1) (heap_state s2);
    subst s s1; rew_fmap*. }
  { rewrite~ hstar_hpure_l. split~. subst s s1. rew_heap*.
    applys* isframe_rw_elim. }
  { auto. }
Qed. *) Admitted.

Lemma hoare_set : forall HI HO w p v,
  isframe HI HO ->
  hoare (val_set (val_loc p) v)
    ((p ~~> w) \* HI)
    (fun r => \[r = val_unit] \* (p ~~> v) \* HO).
Proof using. (*
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
Qed. *) Admitted.

Lemma hoare_free : forall HI HO p v,
  isframe HI HO ->
  hoare (val_free (val_loc p))
    ((p ~~> v) \* HI)
    (fun r => \[r = val_unit] \* HO).
Proof using. (*
  introv NH. intros s1 K0.
  destruct K0 as (h1&h2&P1&P2&D&U). lets (K&N): hsingle_inv P1.
  forwards D': disjoint_of_compat_single D K v.
  exists h2 val_unit. splits.
  { subst h1. applys* eval_free_sep; subst; rew_fmap*. }
  { rewrite hstar_hpure_l. split~. applys* isframe_rw_elim. }
  { subst. rew_fmap*. }
Qed. *) Admitted.



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

(* TODO : move *)
Lemma onlyro_RO : forall H,
  onlyro (RO H).
Proof using.
  introv (h'&K&E). subst. rew_heap*.
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
  (*
  intros H h K. forwards (->&_): (heap_parts h).
  exists (= h^^rw) (= h^^ro). do 2 rewrite hstar_hpure. splits.
  { intros ? ->. rew_heap*. }
  { intros ? ->. rew_heap*. }
  { applys* hstar_intro. applys heap_compat_of_disjoint. applys disjoint_parts. }
Qed.*) Admitted. (* TODO: h = h^^^rw \u h^^^ro = h^^^rw \+ h^^^ro *)

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



(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(* * Reasoning rules, low-level proofs


(* ********************************************************************** *)
(* * Ramified read-only frame rule *)

(* ---------------------------------------------------------------------- *)
(* ** Definition of the [normally] modality *)

Definition normally H : hprop :=
  fun h => H h /\ h^^ro = Fmap.empty.

Instance Normal_normally : forall H,
  Normal (normally H).
Proof using. introv (M&E). auto. Qed.

Lemma normally_erase : forall H,
  normally H ==> H.
Proof using. intros H h (N&E). auto. Qed.

Arguments normally_erase : clear implicits.

(* check if really needed *)
Lemma hwand_normally_l_erase : forall H1 H2,
  H1 \-* H2 ==> normally H1 \-* H2.
Proof using. intros. applys hwand_himpl_l. applys normally_erase. Qed.

Arguments hwand_normally_l_erase : clear implicits.

Lemma normally_intro : forall H,
  Normal H ->
  H ==> normally H.
Proof using. introv N. intros h M. split~. Qed.

Lemma normally_Normal_eq : forall H,
  Normal H -> normally H = H.
Proof using. introv N.
  applys himpl_antisym; [apply normally_erase|apply normally_intro, _].
Qed.

Lemma normally_himpl : forall H1 H2,
  (H1 ==> H2) ->
  normally H1 ==> normally H2.
Proof using. introv M. intros h (N&E). split~. Qed.

Lemma normally_idempotent : forall H,
  normally (normally H) = normally H.
Proof using. intros. apply normally_Normal_eq, _. Qed.

Lemma normally_hpure : forall (P:Prop),
  normally \[P] = \[P].
Proof using. intros. apply normally_Normal_eq, _. Qed.

Lemma normally_hempty :
  normally \[] = \[].
Proof using. intros. apply normally_Normal_eq, _. Qed.

Lemma normally_hexists : forall A (J:A->hprop),
  normally (hexists J) = hexists (fun x => normally (J x)).
Proof using.
  intros. applys himpl_antisym.
  { intros h ((x&N)&E). exists x. split~. }
  { intros h (x&(N&E)). split~. exists~ x. }
Qed.

Lemma normally_hforall : forall A `{IA:Inhab A} (J:A->hprop),
  normally (hforall J) = hforall (fun x => normally (J x)).
Proof using.
  intros. unfolds normally, hforall. applys himpl_antisym.
  { intros h N x. autos*. }
  { intros h N. lets (_&E): N (arbitrary (A:=A)). split.
    { intros x. forwards*: N x. }
    { auto. } }
Qed.

Lemma normally_hforall_drop : forall A (J:A->hprop),
  normally (hforall J) ==> hforall (fun x => (J x)).
Proof using.
  intros. unfolds normally, hforall.
  intros h N x. autos*.
Qed.

Lemma normally_hor : forall H1 H2,
  normally (hor H1 H2) = hor (normally H1) (normally H2).
Proof using.
  intros H1 H2. unfolds hor. rewrite normally_hexists.
  fequals. applys fun_ext_1. intros b. destruct* b.
Qed.

Lemma normally_hand_l : forall H1 H2,
  normally (hand H1 H2) = hand (normally H1) H2.
Proof using.
  intros H1 H2. unfolds hand. applys himpl_antisym.
  { rewrite normally_hforall; [|typeclass].
    applys himpl_hforall_r. intros b. destruct b.
    { applys* himpl_hforall_l true. }
    { applys* himpl_hforall_l false. applys* normally_erase. } }
  { (* TODO: is it possible to complete this proof without revealing [h]? *)
    intros h M. lets M1: M true. lets M2: M false.
    rewrite normally_hforall; [|typeclass]. intros b. destruct b.
    { auto. }
    { destruct M1. split*. } }
Qed.

Lemma normally_hand_r : forall H1 H2,
  normally (hand H1 H2) = hand H1 (normally H2).
Proof using.
  intros. rewrite hand_sym. rewrite normally_hand_l.
  rewrite* hand_sym.
Qed.

Lemma normally_hstar : forall H1 H2,
  normally (H1 \* H2) = normally H1 \* normally H2.
Proof using.
  intros. applys himpl_antisym.
  { intros h ((h1&h2&M1&M2&M3&M4)&E). subst h. rew_heap~ in E.
    exists h1 h2. splits~.
    { split~. applys* Fmap.union_eq_empty_inv_l. }
    { split~. applys* Fmap.union_eq_empty_inv_r. } }
  { intros. intros h (h1&h2&(M1&E1)&(M2&E2)&M3&M4). split.
    { exists~ h1 h2. }
    { subst h. rew_heap~. rewrite E1,E2. rew_fmap~. } }
Qed.

Lemma normally_hwand : forall H1 H2,
  normally (H1 \-* H2) ==> normally H1 \-* normally H2.
Proof using.
  intros. unfold hwand. rewrite normally_hexists. xpull ;=> H3.
  rewrite normally_hstar, normally_hpure. xsimpl (normally H3).
  intros M. rewrite <- normally_hstar. applys~ normally_himpl.
Qed.

Lemma normally_hwand_normal : forall H1 H2,
  Normal H1 ->
  normally (H1 \-* H2) ==> H1 \-* normally H2.
Proof.
  intros. xchanges normally_hwand. rewrite normally_Normal_eq; auto.
  xsimpl.
Qed.

Lemma normally_hwand_hstar : forall H1 H2,
  H1 \* (H1 \-* normally H2) ==> H1 \* normally (H1 \-* H2).
Proof.
  intros H1 H2 h (h1 & h2 & Hh1 & Hh2 & ? & ->). eexists _, _.
  split; [eauto|split; [|eauto]]; []. destruct Hh2 as [H0 IMPL].
  rewrite hstar_comm, hstar_hpure in IMPL. destruct IMPL as [IMPL ?]. split.
  { exists H0. rewrite hstar_comm, hstar_hpure.
    eauto using himpl_trans, normally_erase. }
  destruct (IMPL (h1 \u h2)). { eexists _, _; eauto. }
  eapply Fmap.union_eq_empty_inv_r. rewrite <- heap_union_r; eauto.
Qed.

(** Alternative definition of [Normal] in terms of [normally] *)

Definition Normal' H :=
  (H ==> normally H).

Lemma Normal_eq_Normal' :
  Normal = Normal'.
Proof using.
  applys pred_ext_1. intros H. unfold Normal, Normal', normally. iff N.
  { intros h M. split~. }
  { intros h M. forwards~ (R&E): N h. }
Qed.

(* ---------------------------------------------------------------------- *)
(* ** Read-only frame rule reformulated using normally *)

Lemma triple_frame_read_only' : forall t H1 Q1 H2,
  triple t (H1 \* RO H2) Q1 ->
  triple t (H1 \* normally H2) (Q1 \*+ normally H2).
Proof using.
  introv M. intros h1 h2 D (h11&h12&P11&P12&R1&R2).
  lets R1': heap_compat_ro_r R1.
  destruct P12 as (N&E12).
  subst h1. lets~ (D1&D2): heap_compat_union_l_inv (rm D).
  asserts R12: (heap_state (toro h12) = heap_state h12).
  { unstate. rewrite E12. fmap_eq. }
  asserts C: (heap_compat (h11 \u toro h12) h2).
  { apply~ heap_compat_union_l. applys~ heap_compat_ro_l. }
  forwards~ (h1'&v&(N1&N2&N3&N4)): (rm M) (h11 \u (toro h12)) h2.
  { exists h11 (toro h12). splits~.
    { applys~ toro_pred. } }
  rew_heap~ in N3. rewrite E12 in N3.
  lets G: heap_disjoint_parts h1'.
  forwards (h1''&F1&F2): heap_make (h1'^^rw \+ h12^^rw) (h11^^ro).
  { rewrite N3 in G. fmap_disjoint. }
  asserts C': (heap_compat h1'' h2).
  { unfolds. rewrite F1,F2. split.
    { destruct~ D1. }
    { lets G2: heap_disjoint_parts h2. rewrite N3 in G.
      fmap_disjoint. } }
  exists h1'' v. splits.
  { auto. }
  { applys_eq N2; try fmap_eq~.
    { rewrite~ R12. }
    { fequals. unstate. rewrite F1,F2,N3. fmap_eq. } }
  { rew_heap~. rewrite F2,E12. fmap_eq~. }
  {  clears h2.
     rename h1'' into hd. rename H2 into Hb. sets Ha: (Q1 v).
     rename h1' into ha.  rewrite~ Fmap.union_empty_r in N3.
     rename h12 into hb. rename h11 into hc.
     (* LATER: begin separate lemma *)
     destruct N4 as (hx&hy&V1&V2&V3&V4).
     lets G': G. rewrite N3 in G'. rewrite V2 in G'. rew_heap~ in G'.
     asserts C1: (heap_compat hx hb).
     { unfolds. rewrite E12. split.
       { auto. }
       { lets Gx: heap_disjoint_parts hx. rewrite V3. auto. } }
     forwards~ (hyf&W1&W2): heap_make (hy^^rw) (Fmap.empty:state).
     forwards~ (hcr&Y1&Y2): heap_make (Fmap.empty:state) (hc^^ro).
     (* LATER: find a way to automate these lemmas *)
     (* LATER: automate disjoint_parts use by fmap_disjoint *)
     asserts C2: (heap_compat hcr hyf).
     { unfolds. split.
       { rewrite~ W2. }
       { rewrite Y1,Y2,W1,W2. fmap_disjoint. } }
     asserts C3: (heap_compat hx hcr).
     { unfolds. split.
       { rewrite~ V3. }
       { rewrite Y1,Y2,V3. fmap_disjoint. } }
     asserts C4: (heap_compat hx hyf).
     { unfolds. split.
       { rewrite~ W2. }
       { rewrite W1,W2,V3. fmap_disjoint. } }
     asserts C5: (heap_compat hb hyf).
     { unfolds. split.
       { rewrite~ W2. }
       { rewrite W1,W2,E12. fmap_disjoint. } }
     asserts C6: (heap_compat hb hcr).
     { unfolds. split.
       { rewrite~ E12. }
       { rewrite Y1,Y2,E12. fmap_disjoint. } }
     exists (hx \u hb) (hcr \u hyf). splits.
     { auto. }
     { applys heap_eq. split.
       { rewrite F1,V2. rew_heap~. rewrite Y1,W1.
         rewrite Fmap.union_empty_l.
         do 2 rewrite Fmap.union_assoc. fequals.
         applys Fmap.union_comm_of_disjoint. auto. }
       { rew_heap~. rewrite V3,E12,W2,Y2,F2. fmap_eq. } }
     { rew_heap~. rewrite V3,E12. fmap_eq. }
     { exists~ hx hb. splits~. split~. } }
Qed.

(** Derived rule with both frame and read-only frame, using normally *)

Lemma triple_frame_read_only_with_frame : forall t H1 H2 H3 Q1,
  triple t (H1 \* RO H2) Q1 ->
  triple t (H1 \* normally H2 \* normally H3) ((Q1 \*+ normally H2) \*+ normally H3).
Proof using.
  introv M. rewrite <- hstar_assoc. applys triple_frame.
  { applys~ triple_frame_read_only'. }
  { applys Normal_normally. }
Qed.

Lemma triple_frame_read_only_with_frame' : forall t H1 H2 H3 Q1,
  triple t (H1 \* RO H2) Q1 ->
  triple t (H1 \* normally H2 \* normally H3) ((Q1 \*+ normally H2) \*+ H3).
Proof using.
  introv M. lets N: triple_frame_read_only_with_frame H3 M.
  applys triple_conseq N. { xsimpl. } { intros x. xsimpl. apply normally_erase. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Definition of the ROFrame connective *)

Definition ROFrame (H1 H2 : hprop) :=
  \exists H3, normally H3 \* (RO(H3) \-* H1) \* (H3 \-* H2).

Lemma ROFrame_himpl : forall H1 H2 H1' H2',
  H1 ==> H1' ->
  H2 ==> H2' ->
  ROFrame H1 H2 ==> ROFrame H1' H2'.
Proof.
  unfold ROFrame. intros H1 H2 H1' H2' MONO1 MONO2.
  apply himpl_hexists_l ;=>H3. apply himpl_hexists_r with H3. xsimpl.
  rewrite hstar_comm. applys himpl_frame_lr; xsimpl~.
Qed.

Lemma ROFrame_intro : forall H1 H2,
  H1 \* H2 ==> ROFrame H1 H2.
Proof.
  intros. unfold ROFrame. apply himpl_hexists_r with \[].
  rewrite normally_hempty, RO_empty, hstar_hempty_l.
  eapply himpl_trans; [apply himpl_frame_r|apply himpl_frame_l];
    apply himpl_hwand_r; xsimpl.
Qed.

Lemma ROFrame_frame_l : forall H1 H2 H3,
  H1 \* ROFrame H2 H3 ==> ROFrame (H1 \* H2) H3.
Proof.
  intros. unfold ROFrame. xpull ;=> HF. apply himpl_hexists_r with HF. xsimpl.
Qed.

Lemma ROFrame_frame_lr : forall H1 H2 H3,
  Normal H1 ->
  H1 \* ROFrame H2 H3 ==> ROFrame (RO(H1) \* H2) (H1 \* H3).
Proof.
  intros H1 H2 H3 NORM.
  unfold ROFrame. xpull ;=> HF. apply himpl_hexists_r with (H1 \* HF).
  xchange (normally_intro NORM). rewrite normally_hstar. xsimpl.
  applys himpl_frame_lr.
  { xsimpl. xchange (>> RO_star H1 HF). }
  { xsimpl. }
Qed.

Lemma ROFrame_frame_lr' : forall H1 H2 H3,
  Normal H1 ->
  H1 \* ROFrame H2 (H1 \-* H3) ==> ROFrame (RO(H1) \* H2) H3.
Proof.
  intros H1 H2 H3 NORM. xchange (@ROFrame_frame_lr H1 H2 (H1 \-* H3) NORM).
  xsimpl. apply ROFrame_himpl; [xsimpl|]. apply hwand_cancel.
Qed.

Lemma ROFrame_frame_r : forall H1 H2 H3,
  H1 \* ROFrame H2 H3 ==> ROFrame H2 (H1 \* H3).
Proof.
  intros H1 H2 H3. unfold ROFrame. xpull ;=> HF. apply himpl_hexists_r with HF.
  xsimpl.
Qed.

(* ---------------------------------------------------------------------- *)
(* ** Ramified read-only frame rule *)

Lemma triple_ramified_frame_read_only_core : forall H2 t H Q H' Q',
  triple t H' Q' ->
  H = normally H2 \* (RO H2 \-* H') \* (H2 \-* normally (Q' \--* Q)) ->
  triple t H Q.
Proof using.
  introv M W. subst H.
  applys~ triple_conseq ((normally H2 \* normally (normally H2 \-* Q' \--* Q)) \* (RO H2 \-* H')).
  { (* TODO: proof not supported by xsimpl, which cancels out too aggressively *)
    applys himpl_trans (normally H2 \* (RO H2 \-* H') \* (normally H2 \-* normally (Q' \--* Q))).
    { xsimpl. xchange (hwand_normally_l_erase H2 (normally (Q' \--* Q))). }
    { rewrite <- hstar_comm. rewrite <- (hstar_comm (RO H2 \-* H')). rewrite hstar_assoc.
      apply himpl_frame_r. rewrite hstar_comm.
      applys (>> normally_hwand_hstar (normally H2) (Q' \--* Q)). } }
  { forwards K: triple_frame_read_only_with_frame t
                 (RO H2 \-* H') H2 (normally H2 \-* (Q' \--* Q)) Q'.
    { applys~ triple_conseq M. xsimpl. }
    { clear M. applys triple_conseq (rm K).
      { xsimpl. }
      { intros x. xchange (>> normally_erase (normally H2 \-* (Q' \--* Q))). } } }
Qed.

Lemma triple_ramified_frame_read_only : forall t H Q H' Q',
  triple t H' Q' ->
  H ==> ROFrame H' (normally (Q' \--* Q)) ->
  triple t H Q.
Proof using.
  introv M W. applys~ triple_conseq Q (rm W).
  applys triple_hexists. intros H2.
  asserts M': (triple t H' Q').
  { applys* triple_conseq H'. }
  clear M. applys* triple_ramified_frame_read_only_core.
Qed.

Lemma triple_let_ramified_frame_read_only : forall z t1 t2 H1 H Q1 Q Q',
  triple t1 H1 Q1 ->
  H ==> ROFrame H1 (Q1 \--* Q') ->
  (forall (X:val), triple (subst1 z X t2) (Q' X) Q) ->
  triple (trm_let z t1 t2) H Q.
Proof.
  intros x t1 t2 H1 H Q1 Q Q' Ht1 IMPL Ht2L.
  eapply triple_conseq; [apply IMPL| |auto].
  apply triple_hexists. intros H2. rewrite <-hstar_assoc.
  eapply triple_let.
  - rewrite hstar_comm. apply triple_frame_read_only, _.
    eapply triple_conseq; [|apply Ht1|auto].
    applys himpl_trans (hwand_cancel (RO H2) H1). xsimpl.
    apply RO_covariant, normally_erase.
  - intros X. eapply triple_conseq; [|apply Ht2L|auto].
    xchange (>> normally_erase H2).
Qed.




*)

