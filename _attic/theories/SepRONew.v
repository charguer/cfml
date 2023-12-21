(**

This file formalizes "Separation Logic with Temporary
Read-Only Permissions", as described in the ESOP'17
paper by Arthur Charguéraud and François Pottier.

This file contains:
- a definition of heaps as pairs of states,
- an instantiation of the functor from the file LibSepFunctor.v,
- a definition of triples,
- statement and proofs of SL reasoning rules.

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
Generalizable Variable A.


(* ********************************************************************** *)
(* * Core of the logic *)

Module Export SepROCore <: SepCore.


(* ---------------------------------------------------------------------- *)
(** Heaps *)

Declare Scope heap_scope.
Open Scope heap_scope.

(** Representation of heaps as pairs *)

Definition heap : Type :=
  { h : (state*state)%type | let '(f,r) := h in Fmap.disjoint f r }.

(* Projections *)

Program Definition proj_rw (h:heap) : heap :=
  match h with (f,r) => (f,Fmap.empty) end.

Program Definition proj_ro (h:heap) : heap :=
  match h with (f,r) => (Fmap.empty,r) end.

Notation "h '^rw'" := (proj_rw h)
   (at level 9, format "h '^rw'") : heap_scope.

Notation "h '^ro'" := (proj_ro h)
   (at level 9, format "h '^ro'") : heap_scope.

(** State associated with a heap *)

Program Definition heap_state (h : heap) : state :=
  match h with (f,r) => f \+ r end.

(** Conversion to read-only:
   [toro h] defines the read-only heap associated with [h],
    i.e. covering the same memory cells, but with all tagged
    as read-only. *)

Program Definition toro (h:heap) : heap :=
  match h with (f,r) => (Fmap.empty, f \+ r) end.

(** Empty *)

Program Definition heap_empty : heap :=
  (Fmap.empty, Fmap.empty).

(** Single *)

Program Definition heap_single (p:loc) (v:val) : heap :=
  (Fmap.single p v, Fmap.empty).

(** Inhabited heaps *)

Global Instance heap_inhab : Inhab heap.
Proof using. applys Inhab_of_val heap_empty. Qed.

(** Starable heaps: disjoint owned heaps, agreeible read-only heaps *)

Program Definition heap_compat (h1 h2 : heap) : Prop :=
  match h1 with (f1,r1) =>
  match h2 with (f2,r2) =>
       Fmap.agree r1 r2
    /\ (\# f1 f2 (r1 \+ r2))
  end end.

(** Union of heaps.
    The operation [h1 \u h2] is partial. When the arguments are
    not compatible, it returns an unspecified result.
    We implement it using a classical logic test, so as to avoid
    dependently-typed programming. *)

Lemma heap_union_correct :  forall (f1 f2 r1 r2:state),
   \# f1 f2 (r1 \+ r2) ->
   \# (f1 \+ f2) (r1 \+ r2).
Proof using. intros. fmap_disjoint. Qed.

Program Definition heap_union (h1 h2 : heap) : heap :=
  If heap_compat h1 h2 then
    match h1 with (f1,r1) =>
    match h2 with (f2,r2) =>
      ((f1 \+ f2), (r1 \+ r2))
    end end
  else arbitrary.
Next Obligation.
  destruct h1 as ((f1',r1'),D1). inverts Heq_h1.
  destruct h2 as ((f2',r2'),D2). inverts Heq_h2.
  match goal with H: heap_compat _ _ |- _ => destruct H as (H1&H2) end.
  applys* heap_union_correct.
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
  h^ro = heap_empty.

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

Ltac disjoint_solve tt :=
  rew_disjoint; jauto_set; solve
  [ assumption
  | apply disjoint_sym; assumption
  | apply disjoint_empty_l
  | apply disjoint_empty_r ].

Hint Extern 1 (disjoint _ _) => disjoint_solve tt.
Hint Extern 1 (disjoint_3 _ _ _) => disjoint_solve tt.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [union] *)

Lemma heap_union_eq_of_compat : forall h1 h2 f1 f2 r1 r2 D1 D2,
  heap_compat h1 h2 ->
  h1 = exist (f1,r1) D1 ->
  h2 = exist (f2,r2) D2 ->
  exists Du,
  h1 \u h2 = exist (f1 \+ f2, r1 \+ r2) Du.
Proof using.
  introv C -> ->. lets (Ca&Cb): C. unfold heap_union.
  case_classic. simple*.
Qed.

(* not needed *)
Lemma heap_union_exists_eq_of_compat : forall f1 f2 r1 r2 D1 D2
  (C:heap_compat (exist (f1,r1) D1) (exist (f2,r2) D2)),
  (exist (f1,r1) D1) \u (exist (f2,r2) D2) = exist (f1 \+ f2, r1 \+ r2)
   ((heap_union_obligation_1 (exist (f1, r1) D1) (exist (f2, r2) D2) C eq_refl eq_refl)).
Proof using.
  intros. forwards* (Du'&->): heap_union_eq_of_compat C. fequals.
Qed.



(* ---------------------------------------------------------------------- *)
(* ** Properties of [proj] *)

(** Two heaps are equal iff their projections are equal. *)

Lemma heap_eq_projs : forall h1 h2,
  h1^rw = h2^rw ->
  h1^ro = h2^ro ->
  h1 = h2.
Proof using.
  intros ((f1,r1),D1) ((f2,r2),D2) E1 E2. inverts E1. inverts E2. fequals.
Qed.

(** The two projections are disjoint, hence compatible. *)

Lemma heap_compat_projs : forall h,
  heap_compat (h^rw) (h^ro).
Proof using.
  hint agree_empty_l.
  intros ((f,r),D). split; simple*.
Qed.

(** Projections *)

Ltac proj_prove :=
  intros; unfold proj_rw, proj_ro; simpl; fequals.

Lemma proj_rw_empty :
  heap_empty^rw = heap_empty.
Proof using. unfold heap_empty. proj_prove. Qed.

Lemma proj_ro_empty :
  heap_empty^ro = heap_empty.
Proof using. unfold heap_empty. proj_prove. Qed.

Hint Rewrite proj_rw_empty proj_ro_empty : rew_heaps.

Lemma proj_rw_single : forall p v,
  (heap_single p v)^rw = (heap_single p v).
Proof using. unfold single. proj_prove. Qed.

Lemma proj_ro_single : forall p v,
  (heap_single p v)^ro = heap_empty.
Proof using. unfold single. proj_prove. Qed.

Hint Rewrite proj_rw_single proj_ro_single : rew_heaps.

Lemma proj_rw_idempotent : forall h,
  (h^rw)^rw = h^rw.
Proof using. intros ((f,r),D). proj_prove. Qed.

Lemma proj_ro_idempotent : forall h,
  (h^ro)^ro = h^ro.
Proof using. intros ((f,r),D). proj_prove. Qed.

Hint Rewrite proj_rw_idempotent proj_ro_idempotent : rew_fmap rew_heaps.

Lemma proj_ro_proj_rw : forall h,
  (h^rw)^ro = heap_empty.
Proof using. intros ((f,r),D). proj_prove. Qed.

Lemma proj_rw_proj_ro : forall h,
  (h^ro)^rw = heap_empty.
Proof using. intros ((f,r),D). proj_prove. Qed.

Hint Rewrite proj_ro_proj_rw proj_rw_proj_ro : rew_fmap rew_heaps.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [heap_compat] *)

Lemma heap_compat_sym : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat h2 h1.
Proof using.
  hint agree_sym.
  intros ((f1,r1),D1) ((f2,r2),D2) (Ca&Cb). split*.
Qed.

Lemma heap_compat_refl_if_ro : forall h,
  h^rw = heap_empty ->
  heap_compat h h.
Proof using.
  hint Fmap.agree_refl.
  intros ((f,r),D) E. unfolds proj_rw. simpls. inverts E. split*.
Qed.

Lemma heap_compat_empty_l : forall h,
  heap_compat heap_empty h.
Proof using.
  hint agree_empty_l.
  intros ((f,r),D). split*.
Qed.

Lemma heap_compat_empty_r : forall h,
  heap_compat h heap_empty.
Proof using. autos* heap_compat_sym heap_compat_empty_l. Qed.

Hint Resolve heap_compat_empty_l heap_compat_empty_r.

Lemma heap_compat_union_l : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h1 h3 ->
  heap_compat h2 h3 ->
  heap_compat (h1 \u h2) h3.
Proof using.
  hint agree_union_l.
  intros ((f1,r1),D1) ((f2,r2),D2) ((f3,r3),D3) C1 (C2a&C2b) (C3a&C3b).
  forwards* (Du&->): heap_union_eq_of_compat C1. split*.
Qed.

Lemma heap_compat_union_r : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h1 h3 ->
  heap_compat h2 h3 ->
  heap_compat h1 (h2 \u h3).
Proof using. hint heap_compat_sym, heap_compat_union_l. autos*. Qed.

Lemma heap_compat_fresh_single : forall h v,
  exists p, p <> null /\ heap_compat (heap_single p v) h.
Proof using.
  hint agree_empty_l.
  intros. forwards~ (p&D&N): (Fmap.single_fresh null (heap_state h) v).
  exists p. splits~.
  { destruct h as ((f,r)&D'). unfolds heap_compat, heap_state; simpls*. }
Qed.

Lemma heap_compat_single_l : forall v p h,
  disjoint (single p v) (heap_state h) ->
  heap_compat (heap_single p v) h.
Proof using.
  hint agree_empty_l. introv M. destruct h as ((f,r)&D).
  unfolds heap_state; simpls. split; [auto|]. rew_fmap. splits*.
Qed.

Lemma heap_compat_single_l_inv : forall v p h,
  heap_compat (heap_single p v) h ->
  disjoint (single p v) (heap_state h).
Proof using.
  introv C. destruct h as ((f,r)&D).
  unfolds heap_compat, heap_state; simpls*.
Qed.



(* ---------------------------------------------------------------------- *)
(* ** Properties of [heap_compat] on [proj] *)

Lemma heap_compat_proj_ro_r : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat h1 (h2^ro).
Proof using.
  hint agree_empty_r.
  intros ((f1,r1),D1) ((f2,r2),D2) (Ca&Cb). split*.
Qed.

Lemma heap_compat_proj_ro_l : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat (h1^ro) h2.
Proof using.
  introv D. autos* heap_compat_proj_ro_r heap_compat_sym.
Qed.

Arguments heap_compat_proj_ro_r [h1] [h2].
Arguments heap_compat_proj_ro_l [h1] [h2].

Hint Resolve heap_compat_proj_ro_r heap_compat_proj_ro_l.

Lemma heap_compat_proj_rw_r : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat h1 (proj_rw h2).
Proof using.
  hint agree_empty_r.
  intros ((f1,r1),D1) ((f2,r2),D2) (Ca&Cb). split*.
Qed.

Lemma heap_compat_proj_rw_l : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat (proj_rw h1) (h2).
Proof using.
  introv D. autos* heap_compat_proj_rw_r heap_compat_sym.
Qed.

Arguments heap_compat_proj_rw_r [h1] [h2].
Arguments heap_compat_proj_rw_l [h1] [h2].

Hint Resolve heap_compat_proj_rw_r heap_compat_proj_rw_l.

Lemma proj_rw_union : forall h1 h2,
  heap_compat h1 h2 ->
  (h1 \u h2)^rw = (h1^rw) \u (h2^rw).
Proof using.
  intros ((f1,r1),D1) ((f2,r2),D2) C.
  forwards* (Da&->): heap_union_eq_of_compat C.
  lets C': heap_compat_proj_rw_r (heap_compat_proj_rw_l C).
  unfolds proj_rw. simpls.
  forwards* (Db&->): heap_union_eq_of_compat C'.
  fequal_support_for_exist tt.
  fequals. fequals. rew_fmap*.
Qed.

Lemma proj_ro_union : forall h1 h2,
  heap_compat h1 h2 ->
  (h1 \u h2)^ro = (h1^ro) \u (h2^ro).
Proof using.
  intros ((f1,r1),D1) ((f2,r2),D2) C.
  forwards* (Da&->): heap_union_eq_of_compat C.
  lets C': heap_compat_proj_ro_r (heap_compat_proj_ro_l C).
  unfolds proj_ro. simpls.
  forwards* (Db&->): heap_union_eq_of_compat C'.
  fequals. fequals. rew_fmap*.
Qed.

Hint Rewrite proj_rw_union proj_ro_union : rew_heaps.


(* ---------------------------------------------------------------------- *)
(* ** More properties of [heap_union] *)

Lemma heap_union_comm : forall h1 h2,
  heap_compat h1 h2 ->
  h1 \u h2 = h2 \u h1.
Proof using.
  intros ((f1,r1),D1) ((f2,r2),D2) C.
  lets C': heap_compat_sym C.
  forwards* (G1&->): heap_union_eq_of_compat C.
  forwards* (G2&->): heap_union_eq_of_compat C'.
  fequals. destruct C. fequals.
  { applys* Fmap.union_comm_of_disjoint. }
  { applys* Fmap.union_comm_of_agree. }
Qed.

Lemma heap_union_assoc : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h2 h3 ->
  heap_compat h1 h3 ->
  (h1 \u h2) \u h3 = h1 \u (h2 \u h3).
Proof using.
  introv C1 C2 C3.
  forwards* C4: heap_compat_union_l h1 h2 h3.
  forwards* C5: heap_compat_union_r h1 h2 h3.
  destruct h1 as ((f1,r1),D1).
  destruct h2 as ((f2,r2),D2).
  destruct h3 as ((f3,r3),D3).
  forwards* (G1&E1): heap_union_eq_of_compat C1. rewrite E1 in *.
  forwards* (G2&E2): heap_union_eq_of_compat C2. rewrite E2 in *.
  forwards* (G3&->): heap_union_eq_of_compat C4.
  forwards* (G4&->): heap_union_eq_of_compat C5.
  fequals. fequals; fmap_eq.
Qed.

Lemma heap_union_empty_l : forall h,
  heap_empty \u h = h.
Proof using.
  intros h. lets C: (heap_compat_empty_l h).
  destruct h as ((f,r),D).
  forwards* (G&->): heap_union_eq_of_compat C.
  fequals. fequals; fmap_eq.
Qed.

Lemma heap_union_empty_r : forall h,
  h \u heap_empty = h.
Proof using.
  intros. rewrite* heap_union_comm. apply* heap_union_empty_l.
Qed.

Hint Rewrite heap_union_empty_l heap_union_empty_r: rew_heaps.


(* ---------------------------------------------------------------------- *)

(** Decomposition as union of its two projections. *)

Lemma heap_components : forall h,
  heap_compat (h^rw) (h^ro) /\ h = (h^rw) \u (h^ro).
Proof using.
  intros. lets C: heap_compat_projs h. split*.
  { applys heap_eq_projs; rew_heaps*. }
Qed.

Lemma heap_eq_union_projs : forall h,
  h = (h^rw) \u (h^ro).
Proof using.
  intros. lets C: heap_compat_projs h.
  intros. applys heap_eq_projs; rew_heaps*.
Qed.

Lemma heap_eq_union_same_if_ro : forall h,
  h^rw = heap_empty ->
  h = (h \u h).
Proof using.
  introv E. forwards C: heap_compat_refl_if_ro E.
  destruct h as ((f,r),D). inverts E.
  forwards* (G1&->): heap_union_eq_of_compat C.
  fequals. fequals. { rew_fmap*. } { rewrite* union_self. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Auxiliary function [toro] *)

Lemma proj_rw_toro : forall h,
  (toro h)^rw = heap_empty.
Proof using. intros ((f,r)&D). auto. Qed.

Lemma proj_ro_toro : forall h,
  (toro h)^ro = (toro h).
Proof using. intros ((f,r)&D). auto. Qed.

Hint Rewrite proj_rw_toro proj_ro_toro : rew_heaps.

Lemma heap_compat_toro_l : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat (toro h1) h2.
Proof using.
  intros ((f1,r1)&D1) ((f2,r2),D2) (Ca&Cb). split.
  { applys~ Fmap.agree_union_l. applys~ Fmap.agree_of_disjoint. }
  { auto. }
Qed.

Lemma heap_compat_toro_r : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat h1 (toro h2).
Proof using.
  hint heap_compat_toro_l, heap_compat_sym. autos*.
Qed.

Lemma heap_compat_toro : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat (toro h1) (toro h2).
Proof using.
  introv M. applys heap_compat_toro_l. applys* heap_compat_toro_r.
Qed.

Lemma heap_compat_toro_r_inv : forall h1 h2,
  heap_compat h1 (toro h2) ->
  h1^ro = heap_empty ->
  heap_compat h1 h2.
Proof using.
  hint agree_of_disjoint.
  intros ((f1,r1)&D1) ((f2,r2),D2) (Ca&Cb) E. inverts E.
  forwards* (G1&G2): Fmap.agree_union_r_inv Ca. split*.
Qed.

Lemma toro_if_ro : forall h,
  h^rw = heap_empty ->
  toro h = h.
Proof using.
  intros ((f,r),D) E. unfolds proj_rw. simpls. inverts E.
  unfolds toro; simpl. fequals. fequals. rew_fmap*.
Qed.

Lemma toro_idempotent : forall h,
  toro (toro h) = toro h.
Proof using.
  intros ((f,r),D). unfold toro; simpl. fequals. rew_fmap*.
Qed.

Lemma toro_empty :
  toro heap_empty = heap_empty.
Proof using.
  unfold heap_empty, toro; simpl. fequals. rew_fmap*.
Qed.

Lemma toro_union : forall h1 h2,
  heap_compat h1 h2 ->
  toro (h1 \u h2) = (toro h1) \u (toro h2).
Proof using.
  intros ((f1,r1)&D1) ((f2,r2),D2) C. lets (Ca&Cb): C.
  lets C': heap_compat_toro C.
  forwards* (G1&->): heap_union_eq_of_compat C.
  forwards* (G2&->): heap_union_eq_of_compat C'.
  unfold toro; simpl. fequals. fequals; fmap_eq.
Qed.

Hint Rewrite toro_empty toro_union toro_idempotent : rew_heaps.

Lemma toro_eq_union_same : forall h,
  toro h = (toro h) \u (toro h).
Proof using.
  intros h.
  forwards C: heap_compat_refl_if_ro (toro h). { rew_heaps*. }
  destruct h as ((f,r),D).
  forwards* (G1&->): heap_union_eq_of_compat C.
  unfold toro; simpl. fequals. fequals. rew_fmap*.
  rewrite* union_self.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [heap_state] *)

Lemma heap_state_empty :
  heap_state heap_empty = Fmap.empty.
Proof.
  unfold heap_empty, heap_state. simpl. rew_fmap*.
Qed.

Lemma heap_state_single : forall p v,
  heap_state (heap_single p v) = (Fmap.single p v).
Proof.
  intros. unfold heap_single, heap_state; simpl. rew_fmap*.
Qed.

Lemma heap_state_union : forall h1 h2,
  heap_compat h1 h2 ->
  heap_state (h1 \u h2) = heap_state h1 \+ heap_state h2.
Proof using.
  intros ((f1,r1),D1) ((f2,r2),D2) C.
  forwards* (G1&->): heap_union_eq_of_compat C.
  unfold heap_state; simpl. fmap_eq.
Qed.

Lemma heap_state_toro : forall h,
  heap_state (toro h) = heap_state h.
Proof using.
  intros ((f,r)&D). unfold heap_state, toro. simpl. rew_fmap*.
Qed.

Hint Rewrite heap_state_empty heap_state_single heap_state_union heap_state_toro : rew_fmap.


(* ---------------------------------------------------------------------- *)
(* ** More properties of [heap_compat] *)

Lemma heap_compat_union_l_inv_l : forall h1 h2 h3,
  heap_compat (h1 \u h2) h3 ->
  heap_compat h1 h2 ->
  heap_compat h2 h3.
Proof using.
  intros ((f1,r1),D1) ((f2,r2),D2) ((f3,r3),D3) C' C.
  forwards* (G1&E): heap_union_eq_of_compat C. rewrite E in *.
  clear E. destruct C as (Ca&Cb). destruct C' as (C'a&C'b).
  forwards~ (N1&N2): Fmap.agree_union_l_inv C'a. split*.
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
  autos* heap_compat_union_l_inv_l heap_compat_union_l_inv_r.
Qed.

Lemma heap_compat_union_r_inv : forall h1 h2 h3,
  heap_compat h1 (h2 \u h3) ->
  heap_compat h2 h3 ->
  heap_compat h1 h2 /\ heap_compat h1 h3.
Proof using.
  hint heap_compat_sym.
  introv M1 M2. rewrite* heap_union_comm in M1.
  lets M1': heap_compat_sym M1.
  forwards~ (N1&N2): heap_compat_union_l_inv M1'.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of hempty *)

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
  { rewrite (hempty_inv M1). rew_heaps*. }
  { exists~ heap_empty h. }
Qed.

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof using.
  hint heap_union_comm, heap_compat_sym.
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
  fun h =>    h = heap_single l v
           /\ l <> null.

Notation "l '~~~>' v" := (hsingle l v)
  (at level 32, no associativity) : heap_scope.

Notation "l '~~>' v" := (hsingle l v)
  (at level 32, no associativity) : heap_scope.
(* TODO: choose *)

Lemma hsingle_intro : forall l v,
  l <> null ->
  (l ~~> v) (heap_single l v).
Proof using. intros. split~. Qed.

Lemma hsingle_inv : forall h l v,
  (l ~~~> v) h ->
  h = heap_single l v /\ (l <> null).
Proof using. auto. Qed.

Lemma hstar_hsingle_same_loc : forall (l:loc) (v1 v2:val),
  (l ~~~> v1) \* (l ~~~> v2) ==> \[False].
Proof using.
  intros. intros h (h1&h2&(E1&N1)&(E2&N2)&C&E). subst. false.
  unfolds heap_single, heap_compat; simpls.
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

Lemma onlyrw_proj_ro : forall h H,
  onlyrw H ->
  H h ->
  h^ro = heap_empty.
Proof using. introv N K. applys* N. Qed.

Lemma onlyrw_proj_rw : forall h H,
  onlyrw H ->
  H h ->
  h^rw = h.
Proof using.
  introv N K. rewrite (heap_eq_union_projs h) at 2.
  rewrite* N. rew_heaps*.
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
  introv M. unfolds hempty, hpure. subst. rew_heaps*.
Qed.

Lemma onlyrw_hpure : forall P,
  onlyrw \[P].
Proof using.
  Transparent hpure.
  introv (p&M). unfolds hempty. subst. rew_heaps*.
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
Proof using. introv (->&N). rew_heaps. autos*. Qed.

Lemma onlyrw_hstar : forall H1 H2,
  onlyrw H1 ->
  onlyrw H2 ->
  onlyrw (H1 \* H2).
Proof using.
  introv N1 N2 (h1&h2&P1&P2&M1&->). rew_heaps*.
  rewrites (>> N1 P1). rewrites (>> N2 P2). rew_heaps*.
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
  introv N (h1&h2&P1&P2&M1&->). rew_heaps*.
  lets (MP&ME): hpure_inv P1. rewrites (rm ME).
  rewrites~ (>> N P2). rew_heaps*.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** onlyro *)

Definition onlyro (H:hprop) : Prop :=
  forall h, H h -> h^rw = heap_empty.

Definition onlyro_post A (Q:A->hprop) : Prop :=
  forall x, onlyro (Q x).

Lemma onlyro_proj_ro : forall h H,
  onlyro H ->
  H h ->
  h^ro = h.
Proof using.
  introv N K. rewrite (heap_eq_union_projs h) at 2.
  rewrite* N. rew_heaps*.
Qed.

Lemma onlyro_proj_rw : forall h H,
  onlyro H ->
  H h ->
  h^rw = heap_empty.
Proof using. introv N K. applys* N. Qed.

Lemma onlyro_hempty :
  onlyro hempty.
Proof using.
  introv M. unfolds hempty, hpure. subst. rew_heaps*.
Qed.

Lemma onlyro_hstar : forall H1 H2,
  onlyro H1 ->
  onlyro H2 ->
  onlyro (H1 \* H2).
Proof using.
  introv N1 N2 (h1&h2&P1&P2&M1&EQ). subst. rew_heaps*.
  rewrite* N1. rewrite* N2. rew_heaps*.
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

Lemma onlyro_duplicatable : forall H,
  onlyro H ->
  duplicatable H.
Proof using.
  intros H N h M. specializes N M.
  applys_eq* (>> hstar_intro h h).
  { applys* heap_eq_union_same_if_ro. }
  { applys* heap_compat_refl_if_ro. }
Qed.



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

Lemma RO_heap_empty : forall (H:hprop),
  H heap_empty ->
  RO H heap_empty.
Proof using. introv N. exists heap_empty. rew_heaps*. Qed.

Hint Resolve toro_pred RO_heap_empty.

Lemma RO_covariant : forall H1 H2,
  H1 ==> H2 ->
  (RO H1) ==> (RO H2).
Proof using.
  introv M. intros h (h'&M1&->). auto.
Qed.

Lemma RO_hempty :
  RO \[] = \[].
Proof using.
  intros. apply pred_ext_1. intros h.
  unfold hempty. iff (h'&->&->) ->; rew_heaps*.
Qed.

Lemma RO_pure : forall P,
  RO \[P] = \[P].
Proof using.
  hint hpure_intro.
  intros. apply pred_ext_1. intros h.
  iff (h'&(M1p&M2)&->) (MP&M1).
  { lets ->: hempty_inv M2. rew_heaps*. }
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
  exists (toro h1) (toro h2). rew_heaps*.
Qed.

Arguments RO_hstar : clear implicits.

Lemma onlyro_RO : forall H,
  onlyro (RO H).
Proof using.
  introv (h'&K&E). subst. rew_heaps*.
Qed.

Lemma RO_duplicatable : forall H,
  duplicatable (RO H).
Proof using.
  intros. applys onlyro_duplicatable. applys onlyro_RO.
Qed.

Lemma RO_onlyro : forall H,
  onlyro H ->
  RO H = H.
Proof using.
  introv M. extens. intros h. unfold RO. iff (h'&N&->) R.
  { rewrite* toro_if_ro. }
  { exists h. rewrite* toro_if_ro. }
Qed.

Lemma RO_RO : forall H,
  RO (RO H) = RO H.
Proof using.
  intros. rewrite* RO_onlyro. { applys onlyro_RO. }
Qed.

End RO.



(* ********************************************************************** *)
(* * Elimination lemmas useful to simplify proofs *)

(* TODO: rename *)

Lemma onlyrw_rw_elim : forall H h,
  onlyrw H ->
  H h ->
  H (h^rw).
Proof using.
  introv NF K. lets K': K.
  rewrite (heap_eq_union_projs h) in K.
  rewrites* (>> onlyrw_proj_ro NF) in K. rew_heaps* in K.
Qed.

Lemma onlyrw_onlyro_rw_elim : forall HF HR h,
  onlyrw HF ->
  onlyro HR ->
  (HF \* HR) h ->
  HF (h^rw).
Proof using.
  introv NF NR (h1&h2&K1&K2&D&->). rew_heaps*.
  rewrites* (>> onlyro_proj_rw K2). rew_heaps.
  rewrites* (>> onlyrw_proj_rw K1).
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

Lemma isframe_isframe : forall HI1 HO1 HI2 HO2,
  isframe HI1 HO1 ->
  isframe HI2 HO2 ->
  isframe (HI1 \* HI2) (HO1 \* HO2).
Proof using.
  introv (HR1&NF1&NR1&E1) (HR2&NF2&NR2&E2).
  exists (HR1 \* HR2). splits.
  { auto with onlyrw. }
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
(* ** Definition of Hoare triples in a logic with read-only predicates *)

Definition hoare (t:trm) (H:hprop) (Q:val->hprop) :=
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

Lemma hoare_frame_read_only : forall t H1 Q1 HI HO,
  hoare t (H1 \* RO HI) Q1 ->
  isframe HI HO ->
  hoare t (H1 \* HI) (Q1 \*+ HO).
Proof using.
  hint heap_compat_union_l, heap_compat_union_r, heap_compat_toro_r.
  introv M N. intros ? (h1&h2&P1&P2&C1&->).
  forwards (h'&v&R&L&S): M (h1 \u toro h2).
  { applys* hstar_intro h1 (toro h2). { applys* toro_pred. } }
  lets (D'&E'): heap_components h'.
  lets C1': heap_compat_toro_r C1.
  rewrites S in *. rew_heaps* in *.
  forwards* (D1'&D2'): heap_compat_union_r_inv (rm D').
  forwards D2'': heap_compat_toro_r_inv D2'. { rew_heaps*. }
  exists ((h'^rw) \u (h1^ro) \u h2) v. splits.
  { applys_eq R.
     { rew_fmap*. }
     { rewrites (rm E'). rew_heaps*. rew_fmap*. } }
  { rew_heaps*. applys* hstar_intro. { applys* isframe_rw_elim. } }
  { rew_heaps*. }
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
  lets ->: hempty_inv M1. rew_heaps*.
Qed.


(* ********************************************************************** *)
(** * Hoare rules for term constructs *)

Implicit Types v : val.
Implicit Types p : loc.

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
  hint heap_compat_union_l, heap_compat_union_r.
  hint heap_compat_toro_l, heap_compat_toro_r.
  hint heap_compat_proj_ro_l, heap_compat_proj_ro_r.
  introv HF M1 M2. intros h K.
  destruct K as (h2&hr&P1&P2&D1&U1).
  destruct P2 as (hI&h1&PI&PO&D2&U2).
  rewrite U2 in D1. lets (D3&D4): heap_compat_union_r_inv D1 D2.
  forwards (h1'&v1&R1&K1&E1): (rm M1) (toro h2 \u hI \u h1).
  { applys* hstar_intro.
    { applys* toro_pred. }
    { applys* hstar_intro. } }
  (* Adding compatibility facts *)
  lets (Da&Ea): heap_components h1'.
  rewrite E1 in Da. rew_heaps* in Da.
  forwards* (C3&C4): heap_compat_union_r_inv Da.
  forwards* (C5&C6): heap_compat_union_r_inv C4.
  forwards C7: heap_compat_toro_r_inv C3. { rew_heaps*. }
  (* Remaining of the proof *)
  forwards (h2'&v2&R2&K2&E2): (rm M2) v1 (= hI^ro \u h1^ro) (h1'^rw \u h2 \u hI^ro \u h1^ro).
  { intros ? ->. rew_heaps*. }
  { rewrite <- hstar_assoc. applys* hstar_intro.
    { applys* hstar_intro. } }
  exists h2' v2. splits*.
  { applys eval_let_trm (heap_state h1').
    { applys_eq R1. subst h hr. rew_fmap*. }
    { applys_eq R2.
      rewrite Ea at 1. rewrite E1. rew_heaps*. rew_fmap*. } }
  { rewrite E2. rewrite U1,U2. rew_heaps*. }
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
  introv NF. intros hI KI.
  forwards (p&N&C): heap_compat_fresh_single hI v.
  lets D: heap_compat_single_l_inv C.
  exists ((heap_single p v) \u hI) (val_loc p). splits.
  { rew_fmap*. applys~ eval_ref_sep. }
  { rew_heaps*. applys~ hstar_intro.
    { exists p. rewrite~ hstar_hpure_l. split~. applys* hsingle_intro. }
    { applys* isframe_rw_elim. } }
  { rew_heaps*. }
Qed.

Lemma hoare_get_ro : forall HI HO v p,
  isframe HI HO ->
  hoare (val_get p)
    (RO (p ~~> v) \* HI)
    (fun r => \[r = v] \* HO).
Proof using.
  introv NH. intros h (h1&h2&K1&K2&D&E).
  destruct K1 as (h'&K'&E1). lets (->&N): hsingle_inv K'.
  exists h v. splits.
  { applys* eval_get_sep (heap_state h1) (heap_state h2);
    subst; rew_fmap*. }
  { rewrite~ hstar_hpure_l. split~. subst h h1. rew_heaps*.
    applys* isframe_rw_elim. }
  { auto. }
Qed.

Lemma hoare_set : forall HI HO w p v,
  isframe HI HO ->
  hoare (val_set (val_loc p) v)
    ((p ~~> w) \* HI)
    (fun r => \[r = val_unit] \* (p ~~> v) \* HO).
Proof using.
  introv NH. intros h K0.
  destruct K0 as (h1&h2&P1&P2&C&->). lets (->&N): hsingle_inv P1.
  lets D: heap_compat_single_l_inv C.
  lets D': disjoint_single_set v D.
  lets C': heap_compat_single_l D'.
  exists ((heap_single p v) \u h2) val_unit. splits.
  { applys* eval_set_sep (single p w) (single p v) (heap_state h2);
    subst; rew_fmap*. }
  { rewrite hstar_hpure_l. split~.
    { rew_heaps*. applys* hstar_intro.
      { applys* hsingle_intro. } { applys* isframe_rw_elim. } } }
  { rew_heaps*. }
Qed.

Lemma hoare_free : forall HI HO p v,
  isframe HI HO ->
  hoare (val_free (val_loc p))
    ((p ~~> v) \* HI)
    (fun r => \[r = val_unit] \* HO).
Proof using.
  introv NH. intros h K0.
  destruct K0 as (h1&h2&P1&P2&C&->). lets (->&N): hsingle_inv P1.
  lets D: heap_compat_single_l_inv C.
  exists h2 val_unit. splits.
  { applys* eval_free_sep; subst; rew_fmap*. }
  { rewrite hstar_hpure_l. split~. applys* isframe_rw_elim. }
  { rew_heaps*. }
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

(** The basic frame rule, which does not introduces read-only permissions,
   is inherent to the definition of triple. *)

Lemma triple_frame : forall HI HO t H1 Q1,
  triple t H1 Q1 ->
  isframe HI HO ->
  triple t (H1 \* HI) (Q1 \*+ HO).
Proof using.
  introv M F. intros HI' HO' F'.
  lets F'': isframe_isframe F F'.
  applys hoare_conseq. { applys M F''. } { xsimpl. } { xsimpl. }
Qed.

(** Corollary: read-only permissions may be freely discarded. *)

Lemma triple_onlyro : forall t H1 Q1 H2,
  triple t H1 Q1 ->
  onlyro H2 ->
  triple t (H1 \* H2) Q1.
Proof using.
  introv M N. forwards* F: (>> isframe_onlyro H2 isframe_hempty).
  applys triple_conseq.
  { applys* triple_frame M F. }
  { xsimpl*. }
  { xsimpl*. }
Qed.

Lemma triple_hro_pre : forall t H H' Q,
  triple t H Q ->
  triple t (H \* RO H') Q.
Proof using.
  introv M. applys* triple_onlyro. applys onlyro_RO.
Qed.

(** Corollary: the read-write permissions may be framed. *)

Lemma triple_frame_onlyrw : forall t H1 Q1 H2,
  triple t H1 Q1 ->
  onlyrw H2 ->
  triple t (H1 \* H2) (Q1 \*+ H2).
Proof using.
  introv M N. forwards* F: (>> isframe_onlyrw H2 isframe_hempty).
  applys triple_conseq.
  { applys* triple_frame M F. }
  { xsimpl*. }
  { xsimpl*. }
Qed.

(** Corollary: the classic conseq-frame rule. *)

Lemma triple_conseq_frame_onlyrw : forall H Q t H1 Q1 H2,
  triple t H1 Q1 ->
  H ==> (H1 \* H2) ->
  (Q1 \*+ H2) ===> Q ->
  onlyrw H2 ->
  triple t H Q.
Proof using.
  introv M WH WQ N. applys triple_conseq WH WQ.
  applys* triple_frame_onlyrw.
Qed.

(** The read-only frame rule is derived from its counterpart
    on Hoare triples. *)

Lemma triple_frame_read_only : forall HI HO t H1 Q1,
  triple t (H1 \* RO HI) Q1 ->
  isframe HI HO ->
  triple t (H1 \* HI) (Q1 \*+ HO).
Proof using.
  introv M F. intros HI' HO' F'.
  lets R: M F'. applys hoare_conseq.
  { applys hoare_frame_read_only (H1 \* HI') (Q1 \*+ HO' \*+ \GC) F.
    applys hoare_conseq R. { xsimpl. } { xsimpl. } }
  { xsimpl. } { xsimpl. }
Qed.

(** Corollary: the original statement of the read-only frame rule *)

Lemma triple_frame_read_only_original : forall t H1 Q1 H2,
  triple t (H1 \* RO H2) Q1 ->
  onlyrw H2 ->
  triple t (H1 \* H2) (Q1 \*+ H2).
Proof using.
  introv M N. lets F: isframe_onlyrw isframe_hempty N.
  rew_heap in *. applys* triple_frame_read_only F.
Qed.

(** Discard rules *)

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
(** To facilitate garbage collection in the precondition, we introduce
   [hdiscardable H], which covers the union of [haffine] and [onlyro]. *)

Definition hdiscardable (H:hprop) : Prop :=
  H ==> \exists HN HR, \[haffine HN] \* \[onlyro HR] \* (HN \* HR).

(** Any predicate satisfying [hdiscardable] may be removed.
    Interestingly, [RO H] predicate is discardable, and
    a predicate [H] satisfying [haffine] is also discardable. *)

Lemma triple_hdiscardable : forall t H H' Q,
  triple t H Q ->
  hdiscardable H' ->
  triple t (H \* H') Q.
Proof using.
  introv M N. unfolds in N.  (* xtchange *)
  rewrite hstar_comm. lets WH: himpl_frame_l H (rm N).
  applys triple_conseq (rm WH). rewrite hstar_hexists.
  applys triple_hexists. intros HN. rewrite hstar_hexists.
  applys triple_hexists. intros HR. rewrite hstar_assoc.
  applys triple_hpure. intros NN. rewrite hstar_assoc.
  applys triple_hpure. intros NR. rewrite hstar_assoc.
  rewrite hstar_comm. applys triple_haffine_pre NN.
  rewrite hstar_comm. applys triple_onlyro NR. applys M. auto.
Qed.

Lemma hdiscardable_haffine : forall H,
  haffine H ->
  hdiscardable H.
Proof using.
  introv M. unfolds. xsimpl H \[].
  { auto. }
  { applys onlyro_hempty. }
Qed.

Lemma hdiscardable_RO : forall H,
  hdiscardable (RO H).
Proof using.
  intros. unfolds. xsimpl \[] (RO H).
  { applys haffine_hempty. }
  { applys onlyro_RO. }
Qed.

Lemma hdiscardable_hempty :
  hdiscardable \[].
Proof using.
  unfolds. xsimpl \[] \[].
  { applys haffine_hempty. }
  { applys onlyro_hempty. }
Qed.

Lemma hdiscardable_hstar : forall H1 H2,
  hdiscardable H1 ->
  hdiscardable H2 ->
  hdiscardable (H1 \* H2).
Proof using.
  introv M1 M2. unfolds. xchange M1. intros HN1 HR1 F1 G1.
  xchange M2. intros HN2 HR2 F2 G2. xsimpl (HN1 \* HN2) (HR1 \* HR2).
  { applys* haffine_hstar. }
  { applys* onlyro_hstar. }
Qed.

Lemma hdiscardable_hexists : forall A (J:A->hprop),
  (forall x, hdiscardable (J x)) ->
  hdiscardable (hexists J).
Proof using.
  introv M1. unfolds. xpull. intros x. xchange M1. intros HN1 HR1 F1 G1.
  xsimpl* HN1 HR1.
Qed.

Lemma hdiscardable_hforall : forall A (J:A->hprop) (x:A),
  hdiscardable (J x) ->
  hdiscardable (hforall J).
Proof using.
  introv M1. unfolds hdiscardable. applys himpl_trans. applys hforall_specialize x.
  apply M1.
Qed.

Lemma hdiscardable_hor : forall H1 H2,
  hdiscardable H1 ->
  hdiscardable H2 ->
  hdiscardable (hor H1 H2).
Proof using.
  introv M1 M2. unfolds hdiscardable. unfolds hor. xpull. intros b.
  case_if*.
Qed.

Lemma hdiscardable_hgc :
  hdiscardable \GC.
Proof using.
  intros. unfolds. rewrite hgc_eq. xpull. intros H1 F1.
  xsimpl H1 \[].
  { auto. }
  { applys onlyro_hempty. }
Qed.

Lemma hdiscardable_covariant : forall H1 H2,
  H1 ==> H2 ->
  hdiscardable H2 ->
  hdiscardable H1.
Proof using.
  introv W M. unfolds hdiscardable. applys himpl_trans W M.
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
  intros. intros HI HO HF. rew_heaps.
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
  introv M N. applys triple_conseq_frame_onlyrw N.
  { applys triple_val. }
  { xsimpl. }
  { xchanges M. intros ? ->. xsimpl*. }
Qed.

Lemma triple_fix : forall f x t1,
  triple (trm_fix f x t1) \[] (fun r => \[r = (val_fix f x t1)]).
Proof using.
  intros. intros HI HO HF. rew_heaps.
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
  introv M N. applys triple_conseq_frame_onlyrw N.
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
        forwards* HFb: isframe_onlyro H3 (rm HFa). rew_heaps in HFb.
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
  intros H h K. forwards (D&->): (heap_components h).
  exists (= h^rw) (= h^ro). do 2 rewrite hstar_hpure. splits.
  { intros ? ->. rew_heaps*. }
  { intros ? ->. rew_heaps*. }
  { applys* hstar_intro. }
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



(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(* *

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
  { intros h ((h1&h2&M1&M2&M3&M4)&E). subst h. rew_heaps~ in E.
    exists h1 h2. splits~.
    { split~. applys* Fmap.union_eq_empty_inv_l. }
    { split~. applys* Fmap.union_eq_empty_inv_r. } }
  { intros. intros h (h1&h2&(M1&E1)&(M2&E2)&M3&M4). split.
    { exists~ h1 h2. }
    { subst h. rew_heaps~. rewrite E1,E2. rew_fmap~. } }
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
  rew_heaps~ in N3. rewrite E12 in N3.
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
  { rew_heaps~. rewrite F2,E12. fmap_eq~. }
  {  clears h2.
     rename h1'' into hd. rename H2 into Hb. sets Ha: (Q1 v).
     rename h1' into ha.  rewrite~ Fmap.union_empty_r in N3.
     rename h12 into hb. rename h11 into hc.
     (* LATER: begin separate lemma *)
     destruct N4 as (hx&hy&V1&V2&V3&V4).
     lets G': G. rewrite N3 in G'. rewrite V2 in G'. rew_heaps~ in G'.
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
       { rewrite F1,V2. rew_heaps~. rewrite Y1,W1.
         rewrite Fmap.union_empty_l.
         do 2 rewrite Fmap.union_assoc. fequals.
         applys Fmap.union_comm_of_disjoint. auto. }
       { rew_heaps~. rewrite V3,E12,W2,Y2,F2. fmap_eq. } }
     { rew_heaps~. rewrite V3,E12. fmap_eq. }
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
  rewrite normally_hempty, RO_hempty, hstar_hempty_l.
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
  { xsimpl. xchange (>> RO_hstar H1 HF). }
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

