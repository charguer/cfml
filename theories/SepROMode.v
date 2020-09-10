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





(* ********************************************************************** *)
(* * Core of the logic *)

Module Export SepROCore <: SepCore.

Implicit Types l : loc.
Implicit Types v : val.


(* ---------------------------------------------------------------------- *)
(** Heaps *)

Declare Scope heap_scope.

(** Definition of access modes: read-write or read-only *)

Inductive mode :=
  | mode_rw : mode
  | mode_ro : mode.

Implicit Types m : mode.

(** Representation of heaps as states with locations tagged by a mode *)

Definition heap : Type := fmap loc (val*mode)%type.

(** Affinity is trivial *)

Definition heap_affine (h:heap) := True.

(** Projections of the rw or ro part of a heap *)

Definition heap_rw (h:heap) : heap :=
  Fmap.filter (fun l '(v,m) => m = mode_rw) h.

Definition heap_ro (h:heap) : heap :=
  Fmap.filter (fun l '(v,m) => m = mode_ro) h.

Notation "h '^rw'" := (heap_rw h)
   (at level 9, format "h '^rw'") : heap_scope.

Notation "h '^ro'" := (heap_ro h)
   (at level 9, format "h '^ro'") : heap_scope.

Open Scope heap_scope.

(** [to_ro h] defines the read-only heap associated with [h],
    i.e. covering the same memory cells, but with all tagged
    as read-only. *)

Definition to_ro (h:heap) : heap :=
  Fmap.map_ (fun l '(v,m) => (v,mode_ro)) h.

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
     Fmap.disjoint (h1^rw) (h2^rw)
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

Lemma haffine_any : forall H,
  haffine H.
Proof using. introv M. hnfs*. Qed.

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



(* ---------------------------------------------------------------------- *)
(* ** Equalities on [heap] *)

Lemma heap_eq_union_rw_ro : forall h,
  h = (h^rw) \u (h^ro).
Proof using. skip. Qed.

(** Note: it is always the case that [Fmap.disjoint (h^rw) (h^ro)]. *)

Lemma heap_disjoint_components : forall h,
  \# (h^rw) (h^ro).
Proof using. skip. Qed.

Lemma heap_eq : forall h1 h2,
  (h1^rw = h2^rw /\ h1^ro = h2^ro) ->
  h1 = h2.
Proof using. skip. Qed.

(* TODO: check what's actually needed *)
Lemma heap_eq_forward : forall h1 h2,
  h1 = h2 ->
  h1^rw = h2^rw /\ h1^ro = h2^ro.
Proof using. intros. subst*. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [to_ro] *)

Lemma to_ro_rw : forall h,
  (to_ro h)^rw = Fmap.empty.
Proof using. skip. Qed.

Lemma to_ro_ro : forall h,
  (to_ro h)^ro = (to_ro h).
Proof using. skip. Qed.

Lemma to_ro_state : forall h,
  heap_state (to_ro h) = heap_state h.
Proof using. skip. Qed.
(*Proof using.
  intros h. do 2 rewrite heap_eq_union_rw_ro. rewrite to_ro_f, to_ro_r.
  fmap_eq.
Qed. *)


(* ---------------------------------------------------------------------- *)
(* ** Properties of [heap_union] *)

(*
Lemma heap_union_def : forall h1 h2,
  heap_compat h1 h2 ->
  exists D,
  h1 \u h2 = exist (h1^rw \+ h2^rw, h1^ro \+ h2^ro) D.
Proof using.
  introv M. unfold heap_union.
  rewrite (classicT_l M). esplit. destruct~ M.
Qed.

Lemma heap_union_spec : forall h1 h2,
  heap_compat h1 h2 ->
     (h1 \u h2)^rw = h1^rw \+ h2^rw
  /\ (h1 \u h2)^ro = h1^ro \+ h2^ro.
Proof using.
  introv M. lets (D&E): heap_union_def M. rewrite~ E.
Qed.
*)

Lemma heap_union_f : forall h1 h2,
  heap_compat h1 h2 ->
  (h1 \u h2)^rw = h1^rw \u h2^rw.
Proof using. skip. (*
  introv D. unfold heap_union. rewrite (classicT_l D).
  destruct h1 as ((f1,r1)&D1). destruct h2 as ((f2,r2)&D2).
  unstate. fmap_eq. *)
Qed.

Lemma heap_union_r : forall h1 h2,
  heap_compat h1 h2 ->
  (h1 \u h2)^ro = h1^ro \u h2^ro.
Proof using. skip. (*
  introv D. unfold heap_union. rewrite (classicT_l D).
  destruct h1 as ((f1,r1)&D1). destruct h2 as ((f2,r2)&D2).
  unstate. fmap_eq. *)
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [heap_compat] *)

Lemma heap_compat_def : forall h1 h2,
    heap_compat h1 h2
  = (  Fmap.disjoint (h1^rw) (h2^rw)
    /\ Fmap.agree (h1^ro) (h2^ro)).
Proof using. auto. Qed.

Hint Rewrite heap_compat_def : rew_disjoint.

Lemma heap_compat_sym : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat h2 h1.
Admitted. (*
Proof using. introv (M1&M2). split~. Qed.*)

Hint Resolve heap_compat_sym.

Lemma heap_compat_empty_l : forall h,
  heap_compat heap_empty h.
Admitted. (*
Proof using.
  intros. lets: heap_disjoint_components h.
  unfold heap_empty. split; simpl.
  { apply Fmap.agree_empty_l. }
  { fmap_disjoint. }
Qed.*)

Lemma heap_compat_empty_r : forall h,
  heap_compat h heap_empty.
Admitted.
(*
Proof using.
  hint heap_compat_sym, heap_compat_empty_l. auto.
Qed.*)

Lemma heap_compat_union_l : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h1 h3 ->
  heap_compat h2 h3 ->
  heap_compat (h1 \u h2) h3.
Admitted. (*
Proof using.
  Hint Unfold heap_compat.
  intros ((f1&r1)&S1) ((f2&r2)&S2) ((f3&r3)&S3).
  intros (C1&D1) (C2&D2) (C3&D3). split; simpls.
  { rewrite heap_union_r; [|auto]. simpl. applys~ Fmap.agree_union_l. }
  { rewrite heap_union_r; [|auto]. rewrite heap_union_f; [|auto].
    simpl. fmap_disjoint. }
Qed .*)

Lemma heap_compat_union_r : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h1 h3 ->
  heap_compat h2 h3 ->
  heap_compat h1 (h2 \u h3).
Admitted.
(*
Proof using. hint heap_compat_sym, heap_compat_union_l. autos*.
Qed.*)

Lemma heap_compat_refl_if_ro : forall h,
  h^rw = Fmap.empty ->
  heap_compat h h.

Admitted.
(*
Proof using.
  introv M. split.
  { apply Fmap.agree_refl. }
  { rewrite M. fmap_disjoint. }
Qed.*)

Lemma heap_compat_ro_l : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat (to_ro h1) h2.
Admitted. (*
Proof using.
  introv (N1&N2). split; simpl.
  { applys~ Fmap.agree_union_l. applys~ Fmap.agree_of_disjoint. }
  { fmap_disjoint. }
Qed.*)

Lemma heap_compat_ro_r : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat h1 (to_ro h2).
Admitted. 
(*
Proof using.
  hint heap_compat_ro_l, heap_compat_sym. autos*.
Qed.*)

Lemma heap_compat_ro : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat (to_ro h1) (to_ro h2).
Admitted. (*
Proof using.
  introv (M1&M2). split.
  { do 2 rewrite to_ro_r.
    applys~ Fmap.agree_union_lr. }
  { do 2 rewrite to_ro_f. fmap_disjoint. }
Qed.*)


(* ---------------------------------------------------------------------- *)
(* ** Properties of [heap_empty] *)

Lemma heap_empty_state : heap_state heap_empty = Fmap.empty.
Proof. unfold heap_empty. unfold heap_state. fmap_eq. skip. Qed.

Hint Rewrite heap_empty_state : rew_heap.


(* ---------------------------------------------------------------------- *)
(* ** More properties of [heap_union] *)

Lemma heap_union_comm : forall h1 h2,
  (* heap_compat h1 h2 ->   Hypothesis not needed! *)
  h1 \u h2 = h2 \u h1.
Admitted. (*
Proof using.
  intros. hint heap_compat_sym. unfold heap_union.
  tests E: (heap_compat h1 h2); tests E': (heap_compat h2 h1);
   try auto_false.
  fequals. fequals.
  { applys Fmap.union_comm_of_disjoint. { destruct E. fmap_disjoint. } }
  { applys Fmap.union_comm_of_agree. { destruct~ E. } }
Qed.*)

Lemma heap_union_assoc : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h2 h3 ->
  heap_compat h1 h3 ->
  (h1 \u h2) \u h3 = h1 \u (h2 \u h3).
Admitted. (*
Proof using.
  introv M1 M2 M3. applys heap_eq.
  forwards~ (E1&E2): heap_union_spec (h1 \u h2) h3.
  { applys~ heap_compat_union_l. }
  rewrites (rm E1). rewrites (rm E2).
  forwards~ (E1&E2): heap_union_spec h1 h2.
  rewrites (rm E1). rewrites (rm E2).
  forwards~ (E1&E2): heap_union_spec h1 (h2 \u h3).
  { applys~ heap_compat_union_r. }
  rewrites (rm E1). rewrites (rm E2).
  rewrite~ heap_union_f. rewrite~ heap_union_r.
  split; fmap_eq.
Qed.*)

Hint Resolve heap_union_comm.

Lemma heap_union_empty_l : forall h,
  heap_empty \u h = h.
Admitted. (*
Proof using.
  intros h. unfold heap_union.
  rewrite (classicT_l (heap_compat_empty_l h)).
  destruct h as ((f,r)&D). simpl.
  fequals_rec; fmap_eq.
Qed.*)

Lemma heap_union_empty_r : forall h,
  h \u heap_empty = h.
Admitted. (*
Proof using.
  intros. rewrite heap_union_comm. apply heap_union_empty_l.
Qed.*)

Lemma heap_union_state : forall h1 h2,
  heap_compat h1 h2 ->
  heap_state (h1 \u h2) = heap_state h1 \+ heap_state h2.
Admitted. (*
Proof using.
  introv D. unfold heap_union. rewrite (classicT_l D).
  destruct h1 as ((f1,r1)&D1). destruct h2 as ((f2,r2)&D2).
  unstate. fmap_eq.
Qed.*)

Hint Rewrite heap_union_state : rew_fmap.

Lemma heap_compat_components : forall h,
  heap_compat h^rw h^ro.
Admitted.

Lemma heap_state_components : forall h,
  heap_state h = heap_state (h^rw) \+ heap_state (h^ro).
Proof using. 
  intros. rewrite (heap_eq_union_rw_ro h) at 1.
  rewrite* heap_union_state. applys* heap_compat_components.
Qed.
    
  



Hint Rewrite heap_union_empty_l heap_union_empty_r
  (* heap_full_f heap_full_r *)
  (*to_ro_f to_ro_r *) heap_union_f heap_union_r : rew_heap.
  (* add heap_union_assoc? *)

Tactic Notation "rew_heap" :=
  autorewrite with rew_heap.
Tactic Notation "rew_heap" "~" :=
  rew_heap; auto_tilde.
Tactic Notation "rew_heap" "in" hyp(H) :=
  autorewrite with rew_heap in H.
Tactic Notation "rew_heap" "~" "in" hyp(H) :=
  rew_heap in H; auto_tilde.
Tactic Notation "rew_heap" "in" "*" :=
  autorewrite with rew_heap in *.
Tactic Notation "rew_heap" "~" "in" "*" :=
  rew_heap in *; auto_tilde.

Ltac heap_eq :=
  solve [ rew_heap; subst; auto ].


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
Proof using. applys haffine_any. Qed.

Lemma haffine_hstar : forall H1 H2,
  haffine H1 ->
  haffine H2 ->
  haffine (H1 \* H2).
Proof using. intros. applys haffine_any. Qed.

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

Lemma hgc_intro : forall h,
  \GC h.
Proof using. intros. applys hgc_of_heap_affine. hnfs*. Qed.

End Aux.

Global Opaque heap_affine.


(* ---------------------------------------------------------------------- *)
(* ** Singleton heap *)

Definition hsingle (l:loc) (v:val) : hprop :=
  fun h => (*   h^rw = Fmap.single l v
           /\ h^ro = Fmap.empty *)
              h = Fmap.single l (v, mode_rw)
           /\ l <> null.

Notation "l '~~~>' v" := (hsingle l v)
  (at level 32, no associativity) : heap_scope.

Lemma single_rw : forall l v,
  ((Fmap.single l (v, mode_rw))^rw) = Fmap.single l (v, mode_rw).
Proof using. skip. Qed.

Hint Rewrite single_rw : rew_heap.

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
Proof using. skip. Qed.

Notation Normal_post Q := (forall x, Normal (Q x)).

(* TEMP *)
Lemma heap_empty_ro : 
  (heap_empty^ro) = empty.
Proof using. skip. Qed.

Hint Rewrite heap_empty_ro : rew_heap.

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

Lemma Normal_hempty' : (* simpler proof *)
  Normal \[].
Proof using.
  intros. rewrite hempty_eq_hpure_true. applys~ Normal_hpure.
Qed.

Instance Normal_hsingle : forall l v,
  Normal (hsingle l v).
Proof using.
  Transparent hsingle.
  introv M. unfolds hsingle. skip.
Qed.

Instance Normal_hstar : forall H1 H2,
  Normal H1 ->
  Normal H2 ->
  Normal (H1 \* H2).
Proof using.
  introv N1 N2 (h1&h2&P1&P2&M1&EQ).
  lets (_&E): heap_eq_forward EQ. simpls. rewrite E.
  rewrite~ heap_union_r.
  rewrites (>> N1 P1). rewrites (>> N2 P2). rew_heap*.
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
  rewrite~ heap_union_r.
  lets (MP&ME): hpure_inv P1. rewrites (rm ME).
  rewrites~ (>> N P2). rew_heap*.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Definitions and properties of [RO] *)

Definition RO (H:hprop) : hprop :=
  fun h => exists h', H h' /\ h = to_ro h'.

Lemma RO_duplicatable : forall H,
  duplicatable (RO H).
Proof using. Admitted. (*
  intros H h M. lets (h'&M1&M2&M3): M. subst.
  lets D: heap_compat_refl_if_ro M2.
  exists h h. splits~.
  { applys heap_eq. rewrite~ heap_union_f.
    rewrite~ heap_union_r. rewrite M2.
    split. fmap_eq. rewrite~ Fmap.union_self. }
Qed. *)

Lemma RO_covariant : forall H1 H2,
  H1 ==> H2 ->
  (RO H1) ==> (RO H2).
Proof using. Admitted. (*
  introv M. intros h (h'&M1&M2&M3). exists~ h'.
Qed. *)

Lemma RO_RO : forall H,
  RO (RO H) = RO H.
Proof using. Admitted. (*
  intros. apply pred_ext_1. intros h.
  iff (h'&(h''&M1'&M2'&M3')&M2&M3) (h'&M1&M2&M3).
  { exists h''. splits~.
    rewrite M3. rewrite M3'. rewrite M2'. fmap_eq. }
  { exists h. splits~.
    { exists h'. split~. }
    { rewrite M2. fmap_eq. } }
Qed. *)

Lemma RO_empty :
  RO \[] = \[].
Proof using. Admitted. (*
  intros. apply pred_ext_1. intros h.
  unfold hempty. iff (h'&M1&M2&M3) M1.
  { rewrite M1 in M3. rew_fmap. apply heap_eq. auto. }
  { exists h. rewrite M1. splits~. rew_fmap~. }
Qed. *)

Lemma RO_pure : forall P,
  RO \[P] = \[P].
Proof using. Admitted. (*
  intros. apply pred_ext_1. intros h.
  iff (h'&(M1p&M2)&M3&M4) (MP&M1); unfolds hempty.
  { rewrite M2 in M4. rew_fmap. split~. apply heap_eq. auto. }
  { exists h. rewrite M1. splits~. { split~. split~. } { rew_fmap~. } }
Qed. *)

Lemma RO_empty' : (* simpler proof *)
  RO \[] = \[].
Proof using. Admitted. (*
  intros. rewrite hempty_eq_hpure_true. rewrite~ RO_pure.
Qed. *)

Lemma RO_hexists : forall A (J:A->hprop),
    RO (hexists J)
  = \exists x, RO (J x).
Proof using.
Admitted.
(*
  intros. apply pred_ext_1. intros h.
  iff (h'&(x&M1)&M2&M3) (x&(h'&M1&M2&M3)).
  { exists x. exists* h'. }
  { exists h'. splits~. { exists~ x. } }
Qed. *)

(* NOT NEEDED?
Lemma RO_if : forall (b:bool) H1 H2,
    RO (if b then H1 else H2)
  = (if b then RO H1 else RO H2).
Proof using. intros. destruct* b. Qed.
*)

Lemma RO_or : forall H1 H2,
     RO (hor H1 H2)
  ==> hor (RO H1) (RO H2).
Proof using. Admitted. (*
  intros. unfolds hor. rewrite RO_hexists.
  applys himpl_hexists. intros b. destruct* b.
Qed. *)

Lemma RO_star : forall H1 H2,
  RO (H1 \* H2) ==> (RO H1 \* RO H2).
Proof using. Admitted. (*
  intros. intros h (h'&(h1&h2&N1&P1&P2&N2)&M2&M3).
  lets C: (@heap_compat_ro h1 h2).
  exists (to_ro h1) (to_ro h2). splits.
  { exists~ h1. }
  { exists~ h2. }
  { auto. }
  { applys heap_eq. rew_heap~. split.
    { rewrite M2. fmap_eq. }
    { rewrite M3,N2. rew_heap~. fmap_eq. } }
Qed. *)

Lemma to_ro_pred : forall (H:hprop) h,
  H h ->
  RO H (to_ro h).
Proof using. Admitted. (*
  introv N. exists h. split~.
Qed. *)

Arguments RO_star : clear implicits.


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
  { himpl_fold~. }
  exists h' v. splits~. { himpl_fold. auto. }
Qed.


Lemma hoare_named_heap : forall t H Q,
  (forall h, H h -> hoare t (= h) Q) ->
  hoare t H Q.
Proof using. introv M. intros h Hh. applys* M. Qed.



Hint Rewrite to_ro_rw to_ro_ro : rew_heap.

Lemma hoare_frame_read_only : forall t H1 Q1 H2,
  hoare t (H1 \* RO H2) Q1 ->
  Normal H2 ->
  hoare t (H1 \* H2) (Q1 \*+ H2).
Proof using.
  introv M N. intros h (h1&h2&P1&P2&R1&R2).
  forwards (h'&v&R&L&S): M (h1 \u to_ro h2).
  { exists h1 (to_ro h2). splits~. 
    { applys* to_ro_pred. }
    { applys* heap_compat_ro_r. } }
  rewrite (heap_eq_union_rw_ro h') in R.
  rewrite heap_union_state in R.
  rewrite heap_union_state in R.
  rewrite S in R.
  rew_heap in R. 
  rewrite heap_union_state in R.
  exists (h'^rw \u h1^ro \u h2) v. splits.
  { rewrite heap_union_state.  rewrite heap_union_state. rewrite to_ro_state in R.
     subst h. rewrite heap_union_state. applys_eq R. skip. skip. skip. }
  { rew_heap. exists ___. skip. skip.
    (* normal -> rw is empty *)
    (* ro rw -> empty *)  skip . skip. (* h2^ro is empty *) skip. skip. }
  { skip. }
  { skip. }
  { skip. }
  { skip. }
  { applys* heap_compat_ro_r. }
Qed. (* TODO *)


(* ********************************************************************** *)
(** * Hoare rules for term constructs *)

Implicit Types v : val.


Lemma hoare_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, hoare t (J x) Q) ->
  hoare t (hexists J) Q.
Proof. introv M. intros h (x&Hh). applys M Hh. Qed.

Lemma hoare_hpure : forall t (P:Prop) H Q,
  (P -> hoare t H Q) ->
  hoare t (\[P] \* H) Q.
Proof.
  introv M. intros h (h1&h2&(HP&M1)&M2&D&U). hnf in M1. subst. rew_heap*.
Qed.


(* ########################################################### *)
(** ** Reasoning rules for terms, for Hoare triples. *)

Lemma hoare_val : forall v H Q,
  Normal_post Q ->
  H ==> Q v ->
  hoare (trm_val v) H Q.
Proof.
  introv N M. intros h K. exists h v. splits~.
  { applys eval_val. }
  { specializes M K. rewrites~ (>> Normal_rw M). }
Qed.

Lemma hoare_fix : forall f x t1 H Q,
  Normal_post Q ->
  H ==> Q (val_fix f x t1) ->
  hoare (trm_fix f x t1) H Q.
Proof.
  introv N M. intros h K. exists h (val_fix f x t1). splits~.
  { applys* eval_fix. }
  { specializes M K. rewrites~ (>> Normal_rw M). }
Qed.

Lemma hoare_app : forall v1 v2 (f:var) x t1 H Q,
  Normal_post Q ->
  v1 = val_fix f x t1 ->
  f <> x ->
  hoare (subst x v2 (subst f v1 t1)) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof.
  introv N E D M. intros s K0. forwards (s'&v&R1&K1&E1): (rm M) K0.
  exists s' v. splits~. { applys* eval_app E R1. auto_false. }
Qed.

Hint Extern 1 (heap_compat _ _) => skip.
Hint Extern 1 (disjoint _ _) => skip.

Axiom RO_ro : forall h,
  RO (= (h^ro)) (h^ro).

Axiom ro_ro : forall h,
  (h^ro)^ro = h^ro.

Axiom rw_ro : forall h,
  (h^rw)^ro = Fmap.empty.

Axiom ro_rw : forall h,
  (h^ro)^rw = Fmap.empty.

Hint Rewrite rw_ro ro_rw ro_ro heap_union_state to_ro_state : rew_heap.

Lemma hoare_let : forall x t1 t2 H1 H2 Q Q1,
  hoare t1 (H1 \* RO H2) Q1 ->
  (forall v H3, hoare (subst x v t2) (Q1 v \* H2 \* RO H3) Q) ->
  hoare (trm_let x t1 t2) (H1 \* H2) Q.
Proof.
  introv M1 M2 (h1&h2&P1&P2&D&U).
  forwards* (h1'&v1&R1&K1&E1): (rm M1) (h1 \u to_ro h2).
  { do 2 esplit. splits*. { applys* to_ro_pred. } }
  forwards* (h2'&v2&R2&K2&E2): (rm M2) v1 (= (h1^ro)) (h1'^rw \u h2 \u h1^ro).
  { do 2 esplit. (* TODO: tactic *) splits*.
    do 2 esplit. splits*. applys RO_ro. } 
  exists h2' v2. splits*.
  { applys eval_let_trm (heap_state h1').
    { applys_eq R1. subst h. rew_heap*. } 
    { applys_eq R2. rewrite (heap_state_components h1').
      rewrite E1. rew_heap*. fmap_eq*. } }
    { rewrite E2. rewrite U. rew_heap*. }
Qed.

Lemma hoare_if : forall (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.
Proof.
  introv M1. intros h Hh. forwards* (h1'&v1&R1&K1&E1): (rm M1).
  exists h1' v1. splits*. { applys* eval_if. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Definition of SL triples in a logic with read-only predicates *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) :=
  forall H', Normal H' -> hoare t (H \* H') (Q \*+ H' \*+ \GC).



(* ---------------------------------------------------------------------- *)
(* ** Connection with Hoare triples *)

(** Lemma to introduce hoare instances for establishing triples,
    integrating the consequence rule. *)

Lemma triple_of_hoare : forall t H Q,
  (forall H', exists Q', hoare t (H \* H') Q' /\ Q' ===> Q \*+ H' \*+ \GC) ->
  triple t H Q.
Proof using.
  introv M. intros HF N. lets (Q'&R&W): M HF. applys* hoare_conseq R.
Qed.

(** Lemma to reciprocally deduce a hoare triple from a SL triple *)

Lemma hoare_of_triple : forall t H Q HF,
  triple t H Q ->
  hoare t ((H \* HF) \* \GC) (fun r => (Q r \* HF) \* \GC).
Proof using.
  introv M. applys hoare_conseq. { applys M. } { xsimpl. } { xsimpl. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** SL rules structural *)

Lemma triple_frame_read_only : forall t H1 Q1 H2,
  triple t (H1 \* RO H2) Q1 ->
  Normal H2 ->
  triple t (H1 \* H2) (Q1 \*+ H2).
Proof using.
  introv M N. intros H' N'.
  specializes M N'.
  rewrite hstar_comm in M. rewrite <- hstar_assoc in M.
  rewrite hstar_comm. rewrite <- hstar_assoc.
  applys hoare_conseq. applys~ hoare_frame_read_only M. xsimpl. xsimpl.
Qed.


Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using. intros. applys* local_conseq. Qed.

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using. intros. applys* local_frame. Qed.

Lemma triple_ramified_frame : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  triple t H Q.
Proof using. intros. applys* local_ramified_frame. Qed.

Lemma triple_ramified_frame_hgc : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* (Q \*+ \GC)) ->
  triple t H Q.
Proof using. intros. applys* local_ramified_frame_hgc. Qed.

Lemma triple_ramified_frame_htop : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* (Q \*+ \Top)) ->
  triple t H Q.
Proof using. introv M1 W. rewrite <- hgc_eq_htop in W. applys* triple_ramified_frame_hgc. Qed.

Lemma triple_hgc_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \GC) Q.
Proof using. intros. applys* local_hgc_pre. Qed.

Lemma triple_hgc_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.
Proof using. intros. applys* local_hgc_post. Qed.

Lemma triple_htop_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \Top) Q.
Proof using. introv M. rewrite <- hgc_eq_htop. applys* triple_hgc_pre. Qed.

Lemma triple_htop_post : forall t H Q,
  triple t H (Q \*+ \Top) ->
  triple t H Q.
Proof using. introv M. rewrite <- hgc_eq_htop in M. applys* triple_hgc_post. Qed.

Lemma triple_hany_pre : forall t H H' Q,
  triple t H Q ->
  triple t (H \* H') Q.
Proof using.
  introv M. applys triple_conseq.
  { applys* triple_htop_pre. }
  { xsimpl. } { xsimpl. }
Qed.

Lemma triple_hany_post : forall t H H' Q,
  triple t H (Q \*+ H') ->
  triple t H Q.
Proof using.
  introv M. applys triple_htop_post.
  applys triple_conseq M; xsimpl.
Qed.

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using. intros. applys* local_hexists. Qed.

Lemma triple_hforall : forall A (x:A) t (J:A->hprop) Q,
  triple t (J x) Q ->
  triple t (hforall J) Q.
Proof using. intros. applys* local_hforall. Qed.

Lemma triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using. intros. applys* local_hpure. Qed.

Lemma triple_hwand_hpure_l : forall t (P:Prop) H Q,
  P ->
  triple t H Q ->
  triple t (\[P] \-* H) Q.
Proof using. intros. applys* local_hwand_hpure_l. Qed.

Lemma triple_hor : forall t H1 H2 Q,
  triple t H1 Q ->
  triple t H2 Q ->
  triple t (hor H1 H2) Q.
Proof using. intros. applys* local_hor. Qed.

Lemma triple_hand_l : forall t H1 H2 Q,
  triple t H1 Q ->
  triple t (hand H1 H2) Q.
Proof using. intros. applys* local_hand_l. Qed.

Lemma triple_hand_r : forall t H1 H2 Q,
  triple t H2 Q ->
  triple t (hand H1 H2) Q.
Proof using. intros. applys* local_hand_r. Qed.

Lemma triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.
Proof using. intros. applys* local_conseq_frame. Qed.

Lemma triple_conseq_frame_hgc : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \GC ->
  triple t H Q.
Proof using. intros. applys* local_conseq_frame_hgc. Qed.



(* ---------------------------------------------------------------------- *)
(* ** SL rules for terms *)

Lemma triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using.
  introv M. intros HF. applys hoare_val. { xchanges M. }
Qed.

Lemma triple_fixs : forall f xs t1 H Q,
  xs <> nil ->
  H ==> Q (val_fixs f xs t1) ->
  triple (trm_fixs f xs t1) H Q.
Proof using.
  introv N M. intros HF. applys~ hoare_fixs. { xchanges M. }
Qed.

Lemma triple_constr : forall id vs H Q,
  H ==> Q (val_constr id vs) ->
  triple (trm_constr id vs) H Q.
Proof using.
  introv M. intros HF. applys hoare_constr. { xchanges M. }
Qed.

Lemma triple_constr_trm : forall id ts t1 vs H Q Q1,
  triple t1 H Q1 ->
  (forall (X:val), triple (trm_constr id ((trms_vals vs)++(trm_val X)::ts)) (Q1 X) Q) ->
  triple (trm_constr id ((trms_vals vs)++t1::ts)) H Q.
Proof using.
  introv M1 M2. intros HF. applys~ hoare_constr_trm.
  { intros v. applys* hoare_of_triple. }
Qed.

Lemma triple_let : forall z t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall (X:val), triple (subst1 z X t2) (Q1 X) Q) ->
  triple (trm_let z t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF. applys hoare_let.
  { applys M1. }
  { intros v. applys* hoare_of_triple. }
Qed.

Lemma triple_seq : forall t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall (X:val), triple t2 (Q1 X) Q) ->
  triple (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2. applys* triple_let. (* BIND intros. rewrite* subst1_anon. *)
Qed.

Lemma triple_if : forall (b:bool) t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros HF. applys hoare_if. applys M1.
Qed.

Lemma triple_if_bool : forall (b:bool) t1 t2 H Q,
  (b = true -> triple t1 H Q) ->
  (b = false -> triple t2 H Q) ->
  triple (trm_if b t1 t2) H Q.
Proof using.
  introv M1 M2. applys triple_if. case_if*.
Qed.

Lemma triple_if_trm : forall Q1 t0 t1 t2 H Q,
  triple t0 H Q1 ->
  (forall v, triple (trm_if v t1 t2) (Q1 v) Q) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF. applys* hoare_if_trm.
  { intros v. applys* hoare_of_triple. }
Qed.

Lemma triple_if_trm' : forall Q1 t0 t1 t2 H Q, (* not very useful *)
  triple t0 H Q1 ->
  (forall (b:bool), triple (if b then t1 else t2) (Q1 b) Q) ->
  (forall v, ~ is_val_bool v -> (Q1 v) ==> \[False]) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2 M3. applys* triple_if_trm.
  { intros v. tests C: (is_val_bool v).
    { destruct C as (b&E). subst. applys* triple_if. }
    { xtchange* M3. xtpull ;=>. false. } }
Qed.

Lemma triple_apps_funs : forall xs F (Vs:vals) t1 H Q,
  F = (val_funs xs t1) ->
  var_funs xs (length Vs) ->
  triple (substn xs Vs t1) H Q ->
  triple (trm_apps F Vs) H Q.
Proof using. introv E N M. intros HF. applys* hoare_apps_funs. Qed.

Lemma triple_apps_fixs : forall xs (f:var) F (Vs:vals) t1 H Q,
  F = (val_fixs f xs t1) ->
  var_fixs f xs (length Vs) ->
  triple (substn (f::xs) (F::Vs) t1) H Q ->
  triple (trm_apps F Vs) H Q.
Proof using. introv E N M. intros HF. applys* hoare_apps_fixs. Qed.

(* ---------------------------------------------------------------------- *)
(* ** SL rules for primitive functions over the state *)

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists l, \[r = val_loc l] \* l ~~~> v).
Proof using.
  intros. applys triple_of_hoare. intros HF. rew_heap.
  esplit; split. { applys hoare_ref. } { xsimpl*. }
Qed.

Lemma triple_get : forall v l,
  triple (val_get (val_loc l))
    (l ~~~> v)
    (fun x => \[x = v] \* (l ~~~> v)).
Proof using.
  intros. applys triple_of_hoare. intros HF.
  esplit; split. { applys hoare_get. } { xsimpl*. }
Qed.

Lemma triple_set : forall w l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => \[r = val_unit] \* l ~~~> w).
Proof using.
  intros. applys triple_of_hoare. intros HF.
  esplit; split. { applys hoare_set. } { xsimpl*. }
Qed.

Lemma triple_set' : forall w l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => l ~~~> w).
Proof using. intros. xapplys* triple_set. Qed.

Lemma triple_free : forall l v,
  triple (val_free (val_loc l))
    (l ~~~> v)
    (fun r => \[r = val_unit]).
Proof using.
  intros. applys triple_of_hoare. intros HF.
  esplit; split. { applys hoare_free. } { xsimpl*. }
Qed.


(* ********************************************************************** *)
(* * Reasoning rules, low-level proofs *)


Hint Resolve heap_compat_union_l heap_compat_union_r.
Hint Resolve Fmap.agree_empty_l Fmap.agree_empty_r.


(* ---------------------------------------------------------------------- *)
(* ** Definition and properties of [on_rw_sub] *)

Program Definition on_rw_sub H h :=
  exists h1 h2, heap_compat h1 h2
             /\ h = h1 \u h2
             /\ h1^ro = Fmap.empty
             /\ H h1.

Lemma on_rw_sub_base : forall H h,
  H h ->
  h^ro = Fmap.empty ->
  on_rw_sub H h.
Proof using.
  intros H h M N. exists h heap_empty. splits~.
  { applys heap_compat_empty_r. }
  { heap_eq. }
Qed.

Lemma on_rw_sub_htop : forall H h,
  on_rw_sub (H \* \Top) h ->
  on_rw_sub H h.
Proof using.
  introv (h1&h2&N1&N2&N3&(h3&h4&M2&(H'&M3)&D&U)).
  subst h h1. rew_heap~ in N3.
  lets~ (N1a&N1b): heap_compat_union_l_inv N1.
  exists h3 (h4 \u h2). splits~.
  { applys~ heap_union_assoc. }
  { forwards~: Fmap.union_eq_empty_inv_l N3. }
Qed.

Lemma on_rw_sub_htop' : forall H h,
  (H \* \Top) h ->
  Normal H ->
  on_rw_sub H h.
Proof using.
  introv (h1&h2&N1&N2&N3&N4) N. exists h1 h2. splits~.
Qed.

Lemma on_rw_sub_htop_inv : forall H h,
  on_rw_sub H h ->
  (H \* \Top) h.
Proof using.
  introv M. destruct M as (h1&h2&M1&M2&M3&M4). subst.
  exists h1 h2. splits~. exists~ (= h2).
Qed.

Lemma on_rw_sub_union_r : forall H h1 h2,
  on_rw_sub H h1 ->
  heap_compat h1 h2 ->
  on_rw_sub H (h1 \u h2).
Proof using.
  introv (h11&h12&N1&N2&N3&N4) C.
  subst h1. lets~ (N1a&N1b): heap_compat_union_l_inv C.
  exists h11 (h12 \u h2). splits~.
  { applys~ heap_union_assoc. }
Qed.

Lemma on_rw_sub_weaken : forall Q Q' v h,
  on_rw_sub (Q v) h ->
  Q ===> Q' ->
  on_rw_sub (Q' v) h.
Proof using.
  introv (h1&h2&N1&N2&N3&N4) HQ. lets N4': HQ N4. exists~ h1 h2.
Qed.

(*

(* ---------------------------------------------------------------------- *)
(* ** Definition of triples *)

Implicit Types v w : val.
Implicit Types t : trm.

(** Recall that the projection [heap_state : heap >-> state]
   is used as a Coercion, so that we can write [h] where the
   union of the underlying states is expected. *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) :=
  forall h1 h2, heap_compat h1 h2 -> H h1 ->
  exists h1' v,
       heap_compat h1' h2
    /\ eval (h1 \u h2) t (h1' \u h2) v
    /\ h1'^ro = h1^ro
    /\ on_rw_sub (Q v) h1'.


(* ---------------------------------------------------------------------- *)
(* ** Structural rules *)

Lemma triple_hexists : forall t A (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using. introv M D (x&Jx). applys* M. Qed.

Lemma triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. rewrite hpure_eq_hexists_empty. rewrite hstar_hexists.
  rew_heap. applys* triple_hexists.
Qed.

Lemma triple_htop_post : forall t H Q,
  triple t H (Q \*+ \Top) ->
  triple t H Q.
Proof using.
  introv M D P1.
  forwards* (h1'&v&(N1&N2&N3&N4)): (rm M) h1.
  exists h1' v. splits~. applys~ on_rw_sub_htop.
Qed.

Lemma triple_htop_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \Top) Q.
Proof using.
  introv M. intros h1 h2 D (h11&h12&P11&P12&R1&R2). subst h1.
  lets~ (D1&D2): heap_compat_union_l_inv (rm D).
  forwards* (h1'&v&(N1&N2&N3&N4)): (rm M) (h12 \u h2) (rm P11).
  lets~ (D3&D4): heap_compat_union_r_inv (rm N1).
  exists (h1' \u h12) v. splits~.
  { applys_eq N2; try fmap_eq~. }
  { rew_heap~. rewrite N3. fmap_eq~. }
  { applys~ on_rw_sub_union_r. }
Qed.

Lemma triple_conseq : forall t H' Q' H Q,
  H ==> H' ->
  triple t H' Q' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
  introv MH M MQ. intros h1 h2 D P1.
  lets P1': (rm MH) (rm P1).
  forwards~ (h1'&v&(N1&N2&N3&N4)): (rm M) h2 (rm P1').
  exists h1' v. splits~.
  { applys~ on_rw_sub_weaken Q'. }
Qed.

Lemma triple_hor : forall t H1 H2 Q,
  triple t H1 Q ->
  triple t H2 Q ->
  triple t (hor H1 H2) Q.
Proof using.
  introv M1 M2. unfold hor. applys triple_hexists.
  intros b. destruct* b.
Qed.

Lemma triple_hor_symmetric : forall t H1 H2 Q1 Q2,
  triple t H1 Q1 ->
  triple t H2 Q2 ->
  triple t (hor H1 H2) (fun x => hor (Q1 x) (Q2 x)).
Proof using.
  introv M1 M2. apply~ triple_hor.
  { applys~ triple_conseq. applys M1. intros x. applys himpl_hor_r_r. }
  { applys~ triple_conseq. applys M2. intros x. applys himpl_hor_r_l. }
Qed.

Lemma triple_frame_read_only : forall t H1 Q1 H2,
  triple t (H1 \* RO H2) Q1 ->
  Normal H2 ->
  triple t (H1 \* H2) (Q1 \*+ H2).
Proof using.
  introv M N. intros h1 h2 D (h11&h12&P11&P12&R1&R2).
  lets R1': heap_compat_ro_r R1.
  lets E12: (rm N) P12.
  subst h1. lets~ (D1&D2): heap_compat_union_l_inv (rm D).
  asserts R12: (heap_state (to_ro h12) = heap_state h12).
  { unstate. rewrite E12. fmap_eq. }
  asserts C: (heap_compat (h11 \u to_ro h12) h2).
  { apply~ heap_compat_union_l. applys~ heap_compat_ro_l. }
  forwards~ (h1'&v&(N1&N2&N3&N4)): (rm M) (h11 \u (to_ro h12)) h2.
  { exists h11 (to_ro h12). splits~.
    { applys~ to_ro_pred. } }
  rew_heap~ in N3. rewrite E12 in N3.
  lets G: heap_disjoint_components h1'.
  forwards (h1''&F1&F2): heap_make (h1'^rw \+ h12^rw) (h11^ro).
  { rewrite N3 in G. fmap_disjoint. }
  asserts C': (heap_compat h1'' h2).
  { unfolds. rewrite F1,F2. split.
    { destruct~ D1. }
    { lets G2: heap_disjoint_components h2. rewrite N3 in G.
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
       { lets Gx: heap_disjoint_components hx. rewrite V3. auto. } }
     forwards~ (hyf&W1&W2): heap_make (hy^rw) (Fmap.empty:state).
     forwards~ (hcr&Y1&Y2): heap_make (Fmap.empty:state) (hc^ro).
     (* LATER: find a way to automate these lemmas *)
     (* LATER: automate disjoint_components use by fmap_disjoint *)
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
     { exists~ hx hb. } }
Qed.

Lemma triple_frame : forall t H1 Q1 H2,
  triple t H1 Q1 ->
  Normal H2 ->
  triple t (H1 \* H2) (Q1 \*+ H2).
Proof using.
  introv M N. applys~ triple_frame_read_only.
  applys triple_conseq (H1 \* \Top). xsimpl.
  applys* triple_htop_pre. auto.
Qed.

Lemma triple_red : forall t1 t2 H Q,
  (forall m m' r, eval m t1 m' r -> eval m t2 m' r) ->
  triple t1 H Q ->
  triple t2 H Q.
Proof using.
  introv T M. intros h1 h2 D P1.
  forwards* (h'&v&N1&N2&N3&N4): (rm M) P1.
  exists h' v. splits~.
Qed.

(* ---------------------------------------------------------------------- *)
(* ** Customizing xtpull for RO triples, which are not local *)

Lemma xtpull_hpure (H1 H2 : hprop) (P : Prop) (Q : val -> hprop) (t : trm) :
  (P -> triple t (H1 \* H2) Q) -> triple t (H1 \* \[P] \* H2) Q.
Proof. intros. rewrite hstar_comm_assoc. auto using triple_hpure. Qed.

Lemma xtpull_hexists (H1 H2 : hprop) (A : Type) (J:A->hprop)
      (Q : val -> hprop) (t : trm) :
  (forall x, triple t (H1 \* ((J x) \* H2)) Q) ->
  triple t (H1 \* (hexists J \* H2)) Q.
Proof using.
  intros. rewrite hstar_comm_assoc, hstar_hexists. apply triple_hexists.
  intros. rewrite~ hstar_comm_assoc.
Qed.

Lemma xtpull_id A (x X : A) (H1 H2 : hprop) (Q : val -> hprop) (t : trm) :
  (x = X -> triple t (H1 \* H2) Q) -> triple t (H1 \* (x ~> Id X \* H2)) Q.
Proof using. intros. rewrite repr_eq. apply xtpull_hpure. auto. Qed.

Ltac xtpull_hpure tt ::= apply xtpull_hpure; intro.
Ltac xtpull_hexists tt ::= apply xtpull_hexists; intro.
Ltac xtpull_id tt ::= apply xtpull_id; intro.


(* ---------------------------------------------------------------------- *)
(* ** Customizing xtchange for RO triples, which are not local *)

Lemma xtchange_lemma' : forall H1 H1' H2 t H Q,
  (H1 ==> H1') ->
  (H ==> H1 \* H2) ->
  triple t (H1' \* H2) Q ->
  triple t H Q.
Proof using.
  introv W1 W2 M. applys~ triple_conseq M.
  xchange W2. xchanges W1.
Qed.

Ltac xtchange_apply L cont1 cont2 ::=
   eapply xtchange_lemma';
     [ applys L | cont1 tt | cont2 tt (*xtag_pre_post*) ].

Ltac xtchange_with_core cont1 cont2 H H' ::=
  eapply xtchange_lemma' with (H1:=H) (H1':=H');
    [ | cont1 tt | cont2 tt (* xtag_pre_post*)  ].


(* ---------------------------------------------------------------------- *)
(* ** Term rules *)

Lemma triple_val : forall v H Q,
  H ==> Q v ->
  Normal H ->
  triple (trm_val v) H Q.
Proof using.
  introv M HS. intros h1 h2 D P1. specializes HS P1.
  exists h1 v. splits~.
  { applys eval_val. }
  { specializes M P1. applys~ on_rw_sub_base. }
Qed.

(* DEPRECATED
Lemma triple_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  Normal H ->
  triple (trm_fun x t1) H Q.
Proof using.
  introv M HS. intros h1 h2 D P1. exists___. splits*.
  { applys eval_fun. }
  { specializes M P1. applys~ on_rw_sub_base. }
Qed.
*)

Lemma triple_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  Normal H ->
  triple (trm_fix f x t1) H Q.
Proof using.
  introv M HS. intros h1 h2 D P1. exists___. splits*.
  { applys eval_fix. }
  { specializes M P1. applys~ on_rw_sub_base. }
Qed.

Lemma triple_if : forall (b:bool) t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if b t1 t2) H Q.
Proof using.
  introv M. intros h1 h2 D N. forwards* (h'&v'&(N1&N2&N3&N4)): (rm M) h1.
  exists h' v'. splits~. { applys~ eval_if. }
Qed.

Lemma triple_let : forall z t1 t2 H1 H2 Q Q1,
  triple t1 H1 Q1 ->
  (forall (X:val), triple (subst1 z X t2) (Q1 X \* H2) Q) ->
  triple (trm_let z t1 t2) (H1 \* H2) Q.
Proof using.
  introv M1 M2. intros h1 h2 D (h11&h12&P11&P12&R1&R2).
  subst h1. lets~ (D1&D2): heap_compat_union_l_inv (rm D).
  forwards~ (h1'&v1&(N1&N2&N3&N4)): (rm M1) (h12 \u h2) (rm P11).
  destruct N4 as (hx&hy&K1&K2&K3&K4).
  subst h1'. forwards~ (N1a&N1b): heap_compat_union_l_inv N1.
  forwards~ (N1aa&N1ab): heap_compat_union_r_inv N1a.
  forwards~ (N1ba&N1bb): heap_compat_union_r_inv N1b.
  forwards~ (h1''&v2&(T1&T2&T3&T4)): ((rm M2) v1) (h12 \u hx) (hy \u h2).
  { exists~ hx h12. }
  forwards~ (T1a&T1b): heap_compat_union_r_inv T1.
  exists (h1'' \u hy) v2. splits~.
  { applys eval_let_trm.
    { applys_eq~ N2. rewrite~ heap_union_assoc. }
    { applys_eq~ T2.
      { fequals.
        rewrite~ (@heap_union_comm h12 hx).
        do 2 rewrite~ heap_union_assoc. fequals.
        rewrite~ <- heap_union_assoc.
        rewrite~ (@heap_union_comm hy h12).
        rewrite~ heap_union_assoc. }
      { rewrite~ heap_union_assoc. } } }
  { rew_heap~. rewrite T3. rew_heap~. rewrite <- N3. rew_heap~.
    rewrite (Fmap.union_comm_of_agree (hx^ro \+ hy^ro) h12^ro).
    rewrite~ Fmap.union_assoc. applys Fmap.agree_union_l.
    destruct~ N1aa. destruct~ N1ba. }
  { applys~ on_rw_sub_union_r. }
Qed.

Lemma triple_let_simple : forall z t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall (X:val), triple (subst1 z X t2) (Q1 X) Q) ->
  triple (trm_let z t1 t2) H Q.
Proof using.
  introv M1 M2.
  applys_eq~ (>> triple_let \[] M1).
  { rewrite* hstar_hempty_r. }
  { intros X. rewrite* hstar_hempty_r. }
Qed.

Lemma triple_let_val : forall z v1 t2 H Q,
  (forall (X:val), X = v1 -> triple (subst1 z X t2) H Q) ->
  triple (trm_let z (trm_val v1) t2) H Q.
Proof using.
  introv M. forwards~ M': M.
  applys_eq (>> triple_let \[] Q (fun x => \[x = v1])).
  { rewrite~ hstar_hempty_l. }
  { applys triple_val. rewrite <- (@hstar_hempty_r \[v1=v1]).
    applys~ himpl_hstar_hpure_r. applys Normal_hempty. }
  { intros X. applys triple_hpure. applys M. }
Qed.

Lemma triple_app_fix : forall (f:bind) F x X t1 H Q,
  F = val_fix f x t1 ->
  f <> x ->
  triple (subst2 f F x X t1) H Q ->
  triple (trm_app F X) H Q.
Proof using.
  introv EF N M. subst. applys triple_red (rm M).
  introv R. hint eval_val. applys* eval_app_trm.
Qed.

(* LATER: derivable let-fix rule

Definition spec_fix (f:var) (x:var) (t1:trm) (F:val) :=
  forall X, triple (subst f F (subst x X t1)) ===> triple (trm_app F X).

Lemma triple_let_fix : forall f x t1 t2 H Q,
  (forall (F:val), spec_fix f x t1 F -> triple (subst f F t2) H Q) ->
  Normal H ->
  triple (trm_let f (trm_fix f x t1) t2) H Q.
Proof using.
  introv M HS. applys triple_let_simple (fun F => \[spec_fix f x t1 F] \* H).
  { applys~ triple_fix. xsimpl~. introv R. applys* triple_app_fix. }
  { intros F. applys triple_hpure. applys M. }
Qed.
*)

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists l, \[r = val_loc l] \* l ~~~> v).
Proof using.
  intros. intros h1 h2 _ P1.
  lets E: hempty_inv P1. subst h1.
  forwards~ (l&Dl&Nl): (Fmap.single_fresh null (heap_state h2) v).
  lets~ (h1'&E1&E2): heap_make (Fmap.single l v) (Fmap.empty:state).
  asserts E3: (heap_state h1' = Fmap.single l v).
  { unstate. rewrite E1,E2. fmap_eq. }
  asserts D1': (\# (heap_state h2) (heap_state h1')).
  { unfold heap_state at 2. rewrite E1,E2. fmap_disjoint. }
  (* LATER: beautify the assertions above *)
  exists h1' (val_loc l).
  asserts C: (heap_compat h1' h2).
  { split.
    { rewrite~ E2. }
    { rewrite E1,E2. lets: heap_disjoint_components h2.
      fmap_disjoint. } }
  splits~.
  { rew_heap. rew_fmap~. applys~ eval_ref_sep. }
  { applys~ on_rw_sub_base. exists l.
    applys~ himpl_hstar_hpure_r (l ~~~> v). split~. }
Qed.

Lemma triple_get_ro : forall v l,
  triple (val_get (val_loc l))
    (RO (l ~~~> v))
    (fun x => \[x = v]).
Proof using.
  intros. intros h1 h2 D (h1'&(E1'&E2'&NL)&E1&E2).
  rewrites E2' in E2. rewrite Fmap.union_empty_r in E2.
  exists h1 v. splits~.
  { rew_fmap~. unfold heap_state. rewrite E1,E2,E1'. rew_fmap.
    applys~ eval_get_sep. }
  { exists heap_empty h1. splits~.
    { applys~ heap_compat_empty_l. }
    { heap_eq. }
    { applys~ hpure_intro. } }
Qed.

Lemma triple_set : forall w l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => \[r = val_unit] \* l ~~~> w).
Proof using.
  intros. intros h1 h2 D (E1&E2&NL).
  lets~ (h1'&E1'&E2'): heap_make (Fmap.single l w) (Fmap.empty:state).
  exists h1' val_unit.
  asserts Dl: (Fmap.disjoint (Fmap.single l w) (heap_state h2)).
  { destruct D as (D1&D2). rewrite E1 in D2. unstate.
    applys Fmap.disjoint_single_set v. auto. }
  asserts C: (heap_compat h1' h2).
  { destruct D as (D1&D2). unfolds. rewrite E1',E2'.
    unfold heap_state in Dl. split~. }
  splits~.
  { rew_fmap~. rewrite (@heap_fmap_def h1'). rewrite (@heap_fmap_def h1).
    rewrite E1,E1',E2,E2'. rew_fmap.
    applys eval_set_sep; try reflexivity.
    { eapply Fmap.disjoint_single_set; eauto. } }
  { rewrite E2,E2'. auto. }
  { applys~ on_rw_sub_base. applys~ himpl_hstar_hpure_r (l ~~~> w). split~. }
Qed.

Lemma triple_add : forall (n1 n2:int),
  triple (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).
Proof using.
  intros. intros h1 h2 D E.
  exists h1 (n1+n2). splits~.
  { applys* eval_binop. applys* evalbinop_add. }
  { exists heap_empty h1. splits~.
    { applys~ heap_compat_empty_l. }
    { heap_eq. }
    { applys~ hpure_intro. } }
Qed.



(* ********************************************************************** *)
(* * Ramified read-only frame rule *)

(* ---------------------------------------------------------------------- *)
(* ** Definition of the [normally] modality *)

Definition normally H : hprop :=
  fun h => H h /\ h^ro = Fmap.empty.

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
  { intros h N. lets (_&E): N arbitrary. split.
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
  asserts R12: (heap_state (to_ro h12) = heap_state h12).
  { unstate. rewrite E12. fmap_eq. }
  asserts C: (heap_compat (h11 \u to_ro h12) h2).
  { apply~ heap_compat_union_l. applys~ heap_compat_ro_l. }
  forwards~ (h1'&v&(N1&N2&N3&N4)): (rm M) (h11 \u (to_ro h12)) h2.
  { exists h11 (to_ro h12). splits~.
    { applys~ to_ro_pred. } }
  rew_heap~ in N3. rewrite E12 in N3.
  lets G: heap_disjoint_components h1'.
  forwards (h1''&F1&F2): heap_make (h1'^rw \+ h12^rw) (h11^ro).
  { rewrite N3 in G. fmap_disjoint. }
  asserts C': (heap_compat h1'' h2).
  { unfolds. rewrite F1,F2. split.
    { destruct~ D1. }
    { lets G2: heap_disjoint_components h2. rewrite N3 in G.
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
       { lets Gx: heap_disjoint_components hx. rewrite V3. auto. } }
     forwards~ (hyf&W1&W2): heap_make (hy^rw) (Fmap.empty:state).
     forwards~ (hcr&Y1&Y2): heap_make (Fmap.empty:state) (hc^ro).
     (* LATER: find a way to automate these lemmas *)
     (* LATER: automate disjoint_components use by fmap_disjoint *)
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


(* ********************************************************************** *)
(* * Derived rules for practical proofs *)

Lemma triple_apps_funs : forall xs F (Vs:vals) t1 H Q,
  F = (val_funs xs t1) ->
  var_funs xs (LibList.length Vs) ->
  triple (substn xs Vs t1) H Q ->
  triple (trm_apps F Vs) H Q.
Proof using.
  introv E N M. intros h1 h2 D H1.
  forwards~ (h1'&v&N1&N2&N3&N4): (rm M) h2 H1.
  exists h1' v. splits~. { subst. applys~ eval_apps_funs. }
Qed.

Lemma var_funs_exec_elim : forall (n:nat) xs,
  var_funs_exec xs n ->
  var_funs xs n.
Proof using. introv M. rewrite var_funs_exec_eq in M. rew_istrue~ in M. Qed.

Hint Resolve var_funs_exec_elim.

Lemma triple_let' : forall z t1 t2 H2 H1 H Q Q1,
  H ==> (H1 \* H2) ->
  triple t1 H1 Q1 ->
  (forall (X:val), triple (subst1 z X t2) (Q1 X \* H2) Q) ->
  triple (trm_let z t1 t2) H Q.
Proof using. introv WP M1 M2. applys* triple_conseq WP. applys* triple_let. Qed.

Lemma triple_letfun : forall (f:bind) x t1 t2 H Q,
  (forall F, triple (subst1 f F t2) (\[F = val_fun x t1] \* H) Q) ->
  triple (trm_let f (trm_fun x t1) t2) H Q.
Proof using.
  introv M. applys triple_let' H (fun F => \[F = val_fun x t1]).
  { xsimpl. }
  { applys triple_fix. xsimpl~. typeclass. }
  { intros F. applys M. }
Qed.

Lemma triple_frame_read_only_conseq : forall t H1 Q1 H2 H Q,
  H ==> (H1 \* H2) ->
  Normal H1 ->
  triple t (RO H1 \* H2) Q1 ->
  (Q1 \*+ H1) ===> Q ->
  triple t H Q.
Proof using.
  introv WP M N WQ. applys* triple_conseq (rm WP) (rm WQ).
  forwards~ R: triple_frame_read_only t H2 Q1 H1.
  { rewrite~ hstar_comm. } { rewrite~ hstar_comm. }
Qed.


*)
