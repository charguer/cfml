(**

This file contains a representation of finite maps
that may be used for representing a store. It also
provides lemmas and tactics for reasoning about
operations on the store (read, write, union).

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From TLC Require Import LibCore.


(** The type [map A B] is represented as a function of type [A -> option B].

    Type type [fmap A B] is represented as a pair of a map of type [map A B]
    and a proof that the domain of the map is finite. The finiteness of the
    domain is witnessed by a list of keys such that the map binds any key
    not in that list to [None].

*)



(* ********************************************************************** *)
(** * Maps (partial functions) *)

(* ---------------------------------------------------------------------- *)
(* ** Representation *)

(** Type of partial functions from A to B *)

Definition map (A B : Type) : Type :=
  A -> option B.


(* ---------------------------------------------------------------------- *)
(* ** Operations *)

(** Disjoint union of two partial functions *)

Definition map_union (A B : Type) (f1 f2 : map A B) : map A B :=
  fun (x:A) => match f1 x with
           | Some y => Some y
           | None => f2 x
           end.

(** Removal from a partial functions *)

Definition map_remove (A B : Type) (f : map A B) (k:A) : map A B :=
  fun (x:A) => If x = k then None else f x.

(** Finite domain of a partial function *)

Definition map_finite (A B : Type) (f : map A B) :=
  exists (L : list A), forall (x:A), f x <> None -> mem x L.

(** Disjointness of domain of two partial functions *)

Definition map_disjoint (A B : Type) (f1 f2 : map A B) :=
  forall (x:A), f1 x = None \/ f2 x = None.

(** Compatibility of two partial functions on the intersection
    of their domains (only for Separation Logic with RO-permissions) *)

Definition map_agree (A B : Type) (f1 f2 : map A B) :=
  forall x v1 v2,
  f1 x = Some v1 ->
  f2 x = Some v2 ->
  v1 = v2.

(** Domain of a map (as a predicate) *)

Definition map_indom (A B : Type) (f1 : map A B) : (A->Prop) :=
  fun (x:A) => f1 x <> None.


(* ---------------------------------------------------------------------- *)
(** Properties *)

Section MapOps.
Variables (A B : Type).
Implicit Types f : map A B.

(** Symmetry of disjointness *)

Lemma map_disjoint_sym :
  sym (@map_disjoint A B).
Proof using.
  introv H. unfolds map_disjoint. intros z. specializes H z. intuition.
Qed.

(** Commutativity of disjoint union *)

Lemma map_union_comm : forall f1 f2,
  map_disjoint f1 f2 ->
  map_union f1 f2 = map_union f2 f1.
Proof using.
  introv H. unfold map.
  extens. intros x. unfolds map_disjoint, map_union.
  specializes H x. cases (f1 x); cases (f2 x); auto. destruct H; false.
Qed.

(** Finiteness of union *)

Lemma map_union_finite : forall f1 f2,
  map_finite f1 ->
  map_finite f2 ->
  map_finite (map_union f1 f2).
Proof using.
  introv [L1 F1] [L2 F2]. exists (L1 ++ L2). intros x M.
  specializes F1 x. specializes F2 x. unfold map_union in M.
  apply mem_app. destruct~ (f1 x).
Qed.

(** Finiteness of removal *)

Definition map_remove_finite : forall x f,
  map_finite f ->
  map_finite (map_remove f x).
Proof using.
  introv [L F]. exists L. intros x' M.
  specializes F x'. unfold map_remove in M. case_if~.
Qed.

End MapOps.


(* ********************************************************************** *)
(** * Finite maps *)

(* ---------------------------------------------------------------------- *)
(** Definition of the type of finite maps *)

Inductive fmap (A B : Type) : Type := make {
  fmap_data :> map A B;
  fmap_finite : map_finite fmap_data }.

Arguments make [A] [B].


(* ---------------------------------------------------------------------- *)
(** Operations *)

(** Empty fmap *)

Program Definition empty (A B : Type) : fmap A B :=
  make (fun l => None) _.
Next Obligation. exists (@nil A). auto_false. Qed.

Arguments empty {A} {B}.

(** Singleton fmap *)

Program Definition single A B (x:A) (v:B) : fmap A B :=
  make (fun x' => If x = x' then Some v else None) _.
Next Obligation.
  exists (x::nil). intros. case_if. subst~.
Qed.

(** Union of fmaps *)

Program Definition union A B (h1 h2:fmap A B) : fmap A B :=
  make (map_union h1 h2) _.
Next Obligation. destruct h1. destruct h2. apply~ map_union_finite. Qed.

Notation "h1 \+ h2" := (union h1 h2)
   (at level 51, right associativity) : fmap_scope.

Open Scope fmap_scope.

(** Update of a fmap *)

Definition update A B (h:fmap A B) (x:A) (v:B) : fmap A B :=
  union (single x v) h.
  (* Note: the union operation first reads in the first argument. *)

(** Read in a fmap *)

Definition read (A B : Type) {IB:Inhab B} (h:fmap A B) (x:A) : B :=
  match fmap_data h x with
  | Some y => y
  | None => arbitrary
  end.

(** Removal from a fmap *)

Program Definition remove A B (h:fmap A B) (x:A) : fmap A B :=
  make (map_remove h x) _.
Next Obligation. destruct h. apply~ map_remove_finite. Qed.

(** Domain of a fmap (as a predicate) *)

Definition indom (A B: Type) (h:fmap A B) : (A->Prop) :=
  map_indom h.


(* ---------------------------------------------------------------------- *)
(** Properties *)

(** Inhabited type [fmap] *)

Global Instance Inhab_fmap A B : Inhab (fmap A B).
Proof using. intros. applys Inhab_of_val (@empty A B). Qed.

(** Compatible fmaps (only for Separation Logic with RO-permissions) *)

Definition agree A B (h1 h2:fmap A B) :=
  map_agree h1 h2.

(** Disjoint fmaps *)

Definition disjoint A B (h1 h2 : fmap A B) : Prop :=
  map_disjoint h1 h2.

(** Three disjoint fmaps (not needed for basic separation logic) *)

Definition disjoint_3 A B (h1 h2 h3 : fmap A B) :=
     disjoint h1 h2
  /\ disjoint h2 h3
  /\ disjoint h1 h3.

(** Notation for disjointness *)

Module NotationForFmapDisjoint.

Notation "\# h1 h2" := (disjoint h1 h2)
  (at level 40, h1 at level 0, h2 at level 0, no associativity) : fmap_scope.

Notation "\# h1 h2 h3" := (disjoint_3 h1 h2 h3)
  (at level 40, h1 at level 0, h2 at level 0, h3 at level 0, no associativity)
  : fmap_scope.

End NotationForFmapDisjoint.

Import NotationForFmapDisjoint.


(* ********************************************************************** *)
(* * Lemmas about Fmap *)

Section FmapProp.
Variables (A B : Type).
Implicit Types f g h : fmap A B.

(* ---------------------------------------------------------------------- *)
(* ** Equality *)

Lemma make_eq : forall (f1 f2:map A B) F1 F2,
  (forall x, f1 x = f2 x) ->
  make f1 F1 = make f2 F2.
Proof using.
  introv H. asserts: (f1 = f2). { unfold map. extens~. }
  subst. fequals. (* note: involves proof irrelevance *)
Qed.

Lemma eq_inv_fmap_data_eq : forall h1 h2,
  h1 = h2 ->
  forall x, fmap_data h1 x = fmap_data h2 x.
Proof using. intros. fequals. Qed.

Lemma fmap_extens : forall h1 h2,
  (forall x, fmap_data h1 x = fmap_data h2 x) ->
  h1 = h2.
Proof using. intros [f1 F1] [f2 F2] M. simpls. applys~ make_eq. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Disjointness *)

Lemma disjoint_sym : forall h1 h2,
  \# h1 h2 ->
  \# h2 h1.
Proof using. intros [f1 F1] [f2 F2]. apply map_disjoint_sym. Qed.

Lemma disjoint_comm : forall h1 h2,
  \# h1 h2 = \# h2 h1.
Proof using. lets: disjoint_sym. extens*. Qed.

Lemma disjoint_empty_l : forall h,
  \# empty h.
Proof using. intros [f F] x. simple~. Qed.

Lemma disjoint_empty_r : forall h,
  \# h empty.
Proof using. intros [f F] x. simple~. Qed.

Hint Resolve disjoint_sym disjoint_empty_l disjoint_empty_r.

Lemma disjoint_union_eq_r : forall h1 h2 h3,
  \# h1 (h2 \+ h3) =
  (\# h1 h2 /\ \# h1 h3).
Proof using.
  intros [f1 F1] [f2 F2] [f3 F3].
  unfolds disjoint, union. simpls.
  unfolds map_disjoint, map_union. extens. iff M [M1 M2].
  split; intros x; specializes M x;
   destruct (f2 x); intuition; tryfalse.
  intros x. specializes M1 x. specializes M2 x.
   destruct (f2 x); intuition.
Qed.

Lemma disjoint_union_eq_l : forall h1 h2 h3,
  \# (h2 \+ h3) h1 =
  (\# h1 h2 /\ \# h1 h3).
Proof using.
  intros. rewrite disjoint_comm.
  apply disjoint_union_eq_r.
Qed.

Lemma disjoint_single_single : forall (x1 x2:A) (v1 v2:B),
  x1 <> x2 ->
  \# (single x1 v1) (single x2 v2).
Proof using.
  introv N. intros x. simpls. do 2 case_if; auto.
Qed.

Lemma disjoint_single_single_same_inv : forall (x:A) (v1 v2:B),
  \# (single x v1) (single x v2) ->
  False.
Proof using.
  introv D. specializes D x. simpls. case_if. destruct D; tryfalse.
Qed.

Lemma disjoint_3_unfold : forall h1 h2 h3,
  \# h1 h2 h3 = (\# h1 h2 /\ \# h2 h3 /\ \# h1 h3).
Proof using. auto. Qed.

Lemma disjoint_single_set : forall h l v1 v2,
  \# (single l v1) h ->
  \# (single l v2) h.
Proof using.
  introv M. unfolds disjoint, single, map_disjoint; simpls.
  intros l'. specializes M l'. case_if~. destruct M; auto_false.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Union *)

Lemma union_self : forall h,
  h \+ h = h.
Proof using.
  intros [f F]. apply~ make_eq. simpl. intros x.
  unfold map_union. cases~ (f x).
Qed.

Lemma union_empty_l : forall h,
  empty \+ h = h.
Proof using.
  intros [f F]. unfold union, map_union, empty. simpl.
  apply~ make_eq.
Qed.

Lemma union_empty_r : forall h,
  h \+ empty = h.
Proof using.
  intros [f F]. unfold union, map_union, empty. simpl.
  apply make_eq. intros x. destruct~ (f x).
Qed.

Lemma union_eq_empty_inv_l : forall h1 h2,
  h1 \+ h2 = empty ->
  h1 = empty.
Proof using.
  intros (f1&F1) (f2&F2) M. inverts M as M.
  applys make_eq. intros l.
  unfolds map_union.
  lets: fun_eq_1 l M.
  cases (f1 l); auto_false.
Qed.

Lemma union_eq_empty_inv_r : forall h1 h2,
  h1 \+ h2 = empty ->
  h2 = empty.
Proof using.
  intros (f1&F1) (f2&F2) M. inverts M as M.
  applys make_eq. intros l.
  unfolds map_union.
  lets: fun_eq_1 l M.
  cases (f1 l); auto_false.
Qed.

Lemma union_comm_of_disjoint : forall h1 h2,
  \# h1 h2 ->
  h1 \+ h2 = h2 \+ h1.
Proof using.
  intros [f1 F1] [f2 F2] H. simpls. apply make_eq. simpl.
  intros. rewrite~ map_union_comm.
Qed.

Lemma union_comm_of_agree : forall h1 h2,
  agree h1 h2 ->
  h1 \+ h2 = h2 \+ h1.
Proof using.
  intros [f1 F1] [f2 F2] H. simpls. apply make_eq. simpl.
  intros l. specializes H l. unfolds map_union. simpls.
  cases (f1 l); cases (f2 l); auto. fequals. applys* H.
Qed.

Lemma union_assoc : forall h1 h2 h3,
  (h1 \+ h2) \+ h3 = h1 \+ (h2 \+ h3).
Proof using.
  intros [f1 F1] [f2 F2] [f3 F3]. unfolds union. simpls.
  apply make_eq. intros x. unfold map_union. destruct~ (f1 x).
Qed.

(*
Lemma union_eq_inv_of_disjoint : forall h2 h1 h1' : fmap,
  \# h1 h2 ->
  agree h1' h2 ->
  h1 \+ h2 = h1' \+ h2 ->
  h1 = h1'.
Proof using.
  intros [f2 F2] [f1 F1] [f1' F1'] D D' E.
  applys make_eq. intros x. specializes D x. specializes D' x.
  lets E': eq_inv_fmap_data_eq (rm E) x. simpls.
  unfolds map_union.
  cases (f1 x); cases (f2 x); try solve [cases (f1' x); destruct D; congruence ].
  destruct D; try false.
  rewrite H in E'. inverts E'.
  cases (f1' x); cases (f1 x);
    destruct D; try congruence.
  false.
    destruct D'; try congruence.
Qed.
*)

Lemma union_eq_inv_of_disjoint : forall h2 h1 h1',
  \# h1 h2 ->
  \# h1' h2 ->
  h1 \+ h2 = h1' \+ h2 ->
  h1 = h1'.
Proof using.
  intros [f2 F2] [f1' F1'] [f1 F1] D D' E.
  applys make_eq. intros x. specializes D x. specializes D' x.
  lets E': eq_inv_fmap_data_eq (rm E) x. simpls.
  unfolds map_union.
  cases (f1' x); cases (f1 x);
    destruct D; try congruence;
    destruct D'; try congruence.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Compatibility *)

Lemma agree_refl : forall h,
  agree h h.
Proof using.
  intros h. introv M1 M2. congruence.
Qed.

Lemma agree_sym : forall f1 f2,
  agree f1 f2 ->
  agree f2 f1.
Proof using.
  introv M. intros l v1 v2 E1 E2.
  specializes M l E1.
Qed.

Lemma agree_of_disjoint : forall h1 h2,
  disjoint h1 h2 ->
  agree h1 h2.
Proof using.
  introv HD. intros l v1 v2 M1 M2. destruct (HD l); false.
Qed.

Lemma agree_empty_l : forall h,
  agree empty h.
Proof using. intros h l v1 v2 E1 E2. simpls. false. Qed.

Lemma agree_empty_r : forall h,
  agree h empty.
Proof using.
  hint agree_sym, agree_empty_l. eauto.
Qed.

Lemma agree_union_l : forall f1 f2 f3,
  agree f1 f3 ->
  agree f2 f3 ->
  agree (f1 \+ f2) f3.
Proof using.
  introv M1 M2. intros l v1 v2 E1 E2.
  specializes M1 l. specializes M2 l.
  simpls. unfolds map_union. cases (fmap_data f1 l).
  { inverts E1. applys* M1. }
  { applys* M2. }
Qed.

Lemma agree_union_r : forall f1 f2 f3,
  agree f1 f2 ->
  agree f1 f3 ->
  agree f1 (f2 \+ f3).
Proof using.
  hint agree_sym, agree_union_l. eauto.
Qed.

Lemma agree_union_lr : forall f1 g1 f2 g2,
  agree g1 g2 ->
  \# f1 f2 (g1 \+ g2) ->
  agree (f1 \+ g1) (f2 \+ g2).
Proof using.
  introv M1 (M2a&M2b&M2c).
  rewrite disjoint_union_eq_r in *.
  applys agree_union_l; applys agree_union_r;
    try solve [ applys* agree_of_disjoint ].
  auto.
Qed.

Lemma agree_union_ll_inv : forall f1 f2 f3,
  agree (f1 \+ f2) f3 ->
  agree f1 f3.
Proof using.
  introv M. intros l v1 v2 E1 E2.
  specializes M l. simpls. unfolds map_union.
  rewrite E1 in M. applys* M.
Qed.

Lemma agree_union_rl_inv : forall f1 f2 f3,
  agree f1 (f2 \+ f3) ->
  agree f1 f2.
Proof using.
  hint agree_union_ll_inv, agree_sym. eauto.
Qed.

Lemma agree_union_lr_inv_agree_agree : forall f1 f2 f3,
  agree (f1 \+ f2) f3 ->
  agree f1 f2 ->
  agree f2 f3.
Proof using.
  introv M D. rewrite~ (@union_comm_of_agree f1 f2) in M.
  applys* agree_union_ll_inv.
Qed.

Lemma agree_union_rr_inv_agree : forall f1 f2 f3,
  agree f1 (f2 \+ f3) ->
  agree f2 f3 ->
  agree f1 f3.
Proof using.
  hint agree_union_lr_inv_agree_agree, agree_sym. eauto.
Qed.

Lemma agree_union_l_inv : forall f1 f2 f3,
  agree (f1 \+ f2) f3 ->
  agree f1 f2 ->
     agree f1 f3
  /\ agree f2 f3.
Proof using.
  (* LATER: proofs redundant with others above *)
  introv M2 M1. split.
  { intros l v1 v2 E1 E2.
    specializes M1 l v1 v2 E1. applys~ M2 l v1 v2.
    unfold union, map_union; simpl. rewrite~ E1. }
  { intros l v1 v2 E1 E2.
    specializes M1 l. specializes M2 l.
    unfolds union, map_union; simpls.
    cases (fmap_data f1 l). (* LATER: name b *)
    { applys eq_trans b. symmetry. applys~ M1. applys~ M2. }
    { auto. } }
Qed.

Lemma agree_union_r_inv : forall f1 f2 f3,
  agree f1 (f2 \+ f3) ->
  agree f2 f3 ->
     agree f1 f2
  /\ agree f1 f3.
Proof using.
  hint agree_sym.
  intros. forwards~ (M1&M2): agree_union_l_inv f2 f3 f1.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Domain *)

(* TODO: consistent renaming *)
Implicit Types s : fmap A B.
Implicit Types l : A.
Implicit Types v : B.

Lemma indom_single : forall l v,
  indom (single l v) l.
Proof using.
  intros. hnf. simpl. case_if. auto_false.
Qed.

Lemma indom_union_l : forall s1 s2 l,
  indom s1 l ->
  indom (union s1 s2) l.
Proof using.
  intros. hnf. unfold union, map_union. simpl.
  case_eq (fmap_data s1 l); auto_false.
Qed.

Lemma indom_union_r : forall s1 s2 l,
  indom s2 l ->
  indom (union s1 s2) l.
Proof using.
  intros. hnf. unfold union, map_union. simpl.
  case_eq (fmap_data s1 l); auto_false.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Disjoint and domain *)

Lemma disjoint_eq_not_indom_both : forall s1 s2,
  disjoint s1 s2 = (forall l, indom s1 l -> indom s2 l -> False).
Proof using.
  extens. iff D E.
  { introv M1 M2. destruct (D l); false*. }
  { intros l. specializes E l. unfolds indom, map_indom.
    applys not_not_inv. intros N. rew_logic in N. false*. }
Qed.

Lemma disjoint_of_not_indom_both : forall s1 s2,
  (forall l, indom s1 l -> indom s2 l -> False) ->
  disjoint s1 s2.
Proof using. introv M. rewrite~ disjoint_eq_not_indom_both. Qed.

Lemma disjoint_inv_not_indom_both : forall s1 s2 l,
  disjoint s1 s2 ->
  indom s1 l ->
  indom s2 l ->
  False.
Proof using. introv. rewrite* disjoint_eq_not_indom_both. Qed.

Lemma disjoint_single_of_not_indom : forall h l v,
  ~ indom h l ->
  disjoint (single l v) h.
Proof using.
  introv N. unfolds disjoint, map_disjoint. unfolds single, indom, map_indom.
  simpl. rew_logic in N. intros l'. case_if; subst; autos*.
Qed.

(* Remark: the reciprocal of the above lemma is a special instance of
   [disjoint_inv_not_indom_both] *)


(* ---------------------------------------------------------------------- *)
(* ** Read *)

Lemma read_single : forall {IB:Inhab B} l v,
  read (single l v) l = v.
Proof using.
  intros. unfold read, single. simpl. case_if~.
Qed.

Lemma read_union_l : forall {IB:Inhab B} s1 s2 l,
  indom s1 l ->
  read (union s1 s2) l = read s1 l.
Proof using.
  intros. unfold read, union, map_union. simpl.
  case_eq (fmap_data s1 l); auto_false.
Qed.

Lemma read_union_r : forall {IB:Inhab B} s1 s2 l,
  ~ indom s1 l ->
  read (union s1 s2) l = read s2 l.
Proof using.
  intros. unfold read, union, map_union. simpl.
  case_eq (fmap_data s1 l).
  { intros v Hv. false H. auto_false. }
  { auto_false. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Update *)

Lemma update_eq_union_single : forall s l v,
  update s l v = union (single l v) s.
Proof using. auto. Qed.

Lemma update_single : forall s l v w,
  update (single l v) l w = single l w.
Proof using.
  intros. rewrite update_eq_union_single.
  applys make_eq. intros x.
  unfold map_union, single. simpl. case_if~.
Qed.

Lemma update_union_l : forall s1 s2 l v,
  indom s1 l ->
  update (union s1 s2) l v = union (update s1 l v) s2.
Proof using.
  intros. do 2 rewrite update_eq_union_single.
  applys make_eq. intros x.
  unfold map_union, union, map_union. simpl. case_if~.
Qed.

Lemma update_union_r : forall s1 s2 l v,
  ~ indom s1 l ->
  update (union s1 s2) l v = union s1 (update s2 l v).
Proof using.
  introv M. asserts IB: (Inhab B). { applys Inhab_of_val v. }
  do 2 rewrite update_eq_union_single.
  applys make_eq. intros x.
  unfold map_union, union, map_union. simpl. case_if~.
  { subst. case_eq (fmap_data s1 x); auto_false.
    { intros w Hw. false M. auto_false. } }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Removal *)

Lemma remove_union_single_l : forall s l v,
  ~ indom s l ->
  remove (union (single l v) s) l = s.
Proof using.
  introv M. applys fmap_extens. intros x.
  unfold remove, map_remove, union, map_union, single. simpls.
  case_if. (* LATER: simplify? *)
  { destruct s as [f F]. unfolds indom, map_indom. simpls. subst. rew_logic~ in M. }
  { case_if~. }
Qed.

End FmapProp.


(* ---------------------------------------------------------------------- *)
(* ** Arguments *)

Arguments union_assoc [A] [B].
Arguments union_comm_of_disjoint [A] [B].
Arguments union_comm_of_agree [A] [B].


(* ********************************************************************** *)
(* * Tactics *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [disjoint] for proving disjointness results *)

(** [disjoint] proves goals of the form [\# h1 h2] and
    [\# h1 h2 h3] by expanding all hypotheses into binary forms
    [\# h1 h2] and then exploiting symmetry and disjointness
    with [empty]. *)

Module Export DisjointHints.
Hint Resolve disjoint_sym disjoint_empty_l disjoint_empty_r.
End DisjointHints.

Hint Rewrite
  disjoint_union_eq_l
  disjoint_union_eq_r
  disjoint_3_unfold : rew_disjoint.

Tactic Notation "rew_disjoint" :=
  autorewrite with rew_disjoint in *.
Tactic Notation "rew_disjoint" "*" :=
  rew_disjoint; auto_star.

Tactic Notation "fmap_disjoint" :=
  solve [ subst; rew_disjoint; jauto_set; auto ].

Lemma disjoint_demo : forall A B (h1 h2 h3 h4 h5:fmap A B),
  h1 = h2 \+ h3 ->
  \# h2 h3 ->
  \# h1 h4 h5 ->
  \# h3 h2 h5 /\ \# h4 h5.
Proof using.
  intros. dup 2.
  { subst. rew_disjoint. jauto_set. auto. auto. auto. auto. }
  { fmap_disjoint. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [eq] for proving equality of fmaps,
      and tactic [rew_fmap] to normalize fmap expressions. *)

Section StateEq.
Variables (A B : Type).
Implicit Types h : fmap A B.

(** [eq] proves equalities between unions of fmaps, of the form
    [h1 \+ h2 \+ h3 \+ h4 = h1' \+ h2' \+ h3' \+ h4']
    It attempts to discharge the disjointness side-conditions.
    Disclaimer: it cancels heaps at depth up to 4, but no more. *)

Lemma union_eq_cancel_1 : forall h1 h2 h2',
  h2 = h2' ->
  h1 \+ h2 = h1 \+ h2'.
Proof using. intros. subst. auto. Qed.

Lemma union_eq_cancel_1' : forall h1,
  h1 = h1.
Proof using. intros. auto. Qed.

Lemma union_eq_cancel_2 : forall h1 h1' h2 h2',
  \# h1 h1' ->
  h2 = h1' \+ h2' ->
  h1 \+ h2 = h1' \+ h1 \+ h2'.
Proof using.
  intros. subst. rewrite <- union_assoc.
  rewrite (union_comm_of_disjoint h1 h1').
  rewrite~ union_assoc. auto.
Qed.

Lemma union_eq_cancel_2' : forall h1 h1' h2,
  \# h1 h1' ->
  h2 = h1' ->
  h1 \+ h2 = h1' \+ h1.
Proof using.
  intros. subst. apply~ union_comm_of_disjoint.
Qed.

Lemma union_eq_cancel_3 : forall h1 h1' h2 h2' h3',
  \# h1 (h1' \+ h2') ->
  h2 = h1' \+ h2' \+ h3' ->
  h1 \+ h2 = h1' \+ h2' \+ h1 \+ h3'.
Proof using.
  intros. subst.
  rewrite <- (union_assoc h1' h2' h3').
  rewrite <- (union_assoc h1' h2' (h1 \+ h3')).
  apply~ union_eq_cancel_2.
Qed.

Lemma union_eq_cancel_3' : forall h1 h1' h2 h2',
  \# h1 (h1' \+ h2') ->
  h2 = h1' \+ h2' ->
  h1 \+ h2 = h1' \+ h2' \+ h1.
Proof using.
  intros. subst.
  rewrite <- (union_assoc h1' h2' h1).
  apply~ union_eq_cancel_2'.
Qed.

Lemma union_eq_cancel_4 : forall h1 h1' h2 h2' h3' h4',
  \# h1 ((h1' \+ h2') \+ h3') ->
  h2 = h1' \+ h2' \+ h3' \+ h4' ->
  h1 \+ h2 = h1' \+ h2' \+ h3' \+ h1 \+ h4'.
Proof using.
  intros. subst.
  rewrite <- (union_assoc h1' h2' (h3' \+ h4')).
  rewrite <- (union_assoc h1' h2' (h3' \+ h1 \+ h4')).
  apply~ union_eq_cancel_3.
Qed.

Lemma union_eq_cancel_4' : forall h1 h1' h2 h2' h3',
  \# h1 (h1' \+ h2' \+ h3') ->
  h2 = h1' \+ h2' \+ h3' ->
  h1 \+ h2 = h1' \+ h2' \+ h3' \+ h1.
Proof using.
  intros. subst.
  rewrite <- (union_assoc h2' h3' h1).
  apply~ union_eq_cancel_3'.
Qed.

End StateEq.

Hint Rewrite
  union_assoc
  union_empty_l
  union_empty_r : rew_fmap.

Tactic Notation "rew_fmap" :=
  autorewrite with rew_fmap in *.

Tactic Notation "rew_fmap" "~" :=
  rew_fmap; auto_tilde.

Tactic Notation "rew_fmap" "*" :=
  rew_fmap; auto_star.

Ltac fmap_eq_step tt :=
  match goal with | |- ?G => match G with
  | ?h1 = ?h1 => apply union_eq_cancel_1'
  | ?h1 \+ ?h2 = ?h1 \+ ?h2' => apply union_eq_cancel_1
  | ?h1 \+ ?h2 = ?h1' \+ ?h1 => apply union_eq_cancel_2'
  | ?h1 \+ ?h2 = ?h1' \+ ?h1 \+ ?h2' => apply union_eq_cancel_2
  | ?h1 \+ ?h2 = ?h1' \+ ?h2' \+ ?h1 => apply union_eq_cancel_3'
  | ?h1 \+ ?h2 = ?h1' \+ ?h2' \+ ?h1 \+ ?h3' => apply union_eq_cancel_3
  | ?h1 \+ ?h2 = ?h1' \+ ?h2' \+ ?h3' \+ ?h1 => apply union_eq_cancel_4'
  | ?h1 \+ ?h2 = ?h1' \+ ?h2' \+ ?h3' \+ ?h1 \+ ?h4' => apply union_eq_cancel_4
  end end.

Tactic Notation "fmap_eq" :=
  subst;
  rew_fmap;
  repeat (fmap_eq_step tt);
  try match goal with
  | |- \# _ _ => fmap_disjoint
  | |- \# _ _ _ => fmap_disjoint
  end.

Tactic Notation "fmap_eq" "~" :=
  fmap_eq; auto_tilde.

Tactic Notation "fmap_eq" "*" :=
  fmap_eq; auto_star.

Lemma fmap_eq_demo : forall A B (h1 h2 h3 h4 h5:fmap A B),
  \# h1 h2 h3 ->
  \# (h1 \+ h2 \+ h3) h4 h5 ->
  h1 = h2 \+ h3 ->
  h4 \+ h1 \+ h5 = h2 \+ h5 \+ h4 \+ h3.
Proof using.
  intros. dup 2.
  { subst. rew_fmap.
    fmap_eq_step tt. fmap_disjoint.
    fmap_eq_step tt.
    fmap_eq_step tt. fmap_disjoint. auto. }
  { fmap_eq. }
Qed.



(* ********************************************************************** *)
(** * Consecutive locations and fresh locations *)

(* ---------------------------------------------------------------------- *)
(** ** Consecutive locations *)

Fixpoint conseqs (B:Type) (l:nat) (vs:list B) : fmap nat B :=
  match vs with
  | nil => empty
  | v::vs' => (single l v) \+ (conseqs (S l) vs')
  end.

Lemma conseqs_nil : forall B (l:nat),
  conseqs l (@nil B) = empty.
Proof using. auto. Qed.

Lemma conseqs_cons : forall B (l:nat) (v:B) (vs:list B),
  conseqs l (v::vs) = (single l v) \+ (conseqs (S l) vs).
Proof using. auto. Qed.

Opaque conseqs.


(* ---------------------------------------------------------------------- *)
(** ** Consecutive locations *)

Fixpoint conseq (B:Type) (l:nat) (k:nat) (v:B) : fmap nat B :=
  match k with
  | O => empty
  | S k' => (single l v) \+ (conseq (S l) k' v)
  end.

Lemma conseq_zero : forall B (l:nat) (v:B),
  conseq l O v = empty.
Proof using. auto. Qed.

Lemma conseq_succ : forall B (l:nat) (k:nat) (v:B),
  conseq l (S k) v = (single l v) \+ (conseq (S l) k v).
Proof using. auto. Qed.

Opaque conseq.


(* ---------------------------------------------------------------------- *)
(** ** Properties of fresh consecutive locations *)

(** These lemmas are useful to prove:
    [forall h v, exists l, disjoint (single l v) h]. *)

Definition loc_fresh_gen (L : list nat) :=
  (1 + fold_right plus O L)%nat.

Lemma loc_fresh_ind : forall l L,
  mem l L ->
  (l < loc_fresh_gen L)%nat.
Proof using.
  intros l L. unfold loc_fresh_gen.
  induction L; introv M; inverts M; rew_listx.
  { math. }
  { forwards~: IHL. math. }
Qed.

Lemma loc_fresh_nat_ge : forall (L:list nat),
  exists (l:nat), forall (i:nat), ~ mem (l+i)%nat L.
Proof using.
  intros L. exists (loc_fresh_gen L). intros i M.
  lets: loc_fresh_ind M. math.
Qed.

Lemma loc_fresh_nat : forall (L:list nat),
  exists (l:nat), ~ mem l L.
Proof using.
  intros L. forwards (l&P): loc_fresh_nat_ge L.
  exists l. intros M. applys (P 0%nat). applys_eq M 2. math.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Extension of a number of consecutive fresh locations *)

Section FmapFresh.
Variables (B : Type).
Implicit Types h : fmap nat B.

Lemma exists_not_indom : forall null h,
  exists l, ~ indom h l /\ l <> null.
Proof using.
  intros null (m&(L&M)). unfold indom, map_indom. simpl.
  lets (l&F): (loc_fresh_nat (null::L)).
  exists l. split.
  { simpl. intros l'. forwards~ E: M l. }
  { intro_subst. applys~ F. }
Qed.

Lemma single_fresh : forall null h v,
  exists l, \# (single l v) h /\ l <> null.
Proof using.
  intros. forwards (l&F&N): exists_not_indom null h.
  exists l. split~. applys* disjoint_single_of_not_indom.
Qed.

Lemma conseq_fresh : forall null h k v,
  exists l, \# (conseqs l (LibList.make k v)) h /\ l <> null.
Proof using.
  intros null (m&(L&M)) k v.
  unfold disjoint, map_disjoint. simpl.
  lets (l&F): (loc_fresh_nat_ge (null::L)).
  exists l. split.
  { intros l'. gen l. induction k; intros.
    { simple~. }
    { rewrite make_succ. rewrite conseqs_cons.
      destruct (IHk (S l)%nat) as [E|?].
      { intros i N. applys F (S i). applys_eq N 2. math. }
      { simpl. unfold map_union. case_if~.
        { subst. right. applys not_not_inv. intros H. applys F 0%nat.
          constructor. math_rewrite (l'+0 = l')%nat. applys~ M. } }
      { auto. } } }
  { intro_subst. applys~ F 0%nat. rew_nat. auto. }
Qed.

Lemma disjoint_single_conseq : forall B l l' k (v:B),
  (l < l')%nat \/ (l >= l'+k)%nat ->
  \# (single l v) (conseqs l' (LibList.make k v)).
Proof using.
  introv N. gen l'. induction k; intros.
  { rewrite make_zero. rewrite~ conseqs_nil. }
  { rewrite make_succ. rewrite conseqs_cons. rew_disjoint. split.
    { applys disjoint_single_single. destruct N; math. }
    { applys IHk. destruct N. { left; math. } { right; math. } } }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Existence of nonempty heaps *)

(** This lemma is useful for constructing counterexamples. *)

Lemma exists_not_empty : forall `{IB:Inhab B},
  exists (h:fmap nat B), h <> empty.
Proof using.
  intros. sets l: 0%nat. sets h: (single l arbitrary).
  exists h. intros N.
  sets h': (empty:fmap nat B).
  asserts M1: (indom h l).
  { applys indom_single. }
  asserts M2: (~ indom h' l).
  { unfolds @indom, map_indom, @empty. simpls. auto_false. }
  rewrite N in M1. false*.
Qed.

End FmapFresh.
