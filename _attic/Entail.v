(**

This file formalizes entailement, written [H ==> H'], and its generalization
to postconditions, written [Q ===> Q'].

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Export Semantics.
Open Scope fmap_scope.


(* ********************************************************************** *)
(** * Entailment *)

(** The definition of entailment is polymorphic in the type of heaps,
    which could be state, but also more elaborated structures in
    extensions of Separation Logic (e.g. with time credits). *)


(* ---------------------------------------------------------------------- *)
(* ** Predicate extensionality, specialized to heap predicates *)

(** Predicate extensionality follows from functional extensional
    and propositional extensionality, which we take as axiom
    (in TLC's LibAxioms file). *)

Lemma hprop_extens : forall A (H1 H2:A->Prop),
  (forall h, H1 h <-> H2 h) ->
  (H1 = H2).
Proof using.
  introv M. applys fun_ext_1. intros h. applys* prop_ext.
Qed.

(* ---------------------------------------------------------------------- *)
(* ** Definition of entailment *)

(** [H1 ==> H2] is defined as [forall h, H1 h -> H2 h]. *)

Definition himpl A (H1 H2:A->Prop) :=
  forall x, H1 x -> H2 x.

Notation "H1 ==> H2" := (himpl H1 H2)
  (at level 55) : heap_scope.

(** [Q1 ===> Q2] is defined as [forall x h, Q1 x h -> Q2 x h].
    It is thus equivalent to [forall x, Q1 x ==> Q2 x].
    Thus, invoking [intro] on a [===>] goal leaves a [==>] goal. *)

Definition qimpl A B (Q1 Q2:A->B->Prop) :=
  forall r, himpl (Q1 r) (Q2 r).

Notation "Q1 ===> Q2" := (qimpl Q1 Q2)
  (at level 55) : heap_scope.

Open Scope heap_scope.


(* ---------------------------------------------------------------------- *)
(* ** Properties of entailment *)

Section HimplProp.
Variable A : Type.
Implicit Types H : A -> Prop.

Hint Unfold himpl.

(** Entailment is reflexive, symmetric, transitive *)

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. intros h. auto. Qed.

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

(** Paragraphe of the definition, used by tactics *)

Lemma himpl_inv : forall H1 H2 (h:A),
  (H1 ==> H2) ->
  (H1 h) ->
  (H2 h).
Proof using. auto. Qed.

(** Reformulation of reflexivity, used by tactics *)

Lemma himpl_of_eq : forall H1 H2,
  H1 = H2 ->
  H1 ==> H2.
Proof. intros. subst. applys~ himpl_refl. Qed.

Lemma himpl_of_eq_sym : forall H1 H2,
  H1 = H2 ->
  H2 ==> H1.
Proof. intros. subst. applys~ himpl_refl. Qed.

End HimplProp.

Arguments himpl_of_eq [A] [H1] [H2].
Arguments himpl_of_eq_sym [A] [H1] [H2].
Arguments himpl_antisym [A] [H1] [H2].

Hint Resolve himpl_refl.

(** Reflexivity for postconditions *)

Lemma qimpl_refl : forall A B (Q:A->B->Prop),
  Q ===> Q.
Proof using. intros. hnfs*. Qed.

Hint Resolve qimpl_refl.


