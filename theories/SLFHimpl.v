(**

Separation Logic Foundations

Chapter: "Himpl".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From TLC Require Import LibCore.
From Sep Require Import Semantics.

(* TODO move *)
  Module CoercionsFromStrings.
  Coercion string_to_var (x:string) : var := x.
  End CoercionsFromStrings.
  Arguments fmap_single {A} {B}.
  Arguments fmap_union {A} {B}.
  Arguments fmap_disjoint {A} {B}.

  Import NotationForVariables NotationForTerms CoercionsFromStrings.

Close Scope fmap_scope.

From Sep Require Import SLFHprop.


(* ####################################################### *)
(** * The chapter in a rush *)

(* ******************************************************* *)
(** ** Definition of entailment *)

(** The "entailement relationship" [H1 ==> H2] asserts that any
    heap satisfying [H1] also satisfies [H2]. *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall (h:heap), H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55).

(** [H1 ==> H2] captures the fact that [H1] is a stronger precondition
    than [H2], in the sense that it is more restrictive.

    It is also useful to describe that a postcondition is stronger than
    another one, that is, that a postcondition "entails" another one.
    For that purpose, we introduce [Q1 ===> Q2], which asserts that
    for any value [v], the heap predicate [Q1 v] entails [Q2 v]. 
 
    Equivalently, [Q1 ===> Q2] holds if for any value [v] and any heap [h],
    the proposition [Q1 v h] implies [Q2 v h]. *)

Definition qimpl (Q1 Q2:val->hprop) : Prop :=
  forall (v:val), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55).

(** The entailement relation appears in particular in the consequence
    rule. *)

Lemma rule_conseq : forall t H Q H' Q',
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
  introv M WH WQ. rewrite triple_iff_triple_lowlevel in *.
  unfold triple_lowlevel in *. 
  intros h1 h2 D P1. lets P1': WH P1.
  lets M': M D P1'.
  destruct M' as (v&h1'&h3'&D'&R&HQ).
  exists v h1' h3'. splits~. applys WQ. auto.
Qed.



Parameter himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).


(* ####################################################### *)
(** * Additional exercises *)

(* ******************************************************* *)
(** ** Alternative proofs for the consequence rules. *)

(* EX2! (Hoare_conseq) *)
(** Prove the consequence rule for Hoare triples. *)

Lemma Hoare_conseq : forall t H Q H' Q',
  Hoare_triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  Hoare_triple t H Q.
Proof using.
(* SOLUTION *)
  introv M WH WQ. unfold Hoare_triple.
  intros s Ps. lets Ps': WH Ps.
  lets M': M Ps'.
  destruct M' as (v&s'&R&HQ).
  exists v s'. splits~. applys WQ. auto.
(* /SOLUTION *)
Qed.

(* EX2! (rule_conseq) *)
(** Prove the consequence rule by leveraging the lemma [Hoare_conseq],
    rather than going through the definition of [triple_lowlevel]. 
    Hint: apply lemma [Hoare_conseq] with the appropriate arguments,
    and use lemma [applys himpl_frame_l] to prove the entailments. *)

Lemma rule_conseq' : forall t H Q H' Q',
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
(* SOLUTION *)
  introv M WH WQ. unfold triple. intros H''.
  applys Hoare_conseq M. 
  { applys himpl_frame_l. applys WH. }
  { intros x. applys himpl_frame_l. applys himpl_frame_l. applys WQ. }
(* /SOLUTION *)
Qed.





From Sep Require Import SepBase.