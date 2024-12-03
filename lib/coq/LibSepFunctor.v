(**

This file formalizes a functor that may be instantiated con construct, e.g.
  -- a standard Separation Logic,
  -- a Separation Logic extended with credits,
  -- a Separation Logic extended with temporary read-only permissions.

The functor in this file assumes:
- a type for heaps
- a definition of \[P] (lifting of pure predicates) and of \* (star)
- five properties of these operators
  (neutral element, commutativity and associativity of star,
   extrusion of existentials, and frame property for entailment).

The functor also provides:

- derived heap operators: \[], (\exists _,_), \Top
- a number of useful lemmas for reasoning about these operators
- notation for representation predicates: [x ~> R X].

- [rew_heap] normalizes heap predicate expressions
- [xpull] extracts existentials and pure facts from LHS of entailments
- [xsimpl] simplifies heap entailments (it calls [xpull] first)
- [xsimplh] uses [xsimpl] to solves goal of the form [X: H h, ... |- H' h]
- [xchange] performs transitivity steps in entailments, modulo frame

- [xtpull] extracts existentials and pure facts from preconditions.
- [xtchange] performs transitivity steps in preconditions.
- [xapply] applies a lemma (triple or characteristic formula) modulo
  frame and weakening.
- [xunfold] unfolds representation predicates of the form [x ~> R X]

- [xtpulls] is like [xtpull] but performs one substitution automatically.
- [xtchanges] is like [xtchange] but calls [xsimpl] to simplify subgoals.
- [xapplys] is like [xapply] but calls [xsimpl] to simplify subgoals.

- [mklocal F] is a predicate transformer used by characteristic formulae.
- [local F], where [F] is typically a triple or a characteristic formula,
  asserts that [F] can be subject to frame, weakening, and extraction
  of existentials and pure facts from preconditions. Tactics such as
  [xapply] apply the frame rule in a generic manner, and produce a
  [local] subgoal as side-condition.
- [xlocal] automatically discharges goals of the form [local F].

Author: Arthur Charguéraud, with contributions from Jacques-Henri Jourdan.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From TLC Require Export LibCore.
From TLC Require Import LibMonoid.
From CFML Require Export LibSepTLCbuffer LibSepSimpl.


(* ********************************************************************** *)
(** * Assumptions of the functor *)

Module Type SepCore.

Declare Scope heap_scope.

(* ---------------------------------------------------------------------- *)
(* ** Axiomatization of Heap Operators *)

(** Type of heaps *)

Parameter heap : Type.

(** Empty heap *)

Parameter heap_empty : heap.

(** Compatibility of two heaps *)

Parameter heap_compat : heap -> heap -> Prop.

(** Union of two compatible heaps *)

Parameter heap_union : heap -> heap -> heap.

Declare Scope heap_union_scope.

Notation "h1 \u h2" := (heap_union h1 h2)
   (at level 37, right associativity) : heap_union_scope.

Open Scope heap_union_scope.

(** Affine heaps *)

Parameter heap_affine : heap -> Prop.

(** Symmetry of [heap_compat] *)

Parameter heap_compat_sym : forall h1 h2,
  heap_compat h1 h2 ->
  heap_compat h2 h1.

(** [heap_compat] on [heap_empty] *)

Parameter heap_compat_empty_l : forall h,
  heap_compat heap_empty h.

(** [heap_compat] on [heap_union] *)

Parameter heap_compat_union_l_eq: forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat (h1 \u h2) h3 = (heap_compat h1 h3 /\ heap_compat h2 h3).

(** [heap_union] neutral, commutativity, and asociativity *)

Parameter heap_union_empty_l : forall h,
  heap_empty \u h = h.

Parameter heap_union_comm : forall h1 h2,
  heap_compat h1 h2 ->
  h1 \u h2 = h2 \u h1.

Parameter heap_union_assoc : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h2 h3 ->
  heap_compat h1 h3 ->
  (h1 \u h2) \u h3 = h1 \u (h2 \u h3).

(** Distribution of [heap_affine] on empty and union. *)

Parameter heap_affine_empty :
  heap_affine heap_empty.

Parameter heap_affine_union : forall h1 h2,
  heap_affine h1 ->
  heap_affine h2 ->
  heap_compat h1 h2 ->
  heap_affine (h1 \u h2).

End SepCore.


(* ********************************************************************** *)
(** * Assumptions of the functor with credits *)

Module Type SepCoreCredits.

Include SepCore.

Parameter use_credits : bool.

Notation "'credits'" := Z.

Parameter heap_credits : credits -> heap.

Parameter heap_compat_credits : forall n m,
  heap_compat (heap_credits n) (heap_credits m).

Parameter heap_credits_skip :
  use_credits = false ->
  forall n, heap_credits n = heap_empty.

Parameter heap_credits_zero :
  heap_credits 0 = heap_empty.

Parameter heap_credits_add : forall n m,
  heap_credits (n + m) = heap_union (heap_credits n) (heap_credits m).

Parameter heap_credits_affine : forall n,
  n >= 0 ->
  heap_affine (heap_credits n).

End SepCoreCredits.



(* ********************************************************************** *)
(** * Definition of heap predicates *)

Module SepSetupCredits (SH : SepCoreCredits).

Module Export SepSimplArgsCredits.

Include SH.

Open Scope heap_scope.

Implicit Types h : heap.
Implicit Types P : Prop.


(* ---------------------------------------------------------------------- *)
(* ** Heap Predicates and Entailment *)

(** Type of heap predicates *)

Definition hprop := heap -> Prop.

Implicit Types H : hprop.

Global Instance Inhab_hprop : Inhab hprop.
Proof using. intros. apply (Inhab_of_val (fun _ => True)). Qed.

(** Entailment for heap predicates *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall (h:heap), H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55) : heap_scope.

Local Open Scope heap_scope.

(** Entailment for postconditions *)

Definition qimpl A (Q1 Q2:A->hprop) : Prop :=
  forall (v:A), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55) : heap_scope.

(** Properties of entailment *)

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. introv M. auto. Qed.

Hint Resolve himpl_refl.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using. introv M1 M2. intros h H1h. eauto. Qed.

Lemma himpl_trans' : forall H2 H1 H3,
  (H2 ==> H3) ->
  (H1 ==> H2) ->
  (H1 ==> H3).
Proof using. intros. applys* himpl_trans H2. Qed.

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  (H1 = H2).
Proof using. introv M1 M2. applys pred_ext_1. intros h. iff*. Qed.

(** Additional properties of [himpl] *)

(* --TODO: is this lemma really needed? *)
Lemma himpl_forall_trans : forall H1 H2,
  (forall H, H ==> H1 -> H ==> H2) ->
  H1 ==> H2.
Proof using. introv M. applys~ M. Qed.

Lemma himpl_inv : forall H1 H2 h,
  (H1 ==> H2) ->
  (H1 h) ->
  (H2 h).
Proof using. auto. Qed.

(** Properties of entailment for postconditions *)

Lemma qimpl_refl : forall A (Q:A->hprop),
  Q ===> Q.
Proof using. intros A Q v. applys himpl_refl. Qed.

Lemma qimpl_trans : forall A (Q2 Q1 Q3:A->hprop),
  (Q1 ===> Q2) ->
  (Q2 ===> Q3) ->
  (Q1 ===> Q3).
Proof using. introv M1 M2. intros v. applys* himpl_trans. Qed.

Lemma qimpl_antisym : forall A (Q1 Q2:A->hprop),
  (Q1 ===> Q2) ->
  (Q2 ===> Q1) ->
  (Q1 = Q2).
Proof using.
  introv M1 M2. applys fun_ext_1. intros v. applys* himpl_antisym.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Core Operators *)

(** Empty heap predicate *)

Definition hempty : hprop :=
  fun h => h = heap_empty.

Notation "\[]" := (hempty)
  (at level 0) : heap_scope.

(** Star *)

Definition hstar (H1 H2 : hprop) : hprop :=
  fun h => exists h1 h2,
               H1 h1
            /\ H2 h2
            /\ heap_compat h1 h2
            /\ h = heap_union h1 h2.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : heap_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : heap_scope.

(** Quantifiers *)

Definition hexists A (J:A->hprop) : hprop :=
  fun h => exists x, J x h.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'") : heap_scope.

Definition hforall (A : Type) (J : A -> hprop) : hprop :=
  fun h => forall x, J x h.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : heap_scope.

(** Pure propositions lifted to heap predicates,
  written [ \[P] ].

  Remark: the definition below is equivalent to
  [fun h => (hempty h /\ P)]. *)

Definition hpure (P:Prop) : hprop :=
  hexists (fun (p:P) => hempty).

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]") : heap_scope.

(** Magic wand, written [H1 \-* H2] *)

Definition hwand (H1 H2 : hprop) : hprop :=
  hexists (fun (H:hprop) => H \* (hpure (H1 \* H ==> H2))).

Notation "H1 \-* H2" := (hwand H1 H2)
  (at level 43, right associativity) : heap_scope.

(** Magic wand for postconditions, written [Q1 \--* Q2] *)

Definition qwand A (Q1 Q2:A->hprop) : hprop :=
  hforall (fun x => hwand (Q1 x) (Q2 x)).

Notation "Q1 \--* Q2" := (qwand Q1 Q2)
  (at level 43) : heap_scope.

Open Scope heap_scope.
Delimit Scope heap_scope with hprop.

(** Disjunction, equivalent to [fun h => H1 h \/ H2 h] *)

Definition hor (H1 H2 : hprop) : hprop :=
  \exists (b:bool), if b then H1 else H2.

(** Non-separating conjunction, equivalent to [fun h => H1 h /\ H2 h] *)

Definition hand (H1 H2 : hprop) : hprop :=
  \forall (b:bool), if b then H1 else H2.

(** The "Top" predicate, written [\Top], which holds of any heap,
  implemented as [\exists H, H]. *)

Definition htop : hprop :=
  hexists (fun (H:hprop) => H).

Notation "\Top" := (htop) : heap_scope.

(** Affinity *)

Definition haffine (H : hprop) : Prop :=
  forall h, H h -> heap_affine h.

(** Affinity for postconditions *)

Definition haffine_post (A:Type) (J:A->hprop) : Prop :=
  forall x, haffine (J x).

(** The "GC" predicate, written [\GC], which holds of any heap,
  implemented as [\exists H, \[affine H] \* H]. *)

Definition hgc : hprop :=
  \exists H, \[haffine H] \* H.

Notation "\GC" := (hgc) : heap_scope.

(** Credits, written [\$ n] *)

Definition hcredits (n:credits) : hprop :=
  fun h => h = heap_credits n.

Notation "'\$' n" := (hcredits n)
  (at level 40,
   n at level 0,
   format "\$ n") : heap_scope.

(** Additional notation for entailment
    [H1 ==+> H2] is short for [H1 ==> H1 \* H2] *)

Declare Scope heap_scope_ext.

Notation "H1 ==+> H2" := (H1%hprop ==> hstar H1%hprop H2%hprop)
  (at level 55, only parsing) : heap_scope_ext.


(* ---------------------------------------------------------------------- *)
(* ** Derived properties of operations on heaps *)

Lemma heap_compat_sym_eq : forall h1 h2,
  heap_compat h1 h2 = heap_compat h2 h1.
Proof using. hint heap_compat_sym. extens. iff*. Qed.

Lemma heap_compat_empty_r : forall h,
  heap_compat h heap_empty.
Proof using. autos* heap_compat_sym heap_compat_empty_l. Qed.

Lemma heap_union_empty_r : forall h,
  h \u heap_empty = h.
Proof using.
  intros. rewrite* heap_union_comm. apply* heap_union_empty_l.
  applys* heap_compat_empty_r.
Qed.

Lemma heap_compat_union_r_eq: forall h1 h2 h3,
  heap_compat h2 h3 ->
  heap_compat h1 (h2 \u h3) = (heap_compat h1 h2 /\ heap_compat h1 h3).
Proof using.
  introv M. rewrite heap_compat_sym_eq. rewrite* heap_compat_union_l_eq.
  rewrite (heap_compat_sym_eq h2). rewrite* (heap_compat_sym_eq h3).
Qed.

Lemma heap_compat_union_l : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h1 h3 ->
  heap_compat h2 h3 ->
  heap_compat (h1 \u h2) h3.
Proof using. introv M1 M2 M3. rewrite* heap_compat_union_l_eq. Qed.

Lemma heap_compat_union_r : forall h1 h2 h3,
  heap_compat h1 h2 ->
  heap_compat h1 h3 ->
  heap_compat h2 h3 ->
  heap_compat h1 (h2 \u h3).
Proof using. hint heap_compat_sym, heap_compat_union_l. autos*. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Tactic *)

Hint Rewrite heap_union_empty_l heap_union_empty_r heap_union_assoc : rew_heaps.

Tactic Notation "rew_heaps" :=
  autorewrite with rew_heaps.
Tactic Notation "rew_heaps" "in" hyp(H) :=
  autorewrite with rew_heaps in H.
Tactic Notation "rew_heaps" "in" "*" :=
  autorewrite with rew_heaps in *.

Tactic Notation "rew_heaps" "~" :=
  rew_heaps; auto_tilde.
Tactic Notation "rew_heaps" "~" "in" hyp(H) :=
  rew_heaps in H; auto_tilde.
Tactic Notation "rew_heaps" "~" "in" "*" :=
  rew_heaps in *; auto_tilde.

Tactic Notation "rew_heaps" "*" :=
  rew_heaps; auto_star.
Tactic Notation "rew_heaps" "*" "in" hyp(H) :=
  rew_heaps in H; auto_star.
Tactic Notation "rew_heaps" "*" "in" "*" :=
  rew_heaps in *; auto_star.


(* ---------------------------------------------------------------------- *)
(* ** Introduction and Inversion Lemmas for Core Heap Predicates *)

(** Core heap predicates *)

Lemma hempty_intro :
  \[] heap_empty.
Proof using. hnfs~. Qed.

Lemma hempty_inv : forall h,
  \[] h ->
  h = heap_empty.
Proof using. introv M. auto. Qed.

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  heap_compat h1 h2 ->
  (H1 \* H2) (h1 \u h2).
Proof using. intros. exists~ h1 h2. Qed.

Lemma hstar_inv : forall H1 H2 h,
  (H1 \* H2) h ->
  exists h1 h2, H1 h1 /\ H2 h2 /\ heap_compat h1 h2 /\ h = h1 \u h2.
Proof using. introv M. hnf in M. eauto. Qed.

Lemma hexists_intro : forall A (J:A->hprop) x h,
  J x h ->
  (hexists J) h.
Proof using. introv M. exists~ x. Qed.

Lemma hexists_inv : forall A (J:A->hprop) h,
  (hexists J) h ->
  exists x, J x h.
Proof using. introv M. hnf in M. eauto. Qed.

Lemma hforall_intro : forall A (J:A->hprop) h,
  (forall x, J x h) ->
  (hforall J) h.
Proof using. introv M. applys* M. Qed.

Lemma hforall_inv : forall A (J:A->hprop) h,
  (hforall J) h ->
  forall x, J x h.
Proof using. introv M. applys* M. Qed.

(** Derived heap predicates *)

Lemma hpure_intro : forall P,
  P ->
  \[P] heap_empty.
Proof using. introv M. exists*. apply hempty_intro. Qed.

Lemma hpure_inv : forall P h,
  \[P] h ->
  P /\ h = heap_empty.
Proof using. introv (p&M). split*. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Proving core properties of operators *)

(** Lemmas from this section should be the last ones to access the
    internal definition of the operators hempty and hstar. *)

Section CoreProperties.
Hint Resolve heap_compat_empty_l heap_compat_empty_r
  heap_union_empty_l heap_union_empty_r hempty_intro
  heap_compat_union_l heap_compat_union_r.

(** Empty is left neutral for star *)

Lemma hstar_hempty_l : forall H,
  \[] \* H = H.
Proof using.
  intros. applys pred_ext_1. intros h.
  iff (h1&h2&M1&M2&D&->) M.
  { rewrite (hempty_inv M1). rew_heaps*. }
  { exists~ heap_empty h. }
Qed.

(** Star is commutative *)

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof using.
  hint heap_union_comm, heap_compat_sym.
  intros. unfold hstar. extens. intros h.
  iff (h1&h2&M1&M2&D&U).
  { exists h2 h1. subst~. }
  { exists h2 h1. subst~. }
Qed.

(** Star is associative *)

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using.
  hint heap_compat_union_r, heap_compat_union_l, hstar_intro.
  intros. extens. intros h. split.
  { intros (h'&h3&(h1&h2&M2&P1&P2&->)&M3&M1&->).
    rewrite* heap_compat_union_l_eq in M1.
    exists* h1 (h2 \u h3). rewrite* heap_union_assoc. }
  { intros (h1&h'&P1&(h2&h3&M2&P2&P3&->)&M1&->).
    rewrite* heap_compat_union_r_eq in M1.
    exists* (h1 \u h2) h3. rewrite* heap_union_assoc. }
Qed.

(** Extrusion of existentials out of star *)

Lemma hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof using.
  hint hexists_intro.
  intros. applys pred_ext_1. intros h. iff M.
  { destruct M as (h1&h2&(x&M1)&M2&D&U). exists* x h1 h2. }
  { destruct M as (x&(h1&h2&M1&M2&D&U)). exists* h1 h2. }
Qed.

(** Extrusion of foralls out of star *)

Lemma hstar_hforall : forall H A (J:A->hprop),
  (hforall J) \* H ==> hforall (J \*+ H).
Proof using.
  intros. intros h M. destruct M as (h1&h2&M1&M2&D&U).
  intros x. exists~ h1 h2.
Qed.

(** The frame property (star on H2) holds for entailment *)

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof using. introv W (h1&h2&?). exists* h1 h2. Qed.

(** Properties of [haffine] *)

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

(** Properties of [hpure] *)

Lemma hstar_hpure_l : forall P H h,
  (\[P] \* H) h = (P /\ H h).
Proof using.
  intros. extens. unfold hpure.
  rewrite hstar_hexists.
  rewrite* hstar_hempty_l.
  iff (p&M) (p&M). { split~. } { exists~ p. }
Qed.

End CoreProperties.

Global Opaque hempty hpure hstar hexists.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [hstar] *)

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof using.
  applys neutral_r_of_comm_neutral_l.
  applys~ hstar_comm.
  applys~ hstar_hempty_l.
Qed.

Lemma himpl_frame_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1 \* H2').
Proof using.
  introv M. do 2 rewrite (@hstar_comm H1). applys~ himpl_frame_l.
Qed.

Lemma himpl_frame_lr : forall H1 H1' H2 H2',
  H1 ==> H1' ->
  H2 ==> H2' ->
  (H1 \* H2) ==> (H1' \* H2').
Proof using.
  introv M1 M2. applys himpl_trans. applys~ himpl_frame_l M1. applys~ himpl_frame_r.
Qed.

Lemma himpl_hstar_trans_l : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H2 \* H3 ==> H4 ->
  H1 \* H3 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans' M2. applys himpl_frame_l M1.
Qed.

Lemma himpl_hstar_trans_r : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H3 \* H2 ==> H4 ->
  H3 \* H1 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans' M2. applys himpl_frame_r M1.
Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of [hpure] *)

Lemma hstar_hpure_r : forall P H h,
  (H \* \[P]) h = (H h /\ P).
Proof using.
  intros. rewrite hstar_comm. rewrite hstar_hpure_l. apply* prop_ext.
Qed.

(* backward compatibility *)
Definition hstar_hpure := hstar_hpure_l.

  (* corollary only used for the SL course *)
Lemma hstar_hpure_iff : forall P H h,
  (\[P] \* H) h <-> (P /\ H h).
Proof using. intros. rewrite* hstar_hpure. Qed.

Lemma himpl_hstar_hpure_r : forall P H H',
  P ->
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof using.
  introv HP W. intros h K. rewrite* hstar_hpure.
  (* derivable, nevertheless useful to have here...
  introv HP W. rewrite <- (hstar_hempty_l H).
  applys himpl_frame_lr W. applys~ himpl_hempty_hpure. *)
Qed.

Lemma hpure_inv_hempty : forall P h,
  \[P] h ->
  P /\ \[] h.
Proof using.
  introv M. rewrite <- hstar_hpure.
  rewrite~ hstar_hempty_r.
Qed.

Lemma hpure_intro_hempty : forall P h,
  \[] h ->
  P ->
  \[P] h.
Proof using.
  introv M N. rewrite <- (hstar_hempty_l \[P]).
  rewrite hstar_comm. rewrite~ hstar_hpure.
Qed.

Lemma himpl_hempty_hpure : forall P,
  P ->
  \[] ==> \[P].
Proof using. introv HP. intros h Hh. applys* hpure_intro_hempty. Qed.

Lemma himpl_hstar_hpure_l : forall P H H',
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.
Proof using.
  introv W Hh. rewrite hstar_hpure in Hh. applys* W.
Qed.

Lemma hempty_eq_hpure_true :
  \[] = \[True].
Proof using.
  applys pred_ext_1. intros h. iff M.
  { applys* hpure_intro_hempty. }
  { forwards*: hpure_inv_hempty M. }
Qed.

Lemma hfalse_hstar_any : forall H,
  \[False] \* H = \[False].
Proof using.
  intros. applys pred_ext_1. intros h. rewrite hstar_hpure. iff M.
  { false*. } { lets: hpure_inv_hempty M. false*. }
Qed.

Lemma hpure_eq_hexists_empty : forall P,
  \[P] = (\exists (p:P), \[]).
Proof using. auto. Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of [hexists] *)

Lemma himpl_hexists_l : forall A H (J:A->hprop),
  (forall x, J x ==> H) ->
  (hexists J) ==> H.
Proof using. introv W. intros h (x&Hh). applys* W. Qed.

Lemma himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (hexists J).
Proof using. introv W. intros h. exists x. apply~ W. Qed.

Lemma himpl_hexists : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hexists J1 ==> hexists J2.
Proof using.
  introv W. applys himpl_hexists_l. intros x. applys himpl_hexists_r W.
Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of [hforall] *)

Lemma himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (hforall J).
Proof using. introv M. intros h Hh x. apply~ M. Qed.

Lemma himpl_hforall_l : forall A x (J:A->hprop) H,
  (J x ==> H) ->
  (hforall J) ==> H.
Proof using. introv M. intros h Hh. apply~ M. Qed.

Lemma himpl_hforall_l_exists : forall A (J:A->hprop) H,
  (exists x, J x ==> H) ->
  (hforall J) ==> H.
Proof using. introv (x&M). applys* himpl_hforall_l. Qed.

Lemma himpl_hforall : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hforall J1 ==> hforall J2.
Proof using.
  introv W. applys himpl_hforall_r. intros x. applys himpl_hforall_l W.
Qed.

Lemma hforall_specialize : forall A (x:A) (J:A->hprop),
  (hforall J) ==> (J x).
Proof using. intros. applys* himpl_hforall_l x. Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of hwand (others are found further in the file) *)

Lemma hwand_eq_hexists : forall H1 H2,
  (H1 \-* H2) = (\exists H, H \* \[H1 \* H ==> H2]).
Proof using. auto. Qed.

Lemma hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 \-* H2) <-> (H1 \* H0 ==> H2).
Proof using.
  unfold hwand. iff M.
  { rewrite hstar_comm. applys himpl_hstar_trans_l (rm M).
    rewrite hstar_hexists. applys himpl_hexists_l. intros H.
    rewrite (hstar_comm H). rewrite hstar_assoc.
    rewrite (hstar_comm H H1). applys~ himpl_hstar_hpure_l. }
  { applys himpl_hexists_r H0.
    rewrite <- (hstar_hempty_r H0) at 1.
    applys himpl_frame_r. applys himpl_hempty_hpure M. }
Qed.

Lemma himpl_hwand_r : forall H1 H2 H3,
  H2 \* H1 ==> H3 ->
  H1 ==> (H2 \-* H3).
Proof using. introv M. rewrite~ hwand_equiv. Qed.

Lemma himpl_hwand_r_inv : forall H1 H2 H3,
  H1 ==> (H2 \-* H3) ->
  H2 \* H1 ==> H3.
Proof using. introv M. rewrite~ <- hwand_equiv. Qed.

Lemma hwand_cancel : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.
Proof using. intros. rewrite~ <- hwand_equiv. Qed.

Arguments hwand_cancel : clear implicits.

Lemma himpl_hempty_hwand_same : forall H,
  \[] ==> (H \-* H).
Proof using. intros. rewrite hwand_equiv. rewrite~ hstar_hempty_r. Qed.

Lemma hwand_hempty_l : forall H,
  (\[] \-* H) = H.
Proof using.
  intros. applys himpl_antisym.
  { rewrite <- (hstar_hempty_l (\[] \-* H)). applys hwand_cancel. }
  { rewrite hwand_equiv. rewrite~ hstar_hempty_l. }
Qed.

Lemma hwand_hpure_l : forall P H,
  P ->
  (\[P] \-* H) = H.
Proof using.
  introv HP. applys himpl_antisym.
  { lets K: hwand_cancel \[P] H. applys himpl_trans' K.
    applys* himpl_hstar_hpure_r. }
  { rewrite hwand_equiv. applys* himpl_hstar_hpure_l. }
Qed.

Arguments hwand_hpure_l : clear implicits.

Lemma hwand_curry : forall H1 H2 H3,
  (H1 \* H2) \-* H3 ==> H1 \-* (H2 \-* H3).
Proof using.
  intros. apply himpl_hwand_r. apply himpl_hwand_r.
  rewrite <- hstar_assoc. rewrite (hstar_comm H1 H2).
  applys hwand_cancel.
Qed.

Lemma hwand_uncurry : forall H1 H2 H3,
  H1 \-* (H2 \-* H3) ==> (H1 \* H2) \-* H3.
Proof using.
  intros. rewrite hwand_equiv. rewrite (hstar_comm H1 H2).
  rewrite hstar_assoc. applys himpl_hstar_trans_r.
  { applys hwand_cancel. } { applys hwand_cancel. }
Qed.

Lemma hwand_curry_eq : forall H1 H2 H3,
  (H1 \* H2) \-* H3 = H1 \-* (H2 \-* H3).
Proof using.
  intros. applys himpl_antisym.
  { applys hwand_curry. }
  { applys hwand_uncurry. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of [qwand] *)

Lemma qwand_equiv : forall H A (Q1 Q2:A->hprop),
  H ==> (Q1 \--* Q2) <-> (Q1 \*+ H) ===> Q2.
Proof using.
  unfold qwand. iff M.
  { intros x. rewrite hstar_comm. applys himpl_hstar_trans_l (rm M).
    applys himpl_trans. applys hstar_hforall. simpl.
    applys himpl_hforall_l x. rewrite hstar_comm. applys hwand_cancel. }
  { applys himpl_hforall_r. intros x. rewrite* hwand_equiv. }
Qed.

Lemma himpl_qwand_r : forall A (Q1 Q2:A->hprop) H,
  Q1 \*+ H ===> Q2 ->
  H ==> (Q1 \--* Q2).
Proof using. introv M. rewrite~ qwand_equiv. Qed.

Arguments himpl_qwand_r [A].

Lemma qwand_specialize : forall A (x:A) (Q1 Q2:A->hprop),
  (Q1 \--* Q2) ==> (Q1 x \-* Q2 x).
Proof using. intros. applys* himpl_hforall_l x. Qed.

Arguments qwand_specialize [ A ].


(* ---------------------------------------------------------------------- *)
(** Properties of [htop] *)

Lemma htop_intro : forall h,
  \Top h.
Proof using. intros. unfold htop. applys* hexists_intro (=h). Qed.

Lemma himpl_htop_r : forall H,
  H ==> \Top.
Proof using. intros. intros h Hh. applys* htop_intro. Qed.

Lemma htop_eq :
  \Top = (\exists H, H).
Proof using. auto. Qed.

Lemma hstar_htop_htop :
  \Top \* \Top = \Top.
Proof using.
  applys himpl_antisym.
  { applys himpl_htop_r. }
  { rewrite <- (hstar_hempty_r \Top) at 1. applys himpl_frame_r.
    applys himpl_htop_r. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [haffine] *)

Lemma haffine_eq : forall H,
  haffine H = (forall h, H h -> heap_affine h).
Proof using. auto. Qed.

Lemma haffine_hexists : forall A (J:A->hprop),
  haffine_post J ->
  haffine (hexists J).
Proof using. introv F1 (x&Hx). applys* F1. Qed.

Lemma haffine_hforall : forall A `{Inhab A} (J:A->hprop),
  haffine_post J ->
  haffine (hforall J).
Proof using. introv IA F1 Hx. applys* F1 (arbitrary (A:=A)). Qed.

Lemma haffine_hpure : forall P,
  haffine \[P].
Proof using.
  intros. rewrite hpure_eq_hexists_empty. applys haffine_hexists.
  intros HP. applys* haffine_hempty.
Qed.

Lemma haffine_hgc :
  haffine \GC.
Proof using.
  applys haffine_hexists. intros H h Hh. rewrite hstar_hpure in Hh.
  destruct Hh as [M N]. applys* M.
Qed.

Transparent haffine. (* TODO: remove? *)

Lemma haffine_hstar_hpure_l : forall (P:Prop) H,
  (P -> haffine H) ->
  haffine (\[P] \* H).
Proof using.
  introv M. intros h N. rewrite hstar_hpure_l in N. applys* M.
Qed.


(* ---------------------------------------------------------------------- *)
(** Properties of hgc *)

Lemma hgc_eq :
  \GC = (\exists H, \[haffine H] \* H).
Proof using. auto. Qed.

Lemma hgc_of_heap_affine : forall h,
  heap_affine h ->
  \GC h.
Proof using.
  intros. rewrite hgc_eq. exists (=h).
  rewrite hstar_hpure. split~. { introv ->. auto. }
Qed.

Lemma himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.
Proof using.
  introv M. rewrite hgc_eq. applys himpl_hexists_r H.
  applys~ himpl_hstar_hpure_r.
  (* low-level: [intros h K. applys hgc_of_heap_affine. applys M K. *)
Qed.

Lemma hempty_himpl_hgc :
  \[] ==> \GC.
Proof using. applys himpl_hgc_r. applys haffine_hempty. Qed.

Lemma himpl_same_hstar_hgc_r : forall H,  (* needed? *)
  H ==> H \* \GC.
Proof using.
  intros. (* himpl_frame_r *)
  rewrite hstar_comm. rewrite <- (hstar_hempty_l H) at 1.
  applys himpl_frame_l. applys himpl_hgc_r. applys haffine_hempty.
Qed.

Lemma himpl_hstar_hgc_r : forall H H', (* needed? *)
  H ==> H' ->
  H ==> H' \* \GC.
Proof using.
  introv M. applys himpl_trans (rm M). applys himpl_same_hstar_hgc_r.
Qed.

Lemma hstar_hgc_hgc :
  \GC \* \GC = \GC. (* --TODO : can be simplified *)
Proof using.
  applys himpl_antisym.
  { applys himpl_hgc_r. applys haffine_hstar; applys haffine_hgc. }
  { rewrite <- hstar_hempty_l at 1. applys himpl_frame_l. applys hempty_himpl_hgc. }
Qed.

Lemma hgc_eq_htop_of_haffine_any :
  (forall H, haffine H) ->
  \GC = \Top.
Proof using.
  introv M. applys himpl_antisym.
  { applys himpl_htop_r. }
  { applys himpl_hgc_r. applys M. }
Qed.

Global Opaque haffine hgc.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [hor] *)

Lemma hor_eq_exists_bool : forall H1 H2,
  hor H1 H2 = \exists (b:bool), if b then H1 else H2.
Proof using. auto. Qed.

Lemma hor_sym : forall H1 H2,
  hor H1 H2 = hor H2 H1.
Proof using.
  intros. unfold hor. applys himpl_antisym.
  { applys himpl_hexists_l. intros b.
    applys himpl_hexists_r (neg b). destruct* b. }
  { applys himpl_hexists_l. intros b.
    applys himpl_hexists_r (neg b). destruct* b. }
Qed.

Lemma himpl_hor_r_r : forall H1 H2,
  H1 ==> hor H1 H2.
Proof using. intros. unfolds hor. exists* true. Qed.

Lemma himpl_hor_r_l : forall H1 H2,
  H2 ==> hor H1 H2.
Proof using. intros. unfolds hor. exists* false. Qed.

Lemma himpl_hor_l : forall H1 H2 H3,
  H1 ==> H3 ->
  H2 ==> H3 ->
  hor H1 H2 ==> H3.
Proof using.
  introv M1 M2. unfolds hor. applys himpl_hexists_l. intros b. case_if*.
Qed.

Global Opaque hor.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [hand] *)

Lemma hand_eq_forall_bool : forall H1 H2,
  hand H1 H2 = \forall (b:bool), if b then H1 else H2.
Proof using. auto. Qed.

Lemma hand_sym : forall H1 H2,
  hand H1 H2 = hand H2 H1.
Proof using.
  intros. unfold hand. applys himpl_antisym.
  { applys himpl_hforall_r. intros b.
    applys himpl_hforall_l (neg b). destruct* b. }
  { applys himpl_hforall_r. intros b.
    applys himpl_hforall_l (neg b). destruct* b. }
Qed.

Lemma himpl_hand_l_r : forall H1 H2,
  hand H1 H2 ==> H1.
Proof using. intros. unfolds hand. applys* himpl_hforall_l true. Qed.

Lemma himpl_hand_l_l : forall H1 H2,
  hand H1 H2 ==> H2.
Proof using. intros. unfolds hand. applys* himpl_hforall_l false. Qed.

Lemma himpl_hand_r : forall H1 H2 H3,
  H3 ==> H1 ->
  H3 ==> H2 ->
  H3 ==> hand H1 H2.
Proof using.
  introv M1 M. unfold hand. applys himpl_hforall_r. intros b. case_if*.
Qed.

Global Opaque hand.


(* ---------------------------------------------------------------------- *)
(* Properties of [hcredits] *)

Section Credits.
Transparent hempty hstar haffine.

Lemma hcredits_skip :
  use_credits = false ->
  forall n, \$ n = \[].
Proof using.
  introv E. intros n. applys fun_ext_1. intros h.
  unfolds hcredits. rewrite* (heap_credits_skip E).
Qed.

Lemma hcredits_zero :
  \$ 0 = \[].
Proof using.
  applys fun_ext_1. intros h. unfold hcredits. rewrite* heap_credits_zero.
Qed.

Lemma hcredits_add : forall n m,
  \$ (n+m) = \$ n \* \$ m.
Proof using.
  intros. applys fun_ext_1. intros h. unfold hcredits.
  unfold hstar. extens. iff M.
  { exists __ __. splits*.
    { applys heap_compat_credits. }
    { subst. rewrite* heap_credits_add. } }
  { destruct M as (h1&h2&->&->&C&->).
    rewrite* heap_credits_add. }
Qed.

Lemma haffine_hcredits : forall n,
  n >= 0 ->
  haffine (\$ n).
Proof using. introv H. unfold haffine. introv ->. apply* heap_credits_affine. Qed.

Lemma hcredits_sub : forall (n m : int),
  \$(n-m) = \$ n \* \$ (-m).
Proof using. intros. math_rewrite (n-m = n+(-m)). rewrite* hcredits_add. Qed.

Lemma hcredits_cancel : forall (n: int),
  \$ n \* \$ (-n) = \[].
Proof using. intros. rewrite <- hcredits_add. applys_eq hcredits_zero. fequals. math. Qed.

Lemma hcredits_extract : forall m n,
  \$ n = \$ m \* \$ (n-m).
Proof using. intros. rewrite <- hcredits_add. fequals. math. Qed.

Lemma hwand_hcredits_l : forall H n,
  (\$n \-* H) = (\$(-n) \* H).
Proof using.
  intros H1 n. rewrite hwand_eq_hexists. applys himpl_antisym.
  { applys himpl_hexists_l. intros H2. rewrite hstar_comm.
    apply himpl_hstar_hpure_l. intros M. rewrite <- (hstar_hempty_l H2).
    rewrite <- (hcredits_cancel n). rewrite hstar_assoc.
    rewrites (>> hstar_comm H2). rewrite <- hstar_assoc.
    rewrites (>> hstar_comm H1). applys himpl_frame_l M. }
  { sets H2: (\$(- n) \* H1). applys himpl_hexists_r H2.
    rewrites (hstar_comm H2). applys* himpl_hstar_hpure_r.
    subst H2. rewrite <- hstar_assoc. rewrite hcredits_cancel.
    rewrite* hstar_hempty_l. }
Qed.

End Credits.

Global Opaque hcredits.

(* ---------------------------------------------------------------------- *)

End SepSimplArgsCredits.

Module Export HS := LibSepSimpl.XsimplSetupCredits(SepSimplArgsCredits).

(** Experimental tactic [xsimpl_hand] *)

Tactic Notation "xsimpl_hand" :=
   xsimpl; try (applys himpl_hand_r; xsimpl).


(* ---------------------------------------------------------------------- *)
(* ** Set operators to be opaque *)

Global Opaque hempty hpure hstar hexists htop hgc haffine hand hor.



(* ********************************************************************** *)
(* * More properties of the magic wand *)

(* ---------------------------------------------------------------------- *)
(* ** Properties of [hwand] *)

Lemma hwand_eq_hexists_hstar_hpure : forall H1 H2,
  (H1 \-* H2) = (\exists H, H \* \[H1 \* H ==> H2]).
Proof using. auto. Qed.

Lemma hwand_himpl : forall H1 H1' H2 H2',
  H1' ==> H1 ->
  H2 ==> H2' ->
  (H1 \-* H2) ==> (H1' \-* H2').
Proof using. introv M1 M2. xsimpl. xchange~ M1. Qed.

Lemma hwand_himpl_r : forall H1 H2 H2',
  H2 ==> H2' ->
  (H1 \-* H2) ==> (H1 \-* H2').
Proof using. introv M. applys~ hwand_himpl. Qed.

Lemma hwand_himpl_l : forall H1' H1 H2,
  H1' ==> H1 ->
  (H1 \-* H2) ==> (H1' \-* H2).
Proof using. introv M. applys* hwand_himpl. Qed.

Lemma hwand_hpure_r_intro : forall H1 H2 (P:Prop),
  (P -> H1 ==> H2) ->
  H1 ==> (\[P] \-* H2).
Proof using. introv M. applys himpl_hwand_r. xsimpl*. Qed.

Lemma hstar_hwand : forall H1 H2 H3,
  (H1 \-* H2) \* H3 ==> H1 \-* (H2 \* H3).
Proof using.
  xsimpl.
Qed.
  (* intros. unfold hwand. xsimpl ;=> H4 M. xchanges M.
  unfold hwand. xsimpl ;=> H4 M. *)

Arguments hstar_hwand : clear implicits.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [qwand] *)

Lemma himpl_qwand_hstar_same_r : forall A (Q:A->hprop) H,
  H ==> Q \--* (Q \*+ H).
Proof using. intros. rewrite~ qwand_equiv. Qed.

Lemma himpl_qwand_r_inv : forall H A (Q1 Q2:A->hprop),
  H ==> (Q1 \--* Q2) ->
  (Q1 \*+ H) ===> Q2.
Proof using. introv M. rewrite~ <- qwand_equiv. Qed.

Lemma hstar_qwand : forall H A (Q1 Q2:A->hprop),
  (Q1 \--* Q2) \* H ==> Q1 \--* (Q2 \*+ H).
Proof using. xsimpl.
(*
  intros. unfold qwand. xchanges hstar_hforall.
  applys himpl_hforall. intros x.
  xchanges hstar_hwand.
*)
Qed.

Lemma qwand_cancel : forall A (Q1 Q2:A->hprop),
  Q1 \*+ (Q1 \--* Q2) ===> Q2.
Proof using. xsimpl. Qed.
(*
  intros. intros x.
  xchange (qwand_specialize x Q1 Q2).
  xchanges (hwand_cancel (Q1 x)).
*)

Lemma qwand_cancel_part : forall H A (Q1 Q2:A->hprop),
  H \* ((Q1 \*+ H) \--* Q2) ==> (Q1 \--* Q2).
Proof using.
  intros. applys himpl_qwand_r. intros x.
  xchange (qwand_specialize x).
Qed.

Lemma qwand_himpl : forall A (Q1 Q1' Q2 Q2':A->hprop),
  Q1' ===> Q1 ->
  Q2 ===> Q2' ->
  (Q1 \--* Q2) ==> (Q1' \--* Q2').
Proof using.
  introv M1 M2. applys himpl_hforall_r. intros x.
  applys himpl_hforall_l x. applys* hwand_himpl.
Qed.

Lemma qwand_himpl_l : forall A (Q1 Q1' Q2:A->hprop),
  Q1' ===> Q1 ->
  (Q1 \--* Q2) ==> (Q1' \--* Q2).
Proof using. introv M. applys* qwand_himpl. Qed.

Lemma qwand_himpl_r : forall A (Q1 Q2 Q2':A->hprop),
  Q2 ===> Q2' ->
  (Q1 \--* Q2) ==> (Q1 \--* Q2').
Proof using. introv M. applys* qwand_himpl. Qed.

(* ********************************************************************** *)
(* * haffine_repr *)

Definition haffine_repr a A (G:A -> a -> hprop) :=
  forall x X, haffine (x ~> G X).

Lemma haffine_repr_repr : forall a A (R:A->a->hprop),
  haffine_repr R ->
  haffine_repr (fun X x => x ~> R X).
Proof using. introv M. intros V v. rewrite* repr_eq. Qed.


(* ********************************************************************** *)
(* * Tactics for heap entailments *)

(* ---------------------------------------------------------------------- *)
(** Specific cleanup for formulaes *)

Ltac on_formula_pre cont :=
  match goal with
  | |- _ ?H ?Q => cont H
  | |- _ _ ?H ?Q => cont H
  | |- _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ _ _ _ _ _ ?H ?Q => cont H
  end.

Ltac on_formula_post cont :=
  match goal with
  | |- _ ?H ?Q => cont Q
  | |- _ _ ?H ?Q => cont Q
  | |- _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ _ _ _ _ _ ?H ?Q => cont Q
  end.

Ltac remove_empty_heaps_formula tt :=
  repeat (on_formula_pre ltac:(remove_empty_heaps_from)).


(* ---------------------------------------------------------------------- *)
(* ** The tactic [xaffine] simplifies a goal [haffine H] using structural
      rules. It may be extended to support custom extensions. *)

Create HintDb haffine.

Ltac xaffine_custom tt :=
  eauto with haffine.

(* example extension:

  Ltac xaffine_custom tt ::=
    repeat match goal with
    | |- haffine (hcredits _) => apply affine_credits; auto with zarith
    end.

*)

Ltac xaffine_step tt :=
  match goal with
  | |- haffine_post (_) => intros ? (* todo: interesting to have? *)
  | |- haffine_repr (fun X x => x ~> ?R X) => apply haffine_repr_repr
  | |- haffine_repr _ => intros ? ?
  | |- haffine ?H =>
    match H with
    | (hempty) => apply haffine_hempty
    | (hpure _) => apply haffine_hpure
    | (hstar (hpure _) _) => apply haffine_hstar_hpure_l; intros ?
    | (hstar _ _) => apply haffine_hstar
    | (hgc) => apply haffine_hgc
    | (hexists _) => apply haffine_hexists
    | (hforall _) => apply haffine_hforall
    | ?H' => xaffine_custom tt
    | _ => try assumption
    end
  end.

  (* LATER: automatically use haffine_hstar_hpure_l *)

Ltac xaffine_core tt ::= (* updates definition from [SepSimpl] *)
  repeat (xaffine_step tt).

Tactic Notation "xaffine" :=
  xaffine_core tt.
Tactic Notation "xaffine" "~" :=
  xaffine; auto_tilde.
Tactic Notation "xaffine" "*" :=
  xaffine; auto_star.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xsimplh] to prove [H h] from [H' h] *)

(** [xsimplh] applies to a goal of the form [H h].
   It looks up for an hypothesis of the form [H' h],
   where [H'] is a heap predicate (whose type is syntactically [hprop]).
   It then turns the goal into [H ==> H'], and calls [xsimpl].

   This tactic is very useful for establishing the soundness of
   Separation Logic derivation rules. It should never be used in
   the verification of concrete programs, since a heap [h] should
   never appear explicitly in such a proof, all the reasoning being
   conducted at the level of heap predicates. *)

Ltac xsimplh_core tt :=
  match goal with N: ?H ?h |- _ ?h =>
    match type of H with hprop =>
    applys himpl_inv N; clear N; xsimpl
  end end.

Tactic Notation "xsimplh" := xsimplh_core tt.
Tactic Notation "xsimplh" "~" := xsimplh; auto_tilde.
Tactic Notation "xsimplh" "*" := xsimplh; auto_star.


(* ********************************************************************** *)
(** * Predicate [local] *)

(* ---------------------------------------------------------------------- *)
(* ** Definition of [local] *)

(** Type of characteristic formulae on values of type B *)

Notation "'~~' B" := (hprop->(B->hprop)->Prop)
  (at level 8, only parsing) : type_scope.

(** A formula [F] is mklocal (e.g. [F] could be the predicate SL [triple])
    if it is sufficient for establishing [F H Q] to establish that the
    the formula holds on a subheap, in the sense that [F H1 Q1] with
    [H = H1 \* H2] and [Q = Q1 \*+ H2].
    (Technically, we add an extra [\GC] in to capture the affinity of the logic.) *)

Definition local B (F:~~B) : Prop :=
  forall H Q,
    (H ==> \exists H1 H2 Q1, H1 \* H2 \*
             \[F H1 Q1 /\ Q1 \*+ H2 ===> Q \*+ \GC]) ->
    F H Q.

(** [local_pred S] asserts that [local (S x)] holds for any [x].
    It is useful for describing loop invariants. *)

Definition local_pred A B (S:A->~~B) :=
  forall x, local (S x).


(* ---------------------------------------------------------------------- *)
(* ** Properties of [local] *)

Implicit Type P : Prop.
Implicit Type H : hprop.

(** Remark: for conciseness, we abbreviate names of lemmas,
    e.g. [local_inv_frame] is named [mklocal_conseq_frame]. *)

Section IsLocal.

Variables (B : Type).
Implicit Types (F : ~~B).
Hint Resolve haffine_hempty.

(** A introduction rule to establish [local], exposing the definition *)

Lemma local_intro : forall F,
  (forall H Q,
    (H ==> \exists H1 H2 Q1, H1 \* H2 \*
             \[F H1 Q1 /\ Q1 \*+ H2 ===> Q \*+ \GC]) ->
    F H Q) ->
  local F.
Proof using. auto. Qed.

(** An elimination rule for [local] *)

Lemma local_elim : forall F H Q,
  local F ->
  (H ==> \exists H1 H2 Q1, H1 \* H2 \* \[F H1 Q1 /\ Q1 \*+ H2 ===> Q \*+ \GC]) ->
  F H Q.
Proof using. auto. Qed.

(** An elimination rule for [local] without [htop] *)

Lemma local_elim_frame : forall F H Q,
  local F ->
  (H ==> \exists H1 H2 Q1, H1 \* H2 \* \[F H1 Q1 /\ Q1 \*+ H2 ===> Q]) ->
  F H Q.
Proof using.
  introv L M. applys~ local_elim. xchange M.
  xpull ;=> H1 H2 Q1 (N1&N2). xsimpl H1 H2 Q1. split~.
  xchanges~ N2.
Qed.

(** An elimination rule for [local] specialized for no frame, and no [htop] *)

Lemma local_elim_conseq_pre : forall F H Q,
  local F ->
  (H ==> \exists H1, H1 \* \[F H1 Q]) ->
  F H Q.
Proof using.
  introv L M. applys~ local_elim_frame. xchange M.
  xpull ;=> H1 N. xsimpl H1 \[] Q. splits*. xsimpl.
Qed.

(** Weaken and frame and gc property [mklocal] *)

Lemma local_conseq_frame_hgc : forall F H H1 H2 Q1 Q,
  local F ->
  F H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \GC ->
  F H Q.
Proof using.
  introv L M WH WQ. applys~ local_elim. xchange WH.
  xsimpl~ H1 H2 Q1.
Qed.

(** Weaken and frame properties from [mklocal] *)

Lemma local_conseq_frame : forall H1 H2 Q1 F H Q,
  local F ->
  F H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  F H Q.
Proof using.
  introv L M WH WQ. applys* local_conseq_frame_hgc M. xchanges~ WQ.
Qed.

(** Frame rule *)

Lemma local_frame : forall H2 Q1 H1 F,
  local F ->
  F H1 Q1 ->
  F (H1 \* H2) (Q1 \*+ H2).
Proof using. introv L M. applys~ local_conseq_frame M. Qed.

(** Ramified frame rule *)

Lemma local_ramified_frame : forall Q1 H1 F H Q,
  local F ->
  F H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  F H Q.
Proof using.
  introv L M WH. applys~ local_conseq_frame (Q1 \--* Q) M.
  xsimpl.
Qed.

(** Ramified frame rule with \GC *)

Lemma local_ramified_frame_hgc : forall Q1 H1 F H Q,
  local F ->
  F H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q \*+ \GC) ->
  F H Q.
Proof using.
  introv L M WH. applys~ local_conseq_frame_hgc (Q1 \--* Q \*+ \GC) M.
  xsimpl.
Qed.

(** Consequence rule *)

Lemma local_conseq : forall H' Q' F H Q,
  local F ->
  F H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  F H Q.
Proof using.
  introv L M WH WQ. applys* local_conseq_frame_hgc \[] M.
  { xsimpl*. } { xchanges WQ. }
Qed.

(** Garbage collection on precondition from [mklocal] *)

Lemma local_hgc_pre : forall F H Q,
  local F ->
  F H Q ->
  F (H \* \GC) Q.
Proof using. introv L M. applys~ local_conseq_frame_hgc M. Qed.

Lemma local_conseq_pre_hgc : forall H' F H Q,
  local F ->
  H ==> H' \* \GC ->
  F H' Q ->
  F H Q.
Proof using. introv L WH M. applys* local_conseq_frame_hgc M. Qed.

(** Garbage collection on postcondition from [mklocal] *)

Lemma local_hgc_post : forall F H Q,
  local F ->
  F H (Q \*+ \GC) ->
  F H Q.
Proof using. introv L M. applys* local_conseq_frame_hgc \[] M; xsimpl. Qed.

Lemma local_conseq_post_hgc : forall Q' F H Q,
  local F ->
  F H Q' ->
  Q' ===> Q \*+ \GC ->
  F H Q.
Proof using.
  introv L M WQ. applys* local_conseq_frame_hgc \[] M.
  { xsimpl. } { xchanges WQ. }
Qed.

(** Variant of the above, useful for tactics to specify
    the garbage collected part *)

Lemma local_hgc_pre_on : forall HG H' F H Q,
  local F ->
  haffine HG ->
  H ==> HG \* H' ->
  F H' Q ->
  F H Q.
Proof using. introv L K WH M. applys~ local_conseq_pre_hgc M. xchanges~ WH. Qed.

(** Weakening on pre and post with gc-post from [mklocal] *)

Lemma local_conseq_hgc_post : forall H' Q' F H Q,
  local F ->
  F H' Q' ->
  H ==> H' ->
  Q' ===> Q \*+ \GC ->
  F H Q.
Proof using.
  introv L M WH WQ. applys~ local_conseq_frame_hgc \[] M.
  { xchanges WH. } { xchanges WQ. }
Qed.

(** Weakening on pre and post with gc-pre from [mklocal] *)

Lemma local_conseq_hgc_pre : forall H' Q' F H Q,
  local F ->
  F H' Q' ->
  H ==> H' \* \GC ->
  Q' ===> Q ->
  F H Q.
Proof using.
  introv L M WH WQ. applys~ local_conseq_frame_hgc \GC M.
  { xchanges WQ. }
Qed.

(** Weakening on pre from [mklocal] *)

Lemma local_conseq_pre : forall H' F H Q,
  local F ->
  F H' Q ->
  H ==> H' ->
  F H Q.
Proof using. introv L M WH. applys* local_conseq M. Qed.

(** Weakening on post from [mklocal] *)

Lemma local_conseq_post : forall Q' F H Q,
  local F ->
  F H Q' ->
  Q' ===> Q ->
  F H Q.
Proof using. introv L M WQ. applys* local_conseq M. Qed.

(** Extraction of pure facts from [mklocal] *)

Lemma local_hpure : forall F H P Q,
  local F ->
  (P -> F H Q) ->
  F (\[P] \* H) Q.
Proof using.
  introv L M. applys~ local_elim_conseq_pre. xpull ;=> HP. xsimpl~ H.
Qed.

(** Extraction of existentials from [mklocal] *)

Lemma local_hexists : forall F A (J:A->hprop) Q,
  local F ->
  (forall x, F (J x) Q) ->
  F (hexists J) Q.
Proof using.
  introv L M. applys~ local_elim_conseq_pre. xpull ;=> x. xsimpl* (J x).
Qed.

(** Extraction of existentials below a star from [mklocal] *)

Lemma local_hstar_hexists : forall F H A (J:A->hprop) Q,
  local F ->
  (forall x, F ((J x) \* H) Q) ->
   F (hexists J \* H) Q.
Proof using.
  introv L M. rewrite hstar_hexists. applys~ local_hexists.
Qed.

(** Extraction of forall from [mklocal] *)

Lemma local_hforall : forall A (x:A) F (J:A->hprop) Q,
  local F ->
  F (J x) Q ->
  F (hforall J) Q.
Proof using.
  introv L M. applys~ local_elim_conseq_pre.
  applys himpl_hforall_l x. xsimpl~ (J x).
Qed.

Lemma local_hforall_exists : forall F A (J:A->hprop) Q,
  local F ->
  (exists x, F (J x) Q) ->
  F (hforall J) Q.
Proof using. introv L (x&M). applys* local_hforall. Qed.

(** Extraction of forall below a star from [mklocal] *)
(* --TODO needed? *)

Lemma local_hstar_hforall_l : forall F H A (J:A->hprop) Q,
  local F ->
  (exists x, F ((J x) \* H) Q) ->
  F (hforall J \* H) Q.
Proof using.
  introv L (x&M).
  applys local_conseq_pre; [ auto | | applys hstar_hforall ].
  (* --TODO: fix level for notation \forall and \hstar, so that parentheses show up *)
  (* above line same as: xtchanges hstar_hforall. *)
  applys* local_hforall.
Qed.

(** Case analysis for [hor] *)

Lemma local_hor : forall F H1 H2 Q,
  local F ->
  F H1 Q ->
  F H2 Q ->
  F (hor H1 H2) Q.
Proof using.
  introv L M1 M2. rewrite hor_eq_exists_bool.
  apply* local_hexists. intros b. case_if*.
Qed.

(** Left branch for [hand] *)

Lemma local_hand_l : forall F H1 H2 Q,
  local F ->
  F H1 Q ->
  F (hand H1 H2) Q.
Proof using.
  introv L M1. rewrite hand_eq_forall_bool.
  applys* local_hforall true.
Qed.

(** Right branch for [hand] *)

Lemma local_hand_r : forall F H1 H2 Q,
  local F ->
  F H2 Q ->
  F (hand H1 H2) Q.
Proof using.
  introv L M1. rewrite hand_eq_forall_bool.
  applys* local_hforall false.
Qed.

(** Extraction of heap representation from [mklocal] *)

Lemma local_name_heap : forall F H Q,
  local F ->
  (forall h, H h -> F (= h) Q) ->
  F H Q.
Proof using.
  introv L M. applys~ local_elim_conseq_pre.
  intros h Hh. exists (= h). rewrite hstar_comm.
  applys* himpl_hstar_hpure_r (= h).
Qed.

(** Extraction of pure facts from the precondition under local *)

Lemma local_prop : forall F H Q P,
  local F ->
  (H ==> H \* \[P]) ->
  (P -> F H Q) ->
  F H Q.
Proof using.
  introv L WH M. applys~ local_elim_conseq_pre.
  xchanges WH. rew_heap~.
Qed.

(** Extraction of proof obligations from the precondition under local *)

Lemma local_hwand_hpure_l : forall F (P:Prop) H Q,
  local F ->
  P ->
  F H Q ->
  F (\[P] \-* H) Q.
Proof using.
  introv L HP M. applys~ local_elim_conseq_pre.
  xchanges~ hwand_hpure_l.
Qed.

End IsLocal.

Global Opaque local.


(* ********************************************************************** *)
(** * Definition of the predicate transformer [mklocal] *)
(* --TODO needed? *)

(** Remark: this section might be specific to old-style characteristic formulae *)

(** The [mklocal] predicate is a predicate transformer that allows
    to turn a formula into a mklocal formula. *)

Definition mklocal B (F:~~B) : ~~B :=
  fun (H:hprop) (Q:B->hprop) =>
    H ==> \exists H1 H2 Q1,
       H1 \* H2 \* \[F H1 Q1 /\ Q1 \*+ H2 ===> Q \*+ \GC].

Section Local.
Transparent local.
Variables (B:Type).
Implicit Types (F:~~B).

(** The [mklocal] operator can be freely erased from a conclusion *)

Lemma mklocal_erase : forall F H Q,
  F H Q ->
  mklocal F H Q.
Proof using.
  introv M. unfold mklocal. xsimpl H \[]. splits*. xsimpl.
Qed.

(** [mklocal] is idempotent, i.e. nested applications
   of [mklocal] are redundant *)

Lemma mklocal_mklocal : forall F,
  mklocal (mklocal F) = mklocal F.
Proof using.
  extens. intros H Q. iff M.
  { unfold mklocal. eapply himpl_trans; [apply M|]. xpull ;=> H1 H2 Q1 [P1 P2].
    unfold mklocal in P1. xchange P1. xpull ;=> H1' H2' Q1' [P1' P2'].
    xsimpl H1' (H2 \* H2') Q1'. splits*.
    intros x. xchanges P2'. xchange P2. }
  { apply~ mklocal_erase. }
Qed.

(** The predicate [mklocal] satisfies [local] *)

Lemma local_mklocal : forall F,
  local (mklocal F).
Proof using. introv M. rewrite <- mklocal_mklocal. applys M. Qed.

(** A [mklocal] can be introduced at the head of a formula satisfying [local] *)

Lemma eq_mklocal_of_local : forall F,
  local F ->
  F = mklocal F.
Proof using.
  introv L. applys pred_ext_2. intros H Q. iff M.
  { applys~ mklocal_erase. }
  { applys~ local_elim. }
Qed.

(** [mklocal] is a covariant transformer w.r.t. predicate inclusion *)

Notation "Q1 ===>' Q2" := (forall x y, Q1 x y -> Q2 x y) (at level 55).

Lemma mklocal_weaken : forall F F',
  F ===>' F' ->
  mklocal F ===>' mklocal F'.
Proof using.
  unfold mklocal. introv M. intros H Q N. xchange (rm N) ;=> H1 H2 Q' [P1 P2].
  xsimpl H1 H2 Q'. split~. (* applys~ M. *)
Qed.

(** Extraction of contradictions from the precondition under mklocal *)

Lemma mklocal_false : forall F H Q,
  mklocal F H Q ->
  (forall H' Q', F H' Q' -> False) ->
  (H ==> \[False]).
Proof using.
  introv M N. xchange M. xpull ;=> H' H1 Q' [HF _]. false* N.
Qed.

End Local.


(* ********************************************************************** *)
(* * Tactics for triples and characteristic formulae *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xlocal] to prove side-conditions of the form [mklocal F]. *)

Ltac xlocal_base tt :=
  auto 1.

(* e.g.
Ltac xlocal_base tt ::=
  try first [ applys local_mklocal ].
*)

Ltac xlocal_unfold_pred tt :=
  try match goal with |- local_pred ?S =>
    let r := fresh "TEMP" in intros r end.

Ltac xlocal_core tt :=
  try first [ assumption | xlocal_unfold_pred tt; xlocal_base tt ].

Tactic Notation "xlocal" :=
  xlocal_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xtpull_check] tests whether it would be useful
      to call [xtpull] to extract things from the precondition.
      Applies to a goal of the form [F H Q]. *)

Ltac xtpull_check tt := (* DEPRECATED *)
  idtac.
(*
  let H := xprecondition tt in
  xpull_check_rec H.
*)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xtpull] to extract existentials and pure facts from
      preconditions. *)

(** [xtpull] plays a similar role to [xpull], except that it works on
   goals of the form [F H Q], where [F] is typically a triple predicate
   or a characteristic formula.

   [xtpull] simplifies the precondition [H] as follows:
   - it removes empty heap predicates
   - it pulls pure facts out as hypotheses into the context
   - it pulls existentials as variables into the context.

   At the end, it regeneralizes in the goals the new variables
   from the context, so as to allow the user to introduce them
   by giving appropriate names. *)


(** Lemmas *)

Lemma xtpull_start : forall B (F:~~B) H Q,
  F (\[] \* H) Q ->
  F H Q.
Proof using. intros. rew_heap in *. auto. Qed.

Lemma xtpull_keep : forall B (F:~~B) H1 H2 H3 Q,
  F ((H2 \* H1) \* H3) Q ->
  F (H1 \* (H2 \* H3)) Q.
Proof using. intros. rewrite (hstar_comm H2) in H. rew_heap in *. auto. Qed.

Lemma xtpull_assoc : forall B (F:~~B) H1 H2 H3 H4 Q,
  F (H1 \* (H2 \* (H3 \* H4))) Q ->
  F (H1 \* ((H2 \* H3) \* H4)) Q.
Proof using. intros. rew_heap in *. auto. Qed.

Lemma xtpull_starify : forall B (F:~~B) H1 H2 Q,
  F (H1 \* (H2 \* \[])) Q ->
  F (H1 \* H2) Q.
Proof using. intros. rew_heap in *. auto. Qed.

Lemma xtpull_empty : forall B (F:~~B) H1 H2 Q,
  (F (H1 \* H2) Q) ->
  F (H1 \* (\[] \* H2)) Q.
Proof using. intros. rew_heap. auto. Qed.

Lemma xtpull_hpure : forall B (F:~~B) H1 H2 P Q,
  local F ->
  (P -> F (H1 \* H2) Q) ->
  F (H1 \* (\[P] \* H2)) Q.
Proof using.
  intros. rewrite hstar_comm_assoc. apply~ local_hpure.
Qed.

Lemma xtpull_id : forall A (x X : A) B (F:~~B) H1 H2 Q,
  local F ->
  (x = X -> F (H1 \* H2) Q) ->
  F (H1 \* (x ~> Id X \* H2)) Q.
Proof using. intros. unfold Id. apply~ xtpull_hpure. Qed.

Lemma xtpull_hexists : forall B (F:~~B) H1 H2 A (J:A->hprop) Q,
  local F ->
  (forall x, F (H1 \* ((J x) \* H2)) Q) ->
   F (H1 \* (hexists J \* H2)) Q.
Proof using.
  intros. rewrite hstar_comm_assoc. apply~ local_hstar_hexists.
  intros. rewrite~ hstar_comm_assoc.
Qed.

(*
Lemma xtpull_hwand_hpure_l : forall B (F:~~B) H1 H2 (P:Prop) Q,
  local F ->
  (P -> F (H1 \* H2) Q) ->
   F (H1 \* (\[P] \-* H2)) Q.
*)

Ltac xpull_xtpull_iris_hook tt := idtac.

Ltac xtpull_setup tt :=
  pose ltac_mark;
  intros;
  try match goal with |- ?H ==> ?H' =>
        fail 100 "you should call xpull, not xtpull" end;
  xpull_xtpull_iris_hook tt;
  apply xtpull_start.

Ltac xtpull_post_processing_for_hyp H :=
  idtac.

Ltac xtpull_cleanup tt :=
  remove_empty_heaps_formula tt;
  gen_until_mark_with_processing ltac:(xtpull_post_processing_for_hyp).

Ltac xtpull_hpure tt :=
  apply xtpull_hpure; [ try xlocal | intro ].
Ltac xtpull_hexists tt :=
  apply xtpull_hexists; [ try xlocal | intro ].
Ltac xtpull_id tt :=
  apply xtpull_id; [ try xlocal | intro ].

Ltac xtpull_step tt :=
  let go HP :=
    match HP with _ \* ?HN =>
    match HN with
    | ?H \* _ =>
      match H with
      | \[] => apply xtpull_empty
      | \[_] => xtpull_hpure tt
      | hexists _ => xtpull_hexists tt
      | _ ~> Id _ => xtpull_id tt
      | _ \* _ => apply xtpull_assoc
      | _ => apply xtpull_keep
      end
    | \[] => fail 1
    | _ => apply xtpull_starify
    end end in
  on_formula_pre ltac:(go).

Ltac xtpull_main tt :=
  xtpull_setup tt;
  (repeat (xtpull_step tt));
  xtpull_cleanup tt.

Tactic Notation "xtpull" := xtpull_main tt.
Tactic Notation "xtpull" "~" := xtpull; auto_tilde.
Tactic Notation "xtpull" "*" := xtpull; auto_star.

(* Demo *)

Lemma xtpull_demo_1 : forall H1 H2 A (P:A->Prop) (J:A->hprop) B (F:~~B) (Q:B->hprop),
  local F ->
  F (H1 \* \exists x, (J x \* H2 \* \[P x])) Q.
Proof using.
  introv L. dup.
  { xtpull_setup tt.
    xtpull_step tt.
    xtpull_step tt.
    xtpull_step tt.
    xtpull_step tt.
    xtpull_step tt.
    xtpull_step tt.
    xtpull_step tt.
    xtpull_step tt.
    xtpull_cleanup tt. demo. }
  { xtpull. demo. }
Abort.


(* ---------------------------------------------------------------------- *)
(** Auxiliary tactics used by some tactics *)

(* [xprecondition tt] returns the current precondition. *)

Ltac xprecondition tt :=
  match goal with |- ?R ?H ?Q => constr:(H) end.

(* [xpostcondition tt] returns the current postcondition. *)

Ltac xpostcondition tt :=
  match goal with |- ?E =>
  match get_fun_arg E with (_,?Q) => constr:(Q)
  end end.
  (* --LATER: is this now equivalent to:
     match goal with |- ?J ?Q => constr:(Q) end. *)

(** [xpostcondition_is_evar tt] returns a boolean indicating
    whether the postcondition of the current goal is an evar. *)

Ltac xpostcondition_is_evar tt :=
  let Q := xpostcondition tt in
  is_evar_as_bool Q.


(* ---------------------------------------------------------------------- *)
(* ** [xapply] and [xapplys] *)

(** [xapply E] applies a lemma [E] modulo frame/weakening.
    It applies to a goal of the form [F H Q], and replaces it
    with [F ?H' ?Q'], applies [E] to the goal, then produces
    the side condition [H ==> ?H'] and,
    - if [Q] is instantiated, then leaves [?Q' ===> Q \* \GC]
    - otherwise it instantiates [Q] with [Q'].

    [xapplys E] is like [xapply E] but also attemps to simplify
    the subgoals using [xsimpl].
*)

Ltac xapply_core H cont1 cont2 :=
  forwards_nounfold_then H ltac:(fun K =>
    match xpostcondition_is_evar tt with
    | true => eapply local_conseq_frame; [ xlocal | sapply K | cont1 tt | try apply qimpl_refl ]
    | false => eapply local_conseq_frame_hgc; [ xlocal | sapply K | cont1 tt | cont2 tt ]
    end).

Ltac xapply_base H :=
  xtpull_check tt;
  xapply_core H ltac:(fun tt => idtac) ltac:(fun tt => idtac).

Ltac xapplys_base H :=
  xtpull_check tt;
  xapply_core H ltac:(fun tt => xsimpl) ltac:(fun tt => xsimpl).

Tactic Notation "xapply" constr(H) :=
  xapply_base H.
Tactic Notation "xapply" "~" constr(H) :=
  xapply H; auto_tilde.
Tactic Notation "xapply" "*" constr(H) :=
  xapply H; auto_star.

Tactic Notation "xapplys" constr(H) :=
  xapplys_base H.
Tactic Notation "xapplys" "~" constr(H) :=
  xapplys H; auto_tilde.
Tactic Notation "xapplys" "*" constr(H) :=
  xapplys H; auto_star.


(* Demo *)

Lemma xapply_demo_1 : forall H1 H2 H3 B (F:~~B) (Q1:B->hprop),
  local F ->
  F H1 Q1 ->
  H2 ==> H3 ->
  F (H2 \* H1) (Q1 \*+ H3).
Proof using.
  introv L M HW. dup.
  { xapply M. xsimpl. xchanges HW. }
  { xapplys M. xchanges HW. }
Abort.


(*--------------------------------------------------------*)
(* ** [xtchange] *)

(** [xtchange E] applies to a goal of the form [F H Q]
    and to a lemma [E] of type [H1 ==> H2] or [H1 = H2].
    It replaces the goal with [F H' Q], where [H']
    is computed by replacing [H1] with [H2] in [H].

    The substraction is computed by solving [H ==> H1 \* ?H']
    with [xsimpl]. If you need to solve this implication by hand,
    use [xtchange_no_simpl E] instead.

    [xtchange <- E] is useful when [E] has type [H2 = H1]
      instead of [H1 = H2].

    [xtchange_show E] is useful to visualize the instantiation
    of the lemma used to implement [xtchange].
    *)

(* Lemma used by [xtchange] *)

Lemma xtchange_lemma : forall H1 H1' H2 B H Q (F:~~B),
  local F ->
  (H1 ==> H1') ->
  (H ==> H1 \* H2) ->
  F (H1' \* H2) Q ->
  F H Q.
Proof using.
  introv W1 L W2 M. applys local_conseq_frame __ \[]; eauto.
  xsimpl. xchange~ W2. xsimpl~. rew_heap~.
Qed.

Ltac xtchange_apply L cont1 cont2 :=
   eapply xtchange_lemma;
     [ try xlocal | applys L | cont1 tt | cont2 tt (*xtag_pre_post*) ].

(* Note: the term modif should be either himpl_of_eq or himpl_of_eq_sym *)
Ltac xtchange_forwards L modif cont1 cont2 :=
  forwards_nounfold_then L ltac:(fun K =>
  match modif with
  | __ =>
     match type of K with
     | _ = _ => xtchange_apply (@himpl_of_eq _ _ _ K) cont1 cont2
     | _ => xtchange_apply K cont1 cont2
     end
  | _ => xtchange_apply (@modif _ _ _ K) cont1 cont2
  end).

Ltac xtchange_with_core cont1 cont2 H H' :=
  eapply xtchange_lemma with (H1:=H) (H1':=H');
    [ try xlocal | | cont1 tt | cont2 tt (* xtag_pre_post*)  ].

Ltac xtchange_core cont1 cont2 E modif :=
  match E with
  | ?H ==> ?H' => xtchange_with_core cont1 cont2 H H'
  | _ => xtchange_forwards E modif
          ltac:(fun _ => cont1 tt)
          ltac:(fun _ => cont2 tt)
  end.

Ltac xtchange_base cont1 cont2 E modif :=
  xtpull_check tt;
  match goal with
  | |- _ ==> _ => xchange_core E modif ltac:(xchange_xsimpl_cont) cont2
  | |- _ ===> _ => xchange_core E modif ltac:(xchange_xsimpl_cont) cont2
  | _ => xtchange_core cont1 cont2 E modif
  end.

Ltac xpull_or_xtpull tt :=
  match goal with
  | |- _ ==> _ => xpull
  | |- _ ===> _ => xpull
  | |- _ => xtpull
  end.

Tactic Notation "xtchange" constr(E) :=
  xtchange_base ltac:(fun tt => xsimpl) ltac:(idcont) E __.
Tactic Notation "xtchange" "~" constr(E) :=
  xtchange E; auto_tilde.
Tactic Notation "xtchange" "*" constr(E) :=
  xtchange E; auto_star.

Tactic Notation "xtchange" "<-" constr(E) :=
  xtchange_base ltac:(fun tt => xsimpl) ltac:(idcont) E himpl_of_eq_sym.
Tactic Notation "xtchange" "~" "<-" constr(E) :=
  xtchange <- E; auto_tilde.
Tactic Notation "xtchange" "*" "<-" constr(E) :=
  xtchange <- E; auto_star.

Tactic Notation "xtchanges" constr(E) :=
  xtchange_base ltac:(fun tt => xsimpl) ltac:(fun tt => xpull_or_xtpull tt) E __.
Tactic Notation "xtchanges" "~" constr(E) :=
  xtchanges E; auto_tilde.
Tactic Notation "xtchanges" "*" constr(E) :=
  xtchanges E; auto_star.

Tactic Notation "xtchange_no_simpl" constr(E) :=
  xtchange_base ltac:(idcont) ltac:(idcont)E __.
Tactic Notation "xtchange_no_simpl" "<-" constr(E) :=
  xtchange_base ltac:(idcont) E himpl_of_eq_sym.

Tactic Notation "xtchange_show" constr(E) :=
  xtchange_forwards E __ ltac:(idcont) ltac:(idcont).
Tactic Notation "xtchange_show" "<-" constr(E) :=
  xtchange_forwards himpl_of_eq_sym ltac:(idcont) ltac:(idcont).


(* Demo *)

Lemma xtchange_demo_1 : forall H1 H1' H2 B (F:~~B) (Q:B->hprop),
  local F ->
  H1 ==> H1' ->
  F (H2 \* H1) Q.
Proof using.
  introv L M. xtchange M.
Abort.



(* ********************************************************************** *)
(* * Iterated star *)

(* ---------------------------------------------------------------------- *)
(** Separation commutative monoid [(hstar,hempty)] *)

Definition sep_monoid := monoid_make hstar hempty.

Global Instance Monoid_sep : Monoid sep_monoid.
Proof using. constructor; simpl; intros_all; xsimpl. Qed.

Global Instance Comm_monoid_sep : Comm_monoid sep_monoid.
Proof using.
  constructor; simpl.
  applys Monoid_sep.
  intros_all. apply hstar_comm.
Qed.


(* ---------------------------------------------------------------------- *)
(** [hfold_list] *)

Definition hfold_list A (f:A->hprop) := fix F (l:list A) : hprop :=
  match l with
  | nil => \[]
  | x::l' => f x \* F l'
  end.

Definition hfold_list' A (f:A->hprop) (l:list A) : hprop :=
  LibList.fold sep_monoid f l.

Lemma hfold_list_eq :
  hfold_list = hfold_list'.
Proof using.
  applys fun_ext_3 ;=> A f l. induction l as [|x l'].
  { auto. }
  { unfold hfold_list'. rewrite fold_cons. simpl. rewrite~ IHl'. }
Qed.

Section HfoldList.
Variables (A:Type).
Implicit Types l : list A.
Implicit Types f : A->hprop.
Hint Resolve Monoid_sep.

Lemma hfold_list_nil : forall f,
  hfold_list f nil = \[].
Proof using. auto. Qed.

Lemma hfold_list_cons : forall f x l,
  hfold_list f (x::l) = (f x) \* (hfold_list f l).
Proof using. auto. Qed.

Lemma hfold_list_one : forall f x,
  hfold_list f (x::nil) = f x.
Proof using. intros. simpl. xsimpl. Qed.

End HfoldList.

Hint Rewrite hfold_list_nil hfold_list_cons hfold_list_one : rew_heapx.

(* ---------------------------------------------------------------------- *)
(** [hfold_list2] *)

Definition hfold_list2 A B (f:A->B->hprop) :=
  fix F (l1:list A) (l2:list B) { struct l1 } : hprop :=
  match l1,l2 with
  | nil, nil => \[]
  | x1::l1', x2::l2' => f x1 x2 \* F l1' l2'
  | _, _ =>  arbitrary
    (* using empty instead of arbitrary: fewer proof obligations for haffine *)
  end.

(*
Definition hfold_list2' A B (f:A->B->hprop) (l1:list A) (l2:list B) : hprop :=
  hfold_list' (fun '(x1,x2) => f x1 x2) (LibList.combine l1 l2).

  --- matches only for lists of the same length
*)

Section HfoldList2.
Variables (A B:Type).
Implicit Types f : A->B->hprop.

Lemma hfold_list2_nil : forall f,
  hfold_list2 f nil nil = \[].
Proof using. auto. Qed.

Lemma hfold_list2_cons : forall f x1 x2 l1 l2,
  hfold_list2 f (x1::l1) (x2::l2) = (f x1 x2) \* (hfold_list2 f l1 l2).
Proof using. auto. Qed.

Lemma hfold_list2_one : forall f x1 x2,
  hfold_list2 f (x1::nil) (x2::nil) = f x1 x2.
Proof using. intros. simpl. xsimpl. Qed.

End HfoldList2.

Hint Rewrite hfold_list2_nil hfold_list2_cons hfold_list2_one : rew_heapx.

(* ---------------------------------------------------------------------- *)
(** Tactic [rew_heapx] for normalization of [hfold] *)

Tactic Notation "rew_heapx" :=
  autorewrite with rew_heapx.
Tactic Notation "rew_heapx" "~" :=
  rew_heapx; auto_tilde.
Tactic Notation "rew_heapx" "*" :=
  rew_heapx; auto_star.

(* ---------------------------------------------------------------------- *)
(** Affinity results for [hfold] *)

(* TODO: more haffine results needed *)

Lemma haffine_hfold_list2 : forall A B (l1:list A) (l2:list B) (R:A->B->hprop),
  length l1 = length l2 ->
  (forall x X, mem X l1 -> (* mem x l2 -> *) haffine (x ~> R X)) ->
  haffine (hfold_list2 R l1 l2).
Proof using.
  introv M E. gen l2. induction l1 as [|x1 l1']; destruct l2 as [|x2 l2'];
   rew_list; try (intros; false; math); intros Eq; simpl.
  { xaffine. }
  { xaffine. }
  (* { rewrite* <- (repr_eq (R x1)). } { applys* IHl1'. math. } } *)
Qed. (* LATER: list2_ind_mem *)

Hint Resolve haffine_hfold_list2 : haffine.


(* TODO: hfold_fmap *)

(* ********************************************************************** *)
(* * Weakest-preconditions *)

(* ---------------------------------------------------------------------- *)
(* ** Definition of the weakest precondition for a formula *)

Definition weakestpre (B : Type) (F:hprop->(B->hprop)->Prop) (Q:B->hprop) : hprop :=
  \exists (H:hprop), H \* \[F H Q].

Lemma weakestpre_eq : forall B (F:~~B) H Q,
  local F -> (* in fact, only requires weaken-pre and extract-hexists rules to hold *)
  F H Q = (H ==> weakestpre F Q).
Proof using.
  introv L. applys prop_ext. unfold weakestpre. iff M.
  { xsimpl. rew_heap~. }
  { applys~ local_conseq_pre M. xtpull~. }
Qed.

Lemma weakestpre_conseq : forall B (F:~~B) Q1 Q2,
  local F ->
  Q1 ===> Q2 ->
  weakestpre F Q1 ==> weakestpre F Q2.
Proof using.
  introv L W. unfold weakestpre. xpull ;=> H1 M. xsimpl~.
  xapply M. xsimpl. xsimpl. xchanges W.
Qed.

Lemma weakestpre_conseq_wand : forall B (F:~~B) Q1 Q2,
  local F ->
  (Q1 \--* Q2) \* weakestpre F Q1 ==> weakestpre F Q2.
Proof using.
  introv L. unfold weakestpre. xpull ;=> H1 M.
  xsimpl (H1 \* (Q1 \--* Q2)). xapplys M.
Qed.

Lemma weakestpre_frame : forall B (F:~~B) H Q,
  local F ->
  (weakestpre F Q) \* H ==> weakestpre F (Q \*+ H).
Proof using.
  introv L. unfold weakestpre. xpull ;=> H1 M.
  xsimpl (H1 \* H). xapplys M.
Qed.

Lemma weakestpre_absorb : forall B (F:~~B) Q,
  local F ->
  weakestpre F Q \* \GC ==> weakestpre F Q.
Proof using.
  introv L. unfold weakestpre. xpull ;=> H1 M.
  xsimpl~ (H1 \* \GC). xapplys M.
Qed.

Lemma weakestpre_pre : forall B (F:~~B) Q,
  local F ->
  F (weakestpre F Q) Q.
Proof using. intros. unfold weakestpre. xtpull ;=> H'. auto. Qed.

Lemma himpl_weakestpre : forall B (F:~~B) H Q,
  F H Q ->
  H ==> weakestpre F Q.
Proof using. introv M. unfold weakestpre. xsimpl~ H. Qed.


(* ********************************************************************** *)
(* * Tactics for representation predicates *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xunfold] to unfold heap predicates *)

(** For technical reasons, on a heap predicate [x ~> R X],
  and due to the opacity of the arrow (needed to avoid undesired
  simplifications), a call to [unfold R] does not perform the
  desired unfolding of the representation predicate [R] in the
  form [Rbody X x], but instead leaves something of the
  form [x ~> (fun x' => Rbody X x')]. The latter is  logically
  equivalent to [(fun x' => Rbody X x') x)] and thus to [Rbody X x],
  but it does not simplify by [simpl] as desired.

  The tactic [xunfold] is meant for performing the desired
  unfolding. Its implementation is a bit of a hack, due to limitations
  of [rewrite], which does not work smoothly under binders, and
  fails to properly identify the beta-redex that could be simplified. *)


(** [xunfold at n] unfold the definition of the arrow [~>]
    at the occurrence [n] in the goal. *)

Definition repr' (A:Type) (S:A->hprop) (x:A) : hprop := S x.

Ltac xunfold_at_core n :=
  let h := fresh "temp" in
  ltac_set (h := repr) at n;
  change h with repr';
  unfold repr';
  clear h.

Tactic Notation "xunfold" "at" constr(n) :=
  xunfold_at_core n.

(** [xunfold E] unfolds all occurrences of the representation
    predicate [E].
    Limitation: won't work if E has more than 12 arguments.

    Implementation: converts all occurrences of repr to repr',
    then unfolds these occurrences one by one, and considers
    them for unfolding. *)

Ltac xunfold_arg_core E :=
  let E := get_head E in (* to get rid of typeclasses arguments *)
  change repr with repr';
  let h := fresh "temp" in
  set (h := repr');
  repeat (
    unfold h at 1;
    let ok := match goal with
      | |- context [ repr' (E) _ ] => constr:(true)
      | |- context [ repr' (E _) _ ] => constr:(true)
      | |- context [ repr' (E _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _ _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _ _ _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _ _ _ _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _ _ _ _ _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _ _ _ _ _ _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _ _ _ _ _ _ _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _ _ _ _ _ _ _ _ _) _ ] => constr:(true)
      | |- context [ repr' (E _ _ _ _ _ _ _ _ _ _ _ _) _ ] => constr:(true)
      | _ => constr:(false)
      end in
    match ok with
    | true => unfold repr'
    | false => change repr' with repr
    end);
  clear h;
  first [ progress (simpl E) | unfold E ].

Tactic Notation "xunfold" constr(E) :=
  xunfold_arg_core E.
Tactic Notation "xunfold" "~" constr(E) := xunfold E; auto_tilde.
Tactic Notation "xunfold" "*" constr(E) := xunfold E; auto_star.

(** [xunfold E] unfolds a specific occurrence of the representation
    predicate [E]. *)

Ltac xunfold_arg_at_core E n :=
  let E := get_head E in (* to get rid of typeclasses arguments *)
  let n := number_to_nat n in
  change repr with repr';
  let h := fresh "temp" in
  set (h := repr');
  let E' := fresh "tempR" in
  set (E' := E);
  let rec aux n :=
    try (
      unfold h at 1;
      let ok := match goal with
        | |- context [ repr' (E') _ ] => constr:(true)
        | |- context [ repr' (E' _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _ _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _ _ _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _ _ _ _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _ _ _ _ _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _ _ _ _ _ _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _ _ _ _ _ _ _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _ _ _ _ _ _ _ _ _) _ ] => constr:(true)
        | |- context [ repr' (E' _ _ _ _ _ _ _ _ _ _ _ _) _ ] => constr:(true)
        | _ => constr:(false)
        end in
      match ok with
      | true =>
         match n with
         | (S O)%nat =>
            (* unfold repr' *)
            match goal with
            | |- context [ repr' (E') ?p ] =>
                change (repr' (E') p) with (E p)
            | |- context [ repr' (E' ?x1) ?p ] =>
                change (repr' (E' x1) p) with (E x1 p)
            | |- context [ repr' (E' ?x1 ?x2) ?p ] =>
                change (repr' (E' x1 x2) p) with (E x1 x2 p)
            | |- context [ repr' (E' ?x1 ?x2 ?x3) ?p ] =>
                change (repr' (E' x1 x2 x3) p) with (E x1 x2 x3 p)
            | |- context [ repr' (E' ?x1 ?x2 ?x3 ?x4) ?p ] =>
                change (repr' (E' x1 x2 x3 x4) p) with (E x1 x2 x3 x4 p)
            | |- context [ repr' (E' ?x1 ?x2 ?x3 ?x4 ?x5) ?p ] =>
                change (repr' (E' x1 x2 x3 x4 x5) p) with (E x1 x2 x3 x4 x5 p)
            | |- context [ repr' (E' ?x1 ?x2 ?x3 ?x4 ?x5 ?x6) ?p ] =>
                change (repr' (E' x1 x2 x3 x4 x5 x6) p) with (E x1 x2 x3 x4 x5 x6 p)
            | |- context [ repr' (E' ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7) ?p ] =>
                change (repr' (E' x1 x2 x3 x4 x5 x6 x7) p) with (E x1 x2 x3 x4 x5 x6 x7 p)
            | |- context [ repr' (E' ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8) ?p ] =>
                change (repr' (E' x1 x2 x3 x4 x5 x6 x7 x8) p) with (E x1 x2 x3 x4 x5 x6 x7 x8 p)
            | |- context [ repr' (E' ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9) ?p ] =>
                change (repr' (E' x1 x2 x3 x4 x5 x6 x7 x8 x9) p) with (E x1 x2 x3 x4 x5 x6 x7 x8 x9 p)
           end;
            first [ progress (simpl E) | unfold E ]
         | (S ?n')%nat => change repr' with repr; aux n'
         end
      | false => change repr' with repr; aux n
      end)
     in
  aux n;
  unfold h;
  clear h;
  change repr' with repr;
  unfold E';
  clear E'.

Tactic Notation "xunfold" constr(E) "at" constr(n) :=
  xunfold_arg_at_core E n.

Ltac xunfoldp_post tt :=
  first [ xpull | xtpull ].

Tactic Notation "xunfoldp" "at" constr(n) :=
  xunfold at n; xunfoldp_post tt.

Tactic Notation "xunfoldp" constr(E) :=
  xunfold E; xunfoldp_post tt.

Tactic Notation "xunfoldp" constr(E) "at" constr(n) :=
  xunfold E at n; xunfoldp_post tt.

Ltac xunfolds_post tt :=
  first [ xsimpl | xtpull ].

Tactic Notation "xunfolds" constr(E) :=
  xunfold E; xunfolds_post tt.

Tactic Notation "xunfolds" "~" constr(E) :=
  xunfold E; xunfolds_post tt; auto_tilde.

Tactic Notation "xunfolds" "*" constr(E) :=
  xunfold E; xunfolds_post tt; auto_star.

Tactic Notation "xunfolds" "at" constr(n) :=
  xunfold at n; xunfolds_post tt.

Tactic Notation "xunfolds" constr(E) "at" constr(n) :=
  xunfold E at n; xunfolds_post tt.


(* ---------------------------------------------------------------------- *)
(* ** Set [repr] to be opaque *)

Global Opaque repr.

End SepSetupCredits.



(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Body of the functor with dummy credits *)

Module SepSetup (SH : SepCore).

(** Definition of the functor argument *)

Module Export SHC <: SepCoreCredits.

Include SH.

Open Scope heap_scope.

Definition use_credits : bool :=
  false.

Notation "'credits'" := Z.

Definition heap_credits (n:credits) : heap :=
  heap_empty.

Lemma heap_compat_credits : forall n m,
  heap_compat (heap_credits n) (heap_credits m).
Proof using. intros. applys heap_compat_empty_l. Qed.

Lemma heap_credits_skip :
  use_credits = false ->
  forall n, heap_credits n = heap_empty.
Proof using. auto. Qed.

Lemma heap_credits_zero :
  heap_credits 0 = heap_empty.
Proof using. auto. Qed.

Lemma heap_credits_add : forall n m,
  heap_credits (n + m) = heap_union (heap_credits n) (heap_credits m).
Proof using. intros. rewrite* heap_union_empty_l. Qed.

Lemma heap_credits_affine : forall n,
  n >= 0 ->
  heap_affine (heap_credits n).
Proof using. intros. applys heap_affine_empty. Qed.

End SHC.

(** Instantiation *)

Module Export Setup := SepSetupCredits SHC.

End SepSetup.
