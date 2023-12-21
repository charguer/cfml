(**

This file formalizes Separation Logic with possibly negative
time credits. It is described in the paper:

"Formal Proof and Analysis of an Incremental Cycle Detection Algorithm"
(ITP'19)

It is a variant of the Separation Logic with time credits in [nat],
described in the papers:

- Machine-Checked Verification of the Correctness and Amortized
  Complexity of an Efficient Union-Find Implementation (ITP'15)

- Verifying the Correctness and Amortized Complexity of a Union-Find
  Implementation in Separation Logic with Time Credits (JAR'17)

This file contains:
- a definition of heaps as finite maps from location to values
  paired with a natural number,
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
Open Scope fmap_scope.



(* ********************************************************************** *)
(* * Semantics *)

(* ---------------------------------------------------------------------- *)
(* ** Big-step evaluation with counting of the number of beta reductions
    (used by the formalization of Separation Logic with time credits) *)

Section Redn.
Local Open Scope nat_scope.
Local Open Scope fmap_scope.

Implicit Types t : trm.
Implicit Types v : val.
Implicit Types b : bool.

Inductive eval : nat -> state -> trm -> state -> val -> Prop :=
  | eval_val : forall m v,
      eval 0 m (trm_val v) m v
  | eval_fix : forall m f x t1,
      eval 0 m (trm_fix f x t1) m (val_fix f x t1)
  | eval_if : forall n m1 m2 b r t1 t2,
      eval m1 n (if b then t1 else t2) m2 r ->
      eval m1 n (trm_if (val_bool b) t1 t2) m2 r
  | eval_let : forall n1 n2 m1 m2 m3 z t1 t2 v1 r,
      eval n1 m1 t1 m2 v1 ->
      eval n2 m2 (subst1 z v1 t2) m3 r ->
      eval (n1+n2) m1 (trm_let z t1 t2) m3 r
  | eval_app_arg : forall n1 n2 n3 m1 m2 m3 m4 t1 t2 v1 v2 f x t r,
      eval n1 m1 t1 m2 v1 ->
      eval n2 m2 t2 m3 v2 ->
      v1 = val_fix f x t ->
      eval n3 m3 (subst2 f v1 x v2 t) m4 r ->
      eval (n1+n2+n3+1) m1 (trm_app t1 t2) m4 r
  | eval_ref : forall m v l,
      ~ Fmap.indom m l ->
      l <> null ->
      eval 0 m (val_ref v) (Fmap.update m l v) (val_loc l)
  | eval_get : forall m l,
      Fmap.indom m l ->
      eval 0 m (val_get (val_loc l)) m (Fmap.read m l)
  | eval_set : forall m l v,
      Fmap.indom m l ->
      eval 0 m (val_set (val_loc l) v) (Fmap.update m l v) val_unit
  | eval_free : forall m l,
      Fmap.indom m l ->
      eval 0 m (val_free (val_loc l)) (Fmap.remove m l) val_unit.

Hint Resolve eval_val.

Lemma eval_app_fix_val : forall n m1 m2 v1 v2 f x t r,
  v1 = val_fix f x t ->
  eval n m1 (subst2 f v1 x v2 t) m2 r ->
  eval (n+1) m1 (trm_app v1 v2) m2 r.
Proof using.
  introv E M. subst. applys_eq* eval_app_arg. math.
Qed.

Lemma eval_ref_sep : forall s1 s2 v l,
  l <> null ->
  s2 = Fmap.single l v ->
  Fmap.disjoint s2 s1 ->
  eval 0 s1 (val_ref v) (Fmap.union s2 s1) (val_loc l).
Proof using.
  introv Nl -> D. forwards Dv: Fmap.indom_single l v.
  rewrite <- Fmap.update_eq_union_single. applys~ eval_ref.
  { intros N. applys~ Fmap.disjoint_inv_not_indom_both D N. }
Qed.

Lemma eval_get_sep : forall s s1 s2 l v,
  s = Fmap.union s1 s2 ->
  Fmap.disjoint s1 s2 ->
  s1 = Fmap.single l v ->
  eval 0 s (val_get (val_loc l)) s v.
Proof using.
  introv -> D ->. forwards Dv: Fmap.indom_single l v.
  applys_eq eval_get.
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
  { applys~ Fmap.indom_union_l. }
Qed.

Lemma eval_set_sep : forall s s' h1 h1' h2 l v v',
  s = Fmap.union h1 h2 ->
  s' = Fmap.union h1' h2 ->
  Fmap.disjoint h1 h2 ->
  h1 = Fmap.single l v ->
  h1' = Fmap.single l v' ->
  eval 0 s (val_set (val_loc l) v') s' val_unit.
Proof using.
  introv -> -> D -> ->. forwards Dv: Fmap.indom_single l v.
  applys_eq eval_set.
  { rewrite~ Fmap.update_union_l. fequals.
    rewrite~ Fmap.update_single. }
  { applys~ Fmap.indom_union_l. }
Qed.

Lemma eval_free_sep : forall s1 s2 v l,
  s1 = Fmap.union (Fmap.single l v) s2 ->
  Fmap.disjoint (Fmap.single l v) s2 ->
  eval 0 s1 (val_free l) s2 val_unit.
Proof using.
  introv -> D. forwards Dv: Fmap.indom_single l v.
  applys_eq eval_free.
  { rewrite~ Fmap.remove_union_single_l.
    intros Dl. applys Fmap.disjoint_inv_not_indom_both D Dl.
    applys Fmap.indom_single. }
  { applys~ Fmap.indom_union_l. }
Qed.

End Redn.



(* ********************************************************************** *)
(* * Core of the logic *)

Module Export SepCreditsCore <: SepCore.


(* ---------------------------------------------------------------------- *)
(* ** Representation of credits *)

(** Representation of credits *)

Definition credits : Type := int.

(** Hint for [math] tactic to unfold [credits] definition *)

Ltac math_0 ::= unfolds credits.

(** Zero and one credits *)

Definition credits_zero : credits := 0.

Definition credits_one : credits := 1.


(* ---------------------------------------------------------------------- *)
(** Heaps *)

Declare Scope heap_scope.

(** Type of heaps *)

Definition heap : Type := (state * credits)%type.

(** Empty heap *)

Definition heap_empty : heap :=
  (Fmap.empty, 0).

(** Projections *)

Definition heap_state (h:heap) : state :=
  match h with (m,c) => m end.

Definition heap_credits (h:heap) : credits :=
  match h with (m,c) => c end.

Notation "h '^s'" := (heap_state h)
   (at level 9, format "h '^s'") : heap_scope.

Notation "h '^c'" := (heap_credits h)
   (at level 9, format "h '^c'") : heap_scope.

Open Scope heap_scope.

(** Disjoint heaps *)

Definition heap_disjoint (h1 h2 : heap) : Prop :=
  Fmap.disjoint (h1^s) (h2^s).

Notation "\# h1 h2" := (heap_disjoint h1 h2)
  (at level 40, h1 at level 0, h2 at level 0, no associativity) : heap_scope.

(** Union of heaps *)

Definition heap_union (h1 h2 : heap) : heap :=
   (h1^s \+ h2^s, h1^c + h2^c).

Declare Scope heap_union_scope.

Notation "h1 \u h2" := (heap_union h1 h2)
   (at level 37, right associativity) : heap_union_scope.

Local Open Scope heap_union_scope.

(** Affine heaps are those such that [heap_credits c >= 0] *)

Definition heap_affine (h:heap) : Prop :=
  h^c >= 0.

(** Properties of [heap_affine] *)

Lemma heap_affine_heap_empty :
  heap_affine heap_empty.
Proof using.
  unfold heap_affine, heap_empty. simpl. math.
Qed.

Lemma heap_affine_heap_union : forall h1 h2,
  heap_affine h1 ->
  heap_affine h2 ->
  heap_affine (h1 \u h2).
Proof using.
  intros [m1 n1] [m2 n2] M1 M2. unfolds heap_affine, heap_union.
  simpls. math.
Qed.


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

Definition hstar (H1 H2 : hprop) : hprop :=
  fun h => exists h1 h2,
              H1 h1
           /\ H2 h2
           /\ heap_disjoint h1 h2
           /\ h = h1 \u h2.

Definition hexists A (J : A -> hprop) : hprop :=
  fun h => exists x, J x h.

Definition hforall A (J : A -> hprop) : hprop :=
  fun h => forall x, J x h.

(** Notation *)

Notation "\[]" := (hempty)
  (at level 0) : heap_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : heap_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : heap_scope.


(* ---------------------------------------------------------------------- *)
(* ** Types *)

Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ---------------------------------------------------------------------- *)
(* ** Tactic for automation *)

Hint Extern 1 (_ = _ :> heap) => fmap_eq.

Lemma heap_disjoint_def : forall h1 h2,
  heap_disjoint h1 h2 = Fmap.disjoint (h1^s) (h2^s).
Proof using. auto. Qed.

Hint Rewrite heap_disjoint_def : rew_disjoint.

Tactic Notation "fmap_disjoint_pre" :=
  subst; rew_disjoint; jauto_set.

Hint Extern 1 (heap_disjoint _ _) => fmap_disjoint_pre.


(* ---------------------------------------------------------------------- *)
(* ** Equalities on [heap] *)

Lemma heap_eq : forall h1 h2,
  (h1^s = h2^s /\ h1^c = h2^c) -> h1 = h2.
Proof using.
  intros (s1,n1) (s2,n2) (M1&M2). simpls. subst. fequals.
Qed.

Lemma heap_eq_forward : forall h1 h2,
  h1 = h2 ->
  h1^s = h2^s /\ h1^c = h2^c.
Proof using. intros (s1,n1) (s2,n2) M. inverts~ M. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [heap_disjoint] *)

Lemma heap_disjoint_sym : forall h1 h2,
  \# h1 h2 ->
  \# h2 h1.
Proof using.
  intros [m1 n1] [m2 n2] H. simpls.
  hint Fmap.disjoint_sym. autos*.
Qed.

Lemma heap_disjoint_comm : forall h1 h2,
  \# h1 h2 = \# h2 h1.
Proof using.
  intros [m1 n1] [m2 n2]. simpls.
  hint heap_disjoint_sym. extens*.
Qed.

Lemma heap_disjoint_empty_l : forall h,
  \# heap_empty h.
Proof using. intros [m n]. hint Fmap.disjoint_empty_l. hnfs*. Qed.

Lemma heap_disjoint_empty_r : forall h,
  \# h heap_empty.
Proof using. intros [m n]. hint Fmap.disjoint_empty_r. hnfs*. Qed.

Lemma heap_disjoint_union_eq_r : forall h1 h2 h3,
  \# h1 (h2 \u h3) = (\# h1 h2 /\ \# h1 h3).
Proof using.
  intros [m1 n1] [m2 n2] [m3 n3].
  unfolds heap_disjoint, heap_union. simpls.
  rewrite Fmap.disjoint_union_eq_r. extens*.
Qed.

Lemma heap_disjoint_union_eq_l : forall h1 h2 h3,
  \# (h2 \u h3) h1 = (\# h1 h2 /\ \# h1 h3).
Proof using.
  intros. rewrite heap_disjoint_comm.
  apply heap_disjoint_union_eq_r.
Qed.

Hint Resolve
   heap_disjoint_sym
   heap_disjoint_empty_l heap_disjoint_empty_r
   heap_disjoint_union_eq_l heap_disjoint_union_eq_r.

Tactic Notation "rew_disjoint" :=
  autorewrite with rew_disjoint in *.
Tactic Notation "rew_disjoint" "*" :=
  rew_disjoint; auto_star.


(* ---------------------------------------------------------------------- *)
(* ** Properties of [heap_union] *)

Lemma heap_union_comm : forall h1 h2,
  \# h1 h2 ->
  h1 \u h2 = h2 \u h1.
Proof using.
  intros [m1 n1] [m2 n2] H. unfold heap_union.
  simpl. fequals. fmap_eq. math.
Qed.

Lemma heap_union_assoc : forall h1 h2 h3,
  (h1 \u h2) \u h3 = h1 \u (h2 \u h3).
Proof using.
  intros [m1 n1] [m2 n2] [m3 n3]. unfolds heap_union.
  simpl. fequals. fmap_eq. math.
Qed.

Lemma heap_union_empty_l : forall h,
  heap_empty \u h = h.
Proof using.
  intros [m n]. unfold heap_union, heap_empty. simpl.
  fequals. apply~ Fmap.union_empty_l.
Qed.

Lemma heap_union_empty_r : forall h,
  h \u heap_empty = h.
Proof using.
  intros. rewrite~ heap_union_comm. apply~ heap_union_empty_l.
Qed.

Lemma heap_union_state : forall h1 h2,
  heap_state (h1 \u h2) = (heap_state h1) \+ (heap_state h2).
Proof using. intros (m1&n1) (m2&n2). auto. Qed.

Lemma heap_union_credits : forall h1 h2,
  heap_credits (h1 \u h2) = (heap_credits h1 + heap_credits h2).
Proof using. intros (m1&n1) (m2&n2). auto. Qed.

Hint Resolve heap_union_comm
   heap_union_empty_l heap_union_empty_r.

Hint Rewrite heap_union_state : rew_disjoint.

(* Extend the tactic [fmap_eq] with distribution of [heap_state] *)
Hint Rewrite heap_union_state : rew_fmap_for_fmap_eq.

Hint Rewrite
  heap_union_empty_l heap_union_empty_r
  heap_union_state heap_union_credits : rew_heap.

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
(* ** Properties of empty *)

Lemma hempty_intro :
  \[] heap_empty.
Proof using. hnfs~. Qed.

Lemma hempty_inv : forall h,
  \[] h ->
  h = heap_empty.
Proof using. auto. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Core properties *)

Section Properties.

Hint Resolve hempty_intro.

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
  intros H1 H2. unfold hprop, hstar. extens. intros h.
  iff (h1&h2&M1&M2&D&U); rewrite~ heap_union_comm in U; exists* h2 h1.
Qed.

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using.
  intros H1 H2 H3. unfold hprop, hstar. extens. intros h. split.
  { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U). subst h'.
    exists h1 (h2 \u h3). splits~.
    { exists h2 h3. splits*. }
    { subst. applys heap_eq. split. { fmap_eq. } { simpl; math. } } }
  { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U). subst h'.
    exists (h1 \u h2) h3. splits~.
    { exists h1 h2. splits*. }
    { subst. applys heap_eq. split. { fmap_eq. } { simpl; math. } } }
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
  introv M. lets ->: hempty_inv M. applys heap_affine_heap_empty.
Qed.

Lemma haffine_hstar : forall H1 H2,
  haffine H1 ->
  haffine H2 ->
  haffine (H1 \* H2).
Proof using.
  introv F1 F2 (h1&h2&M1&M2&D&->). applys* heap_affine_heap_union.
Qed.

End Properties.

End SepCreditsCore.



(* ********************************************************************** *)
(* * Derived properties of the logic *)

(** Here, we instantiate the functors to obtained derived definitions,
  lemmas, notation, and tactics. *)

Module Export SepCreditsSetup := SepSetup SepCreditsCore.
Export SepCreditsCore.

Local Open Scope heap_union_scope.

Implicit Types H : hprop.
Implicit Types Q : val->hprop.
Implicit Types P : Prop.

(* ********************************************************************** *)
(* * Specific properties of the logic *)


(* ---------------------------------------------------------------------- *)
(* ** Auxiliary lemmas *)

Section Aux.

Lemma hpure_inv : forall P h,
  \[P] h ->
  P /\ h = heap_empty.
Proof using.
  introv M. lets (HP&HE): hpure_inv_hempty M.
  lets*: hempty_inv HE.
Qed.

Lemma hpure_intro : forall P,
  P ->
  \[P] heap_empty.
Proof using. introv M. applys~ hpure_intro_hempty. applys hempty_intro. Qed.

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  heap_disjoint h1 h2 ->
  (H1 \* H2) (h1 \u h2).
Proof using. intros. exists~ h1 h2. Qed.

Lemma hstar_inv : forall H1 H2 h,
  (H1 \* H2) h ->
  exists h1 h2, H1 h1 /\ H2 h2 /\ heap_disjoint h1 h2 /\ h = h1 \u h2.
Proof using. introv M. hnf in M. eauto. Qed.

End Aux.


(* ---------------------------------------------------------------------- *)
(* ** Singleton heap *)

Definition hsingle (l:loc) (v:val) : hprop :=
  fun h => h^s = Fmap.single l v /\ h^c = credits_zero /\ l <> null.

Notation "l '~~~>' v" := (hsingle l v)
  (at level 32, no associativity) : heap_scope.
Notation "l '~~>' v" := (hsingle l v)
  (at level 32, no associativity) : heap_scope.

Lemma hsingle_intro : forall l v,
  l <> null ->
  (l ~~~> v) ((Fmap.single l v), credits_zero).
Proof using. intros. split~. Qed.

Lemma hsingle_inv : forall h l v,
  (l ~~~> v) h ->
  h = (Fmap.single l v, credits_zero) /\ (l <> null).
Proof using. intros (s,n) l v (E1&E2&N). simpls*. Qed.

Lemma hstar_hsingle_same_loc : forall (l:loc) (v1 v2:val),
  (l ~~~> v1) \* (l ~~~> v2) ==> \[False].
Proof using.
  intros. unfold hsingle.
  intros h ((m1&n1)&(m2&n2)&(E1&X1&N1)&(E2&X2&N2)&D&E). false.
  subst. applys* Fmap.disjoint_single_single_same_inv l v1 v2.
  unfolds in D. rewrite <- E1. rewrite <- E2. auto.
Qed.

Arguments hstar_hsingle_same_loc : clear implicits.

Lemma haffine_hsingle : forall l v,
  haffine (hsingle l v).
Proof using.
  intros. rewrite haffine_eq.
  introv (E&Ec&_). unfold heap_affine. rewrite Ec.
  unfold credits_zero. math.
Qed.

Global Opaque hsingle.

(* ** Configure [hcancel] to make it aware of [hsingle] *)

(* not needed? *)
Ltac xsimpl_hook H ::=
  match H with
  | hsingle _ _ => xsimpl_cancel_same H
  end.

Global Opaque hsingle.


(* ---------------------------------------------------------------------- *)
(* ** Credits heap *)

Definition mk_heap_credits (n:credits) : heap :=
  (Fmap.empty:state, n).

Definition hcredits (n:credits) : hprop :=
  fun h => h = mk_heap_credits n.

Notation "'\$' n" := (hcredits n)
  (at level 40, format "\$ n") : heap_scope.

Lemma heap_credit_mk_heap_credits : forall n,
  (mk_heap_credits n)^c = n.
Proof using. auto. Qed.

Hint Rewrite heap_credit_mk_heap_credits : rew_heap.

Lemma hcredits_mk_heap_credits : forall n,
  (\$n) (mk_heap_credits n).
Proof using. intros. unfolds* hcredits. Qed.

Lemma hcredits_inv : forall n h,
  (\$n) h ->
  h^s = Fmap.empty /\ h^c = n.
Proof using.
  introv N. unfolds hcredits, mk_heap_credits. subst*.
Qed.

Lemma haffine_hcredits : forall n,
  n >= 0 ->
  haffine (\$ n).
Proof using.
  introv N. rewrite haffine_eq. introv Hh.
  lets (Hs&Hc): hcredits_inv Hh. unfold heap_affine. rewrite* Hc.
Qed.

Global Opaque hcredits.


(* ---------------------------------------------------------------------- *)
(* ** Affinity *)

Section Affine.
Transparent haffine.

Lemma hgc_intro : forall h,
  h^c >= 0 ->
  \GC h.
Proof using. introv N. applys* hgc_of_heap_affine. Qed.

Lemma haffine_heap_inv : forall H h,
  haffine H ->
  H h ->
  h^c >= 0.
Proof using. introv F M. applys F M. Qed.

Lemma hgc_heap_inv : forall h,
  \GC h ->
  h^c >= 0.
Proof using. introv N. applys* haffine_heap_inv. applys haffine_hgc. Qed.

End Affine.

Global Opaque heap_affine.


(* ---------------------------------------------------------------------- *)
(* ** Properties of credits *)

Section Credits.
Transparent hcredits hempty hpure hstar mk_heap_credits heap_union heap_disjoint.

Lemma hcredits_zero_eq : \$ 0 = \[].
Proof using.
  unfold hcredits, hempty, heap_empty.
  applys pred_ext_1. intros [m n]; simpl. unfold mk_heap_credits. iff*.
Qed.

Lemma hcredits_add_eq : forall n m,
  \$ (n+m) = \$ n \* \$ m.
Proof using.
  intros c1 c2. unfold hcredits, hstar, heap_union, heap_disjoint, mk_heap_credits.
  applys pred_ext_1. intros [m n]. iff M.
  { inverts M. exists. splits*; simpl; try fmap_eq.
    { fequals. fmap_eq. math. } }
  { destruct M as ([m1 n1]&[m2 n2]&M3&M4&M5&M6).
    inverts M3. inverts M4. rewrite M6. simpl. fequals. fmap_eq. }
Qed.

Lemma hcredits_sub : forall n m,
  (n >= m) ->
  \$ n ==> \$ m \* \$ (n-m).
Proof using.
  introv M. rewrite <- hcredits_add_eq.
  math_rewrite (m + (n-m) = n). auto.
Qed.

Lemma hcredits_drop : forall n m,
  n >= m ->
  exists H', haffine H' /\ \$ n ==> \$ m \* H'.
Proof using.
  introv M. exists (\$(n-m)). split.
  { apply haffine_hcredits. math. }
  { applys* hcredits_sub. }
Qed.

End Credits.



(* ********************************************************************** *)
(* * Reasoning Rules *)

Implicit Types t : trm.
Implicit Types v w : val.
Implicit Types h : heap.
Implicit Types p : loc.


(* ---------------------------------------------------------------------- *)
(* ** Definitions of [pay] *)

Definition pay_one H H' :=
  H ==> (\$ 1) \* H'.

Lemma pay_one_elim : forall H H' h,
  pay_one H H' ->
  H h ->
  exists h', H' h' /\ h = (mk_heap_credits 1 \u h').
Proof using.
  introv HP N. lets N': (rm HP) (rm N). rew_heap in N'.
  destruct N' as (h1&h2&N1&N2&N3&N4).
  lets (N1'&N2'): hcredits_inv (rm N1).
  destruct h1 as [n1 c1]. simpls. subst*.
Qed.

Lemma pay_one_frame : forall H H' HF,
  pay_one H H' ->
  pay_one (H \* HF) (H' \* HF).
Proof using.
  introv M. unfolds pay_one. xchange M.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Definition of Hoare triples *)


Definition hoare (t:trm) (H:hprop) (Q:val->hprop) :=
  forall h, H h -> exists n h' v, eval n (heap_state h) t (heap_state h') v
                             /\ Q v h'
                             /\ heap_credits h = n + heap_credits h'.

(* ---------------------------------------------------------------------- *)
(* ** Hoare rules *)

Lemma hoare_conseq : forall t H' Q' H Q,
  hoare t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoare t H Q.
Proof using.
  introv M MH MQ HF. forwards (n&h'&v&R&K&S): M h.
  { applys* MH. }
  exists n h' v. splits~. { applys MQ K. }
Qed.

Lemma hoare_val : forall H' v,
  hoare (trm_val v) H' (fun r => \[r = v] \* H').
Proof using.
  introv. intros h K. exists 0%nat h v. splits~.
  { applys eval_val. }
  { rewrite* hstar_hpure_l. }
Qed.

Lemma hoare_fix : forall H' f x t1,
  hoare (trm_fix f x t1) H' (fun r => \[r = (val_fix f x t1)] \* H').
Proof using.
  introv. intros h K. exists 0%nat h (val_fix f x t1). splits~.
  { applys eval_fix. }
  { rewrite* hstar_hpure_l. }
Qed.

Lemma hoare_app_fix : forall v1 v2 (f:var) x t1 H H' Q,
  v1 = val_fix f x t1 ->
  f <> x ->
  pay_one H H' ->
  hoare (subst x v2 (subst f v1 t1)) H' Q ->
  hoare (trm_app v1 v2) H Q.
Proof using.
  introv E D HP M. intros h K0.
  lets (h'&K'&->): pay_one_elim (rm HP) (rm K0).
  forwards (n&h''&v&R1&K1&E1): (rm M) K'.
  exists (n+1)%nat h'' v. splits*.
  { applys* eval_app_fix_val. applys_eq R1; try fmap_eq. }
  { rew_heap. math. }
Qed.

Lemma hoare_let : forall z t1 t2 H Q Q1,
  hoare t1 H Q1 ->
  (forall v, hoare (subst1 z v t2) (Q1 v) Q) ->
  hoare (trm_let z t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (n1&h1'&v1&R1&K1&E1): (rm M1).
  forwards* (n2&h2'&v2&R2&K2&E2): (rm M2).
  exists (n1+n2)%nat h2' v2. splits~.
  { applys~ eval_let R2. }
  { math. }
Qed.

Lemma hoare_if : forall (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros h Hh. forwards* (n1&h1'&v1&R1&K1&E1): (rm M1).
  exists n1 h1' v1. splits*. { applys* eval_if. }
Qed.

Lemma hoare_ref : forall H v,
  hoare (val_ref v)
    H
    (fun r => (\exists l, \[r = val_loc l] \* l ~~~> v) \* H).
Proof using.
  intros. intros h Hh.
  forwards~ (l&Dl&Nl): (Fmap.single_fresh null (h^s) v).
  forwards~ Hh1': hsingle_intro l v.
  sets h1': ((Fmap.single l v),credits_zero).
  exists 0%nat (h1' \u h) (val_loc l). splits~.
  { applys~ eval_ref_sep. }
  { apply~ hstar_intro. { exists l. xsimplh~. } }
Qed.

Lemma hoare_get : forall H v l,
  hoare (val_get (val_loc l))
    ((l ~~~> v) \* H)
    (fun x => \[x = v] \* (l ~~~> v) \* H).
Proof using.
  intros. intros h Hh. exists 0%nat h v. splits~.
  { destruct Hh as (h1&h2&(N1a&N1b)&N2&N3&N4).
    subst h. applys* eval_get_sep. }
  { xsimplh~. }
Qed.

Lemma hoare_set : forall H w l v,
  hoare (val_set (val_loc l) w)
    ((l ~~~> v) \* H)
    (fun r => \[r = val_unit] \* (l ~~~> w) \* H).
Proof using.
  intros. intros h Hh. destruct Hh as (h1&h2&(N1a&N1b&N1c)&N2&N3&N4).
  forwards~ Hh1': hsingle_intro l w.
  sets h1': ((Fmap.single l w), credits_zero).
  exists 0%nat (h1' \u h2) val_unit. splits~.
  { subst h. applys eval_set_sep; rew_heap*. }
  { rewrite hstar_hpure. split~.
    { applys hstar_intro.
      { hnfs~. }
      { xsimplh~. }
      { unfold h1'. unfolds heap_disjoint. rewrite N1a in N3.
        applys~ Fmap.disjoint_single_set v. } } }
   { subst h h1'. rew_heap. simpl. math. }
Qed.

Lemma hoare_free : forall H l v,
  hoare (val_free (val_loc l))
    ((l ~~~> v) \* H)
    (fun r => \[r = val_unit] \* H).
Proof using.
  intros. intros h Hh. destruct Hh as (h1&h2&N1&N2&N3&N4).
  lets (E1&X1): hsingle_inv N1.
  exists 0%nat h2 val_unit. split.
  { subst h h1. applys* eval_free_sep. }
  { subst h h1. rewrite* hstar_hpure. }
Qed.

(* ---------------------------------------------------------------------- *)
(* ** Definition of SL triples *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall H', hoare t (H \* H') (Q \*+ H' \*+ \GC).

(** Triple satisfy the [local] predicate *)

Lemma local_triple : forall t,
  local (triple t).
Proof using.
  intros. applys local_intro. intros H Q M H'.
  intros h (h1&h2&N1&N2&N3&N4). hnf in M.
  lets (H1&H2&Q1&R): M N1.
  rewrite <- hstar_assoc, hstar_comm, hstar_hpure in R.
  lets ((R1&R2)&R3): R.
  forwards (n&h'&v&S1&S2&S3): R1 (H2\*H') h.
  { subst h. rewrite <- hstar_assoc. exists~ h1 h2. }
  exists n h' v. splits~. rewrite <- hstar_hgc_hgc.
  applys himpl_inv S2.
  xchange (R2 v). xsimpl.
Qed.

Hint Resolve local_triple.


(* ---------------------------------------------------------------------- *)
(* ** Structural rules *)

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

Lemma triple_hgc_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \GC) Q.
Proof using. intros. applys* local_hgc_pre. Qed.

Lemma triple_hgc_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.
Proof using. intros. applys* local_hgc_post. Qed.

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

Lemma triple_conseq_frame_hgc : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \GC ->
  triple t H Q.
Proof using. intros. applys* local_conseq_frame_hgc. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Auxiliary conversions *)

Lemma triple_of_hoare : forall t H Q,
  (forall H',
     exists Q', hoare t (H \* H') Q' /\ Q' ===> Q \*+ H' \*+ \GC) ->
  triple t H Q.
Proof using.
  introv M. intros H'. forwards* (Q'&R&W): M H'. applys* hoare_conseq R.
Qed.

Lemma hoare_of_triple : forall t H Q HF,
  triple t H Q ->
  hoare t ((H \* HF) \* \GC) (fun r => (Q r \* HF) \* \GC).
Proof using.
  introv M. applys hoare_conseq. { applys M. } { xsimpl. } { xsimpl. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** SL rules for terms *)

Lemma triple_val : forall v,
  triple (trm_val v) \[] (fun r => \[r = v]).
Proof using.
  intros. intros H'. rew_heap.
  applys hoare_conseq.
  { applys* hoare_val. }
  { xsimpl. }
  { xsimpl*. }
Qed.

Lemma triple_val_framed : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using.
  introv M. applys* local_conseq_frame.
  { applys triple_val. }
  { xsimpl. }
  { xchanges M. intros ? ->. xsimpl*. }
Qed.

Lemma triple_fix : forall f x t1,
  triple (trm_fix f x t1) \[] (fun r => \[r = (val_fix f x t1)]).
Proof using.
  intros. intros H'. rew_heap.
  applys hoare_conseq.
  { applys* hoare_fix. }
  { xsimpl. }
  { xsimpl*. }
Qed.

Lemma triple_fix_framed : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triple (trm_fix f x t1) H Q.
Proof using.
  introv M. applys* local_conseq_frame.
  { applys triple_fix. }
  { xsimpl. }
  { xchanges M. intros ? ->. xsimpl*. }
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

Lemma triple_if : forall (b:bool) t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros H'. applys hoare_if. applys~ M1.
Qed.

Lemma triple_app_fix : forall (f:var) F x X t1 H H' Q,
  F = val_fix f x t1 ->
  f <> x ->
  pay_one H H' ->
  triple (subst2 f F x X t1) H' Q ->
  triple (trm_app F X) H Q.
Proof using.
  introv EF N HP M. intros H''. applys* hoare_app_fix EF N.
  { applys* pay_one_frame. }
Qed.

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists l, \[r = val_loc l] \* l ~~~> v).
Proof using.
  intros. applys~ triple_of_hoare.
  intros H'. esplit. split.
  { rew_heap. applys* hoare_ref. } { xsimpl*. }
Qed.

Lemma triple_get : forall v l,
  triple (val_get (val_loc l))
    (l ~~~> v)
    (fun x => \[x = v] \* (l ~~~> v)).
Proof using.
  intros. applys triple_of_hoare. intros H'.
  esplit; split. { applys* hoare_get. } { xsimpl*. }
Qed.

Lemma triple_set : forall (w:val) l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => \[r = val_unit] \* l ~~~> w).
Proof using.
  intros. applys triple_of_hoare. intros H'.
  esplit; split. { applys* hoare_set. } { xsimpl*. }
Qed.

Lemma triple_free : forall l v,
  triple (val_free (val_loc l))
    (l ~~~> v)
    (fun r => \[r = val_unit]).
Proof using.
  intros. applys triple_of_hoare. intros H'.
  esplit; split. { applys* hoare_free. } { xsimpl*. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Intrepretation for full executions *)

(** Interpretation of triples for full executions:
    the number of credits in the precondition is an upper bound
    on the number of steps taken by the execution.

    The post-condition is required to be affine to ensure that
    it does not store negative credits. *)

Lemma triple_hcredits : forall t m Q,
  triple t (\$ m) Q ->
  haffine_post Q ->
  exists n s' v,
     eval n Fmap.empty t s' v
  /\ ((n:int) <= m).
Proof using.
  introv M HF. forwards (n&h&v&R&K&C): (rm M) hempty (mk_heap_credits m).
  { rew_heap. applys hcredits_mk_heap_credits. }
  rew_heap in K. exists n (h^s) v. splits*.
  { simpls. forwards N: haffine_heap_inv K.
    { applys haffine_hstar. applys* HF. applys haffine_hgc. }
   math. }
Qed.

