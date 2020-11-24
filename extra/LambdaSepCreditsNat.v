(**

This file formalizes "Separation Logic with Time Credits",
following the presentation by Arthur Charguéraud and
François Pottier described in the following papers:

- Machine-Checked Verification of the Correctness and Amortized
  Complexity of an Efficient Union-Find Implementation (ITP'15)

- Verifying the Correctness and Amortized Complexity of a Union-Find
  Implementation in Separation Logic with Time Credits (JAR'17)

This file contains:
- a definition of heaps as finite maps from location to values
  paired with a natural number,
- an instantiation of the functor from the file SepFunctor.v,
- a definition of triples,
- statement and proofs of SL reasoning rules.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Export LambdaSemantics SepFunctor.
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

Inductive red : nat -> state -> trm -> state -> val -> Prop :=
  | red_val : forall m v,
      red 0 m (trm_val v) m v
  | red_fix : forall m f x t1,
      red 0 m (trm_fix f x t1) m (val_fix f x t1)
  | red_if : forall n1 n2 m1 m2 m3 b r t0 t1 t2,
      red n1 m1 t0 m2 (val_bool b) ->
      red n2 m2 (if b then t1 else t2) m3 r ->
      red (n1+n2) m1 (trm_if t0 t1 t2) m3 r
  | red_let : forall n1 n2 m1 m2 m3 z t1 t2 v1 r,
      red n1 m1 t1 m2 v1 ->
      red n2 m2 (subst1 z v1 t2) m3 r ->
      red (n1+n2) m1 (trm_let z t1 t2) m3 r
  | red_app_arg : forall n1 n2 n3 m1 m2 m3 m4 t1 t2 v1 v2 f x t r,
      red n1 m1 t1 m2 v1 ->
      red n2 m2 t2 m3 v2 ->
      v1 = val_fix f x t ->
      red n3 m3 (subst2 f v1 x v2 t) m4 r ->
      red (n1+n2+n3+1) m1 (trm_app t1 t2) m4 r
  | red_ref : forall ma mb v l,
      mb = (fmap_single l v) ->
      \# ma mb ->
      red 0 ma (val_ref v) (mb \+ ma) (val_loc l)
  | red_get : forall m l v,
      fmap_data m l = Some v ->
      red 0 m (val_get (val_loc l)) m v
  | red_set : forall m m' l v,
      m' = fmap_update m l v ->
      red 0 m (val_set (val_loc l) v) m' val_unit.

Hint Resolve red_val.

Lemma red_app_fix_val : forall n m1 m2 v1 v2 f x t r,
  v1 = val_fix f x t ->
  red n m1 (subst2 f v1 x v2 t) m2 r ->
  red (n+1) m1 (trm_app v1 v2) m2 r.
Proof using.
  introv E M. subst. applys equates_5.
  applys* red_app_arg. math.
  (* TODO here and above applys_eq 5 red_app. *)
Qed.

End Redn.



(* ********************************************************************** *)
(* * Core of the logic *)

Module Export SepCreditsCore <: SepCore.


(* ---------------------------------------------------------------------- *)
(* ** Representation of credits *)

(** Representation of credits *)

Definition credits : Type := nat.

(** Zero and one credits *)

Definition credits_zero : credits := 0%nat.

Definition credits_one : credits := 1%nat.


(* ---------------------------------------------------------------------- *)
(** Heaps *)

(** Type of heaps *)

Definition heap : Type := (state * credits)%type.

(** Empty heap *)

Definition heap_empty : heap :=
  (fmap_empty, 0%nat).

(** Projections *)

Coercion heap_state (h:heap) : state :=
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
  \# (h1^s) (h2^s).

Notation "\# h1 h2" := (heap_disjoint h1 h2)
  (at level 40, h1 at level 0, h2 at level 0, no associativity) : heap_scope.

(** Union of heaps *)

Definition heap_union (h1 h2 : heap) : heap :=
   (h1^s \+ h2^s, (h1^c + h2^c)%nat).

Notation "h1 \u h2" := (heap_union h1 h2)
   (at level 37, right associativity) : heap_scope.


(* ---------------------------------------------------------------------- *)
(** Hprop *)

(** Type of heap predicates *)

Definition hprop := heap -> Prop.

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
  heap_disjoint h1 h2 = fmap_disjoint (h1^s) (h2^s).
Proof using. auto. Qed.

Hint Rewrite heap_disjoint_def : rew_disjoint.

Tactic Notation "fmap_disjoint_pre" :=
  subst; rew_disjoint; jauto_set.

Hint Extern 1 (\# _ _) => fmap_disjoint_pre.

Ltac math_0 ::= unfolds credits.


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
  \# h1 h2 -> \# h2 h1.
Proof using.
  intros [m1 n1] [m2 n2] H. simpls.
  hint fmap_disjoint_sym. autos*.
Qed.

Lemma heap_disjoint_comm : forall h1 h2,
  \# h1 h2 = \# h2 h1.
Proof using.
  intros [m1 n1] [m2 n2]. simpls.
  hint fmap_disjoint_sym. extens*.
Qed.

Lemma heap_disjoint_empty_l : forall h,
  \# heap_empty h.
Proof using. intros [m n]. hint fmap_disjoint_empty_l. hnfs*. Qed.

Lemma heap_disjoint_empty_r : forall h,
  \# h heap_empty.
Proof using. intros [m n]. hint fmap_disjoint_empty_r. hnfs*. Qed.

Lemma heap_disjoint_union_eq_r : forall h1 h2 h3,
  \# h1 (h2 \u h3) = (\# h1 h2 /\ \# h1 h3).
Proof using.
  intros [m1 n1] [m2 n2] [m3 n3].
  unfolds heap_disjoint, heap_union. simpls.
  rewrite fmap_disjoint_union_eq_r. extens*.
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
  fequals. apply~ fmap_union_empty_l.
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
  heap_credits (h1 \u h2) = (heap_credits h1 + heap_credits h2)%nat.
Proof using. intros (m1&n1) (m2&n2). auto. Qed.

Hint Resolve heap_union_comm
   heap_union_empty_l heap_union_empty_r.

Hint Rewrite heap_union_state : rew_disjoint.

Hint Rewrite heap_union_state : rew_fmap.

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
  intros. applys hprop_extens. intros h.
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
  intros. applys hprop_extens. intros h. iff M.
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

End Properties.

End SepCreditsCore.



(* ********************************************************************** *)
(* * Derived properties of the logic *)

(** Here, we instantiate the functors to obtained derived definitions,
  lemmas, notation, and tactics. *)

Module Export SepCreditsSetup := SepSetup SepCreditsCore.
Export SepCreditsCore.

Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ********************************************************************** *)
(* * Specific properties of the logic *)

(* ---------------------------------------------------------------------- *)
(* ** Singleton heap *)

Definition hsingle (l:loc) (v:val) : hprop :=
  fun h => h^s = fmap_single l v /\ h^c = credits_zero /\ l <> null.

Notation "l '~~~>' v" := (hsingle l v)
  (at level 32, no associativity) : heap_scope.

Lemma hstar_hsingle_same_loc_disjoint : forall (l:loc) (v1 v2:val),
  (l ~~~> v1) \* (l ~~~> v2) ==> \[False].
Proof using.
  intros. unfold hsingle.
  intros h ((m1&n1)&(m2&n2)&(E1&X1&N1)&(E2&X2&N2)&D&E). false.
  subst. applys* fmap_disjoint_single_single_same_inv l v1 v2.
  unfolds in D. rewrite <- E1. rewrite <- E2. auto.
Qed.

Global Opaque hsingle.

(* ** Configure [hcancel] to make it aware of [hsingle] *)

Ltac hcancel_hook H :=
  match H with
  | hsingle _ _ => hcancel_try_same tt
  end.

Global Opaque hsingle.


(* ---------------------------------------------------------------------- *)
(* ** Credits heap *)

Definition hcredits (n:nat) : hprop :=
  fun h => h^s = fmap_empty /\ h^c = n.

Notation "'\$' n" := (hcredits n)
  (at level 40, format "\$ n") : heap_scope.

Lemma hcredits_inv : forall h n,
  (\$ n) h -> h = (fmap_empty,n).
Proof using. intros (m,n') n (M1&M2). simpls. subst*. Qed.

Global Opaque hcredits.


(* ---------------------------------------------------------------------- *)
(* ** Properties of credits *)

Section Credits.
Transparent hcredits hempty hpure hstar
  heap_union heap_disjoint.

Lemma credits_zero_eq : \$ 0 = \[].
Proof using.
  unfold hcredits, hempty, heap_empty.
  applys pred_ext_1. intros [m n]; simpl. iff [M1 M2] M.
  { subst~. }
  { inverts~ M. }
Qed.

Lemma credits_split_add : forall (n m : nat),
  \$ (n+m) = \$ n \* \$ m.
Proof using.
  intros c1 c2. unfold hcredits, hstar, heap_union, heap_disjoint.
  applys pred_ext_1. intros [m n].
  iff [M1 M2] ([m1 n1]&[m2 n2]&(M1&E1)&(M2&E2)&M3&M4).
  { exists (fmap_empty:state,c1) (fmap_empty:state,c2). simpls. splits*. }
  { simpls. inverts M4. subst. split~. fmap_eq. }
Qed.

Lemma credits_substract : forall (n m : nat),
  (n >= m)%nat ->
  \$ n ==> \$ m \* \$ (n-m).
Proof using.
  introv M. rewrite <- credits_split_add.
  math_rewrite (m + (n-m) = n)%nat. auto.
Qed.

End Credits.


(* ---------------------------------------------------------------------- *)
(* ** Tactics for reductions *)

Ltac fmap_red_base tt ::=
  match goal with H: red _ _ ?t _ _ |- red _ _ ?t _ _ =>
    applys_eq H 2 4; try fmap_eq end.



(* ********************************************************************** *)
(* * Reasoning Rules *)

Implicit Types t : trm.
Implicit Types v w : val.
Implicit Types h : heap.


(* ---------------------------------------------------------------------- *)
(* ** Definition of triples *)

Definition triple t H Q :=
  forall H' h,
  (H \* H') h ->
  exists n h' v,
       red n (h^s) t (h'^s) v
    /\ (Q v \* \Top \* H') h'
    /\ (h^c = n + h'^c)%nat.


(* ---------------------------------------------------------------------- *)
(* ** Definitions of [pay] *)

Definition pay_one H H' :=
  H ==> (\$ 1%nat) \* H'.


(* ---------------------------------------------------------------------- *)
(* ** Structural rules *)

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using.
  introv M. intros HF h N. rewrite hstar_hexists in N.
  destruct N as (x&N). applys* M.
Qed.

Lemma triple_hprop : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. rewrite hpure_eq_hexists_empty. rewrite hstar_hexists.
  rew_heap. applys* triple_hexists.
Qed.

Lemma triple_conseq : forall t H' Q' H Q,
  H ==> H' ->
  triple t H' Q' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
  introv MH M MQ. intros HF h N.
  forwards (n&h'&v&R&K&C): (rm M) HF h. { hhsimpl~. }
  exists n h' v. splits~. { hhsimpl. hchanges~ (MQ v). }
Qed.

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using.
  introv M. intros HF h N. rewrite hstar_assoc in N.
  forwards (n&h'&v&R&K&C): (rm M) (H' \* HF) h. { hhsimpl~. }
  exists n h' v. splits~. { hhsimpl~. }
Qed.

Lemma triple_htop_post : forall t H Q,
  triple t H (Q \*+ \Top) ->
  triple t H Q.
Proof using.
  introv M. intros HF h N. forwards* (n&h'&v&R&K&C): (rm M) HF h.
  exists n h' v. splits~. { rewrite <- htop_hstar_htop. hhsimpl. }
Qed.

Lemma triple_htop_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \Top) Q.
Proof using.
  introv M. applys triple_htop_post. applys~ triple_frame.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Term rules *)

Lemma triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using.
  introv M. intros HF h N. exists 0%nat h v. splits~.
  { applys red_val. }
  { hhsimpl. hchanges M. }
Qed.

Lemma triple_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triple (trm_fix f x t1) H Q.
Proof using.
  introv M. intros HF h N. exists. splits.
  { applys red_fix. }
  { hhsimpl. hchanges M. }
  { math. }
Qed.

Definition is_val_bool (v:val) : Prop :=
  exists b, v = val_bool b.

Lemma triple_if : forall Q1 t0 t1 t2 H Q,
  triple t0 H Q1 ->
  (forall (b:bool), triple (if b then t1 else t2) (Q1 b) Q) ->
  (forall v, ~ is_val_bool v -> (Q1 v) ==> \[False]) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2 M3. intros HF h N.
  forwards* (n&h1'&v&R1&K1&C1): (rm M1) HF h.
  tests C: (is_val_bool v).
  { destruct C as (b&E). subst. forwards* (n'&h'&v'&R&K&C2): (rm M2) h1'.
    exists (n+n')%nat h' v'. splits~.
    { applys* red_if. }
    { rewrite <- htop_hstar_htop. rew_heap~. }
    { math. } }
  { specializes M3 C.
    asserts Z: ((\[False] \* \Top \* HF) h1').
    { applys himpl_trans K1. hchange M3. hsimpl. hsimpl. }
    repeat rewrite hfalse_hstar_any in Z.
    lets: hpure_inv Z. false*. } (* TODO: shorten this *)
Qed.

Lemma triple_if_bool : forall (b:bool) t1 t2 H Q,
  (b = true -> triple t1 H Q) ->
  (b = false -> triple t2 H Q) ->
  triple (trm_if b t1 t2) H Q.
Proof using.
  introv M1 M2. applys triple_if (fun r => \[r = val_bool b] \* H).
  { applys triple_val. hsimpl~. }
  { intros b'. applys~ triple_hprop. intros E. inverts E. case_if*. }
  { intros v' N. hpull. intros E. inverts~ E. false N. hnfs*. }
Qed.

Lemma triple_let : forall z t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall (X:val), triple (subst1 z X t2) (Q1 X) Q) ->
  triple (trm_let z t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF h N.
  lets~ (n1&h1'&v1&R1&K1&C1): (rm M1) HF h.
  forwards* (n2&h2'&v2&R2&K2&C2): (rm M2) (\Top \* HF) h1'.
  exists (n1+n2)%nat h2' v2. splits~.
  { applys~ red_let R2. }
  { rewrite <- htop_hstar_htop. hhsimpl. }
  { math. }
Qed.

Lemma triple_let_val : forall z v1 t2 H Q,
  (forall (X:val), X = v1 -> triple (subst1 z X t2) H Q) ->
  triple (trm_let z (trm_val v1) t2) H Q.
Proof using.
  introv M. forwards~ M': (rm M).
  applys_eq~ (>> triple_let H (fun x => \[x = v1] \* H)) 2.
  { applys triple_val. hsimpl~. }
  { intros X. applys triple_hprop. intro_subst. applys M'. }
Qed.

Lemma triple_app_fix : forall f x F V t1 H H' Q,
  F = (val_fix f x t1) ->
  pay_one H H' ->
  triple (subst2 f F x V t1) H' Q ->
  triple (trm_app F V) H Q.
Proof using.
  introv EF HP M. intros HF h N. unfolds pay_one.
  lets HP': himpl_frame_l HF (rm HP).
  lets N': (rm HP') (rm N). rew_heap in N'.
  destruct N' as (h1&h2&N1&N2&N3&N4).
  lets N1': hcredits_inv (rm N1). inverts N1'.
  lets (Na&Nb): heap_eq_forward (rm N4). simpls. subst.
  lets~ (n&h'&v&R&K&C): (rm M) HF h2.
  exists (n+1)%nat h' v. splits~.
  { applys* red_app_fix_val. fmap_red~. }
  { math. }
Qed.

Section RulesPrimitiveOps.
Transparent hstar hsingle.

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists l, \[r = val_loc l] \* l ~~~> v).
Proof using.
  intros. intros HF h N. rew_heap in N.
  forwards~ (l&Dl&Nl): (fmap_single_fresh null (h^s) v).
  sets m1': (fmap_single l v).
  exists 0%nat ((m1' \+ h^s),h^c) (val_loc l). splits~.
  { applys~ red_ref. }
  { exists (m1',0%nat) h. split.
    { exists l. applys~ himpl_hpure_r. unfold m1'. hnfs~. }
    { splits~. hhsimpl~. } }
Qed.

Lemma triple_get : forall v l,
  triple (val_get (val_loc l))
    (l ~~~> v)
    (fun x => \[x = v] \* (l ~~~> v)).
Proof using.
  intros. intros HF h N. lets N': N.
  destruct N as (h1&h2&(N1a&N1b)&N2&N3&N4).
  forwards (E1&E2): heap_eq_forward (rm N4). simpls.
  exists 0%nat h v. splits~.
  { applys red_get. rewrite E1. applys~ fmap_union_single_l_read. }
  { rew_heap. rewrite hstar_pure. split~. hhsimpl~. }
Qed.

Lemma triple_set : forall w l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => \[r = val_unit] \* l ~~~> w).
Proof using.
  intros. intros HF h N. destruct N as (h1&h2&(N1a&N1b&N1c)&N2&N3&N4).
  forwards (E1&E2): heap_eq_forward (rm N4). simpls.
  sets m1': (fmap_single l w).
  exists 0%nat ((m1' \+ h2^s), h2^c) val_unit. splits~.
  { applys red_set. rewrite E1. unfold m1'. rewrite N1a.
    applys~ fmap_union_single_to_update. }
  { rew_heap. rewrite hstar_pure. split~.
    { exists (m1',0%nat) h2. splits~.
      { hnfs~. }
      { hhsimpl~. }
      { unfold m1'. unfolds heap_disjoint. rewrite N1a in N3.
        applys~ fmap_disjoint_single_set v. } } }
   { simpls. rewrite N1b in E2. unfolds credits_zero. math. }
Qed.

End RulesPrimitiveOps.


(* ********************************************************************** *)
(* * Bonus *)


(* ---------------------------------------------------------------------- *)
(* ** Triples satisfy the [local] predicate *)

(* TODO update
Lemma is_local_triple : forall t,
  is_local (triple t).
Proof using.
  intros. applys pred_ext_2. intros H Q. iff M.
  { intros h Hh. forwards (h'&v&N1&N2): M \[] h.
    { hhsimpl. }
    exists H \[] Q. hhsimpl. split~. hsimpl. }
  { intros H' h Hh. lets (h1&h2&N1&N2&N3&N4): Hh. hnf in M.
    lets (H1&H2&Q1&R): M N1. rewrite <-hstar_assoc, hstar_comm, hstar_pure in R.
    lets ((R1&R2)&R3): R.
    forwards (n&h'&v&S1&S2&S3): R1 (H2\*H') h.
    { subst h. rewrite <- hstar_assoc. exists~ h1 h2. }
    exists n h' v. splits~. rewrite <- htop_hstar_htop.
    applys himpl_inv S2.
    hchange (R2 v). hsimpl. }
Qed.
*)


(* ---------------------------------------------------------------------- *)
(* ** Alternative, slightly lower-level definition of triples *)

Definition triple' (t:trm) (H:hprop) (Q:val->hprop) :=
  forall H' m c,
  (H \* H') (m, c) ->
  exists n m' c' v,
       red n m t m' v
    /\ (Q v \* \Top \* H') (m', c')
    /\ (c = n + c')%nat.

Lemma triple_eq_triple' : triple = triple'.
Proof using.
  applys pred_ext_3. intros t H Q.
  unfold triple, triple'. iff M.
  { introv P1. forwards~ (n&h'&v&R1&R2&R3): M H' (m,c).
    exists n (h'^s) (h'^c) v. splits~.
    applys_eq R2 1. applys~ heap_eq. }
  { introv P1. forwards (n&m'&c'&v&R1&R2&R3): M H' (h^s) (h^c).
    { applys_eq P1 1. applys~ heap_eq. }
    exists n (m',c') v. splits~. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Alternative, lower-level definition of triples *)

Definition triple'' t H Q :=
  forall m1 c1 m2,
  fmap_disjoint m1 m2 ->
  H (m1,c1) ->
  exists n m1' m3' c1' v,
       fmap_disjoint_3 m1' m3' m2
    /\ red n (m1 \+ m2) t (m1' \+ m3' \+ m2) v
    /\ (Q v) (m1',c1')
    /\ (c1 >= n + c1')%nat.

Lemma triple_eq_triple'' : triple = triple''.
Proof using.
  hint htop_intro.
  applys pred_ext_3. intros t H Q.
  rewrite triple_eq_triple'.
  unfold triple', triple''. iff M.
  { introv D P1.
    forwards~ (n&m'&c'&v&R1&R2&R4): M (=(m2,0%nat)) (m1 \+ m2) c1.
    { exists (m1,c1) (m2,0%nat). splits~. applys heap_eq. simple~. }
    rewrite <- hstar_assoc in R2.
    destruct R2 as ((m1''&c1'')&h2'&N0&N1&N2&N3). subst h2'.
    destruct N0 as ((m1'&c1')&(m3'&c3')&T0&T1&T2&T3).
    exists n m1' m3' c1' v.
    lets (?&?): heap_eq_forward (rm T3).
    lets (?&?): heap_eq_forward (rm N3). simpls.
    splits~.
    { subst. rew_disjoint; simpls; rew_disjoint. destruct N2.
     splits~. }
    { fmap_red. }
    { math. } }
  { introv (h1&h2&N1&N2&D&U).
    forwards~ (n&m1'&m3'&c1'&v&R1&R2&R3&R4): M (h1^s) (h1^c) (h2^s).
    { applys_eq N1 1. applys~ heap_eq. }
    lets (?&?): heap_eq_forward (rm U). simpls.
    exists n (m1' \+ m3' \+ h2^s) (c-n)%nat v. splits~.
    { fmap_red. }
    { exists (m1',c1') (m3' \+ h2^s, (h2^c + h1^c - n - c1')%nat). splits~.
      { exists (m3',(h1^c - n - c1')%nat) h2. splits~.
        { applys heap_eq. splits~. simpls. math. } }
      { subst. rew_disjoint; simpls; rew_disjoint. autos*. }
      { applys heap_eq. splits~. simpls. subst. math. } }
    { math. }  }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Derived rule for let-binding of a recursive function *)

(* TEMPORARY *)

Definition spec_fix (f:var) (x:var) (t1:trm) (F:val) :=
  forall X H H' Q,
    pay_one H H' ->
    triple (subst2 f F x X t1) H' Q ->
    triple (trm_app F X) H Q.

Lemma triple_let_fix : forall f x t1 t2 H Q,
  (forall (F:val), spec_fix f x t1 F -> triple (subst1 f F t2) H Q) ->
  triple (trm_let f (trm_fix f x t1) t2) H Q.
Proof using.
  introv M. applys triple_let (fun F => \[spec_fix f x t1 F] \* H).
  { applys triple_fix. hsimpl~.
    intros F H' H'' Q' M1 M2. applys* triple_app_fix. }
  { intros F. applys triple_hprop. applys M. }
Qed.
