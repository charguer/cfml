(**

This file formalizes standard Separation Logic. It contains:
- a definition of heaps as finite maps from location to values,
- an instantiation of the functor from the file [SepFunctor.v],
- a definition of triples,
- statement and proofs of structural rules,
- statement and proofs of rules for terms,
- statement and proofs of rules for primitive operations,
- bonuses: an alternative definition of triples, and derived rules.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Export LambdaSemantics SepFunctor.
Open Scope fmap_scope.

Ltac auto_star ::= jauto.

Implicit Types f : var.
Implicit Types v w : val.
Implicit Types t : trm.
Implicit Types n : int.
Implicit Types l : loc.
Implicit Types k : field.


(* ********************************************************************** *)
(* * Core of the logic *)

Module Export SepBasicCore <: SepCore.


(* ---------------------------------------------------------------------- *)
(** Heaps *)

(** A heap is a state (a finite map from location to values)
   as defined in [LambdaSemantics.v]. *)

Definition heap : Type := (state)%type.

(** For uniformity with other instantiations of the Separation Logic
  functor, we introduce local names for operations and lemmas on heaps. *)

Definition heap_empty : heap := fmap_empty.

Notation "h1 \u h2" := (fmap_union h1 h2)
  (at level 37, right associativity) : heap_scope.
  (* LATER: could try to introduce [heap_union := fmap_union] *)

Definition heap_union_empty_l := fmap_union_empty_l.

Definition heap_union_empty_r := fmap_union_empty_r.

Definition heap_union_comm := fmap_union_comm_of_disjoint.


(* ---------------------------------------------------------------------- *)
(** Hprop *)

(** A heap predicate, type [hprop] is a predicate over such heaps. *)

Definition hprop := heap -> Prop.

(** Empty heap predicate: [ \[] ] *)

Definition hempty : hprop :=
  fun h => h = heap_empty.

(** Separating conjunction: [H1 \* H2] *)

Definition hstar (H1 H2 : hprop) : hprop :=
  fun h => exists h1 h2, H1 h1
                      /\ H2 h2
                      /\ (\# h1 h2)
                      /\ h = h1 \+ h2.

(** Quantifiers *)

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
(* ** Types *)

Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ---------------------------------------------------------------------- *)
(* ** Tactic for automation *)

Hint Extern 1 (_ = _ :> heap) => fmap_eq.

Tactic Notation "fmap_disjoint_pre" :=
  subst; rew_disjoint; jauto_set.

Hint Extern 1 (\# _ _) => fmap_disjoint_pre.


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
  { exists heap_empty h. unfold heap_empty. auto. }
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
  intros H1 H2 H3. applys hprop_extens. intros h. split.
  { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U). subst h'.
    exists h1 (h2 \+ h3). splits~. { exists* h2 h3. } }
  { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U). subst h'.
    exists (h1 \+ h2) h3. splits~. { exists* h1 h2. } }
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

End SepBasicCore.


(* ********************************************************************** *)
(* * Derived properties of the logic *)

(** Here, we instantiate the functors to obtained derived definitions,
  lemmas, notation, and tactics. *)

Module Export SepBasicSetup := SepSetup SepBasicCore.
Export SepBasicCore.

Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ********************************************************************** *)
(* * Specific properties of the logic *)

(* ---------------------------------------------------------------------- *)
(* ** Auxiliary lemmas *)

Lemma hpure_inv' : forall P h,
  \[P] h ->
  P /\ h = heap_empty.
Proof using. introv M. lets (HP&HE): hpure_inv M. lets*: hempty_inv HE. Qed.

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  \# h1 h2 ->
  (H1 \* H2) (h1 \u h2).
Proof using. intros. exists~ h1 h2. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Singleton heap *)

(** Definition of the singleton heap predicate, written [r ~~~> v] *)

Definition hsingle (l:loc) (v:val) : hprop :=
  fun h => h = fmap_single l v /\ l <> null.

Notation "l '~~~>' v" := (hsingle l v)
  (at level 32, no associativity) : heap_scope.

Lemma hsingle_fmap_single : forall l v,
  l <> null ->
  (l ~~~> v) (fmap_single l v).
Proof using. intros. split~. Qed.

Lemma hstar_hsingle_same_loc_disjoint : forall l v1 v2,
  (l ~~~> v1) \* (l ~~~> v2) ==> \[False].
Proof using.
  intros. unfold hsingle. intros h (h1&h2&E1&E2&D&E). false.
  subst. applys* fmap_disjoint_single_single_same_inv.
Qed.

Lemma hsingle_not_null : forall l v,
  (l ~~~> v) ==> (l ~~~> v) \* \[l <> null].
Proof using.
  introv. intros h (Hh&Nl).
  exists h heap_empty. splits~.
  { unfold hsingle. splits~. }
  { applys~ hpure_intro. applys~ hempty_intro. }
  { unfold heap_empty. auto. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Singleton field heap *)

(** Definition of the heap predicate describing a single record field,
  written [l `.` f ~> v]. *)

Definition hfield (l:loc) (k:field) (v:val) : hprop :=
  (l+k)%nat ~~~> v \* \[ l <> null ].

Notation "l `.` k '~~~>' v" := (hfield l k v)
  (at level 32, k at level 0, no associativity,
   format "l `.` k  '~~~>'  v") : heap_scope.

Lemma hstar_hfield_same_loc_disjoint : forall l k v1 v2,
  (l`.`k ~~~> v1) \* (l`.`k ~~~> v2) ==> \[False].
Proof using.
  intros. unfold hfield. hpull ;=> N1 N2.
  applys hstar_hsingle_same_loc_disjoint.
Qed.

Lemma hfield_not_null : forall l k v,
  (l`.`k ~~~> v) ==> (l`.`k ~~~> v) \* \[l <> null].
Proof using.
  intros. subst. unfold hfield. hchanges~ hsingle_not_null.
Qed.

Arguments hfield_not_null : clear implicits.

Lemma hfield_eq_fun_hsingle :
  hfield = (fun l k v => ((l+k)%nat ~~~> v) \* \[l <> null]).
Proof using. intros. auto. Qed.

Lemma hfield_to_hsingle : forall l k v,
  (l`.`k ~~~> v) ==> ((l+k)%nat ~~~> v) \* \[l <> null].
Proof using. intros. auto. Qed.

Lemma hsingle_to_hfield : forall l k v,
  l <> null ->
  ((l+k)%nat ~~~> v) ==> l`.`k ~~~> v.
Proof using. intros. unfold hfield. hsimpl~. Qed.

Arguments hsingle_to_hfield : clear implicits.

Global Opaque hsingle hfield.


(* ---------------------------------------------------------------------- *)
(* ** Configuration of [hsimpl] *)

(* ** Configure [hsimpl] to make it aware of [hsingle] *)

Ltac hcancel_hook H ::=
  match H with
  | hsingle _ _ => hcancel_try_same tt
  | hfield _ _ _ => hcancel_try_same tt
  end.


(* ---------------------------------------------------------------------- *)
(* ** Auxiliary definitions for [rule_if] and [rule_seq] *)

Definition is_val_bool (v:val) : Prop :=
  exists b, v = val_bool b.


(* ---------------------------------------------------------------------- *)
(* ** Auxiliary definitions for [rule_alloc] *)

Fixpoint Alloc (k:nat) (l:loc) :=
  match k with
  | O => \[]
  | S k' => (\exists v, l ~~~> v) \* (Alloc k' (S l)%nat)
  end.

Lemma Alloc_zero_eq : forall l,
  Alloc O l = \[].
Proof using. auto. Qed.

Lemma Alloc_succ_eq : forall l k,
  Alloc (S k) l = (\exists v, l ~~~> v) \* Alloc k (S l)%nat.
Proof using. auto. Qed.

Global Opaque Alloc.

Hint Rewrite Alloc_zero_eq Alloc_succ_eq : rew_Alloc.

Tactic Notation "rew_Alloc" :=
  autorewrite with rew_Alloc.

Lemma Alloc_fmap_conseq : forall l k v,
  l <> null ->
  (Alloc k l) (fmap_conseq l k v).
Proof using.
  Transparent loc null.
  introv N. gen l. induction k; intros; rew_Alloc.
  { rewrite fmap_conseq_zero. applys~ hempty_intro. }
  { rewrite fmap_conseq_succ. applys hstar_intro.
    { applys hexists_intro. split~. }
    { applys IHk. unfolds loc, null. math. }
    { applys~ fmap_disjoint_single_conseq. } }
Qed.

Lemma Alloc_split_eq : forall k1 (k:nat) p,
  (k1 <= k)%nat ->
  Alloc k p = Alloc k1 p \* Alloc (k-k1)%nat (p + k1)%nat.
Proof using.
  Transparent loc field. unfold field.
  intros k1 k. gen k1. induction k; introv N.
  {math_rewrite (k1 = 0%nat). rew_Alloc. rew_heap~. }
  { destruct k1 as [|k1']; rew_nat.
    { rew_Alloc. rew_heap~. }
    { rew_Alloc. rewrite (IHk k1'); [|math]. rew_heap~. } }
Qed.

Arguments Alloc_split_eq : clear implicits.

Lemma Alloc_split_inv : forall k1 k2 p,
  Alloc k1 p \* Alloc k2 (p + k1)%nat ==> Alloc (k1+k2)%nat p.
Proof using.
  intros. rewrites (Alloc_split_eq k1 (k1+k2)%nat p); [|math]. rew_nat~.
Qed.

(** Tactic for helping reasoning about concrete calls to [alloc] *)

Ltac simpl_abs := (* LATER: will be removed once [abs] computes *)
  match goal with
  | |- context [ abs 0 ] => change (abs 0) with 0%nat
  | |- context [ abs 1 ] => change (abs 1) with 1%nat
  | |- context [ abs 2 ] => change (abs 2) with 2%nat
  | |- context [ abs 3 ] => change (abs 3) with 3%nat
  end.



(* ********************************************************************** *)
(* * Hoare reasoning rules *)

(* ---------------------------------------------------------------------- *)
(* ** Definition of Hoare triples *)

Definition hoare (t:trm) (H:hprop) (Q:val->hprop) :=
  forall h, H h -> exists h' v, red h t h' v /\ Q v h'.


(* ---------------------------------------------------------------------- *)
(* ** Hoare structural rules *)

Lemma hoare_conseq : forall t H' Q' H Q,
  hoare t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoare t H Q.
Proof using.
  introv M MH MQ HF. forwards (h'&v&R&K): M h.
  { hhsimpl~. }
  exists h' v. splits~. { hhsimpl. auto. }
Qed.

Lemma hoare_extract_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, hoare t (J x) Q) ->
  hoare t (hexists J) Q.
Proof using. introv M (x&Hh). applys* M. Qed.

Lemma hoare_extract_hforall : forall t (A:Type) (J:A->hprop) Q,
  (exists x, hoare t (J x) Q) ->
  hoare t (hforall J) Q.
Proof using. introv (x&M) Hh. applys* M. Qed.

Lemma hoare_extract_hprop : forall t (P:Prop) H Q,
  (P -> hoare t H Q) ->
  hoare t (\[P] \* H) Q.
Proof using.
  introv M. applys~ rule_extract_hprop_from_extract_hexists.
  { applys* hoare_extract_hexists. }
Qed.
(* Details:
  introv M (h1&h2&N1&N2&N3&N4).
  destruct (hpure_inv' N1). subst.  
  rewrite heap_union_empty_l. 
  applys* M.
*)

Lemma hoare_extract_hwand_hpure_l : forall t (P:Prop) H Q,
  P ->
  hoare t H Q ->
  hoare t (\[P] \-* H) Q.
Proof using.
  introv HP M. applys~ rule_extract_hwand_hpure_l_from_extract_hexists_and_consequence.
  { applys* hoare_extract_hexists. }
  { introv N W. applys* hoare_conseq. }
Qed.
(* Details:
  introv HP M. intros h (H1&(h1&h2&N1&N2&N3&N4)).
  lets (N2'&E): (hpure_inv' (rm N2)). subst.
  rewrite heap_union_empty_r.
  applys* M. applys N2'. hhsimpl~.
*)

Lemma hoare_named_heap : forall t H Q,
  (forall h, H h -> hoare t (= h) Q) ->
  hoare t H Q.
Proof using. introv M. intros h Hh. applys* M. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Hoare rules for term constructs *)

Lemma hoare_val : forall v H Q,
  H ==> Q v ->
  hoare (trm_val v) H Q.
Proof using.
  introv M. intros h Hh. exists h v. splits.
  { applys red_val. }
  { hhsimpl~. }
Qed.

Lemma hoare_fix : forall (f z:bind) t1 H Q,
  H ==> Q (val_fix f z t1) ->
  hoare (trm_fix f z t1) H Q.
Proof using.
  introv M. intros h Hh. exists___. splits.
  { applys~ red_fix. }
  { hhsimpl~. }
Qed.

Lemma hoare_let : forall z t1 t2 H Q Q1,
  hoare t1 H Q1 ->
  (forall (X:val), hoare (subst1 z X t2) (Q1 X) Q) ->
  hoare (trm_let z t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ red_let R2. }
Qed.

Lemma hoare_if : forall Q1 t0 t1 t2 H Q,
  hoare t0 H Q1 ->
  (forall (b:bool), hoare (if b then t1 else t2) (Q1 b) Q) ->
  (forall v, ~ is_val_bool v -> (Q1 v) ==> \[False]) ->
  hoare (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2 M3. intros h Hh.
  forwards* (h1'&v&R1&K1): (rm M1).
  tests C: (is_val_bool v).
  { destruct C as (b&E). subst. forwards* (h'&v'&R&K): (rm M2).
    exists h' v'. splits~. { applys* red_if. } }
  { false* M3. }
Qed.

Lemma hoare_apps_funs : forall xs F (Vs:vals) t1 H Q,
  F = (val_funs xs t1) ->
  var_funs (length Vs) xs ->
  hoare (substn xs Vs t1) H Q ->
  hoare (trm_apps F Vs) H Q.
Proof using.
  introv E N M. intros h Hh. forwards* (h'&v&R&K): (rm M).
  exists h' v. splits~. { subst. applys* red_app_funs_val. }
Qed.

Lemma hoare_apps_fixs : forall xs f F (Vs:vals) t1 H Q,
  F = (val_fixs f xs t1) ->
  var_fixs f (length Vs) xs ->
  hoare (substn (f::xs) (F::Vs) t1) H Q ->
  hoare (trm_apps F Vs) H Q.
Proof using.
  introv E N M. intros h Hh. forwards* (h'&v&R&K): (rm M).
  exists h' v. splits~. { subst. applys* red_app_fixs_val. }
Qed.

Lemma hoare_while_raw : forall t1 t2 H Q,
  hoare (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) H Q ->
  hoare (trm_while t1 t2) H Q.
Proof using.
  introv M Hh. forwards* (h1'&v1&R1&K1): (rm M).
  exists h1' v1. splits~. { applys* red_while. }
Qed.

Lemma hoare_for_raw : forall (x:var) (n1 n2:int) t3 H (Q:val->hprop),
  hoare (
    If (n1 <= n2)
      then (trm_seq (subst1 x n1 t3) (trm_for x (n1+1) n2 t3))
      else val_unit) H Q ->
  hoare (trm_for x n1 n2 t3) H Q.
Proof using.
  introv M Hh. forwards* (h1'&v1&R1&K1): (rm M).
  exists h1' v1. splits~. { applys* red_for. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Hoare rules for primitives *)

Section HoarePrimitives.
Transparent hstar hsingle hfield hexists loc null.
Hint Unfold hsingle.

Lemma hoare_ref : forall H v,
  hoare (val_ref v)
    H
    (fun r => (\exists l, \[r = val_loc l] \* l ~~~> v) \* H).
Proof using.
  intros. intros h Hh.
  forwards~ (l&Dl&Nl): (fmap_single_fresh null h v).
  forwards~ Hh1': hsingle_fmap_single l v.
  sets h1': (fmap_single l v).
  exists (h1' \u h) (val_loc l). splits~.
  { applys~ red_ref. }
  { apply~ hstar_intro. { exists l. hhsimpl~. } }
Qed.

Lemma hoare_get : forall H v l,
  hoare (val_get (val_loc l))
    ((l ~~~> v) \* H)
    (fun x => \[x = v] \* (l ~~~> v) \* H).
Proof using.
  intros. intros h Hh. exists h v. splits~.
  { applys red_get. destruct Hh as (h1&h2&(N1a&N1b)&N2&N3&N4).
    subst h. applys~ fmap_union_single_l_read. }
  { hhsimpl~. }
Qed.

Lemma hoare_set : forall H w l v,
  hoare (val_set (val_loc l) w)
    ((l ~~~> v) \* H)
    (fun r => \[r = val_unit] \* (l ~~~> w) \* H).
Proof using.
  intros. intros h Hh. destruct Hh as (h1&h2&(N1a&N1b)&N2&N3&N4).
  forwards~ Hh1': hsingle_fmap_single l w.
  sets h1': (fmap_single l w).
  exists (h1' \u h2) val_unit. splits~.
  { applys red_set. subst h h1. applys~ fmap_union_single_to_update. }
  { rewrite hstar_pure. split~. apply~ hstar_intro.
    { applys~ fmap_disjoint_single_set v. } }
Qed.

Lemma hoare_alloc : forall H n,
  n >= 0 ->
  hoare (val_alloc n)
    H
    (fun r => (\exists l, \[r = val_loc l /\ l <> null] \* Alloc (abs n) l) \* H).
Proof using. (* Note: [abs n] currently does not compute in Coq. *)
  introv N. intros h Hh.
  forwards~ (l&Dl&Nl): (fmap_conseq_fresh null h (abs n) val_unit).
  sets h1': (fmap_conseq l (abs n) val_unit).
  exists (h1' \u h) (val_loc l). splits~.
  { applys~ (red_alloc (abs n)). rewrite~ abs_nonneg. }
  { apply~ hstar_intro.
    { exists l. applys~ himpl_hpure_r. applys~ Alloc_fmap_conseq. } }
Qed.

Lemma hoare_redbinop : forall H op v1 v2 v,
  redbinop op v1 v2 v ->
  hoare (op v1 v2)
    H
    (fun r => \[r = v] \* H).
Proof using.
  introv R. intros h Hh. exists h v. splits.
  { applys* red_binop. }
  { hhsimpl~. }
Qed.

End HoarePrimitives.


(* ********************************************************************** *)
(* * SL Reasoning Rules *)

(* ---------------------------------------------------------------------- *)
(* ** Definition of SL triples *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) :=
  forall H', hoare t (H \* H') (Q \*+ H' \*+ \Top).

(** SL triples are "local", in the sense of SepFunctor *)

Lemma is_local_triple : forall t,
  is_local (triple t).
Proof using.
  intros. applys pred_ext_2. intros H Q. iff M.
  { intros h Hh. hhsimpl. split*. hsimpl. }
  { intros H'. applys hoare_named_heap. 
    intros h (h1&h2&N1&N2&N3&N4).
    lets (H1&H2&Q1&M0): (rm M) (rm N1).
    rewrite <-hstar_assoc, hstar_comm, hstar_pure in M0.
    destruct M0 as ((M1&M2)&M3).
    applys hoare_conseq (M1 (H2 \* H')).
    { subst. rewrite <- hstar_assoc. intros h ->. apply~ hstar_intro. }
    { intros x. hchanges (M2 x). } }
Qed.

(** Make tactic [xlocal] aware that triples are local *)

Ltac xlocal_base tt ::=
  try first [ applys is_local_local
            | applys is_local_triple ].


(* ---------------------------------------------------------------------- *)
(* ** SL rules structural *)

Lemma rule_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
  introv M MH MQ. intros HF. applys hoare_conseq M.
  { hchanges MH. }
  { intros x. hchanges (MQ x). }
Qed.

Lemma rule_extract_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using.
  introv M. intros HF. rewrite hstar_hexists.
  applys hoare_extract_hexists. intros. applys* M.
Qed.

Lemma rule_extract_hforall : forall t A (J:A->hprop) Q,
  (exists x, triple t (J x) Q) ->
  triple t (hforall J) Q.
Proof using.
  introv (x&M). intros HF.
  forwards* N: hoare_extract_hforall (fun x => J x \* HF).
  applys* hoare_conseq. applys hstar_hforall.
Qed.

Lemma rule_extract_hprop : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. intros HF. rewrite hstar_assoc.
  applys hoare_extract_hprop. intros. applys* M.
Qed.

Lemma rule_extract_hwand_hpure_l : forall t (P:Prop) H Q,
  P ->
  triple t H Q ->
  triple t (\[P] \-* H) Q.
Proof using.
  introv HP M. intros HF.
  forwards* N: hoare_extract_hwand_hpure_l P.
  applys* hoare_conseq. applys hstar_hwand.
Qed.

Lemma rule_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using.
  introv M. intros HF.
  applys hoare_conseq (M (HF \* H')); hsimpl.
Qed.

Lemma rule_htop_post : forall t H Q,
  triple t H (Q \*+ \Top) ->
  triple t H Q.
Proof using.
  introv M. unfolds triple. intros HF.
  applys hoare_conseq (M HF); hsimpl.
Qed.

Lemma rule_htop_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \Top) Q.
Proof using.
  introv M. applys rule_htop_post. applys~ rule_frame.
Qed.

Lemma rule_combined : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \Top ->
  triple t H Q.
Proof using.
  introv M WH WQ. applys rule_htop_post. applys rule_conseq.
  { applys* rule_frame. } { eauto. } { eauto. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** SL rules for terms *)

Lemma rule_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using.
  introv M. intros HF. applys hoare_val. { hchanges M. }
Qed.

Lemma rule_fix : forall f z t1 H Q,
  H ==> Q (val_fix f z t1) ->
  triple (trm_fix f z t1) H Q.
Proof using.
  introv M. intros HF. applys hoare_fix. { hchanges M. }
Qed.

Lemma rule_let : forall z t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall (X:val), triple (subst1 z X t2) (Q1 X) Q) ->
  triple (trm_let z t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF. applys hoare_let.
  { applys M1. }
  { intros X. simpl. applys hoare_conseq.
    { applys M2. }
    { hsimpl. }
    { intros v. hsimpl. } }
Qed.

Lemma rule_seq : forall t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall (X:val), triple t2 (Q1 X) Q) ->
  triple (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2. applys* rule_let. intros. rewrite* subst1_anon.
Qed.

Lemma rule_if : forall Q1 t0 t1 t2 H Q,
  triple t0 H Q1 ->
  (forall (b:bool), triple (if b then t1 else t2) (Q1 b) Q) ->
  (forall v, ~ is_val_bool v -> (Q1 v) ==> \[False]) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2 M3. intros HF.
  applys hoare_if. 
  { applys* M1. }
  { intros b. applys hoare_conseq. applys* M2. hsimpl. hsimpl. }
  { intros v Hv. hchanges~ M3. hsimpl. }
Qed.

Lemma rule_if_bool : forall (b:bool) t1 t2 H Q,
  (b = true -> triple t1 H Q) ->
  (b = false -> triple t2 H Q) ->
  triple (trm_if b t1 t2) H Q.
Proof using.
  introv M1 M2. applys rule_if (fun r => \[r = val_bool b] \* H).
  { applys rule_val. hsimpl~. }
  { intros b'. applys~ rule_extract_hprop. intros E. inverts E. case_if*. }
  { intros v' N. hpull. intros E. inverts~ E. false N. hnfs*. }
Qed.

Lemma rule_apps_funs : forall xs F (Vs:vals) t1 H Q,
  F = (val_funs xs t1) ->
  var_funs (length Vs) xs ->
  triple (substn xs Vs t1) H Q ->
  triple (trm_apps F Vs) H Q.
Proof using.
  introv E N M. intros H' h Hf. forwards (h'&v&R&K): (rm M) Hf.
  exists h' v. splits~. { subst. applys* red_app_funs_val. }
Qed.

Lemma rule_apps_fixs : forall xs f F (Vs:vals) t1 H Q,
  F = (val_fixs f xs t1) ->
  var_fixs f (length Vs) xs ->
  triple (substn (f::xs) (F::Vs) t1) H Q ->
  triple (trm_apps F Vs) H Q.
Proof using.
  introv E N M. intros H' h Hf. forwards (h'&v&R&K): (rm M) Hf.
  exists h' v. splits~. { subst. applys* red_app_fixs_val. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** SL Rules for loops *)

(** Rule for unfolding the body of a while loop once *)

Lemma rule_while_raw : forall t1 t2 H Q,
  triple (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) H Q ->
  triple (trm_while t1 t2) H Q.
Proof using.
  introv M. intros h Hf. apply hoare_while_raw. applys* M.
Qed.

(** Derived rule helping the set up of proof by inductions,
    by abstracting [trm_while t1 t2] as a fresh variable [t]. *)

Lemma rule_while : forall t1 t2 H Q,
  (forall t,
     (forall H' Q', triple (trm_if t1 (trm_seq t2 t) val_unit) H' Q' ->
                    triple t H' Q') ->
    triple t H Q) ->
  triple (trm_while t1 t2) H Q.
Proof using.
  introv M. applys M. introv K. applys rule_while_raw. applys K.
Qed.

(** Derived rule for reasoning about a while loop using a loop invariant *)

Lemma rule_while_inv : forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) H' t1 t2 H Q,
  let Q' := (fun r => \exists Y, I false Y) in
  wf R ->
  (H ==> (\exists b X, I b X) \* H') ->
  (forall t b X,
      (forall b' X', R X' X -> triple t (I b' X') Q') ->
      triple (trm_if t1 (trm_seq t2 t) val_unit) (I b X) Q') ->
  Q' \*+ H' ===> Q \*+ \Top ->
  triple (trm_while t1 t2) H Q.
Proof using.
  introv WR WH HX WQ. applys rule_combined WH WQ. xpull ;=> b0 X0.
  gen b0. induction_wf IH: WR X0. intros. applys rule_while_raw.
  applys HX. intros b' X' HR'. applys~ IH.
Qed.

(** Rule for unfolding the body of a for-loop once *)

Lemma rule_for_raw : forall (x:var) (n1 n2:int) t3 H (Q:val->hprop),
  triple (
    If (n1 <= n2)
      then (trm_seq (subst1 x n1 t3) (trm_for x (n1+1) n2 t3))
      else val_unit) H Q ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using.
  introv M. intros h Hf. apply hoare_for_raw. applys* M.
Qed.

(** Derived rule for the case of a loop that performs no iteratation *)

Lemma rule_for_gt : forall x n1 n2 t3 H Q,
  n1 > n2 ->
  H ==> Q val_unit \* \Top ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using.
  introv N M. applys rule_for_raw. case_if; [math|].
  applys rule_htop_post. applys* rule_val.
Qed.

(** Derived rule for the case of a loop that performs some iteratations *)

Lemma rule_for_le : forall Q1 (x:var) n1 n2 t3 H Q,
  n1 <= n2 ->
  triple (subst1 x n1 t3) H Q1 ->
  (forall v, triple (trm_for x (n1+1) n2 t3) (Q1 v) Q) ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using.
  introv N M1 M2. applys rule_for_raw. case_if; [|math].
  applys* rule_seq.
Qed.

(** Derived rule using an invariant for reasoning about a for-loop *)

Section RuleForInv.

Ltac auto_star ::= auto with maths.

Lemma rule_for_inv : forall (I:int->hprop) H' (x:var) n1 n2 t3 H Q,
  (n1 <= n2+1) ->
  (H ==> I n1 \* H') ->
  (forall i, n1 <= i <= n2 ->
     triple (subst1 x i t3) (I i) (fun r => I (i+1))) ->
  (I (n2+1) \* H' ==> Q val_unit \* \Top) ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using.
  introv N M1 M2 M3. xchange (rm M1). gen N M2.
  induction_wf IH: (wf_upto (n2+1)) n1; intros.
  tests C: (n1 = n2+1).
  { xapply* rule_for_gt. hchanges M3. }
  { applys* rule_for_le.
    { xapplys* M2. }
    { xpull ;=> _. tests C': (n1 = n2).
      { xapply* rule_for_gt. hchanges M3. }
      { xapplys* IH. } } }
Qed.

End RuleForInv.


(* ---------------------------------------------------------------------- *)
(* ** SL rules for primitive functions over the state *)

Lemma rule_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists l, \[r = val_loc l] \* l ~~~> v).
Proof using.
  intros. intros HF h N.
  forwards~ (l&Dl&Nl): (fmap_single_fresh null h v).
  sets h1': (fmap_single l v).
  exists (h1' \u h) (val_loc l). splits~.
  { applys~ red_ref. }
  { exists h1' h. split.
    { exists l. applys~ himpl_hpure_r. unfold h1'. hnfs~. }
    { splits~. hhsimpl~. } }
Qed.

Lemma rule_get : forall v l,
  triple (val_get (val_loc l))
    (l ~~~> v)
    (fun x => \[x = v] \* (l ~~~> v)).
Proof using.
  intros. intros HF h N. exists h v. splits~.
  { applys red_get. destruct N as (?&?&(?&?)&?&?&?).
    subst h. applys~ fmap_union_single_l_read. }
  { rew_heap. rewrite hstar_pure. split~. hhsimpl~. }
Qed.

Lemma rule_set : forall w l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => \[r = val_unit] \* l ~~~> w).
Proof using.
  intros. intros HF h N. destruct N as (h1&h2&(N0&N1)&N2&N3&N4).
  hnf in N1. sets h1': (fmap_single l w).
  exists (h1' \u h2) val_unit. splits~.
  { applys red_set. subst h h1. applys~ fmap_union_single_to_update. }
  { rew_heap. rewrite hstar_pure. split~. exists h1' h2. splits~.
    { hnfs~. }
    { hhsimpl~. }
    { subst h1. applys~ fmap_disjoint_single_set v. } }
Qed.

Lemma rule_set' : forall w l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => l ~~~> w).
Proof using. intros. xapplys* rule_set. Qed.

Lemma rule_alloc : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (fun r => \exists l, \[r = val_loc l /\ l <> null] \* Alloc (abs n) l).
Proof using. (* Note: [abs n] currently does not compute in Coq. *)
  introv N Hh.
  forwards~ (l&Dl&Nl): (fmap_conseq_fresh null h (abs n) val_unit).
  sets h1': (fmap_conseq l (abs n) val_unit).
  exists (h1' \u h) (val_loc l). splits~.
  { applys (red_alloc (abs n)); eauto.
    rewrite~ abs_nonneg. }
  { exists h1' h. split.
    { exists l. applys~ himpl_hpure_r. applys~ Alloc_fmap_conseq. }
    { splits~. hhsimpl~. } }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** SL rules for other primitive functions *)

Lemma rule_eq : forall v1 v2,
  triple (val_eq v1 v2)
    \[]
    (fun r => \[r = isTrue (v1 = v2)]).
Proof using.
  introv Hh. exists___. splits.
  { applys* red_eq. }
  { hhsimpl~. }
Qed.

Lemma rule_add : forall n1 n2,
  triple (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).
Proof using.
  introv Hh. exists___. splits.
  { applys* red_add. }
  { hhsimpl*. }
Qed.

Lemma rule_sub : forall n1 n2,
  triple (val_sub n1 n2)
    \[]
    (fun r => \[r = val_int (n1 - n2)]).
Proof using.
  introv Hh. exists___. splits.
  { applys* red_sub. }
  { hhsimpl*. }
Qed.

Lemma rule_ptr_add : forall l n,
  l + n >= 0 ->
  triple (val_ptr_add l n)
    \[]
    (fun r => \[r = val_loc (abs (l + n))]).
Proof using.
  introv N Hh. exists___. splits.
  { applys* red_ptr_add (abs (l + n)). rewrite~ abs_nonneg. }
  { hhsimpl*. }
Qed.

Lemma rule_ptr_add_nat : forall l (f:nat),
  triple (val_ptr_add l f)
    \[]
    (fun r => \[r = val_loc (l+f)%nat]).
Proof using.
  intros. xapplys~ rule_ptr_add. { math. }
  { intros. subst. fequals.
    applys eq_nat_of_eq_int. rewrite abs_nonneg; math. }
Qed.

(** Alternative direct proof for [rule_ptr_add_nat] *)

Lemma rule_ptr_add_nat' : forall l (f:nat),
  triple (val_ptr_add l f)
    \[]
    (fun r => \[r = val_loc (l+f)%nat]).
Proof using.
  introv Hh. exists___. splits.
  { applys* red_ptr_add_nat. }
  { hhsimpl*. }
Qed.



(* ********************************************************************** *)
(* * Bonus *)

(* ---------------------------------------------------------------------- *)
(* ** Alternative, low-level definition of triples *)

Section TripleAlternative.

Hint Extern 1 (\# _ _ _) => fmap_disjoint_pre.

Definition triple' t H Q :=
  forall h1 h2,
  \# h1 h2 ->
  H h1 ->
  exists h1' h3' v,
       \# h1' h2 h3'
    /\ red (h1 \u h2) t (h1' \u h3' \u h2) v
    /\ (Q v) h1'.

Lemma triple_eq_triple' : triple = triple'.
Proof using.
  hint htop_intro.
  applys pred_ext_3. intros t H Q.
  unfold triple, triple'. iff M.
  { introv D P1.
    forwards~ (h'&v&R1&R2): M (=h2) (h1 \u h2).
    { exists~ h1 h2. }
    rewrite <- hstar_assoc in R2.
    destruct R2 as (h1''&h2'&N0&N1&N2&N3). subst h2'.
    destruct N0 as (h1'&h3'&T0&T1&T2&T3).
    exists h1' h3' v. splits~. { fmap_red. } }
  { introv (h1&h2&N1&N2&D&U).
    forwards~ (h1'&h3'&v&R1&R2&R3): M h1 h2.
    exists (h1' \u h3' \u h2) v. splits~.
    { fmap_red. }
    { exists~ h1' (h3' \u h2). splits~.
      exists h3' h2. splits~. } }
Qed.

End TripleAlternative.




