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
From Sep Require Export Semantics SepFunctor.
Open Scope fmap_scope.

Ltac auto_star ::= jauto.

Implicit Types f : bind.
Implicit Types v w : val.
Implicit Types t : trm.
Implicit Types vs : vals.
Implicit Types n : int.
Implicit Types l : loc.
Implicit Types k : field.


(* ********************************************************************** *)
(* * Core of the logic *)

Module Export SepBasicCore <: SepCore.


(* ---------------------------------------------------------------------- *)
(** Heaps *)

(** A heap is a state (a finite map from location to values)
   as defined in [Semantics.v]. *)

Definition heap : Type := (state)%type.

(** Affinity is trivial *)

Definition heap_affine (h:heap) := True.

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

(** Affinity is defined in the standard way *)

Definition haffine (H : hprop) : Prop :=
  forall h, H h -> heap_affine h.

Lemma haffine_any : forall H,
  haffine H.
Proof using. introv M. hnfs*. Qed.

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

Lemma haffine_hempty :
  haffine \[].
Proof using. applys haffine_any. Qed.

Lemma haffine_hstar : forall H1 H2,
  haffine H1 ->
  haffine H2 ->
  haffine (H1 \* H2).
Proof using. intros. applys haffine_any. Qed.

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

Section Aux.

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

Lemma hgc_intro : forall h,
  \GC h.
Proof using. intros. applys hgc_of_heap_affine. hnfs*. Qed.

End Aux.

Global Opaque heap_affine.


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
(* ** Configuration of tactics *)

(* ** Configure [hsimpl] to make it aware of [hsingle] *)

Ltac hsimpl_hook H ::=
  match H with
  | hsingle _ _ => hsimpl_cancel_same H
  | hfield _ _ _ => hsimpl_cancel_same H
  end.

(* ** Configure [haffine] to make it aware of [haffine_any] *)

Ltac haffine_custom tt ::=
  apply haffine_any.


(* ---------------------------------------------------------------------- *)
(* ** Auxiliary definitions for [triple_if] and [triple_seq] *)

Definition is_val_bool (v:val) : Prop :=
  exists b, v = val_bool b.


(* ---------------------------------------------------------------------- *)
(* ** Auxiliary definitions for [triple_alloc] *)

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

Lemma hoare_named_heap : forall t H Q,
  (forall h, H h -> hoare t (= h) Q) ->
  hoare t H Q.
Proof using. introv M. intros h Hh. applys* M. Qed.


(* ---------------------------------------------------------------------- *)
(* ** Hoare rules for term constructs *)

Lemma hoare_evalctx : forall C t1 H Q Q1,
  evalctx C ->
  hoare t1 H Q1 ->
  (forall v, hoare (C v) (Q1 v) Q) ->
  hoare (C t1) H Q.
Proof using.
  introv HC M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ red_evalctx R2. }
Qed.

Lemma hoare_val : forall v H Q,
  H ==> Q v ->
  hoare (trm_val v) H Q.
Proof using.
  introv M. intros h Hh. exists h v. splits.
  { applys red_val. }
  { hhsimpl~. }
Qed.

Lemma hoare_fixs : forall (f:bind) xs t1 H Q,
  xs <> nil ->
  H ==> Q (val_fixs f xs t1) ->
  hoare (trm_fixs f xs t1) H Q.
Proof using.
  introv N M. intros h Hh. exists___. splits.
  { applys~ red_fixs. }
  { hhsimpl~. }
Qed.

Lemma hoare_constr : forall id vs H Q,
  H ==> Q (val_constr id vs) ->
  hoare (trm_constr id (trms_vals vs)) H Q.
Proof using.
  introv M. intros h Hh. exists h (val_constr id vs). splits.
  { applys red_constr. }
  { hhsimpl~. }
Qed.

Lemma hoare_constr_trm : forall id ts t1 vs H Q Q1,
  hoare t1 H Q1 -> 
  (forall v, hoare (trm_constr id ((trms_vals vs)++(trm_val v)::ts)) (Q1 v) Q) ->
  hoare (trm_constr id ((trms_vals vs)++t1::ts)) H Q.
Proof using.
  introv M1 M2. intros h Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ red_constr_trm R2. }
Qed.

Lemma hoare_let : forall z t1 t2 H Q Q1,
  hoare t1 H Q1 ->
  (forall v, hoare (subst1 z v t2) (Q1 v) Q) ->
  hoare (trm_let z t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ red_let_trm R2. }
Qed.

Lemma hoare_if_bool : forall (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros h Hh. forwards* (h1'&v1&R1&K1): (rm M1).
  exists h1' v1. splits~. { applys* red_if. }
Qed.

Lemma hoare_if_trm : forall Q1 t0 t1 t2 H Q, (* TODO needed? *)
  hoare t0 H Q1 ->
  (forall v, hoare (trm_if v t1 t2) (Q1 v) Q) ->
  hoare (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. applys* hoare_evalctx (fun t0 => trm_if t0 t1 t2).
  { constructor. }
Qed.

Lemma hoare_apps_funs : forall xs F (Vs:vals) t1 H Q,
  F = (val_funs xs t1) ->
  var_funs (length Vs) xs ->
  hoare (substn xs Vs t1) H Q ->
  hoare (trm_apps F Vs) H Q.
Proof using.
  introv E N M. intros h Hh. forwards* (h'&v&R&K): (rm M).
  exists h' v. splits~. { subst. applys* red_apps_funs. }
Qed.

Lemma hoare_apps_fixs : forall xs (f:var) F (Vs:vals) t1 H Q,
  F = (val_fixs f xs t1) ->
  var_fixs f (length Vs) xs ->
  hoare (substn (f::xs) (F::Vs) t1) H Q ->
  hoare (trm_apps F Vs) H Q.
Proof using.
  introv E N M. intros h Hh. forwards* (h'&v&R&K): (rm M).
  exists h' v. splits~. { subst. applys* red_apps_fixs. }
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

Lemma hoare_match : forall v p t1 pts H Q,
  (forall (G:ctx), Ctx.dom G = patvars p -> v = patsubst G p -> hoare (isubst G t1) H Q) ->
  ((forall (G:ctx), Ctx.dom G = patvars p -> v <> patsubst G p) -> hoare (trm_match v pts) H Q) ->
  hoare (trm_match v ((p,t1)::pts)) H Q.
Proof using.
  introv M1 M2 Hh. tests C: (exists (G:ctx), Ctx.dom G = patvars p /\ v = patsubst G p).
  { destruct C as (G&DG&Ev). forwards* (h1'&v1&R1&K1): (rm M1).
    exists h1' v1. splits~. { applys~ red_match_yes R1. } }
  { forwards* (h1'&v1&R1&K1): (rm M2).
    exists h1' v1. splits~. { applys~ red_match_no R1.
      intros G HG. specializes C G. rew_logic in C. destruct* C. } }
Qed.

Lemma hoare_case_trm : forall t1 pts H Q Q1,
  hoare t1 H Q1 -> 
  (forall v, hoare (trm_match v pts) (Q1 v) Q) ->
  hoare (trm_match t1 pts) H Q.
Proof using.
  introv M1 M2. intros h Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ red_match_trm R2. }
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
  { rewrite hstar_hpure. split~. apply~ hstar_intro.
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
    { exists l. applys~ himpl_hstar_hpure_r. applys~ Alloc_fmap_conseq. } }
Qed.

Lemma hoare_unop : forall v H op v1,
  redunop op v1 v ->
  hoare (op v1)
    H
    (fun r => \[r = v] \* H).
Proof using.
  introv R. intros h Hh. exists h v. splits.
  { applys* red_unop. }
  { hhsimpl~. }
Qed.

Lemma hoare_binop : forall v H op v1 v2,
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
  forall H', hoare t (H \* H') (Q \*+ H' \*+ \GC).

(** SL triples satisfy [is_local], in the sense of SepFunctor *)

Lemma is_local_triple : forall t,
  is_local (triple t).
Proof using.
  intros. applys is_local_intro. intros H Q M H'. 
  applys hoare_named_heap. intros h (h1&h2&N1&N2&N3&N4).
  lets (H1&H2&Q1&M0): (rm M) (rm N1).
  rewrite <- hstar_assoc, hstar_comm, hstar_hpure in M0.
  destruct M0 as ((M1&M2)&M3).
  applys hoare_conseq (M1 (H2 \* H')).
  { subst. rewrite <- hstar_assoc. intros h ->. apply~ hstar_intro. }
  { intros x. hchanges (M2 x). }
Qed.

Hint Resolve is_local_triple.

(** Lemma to introduce hoare instances for establishing triples,
    integrating the consequence rule. *)

Lemma triple_of_hoare : forall t H Q,
  (forall H', exists Q', hoare t (H \* H') Q' /\ Q' ===> Q \*+ H' \*+ \GC) ->
  triple t H Q.
Proof using.
  introv M. intros HF. lets (Q'&N&W): M HF. applys* hoare_conseq N.
Qed.

(** Lemma to reciprocally deduce a hoare triple from a SL triple *)

Lemma hoare_of_triple : forall t H Q HF,
  triple t H Q ->
  hoare t ((H \* HF) \* \GC) (fun r => (Q r \* HF) \* \GC).
Proof using.
  introv M. applys hoare_conseq. { applys M. } { hsimpl. } { hsimpl. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** SL rules structural *)

Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using. intros. applys* is_local_conseq. Qed.

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using. intros. applys* is_local_frame. Qed.

Lemma triple_hgc_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \GC) Q.
Proof using. intros. applys* is_local_hgc_pre. Qed.

Lemma triple_hgc_post : forall t H Q,
  triple t H (Q \*+ \GC) ->
  triple t H Q.
Proof using. intros. applys* is_local_hgc_post. Qed.

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using. intros. applys* is_local_hexists. Qed.

Lemma triple_hforall : forall A (x:A) t (J:A->hprop) Q,
  triple t (J x) Q ->
  triple t (hforall J) Q.
Proof using. intros. applys* is_local_hforall. Qed.

Lemma triple_hforall_exists : forall t A (J:A->hprop) Q, (* TODO: needed?*)
  (exists x, triple t (J x) Q) ->
  triple t (hforall J) Q.
Proof using. intros. applys* is_local_hforall_exists. Qed.

Lemma triple_hprop : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using. intros. applys* is_local_hprop. Qed.

Lemma triple_hwand_hpure_l : forall t (P:Prop) H Q,
  P ->
  triple t H Q ->
  triple t (\[P] \-* H) Q.
Proof using. intros. applys* is_local_hwand_hpure_l. Qed.

Lemma triple_hor : forall t H1 H2 Q,
  triple t H1 Q ->
  triple t H2 Q ->
  triple t (hor H1 H2) Q.
Proof using. intros. applys* is_local_hor. Qed.

Lemma triple_hand_l : forall t H1 H2 Q,
  triple t H1 Q ->
  triple t (hand H1 H2) Q.
Proof using. intros. applys* is_local_hand_l. Qed.

Lemma triple_hand_r : forall t H1 H2 Q,
  triple t H2 Q ->
  triple t (hand H1 H2) Q.
Proof using. intros. applys* is_local_hand_r. Qed.

Lemma triple_conseq_frame_hgc : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \GC ->
  triple t H Q.
Proof using. intros. applys* is_local_conseq_frame_hgc. Qed.


(* ---------------------------------------------------------------------- *)
(* ** SL rules for terms *)

Lemma triple_evalctx : forall C t1 H Q Q1,
  evalctx C ->
  triple t1 H Q1 ->
  (forall v, triple (C v) (Q1 v) Q) ->
  triple (C t1) H Q.
Proof using.
  introv HC M1 M2. intros HF. applys~ hoare_evalctx.
  { intros v. applys* hoare_of_triple. }
Qed.

(** Substitution commutes with evaluation contexts, for triples *)

Lemma triple_isubst_evalctx : forall E C t1 H Q Q1,
  evalctx C ->
  triple (isubst E t1) H Q1 ->
  (forall v, triple (isubst E (C v)) (Q1 v) Q) ->
  triple (isubst E (C t1)) H Q.
Proof using.
  Hint Constructors evalctx.
  Hint Resolve isubst_not_val_not_var.
  introv HC M1 M2. intros HF. inverts HC. (* simpl *)
  { rewrite isubst_trm_constr_args.
    applys triple_evalctx (fun t1 => trm_constr id (trms_vals vs ++ t1 :: map (isubst E) ts)); eauto.
    intros v. specializes M2 v. rewrite isubst_trm_constr_args in M2. applys M2. }
  { applys triple_evalctx (fun t1 => trm_let z t1 (isubst (Ctx.rem z E) t2)); eauto. }
  { applys triple_evalctx (fun t1 => trm_if t1 (isubst E t2) (isubst E t3)); eauto. }
  { applys triple_evalctx (fun t0 => trm_apps t0 (List.map (isubst E) ts)); eauto. }
  { rewrite isubst_trm_apps_args.
    applys triple_evalctx (fun t1 => trm_apps v0 (trms_vals vs ++ t1 :: map (isubst E) ts)); eauto.
    intros v. specializes M2 v. rewrite isubst_trm_apps_args in M2. applys M2. }
  { applys triple_evalctx (fun t1 => trm_for x t1 (isubst E t2) (isubst (Ctx.rem x E) t3)); eauto. }
  { applys triple_evalctx (fun t2 => trm_for x v1 t2 (isubst (Ctx.rem x E) t3)); eauto. }
  { applys triple_evalctx (fun t0 => trm_match t0 (List.map (fun '(pi,ti) => (pi, isubst (Ctx.rem_vars (patvars pi) E) ti)) pts)); eauto. }
Qed.

Lemma triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using.
  introv M. intros HF. applys hoare_val. { hchanges M. }
Qed.

Lemma triple_fixs : forall f xs t1 H Q,
  xs <> nil ->
  H ==> Q (val_fixs f xs t1) ->
  triple (trm_fixs f xs t1) H Q.
Proof using.
  introv N M. intros HF. applys~ hoare_fixs. { hchanges M. }
Qed.

Lemma triple_constr : forall id vs H Q,
  H ==> Q (val_constr id vs) ->
  triple (trm_constr id vs) H Q.
Proof using.
  introv M. intros HF. applys hoare_constr. { hchanges M. }
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

Lemma triple_if_bool : forall (b:bool) t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros HF. applys hoare_if_bool. applys M1.
Qed.

Lemma triple_if_bool_case : forall (b:bool) t1 t2 H Q,
  (b = true -> triple t1 H Q) ->
  (b = false -> triple t2 H Q) ->
  triple (trm_if b t1 t2) H Q.
Proof using.
  introv M1 M2. applys triple_if_bool. case_if*.
Qed.

Lemma triple_if_trm : forall Q1 t0 t1 t2 H Q,
  triple t0 H Q1 ->
  (forall v, triple (trm_if v t1 t2) (Q1 v) Q) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF. applys* hoare_if_trm.
  { intros v. applys* hoare_of_triple. }
Qed.

Lemma triple_if : forall Q1 t0 t1 t2 H Q, (* not very useful *)
  triple t0 H Q1 ->
  (forall (b:bool), triple (if b then t1 else t2) (Q1 b) Q) ->
  (forall v, ~ is_val_bool v -> (Q1 v) ==> \[False]) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2 M3. applys* triple_if_trm.
  { intros v. tests C: (is_val_bool v).
    { destruct C as (b&E). subst. applys* triple_if_bool. }
    { xchange* M3. xpull ;=>. false. } }
Qed.

Lemma triple_apps_funs : forall xs F (Vs:vals) t1 H Q,
  F = (val_funs xs t1) ->
  var_funs (length Vs) xs ->
  triple (substn xs Vs t1) H Q ->
  triple (trm_apps F Vs) H Q.
Proof using.
  introv E N M. intros H' h Hf. forwards (h'&v&R&K): (rm M) Hf.
  exists h' v. splits~. { subst. applys* red_apps_funs. }
Qed.

Lemma triple_apps_fixs : forall xs (f:var) F (Vs:vals) t1 H Q,
  F = (val_fixs f xs t1) ->
  var_fixs f (length Vs) xs ->
  triple (substn (f::xs) (F::Vs) t1) H Q ->
  triple (trm_apps F Vs) H Q.
Proof using.
  introv E N M. intros H' h Hf. forwards (h'&v&R&K): (rm M) Hf.
  exists h' v. splits~. { subst. applys* red_apps_fixs. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** SL Rules for loops *)

(** Rule for unfolding the body of a while loop once *)

Lemma triple_while_raw : forall t1 t2 H Q,
  triple (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) H Q ->
  triple (trm_while t1 t2) H Q.
Proof using.
  introv M. intros h Hf. apply hoare_while_raw. applys* M.
Qed.

(** Derived rule helping the set up of proof by inductions,
    by abstracting [trm_while t1 t2] as a fresh variable [t]. *)

Lemma triple_while : forall t1 t2 H Q,
  (forall t,
     (forall H' Q', triple (trm_if t1 (trm_seq t2 t) val_unit) H' Q' ->
                    triple t H' Q') ->
    triple t H Q) ->
  triple (trm_while t1 t2) H Q.
Proof using.
  introv M. applys M. introv K. applys triple_while_raw. applys K.
Qed.

(** Derived rule for reasoning about a while loop using a loop invariant *)

Lemma triple_while_inv : forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop) H' t1 t2 H Q,
  let Q' := (fun r => \exists Y, I false Y) in
  wf R ->
  (H ==> (\exists b X, I b X) \* H') ->
  (forall t b X,
      (forall b' X', R X' X -> triple t (I b' X') Q') ->
      triple (trm_if t1 (trm_seq t2 t) val_unit) (I b X) Q') ->
  Q' \*+ H' ===> Q \*+ \GC ->
  triple (trm_while t1 t2) H Q.
Proof using.
  introv WR WH HX WQ. applys triple_conseq_frame_hgc WH WQ.
  xpull ;=> b0 X0. gen b0. induction_wf IH: WR X0.
  intros. applys triple_while_raw.
  applys HX. intros b' X' HR'. applys~ IH.
Qed.

(** Rule for unfolding the body of a for-loop once *)

Lemma triple_for_raw : forall (x:var) (n1 n2:int) t3 H (Q:val->hprop),
  triple (
    If (n1 <= n2)
      then (trm_seq (subst1 x n1 t3) (trm_for x (n1+1) n2 t3))
      else val_unit) H Q ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using.
  introv M. intros h Hf. apply hoare_for_raw. applys* M.
Qed.

(** Derived rule for the case of a loop that performs no iteratation *)

Lemma triple_for_gt : forall x n1 n2 t3 H Q,
  n1 > n2 ->
  H ==> Q val_unit \* \GC ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using.
  introv N M. applys triple_for_raw. case_if; [math|].
  applys triple_hgc_post. applys* triple_val.
Qed.

(** Derived rule for the case of a loop that performs some iteratations *)

Lemma triple_for_le : forall Q1 (x:var) n1 n2 t3 H Q,
  n1 <= n2 ->
  triple (subst1 x n1 t3) H Q1 ->
  (forall v, triple (trm_for x (n1+1) n2 t3) (Q1 v) Q) ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using.
  introv N M1 M2. applys triple_for_raw. case_if; [|math].
  applys* triple_seq.
Qed.

(** Derived rule integrating the case analysis on whether iterations
    are performed on not. *)

Lemma triple_for : forall (x:var) (n1 n2:int) t3 H Q,
  (If (n1 <= n2) then
    (exists Q1,
      triple (subst1 x n1 t3) H Q1 /\
      (forall v, triple (trm_for x (n1+1) n2 t3) (Q1 v) Q))
  else
    (H ==> Q val_unit)) ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using.
  introv M. case_if.
  { destruct M. applys* triple_for_le. }
  { xapplys* triple_for_gt. { math. } hchanges* M. }
Qed.

(** Derived rule using an invariant for reasoning about a for-loop *)

Section RuleForInv.

Ltac auto_star ::= auto with maths.

Lemma triple_for_inv : forall (I:int->hprop) H' (x:var) n1 n2 t3 H Q,
  (n1 <= n2+1) ->
  (H ==> I n1 \* H') ->
  (forall i, n1 <= i <= n2 ->
     triple (subst1 x i t3) (I i) (fun r => I (i+1))) ->
  (I (n2+1) \* H' ==> Q val_unit \* \GC) ->
  triple (trm_for x n1 n2 t3) H Q.
Proof using.
  introv N M1 M2 M3. xchange (rm M1). gen N M2.
  induction_wf IH: (wf_upto (n2+1)) n1; intros.
  tests C: (n1 = n2+1).
  { xapply* triple_for_gt. hchanges M3. }
  { applys* triple_for_le.
    { xapplys* M2. }
    { xpull ;=> _. tests C': (n1 = n2).
      { xapply* triple_for_gt. hchanges M3. }
      { xapplys* IH. } } }
Qed.

End RuleForInv.


(* ---------------------------------------------------------------------- *)
(* ** SL rules for pattern matching *)

Lemma triple_match_trm : forall t1 pts H Q Q1,
  triple t1 H Q1 -> 
  (forall v, triple (trm_match v pts) (Q1 v) Q) ->
  triple (trm_match t1 pts) H Q.
Proof using.
  introv M1 M2. intros HF. applys~ hoare_case_trm.
  { intros b. applys* hoare_of_triple. }
Qed.

Lemma triple_match : forall v p t1 pts H Q,
  (forall (G:ctx), Ctx.dom G = patvars p -> v = patsubst G p -> triple (isubst G t1) H Q) ->
  ((forall (G:ctx), Ctx.dom G = patvars p -> v <> patsubst G p) -> triple (trm_match v pts) H Q) ->
  triple (trm_match v ((p,t1)::pts)) H Q.
Proof using.
  introv M1 M2. intros HF. applys hoare_match.
  { introv HG Hv. applys* M1. }
  { introv HG Hv. applys* M2. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** SL rules for primitive functions over the state *)

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists l, \[r = val_loc l] \* l ~~~> v).
Proof using.
  intros. applys triple_of_hoare. intros HF. rew_heap.
  esplit; split. { applys hoare_ref. } { hsimpl*. }
Qed.

Lemma triple_get : forall v l,
  triple (val_get (val_loc l))
    (l ~~~> v)
    (fun x => \[x = v] \* (l ~~~> v)).
Proof using.
  intros. applys triple_of_hoare. intros HF.
  esplit; split. { applys hoare_get. } { hsimpl*. }
Qed.

Lemma triple_set : forall w l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => \[r = val_unit] \* l ~~~> w).
Proof using.
  intros. applys triple_of_hoare. intros HF.
  esplit; split. { applys hoare_set. } { hsimpl*. }
Qed.

Lemma triple_set' : forall w l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => l ~~~> w).
Proof using. intros. xapplys* triple_set. Qed.

Lemma triple_alloc : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (fun r => \exists l, \[r = val_loc l /\ l <> null] \* Alloc (abs n) l).
Proof using.
  intros. applys triple_of_hoare. intros HF.
  esplit; split. { applys~ hoare_alloc. } { hsimpl*. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** SL rules for other primitive functions *)

Lemma triple_unop : forall v op v1,
  redunop op v1 v ->
  triple (op v1) \[] (fun r => \[r = v]).
Proof using.
  introv R. applys triple_of_hoare. intros HF.
  esplit; split. { applys* hoare_unop. } { hsimpl*. }
Qed.

Lemma triple_neg : forall (b1:bool),
  triple (val_neg b1)
    \[]
    (fun r => \[r = val_bool (neg b1)]).
Proof using. intros. applys* triple_unop. applys* redunop_neg. Qed.

Lemma triple_opp : forall n1,
  triple (val_opp n1)
    \[]
    (fun r => \[r = val_int (- n1)]).
Proof using. intros. applys* triple_unop. applys* redunop_opp. Qed.

Lemma triple_binop : forall v op v1 v2,
  redbinop op v1 v2 v ->
  triple (op v1 v2) \[] (fun r => \[r = v]).
Proof using.
  introv R. applys triple_of_hoare. intros HF.
  esplit; split. { applys* hoare_binop. } { hsimpl*. }
Qed.

Lemma triple_eq : forall v1 v2,
  triple (val_eq v1 v2)
    \[]
    (fun r => \[r = isTrue (v1 = v2)]).
Proof using. intros. applys* triple_binop. applys redbinop_eq. Qed.

Lemma triple_neq : forall v1 v2,
  triple (val_neq v1 v2)
    \[]
    (fun r => \[r = isTrue (v1 <> v2)]).
Proof using. intros. applys* triple_binop. applys redbinop_neq. Qed.

Lemma triple_add : forall n1 n2,
  triple (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).
Proof using. intros. applys* triple_binop. applys* redbinop_add. Qed.

Lemma triple_sub : forall n1 n2,
  triple (val_sub n1 n2)
    \[]
    (fun r => \[r = val_int (n1 - n2)]).
Proof using. intros. applys* triple_binop. applys* redbinop_sub. Qed.

Lemma triple_mul : forall n1 n2,
  triple (val_mul n1 n2)
    \[]
    (fun r => \[r = val_int (n1 * n2)]).
Proof using. intros. applys* triple_binop. applys* redbinop_mul. Qed.

Lemma triple_div : forall n1 n2,
  n2 <> 0 ->
  triple (val_div n1 n2)
    \[]
    (fun r => \[r = val_int (Z.quot n1 n2)]).
Proof using. intros. applys* triple_binop. applys* redbinop_div. Qed.

Lemma triple_mod : forall n1 n2,
  n2 <> 0 ->
  triple (val_mod n1 n2)
    \[]
    (fun r => \[r = val_int (Z.rem n1 n2)]).
Proof using. intros. applys* triple_binop. applys* redbinop_mod. Qed.

Lemma triple_le : forall n1 n2,
  triple (val_le n1 n2)
    \[]
    (fun r => \[r = isTrue (n1 <= n2)]).
Proof using. intros. applys* triple_binop. applys* redbinop_le. Qed.

Lemma triple_lt : forall n1 n2,
  triple (val_lt n1 n2)
    \[]
    (fun r => \[r = isTrue (n1 < n2)]).
Proof using. intros. applys* triple_binop. applys* redbinop_lt. Qed.

Lemma triple_ge : forall n1 n2,
  triple (val_ge n1 n2)
    \[]
    (fun r => \[r = isTrue (n1 >= n2)]).
Proof using. intros. applys* triple_binop. applys* redbinop_ge. Qed.

Lemma triple_gt : forall n1 n2,
  triple (val_gt n1 n2)
    \[]
    (fun r => \[r = isTrue (n1 > n2)]).
Proof using. intros. applys* triple_binop. applys* redbinop_gt. Qed.

Lemma triple_ptr_add : forall l n,
  l + n >= 0 ->
  triple (val_ptr_add l n)
    \[]
    (fun r => \[r = val_loc (abs (l + n))]).
Proof using.
  intros. applys* triple_binop. applys* redbinop_ptr_add.
  { rewrite~ abs_nonneg. }
Qed.

(** Derived rule for pointer addition for [nat] addition *)

Lemma triple_ptr_add_nat : forall l (f:nat),
  triple (val_ptr_add l f)
    \[]
    (fun r => \[r = val_loc (l+f)%nat]).
Proof using.
  intros. xapplys~ triple_ptr_add. { math. }
  { intros. subst. fequals.
    applys eq_nat_of_eq_int. rewrite abs_nonneg; math. }
Qed.


(* ********************************************************************** *)
(* * Bonus *)

(* ---------------------------------------------------------------------- *)
(* ** Alternative, low-level definition of triples *)

Definition triple' t H Q :=
  forall h1 h2,
  \# h1 h2 ->
  H h1 ->
  exists h1' h3' v,
       \# h1' h2 h3'
    /\ red (h1 \u h2) t (h1' \u h2 \u h3') v
    /\ (Q v) h1'.


Section TripleLowLevel.

Hint Extern 1 (\# _ _ _) => fmap_disjoint_pre.

Lemma triple_eq_triple' : triple = triple'.
Proof using.
  applys pred_ext_3. intros t H Q.
  unfold triple, triple', hoare. iff M.
  { introv D P1.
    forwards~ (h'&v&R1&R2): M (=h2) (h1 \u h2). { apply~ hstar_intro. }
    destruct R2 as (h2'&h1''&N0&N1&N2&N3).
    destruct N0 as (h1'&h3'&T0&T1&T2&T3). subst.
    exists h1' h1'' v. splits~. { fmap_red. } }
  { introv (h1&h2&N1&N2&D&U).
    forwards~ (h1'&h3'&v&R1&R2&R3): M h1 h2.
    exists (h1' \u h3' \u h2) v. splits~.
    { fmap_red. }
    { subst. rewrite hstar_assoc. apply~ hstar_intro.
      rewrite hstar_comm. applys~ hstar_intro. applys hgc_intro. } }
Qed.

End TripleLowLevel.
