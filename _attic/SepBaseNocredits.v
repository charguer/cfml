(**

This file formalizes standard Separation Logic. It contains:
- a definition of heaps as finite maps from location to values,
- an instantiation of the functor from the file [LibSepFunctor.v],
- a definition of triples,
- statement and proofs of structural rules,
- statement and proofs of rules for terms,
- statement and proofs of rules for primitive operations,
- bonuses: an alternative definition of triples, and derived rules.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From CFML Require Export Semantics LibSepFunctorOld.
From CFML Require Import LibSepFmap.
Module Fmap := LibSepFmap.
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

Declare Scope heap_scope.

(** A heap is a state (a finite map from location to values)
   as defined in [Semantics.v]. *)

Definition heap : Type := (state)%type.

(** Affinity is trivial *)

Definition heap_affine (h:heap) := True.

(** For uniformity with other instantiations of the Separation Logic
  functor, we introduce mklocal names for operations and lemmas on heaps. *)

Definition heap_empty : heap := Fmap.empty.

Declare Scope heap_union_scope.

Notation "h1 \u h2" := (Fmap.union h1 h2)
  (at level 37, right associativity) : heap_union_scope.
  (* --LATER: could try to introduce [heap_union := Fmap.union] *)

Local Open Scope heap_union_scope.

Definition heap_union_empty_l := Fmap.union_empty_l.

Definition heap_union_empty_r := Fmap.union_empty_r.

Definition heap_union_comm := Fmap.union_comm_of_disjoint.

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

(** Empty heap predicate: [ \[] ] *)

Definition hempty : hprop :=
  fun h => h = heap_empty.

(** Separating conjunction: [H1 \* H2] *)

Definition hstar (H1 H2 : hprop) : hprop :=
  fun h => exists h1 h2, H1 h1
                      /\ H2 h2
                      /\ (Fmap.disjoint h1 h2)
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

Open Scope heap_scope.


(* ---------------------------------------------------------------------- *)
(* ** Types *)

Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ---------------------------------------------------------------------- *)
(* ** Tactic for automation *)

Hint Extern 1 (_ = _ :> heap) => fmap_eq.
Hint Extern 1 (_ = _ :> state) => fmap_eq.

Tactic Notation "fmap_disjoint_pre" :=
  subst; rew_disjoint; jauto_set.

Hint Extern 1 (Fmap.disjoint _ _) => fmap_disjoint_pre.


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
  intros H1 H2 H3. applys pred_ext_1. intros h. split.
  { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U). subst h'.
    exists h1 (h2 \+ h3). splits~. { exists* h2 h3. } }
  { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U). subst h'.
    exists (h1 \+ h2) h3. splits~. { exists* h1 h2. } }
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


(* ---------------------------------------------------------------------- *)
(* ** Axiomatization of credits *)

(** TODO: realize this using the model *)

Parameter use_credits : bool.

Notation "'credits'" := Z.

Parameter hcredits : credits -> hprop.
  (* realize as: if use_credits then  "consume n credits"  else \[] *)

Notation "'\$' n" := (hcredits n)
  (at level 40,
   n at level 0,
   format "\$ n") : heap_scope.

Open Scope heap_scope.

Parameter hcredits_skip :
  use_credits = false ->
  forall n, \$ n = \[].

Parameter hcredits_zero :
  \$ 0 = \[].

Parameter hcredits_add : forall n m,
  \$ (n+m) = \$ n \* \$ m.

Parameter haffine_hcredits : forall n,
  n >= 0 ->
  haffine (\$ n).

(* TODO: find out what is a more primitive way to derive [hwand_hcredits_l]. *)

  Definition hpure' (P:Prop) : hprop :=
    hexists (fun (p:P) => hempty).

  Definition hwand' (H1 H2 : hprop) : hprop :=
    hexists (fun (H:hprop) => H \* (hpure' (H1 \* H ==> H2))).

  Parameter hwand_hcredits_l' : forall H n,
    (hwand' (\$n) H) = (\$(-n) \* H).

End SepBasicCore.



(* ********************************************************************** *)
(* * Derived properties of the logic *)

(** Here, we instantiate the functors to obtained derived definitions,
  lemmas, notation, and tactics. *)

Module Export SepBasicSetup := SepSetup SepBasicCore.
Export SepBasicCore.

Local Open Scope heap_union_scope.

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.


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
  Fmap.disjoint h1 h2 ->
  (H1 \* H2) (h1 \u h2).
Proof using. intros. exists~ h1 h2. Qed.

Lemma hstar_inv : forall H1 H2 h,
  (H1 \* H2) h ->
  exists h1 h2, H1 h1 /\ H2 h2 /\ Fmap.disjoint h1 h2 /\ h = h1 \u h2.
Proof using. introv M. hnf in M. eauto. Qed.

Lemma hgc_intro : forall h,
  \GC h.
Proof using. intros. applys hgc_of_heap_affine. hnfs*. Qed.

Lemma hgc_eq_htop :
  \GC = \Top.
Proof using. applys hgc_eq_htop_of_haffine_any. applys haffine_any. Qed.


(** Derived properties about credits *)

Ltac xsimpl_use_credits tt ::=
  constr:(true).

Lemma hcredits_sub : forall (n m : int),
  \$(n-m) = \$ n \* \$ (-m).
Proof using. intros. math_rewrite (n-m = n+(-m)). rewrite* hcredits_add. Qed.

Lemma hcredits_cancel : forall (n: int),
  \$ n \* \$ (-n) = \[].
Proof using. intros. rewrite <- hcredits_add, <- hcredits_zero. fequals. math. Qed.

Lemma hcredits_extract : forall m n,
  \$ n = \$ m \* \$ (n-m).
Proof using. intros. rewrite <- hcredits_add. fequals. math. Qed.

End Aux.

Global Opaque heap_affine.


(* ---------------------------------------------------------------------- *)
(* ** Singleton heap *)

(** Definition of the singleton heap predicate, written [r ~~~> v] *)

Definition hsingle (l:loc) (v:val) : hprop :=
  fun h => h = Fmap.single l v /\ l <> null.

Notation "l '~~~>' v" := (hsingle l v)
  (at level 32, no associativity) : heap_scope.

Lemma hsingle_intro : forall l v,
  l <> null ->
  (l ~~~> v) (Fmap.single l v).
Proof using. intros. split~. Qed.

Lemma hsingle_inv : forall h l v,
  (l ~~~> v) h ->
  h = Fmap.single l v /\ (l <> null).
Proof using. auto. Qed.

Lemma hstar_hsingle_same_loc : forall l v1 v2,
  (l ~~~> v1) \* (l ~~~> v2) ==> \[False].
Proof using.
  intros. unfold hsingle. intros h (h1&h2&E1&E2&D&E). false.
  subst. applys* Fmap.disjoint_single_single_same_inv.
Qed.

Lemma hsingle_not_null : forall l v,
  (l ~~~> v) ==> (l ~~~> v) \* \[l <> null].
Proof using.
  introv. intros h (Hh&Nl).
  exists h heap_empty. splits. (* TODO: splits~ goes into infinite loop *)
  { unfold hsingle. splits~. }
  { applys~ hpure_intro. }
  { unfold heap_empty. auto. }
  { rew_fmap*. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Singleton field heap *)

(** Definition of the heap predicate describing a single record field,
  written [l `. f ~> v]. *)

Definition hfield (l:loc) (k:field) (v:val) : hprop :=
  (l+k)%nat ~~~> v \* \[ l <> null ].

Notation "l `. k '~~~>' v" := (hfield l k v)
  (at level 32, k at level 0, no associativity,
   format "l `. k  '~~~>'  v") : heap_scope.

Lemma hstar_hfield_same_loc : forall l k v1 v2,
  (l`.k ~~~> v1) \* (l`.k ~~~> v2) ==> \[False].
Proof using.
  intros. unfold hfield. xpull ;=> N1 N2.
  applys hstar_hsingle_same_loc.
Qed.

Arguments hstar_hsingle_same_loc : clear implicits.

Lemma hfield_not_null : forall l k v,
  (l`.k ~~~> v) ==> (l`.k ~~~> v) \* \[l <> null].
Proof using.
  intros. subst. unfold hfield. xchanges~ hsingle_not_null.
Qed.

Arguments hfield_not_null : clear implicits.

Lemma hfield_eq_fun_hsingle :
  hfield = (fun l k v => ((l+k)%nat ~~~> v) \* \[l <> null]).
Proof using. intros. auto. Qed.

Lemma hfield_to_hsingle : forall l k v,
  (l`.k ~~~> v) ==> ((l+k)%nat ~~~> v) \* \[l <> null].
Proof using. intros. auto. Qed.

Lemma hsingle_to_hfield : forall l k v,
  l <> null ->
  ((l+k)%nat ~~~> v) ==> l`.k ~~~> v.
Proof using. intros. unfold hfield. xsimpl~. Qed.

Arguments hsingle_to_hfield : clear implicits.

Global Opaque hsingle hfield.


(* ---------------------------------------------------------------------- *)
(* ** Configuration of tactics *)

(* ** Configure [xsimpl] to make it aware of [hsingle] *)

Ltac xsimpl_hook H ::=
  match H with
  | hsingle _ _ => xsimpl_cancel_same H
  | hfield _ _ _ => xsimpl_cancel_same H
  end.

(* ** Configure [haffine] to make it aware of [haffine_any] *)

Ltac xaffine_custom tt ::=
  apply haffine_any.


(* ---------------------------------------------------------------------- *)
(* ** Auxiliary definitions for [triple_if] and [triple_seq] *)

Definition is_val_bool (v:val) : Prop :=
  exists b, v = val_bool b.


(* ---------------------------------------------------------------------- *)
(* ** Auxiliary definitions for [triple_alloc] *)

Fixpoint Alloc (k:nat) (l:loc) : hprop :=
  match k with
  | O => \[]
  | S k' => l ~~~> val_uninitialized \* (Alloc k' (S l)%nat)
  end.

Lemma Alloc_zero_eq : forall l,
  Alloc O l = \[].
Proof using. auto. Qed.

Lemma Alloc_succ_eq : forall l k,
  Alloc (S k) l = l ~~~> val_uninitialized \* Alloc k (S l)%nat.
Proof using. auto. Qed.

Global Opaque Alloc.

Hint Rewrite Alloc_zero_eq Alloc_succ_eq : rew_Alloc.

Tactic Notation "rew_Alloc" :=
  autorewrite with rew_Alloc.

Lemma Alloc_fmap_conseq : forall l k,
  l <> null ->
  (Alloc k l) (Fmap.conseq (LibList.make k val_uninitialized) l).
Proof using.
  Transparent loc null.
  introv N. gen l. induction k; intros; rew_Alloc.
  { rewrite LibList.make_zero, Fmap.conseq_nil. applys~ hempty_intro. }
  { rewrite LibList.make_succ, Fmap.conseq_cons. applys hstar_intro.
    { split~. }
    { applys IHk. unfolds loc, null. math. }
    { applys~ Fmap.disjoint_single_conseq. } }
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


(* ---------------------------------------------------------------------- *)
(* ** Auxiliary definitions for [triple_dealloc] *)

Fixpoint Dealloc (k:nat) (l:loc) : hprop :=
  match k with
  | O => \[]
  | S k' => \exists v, l ~~~> v \* (Dealloc k' (S l)%nat)
  end.

Lemma Dealloc_zero_eq : forall l,
  Dealloc O l = \[].
Proof using. auto. Qed.

Lemma Dealloc_succ_eq : forall l k,
  Dealloc (S k) l = \exists v, l ~~~> v \* Dealloc k (S l)%nat.
Proof using. auto. Qed.

Global Opaque Dealloc.

Hint Rewrite Dealloc_zero_eq Dealloc_succ_eq : rew_Dealloc.

Tactic Notation "rew_Dealloc" :=
  autorewrite with rew_Dealloc.

Lemma Dealloc_inv : forall k l h,
  Dealloc k l h ->
  exists vs, k = LibList.length vs
          /\ h = Fmap.conseq vs l.
Proof using.
  Transparent loc.
  intros k l. gen l. induction k; introv N.
  { rewrite Dealloc_zero_eq in N. exists (@nil val).
    rewrite Fmap.conseq_nil. split~. }
  { rewrite Dealloc_succ_eq in N. lets (v&N2): hexists_inv N.
    lets (h1&h2&R1&R2&R3&R4): hstar_inv N2.
    lets (R1'&Hl): hsingle_inv R1.
    forwards (vs'&Lvs'&Hvs'): IHk R2.
    exists (v::vs'). split.
    { rew_list~. }
    { subst h. rewrite~ Fmap.conseq_cons. } }
Qed.


(* ********************************************************************** *)
(** * Definition of Hoare triples *)

Definition hoare (t:trm) (H:hprop) (Q:val->hprop) :=
  forall h, H h -> exists h' v, eval h t h' v /\ Q v h'.


(* ********************************************************************** *)
(** * Hoare structural rules *)

Lemma hoare_conseq : forall t H' Q' H Q,
  hoare t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoare t H Q.
Proof using.
  introv M MH MQ HF. forwards (h'&v&R&K): M h.
  { applys* MH. }
  exists h' v. splits~. { applys* MQ. }
Qed.

Lemma hoare_named_heap : forall t H Q,
  (forall h, H h -> hoare t (= h) Q) ->
  hoare t H Q.
Proof using. introv M. intros h Hh. applys* M. Qed.


(* ********************************************************************** *)
(** * Hoare rules for term constructs *)

Lemma hoare_evalctx : forall C t1 H Q Q1,
  evalctx C ->
  hoare t1 H Q1 ->
  (forall v, hoare (C v) (Q1 v) Q) ->
  hoare (C t1) H Q.
Proof using.
  introv HC M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval_evalctx R2. }
Qed.

Lemma hoare_val : forall v H Q,
  H ==> Q v ->
  hoare (trm_val v) H Q.
Proof using.
  introv M. intros h Hh. exists h v. splits.
  { applys eval_val. }
  { applys* M. }
Qed.

Lemma hoare_fixs : forall f xs t1 H Q,
  xs <> nil ->
  H ==> Q (val_fixs f xs t1) ->
  hoare (trm_fixs f xs t1) H Q.
Proof using.
  introv N M. intros h Hh. exists. splits.
  { applys~ eval_fixs. }
  { applys* M. }
Qed.

Lemma hoare_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  hoare (trm_fun x t1) H Q.
Proof using. introv M. applys hoare_fixs; auto_false. Qed.

Lemma hoare_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  hoare (trm_fix f x t1) H Q.
Proof using. introv M. applys hoare_fixs; auto_false. Qed.

Lemma hoare_constr : forall id vs H Q,
  H ==> Q (val_constr id vs) ->
  hoare (trm_constr id (trms_vals vs)) H Q.
Proof using.
  introv M. intros h Hh. exists h (val_constr id vs). splits.
  { applys eval_constr. }
  { applys* M. }
Qed.

Lemma hoare_constr_trm : forall id ts t1 vs H Q Q1,
  hoare t1 H Q1 ->
  (forall v, hoare (trm_constr id ((trms_vals vs)++(trm_val v)::ts)) (Q1 v) Q) ->
  hoare (trm_constr id ((trms_vals vs)++t1::ts)) H Q.
Proof using.
  introv M1 M2. intros h Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval_constr_trm R2. }
Qed.

Lemma hoare_let : forall z t1 t2 H Q Q1,
  hoare t1 H Q1 ->
  (forall v, hoare (subst1 z v t2) (Q1 v) Q) ->
  hoare (trm_let z t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval_let_trm R2. }
Qed.

Lemma hoare_seq : forall t1 t2 H Q H1,
  hoare t1 H (fun r => H1) ->
  hoare t2 H1 Q ->
  hoare (trm_seq t1 t2) H Q.
Proof using. introv M1 M2. applys* hoare_let. Qed.

Lemma hoare_if : forall (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros h Hh. forwards* (h1'&v1&R1&K1): (rm M1).
  exists h1' v1. splits~. { applys* eval_if. }
Qed.

Lemma hoare_if_trm : forall Q1 t0 t1 t2 H Q,
  hoare t0 H Q1 ->
  (forall v, hoare (trm_if v t1 t2) (Q1 v) Q) ->
  hoare (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. applys* hoare_evalctx (fun t0 => trm_if t0 t1 t2).
  { constructor. }
Qed.

Lemma hoare_apps_funs : forall xs F vs t1 H Q,
  F = (val_funs xs t1) ->
  var_funs xs (length vs) ->
  hoare (substn xs vs t1) H Q ->
  hoare (trm_apps F vs) H Q.
Proof using.
  introv E N M. intros h Hh. forwards* (h'&v&R&K): (rm M).
  exists h' v. splits~. { subst. applys* eval_apps_funs. }
Qed.

Lemma hoare_apps_fixs : forall xs (f:var) F vs t1 H Q,
  F = (val_fixs f xs t1) ->
  var_fixs f xs (length vs) ->
  hoare (substn (f::xs) (F::vs) t1) H Q ->
  hoare (trm_apps F vs) H Q.
Proof using.
  introv E N M. intros h Hh. forwards* (h'&v&R&K): (rm M).
  exists h' v. splits~. { subst. applys* eval_apps_fixs. }
Qed.

Lemma hoare_while_raw : forall t1 t2 H Q,
  hoare (trm_if t1 (trm_seq t2 (trm_while t1 t2)) val_unit) H Q ->
  hoare (trm_while t1 t2) H Q.
Proof using.
  introv M Hh. forwards* (h1'&v1&R1&K1): (rm M).
  exists h1' v1. splits~. { applys* eval_while. }
Qed.

Lemma hoare_for_raw : forall (x:var) (n1 n2:int) t3 H Q,
  hoare (
    If (n1 <= n2)
      then (trm_seq (subst1 x n1 t3) (trm_for x (n1+1) n2 t3))
      else val_unit) H Q ->
  hoare (trm_for x n1 n2 t3) H Q.
Proof using.
  introv M Hh. forwards* (h1'&v1&R1&K1): (rm M).
  exists h1' v1. splits~. { applys* eval_for. }
Qed.

Lemma hoare_match : forall v p t1 pts H Q,
  (forall (G:ctx), Ctx.dom G = patvars p -> v = patsubst G p -> hoare (isubst G t1) H Q) ->
  ((forall (G:ctx), Ctx.dom G = patvars p -> v <> patsubst G p) -> hoare (trm_match v pts) H Q) ->
  hoare (trm_match v ((p,t1)::pts)) H Q.
Proof using.
  introv M1 M2 Hh. tests C: (exists (G:ctx), Ctx.dom G = patvars p /\ v = patsubst G p).
  { destruct C as (G&DG&Ev). forwards* (h1'&v1&R1&K1): (rm M1).
    exists h1' v1. splits~. { applys~ eval_match_yes R1. } }
  { forwards* (h1'&v1&R1&K1): (rm M2).
    exists h1' v1. splits~. { applys~ eval_match_no R1.
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
  exists h2' v2. splits~. { applys~ eval_match_trm R2. }
Qed.


(* ********************************************************************** *)
(* * Hoare reasoning rules for primitives *)

Section HoarePrimitives.
Transparent hstar hsingle hfield hexists loc null.
Hint Unfold hsingle.

Lemma hoare_ref : forall H v,
  hoare (val_ref v)
    H
    (fun r => (\exists l, \[r = val_loc l] \* l ~~~> v) \* H).
Proof using.
  intros. intros h Hh.
  forwards~ (l&Dl&Nl): (Fmap.single_fresh null h v).
  forwards~ Hh1': hsingle_intro l v.
  sets h1': (Fmap.single l v).
  exists (h1' \u h) (val_loc l). splits~.
  { applys~ eval_ref_sep. }
  { apply~ hstar_intro. { exists l. xsimplh~. } }
Qed.

Lemma hoare_get : forall H v l,
  hoare (val_get (val_loc l))
    ((l ~~~> v) \* H)
    (fun x => \[x = v] \* (l ~~~> v) \* H).
Proof using.
  intros. intros h Hh. exists h v. splits~.
  { destruct Hh as (h1&h2&(N1a&N1b)&N2&N3&N4).
    subst h. applys* eval_get_sep. }
  { xsimplh~. }
Qed.

Lemma hoare_set : forall H w l v,
  hoare (val_set (val_loc l) w)
    ((l ~~~> v) \* H)
    (fun r => \[r = val_unit] \* (l ~~~> w) \* H).
Proof using.
  intros. intros h Hh. destruct Hh as (h1&h2&(N1a&N1b)&N2&N3&N4).
  forwards~ Hh1': hsingle_intro l w.
  sets h1': (Fmap.single l w).
  exists (h1' \u h2) val_unit. splits~.
  { subst h h1. applys eval_set_sep; eauto. }
  { rewrite hstar_hpure. split~. apply hstar_intro. (* TODO: loop *)
    { auto. }
    { auto. }
    { applys~ Fmap.disjoint_single_set v. } }
Qed.

Lemma hoare_free : forall H l v,
  hoare (val_free (val_loc l))
    ((l ~~~> v) \* H)
    (fun r => \[r = val_unit] \* H).
Proof using.
  intros. intros h Hh. destruct Hh as (h1&h2&N1&N2&N3&N4).
  lets (E1&X1): hsingle_inv N1.
  exists h2 val_unit. split.
  { subst h1. applys* eval_free_sep. }
  { rewrite* hstar_hpure. }
Qed.

Lemma hoare_alloc : forall H n,
  n >= 0 ->
  hoare (val_alloc n)
    H
    (fun r => (\exists l, \[r = val_loc l /\ l <> null] \* Alloc (abs n) l) \* H).
Proof using. (* Note: [abs n] currently does not compute in Coq. *)
  introv N. intros h Hh.
  forwards~ (l&Dl&Nl): (Fmap.conseq_fresh null h (LibList.make (abs n) val_uninitialized)).
  match type of Dl with Fmap.disjoint ?hc _ => sets h1': hc end.
  exists (h1' \u h) (val_loc l). splits~.
  { applys~ (eval_alloc (abs n)). rewrite~ abs_nonneg. }
  { apply~ hstar_intro.
    { exists l. applys~ himpl_hstar_hpure_r. applys~ Alloc_fmap_conseq. } }
Qed.

Lemma hoare_dealloc : forall H l n,
  n >= 0 ->
  hoare (val_dealloc n l)
    (Dealloc (abs n) l \* H)
    (fun r => \[r = val_unit] \* H).
Proof using.
  introv N. intros h Hh. destruct Hh as (h1&h2&N1&N2&N3&N4). subst h.
  exists h2 val_unit. split.
  { forwards (vs&Lvs&Hvs): Dealloc_inv N1. applys* eval_dealloc.
    { rewrite <- Lvs. rewrite~ abs_to_int. } }
  { rewrite~ hstar_hpure. }
Qed.

Lemma hoare_unop : forall v H op v1,
  evalunop op v1 v ->
  hoare (op v1)
    H
    (fun r => \[r = v] \* H).
Proof using.
  introv R. intros h Hh. exists h v. splits.
  { applys* eval_unop. }
  { xsimplh~. }
Qed.

Lemma hoare_binop : forall v H op v1 v2,
  evalbinop op v1 v2 v ->
  hoare (op v1 v2)
    H
    (fun r => \[r = v] \* H).
Proof using.
  introv R. intros h Hh. exists h v. splits.
  { applys* eval_binop. }
  { xsimplh~. }
Qed.

End HoarePrimitives.


(* ********************************************************************** *)
(* * SL Reasoning Rules *)

(* ---------------------------------------------------------------------- *)
(* ** Definition of SL triples *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) :=
  forall H', hoare t (H \* H') (Q \*+ H' \*+ \GC).

(** SL triples satisfy [local], in the sense of LibSepFunctor *)

Lemma local_triple : forall t,
  local (triple t).
Proof using.
  intros. applys local_intro. intros H Q M H'.
  applys hoare_named_heap. intros h (h1&h2&N1&N2&N3&N4).
  lets (H1&H2&Q1&M0): (rm M) (rm N1).
  rewrite <- hstar_assoc, hstar_hpure_r in M0.
  destruct M0 as (M1&M2&M3).
  applys hoare_conseq (M2 (H2 \* H')).
  { subst. rewrite <- hstar_assoc. intros h ->. apply~ hstar_intro. }
  { intros x. xchanges (M3 x). }
Qed.

Hint Resolve local_triple.


(* ---------------------------------------------------------------------- *)
(* ** Connection with Hoare triples *)

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
  introv M. applys hoare_conseq. { applys M. } { xsimpl. } { xsimpl. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** SL rules structural *)

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
(* ** SL rules for evalation contexts *)

(** Auxiliary result involved in the proof of the next lemma *)

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
    applys triple_evalctx (fun t1 => trm_constr id (trms_vals vs ++ t1 :: LibList.map (isubst E) ts)); eauto.
    intros v. specializes M2 v. rewrite isubst_trm_constr_args in M2. applys M2. }
  { applys triple_evalctx (fun t1 => trm_let z t1 (isubst (Ctx.rem z E) t2)); eauto. }
  { applys triple_evalctx (fun t1 => trm_if t1 (isubst E t2) (isubst E t3)); eauto. }
  { applys triple_evalctx (fun t0 => trm_apps t0 (List.map (isubst E) ts)); eauto. }
  { rewrite isubst_trm_apps_args.
    applys triple_evalctx (fun t1 => trm_apps v0 (trms_vals vs ++ t1 :: LibList.map (isubst E) ts)); eauto.
    intros v. specializes M2 v. rewrite isubst_trm_apps_args in M2. applys M2. }
  { applys triple_evalctx (fun t1 => trm_for x t1 (isubst E t2) (isubst (Ctx.rem x E) t3)); eauto. }
  { applys triple_evalctx (fun t2 => trm_for x v1 t2 (isubst (Ctx.rem x E) t3)); eauto. }
  { applys triple_evalctx (fun t0 => trm_match t0 (List.map (fun '(pi,ti) => (pi, isubst (Ctx.rem_vars (patvars pi) E) ti)) pts)); eauto. }
Qed. (* --TODO: why List.map and LibList.map are mixed? Would a grammar of contexts work better? *)


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
  xtpull ;=> b0 X0. gen b0. induction_wf IH: WR X0.
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
  { xapplys* triple_for_gt. { math. } xchanges* M. }
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
  introv N M1 M2 M3. xtchange (rm M1). gen N M2.
  induction_wf IH: (wf_upto (n2+1)) n1; intros.
  tests C: (n1 = n2+1).
  { xapply* triple_for_gt. xchanges M3. }
  { applys* triple_for_le.
    { xapplys* M2. }
    { xtpull ;=> _. tests C': (n1 = n2).
      { xapply* triple_for_gt. xchanges M3. }
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

Lemma triple_alloc : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (fun r => \exists l, \[r = val_loc l /\ l <> null] \* Alloc (abs n) l).
Proof using.
  intros. applys triple_of_hoare. intros HF.
  esplit; split. { applys~ hoare_alloc. } { xsimpl*. }
Qed.

Lemma triple_dealloc : forall n l,
  n >= 0 ->
  triple (val_dealloc n l)
    (Dealloc (abs n) l)
    (fun r => \[r = val_unit]).
Proof using.
  intros. applys triple_of_hoare. intros HF.
  esplit; split. { applys~ hoare_dealloc. } { xsimpl*. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** SL rules for other primitive functions *)

Lemma triple_unop : forall v op v1,
  evalunop op v1 v ->
  triple (op v1) \[] (fun r => \[r = v]).
Proof using.
  introv R. applys triple_of_hoare. intros HF.
  esplit; split. { applys* hoare_unop. } { xsimpl*. }
Qed.

Lemma triple_neg : forall (b1:bool),
  triple (val_neg b1)
    \[]
    (fun r => \[r = val_bool (neg b1)]).
Proof using. intros. applys* triple_unop. applys* evalunop_neg. Qed.

Lemma triple_opp : forall n1,
  triple (val_opp n1)
    \[]
    (fun r => \[r = val_int (- n1)]).
Proof using. intros. applys* triple_unop. applys* evalunop_opp. Qed.

Lemma triple_binop : forall v op v1 v2,
  evalbinop op v1 v2 v ->
  triple (op v1 v2) \[] (fun r => \[r = v]).
Proof using.
  introv R. applys triple_of_hoare. intros HF.
  esplit; split. { applys* hoare_binop. } { xsimpl*. }
Qed.

Lemma triple_eq : forall v1 v2,
  triple (val_eq v1 v2)
    \[]
    (fun r => \[r = isTrue (v1 = v2)]).
Proof using. intros. applys* triple_binop. applys evalbinop_eq. Qed.

Lemma triple_neq : forall v1 v2,
  triple (val_neq v1 v2)
    \[]
    (fun r => \[r = isTrue (v1 <> v2)]).
Proof using. intros. applys* triple_binop. applys evalbinop_neq. Qed.

Lemma triple_add : forall n1 n2,
  triple (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_add. Qed.

Lemma triple_sub : forall n1 n2,
  triple (val_sub n1 n2)
    \[]
    (fun r => \[r = val_int (n1 - n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_sub. Qed.

Lemma triple_mul : forall n1 n2,
  triple (val_mul n1 n2)
    \[]
    (fun r => \[r = val_int (n1 * n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_mul. Qed.

Lemma triple_div : forall n1 n2,
  n2 <> 0 ->
  triple (val_div n1 n2)
    \[]
    (fun r => \[r = val_int (Z.quot n1 n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_div. Qed.

Lemma triple_mod : forall n1 n2,
  n2 <> 0 ->
  triple (val_mod n1 n2)
    \[]
    (fun r => \[r = val_int (Z.rem n1 n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_mod. Qed.

Lemma triple_le : forall n1 n2,
  triple (val_le n1 n2)
    \[]
    (fun r => \[r = isTrue (n1 <= n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_le. Qed.

Lemma triple_lt : forall n1 n2,
  triple (val_lt n1 n2)
    \[]
    (fun r => \[r = isTrue (n1 < n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_lt. Qed.

Lemma triple_ge : forall n1 n2,
  triple (val_ge n1 n2)
    \[]
    (fun r => \[r = isTrue (n1 >= n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_ge. Qed.

Lemma triple_gt : forall n1 n2,
  triple (val_gt n1 n2)
    \[]
    (fun r => \[r = isTrue (n1 > n2)]).
Proof using. intros. applys* triple_binop. applys* evalbinop_gt. Qed.

Lemma triple_ptr_add : forall l n,
  l + n >= 0 ->
  triple (val_ptr_add l n)
    \[]
    (fun r => \[r = val_loc (abs (l + n))]).
Proof using.
  intros. applys* triple_binop. applys* evalbinop_ptr_add.
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
  Fmap.disjoint h1 h2 ->
  H h1 ->
  exists h1' h3' v,
       Fmap.disjoint_3 h1' h2 h3'
    /\ eval (h1 \u h2) t (h1' \u h2 \u h3') v
    /\ (Q v) h1'.


Section TripleLowLevel.

Hint Extern 1 (Fmap.disjoint_3 _ _ _) => fmap_disjoint_pre.

Lemma triple_eq_triple' : triple = triple'.
Proof using.
  applys pred_ext_3. intros t H Q.
  unfold triple, triple', hoare. iff M.
  { introv D P1.
    forwards~ (h'&v&R1&R2): M (=h2) (h1 \u h2). { apply~ hstar_intro. }
    destruct R2 as (h2'&h1''&N0&N1&N2&N3).
    destruct N0 as (h1'&h3'&T0&T1&T2&T3). subst.
    exists h1' h1'' v. splits~. { applys_eq~ R1. } }
  { introv (h1&h2&N1&N2&D&U).
    forwards~ (h1'&h3'&v&R1&R2&R3): M h1 h2.
    exists (h1' \u h3' \u h2) v. splits~.
    { applys_eq~ R2. }
    { subst. rewrite hstar_assoc. apply~ hstar_intro.
      rewrite hstar_comm. applys~ hstar_intro. applys hgc_intro. } }
Qed.

End TripleLowLevel.

(** Restore default tactic *)
Ltac auto_star ::= auto_star_default.
