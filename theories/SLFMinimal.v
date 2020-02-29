(**

Separation Logic Foundations

Chapter: "Minimal".

This file contains a minimalist soundness proof for Separation Logic.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From TLC Require Export LibCore.
From Sep Require Export TLCbuffer Var Fmap.
From Sep Require SepSimpl.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Imports *)

(* ########################################################### *)
(** ** Extensionality axioms *)

(** These standard extensionality axioms come from TLC's LibAxiom.v file. *)

Axiom functional_extensionality : forall A B (f g:A->B),
  (forall x, f x = g x) ->
  f = g.

Axiom propositional_extensionality : forall (P Q:Prop),
  (P <-> Q) ->
  P = Q.


(* ########################################################### *)
(** ** Variables *)

(** The file [Var.v] defines the type [var] as an alias for [string].
    It provides the boolean function [var_eq x y] to compare two variables.
    It provides the tactic [case_var] to perform case analysis on
    expressions of the form [if var_eq x y then .. else ..]
    that appear in the goal. *)


(* ########################################################### *)
(** ** Finite maps *)

(** The file [Fmap.v] provides a formalization of finite maps, which
    are then used to represent heaps in the semantics.
    The implementation details need not be revealed.

    The library provides a tactic [fmap_disjoint] to automate the disjointness
    proofs, and a tactic [fmap_eq] to prove equalities between heaps modulo
    associativity and commutativity. Without these two tactics, the
    proofs would be extremely tedious and fragile. *)


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Source language *)

(* ########################################################### *)
(** ** Syntax *)

(** The grammar of the deeply-embedded language includes terms and
    values. Values include basic values such as [int] and [bool],
    locations (memory addresses, represented by natural numbers),
    and primitive operations. *)

(** The grammar of primitive operations includes many operations.
    In this file, we will only focus on addition and division.
    Other operations are specified in the file [SLFExtra.v]. *)

Inductive prim : Type :=
  | val_ref : prim
  | val_get : prim
  | val_set : prim
  | val_free : prim
  | val_add : prim
  | val_div : prim.

Definition loc : Type := nat.

Definition null : loc := 0%nat.

Inductive val : Type :=
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_prim : prim -> val
  | val_fix : var -> var -> trm -> val

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm.

(** The state consists of a finite map from location to values.
    Records and arrays are represented as sets of consecutive cells. *)

Definition state : Type := fmap loc val.

(** The type [heap], a.k.a. [state]. By convention, the "state"
    refers to the full memory state, while the "heap" potentially
    refers to only a fraction of the memory state. *)

Definition heap : Type := state.


(* ########################################################### *)
(** ** Coq tweaks *)

(** [heap_empty] is a handy notation to avoid providing
    type arguments to [Fmap.empty] *)

Notation "'heap_empty'" := (@Fmap.empty loc val)
  (at level 0).

(** Implicit types associated with meta-variables. *)

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types p : loc.
Implicit Types n : int.
Implicit Types v w r vf vx : val.
Implicit Types t : trm.
Implicit Types h : heap.
Implicit Types s : state.

(** The type of values is inhabited. *)

Global Instance Inhab_val : Inhab val.
Proof using. apply (Inhab_of_val val_unit). Qed.


(* ########################################################### *)
(** ** Substitution *)

(** Capture-avoiding substitution, standard definition. *)

Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if_y_eq x (trm_val w) t
  | trm_fix f x t1 => trm_fix f x (if_y_eq f t1 (if_y_eq x t1 (aux t1)))
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (if_y_eq x t2 (aux t2))
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  end.


(* ########################################################### *)
(** ** Coercions *)

(** Coercions to improve conciseness in the statment of evaluation rules. *)

Coercion val_bool : bool >-> val.
Coercion val_int : Z >-> val.
Coercion val_loc : loc >-> val.
Coercion val_prim : prim >-> val.

Coercion trm_val : val >-> trm.
Coercion trm_var : var >-> trm.
Coercion trm_app : trm >-> Funclass.


(* ########################################################### *)
(** ** Semantics *)

(** Big-step evaluation judgement, written [eval s t s' v] *)

Inductive eval : heap -> trm -> heap -> val -> Prop :=
  | eval_val : forall s v,
      eval s (trm_val v) s v
  | eval_fix : forall s f x t1,
      eval s (trm_fix f x t1) s (val_fix f x t1)
  | eval_app_fix : forall s1 s2 v1 v2 f x t1 v,
      v1 = val_fix f x t1 ->
      eval s1 (subst x v2 (subst f v1 t1)) s2 v ->
      eval s1 (trm_app v1 v2) s2 v
  | eval_let : forall s1 s2 s3 x t1 t2 v1 r,
      eval s1 t1 s2 v1 ->
      eval s2 (subst x v1 t2) s3 r ->
      eval s1 (trm_let x t1 t2) s3 r
  | eval_if : forall s1 s2 b v t1 t2,
      eval s1 (if b then t1 else t2) s2 v ->
      eval s1 (trm_if (val_bool b) t1 t2) s2 v
  | eval_add : forall m n1 n2,
      eval m (val_add (val_int n1) (val_int n2)) m (val_int (n1 + n2))
  | eval_div : forall m n1 n2,
       n2 <> 0 ->
     eval m (val_div (val_int n1) (val_int n2)) m (val_int (Z.quot n1 n2))
  | eval_ref : forall s v p,
      ~ Fmap.indom s p ->
      eval s (val_ref v) (Fmap.update s p v) (val_loc p)
  | eval_get : forall s p,
      Fmap.indom s p ->
      eval s (val_get (val_loc p)) s (Fmap.read s p)
  | eval_set : forall s p v,
      Fmap.indom s p ->
      eval s (val_set (val_loc p) v) (Fmap.update s p v) val_unit
  | eval_free : forall s p,
      Fmap.indom s p ->
      eval s (val_free (val_loc p)) (Fmap.remove s p) val_unit.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Heap predicates *)

(** For technical reasons, to enable sharing the code implementing
    the tactic [xmysimpl], we wrap the definitions inside a module. *)

Module SepSimplArgs.


(* ########################################################### *)
(** ** Hprop and entailment *)

(** The type of heap predicates is named [hprop]. *)

Definition hprop := heap -> Prop.

(** Entailment for heap predicates, written [H1 ==> H2]
    (the entailment is linear, although our triples will be affine). *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall h, H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55) : hprop_scope.

Open Scope hprop_scope.

(** Entailment between postconditions, written [Q1 ===> Q2] *)

Definition qimpl A (Q1 Q2:A->hprop) : Prop :=
  forall (v:A), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55) : hprop_scope.

(** Implicit types for meta-variables. *)

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ########################################################### *)
(** ** Definition of heap predicates *)

(** Core heap predicates, and their associated notations:

    - [\[]] denotes the empty heap predicate
    - [\[P]] denotes a pure fact
    - [p ~~> v] denotes a singleton heap
    - [H1 \* H2] denotes the separating conjunction
    - [Q1 \*+ H2] denotes the separating conjunction extending a postcondition
    - [\exists x, H] denotes an existential
    - [\forall x, H] denotes a universal
    - [H1 \-* H2] denotes a magic wand between heap predicates
    - [Q1 \--* Q2] denotes a magic wand between postconditions

*)

Definition hempty : hprop :=
  fun h => (h = Fmap.empty).

Definition hsingle (p:loc) (v:val) : hprop :=
  fun h => (h = Fmap.single p v /\ p <> null).

Definition hstar (H1 H2 : hprop) : hprop :=
  fun h => exists h1 h2, H1 h1
                              /\ H2 h2
                              /\ Fmap.disjoint h1 h2
                              /\ h = Fmap.union h1 h2.

Definition hexists A (J:A->hprop) : hprop :=
  fun h => exists x, J x h.

Definition hforall (A : Type) (J : A -> hprop) : hprop :=
  fun h => forall x, J x h.

Notation "\[]" := (hempty)
  (at level 0) : hprop_scope.

Notation "p '~~>' v" := (hsingle p v) (at level 32) : hprop_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : hprop_scope.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : hprop_scope.

(** Derived heap predicates.

    The following operators are defined in terms of the ones
    above, rather than as functions over heaps, to reduce the proof effort.
    See the summary section in [SLFWand.v] for details. *)

Definition hpure (P:Prop) : hprop :=
  \exists (p:P), \[].

Definition hwand (H1 H2 : hprop) : hprop :=
  \exists H0, H0 \* hpure ((H0 \* H1) ==> H2).

Definition qwand A (Q1 Q2:A->hprop) : hprop :=
  \forall x, hwand (Q1 x) (Q2 x).

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]") : hprop_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : hprop_scope.

Notation "H1 \-* H2" := (hwand H1 H2)
  (at level 43, right associativity) : hprop_scope.

Notation "Q1 \--* Q2" := (qwand Q1 Q2)
  (at level 43) : hprop_scope.



(* ########################################################### *)
(** ** Basic properties of Separation Logic operators *)

(* ################################################ *)
(** *** Tactic for automation *)

(** [auto] is set up to process goals of the form [h1 = h2] by calling
    [fmap_eq], which proves equality modulo associativity and commutativity. *)

Hint Extern 1 (_ = _ :> heap) => fmap_eq.

(** [auto] is set up to process goals of the form [Fmap.disjoint h1 h2] by calling
    [fmap_disjoint], which essentially normalizes all disjointness goals and
    hypotheses, split all conjunctions, and invokes proof search with a base
    of hints specified in [Fmap.v]. *)

Import Fmap.DisjointHints.

Tactic Notation "fmap_disjoint_pre" :=
  subst; rew_disjoint; jauto_set.

Hint Extern 1 (Fmap.disjoint _ _) => fmap_disjoint_pre.


(* ################################################ *)
(** *** Properties of [himpl] and [qimpl] *)

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. introv M. auto. Qed.

Hint Resolve himpl_refl.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using. introv M1 M2. unfolds* himpl. Qed.

Lemma himpl_trans_r : forall H2 H1 H3,
   H2 ==> H3 ->
   H1 ==> H2 ->
   H1 ==> H3.
Proof using. introv M1 M2. applys* himpl_trans M2 M1. Qed.

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  (H1 = H2).
Proof using. introv M1 M2. applys pred_ext_1. intros h. iff*. Qed.

Lemma hprop_op_comm : forall (op:hprop->hprop->hprop),
  (forall H1 H2, op H1 H2 ==> op H2 H1) ->
  (forall H1 H2, op H1 H2 = op H2 H1).
Proof using. introv M. intros. applys himpl_antisym; applys M. Qed.

Lemma qimpl_refl : forall A (Q:A->hprop),
  Q ===> Q.
Proof using. intros. unfolds*. Qed.

Hint Resolve qimpl_refl.


(* ################################################ *)
(** *** Properties of [hempty] *)

Lemma hempty_intro :
  \[] heap_empty.
Proof using. unfolds*. Qed.

Lemma hempty_inv : forall h,
  \[] h ->
  h = heap_empty.
Proof using. auto. Qed.


(* ################################################ *)
(** *** Properties of [hstar] *)

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  Fmap.disjoint h1 h2 ->
  (H1 \* H2) (Fmap.union h1 h2).
Proof using. intros. exists~ h1 h2. Qed.

Lemma hstar_inv : forall H1 H2 h,
  (H1 \* H2) h ->
  exists h1 h2, H1 h1 /\ H2 h2 /\ Fmap.disjoint h1 h2 /\ h = Fmap.union h1 h2.
Proof using. introv M. applys M. Qed.

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof using.
  applys hprop_op_comm. unfold hprop, hstar. intros H1 H2.
  intros h (h1&h2&M1&M2&D&U). rewrite~ Fmap.union_comm_of_disjoint in U.
  exists* h2 h1.
Qed.

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using.
  intros H1 H2 H3. applys himpl_antisym; intros h.
  { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U). subst h'.
    exists h1 (h2 \+ h3). splits~. { applys* hstar_intro. } }
  { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U). subst h'.
    exists (h1 \+ h2) h3. splits~. { applys* hstar_intro. } }
Qed.

Lemma hstar_hempty_l : forall H,
  \[] \* H = H.
Proof using.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&M1&M2&D&U). forwards E: hempty_inv M1. subst.
    rewrite~ Fmap.union_empty_l. }
  { intros M. exists heap_empty h. splits~. { applys hempty_intro. } }
Qed.

Lemma hstar_hempty_r : forall H,
  H \* \[] = H.
Proof using.
  applys neutral_r_of_comm_neutral_l. applys~ hstar_comm. applys~ hstar_hempty_l.
Qed.

Lemma hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof using.
  intros. applys himpl_antisym; intros h.
  { intros (h1&h2&(x&M1)&M2&D&U). exists~ x h1 h2. }
  { intros (x&(h1&h2&M1&M2&D&U)). exists h1 h2. splits~. { exists~ x. } }
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
  introv M1 M2. applys himpl_trans M2. applys himpl_frame_l M1.
Qed.

Lemma himpl_hstar_trans_r : forall H1 H2 H3 H4,
  H1 ==> H2 ->
  H3 \* H2 ==> H4 ->
  H3 \* H1 ==> H4.
Proof using.
  introv M1 M2. applys himpl_trans M2. applys himpl_frame_r M1.
Qed.


(* ################################################ *)
(** ***  Properties of [hpure] *)

Lemma hpure_intro : forall P,
  P ->
  \[P] heap_empty.
Proof using. introv M. exists M. unfolds*. Qed.

Lemma hpure_inv : forall P h,
  \[P] h ->
  P /\ h = heap_empty.
Proof using. introv (p&M). split~. Qed.

Lemma hstar_hpure : forall P H h,
  (\[P] \* H) h = (P /\ H h).
Proof using.
  intros. apply prop_ext. unfold hpure.
  rewrite hstar_hexists. rewrite* hstar_hempty_l.
  iff (p&M) (p&M). { split~. } { exists~ p. }
Qed.

Lemma himpl_hstar_hpure_r : forall P H H',
  P ->
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof using. introv HP W. intros h K. rewrite* hstar_hpure. Qed.

Lemma hpure_inv_hempty : forall P h,
  \[P] h ->
  P /\ \[] h.
Proof using.
  introv M. rewrite <- hstar_hpure. rewrite~ hstar_hempty_r.
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
  applys himpl_antisym; intros h M.
  { applys* hpure_intro_hempty. }
  { forwards*: hpure_inv_hempty M. }
Qed.

Lemma hfalse_hstar_any : forall H,
  \[False] \* H = \[False].
Proof using.
  intros. applys himpl_antisym; intros h; rewrite hstar_hpure; intros M.
  { false*. } { lets: hpure_inv_hempty M. false*. }
Qed.


(* ################################################ *)
(** *** Properties of [hexists] *)

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


(* ################################################ *)
(** *** Properties of [hforall] *)

Lemma himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (hforall J).
Proof using. introv M. intros h Hh x. apply~ M. Qed.

Lemma himpl_hforall_l : forall A x (J:A->hprop) H,
  (J x ==> H) ->
  (hforall J) ==> H.
Proof using. introv M. intros h Hh. apply~ M. Qed.

Lemma himpl_hforall : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hforall J1 ==> hforall J2.
Proof using.
  introv W. applys himpl_hforall_r. intros x. applys himpl_hforall_l W.
Qed.


(* ################################################ *)
(** *** Properties of [hwand] *)

Lemma hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 \-* H2) <-> (H0 \* H1 ==> H2).
Proof using.
  unfold hwand. iff M.
  { applys himpl_hstar_trans_l (rm M).
    rewrite hstar_hexists. applys himpl_hexists_l. intros H.
    rewrite (hstar_comm H). rewrite hstar_assoc.
    applys~ himpl_hstar_hpure_l. }
  { applys himpl_hexists_r H0.
    rewrite <- (hstar_hempty_r H0) at 1.
    applys himpl_frame_r. applys himpl_hempty_hpure M. }
Qed.

Lemma himpl_hwand_r : forall H1 H2 H3,
  H1 \* H2 ==> H3 ->
  H1 ==> (H2 \-* H3).
Proof using. introv M. rewrite~ hwand_equiv. Qed.

Lemma himpl_hwand_r_inv : forall H1 H2 H3,
  H1 ==> (H2 \-* H3) ->
  H1 \* H2 ==> H3.
Proof using. introv M. rewrite~ <- hwand_equiv. Qed.

Lemma hwand_cancel : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.
Proof using. intros. rewrite hstar_comm. rewrite~ <- hwand_equiv. Qed.

Arguments hwand_cancel : clear implicits.

Lemma himpl_hempty_hwand_same : forall H,
  \[] ==> (H \-* H).
Proof using. intros. rewrite hwand_equiv. rewrite~ hstar_hempty_l. Qed.

Lemma hwand_hempty_l : forall H,
  (\[] \-* H) = H.
Proof using.
  intros. applys himpl_antisym.
  { rewrite <- hstar_hempty_l at 1. applys hwand_cancel. }
  { rewrite hwand_equiv. rewrite~ hstar_hempty_r. }
Qed.

Lemma hwand_hpure_l_intro : forall (P:Prop) H,
  P ->
  \[P] \-* H ==> H.
Proof using.
  introv HP. rewrite <- hstar_hempty_l at 1.
  forwards~ K: himpl_hempty_hpure P.
  applys himpl_hstar_trans_l K. applys hwand_cancel.
Qed.

Arguments hwand_hpure_l_intro : clear implicits.

Lemma hwand_curry : forall H1 H2 H3,
  (H1 \* H2) \-* H3 ==> H1 \-* (H2 \-* H3).
Proof using.
  intros. do 2 rewrite hwand_equiv.
  rewrite hstar_assoc. rewrite hstar_comm. applys hwand_cancel.
Qed.

Lemma hwand_uncurry : forall H1 H2 H3,
  H1 \-* (H2 \-* H3) ==> (H1 \* H2) \-* H3.
Proof using.
  intros. rewrite hwand_equiv. rewrite <- (hstar_comm (H1 \* H2)).
  rewrite (@hstar_comm H1). rewrite hstar_assoc.
  applys himpl_hstar_trans_r.
  { applys hwand_cancel. } { applys hwand_cancel. }
Qed.

Lemma hwand_curry_eq : forall H1 H2 H3,
  (H1 \* H2) \-* H3 = H1 \-* (H2 \-* H3).
Proof using.
  intros. applys himpl_antisym.
  { applys hwand_curry. }
  { applys hwand_uncurry. }
Qed.


(* ################################################ *)
(** *** Properties of qwand *)

Lemma qwand_equiv : forall H A (Q1 Q2:A->hprop),
  H ==> (Q1 \--* Q2) <-> (Q1 \*+ H) ===> Q2.
Proof using.
  unfold qwand. iff M.
  { intros x. rewrite hstar_comm. applys himpl_hstar_trans_l (rm M).
    applys himpl_trans. applys hstar_hforall. simpl.
    applys himpl_hforall_l x. rewrite hstar_comm. applys hwand_cancel. }
  { applys himpl_hforall_r. intros x. rewrite hwand_equiv. rewrite* hstar_comm. }
Qed.

Lemma qwand_cancel : forall A (Q1 Q2:A->hprop),
  Q1 \*+ (Q1 \--* Q2) ===> Q2.
Proof using. intros. rewrite <- qwand_equiv. applys qimpl_refl. Qed.

Lemma himpl_qwand_r : forall A (Q1 Q2:A->hprop) H,
  Q1 \*+ H ===> Q2 ->
  H ==> (Q1 \--* Q2).
Proof using. introv M. rewrite~ qwand_equiv. Qed.

Arguments himpl_qwand_r [A].

Lemma qwand_specialize : forall A (x:A) (Q1 Q2:A->hprop),
  (Q1 \--* Q2) ==> (Q1 x \-* Q2 x).
Proof using. intros. applys* himpl_hforall_l x. Qed.

Arguments qwand_specialize [ A ].


(* ################################################ *)
(** *** Properties of [hsingle] *)

Lemma hsingle_intro : forall p v,
  p <> null ->
  (p ~~> v) (Fmap.single p v).
Proof using. introv N. hnfs*. Qed.

Lemma hsingle_inv: forall p v h,
  (p ~~> v) h ->
  h = Fmap.single p v /\ p <> null.
Proof using. auto. Qed.

Lemma hsingle_not_null : forall p v,
  (p ~~> v) ==> (p ~~> v) \* \[p <> null].
Proof using.
  introv. intros h (K&N). rewrite hstar_comm, hstar_hpure.
  split*. subst. applys* hsingle_intro.
Qed.

Lemma hstar_hsingle_same_loc : forall p v1 v2,
  (p ~~> v1) \* (p ~~> v2) ==> \[False].
Proof using.
  intros. unfold hsingle. intros h (h1&h2&E1&E2&D&E). false.
  subst. applys* Fmap.disjoint_single_single_same_inv.
Qed.

Arguments hstar_hsingle_same_loc : clear implicits.


(* ########################################################### *)
(** ** The [xsimpl] tactic *)

(** The definitions and properties above enable us to instantiate
    the [xsimpl] tactic, which implements powerful simplifications
    for Separation Logic entailments.

    For technical reasons, we need to provide a definition for [hgc],
    a restriction of [htop] to affine heap predicates. For our purpose,
    it suffices to define [hgc] as an alias for [htop]. *)


(* ################################################ *)
(** *** Definition and properties of [haffine] and [hgc] *)

Definition haffine (H:hprop) :=
  True.

Lemma haffine_hany : forall (H:hprop),
  haffine H.
Proof using. unfold haffine. auto. Qed.

Lemma haffine_hempty :
  haffine \[].
Proof using. applys haffine_hany. Qed.

Definition hgc := (* equivalent to [\exists H, \[haffine H] \* H] *)
  \exists H, H.

Definition htop := hgc.

Notation "\GC" := (hgc) : hprop_scope.

Lemma haffine_hgc :
  haffine \GC.
Proof using. applys haffine_hany. Qed.

Lemma himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.
Proof using. introv M. Admitted.

Lemma hstar_hgc_hgc :
  \GC \* \GC = \GC.
Proof using. Admitted.


(* ################################################ *)
(** *** Functor instantiation to obtain [xsimpl] *)

Notation "\Top" := (htop) : hprop_scope.

Lemma htop_intro : forall h,
  \Top h.
Proof using. intros. exists~ (=h). Qed.

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
  { rewrite <- hstar_hempty_r at 1. applys himpl_frame_r. applys himpl_htop_r. }
Qed.


End SepSimplArgs.


(** We are now ready to instantiate the functor, and open the
    contents of the module [SepHsimplArgs], essentially pretending
    that we inlined here its contents. *)

Module Export HS := SepSimpl.XsimplSetup(SepSimplArgs).

Export SepSimplArgs.

(** At this point, the tactic [xsimpl] is defined.
    There remains to customize the tactic so that it recognizes
    the predicate [p ~~> v] in a special way when performing
    simplifications. *)

(*  Internal hack: (the comment only makes sense in the context of [SepSimpl]).
    [xsimpl_pick_hsingle H] applies to a goal of the form
    [Xsimpl (Hla, Hlw, Hlt) HR], where [Hla] is of the form
    [H1 \* .. \* Hn \* \[]], and where [H] is of the form [p ~~> v]
    It searches for [p ~~> v'] among the [Hi]. If it finds it, it
    moves this [Hi] to the front, just before [H1]. Else, it fails. *)

Ltac xsimpl_pick_hsingle H :=
  match H with hsingle ?p ?v =>
    xsimpl_pick_st ltac:(fun H' =>
      match H' with (hsingle p ?v') =>
        constr:(true) end)
  end.

(** Internal hack:
    The following instantiation of the [xsimpl] hook enables the tactic
    to simplify [p ~~> v] against [p ~~> v'] by generating the
    side-condition [v = v']. *)

Ltac xsimpl_hook H ::=
  match H with
  | hsingle _ _ => xsimpl_pick_hsingle H; apply xsimpl_lr_cancel_eq;
                   [ xsimpl_lr_cancel_eq_repr_post tt | ]
  end.

(** At this point, the tactic [xsimpl] is available.
    See the file [SLFHimpl.v] for demos of its usage. *)

(** One last hack is to improve the [math] tactic so that it is able
    to handle the [val_int] coercion in goals and hypotheses of the
     form [val_int ?n = val_int ?m], and so that it is able to process
     the well-founded relations [dowto] and [upto] for induction on
     integers. *)

Ltac math_0 ::=
  unfolds downto, upto;
  try match goal with
  | |- val_int _ = val_int _ => fequal
  | H: val_int _ = val_int _ |- _ => inverts H
  end.

(** From now on, all operators have opaque definitions *)

Global Opaque hempty hpure hstar hsingle hexists hforall
              hwand qwand htop hgc haffine.



(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Reasoning rules *)


Ltac xmysimpl_core :=
  try match goal with |- _ = _ :> val -> hprop => intros ? end;
  repeat rewrite hstar_assoc;
  repeat first [ apply himpl_frame_r
               | apply himpl_frame_l 
               | match goal with |- ?H = ?H => apply himpl_refl end ].

Tactic Notation "xmysimpl" := xmysimpl_core.

Tactic Notation "xmysimpl" "*" := xmysimpl; auto_star.


(* ########################################################### *)
(** ** Evaluation rules for primitives in Separation style *)

(** These lemmas reformulated the big-step evaluation rule
    in a Separation-Logic friendly presentation, that is,
    by using disjoint unions as much as possible.
    It is not needed to follow through these proofs. *)

Lemma eval_ref_sep : forall s1 s2 v p,
  s2 = Fmap.single p v ->
  Fmap.disjoint s2 s1 ->
  eval s1 (val_ref v) (Fmap.union s2 s1) (val_loc p).
Proof using.
  introv -> D. forwards Dv: Fmap.indom_single p v.
  rewrite <- Fmap.update_eq_union_single. applys~ eval_ref.
  { intros N. applys~ Fmap.disjoint_inv_not_indom_both D N. }
Qed.

Lemma eval_get_sep : forall s s2 p v,
  s = Fmap.union (Fmap.single p v) s2 ->
  eval s (val_get (val_loc p)) s v.
Proof using.
  introv ->. forwards Dv: Fmap.indom_single p v.
  applys_eq eval_get 1.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.read_union_l. rewrite~ Fmap.read_single. }
Qed.

Lemma eval_set_sep : forall s1 s2 h2 p v1 v2,
  s1 = Fmap.union (Fmap.single p v1) h2 ->
  s2 = Fmap.union (Fmap.single p v2) h2 ->
  Fmap.disjoint (Fmap.single p v1) h2 ->
  eval s1 (val_set (val_loc p) v2) s2 val_unit.
Proof using.
  introv -> -> D. forwards Dv: Fmap.indom_single p v1.
  applys_eq eval_set 2.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.update_union_l. fequals.
    rewrite~ Fmap.update_single. }
Qed.

Lemma eval_free_sep : forall s1 s2 v p,
  s1 = Fmap.union (Fmap.single p v) s2 ->
  Fmap.disjoint (Fmap.single p v) s2 ->
  eval s1 (val_free p) s2 val_unit.
Proof using.
  introv -> D. forwards Dv: Fmap.indom_single p v.
  applys_eq eval_free 2.
  { applys~ Fmap.indom_union_l. }
  { rewrite~ Fmap.remove_union_single_l.
    intros Dl. applys Fmap.disjoint_inv_not_indom_both D Dl.
    applys Fmap.indom_single. }
Qed.


(* ########################################################### *)
(** ** Tactic himpl-fold *)

(** The tactic [himpl_fold] applies to a goal of the form [H1 h].
    It searches the context for an assumption of the from [H2 h],
    then replaces the goal with [H1 ==> H2].
    It also deletes the assumption [H2 h]. *)

Lemma himpl_inv : forall H1 H2 h,
  (H1 ==> H2) ->
  (H1 h) ->
  (H2 h).
Proof using. auto. Qed.

Ltac himpl_fold_core tt :=
  match goal with N: ?H ?h |- _ ?h =>
    applys himpl_inv N; clear N end.

Tactic Notation "himpl_fold" := himpl_fold_core tt.
Tactic Notation "himpl_fold" "~" := himpl_fold; auto_tilde.
Tactic Notation "himpl_fold" "*" := himpl_fold; auto_star.


(* ########################################################### *)
(** ** Hoare reasoning rules *)

(** * Definition of (total correctness) Hoare triples. *)

Definition hoare (t:trm) (H:hprop) (Q:val->hprop) :=
  forall h, H h -> exists h' v, eval h t h' v /\ Q v h'.

(** Structural rules for [hoare] triples. *)

Lemma hoare_conseq : forall t H' Q' H Q,
  hoare t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  hoare t H Q.
Proof using.
  introv M MH MQ HF. forwards (h'&v&R&K): M h. { himpl_fold~. }
  exists h' v. splits~. { himpl_fold~. }
Qed.

Lemma hoare_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, hoare t (J x) Q) ->
  hoare t (hexists J) Q.
Proof using. introv M. intros h (x&Hh). applys M Hh. Qed.

Lemma hoare_hpure : forall t (P:Prop) H Q,
  (P -> hoare t H Q) ->
  hoare t (\[P] \* H) Q.
Proof using.
  introv M. intros h (h1&h2&M1&M2&D&U). destruct M1 as (M1&HP).
  lets E: hempty_inv HP. subst. rewrite Fmap.union_empty_l. applys~ M.
Qed.

Lemma hoare_val : forall v H Q,
  H ==> Q v ->
  hoare (trm_val v) H Q.
Proof using.
  introv M. intros h K. exists h v. splits.
  { applys eval_val. }
  { himpl_fold~. }
Qed.

Lemma hoare_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  hoare (trm_fix f x t1) H Q.
Proof using.
  introv M. intros h K. exists h __. splits.
  { applys~ eval_fix. }
  { himpl_fold~. }
Qed.

Lemma hoare_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  hoare (subst x v2 (subst f v1 t1)) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof using.
  (* this lemma can be bypassed using [wp_eval_like] *)
  (* this lemma can also be proved using [hoare_eval_like] *)
  introv E M. intros s K0. forwards (s'&v&R1&K1): (rm M) K0.
  exists s' v. splits. { applys eval_app_fix E R1. } { applys K1. }
Qed.

Lemma hoare_let : forall x t1 t2 H Q Q1,
  hoare t1 H Q1 ->
  (forall v, hoare (subst x v t2) (Q1 v) Q) ->
  hoare (trm_let x t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ eval_let R2. }
Qed.

Lemma hoare_if : forall (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros h Hh. forwards* (h1'&v1&R1&K1): (rm M1).
  exists h1' v1. splits~. { applys* eval_if. }
Qed.

Lemma hoare_add : forall H n1 n2,
  hoare (val_add n1 n2)
    H
    (fun r => \[r = val_int (n1 + n2)] \* H).
Proof using.
  intros. intros s K0. exists s (val_int (n1 + n2)). split.
  { applys eval_add. }
  { rewrite~ hstar_hpure. }
Qed.

Lemma hoare_div : forall H n1 n2,
  n2 <> 0 ->
  hoare (val_div n1 n2)
    H
    (fun r => \[r = val_int (Z.quot n1 n2)] \* H).
Proof using.
  introv N. intros s K0. exists s (val_int (Z.quot n1 n2)). split.
  { applys eval_div N. }
  { rewrite~ hstar_hpure. }
Qed.

Lemma hoare_ref : forall H v,
  hoare (val_ref v)
    H
    (fun r => (\exists p, \[r = val_loc p] \* p ~~> v) \* H).
Proof using.
  intros. intros s1 K0.
  forwards~ (p&D&N): (Fmap.single_fresh 0%nat s1 v).
  exists (Fmap.union (Fmap.single p v) s1) (val_loc p). split.
  { applys~ eval_ref_sep D. }
  { applys~ hstar_intro.
    { exists p. rewrite~ hstar_hpure. split~. { applys~ hsingle_intro. } } }
Qed.

Lemma hoare_get : forall H v p,
  hoare (val_get p)
    ((p ~~> v) \* H)
    (fun r => \[r = v] \* (p ~~> v) \* H).
Proof using.
  intros. intros s K0. exists s v. split.
  { destruct K0 as (s1&s2&P1&P2&D&U).
    lets (E1&N): hsingle_inv P1. subst s1.
    applys eval_get_sep U. }
  { rewrite~ hstar_hpure. }
Qed.

Lemma hoare_set : forall H w p v,
  hoare (val_set (val_loc p) w)
    ((p ~~> v) \* H)
    (fun r => (p ~~> w) \* H).
Proof using.
  intros. intros s1 K0.
  destruct K0 as (h1&h2&P1&P2&D&U).
  lets (E1&N): hsingle_inv P1.
  exists (Fmap.union (Fmap.single p w) h2) val_unit. split.
  { subst h1. applys eval_set_sep U D. auto. }
  { applys~ hstar_intro.
    { applys~ hsingle_intro. }
    { subst h1. applys Fmap.disjoint_single_set D. } }
Qed.

Lemma hoare_free : forall H p v,
  hoare (val_free (val_loc p))
    ((p ~~> v) \* H)
    (fun r => H).
Proof using.
  intros. intros s1 K0.
  destruct K0 as (h1&h2&P1&P2&D&U).
  lets (E1&N): hsingle_inv P1.
  exists h2 val_unit. split.
  { subst h1. applys eval_free_sep U D. }
  { auto. }
Qed.


(* ########################################################### *)
(** ** Definition of SL triple, and proof of equivalence with [wp]. *)

(** Remark: we deliberately choose to state program specifications
    using [triple] and not [wp], because we find the former concept
    to be more elementary. However, one could very well define
    [triple t H Q] simply as a shorthand for [H ==> wp t Q], rather
    than definining it in terms of Hoare triples as we do here. *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), hoare t (H \* H') (Q \*+ H').


(* ########################################################### *)
(** ** Notation for postconditions of functions that return a pointer. *)

(** [funloc p => H] is short for
    [fun (r:val) => \exists (p:loc), \[r = val_loc p] \* H)]. *)

Notation "'funloc' p '=>' H" :=
  (fun r => \exists p, \[r = val_loc p] \* H)
  (at level 200, p ident, format "'funloc'  p  '=>'  H") : hprop_scope.


(* ########################################################### *)
(** ** Structural rules *)

Lemma triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
  introv M MH MQ. intros HF. applys hoare_conseq M.
  { xchanges MH. }
  { intros x. xchanges (MQ x). }
Qed.

Hint Rewrite hstar_assoc hstar_hempty_l hstar_hempty_r : hstar.

Ltac xmysimpl_core ::=
  try match goal with |- _ ===> _ => intros ? end;
  autorewrite with hstar;
  repeat first [ apply himpl_frame_r
               | apply himpl_frame_l 
               | rewrite hstar_comm; apply himpl_frame_r
               | rewrite hstar_comm; apply himpl_frame_l
               | match goal with |- ?H ==> ?H => apply himpl_refl end
               | match goal with |- ?H ==> ?H' => is_evar H'; apply himpl_refl end ].


Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using.
  introv M. intros HF.
  applys hoare_conseq (M (HF \* H')); xmysimpl.
Qed.

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using.
  introv M. intros HF. rewrite hstar_hexists.
  applys hoare_hexists. intros. applys* M.
Qed.

Lemma triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. intros HF. rewrite hstar_assoc.
  applys hoare_hpure. intros. applys* M.
Qed. (* Note: can also be proved from [triple_hexists] *)

Lemma triple_ramified_frame : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  triple t H Q.
Proof using.
  introv M W. applys triple_conseq. 
  applys triple_frame (Q1 \--* Q) M.
  { applys W. }
  { rewrite~ <- qwand_equiv. }
Qed.


(* ########################################################### *)
(** ** Rules for terms *)

Lemma triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using.
  introv M. intros HF. applys hoare_val. { xchanges M. }
Qed.

Lemma triple_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triple (trm_fix f x t1) H Q.
Proof using.
  introv M. intros HF. applys~ hoare_fix. { xchanges M. }
Qed.

Lemma triple_let : forall x t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall (X:val), triple (subst x X t2) (Q1 X) Q) ->
  triple (trm_let x t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF. applys hoare_let.
  { applys M1. }
  { intros v. applys hoare_conseq M2; xmysimpl. }
Qed.

Lemma triple_if : forall (b:bool) t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros HF. applys hoare_if. applys M1.
Qed.

Lemma triple_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  triple (subst x v2 (subst f v1 t1)) H Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
  introv E M1. intros H'. applys hoare_app_fix E. applys M1.
Qed.


(* ########################################################### *)
(** ** Rules for primitives *)

Lemma triple_add : forall n1 n2,
  triple (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).
Proof using.
  intros. intros H'. applys hoare_conseq hoare_add; xmysimpl*.
Qed.

Lemma triple_div : forall n1 n2,
  n2 <> 0 ->
  triple (val_div n1 n2)
    \[]
    (fun r => \[r = val_int (Z.quot n1 n2)]).
Proof using.
  intros. intros H'. applys* hoare_conseq hoare_div; xmysimpl*.
Qed.

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (funloc p => p ~~> v).
Proof using.
  intros. intros HF. applys hoare_conseq hoare_ref; xmysimpl*.
Qed.

Lemma triple_get : forall v p,
  triple (val_get (val_loc p))
    (p ~~> v)
    (fun x => \[x = v] \* (p ~~> v)).
Proof using.
  intros. intros HF. applys hoare_conseq hoare_get; xmysimpl*.
Qed.

Lemma triple_set : forall w p v,
  triple (val_set (val_loc p) w)
    (p ~~> v)
    (fun _ => p ~~> w).
Proof using.
  intros. intros HF. applys hoare_conseq hoare_set; xmysimpl*.
Qed.

Lemma triple_free : forall p v,
  triple (val_free (val_loc p))
    (p ~~> v)
    (fun _ => \[]).
Proof using.
  intros. intros HF. applys hoare_conseq hoare_free; xmysimpl*.
Qed.

