(** * SLFCore *)

(** This file provides a construction similar to [SLFDirect], except
    that it considers a smaller language (no recursion, no sequence),
    augmented with a non-deterministic random number generator.

    This file includes both a big-step semantics and a small-step
    semantics, together with a proof of equivalence between the two. *)


Set Implicit Arguments.
From SLF (* TLC *) Require Export LibCore.
From SLF (* Sep *) Require Export TLCbuffer Var Fmap.
From SLF (* Sep *) Require SepSimpl.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Core language *)

(* ########################################################### *)
(** ** Values and Terms *)

(** See [SLFDirect] for explanations.

    The main addition is the new primitive operator [val_rand], which is
    used to introduce a real source of non-determinism in the semantics.
    It is explained in chapter [SLFNondet].

    Another minor addition is the special value [val_error], which is used
    in bonus chapter [SLFComplete] only. *)

Definition loc : Type := nat.

Definition null : loc := 0%nat.

Inductive val : Type :=
  | val_error : val
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_fun : var -> trm -> val
  | val_fix : var -> var -> trm -> val
  | val_ref : val
  | val_get : val
  | val_set : val
  | val_free : val
  | val_add : val
  | val_rand : val

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm.

Coercion val_loc : loc >-> val.
Coercion val_bool : bool >-> val.
Coercion val_int : Z >-> val.
Coercion trm_val : val >-> trm.
Coercion trm_app : trm >-> Funclass.

Definition state : Type := fmap loc val.
Definition heap : Type := state.

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

Instance Inhab_val : Inhab val.
Proof using. apply (Inhab_of_val val_unit). Qed.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types p : loc.
Implicit Types n : int.
Implicit Types v w r vf vx : val.
Implicit Types t : trm.
Implicit Types h : heap.
Implicit Types s : state.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Heap Predicates *)

(** For technical reasons, to enable sharing the code implementing
    the tactic [xsimpl], we wrap the definitions inside a module. *)

Module SepSimplArgs.


(* ########################################################### *)
(** ** Hprop and Entailment *)

Declare Scope hprop_scope.
Open Scope hprop_scope.

(** The type of heap predicates is named [hprop]. *)

Definition hprop := heap -> Prop.

(** Entailment for heap predicates, written [H1 ==> H2]
    (the entailment is linear, although our triples will be affine). *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall h, H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55) : hprop_scope.

(** Entailment between postconditions, written [Q1 ===> Q2] *)

Definition qimpl A (Q1 Q2:A->hprop) : Prop :=
  forall (v:A), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55) : hprop_scope.

(** Implicit types for meta-variables. *)

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ########################################################### *)
(** ** Definition of Heap Predicates *)

(** Core heap predicates, and their associated notations:

    - [\[]] denotes the empty heap predicate
    - [\[P]] denotes a pure fact
    - [\Top] denotes the true heap predicate (affine)
    - [p ~~> v] denotes a singleton heap
    - [H1 \* H2] denotes the separating conjunction
    - [Q1 \*+ H2] denotes the separating conjunction extending a postcondition
    - [\exists x, H] denotes an existential
    - [\forall x, H] denotes a universal
    - [H1 \-* H2] denotes a magic wand between heap predicates
    - [Q1 \--* Q2] denotes a magic wand between postconditions

*)

Notation "'heap_empty'" := (@Fmap.empty loc val)
  (at level 0).
Notation "h1 \u h2" := (Fmap.union h1 h2)
  (at level 37, right associativity).


Definition hempty : hprop :=
  fun h => (h = heap_empty).

Definition hsingle (p:loc) (v:val) : hprop :=
  fun h => (h = Fmap.single p v).

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

Definition htop : hprop :=
  \exists (H:hprop), H.

Definition hwand (H1 H2 : hprop) : hprop :=
  \exists H0, H0 \* hpure ((H1 \* H0) ==> H2).

Definition qwand A (Q1 Q2:A->hprop) : hprop :=
  \forall x, hwand (Q1 x) (Q2 x).

Notation "\[ P ]" := (hpure P)
  (at level 0, format "\[ P ]") : hprop_scope.

Notation "\Top" := (htop) : hprop_scope.

Notation "Q \*+ H" := (fun x => hstar (Q x) H)
  (at level 40) : hprop_scope.

Notation "H1 \-* H2" := (hwand H1 H2)
  (at level 43, right associativity) : hprop_scope.

Notation "Q1 \--* Q2" := (qwand Q1 Q2)
  (at level 43) : hprop_scope.



(* ########################################################### *)
(** ** Basic Properties of Separation Logic Operators *)

(* ################################################ *)
(** *** Tactic for Automation *)

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

Lemma hstar_hpure_l : forall P H h,
  (\[P] \* H) h = (P /\ H h).
Proof using.
  intros. apply prop_ext. unfold hpure.
  rewrite hstar_hexists. rewrite* hstar_hempty_l.
  iff (p&M) (p&M). { split~. } { exists~ p. }
Qed.

Lemma hstar_hpure_r : forall P H h,
  (H \* \[P]) h = (H h /\ P).
Proof using.
  intros. rewrite hstar_comm. rewrite hstar_hpure_l. apply* prop_ext.
Qed.

Lemma himpl_hstar_hpure_r : forall P H H',
  P ->
  (H ==> H') ->
  H ==> (\[P] \* H').
Proof using. introv HP W. intros h K. rewrite* hstar_hpure_l. Qed.

Lemma hpure_inv_hempty : forall P h,
  \[P] h ->
  P /\ \[] h.
Proof using.
  introv M. rewrite <- hstar_hpure_l. rewrite~ hstar_hempty_r.
Qed.

Lemma hpure_intro_hempty : forall P h,
  \[] h ->
  P ->
  \[P] h.
Proof using.
  introv M N. rewrite <- (hstar_hempty_l \[P]). rewrite~ hstar_hpure_r.
Qed.

Lemma himpl_hempty_hpure : forall P,
  P ->
  \[] ==> \[P].
Proof using. introv HP. intros h Hh. applys* hpure_intro_hempty. Qed.

Lemma himpl_hstar_hpure_l : forall P H H',
  (P -> H ==> H') ->
  (\[P] \* H) ==> H'.
Proof using.
  introv W Hh. rewrite hstar_hpure_l in Hh. applys* W.
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
  intros. applys himpl_antisym; intros h; rewrite hstar_hpure_l; intros M.
  { false*. } { lets: hpure_inv_hempty M. false*. }
Qed.


(* ################################################ *)
(** *** Properties of [hexists] *)

Lemma hexists_intro : forall A (x:A) (J:A->hprop) h,
  J x h ->
  (hexists J) h.
Proof using. intros. exists~ x. Qed.

Lemma hexists_inv : forall A (J:A->hprop) h,
  (hexists J) h ->
  exists x, J x h.
Proof using. intros. destruct H as [x H]. exists~ x. Qed.

Lemma himpl_hexists_l : forall A H (J:A->hprop),
  (forall x, J x ==> H) ->
  (hexists J) ==> H.
Proof using. introv W. intros h (x&Hh). applys* W. Qed.

Lemma himpl_hexists_r : forall A (x:A) H J,
  (H ==> J x) ->
  H ==> (hexists J).
Proof using. introv W. intros h. exists x. apply~ W. Qed.

(* not needed *)
Lemma himpl_hexists : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hexists J1 ==> hexists J2.
Proof using.
  introv W. applys himpl_hexists_l. intros x. applys himpl_hexists_r W.
Qed.


(* ################################################ *)
(** *** Properties of [hforall] *)

Lemma hforall_intro : forall A (J:A->hprop) h,
  (forall x, J x h) ->
  (hforall J) h.
Proof using. introv M. applys* M. Qed.

Lemma hforall_inv : forall A (J:A->hprop) h,
  (hforall J) h ->
  forall x, J x h.
Proof using. introv M. applys* M. Qed.

Lemma himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (hforall J).
Proof using. introv M. intros h Hh x. apply~ M. Qed.

Lemma himpl_hforall_l : forall A x (J:A->hprop) H,
  (J x ==> H) ->
  (hforall J) ==> H.
Proof using. introv M. intros h Hh. apply~ M. Qed.

Lemma hforall_specialize : forall A (x:A) (J:A->hprop),
  (hforall J) ==> (J x).
Proof using. intros. applys* himpl_hforall_l x. Qed.

(* not needed *)
Lemma himpl_hforall : forall A (J1 J2:A->hprop),
  J1 ===> J2 ->
  hforall J1 ==> hforall J2.
Proof using.
  introv W. applys himpl_hforall_r. intros x. applys himpl_hforall_l W.
Qed.


(* ################################################ *)
(** *** Properties of [hwand] *)

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
  { rewrite <- hstar_hempty_l at 1. applys hwand_cancel. }
  { rewrite hwand_equiv. rewrite~ hstar_hempty_l. }
Qed.

Lemma hwand_hpure_l : forall P H,
  P ->
  (\[P] \-* H) = H.
Proof using.
  introv HP. applys himpl_antisym.
  { lets K: hwand_cancel \[P] H. applys himpl_trans K.
    applys* himpl_hstar_hpure_r. }
  { rewrite hwand_equiv. applys* himpl_hstar_hpure_l. }
Qed.

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

Lemma hwand_inv : forall h1 h2 H1 H2,
  (H1 \-* H2) h2 ->
  H1 h1 ->
  Fmap.disjoint h1 h2 ->
  H2 (h1 \u h2).
Proof using.
  introv M2 M1 D. unfolds hwand. lets (H0&M3): hexists_inv M2.
  lets (h0&h3&P1&P3&D'&U): hstar_inv M3. lets (P4&E3): hpure_inv P3.
  subst h2 h3. rewrite union_empty_r in *. applys P4. applys* hstar_intro.
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
  { applys himpl_hforall_r. intros x. rewrite* hwand_equiv. }
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
(** *** Properties of [htop] *)

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


(* ################################################ *)
(** *** Properties of [hsingle] *)

Lemma hsingle_intro : forall p v,
  (p ~~> v) (Fmap.single p v).
Proof using. intros. hnfs*. Qed.

Lemma hsingle_inv: forall p v h,
  (p ~~> v) h ->
  h = Fmap.single p v.
Proof using. auto. Qed.

Lemma hstar_hsingle_same_loc : forall p w1 w2,
  (p ~~> w1) \* (p ~~> w2) ==> \[False].
Proof using.
  intros. unfold hsingle. intros h (h1&h2&E1&E2&D&E). false.
  subst. applys* Fmap.disjoint_single_single_same_inv.
Qed.

Arguments hstar_hsingle_same_loc : clear implicits.


(* ################################################ *)
(** *** The [xsimpl] tactic *)

(** The definitions and properties above enable us to instantiate
    the [xsimpl] tactic, which implements powerful simplifications
    for Separation Logic entailments.

    For technical reasons, we need to provide a definition for [hgc],
    a restriction of [htop] to affine heap predicates. For our purpose,
    it suffices to define [hgc] as an alias for [htop]. *)


(* ################################################ *)
(** *** Definition and Properties of [haffine] and [hgc] *)

Definition haffine (H:hprop) :=
  True.

Lemma haffine_hany : forall (H:hprop),
  haffine H.
Proof using. unfold haffine. auto. Qed.

Lemma haffine_hempty :
  haffine \[].
Proof using. applys haffine_hany. Qed.

Definition hgc := (* equivalent to [\exists H, \[haffine H] \* H] *)
  htop.

Notation "\GC" := (hgc) : hprop_scope.

Lemma haffine_hgc :
  haffine \GC.
Proof using. applys haffine_hany. Qed.

Lemma himpl_hgc_r : forall H,
  haffine H ->
  H ==> \GC.
Proof using. introv M. applys himpl_htop_r. Qed.

Lemma hstar_hgc_hgc :
  \GC \* \GC = \GC.
Proof using. applys hstar_htop_htop. Qed.


(* ################################################ *)
(** *** Functor Instantiation to Obtain [xsimpl] *)

End SepSimplArgs.

(** See [SLFDirect] for explanations. *)

Module Export HS := SepSimpl.XsimplSetup(SepSimplArgs).

Export SepSimplArgs.

Global Opaque hempty hpure hstar hsingle hexists hforall
              hwand qwand htop hgc haffine.

