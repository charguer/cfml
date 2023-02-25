Set Implicit Arguments.
From CFML Require Import WPLib.
From CFML Require Import Stdlib.
From EXAMPLES Require Import PairingHeap_ml MList_proof.
From TLC Require Import LibListZ LibMultiset.
Import SpecMListOf.
Open Scope comp_scope.





Lemma haffine_any : forall H,
  haffine H.
Hint Resolve haffine_any.

(* TODO: move
Proof using.
Transparent heap heap_affine.
 intros. rewrite haffine_eq. unfolds* heap_affine. Qed.


 *)


(* Copy-paste of earlier definitions to work around a notation bug in Coq *)

Notation "<[ e ]>" :=
 e
 (at level 0, e custom wp at level 99) : wp_scope.

Notation "'Let' x ':=' F1 'in' F2" :=
 ((*Wptag*) (Wpgen_let_trm F1 (fun x => F2)))
 (in custom wp at level 69,
  x ident,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  right associativity,
 format "'[v' '[' 'Let'  x  ':='  F1  'in' ']' '/' '[' F2 ']' ']'") : wp_scope.

Notation "'Seq' F1 ; F2" :=
 ((*Wptag*) (Wpgen_seq F1 F2))
 (in custom wp at level 68,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  right associativity,
  format "'[v' 'Seq'  '[' F1 ']'  ; '/' '[' F2 ']' ']'") : wp_scope.




(**

Formalization of pairing heaps, covering both
- purely functional pairing heaps (in Coq code)
- ephemeral (pointer-based) pairing heaps in CFML2

More information about pairing heaps:
  https://www.cise.ufl.edu/~sahni/dsaaj/enrich/c13/pairing.htm

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Representation and lemmas *)

(* ********************************************************************** *)
(** ** Types of elements *)

(** For simplicity, assume the priority queue to store integer values.
    It is not hard to generalize everything to any ordered type. *)

Notation "'elem'" := (int).
Notation "'elems'" := (multiset elem).


(* ******************************************************* *)
(** ** Data structure and definitions *)

(** Functional representation of a node in a (nonempty) pairing heap *)

Inductive node : Type :=
  | Node : elem -> list node -> node.

Instance Inhab_node : Inhab node.
Proof using. applys Inhab_of_val (Node arbitrary nil). Qed.

(** Functional representation of a possibly-empty pairing heap *)

Definition heap := option node.

Instance Inhab_heap : Inhab heap.
Proof using. applys Inhab_of_val (@None node). Qed.

(** Auxiliary definition for specifications *)

Definition min_of (E:elems) (x:elem) : Prop :=
  x \in E /\ forall_ y \in E, x <= y.

(** Auxiliary definition for stating invariants follow. *)

(** [is_ge x] is a predicate that characterizes items no less than [x] *)

Definition is_ge (x y:elem) : Prop :=
  x <= y.

(** [list_union Es] computes the iterated union of the multisets in the list [Es] *)

Definition list_union (Es:list elems) : elems :=
  LibList.fold_right union \{} Es.

(** [inv n E] relates a tree node [n] with the multiset [E] made of
    the items that the tree contains *)

Inductive inv : node -> elems -> Prop :=
  | inv_Node : forall x ns Es E,
      Forall2 inv ns Es ->
      Forall (foreach (is_ge x)) Es ->
      E = \{x} \u (list_union Es) ->
      inv (Node x ns) E.


(* ******************************************************* *)
(** ** Lemmas and tactics *)

(** Implicit Types *)

Implicit Types n : node.
Implicit Types p q l : loc.
Implicit Types x y : elem.
Implicit Types h : heap.
Implicit Types hs : list node.
Implicit Types E : elems.
Implicit Types Es : list elems.

(** Normalization lemmas for [list_union] *)

Lemma list_union_nil :
  list_union (@nil elems) = \{}.
Proof using. auto. Qed.

Lemma list_union_cons : forall E Es,
  list_union (E::Es) = E \u list_union Es.
Proof using. auto. Qed.

(** Hints *)

Hint Rewrite list_union_nil list_union_cons : rew_listx.
Hint Rewrite (@union_empty_r elems _ _ _) (@union_empty_l elems _ _ _) : rew_listx.
Hint Extern 1 (_ < _) => simpl; math.
Hint Extern 1 (_ <= _) => simpl; math.
Hint Extern 1 (_ = _ :> multiset _) => rew_listx; multiset_eq.
Hint Extern 1 (_ \in _) => multiset_in.
Hint Constructors Forall Forall2 list_sub.
Hint Unfold is_ge.

(** Lemmas to manipulate the invariant [Forall (foreach (is_ge x)) Es] *)

Lemma Forall_foreach_is_ge_inv : forall x y Es,
  Forall (foreach (is_ge x)) Es ->
  y \in list_union Es ->
  x <= y.
Proof using.
  introv M Hy. unfolds list_union. induction M; rew_listx in *.
  { multiset_in Hy. }
  { multiset_in Hy. { applys* H. } { applys* IHM. } }
Qed.

Lemma foreach_list_union : forall P Es,
  Forall (foreach P) Es ->
  foreach P (list_union Es).
Proof using.
  introv M. induction M.
  { applys foreach_empty. }
  { unfold list_union; rew_listx. applys* foreach_union. }
Qed.

(** Key auxiliary lemmas for the verification proofs
    (both for the functional version and the imperative version) *)

Lemma inv_not_empty : forall n E,
  inv n E ->
  E <> \{}.
Proof using. introv I. inverts I. multiset_inv. Qed.

Lemma merge_lemma : forall x1 x2 ns1 ns2 Es1 Es2,
  Forall2 inv ns1 Es1 ->
  Forall2 inv ns2 Es2 ->
  Forall (foreach (is_ge x2)) Es1 ->
  Forall (foreach (is_ge x1)) Es2 ->
  x1 <= x2 ->
  inv (Node x1 (Node x2 ns1 :: ns2)) ('{x1} \u '{x2} \u list_union Es1 \u list_union Es2).
Proof using.
  introv Is1 Is2 Ks1 Ks2 L. applys_eq inv_Node. constructor.
  { applys* inv_Node. }
  { eauto. }
  { constructors.
    { applys foreach_union.
      { applys* foreach_single. }
      { applys* foreach_list_union. applys Forall_pred_incl Ks1.
        { intros x Hx. applys* foreach_weaken. { intros y Hy. unfolds* is_ge. } } } }
    { eauto. } }
  { autos*. }
Qed.

Lemma pop_min_lemma : forall x Es,
  Forall (foreach (is_ge x)) Es ->
  min_of (\{x} \u list_union Es) x.
Proof.
  introv M. split.
  { auto. }
  { intros y Hy. multiset_in Hy.
    { auto. } { applys* Forall_foreach_is_ge_inv Es. } }
Qed.



(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Imperative pairing heaps *)

(* ******************************************************* *)
(** ** Representation predicates *)

(** [q ~> Tree n] is a notation for [Tree n q]. It relates a pointer [q] with the
    functional tree structure [n] that it represents in memory *)


Fixpoint Tree (n:node) (q:loc) { struct n } : hprop :=
  match n with
  | Node x hs =>
      \exists (q':loc),
         q  ~~~>`{ value' := x; sub' := q' }
      \* q' ~> MListOf Tree hs
  end.

(** [q ~> Repr E] related a pointer [q] with the multiset of items [E]
    that are stored in the tree *)

Definition Repr (E:elems) (q:loc) : hprop :=
  \exists n, q ~> Tree n \* \[inv n E].

(** [q ~> Heap E] relates a pointer on a heap [p] with the multiset of items [E]
    that are stored in the heap. It uses [Contents E c] as an auxiliary definition. *)

Definition Contents (E:elems) (c:contents_) : hprop :=
  match c with
  | Empty => \[E = \{}]
  | Nonempty p => (p ~> Repr E)
  end.

Definition Heap (E:elems) (p:heap_) : hprop :=
  \exists c, p ~~> c \* Contents E c.


(* ******************************************************* *)
(** ** Paraphrase definitions as equalities *)

Lemma Tree_Node : forall q x hs,
  q ~> Tree (Node x hs) =
      \exists l, q ~~~> `{ value' := x; sub' := l }
              \* l ~> MListOf Tree hs.
Proof using. auto. Qed.

Lemma Contents_eq : forall E c,
  Contents E c = (match c with
  | Empty => \[E = \{}]
  | Nonempty p => (p ~> Repr E)
  end).
Proof using. auto. Qed.

Lemma Heap_eq : forall p E,
  p ~> Heap E = \exists c, p ~~> c \* Contents E c.
Proof using. auto. Qed.

Lemma Repr_eq : forall q E,
  q ~> Repr E = \exists n, q ~> Tree n \* \[inv n E].
Proof using. auto. Qed.


(* ******************************************************* *)
(** ** Lemmas about representation predicates *)

Lemma Repr_not_empty : forall q E,
  q ~> Repr E ==> \[E <> \{}] \* q ~> Repr E.
Proof using.
  intros. xunfold Repr. xpull ;=> n I. lets: inv_not_empty I. xsimpl*.
Qed.

Lemma Contents_is_empty : forall c E,
  Contents E c ==> \[c = Empty <-> E = \{}] \* Contents E c.
Proof using.
  intros.  unfold Contents. destruct c.
  { xsimpl*. }
  { xchange Repr_not_empty ;=> N. xsimpl. iff H; false. }
Qed.

Lemma Heap_Nonempty : forall p q E,
  p ~~> Nonempty q \* q ~> Repr E ==> p ~> Heap E.
Proof using.
  intros. xchanges Repr_not_empty ;=> N. xunfold Heap. xsimpl.
Qed.

Lemma Heap_Empty : forall p,
  p ~~> Empty ==> p ~> Heap \{}.
Proof using. intros. xunfold Heap. unfold Contents. xsimpl*. Qed.


(* ******************************************************* *)
(** ** Verification *)

Lemma Triple_create :
  SPEC (create tt)
    PRE \[]
    POST (fun p => p ~> Heap \{}).
Proof using.
  xcf. xapp. xunfold Heap. unfold Contents. xsimpl*. 
Qed.

Hint Extern 1 (RegisterSpec create) => Provide Triple_create.

Lemma Triple_is_empty : forall p E,
  SPEC (is_empty p)
    PRE (p ~> Heap E)
    POST (fun b => \[b = isTrue (E = \{})] \* p ~> Heap E).
Proof using.
  xcf. xunfolds Heap ;=> q. xapp. xapp.
  xchanges~ Contents_is_empty.
Qed.

Hint Extern 1 (RegisterSpec (is_empty)) => Provide Triple_is_empty.

Lemma Triple_merge : forall q1 q2 E1 E2,
  SPEC (merge q1 q2)
    PRE (q1 ~> Repr E1 \* q2 ~> Repr E2)
    POST (fun q => q ~> Repr (E1 \u E2)).
Proof using.
  xcf. xchange (Repr_eq q1) ;=> [x1 hs1] I1.
  xchange (Repr_eq q2) ;=> [x2 hs2] I2.
  xchange (Tree_Node q1) ;=> l1.
  xchange (Tree_Node q2) ;=> l2.
  inverts I1 as Is1 Ks1. inverts I2 as Is2 Ks2.
  xif ;=> C.
  { xapp. xchange <- (Tree_Node q2). xapp. 
    xchange <- Tree_Node. xchange <- Repr_eq.
    applys* merge_lemma. xvals*. }
  { xapp. xchange <- (Tree_Node q1). xapp.
    xchange <- Tree_Node. xchange <- Repr_eq.
    applys* merge_lemma. xvals*. }
Qed.

Hint Extern 1 (RegisterSpec merge) => Provide Triple_merge.

Lemma Triple_insert : forall p x E,
  SPEC (insert p x)
    PRE (p ~> Heap E)
    POST (fun (_:unit) => p ~> Heap (E \u \{x})).
Proof using.
  xcf. xchange Heap_eq ;=> q. xapp ;=> l. xapp ;=> q2.
  xchange <- Tree_Node. xchange <- Repr_eq. { applys* inv_Node. }
  rew_listx. xapp. xmatch; simpl.
  { xpull ;=> ->. xapp. xchanges* Heap_Nonempty. }
  { xapp ;=> r. xapp. xchanges* Heap_Nonempty. }
Qed.

Hint Extern 1 (RegisterSpec insert) => Provide Triple_insert.

Lemma Triple_merge_pairs : forall ns l Es,
  ns <> nil ->
  Forall2 inv ns Es ->
  SPEC (merge_pairs l)
    PRE (l ~> MListOf Tree ns)
    POST (fun q => q ~> Repr (list_union Es)).
Proof using.
  intros ns. induction_wf IH: list_sub ns; introv N Is.
  xcf. xapp~ ;=> q1 n1 ns' ->. inverts Is as I1 Is. rename r into Es'.
  xif ;=> C.
  { subst. inverts Is. rew_listx. xval. xchanges* <- Repr_eq. }
  { xapp~ ;=> q2 n2 ns'' ->. inverts Is as I2 Is. rename r into Es''.
    do 2 xchange* <- Repr_eq. xapp ;=> r. xif ;=> C'.
    { subst. inverts Is. rew_listx. xval. xsimpl. }
    { xapp* ;=> r'. xapp ;=> r''. rew_listx. xsimpl*. } }
Qed.

Hint Extern 1 (RegisterSpec merge_pairs) => Provide Triple_merge_pairs.

Lemma Triple_pop_min : forall p E,
  E <> \{} ->
  SPEC (pop_min p)
    PRE (p ~> Heap E)
    POST (fun x => \exists E', \[min_of E x /\ E = \{x} \u E'] \* p ~> Heap E').
Proof using.
  introv HE. xcf. xchange Heap_eq ;=> c. xapp. 
  destruct c as [|q]; simpl; xpull. 
  xchange Repr_eq ;=> [x hs] I. invert I ;=> ? ? ? ? Is Ks Eq -> -> ->.
  xchange Tree_Node ;=> l. xmatch. xapp. xapp. xapp.
  xseq (fun (_:unit) => \exists E', \[E = '{x} \u E'] \* p ~> Heap E' \* \GC).
  { xif ;=> C2. 
    { subst. inverts Is. inverts Ks. rew_listx. xapp. xchanges* Heap_Empty. }
    { xapp. xapp* ;=> r. xapp. xchange Heap_Nonempty. xsimpl*. } }
  { xpull ;=> E' ->. xval. xsimpl. split~. { rewrite Eq. applys~ pop_min_lemma. } }
Qed.

Hint Extern 1 (RegisterSpec pop_min) => Provide Triple_pop_min.

