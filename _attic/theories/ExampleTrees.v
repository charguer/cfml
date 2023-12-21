(**

This file formalizes mutable trees examples in lifted Separation Logic,
using lifted characteristic formulae.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Import Example.
From TLC Require Import LibSet.
Generalizable Variables A B.

Implicit Types x : int.
Implicit Types p : loc.
Implicit Types E : (LibSet.set int).


(**--TODO: move*)

Instance Le_total_order_Z : Le_total_order (A:=Z).
Proof using.
  constructor. constructor. constructor; unfolds.
  math. math. math. unfolds.
  intros. tests: (x <= y). left~. right. math.
Qed.


(* ********************************************************************** *)
(* * Formalization of binary trees *)

(** To avoid noise, we specialize the type of items to [int] *)


(* ---------------------------------------------------------------------- *)
(* ** Fields *)

Definition item : field := 0%nat.
Definition left : field := 1%nat.
Definition right : field := 2%nat.

Notation "'val_get_item'" := (val_get_field item).
Notation "'val_get_left'" := (val_get_field left).
Notation "'val_get_right'" := (val_get_field right).

Notation "'val_set_item'" := (val_set_field item).
Notation "'val_set_left'" := (val_set_field left).
Notation "'val_set_right'" := (val_set_field right).


(* ---------------------------------------------------------------------- *)
(* ** Logical trees *)

Inductive tree : Type :=
  | Leaf : tree
  | Node : int -> tree -> tree -> tree.

Implicit Types T : tree.

(** Inhabited type *)

Instance tree_Inhab : Inhab tree.
Proof using. apply (Inhab_of_val Leaf). Qed.

(** Well-founded order on trees *)

Inductive tree_sub : binary (tree) :=
  | tree_sub_1 : forall x T1 T2,
      tree_sub T1 (Node x T1 T2)
  | tree_sub_2 : forall x T1 T2,
      tree_sub T2 (Node x T1 T2).

Lemma tree_sub_wf : wf tree_sub.
Proof using.
  intros T. induction T; constructor; intros t' H; inversions~ H.
Qed.

Hint Resolve tree_sub_wf : wf.


(* ---------------------------------------------------------------------- *)
(* ** Representation predicate *)

Notation "'Cell' x p1 p2" :=
  (Record`{ item := x; left := p1; right := p2 })
  (at level 69, x at level 0, p1 at level 0, p2 at level 0).

Fixpoint MTree (T:tree) (p:loc) : hprop :=
  match T with
  | Leaf => \[p = null]
  | Node x T1 T2 => \exists p1 p2,
         (p ~> Cell x p1 p2)  (* p ~> Record`{ item := x; left := p1; right := p2 }) *)
      \* (p1 ~> MTree T1)
      \* (p2 ~> MTree T2)
  end.


(* ---------------------------------------------------------------------- *)
(* ** Lemmas *)

(** Lemmas for leaves *)

Lemma MTree_leaf_eq : forall p,
  (p ~> MTree Leaf) = \[p = null].
Proof using. intros. xunfold~ MTree. Qed.

Lemma MTree_leaf :
  \[] ==> (null ~> MTree Leaf).
Proof using. intros. rewrite MTree_leaf_eq. xsimpl~. Qed.

Lemma MTree_null_eq : forall T,
  (null ~> MTree T) = \[T = Leaf].
Proof using.
  intros. destruct T.
  { xunfold MTree. applys himpl_antisym; xsimpl~. }
  { xunfold MTree. applys himpl_antisym.
    { xpull ;=> p'. xchange (hRecord_not_null null).
      { simpl. unfold item. auto. }
      { xpull; auto_false. } }
    { xpull. } }
Qed. (* todo: factorize with proof for lists *)

Lemma MTree_null_inv : forall T,
  (null ~> MTree T) ==+> \[T = Leaf].
Proof using.
  intros. destruct T.
  { xsimpl~. }
  { rewrite MTree_null_eq. xsimpl. }
Qed.

(** Lemmas for nodes *)

Lemma MTree_node_eq : forall p x T1 T2,
  (p ~> MTree (Node x T1 T2)) =
  \exists p1 p2,
  (p ~> Cell x p1 p2) \* (p1 ~> MTree T1) \* (p2 ~> MTree T2).
Proof using. intros. xunfold MTree at 1. simple~. Qed.

Lemma MTree_node : forall p p1 p2 x T1 T2,
  (p ~> Cell x p1 p2) \* (p1 ~> MTree T1) \* (p2 ~> MTree T2) ==>
  (p ~> MTree (Node x T1 T2)).
Proof using. intros. rewrite MTree_node_eq. xsimpl. Qed.

Lemma MTree_not_null_inv_not_leaf : forall p T,
  p <> null ->
  p ~> MTree T ==+> \[T <> Leaf].
Proof using.
  intros. destruct T.
  { xchanges -> (MTree_leaf_eq p). }
  { xsimpl. auto_false. }
Qed.

Lemma MTree_not_null_inv_node : forall p T,
  p <> null ->
  (p ~> MTree T) ==>
  \exists x p1 p2 T1 T2, \[T = Node x T1 T2] \*
    (p ~> Cell x p1 p2) \* (p1 ~> MTree T1) \* (p2 ~> MTree T2).
Proof using.
  intros. xchange~ (@MTree_not_null_inv_not_leaf p). xpull. intros.
  destruct T; tryfalse.
  xchange (MTree_node_eq p). xsimpl~.
Qed.

Arguments MTree_not_null_inv_not_leaf : clear implicits.
Arguments MTree_not_null_inv_node : clear implicits.



(* ********************************************************************** *)
(* * Copy of a tree *)

(* ---------------------------------------------------------------------- *)
(* ** Node allocation *)

Definition val_new_node := val_new_record 3%nat.

(** Above equivalent to :

Definition val_new_node :=
  ValFun 'x 'y 'z :=
    Let 'p := val_alloc 3 in
    val_set_item 'p 'x;;;
    val_set_left 'p 'y;;;
    val_set_right 'p 'z;;;
    'p.
*)

Lemma Triple_new_node : forall x p1 p2,
  Triple (val_new_node ``x ``p1 ``p2)
    PRE \[]
    POST (fun p => (p ~> Cell x p1 p2)).
Proof using. xtriple_new_record. Qed.

Hint Extern 1 (Register_Spec val_new_node) => Provide Triple_new_node.


(* ---------------------------------------------------------------------- *)
(* ** Tree copy *)

Definition val_tree_copy :=
  ValFix 'f 'p :=
    If_ val_eq 'p null Then null Else (
      Let 'x := val_get_item 'p in
      Let 'p1 := val_get_left 'p in
      Let 'p2 := val_get_right 'p in
      Let 'q1 := 'f 'p1 in
      Let 'q2 := 'f 'p2 in
      val_new_node 'x 'q1 'q2
   ).

Hint Constructors tree_sub.

Lemma Triple_tree_copy : forall p T,
  Triple (val_tree_copy ``p)
    PRE (p ~> MTree T)
    POST (fun (p':loc) => (p ~> MTree T) \* (p' ~> MTree T)).
Proof using.
  intros. gen p. induction_wf IH: tree_sub_wf T. xcf.
  xapps~. xif ;=> C.
  { xval. subst p. rewrite MTree_null_eq. xsimpl~. }
  { xtchanges~ (MTree_not_null_inv_node p) ;=> x p1 p2 T1 T2 E. subst.
  xapps. xapps. xapps. xapp~ IH as p1'. xapp~ IH as p2'.
  xapp. intros p'. do 2 rewrite MTree_node_eq. xsimpl. }
Qed.


(* ********************************************************************** *)
(* * Complete binary trees *)

(* ---------------------------------------------------------------------- *)
(* ** Representation *)

Inductive depth : nat -> tree -> Prop :=
  | depth_leaf :
      depth 0%nat Leaf
  | depth_node : forall x n T1 T2,
      depth n T1 ->
      depth n T2 ->
      depth (S n) (Node x T1 T2).

Definition MTreeDepth (n:nat) (T:tree) (p:loc) : hprop :=
  (p ~> MTree T) \* \[depth n T].

Definition MTreeComplete (T:tree) (p:loc) : hprop :=
  \exists n, (p ~> MTree T) \* \[depth n T].


(* ---------------------------------------------------------------------- *)
(* ** Alternative representation *)

Definition MTreeComplete' (T:tree) (p:loc) : hprop :=
  \exists n, (p ~> MTreeDepth n T).

Definition MTreeComplete'' (T:tree) (p:loc) : hprop :=
  (p ~> MTree T) \* \[exists n, depth n T].

Lemma MTreeComplete'_eq : MTreeComplete' = MTreeComplete.
Proof using.
  applys fun_ext_2 ;=> T p.
  unfold MTreeComplete, MTreeComplete'.
  xunfold~ MTreeDepth.
Qed.

Lemma MTreeComplete''_eq : MTreeComplete'' = MTreeComplete.
Proof using.
  applys fun_ext_2 ;=> T p.
  unfold MTreeComplete, MTreeComplete''.
  applys himpl_antisym.
  { xpull ;=> (n&E). xsimpl*. }
  { xpull ;=> n E. xsimpl*. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Copy of a complete binary tree *)

Lemma Triple_tree_copy_complete : forall p T,
  Triple (val_tree_copy ``p)
    PRE (p ~> MTreeComplete T)
    POST (fun (p':loc) => (p ~> MTreeComplete T) \* (p' ~> MTreeComplete T)).
Proof using.
  intros. xunfolds MTreeComplete ;=> n Hn. xapplys* Triple_tree_copy.
Qed.


(* ********************************************************************** *)
(* * Binary search trees *)

From TLC Require Import LibOrder.

(* ---------------------------------------------------------------------- *)
(* ** Representation *)

(** Characterization of binary search trees *)

Definition is_lt (X Y:int) := Y < X.
Definition is_gt (X Y:int) := X < Y.

Inductive stree : tree -> LibSet.set int -> Prop :=
  | sLeaf :
      stree Leaf \{}
  | sNode : forall y T1 T2 E1 E2 E,
      stree T1 E1 ->
      stree T2 E2 ->
      foreach (is_lt y) E1 ->
      foreach (is_gt y) E2 ->
      E =' (\{y} \u E1 \u E2) ->
      stree (Node y T1 T2) E.

(** Representation predicate for binary search trees
    [p ~> Stree T] *)

Definition Stree (E:set int) (p:loc) :=
  \exists (T:tree), (p ~> MTree T) \* \[stree T E].


(* ---------------------------------------------------------------------- *)
(* ** Unfolding lemmas *)

(** Unfolding lemmas for TreeList *)

Lemma focus_Stree : forall p E,
  p ~> Stree E ==>
  \exists (T:tree), p ~> MTree T \* \[stree T E].
Proof using. intros. xunfold Stree. xsimpl~. Qed.

Lemma unfocus_Stree : forall p T E,
  p ~> MTree T \* \[stree T E] ==> p ~> Stree E.
Proof using. intros. xunfold Stree. xsimpl~. Qed.

Global Opaque Stree.


(* ---------------------------------------------------------------------- *)
(* ** Automation *)

Hint Extern 1 (_ = _ :> LibSet.set _) => set_prove : set.

Ltac auto_tilde ::= eauto.
Ltac auto_star ::= try solve [ intuition (eauto with set) ].

Lemma foreach_gt_notin : forall E x y,
  foreach (is_gt y) E ->
  lt x y ->
  x \notin E.
Proof using. introv F L N. lets H: (F _ N). applys* lt_slt_false L. Qed.

Lemma foreach_lt_notin : forall E x y,
  foreach (is_lt y) E ->
  lt y x ->
  x \notin E.
Proof using. introv F L N. lets H: (F _ N). applys* lt_slt_false L. Qed.

Hint Constructors tree_sub.


(* ---------------------------------------------------------------------- *)
(* ** Implementation of search *)

(* TODO: comparison primitives

let rec search x p =
  if p == null then false else
  let y = p.data in
  if x < y then search x p.left
  else if x > y then search x p.right
  else true

*)


(* ---------------------------------------------------------------------- *)
(* ** Verification *)

(*

Lemma search_spec_ind :
  Spec search (x:int) (p:loc) |R>>
     forall T E, stree T E ->
     R (p ~> Tree T)
       (fun b => \[b = isTrue (x \in E)] \* p ~> Tree T).
Proof using.
  xinduction_heap (tree_sub).
  xcf. intros x p T. introv IH IE.
  xapps. xif.
  xtchange focus_tree_null. xextracts. xret.
   inverts IE. xsimpl. xchanges unfocus_Leaf.
   fold_bool; rew_istrue. intros H. set_in H.
  xtchange~ (@focus_tree_not_null p).
   xextract as y p1 p2 T1 T2 EQ. subst T.
   inverts IE. xapps. xif.
  xapps. xapp*. intros b.
   xchange (@unfocus_Node p). xsimpl.
   subst b. extens; rew_istrue. subst E. iff M.
    eauto.
    set_in M.
      math.
      auto.
      false* foreach_gt_notin H6 C0.
  xif. xapps. xapps*. intros b.
    xchange (@unfocus_Node p). xsimpl.
   subst b. extens; rew_istrue. subst E. iff M.
    rewrite <- for_set_union_empty_r.
     repeat rewrite <- for_set_union_assoc.
     apply in_union_get_3. assumption.
    set_in M.
      math.
      lets: foreach_lt_notin x H4 __. math. false.
      auto.
  xret.
    xchange (@unfocus_Node p). xsimpl. subst E.
    asserts_rewrite (x = y). math. auto.
Qed.

Lemma search_spec :
  Spec search (x:int) (p:loc) |R>>
     forall E,
     R (p ~> Stree E)
       (fun b => \[b = isTrue (x \in E)] \* p ~> Stree E).
Proof using.
  xweaken search_spec_ind. simpl. introv M S1. intros.
  xtchange (@focus_Stree x2). xextract as T1 R1.
  xapply S1. eauto. xsimpl. intros. hextracts.
  xchange* (@unfocus_Stree x2). xsimpl*.
Qed.

*)


(* ********************************************************************** *)
(* * Reference on trees *)

(* TODO: ref on a search tree, specification of [insert] *)
