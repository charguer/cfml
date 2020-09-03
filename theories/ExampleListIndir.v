(**

This file formalizes mutable list examples in CFML 2.0,
using a representation of lists as a reference on
either null or on a two-cell record.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Import Example.
Generalizable Variables A B.

Implicit Types p q : loc.
Implicit Types n m : int.


(* TODO -- pointer arithmetic *)


Definition pointer_field (l:loc) (k:field) :=
  (l+k)%nat.




Notation "l `. k" := (pointer_field l k)
  (at level 32, k at level 0, no associativity,
   format "l `. k") : heap_scope.


Definition val_field (k:field) : val :=
  Fun 'p :=
    val_ptr_add 'p (nat_to_Z k).

Notation "l ``. k" := (val_field k l)
  (at level 32, k at level 0, no associativity,
   format "l ``. k") : heap_scope.


Parameter Triple_val_field : forall (k:field) (p:loc),
  TRIPLE ((val_field k) ``p)
    PRE \[]
    POST (fun (q:loc) => \[q = p`.k]).

Hint Extern 1 (Register_Spec (val_field _)) => Provide Triple_val_field.


Parameter Triple_val_get_field : forall (k:field) (p:loc) `{EA:Enc A} (v:A),
  TRIPLE ((val_get_field k) ``p)
    PRE (p`.k ~~> v)
    POST (fun (r:A) => \[r = v] \* p`.k ~~> v).

Hint Extern 1 (Register_Spec (val_get_field _)) => Provide Triple_val_get_field.





(* ********************************************************************** *)
(* * Towards a representation *)

(** Let's try to first formalize the C representation:
[[

    type list = node**
       // the pointer is null for an empty list
       // the pointer is the address of a record otherwise

    type node = record {
      item  head;
      node* tail;
    };
]]
*)


Definition head : field := 0%nat.
Definition tail : field := 1%nat.



(* ---------------------------------------------------------------------- *)
(** Representation of segments *)

Fixpoint MListSeg A `{EA:Enc A} (r:loc) (L:list A) (p:loc) : hprop :=
  match L with
  | nil => \[p = r]
  | x::L' => \exists (q:loc), p ~~> q \* q`.head ~~> x \* q`.tail ~> MListSeg r L'
  end.



Section SegProperties.

Lemma MListSeg_nil : forall A `{EA:Enc A} p r,
  p ~> (MListSeg r (@nil A)) = \[p = r].
Proof using. intros. xunfold~ MListSeg. Qed.

Lemma MListSeg_cons : forall A `{EA:Enc A} p r x (L':list A),
  p ~> MListSeg r (x::L') =
  \exists (q:loc), p ~~> q \* q`.head ~~> x \* q`.tail ~> MListSeg r L'.
Proof using. intros. xunfold MListSeg at 1. simple~. Qed.

Global Opaque MListSeg.

Lemma MListSeg_one : forall A `{EA:Enc A} p r (x:A),
  p ~> MListSeg r (x::nil) =
  \exists (q:loc), p ~~> q \* q`.head ~~> x \* \[q`.tail = r].
Proof using. intros. rewrite MListSeg_cons. fequals. Qed.

Lemma MListSeg_concat : forall A `{EA:Enc A} p1 r (L1 L2:list A),
  p1 ~> MListSeg r (L1++L2) = \exists p2, p1 ~> MListSeg p2 L1 \* p2 ~> MListSeg r L2.
Proof using.
  intros. gen p1. induction L1 as [|x L1']; intros; rew_list.
  { applys himpl_antisym.
    { (* TODO fix [xsimpl r]. *) applys himpl_hexists_r p1.
      (* TODO: xsimpl bug *) xchange~ <- MListSeg_nil. }
    { xpull ;=> p2. xchange* MListSeg_nil. } }
  { applys himpl_antisym.
    { rewrite MListSeg_cons. xpull ;=> q. xchange IHL1' ;=> p2.
      xchanges <- MListSeg_cons. }
    { xpull ;=> p2. xchange MListSeg_cons ;=> q. xchange <- IHL1'.
      xchange <- MListSeg_cons. } }
Qed.

End SegProperties.

Arguments MListSeg_nil : clear implicits.
Arguments MListSeg_cons : clear implicits.
Arguments MListSeg_one : clear implicits.
Arguments MListSeg_concat : clear implicits.


(* ---------------------------------------------------------------------- *)
(** Representation of full lists *)

Definition MList A `{EA:Enc A} (L:list A) (p:loc) : hprop :=
  \exists (r:loc), p ~> MListSeg r L \* r ~~> null.

Definition MListTail A `{EA:Enc A} (L:list A) (q:loc) : hprop :=
  match L with
  | nil => \[q = null]
  | x::L' => q`.head ~~> x \* q`.tail ~> MList L'
  end.


Lemma MList_eq : forall A `{EA:Enc A} (L:list A) (p:loc),
  p ~> MList L =
  \exists (r:loc), p ~> MListSeg r L \* r ~~> null.
Proof using. intros. xunfold~ MList. Qed.

Lemma MListTail_eq : forall A `{EA:Enc A} (L:list A) (q:loc),
  q ~> MListTail L =
   match L with
  | nil => \[q = null]
  | x::L' => q`.head ~~> x \* q`.tail ~> MList L'
  end.
Proof using. intros. xunfold~ MListTail. Qed.


Lemma MListTail_nil : forall A `{EA:Enc A} (q:loc),
  q ~> MListTail (@nil A) = \[q = null].
Proof using. intros. rewrite~ MListTail_eq. Qed.

Lemma MListTail_cons : forall A `{EA:Enc A} (x:A) (L':list A) (q:loc),
  q ~> MListTail (x::L') = q`.head ~~> x \* q`.tail ~> MList L'.
Proof using. intros. rewrite~ MListTail_eq. Qed.

Lemma MListTail_null : forall A `{EA:Enc A} (L:list A) (q:loc),
  q ~> MListTail L ==> q ~> MListTail L \* \[q = null <-> L = nil].
Proof using.
  intros. destruct L; xunfold MListTail.
  { xsimpl*. }
  { unfold pointer_field, head. rewrite Hfield_eq_fun_Hsingle.
    xunfold at 1. xunfold at 3.
    (* math_rewrite ((q+0%nat) = q)%nat.
    xchange Hsingle_not_null ;=> E. *)
    xsimpl; auto_false*. }
Qed.

Lemma MListTail_if : forall A `{EA:Enc A} (L:list A) (q:loc),
  q ~> MListTail L =
  If q = null
    then \[L = nil]
    else \exists x L', \[L = x::L'] \* q`.head ~~> x \* q`.tail ~> MList L'.
Proof using.
  intros. apply himpl_antisym.
  { xchange MListTail_null ;=> M. destruct L as [|x L']; xunfold MListTail.
    { case_if. { xsimpl*. } { xpull. (* TODO: xsimpl leaves shelved variables *) } }
    { case_if. { rewrite M in C. tryfalse. } { xsimpl*. } } }
  { xunfold MListTail. case_if.
    { xsimpl ;=> ->. xsimpl*. }
    { xpull ;=> x L' ->. xsimpl. } }
Qed.

Lemma MList_Tail : forall A `{EA:Enc A} (L:list A) (p:loc),
  p ~> MList L =
  \exists (q:loc), p ~~> q \* q ~> MListTail L.
Proof using.
  intros. xunfold MList. destruct L.
  { xunfold MListTail. applys himpl_antisym.
    { xpull ;=> r. xchange MListSeg_nil ;=> ->. xsimpl~. }
    { xpull ;=> ? ->. xsimpl p. xchange~ <- MListSeg_nil. } }
  { xunfold MListTail. applys himpl_antisym.
    { xpull ;=> r. rewrite MListSeg_cons. xpull ;=> q. xsimpl q. xchange <- MList_eq. }
    { xpull ;=> q. xchange MList_eq ;=> r. xsimpl r. xchange <- MListSeg_cons. } }
Qed.

Lemma MList_Tail_null : forall A `{EA:Enc A} (L:list A) (p:loc),
  p ~> MList L ==>
  \exists (q:loc), p ~~> q \* q ~> MListTail L \* \[q = null <-> L = nil].
Proof using.
  intros. xchange MList_Tail ;=> q. xchange MListTail_null ;=> M. xsimpl*.
Qed.

Lemma MList_Tail_if : forall A `{EA:Enc A} (L:list A) (p:loc),
  p ~> MList L ==>
  \exists (q:loc), p ~~> q \* If q = null
    then \[L = nil]
    else \exists x L', \[L = x::L'] \* q`.head ~~> x \* q`.tail ~> MList L'.
Proof using.
  intros. xchange MList_Tail ;=> q. xchange MListTail_if. xsimpl*.
Qed.

Lemma MList_nil : forall p A `{EA:Enc A},
  (p ~> MList (@nil A)) = p ~~> null.
Proof using.
  intros. xunfold MList. applys himpl_antisym.
  { xpull ;=> r. xchange* MListSeg_nil. }
  { xsimpl. xchange~ <- MListSeg_nil. }
Qed.

Lemma MList_cons : forall p A `{EA:Enc A} (x:A) L',
  p ~> MList (x::L') =
  \exists q, p ~~> q \* q`.head ~~> x \* q`.tail ~> MList L'.
Proof using.
  intros. xunfold MList. applys himpl_antisym.
  { xpull ;=> r. xchanges MListSeg_cons. }
  { xpull ;=> q r. xsimpl r. xchange <- MListSeg_cons. }
Qed.

Arguments MList_eq : clear implicits.
Arguments MList_Tail : clear implicits.
Arguments MList_nil : clear implicits.
Arguments MList_cons : clear implicits.

Global Opaque MList MListTail.


(* ********************************************************************** *)
(* ** Node allocation *)

Parameter mk_node : val.

Parameter Triple_mk_node : forall A `{EA:Enc A} (x:A) (q:loc),
  TRIPLE (mk_node ``x ``q)
    PRE \[]
    POST (fun p => p`.head ~~> x \* p`.tail ~~> q).

Hint Extern 1 (Register_Spec (mk_node)) => Provide @Triple_mk_node.


(* ********************************************************************** *)
(* ** Push (inserts an element at the head of the list, in place) *)

(**
[[
    void push(node** p, item x) {
      *p = mk_node(x, *p);
    }
]]
*)

Definition push : val :=
  Fun 'p 'x :=
    'p ':= mk_node 'x ('!'p).

Lemma Triple_push : forall A `{EA:Enc A} (L:list A) (p:loc) (x:A),
  TRIPLE (push p ``x)
    PRE (p ~> MList L)
    POST (fun (_:unit) => p ~> MList (x::L)).
Proof using.
  xwp. xchange MList_Tail ;=> q. xapp. xapp ;=> q'. xapp.
  (*
  xchange <- (>> MList_Tail q). xchange <- (MList_cons q').
Qed.
*)
Admitted.

Hint Extern 1 (Register_Spec (push)) => Provide @Triple_push.


(* ********************************************************************** *)
(* * Length of a mutable list *)

(**
[[
    int mlength(node** p) =
      node* q = *p;
      if (q == null) {
        return 0;
      } else {
        return 1 + mlength(&q.tail);
      }
]]
*)

Definition mlength : val :=
  Fix 'f 'p :=
    Let 'q := '! 'p in
    If_ 'q '= null
      Then 0
      Else 1 '+ 'f ('q ``.tail).

Lemma Triple_mlength : forall A `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (mlength ``p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  intros. gen p. induction_wf IH: list_sub_wf L; intros. xwp.
  xchange MList_Tail_if ;=> q. xapp. xapp~.
  xif ;=> C; case_if; xpull.
  { intros ->. xval. subst q. xchange <- MList_nil. xsimpl*. }
  { intros x L' ->. xapp. xapp~. xapp. xchanges* <- MList_cons. }
Qed.


(* ********************************************************************** *)
(* * List Copy, recursion on nodes *)

(**
[[
    node* copy_node(node* q) =
      if (q == null) {
        return null;
      } else {
        return mk_node(q.head, copy_node(q.tail));
      }
]]
*)

Definition copy_node :=
  Fix 'f 'q :=
    If_ val_eq 'q null
      Then null
      Else mk_node ('q'.head) ('f ('q'.tail)).

Lemma Triple_copy_node : forall A `{EA:Enc A} q (L:list A),
  TRIPLE (copy_node ``q)
    PRE (q ~> MListTail L)
    POST (fun (q':loc) =>
         (q ~> MListTail L) \* (q' ~> MListTail L)).
Proof using.
  intros. gen q. induction_wf IH: list_sub_wf L. xwp.
  xapp~. xchange MListTail_if. xif ;=> C; case_if; xpull.
  { intros ->. xval. do 2 rewrite (MListTail_nil). xsimpl~. }
  { intros x L' ->. xapp Triple_val_get_field. (* todo fix, if no record using single *)
    xchange MList_Tail ;=> q'.
(* xapp Triple_val_get_field. (* idem *)
    xapp~ ;=> q2'. xchange <- MList_Tail. xapp ;=> q2.
    xchange <- MList_Tail. xchange <- MListTail_cons. xchanges <- MListTail_cons. }
Qed.
*)
Admitted.

Hint Extern 1 (Register_Spec copy_node) => Provide Triple_copy_node.


(** Copy of full list, destination passing style
[[
    void copy_list(node** p, node** p2) =
      *p2 = copy_node( *p );
]]
*)

Definition copy_list :=
  Fun 'p 'p2 :=
    'p2 ':= copy_node ('! 'p).

Lemma Triple_copy_list : forall p p2 `{EA:Enc A} (L:list A),
  TRIPLE (copy_list ``p ``p2)
    PRE (p ~> MList L \* (\exists (q2:loc), p2 ~~> q2))
    POST (fun (_:unit) => p ~> MList L \* p2 ~> MList L).
Proof using.
  intros. xwp. xpull ;=> q2. xchange MList_Tail ;=> q.
  xapp. xapp ;=> q2'. xapp. xchange <- MList_Tail. xchanges <- MList_Tail.
Qed.



(* ********************************************************************** *)
(* * List Copy, recursion on lists *)

(** Exercise: verify this alternative implementation of copy_list.
[[
    node* copy_list(node** p) =
      node* q = *p;
      if (q == null) {
        return null;
      } else {
        node* q2 = mk_node(q.head, copy_list(&q.tail));
        *p2 = q2;
        copy(&q.tail, &q2.tail);
      }
]]
*)



