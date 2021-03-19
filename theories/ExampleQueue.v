(**

This file provides examples of the verification of a mutable queue,
using CFML 2.0.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)


Set Implicit Arguments.
Generalizable Variables A B.
From Sep Require Import Example ExampleListNull.

Implicit Types p q : loc.
Implicit Types n : int.
Implicit Types v : val.




(* ********************************************************************** *)
(* * Mutable queue *)

(* ---------------------------------------------------------------------- *)
(** ** Representation *)

(** The mutable queue stores items in a linked list. The queue is described by
    a record made of two pointers, one on the front cell of the list, and one
    on the back cell (i.e. the last cell) of that list. The last cell of the
    list contains a default value that is not treated as a proper item. The role
    of the last cell is to ensure that even an empty queue contains at least
    one cell, thereby avoiding a special treatment for empty queues.

    Concretely, a queue at location [p] consists of a cell with fields [f] and [b],
    a linked list segment from location [f] to location [b], storing a list [L] of
    items, and a special cell at location [b] storing the default value [d], and
    whose tail field stores the [null] value. *)

Definition MQueue A `{EA:Enc A} (L:list A) (p:loc) :=
  \exists (f:loc) (b:loc) (d:A),
    p ~> MCell f b \* f ~> MListSeg b L \* b ~> MCell d null.

Lemma MQueue_eq : forall (p:loc) `{EA:Enc A} (L:list A),
  p ~> MQueue L =
   \exists (f:loc) (b:loc) (d:A),
    p ~> MCell f b \* f ~> MListSeg b L \* b ~> MCell d null.
Proof using. intros. xunfold~ MQueue. Qed.



(* ********************************************************************** *)
(* ** Is-empty *)

(**
[[
  let is_empty p =
    p.head == p.tail
]]
*)

Definition is_empty :=
  Fun 'p :=
    'p'.head '= 'p'.tail.

Lemma Triple_is_empty : forall A `{EA:Enc A} (L:list A) p,
  TRIPLE (is_empty p)
    PRE (p ~> MQueue L)
    POST (fun r => \[r = isTrue (L = nil)] \* p ~> MQueue L).
Proof using.
  xwp. xunfolds MQueue ;=> f b d. xapp. xapp. xapp~.
  xchange (MListSeg_MCell_conflict) ;=> M. xsimpl*.
Qed.

Hint Extern 1 (Register_Spec is_empty) => Provide Triple_is_empty.


(* ********************************************************************** *)
(* ** Create *)

(** The function [create] takes as argument a default value [d] of type [A].
    It allocates adummy cell, at location [c]. It then allocates a queue record
    with a front pointer and a back pointer both set to [c].
[[
  let create d =
    let c = mk_cell d null in
    mk_cell c c
]]
*)

Definition create :=
  Fun 'd :=
    Let 'c := mk_cell 'd null in
    mk_cell 'c 'c.

Lemma Triple_create : forall A `{EA:Enc A} (d:A),
  TRIPLE (create ``d)
    PRE \[]
    POST (fun (p:loc) => p ~> MQueue (@nil A)).
Proof using.
  xwp. xunfold MQueue. xapp ;=> c. xapp ;=> p.
  xchanges (MListSeg_nil_intro c).
Qed.

Hint Extern 1 (Register_Spec create) => Provide Triple_create.


(* ********************************************************************** *)
(* ** Push front *)

(** The function [push_front p x] inserts an item [x] at the front of the
    queue at location [p], in place.
[[
  let push_front p x =
    p.head := mk_cell x p.head
]]
*)

Definition push_front :=
  Fun 'p 'x :=
    Set 'p'.head ':= mk_cell 'x ('p'.head).

Lemma Triple_push_front : forall A `{EA:Enc A} p L (x:A),
  TRIPLE (push_front ``p ``x)
    PRE (p ~> MQueue L)
    POST (fun (_:unit) => p ~> MQueue (x::L)).
Proof using.
  xwp. xunfold MQueue. xpull ;=> f b d. xapp. xapp ;=> q. xapp.
  xchanges <- (MListSeg_cons q).
Qed.

Hint Extern 1 (Register_Spec push_front) => Provide Triple_push_front.


(* ********************************************************************** *)
(* ** Pop front *)

(** The function [pop_front p] assumes a nonempty queue at location [p], and
    extracts the head item [x] from that queue, in place.

[[
  let pop_front p =
    let f = p.head in
    let x = f.head in
    p.head := f.tail;
    x
]]
*)

Definition pop_front :=
  Fun 'p :=
    Let 'f := 'p'.head in
    Let 'x := 'f'.head in
    Set 'p'.head ':= ('f'.tail) '; (* TODO: pb without parenthesis *)
    'x.

(* TODO FIX NOTATIONS display record field *)

Lemma Triple_pop_front : forall A `{EA:Enc A} p (L:list A),
  L <> nil ->
  TRIPLE (pop_front ``p)
    PRE (p ~> MQueue L)
    POST (fun x => \exists L', \[L = x::L'] \* p ~> MQueue L').
Proof using.
  xwp. destruct L as [|x L']; tryfalse.
  xunfold MQueue. xpull ;=> f b d.
  xchange MListSeg_cons ;=> f'.
  xapp. xapp. xapp. xapp. xvals*.
Qed.

Hint Extern 1 (Register_Spec pop_front) => Provide Triple_pop_front.


(* ********************************************************************** *)
(* ** Push back *)

(** The function [push_back p x] inserts the item [x] at the back of the queue,
    in place. The function runs in constant time.

[[
  let push_back p x =
    let b = p.tail in
    b.tail := mk_cell b.head null;
    b.head := x
]]
*)

Definition push_back :=
  Fun 'p 'x :=
    Let 'b := 'p'.tail in
    Let 'c := mk_cell ('b'.head) null in
    Set 'b'.head ':= 'x ';
    Set 'b'.tail ':= 'c ';
    Set 'p'.tail ':= 'c.

Lemma Triple_push_back : forall A `{EA:Enc A} p x (L:list A),
  TRIPLE (push_back ``p ``x)
    PRE (p ~> MQueue L)
    POST (fun (_:unit) => p ~> MQueue (L++x::nil)).
Proof using.
  xwp. xunfold MQueue. xpull ;=> f b d.
  xapp. xapp. xapp ;=> c. xapp. xapp. xapp.
  xchanges <- MListSeg_last.
Qed.

Hint Extern 1 (Register_Spec push_back) => Provide Triple_push_back.


(* ********************************************************************** *)
(* ** Transfer *)

(** The function [transfer p1 p2] migrates all the items from the queue [p2]
    to the back of the queue [p1], then clears [p2].

    If [p2] is empty there is nothing to do. Else, the function performs
    copy the data from the front cell of [p2] into the back cell of [p1],
    then sets the back pointer of [p2] as new back pointer for [p1].

[[
  let transfer p1 p2 =
    if not (is_empty p2) then begin
      let b1 = p1.tail in
      let f2 = p2.front in
      b1.head := f2.head;
      b1.tail := f2.tail;
      p1.tail := p2.tail
    end
]]
*)

Definition transfer :=
  Fun 'p1 'p2 :=
    If_ 'not (is_empty 'p2) Then
       Let 'b1 := 'p1'.tail in
       Let 'f2 := 'p2'.head in
       Let 'd := 'b1'.head in
       Set 'b1'.head ':= ('f2'.head) ';
       Set 'b1'.tail ':= ('f2'.tail) ';
       Set 'p1'.tail ':= ('p2'.tail) ';
       Set 'f2'.head ':= 'd ';
       Set 'f2'.tail ':= ``null ';
       Set 'p2'.tail ':= 'f2
    End.

(* TODO: remove ' in Set, for symmetry with let *)

Lemma Triple_transfer : forall A `{EA:Enc A} (L1 L2:list A) p1 p2,
  TRIPLE (transfer p1 p2)
    PRE (p1 ~> MQueue L1 \* p2 ~> MQueue L2)
    POST (fun (_:unit) => p1 ~> MQueue (L1 ++ L2) \* p2 ~> MQueue (@nil A)).
Proof using.
  xwp. xapp. xapp. xif ;=> C.
  { xunfold MQueue. xpull ;=> f2 b2 d2 f1 b1 d1. (* TODO: fix order, should be preserved *)
    destruct L2 as [|x L2']; tryfalse.
    xchange MListSeg_cons ;=> c2.
    xapp. xapp. xapp. xapp. xapp. xapp. xapp. xapp. xapp. xapp. xapp. xapp.
    xchange <- (MListSeg_cons b1). xchange <- (MListSeg_concat f1).
    xchanges (MListSeg_nil_intro f2). }
  { subst. rew_list. xvals~. }
Qed.


(* ********************************************************************** *)
(* ** Bonus *)

(** Alternative specification for [pop_front] for the case the list
    is already of the form [x::L']. *)

Lemma triple_pop_front' : forall A `{EA:Enc A} p x (L':list A),
  TRIPLE (pop_front p)
    PRE (p ~> MQueue (x::L'))
    POST (fun r => \[r = x] \* p ~> MQueue L').
Proof using.
  intros. xapply (>> Triple_pop_front (x::L')).
  { auto_false. }
  { xsimpl. }
  { xpull ;=> r L'2 E. inverts E. xsimpl~. }
Qed.


