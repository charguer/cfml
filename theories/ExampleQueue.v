(**

This file provides examples of the verification of a mutable queue,
using CFML 2.0.

Author: Arthur Charguéraud.
License: MIT.

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

Definition MQueue `{EA:Enc A} (L:list A) (p:loc) :=
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
  VFun 'p :=
    'p'.head '= 'p'.tail.

Lemma Triple_is_empty : forall `{EA:Enc A} (L:list A) p,
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
  VFun 'd :=
    Let 'c := mk_cell 'd null in
    mk_cell 'c 'c.

Lemma Triple_create : forall `{EA:Enc A} (d:A),
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
  VFun 'p 'x :=
    Set 'p'.head ':= mk_cell 'x ('p'.head).

Lemma Triple_push_front : forall `{EA:Enc A} p L (x:A),
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
  VFun 'p :=
    Let 'f := 'p'.head in    
    Let 'x := 'f'.head in
    Set 'p'.head ':= ('f'.tail) '; (* TODO: pb without parenthesis *)
    'x.

(* TODO FIX NOTATIONS display record field *)

Lemma Triple_pop_front : forall `{EA:Enc A} p (L:list A),
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
  VFun 'p 'x :=
    Let 'b := 'p'.tail in
    Let 'c := mk_cell ('b'.head) null in
    Set 'b'.head ':= 'x ';
    Set 'b'.tail ':= 'c ';
    Set 'p'.tail ':= 'c.

Lemma Triple_push_back : forall `{EA:Enc A} p x (L:list A),
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
(* ** Bonus *)

(** Alternative specification for [pop_front] for the case the list
    is already of the form [x::L']. *)

Lemma triple_pop_front' : forall `{EA:Enc A} p x (L':list A),
  TRIPLE (pop_front p)
    PRE (p ~> MQueue (x::L'))
    POST (fun r => \[r = x] \* p ~> MQueue L').
Proof using.
  intros. xapply (>> Triple_pop_front (x::L')).
  { auto_false. }
  { xsimpl. }
  { xpull ;=> r L'2 E. inverts E. xsimpl~. }
Qed.

(* TODO: disable RET notation in TRIPLE *)
 

(* ********************************************************************** *)
(* * Transfer

 


Definition val_transfer :=
  ValFun 'p1 'p2 :=
    Let 'e2 := val_is_empty 'p2 in
    If_ val_not 'e2 Then
       Let 'b1 := val_get_tl 'p1 in
       Let 'f2 := val_get_hd 'p2 in
       Let 'x2 := val_get_hd 'f2 in
       Let 'n2 := val_get_tl 'f2 in
       Let 'b2 := val_get_tl 'p2 in
       val_set_tl 'p1 'b2 ;;;
       val_set_hd 'b1 'x2 ;;;
       val_set_tl 'b1 'n2 ;;;
       val_set_tl 'p2 'f2
    End.

Lemma Triple_transfer : forall `{EA:Enc A} (L1 L2:list A) p1 p2,
  Triple (val_transfer p1 p2)
    (p1 ~> MQueue L1 \* p2 ~> MQueue L2)
    (fun (_:unit) => p1 ~> MQueue (L1 ++ L2) \* p2 ~> MQueue nil).
Proof using.
  xcf. xapps. xapps. xif ;=> C.
  { xunfold MQueue. xtpull ;=> f2 b2 vx2 vy2 f1 b1 vx1 vy1.
    destruct L2 as [|x L2']; tryfalse.
    rewrite MListSeg_cons_eq. xtpull ;=> f2'.
    xapps. xapps. xapps. xapps.
    xapps~. xapps~. xapps~. xapps~. xapps~.
    xchange (>> (@MListSeg_last) f1).
    xchange (MListSeg_concat f1 f2'). rew_list.
    xchange (MListSeg_nil f2). xsimpl~. }
  { subst. rew_list. xvals~. }
Qed.

(*
*)



(* ********************************************************************** *)
(* ** Create *)

(* ---------------------------------------------------------------------- *)
(** Transfer *)

Definition val_transfer :=
  ValFun 'p1 'p2 :=
    Let 'e2 := val_is_empty 'p2 in
    If_ val_not 'e2 Then
       Let 'b1 := val_get_tl 'p1 in
       Let 'f2 := val_get_hd 'p2 in
       Let 'x2 := val_get_hd 'f2 in
       Let 'n2 := val_get_tl 'f2 in
       Let 'b2 := val_get_tl 'p2 in
       val_set_tl 'p1 'b2 ;;;
       val_set_hd 'b1 'x2 ;;;
       val_set_tl 'b1 'n2 ;;;
       val_set_tl 'p2 'f2
    End.

Lemma triple_transfer : forall L1 L2 p1 p2,
  triple (val_transfer p1 p2)
    (MQueue L1 p1 \* MQueue L2 p2)
    (fun r => MQueue (L1 ++ L2) p1 \* MQueue nil p2).
Proof using.
  xcf. xapps. xapps. xif ;=> C.
  { unfold MQueue. xtpull ;=> f2 b2 vx2 vy2 f1 b1 vx1 vy1.
    destruct L2 as [|x L2']; tryfalse.
    xtchanges MListSeg_cons_eq ;=> f2'.
    xapps. xapps. xapps. xapps.
    xapps~. xapps~. intros _. xapps~. intros _. xapps~. intros _. xapps~.
    intros r. xchange (MListSeg_last f1).
    xchange (MListSeg_concat f1 f2' b2). rew_list.
    xchange (MListSeg_nil f2). xsimpl~. }
  { subst. rew_list. xvals~. }
Qed.

*)