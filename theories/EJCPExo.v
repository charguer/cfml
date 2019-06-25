(**

EJCP: hands-on session.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.

From Sep Require Import Example.
From Sep Require ExampleStack ExampleList.


(* TODO: move *)

Parameter list_concat : val.

Notation "t1 '++ t2" :=
  (list_concat t1 t2)
  (at level 68) : trm_scope.

Parameter Triple_list_concat : forall `{Enc A} (l1 l2:list A),
  TRIPLE (list_concat l1 l2)
    PRE \[]
    POST (fun r => \[r = l1 ++ l2]).

Hint Extern 1 (Register_Spec (list_concat)) => Provide @Triple_list_concat.



(* ####################################################### *)
(** * Basic functions *)

Module ExampleBasic.


(* ******************************************************* *)
(** ** Basic pure function *)

(** 
[[
  let double n =
    n + n
]]
*)

Definition double :=
  VFun 'n :=
    'n '+ 'n.

Lemma Triple_double : forall n,
  TRIPLE (double n)
    PRE \[]
    POST (fun m => \[m = 2 * n]).
Proof using.
Abort.


(* ******************************************************* *)
(** ** Basic imperative function with one argument *)

(** 
[[
  let inplace_double p =
    p := !p + !p
]]
*)

Definition inplace_double :=
  VFun 'p :=
    ('! 'p) '+ ('! 'p).

Lemma Triple_inplace_double : forall p,
  TRIPLE (inplace_double p)
    PRE (p ~~> n)
    POST (fun (_:unit) => p ~~> (2 * n)).
Proof using.
Abort.


(* ******************************************************* *)
(** ** Basic imperative function with two arguments (white belt) *)

(** 
[[
  let decr_and_incr p q =
    decr p;
    incr q
]]
*)

Definition decr_and_incr :=
  VFun 'p 'q :=
    incr 'p ';
    decr 'q.

Lemma Triple_decr_and_incr : forall p q n m,
  TRIPLE (decr_and_incr p q)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (_:unit) => p ~~> (n-1) \* q ~~> (m+1)).
Proof using.
Abort.


(* ******************************************************* *)
(** *** A recursive function (yellow belt) *) 

(** Here, we will assume [!p > 0].

[[
  let rec transfer p q =
    if !p > 0 then (
      decr p;
      incr q;
      transfer p q
    )
]]
*)

Definition transfer :=
  VFix 'f 'p 'q :=
    If_ '! 'p '> 0 Then
      incr 'p ';
      decr 'q ';
      'f 'p 'q
    End.

Lemma Triple_transfer : forall p q n m,
  n > 0 ->
  TRIPLE (transfer p q)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (_:unit) => p ~~> 0 \* q ~~> (n + m)).
Proof using.
Abort.


End ExampleBasic.


(* ####################################################### *)
(** * Stack *)

Module ExampleStack.
Import Stackn.

(** Recall from [ExampleStack.v]
[[
  type 'a lstack = { data : 'a list; size : int }
]]
*)

(* ******************************************************* *)
(** ** The clear function *) 

(** 
[[
   let clear p =  
     p.data <- [];
     p.size <- 0
]]
*)

Definition clear :=
  VFun 'p :=
    Set 'p'.data := ('nil%val) ';
    Set 'p'.size := 0.

Lemma Triple_clear : forall `{Enc A} (p:loc) (L:list A),
  TRIPLE (clear p)
    PRE (p ~> Stackn L)
    POST (fun (u:unit) => (p ~> Stackn nil).
Proof using.
  xwp. xunfold Stackn. xapp. xappn.
  xsimpl.
Qed.

Hint Extern 1 (Register_Spec (clear)) => Provide @Triple_clear.


(* ******************************************************* *)
(** ** The concat function (orange belt)  *) 

(** 
[[
   let concat p1 p2 =
     p1.data <- p1.data @ p2.data;
     p1.size <- p1.size + p2.size;
     clear p2
]]
*)

Definition concat :=
  VFun 'p1 'p2 :=
    Set 'p1'.data := 'p1'.data '++ 'p2'.data;
    Set 'p2'.size := 'p1'.size '+ 'p2'.size;
    clear 'p2.

Lemma Triple_clear : forall `{Enc A} (p1 p2:loc) (L1 L2:list A),
  TRIPLE (concat p1 p2)
    PRE (p1 ~> Stackn L1 \* p2 ~> Stackn L2)
    POST (fun (u:unit) => p1 ~> Stackn (L1 ++ L2) \* p2 ~> Stackn nil).
Proof using.
  xwp. xunfold Stackn. xapp. xappn.
  xsimpl.
Qed.

End ExampleStack.



(* ####################################################### *)
(** * Mutable lists *)

Module ExampleList.


(* ******************************************************* *)
(** ** Push back using append *)


(* ******************************************************* *)
(** ** Pop back *)


(* ******************************************************* *)
(** ** Nondestructive append (blue belt) *)

Definition nondestructive_append : val :=
  VFix 'f 'p1 'p2 :=
    If_ is_empty 'p1 
      Then copy 'p2
      Else mk_cons (head 'p1) ('f (tail 'p1) 'p2).

Lemma Triple_nondestructive_append : forall `{EA:Enc A} (L1 L2:list A) (p1 p2:loc),
  TRIPLE (nondestructive_append p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (p3:loc) => p1 ~> MList L1 \* p2 ~> MList L2 \* p3 ~> MList (L1++L2)).
Proof using.
  intros. gen p1. induction_wf IH: (@list_sub A) L1. intros.
  xwp. xif ;=> C.
  { xapp Triple_copy ;=> p3. xsimpl*. }
  { xchanges~ (MList_not_nil p1) ;=> x L1' p1' ->.
    xapp. xapp. xapp* ;=> p3'. xchanges <- (MList_cons p1).
    xapp ;=> p3. xsimpl. }
Qed.

Hint Extern 1 (Register_Spec (nondestructive_append)) => Provide @Triple_nondestructive_append.


End ExampleList.
