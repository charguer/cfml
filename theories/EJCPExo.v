(**

EJCP: hands-on session.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
Generalizable Variables A.
From Sep Require Import Example.
From Sep Require ExampleStack ExampleList.
Open Scope comp_scope. (* TODO: move *)
Implicit Types n m : int.
Implicit Types p q : loc.

(* TODO: move *)

Parameter list_concat : val.

Notation "t1 '++ t2" :=
  (list_concat t1 t2)
  (at level 68) : trm_scope.

Parameter Triple_list_concat : forall `{Enc A} (l1 l2:list A),
  TRIPLE (list_concat ``l1 ``l2)
    PRE \[]
    POST (fun r => \[r = l1 ++ l2]).

Hint Extern 1 (Register_Spec (list_concat)) => Provide @Triple_list_concat.



(* ####################################################### *)
(** * Basic functions *)

Module ExoBasic.


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
  xwp. xapp. xsimpl. math.
Qed.


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
    'p ':= ('!'p '+ '!'p).

Lemma Triple_inplace_double : forall p n,
  TRIPLE (inplace_double p)
    PRE (p ~~> n)
    POST (fun (_:unit) => p ~~> (2 * n)).
Proof using.
  xwp. xapp. xapp. xapp. xapp. xsimpl. math.
Qed.


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
    decr 'p ';
    incr 'q.

Lemma Triple_decr_and_incr : forall p q n m,
  TRIPLE (decr_and_incr p q)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (_:unit) => p ~~> (n-1) \* q ~~> (m+1)).
Proof using.
  xwp. xapp. xapp. xsimpl.
Qed.


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
      decr 'p ';
      incr 'q ';
      'f 'p 'q
    End.

Lemma Triple_transfer : forall p q n m,
  n >= 0 ->
  TRIPLE (transfer p q)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (_:unit) => p ~~> 0 \* q ~~> (n + m)).
Proof using.
  introv N. gen m N. induction_wf IH: (downto 0) n. intros.
  xwp. xapp. xapp. xif ;=> C.
  { xapp. xapp. xapp. { hnf. math. } { math. } 
    xsimpl. math. }
  { xval tt. xsimpl. math. math. }
Qed.

End ExoBasic.


(* ####################################################### *)
(** * Stack *)

Module ExoStack.
Import ExampleStack.Stackn.

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
    Set 'p'.data ':= ``nil '; (* TODO: ('nil%val)*)
    Set 'p'.size ':= ``0.

Lemma Triple_clear : forall `{Enc A} (p:loc) (L:list A),
  TRIPLE (clear p)
    PRE (p ~> Stackn L)
    POST (fun (u:unit) => p ~> Stackn nil).
Proof using.
  xwp. xunfold Stackn. xapp. xapp. xsimpl.
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

(* TODO move *)

Lemma Stackn_eq : forall (p:loc) `{Enc A} (L:list A),
  p ~> Stackn L =
  p ~> Record`{ data := L; size := LibListZ.length L }.
Proof using. auto. Qed.

Definition concat :=
  VFun 'p1 'p2 :=
    Set 'p1'.data ':= (('p1'.data) '++ ('p2'.data)) ';
    Set 'p1'.size ':= (('p1'.size) '+ ('p2'.size)) ';
    clear 'p2.

Lemma Triple_concat : forall `{Enc A} (p1 p2:loc) (L1 L2:list A),
  TRIPLE (concat p1 p2)
    PRE (p1 ~> Stackn L1 \* p2 ~> Stackn L2)
    POST (fun (u:unit) => p1 ~> Stackn (L1 ++ L2) \* p2 ~> Stackn nil).
Proof using.
  xwp. xunfold Stackn. xapp. xapp. xapp. xapp. xapp. xapp. xapp.
  xapp. xchange <- (Stackn_eq p1).
  (* TODO: xsimpl do record_eq *) { xrecord_eq. rew_listx. auto. }
  xchange <- (Stackn_eq p2). xapp. xsimpl.
Qed.

End ExoStack.


(* ####################################################### *)
(** * Mutable lists *)

Module ExoList.
Import ExampleList.MList.
Hint Extern 1 (Register_Spec (is_empty)) => Provide @Triple_is_empty.
Hint Extern 1 (Register_Spec (create)) => Provide @Triple_create.

(* ******************************************************* *)
(** ** Create one element *)

(**
[[
  let mk_one x =
    mk_cons x (create())
]]
*)

Definition mk_one : val :=
  VFun 'x :=
     mk_cons 'x (create '()).

Lemma Triple_mk_one : forall A `{EA:Enc A} (x:A),
  TRIPLE (mk_one ``x)
    PRE \[]
    POST (fun p => p ~> MList (x::nil)).
Proof using.
  intros. xwp. xapp ;=> q. xapp. xsimpl.
Qed.

Hint Extern 1 (Register_Spec (mk_one)) => Provide @Triple_mk_one.


(* ******************************************************* *)
(** ** Push back using append *)

(** Note: [L&x] is a notation for [L++x::nil]. *)

(**
[[
  let push_back p x =
    inplace_append p (mk_one x)
]]
*)

Definition push_back : val :=
  VFun 'p 'x :=
    inplace_append 'p (mk_one 'x).

Lemma Triple_push_back : forall `{EA:Enc A} (L:list A) (x:A) (p:loc),
  TRIPLE (push_back ``p ``x)
    PRE (p ~> MList L)
    POST (fun (_:unit) => p ~> MList (L++x::nil)).
Proof using.
  xwp. xapp ;=> q. xapp. xsimpl.
Qed.


(* ******************************************************* *)
(** ** Push back not using append (blue belt) *)

Definition push_back' : val :=
  VFix 'f 'p1 'x :=
    If_ is_empty 'p1 
      Then set_cons 'p1 'x (create '())
      Else 'f (tail 'p1) 'x.

Lemma Triple_push_back' : forall `{EA:Enc A} (L:list A) (x:A) (p:loc),
  TRIPLE (push_back' ``p ``x)
    PRE (p ~> MList L)
    POST (fun (_:unit) => p ~> MList (L++x::nil)).
Proof using.
  intros. gen p. induction_wf IH: (@list_sub A) L. intros.
  xwp. xif ;=> C. 
  { xchanges (MList_eq p) ;=> v1.
    xapp ;=> q. xapp. xchanges* <- (MList_cons p). }
  { xchanges~ (MList_not_nil p) ;=> y L' p' ->.
    xapp. xapp. { auto. } xchanges <- MList_cons. }
Qed.


(* ******************************************************* *)
(** ** Nondestructive append (violet belt) *)

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
  xwp. xapp. xif ;=> C.
  { xapp Triple_copy ;=> p3. xsimpl*. }
  { xchanges~ (MList_not_nil p1) ;=> x L1' p1' ->.
    xapp. xapp. xapp* ;=> p3'. xchanges <- (MList_cons p1).
    xapp ;=> p3. xsimpl. }
Qed.


(* ******************************************************* *)
(** ** Pop back (brown belt) *)

(**
[[
  let rec pop_back p =
    if is_empty (tail p) then (
      let x = head p in
      set_nil p;
      x 
    ) else (
      pop_back (tail p)
    )
]]
*)

Definition pop_back : val :=
  VFix 'f 'p :=
    If_ is_empty (tail 'p) Then (
      Let 'x := head 'p in
      set_nil 'p ';
      'x
    ) Else (
      'f (tail 'p)
    ).

Lemma Triple_pop_back : forall `{EA:Enc A} (L:list A) (p:loc),
  L <> nil ->
  TRIPLE (pop_back ``p)
    PRE (p ~> MList L)
    POST (fun x => \exists L1, \[L = L1++x::nil] \* p ~> MList L1).
Proof using.
  introv. gen p. induction_wf IH: (@list_sub A) L. introv N.
  xwp. destruct L as [|x L']; tryfalse. xchange MList_cons ;=> p'.
  xapp. xapp. xif ;=> C.
  { skip. }
  { xapp. xapp. { auto. } { auto. } intros y L1' ->.
    xsimpl (x::L1'). { rew_list. auto. } xchanges <- MList_cons. }
Qed.

End ExoList.



