(**

This file provides examples of the verification of a mutable stack,
and of a mutable stack with size available in constant time.
using CFML 2.0.

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
Generalizable Variables A B.
From Sep Require Import Example.



(* ********************************************************************** *)
(* * Stack *)

(** Implementation of a stack as a reference on a list *)

Module Stack.

(** OCaml syntax
[[

  type 'a stack = ('a list) ref

  let create () =
    ref []

  let is_empty p =
    !p = []

  let push p x =
    p := x :: !p

  let pop p =
    match !p with
    | [] -> raise Not_found
    | x::r -> p := r; x

  let rev_append f p1 p2 =
    if not (is_empty p1) then begin
      let x = pop p1 in
      push p2 x;
      f p1 p2
    end
]]
*)

(** Code *)

Definition create : val :=
  VFun 'u :=
   val_ref 'nil.

Definition is_empty : val :=
  VFun 'p :=
    val_get 'p '= 'nil.

Definition push : val :=
  VFun 'p 'x :=
   'p ':= ('x ':: (val_get 'p)).

Definition pop : val :=
  VFun 'p :=
   Let 'q := val_get 'p in
   Match 'q With
   '| 'nil '=> 'Fail
   '| 'x ':: 'r '=> ('p ':= 'r) '; 'x
   End.

Definition rev_append : val :=
  VFix 'f 'p1 'p2 :=
    If_ 'not (is_empty 'p1) Then
       Let 'x := pop 'p1 in
       push 'p2 'x ';
       'f 'p1 'p2
    End.

(** Representation predicate *)

Definition Stack `{Enc A} (L:list A) (p:loc) : hprop :=
  p ~~> L.

(** Verification *)

Lemma Triple_create : forall `{Enc A},
  TRIPLE (create '())
    PRE \[]
    POST (fun p => (p ~> Stack (@nil A))).
Proof using.
  xwp. xval nil. xapp. hsimpl.
Qed.

Hint Extern 1 (Register_Spec create) => Provide @Triple_create.

Lemma Triple_is_empty : forall `{Enc A} (p:loc) (L:list A),
  TRIPLE (is_empty p)
    PRE (p ~> Stack L)
    POST (fun (b:bool) => \[b = isTrue (L = nil)] \* p ~> Stack L).
Proof using.
  xwp. xunfold Stack. xapp. xval nil.
  xapp~ @Triple_eq_r. hsimpl*.
Qed.

Hint Extern 1 (Register_Spec is_empty) => Provide @Triple_is_empty.

Lemma Triple_push : forall `{Enc A} (p:loc) (x:A) (L:list A),
  TRIPLE (push p (``x))
    PRE (p ~> Stack L)
    POST (fun (u:unit) => (p ~> Stack (x::L))).
Proof using.
  xwp. xunfold Stack. xapp. xval (x::L). xapp. hsimpl.
Qed.

Hint Extern 1 (Register_Spec push) => Provide @Triple_push.

Lemma Triple_pop : forall `{Enc A} (p:loc) (L:list A),
  L <> nil ->
  TRIPLE (pop p)
    PRE (p ~> Stack L)
    POST (fun (x:A) => \exists L', \[L = x::L'] \* (p ~> Stack L')).
Proof using.
  introv N. xwp. xunfold Stack. xapp.
  applys xmatch_lemma_list.
  { intros HL. xfail. }
  { intros X L' HL. xapp. xval. hsimpl~. }
Qed.

Hint Extern 1 (Register_Spec pop) => Provide @Triple_pop.

Opaque Stack.

Lemma Triple_rev_append : forall `{Enc A} (p1 p2:loc) (L1 L2:list A),
  TRIPLE (rev_append p1 p2)
    PRE (p1 ~> Stack L1 \* p2 ~> Stack L2)
    POST (fun (u:unit) => p1 ~> Stack nil \* p2 ~> Stack (rev L1 ++ L2)).
Proof using.
  intros. gen p1 p2 L2. induction_wf IH: (@list_sub A) L1. intros.
  xwp. xapp. xapp. xif ;=> C.
  { (* case cons *)
    xapp~ ;=> x L1' E. xapp. xapp. { subst*. } hsimpl. subst. rew_list~. }
  { (* case nil *)
    xval tt. hsimpl~. subst. rew_list~. }
Qed.

Hint Extern 1 (Register_Spec rev_append) => Provide @Triple_rev_append.

End Stack.



(* ********************************************************************** *)
(* * Stack with length *)

(** Implementation of a stack with a size as a record made of
    a list and a size field *)

Module Stackn.

(** OCaml syntax
[[
  type 'a lstack = { data : 'a list; size : int }

  let create () =
    { data = []; size = 0 }

  let is_empty p =
    p.size = 0

  let push p x =
    p.data <- x :: p.data;
    p.size <- p.size + 1

  let pop p =
    match !p.data with
    | [] -> raise Not_found
    | x::r -> 
        p.data <- r;
        p.size <- p.size - 1;
        x

   let clear p =  
     p.data <- [];
     p.size <- 0

   let concat p1 p2 =
     p1.data <- p1.data @ p2.data;
     p1.size <- p1.size + p2.size;
     clear p2
]]
*)

(** Source code *)

Definition data : field := 0%nat.
Definition size : field := 1%nat.

Definition create : val :=
  VFun 'u :=
    New`{ data := ('nil%val); size := 0 }.

Definition is_empty : val :=
  VFun 'p :=
    'p'.size '= 0.

Definition val_push : val :=
  VFun 'p 'x :=
   Set 'p'.data ':= ('x ':: 'p'.data) ';
   Set 'p'.size ':= ('p'.size '+ 1).

Definition val_pop : val :=
  VFun 'p :=
   Let 'q := 'p'.data in 
   Match 'q With (* LATER: allow inline *)
   '| 'nil '=> 'Fail
   '| 'x ':: 'r '=> 
       Set 'p'.data ':= 'r ';
       Set 'p'.size ':= ('p'.size '- 1) ';
       'x
   End.

(** Representation predicate *)

Definition Stackn `{Enc A} (L:list A) (p:loc) : hprop :=
  p ~> Record`{ data := L; size := LibListZ.length L }.


(** Verification *)

Lemma Triple_create : forall `{Enc A},
  TRIPLE (create '())
    PRE \[]
    POST (fun p => (p ~> Stackn (@nil A))).
Proof using.
  xwp. xunfold Stackn. xnew (>> (@nil A) 0). skip. (* TODO *) intros p. hsimpl.
Qed.

Lemma Triple_is_empty : forall `{Enc A} (p:loc) (L:list A),
  TRIPLE (is_empty p)
    PRE (p ~> Stackn L)
    POST (fun (b:bool) => \[b = isTrue (L = nil)] \* p ~> Stackn L).
Proof using.
  xwp. xunfold Stackn. xapp. xapp~. hsimpl.
  rewrite* LibListZ_length_zero_eq_eq_nil.
Qed.

Lemma Triple_push : forall `{Enc A} (p:loc) (x:A) (L:list A),
  TRIPLE (val_push p (``x))
    PRE (p ~> Stackn L)
    POST (fun (u:unit) => (p ~> Stackn (x::L))).
Proof using.
  xwp. xunfold Stackn. xapp. xval (x::L). xappn.
  hsimpl. (* LATER: hsimpl could do xrecord_eq *) 
  xrecord_eq. rew_list; math.
Qed.

Lemma Triple_pop : forall `{Enc A} (p:loc) (L:list A),
  L <> nil ->
  TRIPLE (val_pop p)
    PRE (p ~> Stackn L)
    POST (fun (x:A) => \exists L', \[L = x::L'] \* (p ~> Stackn L')).
Proof using.
  introv N. xwp. xunfold Stackn. xapp.
  applys xmatch_lemma_list.
  { intros HL. xfail. }
  { intros X L' HL. xappn. xval. hsimpl*. 
    (* LATER:  hsimpl could do xrecord_eq *) 
    xrecord_eq. subst; rew_list; math. }
Qed.

End Stackn.




