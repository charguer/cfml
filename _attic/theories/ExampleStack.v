(**

This file provides examples of the verification of a mutable stack,
and of a mutable stack with size available in constant time.
using CFML 2.0.

See examples/Stack for corresponding formalization using the OCaml front-end.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)


Set Implicit Arguments.
Generalizable Variables A B.
From Sep Require Import Example.


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Stack as a reference on a list *)

Module Stack.

(* ********************************************************************** *)
(** ** Ocaml syntax *)

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

(* ********************************************************************** *)
(** ** Embedded syntax *)

Definition create : val :=
  Fun 'u :=
   val_ref 'nil.

Definition is_empty : val :=
  Fun 'p :=
    val_get 'p '= 'nil.

Definition push : val :=
  Fun 'p 'x :=
   'p ':= ('x ':: (val_get 'p)).

Definition pop : val :=
  Fun 'p :=
   Let 'q := val_get 'p in
   Match 'q With
   '| 'nil '=> 'Fail
   '| 'x ':: 'r '=> ('p ':= 'r) '; 'x
   End.

Definition rev_append : val :=
  Fix 'f 'p1 'p2 :=
    If_ 'not (is_empty 'p1) Then
       Let 'x := pop 'p1 in
       push 'p2 'x ';
       'f 'p1 'p2
    End.


(* ********************************************************************** *)
(** ** Representation predicate *)

(** [p ~> Stack L] relates a pointer [p] with the list [L] made of
    the elements in the stack. *)

Definition Stack A `{Enc A} (L:list A) (p:loc) : hprop :=
  p ~~> L.


(* ********************************************************************** *)
(** ** Verification *)

Lemma Triple_create : forall A `{Enc A},
  TRIPLE (create '())
    PRE \[]
    POST (fun p => (p ~> Stack (@nil A))).
Proof using.
  xwp. xval. xapp. xsimpl.
Qed.

Hint Extern 1 (Register_Spec create) => Provide Triple_create.

Lemma Triple_is_empty : forall A `{Enc A} (p:loc) (L:list A),
  TRIPLE (is_empty p)
    PRE (p ~> Stack L)
    POST (fun (b:bool) => \[b = isTrue (L = nil)] \* p ~> Stack L).
Proof using.
  xwp. xunfold Stack. xapp. xval. xapp~. xsimpl*.
Qed.

Hint Extern 1 (Register_Spec is_empty) => Provide Triple_is_empty.

Lemma Triple_push : forall A `{Enc A} (p:loc) (x:A) (L:list A),
  TRIPLE (push p (``x))
    PRE (p ~> Stack L)
    POST (fun (u:unit) => (p ~> Stack (x::L))).
Proof using.
  xwp. xunfold Stack. xapp. xval. xapp. xsimpl.
Qed.

Hint Extern 1 (Register_Spec push) => Provide Triple_push.

Lemma Triple_pop : forall A `{Enc A} (p:loc) (L:list A),
  L <> nil ->
  TRIPLE (pop p)
    PRE (p ~> Stack L)
    POST (fun (x:A) => \exists L', \[L = x::L'] \* (p ~> Stack L')).
Proof using.
  introv N. xwp. xunfold Stack. xapp.
  applys xmatch_lemma_list.
  { intros HL. xfail. }
  { intros X L' HL. xapp. xval. xsimpl~. }
Qed.

Hint Extern 1 (Register_Spec pop) => Provide Triple_pop.

Opaque Stack.

Lemma Triple_rev_append : forall A `{Enc A} (p1 p2:loc) (L1 L2:list A),
  TRIPLE (rev_append p1 p2)
    PRE (p1 ~> Stack L1 \* p2 ~> Stack L2)
    POST (fun (u:unit) => p1 ~> Stack (@nil A) \* p2 ~> Stack (rev L1 ++ L2)).
Proof using.
  intros. gen p1 p2 L2. induction_wf IH: (@list_sub A) L1. intros.
  xwp. xapp. xapp. xif ;=> C.
  { (* case cons *)
    xapp~ ;=> x L1' E. xapp. xapp. { subst*. } xsimpl. subst. rew_list~. }
  { (* case nil *)
    xval. xsimpl~. subst. rew_list~. }
Qed.

Hint Extern 1 (Register_Spec rev_append) => Provide Triple_rev_append.

End Stack.



(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Stack as a record with a list and a size field *)

Module Stackn.

(* ********************************************************************** *)
(** ** OCaml syntax *)

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


(* ********************************************************************** *)
(** ** Embedded code *)

Definition data : field := 0%nat.
Definition size : field := 1%nat.

Definition create : val :=
  Fun 'u :=
    New`{ data := ('nil%val); size := 0 }.

Definition is_empty : val :=
  Fun 'p :=
    'p'.size '= 0.

Definition push : val :=
  Fun 'p 'x :=
   Set 'p'.data ':= 'x ':: 'p'.data ';
   Set 'p'.size ':= 'p'.size '+ 1.

Definition pop : val :=
  Fun 'p :=
   Let 'q := 'p'.data in
   Match 'q With (* LATER: allow inline *)
   '| 'nil '=> 'Fail
   '| 'x ':: 'r '=>
       Set 'p'.data ':= 'r ';
       Set 'p'.size ':= 'p'.size '- 1 ';
       'x
   End.



(* ********************************************************************** *)
(** ** Representation predicate *)

(** [p ~> Stackn L] relates a pointer [p] with the list [L] made of
    the elements in the stack. *)

Definition Stackn A `{Enc A} (L:list A) (p:loc) : hprop :=
  p ~> Record`{ data := L; size := LibListZ.length L }.

Lemma Stackn_eq : forall (p:loc) A (EA:Enc A) (L:list A),
  p ~> Stackn L =
  p ~> Record`{ data := L; size := LibListZ.length L }.
Proof using. auto. Qed.


(* ********************************************************************** *)
(** ** Verification *)

Lemma Triple_create : forall A `{Enc A},
  TRIPLE (create '())
    PRE \[]
    POST (fun p => (p ~> Stackn (@nil A))).
Proof using.
  xwp. xunfold Stackn. xnew (>> (@nil A) 0) ;=> p. xsimpl.
Qed.

Lemma Triple_is_empty : forall A `{Enc A} (p:loc) (L:list A),
  TRIPLE (is_empty p)
    PRE (p ~> Stackn L)
    POST (fun (b:bool) => \[b = isTrue (L = nil)] \* p ~> Stackn L).
Proof using.
  xwp. xunfold Stackn. xapp. xapp~. xsimpl.
  rewrite* LibListZ.length_zero_eq_eq_nil.
Qed.

Lemma Triple_push : forall A `{Enc A} (p:loc) (x:A) (L:list A),
  TRIPLE (push p (``x))
    PRE (p ~> Stackn L)
    POST (fun (u:unit) => (p ~> Stackn (x::L))).
Proof using.
  xwp. xunfold Stackn. xapp. xval. xappn. xsimpl*.
Qed.

Lemma Triple_pop : forall A `{Enc A} (p:loc) (L:list A),
  L <> nil ->
  TRIPLE (pop p)
    PRE (p ~> Stackn L)
    POST (fun (x:A) => \exists L', \[L = x::L'] \* (p ~> Stackn L')).
Proof using.
  introv N. xwp. xunfold Stackn. xapp.
  applys xmatch_lemma_list.
  { intros HL. xfail. }
  { intros X L' HL. xappn. xval. xsimpl*. }
Qed.



(* ####################################################### *)
(** * Stack exercises *)

(** Hints:
    - [xunfold Stackn] to unfold all
    - [xchange Stackn_eq] to unfold one
    - [xchange <- Stackn_eq] to fold one
    - [xchange (Stackn_eq p)] to unfold the one at pointer [p]
    - [xchange <- (Stackn_eq p)] to fold the one at pointer [p]
    - [xchanges] to invoke [xsimpl] subsequently
*)

(*
Module ExoStack.
Import ExampleStack.Stackn.
*)

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
  Fun 'p :=
    Set 'p'.data ':= 'nil ';
    Set 'p'.size ':= ``0.

Lemma Triple_clear : forall A `{Enc A} (p:loc) (L:list A),
  TRIPLE (clear p)
    PRE (p ~> Stackn L)
    POST (fun (u:unit) => p ~> Stackn (@nil A)).
Proof using.
  (* SOLUTION *) xwp. xunfold Stackn. xval. xapp. xapp. xsimpl. (* /SOLUTION *)
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
  Fun 'p1 'p2 :=
    Set 'p1'.data ':= 'p1'.data '++ 'p2'.data ';
    Set 'p1'.size ':= 'p1'.size '+ 'p2'.size ';
    clear 'p2.

Lemma Triple_concat : forall A `{Enc A} (p1 p2:loc) (L1 L2:list A),
  TRIPLE (concat p1 p2)
    PRE (p1 ~> Stackn L1 \* p2 ~> Stackn L2)
    POST (fun (u:unit) => (* SOLUTION *) p1 ~> Stackn (L1 ++ L2) \* p2 ~> Stackn (@nil A) (* /SOLUTION *)).
Proof using.
  (* SOLUTION *)
  xwp. xunfold Stackn. xapp. xapp. xapp. xapp. xapp. xapp. xapp.
  xapp. xchange <- (Stackn_eq p1). { rew_listx. auto. }
  xchange <- (Stackn_eq p2). xapp. xsimpl.
  (* /SOLUTION *)
Qed.

(*
End ExoStack.
*)

End Stackn.