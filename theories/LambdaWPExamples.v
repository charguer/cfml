(**

This file defines tactics for manipulating characteristic formula 
in weakest-precondition form, in lifted Separation Logic,
as defined in [LambdaWPLifted.v].

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
From Sep Require Export LambdaWPTactics.
Generalizable Variables A B.

Import NotationForVariables NotationForTerms.
Open Scope val_scope.
Open Scope pat_scope.
Open Scope trm_scope.


(* ********************************************************************** *)
(* * Demo *)



(* ********************************************************************** *)
(* * Point *)

Module Factorial.

Parameter facto : int -> int.
Parameter facto_zero : facto 0 = 1.
Parameter facto_one : facto 1 = 1.
Parameter facto_succ : forall n, n >= 1 -> facto n = n * facto(n-1).

(*

  let rec facto_rec n =
    if n <= 1 then 1 else n * facto_rec (n-1)

  let facto_ref_rec_up n =
    let r = ref 1 in
    let rec f x =
      if x <= n
        then r := !r * x; f (x+1) in
    f 1;
    !r

  let facto_ref_rec_down n =
    let r = ref 1 in
    let rec f n =
      if n > 1
        then r := !r * n; f (n-1) in
    f n; 
    !r

  let facto_for n =
    let r = ref 1 in
    for x = 1 to n do
      r := !r * x;
    done;
    !r

  let facto_for_down n =
    let r = ref 1 in
    for x = 0 to n-1 do 
      r := !r * (n-x);
    done;
    !r

  let facto_for_downto n =
    let r = ref 1 in
    for x = n downto 1 do 
      r := !r * x;
    done;
    !r

  let facto_for_downto2 n =
    let r = ref 1 in
    for x = n downto 2 do 
      r := !r * x;
    done;
    !r

  let facto_while_up n =
    let r = ref 1 in
    let x = ref 1 in
    while get x <= n do
      r := !r * !x;
      incr x;
    done;
    !r

  let facto_while_down n =
    let r = ref 1 in
    let x = ref n in
    while get x > 1 do
      r := !r * !x;
      decr x;
    done;
    !r
*)

End Factorial.



(* ********************************************************************** *)
(* * Point *)

Module Point.

Definition X : field := 0%nat.
Definition Y : field := 1%nat.
Definition S : field := 2%nat.

(*
Definition Point (p:loc) : hprop :=
  \exists x y s, p ~> Record`{ X := x; Y := y; S := s } \* [ s = x + y ].
*)


End Point.


(* ********************************************************************** *)
(* * Mutable lists *)


Module MList.

(*
  - For recursive predicate: would be useful to recall the duality between
   `Fixpoint` and `Inductive` for defining predicates, taking the example of `In` and `Forall` on lists.
*)
(*
    ```
       Fixpoint MList A `{EA:Enc A} (L:list A) (p:loc) : hprop :=
         Hexists v, p ~> v  \*
         match L with
         | nil => \[v = Nil]
         | x::L => Hexists p', \[v = Cons(x,p')] \* (p' ~> MList L')
         end.
    ```


   length : using recursion + using loop
   copy : using recursion + using loop
   append (destructive, or non-destructive)
   mem
   count
   in-place reversal
   cps-append (bonus example)
   split 
   combine  
   basic sorting on list of integers, e.g. merge sort, insertion sort

*)

End MList.


(* ********************************************************************** *)
(* * Basic *)

Module Basic.

(* ---------------------------------------------------------------------- *)
(** Incr *)

Definition val_incr : val :=
  ValFun 'p :=
   'p ':= ((val_get 'p) '+ 1).

(* VARIANT:
  ValFun 'p :=
    Let 'n := val_get 'p in
   'p ':= ('n '+ 1).
*)

Lemma Triple_incr : forall (p:loc) (n:int),
  TRIPLE (val_incr p)
    PRE (p ~~> n)
    POST (fun (r:unit) => (p ~~> (n+1))).
Proof using.
  intros.
  (* optional simplification step to reveal [trm_apps] *)
  simpl combiner_to_trm.
  (* xtriple *)
  applys xtriple_lemma_funs.
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  simpl.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xlet *)
  eapply Local_erase.
  (* xapps *)
  applys @xapps_lemma. { applys Triple_get. } hsimpl.
  (* return *)
  applys @xreturn_lemma_val.
  (* xapp *)
  applys @xapp_lemma. { eapply @Triple_set. } hsimpl.
  (* done *) 
  auto.
Qed.

Lemma Triple_incr_frame : forall (p1 p2:loc) (n1 n2:int),
  TRIPLE (val_incr p1)
    PRE (p1 ~~> n1 \* p2 ~~> n2)
    POST (fun (r:unit) => (p1 ~~> (n1+1) \* p2 ~~> n2)).
Proof using.
  skip.
Qed.

(* TODO SHOULD BE:

  xtriple.
  xlet. { xapp. xapplys triple_get. }
  hpull ;=> ? ->.
  xlet. { xapp. xapplys triple_add. }
  hpull ;=> ? ->.
  xapp. xapplys triple_set. auto.

then just:

  xtriple.
  xapp.
  xapp.
  xapp.

*)

(*

(* ---------------------------------------------------------------------- *)
(** Swap *)

Definition val_swap :=
  ValFun 'p 'q :=
    Let 'x := val_get 'p in
    Let 'y := val_get 'q in
    val_set 'p 'y ;;;
    val_set 'q 'x.

Lemma Triple_swap_neq : forall A1 A2 `{EA1:Enc A1} `{EA2:Enc A2} (v:A1) (w:A2) p q,
  Triple (val_swap ``p ``q)
    PRE (p ~~> v \* q ~~> w)
    POST (fun (r:unit) => p ~~> w \* q ~~> v).
Proof using.
  xtriple. xapps. xapps. xapps. xapps. hsimpl~.
Qed.

Lemma Triple_swap_eq : forall A1 `{EA1:Enc A1} (v:A1) p,
  Triple (val_swap ``p ``p)
    PRE (p ~~> v)
    POST (fun (r:unit) => p ~~> v).
Proof using.
  xtriple. xapps. xapps. xapps. xapps. hsimpl~.
Qed.


(* ---------------------------------------------------------------------- *)
(** Succ using incr *)

Definition val_succ_using_incr :=
  ValFun 'n :=
    Let 'p := val_ref 'n in
    val_incr 'p ;;;
    Let 'x := val_get 'p in
    'x.

Lemma triple_succ_using_incr : forall n,
  triple (val_succ_using_incr n)
    \[]
    (fun r => \[r = n+1]).
Proof using.
  xtriple. xapp as p. intros; subst. xapp~. intros _. xapps~.
  (* not possible: applys local_erase. unfold cf_val. hsimpl. *)
  xvals~.
Qed.



(* ---------------------------------------------------------------------- *)
(** Basic let-binding example *)

Definition val_example_let :=
  ValFun 'n :=
    Let 'a := 'n '+ 1 in
    Let 'b := 'n '- 1 in
    'a '+ 'b.

Lemma Triple_val_example_let : forall n,
  Triple (val_example_let n)
    PRE \[]
    POST (fun r => \[r = 2*n]).
Proof using.
  xtriple. xapps. xapps. xapp. hsimpl. math.
Qed.


(* ---------------------------------------------------------------------- *)
(** Basic let-binding example *)

(*
  let val_example_one_ref n =
    let i = ref 0 in
    incr i;
    !i
*)

Definition val_example_one_ref :=
  ValFun 'n :=
    Let 'k := 'n '+ 1 in
    Let 'i := 'ref 'k in
    val_incr 'i ;;;
    '!'i.

Lemma Triple_val_example_one_ref : forall n,
  Triple (val_example_one_ref n)
    PRE \[]
    POST (fun r => \[r = n+2]).
Proof using.
  xtriple. xapps. xapps ;=> r. xapp~. xapp~. hsimpl. math.
Qed.


(* ---------------------------------------------------------------------- *)
(** Basic let-binding two ref *)

(*
  let val_example_two_ref n =
    let i = ref 0 in
    let r = ref n in
    decr r;
    incr i;
    r := !i + !r;
    !i + !r
*)

Definition val_example_two_ref :=
  ValFun 'n :=
    Let 'i := 'ref 0 in
    Let 'r := 'ref 'n in
    val_decr 'r ;;;
    val_incr 'i ;;;
    Let 'i1 := '!'i in
    Let 'r1 := '!'r in
    Let 's := 'i1 '+ 'r1 in
    'r ':= 's ;;;
    Let 'i2 := '!'i in
    Let 'r2 := '!'r in
    'i2 '+ 'r2.

Lemma Triple_val_example_two_ref : forall n,
  Triple (val_example_two_ref n)
    PRE \[]
    POST (fun r => \[r = n+1]).
Proof using.
  xtriple. xapp ;=> i. xapp ;=> r.
  xapp~. xapp~. xapps. xapps. xapps. xapps~.
  xapps. xapps. xapps.
  hsimpl. math.
Qed.

*)

End Basic.


(* ********************************************************************** *)
(* * Test *)

Module Test.

(* ---------------------------------------------------------------------- *)
(* ** Case without variables *)

Definition val_test1 : val :=
  ValFun 'p :=
    Case' 'p = pat_unit Then 'Fail Else 'Fail.

Lemma Triple_test1 : forall (p:loc),
  TRIPLE (val_test1 ``p)
    PRE \[]
    POST (fun (u:unit) => \[]).
Proof using.
  intros.
  (* xtriple *)
  applys xtriple_lemma_funs; try reflexivity. simpl.
Admitted.


(* ---------------------------------------------------------------------- *)
(* ** Case with 1 variable *)

Definition val_test2 : val :=
  ValFun 'p :=
    Case' 'p = 'x Then 'x Else 'Fail.

Lemma Triple_test2 : forall (p:loc),
  TRIPLE (val_test2 p)
    PRE \[]
    POST (fun (u:unit) => \[]).
Proof using.
  intros.
  (* xtriple *)
  applys xtriple_lemma_funs; try reflexivity. simpl.
Admitted.


(* ---------------------------------------------------------------------- *)
(* ** Match without variables *)


Definition val_test0 : val :=
  ValFun 'p :=
    Case' 'p = pat_unit Then 'Fail Else
    Case' 'p = pat_unit Then 'p Else 
    'Fail.

Lemma triple_test0 : forall (p:loc),
  TRIPLE (val_test0 p)
    PRE \[]
    POST (fun (u:unit) => \[]).
Proof using.
  intros.
  (* xtriple *)
  applys xtriple_lemma_funs; try reflexivity. simpl.
Admitted.


End Test.

(* ********************************************************************** *)
(* * Stack *)

Module Stack.

Definition val_is_empty : val :=
  ValFun 'p :=
    val_get 'p '= 'nil.

Definition val_empty : val :=
  ValFun 'u :=
   val_ref 'nil.

Definition val_push : val :=
  ValFun 'p 'x :=
   'p ':= ('x ':: (val_get 'p)).

Definition val_pop : val :=
  ValFun 'p :=
   (Let 'q := val_get 'p in
   Match 'q With
   '| 'nil '=> 'Fail
   '| 'x ':: 'r '=> ('p ':= 'r) '; 'x
   End).

Definition val_rev_append : val :=
  ValFix 'f 'p1 'p2 :=
    If_ val_is_empty 'p1 Then '() Else 
       Let 'x := val_pop 'p1 in
       val_push 'p2 'x ';
       'f 'p1 'p2.


Definition Stack `{Enc A} (L:list A) (p:loc) : hprop :=
  p ~~> L.


Lemma Triple_is_empty : forall `{Enc A} (p:loc) (L:list A),
  TRIPLE (val_is_empty p)
    PRE (p ~> Stack L)
    POST (fun (b:bool) => \[b = isTrue (L = nil)] \* p ~> Stack L).
Proof using.
  (* xtriple *)
  intros. applys xtriple_lemma_funs; try reflexivity; simpl.
  (* xunfold *)
  xunfold Stack.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xapps *)
  applys @xapps_lemma. { eapply @Triple_get. } hsimpl.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xval *)
  applys~ (xval_lemma nil).
  (* xapps *)
  applys @xapps_lemma_pure. { applys @Triple_eq_val. } hsimpl.
  (* done *)
  rewrite* @Enc_injective_value_eq_r.
Qed.

Lemma Triple_pop : forall `{Enc A} (p:loc) (L:list A),
  L <> nil ->
  TRIPLE (val_pop p)
    PRE (p ~> Stack L)
    POST (fun (x:A) => \exists L', \[L = x::L'] \* (p ~> Stack L')).
Proof using.
  introv N.
  (* xtriple *)
  applys xtriple_lemma_funs; try reflexivity; simpl.
  (* xunfold *)
  xunfold Stack.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xapps *)
  applys @xapps_lemma. { eapply @Triple_get. } hsimpl.
  (* Two ways of completing the proof *)
  dup.
  (* xcase with lemma for match list *)
  { applys xmatch_lemma_list.
    { intros HL. 
      (* xfail *)
      false. }
    { intros X L' HL. 
      (* xseq *)
      applys xseq_lemma.
      (* xapp *)
      applys @xapp_lemma. { applys @Triple_set. } hsimpl.
      (* xval *)
      applys~ xval_lemma.
      (* done *)
      hsimpl~. } }
  (* inlining the proof of xmatch_list *)
  { applys xcase_lemma0 ;=> E1.
    { destruct L; tryfalse. }
    { applys xcase_lemma2.
      2: { intros E. destruct L; rew_enc in *; tryfalse. }
      { intros x1 x2 E2. destruct L as [|x L']; rew_enc in *; tryfalse.
        inverts E2.
        (* xseq *)
        applys xseq_lemma.
        (* xapp *)
        applys @xapp_lemma. { applys @Triple_set. } hsimpl.
        (* xval *)
        applys~ xval_lemma.
        (* post *)
        hsimpl~. } } }
Qed.

Lemma Triple_empty : forall `{Enc A} (u:unit),
  TRIPLE (val_empty u)
    PRE \[]
    POST (fun p => (p ~> Stack (@nil A))).
Proof using.
  (* xtriple *)
  intros. applys xtriple_lemma_funs; try reflexivity; simpl.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xval *)
  applys~ (xval_lemma_val (@nil A)).
  (* xapp *)
  applys @xapp_lemma. { eapply @Triple_ref. } hsimpl.
  (* done *)
  auto.
Qed.

Lemma Triple_push : forall `{Enc A} (p:loc) (x:A) (L:list A),
  TRIPLE (val_push p (``x))
    PRE (p ~> Stack L)
    POST (fun (u:unit) => (p ~> Stack (x::L))).
Proof using.
  (* xtriple *)
  intros. applys xtriple_lemma_funs; try reflexivity; simpl.
  (* xunfold *)
  xunfold Stack.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xapps *)
  applys @xapps_lemma. { eapply @Triple_get. } hsimpl.
  (* xval *)
  applys~ (xval_lemma_val (x::L)).
  (* xapps *)
  applys @xapp_lemma. { eapply @Triple_set. } hsimpl. 
  (* done *)
  auto.
Qed.

Opaque Stack.

Lemma Triple_rev_append : forall `{Enc A} (p1 p2:loc) (L1 L2:list A),
  TRIPLE (val_rev_append p1 p2)
    PRE (p1 ~> Stack L1 \* p2 ~> Stack L2)
    POST (fun (u:unit) => p1 ~> Stack nil \* p2 ~> Stack (rev L1 ++ L2)).
Proof using.
  intros. gen p1 p2 L2. induction_wf IH: (@list_sub A) L1. intros.
  (* xtriple *)
  intros. applys xtriple_lemma_fixs; try reflexivity; simpl.
  (* xlet *)
  applys xlet_typed_lemma.
  (* xapps *)
  applys @xapps_lemma. { eapply @Triple_is_empty. } hsimpl.
  (* xif *)
  applys @xifval_lemma_isTrue ;=> C.
  (* case nil *)
  { (* xval *)
    applys~ (xval_lemma tt).
    (* done *)
    hsimpl. subst. rew_list~. }
  (* case cons *)
  { (* xlet-poly *)
    notypeclasses refine (xlet_lemma _ _ _ _ _).
    (* xapp *)
    applys @xapp_lemma. { applys @Triple_pop. eauto. } hsimpl ;=> x L1' E.
    (* xseq *)
    applys xseq_lemma.
    (* xapp *)
    applys @xapp_lemma. { applys @Triple_push. } hsimpl.
    (* xapp *)
    applys @xapp_lemma. { applys IH L1'. subst*. } hsimpl.
    (* done *)
    hsimpl. subst. rew_list~. }
Qed.


End Stack.



















