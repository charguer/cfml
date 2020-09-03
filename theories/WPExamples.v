(**

This file provides examples of proofs manipulating characteristic formula
in weakest-precondition form, in lifted Separation Logic,
as defined in [WPLifted.v].

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)


Set Implicit Arguments.
Generalizable Variables A B.
From Sep Require Import Example.

(* TODO *)
Lemma himpl_trans' : forall (H1 H2 H3:hprop),
  H2 ==> H3 ->
  H1 ==> H2 ->
  H1 ==> H3.
Proof using. introv M1 M2. applys* himpl_trans. Qed.




(* ---------------------------------------------------------------------- *)
(** If-val test *)

Definition example_ifval : val :=
  Fun 'u :=
    If_ true Then 0 Else 1.

Lemma Triple_example_ifval :
  TRIPLE (example_ifval tt)
    PRE \[]
    POST (fun r => \[ r = 0 ]).
Proof using.
  xwp. dup.
  { xval. xif ;=> C; tryfalse. xval. xsimpl. auto. }
  { xif ;=> C; tryfalse. xvals*. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Incr *)

Definition val_incr : val :=
  Fun 'p :=
   'p ':= ((val_get 'p) '+ 1).

(* VARIANT:
  Fun 'p :=
    Let 'n := val_get 'p in
   'p ':= ('n '+ 1).
*)

Lemma Triple_incr : forall (p:loc) (n:int),
  TRIPLE (val_incr p)
    PRE (p ~~> n)
    POST (fun (r:unit) => (p ~~> (n+1))).
Proof using.
  xwp. xappn. xsimpl~.
Qed.

(*
Lemma Triple_incr_frame : forall (p1 p2:loc) (n1 n2:int),
  TRIPLE (val_incr p1)
    PRE (p1 ~~> n1 \* p2 ~~> n2)
    POST (fun (r:unit) => (p1 ~~> (n1+1) \* p2 ~~> n2)).
Proof using.
Qed.
*)

(* TODO SHOULD BE:

  xtriple.
  xlet. { xapp. xapplys triple_get. }
  xpull ;=> ? ->.
  xlet. { xapp. xapplys triple_add. }
  xpull ;=> ? ->.
  xapp. xapplys triple_set. auto.

then just:

  xtriple.
  xapp.
  xapp.
  xapp.

*)

Hint Extern 1 (Register_Spec (val_incr)) => Provide Triple_incr.



(* ********************************************************************** *)
(* * Let *)

Definition xlet_test : val :=
  Fun 'x :=
     Let 'p := 3 in
     'p.

Lemma xlet_lemma' : forall A1 (EA1: protect (Enc A1)) H A (EA:Enc A) (Q:A->hprop) (F1:Formula) (F2of:forall A2 (EA2:Enc A2),A2->Formula),
  (H ==> F1 _ (EA1 : Enc A1) (fun (X:A1) => ^(F2of _ (EA1 : Enc A1) X) Q)) ->
  H ==> ^(Wpgen_let F1 (@F2of)) Q.
Proof using. introv M. applys MkStruct_erase. xsimpl* A1 EA1. Qed.

Lemma Triple_xlet_test : forall (x:unit),
  TRIPLE (xlet_test x)
    PRE \[]
    POST (fun (r:int) => \[r = 3]).
Proof using.
  xwp.
  (*   notypeclasses refine (xlet_lemma _ _ _ _ _). *)
  eapply xlet_lemma'.
  xval 3.
  xvals~.
Qed.


(* ********************************************************************** *)
(* * Point *)

Module Point.
Implicit Type p : loc.
Implicit Type x y k : int.

Definition X : field := 0%nat.
Definition Y : field := 1%nat.
Definition K : field := 2%nat.

Definition Point (x y:int) (p:loc) : hprop :=
  \exists k, p ~> Record`{ X := x; Y := y; K := k } \* \[ k = x + y ].


Definition val_move_X : val :=
  Fun 'p :=
   Set 'p'.X ':= ('p'.X '+ 1) ';
   Set 'p'.K ':= ('p'.K '+ 1).


Lemma Triple_move_X : forall p x y,
  TRIPLE (val_move_X p)
    PRE (Point x y p)
    POST (fun (_:unit) => (Point (x+1) y p)).
Proof using.
  xwp.
  xunfolds Point ;=> k Hk.
  xappn. xsimpl. math.
Qed.


End Point.




(*
  course -> For recursive predicate: would be useful to recall the duality between
  `Fixpoint` and `Inductive` for defining predicates, taking the example of `In` and `Forall` on lists.
*)



(* ********************************************************************** *)
(* * Mutable lists, without points-to notation *)


Module MListNopoints.


Definition Nil : val := val_constr "nil" nil.
Definition Cons `{Enc A} (V:A) (p:loc) : val := val_constr "cons" (``V::``p::nil).


Fixpoint MList A `{EA:Enc A} (L:list A) (p:loc) : hprop :=
  \exists v, p ~~> v \*
  match L with
  | nil => \[v = Nil]
  | x::L' => \exists p', \[v = Cons x p'] \* (MList L' p')
  end.

Lemma MList_unfold :
  MList = fun A `{EA:Enc A} (L:list A) (p:loc) =>
    \exists v, p ~~> v \*
    match L with
    | nil => \[v = Nil]
    | x::L' => \exists p', \[v = Cons x p'] \* (MList L' p')
    end.
Proof using. applys fun_ext_4; intros A EA L p. destruct L; auto. Qed.

Lemma MList_nil_eq : forall A `{EA:Enc A} (p:loc),
  (MList nil p) = (p ~~> Nil).
Proof using.
  intros. xunfold MList. applys himpl_antisym.
  { xpull ;=> ? ->. auto. }
  { xsimpl~. }
Qed.



(* ---------------------------------------------------------------------- *)
(** Length *)

Definition val_mlist_length : val :=
  Fix 'f 'p :=
    Let 'v := val_get 'p in
    Match 'v With
    '| 'Cstr "nil" '=> 0
    '| 'Cstr "cons" 'x 'q '=> 1 '+ 'f 'q
    End.

Lemma Triple_mlist_length_1 : forall A `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (val_mlist_length p)
    PRE (MList L p)
    POST (fun (r:int) => \[r = length L] \* MList L p).
Proof using.
  intros. gen p. induction_wf IH: (@list_sub A) L. intros.
  xwp.
  xlet.
  (* xunfold *)
  pattern MList at 1. rewrite MList_unfold. xpull ;=> v. xapp.
  (* xcase *)
  applys xcase_lemma0 ;=> E1.
  { destruct L as [|x L']; xpull.
    { intros ->. applys~ @xval_lemma 0. xsimpl. rew_list~. rewrite~ MList_nil_eq. xsimpl. }
    { intros q ->. tryfalse. } }
  { applys xcase_lemma2.
    { intros x q E.
      destruct L as [|x' L']; xpull.
      { intros ->. tryfalse. }
      { intros q' E'. subst v. rewrite enc_val_eq in *. inverts E.
        xapp* IH. xsimpl. xapp.
        (* done *)
        pattern MList at 2. rewrite MList_unfold. xsimpl*.  (* rew_list; math.*) } }
    { intros N. destruct L as [|x L']; xpull.
      { intros ->. rewrite enc_val_eq in *. unfolds Nil. false. }
      { intros q ->. rewrite enc_val_eq in *. unfolds @Cons. false. } } }
Qed.

End MListNopoints.


(* ********************************************************************** *)
(* * Basic *)

Module Basic.



(* ---------------------------------------------------------------------- *)
(** Negation *)

Definition val_myneg :=
  Fun 'b :=
    If_ 'b '= true Then false Else true.

Lemma Triple_decr : forall (b:bool),
  TRIPLE (val_myneg b)
    PRE \[]
    POST (fun (r:bool) => \[r = !b]).
Proof using.
  xwp.
(*
  (* TODO fix xapp *)
  xlet. xapp_debug. lets K: (>> Spec b true). typeclass. apply K.
   unfold protect. xsimpl.
  intros ? ->.
  xif ;=> C.
  { subst. xvals*. }
  { xvals. destruct b; auto_false. }
Qed.
*)
Abort.


(* ---------------------------------------------------------------------- *)
(** Disequality test  -- DEPRECATED

Definition val_myneq :=
  Fun 'm 'n :=
    val_myneg ('m '= 'n).

Lemma Triple_myneq : forall (v1 v2:val),
  TRIPLE (val_myneq v1 v2)
    PRE \[]
    POST (fun (r:bool) => \[r = isTrue (v1 <> v2)]).
Proof using.
  xwp.
  (* TODO fix xapp *)
  xlet. xapp_debug. lets K: (>> Spec v1 v2). typeclass. apply K.
   unfold protect. xsimpl.
 xapp Triple_eq. xapps. xsimpl ;=> ? ->. rew_isTrue~.
Qed.
*)

(*

(* ---------------------------------------------------------------------- *)
(** Swap *)

Definition val_swap :=
  Fun 'p 'q :=
    Let 'x := val_get 'p in
    Let 'y := val_get 'q in
    val_set 'p 'y ;;;
    val_set 'q 'x.

Lemma Triple_swap_neq : forall A1 A2 `{EA1:Enc A1} `{EA2:Enc A2} (v:A1) (w:A2) p q,
  Triple (val_swap ``p ``q)
    PRE (p ~~> v \* q ~~> w)
    POST (fun (r:unit) => p ~~> w \* q ~~> v).
Proof using.
  xtriple. xapps. xapps. xapps. xapps. xsimpl~.
Qed.

Lemma Triple_swap_eq : forall A1 `{EA1:Enc A1} (v:A1) p,
  Triple (val_swap ``p ``p)
    PRE (p ~~> v)
    POST (fun (r:unit) => p ~~> v).
Proof using.
  xtriple. xapps. xapps. xapps. xapps. xsimpl~.
Qed.


(* ---------------------------------------------------------------------- *)
(** Succ using incr *)

Definition val_succ_using_incr :=
  Fun 'n :=
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
  (* not possible: applys mklocal_erase. unfold cf_val. xsimpl. *)
  xvals~.
Qed.


(* ---------------------------------------------------------------------- *)
(** Basic let-binding example *)

Definition val_example_let :=
  Fun 'n :=
    Let 'a := 'n '+ 1 in
    Let 'b := 'n '- 1 in
    'a '+ 'b.

Lemma Triple_val_example_let : forall n,
  Triple (val_example_let n)
    PRE \[]
    POST (fun r => \[r = 2*n]).
Proof using.
  xtriple. xapps. xapps. xapp. xsimpl. math.
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
  Fun 'n :=
    Let 'k := 'n '+ 1 in
    Let 'i := 'ref 'k in
    val_incr 'i ;;;
    '!'i.

Lemma Triple_val_example_one_ref : forall n,
  Triple (val_example_one_ref n)
    PRE \[]
    POST (fun r => \[r = n+2]).
Proof using.
  xtriple. xapps. xapps ;=> r. xapp~. xapp~. xsimpl. math.
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
  Fun 'n :=
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
  xsimpl. math.
Qed.

*)

End Basic.



(* ********************************************************************** *)
(* * Factorial *)

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


(* EXO:

   mem
   count
   in-place reversal
   cps-append (bonus example)
   split
   combine
   basic sorting on list of integers, e.g. merge sort, insertion sort

*)


(* TODO: find a way using uconstr to support the syntax:
    [induction_wf IH: list_sub L1] *)



















