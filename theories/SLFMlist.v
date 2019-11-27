
(**

This file formalizes mutable list examples in CFML 2.0.
using a representation of lists as either null or a two-cell record.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import Example.
Generalizable Variables A B.
Open Scope heap_scope_ext.

Implicit Types p : loc.
Implicit Types n : int.


(* ******************************************************* *)

(** Hints:
    - [xwp] to begin the proof
    - [xapp] for applications, or [xappn] to repeat
    - [xif] for a case analysis
    - [xval] for a value
    - [xsimpl] to prove entailments
    - [auto], [math], [rew_list] to prove pure facts
      or just [*] after a tactic to invoke automation.
*)



(* ********************************************************************** *)
(* * Field names *)

Definition head : field := 0%nat.
Definition tail : field := 1%nat.


(* ********************************************************************** *)
(* * Towards a representation *)

(* ---------------------------------------------------------------------- *)
(** ** C-style datatype *)

(** Let's try to first formalize the C representation:
[[
    typedef struct node {
      item  head;
      node* tail;
    };
    // with node = null for the empty list
]]
*)

(* ---------------------------------------------------------------------- *)
(** ** Inductive presentation (does not work) *)

(** [p ~> MList L], (hypothetically) defined as an inductive predicate

[[

  -----------------
  null ~> MList nil

  p ~> Record`{ head := x; tail := p'}      p' ~> MList L'
  -------------------------------------------------------
                       p ~> MList (x::L')

]]

*)

(* ---------------------------------------------------------------------- *)
(** ** Recursive presentation *)

Module MListVal.

(** Recursive of [p ~> MList L], that is, [MList L p]. *)

Fixpoint MList (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists p', p ~> Record`{ head := x; tail := p'} \* (p' ~> MList L')
  end.

End MListVal.





(* ********************************************************************** *)
(* * Formalization of list cells *)

Notation "'MCell' x q" :=
  (Record`{ head := x; tail := q })
  (at level 19, x at level 0, q at level 0).


Lemma MCell_null : forall A `{EA:Enc A} (x:A) (p':loc),
  null ~> MCell x p' = \[False].
Proof using.
  intros. applys himpl_antisym.
  { xchange hRecord_not_null. simpl. unfold head. auto. } (* todo simplify *)
  { xpull. }
Qed.

Lemma MCell_not_null : forall (p:loc) A `{EA:Enc A} (x:A) (p':loc),
  p ~> MCell x p' ==+> \[p <> null].
Proof using.
  intros. tests C: (p = null). { xchange MCell_null. } { xsimpl~. }
Qed.

Lemma MCell_conflict : forall p1 p2 `{EA1:Enc A1} `{EA2:Enc A2} (x1 x2:A1) (y1 y2:A2),
  p1 ~> MCell x1 y1 \* p2 ~> MCell x2 y2 ==+> \[p1 <> p2].
(* TODO: two records with one common field have disjoint addresses *)
Admitted.

Arguments MCell_null : clear implicits.
Arguments MCell_not_null : clear implicits.
Arguments MCell_conflict : clear implicits.


(* ********************************************************************** *)
(* * Formalization of mutable lists with null pointers *)


(* ---------------------------------------------------------------------- *)
(* ** Representation *)

Fixpoint MList A `{EA:Enc A} (L:list A) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists (p':loc), p ~> MCell x p' \* p' ~> MList L'
  end.

(* (p ~> Record`{ head := x; tail := p' }) *)

(* ---------------------------------------------------------------------- *)
(* ** Lemmas *)

Section Properties.

Lemma MList_eq : forall (p:loc) A `{EA:Enc A} (L:list A),
  p ~> MList L =
  match L with
  | nil => \[p = null]
  | x::L' => \exists (p':loc), (p ~> Record`{ head := x; tail := p' }) \* (p' ~> MList L')
  end.
Proof using. intros. xunfold~ MList. destruct~ L. Qed.

Lemma MList_nil : forall p A `{EA:Enc A},
  (p ~> MList (@nil A)) = \[p = null].
Proof using. intros. xunfold~ MList. Qed.

Lemma MList_cons : forall p A `{EA:Enc A} (x:A) L',
  p ~> MList (x::L') =
  \exists p', p ~> MCell x p' \* p' ~> MList L'.
Proof using. intros. xunfold~ MList. Qed.

Global Opaque MList.

Lemma MList_null : forall A `{EA:Enc A} (L:list A),
  (null ~> MList L) = \[L = nil].
Proof using.
  intros. destruct L.
  { rewrite MList_nil. xsimpl*. }
  { rewrite MList_cons. applys himpl_antisym. (* todo xsimpl. too much *)
    { xpull ;=> p'. xchange MCell_null. }
    { xpull. (* TODO xsimpl. pb *) } }
Qed.

Lemma MList_nil_intro : forall A `{EA:Enc A},
  \[] ==> (null ~> MList (@nil A)).
Proof using. intros. rewrite MList_null. xsimpl*. Qed.

Lemma MList_null_inv : forall A `{EA:Enc A} (L:list A),
  null ~> MList L ==>
  null ~> MList L \* \[L = nil].
Proof using. intros. rewrite MList_null. xsimpl*. Qed.

Lemma MList_not_null_inv_not_nil : forall p A `{EA:Enc A} (L:list A),
  p <> null ->
  p ~> MList L ==> p ~> MList L \* \[L <> nil].
Proof using.
  intros. destruct L. { xchanges MList_nil. } { xsimpl*. }
Qed.

Lemma MList_not_null_inv_cons : forall p A `{EA:Enc A} (L:list A),
  p <> null ->
  p ~> MList L ==> \exists x p' L',
       \[L = x::L']
    \* p ~> MCell x p'
    \* p' ~> MList L'.
Proof using.
  intros. xchange~ MList_not_null_inv_not_nil ;=> M.
  destruct L; tryfalse. xchanges~ MList_cons.
Qed.

Lemma MList_if : forall p A `{EA:Enc A} (L:list A),
  p ~> MList L ==>
  If p = null
    then \[L = nil]
   else \exists x p' L', \[L = x::L'] \* p ~> MCell x p' \* p' ~> MList L'.
Proof using.
  intros. destruct L as [|x L'].
  { xchanges MList_nil ;=> M. case_if. xsimpl~. }
  { xchange MList_cons ;=> p'. case_if.
    { subst. xchange MCell_null. }
    { xsimpl~. } }
Qed.

End Properties.

Arguments MList_eq : clear implicits.
Arguments MList_nil : clear implicits.
Arguments MList_cons : clear implicits.
Arguments MList_null : clear implicits.
Arguments MList_nil_intro : clear implicits.
Arguments MList_null_inv : clear implicits.
Arguments MList_not_null_inv_not_nil : clear implicits.
Arguments MList_not_null_inv_cons : clear implicits.




(* ********************************************************************** *)
(* ** Node allocation *)

Definition mk_cell :=
  VFun 'x 'q :=
    New`{ head := 'x; tail := 'q }.

Lemma Triple_mk_cell : forall `{EA:Enc A} (x:A) (q:loc),
  TRIPLE (mk_cell ``x ``q)
    PRE \[]
    POST (fun p => (p ~> MCell x q)).
Proof using. xwp. xnew (>> x q). xsimpl. Qed.

Hint Extern 1 (Register_Spec mk_cell) => Provide Triple_mk_cell.


(* ********************************************************************** *)
(* * Length of a mutable list *)

(**
[[
    let rec mlength p =
      if p == null
        then 0
        else 1 + mlength (tail p)
]]
*)

Definition mlength : val :=
  VFix 'f 'p :=
    If_ 'p '= null
      Then 0
      Else 1 '+ 'f ('p'.tail).

Lemma Triple_mlength : forall A `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (mlength ``p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  intros. gen p. induction_wf: list_sub_wf L; intros. xwp.
  xapp~. xchange MList_if. xif ;=> C; case_if; xpull.
  { intros ->. xval. xchanges* <- (MList_nil p). }
  { intros x q L' ->. xapp. xapp~. xapp. xchanges* <- (MList_cons p). }
Qed.

Hint Extern 1 (Register_Spec mlength) => Provide Triple_mlength.



(* ********************************************************************** *)
(* * List Copy *)

(**
[[
    let rec copy p =
      if p == null
        then null
        else mk_cell (p.head) (copy p.tail)
]]
*)

Definition copy : val :=
  VFix 'f 'p :=
    If_ 'p  '= null
      Then null
      Else mk_cell ('p'.head) ('f ('p'.tail)).

Lemma Triple_copy : forall p (L:list int),
  TRIPLE (copy ``p)
    PRE (p ~> MList L)
    POST (fun (p':loc) => (p ~> MList L) \* (p' ~> MList L)).
Proof using.
  intros. gen p. induction_wf IH: list_sub_wf L. xwp.
  xapp~. xchange MList_if. xif ;=> C; case_if; xpull.
  { intros ->. xval. xchanges~ <- (MList_nil p). xchanges* <- (MList_nil null). }
  { intros x q L' ->. xapp. xapp. xapp~ ;=> q'. xapp ;=> p'.
    xchanges <- (MList_cons p). xchanges* <- (MList_cons p'). }
Qed.

Hint Extern 1 (Register_Spec copy) => Provide Triple_copy.



(* ********************************************************************** *)
(* * Increment through a mutable list *)

Definition val_mlist_incr : val :=
  ValFix 'f 'p :=
    If_ 'p '<> null Then (
      Let 'x := val_get_hd 'p in
      Let 'y := 'x '+ 1 in
      val_set_hd 'p 'y;;;
      Let 'q := val_get_tl 'p in
      'f 'q
    ) End.

Lemma Triple_mlist_incr : forall (L:list int) (p:loc),
  TRIPLE (val_mlist_incr ``p)
    PRE (p ~> MList L)
    POST (fun (r:unit) => p ~> MList (LibList.map (fun x => x+1) L)).
Proof using.
  intros. gen p. induction_wf: list_sub_wf L; intros. xcf.
  xapps~. xif ;=> C.
  { xtchanges~ (MList_not_null_inv_cons p) ;=> x p' L' EL.
    xapps. xapps. xapps. xapps. xapps~.
    xchanges~ (>> MList_cons p Enc_int). }
  { subst. xtchanges MList_null_inv ;=> EL. xvals~. }
Qed.



(* ********************************************************************** *)
(* * Out-of-place append of two mutable lists *)

Definition val_mlist_append : val :=
  ValFix 'f 'p1 'p2 :=
    If_ val_eq 'p1 null Then (
      val_mlist_copy 'p2
    ) Else (
      Let 'x := val_get_hd 'p1 in
      Let 'c1 := val_get_tl 'p1 in
      Let 'p := 'f 'c1 'p2 in
      val_new_cell 'x 'p
    ).

Lemma Triple_mlist_append : forall (L1 L2:list int) (p1 p2:loc),
  TRIPLE (val_mlist_append ``p1 ``p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (p:loc) =>
         p ~> MList (L1++L2) \* p1 ~> MList L1 \* p2 ~> MList L2).
Proof using.
  intros. gen p1. induction_wf: list_sub_wf L1; intros. xcf.
  xapps~. xif ;=> C.
  { subst. xtchanges MList_null_inv ;=> EL. xapp.
    intros p. subst. rew_list. xsimpl. }
  { xtchanges~ (MList_not_null_inv_cons p1) ;=> x p1' L' EL.
    xapps. xapps. xapp~ as p'. xapps. intros p. subst. rew_list.
    xchange~ (>> MList_cons p Enc_int).
    xchanges~ (>> MList_cons p1 Enc_int). }
Qed.




Module ExoList.
Import ExampleList.MList.


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
  (* SOLUTION *) intros. xwp. xapp ;=> q. xapp. xsimpl. (* /SOLUTION *)
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

(** Recall:
[[
  TRIPLE (inplace_append p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (_:unit) => p1 ~> MList (L1++L2)).
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
  (* SOLUTION *) xwp. xapp ;=> q. xapp. xsimpl. (* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Push back not using append (blue belt) *)

(** Hint: the following function is a specialization of
    [inplace_append] for the case where the second list
    consists of a single element. Its proof is similar. *)

(**
[[
  let rec push_back' p x =
    if is_empty p
      then set_cons p x (create())
      else push_back' (tail p) x
]]
*)

Definition push_back' : val :=
  VFix 'f 'p 'x :=
    If_ is_empty 'p
      Then set_cons 'p 'x (create '())
      Else 'f (tail 'p) 'x.

Lemma Triple_push_back' : forall `{EA:Enc A} (L:list A) (x:A) (p:loc),
  TRIPLE (push_back' ``p ``x)
    PRE (p ~> MList L)
    POST (fun (_:unit) => p ~> MList (L++x::nil)).
Proof using.
  intros. gen p. induction_wf IH: (@list_sub A) L. intros.
  (* SOLUTION *)
  xwp. xif ;=> C.
  { subst. xchanges (MList_eq p) ;=> v1.
    xapp ;=> q. xapp. xchanges <- (MList_cons p). }
  { xchanges~ (MList_not_nil p) ;=> y L' p' ->.
    xapp. xapp. { auto. } xchanges <- MList_cons. }
  (* /SOLUTION *)
Qed.




