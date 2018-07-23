(**

This file formalizes mutable queues in plain Separation Logic,
using characteristic formulae.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import LambdaCF LambdaStruct.
From Sep Require Import ExampleListNonlifted.
Generalizable Variables A B.

Ltac auto_star ::= jauto.

Implicit Types p q : loc.
Implicit Types n : int.
Implicit Types v : val.


(* ********************************************************************** *)
(* * Mutable queue *)

(* ---------------------------------------------------------------------- *)
(** Representation *)

Definition MQueue (L:list val) (p:loc) :=
  \exists (pf:loc), \exists (pb:loc), \exists (vx:val), \exists (vy:val),
    MCell pf pb p \* MListSeg pb L pf \* MCell vx vy pb.


(* ---------------------------------------------------------------------- *)
(** Create *)

Definition val_create :=
  ValFun 'v :=
    Let 'r := val_alloc 2 in
    val_new_cell 'r 'r.

Lemma triple_create :
  triple (val_create val_unit)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* MQueue nil p).
Proof using.
  xcf. unfold MQueue.
  xapp triple_alloc_cell as r. intros p v1 v2. intro_subst.
  xapp~. hpull ;=> r x E. hsimpl~.
  { rewrite MListSeg_nil_eq. hsimpl~. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Is empty *)

Definition val_is_empty :=
  ValFun 'p :=
    Let 'x := val_get_hd 'p in
    Let 'y := val_get_tl 'p in
    val_eq 'x 'y.

Lemma triple_is_empty : forall L p,
  triple (val_is_empty p)
    (MQueue L p)
    (fun r => \[r = isTrue (L = nil)] \* MQueue L p).
Proof using.
  xcf. unfold MQueue. xpull ;=> pf pb vx vy.
  xapps. xapps.
  xchanges (MListSeg_then_MCell_inv_neq pf pb) ;=> R.
  (* xchange (MListSeg_then_MCell_inv_neq pf pb). xpull ;=> R. *)
  xapp. hsimpl ;=> ? ->. fequals. rew_bool_eq. rewrite R. iff; congruence.
Qed.

Hint Extern 1 (Register_spec val_is_empty) => Provide triple_is_empty.


(* ---------------------------------------------------------------------- *)
(** Push back *)

Definition val_push_back :=
  ValFun 'v 'p :=
    Let 'q := val_get_tl 'p in
    Let 'r := val_alloc 2 in
    val_set_hd 'q 'v ;;;
    val_set_tl 'q 'r ;;;
    val_set_tl 'p 'r.

Lemma triple_push_back : forall L v p,
  triple (val_push_back v p)
    (MQueue L p)
    (fun r => MQueue (L&v) p).
Proof using.
  xcf. unfold MQueue. xpull ;=> pf pb vx vy.
  xapps. xapp triple_alloc_cell as r. intros pb' v1 v2. intro_subst.
  xapp~. intros _. xapp~. intros _. xapp~. hchanges~ MListSeg_last.
Qed.


(* ---------------------------------------------------------------------- *)
(** Push front *)

Definition val_push_front :=
  ValFun 'v 'p :=
    Let 'q := val_get_hd 'p in
    Let 'r := val_new_cell 'v 'q in
    val_set_hd 'p 'r.

Lemma triple_push_front : forall L v p,
  triple (val_push_front v p)
    (MQueue L p)
    (fun r => MQueue (v::L) p).
Proof using.
  xcf. unfold MQueue. xpull ;=> pf pb vx vy.
  xapps. xapp as r. intros x. intro_subst.
  xapp. hsimpl~. intros _. hchanges (@MListSeg_cons x).
Qed.


(* ---------------------------------------------------------------------- *)
(** Pop front *)

Definition val_pop_front :=
  ValFun 'v 'p :=
    Let 'q := val_get_hd 'p in
    Let 'x := val_get_hd 'q in
    Let 'r := val_get_tl 'q in
    val_set_hd 'p 'r;;;
    'x.

Lemma triple_pop_front : forall L v p,
  L <> nil ->
  triple (val_pop_front v p)
    (MQueue L p)
    (fun v => \exists L', \[L = v::L'] \* MQueue L' p).
Proof using.
  xcf. unfold MQueue. xpull ;=> pf pb vx vy.
  destruct L as [|x L']; tryfalse.
  rewrite MListSeg_cons_eq. xpull ;=> pf'.
  xapps. xapps. xapps. xapp~. intros _. xvals~.
Qed.

Lemma triple_pop_front' : forall L v p x,
  triple (val_pop_front v p)
    (MQueue (x::L) p)
    (fun r => \[r = x] \* MQueue L p).
Proof using.
  intros. xapply (@triple_pop_front (x::L)).
  { auto_false. }
  { hsimpl. }
  { intros r. hpull ;=> L' E. inverts E. hsimpl~. }
Qed.


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
  { unfold MQueue. xpull ;=> pf2 pb2 vx2 vy2 pf1 pb1 vx1 vy1.
    destruct L2 as [|x L2']; tryfalse.
    xchanges MListSeg_cons_eq ;=> pf2'.
    xapps. xapps. xapps. xapps.
    xapps~. xapps~. intros _. xapps~. intros _. xapps~. intros _. xapps~.
    intros r. hchange (MListSeg_last pf1).
    hchange (MListSeg_concat pf1 pf2' pb2). rew_list.
    hchange (MListSeg_nil pf2). hsimpl~. }
  { subst. rew_list. xvals~. }
Qed.
