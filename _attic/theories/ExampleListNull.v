(**

This file formalizes mutable list examples in CFML 2.0.
using a representation of lists as either null or a two-cell record.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Import Example.
Generalizable Variables A B.
Open Scope heap_scope_ext.

Implicit Types p : loc.
Implicit Types n : int.



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


(* ---------------------------------------------------------------------- *)
(** Representation of list segments *)

Fixpoint MListSeg A `{EA:Enc A} (q:loc) (L:list A) (p:loc) : hprop :=
  match L with
  | nil => \[p = q]
  | x::L' => \exists (p':loc), (p ~> MCell x p') \* (p' ~> MListSeg q L')
  end.


(* ---------------------------------------------------------------------- *)
(** Lemmas *)

Section SegProperties.

Lemma MListSeg_eq : forall (p:loc) A `{EA:Enc A} (q:loc) (L:list A),
  p ~> MListSeg q L =
  match L with
  | nil => \[p = q]
  | x::L' => \exists (p':loc), (p ~> MCell x p') \* (p' ~> MListSeg q L')
  end.
Proof using. intros. xunfold~ @MListSeg. destruct~ L. Qed.

Lemma MListSeg_nil : forall p q A `{EA:Enc A},
  p ~> (MListSeg q (@nil A)) = \[p = q].
Proof using. intros. xunfold~ MListSeg. Qed.

Global Arguments MListSeg_nil : clear implicits.

Lemma MListSeg_cons : forall p q A `{EA:Enc A} x (L':list A),
  p ~> MListSeg q (x::L') =
  \exists (p':loc), (p ~> MCell x p') \* p' ~> MListSeg q L'.
Proof using. intros. xunfold~ MListSeg. Qed.

Global Arguments MListSeg_cons : clear implicits.

Global Opaque MListSeg.

Lemma MListSeg_nil_intro : forall p A `{EA:Enc A},
  \[] = p ~> MListSeg p (@nil A).
Proof using. intros. rewrite MListSeg_nil. xsimpl*. Qed.

Global Arguments MListSeg_nil_intro : clear implicits.

Lemma MListSeg_one : forall p q A `{EA:Enc A} (x:A),
  p ~> MListSeg q (x::nil) = p ~> (MCell x q).
Proof using.
  intros. rewrite MListSeg_cons. applys himpl_antisym.
  { xpull ;=> p'. xchange MListSeg_nil ;=> ->. xsimpl. }
  { xsimpl q. xchanges* <- MListSeg_nil. }
Qed.

Global Arguments MListSeg_one : clear implicits.

Lemma MListSeg_MList : forall p A `{EA:Enc A} (L:list A),
  p ~> MListSeg null L = p ~> MList L.
Proof using.
  intros. gen p. induction L; intros.
  { rewrite MListSeg_nil. rewrite~ MList_nil. }
  { rewrite MListSeg_cons. rewrite MList_cons.
    fequals. apply fun_ext_1. intros q. (* todo simplify *)
    rewrite~ IHL. }

Qed.

Global Arguments MListSeg_MList : clear implicits.

Lemma MListSeg_concat : forall p1 p3 A `{EA:Enc A} (L1 L2:list A),
  p1 ~> MListSeg p3 (L1++L2) =
  \exists p2, p1 ~> MListSeg p2 L1 \* p2 ~> MListSeg p3 L2.
Proof using.
  intros. gen p1. induction L1 as [|x L1']; intros; rew_list.
  { applys himpl_antisym.
    { applys himpl_hexists_r p1. (* TODO fix  xsimpl p1. *)
      xchange~ <- MListSeg_nil. }
    {  xpull ;=> p2. xchange~ MListSeg_nil ;=> ->. xsimpl. } }
  { rewrite MListSeg_cons. applys himpl_antisym.
    { xpull ;=> p1'. xchange IHL1' ;=> p2. xsimpl p2. xchange <- MListSeg_cons. }
    { xpull ;=> p2. xchange MListSeg_cons ;=> p1'. xchanges <- IHL1'. } }
Qed.

Global Arguments MListSeg_concat : clear implicits.

Lemma MListSeg_last : forall p1 p3 A `{EA:Enc A} x (L:list A),
  p1 ~> MListSeg p3 (L&x) =
  \exists p2, p1 ~> MListSeg p2 L \* p2 ~> (MCell x p3).
Proof using.
  intros. rewrite MListSeg_concat.
  fequals. apply fun_ext_1. intros p2. (* todo simplify *)
  rewrite~ MListSeg_one.
Qed.

Global Arguments MListSeg_last : clear implicits.

Lemma MListSeg_MCell_conflict : forall (p q:loc) A `{EA:Enc A} (L:list A) (x:A) (q':loc),
  p ~> MListSeg q L \* q ~> MCell x q' ==+> \[L = nil <-> p = q].
Proof using.
  intros. destruct L.
  { xchange MListSeg_nil. xsimpl*. split*. (* TODO: why not proved? *) }
  { xchange MListSeg_cons ;=> p'. tests: (p = q).
    { xchange (@MCell_conflict q q A EA loc Enc_loc). }
    { xsimpl*. xchange <- MListSeg_cons. } }
Qed.

Global Arguments MListSeg_MCell_conflict : clear implicits.

End SegProperties.



(* ********************************************************************** *)
(* ** Node allocation *)

Definition mk_cell :=
  Fun 'x 'q :=
    New`{ head := 'x; tail := 'q }.

Lemma Triple_mk_cell : forall A `{EA:Enc A} (x:A) (q:loc),
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
  Fix 'f 'p :=
    If_ 'p '= null
      Then 0
      Else 1 '+ 'f ('p'.tail).

Lemma Triple_mlength : forall A `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (mlength ``p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  intros. gen p. induction_wf IH: list_sub_wf L; intros. xwp.
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
  Fix 'f 'p :=
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
(* ********************************************************************** *)
(* ********************************************************************** *)
(* LATER

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


(* ********************************************************************** *)
(* * Out-of-place append of two aliased mutable lists *)

Lemma Triple_mlist_append_aliased : forall (L:list int) (p1:loc),
  TRIPLE (val_mlist_append ``p1 ``p1)
    PRE (p1 ~> MList L)
    POST (fun (p:loc) => p ~> MList (L++L) \* p1 ~> MList L).
Proof using.
  cuts K: (forall (L L1 L2:list int) (p1 p3:loc),
    L = L1++L2 ->
    TRIPLE (val_mlist_append ``p3 ``p1)
      PRE (p1 ~> MListSeg p3 L1 \* p3 ~> MList L2)
      POST (fun (p:loc) => p ~> MList (L2++L) \* p1 ~> MList L)).
  { intros. xtchange (MListSeg_nil p1). xapplys (K L nil L). rew_list~. }
  intros. gen p3 L1. induction_wf: list_sub_wf L2; intros. xcf.
  xapps~. xif ;=> C.
  { subst. xtchanges MList_null_inv ;=> EL. subst. rew_list.
    rewrite MList_nil_eq. xtpull ;=> _.
    xtchange (>> (@MListSeg_to_MList int) p1).
    xapp. intros p. rew_list. xsimpl. }
  { xtchanges~ (MList_not_null_inv_cons p3) ;=> x p3' L2' EL2.
    xapps. xapps.
    xtchange (>> (@MListSeg_last int) p1).
    xapp~ (>> IH L2' (L1&x)) as p'. xapps.
    intros p. xchange~ (>> (@MList_cons) p Enc_int).
    subst. rew_list. xsimpl. }
Qed.





(* ********************************************************************** *)
(* * Length of a mutable list using a loop *)

Definition val_mlist_length_loop : val :=
  ValFun 'p1 :=
    Let 'r := val_ref 'p1 in
    Let 'n := val_ref 0 in
    While (Let 'p := val_get 'r in
           'p '<> null) Do
      val_incr 'n ;;;
      Let 'p := val_get 'r in
      Let 'q := val_get_tl 'p in
      val_set 'r 'q
    Done ;;;
    val_get 'n.

Lemma Triple_mlist_length_loop : forall A `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (val_mlist_length_loop ``p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  xcf. xapp ;=> r. xapp ;=> n.
  { xwhile as R.
    cuts K: (forall (nacc:int),
       ^R (r ~~> p \* p ~> MList L \* n ~~> nacc)
         (fun (_:unit) => p ~> MList L \* n ~~> (nacc + length L))).
    { xapplys* K. }
    gen p. induction_wf: list_sub_wf L; intros. applys (rm HR).
    xlet. { xapps. xapps~. } xtpull ;=> ? ->. xif ;=> C.
    { xtchanges~ (MList_not_null_inv_cons p) ;=> p' x L' EL. xseq.
      { xseq. xapp~. xapps. xapps. xapps~. }
      { xapply~ (>> IH L'). { xsimpl. } { xpull. xchanges~ (MList_cons p). } } }
    { inverts C. xtchanges MList_null_inv ;=> EL. xvals~. }
  { xapp. xsimpl~. } }
Qed.

(* TODO: another proof using a loop invariant with segments:

  \exists L1 L2 q,
     \[L = L1 ++ L2] \* (n ~~> length L1) \* (f ~~> q)
     \* (p ~~> MListSeq q L1) \* (q ~~> MList L2)
  *)


(* ********************************************************************** *)
(* * Length of a mutable list *)

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
(* * In-place list reversal *)

Definition val_mlist_in_place_rev : val :=
  ValFun 'p1 :=
    Let 'r := val_ref 'p1 in
    Let 's := val_ref null in
    While (Let 'p := val_get 'r in
           'p '<> null) Do
      Let 'p := val_get 'r in
      Let 'q := val_get_tl 'p in
      val_set 'r 'q ;;;
      Let 't := val_get 's in
      val_set_tl 'p 't ;;;
      val_set 's 'p
    Done ;;;
    val_get 's.

Lemma Triple_mlist_in_place_rev : forall A `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (val_mlist_in_place_rev ``p)
    PRE (p ~> MList L)
    POST (fun (p':loc) => p' ~> MList (rev L)).
Proof using.
  intros. rename p into p0. xcf. xapps ;=> rp. xapps ;=> rs.
  xseq. (* todo xwhile_inv *)
  { applys mklocal_erase. applys Cf_while_of_Cf_while_inv. hnf.
    sets I: (fun (b:bool) (L1:list A) => \exists p s L2,
      \[b = isTrue (L1 <> nil)] \* \[L = rev L2 ++ L1]
      \* rp ~~> p \* p ~> MList L1 \* rs ~~> s \* s ~> MList L2).
    exists __ I (@list_sub A) __. splits.
    { solve_wf. }
    { xchange MList_nil. unfold I. xsimpl*. }
    { intros F LF b L1 IH. unfold I at 1. xtpull ;=> p s L2 E1 E2. clears b.
      xlet. { xapps. xapps~. } xtpull ;=> ? ->.
      xif ;=> Cb.
      { xtchanges~ (MList_not_null_inv_cons p) ;=> x p1' L1' EL1.
        xseq. (* todo: problem of parentheses around xwhile body *)
        { xapps. xapps. xapps. xapps. xapps. xapps. }
        { xapps~. { unfold I. xchanges~ (MList_cons p). } } }
      { xval. subst p. unfold I. xchanges~ MList_null_inv. } }
    { xsimpl. } }
  { xtpull ;=> L1 p s L2 E1 E2. xapp. xpull ;=> ? ->. xsimpl~. }
Qed.


(* ********************************************************************** *)
(* * CPS append *)

Definition val_mlist_cps_append : val :=
  ValFix 'f 'p 'q 'k :=
    If_ val_eq 'p null Then (
      'k 'q
    ) Else (
      LetFun 'k2 'r := (val_set_tl 'p 'r ;;; 'k 'p) in
      Let 't := val_get_tl 'p in
      'f 't 'q 'k2
    ).

Lemma Triple_mlist_cps_append : forall A `{EA:Enc A} (L M:list A) (p q:loc) (k:func),
  forall `{EB: Enc B} (H:hprop) (Q:B->hprop),
  (forall (r:loc), TRIPLE (k ``r)
     PRE (r ~> MList (L ++ M) \* H)
     POST Q) ->
  TRIPLE (val_mlist_cps_append ``p ``q ``k)
    PRE (p ~> MList L \* q ~> MList M \* H)
    POST Q.
Proof using.
  intros A EA L. induction_wf IH: (@list_sub A) L. introv Hk.
  xcf. xapps~. xif ;=> C.
  { subst. xtchanges MList_null_eq ;=> E. subst. xapp. xsimpl~. }
  { xval ;=> F EF. sets R: (5%nat). (* todo: hide number *)
    xtchanges~ (MList_not_null_inv_cons p) ;=> x p' L' EL.
    xapps. xapp (>> IH (H \* (p ~> Record`{hd:=x; tl:=p'}))).
    { subst~. }
    { intros r. subst F. xcf.
      xapps. simpl. (* todo: maybe should be done by xapps *)
      xtchange (MList_cons p). subst L. xapps. xsimpl~. }
    { xsimpl. } }
Qed.

(* Note that K' could be given the following spec, rather than inlining its code:
     Triple (k' ``r)
       PRE (p ~~> (x,p') \* r ~> Mlist (L'++M) \* H)
       POST Q.
*)


(* ********************************************************************** *)
(* * Fold-left function *)


(* ********************************************************************** *)
(* * Map function *)


(* ********************************************************************** *)
(* * Find function *)




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




(* ********************************************************************** *)
(* * Length of a mutable list using a loop *)

Definition val_mlist_length_loop : val :=
  ValFun 'p1 :=
    Let 'r := val_ref 'p1 in
    Let 'n := val_ref 0 in
    While (Let 'p := val_get 'r in
           'p '<> null) Do
      val_incr 'n ;;;
      Let 'p := val_get 'r in
      Let 'q := val_get_tl 'p in
      val_set 'r 'q
    Done ;;;
    val_get 'n.

Lemma Triple_mlist_length_loop : forall A `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (val_mlist_length_loop ``p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  xcf. xapp ;=> r. xapp ;=> n.
  { xwhile as R.
    cuts K: (forall (nacc:int),
       ^R (r ~~> p \* p ~> MList L \* n ~~> nacc)
         (fun (_:unit) => p ~> MList L \* n ~~> (nacc + length L))).
    { xapplys* K. }
    gen p. induction_wf: list_sub_wf L; intros. applys (rm HR).
    xlet. { xapps. xapps~. } xtpull ;=> ? ->. xif ;=> C.
    { xtchanges~ (MList_not_null_inv_cons p) ;=> p' x L' EL. xseq.
      { xseq. xapp~. xapps. xapps. xapps~. }
      { xapply~ (>> IH L'). { xsimpl. } { xpull. xchanges~ (MList_cons p). } } }
    { inverts C. xtchanges MList_null_inv ;=> EL. xvals~. }
  { xapp. xsimpl~. } }
Qed.

(* TODO: another proof using a loop invariant with segments:

  \exists L1 L2 q,
     \[L = L1 ++ L2] \* (n ~~> length L1) \* (f ~~> q)
     \* (p ~~> MListSeq q L1) \* (q ~~> MList L2)
  *)


(* ********************************************************************** *)
(* * In-place list reversal *)

Definition val_mlist_in_place_rev : val :=
  ValFun 'p1 :=
    Let 'r := val_ref 'p1 in
    Let 's := val_ref null in
    While (Let 'p := val_get 'r in
           'p '<> null) Do
      Let 'p := val_get 'r in
      Let 'q := val_get_tl 'p in
      val_set 'r 'q ;;;
      Let 't := val_get 's in
      val_set_tl 'p 't ;;;
      val_set 's 'p
    Done ;;;
    val_get 's.

Lemma Triple_mlist_in_place_rev : forall A `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (val_mlist_in_place_rev ``p)
    PRE (p ~> MList L)
    POST (fun (p':loc) => p' ~> MList (rev L)).
Proof using.
  intros. rename p into p0. xcf. xapps ;=> rp. xapps ;=> rs.
  xseq. (* todo xwhile_inv *)
  { applys mklocal_erase. applys Cf_while_of_Cf_while_inv. hnf.
    sets I: (fun (b:bool) (L1:list A) => \exists p s L2,
      \[b = isTrue (L1 <> nil)] \* \[L = rev L2 ++ L1]
      \* rp ~~> p \* p ~> MList L1 \* rs ~~> s \* s ~> MList L2).
    exists __ I (@list_sub A) __. splits.
    { solve_wf. }
    { xchange MList_nil. unfold I. xsimpl*. }
    { intros F LF b L1 IH. unfold I at 1. xtpull ;=> p s L2 E1 E2. clears b.
      xlet. { xapps. xapps~. } xtpull ;=> ? ->.
      xif ;=> Cb.
      { xtchanges~ (MList_not_null_inv_cons p) ;=> x p1' L1' EL1.
        xseq. (* todo: problem of parentheses around xwhile body *)
        { xapps. xapps. xapps. xapps. xapps. xapps. }
        { xapps~. { unfold I. xchanges~ (MList_cons p). } } }
      { xval. subst p. unfold I. xchanges~ MList_null_inv. } }
    { xsimpl. } }
  { xtpull ;=> L1 p s L2 E1 E2. xapp. xpull ;=> ? ->. xsimpl~. }
Qed.


(* ********************************************************************** *)
(* * CPS append *)

Definition val_mlist_cps_append : val :=
  ValFix 'f 'p 'q 'k :=
    If_ val_eq 'p null Then (
      'k 'q
    ) Else (
      LetFun 'k2 'r := (val_set_tl 'p 'r ;;; 'k 'p) in
      Let 't := val_get_tl 'p in
      'f 't 'q 'k2
    ).

Lemma Triple_mlist_cps_append : forall A `{EA:Enc A} (L M:list A) (p q:loc) (k:func),
  forall `{EB: Enc B} (H:hprop) (Q:B->hprop),
  (forall (r:loc), TRIPLE (k ``r)
     PRE (r ~> MList (L ++ M) \* H)
     POST Q) ->
  TRIPLE (val_mlist_cps_append ``p ``q ``k)
    PRE (p ~> MList L \* q ~> MList M \* H)
    POST Q.
Proof using.
  intros A EA L. induction_wf IH: (@list_sub A) L. introv Hk.
  xcf. xapps~. xif ;=> C.
  { subst. xtchanges MList_null_eq ;=> E. subst. xapp. xsimpl~. }
  { xval ;=> F EF. sets R: (5%nat). (* todo: hide number *)
    xtchanges~ (MList_not_null_inv_cons p) ;=> x p' L' EL.
    xapps. xapp (>> IH (H \* (p ~> Record`{hd:=x; tl:=p'}))).
    { subst~. }
    { intros r. subst F. xcf.
      xapps. simpl. (* todo: maybe should be done by xapps *)
      xtchange (MList_cons p). subst L. xapps. xsimpl~. }
    { xsimpl. } }
Qed.

(* Note that K' could be given the following spec, rather than inlining its code:
     Triple (k' ``r)
       PRE (p ~~> (x,p') \* r ~> Mlist (L'++M) \* H)
       POST Q.
*)

*)

