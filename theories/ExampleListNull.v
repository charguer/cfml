(**

This file formalizes mutable list examples in CFML 2.0.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import Example.
Generalizable Variables A B.

Implicit Types p q : loc.
Implicit Types n m : int.

Definition pointer_field (l:loc) (k:field) := 
  (l+k)%nat.

Notation "l `. k" := (pointer_field l k)
  (at level 32, k at level 0, no associativity,
   format "l `. k") : heap_scope.


Definition val_field (k:field) : val :=
  VFun 'p :=
    val_ptr_add 'p (nat_to_Z k).

Notation "l ``. k" := (val_field k l)
  (at level 32, k at level 0, no associativity,
   format "l ``. k") : heap_scope.



(* ********************************************************************** *)
(* * Towards a representation *)

(** Let's try to first formalize the C representation:
[[

    type list<A> = (node<A>)*
       // the pointer is null for an empty list
       // the pointer is the address of a record otherwise

    type node<A> = record { 
      A       head; 
      list<A> tail;
    };
]]
*)
Module MListNull.

Definition head : field := 0%nat.
Definition tail : field := 1%nat.



(* ---------------------------------------------------------------------- *)
(** Representation of segments *)

Fixpoint MListSeg `{EA:Enc A} (r:loc) (L:list A) (p:loc) : hprop :=
  match L with
  | nil => \[p = r]
  | x::L' => \exists (q:loc), p ~~> q \* q`.head ~~> x \* q`.tail ~> MListSeg r L'
  end.


(* ---------------------------------------------------------------------- *)
(** Properties of segments *)

Section SegProperties.

Lemma MListSeg_nil : forall `{EA:Enc A} p r,
  p ~> (MListSeg r (@nil A)) = \[p = r].
Proof using. intros. xunfold~ MListSeg. Qed.

Lemma MListSeg_cons : forall `{EA:Enc A} p r x (L':list A),
  p ~> MListSeg r (x::L') =
  \exists (q:loc), p ~~> q \* q`.head ~~> x \* q`.tail ~> MListSeg r L'.
Proof using. intros. xunfold MListSeg at 1. simple~. Qed.

Global Opaque MListSeg.

Lemma MListSeg_one : forall `{EA:Enc A} p r (x:A),
  p ~> MListSeg r (x::nil) =
  \exists (q:loc), p ~~> q \* q`.head ~~> x \* \[q`.tail = r].
Proof using. intros. rewrite MListSeg_cons. fequals. Qed.

Lemma MListSeg_concat : forall `{EA:Enc A} p1 r (L1 L2:list A),
  p1 ~> MListSeg r (L1++L2) = \exists p2, p1 ~> MListSeg p2 L1 \* p2 ~> MListSeg r L2.
Proof using.
  intros. gen p1. induction L1 as [|x L1']; intros; rew_list.
  { applys himpl_antisym.
    { (* TODO fix [xsimpl r]. *) applys himpl_hexists_r p1.
      (* TODO: xsimpl bug *) xchange~ <- MListSeg_nil. }
    { xpull ;=> p2. xchange* MListSeg_nil. } }
  { applys himpl_antisym. 
    { rewrite MListSeg_cons. xpull ;=> q. xchange IHL1' ;=> p2.
      xchanges <- MListSeg_cons. }
    { xpull ;=> p2. xchange MListSeg_cons ;=> q. xchange <- IHL1'.
      xchange <- MListSeg_cons. } }
Qed.

End SegProperties.

Arguments MListSeg_nil : clear implicits.
Arguments MListSeg_cons : clear implicits.
Arguments MListSeg_one : clear implicits.
Arguments MListSeg_concat : clear implicits.


(* ---------------------------------------------------------------------- *)
(** Representation of full lists *)

Definition MList `{EA:Enc A} (L:list A) (p:loc) : hprop :=
  \exists (r:loc), p ~> MListSeg r L \* r ~~> null.

Lemma MList_eq : forall `{EA:Enc A} (L:list A) (p:loc),
  p ~> MList L =
  \exists (r:loc), p ~> MListSeg r L \* r ~~> null.
Proof using. intros. xunfold~ MList. Qed.


Definition MListTail `{EA:Enc A} (L:list A) (q:loc) : hprop :=
  match L with
  | nil => \[q = null]
  | x::L' => q`.head ~~> x \* q`.tail ~> MList L'
  end.

Lemma MListTail_eq : forall `{EA:Enc A} (L:list A) (q:loc),
  q ~> MListTail L =
   match L with
  | nil => \[q = null]
  | x::L' => q`.head ~~> x \* q`.tail ~> MList L'
  end.
Proof using. intros. xunfold~ MListTail. Qed.

Lemma MListTail_cons : forall `{EA:Enc A} (x:A) (L':list A) (q:loc),
  q ~> MListTail (x::L') = q`.head ~~> x \* q`.tail ~> MList L'.
Proof using. intros. rewrite~ MListTail_eq. Qed.

Lemma MListTail_null : forall `{EA:Enc A} (L:list A) (q:loc),
  q ~> MListTail L ==> q ~> MListTail L \* \[q = null <-> L = nil].
Proof using.
  intros. destruct L; xunfold MListTail.
  { xsimpl*. }
  { unfold pointer_field, head. math_rewrite (q + 0 = q)%nat.
    xchange Hsingle_not_null ;=> E. xsimpl. auto_false*. }
Qed.

Lemma MListTail_if : forall `{EA:Enc A} (L:list A) (q:loc),
  q ~> MListTail L =
  If q = null 
    then \[L = nil] 
    else \exists x L', \[L = x::L'] \* q`.head ~~> x \* q`.tail ~> MList L'.
Proof using.
  intros. apply himpl_antisym.
  { xchange MListTail_null ;=> M. destruct L as [|x L']; xunfold MListTail.
    { case_if. { xsimpl*. } { xpull. (* TODO: xsimpl leaves shelved variables *) } }
    { case_if. { rewrite M in C. tryfalse. } { xsimpl*. } } }
  { xunfold MListTail. case_if.
    { xsimpl ;=> ->. xsimpl*. }
    { xpull ;=> x L' ->. xsimpl. } }
Qed.

Lemma MList_head : forall `{EA:Enc A} (L:list A) (p:loc),
  p ~> MList L =
  \exists (q:loc), p ~~> q \* q ~> MListTail L.
Proof using.
  intros. xunfold MList. destruct L.
  { xunfold MListTail. applys himpl_antisym.
    { xpull ;=> r. xchange MListSeg_nil ;=> ->. xsimpl~. }
    { xpull ;=> ? ->. xsimpl p. xchange~ <- MListSeg_nil. } }
  { xunfold MListTail. applys himpl_antisym.
    { xpull ;=> r. rewrite MListSeg_cons. xpull ;=> q. xsimpl q. xchange <- MList_eq. }
    { xpull ;=> q. xchange MList_eq ;=> r. xsimpl r. xchange <- MListSeg_cons. } }
Qed.

Lemma MList_head_null : forall `{EA:Enc A} (L:list A) (p:loc),
  p ~> MList L ==>
  \exists (q:loc), p ~~> q \* q ~> MListTail L \* \[q = null <-> L = nil].
Proof using.
  intros. xchange MList_head ;=> q. xchange MListTail_null ;=> M. xsimpl*.
Qed.

Lemma MList_head_if : forall `{EA:Enc A} (L:list A) (p:loc),
  p ~> MList L ==>
  \exists (q:loc), p ~~> q \* If q = null 
    then \[L = nil] 
    else \exists x L', \[L = x::L'] \* q`.head ~~> x \* q`.tail ~> MList L'.
Proof using.
  intros. xchange MList_head ;=> q. xchange MListTail_if. xsimpl*.
Qed.

Lemma MList_nil : forall p A `{EA:Enc A},
  (p ~> MList (@nil A)) = p ~~> null.
Proof using.
  intros. xunfold MList. applys himpl_antisym.
  { xpull ;=> r. xchange* MListSeg_nil. }
  { xsimpl. xchange~ <- MListSeg_nil. }
Qed.

Lemma MList_cons : forall p A `{EA:Enc A} (x:A) L',
  p ~> MList (x::L') =
  \exists q, p ~~> q \* q`.head ~~> x \* q`.tail ~> MList L'.
Proof using.
  intros. xunfold MList. applys himpl_antisym.
  { xpull ;=> r. xchanges MListSeg_cons. }
  { xpull ;=> q r. xsimpl r. xchange <- MListSeg_cons. }
Qed.

Arguments MList_eq : clear implicits.
Arguments MList_head : clear implicits.
Arguments MList_nil : clear implicits.
Arguments MList_cons : clear implicits.

Global Opaque MList MListTail.


(* ********************************************************************** *)
(* ** Node allocation *)

Parameter mk_node : val.

Parameter Triple_mk_node : forall `{EA:Enc A} (x:A) (q:loc),
  TRIPLE (mk_node ``x ``q)
    PRE \[]
    POST (fun p => p`.head ~~> x \* p`.tail ~~> q).

Hint Extern 1 (Register_Spec (mk_node)) => Provide @Triple_mk_node.


(* ********************************************************************** *)
(* ** Push *)

(** 
[[
    let push p x =
      p := mk_node x (!p)
]]
*)

Definition push : val :=
  VFun 'p 'x :=
    'p ':= mk_node 'x ('!'p).

Lemma Triple_push : forall `{EA:Enc A} (L:list A) (p:loc) (x:A),
  TRIPLE (push p ``x)
    PRE (p ~> MList L)
    POST (fun (_:unit) => p ~> MList (x::L)).
Proof using.
  xwp. xchange MList_head ;=> q. xapp. xapp ;=> q'. xapp.
  xchange <- MList_head. xchanges <- MList_cons.
Qed.

Hint Extern 1 (Register_Spec (push)) => Provide @Triple_push.



(* ********************************************************************** *)
(* * Pointer arithmetic *)


Parameter Triple_val_field : forall (k:field) (p:loc),
  TRIPLE ((val_field k) ``p)
    PRE \[]
    POST (fun (q:loc) => \[q = p`.k]).

Hint Extern 1 (Register_Spec (val_field _)) => Provide Triple_val_field.



(* ********************************************************************** *)
(* * Length of a mutable list *)

Definition mlength : val :=
  VFix 'f 'p :=
    Let 'q := '! 'p in
    If_ 'q '= null 
      Then 0
      Else 1 '+ 'f ('q ``.tail).

Lemma Triple_mlength : forall A `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (mlength ``p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  intros. gen p. induction_wf: list_sub_wf L; intros. xwp.
  xchange MList_head_if ;=> q. xapp. xapp~.
  xif ;=> C; case_if; xpull.
  { intros ->. xval. subst q. xchange <- MList_nil. xsimpl*. }
  { intros x L' ->. xapp. xapp~. xapp. xchanges* <- MList_cons. }
Qed.



(*


(* ********************************************************************** *)
(* * List Copy *)

Definition val_mlist_copy :=
  VFix 'f 'p :=
    If_ val_eq 'p null Then null Else (
      Let 'x := val_get_hd 'p in
      Let 'p1 := val_get_tl 'p in
      Let 'p2 := 'f 'p1 in
      val_new_cell 'x 'p2
   ).

Lemma Triple_mlist_copy : forall p (L:list int),
  TRIPLE (val_mlist_copy ``p)
    PRE (p ~> MList L)
    POST (fun (p':loc) =>
         (p ~> MList L) \* (p' ~> MList L)).
Proof using.
  intros. gen p. induction_wf IH: list_sub_wf L. xwp.
  xapps~.  xif ;=> C.
  { xval. subst p. rewrite MList_null_eq. xsimpl~. }
  { xtchanges~ (MList_not_null_inv_cons p) ;=> x p1 T1 E.
    subst. xapps. xapps. xapp~ as p1'. xapp.
    intros p'. do 2 rewrite MList_cons_eq. xsimpl. }
Qed.

Hint Extern 1 (Register_Spec val_mlist_copy) => Provide Triple_mlist_copy.




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
