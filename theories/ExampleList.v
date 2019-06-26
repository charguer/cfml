(**

This file formalizes mutable list examples in CFML 2.0.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import Example.
Generalizable Variables A B.

Implicit Types p : loc.
Implicit Types n : int.


(* ********************************************************************** *)
(* * Automation *)

(** Strengthen version of the automation associated with the star,
    e.g. in [mytactic* args]. *)
 
Ltac auto_star ::=
  try solve [ intuition eauto
            | intros; subst; rew_list in *; 
              solve [ math 
                    | auto_false_base ltac:(fun tt => intuition eauto) ] ].



(* ********************************************************************** *)
(* * Towards a representation *)

(** Let's try to first formalize the C representation:
[[
    typedef struct node<A> { 
      A head; 
      node<A>* tail; 
    };
    // with node = null for the empty list
]]
*)
Module MListNull.

Definition head : field := 0%nat.
Definition tail : field := 1%nat.

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

(** Recursive of [p ~> MList L], that is, [MList L p]. *)

Fixpoint MList (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists p', p ~> Record`{ head := x; tail := p'} \* (p' ~> MList L')
  end.

End MListNull.

(* ---------------------------------------------------------------------- *)
(** ** Recursive presentation for a ML representation *)

(** 
[[
  type 'a mlist = ('a contents) ref
  and  'a contents = Nil | Cons of 'a * 'a mlist
]]

Let's begin by assuming that type ['a] is represented as type [val].
*)

Module MListVal.

Definition Nil : val := val_constr "nil" nil.
Definition Cons (v:val) (p:loc) : val := val_constr "cons" (v::(val_loc p)::nil).

Fixpoint MList (L:list val) (p:loc) : hprop :=
  \exists v, p ~~> v \*
  match L with
  | nil => \[v = Nil]
  | x::L' => \exists p', \[v = Cons x p'] \* (p' ~> MList L')
  end.

End MListVal.

(** The definition below is similar, but uses encoders for type ['a] *)


(* ********************************************************************** *)
(* * Representation *)

Module MList.

(* ---------------------------------------------------------------------- *)
(** ** Representation *)

(** Embedded constructors *)

Definition Nil : val := val_constr "nil" nil.
Definition Cons `{Enc A} (V:A) (p:loc) : val := val_constr "cons" (``V::``p::nil).

(** Representation predicate *)

Fixpoint MList A `{EA:Enc A} (L:list A) (p:loc) : hprop :=
  \exists v, p ~~> v \*
  match L with
  | nil => \[v = Nil]
  | x::L' => \exists p', \[v = Cons x p'] \* (p' ~> MList L')
  end.


(* ---------------------------------------------------------------------- *)
(** ** Lemmas about the representation *)

(** Name for the match part inside the body of the definition *)

Definition MList_contents (v:val) A `{EA:Enc A} (L:list A) : hprop :=
  match L with
  | nil => \[v = Nil]
  | x::L' => \exists p', \[v = Cons x p'] \* (p' ~> MList L')
  end.

Lemma MList_contents_Nil : forall A `{EA:Enc A} (L:list A),
  (MList_contents Nil L) ==> \[L = nil].
Proof using.
  intros. unfold MList_contents. destruct L; xsimpl~.
Qed.

Lemma MList_eq : forall (p:loc) A `{EA:Enc A} (L:list A),
  p ~> MList L = (\exists v, p ~~> v \* MList_contents v L).
Proof using. intros. destruct L; auto. Qed.

Lemma MList_nil : forall (p:loc) A `{EA:Enc A},
  (p ~> MList nil) = (p ~~> Nil).
Proof using.
  intros. xunfold MList. applys himpl_antisym.
  { xpull ;=> ? ->. auto. }
  { xsimpl~. }
Qed.

Lemma MList_cons : forall (p:loc) A `{EA:Enc A} x (L':list A),
  p ~> MList (x::L') = \exists p', p ~~> (Cons x p') \* (p' ~> MList L').
Proof using. intros. xunfold MList at 1. xsimpl~. Qed.

Lemma MList_not_nil : forall (p:loc) A `{EA:Enc A} (L:list A),
  L <> nil ->
  p ~> MList L ==> \exists x L' p', \[L = x::L'] \* p ~~> (Cons x p') \* (p' ~> MList L').
Proof using. introv N. destruct L as [|x L']; tryfalse. xchanges* MList_cons. Qed.

Arguments MList_not_nil : clear implicits.



(* ********************************************************************** *)
(* * Basic operations *)

(* ---------------------------------------------------------------------- *)
(** Match on a list *)

Lemma Mlist_unfold_match' : forall `{EA:Enc A} (L:list A) (p:loc) `{EB:Enc B} 
  (F1:Formula) (F2:val->val->Formula) (Q:B->hprop),
  PRE
    (p ~> MList L)
  \* (hand (\[L = nil] \-* p ~> MList L \-* ^F1 Q)
           (\forall q' x' L', \[L = x'::L']
              \-* p ~~> (Cons x' q') 
              \-* q' ~> MList L'
              \-* ^(F2 ``x' ``q' : Formula) Q))
  CODE (Let_ [A0 EA0] X := `App (trm_val (val_prim val_get)) (val_loc p) in
         Case ``X = 'VCstr "nil" '=> F1 
      '| Case ``X = 'VCstr "cons" X0 X1 [X0 X1] '=> F2 X0 X1
      '| Fail) 
  POST Q.
Proof using.
  intros.
  xlet.  xchanges (MList_eq p) ;=> v. unfolds MList_contents. xapp.
  applys xcase_lemma0 ;=> E1.
  { destruct L as [|x L']; xpull.
    { intros ->. xchange himpl_hand_l_r. xchange~ (hwand_hpure_l_intro).
     xchange <- (MList_nil p). }
    { intros q ->. tryfalse. } }
  { applys xcase_lemma2.
    { intros x q E.
      destruct L as [|x' L']; xpull.
      { intros ->. tryfalse. }
      { intros q' E'. subst v. rewrite enc_val_eq in *. inverts E.
        xchange himpl_hand_l_l. do 3 xchange hforall_specialize.
        xchange~ hwand_hpure_l_intro. } }
    { intros N. destruct L as [|x L']; xpull.
      { intros ->. rewrite enc_val_eq in *. unfolds Nil. false. }
      { intros q ->. rewrite enc_val_eq in *. unfolds @Cons. false. } } }
Qed.

Lemma Mlist_unfold_match : forall `{EA:Enc A} (L:list A) (p:loc) `{EB:Enc B} 
  (F1:Formula) (F2:val->val->Formula) (Q:B->hprop) H,
  H ==>
    (p ~> MList L)
  \* (hand (\[L = nil] \-* p ~> MList L \-* ^F1 Q)
           (\forall q' x' L', \[L = x'::L']
              \-* p ~~> (Cons x' q') 
              \-* q' ~> MList L'
              \-* ^(F2 ``x' ``q' : Formula) Q)) ->
  H ==> ^ (Let_ [A0 EA0] X := `App (trm_val (val_prim val_get)) (val_loc p) in
         Case ``X = 'VCstr "nil" '=> F1 
      '| Case ``X = 'VCstr "cons" X0 X1 [X0 X1] '=> F2 X0 X1
      '| Fail) Q.
Proof using. introv M. xchange M. applys @Mlist_unfold_match'. Qed.


(* ---------------------------------------------------------------------- *)
(** [is_empty] *)

Definition is_empty : val :=
  VFun 'p :=
    Match '! 'p With
    '| 'Cstr "nil" '=> true 
    '| 'Cstr "cons" 'x 'q '=> false
    End.

Lemma Triple_is_empty : forall A `{EA:Enc A} (L:list A) p,
  TRIPLE (is_empty ``p)
    PRE (p ~> MList L)
    POST (fun (b:bool) => \[b = isTrue (L = nil)] \* p ~> MList L).
Proof using.
  intros. xwp. applys @Mlist_unfold_match. xsimpl_hand.
  { (* nil *)
    intros EL. xval. xsimpl~. }
  { (* cons *) 
    intros p' x' L' ->. xval. xchanges* <- (MList_cons p). }
Qed.

Hint Extern 1 (Register_Spec (is_empty)) => Provide @Triple_is_empty.


(* ---------------------------------------------------------------------- *)
(** [head] and [tail] *)

Definition head : val :=
  VFun 'p :=
    Match '! 'p With
    '| 'Cstr "cons" 'x 'q '=> 'x
    End.

Lemma Triple_head : forall A `{EA:Enc A} p x q,
  TRIPLE (head ``p)
    PRE (p ~~> (Cons x q))
    POST (fun r => \[r = x] \* p ~~> (Cons x q)).
Proof using.
  intros. xwp. xapp. applys xcase_lemma2. 
  { (* cons *) intros p' x' E. rew_enc in E. unfolds @Cons. inverts E. xval. xsimpl~. }
  { (* else *) xfail*. }
Qed.

Hint Extern 1 (Register_Spec (head)) => Provide @Triple_head.

Definition tail : val :=
  VFun 'p :=
    Match '! 'p With
    '| 'Cstr "cons" 'x 'q '=> 'q
    End.

Lemma Triple_tail : forall A `{EA:Enc A} p x q,
  TRIPLE (tail ``p)
    PRE (p ~~> (Cons x q))
    POST (fun r => \[r = q] \* p ~~> (Cons x q)).
Proof using.
  intros. xwp. xapp. applys xcase_lemma2. 
  { (* cons *) intros p' x' E. rew_enc in E. unfolds @Cons. inverts E. xval. xsimpl~. }
  { (* else *) xfail*. }
Qed.

Hint Extern 1 (Register_Spec (tail)) => Provide @Triple_tail.


(* ---------------------------------------------------------------------- *)
(** [create] and [mk_cons] *)

Definition create : val :=
  VFun 'u :=
    val_ref ('Cstr "nil").

Lemma Triple_create : forall A `{EA:Enc A},
  TRIPLE (create ``tt)
    PRE \[]
    POST (fun p => p ~> MList (@nil A)).
Proof using.
  intros. xwp. xval (@nil A). xapp ;=> p. xchanges <- MList_nil.
Qed.

Hint Extern 1 (Register_Spec (create)) => Provide @Triple_create.

Definition mk_cons : val :=
  VFun 'x 'q :=
    val_ref ('Cstr "cons" 'x 'q).

Lemma Triple_mk_cons : forall A `{EA:Enc A} (L:list A) (x:A) (q:loc),
  TRIPLE (mk_cons ``x ``q)
    PRE (q ~> MList L)
    POST (fun p => p ~> MList (x::L)).
Proof using.
  intros. xwp. xval (Cons x q). xapp ;=> p. xchanges <- MList_cons.
Qed.

Hint Extern 1 (Register_Spec (mk_cons)) => Provide @Triple_mk_cons.


(* ---------------------------------------------------------------------- *)
(** [set_nil], [set_cons], [set_head], and [set_tail] *)

Definition set_nil : val :=
  VFun 'p :=
    'p ':= 'Cstr "nil".

Lemma Triple_set_nil : forall p (v:val),
  TRIPLE (set_nil ``p)
    PRE (p ~~> v)
    POST (fun (_:unit) => p ~~> Nil).
Proof using.
  intros. xwp. xval (Nil). xapp. xsimpl.
Qed.

Hint Extern 1 (Register_Spec (set_nil)) => Provide @Triple_set_nil.

Definition set_cons : val :=
  VFun 'p 'x 'q :=
    'p ':= 'Cstr "cons" 'x 'q.

Lemma Triple_set_cons : forall A `{EA:Enc A} p (v:val) (x:A) q,
  TRIPLE (set_cons ``p ``x ``q)
    PRE (p ~~> v)
    POST (fun (_:unit) => p ~~> Cons x q).
Proof using.
  intros. xwp. xval (Cons x q). xapp. xsimpl.
Qed.

Hint Extern 1 (Register_Spec (set_cons)) => Provide @Triple_set_cons.

Definition set_head : val :=
  VFun 'p 'x2 :=
    Match '! 'p With
    '| 'Cstr "cons" 'x1 'q '=> 'p ':= ('Cstr "cons" 'x2 'q)
    End.

Lemma Triple_set_head : forall A `{EA:Enc A} q p x1 x2,
  TRIPLE (set_head ``p ``x2)
    PRE (p ~~> Cons x1 q)
    POST (fun (_:unit) => p ~~> Cons x2 q).
Proof using.
  intros. xwp. xapp. applys xcase_lemma2. 
  { (* cons *) intros p' x' E. rew_enc in E. unfolds @Cons. inverts E.
     xval (Cons x2 q). xapp. xsimpl~. }
  { (* else *) xfail*. }
Qed.

Hint Extern 1 (Register_Spec (set_head)) => Provide @Triple_set_head.

Definition set_tail : val :=
  VFun 'p 'q2 :=
    Match '! 'p With
    '| 'Cstr "cons" 'x 'q '=> 'p ':= ('Cstr "cons" 'x 'q2)
    End.

Lemma Triple_set_tail : forall A `{EA:Enc A} p x q1 q2,
  TRIPLE (set_tail ``p ``q2)
    PRE (p ~~> Cons x q1)
    POST (fun (_:unit) => p ~~> Cons x q2).
Proof using.
  intros. xwp.  xapp. applys xcase_lemma2. 
  { (* cons *) intros p' x' E. rew_enc in E. unfolds @Cons. inverts E.
     xval (Cons x q2). xapp. xsimpl~. }
  { (* else *) intros N. false N. reflexivity. }
Qed.

Hint Extern 1 (Register_Spec (set_tail)) => Provide @Triple_set_tail.


(* ---------------------------------------------------------------------- *)
(** [push] *)

Definition push : val :=
  VFun 'p 'x :=
    Let 'q := '!'p in
    set_cons 'p 'x (val_ref 'q).

Lemma Triple_push : forall `{EA:Enc A} (L:list A) (p:loc) (x:A),
  TRIPLE (push p ``x)
    PRE (p ~> MList L)
    POST (fun (_:unit) => p ~> MList (x::L)).
Proof using.
  xwp. xchange MList_eq ;=> q. xapp. xapp ;=> q2. xapp.
  xchange <- MList_eq. xchanges <- MList_cons.
Qed.

Hint Extern 1 (Register_Spec (push)) => Provide @Triple_push.


(* ---------------------------------------------------------------------- *)
(** [pop] *)

Definition pop : val :=
  VFun 'p  :=
    Let 'x := head 'p in
    ('p ':= '! (tail 'p)) ';
    'x.

Lemma Triple_pop : forall `{EA:Enc A} (L:list A) (p:loc),
  L <> nil ->
  TRIPLE (pop p)
    PRE (p ~> MList L)
    POST (fun (x:A) => \exists L', \[L = x::L'] \* p ~> MList L').
Proof using.
  introv N. xwp. destruct L as [|x L']; tryfalse. xchange MList_cons ;=> q.
  xapp. xchange MList_eq ;=> q2. xapp. xapp. xapp. xchange <- (MList_eq p). xvals*.
Qed.

Hint Extern 1 (Register_Spec (pop)) => Provide @Triple_pop.



(* ********************************************************************** *)
(* * High-level operations *)


(* ---------------------------------------------------------------------- *)
(** [mlength] *)

Definition mlength : val :=
  VFix 'f 'p :=
    If_ is_empty 'p 
      Then 0 
      Else 1 '+ 'f (tail 'p).

Lemma Triple_mlength : forall `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (mlength p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  intros. gen p. induction_wf IH: (@list_sub A) L. intros.
  xwp. xapp. xif ;=> E.
  { xval 0. xsimpl*. }
  { xchanges~ MList_not_nil ;=> x L' p' ->.
    xapp. xapp~. xapp~. xchange <- MList_cons. xsimpl*. }
Qed.

Hint Extern 1 (Register_Spec (mlength)) => Provide @Triple_mlength.


(* ---------------------------------------------------------------------- *)
(** [copy] *)

Definition copy : val :=
  VFix 'f 'p :=
    If_ is_empty 'p 
      Then create '() 
      Else mk_cons (head 'p) ('f (tail 'p)).

Lemma Triple_copy : forall `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (copy p)
    PRE (p ~> MList L)
    POST (fun (q:loc) => p ~> MList L \* q ~> MList L).
Proof using.
  intros. gen p. induction_wf IH: (@list_sub A) L. intros.
  xwp. xapp. xif ;=> E.
  { xapp ;=> p'. xsimpl*. }
  { xchanges~ MList_not_nil ;=> x L' p' ->.
    xapp. xapp~. xapp~ ;=> q'. xapp ;=> q.
    xchanges <- MList_cons. }
Qed.

Hint Extern 1 (Register_Spec (copy)) => Provide @Triple_copy.


(* ---------------------------------------------------------------------- *)
(** [iter] *)

Definition iter : val :=
  VFix 'g 'f 'p :=
    If_ 'not (is_empty 'p) Then
      'f (head 'p) ';
      'g 'f (tail 'p)
    End.

Lemma Triple_iter : forall `{EA:Enc A} (I:list A->hprop) (L:list A) (f:func) (p:loc),
  (forall x L1 L2, L = L1++x::L2 ->
    TRIPLE (f ``x)
      PRE (I L1)
      POST (fun (_:unit) => I (L1&x)))
  ->
  TRIPLE (iter ``f ``p)
    PRE (p ~> MList L \* I nil)
    POST (fun (_:unit) => p ~> MList L \* I L).
Proof using.
  introv Specf.
  cuts G: (forall L1 L2, L = L1++L2 ->
    TRIPLE (iter ``f ``p)
      PRE (p ~> MList L2 \* I L1)
      POST (fun (_:unit) => p ~> MList L2 \* I L)).
  { applys~ G. }
  intros L1 L2 E. gen p L1. induction_wf: list_sub_wf L2; intros.
  xwp. xapp~. xapp. xif ;=> C.
  { xchanges~ MList_not_nil ;=> x L2' p2' ->.
    xapp. xapp*. (* xapp (>> __ L2'). *) 
    xapp. xapp*. xchanges <- MList_cons. }
  { xval tt. subst; rew_list. xsimpl. }
Qed.

Hint Extern 1 (Register_Spec (iter)) => Provide @Triple_iter.


(* ---------------------------------------------------------------------- *)
(** Length of a mutable list using iter *)

Definition length_using_iter : val :=
  VFun 'p :=
    Let 'n := val_ref ``0 in
    iter (Fun 'x := incr 'n) 'p ';
    '! 'n.

Lemma Triple_mlist_length_using_iter : forall A `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (length_using_iter ``p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  xwp. xapp ;=> n. xfun.
  xapp (>> __ (fun (K:list A) => n ~~> (length K:Z))).
  { intros x K T E. xwp. xapp. xsimpl*. }
  xapp. xsimpl~.
Qed.


(* ---------------------------------------------------------------------- *)
(** Nondestructive append *)

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

(* ---------------------------------------------------------------------- *)
(** Destructive append *)

Definition inplace_append : val :=
  VFix 'f 'p1 'p2 :=
    If_ is_empty 'p1 
      Then 'p1 ':= '! 'p2
      Else 'f (tail 'p1) 'p2.

Lemma Triple_inplace_append : forall `{EA:Enc A} (L1 L2:list A) (p1 p2:loc),
  TRIPLE (inplace_append p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (_:unit) => p1 ~> MList (L1++L2)).
Proof using.
  intros. gen p1. induction_wf IH: (@list_sub A) L1. intros.
  xwp. xif ;=> C. 
  { xchanges (MList_eq p1) ;=> v1. xchanges (MList_eq p2) ;=> v2.
    xapp. xapp. xchanges* <- (MList_eq p1). }
  { xchanges~ (MList_not_nil p1) ;=> x L1' p1' ->.
    xapp. xapp*. xchanges <- (MList_cons p1). }
Qed.

Hint Extern 1 (Register_Spec (inplace_append)) => Provide @Triple_inplace_append.


(* ---------------------------------------------------------------------- *)
(** CPS append *)

Definition cps_append_aux : val :=
  VFix 'f 'p1 'p2 'k :=
    If_ is_empty 'p1 
      Then 'k 'p2
      Else 'f (tail 'p1) 'p2 (Fun 'r := (set_tail 'p1 'r '; 'k 'p1)).

Definition cps_append : val :=
  VFun 'p1 'p2 :=
    cps_append_aux 'p1 'p2 (Fun 'r := 'r).

Lemma Triple_cps_append_aux : forall A `{EA:Enc A} (L1 L2:list A) (p1 p2:loc) (k:func),
  forall `{EB: Enc B} (H:hprop) (Q:B->hprop),
  (forall (p3:loc), TRIPLE (k ``p3)
     PRE (p3 ~> MList (L1 ++ L2) \* H)
     POST Q) ->
  TRIPLE (cps_append_aux ``p1 ``p2 ``k)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2 \* H)
    POST Q.
Proof using.
  introv Hk. gen H p1 p2 L2 k. induction_wf IH: (@list_sub A) L1. intros.
  xwp. xapp (>> __ EA). xif ;=> C.
  { subst. xapp. xsimpl~. }
  { xchanges~ (MList_not_nil p1) ;=> x L1' p1' ->.
    xapp (>> __ EA). xfun. 
    (* LATER: xapp (>> IH L1' (H \* (p1 ~~> Cons x p1'))). *)
    lets IH': (>> (rm IH) L1' (H \* (p1 ~~> Cons x p1'))).
    { autos*. }
    xapp IH'; clear IH'. (* LATER: xapp (rm IH') *)
    { intros p3. xwp. xapp (>> __ EA). xapp. 
      xchanges <- (MList_cons p1). }
    xsimpl*. }
Qed.

Lemma Triple_mlist_cps_append : forall A `{EA:Enc A} (L1 L2:list A) (p1 p2:loc),
  TRIPLE (cps_append ``p1 ``p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun p3 => p3 ~> MList (L1 ++ L2)).
Proof using.
  intros. xwp. xfun. xapp (>> (@Triple_cps_append_aux) \[] (fun p3 => p3 ~> MList (L1 ++ L2))).
  { intros p3. xwp. xval. xsimpl. }
  xsimpl.
Qed.


(* Note that the continuation k' used in the recursive call
   could be given the following spec, rather than inlining its code:
[[
     Triple (k' ``r)
       PRE (p ~~> (x,p') \* r ~> Mlist (L'++M) \* H)
       POST Q.
]]
*)



(* ********************************************************************** *)
(* * Bonus *)

(* ---------------------------------------------------------------------- *)
(** Length using iter but not incr *)

Definition length_using_iter' : val :=
  VFun 'p :=
    Let 'n := val_ref ``0 in
    iter (Fun 'x := ('n ':= ('!'n '+ 1))) 'p ';
    '! 'n.

Lemma Triple_mlist_length_using_iter' : forall A `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (length_using_iter' ``p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  xwp. xapp ;=> n. xfun.
  xapp (>> __ (fun (K:list A) => n ~~> (length K:Z))).
  { intros x K T E. xwp. xappn. xsimpl*. }
  xapp. xsimpl~.
Qed.


(* ---------------------------------------------------------------------- *)
(** Alternative spec and proofs for set_nil *)

Lemma Triple_set_nil_of_MList : forall A `{EA:Enc A} (L:list A) p,
  TRIPLE (set_nil ``p)
    PRE (p ~> MList L)
    POST (fun (_:unit) => p ~> MList (@nil A)).
Proof using.
  intros. xtriple. xchange @MList_eq ;=> v. xapp. rewrite MList_nil. xsimpl.
Qed.

Lemma Triple_set_nil_of_MList_direct_proof : forall A `{EA:Enc A} (L:list A) p,
  TRIPLE (set_nil ``p)
    PRE (p ~> MList L)
    POST (fun (_:unit) => p ~> MList (@nil A)).
Proof using.
  intros. xwp. xchange MList_eq ;=> v.
  xval (Nil). xapp. rewrite MList_nil. xsimpl.
Qed.


(* ---------------------------------------------------------------------- *)
(** Detailed proof for is_empty *)

Lemma Triple_is_empty' : forall A `{EA:Enc A} (L:list A) p,
  TRIPLE (is_empty ``p)
    PRE (p ~> MList L)
    POST (fun (b:bool) => \[b = isTrue (L = nil)] \* p ~> MList L).
Proof using.
  intros. xwp. xchange MList_eq ;=> v. xapp. 
  applys xcase_lemma0 ;=> E1.
  { rew_enc in E1. subst. xchange MList_contents_Nil ;=> ->.
    xchange <- MList_nil. xval. xsimpl~. }
  { applys xcase_lemma2.
    { intros x' q' E. rew_enc in E. inverts E. unfold MList_contents.
      destruct L as [|x L'].
      { xpull. }
      { xval. xpull ;=> p' E'. xchange <- (MList_cons p). applys E'.
        xsimpl. auto_false. } }
    { intros N. unfold MList_contents. destruct L as [|x L']; xpull.
      { intros ->. rewrite enc_val_eq in *. unfolds Nil. false. }
      { intros q ->. rewrite enc_val_eq in *. unfolds @Cons. false. } } }
Qed.



(* ********************************************************************** *)
(* * List segments *)

(** Representation *)

Fixpoint MListSeg A `{EA:Enc A} (q:loc) (L:list A) (p:loc) : hprop :=
  match L with
  | nil => \[p = q]
  | x::L' => \exists p', p ~~> (Cons x p') \* (p' ~> MListSeg q L')
  end.

Section SegProperties.

Lemma MListSeg_nil : forall `{EA:Enc A} p q,
  p ~> (MListSeg q (@nil A)) = \[p = q].
Proof using. intros. xunfold~ MListSeg. Qed.

Lemma MListSeg_cons : forall `{EA:Enc A} p q x (L':list A),
  p ~> MListSeg q (x::L') =
  \exists (p':loc), (p ~~> Cons x p') \* p' ~> MListSeg q L'.
Proof using. intros. xunfold~ MListSeg. Qed.

Global Opaque MListSeg.

Lemma MListSeg_nil_of_hempty : forall `{EA:Enc A} p,
  \[] ==> p ~> MListSeg p (@nil A).
Proof using. intros. rewrite MListSeg_nil. xsimpl~. Qed.

Lemma MListSeg_one : forall `{EA:Enc A} p q (x:A),
  p ~~> (Cons x q) = p ~> MListSeg q (x::nil).
Proof using.
  intros. rewrite MListSeg_cons. applys himpl_antisym.
  { xsimpl. rewrite MListSeg_nil. xsimpl~. }
  { xpull ;=> p'. rewrite MListSeg_nil. xsimpl~. }
Qed.

Lemma MListSeg_concat : forall `{EA:Enc A} p1 p3 (L1 L2:list A),
  p1 ~> MListSeg p3 (L1++L2) = \exists p2, p1 ~> MListSeg p2 L1 \* p2 ~> MListSeg p3 L2.
Proof using.
  intros. gen p1. induction L1 as [|x L1']; intros.
  { rew_list. applys himpl_antisym. (* Note: xsimpl too aggressive here *)
    { xchanges (MListSeg_nil_of_hempty p1). }
    { xpull ;=> p2. rewrite MListSeg_nil. xsimpl*. } }
  { rew_list. applys himpl_antisym.
    { rewrite (MListSeg_cons p1). xpull ;=> p1'. xchange IHL1' ;=> p2.
      xchanges <- (>> MListSeg_cons p1). }
    { xpull ;=> p2. rewrite (MListSeg_cons p1). xpull ;=> p1'.
      xchange <- IHL1'. xchanges <- (>> MListSeg_cons p1). } }
Qed.

Lemma MListSeg_last : forall `{EA:Enc A} p1 p3 x (L:list A),
  p1 ~> MListSeg p3 (L&x) = \exists p2, p1 ~> MListSeg p2 L \* p2 ~~> (Cons x p3).
Proof using.
  intros. rewrite MListSeg_concat. applys himpl_antisym.
  { xpull ;=> p2. rewrite <- MListSeg_one. xsimpl. }
  { xpull ;=> p2. rewrite MListSeg_one. xsimpl. }
Qed.

Lemma MList_eq_MListSeg : forall `{EA:Enc A} p (L:list A),
  p ~> MList L = (\exists q, p ~> MListSeg q L \* q ~~> Nil).
Proof using.
  intros. gen p. induction L as [|x L']; intros.
  { rewrite MList_nil. xsimpl.
    { xsimpl. rewrite MListSeg_nil. xsimpl~. }
    { xpull ;=> p'. rewrite MListSeg_nil. xsimpl*. } }
  { rewrite MList_cons. applys himpl_antisym.
    { xpull ;=> p'. rewrite IHL'. xpull ;=> q. xchanges <- MListSeg_cons. }
    { xpull ;=> q. rewrite MListSeg_cons. xpull ;=> p'. xchanges <- IHL'. } }
Qed. (* Note: using rewrite below existential binders, the proof would be far easier *)

End SegProperties.



(* ********************************************************************** *)
(* * Lists with recursive ownership *)

(* ---------------------------------------------------------------------- *)
(** ** Recursive representation predicate: works, but not modular *)

(**
[[
  Definition MListOf A `{EA:Enc A} TA (R:TA->A->hprop) (L:list TA) (p:loc) : hprop :=
    match L with
    | nil => \[p = null]
    | X::L' => \exists x p', p ~> Record`{ head := x; tail := p'} 
                     \* (x ~> R X) \* (p' ~> MListOf R L')
    end.
]]
*)

(* ---------------------------------------------------------------------- *)
(** ** Representation predicate for [MListOf] *)

Module MListOf.

Definition MListOf A `{EA:Enc A} TA (R:TA->A->hprop) (L:list TA) (p:loc) : hprop :=
  \exists (l:list A), \[length l = length L] \* p ~> MList l
                      \* hfold_list2 (fun X x => x ~> R X) L l. 

(* ---------------------------------------------------------------------- *)
(** ** Derived specifications for stack operations *)

Section Ops.

Context A {EA:Enc A} TA (R:TA->A->hprop).
Implicit Types L : list TA.
Implicit Types x : A.
Implicit Types X : TA.

Lemma Triple_create : 
  TRIPLE (create tt)
    PRE \[]
    POST (fun p => p ~> MListOf R nil).
Proof using.
  xtriple. xapp ;=> p. xunfold MListOf. xsimpl*.
  { rew_heapx. xsimpl. } 
Qed.

Lemma Triple_is_empty : forall L p,
  TRIPLE (is_empty p)
    PRE (p ~> MListOf R L)
    POST (fun b => \[b = isTrue (L = nil)] \* p ~> MListOf R L).
Proof using.
  xtriple. xunfold MListOf. xpull ;=> l E. xapp. xsimpl*.
  { applys* list_same_length_inv_nil. }
Qed.

Lemma Triple_push : forall L p x X,
  TRIPLE (push p ``x)
    PRE (p ~> MListOf R L \* x ~> R X)
    POST (fun (_:unit) => p ~> MListOf R (X::L)).
Proof using.
  xtriple. xunfold MListOf. xpull ;=> l E. xapp.
  xsimpl (x::l). { rew_list~. } { rew_heapx. xsimpl. }
Qed.

Lemma Triple_pop : forall L p,
  L <> nil ->
  TRIPLE (pop p)
    PRE (p ~> MListOf R L)
    POST (fun x => \exists X L', \[L = X::L'] \* x ~> R X \* p ~> MListOf R L').
Proof using.
  xtriple. xunfold MListOf. xpull ;=> l E. xapp.
  { rewrites~ (>> list_same_length_inv_nil L). }
  intros x l' ->. destruct L as [|X L']; rew_listx in *; tryfalse.
  rew_heapx. xsimpl*.
Qed.

End Ops.

Module MListOfSpecs.
Hint Extern 1 (Register_Spec (create)) => Provide @Triple_create.
Hint Extern 1 (Register_Spec (is_empty)) => Provide @Triple_is_empty.
Hint Extern 1 (Register_Spec (push)) => Provide @Triple_push.
Hint Extern 1 (Register_Spec (pop)) => Provide @Triple_pop.
End MListOfSpecs.

Global Opaque MListOf.

End MListOf.

End MList.
