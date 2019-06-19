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

(*
Hint Extern 1 (_ = _ :> Z) => subst; rew_list; math.
Hint Extern 1 (_ = _ :> list _) => subst; rew_list.
Hint Extern 1 (list_sub _ _) => subst.
*)


Tactic Notation "hsimpl_hand" :=
   hsimpl; try (applys himpl_hand_r; hsimpl).

Tactic Notation "hchanges" "*" "<-" constr(E) :=
  hchanges <- E; auto_star.


(* ********************************************************************** *)
(* * Towards a representation *)

Module MListNull.

Definition head : field := 0%nat.
Definition tail : field := 1%nat.

(** [p ~> MList L], (hypothetically) defined as an inductive predicate 

[[

  -----------------
  null ~> MList nil

  p ~> Record`{ head := x; tail := p'}      p' ~> MList L'
  -------------------------------------------------------
                       p ~> MList (x::L')

]]

*)

(** Recursive of [p ~> MList L], that is, [MList L p]. *)

Fixpoint MList (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists p', p ~> Record`{ head := x; tail := p'} \* (p' ~> MList L')
  end.

End MListNull.




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



(* ********************************************************************** *)
(* * Representation *)

Module MList.

Definition Nil : val := val_constr "nil" nil.
Definition Cons `{Enc A} (V:A) (p:loc) : val := val_constr "cons" (``V::``p::nil).

Fixpoint MList A `{EA:Enc A} (L:list A) (p:loc) : hprop :=
  \exists v, p ~~> v \*
  match L with
  | nil => \[v = Nil]
  | x::L' => \exists p', \[v = Cons x p'] \* (p' ~> MList L')
  end.

Definition MList_contents (v:val) A `{EA:Enc A} (L:list A) : hprop :=
  match L with
  | nil => \[v = Nil]
  | x::L' => \exists p', \[v = Cons x p'] \* (p' ~> MList L')
  end.

Lemma MList_contents_Nil : forall A `{EA:Enc A} (L:list A),
  (MList_contents Nil L) ==> \[L = nil].
Proof using.
  intros. unfold MList_contents. destruct L; hsimpl~.
Qed.

Lemma MList_contents_Nil_keep : forall A `{EA:Enc A} (L:list A),
  (MList_contents Nil L) ==> \[L = nil] \* (MList_contents Nil L).
Proof using.
  intros. unfold MList_contents. destruct L; hsimpl~.
Qed.

Lemma MList_contents_Cons : forall A `{EA:Enc A} (L:list A) x p',
  (MList_contents (Cons x p') L) ==> \exists L', \[L = x::L'] \* (p' ~> MList L').
Proof using.
  intros. unfold MList_contents. destruct L.
  { hsimpl. }
  { hpull ;=> p'' E. unfolds @Cons.
    rewrite (enc_loc_eq p'), (enc_loc_eq p'') in E. (* rew_enc in *. *)
    asserts_rewrite (x = a). { admit. }
    (* Enc_injective EA --- all encoders should be injective!  *)
    inverts E. hsimpl~. }
Admitted.

Lemma MList_contents_Cons' : forall A `{EA:Enc A} (L:list A) x p',
  (MList_contents (Cons x p') L) ==> \exists x' L', \[L = x'::L'] \* \[``x = ``x'] \* (p' ~> MList L').
Proof using.
  intros. unfold MList_contents. destruct L.
  { hpull. } (* TODO: hsimpl. should not create evars!  Show Existentials.  *)
  { hpull ;=> p'' E. unfolds @Cons.
    rewrite (enc_loc_eq p'), (enc_loc_eq p'') in E.
    inverts E. hsimpl~ a L. }
Qed.


Lemma MList_eq : forall (p:loc) A `{EA:Enc A} (L:list A),
  p ~> MList L = (\exists v, p ~~> v \* MList_contents v L).
Proof using. intros. destruct L; auto. Qed.

Arguments MList_eq : clear implicits.

Lemma MList_unfold : forall A `{EA:Enc A} (L:list A) (p:loc),
  p ~> MList L ==>
    (\exists v, p ~~> v \*
    match L with
    | nil => \[v = Nil]
    | x::L' => \exists p', \[v = Cons x p'] \* (p' ~> MList L')
    end).
Proof using. intros. rewrite~ MList_eq. Qed.

Lemma MList_unfold_case : forall A `{EA:Enc A} (L:list A) (p:loc),
  p ~> MList L ==>
    match L with
    | nil => p ~~> Nil
    | x::L' => \exists p', (p ~~> Cons x p') \* (p' ~> MList L')
    end.
Proof using. intros. hchange MList_unfold ;=> v. destruct L; hsimpl~. Qed.

Lemma MList_cons_unfold : forall (p:loc) A `{EA:Enc A} x (L':list A),
  p ~> MList (x::L') ==> \exists p', p ~~> (Cons x p') \* (p' ~> MList L').
Proof using. intros. xunfold MList at 1. hsimpl~. Qed.

Arguments MList_cons_unfold : clear implicits.

Lemma MList_not_nil_unfold : forall (p:loc) A `{EA:Enc A} (L:list A),
  L <> nil ->
  p ~> MList L ==> \exists x L' p', \[L = x::L'] \* p ~~> (Cons x p') \* (p' ~> MList L').
Proof using. introv N. destruct L as [|x L']; tryfalse. hchanges* MList_cons_unfold. Qed.

Arguments MList_not_nil_unfold : clear implicits.

Lemma MList_cons_fold : forall (p:loc) A `{EA:Enc A} x p' (L':list A),
  p ~~> (Cons x p') \* (p' ~> MList L') ==> p ~> MList (x::L').
Proof using. intros. rewrites (>> MList_eq (x::L')). unfold MList_contents. hsimpl~. Qed.

Arguments MList_cons_fold : clear implicits.

Lemma MList_nil_eq : forall (p:loc) A `{EA:Enc A},
  (p ~> MList nil) = (p ~~> Nil).
Proof using.
  intros. xunfold MList. applys himpl_antisym.
  { hpull ;=> ? ->. auto. }
  { hsimpl~. }
Qed.

Arguments MList_nil_eq : clear implicits.

Lemma MList_nil_unfold : forall (p:loc) A `{EA:Enc A},
  (p ~> MList nil) ==> (p ~~> Nil).
Proof using. intros. rewrite~ MList_nil_eq. Qed.

Arguments MList_nil_unfold : clear implicits.

Lemma MList_nil_fold : forall (p:loc) A `{EA:Enc A},
  (p ~~> Nil) ==> (p ~> MList nil).
Proof using. intros. rewrite~ MList_nil_eq. Qed.

Arguments MList_nil_fold : clear implicits.


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
  CODE (Let [A0 EA0] X := `App (trm_val (val_prim val_get)) (val_loc p) in
         Case ``X = 'VCstr "nil" '=> F1 
      '| Case ``X = 'VCstr "cons" X0 X1 [X0 X1] '=> F2 X0 X1
      '| Fail) 
  POST Q.
Proof using.
  intros.
  xlet. hchanges (MList_unfold L) ;=> v. xapp.
  applys xcase_lemma0 ;=> E1.
  { destruct L as [|x L']; hpull.
    { intros ->. hchange himpl_hand_l_r. hchange~ (hwand_hpure_l_intro).
     hchange (MList_nil_fold p). }
    { intros q ->. tryfalse. } }
  { applys xcase_lemma2.
    { intros x q E.
      destruct L as [|x' L']; hpull.
      { intros ->. tryfalse. }
      { intros q' E'. subst v. rewrite enc_val_eq in *. inverts E.
        hchange himpl_hand_l_l. do 3 hchange hforall_specialize.
        hchange~ hwand_hpure_l_intro. } }
    { intros N. destruct L as [|x L']; hpull.
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
  H ==> ^ (Let [A0 EA0] X := `App (trm_val (val_prim val_get)) (val_loc p) in
         Case ``X = 'VCstr "nil" '=> F1 
      '| Case ``X = 'VCstr "cons" X0 X1 [X0 X1] '=> F2 X0 X1
      '| Fail) Q.
Proof using. introv M. hchange M. applys @Mlist_unfold_match'. Qed.


(* ---------------------------------------------------------------------- *)
(** [is_nil] *)

Definition is_nil : val :=
  VFun 'p :=
    Match '! 'p With
    '| 'Cstr "nil" '=> true 
    '| 'Cstr "cons" 'x 'q '=> false
    End.

Lemma Triple_is_nil : forall A `{EA:Enc A} (L:list A) p,
  TRIPLE (is_nil ``p)
    PRE (p ~> MList L)
    POST (fun (b:bool) => \[b = isTrue (L = nil)] \* p ~> MList L).
Proof using.
  intros. xwp. applys @Mlist_unfold_match. hsimpl_hand.
  { (* nil *)
    intros EL. xval. hsimpl~. }
  { (* cons *) 
    intros p' x' L' ->. xval. hchanges* (MList_cons_fold p). }
Qed.

Hint Extern 1 (Register_Spec (is_nil)) => Provide @Triple_is_nil.


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
  { (* cons *) intros p' x' E. rew_enc in E. unfolds @Cons. inverts E. xval. hsimpl~. }
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
  { (* cons *) intros p' x' E. rew_enc in E. unfolds @Cons. inverts E. xval. hsimpl~. }
  { (* else *) xfail*. }
Qed.

Hint Extern 1 (Register_Spec (tail)) => Provide @Triple_tail.


(* ---------------------------------------------------------------------- *)
(** [mk_nil] and [mk_cons] *)

Definition mk_nil : val :=
  VFun 'u :=
    val_ref ('Cstr "nil").

Lemma Triple_mk_nil : forall A `{EA:Enc A},
  TRIPLE (mk_nil ``tt)
    PRE \[]
    POST (fun p => p ~> MList (@nil A)).
Proof using.
  intros. xwp. xval (@nil A). xapp ;=> p. hchanges MList_nil_fold.
Qed.

Hint Extern 1 (Register_Spec (mk_nil)) => Provide @Triple_mk_nil.

Definition mk_cons : val :=
  VFun 'x 'q :=
    val_ref ('Cstr "cons" 'x 'q).

Lemma Triple_mk_cons : forall A `{EA:Enc A} (L:list A) (x:A) (q:loc),
  TRIPLE (mk_cons ``x ``q)
    PRE (q ~> MList L)
    POST (fun p => p ~> MList (x::L)).
Proof using.
  intros. xwp. xval (Cons x q). xapp ;=> p. hchanges MList_cons_fold.
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
  intros. xwp. xval (Nil). xapp. hsimpl.
Qed.

Hint Extern 1 (Register_Spec (set_nil)) => Provide @Triple_set_nil.

Definition set_cons : val :=
  VFun 'p 'x 'q :=
    'p ':= 'Cstr "cons" 'x 'q.

Lemma Triple_set_cons : forall A `{EA:Enc A} (L:list A) p (v:val) (x:A) q,
  TRIPLE (set_cons ``p ``x ``q)
    PRE (p ~~> v)
    POST (fun (_:unit) => p ~~> Cons x q).
Proof using.
  intros. xwp. xval (Cons x q). xapp. hsimpl.
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
     xval (Cons x2 q). xapp. hsimpl~. }
  { (* else *) xfail*. (* intros N. false N. reflexivity. *) }
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
     xval (Cons x q2). xapp. hsimpl~. }
  { (* else *) intros N. false N. reflexivity. }
Qed.

Hint Extern 1 (Register_Spec (set_tail)) => Provide @Triple_set_tail.



(* ********************************************************************** *)
(* * High-level operations *)

(* ---------------------------------------------------------------------- *)
(** [mlength] *)

Definition mlength : val :=
  VFix 'f 'p :=
    If_ is_nil 'p 
      Then 0 
      Else 1 '+ 'f (tail 'p).

Lemma Triple_mlength : forall `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (mlength p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  intros. gen p. induction_wf IH: (@list_sub A) L. intros.
  xwp. xapp. xif ;=> E.
  { xval 0. hsimpl*. }
  { hchanges~ MList_not_nil_unfold ;=> x L' p' ->.
    xapp. xapp~. xapp~. hchange MList_cons_fold. hsimpl*. }
Qed.

    (* hchanges~ MList_not_nil_unfold ;=> x L' p' ->.
      short for
      destruct L as [|x L']; tryfalse. hchange MList_cons_unfold ;=> p'. *)


(* ---------------------------------------------------------------------- *)
(** [copy] *)

Definition copy : val :=
  VFix 'f 'p :=
    If_ is_nil 'p 
      Then mk_nil '() 
      Else mk_cons (head 'p) ('f (tail 'p)).

Lemma Triple_copy : forall `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (copy p)
    PRE (p ~> MList L)
    POST (fun (q:loc) => p ~> MList L \* q ~> MList L).
Proof using.
  intros. gen p. induction_wf IH: (@list_sub A) L. intros.
  xwp. xapp. xif ;=> E.
  { xapp ;=> p'. hsimpl*. }
  { hchanges~ MList_not_nil_unfold ;=> x L' p' ->.
    xapp. xapp~. xapp~ ;=> q'. xapp ;=> q.
    hchanges MList_cons_fold. }
Qed.


(* ---------------------------------------------------------------------- *)
(** [iter] *)

Definition iter : val :=
  VFix 'g 'f 'p :=
    If_ 'not (is_nil 'p) Then
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
  { hchanges~ MList_not_nil_unfold ;=> x L2' p2' ->.
    xapp. xapp*. (* xapp (>> __ L2'). *) 
    xapp. xapp*. hchanges MList_cons_fold. }
  { xval tt. subst; rew_list. hsimpl. }
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
  { intros x K T E. xwp. xapp. hsimpl*. }
  xapp. hsimpl~.
Qed.


(* ---------------------------------------------------------------------- *)
(** Nondestructive append *)

Definition nondestructive_append : val :=
  VFix 'f 'p1 'p2 :=
    If_ is_nil 'p1 
      Then copy 'p2
      Else mk_cons (head 'p1) ('f (tail 'p1) 'p2).

Lemma Triple_nondestructive_append : forall `{EA:Enc A} (L1 L2:list A) (p1 p2:loc),
  TRIPLE (nondestructive_append p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (p3:loc) => p1 ~> MList L1 \* p2 ~> MList L2 \* p3 ~> MList (L1++L2)).
Proof using.
  intros. gen p1. induction_wf IH: (@list_sub A) L1. intros.
  xwp. xif ;=> C.
  { xapp Triple_copy ;=> p3. hsimpl*. }
  { hchanges~ (MList_not_nil_unfold p1) ;=> x L1' p1' ->.
    xapp. xapp. xapp* ;=> p3'. hchanges (MList_cons_fold p1).
    xapp ;=> p3. hsimpl. }
Qed.

Hint Extern 1 (Register_Spec (nondestructive_append)) => Provide @Triple_nondestructive_append.



(* ---------------------------------------------------------------------- *)
(** Destructive append *)

Definition inplace_append : val :=
  VFix 'f 'p1 'p2 :=
    If_ is_nil 'p1 
      Then 'p1 ':= '! 'p2
      Else 'f (tail 'p1) 'p2.

Lemma Triple_inplace_append : forall `{EA:Enc A} (L1 L2:list A) (p1 p2:loc),
  TRIPLE (inplace_append p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (_:unit) => p1 ~> MList (L1++L2)).
Proof using.
  intros. gen p1. induction_wf IH: (@list_sub A) L1. intros.
  xwp. xif ;=> C. 
  { hchanges (MList_eq p1) ;=> v1. hchanges (MList_eq p2) ;=> v2.
    xapp. xapp. hchanges* <- (MList_eq p1). }
  { hchanges~ (MList_not_nil_unfold p1) ;=> x L1' p1' ->.
    xapp. xapp*. hchanges (MList_cons_fold p1). }
Qed.

Hint Extern 1 (Register_Spec (inplace_append)) => Provide @Triple_inplace_append.


(* ---------------------------------------------------------------------- *)
(** CPS append *)

Definition cps_append_aux : val :=
  VFix 'f 'p1 'p2 'k :=
    If_ is_nil 'p1 
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
  xwp. xapp (>> __ EA). (* LATER: resolve typeclass better *)
  xif ;=> C.
  { subst. xapp. hsimpl~. }
  { hchanges~ (MList_not_nil_unfold p1) ;=> x L1' p1' ->.
    xapp (>> __ EA). xfun. 
    (* LATER: xapp (>> IH L1' (H \* (p1 ~~> Cons x p1'))). *)
    lets IH': (>> (rm IH) L1' (H \* (p1 ~~> Cons x p1'))).
    { autos*. }
    xapp IH'; clear IH'. (* LATER: xapp (rm IH') *)
    { intros p3. xwp. xapp (>> __ EA). xapp. 
      hchanges (MList_cons_fold p1). }
    hsimpl*. }
Qed.

(* Hint Extern 1 (Register_Spec (cps_append_aux)) => Provide @Triple_cps_append_aux. *)

Lemma Triple_mlist_cps_append : forall A `{EA:Enc A} (L1 L2:list A) (p1 p2:loc),
  TRIPLE (cps_append ``p1 ``p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun p3 => p3 ~> MList (L1 ++ L2)).
Proof using.
  intros. xwp. xfun. xapp (>> (@Triple_cps_append_aux) \[] (fun p3 => p3 ~> MList (L1 ++ L2))).
  { intros p3. xwp. xval. hsimpl. }
  hsimpl.
Qed.


(* Note that the continuation k' used in the recursive call
   could be given the following spec, rather than inlining its code:
     Triple (k' ``r)
       PRE (p ~~> (x,p') \* r ~> Mlist (L'++M) \* H)
       POST Q.
*)

(* LATER:    length : using loop *)





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
  { intros x K T E. xwp. xappn. hsimpl*. }
  xapp. hsimpl~.
Qed.


(* ---------------------------------------------------------------------- *)
(** Alternative spec and proofs for set_nil *)

Lemma Triple_set_nil_of_MList : forall A `{EA:Enc A} (L:list A) p,
  TRIPLE (set_nil ``p)
    PRE (p ~> MList L)
    POST (fun (_:unit) => p ~> MList (@nil A)).
Proof using.
  intros. xtriple. hchange @MList_eq ;=> v. xapp. rewrite MList_nil_eq. hsimpl.
Qed.

Lemma Triple_set_nil_of_MList_direct_proof : forall A `{EA:Enc A} (L:list A) p,
  TRIPLE (set_nil ``p)
    PRE (p ~> MList L)
    POST (fun (_:unit) => p ~> MList (@nil A)).
Proof using.
  intros. xwp. hchange MList_eq ;=> v.
  xval (Nil). xapp. rewrite MList_nil_eq. hsimpl.
Qed.

(* ---------------------------------------------------------------------- *)
(** Detailed proof for is_nil *)

Lemma Triple_is_nil' : forall A `{EA:Enc A} (L:list A) p,
  TRIPLE (is_nil ``p)
    PRE (p ~> MList L)
    POST (fun (b:bool) => \[b = isTrue (L = nil)] \* p ~> MList L).
Proof using.
  intros. xwp. hchange MList_eq ;=> v. xapp. 
  applys xcase_lemma0 ;=> E1.
  { rew_enc in E1. subst. hchange MList_contents_Nil ;=> ->.
    hchange MList_nil_fold. xval. hsimpl~. }
  { applys xcase_lemma2.
    { intros x' q' E. rew_enc in E. inverts E. unfold MList_contents.
      destruct L as [|x L'].
      { hpull. }
      { xval. hpull ;=> p' E'. hchange (MList_cons_fold p). applys E'.
        hsimpl. auto_false. } }
    { intros N. unfold MList_contents. destruct L as [|x L']; hpull.
      { intros ->. rewrite enc_val_eq in *. unfolds Nil. false. }
      { intros q ->. rewrite enc_val_eq in *. unfolds @Cons. false. } } }
Qed.


(* ---------------------------------------------------------------------- *)
(** Detailed proof for set_head *)

(*
Lemma Triple_set_head' : forall A `{EA:Enc A} (L:list A) p x y,
  TRIPLE (set_head ``p ``y)
    PRE (p ~> MList (x::L))
    POST (fun (_:unit) => p ~> MList (y::L)).
Proof using.
  intros. (*  xwp. xgc_post. *) xwp_fun' tt.
  hchange MList_cons_unfold ;=> q. xapp.
  applys xcase_lemma0 ;=> E1.
  { false. }
  { applys xcase_lemma2.
    { intros x' q' E. unfold Cons in E. rew_enc in E. inverts E.
      xval (Cons y q). xapp. hchanges MList_cons_fold. }
    { intros N. false N. reflexivity. } }
Qed.
*)


End MList.

