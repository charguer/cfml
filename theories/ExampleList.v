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


(* ********************************************************************** *)
(* * Representation *)

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


Lemma MList_eq' : forall (p:loc) A `{EA:Enc A} (L:list A),
  p ~> MList L = (\exists v, p ~~> v \* MList_contents v L).
Proof using. intros. destruct L; auto. Qed.

Lemma MList_eq : forall A `{EA:Enc A} (L:list A) (p:loc),
  p ~> MList L = (\exists v, p ~~> v \* MList_contents v L).
Proof using. intros. destruct L; auto. Qed.

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

Lemma MList_cons_fold : forall (p:loc) A `{EA:Enc A} x p' (L':list A),
  p ~~> (Cons x p') \* (p' ~> MList L') ==> p ~> MList (x::L').
Proof using. intros. rewrite (MList_eq (x::L')). unfold MList_contents. hsimpl~. Qed.

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

Lemma Triple_set_nil : forall A `{EA:Enc A} (L:list A) p v,
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

Lemma Triple_set_cons : forall A `{EA:Enc A} (L:list A) p v x q,
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
  { (* nil *)
    xval 0. hsimpl*. }
  { (* cons *)
    destruct L as [|x L']; tryfalse. hchange MList_cons_unfold ;=> p'.
    xapp. xapp~. xapp~. hchange MList_cons_fold. hsimpl*. }
Qed.


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
  { (* nil *)
    xapp ;=> p'. hsimpl*. }
  { (* cons *)
    destruct L as [|x L']; tryfalse.
    hchange MList_cons_unfold ;=> p'.
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
  { destruct L2 as [|x L2']; tryfalse. hchange MList_cons_unfold ;=> p'.
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
    iter (Fun 'x := ('n ':= ('!'n '+ 1))) 'p ';
    '! 'n.

(*
Definition length_using_iter' : val :=
  VFun 'p :=
    Let 'n := val_ref ``0 in
    LetFun 'f 'x := incr 'n in
    iter 'f 'p ';
    '! 'n.
*)

Lemma Triple_mlist_length_using_iter : forall A `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (length_using_iter ``p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  xwp. xapp ;=> n. xfun.
  xapp (>> __ (fun (K:list A) => n ~~> (length K:Z))). (* TODO: __ *)
  { intros x K T E. xwp. xappn. hsimpl*. }
  xapp. hsimpl~.
Qed.




(* ---------------------------------------------------------------------- *)
(** Proof details *)


Lemma Triple_set_nil' : forall A `{EA:Enc A} (L:list A) p,
  TRIPLE (set_nil ``p)
    PRE (p ~> MList L)
    POST (fun (_:unit) => p ~> MList (@nil A)).
Proof using.
  intros. xwp. hchange MList_eq ;=> v.
  xval (Nil). xapp. rewrite MList_nil_eq. hsimpl.
Qed.

(** Same proof with details *)

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

(*

-----------


(* ---------------------------------------------------------------------- *)
(** Old code revealing implementation *)

Module MListReveal.

(* ---------------------------------------------------------------------- *)
(** Length -- code revealing implementation *)

Definition val_mlist_length : val :=
  VFix 'f 'p :=
    Match '! 'p With
    '| 'Cstr "nil" '=> 0
    '| 'Cstr "cons" 'x 'q '=> 1 '+ 'f 'q
    End.

Lemma Triple_mlist_length : forall `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (val_mlist_length p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  intros. gen p. induction_wf IH: (@list_sub A) L. intros.
  xwp. 
  (* TODO tactic: *) applys himpl_trans'. applys Mlist_unfold_match'. hsimpl.
  (* TODO tactic: *) applys himpl_hand_r; hsimpl.
  (* applys applys Mlist_unfold_match. *)
  { (* nil *)
    intros EL. xval 0. hsimpl. subst. rew_list~. } 
  { (* cons *) 
    intros p' x' L' ->. xlet. xapp* IH. xapp. 
    hchanges (MList_cons_fold p). rew_list; math. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Length detailed -- code revealing implementation *)

Lemma Triple_mlist_length_detailed : forall `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (val_mlist_length p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  intros. gen p. induction_wf IH: (@list_sub A) L. intros.
  xwp.
  xlet. hchanges (MList_unfold L) ;=> v. xapp.
  (* xcase *)
  applys xcase_lemma0 ;=> E1.
  { destruct L as [|x L']; hpull.
    { intros ->. applys~ @xval_lemma 0. hsimpl. rew_list~. rewrite~ MList_nil_eq. hsimpl. }
    { intros q ->. tryfalse. } }
  { applys xcase_lemma2.
    { intros x q E.
      destruct L as [|x' L']; hpull.
      { intros ->. tryfalse. }
      { intros p' E'. subst v. rewrite enc_val_eq in *. inverts E.
        xlet. xapp* IH. xapp. 
        hchanges (MList_cons_fold p). rew_list; math. } }
    { intros N. destruct L as [|x L']; hpull.
      { intros ->. rewrite enc_val_eq in *. unfolds Nil. false. }
      { intros q ->. rewrite enc_val_eq in *. unfolds @Cons. false. } } }
Qed.


(* ---------------------------------------------------------------------- *)
(** Copy -- code revealing implementation *)

Definition val_mlist_copy : val :=
  VFix 'f 'p :=
    Match '! 'p With
    '| 'Cstr "nil" '=> val_ref ('Cstr "nil")
    '| 'Cstr "cons" 'x 'p2 '=> val_ref ('Cstr "cons" 'x ('f 'p2))
    End.

Lemma Triple_mlist_copy : forall `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (val_mlist_copy p)
    PRE (p ~> MList L)
    POST (fun (q:loc) => p ~> MList L \* q ~> MList L).
Proof using.
  intros. gen p. induction_wf IH: (@list_sub A) L. intros.
  xwp. (* TODO: tactic *) applys himpl_trans'. applys Mlist_unfold_match'. hsimpl. 
  applys himpl_hand_r; hsimpl.
  { (* nil *)
     intros ->. xval Nil. xapp ;=> q. hchanges (MList_nil_fold q). }
  { (* cons *)
    intros p2 x L2 ->.
    xlet. xapp* IH ;=> q'. xval (Cons x q'). xapp ;=> q. 
    hchange (MList_cons_fold q). hchanges (MList_cons_fold p). }
Qed.

(* LATER: copy using loop *)



(* ---------------------------------------------------------------------- *)
(** Append nondestructive -- code revealing implementation *)

Definition val_mlist_nondestructive_append : val :=
  VFix 'f 'p1 'p2 :=
    Match '! 'p1 With
    '| 'Cstr "nil" '=> val_mlist_copy 'p2
    '| 'Cstr "cons" 'x 'q1 '=> val_ref ('Cstr "cons" 'x ('f 'q1 'p2))  
    End.

Lemma Triple_mlist_nondestructive_append : forall `{EA:Enc A} (L1 L2:list A) (p1 p2:loc),
  TRIPLE (val_mlist_nondestructive_append p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (p3:loc) => p1 ~> MList L1 \* p2 ~> MList L2 \* p3 ~> MList (L1++L2)).
Proof using.
  intros. gen p1. induction_wf IH: (@list_sub A) L1. intros.
  xwp. (* TODO: tactic *)  applys himpl_trans'. applys Mlist_unfold_match'. hsimpl. 
  applys himpl_hand_r; hsimpl.
  { (* nil *)
     intros ->. xapp Triple_mlist_copy ;=> p3. hsimpl. }
  { (* cons *) 
    intros p' x L' ->.
    xapp* IH ;=> p3'. hchanges (MList_cons_fold p1). 
    xval (Cons x p3'). xapp ;=> p3.
    hchanges (MList_cons_fold p3). }
Qed.



(* ---------------------------------------------------------------------- *)
(** Append inplace -- code revealing implementation *)

Definition val_mlist_inplace_append : val :=
  VFix 'f 'p1 'p2 :=
    Match '! 'p1 With
    '| 'Cstr "nil" '=> 'p1 ':= '! 'p2
    '| 'Cstr "cons" 'x 'q1 '=> 'f 'q1 'p2
    End.

Arguments MList_eq : clear implicits.

Lemma Triple_mlist_inplace_append : forall `{EA:Enc A} (L1 L2:list A) (p1 p2:loc),
  TRIPLE (val_mlist_inplace_append p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (_:unit) => p1 ~> MList (L1++L2)).
Proof using.
  intros. gen p1. induction_wf IH: (@list_sub A) L1. intros.
  xwp. applys himpl_trans'. applys Mlist_unfold_match'. hsimpl. 
  applys himpl_hand_r; hsimpl.
  { (* nil *)
     intros ->. rew_list.
     hchanges (MList_eq' p2) ;=> v2.
     hchanges (MList_eq' p1) ;=> v1.
     xapp.
     applys structural_hgc. applys structural_MkStruct. (* TODO: xgc *)
     xapp. (* todo : gc by default in xapp ? *) hchange <- (MList_eq' p1). } 
  { (* cons *) 
    intros p' x L' ->.
    xapp* IH. hchanges (MList_cons_fold p1). }
Qed.

End MListReveal.

(* LATER:    length : using loop *)

End MList.







------------
(* ********************************************************************** *)
(* * Formalization of mutable lists, with lifting *)

(* ---------------------------------------------------------------------- *)
(* ** Fields *)

Definition hd : field := 0%nat.
Definition tl : field := 1%nat.

Notation "'val_get_hd'" := (val_get_field hd).
Notation "'val_get_tl'" := (val_get_field tl).
Notation "'val_set_hd'" := (val_set_field hd).
Notation "'val_set_tl'" := (val_set_field tl).


(* ---------------------------------------------------------------------- *)
(* ** Representation *)

Fixpoint MList A `{EA:Enc A} (L:list A) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists (p':loc), (p ~> Record`{ hd := x; tl := p' }) \* (p' ~> MList L')
  end.

Notation "'MCell' x q" :=
  (Record`{ hd := x; tl := q })
  (at level 19, x at level 0, q at level 0).


(* ---------------------------------------------------------------------- *)
(* ** Lemmas *)

Section Properties.

(** Conversion lemmas for empty lists *)

Lemma MList_nil_eq : forall p A `{EA:Enc A},
  (p ~> MList (@nil A)) = \[p = null].
Proof using. intros. xunfold~ MList. Qed.

Lemma MList_nil : forall A `{EA:Enc A},
  \[] ==> (null ~> MList (@nil A)).
Proof using. intros. rewrite MList_nil_eq. hsimpl~. Qed.

Lemma MList_null_eq : forall A `{EA:Enc A} (L:list A),
  (null ~> MList L) = \[L = nil].
Proof using.
  intros. destruct L.
  { xunfold MList. applys himpl_antisym; hsimpl~. }
  { xunfold MList. applys himpl_antisym.
    { hpull ;=> p'. hchange (hRecord_not_null null).
      { simpl. unfold hd. auto. } }
    { hpull. } }
Qed.

Lemma MList_null_inv : forall A `{EA:Enc A} (L:list A),
  null ~> MList L ==> null ~> MList L \* \[L = nil].
Proof using.
  intros. destruct L.
  { hsimpl~. }
  { rewrite MList_null_eq. hsimpl. }
Qed.

(** Conversion lemmas for non-empty lists *)

Lemma MList_cons_eq : forall p A `{EA:Enc A} (x:A) L',
  p ~> MList (x::L') =
  \exists p', (p ~> Record`{ hd := x; tl := p' }) \* p' ~> MList L'.
Proof using. intros. xunfold MList at 1. simple~. Qed.

Lemma MList_cons : forall p p' A `{EA:Enc A} (x:A) L',
  (p ~> Record`{ hd := x; tl := p' }) \* p' ~> MList L' ==>
  p ~> MList (x::L').
Proof using. intros. rewrite MList_cons_eq. hsimpl. Qed.

Lemma MList_not_null_inv_not_nil : forall p A `{EA:Enc A} (L:list A),
  p <> null ->
  p ~> MList L ==> p ~> MList L \* \[L <> nil].
Proof using.
  intros. destruct L.
  { hchanges -> (MList_nil_eq p). }
  { hsimpl. auto_false. }
Qed.

Lemma MList_not_null_inv_cons : forall p A `{EA:Enc A} (L:list A),
  p <> null ->
  p ~> MList L ==> \exists x p' L',
       \[L = x::L']
    \* (p ~> Record`{ hd := x; tl := p' })
    \* p' ~> MList L'.
Proof using.
  intros. hchange~ (@MList_not_null_inv_not_nil p). hpull. intros.
  destruct L; tryfalse.
  hchange (MList_cons_eq p). hsimpl~.
Qed.

End Properties.

Arguments MList_null_inv : clear implicits.
Arguments MList_cons_eq : clear implicits.
Arguments MList_cons : clear implicits.
Arguments MList_not_null_inv_not_nil : clear implicits.
Arguments MList_not_null_inv_cons : clear implicits.

Global Opaque MList.



(* ---------------------------------------------------------------------- *)
(** Representation *)

Fixpoint MListSeg `{EA:Enc A} (q:loc) (L:list A) (p:loc) : hprop :=
  match L with
  | nil => \[p = q]
  | x::L' => \exists (p':loc), (p ~> MCell x p') \* (p' ~> MListSeg q L')
  end.


(* ---------------------------------------------------------------------- *)
(** Properties *)

Section SegProperties.

Lemma MListSeg_nil_eq : forall `{EA:Enc A} p q,
  p ~> (MListSeg q (@nil A)) = \[p = q].
Proof using. intros. xunfold~ MListSeg. Qed.

Lemma MListSeg_cons_eq : forall `{EA:Enc A} p q x (L':list A),
  p ~> MListSeg q (x::L') =
  \exists (p':loc), (p ~> MCell x p') \* p' ~> MListSeg q L'.
Proof using. intros. xunfold MListSeg at 1. simple~. Qed.

Global Opaque MListSeg.

Lemma MListSeg_nil : forall `{EA:Enc A} p,
  \[] ==> p ~> MListSeg p (@nil A).
Proof using. intros. rewrite MListSeg_nil_eq. hsimpl~. Qed.

Lemma MListSeg_cons : forall `{EA:Enc A} p p' q x (L':list A),
  p ~> (MCell x p') \* p' ~> MListSeg q L' ==> p ~> MListSeg q (x::L').
Proof using. intros. rewrite MListSeg_cons_eq. hsimpl. Qed.

Lemma MListSeg_one : forall `{EA:Enc A} p q (x:A),
  p ~> (MCell x q) ==> p ~> MListSeg q (x::nil).
Proof using.
  intros. hchange (MListSeg_nil q). hchanges (>> MListSeg_cons p).
Qed.

Lemma MListSeg_to_MList : forall `{EA:Enc A} p (L:list A),
  p ~> MListSeg null L ==> p ~> MList L.
Proof using.
  intros. gen p. induction L; intros.
  { rewrite MListSeg_nil_eq. rewrite MList_nil_eq. auto. }
  { rewrite MListSeg_cons_eq. rewrite MList_cons_eq.
    hpull ;=> p'. hchange IHL. hsimpl~. }
Qed.

Lemma MListSeg_concat : forall `{EA:Enc A} p1 p2 p3 (L1 L2:list A),
  p1 ~> MListSeg p2 L1 \* p2 ~> MListSeg p3 L2 ==> p1 ~> MListSeg p3 (L1++L2).
Proof using.
  intros. gen p1. induction L1 as [|x L1']; intros.
  { rewrite MListSeg_nil_eq. hpull ;=> E. subst. rew_list~. }
  { rew_list. hchange (MListSeg_cons_eq p1). hpull ;=> p1'.
    hchange (IHL1' p1'). hchanges (>> MListSeg_cons p1). }
Qed.

Lemma MListSeg_last : forall `{EA:Enc A} p1 p2 p3 x (L:list A),
  p1 ~> MListSeg p2 L \* p2 ~> (MCell x p3) ==> p1 ~> MListSeg p3 (L&x).
Proof using.
  intros. hchange (>> MListSeg_one p2). hchanges (>> (@MListSeg_concat) p1 p2).
Qed.

End SegProperties.



(* ---------------------------------------------------------------------- *)
(* ** Node allocation *)

(*
Definition val_new_cell : val := val_new_record 2%nat.

(** Above equivalent to :

Definition val_new_cell :=
  ValFun 'x 'y :=
    Let 'p := val_alloc 2 in
    val_set_item 'p 'x;;;
    val_set_left 'p 'y;;;
    'p.
*)
*)(**

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


(* ********************************************************************** *)
(* * Formalization of mutable lists, with lifting *)

(* ---------------------------------------------------------------------- *)
(* ** Fields *)

Definition hd : field := 0%nat.
Definition tl : field := 1%nat.

Notation "'val_get_hd'" := (val_get_field hd).
Notation "'val_get_tl'" := (val_get_field tl).
Notation "'val_set_hd'" := (val_set_field hd).
Notation "'val_set_tl'" := (val_set_field tl).


(* ---------------------------------------------------------------------- *)
(* ** Representation *)

Fixpoint MList A `{EA:Enc A} (L:list A) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists (p':loc), (p ~> Record`{ hd := x; tl := p' }) \* (p' ~> MList L')
  end.

Notation "'MCell' x q" :=
  (Record`{ hd := x; tl := q })
  (at level 19, x at level 0, q at level 0).


(* ---------------------------------------------------------------------- *)
(* ** Lemmas *)

Section Properties.

(** Conversion lemmas for empty lists *)

Lemma MList_nil_eq : forall p A `{EA:Enc A},
  (p ~> MList (@nil A)) = \[p = null].
Proof using. intros. xunfold~ MList. Qed.

Lemma MList_nil : forall A `{EA:Enc A},
  \[] ==> (null ~> MList (@nil A)).
Proof using. intros. rewrite MList_nil_eq. hsimpl~. Qed.

Lemma MList_null_eq : forall A `{EA:Enc A} (L:list A),
  (null ~> MList L) = \[L = nil].
Proof using.
  intros. destruct L.
  { xunfold MList. applys himpl_antisym; hsimpl~. }
  { xunfold MList. applys himpl_antisym.
    { hpull ;=> p'. hchange (hRecord_not_null null).
      { simpl. unfold hd. auto. } }
    { hpull. } }
Qed.

Lemma MList_null_inv : forall A `{EA:Enc A} (L:list A),
  null ~> MList L ==> null ~> MList L \* \[L = nil].
Proof using.
  intros. destruct L.
  { hsimpl~. }
  { rewrite MList_null_eq. hsimpl. }
Qed.

(** Conversion lemmas for non-empty lists *)

Lemma MList_cons_eq : forall p A `{EA:Enc A} (x:A) L',
  p ~> MList (x::L') =
  \exists p', (p ~> Record`{ hd := x; tl := p' }) \* p' ~> MList L'.
Proof using. intros. xunfold MList at 1. simple~. Qed.

Lemma MList_cons : forall p p' A `{EA:Enc A} (x:A) L',
  (p ~> Record`{ hd := x; tl := p' }) \* p' ~> MList L' ==>
  p ~> MList (x::L').
Proof using. intros. rewrite MList_cons_eq. hsimpl. Qed.

Lemma MList_not_null_inv_not_nil : forall p A `{EA:Enc A} (L:list A),
  p <> null ->
  p ~> MList L ==> p ~> MList L \* \[L <> nil].
Proof using.
  intros. destruct L.
  { hchanges -> (MList_nil_eq p). }
  { hsimpl. auto_false. }
Qed.

Lemma MList_not_null_inv_cons : forall p A `{EA:Enc A} (L:list A),
  p <> null ->
  p ~> MList L ==> \exists x p' L',
       \[L = x::L']
    \* (p ~> Record`{ hd := x; tl := p' })
    \* p' ~> MList L'.
Proof using.
  intros. hchange~ (@MList_not_null_inv_not_nil p). hpull. intros.
  destruct L; tryfalse.
  hchange (MList_cons_eq p). hsimpl~.
Qed.

End Properties.

Arguments MList_null_inv : clear implicits.
Arguments MList_cons_eq : clear implicits.
Arguments MList_cons : clear implicits.
Arguments MList_not_null_inv_not_nil : clear implicits.
Arguments MList_not_null_inv_cons : clear implicits.

Global Opaque MList.



(* ---------------------------------------------------------------------- *)
(** Representation *)

Fixpoint MListSeg `{EA:Enc A} (q:loc) (L:list A) (p:loc) : hprop :=
  match L with
  | nil => \[p = q]
  | x::L' => \exists (p':loc), (p ~> MCell x p') \* (p' ~> MListSeg q L')
  end.


(* ---------------------------------------------------------------------- *)
(** Properties *)

Section SegProperties.

Lemma MListSeg_nil_eq : forall `{EA:Enc A} p q,
  p ~> (MListSeg q (@nil A)) = \[p = q].
Proof using. intros. xunfold~ MListSeg. Qed.

Lemma MListSeg_cons_eq : forall `{EA:Enc A} p q x (L':list A),
  p ~> MListSeg q (x::L') =
  \exists (p':loc), (p ~> MCell x p') \* p' ~> MListSeg q L'.
Proof using. intros. xunfold MListSeg at 1. simple~. Qed.

Global Opaque MListSeg.

Lemma MListSeg_nil : forall `{EA:Enc A} p,
  \[] ==> p ~> MListSeg p (@nil A).
Proof using. intros. rewrite MListSeg_nil_eq. hsimpl~. Qed.

Lemma MListSeg_cons : forall `{EA:Enc A} p p' q x (L':list A),
  p ~> (MCell x p') \* p' ~> MListSeg q L' ==> p ~> MListSeg q (x::L').
Proof using. intros. rewrite MListSeg_cons_eq. hsimpl. Qed.

Lemma MListSeg_one : forall `{EA:Enc A} p q (x:A),
  p ~> (MCell x q) ==> p ~> MListSeg q (x::nil).
Proof using.
  intros. hchange (MListSeg_nil q). hchanges (>> MListSeg_cons p).
Qed.

Lemma MListSeg_to_MList : forall `{EA:Enc A} p (L:list A),
  p ~> MListSeg null L ==> p ~> MList L.
Proof using.
  intros. gen p. induction L; intros.
  { rewrite MListSeg_nil_eq. rewrite MList_nil_eq. auto. }
  { rewrite MListSeg_cons_eq. rewrite MList_cons_eq.
    hpull ;=> p'. hchange IHL. hsimpl~. }
Qed.

Lemma MListSeg_concat : forall `{EA:Enc A} p1 p2 p3 (L1 L2:list A),
  p1 ~> MListSeg p2 L1 \* p2 ~> MListSeg p3 L2 ==> p1 ~> MListSeg p3 (L1++L2).
Proof using.
  intros. gen p1. induction L1 as [|x L1']; intros.
  { rewrite MListSeg_nil_eq. hpull ;=> E. subst. rew_list~. }
  { rew_list. hchange (MListSeg_cons_eq p1). hpull ;=> p1'.
    hchange (IHL1' p1'). hchanges (>> MListSeg_cons p1). }
Qed.

Lemma MListSeg_last : forall `{EA:Enc A} p1 p2 p3 x (L:list A),
  p1 ~> MListSeg p2 L \* p2 ~> (MCell x p3) ==> p1 ~> MListSeg p3 (L&x).
Proof using.
  intros. hchange (>> MListSeg_one p2). hchanges (>> (@MListSeg_concat) p1 p2).
Qed.

End SegProperties.



(* ---------------------------------------------------------------------- *)
(* ** Node allocation *)

(*
Definition val_new_cell : val := val_new_record 2%nat.

(** Above equivalent to :

Definition val_new_cell :=
  ValFun 'x 'y :=
    Let 'p := val_alloc 2 in
    val_set_item 'p 'x;;;
    val_set_left 'p 'y;;;
    'p.
*)
*)

Parameter val_new_cell : val.

Lemma Triple_new_cell : forall `{EA:Enc A} (x:A) (q:loc),
  TRIPLE (val_new_cell ``x ``q)
    PRE \[]
    POST (fun p => (p ~> MCell x q)).
(*
Proof using. xtriple_new_record. Qed.
*)
Admitted.

Hint Extern 1 (Register_Spec val_new_cell) => Provide Triple_new_cell.

Opaque val_new_cell.


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
  intros. gen p. induction_wf IH: list_sub_wf L. xcf.
  xapps~. xif ;=> C.
  { xval. subst p. rewrite MList_null_eq. hsimpl~. }
  { xchanges~ (MList_not_null_inv_cons p) ;=> x p1 T1 E.
    subst. xapps. xapps. xapp~ as p1'. xapp.
    intros p'. do 2 rewrite MList_cons_eq. hsimpl. }
Qed.

Hint Extern 1 (Register_Spec val_mlist_copy) => Provide Triple_mlist_copy.



(* ********************************************************************** *)
(* * Length of a mutable list *)

(** Note: same definition as in [ExampleListNonLifted] *)

Definition val_mlist_length : val :=
  VFix 'f 'p :=
    If_ 'p '<> null Then (
      Let 'q := val_get_tl 'p in
      Let 'n := 'f 'q in
      val_add 'n 1
    ) Else (
      0
    ).

Lemma Triple_mlist_length : forall A `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (val_mlist_length ``p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  intros. gen p. induction_wf: list_sub_wf L; intros. xcf.
  xapps~. xif ;=> C.
  { xchanges~ (MList_not_null_inv_cons p) ;=> x p' L' EL.
    xapps. xapps~ (IH L'). xchange (MList_cons p).
    xapps. hsimpl ;=> ? ->. auto. }
  { subst. xchanges MList_null_inv ;=> EL. xvals~. }
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
  { subst. xchanges MList_null_inv ;=> EL. xapp.
    intros p. subst. rew_list. hsimpl. }
  { xchanges~ (MList_not_null_inv_cons p1) ;=> x p1' L' EL.
    xapps. xapps. xapp~ as p'. xapps. intros p. subst. rew_list.
    hchange~ (>> MList_cons p Enc_int).
    hchanges~ (>> MList_cons p1 Enc_int). }
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
  { intros. xchange (MListSeg_nil p1). xapplys (K L nil L). rew_list~. }
  intros. gen p3 L1. induction_wf: list_sub_wf L2; intros. xcf.
  xapps~. xif ;=> C.
  { subst. xchanges MList_null_inv ;=> EL. subst. rew_list.
    rewrite MList_nil_eq. xpull ;=> _.
    xchange (>> (@MListSeg_to_MList int) p1).
    xapp. intros p. rew_list. hsimpl. }
  { xchanges~ (MList_not_null_inv_cons p3) ;=> x p3' L2' EL2.
    xapps. xapps.
    xchange (>> (@MListSeg_last int) p1).
    xapp~ (>> IH L2' (L1&x)) as p'. xapps.
    intros p. hchange~ (>> (@MList_cons) p Enc_int).
    subst. rew_list. hsimpl. }
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
    xlet. { xapps. xapps~. } xpull ;=> ? ->. xif ;=> C.
    { xchanges~ (MList_not_null_inv_cons p) ;=> p' x L' EL. xseq.
      { xseq. xapp~. xapps. xapps. xapps~. }
      { xapply~ (>> IH L'). { hsimpl. } { hpull. hchanges~ (MList_cons p). } } }
    { inverts C. xchanges MList_null_inv ;=> EL. xvals~. }
  { xapp. hsimpl~. } }
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
  { xchanges~ (MList_not_null_inv_cons p) ;=> x p' L' EL.
    xapps. xapps. xapps. xapps. xapps~.
    hchanges~ (>> MList_cons p Enc_int). }
  { subst. xchanges MList_null_inv ;=> EL. xvals~. }
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
    { hchange MList_nil. unfold I. hsimpl*. }
    { intros F LF b L1 IH. unfold I at 1. xpull ;=> p s L2 E1 E2. clears b.
      xlet. { xapps. xapps~. } xpull ;=> ? ->.
      xif ;=> Cb.
      { xchanges~ (MList_not_null_inv_cons p) ;=> x p1' L1' EL1.
        xseq. (* todo: problem of parentheses around xwhile body *)
        { xapps. xapps. xapps. xapps. xapps. xapps. }
        { xapps~. { unfold I. hchanges~ (MList_cons p). } } }
      { xval. subst p. unfold I. hchanges~ MList_null_inv. } }
    { hsimpl. } }
  { xpull ;=> L1 p s L2 E1 E2. xapp. hpull ;=> ? ->. hsimpl~. }
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
  { subst. xchanges MList_null_eq ;=> E. subst. xapp. hsimpl~. }
  { xval ;=> F EF. sets R: (5%nat). (* todo: hide number *)
    xchanges~ (MList_not_null_inv_cons p) ;=> x p' L' EL.
    xapps. xapp (>> IH (H \* (p ~> Record`{hd:=x; tl:=p'}))).
    { subst~. }
    { intros r. subst F. xcf.
      xapps. simpl. (* todo: maybe should be done by xapps *)
      xchange (MList_cons p). subst L. xapps. hsimpl~. }
    { hsimpl. } }
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
  { subst. xchanges MList_null_inv ;=> EL. xapp.
    intros p. subst. rew_list. hsimpl. }
  { xchanges~ (MList_not_null_inv_cons p1) ;=> x p1' L' EL.
    xapps. xapps. xapp~ as p'. xapps. intros p. subst. rew_list.
    hchange~ (>> MList_cons p Enc_int).
    hchanges~ (>> MList_cons p1 Enc_int). }
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
    xlet. { xapps. xapps~. } xpull ;=> ? ->. xif ;=> C.
    { xchanges~ (MList_not_null_inv_cons p) ;=> p' x L' EL. xseq.
      { xseq. xapp~. xapps. xapps. xapps~. }
      { xapply~ (>> IH L'). { hsimpl. } { hpull. hchanges~ (MList_cons p). } } }
    { inverts C. xchanges MList_null_inv ;=> EL. xvals~. }
  { xapp. hsimpl~. } }
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
    { hchange MList_nil. unfold I. hsimpl*. }
    { intros F LF b L1 IH. unfold I at 1. xpull ;=> p s L2 E1 E2. clears b.
      xlet. { xapps. xapps~. } xpull ;=> ? ->.
      xif ;=> Cb.
      { xchanges~ (MList_not_null_inv_cons p) ;=> x p1' L1' EL1.
        xseq. (* todo: problem of parentheses around xwhile body *)
        { xapps. xapps. xapps. xapps. xapps. xapps. }
        { xapps~. { unfold I. hchanges~ (MList_cons p). } } }
      { xval. subst p. unfold I. hchanges~ MList_null_inv. } }
    { hsimpl. } }
  { xpull ;=> L1 p s L2 E1 E2. xapp. hpull ;=> ? ->. hsimpl~. }
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
  { subst. xchanges MList_null_eq ;=> E. subst. xapp. hsimpl~. }
  { xval ;=> F EF. sets R: (5%nat). (* todo: hide number *)
    xchanges~ (MList_not_null_inv_cons p) ;=> x p' L' EL.
    xapps. xapp (>> IH (H \* (p ~> Record`{hd:=x; tl:=p'}))).
    { subst~. }
    { intros r. subst F. xcf.
      xapps. simpl. (* todo: maybe should be done by xapps *)
      xchange (MList_cons p). subst L. xapps. hsimpl~. }
    { hsimpl. } }
Qed.

(* Note that K' could be given the following spec, rather than inlining its code:
     Triple (k' ``r)
       PRE (p ~~> (x,p') \* r ~> Mlist (L'++M) \* H)
       POST Q.
*)

*)

