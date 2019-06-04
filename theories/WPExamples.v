(**

This file provides examples of proofs manipulating characteristic formula 
in weakest-precondition form, in lifted Separation Logic,
as defined in [WPLifted.v].

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
From Sep Require Export WPRecord.
Generalizable Variables A B.

Import NotationForVariables NotationForTerms.
Open Scope val_scope.
Open Scope pat_scope.
Open Scope trm_scope.


(* TODO *)
Lemma himpl_trans' : forall (H1 H2 H3:hprop),
  H2 ==> H3 ->
  H1 ==> H2 ->
  H1 ==> H3.
Proof using. introv M1 M2. applys* himpl_trans. Qed.


(* ********************************************************************** *)
(* * Let *)

Definition xlet_test : val :=
  VFun 'p :=
     Let 'p := 3 in 
     'p.




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
  VFun 'p :=
   Set 'p'.X ':= ('p'.X '+ 1) ';
   Set 'p'.K ':= ('p'.K '+ 1).


Lemma Triple_move_X : forall p x y,
  TRIPLE (val_move_X p)
    PRE (Point x y p)
    POST (fun (_:unit) => (Point (x+1) y p)).
Proof using.
  xwp.
  xunfolds Point ;=> k Hk. 
(* TEST
  xseq. xlet. xlet. xapp_record tt.
notypeclasses refine (xapp_lemma _ _ ). xapp. eapply @triple_add.
 xapp.
 xapp.
  xapp. eapply @xapp_lemma. lets: triple_add. simpls. unfold trms_vals. rew_enc. rew_listx. eapply H. Transparent trm_apps. eapply H. rew_trm_apps.
notypeclasses refine (xlet_lemma _ _ _ _ _).
*)
  xappn. hsimpl. math.
Qed.


End Point.


(* ********************************************************************** *)
(* * Mutable lists *)


Module MList.


Definition Nil : val := val_constr "nil" nil.
Definition Cons `{Enc A} (V:A) (p:loc) : val := val_constr "cons" (``V::``p::nil).

(*
  course -> For recursive predicate: would be useful to recall the duality between
  `Fixpoint` and `Inductive` for defining predicates, taking the example of `In` and `Forall` on lists.
*)


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


(* ---------------------------------------------------------------------- *)
(** Length *)

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
(** Length detailed *)

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
    { intros ->. applys~ @xval_lemma 0. hsimpl. rew_list~. rewrite~ MList_nil_eq. }
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
(** Copy *)

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
    hchange (MList_cons_fold q). hchange (MList_cons_fold p). }
Qed.

(* LATER: copy using loop *)



(* ---------------------------------------------------------------------- *)
(** Append nondestructive *)

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
(** Append inplace *)

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



(* LATER:    length : using loop *)

End MList.


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
  { hpull ;=> ? ->. auto. }
  { hsimpl~. }
Qed.



(* ---------------------------------------------------------------------- *)
(** Length *)

Definition val_mlist_length : val :=
  VFix 'f 'p :=
    Let 'v := val_get 'p in
    Match 'v With
    '| 'Cstr "nil" '=> 0
    '| 'Cstr "cons" 'x 'q '=> 1 '+ 'f 'q
    End.

Lemma Triple_mlist_length_1 : forall `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (val_mlist_length p)
    PRE (MList L p)
    POST (fun (r:int) => \[r = length L] \* MList L p).
Proof using.
  intros. gen p. induction_wf IH: (@list_sub A) L. intros.
  xwp.
  xlet.
  (* xunfold *)
  pattern MList at 1. rewrite MList_unfold. hpull ;=> v. xapp.
  (* xcase *)
  applys xcase_lemma0 ;=> E1.
  { destruct L as [|x L']; hpull.
    { intros ->. applys~ @xval_lemma 0. hsimpl. rew_list~. rewrite~ MList_nil_eq. }
    { intros q ->. tryfalse. } }
  { applys xcase_lemma2.
    { intros x q E.
      destruct L as [|x' L']; hpull.
      { intros ->. tryfalse. }
      { intros q' E'. subst v. rewrite enc_val_eq in *. inverts E.
        xapp* IH. hsimpl. xapp.
        (* done *)
        pattern MList at 2. rewrite MList_unfold. hsimpl*. rew_list; math. } }
    { intros N. destruct L as [|x L']; hpull.
      { intros ->. rewrite enc_val_eq in *. unfolds Nil. false. }
      { intros q ->. rewrite enc_val_eq in *. unfolds @Cons. false. } } }
Qed.

End MListNopoints.


(* ********************************************************************** *)
(* * Basic *)

Module Basic.

(* ---------------------------------------------------------------------- *)
(** Incr *)

Definition val_incr : val :=
  VFun 'p :=
   'p ':= ((val_get 'p) '+ 1).

(* VARIANT:
  VFun 'p :=
    Let 'n := val_get 'p in
   'p ':= ('n '+ 1).
*)

Lemma Triple_incr : forall (p:loc) (n:int),
  TRIPLE (val_incr p)
    PRE (p ~~> n)
    POST (fun (r:unit) => (p ~~> (n+1))).
Proof using.
  xwp. xappn~.
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


(* ---------------------------------------------------------------------- *)
(** Negation *)

Definition val_myneg :=
  VFun 'b := 
    If_ 'b '= true Then false Else true.

Lemma Triple_decr : forall (b:bool),
  TRIPLE (val_myneg b)
    PRE \[]
    POST (fun (r:bool) => \[r = !b]).
Proof using.
  xwp. 
  (* TODO fix xapp *)
  xlet. xapp_debug. lets K: (>> Spec b true). typeclass. apply K.
   unfold protect. hsimpl.
  intros ? ->. 
  xif ;=> C.
  { subst. xval. hsimpl*. } (* TODO: xvals *) 
  { xval. hsimpl. destruct b; auto_false. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Disequality test  -- DEPRECATED

Definition val_myneq :=
  VFun 'm 'n :=
    val_myneg ('m '= 'n).

Lemma Triple_myneq : forall (v1 v2:val),
  TRIPLE (val_myneq v1 v2)
    PRE \[]
    POST (fun (r:bool) => \[r = isTrue (v1 <> v2)]).
Proof using.
  xwp. 
  (* TODO fix xapp *)
  xlet. xapp_debug. lets K: (>> Spec v1 v2). typeclass. apply K.
   unfold protect. hsimpl.
 xapp Triple_eq. xapps. hsimpl ;=> ? ->. rew_isTrue~.
Qed.
*)

(*

(* ---------------------------------------------------------------------- *)
(** Swap *)

Definition val_swap :=
  VFun 'p 'q :=
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
  VFun 'n :=
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
  (* not possible: applys mklocal_erase. unfold cf_val. hsimpl. *)
  xvals~.
Qed.


(* ---------------------------------------------------------------------- *)
(** Basic let-binding example *)

Definition val_example_let :=
  VFun 'n :=
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
  VFun 'n :=
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
  VFun 'n :=
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
(* * Stack *)


Module Stack.

Definition val_is_empty : val :=
  VFun 'p :=
    val_get 'p '= 'nil.

Definition val_empty : val :=
  VFun 'u :=
   val_ref 'nil.

Definition val_push : val :=
  VFun 'p 'x :=
   'p ':= ('x ':: (val_get 'p)).

Definition val_pop : val :=
  VFun 'p :=
   Let 'q := val_get 'p in
   Match 'q With
   '| 'nil '=> 'Fail
   '| 'x ':: 'r '=> ('p ':= 'r) '; 'x
   End.

Definition val_rev_append : val :=
  VFix 'f 'p1 'p2 :=
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
  xwp. xunfold Stack. xapp. xval nil.
  xapp @Triple_eq_val.
  hsimpl. rewrite* @Enc_injective_value_eq_r.
Qed.

Lemma Triple_empty : forall `{Enc A} (u:unit),
  TRIPLE (val_empty u)
    PRE \[]
    POST (fun p => (p ~> Stack (@nil A))).
Proof using.
  xwp. xval nil. xapp~.
Qed.

Lemma Triple_push : forall `{Enc A} (p:loc) (x:A) (L:list A),
  TRIPLE (val_push p (``x))
    PRE (p ~> Stack L)
    POST (fun (u:unit) => (p ~> Stack (x::L))).
Proof using.
  xwp. xunfold Stack. xapp. xval (x::L). xapp~.
Qed.

Lemma Triple_pop : forall `{Enc A} (p:loc) (L:list A),
  L <> nil ->
  TRIPLE (val_pop p)
    PRE (p ~> Stack L)
    POST (fun (x:A) => \exists L', \[L = x::L'] \* (p ~> Stack L')).
Proof using.
  introv N. xwp. xunfold Stack. xapp.
  applys xmatch_lemma_list.
  { intros HL. xfail. }
  { intros X L' HL. xapp. xval. hsimpl~. }
Qed.

Opaque Stack.

Hint Extern 1 (Register_Spec (val_is_empty)) => Provide @Triple_is_empty.
Hint Extern 1 (Register_Spec (val_push)) => Provide @Triple_push.
Hint Extern 1 (Register_Spec (val_pop)) => Provide @Triple_pop.


Lemma Triple_rev_append : forall `{Enc A} (p1 p2:loc) (L1 L2:list A),
  TRIPLE (val_rev_append p1 p2)
    PRE (p1 ~> Stack L1 \* p2 ~> Stack L2)
    POST (fun (u:unit) => p1 ~> Stack nil \* p2 ~> Stack (rev L1 ++ L2)).
Proof using.
  intros. gen p1 p2 L2. induction_wf IH: (@list_sub A) L1. intros.
  xwp. xapp. xif ;=> C.
  { (* case nil *)
    xval tt. hsimpl~. subst. rew_list~. }
  { (* case cons *)
    xapp~ ;=> x L1' E.
    xapp.
    xapp. { subst*. } hsimpl. subst. rew_list~. }
Qed.

End Stack.



(* ********************************************************************** *)
(* * Stack with length *)

Module StackLength.

Definition data : field := 0%nat.
Definition size : field := 1%nat.

(*
Definition val_is_empty : val :=
  VFun 'p :=
    val_get 'p '= 'nil.

Definition val_empty : val :=
  VFun 'u :=
   val_ref 'nil.
*)

Definition val_push : val :=
  VFun 'p 'x :=
   Set 'p'.data ':= ('x ':: 'p'.data) ';
   Set 'p'.size ':= ('p'.size '+ 1).

Definition val_pop : val :=
  VFun 'p :=
   Let 'q := 'p'.data in 
   Match 'q With (* TODO: allow inline *)
   '| 'nil '=> 'Fail
   '| 'x ':: 'r '=> 
       Set 'p'.data ':= 'r ';
       Set 'p'.size ':= ('p'.size '- 1) ';
       'x
   End.

(* TODO: concat function with the sum of the lengths *)

(*
Definition val_rev_append : val :=
  VFix 'f 'p1 'p2 :=
    If_ val_is_empty 'p1 Then '() Else 
       Let 'x := val_pop 'p1 in
       val_push 'p2 'x ';
       'f 'p1 'p2.
*)

Definition Stackn `{Enc A} (L:list A) (p:loc) : hprop :=
  p ~> Record`{ data := L; size := (length L : int) }.

(*
Lemma Triple_is_empty : forall `{Enc A} (p:loc) (L:list A),
  TRIPLE (val_is_empty p)
    PRE (p ~> Stack L)
    POST (fun (b:bool) => \[b = isTrue (L = nil)] \* p ~> Stack L).
Proof using.
  xwp. xunfold Stack. xapp. xval nil.
  xapp @Triple_eq_val.
  hsimpl. rewrite* @Enc_injective_value_eq_r.
Qed.

Lemma Triple_empty : forall `{Enc A} (u:unit),
  TRIPLE (val_empty u)
    PRE \[]
    POST (fun p => (p ~> Stack (@nil A))).
Proof using.
  xwp. xval nil. xapp~.
Qed.
*)


Lemma Triple_push : forall `{Enc A} (p:loc) (x:A) (L:list A),
  TRIPLE (val_push p (``x))
    PRE (p ~> Stackn L)
    POST (fun (u:unit) => (p ~> Stackn (x::L))).
Proof using.
  xwp. xunfold Stackn. xapp. xval (x::L). xappn.
  hsimpl. (* hsimpl could do xrecord_eq *) 
  xrecord_eq. rew_list; math.
Qed.

Lemma Triple_pop : forall `{Enc A} (p:loc) (L:list A),
  L <> nil ->
  TRIPLE (val_pop p)
    PRE (p ~> Stackn L)
    POST (fun (x:A) => \exists L', \[L = x::L'] \* (p ~> Stackn L')).
Proof using.
  introv N. xwp. xunfold Stackn. xapp.
  applys xmatch_lemma_list.
  { intros HL. xfail. }
  { intros X L' HL. xappn. xval. hsimpl*. (* hsimpl could do xrecord_eq *) 
    xrecord_eq. subst; rew_list; math. }
Qed.

Opaque Stackn.

End StackLength.


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



















