(**

This file formalizes examples of first-class functions in plain
Separation Logic, using lifted characteristic formulae.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import Example.
Generalizable Variables A B.

Implicit Types p : loc.
Implicit Types n : int.



(* ********************************************************************** *)
(* * Apply function *)

Definition val_apply : val :=
  ValFun 'f 'x := ('f 'x).

Lemma Rule_apply : forall (f:func) `{EA:Enc A} (x:A),
  forall (H:hprop) `{EB:Enc B} (Q:B->hprop),
  Triple (f ``x) H Q ->
  Triple (val_apply ``f ``x) H Q.
Proof using.
  introv M. xcf. (* todo why not simplified? *)
    unfold Substn, substn; simpl; rew_enc_dyn.
  xapp. hsimpl~.
Qed.

Lemma Rule_apply' : forall (f:func) `{EA:Enc A} (x:A),
  forall (H:hprop) `{EB:Enc B} (Q:B->hprop),
  Triple (val_apply f ``x)
    PRE (\[Triple (f ``x) H Q] \* H)
    POST Q.
Proof using. intros. xpull ;=> M. applys~ Rule_apply. Qed.



(* ********************************************************************** *)
(* * RefApply function *)

Definition val_refapply : val :=
  ValFun 'f 'r :=
    Let 'x := val_get 'r in
    Let 'y := 'f 'x in
    val_set 'r 'y.

Lemma Rule_refapply_pure : forall (f:func) `{EA:Enc A} (r:loc) (x:A),
  forall `{EB:Enc B} (P:A->B->Prop),
  Triple (f ``x)
    PRE \[]
    POST (fun y => \[P x y])
  ->
  Triple (val_refapply ``f ``r)
    PRE (r ~~> x)
    POST (fun (_:unit) => \exists y, \[P x y] \* r ~~> y).
Proof using.
  introv M. xcf. xapps. xapp ;=> y E. xapp. hsimpl~.
Qed.

Lemma Rule_refapply_effect : forall (f:func) `{EA:Enc A} (r:loc) (x:A),
  forall `{EB:Enc B} (P:A->B->Prop) (H H':hprop),
  Triple (f ``x)
    PRE H
    POST (fun y => \[P x y] \* H')
  ->
  Triple (val_refapply ``f ``r)
    PRE (r ~~> x \* H)
    POST (fun (_:unit) => \exists y, \[P x y] \* r ~~> y \* H').
Proof using.
  introv M. xcf. xapps. xapp ;=> y E. xapp. hsimpl~.
Qed.



(* ********************************************************************** *)
(* * Twice function *)

Definition val_twice : val :=
  ValFun 'f :=
    'f '() ;;;
    'f '().

Lemma Rule_twice : forall (f:func) (H H':hprop) `{EB:Enc B} (Q:B->hprop),
  Triple (f ``tt) H (fun (_:unit) => H') ->
  Triple (f ``tt) H' Q ->
  Triple (val_twice ``f) H Q.
Proof using.
  introv M1 M2. xcf. xseq. xapp M1. xapp M2. hsimpl~.
Qed.


(* ********************************************************************** *)
(* * Repeat function *)

Definition val_repeat : val :=
  ValFun 'n 'f :=
    For 'i := 1 To 'n Do
      'f '()
    Done.

Axiom xfor_inv_lemma : forall (I:int->hprop),
  forall (a:int) (b:int) (F:int->Formula) H H',
  (a <= b+1) ->
  (H ==> I a \* H') ->
  (forall i, a <= i <= b -> ^(F i) (I i) (fun (_:unit) => I(i+1))) ->
  ^(Cf_for a b F) H (fun (_:unit) => I (b+1) \* H').



Lemma Rule_consequence_post : forall t `{Enc A} (Q':A->hprop) H (Q:A->hprop),
  Triple t H Q' ->
  Q' ===> Q ->
  Triple t H Q.
Proof using. introv MH M MQ. applys* Rule_consequence MH. Qed.

Lemma xfor_simplify_inequality_lemma : forall (n:int),
  ((n-1)+1) = n.
Proof using. math. Qed.

Lemma Rule_repeat : forall (I:int->hprop) (f:func) (n:int),
  n >= 0 ->
  (forall i, 0 <= i < n ->
     Triple (f ``tt)
       PRE (I i)
       POST (fun (_:unit) => I (i+1)))
  ->
  Triple (val_repeat ``n ``f)
    PRE (I 0)
    POST (fun (_:unit) => I n).
Proof using.
  introv N M. xcf.
  asserts_rewrite (``n = val_int n). auto. (* todo: investigate *)
  applys local_weaken_post. xlocal.
  applys local_erase. applys xfor_inv_lemma (fun i => (I (i-1))).
  { math. }
  { hsimpl. }
  { intros i Hi. xapp. { math. } { math_rewrite (i-1+1=i+1-1). hsimpl. } }
  { math_rewrite (n+1-1=n). hsimpl. }
  (* todo : avoid math_rewrite,
     thanks to hsimpl simplification of invariants *)
Qed.


(* ********************************************************************** *)
(* * Iteration (iter, fold, map, find) on lists: see [ExampleList.v] *)


(* ********************************************************************** *)
(* * Counter function *)

Implicit Types g : val.


(* ---------------------------------------------------------------------- *)
(** Representation *)

Definition MCount (n:int) (g:val) : hprop :=
  \exists p, (p ~~> n) \*
    \[ forall n', Triple (g val_unit)
                  (p ~~> n')
                  (fun r => \[r = n'+1] \* (p ~~> (n'+1))) ].

(* TODO: fix priority of p ~~> (n'+1) differently *)


(* ---------------------------------------------------------------------- *)
(** Specification *)


Lemma Rule_MCount : forall n g,
  Triple (g '()) (g ~> MCount n) (fun r => \[ r = n+1 ] \* g ~> MCount (n+1)).
Proof using.
  intros. xunfolds MCount at 1 ;=> p Hg. xapp.
  hpulls. xunfold MCount. hsimpl~.
Qed.


(* ---------------------------------------------------------------------- *)
(** Implementation *)

Definition val_mkcounter : val :=
  ValFun 'u :=
    Let 'p := val_ref 0 in
    (Fun 'v := val_incr 'p ;;; val_get 'p).


(* ---------------------------------------------------------------------- *)
(** Verification *)

Lemma Rule_mkcounter :
  Triple (val_mkcounter ``val_unit)
    \[]
    (fun g => g ~> MCount 0).
Proof using.
  xcf. xapps ;=> r. xval. xunfold MCount. hsimpl.
  { intros n'. xcf. xapp~. xapp. hsimpl~. }
Qed.

Hint Extern 1 (Register_Spec val_mkcounter) => Provide Rule_mkcounter.


(* ---------------------------------------------------------------------- *)
(** Demo *)

Definition trm_test_mkcounter : trm :=
  Let 'c := val_mkcounter '() in
  Let 'n := 'c '() in
  Let 'm := 'c '() in
  val_add 'n 'm.

Lemma rule_test_mkcounter :
  Triple trm_test_mkcounter
    \[]
    (fun r => \[r = 3]).
Proof using.
  xcf_trm 100%nat. (* todo: make xcf work *)
  xapp as C.
  xapps Rule_MCount.
  xapps Rule_MCount.
  xapps.
  hsimpl~.
Qed.
