(**

This file formalizes basic examples in plain Separation Logic,
both using triples directly and using characteristic formulae.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Import SepBase LambdaCF LibSepTLCbuffer LambdaStruct.
Generalizable Variables A B.

Ltac auto_star ::= jauto.

Implicit Type p q : loc.
Implicit Types n : int.


(* ********************************************************************** *)
(* * Basic functions *)


(* ---------------------------------------------------------------------- *)
(** Increment function -- details *)

(* From LambdaStruct

Definition val_incr :=
  ValFun 'p :=
    Let 'n := val_get 'p in
    Let 'm := 'n '+ 1 in
    val_set 'p 'm.
*)

(** Low-level proof *)

Lemma triple_incr_1 : forall p n,
  triple (val_incr p)
    (p ~~~> n)
    (fun r => (p ~~~> (n+1))).
Proof using.
  intros. applys triple_app. reflexivity. simpl.
  applys triple_let. { applys triple_get. } simpl.
  intros x. apply triple_hpure. intros E. subst.
  applys triple_let.
  { applys triple_frame_consequence (p ~~~> n).
    { xsimpl. }
    { applys triple_add. }
    { xsimpl. } }
  simpl. intros y. apply triple_hpure. intros E. subst.
  applys triple_conseq.
  { xsimpl. }
  { applys triple_set. }
  { intros r. applys himpl_hpure_l. intros E. subst. auto. }
Qed.

(** Same proof using [xapply], [xapplys] and [xtpull] *)

Lemma triple_incr_2 : forall p n,
  triple (val_incr p)
    (p ~~~> n)
    (fun r => (p ~~~> (n+1))).
Proof using.
  intros. applys triple_app. reflexivity. simpl.
  applys triple_let. { applys triple_get. } simpl.
  intros x. xtpull. intros E. subst.
  applys triple_let. { xapplys triple_add. }
  simpl. intros y. xtpull. intro_subst.
  xapplys triple_set.
Qed.

(** Same proof using characteristic formulae without tactics *)

Lemma triple_incr_3 : forall p n,
  triple (val_incr p)
    (p ~~~> n)
    (fun r => (p ~~~> (n+1))).
Proof using.
  intros. applys triple_app_fun_of_cf_iter 20%nat. reflexivity. simpl.
  applys mklocal_erase. esplit. split.
  { applys mklocal_erase. xapplys triple_get. }
  intros x. xtpull. intros E. subst.
  applys mklocal_erase. esplit. split.
  { applys mklocal_erase. xapplys triple_add. }
  intros y. xtpull. intros E. subst.
  applys mklocal_erase. xapplys triple_set.
Qed.

(** Same proof using support for nary functions *)

Lemma triple_incr_4 : forall p n,
  triple (val_incr p)
    (p ~~~> n)
    (fun r => (p ~~~> (n+1))).
Proof using.
  intros. rew_nary. unfold val_incr.
  rew_nary. rew_trms_vals. (* show coercion *)
  applys triple_apps_funs_of_cf_iter 20%nat.
  { reflexivity. }
  { reflexivity. }
  simpl.
  (* then continue as before *)
Abort.

(** Same proof using characteristic formulae with tactics *)

Lemma triple_incr_5 : forall p n,
  triple (val_incr p)
    (p ~~~> n)
    (fun r => (p ~~~> (n+1))).
Proof using.
  xcf. xlet as x. xapp. xtpull. intro_subst.
  xlet as y. xapp. xtpull. intro_subst.
  xapp. xsimpl.
Qed.

(** Same proof using characteristic formulae with more tactics *)

Lemma triple_incr_6 : forall p n,
  triple (val_incr p)
    (p ~~~> n)
    (fun r => (p ~~~> (n+1))).
Proof using.
  xcf. xapp as x. intro_subst.
  xapp as y. intro_subst.
  xapps. xsimpl~.
Qed.

(** Same proof using characteristic formulae with yet more
  powerful tactics *)

Lemma triple_incr__7 : forall p n,
  triple (val_incr p)
    (p ~~~> n)
    (fun r => (p ~~~> (n+1))).
Proof using.
  xcf. xapps. xapps. xapps. xsimpl~.
Qed.

Hint Extern 1 (Register_spec val_incr) => Provide triple_incr__7.


(* ---------------------------------------------------------------------- *)
(** Calling incr from a larger context *)

Lemma triple_incr_with_other_1 : forall p n q m,
  triple (val_incr p)
    (p ~~~> n \* q ~~~> m)
    (fun r => (p ~~~> (n+1)) \* q ~~~> m).
Proof using.
  intros. applys triple_frame_consequence (q ~~~> m).
  { xsimpl. }
  { rew_heap. apply triple_incr_5. }
  { intros r. xsimpl. }
Qed.

Lemma triple_incr_with_other_2 : forall p n q m,
  triple (val_incr p)
    (p ~~~> n \* q ~~~> m)
    (fun r => (p ~~~> (n+1)) \* q ~~~> m).
Proof using.
  intros. xapply triple_incr_5.
  { xsimpl. }
  { intros r. xsimpl. }
Qed.

Lemma triple_incr_with_other : forall p n q m,
  triple (val_incr p)
    (p ~~~> n \* q ~~~> m)
    (fun r => (p ~~~> (n+1)) \* q ~~~> m).
Proof using. intros. xapps. xsimpl~. Qed.

Lemma triple_incr_with_frame : forall p n H,
  triple (val_incr p)
    (p ~~~> n \* H)
    (fun r => (p ~~~> (n+1)) \* H).
Proof using. intros. xapps. xsimpl~. Qed.


(* ---------------------------------------------------------------------- *)
(** Swap function *)

Definition val_swap :=
  ValFun 'p 'q :=
    Let 'x := val_get 'p in
    Let 'y := val_get 'q in
    val_set 'p 'y ;;;
    val_set 'q 'x.

Lemma triple_swap_neq : forall p q v w,
  triple (val_swap p q)
    (p ~~~> v \* q ~~~> w)
    (fun r => p ~~~> w \* q ~~~> v).
Proof using.
  xcf. xapps. xapps. xapp. intros _.
  xapps. xsimpl~.
Qed.

Lemma triple_swap_eq : forall p v,
  triple (val_swap p p)
    (p ~~~> v)
    (fun r => p ~~~> v).
Proof using.
  xcf. xapps. xapps. xapp~. intros _. xapps. xsimpl~.
Qed.


(* ---------------------------------------------------------------------- *)
(** Succ function using incr *)

Definition val_succ_using_incr :=
  ValFun 'n :=
    Let 'p := val_ref 'n in
    val_incr 'p ;;;
    Let 'x := val_get 'p in
    'x.

Lemma triple_succ_using_incr : forall n,
  triple (val_succ_using_incr n)
    \[]
    (fun r => \[r = n+1]).
Proof using.
  xcf. xapp as p. intros; subst. xapp~. intros _. xapps~.
  (* not possible: applys mklocal_erase. unfold cf_val. xsimpl. *)
  xvals~.
Qed.


(* ---------------------------------------------------------------------- *)
(** Two calls to incr *)

(*
  let val_incr_twice r =
    incr r;
    incr r
*)

Definition val_incr_twice :=
  ValFun 'p :=
    val_incr 'p ;;;
    val_incr 'p.

Lemma triple_incr_twice : forall p n,
  triple (val_incr_twice p)
    (p ~~~> n)
    (fun r => p ~~~> (n+2)).
Proof using.
  xcf. xapp. auto. intros _.
  xapps. (* same as [xapp; xpull] *)
  intros; subst.
  math_rewrite ((n + 1) + 1 = (n + 2)). (* TODO: avoid this ?*)
  xsimpl.
Qed.


(* ---------------------------------------------------------------------- *)
(** Basic let-binding example *)

Definition val_example_let :=
  ValFun 'n :=
    Let 'a := 'n '+ 1 in
    Let 'b := 'n '- 1 in
    'a '+ 'b.

Lemma triple_val_example_let : forall n,
  triple (val_example_let n)
    \[]
    (fun r => \[r = 2*n]).
Proof using.
  xcf. xapps. xapps. xapp.
  xsimpl. intros. subst. fequals. math.
Qed.


(* ---------------------------------------------------------------------- *)
(** Basic one references *)

(*
  let val_example_one_ref n =
    let i = ref 0 in
    incr i;
    !i
*)

Definition val_example_one_ref :=
  ValFun 'n :=
    Let 'k := 'n '+ 1 in
    Let 'i := 'ref 'k in
    val_incr 'i ;;;
    '!'i.

Lemma triple_example_one_ref : forall n,
  triple (val_example_one_ref n)
    \[]
    (fun r => \[r = n+2]).
Proof using.
  xcf.
  xapp. intros; subst.
  xapp. intros I i ?. subst.
  xapp. intros _.
  xapp. intros r. xsimpl. intros; subst. fequals. math.
Qed.



(* ---------------------------------------------------------------------- *)
(** Basic two references *)

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
  ValFun 'n :=
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

Lemma triple_example_two_ref : forall n,
  triple (val_example_two_ref n)
    \[]
    (fun r => \[r = n+1]).
Proof using.
  xcf. xapp ;=> i i' Ei. subst.
  xapp ;=> r r' Er. subst.
  xapp~. intros _. xapp~. intros _.
  xapps. xapps. xapps. xapps~. intros _.
  xapps. xapps. xapps.
  xsimpl. intros. subst. fequals. math.
Qed.
