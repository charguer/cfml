(**

Tutorial file for JFLA 2018

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
Generalizable Variables A B.

From Sep Require LambdaSep LambdaCF LambdaStruct.
From Sep Require LambdaSepLifted LambdaCFLifted LambdaStructLifted.
From Sep Require ExampleListNonlifted ExampleQueueNonlifted.
From TLC Require LibListZ.



(***********************************************************************)
(***********************************************************************)
(***********************************************************************)
(** Basic Separation Logic *)

Module Basic.

Export LambdaSep LambdaCF LambdaStruct.
Export LibListZ.
Open Scope Z_scope.

Implicit Types v : val.
Implicit Types p : loc.
Implicit Types n : int.


(***********************************************************************)
(** Cheat list *)

(**

Heap predicates:
   - \[]
   - \[P]
   - H \* H'
   - r ~~~> v
   - r ~~~> (v+1)
   - Hexists x1 .. xN, H
   - Hexists (x:val), H
   - \Top

Specification syntax:
   - [triple (f x y) H (fun r => H')]

Pure Coq tactics:
   - [tactic ;=> x1 .. xN] for introduction
   - [tactic~] for automation
   - [inverts H] is an enhanced version of [inversion; subst]
   - [rew_list] for normalizing list operations
   - [math] for arithmetic (wrapper for [omega])

Working with entailment [H1 ==> H2]:
   - [hsimpl]
   - [hsimpl X1 .. XN]
   - [hpull]
   - don't use [hcancel], use [hsimpl] instead
   - [hchange]

Working with entailment (Q1 ===> Q2):
   - [intros r], for a fresh r.

Working with triples [triple t H Q] or formulae [cf t H Q]:
   - [xapply E], where [E] is a triple or a formula,
     to apply [E] modulo frame/consequence/top.
   - [xchange E], where [E] is an entailment or an equality,
     to modify the precondition [H].
   - [xpull] to extract quantifiers and pure facts
     from the precondition [H]
   - [xcf] to replace [triple t H Q] with [cf t H Q],
     and compute [cf t].

   - [xapplys E] combines [xapply E] with [hsimpl].
   - [xchanges E] combines [xchange E] with [xpull].

CF tactics:
   - [xval] for values or let+value
   - [xvals] to call [xval] then [hsimpl]
   - [xapp] for application or let+application
   - [xapps] for [xapp] then perform substitution
   - [xseq] for sequence
   - [xlet] for let-binding ([xval] or [xapp] might apply directly)
   - [xif] for conditional

Relevant files:
   - [SepFunctor]: definitions common to several variants of the logic
   - [LambdaSep]: construction of plain Separation Logic
   - [LambdaCF]: caracteristic formula generator
   - [LambdaStruct]: common functions and formalization of arrays
   - Examples in:
       [ExampleBasicNonLifted]
       [ExampleListNonLifted]
       [ExampleUnionFind]

*)


(***********************************************************************)
(** Demo: [hsimpl] *)


Lemma demo_hsimpl_1 : forall (H1 H2 H3 H4 H5 H6:hprop) r n,
  H1 \* (r ~~~> n) \* H2 \* H3 ==> H4 \* H5 \* (r ~~~> n) \* H6.
Proof using.
  intros.
  hsimpl.
Abort.

Lemma demo_hsimpl_2 : forall r s,
  (r ~~~> 3) \* (s ~~~> 4) ==> Hexists (n:int), (r ~~~> (n+1)) \* (s ~~~> (n+2)).
Proof using.
  intros. dup 2.
  { hsimpl. admit. }
  { hsimpl 2. }
Abort.

Lemma demo_hsimpl_3 : forall r,
  (Hexists (n:int), r ~~~> n \* \[n > 0]) ==> (Hexists (m:int), r ~~~> (m+1) \* \[m >= 0]).
Proof using.
  intros. hpull. intros n Hn.
  hsimpl (n-1). math_rewrite (n-1+1 = n). hsimpl. math.
Abort.


(***********************************************************************)
(** Demo: verification of [incr] *)

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

Lemma rule_incr_1 : forall p n,
  triple (val_incr p)
    (p ~~~> n)
    (fun r => \[r = val_unit] \* (p ~~~> (n+1))).
Proof using.
  intros. applys rule_app_fun. reflexivity. simpl.
  applys rule_let. { applys rule_get. } simpl.
  intros x. apply rule_extract_hprop. intros E. subst.
  applys rule_let.
  { applys rule_frame_consequence (p ~~~> n).
    { hsimpl. }
    { applys rule_add. }
    { hsimpl. } }
  simpl. intros y. apply rule_extract_hprop. intros E. subst.
  applys rule_consequence.
  { hsimpl. }
  { applys rule_set. }
  { intros r. applys himpl_hpure_l. intros E. subst.
    applys himpl_hpure_r. { auto. } { auto. } }
Qed.

(** Same proof using [xapply], [xapplys] and [xpull] *)

Lemma rule_incr_2 : forall p n,
  triple (val_incr p)
    (p ~~~> n)
    (fun r => \[r = val_unit] \* (p ~~~> (n+1))).
Proof using.
  intros. applys rule_app_fun. reflexivity. simpl.
  applys rule_let. { applys rule_get. } simpl.
  intros x. xpull. intros E. subst.
  applys rule_let. { xapplys rule_add. }
  simpl. intros y. xpull. intro_subst.
  xapplys rule_set. auto.
Qed.

(** Same proof using characteristic formulae without tactics *)

Lemma rule_incr_3 : forall p n,
  triple (val_incr p)
    (p ~~~> n)
    (fun r => \[r = val_unit] \* (p ~~~> (n+1))).
Proof using.
  intros. applys triple_app_fun_of_cf_iter 20%nat. reflexivity. simpl.
  applys local_erase. esplit. split.
  { applys local_erase. xapplys rule_get. }
  intros x. xpull. intros E. subst.
  applys local_erase. esplit. split.
  { applys local_erase. xapplys rule_add. }
  intros y. xpull. intros E. subst.
  applys local_erase. xapplys rule_set. auto.
Qed.

(** Same proof using support for nary functions *)

Lemma rule_incr_4 : forall p n,
  triple (val_incr p)
    (p ~~~> n)
    (fun r => \[r = val_unit] \* (p ~~~> (n+1))).
Proof using.
  intros. rew_nary. unfold val_incr.
  rew_nary. rew_vals_to_trms. (* show coercion *)
  applys triple_apps_funs_of_cf_iter 20%nat.
  { reflexivity. }
  { reflexivity. }
  simpl.
  (* then continue as before *)
Abort.

(** Same proof using characteristic formulae with tactics *)

Lemma rule_incr_5 : forall p n,
  triple (val_incr p)
    (p ~~~> n)
    (fun r => \[r = val_unit] \* (p ~~~> (n+1))).
Proof using.
  xcf. xlet as x. xapp. xpull. intro_subst.
  xlet as y. xapp. xpull. intro_subst.
  xapp. hsimpl. auto.
Qed.

(** Same proof using characteristic formulae with more tactics *)

Lemma rule_incr_6 : forall p n,
  triple (val_incr p)
    (p ~~~> n)
    (fun r => \[r = val_unit] \* (p ~~~> (n+1))).
Proof using.
  xcf. xapp as x. intro_subst.
  xapp as y. intro_subst.
  xapps. hsimpl~.
Qed.

(** Same proof using characteristic formulae with yet more
  powerful tactics *)

Lemma rule_incr__7 : forall p n,
  triple (val_incr p)
    (p ~~~> n)
    (fun r => \[r = val_unit] \* (p ~~~> (n+1))).
Proof using.
  xcf. xapps. xapps. xapps. hsimpl~.
Qed.

Hint Extern 1 (Register_spec val_incr) => Provide rule_incr__7.


(* ---------------------------------------------------------------------- *)
(** Calling incr from a larger context *)

Lemma rule_incr_with_other_1 : forall p n q m,
  triple (val_incr p)
    (p ~~~> n \* q ~~~> m)
    (fun r => \[r = val_unit] \* (p ~~~> (n+1)) \* q ~~~> m).
Proof using.
  intros. applys rule_frame_consequence (q ~~~> m).
  { hsimpl. }
  { rew_heap. apply rule_incr_5. }
  { intros r. hsimpl. auto. }
Qed.

Lemma rule_incr_with_other_2 : forall p n q m,
  triple (val_incr p)
    (p ~~~> n \* q ~~~> m)
    (fun r => \[r = val_unit] \* (p ~~~> (n+1)) \* q ~~~> m).
Proof using.
  intros. xapply rule_incr_5.
  { hsimpl. }
  { intros r. hsimpl. auto. }
Qed.

Lemma rule_incr_with_other : forall p n q m,
  triple (val_incr p)
    (p ~~~> n \* q ~~~> m)
    (fun r => \[r = val_unit] \* (p ~~~> (n+1)) \* q ~~~> m).
Proof using. intros. xapps. hsimpl~. Qed.

Lemma rule_incr_with_frame : forall p n H,
  triple (val_incr p)
    (p ~~~> n \* H)
    (fun r => \[r = val_unit] \* (p ~~~> (n+1)) \* H).
Proof using. intros. xapps. hsimpl~. Qed.



(***********************************************************************)
(** Demo: verification with let-bindings *)

Definition val_example_let :=
  ValFun 'n :=
    Let 'a := 'n '+ 1 in
    Let 'b := 'n '- 1 in
    'a '+ 'b.

Lemma rule_val_example_let : forall n,
  triple (val_example_let n)
    \[]
    (fun r => \[r = 2*n]).
Proof using.
  xcf. xapps. xapps. xapp.
  hsimpl. intros. subst. fequals. math.
Qed.


(***********************************************************************)
(** Exercise: [incr2] *)

(*
  let val_incr_twice r =
    incr r;
    incr r
*)

Definition val_incr_twice :=
  ValFun 'p :=
    val_incr 'p ;;;
    val_incr 'p.

(* EXERCISE: specify and verify [val_incr_twice] *)






































(* SOLUTION *)
Lemma rule_incr_twice : forall p n,
  triple (val_incr_twice p)
    (p ~~~> n)
    (fun r => \[r = val_unit] \* p ~~~> (n+2)).
Proof using.
  xcf. xapp. auto.
  xapps. (* same as [xapp; hpull] *)
  intros; subst.
  math_rewrite ((n + 1) + 1 = (n + 2)). (* TODO: avoid this ?*)
  hsimpl. auto.
Qed.
(* /SOLUTION *)


(***********************************************************************)
(** Exercise: one ref *)

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

Lemma rule_val_example_one_ref : forall n,
  triple (val_example_one_ref n)
    \[]
    (fun r => \[r = n+2]).
Proof using.
(* EXERCISE: complete proof *)











































(* SOLUTION *)
  xcf.
  xapp. intros; subst.
  xapp. intros I i ?. subst.
  xapp. auto.
  xapp. intros r. hsimpl. intros; subst. fequals. math.
(* /SOLUTION *)
Qed.


(***********************************************************************)
(** Definition: [MList] -- see [ExampleListNonLifted.v] *)

Import ExampleListNonlifted.

(***********************************************************************)
(** Demo : list length -- see also [ExampleListNonLifted.v] *)

Lemma rule_mlist_length_1 : forall L p,
  triple (val_mlist_length p)
    (MList L p)
    (fun r => \[r = val_int (length L)] \* MList L p).
Proof using.
  intros L. induction_wf: list_sub_wf L. xcf.
  xapps. xif ;=> C.
  { xchanges~ (MList_not_null_inv_cons p) ;=> x p' L' EL. subst L.
    xapps. xapps~ (IH L').
    xchange (MList_cons p).
    xapps. hsimpl. isubst. rew_list. fequals. math. }
  { inverts C. xchanges MList_null_inv ;=> EL. subst. xvals~. }
Qed.


(***********************************************************************)
(** Definition: [MQueue] -- see [ExampleQueueNonLifted.v]  *)

Import ExampleQueueNonlifted.

(** Definition MQueue (L:list val) (p:loc) :=
  Hexists (pf:loc), Hexists (pb:loc), Hexists (vx:val), Hexists (vy:val),
    MCell pf pb p \* MListSeg pb L pf \* MCell vx vy pb.
*)

(***********************************************************************)
(** Demo: queue push back *)

Definition val_push_back :=
  ValFun 'v 'p :=
    Let 'q := val_get_tl 'p in
    Let 'r := val_alloc 2 in
    val_set_hd 'q 'v ;;;
    val_set_tl 'q 'r ;;;
    val_set_tl 'p 'r.

Lemma rule_push_back : forall L v p,
  triple (val_push_back v p)
    (MQueue L p)
    (fun r => \[r = val_unit] \* MQueue (L&v) p).
Proof using.
  xcf. unfold MQueue. xpull ;=> pf pb vx vy.
  xapps. xapp rule_alloc_cell as r. intros pb' v1 v2. intro_subst.
  xapp~. xapp~. xapp~. hchanges~ MListSeg_last.
Qed.


(***********************************************************************)
(** Demo: queue pop front *)

Definition val_pop_front :=
  ValFun 'v 'p :=
    Let 'q := val_get_hd 'p in
    Let 'x := val_get_hd 'q in
    Let 'r := val_get_tl 'q in
    val_set_hd 'p 'r;;;
    'x.

Lemma rule_pop_front : forall L v p,
  L <> nil ->
  triple (val_pop_front v p)
    (MQueue L p)
    (fun v => Hexists L', \[L = v::L'] \* MQueue L' p).
Proof using.
  xcf. unfold MQueue. xpull ;=> pf pb vx vy.
  destruct L as [|x L']; tryfalse.
  rewrite MListSeg_cons_eq. xpull ;=> pf'.
  xapps. xapps. xapps. xapp~. xvals~.
Qed.


(***********************************************************************)
(** Exercise: queue push front *)

Definition val_push_front :=
  ValFun 'v 'p :=
    Let 'q := val_get_hd 'p in
    Let 'r := val_new_cell 'v 'q in
    val_set_hd 'p 'r.

Lemma rule_push_front : forall L v p,
  triple (val_push_front v p)
    (MQueue L p)
    (fun r => \[r = val_unit] \* MQueue (v::L) p).
Proof using.
(* EXERCISE: complete proof *)




































(* SOLUTION *)
  xcf. unfold MQueue. xpull ;=> pf pb vx vy.
  xapps. xapp as r. intros x. intro_subst.
  xapp. hsimpl~. isubst. hchanges (@MListSeg_cons x).
(* /SOLUTION *)
Qed.


(***********************************************************************)
(** Exercise: queue pop, alternative *)

Lemma rule_pop_front' : forall L v p x,
  triple (val_pop_front v p)
    (MQueue (x::L) p)
    (fun r => \[r = x] \* MQueue L p).
Proof using.
(* EXERCISE: complete proof
   Hint: use [xapply] on [(@rule_pop_front ...)] *)









































(* SOLUTION *)
  intros. xapply (@rule_pop_front (x::L)).
  { auto_false. }
  { hsimpl. }
  { intros r. hpull ;=> L' E. inverts E. hsimpl~. }
(* /SOLUTION *)
Qed.


(***********************************************************************)
(** Challenge: queue transfer *)

(* EXERCISE: define and verify the function [val_transfer]
   so that is satisfies:

Lemma rule_transfer : forall L1 L2 p1 p2,
  triple (val_transfer p1 p2)
    (MQueue L1 p1 \* MQueue L2 p2)
    (fun r => \[r = val_unit] \* MQueue (L1 ++ L2) p1 \* MQueue nil p2).


  Proof hints:
    - use [hchange] on [MListSeg_cons_eq], [MListSeg_last],
      [MListSeg_concat], and [MListSeg_nil].
    - use [rew_list] to normalize list expressions

*)




































Definition val_transfer :=
(* SOLUTION *)
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
(* /SOLUTION *)

Lemma rule_transfer : forall L1 L2 p1 p2,
  triple (val_transfer p1 p2)
    (MQueue L1 p1 \* MQueue L2 p2)
    (fun r => \[r = val_unit] \* MQueue (L1 ++ L2) p1 \* MQueue nil p2).
Proof using.
(* SOLUTION *)
  xcf. xapps. xapps. xif ;=> C.
  { unfold MQueue. xpull ;=> pf2 pb2 vx2 vy2 pf1 pb1 vx1 vy1.
    destruct L2 as [|x L2']; tryfalse.
    xchanges MListSeg_cons_eq ;=> pf2'.
    xapps. xapps. xapps. xapps.
    xapps~. xapps~. xapps~. xapps~. xapps~.
    intros r. hchange (MListSeg_last pf1).
    hchange (MListSeg_concat pf1 pf2' pb2). rew_list.
    hchange (MListSeg_nil pf2). hsimpl~. }
  { subst. rew_list. xvals~. }
(* /SOLUTION *)
Qed.


End Basic.


(***********************************************************************)
(***********************************************************************)
(***********************************************************************)
(** Lifted Separation Logic *)

Module Lifted.

Export LambdaSepLifted LambdaCFLifted LambdaStructLifted.


(***********************************************************************)
(** Cheat list *)

(**

Additional heap predicates:
   - r ~~> v
   - r ~~> (v+1)
   - r ~~> v
   - r ~> S   notation for [S r]

Specification syntax:
   - [Triple (f ``x ``y) PRE H POST (fun (r:typ) => H')]

Tactic for representation predicates [x ~> R X]:
  - [xunfold R]
  - [xunfold R at n]
  - [xunfold at n]
  - [xunfolds] combines [xunfold] and [hpull]/[xpull]

Additional CF tactics:
   - [xval V] to provide the Coq value [V] corresponding to
     value returned by the code.

Additional relevant files:
   - [LambdaSepLifted]: lifting of plain Separation Logic
   - [LambdaCFLifted]: caracteristic formula generator for lifted logic
   - [LambdaStructLifted]: proofs of common functions, records, arrays
   - Examples in:
       [ExampleBasic]
       [ExampleList]
       [ExampleTrees]

*)


(***********************************************************************)
(** Demo: verification of [incr] *)

Lemma Rule_incr : forall (p:loc) (n:int),
  Triple (val_incr ``p)
    PRE (p ~~> n)
    POST (fun (r:unit) => p ~~> (n+1)).
Proof using.
  xcf. xapps. xapps. xapps. hsimpl~.
Qed.

Hint Extern 1 (Register_Spec val_incr) => Provide Rule_incr.


(***********************************************************************)
(** Exercise: [incr2] *)

Lemma Rule_incr2 : forall (p:loc) (n:int),
  Triple (Basic.val_incr_twice ``p)
    PRE (p ~~> n)
    POST (fun (r:unit) => p ~~> (n+2)).
Proof using.
(* EXERCISE: complete proof *)



































(* SOLUTION *)
  xcf. xapps. xapps. hsimpl~. math.
(* /SOLUTION *)
Qed.



(***********************************************************************)
(** Definition: [MList]  *)

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
  | x::L' => Hexists (p':loc), (p ~> Record`{ hd := x; tl := p' }) \* (p' ~> MList L')
  end.

(* ---------------------------------------------------------------------- *)
(* ** Lemmas --- TODO: reduce *)

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
      { simpl. unfold hd. auto. }
      { hpull; auto_false. } }
    { hpull. } }
Qed.

Lemma MList_null_inv : forall A `{EA:Enc A} (L:list A),
  null ~> MList L ==+> \[L = nil].
Proof using.
  intros. destruct L.
  { hsimpl~. }
  { rewrite MList_null_eq. hsimpl. }
Qed.

(** Conversion lemmas for non-empty lists *)

Lemma MList_cons_eq : forall p A `{EA:Enc A} (x:A) L',
  p ~> MList (x::L') =
  Hexists p', (p ~> Record`{ hd := x; tl := p' }) \* p' ~> MList L'.
Proof using. intros. xunfold MList at 1. simple~. Qed.

Lemma MList_cons : forall p p' A `{EA:Enc A} (x:A) L',
  (p ~> Record`{ hd := x; tl := p' }) \* p' ~> MList L' ==>
  p ~> MList (x::L').
Proof using. intros. rewrite MList_cons_eq. hsimpl. Qed.

Lemma MList_not_null_inv_not_nil : forall p A `{EA:Enc A} (L:list A),
  p <> null ->
  p ~> MList L ==+> \[L <> nil].
Proof using.
  intros. destruct L.
  { hchanges -> (MList_nil_eq p). }
  { hsimpl. auto_false. }
Qed.

Lemma MList_not_null_inv_cons : forall p A `{EA:Enc A} (L:list A),
  p <> null ->
  p ~> MList L ==> Hexists x p' L',
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



(***********************************************************************)
(** Demo: list length *)

(** Note: same definition as before *)

Definition val_mlist_length : val :=
  ValFix 'f 'p :=
    If_ 'p '<> null Then (
      Let 'q := val_get_tl 'p in
      Let 'n := 'f 'q in
      val_add 'n 1
    ) Else (
      0
    ).

Lemma Rule_mlist_length : forall A `{EA:Enc A} (L:list A) (p:loc),
  Triple (val_mlist_length ``p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  intros. gen p. induction_wf: list_sub_wf L; intros. xcf.
  xapps~. xif ;=> C.
  { xchanges~ (MList_not_null_inv_cons p) ;=> x p' L' EL. subst L.
    xapps. xapps~ (IH L'). xchange (MList_cons p).
    xapps. hsimpl. isubst. rew_list~. math. }
  { subst. xchanges MList_null_inv ;=> EL. xvals~. subst. rew_list~. }
Qed.

(***********************************************************************)
(** Demo: new cell *)

Definition val_new_cell : val := val_new_record 2%nat.
Lemma Rule_new_cell : forall `{EA:Enc A} (x:A) (q:loc),
  Triple (val_new_cell ``x ``q)
    PRE \[]
    POST (fun p => (p ~> Record`{ hd := x; tl := q })).
Proof using. xrule_new_record. Qed.

Hint Extern 1 (Register_Spec val_new_cell) => Provide Rule_new_cell.

Opaque val_new_cell.


(***********************************************************************)
(** Exercise: list copy *)

Definition val_mlist_copy :=
  ValFix 'f 'p :=
    If_ val_eq 'p null Then null Else (
      Let 'x := val_get_hd 'p in
      Let 'p1 := val_get_tl 'p in
      Let 'p2 := 'f 'p1 in
      val_new_cell 'x 'p2
   ).

Lemma Rule_mlist_copy : forall p (L:list int),
  Triple (val_mlist_copy ``p)
    PRE (p ~> MList L)
    POST (fun (p':loc) => (p ~> MList L) \* (p' ~> MList L)).
Proof using.
(* EXERCISE: complete proof
   Hints: use [MList_null_eq], [MList_not_null_inv_cons] and [MList_cons_eq] *)































(* SOLUTION *)
  intros. gen p. induction_wf IH: list_sub_wf L. xcf.
  xapps~. xif ;=> C.
  { xval. subst p. rewrite MList_null_eq. hsimpl~. }
  { xchanges~ (MList_not_null_inv_cons p) ;=> x p1 T1 E. subst.
  xapps. xapps. xapp~ as p1'. xapp.
  intros p'. do 2 rewrite MList_cons_eq. hsimpl. }
(* /SOLUTION *)
Qed.


(***********************************************************************)
(** Demo: [MTree] -- see file [ExampleTrees.v] *)


End Lifted.
