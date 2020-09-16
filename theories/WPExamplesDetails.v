(**

This file shows step-by-step details of tactics for manipulating
characteristic formula in weakest-precondition form, in lifted
Separation Logic, as defined in [WPLifted.v].

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)


Set Implicit Arguments.
Generalizable Variables A B.
From Sep Require Import Example.

Ltac auto_star ::= auto_star_default.


(* ********************************************************************** *)
(* * Basic *)

Module Basic.

(* ---------------------------------------------------------------------- *)
(** Incr *)

Definition val_incr : val :=
  Fun 'p :=
   'p ':= ((val_get 'p) '+ 1).

(* VARIANT:
  Fun 'p :=
    Let 'n := val_get 'p in
   'p ':= ('n '+ 1).
*)


Lemma Triple_incr : forall (p:loc) (n:int),
  TRIPLE (val_incr p)
    PRE (p ~~> n)
    POST (fun (r:unit) => (p ~~> (n+1))).
Proof using.
  intros.
  (* optional simplification step to reveal [trm_apps] *)
  simpl combiner_to_trm.
  (* xwp *)
  applys xwp_lemma_funs.
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  simpl.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xlet *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xapps *)
  applys @xapps_lemma. { applys Triple_get. } xapp_post tt.
  (* xapps *)
  applys @xapps_lemma_pure. { applys Triple_add. } xapp_post tt.
  (* xapp *)
  applys @xapp_lemma. { eapply @Triple_set. } xapp_post tt.
  (* done *)
  xsimpl.
Qed.

Lemma Triple_incr' : forall (p:loc) (n:int),
  TRIPLE (val_incr p)
    PRE (p ~~> n)
    POST (fun (r:unit) => (p ~~> (n+1))).
Proof using.
  xwp. xlet. xlet. xapp. xapp. xapp. xsimpl.
Qed.

Lemma Triple_incr'' : forall (p:loc) (n:int),
  TRIPLE (val_incr p)
    PRE (p ~~> n)
    POST (fun (r:unit) => (p ~~> (n+1))).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl.
Qed.

End Basic.


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
  Fun 'p :=
   Set 'p'.X ':= ('p'.X '+ 1) ';
   Set 'p'.K ':= ('p'.K '+ 1).

Lemma Triple_move_X : forall p x y,
  TRIPLE (val_move_X p)
    PRE (Point x y p)
    POST (fun (_:unit) => (Point (x+1) y p)).
Proof using.
  intros.
  (* xwp *)
  applys xwp_lemma_funs; try reflexivity. xwp_simpl.
  (* xunfold *)
  unfold Point. xpull ;=> k Hk.
  (* xseq *)
  applys xseq_lemma.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xapp_record *)
  applys xapp_record_get. xapp_record_get_set_post tt.
   (* applys xcast_lemma. *)
  (* xapps *)
  applys @xapps_lemma_pure. { applys @Triple_add. } xapp_post tt.
  (* xapp_record *)
  applys xapp_record_set. xapp_record_get_set_post tt.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xlet *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xapp_record *)
  applys xapp_record_get. xapp_record_get_set_post tt.
   (* applys xcast_lemma. *)
  (* xapps *)
  applys @xapps_lemma_pure. { applys @Triple_add. } xapp_post tt.
  (* xapp_record *)
  applys xapp_record_set. xapp_record_get_set_post tt.
    (* xsimpl. simpl. xsimpl. unfold protect. *)
  (* done *)
  xsimpl. math.
Qed.

Lemma Triple_move_X' : forall p x y,
  TRIPLE (val_move_X p)
    PRE (Point x y p)
    POST (fun (_:unit) => (Point (x+1) y p)).
Proof using.
  xwp.
  xunfolds Point ;=> k Hk.
  xseq.
  xlet.
  xlet.
  xapp.
  dup. { xapp (@Triple_add). demo. }
  xapp.
  xapp.
  xlet.
  xlet.
  xapp.
  xapp.
  xapp.
  xsimpl. math.
Qed.

Lemma Triple_move_X'' : forall p x y,
  TRIPLE (val_move_X p)
    PRE (Point x y p)
    POST (fun (_:unit) => (Point (x+1) y p)).
Proof using.
  xwp. xunfolds Point ;=> k Hk.
  xapp. xapp. xapp. xapp. xapp. xapp.
  xsimpl. math.
Qed.

  (* TODO [xnew details -> for proof details]
  let Vs := list_boxer_to_dyns (>> (@nil A) 0) in
  applys (@xapp_record_new Vs);
  [ (* TODO try reflexivity *)
  | intros ?; solve [ false ]
  | try reflexivity
  | try reflexivity
  | xsimpl; simpl List.combine; simpl; xsimpl; unfold protect ].  *)

End Point.


(* ********************************************************************** *)
(* * Test match *)

Module TestMatch.

(* ---------------------------------------------------------------------- *)
(* ** Case without variables *)

Definition val_test1 : val :=
  Fun 'p :=
    Match 'p With pat_unit '=> 'Fail End.

Lemma Triple_test1 : forall (p:loc),
  TRIPLE (val_test1 ``p)
    PRE \[]
    POST (fun (u:unit) => \[]).
Proof using.
  xwp.
Abort.


(* ---------------------------------------------------------------------- *)
(* ** Case with 1 variable *)

Definition val_test2 : val :=
  Fun 'p :=
    Match 'p With 'x '=> 'x End.

Lemma Triple_test2 : forall (p:loc),
  TRIPLE (val_test2 p)
    PRE \[]
    POST (fun (u:unit) => \[]).
Proof using.
  xwp.
Abort.


(* ---------------------------------------------------------------------- *)
(* ** Match without variables *)


Definition val_test0 : val :=
  Fun 'p :=
    Match 'p With
    '| pat_unit '=> 'Fail
    '| pat_unit '=> 'p
    End.

Lemma triple_test0 : forall (p:loc),
  TRIPLE (val_test0 p)
    PRE \[]
    POST (fun (u:unit) => \[]).
Proof using.
  xwp.
Abort.


End TestMatch.



(* ********************************************************************** *)
(* * Mutable lists *)


Module MList.


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
  { xpull ;=> ? ->. auto. }
  { xsimpl~. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Length *)

Definition val_mlist_length : val :=
  Fix 'f 'p :=
    Let 'v := val_get 'p in
    Match 'v With
    '| 'Cstr "nil" '=> 0
    '| 'Cstr "cons" 'x 'q '=> 1 '+ 'f 'q
    End.

Lemma Triple_mlist_length_1 : forall A `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (val_mlist_length p)
    PRE (MList L p)
    POST (fun (r:int) => \[r = length L] \* MList L p).
Proof using.
  intros. gen p. induction_wf IH: (@list_sub A) L. intros.
  (* xwp *)
  intros. applys xwp_lemma_fixs; try reflexivity. xwp_simpl.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xunfold *)
  pattern MList at 1. rewrite MList_unfold. xpull ;=> v.
  (* xapps *)
  applys @xapps_lemma. { applys @Triple_get. } xsimpl.
  (* xcase *)
  applys xcase_lemma0 ;=> E1.
  { destruct L as [|x L']; xpull.
    { intros ->. applys~ @xval_lemma 0. xsimpl. rew_list~.
      rewrite~ MList_nil_eq. xsimpl. }
    { intros q ->. tryfalse. } }
  { applys xcase_lemma2.
    { intros x q E.
      destruct L as [|x' L']; xpull.
      { intros ->. tryfalse. }
      { intros q' E'. subst v. rewrite enc_val_eq in *. inverts E.
        (* xlet-poly *)
        notypeclasses refine (xlet_lemma _ _ _ _ _).
        (* xapps *)
        applys @xapps_lemma. { applys* IH. } xapp_post tt.
        (* xapps *)
        applys @xapps_lemma_pure. { applys Triple_add. } xapp_post tt.
        (* done *)
        pattern MList at 2. rewrite MList_unfold. xsimpl*. rew_list; math. } }
    { intros N. destruct L as [|x L']; xpull.
      { intros ->. rewrite enc_val_eq in *. unfolds Nil. false. }
      { intros q ->. rewrite enc_val_eq in *. unfolds @Cons. false. } } }
Qed.

Lemma Triple_mlist_length_1' : forall A `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (val_mlist_length p)
    PRE (MList L p)
    POST (fun (r:int) => \[r = length L] \* MList L p).
Proof using.
  intros. gen p. induction_wf IH: (@list_sub A) L. intros.
  xwp.
  xlet.
  (* xunfold *)
  pattern MList at 1. rewrite MList_unfold. xpull ;=> v.
  xapp.
  (* xcase *)
  applys xcase_lemma0 ;=> E1.
  { destruct L as [|x L']; xpull.
    { intros ->. applys~ @xval_lemma 0. xsimpl. rew_list~.
      rewrite~ MList_nil_eq. xsimpl. }
    { intros q ->. tryfalse. } }
  { applys xcase_lemma2.
    { intros x q E.
      destruct L as [|x' L']; xpull.
      { intros ->. tryfalse. }
      { intros q' E'. subst v. rewrite enc_val_eq in *. inverts E.
        xlet.
        xapp* IH.
        xapp.
        (* done *)
        pattern MList at 2. rewrite MList_unfold. xsimpl*. rew_list; math. } }
    { intros N. destruct L as [|x L']; xpull.
      { intros ->. rewrite enc_val_eq in *. unfolds Nil. false. }
      { intros q ->. rewrite enc_val_eq in *. unfolds @Cons. false. } } }
Qed.


End MList.




(* ********************************************************************** *)
(* * Stack *)


Module Stack.

Definition val_is_empty : val :=
  Fun 'p :=
    val_get 'p '= 'nil.

Definition val_empty : val :=
  Fun 'u :=
   val_ref 'nil.

Definition val_push : val :=
  Fun 'p 'x :=
   'p ':= ('x ':: (val_get 'p)).

Definition val_pop : val :=
  Fun 'p :=
   (Let 'q := val_get 'p in
   Match 'q With
   '| 'nil '=> 'Fail
   '| 'x ':: 'r '=> ('p ':= 'r) '; 'x
   End).

Definition val_rev_append : val :=
  Fix 'f 'p1 'p2 :=
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
  (* xwp *)
  intros. applys xwp_lemma_funs; try reflexivity; xwp_simpl.
  (* xunfold *)
  xunfold Stack.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xapps *)
  applys @xapps_lemma. { eapply @Triple_get. } xapp_post tt.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xval *)
  applys~ (xval_lemma nil).
  (* xapps *)
  applys @xapps_lemma_pure. { applys @Triple_eq_val. } xapp_post tt.
  (* done *)
  xsimpl. rewrite* @Enc_injective_value_eq_r. eauto with Enc_injective.
Qed.

Lemma Triple_is_empty' : forall `{Enc A} (p:loc) (L:list A),
  TRIPLE (val_is_empty p)
    PRE (p ~> Stack L)
    POST (fun (b:bool) => \[b = isTrue (L = nil)] \* p ~> Stack L).
Proof using.
  xwp. xunfold Stack. xlet. xapp. xlet. xval nil.
  xapp @Triple_eq_val. xsimpl. rewrite* @Enc_injective_value_eq_r.
  eauto with Enc_injective.
Qed.


Lemma Triple_pop : forall `{Enc A} (p:loc) (L:list A),
  L <> nil ->
  TRIPLE (val_pop p)
    PRE (p ~> Stack L)
    POST (fun (x:A) => \exists L', \[L = x::L'] \* (p ~> Stack L')).
Proof using.
  introv N.
  (* xwp *)
  applys xwp_lemma_funs; try reflexivity; xwp_simpl.
  (* xunfold *)
  xunfold Stack.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xapps *)
  applys @xapps_lemma. { eapply @Triple_get. } xapp_post tt.
  (* Two ways of completing the proof *)
  dup.
  (* xcase with lemma for match list *)
  { applys xmatch_lemma_list.
    { intros HL.
      (* xfail *)
      false. }
    { intros X L' HL.
      (* xseq *)
      applys xseq_lemma.
      (* xapp *)
      applys @xapp_lemma. { applys @Triple_set. } xapp_post tt.
      (* xval *)
      applys~ xval_lemma.
      (* done *)
      xsimpl~. } }
  (* inlining the proof of xmatch_list *)
  { applys xcase_lemma0 ;=> E1.
    { destruct L; tryfalse. }
    { applys xcase_lemma2.
      2: { intros E. destruct L; rew_enc in *; tryfalse. }
      { intros x1 x2 E2. destruct L as [|x L']; rew_enc in *; tryfalse.
        inverts E2.
        (* xseq *)
        applys xseq_lemma.
        (* xapp *)
        applys @xapp_lemma. { applys @Triple_set. } xapp_post tt.
        (* xval *)
        applys~ xval_lemma.
        (* post *)
        xsimpl~. } } }
Qed.

Lemma Triple_pop' : forall `{Enc A} (p:loc) (L:list A),
  L <> nil ->
  TRIPLE (val_pop p)
    PRE (p ~> Stack L)
    POST (fun (x:A) => \exists L', \[L = x::L'] \* (p ~> Stack L')).
Proof using.
  introv N. xwp. xunfold Stack. xlet. xapp.
  applys xmatch_lemma_list.
  { intros HL. xfail. }
  { intros X L' HL. xseq. xapp. xval. xsimpl~. }
Qed.


Lemma Triple_empty : forall `{Enc A} (u:unit),
  TRIPLE (val_empty u)
    PRE \[]
    POST (fun p => (p ~> Stack (@nil A))).
Proof using.
  (* xwp *)
  intros. applys xwp_lemma_funs; try reflexivity; xwp_simpl.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xval *)
  applys~ (xval_lemma (@nil A)).
  (* xapp *)
  applys @xapp_lemma. { eapply @Triple_ref. } xsimpl. unfold protect.
  (* done *)
  xsimpl.
Qed.

Lemma Triple_empty' : forall `{Enc A} (u:unit),
  TRIPLE (val_empty u)
    PRE \[]
    POST (fun p => (p ~> Stack (@nil A))).
Proof using.
  xwp. xlet. xval nil. xapp. xsimpl~.
Qed.


Lemma Triple_push : forall `{Enc A} (p:loc) (x:A) (L:list A),
  TRIPLE (val_push p (``x))
    PRE (p ~> Stack L)
    POST (fun (u:unit) => (p ~> Stack (x::L))).
Proof using.
  (* xwp *)
  intros. applys xwp_lemma_funs; try reflexivity; xwp_simpl.
  (* xunfold *)
  xunfold Stack.
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xlet-poly *)
  notypeclasses refine (xlet_lemma _ _ _ _ _).
  (* xapps *)
  applys @xapps_lemma. { eapply @Triple_get. } xapp_post tt.
  (* xval *)
  applys~ (xval_lemma (x::L)).
  (* xapps *)
  applys @xapp_lemma. { eapply @Triple_set. } xapp_post tt.
  (* done *)
  xsimpl~.
Qed.

Lemma Triple_push' : forall `{Enc A} (p:loc) (x:A) (L:list A),
  TRIPLE (val_push p (``x))
    PRE (p ~> Stack L)
    POST (fun (u:unit) => (p ~> Stack (x::L))).
Proof using.
  xwp. xunfold Stack. xlet. xlet. xapp. xval (x::L). xapp. xsimpl~.
Qed.


Opaque Stack.


Lemma Triple_rev_append : forall `{Enc A} (p1 p2:loc) (L1 L2:list A),
  TRIPLE (val_rev_append p1 p2)
    PRE (p1 ~> Stack L1 \* p2 ~> Stack L2)
    POST (fun (u:unit) => p1 ~> Stack nil \* p2 ~> Stack (rev L1 ++ L2)).
Proof using.
  intros. gen p1 p2 L2. induction_wf IH: (@list_sub A) L1. intros.
  (* xwp *)
  intros. applys xwp_lemma_fixs; try reflexivity; xwp_simpl.
simpl. (* TODO ! *)
  (* xlet *)
  applys xlet_typed_lemma.
  (* xapps *)
  applys @xapps_lemma. { eapply @Triple_is_empty. } xapp_post tt.
  (* xif *)
  applys @xifval_lemma_isTrue ;=> C.
  (* case nil *)
  { (* xval *)
    applys~ (xval_lemma tt).
    (* done *)
    xsimpl~. subst. rew_list~. }
  (* case cons *)
  { (* xlet-poly *)
    notypeclasses refine (xlet_lemma _ _ _ _ _).
    (* xapp *)
    applys @xapp_lemma. { applys @Triple_pop. eauto. } xapp_post tt ;=> x L1' E.
    (* xseq *)
    applys xseq_lemma.
    (* xapp *)
    applys @xapp_lemma. { applys @Triple_push. } xapp_post tt.
    (* xapp *)
    applys @xapp_lemma. { applys IH L1'. subst*. } xapp_post tt.
    (* done *)
    xsimpl. subst. rew_list~. }
Qed.

Lemma Triple_rev_append' : forall `{Enc A} (p1 p2:loc) (L1 L2:list A),
  TRIPLE (val_rev_append p1 p2)
    PRE (p1 ~> Stack L1 \* p2 ~> Stack L2)
    POST (fun (u:unit) => p1 ~> Stack nil \* p2 ~> Stack (rev L1 ++ L2)).
Proof using.
  intros. gen p1 p2 L2. induction_wf IH: (@list_sub A) L1. intros.
  xwp. xlet. xapp @Triple_is_empty. xif ;=> C.
  { (* case nil *)
    xval tt. xsimpl~. subst. rew_list~. }
  { (* case cons *)
    xlet. xapp~ @Triple_pop ;=> x L1' E.
    xseq. xapp @Triple_push.
    xapp (>> IH L1'). (* [xapp.] also works *)
    { subst*. }
    xsimpl. subst. rew_list~. }
Qed.

Lemma Triple_rev_append'' : forall `{Enc A} (p1 p2:loc) (L1 L2:list A),
  TRIPLE (val_rev_append p1 p2)
    PRE (p1 ~> Stack L1 \* p2 ~> Stack L2)
    POST (fun (u:unit) => p1 ~> Stack nil \* p2 ~> Stack (rev L1 ++ L2)).
Proof using.
  intros. gen p1 p2 L2. induction_wf IH: (@list_sub A) L1. intros.
  xwp. xlet. xapp @Triple_is_empty. xif ;=> C.
  { (* case nil *)
    xval tt. xsimpl~. subst. rew_list~. }
  { (* case cons *)
    xlet. xapp~ @Triple_pop ;=> x L1' E.
    xseq.
    (* xapp: *) xapp @Triple_push. xsimpl.
    dup.
    { xapp (>> IH L1'). { subst*. } xsimpl. subst. rew_list~. }
    { xapp (>> __ L1'). { subst*. } xsimpl. subst. rew_list~. } }
Qed.

End Stack.





















