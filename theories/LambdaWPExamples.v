(**

This file defines tactics for manipulating characteristic formula 
in weakest-precondition form, in lifted Separation Logic,
as defined in [LambdaWPLifted.v].

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
From Sep Require Export LambdaWPLifted.
Open Scope heap_scope.
Generalizable Variables A B.

Implicit Types v w : val.
Implicit Types t : trm.

Import NotationForVariables NotationForTerms.
Open Scope val_scope.
Open Scope pat_scope.
Open Scope trm_scope.



(* ********************************************************************** *)
(* * Demo *)



(* ---------------------------------------------------------------------- *)
(** Notation for triples *)

Notation "'TRIPLE' t 'PRE' H 'POST' Q" :=
  (Triple t H Q)
  (at level 39, t at level 0,
  format "'[v' 'TRIPLE'  t  '/' 'PRE'  H  '/' 'POST'  Q ']'") : triple_scope.

Notation "'`Triple' t 'PRE' H1 'RET' v 'POST' H2" :=
  (Triple t H1 (fun r => \[r = v] \* H2))
  (at level 39, t at level 0,
   format "'[v' '`Triple'  t  '/' 'PRE'  H1  '/'  'RET'  v  '/'  'POST'  H2 ']'") : triple_scope.

(* LATER
Notation "'`Triple' t 'PRE' H1 'BIND' x1 'RET' v 'POST' H2" :=
  (Triple t H1 (fun r => \exists x1, \[r = v] \* H2))
  (at level 39, t at level 0, x1 ident) : triple_scope.

Notation "'`Triple' t 'PRE' H1 'BIND' x1 x2 'RET' v 'POST' H2" :=
  (Triple t H1 (fun r => \exists x1 x2, \[r = v] \* H2))
  (at level 39, t at level 0, x1 ident, x2 ident) : triple_scope.
*)

Open Scope triple_scope.


(* ---------------------------------------------------------------------- *)
(* ** Tactic *) 

Lemma Wp_Triple_of_Wp : forall t H `{EA:Enc A} (Q:A->hprop),
  H ==> ^(Wp Ctx.empty t) Q ->
  H ==> ^(Wp_Triple t) Q.
Proof using. introv M. applys himpl_weakestpre. applys* Triple_of_Wp. Qed.




(* ---------------------------------------------------------------------- *)
(* ** Lemmas for tactics *)

Implicit Types vs : vals.
Implicit Types ts : trms.

Lemma Triple_apps_funs_of_Wp : forall F vs ts xs t `{EA:Enc A} H (Q:A->hprop),
  F = val_funs xs t ->
  trms_to_vals ts = Some vs ->
  var_funs_exec (length vs) xs ->
  H ==> ^(Wp (combine xs vs) t) Q ->
  Triple (trm_apps F ts) H Q.
Proof using.
  introv HF Hvs Hxs M. lets ->: trms_to_vals_spec Hvs.
  rewrite var_funs_exec_eq in Hxs. rew_istrue in Hxs. lets (_&Lxs&_): Hxs.
  applys* Triple_apps_funs. rewrite~ <- isubstn_eq_substn.
  applys* Triple_isubst_of_Wp.
Qed.

Lemma Triple_apps_fixs_of_Wp : forall F (f:var) vs ts xs t `{EA:Enc A} H (Q:A->hprop),
  F = val_fixs f xs t ->
  trms_to_vals ts = Some vs ->
  var_fixs_exec f (length vs) xs ->
  H ==> ^(Wp (combine (f::xs) (F::vs)) t) Q ->
  Triple (trm_apps F ts) H Q.
Proof using.
  introv HF Hvs Hxs M. lets ->: trms_to_vals_spec Hvs.
  rewrite var_fixs_exec_eq in Hxs. rew_istrue in Hxs. lets (_&Lxs&_): Hxs.
  applys* Triple_apps_fixs. rewrite <- isubstn_eq_substn; [|rew_list~].
  applys* Triple_isubst_of_Wp.
Qed.





(* ---------------------------------------------------------------------- *)
(* ** Lemmas for tactics *)





(*
Lemma xlet_lemma : forall Q1 (F1:formula) (F2of:forall `{EA1:Enc A1},A1->Formula) H Q,
  is_local F1 ->
  H ==> F1 Q1 ->
  (forall X, Q1 X ==> F2 X Q) ->
  H ==> Wp_let F1 F2of Q.
Proof using.
  introv L M1 M2. applys local_erase'. applys~ local_weaken M1.
Qed.



Definition Wp_let (F1:Formula) (F2of:forall `{EA1:Enc A1},A1->Formula) : Formula :=
  Local (fun A (EA:Enc A) Q =>
    \exists (A1:Type) (EA1:Enc A1) ,
      ^F1 (fun (X:A1) => ^(F2of X) Q)).

*)

(* use:  notypeclasses refine (xlet_instantiate _ _ _). *)

Lemma xlet_instantiate' : forall A1 (EA1:Enc A1) H Fof,
  H ==> Fof A1 EA1 ->
  H ==> \exists (A1:Type) (EA1:Enc A1), Fof A1 EA1.
Proof using. introv M. hsimpl* A1 EA1. Qed.

Lemma xlet_instantiate : forall A1 (EA1:Enc A1) H `{EA:Enc A} (Q:A->hprop) (F1:Formula) (F2of:forall `{EA1:Enc A2},A2->Formula),
  H ==> ^F1 (fun (X:A1) => ^(F2of X) Q) ->
  H ==> ^(Wp_let F1 (@F2of)) Q.
Proof using.
  introv M. applys Local_erase. notypeclasses refine (xlet_instantiate' _ _ _). applys M.
Qed.

(*
Lemma xlet_typed_instantiate : forall A1 (EA1:Enc A1) H Fof,
  H ==> Fof A1 EA1 ->
  H ==> \exists (A1:Type) (EA1:Enc A1), Fof A1 EA1.
Proof using. introv M. hsimpl* A1 EA1. Qed.
*)

Lemma xapp_triple_to_Wp_Triple : forall A `{EA:Enc A} (Q1:A->hprop) t H1,
  Triple t H1 Q1 ->
  H1 ==> ^(Wp_Triple t) Q1.
Proof using. introv M. applys* himpl_weakestpre. Qed.

Lemma xapp_lemma' : forall A `{EA:Enc A} (Q1:A->hprop) t H1 H Q, (* DEPRECATED *)
  Triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  H ==> ^(Wp_Triple t) Q.
Proof using. 
  introv M1 M2. lets M: xapp_triple_to_Wp_Triple (rm M1).
  hchanges (rm M2). hchanges (rm M).
  applys weakestpre_conseq_wand.
  applys is_local_Triple.
Qed.

Lemma xapp_lemma : forall A `{EA:Enc A} (Q1:A->hprop) t H1 H Q,
  Triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  H ==> ^(Local (Wp_Triple t)) Q.
Proof using.
  introv M1 M2. applys Local_erase. applys* xapp_lemma'.
Qed.

Lemma xval_lemma : forall `{EA:Enc A} (V:A) v H (Q:A->hprop),
  v = ``V ->
  H ==> Q V ->
  H ==> ^(Wp_val v) Q.
Proof using. introv E N. subst. applys Local_erase. hsimpl~ V. Qed.

Lemma xval_lemma_val : forall `{EA:Enc A} (V:A) v H (Q:val->hprop),
  v = ``V ->
  H ==> Q (``V) ->
  H ==> ^(Wp_val v) Q.
Proof using. introv E N. subst. applys Local_erase. hsimpl~ (``V). Qed.



Lemma xcase_lemma : forall F1 (P:Prop) F2 H `{EA:Enc A} (Q:A->hprop),
  (H ==> ^F1 Q) ->
  (P -> H ==> ^F2 Q) ->
  H ==> ^(Wp_case_val F1 P F2) Q.
Proof using. 
  introv M1 M2. apply Local_erase. applys himpl_hand_r. 
  { auto. }
  { applys* hwand_move_l_pure. }
Qed.

Lemma xcase_lemma0 : forall F1 (P1 P2:Prop) F2 H `{EA:Enc A} (Q:A->hprop),
  (P1 -> H ==> ^F1 Q) ->
  (P2 -> H ==> ^F2 Q) ->
  H ==> ^(Wp_case_val (fun `{EA1:Enc A1} (Q:A1->hprop) => \[P1] \-* ^F1 Q) P2 F2) Q.
Proof using. 
  introv M1 M2. applys* xcase_lemma. { applys* hwand_move_l_pure. }
Qed.

Lemma xcase_lemma2 : forall (F1:val->val->Formula) (P1:val->val->Prop) (P2:Prop) F2 H `{EA:Enc A} (Q:A->hprop),
  (forall x1 x2, P1 x1 x2 -> H ==> ^(F1 x1 x2) Q) ->
  (P2 -> H ==> ^F2 Q) ->
  H ==> ^(Wp_case_val (fun `{EA1:Enc A1} (Q:A1->hprop) => \forall x1 x2, \[P1 x1 x2] \-* ^(F1 x1 x2) Q) P2 F2) Q.
Proof using. 
  introv M1 M2. applys* xcase_lemma.
  { repeat (applys himpl_hforall_r ;=> ?). applys* hwand_move_l_pure. }
Qed.

Lemma xmatch_list : forall `{EA:Enc A} (L:list A) (F1:Formula) (F2:val->val->Formula) H `{HB:Enc B} (Q:B->hprop),
  (L = nil -> H ==> ^F1 Q) ->
  (forall X L', L = X::L' -> H ==> ^(F2 ``X ``L') Q) ->
  H ==> ^(Match_ ``L With
         '| 'nil '=> F1
         '| vX ':: vL' [vX vL'] '=> F2 vX vL') Q.
Proof using.
  introv M1 M2. applys xcase_lemma0 ;=> E1.
  { destruct L; rew_enc in *; tryfalse. applys* M1. }
  { destruct L; rew_enc in *; tryfalse. applys xcase_lemma2.
    { intros x1 x2 Hx. inverts Hx. applys* M2. }
    { intros N. false* N. } }
Qed.


Definition xseq_lemma := @Local_erase.
Definition xlet_lemma := @Local_erase.


Lemma xreturn_lemma_typed : forall `{Enc A1} (F:(A1->hprop)->hprop) (Q:A1->hprop) H,
  H ==> F Q ->
  H ==> ^(Formula_typed F) Q.
Proof using.
  introv M. unfold Formula_typed. hsimpl* Q. applys PostChange_refl.
Qed.

Lemma xreturn_lemma_val : forall `{Enc A1} (F:(A1->hprop)->hprop) (Q:val->hprop) H,
  H ==> F (fun (X:A1) => Q (enc X)) ->
  H ==> ^(Formula_typed F) Q.
Proof using.
  introv M. unfold Formula_typed. hsimpl* Q.
  unfold PostChange. intros X. hsimpl* X.
Qed.

Lemma xifval_lemma : forall `{EA:Enc A} b H (Q:A->hprop) (F1 F2:Formula),
  (b = true -> H ==> ^F1 Q) ->
  (b = false -> H ==> ^F2 Q) ->
  H ==> ^(Wp_if_val b F1 F2) Q.
Proof using. introv E N. applys Local_erase. case_if*. Qed.

Lemma xifval_lemma_isTrue : forall `{EA:Enc A} (P:Prop) H (Q:A->hprop) (F1 F2:Formula),
  (P -> H ==> ^F1 Q) ->
  (~ P -> H ==> ^F2 Q) ->
  H ==> ^(Wp_if_val (isTrue P) F1 F2) Q.
Proof using. introv E N. applys Local_erase. case_if*. Qed.




(* ********************************************************************** *)
(* * Point *)

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



(* ********************************************************************** *)
(* * Point *)

Module Point.

Definition X : field := 0%nat.
Definition Y : field := 1%nat.
Definition S : field := 2%nat.

(*
Definition Point (p:loc) : hprop :=
  \exists x y s, p ~> Record`{ X := x; Y := y; S := s } \* [ s = x + y ].
*)


End Point.


(* ********************************************************************** *)
(* * Mutable lists *)


Module MList.

(*
  - For recursive predicate: would be useful to recall the duality between
   `Fixpoint` and `Inductive` for defining predicates, taking the example of `In` and `Forall` on lists.
*)
(*
    ```
       Fixpoint MList A `{EA:Enc A} (L:list A) (p:loc) : hprop :=
         Hexists v, p ~> v  \*
         match L with
         | nil => \[v = Nil]
         | x::L => Hexists p', \[v = Cons(x,p')] \* (p' ~> MList L')
         end.
    ```


   length : using recursion + using loop
   copy : using recursion + using loop
   append (destructive, or non-destructive)
   mem
   count
   in-place reversal
   cps-append (bonus example)
   split 
   combine  
   basic sorting on list of integers, e.g. merge sort, insertion sort

*)

End MList.


(* ********************************************************************** *)
(* * Basic *)

Module Basic.

(* ---------------------------------------------------------------------- *)
(** Incr *)

Definition val_incr : val :=
  ValFun 'p :=
   'p ':= ((val_get 'p) '+ 1).

(* VARIANT:
  ValFun 'p :=
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
  (* xcf *)
  applys Triple_apps_funs_of_Wp.
  { reflexivity. }
  { reflexivity. }
  { reflexivity. }
  simpl.
  (* xlet-poly *)
  notypeclasses refine (xlet_instantiate _ _ _ _ _).
  (* xlet *)
  eapply Local_erase.
  (* xapps *)
  applys @xapp_lemma. { applys Triple_get. } hsimpl ;=> ? ->.
  (* return *)
  applys @xreturn_lemma_val.
  (* xapp *)
  applys @xapp_lemma. { eapply @Triple_set. } hsimpl.
  (* done *) 
  auto.
Qed.

Lemma Triple_incr_frame : forall (p1 p2:loc) (n1 n2:int),
  TRIPLE (val_incr p1)
    PRE (p1 ~~> n1 \* p2 ~~> n2)
    POST (fun (r:unit) => (p1 ~~> (n1+1) \* p2 ~~> n2)).
Proof using.
  skip.
Qed.

(* TODO SHOULD BE:

  xcf.
  xlet. { xapp. xapplys triple_get. }
  hpull ;=> ? ->.
  xlet. { xapp. xapplys triple_add. }
  hpull ;=> ? ->.
  xapp. xapplys triple_set. auto.

then just:

  xcf.
  xapp.
  xapp.
  xapp.

*)

(*

(* ---------------------------------------------------------------------- *)
(** Swap *)

Definition val_swap :=
  ValFun 'p 'q :=
    Let 'x := val_get 'p in
    Let 'y := val_get 'q in
    val_set 'p 'y ;;;
    val_set 'q 'x.

Lemma Triple_swap_neq : forall A1 A2 `{EA1:Enc A1} `{EA2:Enc A2} (v:A1) (w:A2) p q,
  Triple (val_swap ``p ``q)
    PRE (p ~~> v \* q ~~> w)
    POST (fun (r:unit) => p ~~> w \* q ~~> v).
Proof using.
  xcf. xapps. xapps. xapps. xapps. hsimpl~.
Qed.

Lemma Triple_swap_eq : forall A1 `{EA1:Enc A1} (v:A1) p,
  Triple (val_swap ``p ``p)
    PRE (p ~~> v)
    POST (fun (r:unit) => p ~~> v).
Proof using.
  xcf. xapps. xapps. xapps. xapps. hsimpl~.
Qed.


(* ---------------------------------------------------------------------- *)
(** Succ using incr *)

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
  (* not possible: applys local_erase. unfold cf_val. hsimpl. *)
  xvals~.
Qed.



(* ---------------------------------------------------------------------- *)
(** Basic let-binding example *)

Definition val_example_let :=
  ValFun 'n :=
    Let 'a := 'n '+ 1 in
    Let 'b := 'n '- 1 in
    'a '+ 'b.

Lemma Triple_val_example_let : forall n,
  Triple (val_example_let n)
    PRE \[]
    POST (fun r => \[r = 2*n]).
Proof using.
  xcf. xapps. xapps. xapp. hsimpl. math.
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
  ValFun 'n :=
    Let 'k := 'n '+ 1 in
    Let 'i := 'ref 'k in
    val_incr 'i ;;;
    '!'i.

Lemma Triple_val_example_one_ref : forall n,
  Triple (val_example_one_ref n)
    PRE \[]
    POST (fun r => \[r = n+2]).
Proof using.
  xcf. xapps. xapps ;=> r. xapp~. xapp~. hsimpl. math.
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

Lemma Triple_val_example_two_ref : forall n,
  Triple (val_example_two_ref n)
    PRE \[]
    POST (fun r => \[r = n+1]).
Proof using.
  xcf. xapp ;=> i. xapp ;=> r.
  xapp~. xapp~. xapps. xapps. xapps. xapps~.
  xapps. xapps. xapps.
  hsimpl. math.
Qed.

*)

End Basic.


(* ********************************************************************** *)
(* * Test *)

Module Test.

(* ---------------------------------------------------------------------- *)
(* ** Case without variables *)

Definition val_test1 : val :=
  ValFun 'p :=
    Case' 'p = pat_unit Then 'Fail Else 'Fail.

Lemma Triple_test1 : forall (p:loc),
  TRIPLE (val_test1 ``p)
    PRE \[]
    POST (fun (u:unit) => \[]).
Proof using.
  intros.
  (* xcf *)
  applys Triple_apps_funs_of_Wp; try reflexivity. simpl.
Admitted.


(* ---------------------------------------------------------------------- *)
(* ** Case with 1 variable *)

Definition val_test2 : val :=
  ValFun 'p :=
    Case' 'p = 'x Then 'x Else 'Fail.

Lemma Triple_test2 : forall (p:loc),
  TRIPLE (val_test2 p)
    PRE \[]
    POST (fun (u:unit) => \[]).
Proof using.
  intros.
  (* xcf *)
  applys Triple_apps_funs_of_Wp; try reflexivity. simpl.
Admitted.


(* ---------------------------------------------------------------------- *)
(* ** Match without variables *)


Definition val_test0 : val :=
  ValFun 'p :=
    Case' 'p = pat_unit Then 'Fail Else
    Case' 'p = pat_unit Then 'p Else 
    'Fail.

Lemma triple_test0 : forall (p:loc),
  TRIPLE (val_test0 p)
    PRE \[]
    POST (fun (u:unit) => \[]).
Proof using.
  intros.
  (* xcf *)
  applys Triple_apps_funs_of_Wp; try reflexivity. simpl.
Admitted.


End Test.

(* ********************************************************************** *)
(* * Stack *)

Module Stack.

Definition val_is_empty : val :=
  ValFun 'p :=
    val_get 'p '= 'nil.

Definition val_empty : val :=
  ValFun 'u :=
   val_ref 'nil.

Definition val_push : val :=
  ValFun 'p 'x :=
   'p ':= ('x ':: (val_get 'p)).

Definition val_pop : val :=
  ValFun 'p :=
   (Let 'q := val_get 'p in
   Match 'q With
   '| 'nil '=> 'Fail
   '| 'x ':: 'r '=> ('p ':= 'r) '; 'x
   End).

Definition val_rev_append : val :=
  ValFix 'f 'p1 'p2 :=
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
  (* xcf *)
  intros. applys Triple_apps_funs_of_Wp; try reflexivity; simpl.
  (* xunfold *)
  xunfold Stack.
  (* xlet-poly *)
  notypeclasses refine (xlet_instantiate _ _ _ _ _).
  (* xapps *)
  applys @xapp_lemma. { eapply @Triple_get. } hsimpl ;=> ? ->.
  (* xlet-poly *)
  notypeclasses refine (xlet_instantiate _ _ _ _ _).
  (* xval *)
  applys~ (xval_lemma nil).
  (* xapps *)
  applys @xapp_lemma. { eapply @Triple_eq_val. } hsimpl ;=> ? ->.
  (* done *)
  hsimpl. rewrite* @Enc_injective_value_eq_r.
Qed.

Lemma Triple_pop : forall `{Enc A} (p:loc) (L:list A),
  L <> nil ->
  TRIPLE (val_pop p)
    PRE (p ~> Stack L)
    POST (fun (x:A) => \exists L', \[L = x::L'] \* (p ~> Stack L')).
Proof using.
  introv N.
  (* xcf *)
  applys Triple_apps_funs_of_Wp; try reflexivity; simpl.
  (* xunfold *)
  xunfold Stack.
  (* xlet-poly *)
  notypeclasses refine (xlet_instantiate _ _ _ _ _).
  (* xapps *)
  applys @xapp_lemma. { eapply @Triple_get. } hsimpl ;=> ? ->.
  (* Two ways of completing the proof *)
  dup.
  (* xcase with lemma for match list *)
  { applys xmatch_list.
    { intros HL. false. }
    { intros X L' HL. 
      (* xseq *)
      applys xseq_lemma.
      (* xapp *)
      applys @xapp_lemma. { applys @Triple_set. } hsimpl.
      (* xval *)
      applys~ xval_lemma.
      (* done *)
      hsimpl~. } }
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
        applys @xapp_lemma. { applys @Triple_set. } hsimpl.
        (* xval *)
        applys~ xval_lemma.
        (* post *)
        hsimpl~. } } }
Qed.

Lemma Triple_empty : forall `{Enc A} (u:unit),
  TRIPLE (val_empty u)
    PRE \[]
    POST (fun p => (p ~> Stack (@nil A))).
Proof using.
  (* xcf *)
  intros. applys Triple_apps_funs_of_Wp; try reflexivity; simpl.
  (* xlet-poly *)
  notypeclasses refine (xlet_instantiate _ _ _ _ _).
  (* xval *)
  applys~ (xval_lemma_val (@nil A)).
  (* xapp *)
  applys @xapp_lemma. { eapply @Triple_ref. } hsimpl.
  (* done *)
  auto.
Qed.

Lemma Triple_push : forall `{Enc A} (p:loc) (x:A) (L:list A),
  TRIPLE (val_push p (``x))
    PRE (p ~> Stack L)
    POST (fun (u:unit) => (p ~> Stack (x::L))).
Proof using.
  (* xcf *)
  intros. applys Triple_apps_funs_of_Wp; try reflexivity; simpl.
  (* xunfold *)
  xunfold Stack.
  (* xlet-poly *)
  notypeclasses refine (xlet_instantiate _ _ _ _ _).
  (* xlet-poly *)
  notypeclasses refine (xlet_instantiate _ _ _ _ _).
  (* xapps *)
  applys @xapp_lemma. { eapply @Triple_get. } hsimpl ;=> ? ->.
  (* xval *)
  applys~ (xval_lemma_val (x::L)).
  (* xapps *)
  applys @xapp_lemma. { eapply @Triple_set. } hsimpl. 
  (* done *)
  auto.
Qed.

Opaque Stack.

Lemma Triple_rev_append : forall `{Enc A} (p1 p2:loc) (L1 L2:list A),
  TRIPLE (val_rev_append p1 p2)
    PRE (p1 ~> Stack L1 \* p2 ~> Stack L2)
    POST (fun (u:unit) => p1 ~> Stack nil \* p2 ~> Stack (rev L1 ++ L2)).
Proof using.
  intros. gen p1 p2 L2. induction_wf IH: (@list_sub A) L1. intros.
  (* xcf *)
  intros. applys Triple_apps_fixs_of_Wp; try reflexivity; simpl.
  (* xlet *)
  applys xlet_lemma.
  (* xapps *)
  applys @xapp_lemma. { eapply @Triple_is_empty. } hsimpl ;=> ? ->.
  (* xif *)
  applys @xifval_lemma_isTrue ;=> C.
  (* case nil *)
  { (* xval *)
    applys~ (xval_lemma tt).
    (* done *)
    hsimpl. subst. rew_list~. }
  (* case cons *)
  { (* xlet-poly *)
    notypeclasses refine (xlet_instantiate _ _ _ _ _).
    (* xapp *)
    applys @xapp_lemma. { applys @Triple_pop. eauto. } hsimpl ;=> x L1' E.
    (* xseq *)
    applys xseq_lemma.
    (* xapp *)
    applys @xapp_lemma. { applys @Triple_push. } hsimpl.
    (* xapp *)
    applys @xapp_lemma. { applys IH L1'. subst*. } hsimpl.
    (* done *)
    hsimpl. subst. rew_list~. }
Qed.


End Stack.



















