(**

This file provides examples of proofs manipulating characteristic formula 
in weakest-precondition form, in lifted Separation Logic,
as defined in [LambdaWPLifted.v].

Author: Arthur Charguéraud.
License: MIT.

*)


Set Implicit Arguments.
From Sep Require Export LambdaWPStruct.
Generalizable Variables A B.

Import NotationForVariables NotationForTerms.
Open Scope val_scope.
Open Scope pat_scope.
Open Scope trm_scope.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xwp] *)

Ltac xwp_fun tt :=
  applys xtriple_lemma_funs; [ reflexivity | reflexivity | reflexivity | xwp_simpl ].

Ltac xwp_fix tt :=
  applys xtriple_lemma_fixs; [ reflexivity | reflexivity | reflexivity | xwp_simpl ].

Ltac xwp_trm tt :=
  fail "not yet implemented".

Ltac xwp_core tt :=
  intros; first [ xwp_fun tt | xwp_fix tt | xwp_trm tt ].

Tactic Notation "xwp" :=
  xwp_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xspec] *)

(* ** Database of specifications used by [xapp], through tactic [xspec] *)

(** A name for the database *)

Definition database_spec := True.

Notation "'Register_goal' G" := (Register database_spec G)
  (at level 69) : xspec_scope.

Open Scope xspec_scope.

(** [xspec G] retreives from the database [database_spec]
    the specification that could apply to a goal [G].
    It places the specification as hypothesis at the head of the goal. *)

Ltac xapp_basic_prepare tt := 
  idtac.

Ltac xspec_context G :=
  fail "not implemented".

Ltac xspec_registered G :=
  ltac_database_get database_spec G.

Ltac xspec_database G :=
   first [ xspec_registered G | xspec_context G ].

Ltac xspec_base tt :=
  match goal with
  | |- ?G => xspec_database G
  end.

Ltac xspec_core tt :=
  xapp_basic_prepare tt;
  xspec_base tt.

Tactic Notation "xspec" :=
  xspec_core tt.

Ltac xspec_prove_triple tt :=
  let H := fresh "Spec" in
  xspec; intro H; apply H.

Ltac xspec_lemma_of_args E :=
  match list_boxer_of E with
  | cons (boxer ltac_wild) ?E' => (* only args provided *)
     let H := fresh "Spec" in
     xspec; intro H; constr:((boxer H)::E')
  | _ => (* spec and args provided *)
     constr:(E)
  end.

Ltac xspec_prove_triple_with_args E :=
  let L := xspec_lemma_of_args E in
  applys L.


(* ---------------------------------------------------------------------- *)
(* ** Registering specifications for lifted triple *)

Notation "'Register_Spec' f" := (Register_goal (Triple (trm_apps (trm_val f) _) _ _))
  (at level 69) : xspec_scope.


(* ---------------------------------------------------------------------- *)
(* ** Specification of primitives *)

Hint Extern 1 (Register_Spec (val_prim val_ref)) => Provide Triple_ref.
Hint Extern 1 (Register_Spec (val_prim val_get)) => Provide Triple_get.
Hint Extern 1 (Register_Spec (val_prim val_set)) => Provide @Triple_set.
Hint Extern 1 (Register_Spec (val_prim val_alloc)) => Provide Triple_alloc.
Hint Extern 1 (Register_Spec (val_prim val_eq)) => Provide Triple_eq.
Hint Extern 1 (Register_Spec (val_prim val_add)) => Provide Triple_add.
Hint Extern 1 (Register_Spec (val_prim val_sub)) => Provide Triple_sub.
Hint Extern 1 (Register_Spec (val_prim val_ptr_add)) => Provide Triple_ptr_add.



(* ---------------------------------------------------------------------- *)
(* ** Tactic [xcast] *)

Ltac xcast_core tt :=
  applys xcast_lemma.

Tactic Notation "xcast" :=
  xcast_core tt.



(* ---------------------------------------------------------------------- *)
(* ** Tactic [xgoal_*] *)

Ltac xgoal_code tt :=
  match goal with |- PRE _ CODE ?C POST _ => constr:(C) end.

Ltac xgoal_code_strip_iswp C :=
  match C with
  | is_Wp ?C' => xgoal_code_strip_iswp C'
  | ?C' => constr:(C')
  end.

Ltac xgoal_code_without_iswp tt :=
  let C := xgoal_code tt in
  xgoal_code_strip_iswp C.

Ltac xgoal_fun tt :=
  match xgoal_code_without_iswp tt with 
  | Wp_app (trm_apps (trm_val ?f) _) => constr:(f)
  end.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp_record] *)

Ltac xapp_record_post tt :=
  hsimpl; simpl; hsimpl; try xcast.

Ltac xapp_record_get tt :=
  applys xapp_record_get; xapp_record_post tt.

Ltac xapp_record_set tt :=
  applys xapp_record_set; xapp_record_post tt.

Ltac xapp_record tt :=
  match xgoal_fun tt with
  | (val_get_field _) => xapp_record_get tt
  | (val_set_field _) => xapp_record_set tt
  end.



(* ---------------------------------------------------------------------- *)
(* ** Tactic [xif] *)

Ltac xif_core tt :=
  first [ applys @xifval_lemma_isTrue
        | applys @xifval_lemma ].

Tactic Notation "xif" :=
  xif_core tt.



(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp] *)

Ltac xapp_post tt :=
  hsimpl.
  
Ltac xapp_apply_lemma cont :=
  first 
    [ applys @xapps_lemma; [ cont tt | xapp_post tt ]
    | applys @xapps_lemma_pure; [ cont tt | xapp_post tt ]
    | applys @xapp_lemma; [ cont tt | xapp_post tt ] ].

Ltac xapp_general tt :=
  xapp_apply_lemma ltac:(xspec_prove_triple).

Ltac xapp_core tt :=
  first [ xapp_record tt
        | xapp_general tt ].

Tactic Notation "xapp" :=
  xapp_core tt.
Tactic Notation "xapp" "~" :=
  xapp; auto_tilde.
Tactic Notation "xapp" "*"  :=
  xapp; auto_star.

Ltac xapp_arg_core E :=
  xapp_apply_lemma ltac:(fun tt => xspec_prove_triple_with_args E).

Tactic Notation "xapp" constr(E) :=
  xapp_arg_core E.
Tactic Notation "xapp" "~" constr(E) :=
  xapp E; auto_tilde.
Tactic Notation "xapp" "*" constr(E) :=
  xapp E; auto_star.

Tactic Notation "xapp_debug" :=
  xapp_apply_lemma tt.

Tactic Notation "xapp_debug" constr(E) :=
  xapp_apply_lemma tt; 
  [ let L := xspec_lemma_of_args E in 
    let H := fresh "Spec" in
    generalize L; intros H
  | ].
 

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xval] *)

Ltac xval_arg E :=
  applys (xval_lemma E); [ try reflexivity | ].

Tactic Notation "xval" uconstr(E) :=
  xval_arg E.
Tactic Notation "xval" "~" uconstr(E) :=
  xval E; auto_tilde.
Tactic Notation "xval" "*" uconstr(E) :=
  xval E; auto_star.

Ltac xval_core tt :=
  applys xval_lemma; [ try reflexivity | ].

Tactic Notation "xval" :=
  xval_core tt.
Tactic Notation "xval" "~" :=
  xval; auto_tilde.
Tactic Notation "xval" "*"  :=
  xval; auto_star.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xseq] *)

Ltac xseq_core tt :=
  applys xseq_lemma.

Tactic Notation "xseq" :=
  xseq_core tt.



(* ---------------------------------------------------------------------- *)
(* ** Tactic [xfail] *)

Ltac xfail_core tt :=
  hpull; false.

Tactic Notation "xfail" :=
  xfail_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xlet] *)

Ltac xlet_poly tt :=
  notypeclasses refine (xlet_lemma _ _ _ _ _).

Ltac xlet_typed tt :=
  applys xlet_typed_lemma.

Ltac xlet_core tt :=
  match xgoal_code_without_iswp tt with
  | (Wp_let_typed _ _) => xlet_typed tt
  | (Wp_let _ _) => xlet_poly tt
  end.

Tactic Notation "xlet" :=
  xlet_core tt.



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
  ValFun 'p :=
   Set 'p'.X ':= ('p'.X '+ 1) ';
   Set 'p'.K ':= ('p'.K '+ 1).


Lemma Triple_move_X : forall p x y,
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
  dup. { xapp (@Triple_add). skip. (* demo *) }
  xapp.
  xapp.
  xlet.
  xlet.
  xapp.
  xapp.
  xapp.
  hsimpl. math.
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
 


(* ---------------------------------------------------------------------- *)
(** Length *)

Definition val_mlist_length : val :=
  ValFix 'f 'p :=
    Let 'v := val_get 'p in
    Match 'v With
    '| '#"nil" '=> 0
    '| '#"cons" 'x 'q '=> 1 '+ 'f 'q
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
  pattern MList at 1. rewrite MList_unfold. hpull ;=> v.
  xapp.
  (* xcase *)
  applys xcase_lemma0 ;=> E1.
  { destruct L as [|x L']; hpull.
    { intros ->. applys~ @xval_lemma 0. hsimpl. skip. (* TODO *) rew_list~. }
    { intros q ->. tryfalse. } }
  { applys xcase_lemma2.
    { intros x q E.
      destruct L as [|x' L']; hpull.
      { intros ->. tryfalse. }
      { intros q' E'. subst v. rewrite enc_val_eq in *. inverts E.
        xlet. 
        xapp* IH. hsimpl. (* TODO: integrate hsimpl? *)
        xapp.
        (* done *)
        pattern MList at 2. rewrite MList_unfold. hsimpl*. rew_list; math. } }
    { intros N. destruct L as [|x L']; hpull.
      { intros ->. rewrite enc_val_eq in *. unfolds Nil. false. }
      { intros q ->. rewrite enc_val_eq in *. unfolds @Cons. false. } } }
Qed.




(*

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
  xwp. xlet. xlet. xapp. xapp. xapp. auto.
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
  xtriple. xapp as p. intros; subst. xapp~. intros _. xapps~.
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
  xtriple. xapp ;=> i. xapp ;=> r.
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
  xwp.
Abort.


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
  xwp.
Abort.


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
  xwp.
Abort.


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
  xwp. xunfold Stack. xlet. xapp. xlet. xval nil.
  xapp @Triple_eq_val. rewrite* @Enc_injective_value_eq_r.
Qed.


Lemma Triple_pop : forall `{Enc A} (p:loc) (L:list A),
  L <> nil ->
  TRIPLE (val_pop p)
    PRE (p ~> Stack L)
    POST (fun (x:A) => \exists L', \[L = x::L'] \* (p ~> Stack L')).
Proof using.
  introv N. xwp. xunfold Stack. xlet. xapp.
  applys xmatch_lemma_list.
  { intros HL. xfail. }
  { intros X L' HL. xseq. xapp. xval. hsimpl~. }
Qed.

Lemma Triple_empty : forall `{Enc A} (u:unit),
  TRIPLE (val_empty u)
    PRE \[]
    POST (fun p => (p ~> Stack (@nil A))).
Proof using.
  xwp. xlet. xval nil. xapp~.
Qed.

Lemma Triple_push : forall `{Enc A} (p:loc) (x:A) (L:list A),
  TRIPLE (val_push p (``x))
    PRE (p ~> Stack L)
    POST (fun (u:unit) => (p ~> Stack (x::L))).
Proof using.
  xwp. xunfold Stack. xlet. xlet. xapp. xval (x::L). xapp~.
Qed.

Opaque Stack.


Lemma Triple_rev_append : forall `{Enc A} (p1 p2:loc) (L1 L2:list A),
  TRIPLE (val_rev_append p1 p2)
    PRE (p1 ~> Stack L1 \* p2 ~> Stack L2)
    POST (fun (u:unit) => p1 ~> Stack nil \* p2 ~> Stack (rev L1 ++ L2)).
Proof using.
  intros. gen p1 p2 L2. induction_wf IH: (@list_sub A) L1. intros.
  xwp. xlet. xapp @Triple_is_empty. xif ;=> C.
  { (* case nil *)
    xval tt. hsimpl. subst. rew_list~. }
  { (* case cons *)
    xlet. xapp~ @Triple_pop ;=> x L1' E. 
    xseq. xapp @Triple_push. 
    xapp (>> IH L1'). { subst*. }
    hsimpl. subst. rew_list~. }
Qed.

End Stack.



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



















