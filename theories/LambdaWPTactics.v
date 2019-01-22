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
Generalizable Variables A.

Implicit Types v w : val.
Implicit Types t : trm.



(* ********************************************************************** *)
(* * Database for registering a specification for each program. *)

(* ---------------------------------------------------------------------- *)
(* ** Database of specifications used by [xapp], through tactic [xspec] *)

(** A name for the database *)

Definition database_spec := True.

Notation "'Register_goal' G" := (Register database_spec G)
  (at level 69) : charac.

(** [xspec G] retreives from the database [database_spec]
    the specification that could apply to a goal [G].
    It places the specification as hypothesis at the head of the goal. *)

Ltac xapp_basic_prepare tt := 
  fail "not instantiated".

Ltac xspec_context G := (* refined only in LambdaCFLifted *)
  fail "not instantiated".

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


(* ---------------------------------------------------------------------- *)
(* ** Registering specifications for lifted triple *)

Notation "'Register_Spec' f" := (Register_goal (Triple (trm_apps (trm_val f) _) _ _))
  (at level 69) : charac.


(* ---------------------------------------------------------------------- *)
(* ** Specification of primitives *)

Hint Extern 1 (Register_Spec (val_prim val_ref)) => Provide Triple_ref.
Hint Extern 1 (Register_Spec (val_prim val_get)) => Provide Triple_get.
Hint Extern 1 (Register_Spec (val_prim val_set)) => Provide Triple_set.
Hint Extern 1 (Register_Spec (val_prim val_alloc)) => Provide Triple_alloc.
Hint Extern 1 (Register_Spec (val_prim val_eq)) => Provide Triple_eq.
Hint Extern 1 (Register_Spec (val_prim val_add)) => Provide Triple_add.
Hint Extern 1 (Register_Spec (val_prim val_sub)) => Provide Triple_sub.
Hint Extern 1 (Register_Spec (val_prim val_ptr_add)) => Provide Triple_ptr_add.




(* ********************************************************************** *)
(* * Auxiliary tactics *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xlocal] *)

Ltac xlocal' :=
  try solve [ apply is_local_local ].
  (*   | apply is_local_wp_triple ]. *)


(*--------------------------------------------------------*)
(* ** [xdecode_args] : used internally *)

Ltac xdecode_arg v :=
  let W := constr:(decode v) in
  let W' := (eval simpl decode in W) in
  match W' with Dyn ?V' =>
    change (trm_val v) with (trm_val (enc V'))
  end.

Ltac xdecode_args_from_trms ts :=
  match ts with
  | (trm_val (enc ?V))::?ts' => xdecode_args_from_trms ts'
  | (trm_val ?v)::?ts' => xdecode_arg v; xdecode_args_from_trms ts'
  | nil => idtac
  end.

Ltac xdecode_args tt :=
  match goal with |- Triple (trm_apps ?f ?ts) ?H ?Q =>
    xdecode_args_from_trms ts end.


(*--------------------------------------------------------*)
(* ** [xeq_encs] : used internally *)

(** [xeq_encs] solves goal of the form [ [`V1; ..; `VN] = encs ?VS ]. *)

Lemma encs_nil :
  encs nil = @nil val.
Proof using. auto. Qed.

Lemma encs_cons : forall `{EA:Enc A} (V:A) (VS:dyns),
  encs ((Dyn V)::VS) = (enc V)::(encs VS).
Proof using. auto. Qed.

Hint Rewrite <- @encs_nil @encs_cons : rew_encs.

Tactic Notation "rew_encs" :=
  autorewrite with rew_encs.

Ltac xeq_encs_core tt :=
  rew_encs; reflexivity.

(* DEPRECATED
match goal with |- ?vs = encs ?Vs => applys (refl_equal (encs (decodes vs))) end.*)

Tactic Notation "xeq_encs" :=
  xeq_encs_core tt.


(*--------------------------------------------------------*)
(* ** [rew_dyn] *)

Hint Rewrite dyn_to_val_dyn_make @enc_decode enc_dyn_make : rew_dyn.
 (* DEPRECATEd: was enc_dyn_eq *)

(** The encoding of a dynamic value [V] is the same as the encoding of V *)

Tactic Notation "rew_dyn" :=
  autorewrite with rew_dyn; simpl dyn_value.
Tactic Notation "rew_dyn" "in" hyp(H) :=
  autorewrite with rew_dyn in H; simpl dyn_value in H.
Tactic Notation "rew_dyn" "in" "*" :=
  autorewrite with rew_dyn in *; simpl dyn_value in *.



(* ********************************************************************** *)
(* * Tactics for computing characteristic formulae *)


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xcf] *)

Ltac xcf_get_fun_remove_encs f :=
  constr:(f).

Ltac xcf_get_fun_from_goal tt :=
  match goal with |- @Triple (trm_apps (trm_val ?f) _) _ _ _ _ => constr:(f) end.

Ltac xcf_get_fun tt :=
  xcf_get_fun_from_goal tt.

Ltac xcf_reveal_fun tt :=
  try (let f := xcf_get_fun tt in
       first [ unfold f
             | match goal with H: f = _ |- _ => rewrite H end ]).

Ltac xcf_trm n :=
 (*  applys triple_trm_of_wp_iter n; [ xcf_post tt ]. *) fail.

Ltac xcf_post tt :=
  simpl; rew_enc_dyn.

Ltac xcf_basic_fun n f':=
  let f := xcf_get_fun tt in
  match f with
  | val_fixs _ _ _ =>
      applys Triple_apps_fixs_of_Wp f';
      [ try unfold f'; try reflexivity (* TODO: how in LambdaCF? *)
        (* reflexivity *)
      | try xeq_encs
      | reflexivity
      | xcf_post tt ]
  end.

Ltac xcf_fun n :=
  let f' := xcf_get_fun tt in
  xcf_reveal_fun tt;
  (*rew_trms_vals;*)
  xcf_basic_fun n f'.

Ltac xcf_prepare_args tt :=
  try xdecode_args tt.

Ltac xcf_core n :=
  intros; first [ xcf_fun n | xcf_trm n ].

Tactic Notation "xcf" :=
  xcf_core 100%nat.

Tactic Notation "xcf_depth" constr(depth) :=
  xcf_core depth.





(* ********************************************************************** *)
(* * Tactics for manipulating characteristic formulae *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xseq] *)

Ltac xseq_core tt :=
  fail "not instantiated".

Tactic Notation "xseq" :=
  xseq_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xlet] *)

Lemma xlet_lemma : forall Q1 (F1:formula) (F2:val->formula) H Q,
  is_local F1 ->
  H ==> F1 Q1 ->
  (forall X, Q1 X ==> F2 X Q) ->
  H ==> wp_let F1 F2 Q.
Proof using.
  introv L M1 M2. applys local_erase'. applys~ local_weaken M1.
Qed.

Ltac xlet_core tt :=
  applys xlet_lemma; [ xlocal' | | ].

Tactic Notation "xlet" :=
  xlet_core tt.

Ltac xlet_as_core X :=
  xlet_core tt; [ | intros X ].

Tactic Notation "xlet" "as" simple_intropattern(X) :=
  xlet_as_core X.



(* ---------------------------------------------------------------------- *)
(* ** Tactic [xif] *)

Ltac xif_post tt :=
  rew_bool_eq.

Ltac xif_core tt :=
  fail "not instantiated".

Tactic Notation "xif" :=
  xif_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xfail] *)

Ltac xfail_core tt :=
  fail "not instantiated".

Tactic Notation "xfail" :=
  xfail_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp] *)

Ltac hpull_cont tt :=
  fail "not instantiated".
Ltac hsimpl_cont tt :=
  fail "not instantiated".
Ltac xapp_let_cont tt :=
  fail "not instantiated".
Ltac xapp_as_let_cont tt :=
  fail "not instantiated".
Ltac xapps_let_cont tt :=
  fail "not instantiated".
Ltac xapp_template xlet_tactic xapp_tactic xlet_cont :=
  fail "not instantiated".
Ltac xapp_with_args E cont_xapply :=
  fail "not instantiated".
Ltac xapp_basic E cont_post tt :=
  fail "not instantiated".

Ltac xapp_debug tt :=
  xapp_basic_prepare tt;
  xapp_with_args __ ltac:(fun H => generalize H).

Ltac xapp_core tt :=
  xapp_template ltac:(fun tt => xlet) ltac:(xapp_basic __ idcont) ltac:(xapp_let_cont).

Ltac xapp_arg_core E :=
  xapp_template ltac:(fun tt => xlet) ltac:(xapp_basic E idcont) ltac:(xapp_let_cont).

Ltac xapp_as_core X :=
  xapp_template ltac:(fun tt => xlet as X) ltac:(xapp_basic __ idcont) ltac:(xapp_as_let_cont).

Ltac xapp_arg_as_core E X :=
  xapp_template ltac:(fun tt => xlet as X) ltac:(xapp_basic E idcont) ltac:(xapp_as_let_cont).

Ltac xapps_core tt :=
  xapp_template ltac:(fun tt => xlet) ltac:(xapp_basic __ hpull_cont) ltac:(xapps_let_cont).

Ltac xapps_arg_core E :=
  xapp_template ltac:(fun tt => xlet) ltac:(xapp_basic E hpull_cont) ltac:(xapps_let_cont).

Tactic Notation "xapp" :=
  xapp_core tt.
Tactic Notation "xapp" "~" :=
  xapp; auto_tilde.
Tactic Notation "xapp" "*"  :=
  xapp; auto_star.

Tactic Notation "xapp" constr(E) :=
  xapp_arg_core E.
Tactic Notation "xapp" "~" constr(E) :=
  xapp E; auto_tilde.
Tactic Notation "xapp" "*" constr(E) :=
  xapp E; auto_star.

Tactic Notation "xapps" :=
  xapps_core tt.
Tactic Notation "xapps" "~" :=
  xapps; auto_tilde.
Tactic Notation "xapps" "*" :=
  xapps; auto_star.

Tactic Notation "xapps" constr(E) :=
  xapps_arg_core E.
Tactic Notation "xapps" "~" constr(E) :=
  xapps E; auto_tilde.
Tactic Notation "xapps" "*" constr(E) :=
  xapps E; auto_star.

Tactic Notation "xapp" "as" simple_intropattern(X) :=
  xapp_as_core X.
Tactic Notation "xapp" "~" "as" simple_intropattern(X) :=
  xapp as X; auto_tilde.
Tactic Notation "xapp" "*" "as" simple_intropattern(X) :=
  xapp as X; auto_star.

Tactic Notation "xapp" constr(E) "as" simple_intropattern(X) :=
  xapp_arg_as_core E X.
Tactic Notation "xapp" "~" constr(E) "as" simple_intropattern(X) :=
  xapp E as X; auto_tilde.
Tactic Notation "xapp" "*" constr(E) "as" simple_intropattern(X) :=
  xapp E as X; auto_star.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xval] and [xvals] *)

Ltac xval_core tt :=
  fail "not instantiated".
Ltac xval_as_core X :=
  fail "not instantiated".
Ltac xvals_core tt :=
  fail "not instantiated".

Tactic Notation "xval" :=
  xval_core tt.
Tactic Notation "xval" "~" :=
  xval; auto_tilde.
Tactic Notation "xval" "*"  :=
  xval; auto_star.

Tactic Notation "xvals" :=
  xvals_core tt.
Tactic Notation "xvals" "~" :=
  xvals; auto_tilde.
Tactic Notation "xvals" "*" :=
  xvals; auto_star.

Tactic Notation "xval" "as" simple_intropattern(X) :=
  xval_as_core X.
Tactic Notation "xval" "~" "as" simple_intropattern(X) :=
  xval as X; auto_tilde.
Tactic Notation "xval" "*" "as" simple_intropattern(X) :=
  xval as X; auto_star.




(* ********************************************************************** *)
(* * Tactics for loops *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xwhile] *)

Ltac xwhile_intros_all R LR HR :=
  fail "not instantiated".
Ltac xwhile_intros R :=
  fail "not instantiated".
Ltac xwhile_basic xwhile_intros_tactic :=
  fail "not instantiated".
Ltac xwhile_core xwhile_tactic :=
  fail "not instantiated".

Tactic Notation "xwhile" "as" ident(R) :=
  xwhile_core ltac:(fun tt => xwhile_basic ltac:(fun tt => xwhile_intros R)).

Tactic Notation "xwhile" "as" ident(R) ident(LR) ident(HR) :=
  xwhile_core ltac:(fun tt => xwhile_basic ltac:(fun tt => xwhile_intros_all R LR HR)).




(* ********************************************************************** *)
(* * Notation for triples *)

(* ---------------------------------------------------------------------- *)
(** Notation for WP *)

(** [WP] denotes [Wp_triple], which is [Weakestpre (@Triple t)],
    where [Weakestpre] is the lifted version of the generic [weakestpre]
    predicate defined in [SepFunctor]. *)

Notation "'WP' t Q" := (^(Wp_Triple t) Q)
  (at level 39, t at level 0, Q at level 0) : triple_scope.

Open Scope triple_scope.


(* ---------------------------------------------------------------------- *)
(** Notation for triples *)

Notation "'TRIPLE' t 'PRE' H 'POST' Q" :=
  (Triple t H Q)
  (at level 39, t at level 0) : triple_scope.

Notation "'TRIPLE' t 'PRE' H1 'RET' v 'POST' H2" :=
  (Triple t H1 (fun r => \[r = v] \* H2))
  (at level 39, t at level 0) : triple_scope.

Notation "'TRIPLE' t 'PRE' H1 'BIND' x1 'RET' v 'POST' H2" :=
  (Triple t H1 (fun r => \exists x1, \[r = v] \* H2))
  (at level 39, t at level 0, x1 ident) : triple_scope.

Notation "'TRIPLE' t 'PRE' H1 'BIND' x1 x2 'RET' v 'POST' H2" :=
  (Triple t H1 (fun r => \exists x1 x2, \[r = v] \* H2))
  (at level 39, t at level 0, x1 ident, x2 ident) : triple_scope.


(* ---------------------------------------------------------------------- *)
(** WIP... *)

(** Notation [TRIPLE t PRE H POST Q]
    in weakest-precondition form *)

(*
Definition TRIPLE_def t H `{EA:Enc A} (Q:A->hprop) :=
  forall Q', H \* \[Q ===> Q'] ==> WP t Q'.

Notation "'TRIPLE' t 'PRE' H1 'POST' Q1" :=
  (TRIPLE_def t H1 Q1)
  (at level 39, t at level 0) : triple_scope.


Notation "'TRIPLE' t 'PRE' H1 'POST' Q1" :=
  (forall Q, H1 \* \[Q1 ===> Q] ==> WP t Q)
  (at level 39, t at level 0) : triple_scope.

*)

(** Notation [TRIPLE t PRE H BIND x y RET v POST Q] 
    in weakest-precondition form  

Notation "'TRIPLE' t 'PRE' H1 'RET' v 'POST' H2" :=
  (forall Q, H1 \* \[(fun r => \[r = v] \* H2) ===> Q] ==> WP t Q)
  (at level 39, t at level 0) : triple_scope.

Notation "'TRIPLE' t 'PRE' H1 'BIND' x1 'RET' v 'POST' H2" :=
  (TRIPLE t PRE H1 POST (fun r => \exists x1, \[r = v] \* H2))
  (* (forall Q, H1 \* \[(fun r => \exists x1, \[r = v] \* H2) ===> Q] ==> Wp_Triple t Q) *)
  (at level 39, t at level 0, x1 ident) : triple_scope.
*)

(* ALTERNATIVE

Notation "'TRIPLE' t 'PRE' H1 'RET' v 'POST' H2" :=
  (forall Q, H1 \* \[H2 ==> Q v] ==> WP t Q)
  (at level 68, t at level 0) : triple_scope.

Notation "'TRIPLE' t 'PRE' H1 'BIND' x1 'RET' v 'POST' H2" :=
  (forall Q, H1 \* \[forall x1, H2 ==> Q v] ==> WP t Q)
  (at level 68, t at level 0, x1 ident) : triple_scope.

Notation "'TRIPLE' t 'PRE' H1 'BIND' x1 x2 x3 'RET' v 'POST' H2" :=
  (forall Q, H1 \* \[forall x1 x2 x3, H2 ==> Q v] ==> WP t Q)
  (at level 68, t at level 0, x1 ident, x2 ident, x3 ident) : triple_scope.

Notation "'TRIPLE' t 'PRE' H1 'BIND' x1 x2 x3 x4 'RET' v 'POST' H2" :=
  (forall Q, H1 \* \[forall x1 x2 x3 x4, H2 ==> Q v] ==> WP t Q)
  (at level 68, t at level 0, x1 ident, x2 ident, x3 ident, x4 ident) : triple_scope.

*)

(* TODO: use recursive notation *)


(* TODO:

Notation "'TRIPLE' t 'PRE' H1 'BIND' x1 'RET' v 'POST' H2" :=
  (Triple t H1 (fun r => \exists x1, \[r = v] \* H2) Q)
 or just:
  (forall Q, H1 \* \[forall x1, H2 ==> Q v] ==> WP t Q)
  (at level 68, t at level 0, x1 ident) : triple_scope.

*)


(* ********************************************************************** *)
(* * Demo *)


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp] demo

Lemma xapp_lemma : forall t H `{EA:Enc A} (Q:A->hprop),
  Triple t H Q ->
  H ==> ^(Wp_app t) Q.
Proof using.
  introv M. applys local_erase'. rewrite~ <- Triple_eq_himpl_Wp_triple.
Qed.

Ltac xapp_core tt ::=
  applys xapp_lemma.

 *)



(* ---------------------------------------------------------------------- *)
(* ** Tactic *) 

Lemma WP_of_Wp : forall t H `{EA:Enc A} (Q:A->hprop),
  H ==> ^(Wp Ctx.empty t) Q ->
  H ==> WP t Q.
Proof using. introv M. applys himpl_weakestpre. applys* Triple_of_Wp. Qed.



Lemma Local_erase' : forall H F `{EA:Enc A} (Q:A->hprop),
  H ==> ^F Q ->
  H ==> ^(Local F) Q.
Proof using.
  introv M. hchanges M. applys local_erase.
Qed.

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
  introv M. applys Local_erase'. notypeclasses refine (xlet_instantiate' _ _ _). applys M.
Qed.

(*
Lemma xlet_typed_instantiate : forall A1 (EA1:Enc A1) H Fof,
  H ==> Fof A1 EA1 ->
  H ==> \exists (A1:Type) (EA1:Enc A1), Fof A1 EA1.
Proof using. introv M. hsimpl* A1 EA1. Qed.
*)

Lemma xapp_triple_to_WP : forall A `{EA:Enc A} (Q1:A->hprop) t H1,
  Triple t H1 Q1 ->
  H1 ==> WP t Q1.
Proof using. introv M. applys* himpl_weakestpre. Qed.

Lemma xapp_lemma' : forall A `{EA:Enc A} (Q1:A->hprop) t H1 H Q,
  Triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  H ==> WP t Q.
Proof using. 
  introv M1 M2. lets M: xapp_triple_to_WP (rm M1).
  hchanges (rm M2). hchanges (rm M).
  applys weakestpre_conseq_wand.
  applys is_local_Triple.
Qed.

Lemma xapp_lemma : forall A `{EA:Enc A} (Q1:A->hprop) t H1 H Q,
  Triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  H ==> ^(Local (Wp_Triple t)) Q.
Proof using.
  introv M1 M2. applys Local_erase'. applys* xapp_lemma'.
Qed.


(*
hsimpl_wand exploits:

hwand_of_himpl
  H1 ==> H2 ->
  \[] ==> (H1 \-* H2).

qwand_of_qimpl
  Q1 ===> Q2 ->
  \[] ==> Q1 \--* Q2.

hwand_move_l
  H1 \* H2 ==> H3 ->
  H1 ==> (H2 \-* H3).

qwand_move_l
  Q1 \*+ H ===> Q2 ->
  H ==> (Q1 \--* Q2).
*)



Ltac hsimpl_wand :=
  first [ applys qwand_of_qimpl 
        | applys qwand_move_l
        | applys hwand_of_himpl 
        | applys hwand_move_l ].


(* ---------------------------------------------------------------------- *)
(* ** Example proof of the [incr] function *)

Module Test.
Import NotationForVariables NotationForTerms.
Open Scope trm_scope.



(* TODO: get that to work
Notation "'`Let' x ':=' F1 'in' F2" :=
  ((Wp_let F1 (fun _ _  x => F2)))
  (at level 69,  x ident, right associativity,
  format "'[v' '[' '`Let'  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : charac.
*)

Lemma Formula_typed_simpl : forall `{Enc A1} (F:(A1->hprop)->hprop) (Q:A1->hprop) H,
  H ==> F Q ->
  H ==> ^(Formula_typed F) Q.
Proof using.
  introv M. unfold Formula_typed. hsimpl* Q. applys PostChange_refl.
Qed.

Lemma Formula_typed_val : forall `{Enc A1} (F:(A1->hprop)->hprop) (Q:val->hprop) H,
  H ==> F (fun (X:A1) => Q (enc X)) ->
  H ==> ^(Formula_typed F) Q.
Proof using.
  introv M. unfold Formula_typed. hsimpl* Q.
  unfold PostChange. intros X. hsimpl* X.
Qed.

Lemma xval_lemma : forall `{EA:Enc A} (V:A) v H (Q:A->hprop),
  v = ``V ->
  H ==> Q V ->
  H ==> ^(Wp_val v) Q.
Proof using. introv E N. subst. applys Local_erase'. hsimpl~ V. Qed.

Lemma xval_lemma_val : forall `{EA:Enc A} (V:A) v H (Q:val->hprop),
  v = ``V ->
  H ==> Q (``V) ->
  H ==> ^(Wp_val v) Q.
Proof using. introv E N. subst. applys Local_erase'. hsimpl~ (``V). Qed.





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

Definition Stack `{Enc A} (L:list A) (p:loc) : hprop :=
  p ~~> L.


(* todo: why [pat_var "x"] displays with quotes? *)

Lemma triple_pop : forall `{Enc A} (p:loc) (L:list A),
  L <> nil ->
  TRIPLE (val_pop ``p)
    PRE (p ~> Stack L)
    POST (fun (x:A) => \exists L', \[L = x::L'] \* (p ~> Stack L')).
Proof using.
  intros.
  (* xcf details: *)
  simpl combiner_to_trm.
  xcf_prepare_args tt. (* -- not needed here *)
  let f := xcf_get_fun tt in 
  unfold f.
  rew_trms_vals.
  applys Triple_apps_funs_of_Wp.
  { reflexivity. }
  { try xeq_encs. }
  { reflexivity. }
  simpl. rew_enc_dyn. (* xcf_post tt. *)
Admitted.


Lemma triple_empty : forall `{Enc A} (u:unit),
  TRIPLE (val_empty ``u)
    PRE \[]
    POST (fun p => (p ~> Stack (@nil A))).
Proof using.
  intros.
 (* xcf details: *)
  simpl combiner_to_trm.
  xcf_prepare_args tt. (* -- not needed here *)
  let f := xcf_get_fun tt in 
  unfold f.
  rew_trms_vals.
  applys Triple_apps_funs_of_Wp.
  { reflexivity. }
  { try xeq_encs. }
  { reflexivity. }
  simpl. rew_enc_dyn. (* xcf_post tt. *)
  (* xletval *)
  apply Local_erase'.
  (* xval *)
  applys~ (xval_lemma_val (@nil A)).
  (* xapp *)
  applys @xapp_lemma. { eapply @Triple_ref. }
  hsimpl; hsimpl_wand.
  hsimpl.
Qed.

(*
Definition enc_list `{Enc A} := (fix f (l:list A) :=
  match l with
  | nil => val_constr 0%nat nil
  | x::l' => val_constr 1%nat ((``x)::(f l')::nil)
  end).

Instance Enc_list2 : forall `{Enc A}, Enc (list A).
Proof using. constructor. applys enc_list. Defined.

Opaque enc_list.
*)

Lemma triple_push : forall `{Enc A} (p:loc) (x:A) (L:list A),
  TRIPLE (val_push ``p ``x)
    PRE (p ~> Stack L)
    POST (fun (u:unit) => (p ~> Stack (x::L))).
Proof using.
  intros.
  (* xcf details: *)
  simpl combiner_to_trm.
  xcf_prepare_args tt. (* -- not needed here *)
  let f := xcf_get_fun tt in 
  unfold f.
  rew_trms_vals.
  applys Triple_apps_funs_of_Wp.
  { reflexivity. }
  { try xeq_encs. }
  { reflexivity. }
  simpl. rew_enc_dyn. (* xcf_post tt. *)
  (* xunfold *)
  xunfold Stack.
  (* xval *)
  apply Local_erase'.
  (* xlet *)
  notypeclasses refine (xlet_instantiate _ _ _ _ _).
  (* xapps *)
  applys @xapp_lemma. { eapply @Triple_get. }
  hsimpl. hsimpl_wand. hsimpl ;=> ? ->.
  (* xval *)
  applys~ (xval_lemma_val (x::L)).
  (* xapps *)
  applys @xapp_lemma. { eapply @Triple_set. }
  hsimpl. hsimpl_wand. hsimpl ;=> ? ->.
Qed.




(*
Definition val_incr :=
  ValFun 'p :=
    Let 'n := val_get 'p in
    Let 'm := 'n '+ 1 in
    val_set 'p 'm.
*)

Definition val_incr : val :=
  ValFun 'p :=
   'p ':= ((val_get 'p) '+ 1).



Lemma triple_incr : forall (p:loc) (n:int),
  TRIPLE (val_incr ``p)
    PRE (p ~~> n)
    POST (fun (r:unit) => (p ~~> (n+1))).
Proof using.
  intros.
  (* xcf details: *)
  simpl combiner_to_trm.
  xcf_prepare_args tt. (* -- not needed here *)
  let f := xcf_get_fun tt in 
  unfold f.
  rew_trms_vals.
  applys Triple_apps_funs_of_Wp.
  { reflexivity. }
  { try xeq_encs. }
  { reflexivity. }
  simpl. rew_enc_dyn. (* xcf_post tt. *)
  (* fst call *)
  apply Local_erase'.
  apply Local_erase'.
  applys @xapp_lemma. { applys Triple_get. }
  hsimpl.
  hsimpl_wand. (* todo: extend hsimpl to do this step *)
  hpull ;=> ? ->.
  (* return *)
  applys @Formula_typed_val. 
  (* snd call *)
  applys @xapp_lemma. { eapply @Triple_set. }
  hsimpl.
  hsimpl_wand.
  hsimpl.
Qed.

(* SHOULD BE:

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

End Test.


























