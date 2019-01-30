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

Import NotationForVariables NotationForTerms.
Open Scope val_scope.
Open Scope pat_scope.
Open Scope trm_scope.

Implicit Types v w : val.
Implicit Types t : trm.
Implicit Types vs : vals.
Implicit Types ts : trms.
Implicit Types H : hprop.




(* ********************************************************************** *)
(* * Reasoning rules for manipulating goals of the form [H ==> ^(Wp t) Q]. *)

(* ---------------------------------------------------------------------- *)
(* ** Lemmas for [xcf], proving goals of the form [Triples (trm_apps F ts)] *)

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
(* ** Lemmas for [xapp] and [xapps] *)

Lemma xapp_lemma : forall A `{EA:Enc A} (Q1:A->hprop) t H1 H Q,
  Triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  H ==> ^(Wp_app t) Q.
Proof using.
  introv M1 M2. applys Local_erase.
  hchanges (rm M2).
  rewrite <- Triple_eq_himpl_Wp_Triple.
  applys* Triple_ramified_frame. hsimpl.
Qed.

Lemma xapps_lemma : forall A `{EA:Enc A} (V:A) H2 t H1 H Q,
  Triple t H1 (fun r => \[r = V] \* H2) ->
  H ==> H1 \* (H2 \-* Q V) ->
  H ==> ^(Wp_app t) Q.
Proof using.
  introv M1 M2. applys xapp_lemma M1. hchanges M2.
  intros ? ->. hchanges (hwand_cancel H2).
Qed.

Lemma xapps_lemma_pure : forall A `{EA:Enc A} (V:A) t H1 H Q,
  Triple t H1 (fun r => \[r = V]) ->
  H ==> H1 \* (Q V) ->
  H ==> ^(Wp_app t) Q.
Proof using.
  introv M1 M2. applys xapps_lemma \[]; rew_heap; eauto.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Lemmas for [xval] *)

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


(* ---------------------------------------------------------------------- *)
(* ** Lemmas for [xreturn] *)

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


(* ---------------------------------------------------------------------- *)
(* ** Lemmas for [xlet] and [xseq] *)

Lemma xlet_lemma : forall A1 (EA1:Enc A1) H `{EA:Enc A} (Q:A->hprop) (F1:Formula) (F2of:forall `{EA1:Enc A2},A2->Formula),
  H ==> ^F1 (fun (X:A1) => ^(F2of X) Q) -> 
  H ==> ^(Wp_let F1 (@F2of)) Q.
Proof using. introv M. applys Local_erase. hsimpl* A1 EA1. Qed.

Definition xlet_typed_lemma := @Local_erase.

Definition xseq_lemma := @Local_erase.


(* ---------------------------------------------------------------------- *)
(* ** Lemmas for [xcase] *)

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

Lemma xmatch_lemma_list : forall `{EA:Enc A} (L:list A) (F1:Formula) (F2:val->val->Formula) H `{HB:Enc B} (Q:B->hprop),
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


(* ---------------------------------------------------------------------- *)
(* ** Lemmas for [xif] *)

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
(* Notation for triples *)

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



(*

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







*)