(**

This file defines tactics for manipulating characteristic formula
in weakest-precondition form, in lifted Separation Logic,
as defined in [WPLifted.v].

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)



Set Implicit Arguments.
From CFML Require Export WPLifted WPHeader.
Import LibListExec.RewListExec.
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
(* Notation for triples *)

(** Display [H ==> ^F Q] as [PRE H CODE F POST Q] *)

Notation "'PRE' H 'CODE' F 'POST' Q" := (H ==> (Wptag F) _ _ Q)
  (at level 8, H, F, Q at level 0,
   format "'[v' 'PRE'  H  '/' 'CODE'  F '/' 'POST'  Q ']'") : wp_scope.

(** Display [Triple t H Q] as [TRIPLE t PRE H POST Q] *)

Declare Scope triple_scope.
Open Scope triple_scope.

Notation "'TRIPLE' t 'PRE' H 'POST' Q" :=
  (Triple t H Q)
  (at level 39, t at level 0,
  format "'[v' 'TRIPLE'  t  '/' 'PRE'  H  '/' 'POST'  Q ']'") : triple_scope.


(* ********************************************************************** *)
(* * Tactics for decoding. *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xdecode] and [xdecodes] *)

(* TODO: check if still the case in 8.12 *)
(* --LATER: WORK AROUND TYPECLASS RESOLUTION BUG *)
Hint Extern 1 (Decode (val_constr "nil" nil) _) =>
  match goal with H: Enc ?A |- _ => eapply (@Decode_nil A) end : Decode.
Hint Extern 1 (Decode (val_constr "cons" (_::_::nil)) _) =>
  match goal with H: Enc ?A |- _ => eapply (@Decode_cons A) end : Decode.

Hint Resolve Decode_None Decode_Some : Decode.
(* --LATER: similar hints needed? *)

Ltac xdecode_core tt :=
  try solve [ typeclasses eauto with Decode ].

Tactic Notation "xdecode" :=
  xdecode_core tt.

Ltac xenc_side_conditions tt :=
  try match goal with
  | |- Enc _ => typeclasses eauto with typeclass_instances
  | |- Decode _ _ => xdecode
  | |- Enc_injective _ => eauto with Enc_injective
  | |- Enc_comparable _ _ => unfold Enc_comparable; eauto with Enc_injective
  end.

(** [xdecodes] applys to a call of the form [Decodes vs ?Vs].
    It refines [Vs] as a list (of type [dyns]) of the same length as [vs],
    and calls [xdecode] on every pair of items at corresponding indices. *)

Ltac xdecodes_splits tt :=
  match goal with
  | |- Decodes nil _ => apply Decodes_nil
  | |- Decodes (_::_) _ => nrapply Decodes_cons; [ | xdecodes_splits tt ]
  end.

Ltac xdecodes_core tt :=
  xdecodes_splits tt; xdecode.

Tactic Notation "xdecodes" :=
  xdecodes_core tt.

Tactic Notation "xdecodes_debug" :=
  xdecodes_splits tt; try xdecode.


(* ********************************************************************** *)
(* * Tactics for manipulating goals of the form [PRE H CODE F POST Q]. *)


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xgoal_code] and [xgoal_fun] *)

Ltac xgoal_code tt :=
  match goal with |- PRE _ CODE ?C POST _ => constr:(C) end.

Ltac xgoal_code_strip_wptag C :=
  match C with
  | Wptag ?C' => xgoal_code_strip_wptag C'
  | ?C' => constr:(C')
  end.

Ltac xgoal_code_without_wptag tt :=
  let C := xgoal_code tt in
  xgoal_code_strip_wptag C.

Ltac xgoal_fun tt :=
  match xgoal_code_without_wptag tt with
  | Wpgen_app (trm_apps (trm_val ?f) _) => constr:(f)
  | Wpgen_App_typed ?T ?f ?Vs => constr:(f)
  end.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xspec] *)

(* ** Database of specifications used by [xapp], through tactic [xspec] *)

(** A name for the database *)

Declare Scope wptactics_scope.
Open Scope wptactics_scope.

Notation "'Register_goal' G" := (Register database_spec G)
  (at level 69) : wptactics_scope.

(** [xspec G] retreives from the database [database_spec]
    the specification that could apply to a goal [G].
    It places the specification as hypothesis at the head of the goal. *)

Ltac xspec_remove_combiner tt :=
  cbn beta delta [ combiner_to_trm ] iota zeta in *.

Ltac xspec_context tt :=
  xspec_remove_combiner tt;
  match goal with
  | H: context [ Triple (trm_apps (trm_val ?f) _) _ _ ]
    |- Triple (trm_apps (trm_val ?f) _) _ _ => generalize H
  | H: context [ Triple (Trm_apps (trm_val ?f) _) _ _ ]
    |- Triple (Trm_apps (trm_val ?f) _) _ _ => generalize H
  end.

Ltac xspec_registered tt :=
  match goal with |- ?G => ltac_database_get database_spec G end.

Ltac xspec_core tt :=
  first [ xspec_registered tt
        | xspec_context tt ].

Tactic Notation "xspec" :=
  xspec_core tt.

(* DEPRECATED
Ltac xspec_prove_cont tt :=
  let H := fresh "Spec" in
  intro H; eapply H; clear H.
*)

Ltac xspec_prove_cont tt :=
  let H := fresh "Spec" in
  intro H; nrapply H;
  xenc_side_conditions tt;
  try clear H.

Ltac xspec_prove_triple tt :=
  xspec; xspec_prove_cont tt.

Ltac xspec_lemma_of_args E :=
  let H := fresh "Spec2" in
  match list_boxer_of E with
  | cons (boxer ltac_wild) ?E' => (* only args provided *)
     let K := fresh "BaseSpec" in (* --TODO: need to clear K at some point... *)
     xspec; intro K;
     lets H: ((boxer K)::E');
     revert H;
     try clear K
  | _ => (* spec and args provided *)
     lets H: E; revert H
  end.

Ltac xspec_prove_triple_with_args E :=
  xspec_lemma_of_args E; xspec_prove_cont tt.

Notation "'Register_Spec' f" := (Register_goal (Triple (trm_apps (trm_val f) _) _ _))
  (at level 69) : wptactics_scope.

(* ** Specification of primitives *)

Hint Extern 1 (Register_Spec (val_prim val_set)) => Provide @Triple_set_Decode.
Hint Extern 1 (Register_Spec (val_prim val_ref)) => Provide @Triple_ref_Decode.
Hint Extern 1 (Register_Spec (val_prim val_get)) => Provide @Triple_get.
Hint Extern 1 (Register_Spec (val_prim val_free)) => Provide @Triple_free.
Hint Extern 1 (Register_Spec (val_prim val_alloc)) => Provide Triple_alloc.

Hint Extern 1 (Register_Spec (val_prim val_eq)) => Provide @Triple_eq_Decode.
Hint Extern 1 (Register_Spec (val_prim val_neq)) => Provide @Triple_neq_Decode.
Hint Extern 1 (Register_Spec (val_prim val_neg)) => Provide Triple_neg.
Hint Extern 1 (Register_Spec (val_prim val_lt)) => Provide Triple_lt.
Hint Extern 1 (Register_Spec (val_prim val_le)) => Provide Triple_le.
Hint Extern 1 (Register_Spec (val_prim val_gt)) => Provide Triple_gt.
Hint Extern 1 (Register_Spec (val_prim val_ge)) => Provide Triple_ge.
Hint Extern 1 (Register_Spec (val_prim val_add)) => Provide Triple_add.
Hint Extern 1 (Register_Spec (val_prim val_sub)) => Provide Triple_sub.
Hint Extern 1 (Register_Spec (val_prim val_ptr_add)) => Provide Triple_ptr_add.
Hint Extern 1 (Register_Spec (val_prim val_mul)) => Provide Triple_mul.
Hint Extern 1 (Register_Spec (val_prim val_div)) => Provide Triple_div.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xwp_simpl] for computing characteristic formulae *)

Arguments var_eq s1 s2 /.
Arguments eq_var_dec s1 s2 /.
Arguments string_dec s1 s2 /.
Arguments string_rec P /.
Arguments string_rect P /.
Arguments sumbool_rec A B P /.
Arguments sumbool_rect A B P /.
Arguments Ascii.ascii_dec a b /.
Arguments Ascii.ascii_rec P /.
Arguments Ascii.ascii_rect P /.
Arguments Bool.bool_dec b1 b2 /.
Arguments bool_rec P /.
Arguments bool_rect P /.

Ltac xwp_simpl :=
  cbn beta delta [
  LibListExec.app LibListExec.combine LibListExec.rev LibListExec.fold_right LibListExec.map
  Datatypes.app List.combine List.rev List.fold_right List.map
  Wpgen Wpaux_getval Wpaux_getval_typed
  Wpaux_apps Wpaux_constr Wpaux_var Wpaux_match
  hforall_vars forall_vars
  trm_case trm_to_pat patvars patsubst combiner_to_trm
  Ctx.app Ctx.empty Ctx.lookup Ctx.add Ctx.rev
  Ctx.rem Ctx.rem_var Ctx.rem_vars Ctx.combine isubst
  var_eq eq_var_dec
  string_dec string_rec string_rect
  sumbool_rec sumbool_rect
  Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
  Bool.bool_dec bool_rec bool_rect ] iota zeta.



(************************************************************)
(** [xtypes] auxiliary functions for reporting type information *)

(* TODO LATER

    - [xtypes_goal tt] shows the type of the application in the
      goal, compared with the one from the specification.

    - [xtypes_hyp S] shows the types of the function involved
      in a specification [S].
*)

Ltac xtypes_type show_arrow T ET :=
  match show_arrow with
  | true => idtac T " { " ET " } -> "
  | false => idtac T " { " ET " } "
  end.

(* [xtypes_dyn_list L] displays the types of the
   arguments in the list [L] *)

Ltac xtypes_dyn_list L :=
  match L with
  | nil => idtac
  | (@dyn_make ?T ?ET ?x) :: ?R => xtypes_type true T ET
  end.

Ltac xtypes_triple E :=
  let aux Vs T ET :=
    xtypes_dyn_list Vs; xtypes_type false T ET in
  match E with
  | (Wptag ?F) => xtypes_triple F
  | (@Wpgen_App_typed ?T ?ET ?f ?Vs) => aux Vs T ET
  | (@Triple (Trm_apps ?f ?Vs) ?T ?ET ?H ?Q) => aux Vs T ET
  end.

Ltac xtypes_goal tt :=
  idtac "=== type of application in goal ===";
  let G := match goal with |- ?G => constr:(G) end in (* TODO: ltac op *)
  xtypes_triple G.

Ltac xtypes_hyp S :=
  idtac "=== type of application in hypothesis ===";
  forwards_nounfold_admit_sides_then S ltac:(fun K =>
    let T := type of K in
    xtypes_triple T).


(************************************************************)
(** ** Tactic [xcf] for invoking a precomputed characteristic formula *)

(** [xcf] applies to a goal with a conclusion of the form
    [Triple t H Q], possibly written using the [SPEC] notation.
    It looks up the characteristic formula associated with [f]
    in the database "database_cf", and exploits it to start
    proving the goal. [xcf] first calls [intros] if needed.

    When [xcf] fails to apply, it is (most usually) because the number
    of arguments, or the types of the arguments, or the return type,
    does not match.

    Variants:

    - [xcf_show] will only display the CF lemma found in the database,
      putting it at the head of the goal.

    - [xcf_show f] displays the CF associated with a given value [f].

    - [xcf_types] compares the types involved in the application from the CF
       with the corresponding types in the goal.
      [xcf_types Spec] to show types of a given spec
*)

 (* TODO: extend to support partial application *)

Ltac xcf_pre tt :=
  intros.

Ltac xcf_target tt :=
  match goal with
  | |- ?f = _ => constr:(f)
  | |- Triple (Trm_apps (trm_val ?f) ?Vs) ?H ?Q => constr:(f)
  end.

Ltac xcf_find f :=
  ltac_database_get database_cf f.

Tactic Notation "xcf_show" constr(f) :=
  xcf_find f.

Tactic Notation "xcf_show" :=
  xcf_pre tt;
  let f := xcf_target tt in
  xcf_find f.

Ltac xcf_top_fun tt :=
  let f := xcf_target tt in
  xcf_find f;
  let Sf := fresh "Spec" in
  intros Sf;
  eapply Sf;
  clear Sf.
  (* xcf_post *) (* try solve_type;  instantiate; *)
  (* TODO: first [ xc f_top_value f | xcf_fallback f | fail 2 ] *)

Ltac xcf_top_value tt :=
  let f := xcf_target tt in
  xcf_find f;
  let Sf := fresh "Spec" in
  intros Sf;
  rewrite Sf;
  clear Sf.
  (* xcf_post *)

Ltac xcf_core tt :=
  xcf_pre tt;
  match goal with
  | |- ?f = _ => xcf_top_value tt
  | _ => xcf_top_fun tt
  end.

(* TODO notation SPECVAL f = v and SPECVAL f st P *)

Tactic Notation "xcf" :=
  xcf_core tt.
Tactic Notation "xcf" "~" :=
  xcf; auto_tilde.
Tactic Notation "xcf" "*" :=
  xcf; auto_star.

(* DEPRECATED
Ltac xcf_post tt :=
  cbv beta;
  remove_head_unit tt.
  (* DEPRECATED
  cbv beta;
  remove_head_unit tt. TODO: should be hnf?
  *)
*)

Ltac xcf_types_core tt :=
  let S := fresh "Spec" in
  intros S;
  xtypes_goal tt;
  xtypes_hyp S;
  clear S.

Ltac xcf_types_core_noarg tt :=
  xcf_show;
  xcf_types_core tt.

Ltac xcf_types_core_arg S :=
  xcf_pre tt;
  generalize S;
  xcf_types_core tt.

Tactic Notation "xcf_types" :=
  xcf_types_core_noarg tt.

Tactic Notation "xcf_types" constr(S) :=
  xcf_types_core_arg S.

(* LATER
Ltac xcf_fallback f :=
  idtac "Warning: could not exploit the specification; maybe the types don't match; check them using [xcf_types]; if you intend to use the specification manually, use [xcf_show].";
  xcf_find f;
  let Sf := fresh "Spec" in
  intros Sf.
*)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xstructural] -- for internal use *)

Ltac xstructural_core tt :=
  applys Structural_Mkstruct.

Tactic Notation "xstructural" :=
  xstructural_core tt.

(* TODO: include assumption, for use in the case of loops *)


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xcleanup] -- for internal use *)

Ltac xcleanup_core tt :=
  rew_bool_eq.

Tactic Notation "xcleanup" :=
  xcleanup_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xwp_xtriple_handle_gc] -- for internal use *)

(* [xwp_xtriple_handle_gc] is used by [xwp] and [wtriple].
   It enables removing [\GC] to simulate a linear logic. *)

Lemma xwp_xtriple_handle_gc_lemma : forall F A `{EA:Enc A} H (Q:A->hprop),
  Structural F ->
  H ==> ^F Q ->
  H ==> ^F (Q \*+ \GC).
Proof using.
  introv HF M. applys* structural_conseq. xsimpl.
Qed.

Ltac xwp_xtriple_remove_gc tt :=
  applys xwp_xtriple_handle_gc_lemma; [ try xstructural | ].

(* By default, [\GC] is preserved. To remove [\GC], set up the re-binding:
   [Ltac xwp_xtriple_handle_gc ::= xwp_xtriple_remove_gc.] *)

Ltac xwp_xtriple_handle_gc tt :=
  idtac.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xwp] *)

Lemma xwp_lemma_funs : forall F vs ts xs t `{EA:Enc A} H (Q:A->hprop),
  F = val_funs xs t ->
  trms_to_vals ts = Some vs ->
  var_funs_exec xs (length vs) ->
  H ==> ^(Wpgen (LibListExec.combine xs vs) t) (Q \*+ \GC) ->
  Triple (trm_apps F ts) H Q.
Proof using.
  introv HF Hvs Hxs M. applys Triple_hgc_post. lets ->: trms_to_vals_spec Hvs.
  rewrite var_funs_exec_eq in Hxs. rew_istrue in Hxs. lets (_&Lxs&_): Hxs.
  rew_list_exec in M; auto. applys* Triple_apps_funs. rewrite~ <- isubstn_eq_substn.
  applys* Triple_isubst_of_Wpgen.
Qed.

Lemma xwp_lemma_fixs : forall F (f:var) vs ts xs t `{EA:Enc A} H (Q:A->hprop),
  F = val_fixs f xs t ->
  trms_to_vals ts = Some vs ->
  var_fixs_exec f xs (length vs) ->
  H ==> ^(Wpgen (LibListExec.combine (f::xs) (F::vs)) t) (Q \*+ \GC) ->
  Triple (trm_apps F ts) H Q.
Proof using.
  introv HF Hvs Hxs M. applys Triple_hgc_post. lets ->: trms_to_vals_spec Hvs.
  rewrite var_fixs_exec_eq in Hxs. rew_istrue in Hxs. lets (_&Lxs&_): Hxs.
  rew_list_exec in M; [| rew_list; auto ].
  applys* Triple_apps_fixs. rewrite <- isubstn_eq_substn; [|rew_list~].
  applys* Triple_isubst_of_Wpgen.
Qed.

Ltac xwp_fun tt :=
  applys xwp_lemma_funs; [ reflexivity | reflexivity | reflexivity
                         | xwp_simpl; xwp_xtriple_handle_gc tt ].

Ltac xwp_fix tt :=
  applys xwp_lemma_fixs; [ reflexivity | reflexivity | reflexivity
                         | xwp_simpl; xwp_xtriple_handle_gc tt ].

Ltac xwp_trm tt :=
  fail "not yet implemented".

Ltac xwp_core tt :=
  intros; first [ xwp_fun tt | xwp_fix tt | xwp_trm tt ].

Tactic Notation "xwp" :=
  xwp_core tt.

(** [xwp_debug] *)

Ltac xwp_debug_core tt :=
  first [ applys xwp_lemma_funs
        | applys xwp_lemma_fixs
        | fail 1 "Goal does not appear to be of the form [Triple (trm_apps F ts) H Q]" ];
  [ first [ reflexivity | fail 1 "The function applied in the triple cannot be unified with [val_funs xs t]" ]
  | first [ reflexivity | fail 1 "One of the arguments in the triple is not must of the form [trm_val v] for some [v]" ]
  | first [ reflexivity | fail 1 "The number of arguments that appear in the triple does not match the exected number of arguments of the function" ]
  | try xwp_simpl ].

Tactic Notation "xwp_debug" :=
  xwp_debug_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xtriple] *)

(* TODO: integrate into [xwp] *)

Lemma xtriple_lemma : forall t f (vs:vals) `{EA:Enc A} H (Q:A->hprop),
  t = trm_apps f (trms_vals vs) ->
  H ==> ^(Wptag (Wpgen_app (trm_apps f (trms_vals vs)))) (Q \*+ \GC) ->
  Triple t H Q.
Proof using.
  introv E M. subst t. applys Triple_hgc_post.
  applys* Triple_of_Wp. unfolds Wpgen_app.
  rewrite <- eq_Mkstruct_of_Structural in M. applys M.
  applys Structural_Wp.
Qed.

Ltac xtriple_pre tt :=
  intros.

Ltac xtriple_core tt :=
  xtriple_pre tt;
  applys xtriple_lemma;
  [ simpl combiner_to_trm; rew_trms_vals; reflexivity
  | xwp_xtriple_handle_gc tt ].

Tactic Notation "xtriple" :=
  xtriple_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xgc] *)

Lemma xgc_post_lemma : forall (H:hprop) (F:Formula) `{Enc A} (Q:A->hprop),
  Structural F ->
  H ==> ^F (Q \*+ \GC) ->
  H ==> ^F Q.
Proof using. introv HF M. applys* structural_hgc. Qed.

Ltac xgc_post_core tt :=
  applys xgc_post_lemma; [ try xstructural | ].

Tactic Notation "xgc_post" :=
  xgc_post_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xseq] *)

Ltac xseq_pre tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_seq _ _) => idtac
  end.

Definition xseq_lemma := @MkStruct_erase.

Ltac xseq_core tt :=
  xseq_pre tt;
  applys xseq_lemma.

Tactic Notation "xseq" :=
  xseq_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xlet] *)

Lemma xlet_lemma : forall A1 (EA1:Enc A1) H `{EA:Enc A} (Q:A->hprop) (F1:Formula) (F2of:forall A2 (EA2:Enc A2),A2->Formula),
  H ==> ^F1 (fun (X:A1) => ^(F2of _ _ X) Q) ->
  H ==> ^(Wpgen_let F1 (@F2of)) Q.
Proof using. introv M. applys MkStruct_erase. xsimpl* A1 EA1. Qed.

Definition xlet_typed_lemma := @MkStruct_erase.

Ltac xlet_poly tt :=
  notypeclasses refine (xlet_lemma _ _ _ _ _).

Ltac xlet_typed tt :=
  applys xlet_typed_lemma.

Ltac xlet_core tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_typed _ _) => xlet_typed tt
  | (Wpgen_let _ _) => xlet_poly tt
  end.

Tactic Notation "xlet" :=
  xlet_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xcast] *)

Ltac xcast_pre tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_Val_no_mkstruct _) => idtac
  end.

Lemma xcast_lemma : forall (H:hprop) `{Enc A} (Q:A->hprop) (X:A),
  H ==> Q X ->
  H ==> ^(Wpgen_Val_no_mkstruct X) Q.
Proof using. introv M. unfolds Wpgen_Val_no_mkstruct. xchange M. applys qimpl_Post_cast_r. Qed.

Ltac xcast_debug tt :=
  idtac "[xcast] fails to simplify due to type mismatch";
  match goal with |-
   ?H ==> (Wptag (@Wpgen_Val_no_mkstruct ?A1 ?EA1 ?X)) ?A2 ?EA2 ?Q =>
   xtypes_type false A1 EA1;
   xtypes_type false A2 EA2
 end.

Ltac xcast_core tt :=
  first [ xcast_pre tt; applys xcast_lemma
        | xcast_debug tt ].

Tactic Notation "xcast" :=
  xcast_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xpost] *)

Lemma xpost_lemma : forall A `{EA:Enc A} (Q1 Q2:A->hprop) H (F:Formula),
  Structural F ->
  H ==> ^F Q1 ->
  Q1 ===> Q2 ->
  H ==> ^F Q2.
Proof using. introv M W. applys* structural_conseq. Qed.

Arguments xpost_lemma : clear implicits.

Ltac xpost_core Q :=
  applys (@xpost_lemma _ _ Q); [ xstructural | | ].

Tactic Notation "xpost" constr(Q) :=
  xpost_core Q.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xlet_xseq_xcast_repeat] *)

Ltac xlet_xseq_xcast tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_typed _ _) => xlet
  | (Wpgen_let _ _) => xlet
  | (Wpgen_seq _ _) => xseq
  | (Wpgen_Val_no_mkstruct _) => xseq
  end.

Ltac xlet_xseq_xcast_repeat tt :=
  repeat (xlet_xseq_xcast tt).


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xreturn] *)

Lemma xreturn_lemma_typed : forall A1 `{Enc A1} (F:(A1->hprop)->hprop) (Q:A1->hprop) H,
  H ==> F Q ->
  H ==> ^(Formula_cast F) Q.
Proof using.
  introv M. unfold Formula_cast. xsimpl* Q. applys qimpl_Post_cast_r.
Qed.

Lemma xreturn_lemma_val : forall A1 `{Enc A1} (F:(A1->hprop)->hprop) (Q:val->hprop) H,
  H ==> F (fun (X:A1) => Q (enc X)) ->
  H ==> ^(Formula_cast F) Q.
Proof using.
  introv M. unfold Formula_cast. xsimpl* (fun X : A1 => Q ``X).
  unfold Post_cast. intros X. unfold Post_cast_val. xsimpl* X.
Qed.

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xapp] *)

(** [xapp]
    [xapp E]

    [xappn]
    [xappn n]

    [xapp_nosubst]
    [xapp_nosubst E]

    [xapp_debug]
    [xapp_debug E]
*)

(* DEBUG XAPP

  xapp_pre tt;
  applys xapp_find_spec_lemma;
    [ xspec;
      let H := fresh "Spec" in
      intro H; eapply H; clear H
    | xapp_select_lemma tt;
      xapp_post tt ].

  xapp_pre tt.
  applys xapp_find_spec_lemma.
  xspec_prove_triple tt .
  xapp_select_lemma tt. xsimpl. xapp_post tt.

  xapp_pre tt.
  applys xapp_find_spec_lifted_lemma.
  xspec_prove_triple tt .
  xapp_select_lifted_lemma tt. xsimpl. xapp_post tt.

*)


Ltac xapp_record tt :=
  fail "implemented later in WPStruct".

Lemma xapp_lemma : forall A `{EA:Enc A} (Q1:A->hprop) t H1 H Q,
  Triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  H ==> ^(Wpgen_app t) Q.
Proof using.
  introv M1 M2. applys MkStruct_erase.
  xchanges (rm M2).
  rewrite <- Triple_eq_himpl_Wp.
  applys* Triple_ramified_frame.
Qed.

Lemma xapps_lemma : forall A `{EA:Enc A} (V:A) H2 t H1 H Q,
  Triple t H1 (fun r => \[r = V] \* H2) ->
  H ==> H1 \* (H2 \-* protect (Q V)) ->
  H ==> ^(Wpgen_app t) Q.
Proof using.
  introv M1 M2. applys xapp_lemma M1. xchanges M2.
  intros ? ->. auto.
Qed.

Lemma xapps_lemma_pure : forall A `{EA:Enc A} (V:A) t H1 H Q,
  Triple t H1 (fun r => \[r = V]) ->
  H ==> H1 \* protect (Q V) ->
  H ==> ^(Wpgen_app t) Q.
Proof using.
  introv M1 M2. applys xapps_lemma \[]; rew_heap; eauto.
Qed.

(* lifted versions *)

Lemma xapp_lifted_lemma : forall A `{EA:Enc A} (Q1:A->hprop) (f:trm) (Vs:dyns) H1 H Q,
  Triple (Trm_apps f Vs) H1 Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  H ==> ^(Wpgen_App_typed A f Vs) Q.
Proof using.
  introv M1 M2. applys MkStruct_erase. xchanges (rm M2).
  applys xreturn_lemma_typed. rewrite <- Triple_eq_himpl_Wp.
  applys* Triple_ramified_frame.
Qed.

Lemma xapps_lifted_lemma : forall A `{EA:Enc A} (V:A) H2 (f:trm) (Vs:dyns) H1 H Q,
  Triple (Trm_apps f Vs) H1 (fun r => \[r = V] \* H2) ->
  H ==> H1 \* (H2 \-* protect (Q V)) ->
  H ==> ^(Wpgen_App_typed A f Vs) Q.
Proof using.
  introv M1 M2. applys xapp_lifted_lemma M1. xchanges M2.
  intros ? ->. auto.
Qed.

Lemma xapps_lifted_lemma_pure : forall A `{EA:Enc A} (V:A) (f:trm) (Vs:dyns) H1 H Q,
  Triple (Trm_apps f Vs) H1 (fun r => \[r = V]) ->
  H ==> H1 \* protect (Q V) ->
  H ==> ^(Wpgen_App_typed A f Vs) Q.
Proof using.
  introv M1 M2. applys xapps_lifted_lemma \[]; rew_heap; eauto.
Qed.

Lemma xapp_find_spec_lifted_lemma : forall A `{EA:Enc A} (Q1:A->hprop) (f:trm) (Vs:dyns) H1 H (Q:A->hprop),
  Triple (Trm_apps f Vs) H1 Q1 ->
  (Triple (Trm_apps f Vs) H1 Q1 ->
   H ==> ^(Wpgen_App_typed A f Vs) Q) ->
  H ==> ^(Wpgen_App_typed A f Vs) Q.
Proof using. auto. Qed.

(* [xapp_pre tt] automatically performs the necessary
   [xlet], [xseq] and [xcast], then checks that the goal
   is a [Wpgen_app] goal.

   Besides, if the goal is a triple, then it converts it
   to [wp]-style using [xtriple]. This is useful when proving
   a specification by weakening an existing one. *)

(* overloaded in WPRecord : TODO: cleanup *)

Ltac xapp_pre_wp tt :=
  xlet_xseq_xcast_repeat tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_app ?t) => idtac
  | (Wpgen_App_typed ?T ?f ?Vs) => idtac
  (* | (Wpgen_record_new ?Lof) => idtac --- added in WPRecord *)
  end.

Ltac xapp_pre_triple tt :=
  match goal with
  | |- (Triple _ _ _) => xtriple
  end.

Ltac xapp_pre tt :=
  first [ xapp_pre_wp tt | xapp_pre_triple tt ].


(** [xapp_post] presents a nice error message in case of failure *)

Definition xapp_hidden (P:Type) (e:P) := e.

Notation "'__XAPP_FAILED_TO_MATCH_PRECONDITION__'" :=
  (@xapp_hidden _ _).

Ltac xapp_report_error tt :=
  match goal with |- context [?Q1 \--* protect ?Q2] =>
    change (Q1 \--* protect Q2) with (@xapp_hidden _ (Q1 \--* protect Q2)) end.

Ltac xapp_post tt :=
  xsimpl;
  first [ xapp_report_error tt
        | unfold protect; xcleanup ].

Ltac xapp_post_basic tt := (* version without error message *)
  xsimpl; unfold protect; xcleanup.


Lemma xapp_find_spec_lemma : forall A `{EA:Enc A} (Q1:A->hprop) t H1 H (Q:A->hprop),
  Triple t H1 Q1 ->
  (Triple t H1 Q1 ->
   H ==> ^(Wpgen_app t) Q) ->
  H ==> ^(Wpgen_app t) Q.
Proof using. auto. Qed.

Ltac xapp_select_lemma tt :=
  let S := fresh "Spec" in
  intro S;
  match type of S with
  | Triple _ _ (fun _ => \[_ = _] \* _) => applys @xapps_lemma
  | Triple _ _ (fun _ => \[_ = _]) => applys @xapps_lemma_pure
  | _ => applys @xapp_lemma
  end; [ applys S | clear S ].

Ltac xapp_apply_lemma cont_prove_triple :=
  (* --TODO should remove *) xapp_pre tt;
  applys xapp_find_spec_lemma;
    [ cont_prove_triple tt
    | xapp_select_lemma tt; xapp_post tt ].

(* lifted versions *)

Ltac xapp_select_lifted_lemma tt := (* TODO: factorize better with xapp_select_lemma *)
  let S := fresh "Spec" in
  intro S;
  match type of S with
  | Triple _ _ (fun _ => \[_ = _] \* _) => applys @xapps_lifted_lemma
  | Triple _ _ (fun _ => \[_ = _]) => applys @xapps_lifted_lemma_pure
  | _ => applys @xapp_lifted_lemma
  end; [ applys S | clear S ].

Ltac xapp_apply_lifted_lemma cont_prove_triple :=
  (* --TODO should remove *) xapp_pre tt;
  applys xapp_find_spec_lifted_lemma;
    [ cont_prove_triple tt
    | xapp_select_lifted_lemma tt; xapp_post tt ].

(* DEPRECATED (too slow)
Ltac xapp_apply_lemma cont_prove_triple :=
  first
    [ applys @xapps_lemma; [ cont_prove_triple tt | xapp_post tt ]
    | applys @xapps_lemma_pure; [ cont_prove_triple tt | xapp_post tt ]
    | applys @xapp_lemma; [ cont_prove_triple tt | xapp_post tt ] ].
*)

Ltac xapp_general tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_app ?t) => xapp_apply_lemma ltac:(xspec_prove_triple)
  | (Wpgen_App_typed ?T ?f ?Vs) => xapp_apply_lifted_lemma ltac:(xspec_prove_triple)
  end.

Ltac xapp_core tt :=
  xapp_pre tt;
  first [ xapp_record tt (* TODO: choose base on goal ? *)
        | xapp_general tt ].

Tactic Notation "xapp" :=
  xapp_core tt.
Tactic Notation "xapp" "~" :=
  xapp; auto_tilde.
Tactic Notation "xapp" "*"  :=
  xapp; auto_star.

Ltac xapp_arg_core E :=
  xapp_pre tt;
  let cont := ltac:(fun tt => xspec_prove_triple_with_args E) in
  match xgoal_code_without_wptag tt with
  | (Wpgen_app ?t) =>  xapp_apply_lemma cont
  | (Wpgen_App_typed ?T ?f ?Vs) => xapp_apply_lifted_lemma cont
  end.

Tactic Notation "xapp" constr(E) :=
  xapp_arg_core E.
Tactic Notation "xapp" "~" constr(E) :=
  xapp E; auto_tilde.
Tactic Notation "xapp" "*" constr(E) :=
  xapp E; auto_star.

Ltac xapp_nosubst_core tt :=
  xapp_pre tt;
  let L := match xgoal_code_without_wptag tt with
    | (Wpgen_app ?t) => constr:(@xapp_lemma)
    | (Wpgen_App_typed ?T ?f ?Vs) => constr:(@xapp_lifted_lemma)
    end in
  applys L; [ xspec_prove_triple tt | xapp_post tt ].

Tactic Notation "xapp_nosubst" :=
  xapp_nosubst_core tt.
Tactic Notation "xapp_nosubst" "~" :=
  xapp_nosubst; auto_tilde.
Tactic Notation "xapp_nosubst" "*"  :=
  xapp_nosubst; auto_star.

Ltac xapp_arg_nosubst_core E :=
  xapp_pre tt;
  (* TODO : factorize pattern *)
  let L := match xgoal_code_without_wptag tt with
    | (Wpgen_app ?t) => constr:(@xapp_lemma)
    | (Wpgen_App_typed ?T ?f ?Vs) => constr:(@xapp_lifted_lemma)
    end in
  applys L; [ xspec_prove_triple_with_args E | xapp_post tt ].

Tactic Notation "xapp_nosubst" constr(E) :=
  xapp_arg_nosubst_core tt.
Tactic Notation "xapp_nosubst" "~" constr(E) :=
  xapp_nosubst E; auto_tilde.
Tactic Notation "xapp_nosubst" "*" constr(E)  :=
  xapp_nosubst E; auto_star.

Tactic Notation "xappn" :=
  repeat (xapp).
Tactic Notation "xappn" "~" :=
  repeat (xapp; auto_tilde).
Tactic Notation "xappn" "*" :=
  repeat (xapp; auto_star).

Tactic Notation "xappn" constr(n) :=
  do n (try (xapp)).
Tactic Notation "xappn" "~" constr(n) :=
  do n (try (xapp; auto_tilde)).
Tactic Notation "xappn" "*" constr(n) :=
  do n (try (xapp; auto_star)).



(* ---------------------------------------------------------------------- *)
(* ** [xapp_debug] *)

Ltac xapp_types_for_val v :=
  match v with
  | val_unit => idtac "unit"
  | val_bool _ => idtac "bool"
  | val_int _ => idtac "int"
  | val_loc _ => idtac "loc"
  | @enc ?T _ _ => idtac T
  | _ => idtac "val"
  end.

Ltac xapp_types_for_vals vs :=
  match vs with
  | nil => idtac
  | ?v :: ?vs' => xapp_types_for_val v; idtac "->"; xapp_types_for_vals vs'
  end.

Ltac xapp_types_for_trms ts :=
  match ts with
  | nil => idtac
  | trms_vals ?vs => xapp_types_for_vals vs
  | ?t :: ?ts' =>
      match t with
      | trm_val ?v => xapp_types_for_val v
      | _ => idtac "trm"
      end;
      idtac "->";
      xapp_types_for_trms ts'
  end.

Ltac xapp_types_in_triple ETriple :=
  match ETriple with @Triple (trm_apps ?f ?ts) ?Tr ?ETr ?H ?Q =>
    xapp_types_for_trms ts;
    idtac Tr
  end.

Ltac xapp_debug_report_instantiated K :=
  let EtripleS := type of K in
  idtac "=== Type of the specification for that function:";
  xapp_types_in_triple EtripleS;
  idtac "";
  idtac "=== Type of the function call in the code:";
  match goal with |- ?EtripleF => xapp_types_in_triple EtripleF end.

Ltac xapp_debug_report H :=
  forwards_then H ltac:(fun K =>
    let X := fresh "SpecInstantiated" in
    generalize K; intros X;
    xapp_debug_report_instantiated X ).

Ltac xspec_with_optional_arg E_or_double_underscore :=
  match E_or_double_underscore with
  | __ => first [ xspec | fail 2 ]
  | ?E => xspec_lemma_of_args E
  end.

Ltac xapp_debug_core E_or_double_underscore :=
  xapp_pre tt; applys @xapp_lemma;
  [ first [ xspec_with_optional_arg E_or_double_underscore;
            let H := fresh "Spec" in intro H; simpl in H; xapp_debug_report H
          | fail 1 "No specification registered for that function" ]
  | ].

Tactic Notation "xapp_debug" constr(E) :=
  xapp_debug_core E.

Tactic Notation "xapp_debug" :=
  xapp_debug_core __.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xval] *)

Lemma xval_lemma_decode : forall A `{EA:Enc A} (V:A) v H (Q:A->hprop),
  Decode v V ->
  H ==> Q V ->
  H ==> ^(Wpgen_val v) Q.
Proof using. introv E N. subst. applys MkStruct_erase. unfold Post_cast_val. xsimpl~ V. Qed.

Lemma xval_lemma : forall A `{EA:Enc A} (V:A) v H (Q:A->hprop),
  v = ``V ->
  H ==> Q V ->
  H ==> ^(Wpgen_val v) Q.
Proof using. introv E N. subst. applys MkStruct_erase. unfold Post_cast_val. xsimpl~ V. Qed.

(* NEEDED? *)
Lemma xval_lemma_val : forall A `{EA:Enc A} (V:A) v H (Q:val->hprop),
  v = ``V ->
  H ==> Q (``V) ->
  H ==> ^(Wpgen_val v) Q.
Proof using. introv E N. subst. applys MkStruct_erase. unfold Post_cast_val. xsimpl~ (``V). Qed.

Lemma xval_lifted_lemma : forall A `{EA:Enc A} (V:A) H (Q:A->hprop),
  H ==> Q V ->
  H ==> ^(Wpgen_Val V) Q.
Proof using.
  introv M. subst. applys MkStruct_erase.
  applys xcast_lemma M.
Qed.

(* [xval_pre tt] automatically performs the necessary
   [xlet], [xseq] and [xcast], then checks that the goal
   is a [Wpgen_val] goal. *)

Ltac xval_pre tt :=
  xlet_xseq_xcast_repeat tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_val _) => idtac
  | (Wpgen_Val _) => idtac
  end.

Ltac xval_arg E :=
  xval_pre tt;
  applys (@xval_lemma _ _ E); [ try reflexivity | ].

Tactic Notation "xval" uconstr(E) :=
  xval_arg E.
Tactic Notation "xval" "~" uconstr(E) :=
  xval E; auto_tilde.
Tactic Notation "xval" "*" uconstr(E) :=
  xval E; auto_star.

Ltac xval_post tt :=
  xcleanup.

Ltac xval_core tt :=
  xval_pre tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_val _) => applys @xval_lemma_decode; [ try xdecode | ]
  | (Wpgen_Val _) => applys xval_lifted_lemma
  end;
  xval_post tt.

Tactic Notation "xval" :=
  xval_core tt.
Tactic Notation "xval" "~" :=
  xval; auto_tilde.
Tactic Notation "xval" "*"  :=
  xval; auto_star.

(** [xvals] is like [xval] followed with [xsimpl] *)

Ltac xvals_arg E :=
  xval E; xsimpl.

Tactic Notation "xvals" uconstr(E) :=
  xvals_arg E.
Tactic Notation "xvals" "~" uconstr(E) :=
  xvals E; auto_tilde.
Tactic Notation "xvals" "*" uconstr(E) :=
  xvals E; auto_star.

Ltac xvals_core tt :=
  xval; xsimpl.

Tactic Notation "xvals" :=
  xvals_core tt.
Tactic Notation "xvals" "~" :=
  xvals; auto_tilde.
Tactic Notation "xvals" "*"  :=
  xvals; auto_star.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xfun] *)

Lemma xfun_lemma : forall (v:val) H (Q:val->hprop),
  H ==> Q v ->
  H ==> ^(Wpgen_val v) Q.
Proof using. introv M. applys~ @xval_lemma M. Qed.

Ltac xfun_core tt :=
  xval_pre tt;
  applys xfun_lemma.

Tactic Notation "xfun" :=
  xfun_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xif] *)

Ltac xif_pre tt :=
  xlet_xseq_xcast_repeat tt;
  try match xgoal_code_without_wptag tt with
  | (Wpgen_app _) => xapp
  | (Wpgen_val _) => xval
  end;
  match xgoal_code_without_wptag tt with
  | (Wpgen_if_bool _ _ _) => idtac
  end.

Lemma xifval_lemma : forall A `{EA:Enc A} b H (Q:A->hprop) (F1 F2:Formula),
  (b = true -> H ==> ^F1 Q) ->
  (b = false -> H ==> ^F2 Q) ->
  H ==> ^(Wpgen_if_bool b F1 F2) Q.
Proof using. introv E N. applys MkStruct_erase. case_if*. Qed.

Lemma xifval_lemma_isTrue : forall A `{EA:Enc A} (P:Prop) H (Q:A->hprop) (F1 F2:Formula),
  (P -> H ==> ^F1 Q) ->
  (~ P -> H ==> ^F2 Q) ->
  H ==> ^(Wpgen_if_bool (isTrue P) F1 F2) Q.
Proof using. introv E N. applys MkStruct_erase. case_if*. Qed.

Ltac xif_post tt :=
  xcleanup.

Ltac xif_core tt :=
  xif_pre tt;
  first [ applys @xifval_lemma_isTrue
        | applys @xifval_lemma ];
  xif_post tt.

Tactic Notation "xif" :=
  xif_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xcase] *)

Ltac xcase_pre tt :=
  xlet_xseq_xcast_repeat tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_case _ _ _) => idtac
  end.

Lemma xcase_lemma : forall F1 (P:Prop) F2 H `{EA:Enc A} (Q:A->hprop),
  (H ==> ^F1 Q) ->
  (P -> H ==> ^F2 Q) ->
  H ==> ^(Wpgen_case F1 P F2) Q.
Proof using.
  introv M1 M2. apply MkStruct_erase. applys himpl_hand_r.
  { auto. }
  { applys* hwand_hpure_r_intro. }
Qed.

Lemma xcase_lemma0 : forall F1 (P1 P2:Prop) F2 H `{EA:Enc A} (Q:A->hprop),
  (P1 -> H ==> ^F1 Q) ->
  (P2 -> H ==> ^F2 Q) ->
  H ==> ^(Wpgen_case (fun A1 (EA1:Enc A1) (Q:A1->hprop) => \[P1] \-* ^F1 Q) P2 F2) Q.
Proof using.
  introv M1 M2. applys* xcase_lemma. { applys* hwand_hpure_r_intro. }
Qed.

Lemma xcase_lemma2 : forall (F1:val->val->Formula) (P1:val->val->Prop) (P2:Prop) F2 H `{EA:Enc A} (Q:A->hprop),
  (forall x1 x2, P1 x1 x2 -> H ==> ^(F1 x1 x2) Q) ->
  (P2 -> H ==> ^F2 Q) ->
  H ==> ^(Wpgen_case (fun A1 (EA1:Enc A1) (Q:A1->hprop) => \forall x1 x2, \[P1 x1 x2] \-* ^(F1 x1 x2) Q) P2 F2) Q.
Proof using.
  introv M1 M2. applys* xcase_lemma.
  { repeat (applys himpl_hforall_r ;=> ?). applys* hwand_hpure_r_intro. }
Qed.


Lemma xmatch_lemma_list : forall A `{EA:Enc A} (L:list A) (F1:Formula) (F2:val->val->Formula) H `{HB:Enc B} (Q:B->hprop),
  (L = nil -> H ==> ^F1 Q) ->
  (forall X L', L = X::L' -> H ==> ^(F2 ``X ``L') Q) ->
  H ==> ^(  Case (``L) = ('nil) '=> F1
         '| Case (``L) = (vX ':: vL') [vX vL'] '=> F2 vX vL'
         '| Fail) Q.
Proof using.
  introv M1 M2. applys xcase_lemma0 ;=> E1.
  { destruct L; rew_enc in *; tryfalse. applys* M1. }
  { destruct L; rew_enc in *; tryfalse. applys xcase_lemma2.
    { intros x1 x2 Hx. inverts Hx. applys* M2. }
    { intros N. false* N. } }
Qed.

(* conclusion above:
  H ==> ^(Match_ ``L With
         '| 'nil '=> F1
         '| vX ':: vL' [vX vL'] '=> F2 vX vL') Q.
*)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xfail] *)

Ltac xfail_core tt :=
  xpull;
  pose ltac_mark;
  intros;
  false;
  gen_until_mark.

Tactic Notation "xfail" :=
  xfail_core tt.

Tactic Notation "xfail" "~" :=
  xfail; auto_tilde.

Tactic Notation "xfail" "*" :=
  xfail; auto_star.





(* ********************************************************************** *)
(* Others *)

Lemma eliminate_eta_in_code : forall A `{EA:Enc A} H1 (Q1:A->hprop) (F1:Formula),
    (PRE H1
    CODE F1
    POST Q1)
  ->
    (PRE H1
    CODE (fun (A0 : Type) (EA0 : Enc A0) (Q : A0 -> hprop) => F1 A0 EA0 Q)
    POST Q1).
Proof using. introv M. xchanges M. Qed.



(* ********************************************************************** *)

(* --TODO: decode typeclass *)

(* --LATER: xif automates xapp *)




(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Loops *)

(*

(*--------------------------------------------------------*)
(* ** [xwhile] *)


(** [xwhile] applies to a goal of the form [(While F1 Do F2) H Q].
    It introduces an abstract local predicate [S] that denotes the behavior
    of the loop. The goal is [S H Q]. An assumption is provided to unfold
    the loop:
    [forall H' Q', (If_ F1 Then (Seq_ F2 ;; S) Else (Ret tt)) H' Q' -> S H' Q'].

    After [xwhile], the typical proof pattern is to generalize the goal
    by calling [assert (forall X, S (Hof X) (Qof X)] for some predicate [Hof]
    and [Qof] and then performing a well-founded induction on [X] w.r.t. wf
    relation. (Or, using [xind_skip] to skip the termination proof.)

    Alternatively, one can call one of the [xwhile_inv] tactics described
    below to automatically set up the induction. The use of an invariant
    makes the proof simpler but

    Forms:

    - [xwhile] is the basic form, described above.

    - [xwhile as S] is equivalent to [xwhile; intros S LS HS].

    - [xwhile_inv I R]  where [R] is a well-founded relation on
      type [A] and then invariant [I] has the form
      [fun (b:bool) (X:A) => H]. Compared with [xwhile], this tactic
      saves the need to set up the induction. However, this tactic
      does not allow calling the [frame] rule during the loop iterations.

    - [xwhile_inv_basic I R]  where [R] is a well-founded relation on
      type [A] and then invariant [I] has the form
      [fun (b:bool) (X:A) => H]. This tactic processes the loop so
      as to provide separate goals for the loop condition and for
      the loop body. However, this tactic should not be use when both
      the loop condition and the loop body require unfolding a
      representation predicate.

    - [xwhile_inv_basic_measure I]  where then invariant [I] has the
      form [fun (b:bool) (m:int) => H], where [b] indicates whether
      the loop has terminated, and [m] gives the measure of [H].
      It is just a special case of [xwhile_inv_basic].

    - [xwhile_inv_skip I] is similar to [xwhile_inv], but the termination
      proof is not required. Here, [I] takes the form [fun (b:bool) => H].

    - [xwhile_inv_basic_skip I] is similar to [xwhile_inv_basic], but the termination
      proof is not required. Here, [I] takes the form [fun (b:bool) => H].

*)

Lemma xwhile_inv_lemma :
  forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop),
  forall (F1:~~bool) (F2:~~unit) H,
  wf R ->
  (H ==> (Hexists b X0, I b X0) \* \GC) ->
  (forall (S:~~unit), is_local S -> forall b X,
      (forall b'' X'', R X'' X -> S (I b'' X'') (# Hexists X', I false X')) ->
      (Let _c := F1 in If_ _c Then (F2 ;; S) Else Ret tt) (I b X) (# Hexists X', I false X')) ->
  (While F1 Do F2 Done_) H (# Hexists X, I false X).
Proof using.
  introv WR HH HS.
  applys local_gc_pre (Hexists b X0, I b X0); [ xlocal | apply HH | ].
  apply local_erase. intros S LS FS.
  xpull ;=> b X0. gen b. induction_wf IH: WR X0. intros.
  applys (rm FS). applys HS. auto.
  intros b'' X'' LX. applys IH. applys LX.
Qed.

Lemma xwhile_inv_basic_lemma :
   forall (A:Type) (I:bool->A->hprop) (R:A->A->Prop),
   forall (F1:~~bool) (F2:~~unit) H,
   wf R ->
   (H ==> (Hexists b X0, I b X0) \* \GC) ->
   (forall b X, F1 (I b X) (fun b' => I b' X)) ->
   (forall X, F2 (I true X) (# Hexists b X', \[R X' X] \* I b X')) ->
   (While F1 Do F2 Done_) H (# Hexists X, I false X).
Proof using.
  introv WR HH HF1 HF2.
  applys local_gc_pre (Hexists b X, I b X); [ xlocal | apply HH | ].
  applys xwhile_inv_lemma (fun X m => I X m) R; [ auto | hsimpl | ].
  introv LS FS. xlet as b'.
  { applys HF1. }
  { simpl. xif.
    { xseq. applys HF2. simpl. xpull ;=>. applys~ FS. }
    { xret. hsimpl. } }
Qed.

Lemma xwhile_inv_basic_measure_lemma :
   forall (I:bool->int->hprop),
   forall (F1:~~bool) (F2:~~unit) H,
   (H ==> (Hexists b m, I b m) \* \GC) ->
   (forall b m, F1 (I b m) (fun b' => I b' m)) ->
   (forall m, F2 (I true m) (# Hexists b m', \[0 <= m' < m] \* I b m')) ->
   (While F1 Do F2 Done_) H (# Hexists m, I false m).
Proof using.
  introv HH HF1 HF2. applys~ xwhile_inv_basic_lemma I (wf_downto 0).
Qed.

(* for cheaters *)
Axiom xwhile_inv_basic_skip_lemma :
   forall (I:bool->hprop),
   forall (F1:~~bool) (F2:~~unit) H,
   (H ==> (Hexists b, I b) \* \GC) ->
   (forall b, F1 (I b) (fun b' => I b')) ->
   (F2 (I true) (# Hexists b, I b)) ->
   (While F1 Do F2 Done_) H (# I false).

(* for cheaters *)
Axiom xwhile_inv_skip_lemma :
  forall (I:bool->hprop),
  forall (F1:~~bool) (F2:~~unit) H,
  (H ==> (Hexists b, I b) \* \GC) ->
  (forall (S:~~unit), is_local S -> forall b,
      (forall b'', S (I b'') (# I false)) ->
      (Let _c := F1 in If_ _c Then (F2 ;; S) Else Ret tt) (I b) (# I false)) ->
  (While F1 Do F2 Done_) H (# I false).

Ltac cfml_relation_of_relation_or_measure E :=
  match type of E with
  | _ -> nat => constr:(LibWf.measure E)
  | _ => E
  end.

Ltac xwhile_pre cont :=
  let aux tt := xuntag tag_while; cont tt in
  match cfml_get_tag tt with
  | tag_while =>
    match cfml_postcondition_is_evar tt with
    | true => aux tt
    | false => xgc_post; [ aux tt | ]
    end
  | tag_seq => xseq; [ aux tt | instantiate; try xpull ]
  end.

Tactic Notation "xwhile" :=
  xwhile_pre ltac:(fun _ => apply local_erase).

Tactic Notation "xwhile" "as" ident(S) :=
  xwhile_pre ltac:(fun _ =>
    let LS := fresh "L" S in
    let HS := fresh "H" S in
    apply local_erase;
    intros S LS HS).

Ltac xwhile_inv_core I R :=
  let R := cfml_relation_of_relation_or_measure R in
  xwhile_pre ltac:(fun _ => apply (@xwhile_inv_lemma _ I R);
    [ auto with wf | | xtag_pre_post ]).

Tactic Notation "xwhile_inv" constr(I) constr(R) :=
  xwhile_inv_core I R.

Ltac xwhile_inv_basic_core I R :=
  let R := cfml_relation_of_relation_or_measure R in
  xwhile_pre ltac:(fun _ => apply (@xwhile_inv_basic_lemma _ I R);
    [ auto with wf | | xtag_pre_post | xtag_pre_post ]).

Tactic Notation "xwhile_inv_basic" constr(I) constr(R) :=
  xwhile_inv_basic_core I R.

Tactic Notation "xwhile_inv_basic_measure" constr(I) :=
  xwhile_pre ltac:(fun _ => apply (@xwhile_inv_basic_measure_lemma I);
    [ | xtag_pre_post | xtag_pre_post ]).

Tactic Notation "xwhile_inv_skip" constr(I) :=
  xwhile_pre ltac:(fun _ => apply (@xwhile_inv_skip_lemma I);
    [ xtag_pre_post | xtag_pre_post ]).

Tactic Notation "xwhile_inv_basic_skip" constr(I)  :=
  xwhile_pre ltac:(fun _ => apply (@xwhile_inv_basic_skip_lemma I);
    [ | xtag_pre_post | xtag_pre_post ]).


(*--------------------------------------------------------*)
(* ** [xfor] *)

(** [xfor] applies to a goal of the form [(For i = a To b Do F) H Q].
    It introduces an abstract local predicate [S] such that [S i]
    denotes the behavior of the loop starting from index [i].
    The initial goal is [S a H Q]. An assumption is provided to unfold
    the loop:
    [forall i H' Q',
     (If_ i <= b Then (Seq_ F ;; S (i+1)) Else (Ret tt)) H' Q' -> S i H' Q'].

    After [xfor], the typical proof pattern is to generalize the goal
    by calling [assert (forall X i, i <= b -> S i (Hof i X) (Qof i X))],
    and then performing an induction on [i].
    (Or, using [xind_skip] to skip the termination proof.)

    Alternatively, one can call one of the [xfor_inv] tactics described
    below to automatically set up the induction. The use of an invariant
    makes the proof simpler but

    Forms:

    - [xfor] is the basic form, described above.

    - [xfor as S] is equivalent to [xwhile; intros S LS HS].

    - [xfor_inv I] specializes the goal for the case [a <= b+1].
      It requests to prove [H ==> I a] and [I (b+1) ==> Q], and
      [forall i, a <= i <= b, F (I i) (# I (i+1))] for iterations.
      Note that the goal will not be provable if [a > b+1].

    - [xfor_inv_void] simplifies the goal in case the loops runs
      no iteration, that is, when [a > b].

    - [xfor_inv_case I] provides two sub goals, one for the case
      [a > b] and one for the case [a <= b].
*)

Lemma xfor_simplify_inequality_lemma : forall (n:int),
  ((n-1)+1) = n.
Proof using. math. Qed.

Ltac xfor_simplify_inequality tt :=
  try rewrite xfor_simplify_inequality_lemma.
  (* TODO: ideally, would restrict the rewriting to the
     occurences created by the application of the lemma. *)

Lemma xfor_inv_case_lemma : forall (I:int->hprop),
   forall (a:int) (b:int) (F:int->~~unit) H (Q:unit->hprop),
   ((a <= b) -> exists H',
          (H ==> I a \* H')
       /\ (forall i, a <= i <= b -> F i (I i) (# I(i+1)))
       /\ (I (b+1) \* H' ==> Q tt \* \GC)) ->
   ((a > b) ->
          (H ==> Q tt \* \GC)) ->
  (For i = a To b Do F i Done_) H Q.
Proof using.
  introv M1 M2. apply local_erase. intros S LS HS.
  tests: (a <= b).
  { forwards (H'&(Ma&Mb&Mc)): (rm M1). math.
    cuts P: (forall i, a <= i <= b+1 -> S i (I i) (# I (b+1))).
    { xapply P. math. hchanges Ma. hchanges Mc. }
    { intros i. induction_wf IH: (upto (b+1)) i. intros Hi.
      applys (rm HS). xif.
      { xseq. applys Mb. math. xapply IH; auto with maths. xsimpl. }
      { xret. math_rewrite (i = b+1). xsimpl. } } }
  { applys (rm HS). xif. { math. } { xret. applys M2. math. } }
Qed.

Lemma xfor_inv_lemma : forall (I:int->hprop),
  forall (a:int) (b:int) (F:int->~~unit) H H',
  (a <= b+1) ->
  (H ==> I a \* H') ->
  (forall i, a <= i <= b -> F i (I i) (# I(i+1))) ->
  (For i = a To b Do F i Done_) H (# I (b+1) \* H').
Proof using.
  introv ML MH MI. applys xfor_inv_case_lemma I; intros C.
  { exists H'. splits~. xsimpl. }
  { xchange MH. math_rewrite (a = b + 1). xsimpl. }
Qed.

Lemma xfor_inv_lemma_pred : forall (I:int->hprop),
  forall (a:int) (n:int) (F:int->~~unit) H H',
  (a <= n) ->
  (H ==> I a \* H') ->
  (forall i, a <= i < n -> F i (I i) (# I(i+1))) ->
  (For i = a To (n - 1) Do F i Done_) H (# I n \* H').
Proof using.
  introv ML MH MI. applys xfor_inv_case_lemma I; intros C.
  { exists H'. splits~.
    { intros. applys MI. math. }
    { math_rewrite ((n-1)+1 = n). xsimpl. } }
  { xchange MH. math_rewrite (a = n). xsimpl. }
Qed.

Lemma xfor_inv_void_lemma :
  forall (a:int) (b:int) (F:int->~~unit) H,
  (a > b) ->
  (For i = a To b Do F i Done_) H (# H).
Proof using.
  introv ML.
  applys xfor_inv_case_lemma (fun (i:int) => \[]); intros C.
  { false. math. }
  { xsimpl. }
Qed.

Ltac xfor_ensure_evar_post cont :=
  match cfml_postcondition_is_evar tt with
  | true => cont tt
  | false => xgc_post; [ cont tt | ]
  end.

Ltac xfor_pre cont :=
  let aux tt := xuntag tag_for; cont tt in
  match cfml_get_tag tt with
  | tag_for => aux tt
  | tag_seq => xseq; [ aux tt | instantiate; try xpull ]
  end.

Ltac xfor_pre_ensure_evar_post cont :=
  xfor_pre ltac:(fun _ =>
    xfor_ensure_evar_post ltac:(fun _ => cont tt)).

Tactic Notation "xfor" :=
  xfor_pre ltac:(fun _ => apply local_erase).

Tactic Notation "xfor" "as" ident(S) :=
  xfor_pre ltac:(fun _ =>
    let LS := fresh "L" S in
    let HS := fresh "H" S in
    apply local_erase;
    intros S LS HS).

Ltac xfor_inv_case_check_post_instantiated tt :=
  lazymatch cfml_postcondition_is_evar tt with
  | true => fail 2 "xfor_inv_case requires a post-condition; use [xpost Q] to set it, or [xseq Q] if the loop is behind a Seq."
  | false => idtac
  end.

Ltac xfor_inv_case_core_then I cont1 cont2 :=
  match cfml_get_tag tt with
  | tag_seq =>
       fail 1 "xfor_inv_case requires a post-condition; use [xseq Q] to assign it."
  | tag_for =>
       xfor_inv_case_check_post_instantiated tt;
       xfor_pre ltac:(fun _ => apply (@xfor_inv_case_lemma I); [ cont1 tt | cont2 tt ])
  end.

Ltac xfor_inv_case_no_intros_core I :=
  xfor_inv_case_core_then I
    ltac:(fun _ => xfor_simplify_inequality tt)
    ltac:(fun _ => idtac).

Ltac xfor_inv_case_core I :=
  let C := fresh "C" in
  xfor_inv_case_core_then I
    ltac:(fun _ => intros C; esplit; splits 3; [ | | xfor_simplify_inequality tt ])
    ltac:(fun _ => intros C).

Tactic Notation "xfor_inv_case" constr(I) :=
  xfor_inv_case_core I.

Ltac xfor_inv_core I :=
  xfor_pre_ensure_evar_post ltac:(fun _ =>
     first [ apply (@xfor_inv_lemma_pred I)
           | apply (@xfor_inv_lemma I) ];
     [ | | xtag_pre_post ]).

Tactic Notation "xfor_inv" constr(I) :=
  xfor_inv_core I.

Ltac xfor_inv_void_core tt :=
  xfor_pre_ensure_evar_post ltac:(fun _ =>
    apply (@xfor_inv_void_lemma)).

Tactic Notation "xfor_inv_void" :=
  xfor_inv_void_core tt.


(*--------------------------------------------------------*)
(* ** [xfor_down] *)

(** [xfor_down] applies to a goal of the form [(For i = a Downto b Do F) H Q].
    It introduces an abstract local predicate [S] such that [S i]
    denotes the behavior of the loop starting from index [i].
    The initial goal is [S a H Q]. An assumption is provided to unfold
    the loop:
    [forall i H' Q',
     (If_ i >= b Then (Seq_ F ;; S (i-1)) Else (Ret tt)) H' Q' -> S i H' Q'].

    See [xfor] for additional comments.

    Forms:

    - [xfor_down] is the basic form, described above.

    - [xfor_down as S] is equivalent to [xwhile; intros S LS HS].

    - [xfor_down_inv I] specializes the goal for the case [a >= b-1].
      It requests to prove [H ==> I b] and [I (a-1) ==> Q], and
      [forall i, b <= i <= a, F (I i) (# I (i-1))] for iterations.
      Note that the goal will not be provable if [a < b-1].

    - [xfor_down_inv_void] simplifies the goal in case the loops runs
      no iteration, that is, when [a < b].

    - [xfor_down_inv_case I] provides two sub goals, one for the case
      [a < b] and one for the case [a >= b].
*)

Lemma xfor_down_inv_case_lemma : forall (I:int->hprop),
   forall (a:int) (b:int) (F:int->~~unit) H (Q:unit->hprop),
   ((a >= b) -> exists H',
          (H ==> I a \* H')
       /\ (forall i, b <= i <= a -> F i (I i) (# I(i-1)))
       /\ (I (b-1) \* H' ==> Q tt \* \GC)) ->
   ((a < b) ->
          (H ==> Q tt \* \GC)) ->
  (For i = a DownTo b Do F i Done_) H Q.
Proof using.
  introv M1 M2. apply local_erase. intros S LS HS.
  tests: (a >= b).
  { forwards (H'&(Ma&Mb&Mc)): (rm M1). math.
    cuts P: (forall i, b-1 <= i <= a -> S i (I i) (# I (b-1))).
    { xapply P. math. hchanges Ma. hchanges Mc. }
    { intros i. induction_wf IH: (downto (b-1)) i. intros Hi.
      applys (rm HS). xif.
      { xseq. applys Mb. math. xapply IH; auto with maths. xsimpl. }
      { xret. math_rewrite (i = b - 1). xsimpl. } } }
  { applys (rm HS). xif. { math. } { xret. applys M2. math. } }
Qed.

Lemma xfor_down_inv_lemma : forall (I:int->hprop),
  forall (a:int) (b:int) (F:int->~~unit) H H',
  (a >= b-1) ->
  (H ==> I a \* H') ->
  (forall i, b <= i <= a -> F i (I i) (# I(i-1))) ->
  (For i = a DownTo b Do F i Done_) H (# I (b-1) \* H').
Proof using.
  introv ML MH MI. applys xfor_down_inv_case_lemma I; intros C.
  { exists H'. splits~. xsimpl. }
  { xchange MH. math_rewrite (a = b - 1). xsimpl. }
Qed.

Lemma xfor_down_inv_void_lemma :
  forall (a:int) (b:int) (F:int->~~unit) H,
  (a < b) ->
  (For i = a DownTo b Do F i Done_) H (# H).
Proof using.
  introv ML.
  applys xfor_down_inv_case_lemma (fun (i:int) => \[]); intros C.
  { false. math. }
  { xsimpl. }
Qed.

Ltac xfor_down_pre cont :=
  let aux tt := xuntag tag_for_down; cont tt in
  match cfml_get_tag tt with
  | tag_for_down => aux tt
  | tag_seq => xseq; [ aux tt | instantiate; try xpull ]
  end.

Ltac xfor_down_pre_ensure_evar_post cont :=
  xfor_down_pre ltac:(fun _ =>
    xfor_ensure_evar_post ltac:(fun _ => cont tt)).

Tactic Notation "xfor_down" :=
  xfor_down_pre ltac:(fun _ => apply local_erase).

Tactic Notation "xfor_down" "as" ident(S) :=
  xfor_down_pre ltac:(fun _ =>
    let LS := fresh "L" S in
    let HS := fresh "H" S in
    apply local_erase;
    intros S LS HS).

Ltac xfor_down_inv_case_core_then I cont1 cont2 :=
  match cfml_get_tag tt with
  | tag_seq =>
       fail 1 "xfor_inv_case requires a post-condition; use [xseq Q] to assign it."
  | tag_for_down =>
       xfor_inv_case_check_post_instantiated tt;
       xfor_down_pre ltac:(fun _ => apply (@xfor_down_inv_case_lemma I);
                                     [ cont1 tt | cont2 tt ])
  end.

Ltac xfor_down_inv_case_no_intros_core I :=
  xfor_down_inv_case_core_then I ltac:(fun _ => idtac) ltac:(fun _ => idtac).

Ltac xfor_down_inv_case_core I :=
  let C := fresh "C" in
  xfor_down_inv_case_core_then I
    ltac:(fun _ => intros C; esplit; splits 3)
    ltac:(fun _ => intros C).

Tactic Notation "xfor_down_inv_case" constr(I) :=
  xfor_down_inv_case_core I.

Ltac xfor_down_inv_core I :=
  xfor_down_pre_ensure_evar_post ltac:(fun _ => apply (@xfor_down_inv_lemma I)).

Tactic Notation "xfor_down_inv" constr(I) :=
  xfor_down_inv_core I.

Ltac xfor_down_inv_void_core tt :=
  xfor_down_pre_ensure_evar_post ltac:(fun _ => apply (@xfor_down_inv_void_lemma)).

Tactic Notation "xfor_down_inv_void" :=
  xfor_down_inv_void_core tt.

*)


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Pattern matching *)


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xdone] *)

Lemma xdone_lemma : forall (Q:unit->hprop) H,
  H ==> Q tt ->
  H ==> ^(Wpgen_done) Q.
Proof using.
  introv M. unfold Wpgen_done.
  applys MkStruct_erase. xchange M. xsimpl.
Qed.

Ltac xdone_core tt :=
  applys xdone_lemma.

Tactic Notation "xdone" :=
  xdone_core tt.


(*

(*--------------------------------------------------------*)
(* ** [xdone] *)

(** [xdone] proves a goal of the form [Done H Q],
    which is in fact equivalent to [True]. *)

Tactic Notation "xdone" :=
  xuntag tag_done; apply local_erase; split.


(*--------------------------------------------------------*)
(* ** [xcleanpat] *)

(** [xcleanpat] is a tactic for removing all the assumptions
    produced by [xcase] and [xmatch] and expressing that the
    previous patterns did not match. *)

Definition xnegpat (P:Prop) := P.

Lemma xtag_negpat_intro : forall (P:Prop), P -> xnegpat P.
Proof using. auto. Qed.

Ltac xuntag_negpat :=  (* useful for debugging *)
  unfold xnegpat in *.

Ltac xtag_negpat H :=
  applys_to H xtag_negpat_intro.

Ltac xcleanpat_core :=
  repeat match goal with H: xnegpat _ |- _ => clear H end.

Tactic Notation "xcleanpat" :=
  xcleanpat_core.


(*--------------------------------------------------------*)
(* ** [xalias] *)

(** [xalias] applies to a goal of the form
    [(Alias x := v in F) H Q]. It adds the assumption [x = v],
    and leaves [F H Q] as new subgoal.

    Variants:
    [xalias as y] allows to rename [x] into [y].
    [xalias as y E] allows to rename [x] into [y] and to
     specify the name of the hypothesis [y = v].
    [xalias_subst] allows to substitute the equality [x = v] right away. *)

Ltac xalias_pre tt :=
  xuntag tag_alias;
  apply local_erase;
  xtag_pre_post.

Tactic Notation "xalias" "as" ident(x) ident(H) :=
  xalias_pre tt;
  intros x H.

Tactic Notation "xalias" "as" ident(x) :=
  let HE := fresh "E" x in
  xalias as x HE.

Tactic Notation "xalias" :=
  xalias_pre tt;
  intro;
  let H := get_last_hyp tt in
  let HE := fresh "E" H in
  intro HE.

Tactic Notation "xalias_subst" :=
  let x := fresh "TEMP" in
  let Hx := fresh "TEMP" in
  xalias as x Hx;
  subst x.


(*--------------------------------------------------------*)
(* ** [xcase] is the new [xcase] *)

(** [xcase] applies to a goal of the form
    [(Case v = p1 Then F1 Else F2) H Q].

   It produces two subgoals.
   - the first subgoal is [F1 H Q] with an hypothesis [E : v = p1].
   - the first subgoal is [F2 H Q] with an hypothesis [E : v <> p1].

   In both subgoals, it attemps deducing false from [E] or inverting [E],
   by calling the tactic [xcase_post E].

   Variants:

   - [xcase as E] allows to name [E].

   - [xcase_no_simpl] does not attempt inverting [E].

   - [xcase_no_simpl as E] allows to name [E];
     it does not attempt inverting [E].

   - [xcase_no_intros] can be used to manually name the variables and
     hypotheses from the case. It does not attempt inverting [E]. *)


(* Implementation note:
   [xcase_post] is a tactic that applies to an hypothesis
   of the form [v = p1] or [v <> p1], and attemps to prove
   false from it, and inverts it if possible. *)

Ltac xclean_trivial_eq tt :=
  repeat match goal with H: ?E = ?E |- _ => clear H end.

Ltac xcase_post H :=
  try solve [ discriminate | false; congruence ];
  try (symmetry in H; inverts H; xclean_trivial_eq tt).

(* Implementation note:
   [xcase_core E cont1 cont2] is the underlying tactic for [xcase].
   It calls [cont1] on the first subgoal and [cont2] on the second subgoal. *)

Ltac xcase_core H cont1 cont2 :=
  xuntag tag_case; apply local_erase; split;
    [ introv H; cont1 tt
    | introv H; xtag_negpat H; cont2 tt ];
  xtag_pre_post.

Ltac xcase_no_intros_core cont1 cont2 :=
  xuntag tag_case; apply local_erase; split;
    [ cont1 tt
    | cont2 tt ];
  xtag_pre_post.
      (* TODO in the second branch:
         pose mark; introv H; xtag_negpat H; gen_until_mark tt *)

Tactic Notation "xcase_no_simpl" "as" ident(H) :=
  xcase_core H ltac:(fun _ => idtac) ltac:(fun _ => idtac).

Tactic Notation "xcase_no_simpl" :=
  let H := fresh "C" in xcase_no_simpl as H.

Tactic Notation "xcase" "as" ident(H) :=
  xcase_no_simpl as H; xcase_post H.

Tactic Notation "xcase" :=
  let H := fresh "C" in xcase as H.

Tactic Notation "xcase_no_intros" :=
   xcase_no_intros_core ltac:(fun _ => idtac) ltac:(fun _ => idtac).



(*--------------------------------------------------------*)
(* ** [xmatch] *)

(** [xmatch] applies to a pattern-matching goal of the form
    [(Match Case v = p1 Then F1
       Else Case v = p2 Then Alias y := w in F2
       Else Done/Fail) H Q].

    By default, the tactic calls the inversion tactic on
    the equalities [v = pi] associated with the case
    (and also calls congruence to attempt proving false).
    [xmatch_no_simpl] can be used to disable such inversions.

    Several variants are available:

    - [xmatch] investigates all the cases, doing inversions,
      and introducing all aliases as equalities.

    - [xmatch_no_alias] is like [xmatch], but does not
      introduce aliases.

    - [xmatch_subst_alias] performs all case analyses,
      and introduces and substitutes all aliases.

    - [xmatch_no_cases] simply remove the [Match] tag and
      leaves the cases to be solved manually using
      [xmatch_case] or [xcase]/[xfail]/[xdone] tactics directly.

    - [xmatch_clean] is a shorthand for [xmatch; xcleanpat]:
      it does not keep the negation of the patterns as hypotheses

    - [xmatch_no_intros] is like [xmatch], but does not
      perform any name introduction or any inversion.
      (need to manually call [xdone] for the last case.)
      (only the negation of patterns are introduced automatically.)

    - [xmatch_no_simpl] is like [xmatch], but does not do inversions.
      [xmatch_no_simpl_no_alias] is also available.
      [xmatch_no_simpl_subst_alias] are also available.

   Like with [xif], the tactic [xmatch] will likely not produce
   solvable goals if the post-condition is an unspecified evar.
   If the post-condition is an evar, call [xpost Q] to set the
   post-condition. Alternatively, the syntax [xmatch Q] will do this.

 *)

Ltac xmatch_case_alias cont :=
  let H := fresh "C" in
  xcase_core H ltac:(fun _ => repeat xalias; xcase_post H)
               ltac:(fun _ => cont tt).

Ltac xmatch_case_no_alias cont :=
  let H := fresh "C" in
  xcase_core H ltac:(fun _ => xcase_post H) ltac:(fun _ => cont tt).

Ltac xmatch_case_no_simpl cont :=
  let H := fresh "C" in
  xcase_core H ltac:(fun _ => idtac) ltac:(fun _ => cont tt).

Ltac xmatch_case_no_intros cont :=
  xcase_no_intros_core
    ltac:(fun _ => idtac)
    ltac:(fun _ => let H := fresh "C" in introv H; xtag_negpat H; cont tt).

Ltac xmatch_case_core cont_case :=
  match cfml_get_tag tt with
  | tag_done => xdone
  | tag_fail => xfail
  | tag_case => cont_case tt
  | _ => fail 100 "unexpected tag in xmatch_case"
  end.

(* [xmatch_cases case_tactic] recursively apply [xmatch_case] using
   [case_tactic] to handle each case. *)

Ltac xmatch_cases case_tactic :=
  xmatch_case_core ltac:(fun _ =>
    case_tactic ltac:(fun _ => xmatch_cases case_tactic)).

Ltac xmatch_check_post_instantiated tt :=
  match cfml_postcondition_is_evar tt with
  | true => fail 100 "xmatch requires a post-condition; use [xmatch Q] or [xpost Q] to set it."
  | false => idtac
  end.

Ltac xmatch_pre cont :=
  xpull_check_not_needed tt;
  xmatch_check_post_instantiated tt;
  xuntag tag_match;
  apply local_erase;
  cont tt.

(* DEPRECATED

  Ltac xmatch_cases case_tactic n :=
    match n with
    | 0%nat => first [ xdone | xfail | idtac ]
    | S ?n' => case_tactic ltac:(fun _ => xmatch_cases case_tactic n')
    | _ => idtac
    end.

  Ltac xmatch_core cont :=
    xpull_check_not_needed tt;
    let tag := cfml_get_tag tt in
    match tag with
    | tag_match ?n => xuntag (tag_match n); cont n
    end.

Tactic Notation "xmatch_no_alias" :=
  xmatch_core ltac:(fun n => xmatch_cases xmatch_case_no_alias n).
Tactic Notation "xmatch_no_simpl_no_alias" :=
  xmatch_core ltac:(fun n => xmatch_cases xmatch_case_no_simpl n).
Tactic Notation "xmatch_no_intros" :=
  xmatch_core ltac:(fun n => xmatch_cases xmatch_case_no_intros n).

*)

Tactic Notation "xmatch_case" :=
  xmatch_case_core ltac:(fun _ => xmatch_case_alias ltac:(fun _ => idtac)).

Tactic Notation "xmatch_no_cases" :=
  xmatch_pre ltac:(fun _ => xtag_pre_post).
Tactic Notation "xmatch_no_alias" :=
  xmatch_pre ltac:(fun _ => xmatch_cases xmatch_case_no_alias).
Tactic Notation "xmatch_no_simpl_no_alias" :=
  xmatch_pre ltac:(fun _ => xmatch_cases xmatch_case_no_simpl).
Tactic Notation "xmatch_no_intros" :=
  xmatch_pre ltac:(fun _ => xmatch_cases xmatch_case_no_intros).
Tactic Notation "xmatch" :=
  xmatch_pre ltac:(fun _ => xmatch_cases xmatch_case_alias).
  (* DEPRECATED xmatch_no_alias; repeat xalias. *)



Tactic Notation "xmatch_no_simpl" :=
   xmatch_no_simpl_no_alias; repeat xalias.
Tactic Notation "xmatch_subst_alias" :=
   xmatch_no_alias; repeat xalias_subst.
Tactic Notation "xmatch_no_simpl_subst_alias" :=
   xmatch_no_simpl_no_alias; repeat xalias_subst.

Tactic Notation "xmatch_clean" :=
  xmatch; xcleanpat.
Tactic Notation "xmatch" constr(Q) :=
  xpost Q; xmatch.


*)


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Others *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xassert] *)

(*

Lemma xassert_lemma : forall A1 `{Enc A1} (F1:(A1->hprop)->hprop) (Q:A1->hprop) H,
  H ==> Q tt ->
  Q tt ==> F1 (fun r => \[r = true] \* Q tt) ->
  H ==> ^(Wpgen_assert F1) Q.
Proof using.
Qed.

Lemma xassert_lemma_inst : forall A1 `{Enc A1} (F1:(A1->hprop)->hprop) (Q:A1->hprop) H,
  H ==> F1 (fun r => \[r = true] \* H) ->
  H ==> ^(Wpgen_assert F1) (fun (_:unit) => H).
Proof using.
  introv M. xchange xassert_lemma.
Qed.

*)



(*--------------------------------------------------------*)
(* ** [xletval] and [xletval_st] *)

(*

(** [xletval] is used to reason on a let-value node, i.e. on a goal
    of the form [(Val x := v in F1) H Q].
    It produces an equality [x = v].

    Use [xletval as y] to rename [x] into [y].
    Use [xletval as y E] to rename [x] into [y] and name [E] the equality [y=v].

    *)

Ltac xletval_pre tt :=
  xpull_check_not_needed tt;
  xuntag tag_val;
  apply local_erase.

Ltac xletval_core x Hx :=
  xletval_pre tt;
  intros x Hx;
  xtag_pre_post.

Tactic Notation "xletval" "as" simple_intropattern(x) simple_intropattern(Hx) :=
  xletval_core x Hx.

Tactic Notation "xletval" "as" simple_intropattern(x) :=
  let Hx := fresh "P" x in xletval_core x Hx.

Ltac xletval_anonymous_impl tt :=
  xletval_pre tt;
  intro;
  let x := get_last_hyp tt in
  revert x;
  let Hx := fresh "P" x in
  intros x Hx;
  xtag_pre_post.

Tactic Notation "xletval" :=
  xletval_anonymous_impl tt.

(** [xletvals] is like [xletval] but it immediately substitutes
    the equality [x = v] produced by [xletval]. *)

Ltac xletvals_core tt :=
  xletval_pre tt; intro; intro_subst; xtag_pre_post.

Tactic Notation "xletvals" :=
  xletvals_core tt.


(** [xletval_st P] is used to assign an abstract specification
    to the value. Instead of producing [x = v] as hypothesis,
    it produces [P x] as hypothesis, and issues [P v] as subgoal.

    Use [xletval_st P as y] to rename [x] into [y].
    Use [xletval_st P as y Hy] to rename [x] into [y] and specify the name
      of the hypothesis [P y]. *)

Ltac xletval_st_core P x Hx :=
  let E := fresh in
  intros x E;
  asserts Hx: (P x); [ subst x | clear E; xtag_pre_post ].

Ltac xletval_st_impl P x Hx :=
  xletval_pre tt; xletval_st_core P x Hx.

Tactic Notation "xletval_st" constr(P) "as" simple_intropattern(x) simple_intropattern(Hx) :=
  xletval_st_impl P x Hx.

Tactic Notation "xletval_st" constr(P) "as" simple_intropattern(x) :=
  let Hx := fresh "P" x in xletval_st_impl P x Hx.

Ltac xletval_st_anonymous_impl P :=
  xletval_pre tt; intro; let x := get_last_hyp tt in revert x;
  let Hx := fresh "P" x in xletval_st_core P x Hx.

Tactic Notation "xletval_st" constr(P) :=
  xletval_st_anonymous_impl P.

*)


(************************************************************)
(** [xgo], [xcf_go] and [xstep] *)

Ltac check_is_Wpgen_record_new F :=  (* refined in WPRecord *)
  fail.

Ltac xstep_once tt :=
  match goal with
  | |- ?G => match xgoal_code_without_wptag tt with
    | (Wpgen_seq _ _) => xseq
    | (Wpgen_let_typed _ _) => xlet
    | (Wpgen_let _ _) => xlet
    | (Wpgen_app _) => xapp
    | (Wpgen_App_typed _ _ _) => xapp
    | (Wpgen_if_bool _ _ _) => xif
    | (Wpgen_val _) => xval
    | (Wpgen_Val _) => xval
    | (Wpgen_Val_no_mkstruct _) => xcast
    | (Wpgen_fail) => xfail
    | ?F => check_is_Wpgen_record_new F; xapp
    (* | (Wpgen_case _ _ _) => xcase *)
    (* TODO complete *)
    end
  | |- _ ==> _ => xsimpl
  | |- _ ===> _ => xsimpl
  end.

Ltac xstep_pre tt :=
  try xpull; intros.

Ltac xstep_core tt :=
  xstep_pre tt; xstep_once tt; instantiate.

Tactic Notation "xstep" :=
  xstep_core tt.
Tactic Notation "xstep" "~" :=
  xstep; auto_tilde.
Tactic Notation "xstep" "*" :=
  xstep; auto_star.

Ltac xgo_core tt :=
  repeat (xstep_core tt).

Tactic Notation "xgo" :=
  xgo_core tt.
Tactic Notation "xgo" "~" :=
  xgo; auto_tilde.
Tactic Notation "xgo" "*" :=
  xgo; auto_star.

Tactic Notation "xcf_go" :=
  xcf; xgo.
Tactic Notation "xcf_go" "~" :=
  xcf_go; auto_tilde.
Tactic Notation "xcf_go" "*" :=
  xcf_go; auto_star.

(*
(*--------------------------------------------------------*)
(* ** [xauto] *)

(** [xauto] is a specialized version of [auto] that works
   well in program verification.

   - it will not attempt any work if the head of the goal
     has a tag (i.e. if it is a characteristif formula),
   - it is able to conclude a goal using [xok]
   - it calls [substs] to substitute all equalities before trying
     to call automation.

   Tactics [xauto], [xauto~] and [xauto*] can be configured
   independently.

   [xsimpl~] is equivalent to [xsimpl; xauto~].
   [xsimpl*] is equivalent to [xsimpl; xauto*].
*)

Ltac xok_core cont :=  (* see [xok] spec further *)
  solve [ hnf; apply refl_rel_incl'
        | apply pred_incl_refl
        | apply hsimpl_to_qunit; reflexivity
        | hsimpl; cont tt ].

Ltac math_0 ::= xclean. (* TODO: why needed? *)

Ltac xauto_common cont :=
  first [
    cfml_check_not_tagged tt;
    try solve [ cont tt
              | solve [ apply refl_equal ]
              | xok_core ltac:(fun _ => solve [ cont tt | substs; cont tt ] )
              | substs; if_eq; solve [ cont tt | apply refl_equal ]  ]
  | idtac ].

Ltac xauto_tilde_default cont := xauto_common cont.
Ltac xauto_star_default cont := xauto_common cont.

Ltac xauto_tilde := xauto_tilde_default ltac:(fun _ => auto_tilde).
Ltac xauto_star := xauto_star_default ltac:(fun _ => auto_star).

Tactic Notation "xauto" "~" := xauto_tilde.
Tactic Notation "xauto" "*" := xauto_star.
Tactic Notation "xauto" := xauto~.

*)



(************************************************************)
(** [DEPRECATED?] *)

Ltac solve_type := (* TODO: still needed? *)
  match goal with |- Type => exact unit end.

Ltac remove_head_unit tt :=
  repeat match goal with
  | |- unit -> _ => intros _
  end.


