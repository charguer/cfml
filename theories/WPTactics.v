(**

This file defines tactics for manipulating characteristic formula
in weakest-precondition form, in lifted Separation Logic,
as defined in [WPLifted.v].

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)



Set Implicit Arguments.
From Sep Require Export WPLifted.
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

(* DEPRECATED
Notation "'CODE' F 'POST' Q" := ((Wptag F) _ _ Q)
  (at level 8, F, Q at level 0,
   format "'[v' 'CODE'  F '/' 'POST'  Q ']'") : wp_scope.
   *)

Notation "'PRE' H 'CODE' F 'POST' Q" := (H ==> (Wptag F) _ _ Q)
  (at level 8, H, F, Q at level 0,
   format "'[v' 'PRE'  H  '/' 'CODE'  F '/' 'POST'  Q ']'") : wp_scope.

(** Display [Triple t H Q] as [TRIPLE t PRE H POST Q]
    with variant [TRIPLE t PRE H REV X POST Q] *)

Declare Scope triple_scope.
Open Scope triple_scope.

Notation "'TRIPLE' t 'PRE' H 'POST' Q" :=
  (Triple t H Q)
  (at level 39, t at level 0,
  format "'[v' 'TRIPLE'  t  '/' 'PRE'  H  '/' 'POST'  Q ']'") : triple_scope.

Notation "'TRIPLE' t 'PRE' H1 'RET' v 'POST' H2" :=
  (Triple t H1 (fun r => \[r = v] \* H2))
  (at level 39, t at level 0,
   format "'[v' 'TRIPLE'  t  '/' 'PRE'  H1  '/'  'RET'  v  '/'  'POST'  H2 ']'") : triple_scope.

(* --LATER

Notation "'`Triple' t 'PRE' H1 'BIND' x1 'RET' v 'POST' H2" :=
  (Triple t H1 (fun r => \exists x1, \[r = v] \* H2))
  (at level 39, t at level 0, x1 ident) : triple_scope.

Notation "'`Triple' t 'PRE' H1 'BIND' x1 x2 'RET' v 'POST' H2" :=
  (Triple t H1 (fun r => \exists x1 x2, \[r = v] \* H2))
  (at level 39, t at level 0, x1 ident, x2 ident) : triple_scope.
*)


(* ********************************************************************** *)
(* * Tactics for decoding. *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xdecode] and [xdecodes] *)

(* --LATER: WORK AROUND TYPECLASS RESOLUTION BUG *)
Hint Extern 1 (Decode (val_constr "nil" nil) _) =>
  match goal with H: Enc ?A |- _ => eapply (@Decode_nil A) end : Decode.
Hint Extern 1 (Decode (val_constr "cons" (_::_::nil)) _) =>
  match goal with H: Enc ?A |- _ => eapply (@Decode_cons A) end : Decode.

Hint Resolve Decode_None Decode_Some : Decode.
(* --LATER: similar hints needed? *)

Ltac xdecode_core tt :=
  try solve [ eauto with Decode ].

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
  end.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xspec] *)

(* ** Database of specifications used by [xapp], through tactic [xspec] *)

(** A name for the database *)

Definition database_spec := True.

Declare Scope xspec_scope.
Open Scope xspec_scope.

Notation "'Register_goal' G" := (Register database_spec G)
  (at level 69) : xspec_scope.

(** [xspec G] retreives from the database [database_spec]
    the specification that could apply to a goal [G].
    It places the specification as hypothesis at the head of the goal. *)

Ltac xspec_remove_combiner tt :=
  cbn beta delta [ combiner_to_trm ] iota zeta in *.

Ltac xspec_context tt :=
  xspec_remove_combiner tt;
  match goal with
   H: context [ Triple (trm_apps (trm_val ?f) _) _ _ ]
   |- Triple (trm_apps (trm_val ?f) _) _ _ => generalize H
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
  (at level 69) : xspec_scope.

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



(* ---------------------------------------------------------------------- *)
(* ** Tactic [xstructural] -- for internal use *)

Ltac xstructural_core tt :=
  applys Structural_Mkstruct.

Tactic Notation "xstructural" :=
  xstructural_core tt.


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
  | (Wpgen_cast _) => idtac
  end.

Lemma xcast_lemma : forall (H:hprop) `{Enc A} (Q:A->hprop) (X:A),
  H ==> Q X ->
  H ==> ^(Wpgen_cast X) Q.
Proof using. introv M. unfolds Wpgen_cast. xchange M. applys qimpl_Post_cast_r. Qed.

Ltac xcast_core tt :=
  xcast_pre tt;
  applys xcast_lemma.

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
  | (Wpgen_cast _) => xseq
  end.

Ltac xlet_xseq_xcast_repeat tt :=
  repeat (xlet_xseq_xcast tt).


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

(* [xapp_pre tt] automatically performs the necessary
   [xlet], [xseq] and [xcast], then checks that the goal
   is a [Wpgen_app] goal.

   Besides, if the goal is a triple, then it converts it
   to [wp]-style using [xtriple]. This is useful when proving
   a specification by weakening an existing one. *)

Ltac xapp_pre_wp tt :=
  xlet_xseq_xcast_repeat tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_app _) => idtac
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

(* DEPRECATED (too slow)
Ltac xapp_apply_lemma cont_prove_triple :=
  first
    [ applys @xapps_lemma; [ cont_prove_triple tt | xapp_post tt ]
    | applys @xapps_lemma_pure; [ cont_prove_triple tt | xapp_post tt ]
    | applys @xapp_lemma; [ cont_prove_triple tt | xapp_post tt ] ].
*)

Ltac xapp_general tt :=
  xapp_apply_lemma ltac:(xspec_prove_triple).

Ltac xapp_core tt :=
  xapp_pre tt;
  first [ xapp_record tt
        | xapp_general tt ].

Tactic Notation "xapp" :=
  xapp_core tt.
Tactic Notation "xapp" "~" :=
  xapp; auto_tilde.
Tactic Notation "xapp" "*"  :=
  xapp; auto_star.

Ltac xapp_arg_core E :=
  xapp_pre tt;
  xapp_apply_lemma ltac:(fun tt => xspec_prove_triple_with_args E).

Tactic Notation "xapp" constr(E) :=
  xapp_arg_core E.
Tactic Notation "xapp" "~" constr(E) :=
  xapp E; auto_tilde.
Tactic Notation "xapp" "*" constr(E) :=
  xapp E; auto_star.

Ltac xapp_nosubst_core tt :=
  xapp_pre tt;
  applys @xapp_lemma; [ xspec_prove_triple tt | xapp_post tt ].

Tactic Notation "xapp_nosubst" :=
  xapp_nosubst_core tt.
Tactic Notation "xapp_nosubst" "~" :=
  xapp_nosubst; auto_tilde.
Tactic Notation "xapp_nosubst" "*"  :=
  xapp_nosubst; auto_star.

Ltac xapp_arg_nosubst_core E :=
  xapp_pre tt;
  applys @xapp_lemma; [ xspec_prove_triple_with_args E | xapp_post tt ].

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

(* [xval_pre tt] automatically performs the necessary
   [xlet], [xseq] and [xcast], then checks that the goal
   is a [Wpgen_val] goal. *)

Ltac xval_pre tt :=
  xlet_xseq_xcast_repeat tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_val _) => idtac
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
  applys @xval_lemma_decode; [ try xdecode | ];
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
  H ==> ^(  Case ``L = 'nil '=> F1
         '| Case ``L = (vX ':: vL') [vX vL'] '=> F2 vX vL'
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
