(**

This file defines tactics for manipulating characteristic formula 
in weakest-precondition form, in lifted Separation Logic,
as defined in [WPLifted.v].

Author: Arthur Charguéraud.
License: MIT.

*)



Set Implicit Arguments.
From Sep Require Export WPLifted.
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

Notation "'TRIPLE' t 'PRE' H 'POST' Q" :=
  (Triple t H Q)
  (at level 39, t at level 0,
  format "'[v' 'TRIPLE'  t  '/' 'PRE'  H  '/' 'POST'  Q ']'") : triple_scope.

Notation "'TRIPLE' t 'PRE' H1 'RET' v 'POST' H2" :=
  (Triple t H1 (fun r => \[r = v] \* H2))
  (at level 39, t at level 0,
   format "'[v' 'TRIPLE'  t  '/' 'PRE'  H1  '/'  'RET'  v  '/'  'POST'  H2 ']'") : triple_scope.

(* LATER

Notation "'`Triple' t 'PRE' H1 'BIND' x1 'RET' v 'POST' H2" :=
  (Triple t H1 (fun r => \exists x1, \[r = v] \* H2))
  (at level 39, t at level 0, x1 ident) : triple_scope.

Notation "'`Triple' t 'PRE' H1 'BIND' x1 x2 'RET' v 'POST' H2" :=
  (Triple t H1 (fun r => \exists x1 x2, \[r = v] \* H2))
  (at level 39, t at level 0, x1 ident, x2 ident) : triple_scope.
*)

Open Scope triple_scope.


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

Notation "'Register_goal' G" := (Register database_spec G)
  (at level 69) : xspec_scope.

Open Scope xspec_scope.

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

Ltac xspec_prove_cont tt :=
  let H := fresh "Spec" in
  intro H; eapply H; clear H.

Ltac xspec_prove_triple tt :=
  xspec; xspec_prove_cont tt.

Ltac xspec_lemma_of_args E :=
  let H := fresh "Spec2" in
  match list_boxer_of E with
  | cons (boxer ltac_wild) ?E' => (* only args provided *)
     let K := fresh "BaseSpec" in (* TODO: need to clear K at some point... *)
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

Hint Extern 1 (Register_Spec (val_prim val_ref)) => Provide Triple_ref.
Hint Extern 1 (Register_Spec (val_prim val_get)) => Provide Triple_get.
Hint Extern 1 (Register_Spec (val_prim val_set)) => Provide @Triple_set.
Hint Extern 1 (Register_Spec (val_prim val_alloc)) => Provide Triple_alloc.
Hint Extern 1 (Register_Spec (val_prim val_neg)) => Provide Triple_neg.
Hint Extern 1 (Register_Spec (val_prim val_eq)) => Provide Triple_eq.
Hint Extern 1 (Register_Spec (val_prim val_add)) => Provide Triple_add.
Hint Extern 1 (Register_Spec (val_prim val_sub)) => Provide Triple_sub.
Hint Extern 1 (Register_Spec (val_prim val_ptr_add)) => Provide Triple_ptr_add.


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
  LibList.combine 
  List.rev Datatypes.app List.fold_right List.map
  Wpgen Wpaux_getval Wpaux_getval_typed
  Wpaux_apps Wpaux_constr Wpaux_var Wpaux_match
  hforall_vars forall_vars
  trm_case trm_to_pat patvars patsubst combiner_to_trm
  Ctx.app Ctx.empty Ctx.lookup Ctx.add 
  Ctx.rem Ctx.rem_var Ctx.rem_vars isubst
  var_eq eq_var_dec 
  string_dec string_rec string_rect
  sumbool_rec sumbool_rect
  Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
  Bool.bool_dec bool_rec bool_rect ] iota zeta.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xwp] *)

Lemma xwp_lemma_funs : forall F vs ts xs t `{EA:Enc A} H (Q:A->hprop),
  F = val_funs xs t ->
  trms_to_vals ts = Some vs ->
  var_funs_exec (length vs) xs ->
  H ==> ^(Wpgen (combine xs vs) t) (Q \*+ \GC) ->
  Triple (trm_apps F ts) H Q.
Proof using.
  introv HF Hvs Hxs M. applys Triple_hgc_post. lets ->: trms_to_vals_spec Hvs.
  rewrite var_funs_exec_eq in Hxs. rew_istrue in Hxs. lets (_&Lxs&_): Hxs.
  applys* Triple_apps_funs. rewrite~ <- isubstn_eq_substn.
  applys* Triple_isubst_of_Wpgen.
Qed.

Lemma xwp_lemma_fixs : forall F (f:var) vs ts xs t `{EA:Enc A} H (Q:A->hprop),
  F = val_fixs f xs t ->
  trms_to_vals ts = Some vs ->
  var_fixs_exec f (length vs) xs ->
  H ==> ^(Wpgen (combine (f::xs) (F::vs)) t) (Q \*+ \GC) ->
  Triple (trm_apps F ts) H Q.
Proof using.
  introv HF Hvs Hxs M. applys Triple_hgc_post. lets ->: trms_to_vals_spec Hvs.
  rewrite var_fixs_exec_eq in Hxs. rew_istrue in Hxs. lets (_&Lxs&_): Hxs.
  applys* Triple_apps_fixs. rewrite <- isubstn_eq_substn; [|rew_list~].
  applys* Triple_isubst_of_Wpgen.
Qed.

Ltac xwp_fun tt :=
  applys xwp_lemma_funs; [ reflexivity | reflexivity | reflexivity | xwp_simpl ].

Ltac xwp_fix tt :=
  applys xwp_lemma_fixs; [ reflexivity | reflexivity | reflexivity | xwp_simpl ].

Ltac xwp_trm tt :=
  fail "not yet implemented".

Ltac xwp_core tt :=
  intros; first [ xwp_fun tt | xwp_fix tt | xwp_trm tt ].

Tactic Notation "xwp" :=
  xwp_core tt.


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

Tactic Notation "xtriple" :=
  applys xtriple_lemma;
  [ simpl combiner_to_trm; rew_trms_vals; reflexivity 
  | ].


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

Lemma xlet_lemma : forall A1 (EA1:Enc A1) H `{EA:Enc A} (Q:A->hprop) (F1:Formula) (F2of:forall `{EA1:Enc A2},A2->Formula),
  H ==> ^F1 (fun (X:A1) => ^(F2of X) Q) -> 
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
Proof using. introv M. unfold Wptag, Wpgen_cast. xchanges~ M. Qed.

Ltac xcast_core tt :=
  xcast_pre tt;
  applys xcast_lemma.

Tactic Notation "xcast" :=
  xcast_core tt.


(* ---------------------------------------------------------------------- *)
(* ** Tactic [xpost] *)

Lemma xpost_lemma : forall `{EA:Enc A} (Q1 Q2:A->hprop) H (F:Formula),
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
   is a [Wpgen_app] goal. *)

Ltac xapp_pre tt :=
  xlet_xseq_xcast_repeat tt; 
  match xgoal_code_without_wptag tt with
  | (Wpgen_app _) => idtac 
  end.

Ltac xapp_post tt :=
  xsimpl; unfold protect; xcleanup.

Lemma xapp_find_spec_lemma : forall A `{EA:Enc A} (Q1:A->hprop) t H1 H Q,
  Triple t H1 Q1 ->
  (Triple t H1 Q1 -> H ==> ^(Wpgen_app t) Q) ->
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
  xapp_pre tt;
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


Ltac xapp_debug_intro tt :=
  let H := fresh "Spec" in
  intro H. 

Tactic Notation "xapp_debug" :=
  applys @xapp_lemma; [ xspec; xapp_debug_intro tt | ].

Tactic Notation "xapp_debug" constr(E) :=
  applys @xapp_lemma; [ xspec_lemma_of_args E; xapp_debug_intro tt | ].

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
(* ** Tactic [xval] *)

Lemma xval_lemma : forall `{EA:Enc A} (V:A) v H (Q:A->hprop),
  v = ``V ->
  H ==> Q V ->
  H ==> ^(Wpgen_val v) Q.
Proof using. introv E N. subst. applys MkStruct_erase. xsimpl~ V. Qed.

(* NEEDED? *)
Lemma xval_lemma_val : forall `{EA:Enc A} (V:A) v H (Q:val->hprop),
  v = ``V ->
  H ==> Q (``V) ->
  H ==> ^(Wpgen_val v) Q.
Proof using. introv E N. subst. applys MkStruct_erase. xsimpl~ (``V). Qed.

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
  applys @xval_lemma; [ try reflexivity | ];
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
  end;
  match xgoal_code_without_wptag tt with
  | (Wpgen_if_case _ _ _) => idtac
  end.

Lemma xifval_lemma : forall `{EA:Enc A} b H (Q:A->hprop) (F1 F2:Formula),
  (b = true -> H ==> ^F1 Q) ->
  (b = false -> H ==> ^F2 Q) ->
  H ==> ^(Wpgen_if_case b F1 F2) Q.
Proof using. introv E N. applys MkStruct_erase. case_if*. Qed.

Lemma xifval_lemma_isTrue : forall `{EA:Enc A} (P:Prop) H (Q:A->hprop) (F1 F2:Formula),
  (P -> H ==> ^F1 Q) ->
  (~ P -> H ==> ^F2 Q) ->
  H ==> ^(Wpgen_if_case (isTrue P) F1 F2) Q.
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
  H ==> ^(Wpgen_case (fun `{EA1:Enc A1} (Q:A1->hprop) => \[P1] \-* ^F1 Q) P2 F2) Q.
Proof using. 
  introv M1 M2. applys* xcase_lemma. { applys* hwand_hpure_r_intro. }
Qed.

Lemma xcase_lemma2 : forall (F1:val->val->Formula) (P1:val->val->Prop) (P2:Prop) F2 H `{EA:Enc A} (Q:A->hprop),
  (forall x1 x2, P1 x1 x2 -> H ==> ^(F1 x1 x2) Q) ->
  (P2 -> H ==> ^F2 Q) ->
  H ==> ^(Wpgen_case (fun `{EA1:Enc A1} (Q:A1->hprop) => \forall x1 x2, \[P1 x1 x2] \-* ^(F1 x1 x2) Q) P2 F2) Q.
Proof using. 
  introv M1 M2. applys* xcase_lemma.
  { repeat (applys himpl_hforall_r ;=> ?). applys* hwand_hpure_r_intro. }
Qed.


Lemma xmatch_lemma_list : forall `{EA:Enc A} (L:list A) (F1:Formula) (F2:val->val->Formula) H `{HB:Enc B} (Q:B->hprop),
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
(* ** Tactic [xreturn] --- NEEDED? *)

Lemma xreturn_lemma_typed : forall `{Enc A1} (F:(A1->hprop)->hprop) (Q:A1->hprop) H,
  H ==> F Q ->
  H ==> ^(Formula_cast F) Q.
Proof using.
  introv M. unfold Formula_cast. xsimpl* Q. applys RetypePost_refl.
Qed.

Lemma xreturn_lemma_val : forall `{Enc A1} (F:(A1->hprop)->hprop) (Q:val->hprop) H,
  H ==> F (fun (X:A1) => Q (enc X)) ->
  H ==> ^(Formula_cast F) Q.
Proof using.
  introv M. unfold Formula_cast. xsimpl* Q.
  unfold RetypePost. intros X. xsimpl* X.
Qed.



(* ********************************************************************** *)
(* Others *)

Lemma eliminate_eta_in_code : forall `{EA:Enc A} H1 (Q1:A->hprop) (F1:Formula),
    (PRE H1
    CODE F1
    POST Q1)
  ->
    (PRE H1
    CODE (fun (A0 : Type) (EA0 : Enc A0) (Q : A0 -> hprop) => F1 A0 EA0 Q)
    POST Q1).
Proof using. introv M. xchanges M. Qed.



(* ********************************************************************** *)

(* TODO: decode typeclass *)

(* LATER: xif automates xapp *)
