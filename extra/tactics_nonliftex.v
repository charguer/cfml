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

Ltac xtriple_core tt :=
  xtriple_pre tt;
  first
  [ applys xtriple_lifted_lemma; xwp_xtriple_handle_gc tt
  | applys xtriple_lemma;
    [ simpl combiner_to_trm; rew_trms_vals; reflexivity
    | xwp_xtriple_handle_gc tt ] ].





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


Ltac xapp_general tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_app ?t) => xapp_apply_lemma ltac:(xspec_prove_triple)
  | (Wpgen_App_typed ?T ?f ?Vs) => xapp_apply_lifted_lemma ltac:(xspec_prove_triple)
  end.

  Ltac xapp_arg_core E :=
  xapp_pre tt;
  let cont := ltac:(fun tt => xspec_prove_triple_with_args E) in
  match xgoal_code_without_wptag tt with
  | (Wpgen_app ?t) =>  xapp_apply_lemma cont
  | (Wpgen_App_typed ?T ?f ?Vs) => xapp_apply_lifted_lemma cont
  end.


Ltac xapp_nosubst_core tt :=
  xapp_pre tt;
  let L := match xgoal_code_without_wptag tt with
    | (Wpgen_app ?t) => constr:(@xapp_lemma)
    | (Wpgen_App_typed ?T ?f ?Vs) => constr:(@xapp_lifted_lemma)
    end in
  applys L; [ xspec_prove_triple tt | xapp_post tt ].



Lemma xapp_find_spec_lemma : forall A `{EA:Enc A} (Q1:A->hprop) (f:trm) (Vs:dyns) H1 H (Q:A->hprop),
  Triple (Trm_apps f Vs) H1 Q1 ->
  (Triple (Trm_apps f Vs) H1 Q1 ->
   H ==> ^(Wpgen_App_typed A f Vs) Q) ->
  H ==> ^(Wpgen_App_typed A f Vs) Q.
Proof using. auto. Qed.

(* ********************************************************************** *)


(* DEPRECATED
Ltac xspec_prove_cont tt :=
  let H := fresh "Spec" in
  intro H; eapply H; clear H.
*)

(* TODO: depreacted? *)
Ltac xspec_prove_cont tt :=
  let H := fresh "Spec" in
  intro H; nrapply H;
  xenc_side_conditions tt;
  try clear H.

(* TODO: depreacted? *)
Ltac xspec_prove_triple tt :=
  xspec;
  xspec_prove_cont tt.

(* TODO: depreacted? *)
Ltac xspec_prove_triple_with_args E :=
  xspec_lemma_of_args E;
  xspec_prove_cont tt.

(* TODO: will be deprecated *)
Notation "'Register_Spec' f" := (Register_goal (Triple (trm_apps (trm_val f) _) _ _))
  (at level 69) : wptactics_scope.

(* ** Specification of primitives *)
(* TODO: will be deprecated *)
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



Lemma xval_lemma_decode : forall A `{EA:Enc A} (V:A) v H (Q:A->hprop),
  Decode v V ->
  H ==> Q V ->
  H ==> ^(Wpgen_val v) Q.
Proof using. introv E N. subst. applys MkStruct_erase. unfold Post_cast_val. xsimpl~ V. Qed.
Ltac xval_pre tt :=
  xlet_xseq_xcast_repeat tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_val _) => idtac
  | (Wpgen_Val _) => idtac
  end.

Ltac xval_core tt :=
  xval_pre tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_val _) => applys @xval_lemma_decode; [ try xdecode | ]
  | (Wpgen_Val _) => applys xval_lifted_lemma
  end;
  xval_post tt.


(* ********************************************************************** *)

Ltac xspec_remove_combiner tt := (* TODO: deprecated *)
  cbn beta delta [ combiner_to_trm ] iota zeta in *.
  xspec_remove_combiner tt;


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
  first [ xlet_core tt
        | xletval ]. (* TODO: document *)

Tactic Notation "xlets" := (* TODO: document *)
  xletvals.

(* ********************************************************************** *)



(** Auxiliary function to obtain the last argument of an application *)

Ltac ltac_get_last_arg E := (* Currently not used *)
  match E with
  | ?F ?X => constr:(X)
  end.
  (* TODO: need to deal with other arities ?*)

(* TODO: DEPRECATED
Notation "'RegisterSpec' f" :=
  (Register_goal (Triple (Trm_apps f _) _ _))
  (at level 69) : wptactics_scope.
*)

(* TODO: will be deprecated *)
Notation "'Register_goal' G" := (Register database_spec G)
  (at level 69) : wptactics_scope.

