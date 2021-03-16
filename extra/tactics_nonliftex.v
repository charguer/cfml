
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
