Set Implicit Arguments.
From CFML Require Import WPLib.

Notation "'int'" := (Z%type).


(********************************************************************)
(** ** Addition for other files *)

Lemma hand_weaken : forall H1 H2 H1' H2',
  H1 ==> H1' ->
  H2 ==> H2' ->
  hand H1 H2 ==> hand H1' H2'.
Proof using.
  introv M1 M2. do 2 rewrite hand_eq_forall_bool.
  applys himpl_hforall_r. intros b. applys himpl_hforall_l b.
  case_if*.
Qed.

Lemma hwand_weaken : forall H1 H2 H1' H2',
  H1' ==> H1 ->
  H2 ==> H2' ->
  (H1 \-* H2) ==> (H1' \-* H2').
Proof using. introv M1 M2. xsimpl. xchanges* M1. Qed.

Lemma himpl_hwand_hpure_l : forall (P:Prop) H1 H2,
  P ->
  H1 ==> H2 ->
  (\[P] \-* H1) ==> H2.
Proof using. introv HP M. rewrite* hwand_hpure_l. Qed.

Lemma himpl_hwand_hpure_r : forall (P:Prop) H H',
  (P -> H ==> H') ->
  H ==> (\[P] \-* H').
Proof using. introv M. xsimpl*. Qed.


Lemma mkstruct_erase_trans : forall A (Q:A->hprop) H f,
  H ==> f Q ->
  H ==> mkstruct f Q.
Proof using. introv M. unfold mkstruct. xchanges M. Qed.


Lemma MkStruct_erase_l_Post : forall (F1:Formula) A (EA:Enc A) (Q:A->hprop) (f2:formula),
  structural f2 ->
  (forall A1 (EA1:Enc A1) (Q1:A1->hprop), ^F1 Q1 ==> f2 (Post Q1)) ->
  ^(MkStruct F1) Q ==> f2 (Post Q).
Proof using.
  introv HS M1. unfold MkStruct.
  rewrites~ (>> eq_mkstruct_of_structural f2).
  unfold mkstruct. xpull. intros Q'. xchange M1. xsimpl.
  intros x. unfold Post. xpull. intros V E. xsimpl*.
Qed.



(********************************************************************)
(** ** Lifted *)

Lemma triple_apps_funs' : forall F vs ts xs t H (Q:val->hprop),
  F = val_funs xs t ->
  trms_to_vals ts = Some vs ->
  var_funs_exec xs (length vs) ->
  H ==> (wpgen (LibListExec.combine xs vs) t) (Q \*+ \GC) ->
  triple (trm_apps F ts) H Q.
Proof using.
  introv HF Hvs Hxs M. applys triple_hgc_post. lets ->: trms_to_vals_spec Hvs.
  rewrite var_funs_exec_eq in Hxs. rew_istrue in Hxs. lets (_&Lxs&_): Hxs.
  rewrite LibListExec.combine_eq in M; auto. (* rew_list_exec in M. *)
  applys* triple_apps_funs. rewrite~ <- isubstn_eq_substn.
  applys* triple_isubst_of_wpgen.
Qed.

Lemma triple_apps_fixs' : forall F vs ts xs t H (Q:val->hprop) (f:var),
  F = val_fixs f xs t ->
  trms_to_vals ts = Some vs ->
  var_fixs_exec (bind_var f) xs (length vs) ->
  H ==> (wpgen (LibListExec.combine (f::xs) (F::vs)) t) (Q \*+ \GC) ->
  triple (trm_apps F ts) H Q.
Proof.
  introv HF Hvs Hxs M. applys triple_hgc_post. lets ->: trms_to_vals_spec Hvs.
  rewrite var_fixs_exec_eq in Hxs. rew_istrue in Hxs. lets (_&Lxs&_): Hxs.
  rewrite LibListExec.combine_eq in M; rew_list; auto. (* rew_list_exec in M. *)
  applys* triple_apps_fixs. rewrite <- isubstn_eq_substn; [|rew_list~].
  applys* triple_isubst_of_wpgen.
Qed.
(* LATER: simplify proof of xwp_lemma_fixs using the above *)


Definition Lifted (F1:Formula) (f1:formula) : Prop :=
  forall A (EA:Enc A) (Q:A->hprop), ^F1 Q ==> f1 (Post Q).

Lemma Lifted_intro : forall (F1:Formula) (f1:formula) A (EA:Enc A) (Q:A->hprop),
  Lifted F1 f1 ->
  ^F1 Q ==> f1 (Post Q).
Proof using. auto. Qed.

Lemma Lifted_intro_gc : forall (F1:Formula) (f1:formula) A (EA:Enc A) (Q:A->hprop),
  Lifted F1 f1 ->
  ^F1 (Q \*+ \GC) ==> f1 (Post Q \*+ \GC).
Proof using.
  introv M1. unfolds Lifted. xchange M1. rewrite Post_star. xsimpl.
Qed.

Transparent Triple.

Lemma Lifted_wp : forall t,
  Lifted (Wp t) (wp t).
Proof using.
  intros. hnf. intros. unfold wp, Wp, Weakestpre, Triple.
  applys himpl_refl.
Qed.

Lemma Lifted_mkstruct : forall F1 f1,
  Lifted F1 f1 ->
  Lifted (MkStruct F1) (mkstruct f1).
Proof using.
  introv M. hnf. intros.
  applys MkStruct_erase_l_Post. applys structural_mkstruct.
  intros. applys himpl_trans; [ | eapply mkstruct_erase ]. applys M.
Qed.

Lemma Lifted_inv : forall F f A {EA:Enc A} (Q:A->hprop) q,
  Lifted F f ->
  (Post Q) ===> q ->
  structural f ->
  ^F Q ==> f q.
Proof using.
  introv M W S. xchange M. applys* structural_conseq W.
Qed.

Lemma Lifted_let : forall F1 f1 A1 {EA1:Enc A1} (F2of:A1->Formula) f2of,
  (Lifted F1 f1) ->
  (forall (X:A1), Lifted (F2of X) (f2of (enc X))) ->
  structural f1 ->
  Lifted (Wpgen_let_trm F1 F2of) (wpgen_let f1 f2of).
Proof using.
  introv M1 M2 S1.
  hnf. intros. applys Lifted_mkstruct. clears A.
  hnf. intros. xpull. intros Q1 HQ1. applys* Lifted_inv M1.
  intros x. unfold Post at 1. xpull. intros X1 ->.
  xchange HQ1. applys M2.
Qed.

Lemma Lifted_seq : forall F1 f1 (F2:Formula) f2of,
  (Lifted F1 f1) ->
  (Lifted F2 (f2of val_unit)) ->
  structural f1 ->
  Lifted (Wpgen_seq F1 F2) (wpgen_let f1 f2of).
Proof using.
  introv M1 M2 S1.
  forwards* R: Lifted_let (fun (_:unit) => F2) f2of M1 S1.
  { intros []. rewrite* enc_unit. }
  unfolds Lifted. intros. applys himpl_trans; [ | applys R].
  unfold Wpgen_seq. unfolds Wpgen_let_trm. applys mkstruct_weaken.
  intros Q'. xsimpl. intros Q1 R1. intros []. auto.
Qed.

Lemma var_funs_exec_eq : forall (b:bool) (P:Prop),
  b = isTrue P -> b = true -> P.
Proof using. intros. subst. rewrite isTrue_eq_true_eq in H0. auto. Qed.

Lemma Lifted_app : forall (A:Type) {EA:Enc A} (f:val) (Vs:dyns) (vs:vals),
  LibList.map (fun V => trm_val (dyn_to_val V)) Vs = trms_vals vs ->
  Lifted (@Wpgen_app A EA f Vs) (wpgen_app f vs).
Proof using.
  introv E. hnf. intros.
  unfolds Wpgen_app, wpgen_app.
  applys Lifted_mkstruct.
  unfold Trm_apps. rewrite <- E.
  applys Lifted_wp.
Qed.

Lemma Lifted_let_inlined : forall f1 F2 f2of (r:val),
  structural f1 ->
  \[] ==> f1 (fun x => \[x = r]) ->
  Lifted F2 (f2of r) ->
  Lifted F2 (wpgen_let_aux f1 f2of).
Proof using.
  introv Sf1 M1 M2. hnf. intros. unfold wpgen_let. applys mkstruct_erase_trans.
  xchange M2. xchange M1. applys* structural_frame. applys* structural_conseq.
  intros x. xsimpl. intros ->. auto.
Qed.


Lemma Lifted_inlined_fun : forall F1 (f:val) (vs:vals) (r:val),
  (triple (trm_apps f vs) \[] (fun x => \[x = r])) ->
  Lifted F1 (wpgen_val r) ->
  Lifted F1 (wpgen_app f vs).
Proof using.
  introv Hf M1. hnf. intros.
  unfold wpgen_app. xchange M1. applys mkstruct_weaken. clear Q. intros Q.
  rewrite <- triple_eq_himpl_wp. applys triple_conseq_frame Hf. xsimpl.
  intros x. xpull. intros ->. xsimpl.
Qed.


Lemma Lifted_if : forall F1 f1 F2 f2 b (v:val),
  v = ``b ->
  (Lifted F1 f1) ->
  (Lifted F2 f2) ->
  Lifted (Wpgen_if b F1 F2) (wpgen_if_val v f1 f2).
Proof using.
  introv E M1 M2.
  hnf. intros. applys Lifted_mkstruct. clears A.
  hnf. intros. subst v. xsimpl b. auto.
  case_if. { applys M1. } { applys M2. }
Qed.



Lemma Triple_of_CF_and_Lifted_funs : forall H A (EA:Enc A) (Q:A->hprop) (F1:Formula) F xs Vs vs t,
  F = val_funs xs t ->
  H ==> ^F1 (Q \*+ \GC) ->
  trms_to_vals (LibList.map (fun V : dyn => trm_val (dyn_to_val V)) Vs) = Some vs ->
  var_funs_exec xs (LibListExec.length vs) ->
  Lifted F1 (wpgen (LibListExec.combine xs vs) t) ->
  Triple (Trm_apps F Vs) H Q.
Proof using.
  introv EF HF1 Evs Hxs Ff. rewrite LibListExec.length_eq in Hxs.
  applys triple_apps_funs' EF Evs Hxs.
  xchange HF1. applys Lifted_intro_gc Ff.
Qed.

Lemma Triple_of_CF_and_Lifted_fixs :
  forall H A (EA:Enc A) (Q:A->hprop) (F1:Formula) F (f:var) xs Vs (vs:vals) t,
  F = val_fixs f xs t ->
  H ==> ^F1 (Q \*+ \GC) ->
  trms_to_vals (LibList.map (fun V : dyn => trm_val (dyn_to_val V)) Vs) = Some vs ->
  var_fixs_exec (bind_var f) xs (LibListExec.length vs) ->
  Lifted F1 (wpgen (LibListExec.combine (f::xs) (F::vs)) t) ->
  Triple (Trm_apps F Vs) H Q.
Proof using.
  introv EF HF1 Evs Hxs Ff. rewrite LibListExec.length_eq in Hxs.
  applys triple_apps_fixs' EF Evs Hxs.
  xchange HF1. applys Lifted_intro_gc Ff.
Qed.

Lemma Lifted_val : forall A (EA:Enc A) (V:A) v,
  v = enc V ->
  Lifted (Wpgen_val V) (wpgen_val v).
Proof using.
  introv M. applys Lifted_mkstruct. hnf. intros A' EA' Q.
  unfold PostCast. xpull. intros V' E.
  unfold Post. xsimpl V'. subst*.
Qed.


Lemma Lifted_let_val : forall A1 (V:A1) {EA1:Enc A1} (F2of:A1->Formula) f1 f2of,
  \[] ==> f1 (fun x => \[x = enc V]) ->
  (forall (X:A1), Lifted (F2of X) (f2of (enc X))) ->
  structural f1 ->
  Lifted (Wpgen_let_val V F2of) (wpgen_let f1 f2of).
Proof using.
  introv M1 M2 S1.
  hnf. intros. applys Lifted_mkstruct. clears A.
  hnf. intros. applys himpl_hforall_l V. applys* himpl_hwand_hpure_l.
  xchange M1. applys* structural_frame.
  applys* structural_conseq. xsimpl. intros ? ->. applys M2.
Qed.

Lemma Lifted_case : forall F1 f1 F2 f2 (P1 P2:Prop),
  (P2 -> P1) ->
  (Lifted F1 f1) ->
  (P1 -> Lifted F2 f2) ->
  Lifted (Wpgen_case F1 P1 F2) (wpgen_case_val f1 P2 f2).
Proof using.
  introv HP M1 M2.
  hnf. intros. applys Lifted_mkstruct. clears A.
  hnf. intros. applys hand_weaken.
  { applys M1. }
  { xsimpl. intros HP2. lets HP1: HP HP2.
    applys himpl_hwand_hpure_l.
    { applys* HP. } { applys* M2. } }
Qed.

Lemma Lifted_fail :
  Lifted Wpgen_fail wpgen_fail.
Proof using.
  hnf. intros. applys Lifted_mkstruct. clears A.
  hnf. intros. xsimpl.
Qed.

Lemma Lifted_fail_false : forall F,
  False ->
  Lifted F wpgen_fail.
Proof using. intros. false. Qed.


Definition CF_matcharg A {EA:Enc A} (V:A) : Prop :=
  True.


Lemma Lifted_match : forall A {EA:Enc A} (V:A) F1 f1 F2 f2 (P1 P2:Prop),
  (CF_matcharg V -> Lifted (Wpgen_case F1 P1 F2) (wpgen_case_val f1 P2 f2)) ->
  Lifted (Wpgen_match V (Wpgen_case F1 P1 F2)) (wpgen_case_val f1 P2 f2).
Proof using. introv M. applys M. hnfs*. Qed.


(* TODO: support trm_seq in wpbase *)



(********************************************************************)
(** ** Primitive ops *)

(* Spec of record initialization *)

Fixpoint record (L:list(field*val)) (r:loc) : hprop :=
  match L with
  | nil => hheader 0 r
  | (f,v)::L' => (r`.f ~~~> v) \* (r ~> record L')
  end.




(********************************************************************)

Ltac xwpgen_simpl := (* LATER: List.fold_right *)
  cbn beta delta [
  LibListExec.app LibListExec.combine LibListExec.rev LibListExec.map
  Datatypes.app List.combine List.rev List.fold_right List.map
  wpaux_var
  (* wpgen Wpaux_apps Wpaux_constr Wpaux_var Wpaux_match *)
  hforall_vars forall_vars
  trm_to_pat patvars patsubst combiner_to_trm
  Ctx.app Ctx.empty Ctx.lookup Ctx.add Ctx.rev
  Ctx.rem Ctx.rem_var Ctx.rem_vars Ctx.combine isubst
  var_eq eq_var_dec
  string_dec string_rec string_rect
  sumbool_rec sumbool_rect
  Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
  Bool.bool_dec bool_rec bool_rect ] iota zeta.

Ltac cf_main :=
  let CF := fresh "CF" in
  hnf; introv CF;
  let A := match goal with |- @Triple ?t ?A ?EA ?H ?Q => constr:(A) end in
  first [ applys Triple_of_CF_and_Lifted_funs (rm CF);
          [ reflexivity | try reflexivity | try reflexivity | ]
        | applys Triple_of_CF_and_Lifted_fixs (rm CF);
          [ reflexivity | try reflexivity | try reflexivity | ] ];
  clears A; unfold Wptag, dyn_to_val; simpl; xwpgen_simpl.

Lemma triple_builtin_search_1 : forall F ts v1 H (Q:val->hprop),
  triple (combiner_to_trm (combiner_nil (trm_val F) (trm_val v1))) H Q ->
  combiner_to_trm (combiner_nil (trm_val F) (trm_val v1)) = (trm_apps (trm_val F) ts) ->
  triple (trm_apps (trm_val F) ts) H Q.
Proof using. introv M <-. auto. Qed.

Lemma triple_builtin_search_2 : forall F ts v1 v2 H (Q:val->hprop),
  triple (combiner_to_trm (combiner_cons (combiner_nil (trm_val F) (trm_val v1)) (trm_val v2))) H Q ->
    combiner_to_trm (combiner_cons (combiner_nil (trm_val F) (trm_val v1)) (trm_val v2))
  = (trm_apps (trm_val F) ts) ->
  triple (trm_apps (trm_val F) ts) H Q.
Proof using. introv M <-. auto. Qed.


Ltac cf_triple_builtin :=
  first [ eapply triple_builtin_search_2; [  eauto with triple_builtin | reflexivity ]
        | eapply triple_builtin_search_1; [  eauto with triple_builtin | reflexivity ] ].

Ltac xpull_himpl_hforall_r :=
  repeat match goal with
  | |- ?H1 ==> ?H2 =>
    match H2 with
    | \forall _, _ => eapply himpl_hforall_r; intro
  end end.

Ltac xsimpl_himpl_hforall_l :=
  repeat match goal with
  | |- ?H1 ==> ?H2 =>
    match H1 with
    | \forall _, _ => eapply himpl_hforall_l
  end end.


(** [cf_struct] removes the leading [mkstruct]. *)

Lemma cf_struct_lemma : forall F H (Q:val->hprop),
  H ==> F Q ->
  H ==> mkstruct F Q.
Proof using. introv M. xchange M. applys mkstruct_erase. Qed.

Tactic Notation "cf_struct" :=
  applys cf_struct_lemma.


(** [cf_truct_if_needed] removes the leading [mkstruct] if there is one. *)

Tactic Notation "cf_struct_if_needed" := (* NEEDED? *)
  try match goal with |- ?H ==> mkstruct ?F ?Q => cf_struct end.


(** [cf_inlined_if_needed] *)


Lemma himpl_wpgen_let_aux : forall v1 f1 f2of Q,
  structural f1 ->
  \[] ==> f1 (fun r => \[r = v1]) ->
  \[] ==> f2of v1 Q ->
  \[] ==> wpgen_let_aux f1 f2of Q.
Proof using.
  introv S1 M1 M2. applys cf_struct_lemma. xchange M1.
  applys* structural_conseq. xchanges M2. intros ? ->. auto.
Qed.

Lemma himpl_wpgen_app : forall (f:val) (vs:vals) Q,
  triple (trm_apps f vs) \[] Q ->
  \[] ==> wpgen_app f vs Q.
Proof using.
  introv M1. applys cf_struct_lemma. rewrite* <- triple_eq_himpl_wp.
Qed.

Lemma himpl_wpgen_val_constr : forall (v:val),
  \[] ==> wpgen_val v (fun x => \[x = v]).
Proof using. intros. apply cf_struct_lemma. xsimpl*. Qed.

Ltac cf_inlined_compute :=
  match goal with |- \[] ==> ?H =>
  match H with
  | wpgen_let_aux ?f1 ?f2of ?Q =>
      eapply himpl_wpgen_let_aux; [ applys structural_mkstruct
                                  | try cf_inlined_compute
                                  | try cf_inlined_compute ]
  | wpgen_app ?f ?vs ?Q =>
      eapply himpl_wpgen_app; try cf_triple_builtin
  | wpgen_val ?v ?Q =>
      apply himpl_wpgen_val_constr
  end end.

Ltac cf_inlined :=
  eapply Lifted_let_inlined; [ applys structural_mkstruct | try cf_inlined_compute | ].

Ltac cf_inlined_app :=
  eapply Lifted_inlined_fun; [ try cf_triple_builtin | ].

Ltac cf_inlined_if_needed :=
  repeat match goal with
  | |- Lifted ?F (wpgen_let_aux ?f1 ?f2of) => cf_inlined
  | |- Lifted (Wpgen_val ?V) (wpgen_app ?f ?vs) => cf_inlined_app
  end.


(* Others *)

Ltac cf_let :=
  cf_inlined_if_needed;
  eapply Lifted_let; [ | | applys structural_mkstruct ].

Ltac cf_val :=
  cf_inlined_if_needed;
  eapply Lifted_val; [ try solve [ reflexivity | fequals ] ].
  (* fequals needed to force evaluation of opaque encoders *)

Ltac cf_letval :=
  cf_inlined_if_needed;
  eapply Lifted_let_val;
    [ try cf_inlined_compute | | applys structural_mkstruct ].

Ltac cf_app_core :=
  eapply Lifted_app; [ reflexivity ].

Ltac cf_let_app :=
  cf_let; [ cf_app_core | intros ? ].

Ltac cf_app :=
  match goal with
  | |- Lifted (Wpgen_let_trm _ _) _ => cf_let_app
  | |- _ => cf_inlined_if_needed; cf_app_core
  end.

(*
Ltac cf_letinlined :=
  eapply Lifted_let_inlined_fun; [ try cf_triple_builtin | ].
*)

Ltac cf_if :=
  cf_inlined_if_needed;
  eapply Lifted_if; [ reflexivity | | ].

Ltac cf_case_negpat_eq H :=
  unfold Wpgen_negpat; intros; intros ->; eapply H; reflexivity.

Ltac cf_case_destruct :=
  let V := match goal with H: CF_matcharg ?V |- _ => constr:(V) end in
  destruct V.

Ltac cf_case_eq_end :=
  xsimpl_himpl_hforall_l;
  applys himpl_hwand_hpure_l;
  [ reflexivity | try apply Lifted_intro ].

Ltac cf_case_eq :=
  let A := fresh "A" in
  let EA := fresh "EA" in
  let Q := fresh "Q" in
  let E := fresh "__MatchEq" in
  hnf; intros A EA Q;
  xpull_himpl_hforall_r;
  eapply himpl_hwand_hpure_r; intros E;
  cf_case_destruct; inverts E;
  try cf_case_eq_end.

Ltac cf_case :=
  let H := fresh "__MatchHyp" in
  eapply Lifted_case;
  [ intros H; try solve [ cf_case_negpat_eq H ]
  | try cf_case_eq
  | intros H ].

Ltac cf_fail :=
  first [ eapply Lifted_fail
        | eapply Lifted_fail_false ].

Ltac cf_match :=
  cf_inlined_if_needed;
  let H := fresh "__MatchArg" in
  eapply Lifted_match; intros H.

Ltac cf_match_fail :=
  cf_fail;
  match goal with H: CF_matcharg ?V |- _ =>
    destruct V; tryfalse; eauto end.

Transparent Enc_list Enc_pair Enc_option.

Ltac cf_inlined' :=
  cf_inlined; [ applys cf_struct_lemma; xsimpl; reflexivity | ].

Ltac cf_seq :=
  cf_inlined_if_needed;
  eapply Lifted_seq; [ | | applys structural_mkstruct ].


Lemma record_to_Record : forall (Lup:Record_fields) (fields:fields) (values:vals) p,
  List.length fields = List.length Lup ->
  List.length fields = List.length values ->
  List.map (fun '(f,_) => f) Lup = fields ->
  List.map enc (List.map (fun '(_,d) => dyn_to_val d) Lup) = values ->
  p ~> record (List.combine fields values) ==> p ~> Record Lup.
Proof using. (* LATER: inline in other proof below? *)
  introv M1 M2 E1 E2. repeat rewrite repr_eq. gen values Lup.
  induction fields as [|F fields']; intros;
   destruct values as [|v values']; simpls; tryfalse;
   destruct Lup as [|[f' [A EA V]] Lup']; simpls; tryfalse.
  { auto. }
  { Transparent Record. simpl. asserts_rewrite (F = f'). { inverts* E1. }
    unfold Hfield. repeat rewrite repr_eq. rewrite dyn_to_val_dyn_make in E2.
    asserts_rewrite (v = enc V). { inverts* E2. } xsimpl.
    applys* IHfields'. inverts* E1. inverts* E2. }
Qed.

Axiom triple_record_init : forall fields values,
  List.length fields = List.length values ->
  triple (trm_apps (val_record_init fields) (trms_vals values)) \[]
    (fun (r:val) => \exists p, \[r = val_loc p] \* p ~> record (List.combine fields values)).

Lemma Lifted_new : forall (Lup:Record_fields) (fields:fields) (values:vals),
  List.length fields = List.length Lup ->
  List.length fields = List.length values ->
  List.map (fun '(f,_) => f) Lup = fields ->
  List.map enc (List.map (fun '(_,d) => dyn_to_val d) Lup) = values ->
  Lifted (Wpgen_record_new (fun _ : loc => Lup)) (wpgen_app ((val_record_init fields)) values).
Proof using.
  introv E1 E2 M1 M2.
  hnf. intros. unfold Wpgen_record_new, wpgen_app.
  applys Lifted_mkstruct. clears A. hnf. intros. rewrite <- triple_eq_himpl_wp.
  applys triple_conseq_frame. applys* triple_record_init. xsimpl.
  xsimpl. intros r p ->. xchange* record_to_Record.
  xchange (qwand_specialize p). unfold Post, PostCast. xsimpl*.
Qed.


Ltac cf_new :=
  cf_inlined_if_needed;
  eapply Lifted_new; [ try reflexivity | try reflexivity | try reflexivity | try reflexivity ].
  (* eapply Lifted_new2; [ try reflexivity | try reflexivity | try reflexivity | try reflexivity | try reflexivity ]. *)




(********************************************************************)
(********************************************************************)
(********************************************************************)

(* DEPRECATED

(** [cf_val] proves a [H ==> wgpen_val Q], instantiate the postcondition if needed *)

Lemma cf_val_lemma : forall v H (Q:val->hprop),
  H ==> Q v ->
  H ==> wpgen_val v Q.
Proof using. introv M. unfold wpgen_val. applys* cf_struct_lemma. Qed.

Lemma cf_val_lemma_inst : forall H v,
  H ==> wpgen_val v (fun x => \[x = v] \* H).
Proof using. intros. applys cf_val_lemma. xsimpl*. Qed.

Tactic Notation "cf_val_inlined" :=
  cf_struct_if_needed; first
  [ eapply cf_val_lemma_inst
  | eapply cf_val_lemma ].

(** [cf_let_aux] proves a [H ==> wgpen_val_aux Q] *)

Lemma cf_let_aux_lemma : forall H F1 F2of Q,
  H ==> F1 (fun v => F2of v Q) ->
  H ==> wpgen_let_aux F1 F2of Q.
Proof using. introv M. applys* cf_struct_lemma. Qed.

Tactic Notation "cf_let_inlined" :=
  eapply cf_let_aux_lemma.

*)



(********************************************************************)
(********************************************************************)
(********************************************************************)


(* DEPRECATED

Lemma cf_app_lemma : forall t Q1 H1 H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  H ==> wp t Q.
Proof using.
  introv M W. rewrite triple_eq_himpl_wp in M. xchange W. xchange M.
  applys structural_elim_nohgc. { applys structural_wp. } { xsimpl. }
  (*  applys wp_ramified_frame. *)
Qed.


Lemma cf_apps_lemma_pure : forall (t:trm) (v:val) H Q,
  triple t \[] (fun r => \[r = v]) ->
  H ==> Q v ->
  H ==> wp t Q.
Proof using.
  introv M1 M2. applys cf_app_lemma M1. xchanges M2. intros ? ->. auto.
Qed.

Lemma cf_apps_lemma_pure_inst : forall (t:trm) (v:val),
  triple t \[] (fun r => \[r = v]) ->
  \[] ==> wp t (fun r => \[r = v]).
Proof using.
  introv M1. applys cf_apps_lemma_pure M1. xsimpl*.
Qed.


(** [cf_app_simpl] performs the final step of the tactic [xapp]. *)

Lemma cf_app_simpl_lemma : forall F H (Q:val->hprop),
  H ==> F Q ->
  H ==> F Q \* (Q \--* protect Q).
Proof using. introv M. xchange M. unfold protect. xsimpl. Qed.

Tactic Notation "cf_app_simpl" :=
  first [ applys cf_app_simpl_lemma (* handles specification coming from [xfun] *)
        | xsimpl; unfold protect (*; xapp_try_clear_unit_result *) ].

(*Tactic Notation "cf_app_pre" :=
  xtriple_if_needed; xseq_xlet_if_needed; xstruct_if_needed. *)

Tactic Notation "cf_app_apply_spec" :=
  first [ solve [ eauto with triple ]
        | match goal with H: _ |- _ => eapply H end ].

(** [xapp] first calls [xtriple] if the goal is [triple t H Q] instead
    of [H ==> wp t Q]. *)

Tactic Notation "cf_app_nosubst" :=
  applys cf_app_lemma; [ cf_app_apply_spec | cf_app_simpl ].

(** [cf_app_try_subst] checks if the goal is of the form:
    - either [forall (r:val), (r = ...) -> ...]
    - or [forall (r:val), forall x, (r = ...) -> ...]

    in which case it substitutes [r] away. *)

Tactic Notation "cf_app_try_subst" :=
  try match goal with
  | |- forall (r:val), (r = _) -> _ => intros ? ->
  | |- forall (r:val), forall x, (r = _) -> _ =>
      let y := fresh x in intros ? y ->; revert y
  end.


Tactic Notation "cf_app" :=
  cf_inlined_if_needed;
  cf_app_nosubst;
  cf_app_try_subst.

Tactic Notation "cf_apps" :=
  cf_inlined_if_needed;
  first [ eapply cf_apps_lemma_pure_inst
        | eapply cf_apps_lemma_pure; [ cf_app_apply_spec |  ] ].


*)





(********************************************************************)
(********************************************************************)
(********************************************************************)

(* DEPRECATED? *)

(********************************************************************)
(** ** Interactive debugging of missing hyps *)

Definition CF_hyps (Ps:list Prop) :=
  LibList.fold_right Logic.and True Ps.

Lemma cf_begin_lemma : forall (P:Prop) (Ps:list Prop),
  (CF_hyps Ps -> P) ->
  CF_hyps Ps ->
  P.
Proof using. intros. unfold CF_hyps. auto. Qed.

Ltac cf_begin :=
  eapply cf_begin_lemma.

Lemma cf_end_lemma :
  CF_hyps nil.
Proof using. hnf. rew_listx. auto. Qed.

Ltac cf_debug :=
  unfold CF_hyps; rew_listx; splits; try solve [eapply cf_end_lemma].

Ltac cf_end name :=
  first
  [ eapply cf_end_lemma (* when all cf_tactics succeeded *)
  | idtac "Error: incomplete proof for" name;
    idtac "Replace cf_end with cf_debug to see the goals";
    cf_debug; skip ].

Lemma cf_error_lemma : forall (Ps:list Prop) (P:Prop),
  CF_hyps Ps ->
  (CF_hyps Ps -> P) ->
  P.
Proof using. auto. Qed.

Ltac cf_error_extend P R2 Ps :=
  match Ps with
  | ?Pi :: ?Ps' =>
      let Ps'2 := cf_error_extend P Ps' in
      constr:(Pi::Ps'2)
  | _ => constr:(P::R2)
  end.

Ltac cf_error :=
  match goal with H: CF_hyps ?Ps |- ?P =>
    let R2 := fresh in
    evar (R2 : list Prop);
    let Ps2 := cf_error_extend P R2 Ps in
    eapply (@cf_error_lemma Ps2 P H);
    subst R2 ; unfold CF_hyps; rew_listx; solve [ intuition ]
  end.

Ltac cf_step cont :=
  first [ cont tt
        | cf_error ].


(* DEMO

Lemma cf_error_demo : True /\ False /\ True.
  cf_begin; [ intros CCFHyps | ].
  { splits.
    { cf_step ltac:(fun tt => split). }
    { cf_step ltac:(fun tt => split). (* cf_error. *) }
    { cf_step ltac:(fun tt => split). } }
  { (* cf_end "foo". *)
    cf_debug. skip. }
Qed.

Lemma cf_error_demo' : True /\ False /\ True.
  cf_begin;
  [ intros CCFHyps;
    splits;
    [ cf_step ltac:(fun tt => split)
    | cf_step ltac:(fun tt => split) (* cf_error. *)
    | cf_step ltac:(fun tt => split) ]
  | cf_end "foo" (* cf_debug *) ].
Qed.

*)


(********************************************************************)
(********************************************************************)
(********************************************************************)

(* DEPRECATED *)
(*
Lemma Lifted_let_inlined_let : forall F2 f2of (f:val) (vs:vals) (r:val),
  (triple (trm_apps f vs) \[] (fun x => \[x = r])) ->
  Lifted F2 (f2of r) ->
  Lifted F2 (wpgen_let (wpgen_app f vs) f2of).
Proof using.
  introv Hf M2.
  applys Lifted_let_inlined r.
  { applys structural_mkstruct. }
  { unfold wpgen_app. applys mkstruct_erase_trans.
    rewrite <- triple_eq_himpl_wp.
    applys triple_conseq_frame Hf.
    { xsimpl. } { xpull. intros x ->. xsimpl*. } }
  { applys M2. }
Qed.
Lemma Lifted_let_inlined : forall f1 F2 f2of (r:val) (Q1:val->hprop),
  structural f1 ->
  \[] ==> f1 Q1 ->
  Q1 ===> (fun x => \[x = r]) ->
  (Lifted F2 (f2of r)) ->
  Lifted F2 (wpgen_let_aux f1 f2of).
Proof using.
*)
(*
  Q1 ==> \exists (A:Type) (EA:Enc A) (V:A), @Post A EA (fun (X:A) => \[X = V])
          \* ( Lifted F2 (f2of r)) ->
  Lifted F2 (wpgen_let_aux f1 f2of).*)

(* DEPRECATED
Lemma Lifted_let_inlined_fun : forall F2 f2of (f:val) (vs:vals) (r:val),
  (triple (trm_apps f vs) \[] (fun x => \[x = r])) ->
  Lifted F2 (f2of r) ->
  Lifted F2 (wpgen_let_aux (wpgen_app f vs) f2of).
Proof using.
  introv Hf M2.
  applys Lifted_let_inlined r.
  { applys structural_mkstruct. }
  { unfold wpgen_app. applys mkstruct_erase_trans.
    rewrite <- triple_eq_himpl_wp.
    applys triple_conseq_frame Hf.
    { xsimpl. } { xpull. intros x ->. xsimpl*. } }
  { applys M2. }
Qed.
*)
(*
Wpgen_let_trm (Wpgen_app int infix_emark__ ((Dyn r) :: nil))
  (fun x0__ : int => Wpgen_app unit infix_colon_eq__ ((Dyn r) :: (Dyn x0__ + n) :: nil)) EA
  (Q \*+ \GC) ==>
wpgen_let (wpgen_app infix_emark__ ``[ r])
  (fun X : val =>
   wpgen_let (wpgen_app infix_plus__ (X :: ``[ n]))
     (fun v1 : val => wpgen_app infix_colon_eq__ (``r :: v1 :: nil))) (Post Q \*+ \GC)
*)


(*
Axiom triple_app_fix_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fix f x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.
*)

(*
From TLC Require Import LibListExec.
*)


(*
Lemma Lifted_wp' : forall t t',
  t = t' ->
  Lifted (Wp t) (wp t').
Proof using.
  introv ->. applys* Lifted_wp.
Qed.
*)


(*
Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := mkstruct (fun Q =>
  F1 (fun X => F2of X Q)).

Definition Wpgen_let_trm (F1:Formula) A1 {EA1:Enc A1} (F2of:A1->Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) (Q:A->hprop) =>
    \exists (Q1:A1->hprop), ^F1 Q1 \* \[forall (X:A1), Q1 X ==> ^(F2of X) Q]).
*)


(* LATER
Lemma Lifted_new2 : forall (Lup:Record_fields) (fields:fields) (values:vals),
  List.length fields = 2%nat ->
  List.length Lup = 2%nat ->
  List.length values = 2%nat ->
  List.map (fun '(f,_) => f) Lup = fields ->
  List.map enc (List.map (fun '(_,d) => dyn_to_val d) Lup) = values ->
  Lifted (Wpgen_record_new (fun _ : loc => Lup)) (wpgen_app ((val_record_init fields)) values).
Proof using.
  introv E1 E2 E3 M1 M2.
  destruct Lup as [|R1 [|R2 []]]; simpls; tryfalse.
  destruct fields as [|f1 [|f2 []]]; simpls; tryfalse.
  destruct values as [|v1 [|v2 []]]; simpls; tryfalse.
  hnf. intros. unfold Wpgen_record_new, wpgen_app.
  applys Lifted_mkstruct. clears A. hnf. intros. rewrite <- triple_eq_himpl_wp.
  unfold val_record_init. simpl.
  match goal with |- context [ trm_apps ?F _ ] => set (G := F) end.
  set (H0 :=((fun r : loc => r ~~~> (R1 :: R2 :: nil)) \--* PostCast loc Q)).
  set (vs := (v1 :: v2 :: nil)).
 applys triple_apps_funs vs H0 (Post Q). reflexivity.
  { applys var_funs_exec_eq. eapply (var_funs_exec_eq _ _). auto. auto. } (* todo: improve *)
  simpl. repeat case_if.
  applys triple_let. unfold val_record_alloc.
  applys triple_alloc.
eapply triple_conseq_frame.
  eapply  triple_apps_funs.
  applys (>> triple_conseq_frame (fun r : loc => r ~~~> (R1 :: R2 :: nil))).
Qed.
*)

