Set Implicit Arguments.
From CFML Require Import WPLib.
From CFML Require Import Stdlib.
From EXAMPLES Require Import Debug_ml.

(*Close Scope wp_scope.

Notation "'LetX' x ':=' F1 'in' F2" :=
 ( (Wpgen_let_trm F1 (fun x => F2)))
 (in custom wp at level 69,
  only printing,
  x ident,
  F1 custom wp at level 99,
  F2 custom wp at level 99,
  right associativity,
  format "'[v' '[' 'LetX'  x  ':='  F1  'in' ']' '/' '[' F2 ']' ']'").
*)

Notation "'int'" := (Z%type).

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



(********************************************************************)
(** ** Primitive ops *)

Axiom triple_infix_plus__ : forall (n1 n2:int),
  triple (infix_plus__ n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).


Axiom triple_infix_amp_amp__ : forall (b1 b2:bool),
  triple (infix_amp_amp__ b1 b2)
    \[]
    (fun r => \[r = val_bool (b1 && b2)]).

Axiom triple_infix_bar_bar__ : forall (b1 b2:bool),
  triple (infix_bar_bar__ b1 b2)
    \[]
    (fun r => \[r = val_bool (b1 || b2)]).



(********************************************************************)
(** ** Formula_formula *)

(*
Axiom triple_app_fix_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fix f x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.
*)

(*
From TLC Require Import LibListExec.
*)

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


Definition Formula_formula (F1:Formula) (f1:formula) : Prop :=
  forall A (EA:Enc A) (Q:A->hprop), ^F1 Q ==> f1 (Post Q).

Lemma Formula_formula_intro_gc : forall (F1:Formula) (f1:formula) A (EA:Enc A) (Q:A->hprop),
  Formula_formula F1 f1 ->
  ^F1 (Q \*+ \GC) ==> f1 (Post Q \*+ \GC).
Proof using. Admitted.

Transparent Triple.

Lemma Formula_formula_wp : forall t,
  Formula_formula (Wp t) (wp t).
Proof using.
  intros. hnf. intros. unfold wp, Wp, Weakestpre, Triple.
  applys himpl_refl.
Qed.

(*
Lemma Formula_formula_wp' : forall t t',
  t = t' ->
  Formula_formula (Wp t) (wp t').
Proof using.
  introv ->. applys* Formula_formula_wp.
Qed.
*)

Lemma Formula_formula_mkstruct : forall F1 f1,
  Formula_formula F1 f1 ->
  Formula_formula (MkStruct F1) (mkstruct f1).
Proof using.
  introv M. hnf. intros.
  applys MkStruct_erase_l_Post. applys structural_mkstruct.
  intros. applys himpl_trans; [ | eapply mkstruct_erase ]. applys M.
Qed.


(*
Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := mkstruct (fun Q =>
  F1 (fun X => F2of X Q)).

Definition Wpgen_let_trm (F1:Formula) A1 {EA1:Enc A1} (F2of:A1->Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) (Q:A->hprop) =>
    \exists (Q1:A1->hprop), ^F1 Q1 \* \[forall (X:A1), Q1 X ==> ^(F2of X) Q]).
*)

Lemma Formula_formula_inv : forall F f A {EA:Enc A} (Q:A->hprop) q,
  Formula_formula F f ->
  (Post Q) ===> q ->
  structural f ->
  ^F Q ==> f q.
Proof using.
  introv M W S. xchange M. applys* structural_conseq W.
Qed.

Lemma Formula_formula_let : forall F1 f1 A1 {EA1:Enc A1} (F2of:A1->Formula) f2of,
  (Formula_formula F1 f1) ->
  (forall (X:A1), Formula_formula (F2of X) (f2of (enc X))) ->
  structural f1 ->
  Formula_formula (Wpgen_let_trm F1 F2of) (wpgen_let f1 f2of).
Proof using.
  introv M1 M2 S1.
  hnf. intros. applys Formula_formula_mkstruct. clears A.
  hnf. intros. xpull. intros Q1 HQ1. applys* Formula_formula_inv M1.
  intros x. unfold Post at 1. xpull. intros X1 ->.
  xchange HQ1. applys M2.
Qed.

Lemma Formula_formula_app : forall (A:Type) {EA:Enc A} (f:val) (Vs:dyns) (vs:vals),
  LibList.map (fun V => trm_val (dyn_to_val V)) Vs = trms_vals vs ->
  Formula_formula (@Wpgen_app A EA f Vs) (wpgen_app f vs).
Proof using.
  introv E. hnf. intros.
  unfolds Wpgen_app, wpgen_app.
  applys Formula_formula_mkstruct.
  unfold Trm_apps. rewrite <- E.
  applys Formula_formula_wp.
Qed.

Lemma Formula_formula_let_inlined : forall f1 F2 f2of (r:val),
  structural f1 ->
  \[] ==> f1 (fun x => \[x = r]) ->
  Formula_formula F2 (f2of r) ->
  Formula_formula F2 (wpgen_let_aux f1 f2of).
Proof using.
  introv Sf1 M1 M2. hnf. intros. unfold wpgen_let. applys mkstruct_erase_trans.
  xchange M2. xchange M1. applys* structural_frame. applys* structural_conseq.
  intros x. xsimpl. intros ->. auto.
Qed.

(*
Lemma Formula_formula_let_inlined_let : forall F2 f2of (f:val) (vs:vals) (r:val),
  (triple (trm_apps f vs) \[] (fun x => \[x = r])) ->
  Formula_formula F2 (f2of r) ->
  Formula_formula F2 (wpgen_let (wpgen_app f vs) f2of).
Proof using.
  introv Hf M2.
  applys Formula_formula_let_inlined r.
  { applys structural_mkstruct. }
  { unfold wpgen_app. applys mkstruct_erase_trans.
    rewrite <- triple_eq_himpl_wp.
    applys triple_conseq_frame Hf.
    { xsimpl. } { xpull. intros x ->. xsimpl*. } }
  { applys M2. }
Qed.
Lemma Formula_formula_let_inlined : forall f1 F2 f2of (r:val) (Q1:val->hprop),
  structural f1 ->
  \[] ==> f1 Q1 ->
  Q1 ===> (fun x => \[x = r]) ->
  (Formula_formula F2 (f2of r)) ->
  Formula_formula F2 (wpgen_let_aux f1 f2of).
Proof using. Admitted.
*)
(*
  Q1 ==> \exists (A:Type) (EA:Enc A) (V:A), @Post A EA (fun (X:A) => \[X = V])
          \* ( Formula_formula F2 (f2of r)) ->
  Formula_formula F2 (wpgen_let_aux f1 f2of).*)

(* DEPRECATED
Lemma Formula_formula_let_inlined_fun : forall F2 f2of (f:val) (vs:vals) (r:val),
  (triple (trm_apps f vs) \[] (fun x => \[x = r])) ->
  Formula_formula F2 (f2of r) ->
  Formula_formula F2 (wpgen_let_aux (wpgen_app f vs) f2of).
Proof using.
  introv Hf M2.
  applys Formula_formula_let_inlined r.
  { applys structural_mkstruct. }
  { unfold wpgen_app. applys mkstruct_erase_trans.
    rewrite <- triple_eq_himpl_wp.
    applys triple_conseq_frame Hf.
    { xsimpl. } { xpull. intros x ->. xsimpl*. } }
  { applys M2. }
Qed.
*)

Lemma Formula_formula_inlined_fun : forall F1 (f:val) (vs:vals) (r:val),
  (triple (trm_apps f vs) \[] (fun x => \[x = r])) ->
  Formula_formula F1 (wpgen_val r) ->
  Formula_formula F1 (wpgen_app f vs).
Proof using.
  introv Hf M1. hnf. intros.
  unfold wpgen_app. xchange M1. applys mkstruct_weaken. clear Q. intros Q.
  rewrite <- triple_eq_himpl_wp. applys triple_conseq_frame Hf. xsimpl.
  intros x. xpull. intros ->. xsimpl.
Qed.


Lemma Formula_formula_if : forall F1 f1 F2 f2 b (v:val),
  v = ``b ->
  (Formula_formula F1 f1) ->
  (Formula_formula F2 f2) ->
  Formula_formula (Wpgen_if b F1 F2) (wpgen_if_val v f1 f2).
Proof using.
  introv E M1 M2.
  hnf. intros. applys Formula_formula_mkstruct. clears A.
  hnf. intros. subst v. xsimpl b. auto.
  case_if. { applys M1. } { applys M2. }
Qed.


(*
Wpgen_let_trm (Wpgen_app int infix_emark__ ((Dyn r) :: nil))
  (fun x0__ : int => Wpgen_app unit infix_colon_eq__ ((Dyn r) :: (Dyn x0__ + n) :: nil)) EA
  (Q \*+ \GC) ==>
wpgen_let (wpgen_app infix_emark__ ``[ r])
  (fun X : val =>
   wpgen_let (wpgen_app infix_plus__ (X :: ``[ n]))
     (fun v1 : val => wpgen_app infix_colon_eq__ (``r :: v1 :: nil))) (Post Q \*+ \GC)
*)


Lemma Triple_of_CF_and_Formula_formula_funs : forall H A (EA:Enc A) (Q:A->hprop) (F1:Formula) F xs Vs vs t,
  F = val_funs xs t ->
  H ==> ^F1 (Q \*+ \GC) ->
  trms_to_vals (LibList.map (fun V : dyn => trm_val (dyn_to_val V)) Vs) = Some vs ->
  var_funs_exec xs (LibListExec.length vs) ->
  Formula_formula F1 (wpgen (LibListExec.combine xs vs) t) ->
  Triple (Trm_apps F Vs) H Q.
Proof using.
  introv EF HF1 Evs Hxs Ff. rewrite LibListExec.length_eq in Hxs.
  applys triple_apps_funs' EF Evs Hxs.
  xchange HF1. applys Formula_formula_intro_gc Ff.
Qed.

Lemma Triple_of_CF_and_Formula_formula_fixs : 
  forall H A (EA:Enc A) (Q:A->hprop) (F1:Formula) F (f:var) xs Vs (vs:vals) t,
  F = val_fixs f xs t ->
  H ==> ^F1 (Q \*+ \GC) ->
  trms_to_vals (LibList.map (fun V : dyn => trm_val (dyn_to_val V)) Vs) = Some vs ->
  var_fixs_exec (bind_var f) xs (LibListExec.length vs) ->
  Formula_formula F1 (wpgen (LibListExec.combine (f::xs) (F::vs)) t) ->
  Triple (Trm_apps F Vs) H Q.
Proof using.
  introv EF HF1 Evs Hxs Ff. rewrite LibListExec.length_eq in Hxs.
  applys triple_apps_fixs' EF Evs Hxs.
  xchange HF1. applys Formula_formula_intro_gc Ff.
Qed.

Lemma Formula_formula_val : forall A (EA:Enc A) (V:A) v,
  v = enc V ->
  Formula_formula (Wpgen_val V) (wpgen_val v).
Proof using.
  introv M. applys Formula_formula_mkstruct. hnf. intros A' EA' Q.
  unfold PostCast. xpull. intros V' E.
  unfold Post. xsimpl V'. subst*.
Qed.


Lemma Formula_formula_case : forall F1 f1 F2 f2 (P1 P2:Prop),
  (P2 -> P1) ->
  (Formula_formula F1 f1) ->
  (P1 -> Formula_formula F2 f2) ->
  Formula_formula (Wpgen_case F1 P1 F2) (wpgen_case_val f1 P2 f2).
Proof using.
  introv HP M1 M2.
  hnf. intros. applys Formula_formula_mkstruct. clears A.
  hnf. intros. applys hand_weaken.
  { applys M1. }
  { xsimpl. intros HP2. lets HP1: HP HP2.
    applys himpl_hwand_hpure_l.
    { applys* HP. } { applys* M2. } }
Qed.

Lemma Formula_formula_fail :
  Formula_formula Wpgen_fail wpgen_fail.
Proof using.
  hnf. intros. applys Formula_formula_mkstruct. clears A.
  hnf. intros. xsimpl.
Qed.

Lemma Formula_formula_fail_false : forall F,
  False ->
  Formula_formula F wpgen_fail.
Proof using. intros. false. Qed.


Definition CF_matcharg A {EA:Enc A} (V:A) : Prop :=
  True.


Lemma Formula_formula_match : forall A {EA:Enc A} (V:A) F1 f1 F2 f2 (P1 P2:Prop),
  (CF_matcharg V -> Formula_formula (Wpgen_case F1 P1 F2) (wpgen_case_val f1 P2 f2)) ->
  Formula_formula (Wpgen_match V (Wpgen_case F1 P1 F2)) (wpgen_case_val f1 P2 f2).
Proof using. introv M. applys M. hnfs*. Qed.



(********************************************************************)

Ltac xwpgen_simpl :=
  cbn beta delta [
  LibListExec.app LibListExec.combine LibListExec.rev LibListExec.fold_right LibListExec.map
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
  first [ applys Triple_of_CF_and_Formula_formula_funs (rm CF);
          [ reflexivity | try reflexivity | try reflexivity | ]
        | applys Triple_of_CF_and_Formula_formula_fixs (rm CF); 
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

Hint Resolve triple_infix_plus__ triple_infix_bar_bar__ triple_infix_amp_amp__
 : triple_builtin.

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


Ltac cf_inlined_compute :=
  match goal with |- \[] ==> ?H =>
  match H with
  | wpgen_let_aux ?f1 ?f2of ?Q => 
      eapply himpl_wpgen_let_aux; [ applys structural_mkstruct
                                  | try cf_inlined_compute
                                  | try cf_inlined_compute ]
  | wpgen_app ?f ?vs ?Q =>
      eapply himpl_wpgen_app; try cf_triple_builtin
  end end.

Ltac cf_inlined :=
  eapply Formula_formula_let_inlined; [ applys structural_mkstruct | try cf_inlined_compute | ].

Ltac cf_inlined_app :=
  eapply Formula_formula_inlined_fun; [ try cf_triple_builtin | ].

Ltac cf_inlined_if_needed :=
  repeat match goal with 
  | |- Formula_formula ?F (wpgen_let_aux ?f1 ?f2of) => cf_inlined
  | |- Formula_formula (Wpgen_val ?V) (wpgen_app ?f ?vs) => cf_inlined_app
  end.


(* Others *)

Ltac cf_let :=
  cf_inlined_if_needed;
  eapply Formula_formula_let; [ | | applys structural_mkstruct ].

Ltac cf_val :=
  cf_inlined_if_needed;
  eapply Formula_formula_val; [ try solve [ reflexivity | fequals ] ].
  (* fequals needed to force evaluation of opaque encoders *)


Ltac cf_app :=
  cf_inlined_if_needed;
  eapply Formula_formula_app; [ reflexivity ].


(*
Ltac cf_letinlined :=
  eapply Formula_formula_let_inlined_fun; [ try cf_triple_builtin | ].
*)

Ltac cf_if :=
  cf_inlined_if_needed;
  eapply Formula_formula_if; [ reflexivity | | ].

Ltac cf_case_negpat_eq H :=
  unfold Wpgen_negpat; intros; intros ->; eapply H; reflexivity.

Ltac cf_case_destruct :=
  let V := match goal with H: CF_matcharg ?V |- _ => constr:(V) end in
  destruct V.

Ltac cf_case_eq :=
  let A := fresh "A" in
  let EA := fresh "EA" in
  let Q := fresh "Q" in
  let E := fresh "__MatchEq" in
  hnf; intros A EA Q;
  xpull_himpl_hforall_r;
  eapply himpl_hwand_hpure_r; intros E;
  cf_case_destruct; inverts E;
  xsimpl_himpl_hforall_l;
  applys himpl_hwand_hpure_l; [ reflexivity | ].


Ltac cf_case :=
  let H := fresh "__MatchHyp" in
  eapply Formula_formula_case;
  [ intros H; try solve [ cf_case_negpat_eq H ]
  | try cf_case_eq
  | intros H ].

Ltac cf_fail :=
  eapply Formula_formula_fail_false.

Ltac cf_match :=
  cf_inlined_if_needed;
  let H := fresh "__MatchArg" in
  eapply Formula_formula_match; intros H.

Ltac cf_match_fail :=
  cf_fail;
  match goal with H: CF_matcharg ?V |- _ =>
    destruct V; tryfalse; eauto end.

Transparent Enc_list Enc_pair Enc_option.



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
(** ** CF proof for prim *)


(*
let prim x =
  x  + (x - 1) + x

*)

Axiom triple_not : forall (b:bool),
  triple (not b)
    \[]
    (fun r => \[r = val_bool (!b)]).


Hint Resolve triple_not
 : triple_builtin.

Axiom triple_infix_minus__ : forall (n1 n2:int),
  triple (infix_minus__ n1 n2)
    \[]
    (fun r => \[r = val_int (n1 - n2)]).

Axiom triple_ignore : forall (v:val),
  triple (val_ignore v)
    \[]
    (fun r => \[r = val_unit]).

Axiom triple_and : forall (b1 b2:bool),
  triple (val_and b1 b2)
    \[]
    (fun r => \[r = (b1 && b2)]).

Axiom triple_or : forall (b1 b2:bool),
  triple (val_or b1 b2)
    \[]
    (fun r => \[r = (b1 || b2)]).

Axiom triple_neg : forall (b1:bool),
  triple (val_neg b1)
    \[]
    (fun r => \[r = (negb b1)]).

(* TODO: use infix__ names? *)

Axiom triple_infix_lt__ : forall (n1 n2:int),
  triple (infix_lt__ n1 n2)
    \[]
    (fun b => \[b = isTrue (n1 < n2)]).

Axiom triple_infix_lt_eq__ : forall (n1 n2:int),
  triple (infix_lt_eq__ n1 n2)
    \[]
    (fun b => \[b = isTrue (n1 <= n2)]).

Axiom triple_infix_gt__ : forall (n1 n2:int),
  triple (infix_gt__ n1 n2)
    \[]
    (fun b => \[b = isTrue (n1 > n2)]).

Axiom triple_infix_gt_eq__ : forall (n1 n2:int),
  triple (infix_gt_eq__ n1 n2)
    \[]
    (fun b => \[b = isTrue (n1 >= n2)]).


(* TODO: triples
Definition val_abs : val :=
  Fun 'x :=
    If_ 'x '< 0 Then '- 'x Else 'x.

Definition val_min : val :=
  Fun 'x 'y :=
    If_ 'x '< 'y Then 'x Else 'y.

Definition val_max : val :=
  Fun 'x 'y :=
    If_ 'x '< 'y Then 'y Else 'x.
*)


Hint Resolve triple_infix_minus__ triple_ignore triple_and triple_or
  triple_neg triple_infix_lt__ triple_infix_lt_eq__ 
  triple_infix_gt__ triple_infix_gt_eq__ : triple_builtin.



(*

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
(** ** CF proof for prim *)


Lemma prim_cf_def : prim_cf_def__.
Proof using.
  cf_main.
  cf_if.
  { cf_val. }
  { cf_val. }
Qed.

Lemma prim_cf_def' : prim_cf_def__.
Proof using.
  cf_main.
  cf_inlined_if_needed. cf_if.
  { cf_inlined_if_needed. cf_val. }
  { cf_inlined_if_needed. cf_val. }
Qed.

Lemma prim_cf_def'' : prim_cf_def__.
Proof using.
  cf_main.
  eapply Formula_formula_let_inlined; [ applys structural_mkstruct | | ].
  { applys himpl_wpgen_let_aux; [ applys structural_mkstruct | | ].
    { applys himpl_wpgen_app. applys triple_not. }
    { applys himpl_wpgen_let_aux; [ applys structural_mkstruct | | ].
      { applys himpl_wpgen_app. applys triple_infix_bar_bar__. }
      { applys himpl_wpgen_app. applys triple_infix_amp_amp__. } } }
  { cf_if.
    { eapply Formula_formula_let_inlined; [ applys structural_mkstruct | | ].
      { applys himpl_wpgen_let_aux; [ applys structural_mkstruct | | ].
        { applys himpl_wpgen_let_aux; [ applys structural_mkstruct | | ].
          { applys himpl_wpgen_let_aux; [ applys structural_mkstruct | | ].
Abort.


(********************************************************************)
(** ** CF proof for polydepth *)



(*
let rec polydepth : 'a. 'a poly -> int = fun s ->
  match s with
  | Empty _ -> 0
  | Pair s2 -> 1 + polydepth s2
*)


Lemma polydepth_cf_def : polydepth_cf_def__.
Proof using.
  cf_main.
  cf_match.
  cf_case.
  { cf_val. }
  { cf_case.
    { cf_let.
      { cf_app. }
      { intros n. cf_inlined_app. cf_val. } }
    { cf_match_fail. } }
Qed.


Lemma polydepth_cf_def' : polydepth_cf_def__.
Proof using.
  cf_main.
  applys Formula_formula_case.
  { intros HN. unfold Wpgen_negpat. intros. applys Enc_neq_inv. applys HN. }
  { unfold Formula_formula. intros A EA Q.
    xsimpl. introv E. destruct s; tryfalse.
    applys himpl_hforall_l.
    applys himpl_hwand_hpure_l; [ reflexivity | ]. simpls. inverts E.
    applys Formula_formula_val; [ reflexivity ]. }
  { intros N1. unfold Formula_formula. intros A EA Q.
    applys Formula_formula_case.
    { intros HN. hnf. intros. applys Enc_neq_inv. applys HN. }
    { clears A. unfold Formula_formula. intros A EA Q.
      applys himpl_hforall_r; intros vx.
      xsimpl. intros E. (*  applys himpl_hwand_r. :..*)
      destruct s as [|s2]. 1:{ false. }
      rew_enc in E. inverts E.
      applys himpl_hforall_l.
      applys himpl_hwand_hpure_l; [ reflexivity | ].
      applys Formula_formula_let; [ | | applys structural_mkstruct ].
      { applys Formula_formula_app; [ reflexivity ]. }
      { intros n. applys Formula_formula_inlined_fun; [ applys triple_infix_plus__ |  ].
        applys Formula_formula_val; [ reflexivity ]. } }
    { intros N2. applys Formula_formula_fail_false.
      destruct s; try false*. } }
Qed.


(********************************************************************)
(** ** CF proof for bools *)

(*
let bools b =

  if true then b || false else b && true
*)

Lemma bools_cf_def : bools_cf_def__.
Proof using.
  cf_main.
  applys Formula_formula_if; [ reflexivity | | ].
  { applys Formula_formula_inlined_fun; [ applys triple_infix_bar_bar__ | ].
    applys Formula_formula_val; [ reflexivity ]. }
  { applys Formula_formula_inlined_fun; [ applys triple_infix_amp_amp__ | ].
    applys Formula_formula_val; [ reflexivity ]. }
Qed.

Lemma bools_cf_def' : bools_cf_def__.
Proof using.
  cf_main. cf_if.
  { cf_inlined_app. cf_val. }
  { cf_inlined_app. cf_val. }
Qed.



(********************************************************************)
(** ** CF proof for pair_swap *)

(*
let pair_swap (x,y) =
  (y,x)
*)

Lemma pair_swap_cf_def : pair_swap_cf_def__.
Proof using.
  cf_main.
  unfold Wpgen_match, Wpgen_negpat. (* optional *)
  applys Formula_formula_case.
  { intros HN. intros. applys Enc_neq_inv. applys HN. }
  { unfold Formula_formula. intros A EA Q.
    xsimpl. intros x y E.
    destruct x0__ as [X Y]. rew_enc in E. inverts E.
    do 2 applys himpl_hforall_l.
    applys himpl_hwand_hpure_l; [ reflexivity | ].
      applys Formula_formula_val; [ reflexivity ]. }
  { intros N. applys Formula_formula_fail_false.
    destruct x0__. false N. reflexivity. }
Qed.



(********************************************************************)
(** ** CF proof for list map *)

(*
let rec listmap f l =
  match l with
  | [] -> []
  | x::t -> f x :: listmap f t
*)


Lemma listmap_cf_def : listmap_cf_def__.
Proof using.
  cf_main.
  cf_match.
  cf_case.
  { cf_val. }
  { cf_case. cf_let.
    { cf_app. }
    { intros n. cf_let.
       { cf_app. }
       { intros m. cf_val. } }
    { cf_match_fail. } }
Qed.

(* not maintained
  cf_main.
  unfold Wpgen_match, Wpgen_negpat. (* optional *)
  applys Formula_formula_case.
  { intros HN. intros. applys Enc_neq_inv. applys HN. }
  { unfold Formula_formula. intros A EA Q.
    xsimpl. introv HN. destruct x0__. 2:{ rew_enc in HN. inverts HN. }
    applys himpl_hwand_hpure_l; [ reflexivity | ].
    applys Formula_formula_val; [ reflexivity ]. }
  { intros N1. unfold Formula_formula. intros A EA Q.
   applys Formula_formula_case.
    { intros HN. intros. applys Enc_neq_inv. applys HN. }
    { clears A. unfold Formula_formula. intros A EA Q.
      applys himpl_hforall_r; intros vx.
      applys himpl_hforall_r; intros vt.
      xsimpl. intros E. (*  applys himpl_hwand_r. :..*)
      destruct l as [|x t]. 1:{ false. }
      rew_enc in E. inverts E.
      do 2 applys himpl_hforall_l.
      applys himpl_hwand_hpure_l; [ reflexivity | ].
      applys Formula_formula_let; [ | | applys structural_mkstruct ].
      { applys Formula_formula_app; [ reflexivity ]. }
      { intros t2.
        applys Formula_formula_let; [ | | applys structural_mkstruct ].
        { applys Formula_formula_app; [ reflexivity ]. }
        { intros r. applys Formula_formula_val; [ reflexivity ]. } } }
    { intros N2. applys Formula_formula_fail_false.
      destruct l; try false*. } }
Qed.
*)


(********************************************************************)
(** ** CF proof for custom list map *)

(*
type 'a mylist = Nil | Cons of 'a * 'a mylist

let rec mymap f l =
  match l with
  | Nil -> Nil
  | Cons(x,t) -> Cons (f x, mymap f t)
*)

Lemma mymap_cf_def : mymap_cf_def__.
Proof using.
  cf_main.
  unfold Wpgen_match, Wpgen_negpat. (* optional *)
  applys Formula_formula_case.
  { intros HN. intros. applys Enc_neq_inv. applys HN. }
  { unfold Formula_formula. intros A EA Q.
    xsimpl. intros HN. destruct l. 2:{ rew_enc in HN. inverts HN. }
    applys himpl_hwand_hpure_l; [ reflexivity | ].
    applys Formula_formula_val; [ reflexivity ]. }
  { intros N1.
    unfold Formula_formula. intros A EA Q.
   applys Formula_formula_case.
    { intros HN. intros. applys Enc_neq_inv. applys HN. }
    { clears A. unfold Formula_formula. intros A EA Q.
      applys himpl_hforall_r; intros vx.
      applys himpl_hforall_r; intros vt.
      xsimpl. intros E. (*  applys himpl_hwand_r. :..*)
      destruct l as [|x t]. 1:{ false. }
      rew_enc in E. inverts E.
      do 2 applys himpl_hforall_l.
      applys himpl_hwand_hpure_l; [ reflexivity | ].
      applys Formula_formula_let; [ | | applys structural_mkstruct ].
      { applys Formula_formula_app; [ reflexivity ]. }
      { intros t2.
        applys Formula_formula_let; [ | | applys structural_mkstruct ].
        { applys Formula_formula_app; [ reflexivity ]. }
        { intros r. applys Formula_formula_val; [ reflexivity ]. } } }
    { intros N2. applys Formula_formula_fail_false.
      destruct l; try false*. } }
Qed.


(********************************************************************)
(** ** CF proof for id *)

(*
let id x = x
*)

Lemma id_cf_def : id_cf_def__.
Proof using.
  cf_main.
  applys Formula_formula_val; [ reflexivity ].
Qed.


(********************************************************************)
(** ** CF proof for apply *)

(*
let apply f x = f x
*)

Lemma apply_cf_def : apply_cf_def__.
Proof using.
  cf_main.
  applys Formula_formula_app; [ reflexivity ].
Qed.


(********************************************************************)
(** ** CF proof for idapp *)

(*
let idapp =
  let a = id 1 in
  let b = id true in
  2
*)

Lemma idapp_cf_def : idapp_cf_def__.
Proof using.
  cf_main.
  (* hnf. introv CF. applys Triple_of_CF_and_Formula_formula (rm CF); try reflexivity.
  unfold Wptag, dyn_to_val; simpl. xwpgen_simpl. *)
  applys Formula_formula_let; [ | | applys structural_mkstruct ].
  { applys Formula_formula_app; [ reflexivity ]. }
  { intros a.
    applys Formula_formula_let; [ | | applys structural_mkstruct ].
    { applys Formula_formula_app; [ reflexivity ]. }
    { intros b.
      applys Formula_formula_val; [ reflexivity ]. } }
Qed.


(********************************************************************)
(** ** CF proof for f *)

(*
let f r n =
  let x = !r in
  r := x + n
*)

Lemma f_cf_def : f_cf_def__.
Proof using.
  cf_main.
  applys Formula_formula_let; [ | | applys structural_mkstruct ].
  { applys Formula_formula_app; [ reflexivity ]. }
  { intros X. cf_inlined.
    applys Formula_formula_app; [ reflexivity ]. }
Qed.



(********************************************************************)
(** ** Verification of f *)

(*
let f r n =
  let x = !r in
  r := x + n
*)


Lemma f_spec : forall r n m,
  SPEC (f r n)
    PRE (r ~~> m)
    POSTUNIT (r ~~> (n+m)).
Proof using. xcf. xapp. xapp. xsimpl. math. Qed.


(*

let rec g x =
  if x = 0 then 0 else
  let y = g (x-1) in
  y + 2

let v = 2

*)








