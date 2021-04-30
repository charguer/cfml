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
  H ==> ^(Wptag (Wpgen_app_untyped (trm_apps f (trms_vals vs)))) (Q \*+ \GC) ->
  Triple t H Q.
Proof using.
  introv E M. subst t. applys Triple_hgc_post.
  applys* Triple_of_Wp. unfolds Wpgen_app_untyped.
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
  H ==> ^(Wpgen_app_untyped t) Q.
Proof using.
  introv M1 M2. applys MkStruct_erase.
  xchanges (rm M2).
  rewrite <- Triple_eq_himpl_Wp.
  applys* Triple_ramified_frame.
Qed.

Lemma xapps_lemma : forall A `{EA:Enc A} (V:A) H2 t H1 H Q,
  Triple t H1 (fun r => \[r = V] \* H2) ->
  H ==> H1 \* (H2 \-* protect (Q V)) ->
  H ==> ^(Wpgen_app_untyped t) Q.
Proof using.
  introv M1 M2. applys xapp_lemma M1. xchanges M2.
  intros ? ->. auto.
Qed.

Lemma xapps_lemma_pure : forall A `{EA:Enc A} (V:A) t H1 H Q,
  Triple t H1 (fun r => \[r = V]) ->
  H ==> H1 \* protect (Q V) ->
  H ==> ^(Wpgen_app_untyped t) Q.
Proof using.
  introv M1 M2. applys xapps_lemma \[]; rew_heap; eauto.
Qed.



Lemma xapp_find_spec_lemma : forall A `{EA:Enc A} (Q1:A->hprop) t H1 H (Q:A->hprop),
  Triple t H1 Q1 ->
  (Triple t H1 Q1 ->
   H ==> ^(Wpgen_app_untyped t) Q) ->
  H ==> ^(Wpgen_app_untyped t) Q.
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
  | (Wpgen_app_untyped ?t) => xapp_apply_lemma ltac:(xspec_prove_triple)
  | (Wpgen_App_typed ?T ?f ?Vs) => xapp_apply_lifted_lemma ltac:(xspec_prove_triple)
  end.

  Ltac xapp_arg_core E :=
  xapp_pre tt;
  let cont := ltac:(fun tt => xspec_prove_triple_with_args E) in
  match xgoal_code_without_wptag tt with
  | (Wpgen_app_untyped ?t) =>  xapp_apply_lemma cont
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
  H ==> ^(Wpgen_unlifted_val v) Q.
Proof using. introv E N. subst. applys MkStruct_erase. unfold Post_cast_val. xsimpl~ V. Qed.
Ltac xval_pre tt :=
  xlet_xseq_xcast_repeat tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_unlifted_val _) => idtac
  | (Wpgen_val _) => idtac
  end.

Ltac xval_core tt :=
  xval_pre tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_unlifted_val _) => applys @xval_lemma_decode; [ try xdecode | ]
  | (Wpgen_val _) => applys xval_lifted_lemma
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

(* ********************************************************************** *)
in xstep
  | (Wpgen_cast _) => xseq
    | (Wpgen_cast _) => xcast

  | (Wpgen_let _ _) => xlet



Lemma xreturn_lemma_val : forall A1 `{Enc A1} (F:(A1->hprop)->hprop) (Q:val->hprop) H,
  H ==> F (fun (X:A1) => Q (enc X)) ->
  H ==> ^(Formula_cast F) Q.
Proof using.
  introv M. unfold Formula_cast. xsimpl* (fun X : A1 => Q ``X).
  unfold Post_cast. intros X. unfold Post_cast_val. xsimpl* X.
Qed.



(* ---------------------------------------------------------------------- *)
(** ** Tactic [xfun] *)

(* TODO: OLD VERSION OF XFUN for partial wpgen operation
   rename to xval_lemma_val?

Lemma xfun_lemma : forall (v:val) H (Q:val->hprop),
  H ==> Q v ->
  H ==> ^(Wpgen_unlifted_val v) Q.
Proof using. introv M. applys~ @xval_lemma M. Qed.

Ltac xfun_core tt :=
  xval_pre tt;
  applys xfun_lemma.

Tactic Notation "xfun" :=
  xfun_core tt.
*)


(*
(* ---------------------------------------------------------------------- *)
(** ** [xauto] *)

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




(* ---------------------------------------------------------------------- *)
(** ** [xletval_st]

TODO

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


(************************************************************************ *)
(* Others *)

(* DEPRECATED
Lemma eliminate_eta_in_code : forall A `{EA:Enc A} H1 (Q1:A->hprop) (F1:Formula),
    (PRE H1
    CODE F1
    POST Q1)
  ->
    (PRE H1
    CODE (fun (A0 : Type) (EA0 : Enc A0) (Q : A0 -> hprop) => F1 A0 EA0 Q)
    POST Q1).
Proof using. introv M. xchanges M. Qed.
*)


(************************************************************************ *)

(* --TODO: decode typeclass *)

(* --LATER: xif automates xapp *)



Lemma xlettrm_lemma : forall A1 (EA1:Enc A1) H `{EA:Enc A} (Q:A->hprop) (F1:Formula) (F2of:forall A2 (EA2:Enc A2),A2->Formula),
  H ==> ^F1 (fun (X:A1) => ^(F2of _ _ X) Q) ->
  H ==> ^(Wpgen_let F1 (@F2of)) Q.
Proof using. introv M. applys MkStruct_erase. xsimpl* A1 EA1. Qed.


(* ---------------------------------------------------------------------- *)
(** ** [xind_skip] *)

(* TODO: document better *)

(** [xind_skip] allows to assume the current goal to be
    already true. It is useful to test a proof before justifying
    termination. It applies to a goal [G] and turns it
    into [G -> G]. Typical usage: [xind_skip ;=> IH].

    Use it for development purpose only.

    Variant: [xind_skip as IH], equivalent to [xind_skip ;=> IH].
*)

Tactic Notation "xind_skip" :=
  let IH := fresh "IH" in admit_goal IH.

Tactic Notation "xind_skip" "as" :=
  let IH := fresh "IH" in admit_goal IH; revert IH.

(* TODO deprecated: in goal by default
Tactic Notation "xind_skip" :=
  let IH := fresh "IH" in admit_goal IH; gen IH.

Tactic Notation "xind_skip" "as" ident(IH) :=
  admit_goal IH.
*)


 (* TODO: check that xapp works for
      exploiting a body. Note that this tactic is essentially equivalent
      to [xletfun as; intros f Sf; assert (Sf': P f); [ | clears Sf; rename Sf' into Sf ]. ] *)



Lemma xval_lemma : forall A `{EA:Enc A} (V:A) v H (Q:A->hprop),
  v = ``V ->
  H ==> Q V ->
  H ==> ^(Wpgen_unlifted_val v) Q.
Proof using. introv E N. subst. applys MkStruct_erase. unfold Post_cast_val. xsimpl~ V. Qed.

(* NEEDED? *)
Lemma xval_lemma_val : forall A `{EA:Enc A} (V:A) v H (Q:val->hprop),
  v = ``V ->
  H ==> Q (``V) ->
  H ==> ^(Wpgen_unlifted_val v) Q.
Proof using. introv E N. subst. applys MkStruct_erase. unfold Post_cast_val. xsimpl~ (``V). Qed.




(* ---------------------------------------------------------------------- *)
(** ** [xval E] *)

Ltac xval_arg E :=
  xval_pre tt;
  eapply (@xval_lemma _ _ E); [ try reflexivity | ].

Tactic Notation "xval" uconstr(E) :=
  xval_arg E.
Tactic Notation "xval" "~" uconstr(E) :=
  xval E; auto_tilde.
Tactic Notation "xval" "*" uconstr(E) :=
  xval E; auto_star.


Ltac xvals_arg E :=
  xval E; xsimpl.

Tactic Notation "xvals" uconstr(E) :=
  xvals_arg E.
Tactic Notation "xvals" "~" uconstr(E) :=
  xvals E; auto_tilde.
Tactic Notation "xvals" "*" uconstr(E) :=
  xvals E; auto_star.



(* ---------------------------------------------------------------------- *)
(** ** Tactic [xcase] *)


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

(* DEPRECATED

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
*)
(* conclusion above:
  H ==> ^(Match_ ``L With
         '| 'nil '=> F1
         '| vX ':: vL' [vX vL'] '=> F2 vX vL') Q.
*)

(* DEPRECATED
Ltac xcase_post_old H :=
  try solve [ discriminate | false; congruence ];
  try (symmetry in H; inverts H; xclean_trivial_eq tt).
*)


Definition Wpgen_cast A1 `{EA1:Enc A1} (V:A1) : Formula :=
  fun A2 (EA2:Enc A2) Q => Post_cast A1 Q V.



(* ---------------------------------------------------------------------- *)
(* ** Lemma for changing the encoder in a triple *)



(** [Post_cast_val Q] turns a postcondition of type [A->hprop] into
    the corresponding postcondition at type [val->hprop]. *)

Definition Post_cast_val A `{EA:Enc A} (Q:A->hprop) : val->hprop :=
  fun (v:val) => \exists (V:A), \[v = enc V] \* Q V.

(** [Post_cast A' Q] turns a postcondition of type [A->hprop] into
    the corresponding postcondition at type [A'->hprop]. *)

Definition Post_cast A2 `{EA2:Enc A2} A1 `{EA1:Enc A1} (Q:A1->hprop) : A2->hprop :=
  fun (V:A2) => Post_cast_val Q (``V).

Arguments Post_cast A2 {EA2} [A1] {EA1} Q.

(** Properties of [Post_cast] *)

Lemma qimpl_Post_cast_r : forall A `{EA:Enc A} (Q:A->hprop),
  Q ===> Post_cast A Q.
Proof using. intros. unfolds Post_cast, Post_cast_val. intros X. xsimpl*. Qed.

Lemma qimpl_Post_cast_l : forall A `{EA:Enc A} (Q:A->hprop),
  Enc_injective EA ->
  Post_cast A Q ===> Q.
Proof using.
  introv M. unfolds Post_cast, Post_cast_val. intros X. xsimpl*.
  intros Y EQ. rewrites (>> Enc_injective_inv M) in EQ. subst*.
Qed.

Lemma Post_cast_val_weaken : forall A1 `{EA:Enc A1} (Q1 Q2:A1->hprop),
  Q1 ===> Q2 ->
  Post_cast_val Q1 ===> Post_cast_val Q2.
Proof using. introv M. unfold Post_cast_val. xpull ;=> ? V ->. xchanges* M. Qed.

Lemma Post_cast_weaken : forall A2 `{EA:Enc A2} A1 `{EA:Enc A1} (Q1 Q2:A1->hprop),
  Q1 ===> Q2 ->
  Post_cast A2 Q1 ===> Post_cast A2 Q2.
Proof using. introv M. intros V. applys* Post_cast_val_weaken. Qed.

Lemma Triple_enc_change :
  forall A1 A2 (t:trm) (H:hprop) `{EA1:Enc A1} (Q1:A1->hprop) `{EA2:Enc A2} (Q2:A2->hprop),
  Triple t H Q1 ->
  Q1 ===> Post_cast A1 Q2 ->
  Triple t H Q2.
Proof using.
  introv M N. unfolds Triple. applys~ triple_conseq (rm M).
  unfold LiftPost. intros v. xpull ;=> V EV. subst. applys N.
Qed.

(** Specialization of [Triple_enc_change] for converting from a postcondition
    of type [val->hprop] *)

Lemma Triple_enc_change_from_val :
  forall (t:trm) (H:hprop) (Q1:val->hprop) A2 `{EA2:Enc A2} (Q2:A2->hprop),
  Triple t H Q1 ->
  Q1 ===> Post_cast_val Q2 ->
  Triple t H Q2.
Proof using. introv M N. applys* Triple_enc_change M. Qed.

(** Specialization of [Triple_enc_change] for converting to a postcondition
    of type [val->hprop]  *)

Lemma Triple_enc_change_to_val :
  forall A1 `{EA1:Enc A1} (t:trm) (H:hprop) (Q1:A1->hprop) (Q2:val->hprop),
  Triple t H Q1 ->
  (forall (X:A1), Q1 X ==> Q2 (enc X)) ->
  Triple t H Q2.
Proof using.
  introv M N. applys* Triple_enc_change M. intros X. xchange (N X).
  unfold Post_cast, Post_cast_val. xsimpl~.
Qed.





Lemma xformula_cast_lemma : forall A `{Enc A} (F:(A->hprop)->hprop) (Q:A->hprop) H,
  H ==> F Q ->
  H ==> ^(FormulaCast F) Q.
Proof using. introv M. rewrite* FormulaCast_self. Qed.



Definition Formula_cast `{Enc A1} (F:(A1->hprop)->hprop) : Formula :=
  fun A2 (EA2:Enc A2) (Q:A2->hprop) =>
    \exists (Q':A1->hprop), F Q' \* \[Q' ===> Post_cast A1 Q].
(* forall V, Q' V ==> \exists (V':A), \[enc V = enc V'] \* Q V'. *)x



Definition Post_cast_val A `{EA:Enc A} (Q:A->hprop) : val->hprop :=
  fun (v:val) => \exists (V:A), \[v = enc V] \* Q V.

(** [Post_cast A' Q] turns a postcondition of type [A->hprop] into
    the corresponding postcondition at type [A'->hprop]. *)

Definition Post_cast A2 `{EA2:Enc A2} A1 `{EA1:Enc A1} (Q:A1->hprop) : A2->hprop :=
  fun (V:A2) => 


Lemma Triple_enc_change :
  forall A1 A2 (t:trm) (H:hprop) `{EA1:Enc A1} (Q1:A1->hprop) `{EA2:Enc A2} (Q2:A2->hprop),
  Triple t H Q1 ->
  Q1 ===> PostCast A1 Q2 ->
  Triple t H Q2.
Proof using.
  introv M N. unfolds Triple. applys~ triple_conseq (rm M). intros v. 
  unfolds Post, PostCast. xpull ;=> V EV. subst. xchanges* N.
Qed.




Definition Wpgen_seq' (F1 F2:Formula) : Formula :=
  MkStruct (fun A (EA:Enc A) Q =>
    \exists (H1:hprop), ^F1 (fun (_:unit) => H1) \* \[H1 ==> ^F2 Q]).





Lemma qimpl_trans : forall A (Q2 Q1 Q3:A->hprop),
  (Q1 ===> Q2) ->
  (Q2 ===> Q3) ->
  (Q1 ===> Q3).
Proof using. introv M1 M2. intros v. applys himpl_trans; eauto. Qed.




Lemma himpl_frame_hcredits : forall n H1 H2,
  \$n \* H1 ==> \$n \* H2 ->
  H1 ==> H2.
Proof using.
  introv M. lets K: himpl_frame_r (\$(-n)) M.
  do 2 rewrite <- hstar_assoc in K.
  rewrite <- hcredits_add_eq in K.
  math_rewrite (-n + n = 0) in K.
  rewrite hcredits_zero_eq in K. xchanges K.
Qed.



(* Dummy instantiation of credits for logics that don't support credits *)

(* TODO: could be a functor instead of being an example *)

Module HcreditsDummy.

(** Assumptions *)

Parameter hprop : Type.

Parameter hempty : hprop.

Parameter hstar : hprop -> hprop -> hprop.

Parameter haffine : hprop -> Prop.

(** Notation *)

Notation "\[]" := (hempty)
  (at level 0) : heap_scope.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity) : heap_scope.

(** Realization *)

Definition hcredits (n:Z) : hprop :=
  \[].

Notation "'\$' n" := (hcredits n)
  (at level 40,
   n at level 0,
   format "\$ n") : heap_scope.

Lemma hcredits_skip :
  use_credits = false ->
  forall n, \$ n = \[].
Proof using. auto. Qed.

Lemma hcredits_zero :
  \$ 0 = \[].
Proof using. auto. Qed.

Lemma hcredits_add : forall n m,
  \$ (n+m) = \$ n \* \$ m.
Proof using. auto. Qed.

Lemma haffine_hcredits : forall n,
  n >= 0 ->
  haffine (\$ n).
Proof using. applys haffine_hempty. Qed.

End HcreditsDummy.




(* TODO: might no longer be needed *)
Lemma neg_sub : forall n m,
  - (n - m) = (-n) + m.
Proof using. math. Qed.

Hint Rewrite neg_sub : rew_int.



Ltac xsimpl_step_lr tt ::=
  match goal with |- Xsimpl (?Nc, ?Hla, \[], \[]) (?Hra, ?Hrg, \[]) =>
    match Hrg with
    | \[] =>
       match Hra with
       | ?H1 \* \[] =>
         match H1 with
         | ?Hra_evar => is_evar Hra_evar; 
              rew_heap; 
              match xsimpl_use_credits tt with
                | true => apply ximpl_lr_refl
                | false =>  apply ximpl_lr_refl_nocredits 
                end
         | ?Q1 \--* ?Q2 => is_evar Q2; eapply ximpl_lr_qwand_unify
         | \[False] \-* ?H2 => apply xsimpl_lr_hwand_hfalse
         | ?H1 \-* ?H2 => xsimpl_flip_acc_l tt; apply xsimpl_lr_hwand
         | ?Q1 \--* ?Q2 =>
             xsimpl_flip_acc_l tt;
             match H1 with
             | @qwand unit ?Q1' ?Q2' => apply xsimpl_lr_qwand_unit
             | _ => apply xsimpl_lr_qwand; intro
             end
         | hforall _ => xsimpl_flip_acc_l tt; apply xsimpl_lr_hforall; intro
                        (* --TODO: optimize for iterated \forall bindings *)
         end
       | \[] => match xsimpl_use_credits tt with
                | true => apply xsimpl_lr_exit_credits_to_hempty
                | false => apply ximpl_lr_refl_nocredits 
                end
       | _ => xsimpl_flip_acc_lr tt; 
              match xsimpl_use_credits tt with
              | true => apply xsimpl_lr_exit_nogc 
              | false => apply xsimpl_lr_exit_nogc_nocredits
              end
       end
    | (\Top \* _) => apply ximpl_lr_htop
    | (\GC \* _) =>
        first
        [ match Hra with ?Hra1 \* \[] => is_evar Hra1;  (* when Hra1 is an evar *)
            match xsimpl_use_credits tt with
            | true => apply xsimpl_lr_exit_instantiate 
            | false => apply xsimpl_lr_exit_instantiate_nocredits
            end
          end
        | (* General case, Hra not just reduced to an evar *)
          let xsimpl_xaffine tt := try remove_empty_heaps_haffine tt; xaffine in
          match xsimpl_use_credits tt with
          | true => apply ximpl_lr_hgc; [ try xsimpl_hcredits_nonneg tt | xsimpl_xaffine tt | ]
          | false => apply ximpl_lr_hgc_nocredits; [ xsimpl_xaffine tt | ]
          end ] 
    | ?Hrg' => xsimpl_flip_acc_lr tt;
              match xsimpl_use_credits tt with
              | true => apply xsimpl_lr_exit 
              | false => apply xsimpl_lr_exit_nocredits
              end

  end end.