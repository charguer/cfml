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


Declare Scope wptactics_scope.
Open Scope wptactics_scope.


(************************************************************************ *)
(** * Internal Tactics *)


(*--------------------------------------------------------*)
(** ** Internal Ltac functions *)

(** Auxiliary tactic for obtaining a boolean answer
    to the question "is E an evar?". TODO: move to TLC *)

Ltac is_evar_as_bool E :=
  constr:(ltac:(first
    [ is_evar E; exact true
    | exact false ])).


(*--------------------------------------------------------*)
(** ** Internal functions to manipulate goal *)

(** [xgoal_code tt] matches goal of the form [PRE H CODE F POST Q] and extracts
    the formula [F]. *)

Ltac xgoal_code tt :=
  match goal with |- PRE _ CODE ?C POST _ => constr:(C) end.
  (* INCORRECT match goal with |- (?H ==> (Wptag ?F) _ _ ?Q) _ => constr:(F) end. *)

(** [xgoal_code_without_wptag] is like [xgoal_code] but it removes the
    [Wptag] wrapper at the head of the formula [F] if there is one,
    using the auxiliary function [xgoal_code_strip_wptag]. *)

Ltac xgoal_code_strip_wptag C :=
  match C with
  | Wptag ?C' => xgoal_code_strip_wptag C'
  | ?C' => constr:(C')
  end.

Ltac xgoal_code_without_wptag tt :=
  let C := xgoal_code tt in
  xgoal_code_strip_wptag C.

(** [xgoal_fun tt] matches goal of the form [PRE H CODE (App f Vs) POST Q] or
    [Triple (Trm_apps f Vs) H Q] and it extract the function [f] being applied. *)

Ltac xgoal_fun tt :=
  match goal with
  | |- Triple (Trm_apps ?f ?Vs) ?H ?Q => constr:(f)
  | |- ?H ==> @Wptag (Wpgen_App_typed ?A ?f ?Vs) _ _ ?Q => constr:(f)
  end.
  (* Alternative for second line:
       match xgoal_code_without_wptag tt with
       | Wpgen_App_typed ?T ?f ?Vs => constr:(f)
       end.
   *)

(* [xgoal_pre tt] matches goal of the form [PRE H CODE F POST Q]  and extracts
    the precondition [H]. *)

Ltac xgoal_pre tt :=
  match goal with |- PRE ?H CODE _ POST _ => constr:(H) end.
  (* match goal with |- ?H ==> _ => constr:(H) end. *)

(* [xgoal_post tt] matches goal of the form [PRE H CODE F POST Q]  and extracts
    the postcondition [Q]. *)

Ltac xgoal_post tt :=
  match goal with |- PRE _ CODE _ POST ?Q => constr:(Q) end.
  (* match goal with |- ?H ==> _ => constr:(H) end. *)

(** [xgoal_post_is_evar tt] returns a boolean indicating
    whether the post-condition of the current goal is an evar. *)

Ltac xgoal_post_is_evar tt :=
  let Q := xgoal_post tt in
  is_evar_as_bool Q.


(* ---------------------------------------------------------------------- *)
(** ** Internal tactic [xspec], for retrieving specifications *)

(** [xspec_registered f] looks for a specification for [f] in the database
    of specifications registered using a hint on [RegisterSpec]. It leaves
    the corresponding specification at head of the goal. *)

Ltac xspec_registered f :=
  ltac_database_get database_spec f.

(** [xspec_context f] finds a specification for [f] among the hypotheses.
    It relies on heuristic, thus sometimes one needs to explicitly refer
    to the hypothesis when invoking [xapp]. It puts a copy of the hypothesis
    found at head of the goal. *)

Ltac xspec_context f :=
  match goal with
  | H: context [ Triple (Trm_apps f _) _ _] |- _ => generalize H
  | H: context [ (_ f) ] |- _ => generalize H (* a named predicate over [f] *)
  | H: context [ f ] |- _ => generalize H (* best effort *)
  end.

(** [xspec] looks for a specification for the function [f] that appears as
    part of a function application in the goal. It looks both in the database
    and in the context. It leaves the specification at head of the goal. *)

Ltac xspec_core tt :=
  let f := xgoal_fun tt in
  first [ xspec_registered f
        | xspec_context f ].

Tactic Notation "xspec" :=
  xspec_core tt.

(** [xspec E] operates as follows, when [f] is the function involved in the goal.
    - if [E] is of the form [(>> __ v1 ... vN)], then the tactic finds the
      specification [Sf] associated with [f], and produces the instantiated
      specification obtained by [lets: Sf v1 .. vN] at head of the goal.
    - otherwise, it assumes [E] to be a specification, and simply puts [E]
      at the head of the goal. *)

Ltac xspec_lemma_of_args E :=
  let H := fresh "Spec_" in
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

Tactic Notation "xspec" constr(E) :=
  xspec_lemma_of_args E.

(** For debugging purposes, [xspec_show_fun] shows the function targeted by [xspec]. *)

Tactic Notation "xspec_show_fun" :=
  first [ let f := xgoal_fun tt in idtac "The goal contains a triple for:" f
        | idtac "xspec expects a goal of the form [Triple t H Q] or [PRE H CODE (App f Vs) POST Q" ].


(* ---------------------------------------------------------------------- *)
(** ** Internal tactic [xtypes], for reporting type information *)

(** [xtypes_type show_arrow T ET] dispays the type [T] and its encoder [ET],
    possibly followed by an arrow if the boolean argument [show_arrow] is [true]. *)

Ltac xtypes_type show_arrow T ET :=
  match show_arrow with
  | true => idtac T " { " ET " } -> "
  | false => idtac T " { " ET " } "
  end.

(** [xtypes_dyn_list L] displays the types involved in the list [L] made
   of values of type [dyn]. Typically [L] is a list of arguments [Vs]. *)

Ltac xtypes_dyn_list L :=
  match L with
  | nil => idtac
  | (@dyn_make ?T ?ET ?x) :: ?R => xtypes_type true T ET
  end.

(** [xtypes_triple E] displays the types involved in [E], which could be
    of the form [Triple (Trm_apps f Vs)] or [PRE _ CODE (App f Vs) POST _]
    or [Wpgen_App_typed T f Vs]. The tactic displays the types of the arguments
    and the return type, as well as the associated encoders. *)

Ltac xtypes_triple E :=
  let aux Vs T ET :=
    xtypes_dyn_list Vs; xtypes_type false T ET in
  match E with
  | (Wptag ?F) => xtypes_triple F
  | (@Wpgen_App_typed ?T ?ET ?f ?Vs) => aux Vs T ET
  | (@Triple (Trm_apps ?f ?Vs) ?T ?ET ?H ?Q) => aux Vs T ET
  | _ => let F := xgoal_code tt in xtypes_triple F
  end.

(** [xtypes_hyp S] displays the types involved in the conclusion
    of a specification lemma [S]. It instantiates the lemma [S]
    using [forwards], thus some of these types may be fresh evars. *)

Ltac xtypes_hyp S :=
  idtac "=== types involved in the application from the hypothesis ===";
  forwards_nounfold_admit_sides_then S ltac:(fun K =>
    let T := type of K in
    xtypes_triple T).

(** [xtypes_goal tt] displays the types involved in the application
    in the goal. *)

Ltac xtypes_goal tt :=
  idtac "=== types involved in the application from the goal ===";
  match xgoal_code_without_wptag tt with ?E => xtypes_triple E end.


(* ---------------------------------------------------------------------- *)
(** ** Internal tactic [xstructural] for proving [Structural F] *)

Ltac xstructural_core tt :=
  applys Structural_Mkstruct.

Tactic Notation "xstructural" :=
  xstructural_core tt.

(* TODO: include a look up in the context, for use in the case of loops *)


(* ---------------------------------------------------------------------- *)
(** ** Internal tactic [xcleanup] for simplifying boolean formulae *)

Ltac xcleanup_core tt :=
  rew_bool_eq.

Tactic Notation "xcleanup" :=
  xcleanup_core tt.


(* ---------------------------------------------------------------------- *)
(** ** Internal tactic [xtriple] *)

(** [xtriple] turns a goal of the form [Triple (Trm_apps f Vs) H Q]
    into the form [PRE H CODE (App f Vs) POST Q]. It is used in the
    implementation of [xapp] for allowing the user to prove a specification
    by refining another existing specification. *)

Lemma xtriple_lemma : forall f (Vs:dyns) `{EA:Enc A} H (Q:A->hprop),
  H ==> ^(Wptag (Wpgen_App_typed A f Vs)) (Q \*+ \GC) ->
  Triple (Trm_apps f Vs) H Q.
Proof using. Admitted. (* TODO *)

Ltac xtriple_pre tt :=
  intros.

Ltac xtriple_core tt :=
  xtriple_pre tt;
  applys xtriple_lemma.
  (*xwp_xtriple_handle_gc tt. *)

Tactic Notation "xtriple" :=
  xtriple_core tt.


(* ---------------------------------------------------------------------- *)
(** ** Internal tactic [xtriple_inv] *)

(** [xtriple_inv] performs the opposite to [xtriple]: it turns a goal of the
    form [PRE H CODE (App f Vs) POST Q] into the form [Triple (Trm_apps f Vs) H Q].
    It is used by [xapp] for exploiting characteristic formulae associated with
    the body of functions. *)

Lemma xtriple_inv_lifted_lemma : forall f (Vs:dyns) A `{EA:Enc A} H (Q:A->hprop),
  Triple (Trm_apps f Vs) H Q ->
  H ==> ^(Wptag (Wpgen_App_typed A f Vs)) Q.
Proof using. Admitted. (* TODO *)

Ltac xtriple_inv_core tt :=
  applys xtriple_inv_lifted_lemma.

Tactic Notation "xtriple_inv" :=
  xtriple_inv_core tt.


(************************************************************************ *)
(** * User Tactics *)

(* ---------------------------------------------------------------------- *)
(** ** Internal tactics [xend] for killing stupid goals *)

(** [xend] solves goals that Coq leaves unproved, of the form [Type] or
    [Type ?A]. Invoke [Unshelve] to see these remaining goals. *)

Ltac solve_enc tt :=
  match goal with |- Enc _ => exact Enc_unit end.

Ltac solve_type tt :=
  match goal with |- Type => exact unit end.

Ltac xend_core tt :=
  try first [ solve_enc tt | solve_type tt ].

Tactic Notation "xend" :=
  xend_core tt.

(* TODO: maybe needed later?
Ltac remove_head_unit tt :=
  repeat match goal with
  | |- unit -> _ => intros _
  end. *)


(* ---------------------------------------------------------------------- *)
(** ** Tactic [xcf] for invoking a precomputed characteristic formula *)

(** [xcf] applies to a goal with a conclusion of the form [SPEC t PRE H POST Q]
    of [Triple t H Q]. It looks up the characteristic formula associated with [f]
    in the database ([database_cf]), and exploits that formula.

    [xcf] automatically calls [intros] before starting, if needed.

    When [xcf] fails, possible cause include:

    - the number of arguments in the specification does not match the number
      of arguments in the code;
    - the types of the arguments don't match the types in the code;
    - the input type of the postcondition does not match the return type of the code;
    - the specification is missing assumptions of the form [{EA:Enc A}].

    For troubleshooting, consider the following variants:

    - [xcf_show] display the characteristic formula for the function in the goal.
    - [let f := xgoal_fun tt in pose f] shows the function in the goal.
    - [xcf_show f] displays the characteristic formula associated with [f].
    - [xcf_types] compares the types involved in the specification with those
      involved in the characteristic formula.
    - [xcf_types E] compares the types involved in the specification with those
      involved in the lemma [E], which is assumed to conclude with a Triple
      like a characteristic formula. *)

Ltac xcf_pre tt :=
  intros.

Ltac xcf_target tt :=
  match goal with
  | |- ?f = _ => constr:(f)
  | |- Triple (Trm_apps ?f ?Vs) ?H ?Q => constr:(f)
  end.

Ltac xcf_find f :=
  ltac_database_get database_cf f.

Ltac xcf_post tt :=
  instantiate;
  try solve_enc tt.
  (* TODO: needed? cbv beta; remove_head_unit tt. *)

Ltac xcf_top_fun tt :=
  let f := xcf_target tt in
  xcf_find f;
  let Sf := fresh "Spec" in
  intros Sf;
  eapply Sf;
  clear Sf;
  xcf_post tt.
  (* TODO: first [ xcf_top_value f | xcf_fallback f | fail 2 ]
      where xcf_fallback is defined in CFML1's CFTactics.V *)

Ltac xcf_top_value tt :=
  let f := xcf_target tt in
  xcf_find f;
  let Sf := fresh "Spec" in
  intros Sf;
  rewrite Sf;
  clear Sf;
  xcf_post tt.

(* [xcf] *)

Ltac xcf_core tt :=
  xcf_pre tt;
  first [ xcf_top_fun tt
        | xcf_top_value tt ].

Tactic Notation "xcf" :=
  xcf_core tt.
Tactic Notation "xcf" "~" :=
  xcf; auto_tilde.
Tactic Notation "xcf" "*" :=
  xcf; auto_star.

(* [xcf_show f] *)

Ltac xcf_show_intro f :=
  let Sf := fresh "Spec" f in
  intros Sf.

Ltac xcf_show_arg_core f :=
  xcf_find f;
  xcf_show_intro f.

Tactic Notation "xcf_show" constr(f) :=
  xcf_show_arg_core f.

(* [xcf_show] *)

Ltac xcf_show_core tt :=
  xcf_pre tt;
  let f := xcf_target tt in
  xcf_show_arg_core f.

Tactic Notation "xcf_show" :=
  xcf_show_core tt.

(* [xcf_types] *)

Ltac xcf_types_core tt :=
  let S := fresh "Spec" in
  intros S;
  xtypes_goal tt;
  xtypes_hyp S;
  clear S.

Ltac xcf_types_core_noarg tt :=
  xcf_show;
  xcf_types_core tt.

Tactic Notation "xcf_types" :=
  xcf_types_core_noarg tt.

(* [xcf_types S] *)

Ltac xcf_types_core_arg S :=
  xcf_pre tt;
  generalize S;
  xcf_types_core tt.

Tactic Notation "xcf_types" constr(S) :=
  xcf_types_core_arg S.

(* TODO: generalize xcf_types to top_value *)

(* LATER
Ltac xcf_fallback f :=
  idtac "Warning: could not exploit the specification; maybe the types don't match; check them using [xcf_types]; if you intend to use the specification manually, use [xcf_show].";
  xcf_find f;
  let Sf := fresh "Spec" in
  intros Sf.
*)


(* ---------------------------------------------------------------------- *)
(** ** Tactic [xgc] *)

(** [The tactic [xgc] adds a [\GC] in the postcondition. Because the
    characteristic formulae already integrate such a [\GC], this tactic
    almost never needs to be invoked in practice. *)

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
(** ** Tactic [xseq] *)

(** The tactic [xseq] applies to a goal of the form [PRE H CODE (Seq F1 ; F2) POST Q]. *)

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


(* [xseq Q] *)

Lemma xseq_lemma_typed_post : forall (H1:hprop) H A (EA:Enc A) (Q:A->hprop) ,
  forall (F1:Formula) (F2:Formula),
  Structural F1 ->
  H ==> ^F1 (fun (_:unit) => H1) ->
  (H1 ==> ^F2 Q) ->
  H ==> ^(@Wpgen_seq F1 F2) Q. (* TODO: EA1 is not guessed right *)
Proof using.
  introv HF1 M1 M2. applys MkStruct_erase. xchange M1.
  applys* Structural_conseq. xchanges M2.
Qed.

Ltac xseq_arg_core H :=
  eapply (@xseq_lemma_typed_post H); [ xstructural | | ].

Tactic Notation "xseq" constr(H) :=
  xseq_arg_core H.


(*--------------------------------------------------------*)
(** ** [xletval] and [xletvals] *)

(* TODO: need more coherence because
      xletfun is xfun
      xletval is not xval...
      xlet can handle xletval but not xfun... *)

(** [xletval] is used to reason on a let-value node, i.e. on a goal
    of the form [H ==> (Val x := v in F1) Q].
    It introduces [x] and [Px: x = v], and leaves (H ==> F1 Q)].

    [xletval as] leaves the fresh variables in the goal.
    It leaves the goal [forall x, x = v -> (H ==> F1 Q)].

    [xletvals] leaves the goal [H ==> F1 Q] with [x] replaced by [v]
    everywhere. *)

(* TODO: here and elsewhere, call xpull_check_not_needed tt; *)

Ltac xletval_pre tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_Val _ _) => idtac
  end.

Lemma xletvals_lemma : forall A `{EA:Enc A} H (Fof:A->Formula) (V:A) A1 `{EA1:Enc A1} (Q:A1->hprop),
  (H ==> ^(Fof V) Q) ->
  H ==> ^(Wpgen_let_Val V Fof) Q.
Proof using.
  introv M. applys MkStruct_erase. xchanges* M. intros ? ->. auto.
Qed.

Lemma xletval_lemma : forall A `{EA:Enc A} H (Fof:A->Formula) (V:A) A1 `{EA1:Enc A1} (Q:A1->hprop),
  (forall x, x = V -> H ==> ^(Fof x) Q) ->
  H ==> ^(Wpgen_let_Val V Fof) Q.
Proof using.
  introv M. applys xletvals_lemma. applys* M.
Qed.

Ltac xletval_common cont :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_Val _ (fun x => _)) =>
     let a := fresh "v" x in
     let Pa := fresh "P" a in
     applys xletval_lemma;
     intros a Pa;
     cont a Pa
  end.

Ltac xletval_core tt :=
  xletval_common ltac:(fun a Pa => idtac).

Tactic Notation "xletval" :=
  xletval_core tt.

Ltac xletvalas_core tt :=
  xletval_common ltac:(fun a Pa => revert a Pa).

Tactic Notation "xletval" "as" :=
  xletvalas_core tt.

Ltac xletvals_core tt :=
  xletval_pre tt;
  applys xletvals_lemma.

Tactic Notation "xletvals" :=
  xletvals_core tt.


(* ---------------------------------------------------------------------- *)
(** ** Tactic [xlet] *)

(* [xlet] *)

(* TODO: auto introduce the name of xlet *)

Lemma xlet_lemma : forall A1 (EA1:Enc A1) H `{EA:Enc A} (Q:A->hprop) (F1:Formula) (F2of:forall A2 (EA2:Enc A2),A2->Formula),
  H ==> ^F1 (fun (X:A1) => ^(F2of _ _ X) Q) ->
  H ==> ^(Wpgen_let F1 (@F2of)) Q.
Proof using. introv M. applys MkStruct_erase. xsimpl* A1 EA1. Qed.

Definition xlet_typed_lemma := @MkStruct_erase.

Ltac xlet_pre tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_typed _ _) => idtac
  end.

Ltac xlet_core tt :=
  xlet_pre tt;
  eapply xlet_typed_lemma.

Tactic Notation "xlet" :=
  first [ xlet_core tt
        | xletval ]. (* TODO: document *)

(* [xlet Q] *)

Lemma xlet_lemma_typed_post : forall A1 (EA1:Enc A1) (Q1:A1->hprop) H A (EA:Enc A) (Q:A->hprop) ,
  forall (F1:Formula) (F2of:A1->Formula),
  Structural F1 ->
  H ==> F1 A1 EA1 Q1 ->
  (forall (X:A1), Q1 X ==> (F2of X) A EA Q) ->
  H ==> ^(@Wpgen_let_typed F1 A1 EA1 (@F2of)) Q. (* TODO: EA1 is not guessed right *)
Proof using.
  introv HF1 M1 M2. applys MkStruct_erase. xchange M1.
  applys* Structural_conseq.
Qed.

Ltac xlet_post_core Q :=
  xlet_pre tt;
  applys (@xlet_lemma_typed_post _ _ Q); [ try xstructural | | ].

Tactic Notation "xlet" constr(Q) :=
  xlet_post_core Q.

(* [xlets] *)

Tactic Notation "xlets" := (* TODO: document *)
  xletvals.


(* ---------------------------------------------------------------------- *)
(** ** Tactic [xcast] *)

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
  xcast_pre tt;
  applys xcast_lemma.

Tactic Notation "xcast" :=
  xcast_core tt.

Tactic Notation "xcast_types" :=
  xcast_debug tt.


(* ---------------------------------------------------------------------- *)
(** ** Tactic [xpost] *)

Lemma xpost_lemma : forall A `{EA:Enc A} (Q1 Q2:A->hprop) H (F:Formula),
  Structural F ->
  H ==> ^F Q1 ->
  Q1 ===> Q2 ->
  H ==> ^F Q2.
Proof using. introv M W. applys* structural_conseq. Qed.

Arguments xpost_lemma : clear implicits.


(* [xpost] *)

Ltac xpost_core tt :=
  eapply (@xpost_lemma); [ xstructural | | ].

Tactic Notation "xpost" :=
  xpost_core tt.

(* [xpost Q] *)

Ltac xpost_arg_core Q :=
  let Q := match type of Q with
           | hprop => constr:(fun (_:unit) => Q)
           | _ => constr:(Q)
           end in
  eapply (@xpost_lemma _ _ Q); [ xstructural | | ].

Tactic Notation "xpost" constr(Q) :=
  xpost_arg_core Q.


(* ---------------------------------------------------------------------- *)
(** ** Tactic [xlet_xseq_xcast_repeat] *)

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
(** ** Tactic [xreturn] *)

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
(** ** Tactic [xapp] *)

(* TODO: update documentation *)

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
      xapp_simpl tt ].

  xapp_pre tt.
  applys xapp_find_spec_lemma.
  xspec_prove_triple tt .
  xapp_select_lemma tt. xsimpl. xapp_simpl tt.

  xapp_pre tt.
  applys xapp_find_spec_lifted_lemma.
  xspec_prove_triple tt .
  xapp_select_lifted_lemma tt. xsimpl. xapp_simpl tt.

*)


Ltac xapp_record tt :=
  fail "implemented later in WPStruct".

Lemma xapp_lemma : forall A `{EA:Enc A} (Q1:A->hprop) (f:val) (Vs:dyns) H1 H Q,
  Triple (Trm_apps f Vs) H1 Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  H ==> ^(Wpgen_App_typed A f Vs) Q.
Proof using.
  introv M1 M2. applys MkStruct_erase. xchanges (rm M2).
  applys xreturn_lemma_typed. rewrite <- Triple_eq_himpl_Wp.
  applys* Triple_ramified_frame.
Qed.

Lemma xapps_lemma : forall A `{EA:Enc A} (V:A) H2 (f:val) (Vs:dyns) H1 H Q,
  Triple (Trm_apps f Vs) H1 (fun r => \[r = V] \* H2) ->
  H ==> H1 \* (H2 \-* protect (Q V)) ->
  H ==> ^(Wpgen_App_typed A f Vs) Q.
Proof using.
  introv M1 M2. applys xapp_lemma M1. xchanges M2.
  intros ? ->. auto.
Qed.

Lemma xapps_lemma_pure : forall A `{EA:Enc A} (V:A) (f:val) (Vs:dyns) H1 H Q,
  Triple (Trm_apps f Vs) H1 (fun r => \[r = V]) ->
  H ==> H1 \* protect (Q V) ->
  H ==> ^(Wpgen_App_typed A f Vs) Q.
Proof using.
  introv M1 M2. applys xapps_lemma \[]; rew_heap; eauto.
Qed.

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
  | (Wpgen_App_typed ?T ?f ?Vs) => idtac
  (* | (Wpgen_record_new ?Lof) => idtac --- added in WPRecord *)
  end.

Ltac xapp_pre_triple tt :=
  match goal with
  | |- (Triple _ _ _) => xtriple
  end.

Ltac xapp_pre tt :=
  first [ xapp_pre_wp tt | xapp_pre_triple tt ].

(** [xapp_simpl] presents a nice error message in case of failure *)

Definition xapp_hidden (P:Type) (e:P) := e.

Notation "'__XAPP_FAILED_TO_MATCH_PRECONDITION__'" :=
  (@xapp_hidden _ _).

Ltac xapp_report_error tt :=
  match goal with |- context [?Q1 \--* protect ?Q2] =>
    change (Q1 \--* protect Q2) with (@xapp_hidden _ (Q1 \--* protect Q2)) end.

Ltac xapp_simpl tt :=
  xsimpl;
  first [ xapp_report_error tt
        | unfold protect; xcleanup ].

Ltac xapp_simpl_basic tt := (* version without error message *)
  xsimpl; unfold protect; xcleanup.

(* [xapp] implementation*)

(* FUTURE
Ltac xapp_select_lemma cont := (* TODO: factorize better with xapp_select_lemma *)
  let S := fresh "Spec" in
  intro S;
  match type of S with
  | Wpgen_body _ => applys @xtriple_inv_lifted_lemma; [ applys S | clear S; cont tt ]
  (* TODO: optimize using  match type of S with context[...] *)
  | Triple _ _ (fun _ => \[_ = _] \* _) => applys @xapps_lemma; [ applys S | clear S ].
  | Triple _ _ (fun _ => \[_ = _]) => applys @xapps_lemma_pure; [ applys S | clear S ].
  | _ => applys @xapp_lemma; [ applys S | clear S ].
  end
*)

Ltac xapp_exploit_spec L cont :=
  let S := fresh "Spec" in
  intro S;
  eapply L;
  [ applys S; clear S
  | clear S; cont tt ].

Ltac xapp_exploit_body tt :=
  let S := fresh "Spec" in
  intro S;
  eapply xtriple_inv_lifted_lemma;
  eapply S;
  clear S.

Ltac xapp_common tt :=
  match goal with |- ?S -> _ =>
  match S with
  | Wpgen_body _ =>
    first [ xapp_exploit_body tt
          | fail 2 "xapp_exploit_body failed" ]
  | _ =>
    first [ xapp_exploit_spec xapps_lemma xapp_simpl
          | xapp_exploit_spec xapps_lemma_pure xapp_simpl
          | xapp_exploit_spec xapp_lemma xapp_simpl ]
  end end.

Ltac xapp_general tt :=
  xspec;
  xapp_common tt.

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

(** [xapp_spec] to show registered specification *)

Tactic Notation "xapp_spec" :=
  xspec_core tt;
  let Spec := fresh "Spec" in
  intros Spec.

Tactic Notation "xapp_spec" constr(E) :=
  xspec E;
  let Spec := fresh "Spec" in
  intros Spec.

(** [xapp E] to provide arguments, where [E] can be a specification, or can
    be of the form [__ E1 ... En] to specify only arguments of the registered
    specification. *)

Ltac xapp_arg_core E :=
  xapp_pre tt;
  xspec_lemma_of_args E;
  xapp_common tt.

Tactic Notation "xapp" constr(E) :=
  xapp_arg_core E.
Tactic Notation "xapp" "~" constr(E) :=
  xapp E; auto_tilde.
Tactic Notation "xapp" "*" constr(E) :=
  xapp E; auto_star.

(** [xapp_nosubst] to prevent substitution *)

(* TODO: xapp_record_no_subst is missing *)

Ltac xapp_nosubst_core tt :=
  xapp_pre tt;
  xspec;
  (* TODO: raise error if spec is a Wpgen_body *)
  xapp_exploit_spec @xapp_lemma xapp_simpl.

Tactic Notation "xapp_nosubst" :=
  xapp_nosubst_core tt.
Tactic Notation "xapp_nosubst" "~" :=
  xapp_nosubst; auto_tilde.
Tactic Notation "xapp_nosubst" "*"  :=
  xapp_nosubst; auto_star.

Ltac xapp_arg_nosubst_core E :=
  xapp_pre tt;
  xspec_lemma_of_args E;
  xapp_exploit_spec @xapp_lemma xapp_simpl.

Tactic Notation "xapp_nosubst" constr(E) :=
  xapp_arg_nosubst_core tt.
Tactic Notation "xapp_nosubst" "~" constr(E) :=
  xapp_nosubst E; auto_tilde.
Tactic Notation "xapp_nosubst" "*" constr(E)  :=
  xapp_nosubst E; auto_star.

(** [xappn] to repeat [xapp] *)

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
(** ** [xapp_debug] *)
(* TODO: deprecated, now using show_types *)

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

(* TODO :factorize xapp_debug *)

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
(** ** Tactic [xval] *)

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
  applys xval_lifted_lemma;
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
(** ** Tactic [xfun] *)

(* TODO: OLD VERSION OF XFUN for partial wpgen operation
   rename to xval_lemma_val?

Lemma xfun_lemma : forall (v:val) H (Q:val->hprop),
  H ==> Q v ->
  H ==> ^(Wpgen_val v) Q.
Proof using. introv M. applys~ @xval_lemma M. Qed.

Ltac xfun_core tt :=
  xval_pre tt;
  applys xfun_lemma.

Tactic Notation "xfun" :=
  xfun_core tt.
*)


(*--------------------------------------------------------*)
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


(*--------------------------------------------------------*)
(** ** [xfun] *)

(** [xfun] applies to a formula of the form [LetFun f := B in F].

    - [xfun] without arguments simply saves the hypothesis about [f]
      for later use. This tactic is useful in particular when there
      is a single occurrence of [f] in the code.

    - [xfun P] can be used to give a specification for [f], proved
      with respect to the most-general specification. Here, [P]
      should take the form [fun f => spec_of_f].
      When this tactic fails, try [xfun_rec; xapp_types.] (* TODO: xfun_types *)

    - [xfun_ind R P] is a shorthand for proving a recursive function
      by well-founded induction on the first argument quantified in [P].
      It is short for [xfun_rec P], followed by [intros n] and
      [induction_wf IH: R n], and then exploiting the characteristic
      formula for the body. The binary relation [R] needs to be
      well-founded. Typical relation includes [downto 0] and [upto n]
      for induction on the type [int]. [R] can also be a measure function,
      as such functions are accepted as arguments of [induction_wf].

    - [xfun_ind_skip P] is a development tactic used to skip the need
      to provide a well-founded relation for justifying termination.

    - [xfun_rec P] is like [xfun P] but it does not perform any
      simplification automatically, leaving a chance for the user
      to apply Coq's induction tactic---though it most case, [xfun_ind]
      should do the job. Use tactic [xapp] (or [apply]) to continue the
      proof after [induction]. (* TODO: check that xapp works for
      exploiting a body. Note that this tactic is essentially equivalent
      to [xfun as; intros f Sf; assert (Sf': P f); [ | clears Sf; rename Sf' into Sf ]. ] *)

    - Also available, the "as" variant, allow the variables and hypotheses
      to be named explicitly.
      [xfun as]
      [xfun P as]
      [xfun_ind R P as]
      [xfun_rec P as]
      [xfun_ind_skip R P as]

*)

Ltac xfun_pre tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_fun _) => idtac
  end.

Lemma xfun_lemma : forall A `{EA:Enc A} (BodyOf:forall A,Enc A->(A->hprop)->hprop) H (Q:A->hprop),
  H ==> ^(BodyOf) Q ->
  H ==> ^(Wpgen_let_fun BodyOf) Q.
Proof using. introv M. applys MkStruct_erase. applys M. Qed.

Lemma xfun_cut_lemma : forall f (SpecOf:val->Prop) (Bf G:Prop),
  (Bf -> SpecOf f) ->
  (SpecOf f -> G) ->
  (Bf -> G).
Proof using. auto. Qed.

Lemma xfun_cut_skip_lemma : forall f (SpecOf:val->Prop) (Bf G:Prop),
  (SpecOf f -> Bf -> SpecOf f) ->
  (SpecOf f -> G) ->
  (Bf -> G).
Admitted. (* This lemma only for development purposes *)

(* [xfun_common cont] extracts the variable [f] and the CF for [f] named [Bf],
   then calls the continuation [cont] with [f] and [Bf] as arguments. *)

Ltac xfun_common cont :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_fun (fun A EA Q => \forall f, _)) =>
     let a := fresh f in
     let Sa := fresh "Spec_" f in
     applys xfun_lemma;
     applys himpl_hforall_r; intros a;
     applys hwand_hpure_r_intro; intros Sa;
     cont a Sa
  end.

(** [xfun_simpl Bf] applies to a goal of the form
    [Bf: characteristic_formula_for_the_body_of_f |- SpecOf f]
    and it exploits [Bf] in order to prove the goal,
    then clears this hypothesis. *)

Ltac xfun_simpl Bf :=
  first [ intros; eapply Bf
        | hnf; intros; eapply Bf ]; (* useful if P is an abstract definition *)
  clear Bf.

(** Core functions (below, [P] corresponds to [SpecOf] *)

Ltac xfun_as_core cont2 :=
  xfun_common cont2.

Ltac xfun_spec_as_core P cont1 cont2 :=
  xfun_common ltac:(fun f Sf =>
    revert Sf;
    applys (@xfun_cut_lemma f P);
    [ let Bf := fresh "Body_" f in
      intros Bf;
      xfun_simpl Bf;
      cont1 f Bf
    | intros Sf;
      cont2 f Sf ]).

Ltac xfun_spec_rec_as_core P cont1 cont2 := (* TODO: factorize?*)
  xfun_common ltac:(fun f Sf =>
    revert Sf;
    applys (@xfun_cut_lemma f P);
    [ let Bf := fresh "Body_" f in
      intros Bf;
      cont1 f Bf
    | intros Sf;
      cont2 f Sf ]).

Ltac xfun_spec_ind_as_core R P cont1 cont2 :=
  xfun_common ltac:(fun f Sf =>
    revert Sf;
    applys (@xfun_cut_lemma f P);
    [ let Bf := fresh "Body_" f in
      intros Bf ?;
      let X := get_last_hyp tt in
      induction_wf_core_then R X ltac:(fun _ =>
        intros Sf;
        xfun_simpl Bf;
        cont1 f Sf)
    | intros Sf;
      cont2 f Sf ]).

Ltac xfun_spec_ind_skip_as_core P cont1 cont2 :=
  xfun_common ltac:(fun f Sf =>
    revert Sf;
    applys (@xfun_cut_skip_lemma f P);
    [ let Bf := fresh "Body_" f in
      intros Sf Bf;
      xfun_simpl Bf;
      cont1 f Sf
    | intros Sf;
      cont2 f Sf ]).

(** Variants with names in the goal *)

Ltac xfun_clean_unused_var tt :=
  match goal with |- val -> _ => intros _ end.

Tactic Notation "xfun" "as" :=
  xfun_as_core ltac:(fun f Sf => revert f Sf).
Tactic Notation "xfun" constr(P) "as" :=
  xfun_spec_as_core P ltac:(fun f Bf => revert f; xfun_clean_unused_var tt) ltac:(fun f Sf => revert f Sf).
Tactic Notation "xfun_rec" constr(P) "as" :=
  xfun_spec_rec_as_core P ltac:(fun f Bf => revert f Bf) ltac:(fun f Sf => revert f Sf).
Tactic Notation "xfun_ind" constr(R) constr(P) "as" :=
  xfun_spec_ind_as_core R P ltac:(fun f Sf => revert f Sf) ltac:(fun f Sf => revert f Sf).
Tactic Notation "xfun_ind_skip" constr(P) "as" :=
  xfun_spec_ind_skip_as_core P ltac:(fun f Sf => revert f Sf) ltac:(fun f Sf => revert f Sf).

(* Variants with names introduced *)

Ltac idcont2 f Sf := idtac.

Tactic Notation "xfun" :=
  xfun_as_core idcont2.
Tactic Notation "xfun" constr(P) :=
  xfun_spec_as_core P idcont2 idcont2.
Tactic Notation "xfun_rec" constr(P) :=
  xfun_spec_rec_as_core P idcont2 idcont2.
Tactic Notation "xfun_ind" constr(R) constr(P) :=
  xfun_spec_ind_as_core R P idcont2 idcont2.
Tactic Notation "xfun_ind_skip" constr(P) :=
  xfun_spec_ind_skip_as_core P idcont2 idcont2.


(*--------------------------------------------------------*)
(** ** [xfuns] *)

(** [xfuns as] applies to mutually recursive functions. *)

(* TODO: provide additional tactics like for [xfun]? *)

Ltac xfuns_as_core tt :=
  applys xfun_lemma;
  pose ltac_mark;
  repeat applys himpl_hforall_r;
  repeat applys hwand_hpure_r_intro;
  gen_until_mark.

Tactic Notation "xfuns" "as" :=
  xfuns_as_core tt.


(* ---------------------------------------------------------------------- *)
(** ** Tactic [xif] *)

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

(** [xif] *)

Ltac xif_core tt :=
  xif_pre tt;
  first [ applys @xifval_lemma_isTrue
        | applys @xifval_lemma ];
  xif_post tt.

Tactic Notation "xif" :=
  xif_core tt.

(** [xif Q] or [xif H] *)

Ltac xif_arg_core Q :=
  xlet_xseq_xcast_repeat tt;
  xpost Q; [ xif_core tt | ].

Tactic Notation "xif" constr(Q) :=
  xif_arg_core Q.


(* ---------------------------------------------------------------------- *)
(** ** Tactic [xcase] *)

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

(* ---------------------------------------------------------------------- *)
(** ** Tactic [xfail] *)

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




(************************************************************************ *)
(************************************************************************ *)
(************************************************************************ *)
(** * Loops *)

(*

(*--------------------------------------------------------*)
(** ** [xwhile] *)


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
    match xgoal_post_is_evar tt with
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
(** ** [xfor] *)

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
  match xgoal_post_is_evar tt with
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
  lazymatch xgoal_post_is_evar tt with
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
(** ** [xfor_down] *)

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


(************************************************************************ *)
(************************************************************************ *)
(************************************************************************ *)
(** * Pattern matching *)


(*--------------------------------------------------------*)
(** ** [xcleanpat] *)

(** [xcleanpat] is a tactic for removing all the negated
    pattern assumptions. *)

Ltac xcleanpat_core :=
  repeat match goal with H: Wpgen_negpat _ |- _ => clear H end.

Tactic Notation "xcleanpat" :=
  xcleanpat_core.


(*--------------------------------------------------------*)
(** ** [xdone] *)

Lemma xdone_lemma : forall A `{EA:Enc A} (Q:A->hprop) H,
  H ==> ^(Wpgen_done) Q.
Proof using.
  intros. unfold Wpgen_done. applys MkStruct_erase. xsimpl.
Qed.

Ltac xdone_core tt :=
  applys xdone_lemma.

Tactic Notation "xdone" :=
  xdone_core tt.


(*--------------------------------------------------------*)
(** ** [xalias] -- deal with aliases using [xletval];
      synonymous tactics are provided *)

(** See documentation of [xletval]. *)

Ltac xalias_pre tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_alias _ _) => idtac
  end.

Ltac xalias_core tt :=
  xalias_pre tt;
  xletval.

Tactic Notation "xalias" :=
  xalias_core tt.

Tactic Notation "xalias" "as" := (* TODO: document *)
  xalias_pre tt;
  xletval as.

Ltac xalias_subst_core tt :=
  xalias_pre tt;
  xletvals.

Tactic Notation "xalias_subst" :=
  xalias_subst_core tt.


(*--------------------------------------------------------*)
(** ** [xcase] is the new [xcase] *)

(** [xcase] applies to a goal of the form
    [(Case v = p1 Then F1 Else F2) H Q]. -- TODO: update syntax

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

(* TODO: change naming policy for handling pattern variables *)

(* [xcase_post] is a tactic that applies to an hypothesis
   of the form [v = p1] or [v <> p1], and attemps to prove
   false from it, and inverts it if possible. *)

Ltac xclean_trivial_eq tt :=
  repeat match goal with H: ?E = ?E |- _ => clear H end.


(* in [xcase_post H], H is either an equality [v = p], or a conjunction [v = p /\ istrue b]
   in case the hypothesis comes from testing a when-clause. *)
(* DEPRECATED
Ltac xcase_post_old H :=
  try solve [ discriminate | false; congruence ];
  try (symmetry in H; inverts H; xclean_trivial_eq tt).
*)

Ltac xcase_post H :=
  let aux1 tt := try solve [ discriminate | false; congruence ] in
  let aux2 E := symmetry in E; inverts E; xclean_trivial_eq tt in
  match type of H with
  | _ /\ _ =>
      try (
        let E := fresh "E" H in
        destruct H as [H E];
        aux1 tt;
        aux2 E (* if inverts E, then keep the original conjunction *)
      )
  | _ =>
      aux1 tt;
      try (aux2 H)
  end.

(* [xcase_core E cont1 cont2] is the underlying tactic for [xcase].
   It calls [cont1] on the first subgoal and [cont2] on the second subgoal. *)

(* TODO xcase_pre tt  is defined elsewhere in this file. *)

Ltac xcase_extract_hyps tt :=
  pose ltac_mark;
  repeat (apply himpl_hforall_r; intro);
  apply hwand_hpure_r_intro; intro;
  gen_until_mark.

Ltac xcase_no_intros_core cont1 cont2 :=
  apply MkStruct_erase; applys himpl_hand_r;
  [ xcase_extract_hyps tt; cont1 tt
  | apply hwand_hpure_r_intro; cont2 tt ].

Ltac xcase_core H cont1 cont2 :=
  xcase_no_intros_core
    ltac:(fun _ => introv H; cont1 tt)
    ltac:(fun _ => introv H; cont2 tt).

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
(** ** [xmatch] *)

(** [xmatch] applies to a pattern-matching goal of the form
    [(Match Case v = p1 Then F1
       Else Case v = p2 Then Alias y := w in F2
       Else Done/Fail) H Q]. -- TODO: update syntax.

    By default, the tactic calls the inversion tactic on
    the equalities [v = pi] associated with the case
    (and also calls congruence to attempt proving false).
    [xmatch_no_simpl] can be used to disable such inversions.

    Several variants are available:

    - [xmatch] investigates all the cases, doing inversions,
      and introducing all aliases as equalities.

    - [xmatch_subst_alias] performs all case analyses,
      and introduces and substitutes away all aliases.

    - [xmatch_no_cases] simply remove the [Wpgen_match] tag and
      leaves the cases to be solved manually using
      [xmatch_case] or [xcase]/[xfail]/[xdone] tactics directly.

    - [xmatch_no_intros] is like [xmatch], but does not
      perform any name introduction or any inversion.
      (One needs to manually call [xdone] for the last case.)

    - [xmatch_no_alias] is like [xmatch], but does not
      introduce aliases.

    - [xmatch_no_simpl] is like [xmatch], but does not do inversions.
      [xmatch_no_simpl_no_alias] is also available.
      [xmatch_no_simpl_subst_alias] are also available.

   Like with [xif], the tactic [xmatch] will likely not produce
   solvable goals if the post-condition is an unspecified evar.
   If the post-condition is an evar, call [xpost Q] to set the
   post-condition. Alternatively, the syntax [xmatch Q] will do this.
*)

(* TODO put back fresh names into the goal *)

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
    ltac:(fun _ => let H := fresh "C" in introv H; cont tt).

Ltac xmatch_case_core cont_case :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_done) => xdone
  | (Wpgen_fail) => xfail
  | (Wpgen_case _ _ _) => first [ cont_case tt | fail 2 ]
  | ?c => idtac c; fail 100 "unexpected tag in xmatch_case"
  end.


(* [xmatch_cases case_tactic] recursively apply [xmatch_case] using
   [case_tactic] to handle each case. *)

Ltac xmatch_cases case_tactic :=
  xmatch_case_core ltac:(fun _ =>
    case_tactic ltac:(fun _ => xmatch_cases case_tactic)).

Ltac xmatch_check_post_instantiated tt :=
  match xgoal_post_is_evar tt with
  | true => fail 100 "xmatch requires a post-condition; use [xmatch Q] or [xpost Q] to set it."
  | false => idtac
  end.

Ltac xmatch_pre tt :=
  (* TODO xpull_check_not_needed tt; *)
  xmatch_check_post_instantiated tt.

Lemma xmatch_lemma : forall A `{EA:Enc A} H (F:Formula) (Q:A->hprop),
  H ==> ^F Q ->
  H ==> ^(Wptag (Wpgen_match F)) Q.
Proof using. auto. Qed.

Ltac xmatch_with cont :=
  xmatch_pre tt;
  apply xmatch_lemma;
  cont tt.

Tactic Notation "xmatch_case" := (* TODO: undocumented?*)
  xmatch_case_core ltac:(fun _ => xmatch_case_alias ltac:(fun _ => idtac)).

Tactic Notation "xmatch" :=
  xmatch_with ltac:(fun _ => xmatch_cases xmatch_case_alias).
Tactic Notation "xmatch" constr(Q) :=
  xpost Q; xmatch.
Tactic Notation "xmatch_no_alias" :=
  xmatch_with ltac:(fun _ => xmatch_cases xmatch_case_no_alias).
Tactic Notation "xmatch_subst_alias" :=
  xmatch_no_alias; repeat xalias_subst.
Tactic Notation "xmatch_no_cases" :=
  xmatch_with ltac:(fun _ => idtac).
Tactic Notation "xmatch_no_intros" :=
  xmatch_with ltac:(fun _ => xmatch_cases xmatch_case_no_intros).
Tactic Notation "xmatch_no_simpl_no_alias" :=
  xmatch_with ltac:(fun _ => xmatch_cases xmatch_case_no_simpl).
Tactic Notation "xmatch_no_simpl" :=
  xmatch_no_simpl_no_alias; repeat xalias.
Tactic Notation "xmatch_no_simpl_subst_alias" :=
  xmatch_no_simpl_no_alias; repeat xalias_subst.


(************************************************************************ *)
(************************************************************************ *)
(************************************************************************ *)
(** * Others *)

(* ---------------------------------------------------------------------- *)
(** ** Tactic [xassert] *)

Lemma xassert_lemma : forall H (Q:unit->hprop) (F1:Formula),
  H ==> ^F1 (fun r => \[r = true] \* H) ->
  H ==> Q tt ->
  H ==> ^(Wpgen_assert F1) Q.
Proof using.
  introv M1 M2. applys Structural_conseq (fun (_:unit) => H).
  { xstructural. }
  { applys MkStruct_erase. applys xreturn_lemma_typed. xsimpl*. }
  { xchanges M2. intros []. auto. }
Qed.

Lemma xassert_lemma_inst : forall H (F1:Formula),
  H ==> ^F1 (fun r => \[r = true] \* H) ->
  H ==> ^(Wpgen_assert F1) (fun (_:unit) => H).
Proof using. introv M. applys* xassert_lemma. Qed.

Ltac xassert_pre tt :=
  xlet_xseq_xcast_repeat tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_assert _) => idtac
  end.

Ltac xassert_core tt :=
  xassert_pre tt;
  first [ eapply xassert_lemma_inst
        | eapply xassert_lemma ].
  (* TODO: alternative: test whether ?Q is an evar *)

Tactic Notation "xassert" :=
  xassert_core tt.



(*--------------------------------------------------------*)
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


(************************************************************)
(** [xgo], [xcf_go] and [xstep] *)

Ltac check_is_Wpgen_record_alloc F :=  (* refined in WPRecord *)
  fail.

Ltac xstep_once tt :=
  match goal with
  | |- ?G => match xgoal_code_without_wptag tt with
    | (Wpgen_seq _ _) => xseq
    | (Wpgen_let_typed _ _) => xlet
    | (Wpgen_let _ _) => xlet
    | (Wpgen_let_Val _ _) => xletval
    | (Wpgen_app _) => xapp
    | (Wpgen_App_typed _ _ _) => xapp
    | (Wpgen_if_bool _ _ _) => xif
    | (Wpgen_val _) => xval
    | (Wpgen_Val _) => xval
    | (Wpgen_Val_no_mkstruct _) => xcast
    | (Wpgen_fail) => xfail
    | (Wpgen_done) => xdone
    | (Wpgen_case _ _ _) => xcase
    | (Wpgen_match _) => xmatch
    | (Wpgen_assert _) => xassert
    | ?F => check_is_Wpgen_record_alloc F; xapp
    (* | (Wpgen_case _ _ _) => xcase *)
    end
  | |- Triple _ _ _ => xapp
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






(************************************************************************ *)
(** * For future use *)

(* ---------------------------------------------------------------------- *)
(** ** Tactic [xwp_simpl] for computing characteristic formulae in coq *)

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
(** ** Tactic [xwp_xtriple_handle_gc] -- for internal use *)
(* TODO: remove? *)

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
(** ** Tactic [xwp] *)
(* TODO: will be deprecated *)

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
