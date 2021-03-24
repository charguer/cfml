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
(************************************************************************ *)
(************************************************************************ *)
(** * Internal Tactics *)


(* ---------------------------------------------------------------------- *)
(** ** Internal Ltac functions *)

(** Auxiliary tactic for obtaining a boolean answer
    to the question "is E an evar?". TODO: move to TLC *)

Ltac is_evar_as_bool E :=
  constr:(ltac:(first
    [ is_evar E; exact true
    | exact false ])).


(* ---------------------------------------------------------------------- *)
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
  | |- ?H ==> @Wptag (Wpgen_app ?A ?f ?Vs) _ _ ?Q => constr:(f)
  end.
  (* Alternative for second line:
       match xgoal_code_without_wptag tt with
       | Wpgen_app ?T ?f ?Vs => constr:(f)
       end.
   *)

(* [xgoal_pre tt] matches goal of the form [PRE H CODE F POST Q] or
    [Triple t H Q] and extracts the precondition [H]. *)

Ltac xgoal_pre tt :=
  match goal with
  | |- PRE ?H CODE _ POST _ => constr:(H)
  | |- Triple _ ?H _ => constr:(H)
  end.

(* [xgoal_post tt] matches goal of the form [PRE H CODE F POST Q] and
   or [Triple (Trm_apps f Vs) H Q] extracts the postcondition [Q]. *)

Ltac xgoal_post tt :=
  match goal with
  | |- PRE _ CODE _ POST ?Q => constr:(Q)
  | |- Triple _ _ ?Q => constr:(Q)
  end.

(** [xgoal_post_is_evar tt] returns a boolean indicating
    whether the post-condition of the current goal is an evar. *)

Ltac xgoal_post_is_evar tt :=
  let Q := xgoal_post tt in
  is_evar_as_bool Q.


(*------------------------------------------------------------------*)
(* ** Internal tactic [xcheck_pull] *)

(** [xcheck_pull tt] raises an error if the user attempts to perform
    an operation on a goal whose precondition is subject to [xpull]. *)

(** [xcheck_pull_error tt] displays the error message. *)

Ltac xcheck_pull_error tt :=
  fail 100 "You should first call xpull.".

(** [xcheck_pull_rec H] raises an error if the heap predicate [H]
    contains existential quantifiers or nonempty pure facts,
    or possibly also if it contains unsimplied beta-redexes. *)

Ltac xcheck_pull_rec H :=
  let rec_after_simpl tt :=
    let H' := eval simpl in H in
     match H' with
     | H => xcheck_pull_error tt
     | _ => xcheck_pull_rec H'
     end
  in
  match H with
  | \[] => idtac
  | \[_ = _ :> unit] => idtac
  | \[_] => xcheck_pull_error tt
  | \exists _,_ => xcheck_pull_error tt
  | ?H1 \* ?H2 => xcheck_pull_rec H1; xcheck_pull_rec H2
  | (fun _ => _) _ => rec_after_simpl tt
  | (let _ := _ in _) => rec_after_simpl tt
  | (let '(_,_) := _ in _) => rec_after_simpl tt
  | _ => idtac
  end.

(** [xcheck_pull tt] checks the precondition for opportunities for [xpull]. *)

Ltac xcheck_pull tt :=
  let H := xgoal_pre tt in
  xcheck_pull_rec H.


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
    or [Wpgen_app T f Vs]. The tactic displays the types of the arguments
    and the return type, as well as the associated encoders. *)

Ltac xtypes_triple E :=
  let aux Vs T ET :=
    xtypes_dyn_list Vs; xtypes_type false T ET in
  match E with
  | (Wptag ?F) => xtypes_triple F
  | (@Wpgen_app ?T ?ET ?f ?Vs) => aux Vs T ET
  | (@Triple (Trm_apps ?f ?Vs) ?T ?ET ?H ?Q) => aux Vs T ET
  | (PRE _ CODE ?C POST _) => xtypes_triple C
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

(** [xtypes_post tt] displays the types involved in the postcondition
    in the goal. *)

Ltac xtypes_post tt :=
  idtac "=== types involved in the postcondition from the goal ===";
  match goal with |- (?H ==> (@Wptag ?F) ?A ?EA ?Q) => xtypes_type false A EA end.
  (* Alternative without encoder
  let Q := xgoal_post tt in
  match type of Q with
  | ?T -> _ => idtac "return type" T
  | _ => idtac "postcondition of type" Q
  end. *)


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
  H ==> ^(Wptag (Wpgen_app A f Vs)) (Q \*+ \GC) ->
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
  H ==> ^(Wptag (Wpgen_app A f Vs)) Q.
Proof using. Admitted. (* TODO *)

Ltac xtriple_inv_core tt :=
  applys xtriple_inv_lifted_lemma.

Tactic Notation "xtriple_inv" :=
  xtriple_inv_core tt.


(* ---------------------------------------------------------------------- *)
(** ** Internal tactic [xletval], used by [xlet] *)

(** [xletval] applies to a goal of the form
    [PRE H CODE (LetVal x := v in F1) POST Q].
    It introduces [x] and [Px: x = v], and leaves [PRE H CODE F1 POST Q].

    [xletvals] leaves the goal [PRE H CODE F1 POST Q] where [x is] replaced
    by [v] everywhere.

    [xletval as] leaves the fresh variables in the goal:
    [forall x, x = v -> (PRE H CODE F1 POST Q)].

    [xletval P as] leaves the fresh variables in the goal:
    [forall x, P x -> (PRE H CODE F1 POST Q)].

    [xletval P] is similar but introduces [x] and [P x]. *)

Ltac xletval_pre tt :=
  xcheck_pull tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_val _ _) => idtac
  end.

(* [xletvals] *)

Lemma xletvals_lemma : forall A `{EA:Enc A} H (Fof:A->Formula) (V:A) A1 `{EA1:Enc A1} (Q:A1->hprop),
  (H ==> ^(Fof V) Q) ->
  H ==> ^(Wpgen_let_val V Fof) Q.
Proof using.
  introv M. applys MkStruct_erase. xchanges* M. intros ? ->. auto.
Qed.

Ltac xletvals_core tt :=
  xletval_pre tt;
  applys xletvals_lemma.

Tactic Notation "xletvals" :=
  xletvals_core tt.

(* [xletval] *)

Lemma xletval_lemma : forall A `{EA:Enc A} H (Fof:A->Formula) (V:A) A1 `{EA1:Enc A1} (Q:A1->hprop),
  (forall x, x = V -> H ==> ^(Fof x) Q) ->
  H ==> ^(Wpgen_let_val V Fof) Q.
Proof using.
  introv M. applys xletvals_lemma. applys* M.
Qed.

Ltac xletval_common cont :=
  xletval_pre tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_val _ (fun x => _)) =>
     let a := fresh "v" x in
     let Pa := fresh "P" a in
     eapply xletval_lemma;
     intros a Pa;
     cont a Pa
  end.

Ltac xletval_core tt :=
  xletval_common ltac:(fun a Pa => idtac).

Tactic Notation "xletval" :=
  xletval_core tt.

(* [xletval as] *)

Ltac xletvalas_core tt :=
  xletval_common ltac:(fun a Pa => revert a Pa).

Tactic Notation "xletval" "as" :=
  xletvalas_core tt.

(* [xletval P] *)

Lemma xletvalst_lemma : forall A `{EA:Enc A} (P:A->Prop) H (Fof:A->Formula) (V:A) A1 `{EA1:Enc A1} (Q:A1->hprop),
  P V ->
  (forall x, P x -> H ==> ^(Fof x) Q) ->
  H ==> ^(Wpgen_let_val V Fof) Q.
Proof using.
  introv HV M. applys xletvals_lemma. applys* M.
Qed.

Ltac xletvalst_common P cont :=
  xletval_pre tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_val _ (fun x => _)) =>
     let a := fresh "v" x in
     let Pa := fresh "P" a in
     eapply (@xletvalst_lemma _ _ P);
     [ | intros a Pa; cont a Pa ]
  end.

Ltac xletvalst_core P :=
  xletvalst_common P ltac:(fun a Pa => idtac).

Tactic Notation "xletval" constr(P) :=
  xletvalst_core P.

(* [xletval P as] *)

Ltac xletvalst_as_core P :=
  xletvalst_common P ltac:(fun a Pa => revert a Pa).

Tactic Notation "xletval" constr(P) "as" :=
  xletvalst_as_core tt.


(* ---------------------------------------------------------------------- *)
(** ** Internal tactic [xlettrm], used by [xlet] *)

(* TODO: xlettrm, how to reuse the name from the code automatically? *)

(** [xlettrm Q1 as] applies to a goal of the form
    [PRE H CODE (Let x := F1 in F2) POST Q].
    It leaves [PRE H CODE F1 POST Q1] for the first goal, and
    [forall x, PRE (Q1 x) CODE F2 POST Q], for the second goal.

    [xlettrm Q1] introduces the name [x] in the context automatically.

    [xlettrm] without argument does something slightly different.
    Instead of introducing an evar for [Q1], it leaves a single goal,
    where the continuation appears in the post, essentially:
    [PRE H CODE F1 POST (fun x => F2 Q)]. Thus, when the proof of [F1]
    completes, there remains exactly the expected goal on [F2].
    Note that it is possible at any point to invoke [xpost] to introduce
    an evar for the postcondition, simulating the behavior of [xlettrm Q1]
    with a fresh evar [Q1]. *)

Ltac xlettrm_pre tt :=
  xcheck_pull tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_trm _ _) => idtac
  end.

(* [xlettrm] *)

Definition xlettrm_typed_lemma := @MkStruct_erase.

Ltac xlettrm_core tt :=
  xlettrm_pre tt;
  eapply xlettrm_typed_lemma.

Tactic Notation "xlettrm" :=
  xlettrm_core tt.

(* [xlettrm Q1] *)

Lemma xlettrmst_lemma : forall A1 (EA1:Enc A1) (Q1:A1->hprop) H A (EA:Enc A) (Q:A->hprop) ,
  forall (F1:Formula) (F2of:A1->Formula),
  Structural F1 ->
  H ==> F1 A1 EA1 Q1 ->
  (forall (X:A1), Q1 X ==> (F2of X) A EA Q) ->
  H ==> ^(@Wpgen_let_trm F1 A1 EA1 (@F2of)) Q.
Proof using.
  introv HF1 M1 M2. applys MkStruct_erase. xchange M1.
  applys* Structural_conseq.
Qed.

Ltac xlettrmst_common Q1 cont :=
  xlettrm_pre tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_trm _ (fun x => _)) =>
     let a := fresh "v" x in
     eapply (@xlettrmst_lemma _ _ Q1);
     [ try xstructural | | intros a; cont a ]
  end.

Tactic Notation "xlettrm" constr(Q1) :=
  xlettrmst_common Q1 ltac:(fun a => idtac).

(* [xlettrm Q1 as] *)

Tactic Notation "xlettrm" constr(Q1) "as" :=
  xlettrmst_common Q1 ltac:(fun a => revert a).


(* ---------------------------------------------------------------------- *)
(** ** [xletfun] *)

(* TODO: xlet_types/xletfun_types *)

(** [xletfun] applies to a formula of the form [LetFun f := B in F].

    - [xletfun] without arguments simply saves the hypothesis about [f]
      for later use. This tactic is useful in particular when there
      is a single occurrence of [f] in the code. It can be used for
      functions and recursive functions.

    - [xletfun P] can be used to give a given specification for [f].
      Typically [P] takes the form [fun f => forall x, SPEC (f x) PRE H POST Q].

    - [xletrec P] is like [xletfun P] but it does not attempt to exploit
      the characteristic formula automatically. Instead, it leaves a chance
      for the user perform an induction by hand. Use tactic [xapp] or [apply]
      to continue the proof after [induction]. Note that the tactic [xletrec R P]
      described next performs all these operations at once.

    - [xletrec R P] is a shorthand for proving a recursive function
      by well-founded induction on the first argument quantified in [P].
      It is short for [xletrec P], followed by [intros n] and
      [induction_wf IH: R n], and then exploiting the characteristic
      formula for the body. The binary relation [R] is to be proved
      well-founded. Typical relation includes [downto 0] and [upto n]
      for induction on the type [int]. [R] can also be a measure function,
      as such functions are accepted as arguments of [induction_wf].

    - [xletrec_skip P] is a development tactic used to skip the need
      to provide a well-founded relation for justifying termination.

    - Also available, the "as" variant, allow the variables and hypotheses
      to be named explicitly:
      [xletfun as],
      [xletfun P as],
      [xletrec R P as],
      [xletrec P as],
      [xletrec_skip R P as]. *)

(* Auxiliary functions for [xletfun] and [xletrec] *)

Ltac xletfun_pre tt :=
  xcheck_pull tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_fun _) => idtac
  end.

Ltac xletfun_clean_unused_var tt :=
  match goal with |- val -> _ => intros _ end.

Ltac idcont2 f Sf := idtac.

(** [xletfun_simpl Bf] applies to a goal of the form
    [Bf: characteristic_formula_for_the_body_of_f |- SpecOf f]
    and it exploits [Bf] in order to prove the goal,
    then clears this hypothesis. *)

Ltac xletfun_simpl Bf :=
  first [ intros; eapply Bf
        | hnf; intros; eapply Bf ]; (* useful if P is an abstract definition *)
  clear Bf.

(* [xletfun_common cont] extracts the variable [f] and the CF for [f] named [Bf],
   then calls the continuation [cont] with [f] and [Bf] as arguments. *)

Lemma xletfun_lemma : forall A `{EA:Enc A} (BodyOf:forall A,Enc A->(A->hprop)->hprop) H (Q:A->hprop),
  H ==> ^(BodyOf) Q ->
  H ==> ^(Wpgen_let_fun BodyOf) Q.
Proof using. introv M. applys MkStruct_erase. applys M. Qed.

Ltac xletfun_common cont :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_fun (fun A EA Q => \forall f, _)) =>
     let a := fresh f in
     let Sa := fresh "Spec_" f in
     applys xletfun_lemma;
     applys himpl_hforall_r; intros a;
     applys hwand_hpure_r_intro; intros Sa;
     cont a Sa
  end.

(* [xletfun] *)

Ltac xletfun_core cont2 :=
  xletfun_common cont2.

Tactic Notation "xletfun" :=
  xletfun_core idcont2.

Tactic Notation "xletfun" "as" :=
  xletfun_core ltac:(fun f Sf => revert f Sf).

(* [xletfun P] *)

Lemma xletfun_cut_lemma : forall f (SpecOf:val->Prop) (Bf G:Prop),
  (Bf -> SpecOf f) ->
  (SpecOf f -> G) ->
  (Bf -> G).
Proof using. auto. Qed.

Ltac xletfun_spec_core P cont1 cont2 :=
  xletfun_common ltac:(fun f Sf =>
    revert Sf;
    applys (@xletfun_cut_lemma f P);
    [ let Bf := fresh "Body_" f in
      intros Bf;
      xletfun_simpl Bf;
      cont1 f Bf
    | intros Sf;
      cont2 f Sf ]).

Tactic Notation "xletfun" constr(P) :=
  xletfun_spec_core P idcont2 idcont2.

Tactic Notation "xletfun" constr(P) "as" :=
  xletfun_spec_core P ltac:(fun f Bf => revert f; xletfun_clean_unused_var tt) ltac:(fun f Sf => revert f Sf).

(* [xletrec P] *)

Ltac xletfun_spec_rec_core P cont1 cont2 := (* TODO: factorize?*)
  xletfun_common ltac:(fun f Sf =>
    revert Sf;
    applys (@xletfun_cut_lemma f P);
    [ let Bf := fresh "Body_" f in
      intros Bf;
      cont1 f Bf
    | intros Sf;
      cont2 f Sf ]).

Tactic Notation "xletrec" constr(P) :=
  xletfun_spec_rec_core P idcont2 idcont2.

Tactic Notation "xletrec" constr(P) "as" :=
  xletfun_spec_rec_core P ltac:(fun f Bf => revert f Bf) ltac:(fun f Sf => revert f Sf).

(* [xletrec R P] *)

Ltac xletfun_spec_ind_core R P cont1 cont2 :=
  xletfun_common ltac:(fun f Sf =>
    revert Sf;
    applys (@xletfun_cut_lemma f P);
    [ let Bf := fresh "Body_" f in
      intros Bf ?;
      let X := get_last_hyp tt in
      induction_wf_core_then R X ltac:(fun _ =>
        intros Sf;
        xletfun_simpl Bf;
        cont1 f Sf)
    | intros Sf;
      cont2 f Sf ]).

Tactic Notation "xletrec" constr(R) constr(P) :=
  xletfun_spec_ind_core R P idcont2 idcont2.

Tactic Notation "xletrec" constr(R) constr(P) "as" :=
  xletfun_spec_ind_core R P ltac:(fun f Sf => revert f Sf) ltac:(fun f Sf => revert f Sf).

(* [xletrec_skip P] *)

Lemma xletfun_cut_skip_lemma : forall f (SpecOf:val->Prop) (Bf G:Prop),
  (SpecOf f -> Bf -> SpecOf f) ->
  (SpecOf f -> G) ->
  (Bf -> G).
Admitted. (* This lemma only for development purposes *)

Ltac xletfun_spec_ind_skip_core P cont1 cont2 :=
  xletfun_common ltac:(fun f Sf =>
    revert Sf;
    applys (@xletfun_cut_skip_lemma f P);
    [ let Bf := fresh "Body_" f in
      intros Sf Bf;
      xletfun_simpl Bf;
      cont1 f Sf
    | intros Sf;
      cont2 f Sf ]).

Tactic Notation "xletrec_skip" constr(P) :=
  xletfun_spec_ind_skip_core P idcont2 idcont2.

Tactic Notation "xletrec_skip" constr(P) "as" :=
  xletfun_spec_ind_skip_core P ltac:(fun f Sf => revert f Sf) ltac:(fun f Sf => revert f Sf).


(* ---------------------------------------------------------------------- *)
(** ** [xletfuns] -- TODO: not yet developed *)

(** [xletfuns as] applies to mutually recursive functions. *)

(* TODO: [xletfun] could see by itself if there are several functions defined. *)
(* TODO: provide additional tactics like for [xletfun]? *)

Ltac xletfuns_as_core tt :=
  applys xletfun_lemma;
  pose ltac_mark;
  repeat applys himpl_hforall_r;
  repeat applys hwand_hpure_r_intro;
  gen_until_mark.

Tactic Notation "xletfuns" "as" :=
  xletfuns_as_core tt.


(************************************************************************ *)
(************************************************************************ *)
(************************************************************************ *)
(** * Generic Tactics *)

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
  | |- Triple (Trm_apps ?f ?Vs) ?H ?Q => constr:(f)
  | |- ?f = _ => constr:(f)
  | |- _ ?f => constr:(f)
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
  let Sf := fresh "Spec_" f in
  intros Sf;
  eapply Sf;
  clear Sf;
  xcf_post tt.
  (* TODO: first [ xcf_top_value f | xcf_fallback f | fail 2 ]
      where xcf_fallback is defined in CFML1's CFTactics.V *)

Ltac xcf_top_value tt :=
  let f := xcf_target tt in
  xcf_find f;
  let Sf := fresh "Spec_" f in
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
  let Sf := fresh "Spec_" f in
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

Ltac xcf_types_core tt :=  (* Also used by xapp_types *)
  let S := fresh "Spec_" in
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
(** ** Tactic [xpost] *)

(** [xpost Q] allows to weaken the current postcondition to [Q].
    If the postcondition is already an evar, it simply instantiates it.

    [xpost] allows to weaken the current postcondition to an evar. *)

Lemma xpost_lemma_inst : forall A `{EA:Enc A} (Q:A->hprop) H (F:Formula),
  H ==> ^F Q ->
  H ==> ^F Q.
Proof using. auto. Qed.

Lemma xpost_lemma : forall A `{EA:Enc A} (Q1 Q2:A->hprop) H (F:Formula),
  Structural F ->
  H ==> ^F Q1 ->
  Q1 ===> Q2 ->
  H ==> ^F Q2.
Proof using. introv M W. applys* structural_conseq. Qed.

Arguments xpost_lemma : clear implicits.

(* [xpost] *)

Ltac xpost_core cont :=
  xcheck_pull tt;
  eapply (@xpost_lemma); [ xstructural | cont tt | ].

Tactic Notation "xpost" :=
  xpost_core idcont.

(* [xpost Q] *)

Ltac xpost_arg_post Q cont :=
  match xgoal_post_is_evar tt with
  | true => eapply (@xpost_lemma_inst _ _ Q); [ cont tt ]
  | false => eapply (@xpost_lemma _ _ Q); [ xstructural | cont tt | ]
  end.

Ltac xpost_arg_core E cont :=
  match type of E with
  | hprop => xpost_arg_post (fun (_:unit) => E) cont
  | _ => xpost_arg_post E cont
  end.

Tactic Notation "xpost" constr(E) :=
  xpost_arg_core E idcont.


(************************************************************************ *)
(************************************************************************ *)
(************************************************************************ *)
(** * Basic term tactics *)


(* ---------------------------------------------------------------------- *)
(** ** Tactic [xseq] *)

(** The tactic [xseq] applies to a goal of the form [PRE H CODE (Seq F1 ; F2) POST Q].
    It produces [PRE H CODE F1 POST ?Q1] and [PRE (?Q1 tt) CODE F2 POST Q].

    The tactic [xseq H1] can be used to specify [Q1] as [fun (_:unit) => H1)]. *)

Ltac xseq_pre tt :=
  xcheck_pull tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_seq _ _) => idtac
  end.

(* [xseq] *)

Definition xseq_lemma := @MkStruct_erase.

Ltac xseq_core tt :=
  xseq_pre tt;
  applys xseq_lemma.

Tactic Notation "xseq" :=
  xseq_core tt.

(* [xseq H1] *)

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

Ltac xseq_arg_core H1 :=
  eapply (@xseq_lemma_typed_post H1); [ xstructural | | ].

Tactic Notation "xseq" constr(H1) :=
  xseq_arg_core H1.


(* ---------------------------------------------------------------------- *)
(** ** Tactic [xlet] *)

(* [xlet] applies to let-bindings for terms, for values, and for functions.
   IT leverages [xlettrm] and [xletval] and [xletfun], whose documentation
   appears earlier in this file. Forms available:

   - [xlet] for trm/val/fun.
   - [xlet as] for val/fun.
   - [xlet Q] for trm.
   - [xlet P] for val/fun.
   - [xlet P as] and [xlet Q as], similarly.
   - [xlets] for val, for performing the substitution.

   The tactics [xletrec] (short name for [xletfunrec]) were defined earlier.

   - [xletrec P] for fun, for a recursive function.
   - [xletrec R P] for fun, for a recursive function, with wf-induction integrated.
   - [xletrec_skip P] for fun, for a recursive function, to skip the termination proof.
   - [xletrec P as] and [xletrec R P as] and [xletrec_skip P as] are also available. *)

(* [xlet] *)

Ltac xlet_core tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_trm _ _) => xlettrm
  | (Wpgen_let_val _ _) => xletval
  | (Wpgen_let_fun _) => xletfun
  end.

Tactic Notation "xlet" :=
  xlet_core tt.

(* [xlet as] *)

Ltac xlet_as_core tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_trm _ _) => fail 2 "xlet as currently not supported for let-trm"
  | (Wpgen_let_val _ _) => xletval as
  | (Wpgen_let_fun _) => xletfun as
  end.

Tactic Notation "xlet" "as" :=
  xlet_as_core tt.

(* [xlet Q] or [xlet P] *)

Ltac xlet_arg_core E :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_trm _ _) => xlettrm E
  | (Wpgen_let_val _ _) => xletval E
  | (Wpgen_let_fun _) => xletfun E
  end.

Tactic Notation "xlet" constr(E) :=
  xlet_arg_core E.

(* [xlet Q as] or [xlet P as] *)

Ltac xlet_arg_as_core E :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_trm _ _) => xlettrm E as
  | (Wpgen_let_val _ _) => xletval E as
  | (Wpgen_let_fun _) => xletfun E as
  end.

Tactic Notation "xlet" constr(E) "as" :=
  xlet_arg_as_core E.

(* [xlets] *)

Ltac xlets_core tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_trm _ _) => fail 2 "xlets does not apply to let-trm"
  | (Wpgen_let_val _ _) => xletvals
  | (Wpgen_let_fun _) =>  fail 2 "xlets does not apply to let-trm"
  end.

Tactic Notation "xlets" :=
  xlets_core tt.


(* ---------------------------------------------------------------------- *)
(** ** Tactic [xlet_xseq_steps] and [xlet_xseq_xapp_steps] *)

(** [xlet_xseq_steps tt] automatically performs as many [xlet] and [xseq] as
    appropriate. *)

Ltac xlet_xseq_step tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_trm _ _) => xlettrm
  | (Wpgen_let_val _ _) => xletval
  | (Wpgen_let_fun _) => xletfun
  | (Wpgen_seq _ _) => xseq
  end.

Ltac xlet_xseq_steps tt :=
  xcheck_pull tt;
  repeat (xlet_xseq_step tt).

(** [xlet_xseq_xapp_steps tt] is similar, but includes [xapp]. *)

Ltac xif_call_xapp_first tt := (* defined further in this file *)
  fail.

Ltac xlet_xseq_xapp_step tt :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_let_trm _ _) => xlettrm
  | (Wpgen_let_val _ _) => xletval
  | (Wpgen_let_fun _) => xletfun
  | (Wpgen_seq _ _) => xseq
  | (Wpgen_app _ _ _) => xif_call_xapp_first tt
  end.

Ltac xlet_xseq_xapp_steps tt :=
  xcheck_pull tt;
  repeat (xlet_xseq_xapp_step tt).


(* ---------------------------------------------------------------------- *)
(** ** Tactic [xval] *)

(* [xval] applies to a goal of the form [PRE H CODE (Val V) POST Q].
   It emits the proof obligation [H ==> Q V].

   [xvals] combines [xval] followed with [xsimpl]. *)

(* [xval] *)

Ltac xval_pre tt :=
  xcheck_pull tt;
  xlet_xseq_steps tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_val _) => idtac
  end.

Lemma xval_lemma : forall A `{EA:Enc A} (V:A) H (Q:A->hprop),
  H ==> Q V ->
  H ==> ^(Wpgen_val V) Q.
Proof using.
  introv M. subst. applys MkStruct_erase.
  applys xcast_lemma M.
Qed.

Ltac xval_post tt :=
  xcleanup.

Ltac xval_core tt :=
  xval_pre tt;
  eapply xval_lemma;
  xval_post tt.

Tactic Notation "xval" :=
  xval_core tt.
Tactic Notation "xval" "~" :=
  xval; auto_tilde.
Tactic Notation "xval" "*"  :=
  xval; auto_star.

(** [xvals] *)

Ltac xvals_core tt :=
  xval; xsimpl.

Tactic Notation "xvals" :=
  xvals_core tt.
Tactic Notation "xvals" "~" :=
  xvals; auto_tilde.
Tactic Notation "xvals" "*"  :=
  xvals; auto_star.


(* ---------------------------------------------------------------------- *)
(** ** Tactic [xif] *)

(* [xif] applies to a goal of the form [PRE H CODE (If b then F1 else F2) POST Q].
   It generates two subgoals: [b = true -> PRE H CODE F1 POST Q]
   and [b false -> PRE H CODE F2 POST Q]. The tactic will produce an error if the
   postcondition [Q] is not instantiated---indeed, it would be a bad idea to try
   to infer [Q] from the then-branch only.

   [xif Q] allows instantiating the postcondition in case it is an evar.
   When the if-statement has return type [unit], the postcondition [Q] can be
   provided as [H] instead of [fun (_:unit) => H].

   Note: the tactic [xif] will automatically invoke not just [xlet] or [xseq],
   but also [xval] or [xapp] (once) if needed, before executing.

   Note: the boolean propositions involved in the hypotheses [b = true] and [b = false]
   may be simplified by the tactic. *) (* TODO: do we need [xif_nosimpl]? *)

Ltac xif_xmatch_pre tt :=
  xlet_xseq_xapp_steps tt;
  xcheck_pull tt; (* TODO: error message might be confusing if this check fails *)
  match xgoal_post_is_evar tt with
  | true => fail 2 "The tactic requires an instantiated postcondition; use [xpost] or pass it as argument."
  | false => idtac
  end.

Ltac xif_pre tt :=
  xif_xmatch_pre tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_if _ _ _) => idtac
  end.

Lemma xifval_lemma : forall A `{EA:Enc A} b H (Q:A->hprop) (F1 F2:Formula),
  (b = true -> H ==> ^F1 Q) ->
  (b = false -> H ==> ^F2 Q) ->
  H ==> ^(Wpgen_if b F1 F2) Q.
Proof using. introv E N. applys MkStruct_erase. case_if*. Qed.

Lemma xifval_lemma_isTrue : forall A `{EA:Enc A} (P:Prop) H (Q:A->hprop) (F1 F2:Formula),
  (P -> H ==> ^F1 Q) ->
  (~ P -> H ==> ^F2 Q) ->
  H ==> ^(Wpgen_if (isTrue P) F1 F2) Q.
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
  xlet_xseq_xapp_steps tt;
  xcheck_pull tt; (* TODO: error message might be confusing if this check fails *)
  xpost_arg_core Q ltac:(fun _ => xif_core tt).

Tactic Notation "xif" constr(Q) :=
  xif_arg_core Q.


(* ---------------------------------------------------------------------- *)
(** ** Tactic [xassert] *)

(* [xassert] applies to a goal of the form [PRE H CODE (Assert F1) POST Q].
   It generates two subgoals: [PRE H CODE F1 POST (fun r => \[r=true] \* H]
   to ensure that the body of the assertion evaluates to [true], and
   [H ==> Q tt] to ensure that if the assertions is not evaluated then it has
   no impact on the correctness of the code.

   If the postcondition [Q] is an evar, then the postcondition is instantiated
   as [fun (_:unit) => H], and the trivial proof obligation [H ==> Q tt] is
   discharged automatically. *)

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
  xcheck_pull tt;
  xlet_xseq_steps tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_assert _) => idtac
  end.

Ltac xassert_core tt :=
  xassert_pre tt;
  first [ eapply xassert_lemma_inst
        | eapply xassert_lemma ].
  (* Note: alternative implementation: test whether the post is an evar,
     then call  [xpost (fun (_:unit) => H)], and use [xsimpl] for the
     second proof obligation. *)

Tactic Notation "xassert" :=
  xassert_core tt.


(************************************************************************ *)
(************************************************************************ *)
(************************************************************************ *)
(** * Applications *)

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

(* How to DEBUG xapp:

    xspec. eapply xapp_lemma. eapply S.

     --- specialized versions: [xapps_lemma] or [xapps_lemma_pure].
*)


Ltac xapp_record tt :=
  fail "implemented later in WPStruct".

Lemma xapp_lemma : forall A `{EA:Enc A} (Q1:A->hprop) (f:val) (Vs:dyns) H1 H Q,
  Triple (Trm_apps f Vs) H1 Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  H ==> ^(Wpgen_app A f Vs) Q.
Proof using.
  introv M1 M2. applys MkStruct_erase. xchanges (rm M2).
  applys xreturn_lemma_typed. rewrite <- Triple_eq_himpl_Wp.
  applys* Triple_ramified_frame.
Qed.

Lemma xapps_lemma : forall A `{EA:Enc A} (V:A) H2 (f:val) (Vs:dyns) H1 H Q,
  Triple (Trm_apps f Vs) H1 (fun r => \[r = V] \* H2) ->
  H ==> H1 \* (H2 \-* protect (Q V)) ->
  H ==> ^(Wpgen_app A f Vs) Q.
Proof using.
  introv M1 M2. applys xapp_lemma M1. xchanges M2.
  intros ? ->. auto.
Qed.

Lemma xapps_lemma_pure : forall A `{EA:Enc A} (V:A) (f:val) (Vs:dyns) H1 H Q,
  Triple (Trm_apps f Vs) H1 (fun r => \[r = V]) ->
  H ==> H1 \* protect (Q V) ->
  H ==> ^(Wpgen_app A f Vs) Q.
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
  xlet_xseq_steps tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_app ?T ?f ?Vs) => idtac
  (* | (Wpgen_record_new ?Lof) => idtac --- added in WPRecord *)
  end.

Ltac xapp_pre_triple tt :=
  match goal with
  | |- (Triple _ _ _) => xtriple
  end.

Ltac xapp_pre tt :=
  xcheck_pull tt;
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

(** [xapp_spec] or [xapp_spec E] to show registered specification *)

Tactic Notation "xapp_spec" :=
  xspec_core tt;
  let Spec := fresh "Spec" in
  intros Spec.

Tactic Notation "xapp_spec" constr(E) :=
  xspec E;
  let Spec := fresh "Spec" in
  intros Spec.

(** [xapp_types] or [xapp_types E] to show types involved *)

Ltac xapp_types_core tt :=
  xcf_types_core tt;
  xtypes_post tt.

Tactic Notation "xapp_types" :=
  xspec_core tt;
  xapp_types_core tt. (* TODO: rename since more general *)

Tactic Notation "xapp_types" constr(E) :=
  xspec E;
  let Spec := fresh "Spec" in
  xapp_types_core tt.

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

Tactic Notation "xappn" constr(n) := (* TODO: does it work with constr? *)
  do n (try (xapp)).
Tactic Notation "xappn" "~" constr(n) :=
  do n (try (xapp; auto_tilde)).
Tactic Notation "xappn" "*" constr(n) :=
  do n (try (xapp; auto_star)).

(** Binding *)

Ltac xif_call_xapp_first tt ::=
  xapp.


(************************************************************************ *)
(************************************************************************ *)
(************************************************************************ *)
(** * Loops *)

(*

(* ---------------------------------------------------------------------- *)
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


(* ---------------------------------------------------------------------- *)
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


(* ---------------------------------------------------------------------- *)
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


(* ---------------------------------------------------------------------- *)
(** ** Tactic [xfail] *)

(** [xfail] applies to a goal of the form [PRE H CODE (Fail) POST Q].
    It turns the goal into [False].
    It proves the goal if the tactic [false] can prove it. *)


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
(** ** [xdone] *)

(** [xdone] applies to a goal of the form [PRE H CODE (Done) POST Q].
    It always proves the goal. Such goals correspond to the virtual
    "catch-all" branch of the pattern matching, in case the pattern
    matching is recognized as exhaustive by the typechecker. *)

Lemma xdone_lemma : forall A `{EA:Enc A} (Q:A->hprop) H,
  H ==> ^(Wpgen_done) Q.
Proof using.
  intros. unfold Wpgen_done. applys MkStruct_erase. xsimpl.
Qed.

Ltac xdone_core tt :=
  applys xdone_lemma.

Tactic Notation "xdone" :=
  xdone_core tt.


(* ---------------------------------------------------------------------- *)
(** ** [xcleanpat] *)

(** [xcleanpat] is a tactic for removing all the negated
    pattern assumptions, which are introduced by [xmatch] or [xcase]. *)

Ltac xcleanpat_core :=
  repeat match goal with H: Wpgen_negpat _ |- _ => clear H end.

Tactic Notation "xcleanpat" :=
  xcleanpat_core.

(* ---------------------------------------------------------------------- *)
(** ** [xalias] *)

(** [xalias] applies to a goal of the form
    [PRE H CODE (Alias x := v in F1) POST Q]. Aliases are generated by
    the "as" bindings in patterns. Such a goal is logically equivalent
    to a let-value, thus [xalias] is essentially another name for [xletval].
    The following forms are available:

    - [xalias]
    - [xalias as] to leaves the variable and equality in the goal
    - [xaliass] to substitute away [x], replacing it with [v]. *)

Lemma xalias_lemma : forall A `{EA:Enc A} (Q:A->hprop) H (F:Formula),
  H ==> ^F Q ->
  H ==> ^(Wptag (Wpgen_alias F)) Q.
Proof using. auto. Qed.

Ltac xalias_pre tt :=
  xcheck_pull tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_alias _) => idtac
  end.

Ltac xalias_common cont :=
  xalias_pre tt;
  eapply xalias_lemma;
  cont tt.

Tactic Notation "xalias" :=
  xalias_common ltac:(fun _ => xletval).

Tactic Notation "xalias" "as" :=
  xalias_common ltac:(fun _ => xletval as).

Tactic Notation "xaliass" :=
  xalias_common ltac:(fun _ => xletvals).


(* ---------------------------------------------------------------------- *)
(** ** Options for [xcase] and [xmatch] *)

(** List of possible options *)

Inductive Xcase_options : Type :=
  | Xcase_manual
  | Xcase_eq_alias
  | Xcase_no_alias
  | Xcase_no_simpl
  | Xcase_as.

(* [xcase_has_option opt options] returns a boolean indicating whether
   [opt] belongs to the list [options]. *)

Ltac xcase_has_option opt options :=
  match options with
  | opt => constr:(true)
  | cons (boxer opt) ?options' => constr:(true)
  | cons (boxer ?opt') ?options' => xcase_has_option opt options'
  | _ => constr:(false)
  end.


(* ---------------------------------------------------------------------- *)
(** ** [xcase] *)

(** [xcase] applies to a goal of the form
    [PRE H CODE (Case v is p {x1 x2} Then F1 Else F2) POST Q],
    arising from a branch of a pattern matching. The tactic produces two subgoals.

    - the first subgoal is [F1 H Q] in a context [forall x1 x2 (E : v = p), ...].
    - the first subgoal is [F2 H Q] under the hypothesis [(forall x1 x2, v <> p)].

    If a when-clause is involved for testing a boolean expression [b], then the
    proposition [v = p] becomes [(v = p) /\ b], and the proposition [v <> p] becomes
    [(v <> p) \/ !b]. The name for these propositions may be specified using the
    syntax [xcase as C].

    The tactic [xcase] attempts to simplify equalities arising from patterns;
    use [xcase Xcase_no_simpl] to keep the original equalities.

    The tactic [xcase] automatically substitutes aliases by default.
    Use [xcase Xcase_eq_alias] to introduce aliases as equality.
    Use [xcase Xcase_no_alias] to leave the aliases untouched in each branch.

    --TODO: refuse uninstantiated postconditions.

    In summary, the variants are:

    - [xcase]
    - [xcase Options]
    - [xcase as C]
    - [xcase Options as C]

    where [Options] is either a single option, or a list of options of the
    form [(>> Option1 .. OptionN)]. The available options are:

    - [Xcase_eq_alias] to introduce aliases as equalities
    - [Xcase_no_alias] to leave aliases untouched
    - [Xcase_no_simpl] to not perform any inversion, using [xcase_no_simpl]
    - [Xcase_as] to leave all names in the goal (if provided, we ignore [as C]). *)

(* TODO: improve naming policy for handling pattern variables *)

Ltac xcase_pre tt :=
  xcheck_pull tt;
  xlet_xseq_steps tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_case _ _ _) => idtac
  end.

(* [xclean_trivial_eq tt] removes equalities of the form [E = E]. *)

Ltac xclean_trivial_eq tt :=
  repeat match goal with H: ?E = ?E |- _ => clear H end.

(* [xcase_post] is a tactic that applies to an hypothesis [H] of the form
   [v = p] or [v <> p], or [(v = p) /\ b] or [(v <> p) \/ !b]. It attempts
   to derive a contradiction, or inverts equalities. *)

Ltac xcase_post H :=
  let aux1 tt := try solve [ discriminate | false; congruence ] in
  let aux2 E := symmetry in E; inverts E; xclean_trivial_eq tt in
  match type of H with
  | _ /\ _ => (* with a matching when-clause *)
      try (
        let E := fresh "E" H in
        destruct H as [H E];
        aux1 tt;
        aux2 E (* if [inverts E] fails, then we keep [(v = p) /\ b] *)
      )
  | _ =>
      aux1 tt;
      try (aux2 H)
  end.

(** [xpull_himpl_hforall_r tt] is equivalent to
    [apply himpl_hforall_r] but it preserves
    the name of the binder. *)

Ltac xpull_himpl_hforall_r tt :=
  match goal with
  | |- ?H ==> hforall (fun x => _) =>
      let a := fresh x in
      apply himpl_hforall_r;
      intro a;
      revert a
  | _ => apply himpl_hforall_r
  end.

(* [xcase_extract_hyps tt] applies to a goal [H ==> (\forall x1 x2, \[E] \-* F Q)].
   and it pulls [x1] and [x2] and [E] out of the entailment, but leaving them
   in the context. *)

Ltac xcase_extract_hyps tt :=
  pose ltac_mark;
  repeat (xpull_himpl_hforall_r tt; intro);
  apply hwand_hpure_r_intro; intro;
  gen_until_mark.

(* Implementation of [xcase_no_simpl], which processes goals in general of the form:
   [hand (\forall x1 x2, ([(v = p) /\ b] \-* (F1 Q)))
         (\[forall x1 x2, (v <> p) \/ !b] \-* (F2 Q))]. *)

Ltac xcase_no_simpl_core cont1 cont2 :=
  apply MkStruct_erase; applys himpl_hand_r;
  [ xcase_extract_hyps tt; cont1 tt
  | apply hwand_hpure_r_intro; cont2 tt ].

(* [xcase_alias] handles one alias *)

Ltac xcase_alias options :=
  match xcase_has_option Xcase_eq_alias options with
  | true => xalias (* eapply xalias_lemma; xletval *)
  | false => xaliass (* eapply xalias_lemma; xletvals *)
  end.
  (* Note: for efficiency reasons, we don't use [xalias] each time. *)
  (* Note: both xalias and xaliass leave exactly one goal *)

(* [case_aliases] handles a series of aliases *)

Ltac xcase_aliases options :=
  match xcase_has_option Xcase_no_alias options with
  | true => idtac
  | false => repeat (xcase_alias options)
  end.

(* [xcase_as_core options H cont1 cont2] processes one case *)

Ltac xcase_as_core options H cont1 cont2 :=
  let cont_simpl tt :=
    match xcase_has_option Xcase_no_simpl options with
    | true => idtac
    | false => xcase_post H
    end in
  let aux tt :=
    let mycont0 tt := introv H; cont_simpl tt in
    let mycont1 tt := mycont0 tt; xcase_aliases options; cont1 tt in
    let mycont2 tt := mycont0 tt; cont2 tt in
    xcase_no_simpl_core mycont1 mycont2
    in
  match xcase_has_option Xcase_as options with
  | true => pose ltac_mark; aux tt; gen_until_mark
  | false => aux tt
  end.

(* [xcase as H] *)

Tactic Notation "xcase" "as" ident(H) :=
  xcase_as_core (>>) H idcont idcont.

(* [xcase] *)

Tactic Notation "xcase" :=
  let H := fresh "C" in
  xcase as H.

(* [xcase options as H] *)

Tactic Notation "xcase" constr(Options) "as" ident(H) :=
  let options := list_boxer_of Options in
  xcase_as_core options H idcont idcont.

(* [xcase options] *)

Tactic Notation "xcase" constr(Options) :=
  let H := fresh "C" in
  xcase Options as H.


(* ---------------------------------------------------------------------- *)
(** ** [xmatch] *)

(** [xmatch] applies to a pattern-matching goal of the form
    [PRE H
     CODE (Match Case v is p1 Then F1
       Else Case v is p2 Then Alias y := w in F2
       Else Done/Fail)
     POST Q].
    The last case is [Done] for exhaustive matching, [Fail] otherwise.
    The matching can also include when clauses (not shown above).

    The tactic [xmatch] calls [xcase] for each of the case,
    then [xdone] or [xfail] on the last (catch-all) branch.

    The tactic [xmatch Xcase_no_cases] simply removes the [xmatch] tag
    and leaves the user work manually on the cases using [xcase], and [xfail]
    or [xdone].

    The tactic [xmatch] attempts to simplify equalities arising from patterns;
    use [xmatch Xcase_no_simpl] to keep the original equalities.

    The tactic [xmatch] automatically substitutes aliases by default.
    Use [xmatch Xcase_eq_alias] to introduce aliases as equality.
    Use [xmatch Xcase_no_alias] to leave the aliases untouched in each branch.

    Like [xif], the tactic [xmatch] will refuse to apply if the postcondition
    is not already instantiated. Use [xpost Q] to set it, or [xmatch Q].
    --TODO: maybe it is fine if only one branch remains after [xmatch]?

    In summary, the variants are:

    - [xmatch]
    - [xmatch Options]
    - [xmatch Q]
    - [xmatch Q Options]

    where [Options] is either a single option, or a list of options of the
    form [(>> Option1 .. OptionN)]. The available options are:

    - [Xcase_manual] to use [xcase] manually on each case
    - [Xcase_eq_alias] to introduce aliases as equalities
    - [Xcase_no_alias] to leave aliases untouched
    - [Xcase_no_simpl] to not perform any inversion
    - [Xcase_as] to leave all names in the goal. *)

(* [xmatch] implementation *)

Lemma xmatch_lemma : forall A `{EA:Enc A} H (F:Formula) (Q:A->hprop),
  H ==> ^F Q ->
  H ==> ^(Wptag (Wpgen_match F)) Q.
Proof using. auto. Qed.

Ltac xmatch_pre tt :=
  xif_xmatch_pre tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_match _) => idtac
  end.

(* [xmatch_cases] processes a cascade of cases *)

Ltac xmatch_cases options :=
  match xgoal_code_without_wptag tt with
  | (Wpgen_done) => xdone
  | (Wpgen_fail) => xfail
  | (Wpgen_case _ _ _) =>
      let H := fresh "C" in
      xcase_as_core options H idcont ltac:(fun _ => xmatch_cases options)
  end.

(* [xmatch_core] implements [xmatch] *)

Ltac xmatch_core options :=
  xmatch_pre tt;
  eapply xmatch_lemma;
  match xcase_has_option Xcase_manual options with
  | true => idtac
  | false =>
      match xcase_has_option Xcase_as options with
      | true => pose ltac_mark; xmatch_cases options; gen_until_mark
      | false => xmatch_cases options
      end
  end.

(* [xmatch_post_core] implements [xmatch Q] *)

Ltac xmatch_post_core Q options :=
  xlet_xseq_xapp_steps tt;
  xcheck_pull tt; (* TODO: error message might be confusing if this check fails *)
  xpost_arg_core Q ltac:(fun _ => xmatch_core options).

(* Surface syntax *)

Tactic Notation "xmatch" :=
  xmatch_core (>>).

Tactic Notation "xmatch" constr(E) :=
  match type of E with
  | Xcase_options => first [ xmatch_core (>> E) | fail 2 ]
  | list Boxer => first [ xmatch_core E | fail 2 ]
  | _ => xmatch_post_core E (>>)
  end.

Tactic Notation "xmatch" constr(Q) constr(Options) :=
  let options := list_boxer_of Options in
  xmatch_post_core Q options.



(************************************************************************ *)
(************************************************************************ *)
(************************************************************************ *)
(** * Automated processing using [xstep] and [xgo] *)

(** [xstep] applies the appropriate x-tactic.

    [xstep n] repeats n times [xstep].

    [xgo] repeats [xstep] as much as possible.

    [xcf_go] is a shorthand for calling [xcf] then [xgo]. *)

Ltac check_is_Wpgen_record_alloc F :=  (* refined in WPRecord *)
  fail.

(* Core implementation *)

Ltac xstep_once tt :=
  match goal with
  | |- ?G => match xgoal_code_without_wptag tt with
    | (Wpgen_seq _ _) => xseq
    | (Wpgen_let_trm _ _) => xlet
    | (Wpgen_let_val _ _) => xletval
    | (Wpgen_let_fun _) => xletfun
    | (Wpgen_app _ _ _) => xapp
    | (Wpgen_if _ _ _) => xif
    | (Wpgen_val _) => xval
    | (Wpgen_fail) => xfail
    | (Wpgen_alias _) => xalias
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

(* [xstep] *)

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

(* [xstep n] *)

Tactic Notation "xstep" integer(n) :=
  do n xstep.
Tactic Notation "xstep" "~" integer(n) :=
  do n (xstep~).
Tactic Notation "xstep" "*" integer(n) :=
  do n (xstep*).

(* [xgo] *)

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



(************************************************************************ *)
(************************************************************************ *)
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


(* ---------------------------------------------------------------------- *)
(** ** Internal tactic [xcast] *)

(** *)

Ltac xcast_pre tt :=
  xcheck_pull tt;
  match xgoal_code_without_wptag tt with
  | (Wpgen_cast _) => idtac
  end.

Ltac xcast_debug tt :=
  idtac "[xcast] fails to simplify due to type mismatch";
  match goal with |-
   ?H ==> (Wptag (@Wpgen_cast ?A1 ?EA1 ?X)) ?A2 ?EA2 ?Q =>
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
