(** This file is intended to be used as [Require] by every file
    that contains proofs with reMYSPECt to characteristic formulae
    generated by CFMLC. *)

From TLC Require Export LibTactics LibCore LibListZ LibInt LibSet LibMap.
From CFML Require Export WPHeader WPTactics WPBuiltin WPArray.

From CFML Require Export WPDisplay.
Global Close Scope wp_scope. (* TODO: remove *)
Global Open Scope cf_scope.

From CFML Require Export WPRecord. (* needs to be last *)
(* Open Scope heap_scope. *)
Global Open Scope record_scope.

(* TODO : also rename heap_scope to hprop_scope
   see what to import from SLF records *)



(************************************************************)
(** Registering of specifications of lifted applications *)

Notation "'RegisterSpec' f" := (Register database_spec f)
  (at level 69) : wptactics_scope.




(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Tactics for unfolding and folding representation predicates *)

(* ********************************************************************** *)
(** ** Hints for xclose *)

Inductive Xclose_hint {A:Type} (p:A) : forall (P:Prop), Type :=
  | xclose_hint : forall (P:Prop) (R_eq:P), Xclose_hint p P.

Lemma Xclose_hint_intro : forall (A:Type) (p:A) (P:Prop),
  P ->
  Xclose_hint p P.
Proof using. intros. constructor*. Qed.

Lemma Xclose_hint_elim : forall (A:Type) (p:A) (P:Prop),
  Xclose_hint p P ->
  P.
Proof using. introv []. auto. Qed.

Ltac xclose_hint_put p R_eq :=
  let H := fresh "Hint_xclose" in
  generalize (@Xclose_hint_intro _ p _ R_eq); intros H.

Ltac xclose_hint_get p cont :=
  match goal with H: Xclose_hint p ?P |- _ =>
    let R_eq := constr:(@Xclose_hint_elim _ _ _ H) in
    cont R_eq; clear H end.

Declare Scope xtactics_scope.

Notation "'Xclose_Hint' p" :=
  (@Xclose_hint _ p _) (at level 0) : xtactics_scope.

Open Scope xtactics_scope.

(*
Ltac xclose_hint_remove tt :=
  match goal with H: @Xclose_hint _ _ _ _ |- _ => clear H end.
*)


(* ********************************************************************** *)
(** ** Database *)

(** The focus database are used to register MYSPECifications
    for accessors to record fields, combined with focus/unfocus operations.
    See example/Stack/StackSized_proof.v for a demo of this feature. *)

Definition database_xopen := True.

Notation "'RegisterOpen' T" := (Register database_xopen T)
  (at level 69) : wptactics_scope.

(* ********************************************************************** *)
(** ** [xopen] *)

(** [xopen] is a tactic for applying [xchange] without having
    to explicitly MYSPECify the name of a focusing lemma.

    [xopen p] applies to a goal of the form
    [F H Q] or [H ==> H'] or [Q ===> Q'].
    It first searches for the pattern [p ~> T] in the pre-condition,
    then looks up in a database for the focus lemma [E] associated with
    the form [T], and then calls [xchange E].

    Example for registering a focusing lemma:
      Hint Extern 1 (RegisterOpen (Tree _)) => Provide tree_open.
    See [Demo_proof.v] for examples.

    Then, use: [xopen p].

    Variants:
    - [xopen_repr R_open p] will use the given opening lemma.

    - [xopen2 p] to perform [xopen p] twice. Only applies when there
      is no existentials to be extracted after the first [xopen].
 *)

(** [xopen_get_lemma R cont] involves [cont R_eq], where
    [R_eq] is the lemma bound to [R] using a command of the form
    [Hint Extern 1 (RegisterOpen R) => Provide R_eq] . *)
Ltac xopen_get_lemma R cont :=
  ltac_database_get database_xopen R;
  let R_eq := fresh "TEMP" in
  intros R_eq; cont R_eq; clear R_eq.

(** [xgoal_state tt] returns the current state.
    It extends [xgoal_pre] by also handling entailments. *)
Ltac xgoal_state tt :=
  match goal with
  | |- ?H1 ==> ?H2 => constr:(H1)
  | |- ?Q1 ===> ?Q2 => constr:(Q1)
  | _ => xgoal_pre tt
  end.

(* [xrepr_for_in p H] searches in heap predicate [H] for the
   representation predicate associated with location [p] *)
Ltac xrepr_for_in p H :=
  match H with context [ p ~> ?T ] => get_head T end.

Ltac xopen_repr_core R_eq p :=
  xclose_hint_put p R_eq;
  xchange (>> R_eq p); xpull.

Tactic Notation "xopen_repr" constr(R_eq) constr(p) :=
  xopen_repr_core R_eq p.

Ltac xopen_internal_core p cont :=
  let H := xgoal_state tt in
  let R := xrepr_for_in p H in
  xopen_get_lemma R cont.

Ltac xopen_core p :=
  xopen_internal_core p ltac:(fun R_eq =>
    xopen_repr_core R_eq p).

Tactic Notation "xopen" constr(t) :=
  xopen_core t.
Tactic Notation "xopen" "~" constr(t) :=
  xopen t; auto_tilde.
Tactic Notation "xopen" "*" constr(t) :=
  xopen t; auto_star.

Tactic Notation "xopen2" constr(x) :=
  xopen x; xopen x.
Tactic Notation "xopen2" "~" constr(x) :=
  xopen2 x; auto_tilde.
Tactic Notation "xopen2" "*" constr(x) :=
  xopen2 x; auto_star.

(* ********************************************************************** *)
(** ** [xclose] *)

(** [xclose] is the symmetrical of [xopen]. It works in the
    same way, except that it looks for an unfocusing lemma.

    [xclose p] applies to a goal of the form
    [F H Q] or [H ==> H'] or [Q ===> Q'].
    It first searches for the pattern [p ~> T] in the pre-condition,
    then looks up a Xclose_hint to get an unfocusing lemma.

    Variants:

    - [xclose p L1 .. Ln] allows to pass arguments to the unfocusing
      lemma.

    - [xclose_repr R_close p] will use the given unfocusing lemma.

    - [xcloses p] is a shortcut for [xclose p; xsimpl].

    - [xclose p1 .. pn] is short for [xclose p1; ..; xclose pn]

    - [xclose2 p] to perform [xclose p] twice.
 *)

(* [boxer_combine p args] builds a list of hint for instantiating
   a lemma. [p] denotes one hint, and [args] denotes either one
   hint or a list of hints of the form [>> arg1 .. argN]. *)
Ltac boxer_combine p args := (* LATER: rename and move *)
  match type of args with
  | list Boxer => constr:(boxer p :: args)
  | _ => constr:(boxer p :: boxer args :: nil)
  end.

Ltac xclose_repr_core R_eq p args :=
  let all_args := boxer_combine p args in
  let lemma := boxer_combine R_eq all_args in
  xchange <- lemma.

Tactic Notation "xclose_repr" constr(R_eq) constr(p) constr(args) :=
  xclose_repr_core R_eq p args.
Tactic Notation "xclose_repr" constr(R_eq) constr(p) :=
  xclose_repr R_eq p (>>).
(* LATER
Tactic Notation "xclose_repr" constr(R_eq) constr(p) constr(arg1) constr(2) :=
  xclose_repr R_eq p (>> arg1 arg2). *)
Tactic Notation "xclose_repr" "*" constr(R_eq) constr(p) :=
  xclose_repr R_eq p; auto_star.
Tactic Notation "xclose_repr" "*" constr(R_eq) constr(p) constr(args) :=
  xclose_repr R_eq p args; auto_star.

Tactic Notation "xcloses_repr" constr(R_eq) constr(p) constr(args) :=
  xclose_repr R_eq p args; xsimpl.
Tactic Notation "xcloses_repr" constr(R_eq) constr(p) :=
  xcloses_repr R_eq p (>>).
Tactic Notation "xcloses_repr" "*" constr(R_eq) constr(p) :=
  xcloses_repr R_eq p; auto_star.
Tactic Notation "xcloses_repr" "*" constr(R_eq) constr(p) constr(args) :=
  xcloses_repr R_eq p args; auto_star.

Ltac xclose_core p args :=
  xclose_hint_get p ltac:(fun R_eq =>
    xclose_repr_core R_eq p args).

Tactic Notation "xclose" constr(p) constr(args) :=
  xclose_core p args.
Tactic Notation "xclose" constr(p) :=
  xclose p (>>).
Tactic Notation "xclose" "*" constr(p) :=
  xclose p; auto_star.
Tactic Notation "xclose" "*" constr(p) constr(args) :=
  xclose p args; auto_star.

Tactic Notation "xclose" constr(t1) constr(t2) :=
  xclose t1; xclose t2.
Tactic Notation "xclose" constr(t1) constr(t2) constr(t3) :=
  xclose t1; xclose t2 t3.
Tactic Notation "xclose" constr(t1) constr(t2) constr(t3) constr(t4) :=
  xclose t1; xclose t2 t3 t4.

Tactic Notation "xclose2" constr(x) :=
  xclose x; xclose x.
Tactic Notation "xclose2" "~" constr(x) :=
  xclose2 x; auto_tilde.
Tactic Notation "xclose2" "*" constr(x) :=
  xclose2 x; auto_star.

Tactic Notation "xcloses" constr(p) constr(args) :=
  xclose p args; xsimpl.
Tactic Notation "xcloses" constr(p) :=
  xcloses p (>>).
Tactic Notation "xcloses" "*" constr(p) :=
  xcloses p; auto_star.
Tactic Notation "xcloses" "*" constr(p) constr(args) :=
  xcloses p args; auto_star.


(************************************************************)
(** DEPRECATED

(** [MYSPEC t PRE H POST Q] is a notation for [Triple t H Q] *)

Notation "'MYSPEC' t 'PRE' H 'POST' Q" :=
  (Triple t H Q)
  (at level 39, t at level 0,
  format "'[v' 'MYSPEC'  t  '/' 'PRE'  H  '/' 'POST'  Q ']'") : triple_scope.

(** [MYSPEC t PRE H POSTUNIT H2] is short for [POST (fun (_:unit) => H2)] *)

Notation "'MYSPEC' t 'PRE' H 'POSTUNIT' H2" :=
  (Triple t H (fun (_:unit) => H2))
  (at level 39, t at level 0, only parsing,
  format "'[v' 'MYSPEC'  t  '/' 'PRE'  H  '/' 'POSTUNIT'  H2 ']'") : triple_scope.

(** [MYSPEC t PRE H RET X POST H2] is short for [POST (fun x => H2)]. *)

Notation "'MYSPEC' t 'PRE' H1 'RET' v 'POST' H2" :=
  (Triple t H1 (fun r => \[r = v] \* H2))
  (at level 39, t at level 0, only parsing,
   format "'[v' 'MYSPEC'  t  '/' 'PRE'  H1  '/'  'RET'  v  '/'  'POST'  H2 ']'") : triple_scope.


(* TODO: CONFLICT when adding the following notation WITH keyword MYSPEC *)

(** [MYSPEC' t INV H POST Q] is short for [MYSPEC T PRE H POST (Q \*+ H)] *)

Notation "'MYSPEC'' t 'INV' H 'POST' Q" :=
  (Triple t H%hprop (Q \*+ H%hprop))
  (at level 69, only parsing,
   format "'[v' 'MYSPEC''  t '/' '[' 'INV'  H  ']'  '/' '[' 'POST'  Q  ']'  ']'")
   : triple_scope.

(** [MYSPEC' t PRE H1 INV H2 POST Q] is short for [MYSPEC T PRE (H1 \* H2) POST (Q \*+ H2)] *)

Notation "'MYSPEC'' t 'PRE' H1 'INV' H2 'POST' Q" :=
  (Triple t (H1 \* H2%hprop) (Q \*+ H2%hprop))
  (at level 69, only parsing,
   format "'[v' 'MYSPEC''  t '/' '[' 'PRE'  H1  ']'  '/' '[' 'INV'  H2  ']'  '/' '[' 'POST'  Q  ']'  ']'")
   : triple_scope.

(** Additional combination of [INV] with [POSTUNIT] and [RET] *)

Notation "'MYSPEC'' t 'INV' H1 'POSTUNIT' H2" :=
  (Triple t H1 (fun (_:unit) => H1 \* H2%hprop))
  (at level 69, only parsing,
   format "'[v' 'MYSPEC''  t '/' '[' 'INV'  H1 ']'  '/' '[' 'POSTUNIT'  H2  ']'  ']'")
   : triple_scope.

Notation "'MYSPEC'' t 'PRE' H1 'INV' H2 'POSTUNIT' H3" :=
  (Triple t (H1 \* H2%hprop) (fun (_:unit) => H3 \* H2%hprop))
  (at level 69, only parsing,
   format "'[v' 'MYSPEC''  t '/' '[' 'PRE'  H1  ']'  '/' '[' 'INV'  H2  ']'  '/' '[' 'POSTUNIT'  H3  ']'  ']'")
   : triple_scope.

Notation "'MYSPEC'' t 'INV' H1 'RET' v 'POST' H2" :=
  (Triple t H1%hprop (fun r => \[r = v] \* H2))
  (at level 69, only parsing,
   format "'[v' 'MYSPEC''  t '/' '[' 'INV'  H1 ']'  '/' '[' 'RET'  v  'POST'  H2  ']'  ']'")
   : triple_scope.

Notation "'MYSPEC'' t 'PRE' H1 'INV' H2 'RET' v 'POST' H3" :=
  (Triple t (H1 \* H2%hprop) (fun r => \[r = v] \* H3 \* H2%hprop))
  (at level 69, only parsing,
   format "'[v' 'MYSPEC''  t '/' '[' 'PRE'  H1  ']'  '/' '[' 'INV'  H2  ']'  '/' '[' 'RET'  v  'POST'  H3  ']'  ']'")
   : triple_scope.
*)
