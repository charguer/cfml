(**

Separation Logic Foundations

Chapter: "WPgen".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import SLFWPsem.
From TLC Require Import LibFix.

Implicit Types f : var.
Implicit Types b : bool.
Implicit Types v : val.
Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ####################################################### *)
(** * The chapter in a rush *)

(** This chapter describes the construction of a function called
    [wpgen] that effectively computes in Coq weakest preconditions.
    The formula computed by [wpgen t] is equivalent to [wp t], but
    is expressed in a way that longer refers to the source code of [t].

    Using the function [wpgen], we'll be able to carry out verification
    proofs using Separation Logic reasoning rules but without never
    needing to reason about program variables and substitutions. *)


(* ******************************************************* *)
(** ** Overview of the weakest precondition generator *)

(** [wpgen t] is defined by recursion on [t], as a function
    that expects a postcondition [Q] and returns a [hprop].
    We call "formula" the result type of [wgpen t]: *)

Definition formula := (val->hprop) -> hprop.

(** The function [wpgen] is defined as shown below.

    The definition makes use of a predicate [mkstruct] to support
    structural rules of Separation Logic. For the moment, just ignore it.

    The details of the definition will be explained in detail
    throughout the chapter. What matters for the moment is to
    get a high-level picture of the shape of the definition.

[[
    Fixpoint wpgen (t:trm) : formula :=
      mkstruct (fun Q => 
        match t with
        | trm_val v => Q v
        | trm_var x => \[False]
        | trm_fun x t1 => Q (val_fun x t1)
        | trm_fix f x t1 => Q (val_fix f x t1)
        | trm_if v0 t1 t2 =>
             \exists (b:bool), \[v0 = val_bool b]
               \* (if b then (wpgen t1) Q else (wpgen t2) Q)
        | trm_seq t1 t2 =>
             (wpgen t1) (fun v => (wpgen t2) Q)
        | trm_let x t1 t2 =>
             (wpgen t1) (fun v => (wpgen (subst x v t2)) Q)
        | trm_app t1 t2 => wp t Q
        end).
]]

    The reason we present this definition as comment is that the above
    definition is not structurally recursive (the let-binding case
    involves a substitution), hence not accepted as such by Coq.

    In the course of this chapter, we'll present two approaches to remedy the
    situation. The first approach relies on a general fixed point combinator.
    The second approach tweaks the definition to pass as extra argument a list
    of bindings and avoid the need for substitutions during the recursion
    process. For now, let us assume the [wpgen] defined and see what we aim for. *)

Module WpgenOverview.

Parameter wpgen : trm -> formula.

(** The soundness theorem that we aim for establishes that [wpgen] can be used
    to establish triples. *)

Parameter triple_of_wpgen : forall H t Q,
  H ==> wpgen t Q ->
  triple t H Q.


(* ******************************************************* *)
(** ** Overview of the [mkstruct] predicate *)

(** The definition of [wpgen] provides, for each term construct,
    a piece of formula that mimics the term reasoning rules from
    Separation Logic. Yet, for [wpgen] to be useful for carrying
    out practical verification proofs, it also needs to also support,
    somehow, the structural rules of Separation Logic.
    The predicate [mkstruct] serves exactly that purpose.
    It is inserted at every "node" in the construction of the 
    formual [wpgen t]. In other words, [wpgen t] always takes the
    form [mkstruct F] for some formula [F], and for any subterm [t1]
    of [t], the recursive call [wpgen t1] yields a formula of the
    form [mkstruct F1]. 

    In what follows, we present the properties expected of [mkstruct],
    and present a simple definition that satisfies the targeted property. *)

(** Recall from the previous chapter that the ramified rule for [wp],
    stated below, captures in a single line all the structural properties
    of Separation Logic. *)

Parameter wp_ramified : forall t Q1 Q2,
  (wp t Q1) \* (Q1 \--* Q2 \*+ \Top) ==> (wp t Q2).

(** If [wpgen] were to satisfy this same property like [wp], then it would
    also capture the expressive power of all the structural rules of 
    Separation Logic. In other words, we would like to have: *)

Parameter wpgen_ramified : forall t Q1 Q2,
  (wpgen t Q1) \* (Q1 \--* Q2 \*+ \Top) ==> (wpgen t Q2).

End WpgenOverview.

(** We have set up [wpgen] so that [wpgen t] is always of the form [mkstruct F]
    for some formula [F]. Thus, to ensure the above entailment, it suffices
    for the definition of [mkstruct] to be a "formula transformer" (more generally
    known as a "predicate transformer") of type [formula->formula] such that:
[[
    Parameter mkstruct_ramified : forall F Q1 Q2,
      (mkstruct F Q1) \* (Q1 \--* Q2 \*+ \Top) ==> (mkstruct F Q2).
]]
    At the same time, in a situation where we do not need to apply any structural
    rule, we'd like to be able to get rid of the leading [mkstruct] in the formula
    produced by [wpgen]. Concretely, we need:

[[
    Lemma mkstruct_erase : forall F Q,
      F Q ==> mkstruct F Q.
]] *)

(** The following definition of [mkmklocal] satisfy the above two properties.
    The tactic [hsimpl] trivializes the proofs. Details are discussed further on. *)

Definition mkstruct (F:formula) : formula := fun (Q:val->hprop) =>
  \exists Q', F Q' \* (Q' \--* (Q \*+ \Top)).

Lemma mkstruct_ramified : forall Q1 Q2 F,
  (mkstruct F Q1) \* (Q1 \--* Q2 \*+ \Top) ==> (mkstruct F Q2).
Proof using. unfold mkstruct. hsimpl. Qed.

Lemma mkstruct_erase : forall Q F,
  F Q ==> mkstruct F Q.
Proof using. unfolds mkstruct. hsimpl. Qed.

Arguments mkstruct_erase : clear implicits.
Arguments mkstruct_ramified : clear implicits.


(* ******************************************************* *)
(** ** Demo of practical proofs using [wpgen]. *)

(** At this point, it may be a good time to illustrate how to
    carry out the proof of the function [mysucc] from [SLFRules],
    this time with help of our [wpgen] function. The proof with
    x-tactics appears further down in the file (reach "THE_DEMO"). 
    However, this demo may not be necessary for anyone who has 
    already experienced verification using CFML's x-tactics. *)


(* ####################################################### *)
(** * Details of the definition of [wpgen] and soundness proof *)

(* ******************************************************* *)
(** ** General structure *)

(** The general shape of the definition of [wpgen] is a
    recursive function on [t], with recursive calls for
    the subterms. The auxiliary functions named [wpgen_val],
    [wpgen_if], etc... describe the body of [wpgen t] for
    each term construct that [t] could be.
    (For the time being, you may forget about [mkstruct].)

[[
  Fixpoint wpgen (t:trm) : formula :=
    mkstruct (match t with
    | trm_val v => wpgen_val v
    | trm_seq t1 t2 => wpgen_seq (wpgen t1) (wpgen t2)
    | trm_if v0 t1 t2 => wpgen_if v0 (wpgen t1) (wpgen t2)
    | ...
    end).
]]
*)

(** Recall the soundness theorem that we aim for:
[[
    Parameter triple_of_wpgen : forall H t Q,
      H ==> wpgen t Q ->
      triple t H Q.
]]
    Because [triple t H Q] is equivalent to [H ==> wp t Q],
    it is sufficient to prove [wpgen t Q ==> wp t Q].

    To factorize statements and improve readibility during the
    inductive proof, let us introduce the following definition,
    which captures the fact that a formula [F] (for example [wpgen t])
    is sound for a term [t]. *)

Definition formula_sound_for (t:trm) (F:formula) : Prop :=
  forall Q, F Q ==> wp t Q.

(** The soundness theorem then reformulates as 
    [forall t, formula_sound_for t (wpgen t)].

    For each auxiliary function, we'll have a soundness lemma.
    For example, for [trm_val], we'll prove:
    [forall v, formula_sound_for [trm_val v] (wpgen_val v)].

    Likewise, we'll have a soundness lemma for [mkstruct]:
    [formula_sound_for t F -> formula_sound_for t (mkstruct F)]. *)

(** In what follows, we present the definition of each of the
    auxiliary functions involved, one per term construct. *)


(* ******************************************************* *)
(** ** Case of values and functions *)

(** First, consider a value [v]. Recall the [wp] of a value. *)

Parameter wp_val : forall v Q,
  Q v ==> wp (trm_val v) Q.

(** The auxiliary function [wpgen_val] is such that the expression
    [wpgen (trm_val v) Q] evaluates to [wpgen_val v Q].
    Since [wpgen (trm_val v) Q] should entail [wp (trm_val v) Q],
    this suggests the definition of [wpgen_val v Q] as [Q v]. *)

Definition wpgen_val (v:val) : formula := fun Q =>
  Q v.

(** Let us check the desired soundness property. *)

Lemma wpgen_val_sound : forall v,
  formula_sound_for (trm_val v) (wpgen_val v).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_val. Qed.

(** The case of functions is very similar. Recall the [wp] for [trm_fun]. *)

Parameter wp_fun : forall x t Q,
  Q (val_fun x t) ==> wp (trm_fun x t) Q.

(** The value of [wpgen (trm_fun x t) Q] may thus be computed as
    [wpgen_val (val_fun x t)]. Formally: *)

Lemma wpgen_fun_sound : forall x t,
  formula_sound_for (trm_fun x t) (wpgen_val (val_fun x t)).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_fun. Qed.

(** Likewise for recursive functions. *)

Lemma wpgen_fix_sound : forall f x t,
  formula_sound_for (trm_fix f x t) (wpgen_val (val_fix f x t)).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_fix. Qed.


(* ******************************************************* *)
(** ** Case of sequences and let-bindings *)

(** Consider a sequence [trm_seq t1 t2]. Recall the rule. *)

Parameter wp_seq : forall t1 t2 Q,
  wp t1 (fun r => wp t2 Q) ==> wp (trm_seq t1 t2) Q.

(** The auxiliary function [wpgen_seq] is such that 
    [wpgen (trm_seq t1 t2) Q] evaluates to 
    [wpgen_seq (wpgen t1) (wpgen t2) Q].

    The rule above suggests that the latter should be defined as:
    [(wpgen t1) (fun r => (wpgen t2 Q))].
    If we let [F1] denote [wpgen t1] and [F2] denote [wpgen t2],
    the formula becomes [F1 (fun r => F2 Q)]. Thus, we let: *)

Definition wpgen_seq (F1 F2:formula) : formula := fun Q =>
  F1 (fun v => F2 Q).

(** When we try to prove that [wpgen_seq F1 F2] is a sound formula
    for [trm_seq t1 t2], we may assume, by induction hypothesis,
    that [F1] is a sound formula for [t1], and [F2] is a sound
    formula for [t2]. The soundness result thus takes the following form. *)

Lemma wpgen_seq_sound : forall F1 F2 t1 t2,
  formula_sound_for t1 F1 ->
  formula_sound_for t2 F2 ->
  formula_sound_for (trm_seq t1 t2) (wpgen_seq F1 F2).
Proof using.
  introv S1 S2. intros Q. unfolds wpgen_seq. applys himpl_trans wp_seq.
  applys himpl_trans S1. applys wp_conseq. intros v. applys S2.
Qed.

(** The case of let-bindings is similar, only with the substitution
    to handle. Recall the rule. *)

Parameter wp_let : forall x t1 t2 Q,
  wp t1 (fun v => wp (subst x v t2) Q) ==> wp (trm_let x t1 t2) Q.

(** This definition suggests [wpgen (trm_let x t1 t2) Q] to be of
    the form [wpgen t1 (fun v => wpgen (subst x v t2) Q)].

    Let [F1] denote [wpgen t1] and [F2of] denote [fun v => wpgen (subst x v t2)].
    The above formula is equivalent to: [F1 (fun v => F2of v Q)].

    The auxiliary function [wpgen_let] is set up to take [F1] and [F2of]
    as arguments. *)

Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := fun Q =>
  F1 (fun v => F2of v Q).

(** The soundness result takes the following form.
    It assumes that [F1] is a sound formula for [t1] and that
    [F2of v] is a sound formula for [subst x v t2], for any [v]. 
    The proof script is essentially the same as for sequences. *)

Lemma wpgen_let_sound : forall F1 F2of x t1 t2,
  formula_sound_for t1 F1 ->
  (forall v, formula_sound_for (subst x v t2) (F2of v)) ->
  formula_sound_for (trm_let x t1 t2) (wpgen_let F1 F2of).
Proof using.
  introv S1 S2. intros Q. unfolds wpgen_let. applys himpl_trans wp_let.
  applys himpl_trans S1. applys wp_conseq. intros v. applys S2.
Qed.


(* ******************************************************* *)
(** ** Case of conditionals *)

(** Consider an expression of the form [trm_if (val_bool b) t1 t2].
    Recall the reasoning rule for conditionals, specifically
    the version expressed that makes the subexpressions
    [wp t1 Q] and [wp t2 Q] visible. *)

Parameter wp_if' : forall b t1 t2 Q,
  (if b then wp t1 Q else wp t2 Q) ==> wp (trm_if b t1 t2) Q.

(** The expression [wpgen (trm_if (val_bool b) t1 t2) Q] should 
    thus evaluate to [if b then (wpgen t1) Q else (wpgen t2) Q].
    If we let [F1] and [F2] denote [wpgen t1] and [wpgen t2], respectively,
    we obtain the formula [if b then F1 Q else F2 Q].

    Yet, it would be insufficient (in the sense "incomplete") for [wpgen] 
    to only treat conditionals of the form [trm_if (val_bool b) t1 t2].
    Indeed, a source program in A-normal form may involve expressions of
    the form [trm_if v0 then t1 else t2], where [v0] could be a variable
    and not necessarily a boolean value. If [v0] is a variable,
    by the time the [wpgen] function reaches it, it should already have
    been substituted in by a value (recall the [subst] in the treatment
    of let-bindings). Thus, we may assume here [v0] to be a value.
    However, this value [v0] may not be syntactically of the form [val_bool b].
    We may only assume that, when reasoning about the conditional, the user
    is able to prove that [v0] is semantically equal to [val_bool b] for some [b].
    In other words, all we can assume is that [exists b, v0 = val_bool b].

    This discussion leads us to define [wpgen (trm_if v0 t1 t2)] as
    [wpgen_if v0 F1 F2], where [F1] denotes [wpgen t1] and [F2] denotes
    [wpgen t2] and [wpgen_if] is defined as: *)

Definition wpgen_if (v:val) (F1 F2:formula) : formula := fun Q =>
  \exists (b:bool), \[v = val_bool b] \* (if b then F1 Q else F2 Q).

(** The soundness proof extracts the information from the hypothesis
    [\exists (b:bool), \[v = val_bool b] ] and concludes using [wp_if]. *)

Lemma wpgen_if_sound : forall F1 F2 v0 t1 t2,
  formula_sound_for t1 F1 ->
  formula_sound_for t2 F2 ->
  formula_sound_for (trm_if v0 t1 t2) (wpgen_if v0 F1 F2).
Proof using.
  introv S1 S2. intros Q. unfold wpgen_if. hpull. intros b ->.
  applys himpl_trans wp_if. case_if. { applys S1. } { applys S2. }
Qed.


(* ******************************************************* *)
(** ** Case of variables *)

(** What should be the weakest precondition of a free variable [x]?
    There is no reasoning rule of the form [triple (trm_var x) H Q].
    Indeed, if a program execution reaches a dandling free variable,
    then the program is stuck.

    Yet, the weakest precondition for a variable needs to be defined,
    somehow. If we really need to introduce a triple for free variables, 
    it could be one with the premise [False]:
[[
              False
      ----------------------
      triple (trm_var x) H Q
]]
    The corresponding weakest-precondition rule would be:
[[
    \[False] ==> wp (trm_var x) Q
]]

    This observation suggests to define [wpgen (trm_var x) Q] as 
    [\[False]]. Let us name [wpgen_fail] the formula [fun Q => \[False]]. *)

Definition wpgen_fail : formula := fun Q =>
  \[False].

(** The function [wpgen] will thus treat variables as follows:
[[
      Fixpoint wpgen (t:trm) : formula :=
        match t with
        | trm_var x => wpgen_fail
        ...
        end.
]]

    The formula [wpgen_fail] is a sound formula not just for
    a variable [trm_var x], but in fact for any term [t].
    Indeed, if [\[False] ==> wp t Q] is always true. *)

Lemma wpgen_fail_sound : forall t,
  formula_sound_for t wpgen_fail.
Proof using. intros. intros Q. unfold wpgen_fail. hpull. Qed.


(* ******************************************************* *)
(** ** Case of applications *)

(** What should be the weakest precondition for an application?
    Well, it depends on the function, and how this function was
    specified. Yet, when constructing the weakest precondition
    by induction on [t], we have no specification at hand.

    We would like to just postpone the reasoning on an application
    until we have established specifications for the function being
    applied. The way we implement the postponing is by defining
    [wpgen (trm_app t1 t2)] as [wp (trm_app t1 t2)]. In other words,
    we fall back to the semantic definition of [wp].

    We define:

[[
  Fixpoint wpgen (t:trm) : formula :=
    match t with
    | trm_app t1 t2 => wp t
    ...
    end.
]]

    As we prove, [wp t] is always a sound formula for a term [t].
*)

Lemma wp_sound : forall t,
  formula_sound_for t (wp t).
Proof using. intros. intros Q. applys himpl_refl. Qed.

(** Remark: recall that we consider terms in A-normal form, thus [t1]
    and [t2] are assumed to be variables at the point where [wgpen]
    reaches the application [trm_app t1 t2]. If [t1] and [t2] could
    be general terms, we would need to call [wpgen] recursively,
    essentially encoding [let x1 = t1 in let x2 = t2 in trm_app x1 x2]. *)


(* ******************************************************* *)
(** ** Soundness of the [mkstruct] predicate transformer *)

(** We need to justify that the addition of [mkstruct] to the head
    of every call to [wpgen] preserves the entailment [wpgen t Q ==> wp t Q].
    To that end, we need to prove that, for any [F], the entailment
    [mkstruct F Q ==> wp t Q] is derivable from the entailment [F Q ==> wp t Q].

    Equivalently, this soundness property can be formulated in the form:
    [formula_sound_for t F -> formula_sound_for t (mkstruct F)],
    or simply [mkstruct F Q ==> F Q]. 

    (Remark: this entailment is the opposite to [mkstruct_erase]) *)

Lemma mkstruct_sound : forall t F,
  formula_sound_for t F ->
  formula_sound_for t (mkstruct F).
Proof using.
  introv M. intros Q. unfold mkstruct. hsimpl ;=> Q'.
  lets N: M Q'. hchange N. applys wp_ramified.
Qed.


(* ******************************************************* *)
(** ** A simple yet non-structurally recursive definition of [wpgen] *)

Module WPgenSubst.

(** We are almost ready to formally define our function [wpgen].
    There are two Coq-specific caveat on our way, however. 

    First, the definition of [wpgen] is not structurally recursive.
    Thus, we'll have to play some tricks to first define it as a functional,
    and then take the fixed point of this functional. The details of this
    fixed point construction are not essential for the moment; they are
    explained further in this chapter. In any case, we will shortly
    afterwards present an alternative definition to [wpgen] which is
    slightly more complex yet structurally recursive.

    Second, the definition of [wpgen] as a pattern matching on terms
    forces us to reveal our general grammar of terms. Indeed, Coq does
    not support notations in the grammar of patterns. We will put as
    comment the intended pattern, and write down the underlying pattern.
    (These patterns reveals the support for n-ary functions and applications,
    and the factorization between functions and recursive functions,
    and between [trm_seq] and [trm_let].) *)

Definition Wpgen wpgen (t:trm) : formula :=
  mkstruct
  match t with
  | (* [trm_val v] => *)  trm_val v =>
       wpgen_val v
  | (* [trm_var x] => *)  trm_var x =>
       wpgen_fail
  | (* [trm_fun x t1] => *)  trm_fixs bind_anon (x::nil) t1 =>
       wpgen_val (val_fun x t1)
  | (* [trm_fix f x t1] => *)  trm_fixs (bind_var f) (x::nil) t1 =>
       wpgen_val (val_fix f x t1)
  | (* [trm_if v0 t1 t2] => *)  trm_if (trm_val v0) t1 t2 =>
       wpgen_if v0 (wpgen t1) (wpgen t2)
  | (* [trm_seq t1 t2] => *)  trm_let bind_anon t1 t2 =>
       wpgen_seq (wpgen t1) (wpgen t2)
  | (* [trm_let x t1 t2] => *)  trm_let (bind_var x) t1 t2 =>
       wpgen_let (wpgen t1) (fun v => wpgen (subst x v t2))
  | (* [trm_app t1 t2] => *)  trm_apps t1 (t2::nil) => 
       wp t
  | (* other terms are outside of the sub-language that we consider,
       so let us here pretend that they are no such terms. *)
    _ => wpgen_fail
  end.

Definition wpgen := FixFun Wpgen.

(** The fixed point equation, which enables unfolding the definition
    of [wpgen], is proved further in this file. *)

Parameter wpgen_fix : forall t, 
  wpgen t = Wpgen wpgen t.

(** We establish the soundness of [wpgen] by induction on [t].
    The induction principle that comes with the sublanguage 
    presented in [SLFRules] is as follows: *)

Parameter trm_induct : forall (P : trm -> Prop),
  (forall v, P (trm_val v)) ->
  (forall x, P (trm_var x)) ->
  (forall x t1 , P t1 -> P (trm_fun x t1)) ->
  (forall (f:var) x t1, P t1 -> P (trm_fix f x t1)) ->
  (forall t1, P t1 -> forall t2, P t2 -> P (trm_app t1 t2)) ->
  (forall t1, P t1 -> forall t2, P t2 -> P (trm_seq t1 t2)) ->
  (forall (x:var) t1, P t1 -> forall t2, P t2 -> P (trm_let x t1 t2)) ->
  (forall v t1, P t1 -> forall t2, P t2 -> P (trm_if v t1 t2)) ->  
  (forall t, P t).

(** However, it does not quite suite our needs. Indeed, in the case
    of a [trm_let x t1 t2], the induction principle applies to [t2],
    but we need to invoke it on [subst x v t2].

    We thus exploit a variant induction principle, justified by an
    induction on the size of a term, for a definition of size where
    all values and functions are considered to be of size one unit.

    This induction principle is stated below. The details of its proof
    are not essential here; they may be found in the appendix to the 
    present chapter. *)

Parameter trm_induct_subst : forall (P : trm -> Prop),
  (forall v, P (trm_val v)) ->
  (forall x, P (trm_var x)) ->
  (forall x t1 , P (trm_fun x t1)) ->
  (forall (f:var) x t1, P (trm_fix f x t1)) ->
  (forall t1, P t1 -> forall t2, P t2 -> P (trm_app t1 t2)) ->
  (forall t1, P t1 -> forall t2, P t2 -> P (trm_seq t1 t2)) ->
  (forall (x:var) t1, P t1 -> forall t2, (forall v, P (subst x v t2)) -> P (trm_let x t1 t2)) ->
  (forall v t1, P t1 -> forall t2, P t2 -> P (trm_if v t1 t2)) ->  
  (forall t, P t).

(** The soundness lemma asserts that [H ==> wpgen t Q] implies
    [triple t H Q]. Recall that, equivalently, it can be formulated as:
    [forall t, formula_sound_for t (wpgen t)].

    The proof is carried out by induction on [t]. For each term
    construct, the proof consists of invoking the lemma [mkstruct_sound]
    to justify soundness of the leading [mkstruct], then invoking
    the soundness lemma specific to that term construct. *)

Lemma wpgen_sound : forall t,
  formula_sound_for t (wpgen t).
Proof using.
  intros. induction t using trm_induct_subst;
   rewrite wpgen_fix; applys mkstruct_sound; simpl.
  { applys wpgen_val_sound. }
  { applys wpgen_fail_sound. }
  { applys wpgen_fun_sound. }
  { applys wpgen_fix_sound. }
  { applys wp_sound. }
  { applys wpgen_seq_sound. { applys IHt1. } { applys IHt2. } }
  { applys wpgen_let_sound. { applys IHt1. } { intros v. applys H. } }
  { applys wpgen_if_sound. { applys IHt1. } { applys IHt2. } }
Qed.

Theorem triple_of_wpgen : forall t H Q,
  H ==> wpgen t Q ->
  triple t H Q.
Proof using. introv M. rewrite wp_equiv. hchange M. applys wpgen_sound. Qed.

End WPgenSubst.


(* ******************************************************* *)
(** ** Definition of [wpgen] as a structurally-recursive function *)

(** We next present an alternative definition to [wpgen] that has
    two important benefits. First, it is structurally recursive,
    thus easier to define in Coq, and more efficient to compute with.
    Second, it performs substitutions easily rather than eagerly,
    improving the asymptotic complexity. 

    The new function takes the form [wpgen E t], where [E] denotes a
    set of bindings from variables to values. Ideally, a "context" [E]
    should be represented using a binary tree, leading to a [wpgen]
    function running in O(n log n) compared with O(n^2) for the previous
    definition which performs substitution during the recursion process.

    However, for simplicity, we will here represent contexts using
    simple association lists. *)

Definition ctx : Type := list (var*val).

(** On contexts, we'll need two basic operations: lookup and removal.

    [lookup x E] returns [Some v] if [x] maps to [v] in [E],
    and [None] if no value is bound to [x]. *)

Fixpoint lookup (x:var) (E:ctx) : option val :=
  match E with
  | nil => None
  | (y,v)::E1 => if var_eq x y
                   then Some v
                   else lookup x E1
  end.

(** [rem x E] removes from [E] all the bindings on [x]. *)

Fixpoint rem (x:var) (E:ctx) : ctx :=
  match E with
  | nil => nil
  | (y,v)::E1 =>
      let E1' := rem x E1 in
      if var_eq x y then E1' else (y,v)::E1'
  end.

(** In order to define [wpgen], we'll also need to define the
    "substitution for a context" function, written [isubst E t].
    This function could be defined by iteratively substituting
    each of the bindings in [E]. However, to simplify the proofs
    and improve efficiency, this function is defined by induction
    on the structure of [t].

    - When reaching a variable, [isubst E (trm_var x)] performs
      a lookup for [x] in [E].
    - When traversing a binding (e.g., to handle [let x = t1 in t2]),
      the bound name is removed from the context (e.g., the recursive
      call is on (rem x E) t2]). *)

Fixpoint isubst (E:ctx) (t:trm) : trm :=
  match t with
  | (* [trm_val v] => *)  trm_val v =>
       v
  | (* [trm_var x] => *)  trm_var x =>
       match lookup x E with
       | None => t
       | Some v => v
       end
  | (* [trm_fun x t1] => *)  trm_fixs bind_anon (x::nil) t1 =>
       trm_fun x (isubst (rem x E) t1)
  | (* [trm_fix f x t1] => *)  trm_fixs (bind_var f) (x::nil) t1 =>
       trm_fix f x (isubst (rem x (rem f E)) t1)
  | (* [trm_if v0 t1 t2] => *)  trm_if (trm_val v0) t1 t2 =>
       trm_if v0 (isubst E t1) (isubst E t2)
  | (* [trm_seq t1 t2] => *)  trm_let bind_anon t1 t2 =>
       trm_seq (isubst E t1) (isubst E t2)
  | (* [trm_let x t1 t2] => *)  trm_let (bind_var x) t1 t2 =>
       trm_let x (isubst E t1) (isubst (rem x E) t2)
  | (* [trm_app t1 t2] => *)  trm_apps t1 (t2::nil) => 
       trm_app (isubst E t1) (isubst E t2)
  (* Other terms are outside of the sub-language that we consider,
     so let us here pretend that they are no such terms.
     Nevertheless, we add support for n-ary applications, so as
     to be able to consider interesting demos. *)
  | trm_apps t1 ts => 
       trm_apps (isubst E t1) (List.map (isubst E) ts)
  | _ => t
  end.

(** The new definition of [wpgen] is similar in structure to the previous
    one, with four major changes. In [wpgen E t]:

    - The extra argument [E] keeps track of the substitutions that
      morally should have been formed in [t]. As we formalize further,
      [wpgen E t] provides a weakest precondition for [isubst E t].

    - When reaching a function [trm_fun x t1], we invoke [wpgen_val]
      not on [val_fun x t1], but on the function value that 
      corresponds to the function term [isubst E (trm_fun x t1)],
      that is, to [val_fun x (isubst (rem x E) t1].

    - When traversing a binder (e.g., [trm_let x t1 t2]), the recursive
      call is performed on an extended context (e.g., [wpgen ((x,v)::E) t2]).
      In comparison, the prior definition of [wpgen] would involve a 
      substitution before the recursive call (e.g., [wpgen (subst x b t2)]).

    - When reaching a variable [trm_var x], we compute the lookup of [x]
      in [E]. We expect [x] to be bound to some value [v], and return
      [wpgen_val v]. If [x] is unbound, then it is a dandling free variable
      so we return [wpgen_fail]. The treatment of variables is captured
      by the following auxiliary definition. *)

Definition wpgen_var (E:ctx) (x:var) : formula :=
  match lookup x E with
  | None => wpgen_fail
  | Some v => wpgen_val v
  end.

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  mkstruct match t with
  | (* [trm_val v] => *)  trm_val v =>
       wpgen_val v
  | (* [trm_var x] => *)  trm_var x =>
       wpgen_var E x
  | (* [trm_fun x t1] => *)  trm_fixs bind_anon (x::nil) t1 =>
       wpgen_val (val_fun x (isubst (rem x E) t1))
  | (* [trm_fix f x t1] => *)  trm_fixs (bind_var f) (x::nil) t1 =>
       wpgen_val (val_fix f x (isubst (rem x (rem f E)) t1))
  | (* [trm_if v0 t1 t2] => *)  trm_if (trm_val v0) t1 t2 =>
       wpgen_if v0 (wpgen E t1) (wpgen E t2)
  | (* [trm_seq t1 t2] => *)  trm_let bind_anon t1 t2 =>
       wpgen_seq (wpgen E t1) (wpgen E t2)
  | (* [trm_let x t1 t2] => *)  trm_let (bind_var x) t1 t2 =>
       wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
  | (* [trm_app t1 t2] => *)  trm_apps t1 ts => 
       wp (isubst E t)
  | (* Other terms are outside of the sub-language that we consider,
       so let us here pretend that they are no such terms. 
       Note the exception in the [trm_app] case, whose pattern we encode
       as [trm_apps t1 ts] to support n-ary applications. *)
    _ => wpgen_fail
  end.

(** In order to establish the soundness of this new definition of [wpgen],
    we need to exploit two basic properties of substitution.
    First, the substitution for the empty context is the identity.
    Second, the substitution for [(x,v)::E] is the same as the 
    substitution for [rem x E] followed with a substitution of [x] by [v].
    The proof of these technical lemmas is given in appendix.
    (The second one reveals quite tricky to obtain.) *)

Parameter isubst_nil : forall t,
  isubst nil t = t.

Parameter isubst_rem : forall x v E t,
  isubst ((x,v)::E) t = subst x v (isubst (rem x E) t).

(** We prove the soundness of [wpgen E t] by structural induction on [t].
    The induction principle that we wish to use is that associated
    with the sublanguage presented in [SLFRules], whose inductive
    definition comes with the following induction principle. *)

Parameter trm_induct : forall (P : trm -> Prop),
  (forall v, P (trm_val v)) ->
  (forall x, P (trm_var x)) ->
  (forall x t1 , P t1 -> P (trm_fun x t1)) ->
  (forall (f:var) x t1, P t1 -> P (trm_fix f x t1)) ->
  (forall t1, P t1 -> forall t2, P t2 -> P (trm_app t1 t2)) ->
  (forall t1, P t1 -> forall t2, P t2 -> P (trm_seq t1 t2)) ->
  (forall (x:var) t1, P t1 -> forall t2, P t2 -> P (trm_let x t1 t2)) ->
  (forall v t1, P t1 -> forall t2, P t2 -> P (trm_if v t1 t2)) ->  
  (forall t, P t).

(** The soundness lemma asserts that [H ==> wpgen t Q] implies
    [triple (isubst E t) H Q]. Equivalently, it can be formulated as:
    [forall t, formula_sound_for (isubst E t) (wpgen t)].

    Appart from the induction that is now structural, the proof script
    is relatively similar to before. Only the treatment of the variable
    case and of the binding traversal differ. *)

Lemma wpgen_sound : forall E t,
  formula_sound_for (isubst E t) (wpgen E t).
Proof using.
  intros. gen E. induction t using trm_induct; intros; simpl; 
   applys mkstruct_sound.
  { applys wpgen_val_sound. } 
  { unfold wpgen_var. case_eq (lookup x E).
    { intros v EQ. applys wpgen_val_sound. }
    { intros N. applys wpgen_fail_sound. } }
  { applys wpgen_fun_sound. } 
  { applys wpgen_fix_sound. }
  { applys wp_sound. }
  { applys wpgen_seq_sound. { applys IHt1. } { applys IHt2. } }
  { applys wpgen_let_sound.
    { applys IHt1. }
    { intros v. rewrite <- isubst_rem. applys IHt2. } }
  { applys wpgen_if_sound. { applys IHt1. } { applys IHt2. } }
Qed.

(** The final result for closed terms asserts that [wpgen nil t]
    computes a weakest precondition for [t], in the sense that
    [H ==> wpgen nil t Q] implies [triple t H Q]. *)

Theorem triple_of_wpgen : forall t H Q,
  H ==> wpgen nil t Q ->
  triple t H Q.
Proof using.
  introv M. rewrite wp_equiv. hchange M.
  lets N: (wpgen_sound nil t). rewrite isubst_nil in N. applys N.
  (* same as: [applys_eq wpgen_sound 1. rewrite~ isubst_nil.] *)
Qed.


(* ####################################################### *)
(** * Practical proofs using [wpgen] *)

Module ExampleProofs.

Import NotationForVariables NotationForTerms CoercionsFromStrings.
Implicit Types n : int.


(* ******************************************************* *)
(** ** Lemmas for handling [wpgen] goals *)

(** For each term construct, and for [mkstruct], we introduce
    a dedicated lemma, called "x-lemma", to help with the 
    elimination of the construct. *)

(** [xstruct_lemma] is a reformulation of [mkstruct_erase]. *)

Lemma xstruct_lemma : forall F H Q,
  H ==> F Q ->
  H ==> mkstruct F Q.
Proof using. introv M. hchange M. applys mkstruct_erase. Qed.

(** [xlet_lemma] reformulates the definition of [wpgen_let].
    It just unfolds the definition. *)

Lemma xlet_lemma : forall H F1 F2of Q,
  H ==> F1 (fun v => F2of v Q) ->
  H ==> wpgen_let F1 F2of Q.
Proof using. introv M. hchange M. Qed.

(** Likewise, [xseq_lemma] reformulates [wpgen_seq]. *)

Lemma xseq_lemma : forall H F1 F2 Q,
  H ==> F1 (fun v => F2 Q) ->
  H ==> wpgen_seq F1 F2 Q.
Proof using. introv M. hchange M. Qed.

(** [xapp_lemma] reformulates the ramified frame rule, with a goal
    as a [wp] (which is produced by [wpgen] on an application),
    and a premise as a triple (because triples are used to state 
    specification lemmas. Observe that the rule includes an identity
    function called [protect], which is used to prevent [hsimpl]
    from performing too aggressive simplifications. *)

Lemma xapp_lemma : forall t Q1 H1 H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  H ==> wp t Q.
Proof using. introv M W. rewrite <- wp_equiv. applys~ triple_ramified_frame M. Qed.

(** The [hsimpl'] tactic is a variant of [hsimpl] that clears the
    identity tag [protect] upon completion. *)

Ltac hsimpl' := hsimpl; unfold protect.

(** [xcf_lemma] is a variant of [wpgen_of_triple] specialized for
    establishing a triple for a function application. The rule reformulates
    [triple_app_fun] with a premise of the form [wpgen E t]. *)

Lemma xcf_lemma : forall v1 v2 x t H Q,
  v1 = val_fun x t ->
  H ==> wpgen ((x,v2)::nil) t Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
  introv M1 M2. applys triple_app_fun M1.
  asserts_rewrite (subst x v2 t = isubst ((x,v2)::nil) t).
  { rewrite isubst_rem. rewrite~ isubst_nil. }
  rewrite wp_equiv. hchange M2. applys wpgen_sound.
Qed.

(** [xtop_lemma] helps exploiting [mkstruct] to augment the postcondition
    with [\Top]. It proves the entailement:
[[
    H ==> mkstruct F (Q \*+ \Top) -> 
    H ==> mkstruct F Q.
]]
*)

Lemma xtop_lemma : forall H Q F,
  H ==> mkstruct F (Q \*+ \Top) ->
  H ==> mkstruct F Q.
Proof using.
  introv M. hchange M. 
  lets N: mkstruct_ramified (Q \*+ \Top) Q F. hchanges N.
Qed.

(** Other lemmas for structural rules, not shown here, can be similarly
    devised. *)


(* ******************************************************* *)
(** ** An example proof *)

(** Recall the definition of the [incr] function, and its specification. *)

Definition incr :=
  VFun 'p :=
    Let 'n := '! 'p in
    Let 'm := 'n '+ 1 in
   'p ':= 'm.

Parameter triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1))).

(** Recall the definition of [mysucc], which allocates a reference
    with contents [n], increments its contents, then reads the output. *)

Definition mysucc :=
  VFun 'n :=
    Let 'r := val_ref 'n in
    incr 'r ';
    '! 'r.

(** Let us specify and prove this function using the x-lemmas. *)

Lemma triple_mysucc_with_xlemmas : forall n,
  triple (trm_app mysucc n)
    \[]
    (fun v => \[v = n+1]).
Proof using.
  intros.
  applys xcf_lemma. { reflexivity. }
  simpl. (* Here the [wpgen] function computes. *)
  (* Observe how each node begin with [mkstruct].
     Observe how program variables are all eliminated. *)
  applys xstruct_lemma.
  applys xlet_lemma.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_ref. }
  hsimpl'. intros ? l ->.
  applys xstruct_lemma.
  applys xseq_lemma.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_incr. }
  hsimpl'. intros ? ->.
  applys xtop_lemma. (* Here we exploit [mkstruct] to apply a structural rule. *)
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_get. }
  hsimpl'. intros ? ->.
  hsimpl'. auto.
Qed.


(* ******************************************************* *)
(** ** Making proof obligations more readable *)

(** Let us introduce a piece of notation for every "wpgen" auxiliary function,
    including [mkstruct]. *)

Notation "'Fail'" :=
  ((wpgen_fail))
  (at level 69) : wp_scope.

Notation "'Val' v" :=
  ((wpgen_val v))
  (at level 69) : wp_scope.

Notation "'`Let' x ':=' F1 'in' F2" :=
  ((wpgen_let F1 (fun x => F2)))
  (at level 69, x ident, right associativity,
  format "'[v' '[' '`Let'  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'") : wp_scope.

Notation "'Seq' F1 ;;; F2" :=
  ((wpgen_seq F1 F2))
  (at level 68, right associativity,
   format "'[v' 'Seq'  '[' F1 ']'  ;;;  '/'  '[' F2 ']' ']'") : wp_scope.

Notation "'App' f v1 " :=
  ((wp (trm_app f v1)))
  (at level 68, f, v1 at level 0) : wp_scope.

Notation "'If'' b 'Then' F1 'Else' F2" :=
  ((wpgen_if b F1 F2))
  (at level 69) : wp_scope.

Notation "` F" := (mkstruct F) (at level 10, format "` F") : wp_scope.

Open Scope wp_scope.

Lemma triple_mysucc_with_notations : forall n,
  triple (trm_app mysucc n)
    \[]
    (fun v => \[v = n+1]).
Proof using.
  intros. applys xcf_lemma. { reflexivity. } simpl.
  (* Obseve the goal here, which is of the form [H ==> "t" Q],
     where "t" reads just like the source code.
     Thus, compared with a goal of the form [triple t H Q],
     we have not lost readability. 
     Yet, compared with [triple t H Q], our goal does not mention
     any program variable at all. *)
Abort.


(* ******************************************************* *)
(** ** Making proof scripts more concise *)

(** For each term construct, and for [mkstruct] goals, we introduce
    a dedicated tactic to apply the corresponding x-lemma, plus
    performs some basic preliminary work. *)

(** [xstruct] eliminates the leading [mkstruct]. *)

Ltac xstruct :=
  applys xstruct_lemma.

(** [xseq] and [xlet] invoke the corresponding lemma, after
    calling [xstruct] if necessary. *)

Ltac xstruct_if_needed :=
  try match goal with |- ?H ==> mkstruct ?F ?Q => xstruct end.

Ltac xlet :=
  xstruct_if_needed; applys xlet_lemma.

Ltac xseq :=
  xstruct_if_needed; applys xseq_lemma.

(** [xapp] invokes [xapp_lemma], after calling [xseq] or [xlet]
    if necessary. *)

Ltac xseq_xlet_if_needed :=
  try match goal with |- ?H ==> mkstruct ?F ?Q => 
  match F with 
  | wpgen_seq ?F1 ?F2 => xseq
  | wpgen_let ?F1 ?F2of => xlet
  end end.

Ltac xapp :=
  xseq_xlet_if_needed; xstruct_if_needed; applys xapp_lemma.

(** [xtop] involves [xtop_lemma], exploiting the leading [mkstruct]. *)

Ltac xtop :=
  applys xtop_lemma.

(** [xcf] applys [xcf_lemma], then computes [wpgen] to begin the proof. *)

Ltac xcf :=
  intros; applys xcf_lemma; [ reflexivity | simpl ].

(** The proof script becomes much more succint. *)

Lemma triple_mysucc_with_xtactics : forall (n:int),
  triple (trm_app mysucc n)
    \[]
    (fun v => \[v = n+1]).
Proof using.
  xcf.
  xapp. { apply triple_ref. } hsimpl' ;=> ? l ->.
  xapp. { apply triple_incr. } hsimpl' ;=> ? ->.
  xtop.
  xapp. { apply triple_get. } hsimpl' ;=> ? ->.
  hsimpl. auto.
Qed.

(* EX2! (triple_incr_with_xtactics) *)
(** Using x-tactics, verify the proof of [incr].
    (The proof was carried out using triples in chapter [SLFRules].) *)

Lemma triple_incr_with_xtactics : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1))).
Proof using.
(* SOLUTION *)
  xcf.
  xapp. { apply triple_get. } hsimpl' ;=> ? ->.
  xapp. { apply triple_add. } hsimpl' ;=> ? ->.
  xapp. { apply triple_set. } hsimpl' ;=> ? ->.
  hsimpl. auto.
(* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Further improvements to the [xapp] tactic. *)

(** We further improve [xapp] in two ways.

    First, we introduce the variant [xapp' E] which mimics the
    proof pattern: [xapp. { apply E. } hsimpl'.]. Concretely,
    [xapp' E] directly exploits the specification [E] rather
    than requiring an explicit [apply E], and a subsequent [hsimpl']. *)

Ltac xapp_pre :=
  xseq_xlet_if_needed; xstruct_if_needed.

Ltac xapp' E :=
  xapp_pre; applys xapp_lemma E; hsimpl'.

(** Second, we introduce the variant [xapps E] to mimic the
    pattern [xapp. { apply E. } hsimpl' ;=> ? ->]. Concretely,
    the tactic [xapps E] exploits a specification [E] whose conclusion
    is of the form [fun r => \[r = v] \* H] or [fun r => \[r = v]],
    and for which the user wishes to immediately substitute [r] away. *)

Lemma xapps_lemma0 : forall t v H1 H Q,
  triple t H1 (fun r => \[r = v]) ->
  H ==> H1 \* (protect (Q v)) ->
  H ==> wp t Q.
Proof using. introv M W. applys xapp_lemma M. hchanges W. intros ? ->. auto. Qed.

Lemma xapps_lemma1 : forall t v H1 H2 H Q,
  triple t H1 (fun r => \[r = v] \* H2) ->
  H ==> H1 \* (H2 \-* protect (Q v)) ->
  H ==> wp t Q.
Proof using. introv M W. applys xapp_lemma M. hchanges W. intros ? ->. auto. Qed.

Ltac xapps E :=
  xapp_pre; first 
  [ applys xapps_lemma0 E
  | applys xapps_lemma1 E ];
  hsimpl'.


(* ******************************************************* *)
(** ** Here is the demo of a practical proof based on x-tactics. *)

(** "THE_DEMO" begins here. *)

(** The proof script for the verification of [incr] looks like this. *)

Lemma triple_incr_with_xapps : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1))).
Proof using.
  xcf.
  xapps triple_get.
  xapps triple_add.
  xapps triple_set.
  hsimpl~.
Qed.

(** The proof script for the verification of [mysucc] is now shorter. *)

Lemma triple_mysucc_with_xapps : forall n,
  triple (trm_app mysucc n)
    \[]
    (fun v => \[v = n+1]).
Proof using.
  xcf.
  xapp' triple_ref ;=> ? l ->.
  xapps triple_incr.
  xtop.
  xapps triple_get.
  hsimpl~.
Qed.

(* TODO: add a few exercises here *)

End ExampleProofs.


(* ####################################################### *)
(** * Appendix: details on the definition of [mkstruct] *)

(** Recall the definition of [mkstruct].
[[
    Definition mkstruct (F:formula) : formula := fun (Q:val->hprop) =>
      \exists Q', F Q' \* (Q' \--* (Q \*+ \Top)).
]]

    Let us first explain in more details why this definition satisfies
    the required properties, namely [mkstruct_erase] and [mkstruct_ramified],
    whose proofs were trivialized by [hsimpl].

    For the lemma [mkstruct_erase], we want to prove [F Q ==> mkstruct F Q].
    This is equivalent to [F Q ==> \exists Q', F Q' \* (Q' \--* Q \*+ \Top)].
    Taking [Q'] to be [Q] and cancelling [F Q] from both sides leaves
    [\[] ==> Q \--* (Q \*+ \Top)], which is equivalent to [Q ==> Q \*+ \Top].

    For the lemma [mkstruct_ramified], we want to prove
    [(mkstruct F Q1) \* (Q1 \--* Q2 \*+ \Top) ==> (mkstruct F Q2)],
    which is equivalent to
    [\exists Q', F Q' \* (Q' \--* Q1 \*+ \Top) \* (Q1 \--* Q2 \*+ \Top) ==>
     \exists Q', F Q' \* (Q' \--* Q2 \*+ \Top)].
    By instantiatiating the LHS [Q'] with the value of the RHS [Q'], and
    cancelling [F Q'] form both sides, the entailment simplifies to:
    [(Q' \--* Q1 \*+ \Top) \* (Q1 \--* Q2 \*+ \Top) ==> (Q' \--* Q2 \*+ \Top)].
    The wand [Q1 \--* (Q2 \*+ \Top)] is equal to [(Q1 \*+ \Top) \--* (Q2 \*+ \Top)]
    (because both are equal to [(Q1 \*+ \Top) \--* (Q2 \*+ \Top \*+ \Top))]).
    Thus, the goal reformulates as
    [Q' \--* (Q1 \*+ \Top)) \* ((Q1 \*+ \Top) \--* (Q2 \*+ \Top)) ==>
     Q' \--* (Q2 \*+ \Top)].
    We conclude by cancelling out [Q1 \*+ \Top] accross the two magic wands
    from the LHS---recall the lemma [hwand_trans_elim] from [SLFHwand]. *)

(** Let us now explain how, to a goal of the form [H ==> mkstruct F Q],
    one can apply the structural rules of Separation Logic.
    Consider for example the ramified frame rule. *)

Parameter triple_ramified_frame : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  triple t H Q.

(** Let us reformulate this lemma in weakest-precondition style, 
    then prove it. *)

Lemma himpl_mkstruct_conseq_frame : forall H Q H1 Q1 F,
  H1 ==> mkstruct F Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  H ==> mkstruct F Q.
Proof using.
  introv M W. hchange W. hchange M. 
  lets N: mkstruct_ramified Q1 Q F. hchanges N.
Qed.

(** An interesting property of [mkstruct] is its idempotence:
    [mkstruct (mkstruct F) = mkstruct F].
    Concretely, applying this predicate transformer more than
    once does not increase expressiveness. *)

(* EX3! (mkstruct_idempotent) *)
(** Prove the idempotence of [mkstruct]. Hint: use [hsimpl]. *)

Lemma mkstruct_idempotent : forall F,
  mkstruct (mkstruct F) = mkstruct F.
Proof using.
  (* SOLUTION *)
  intros. apply fun_ext_1. intros Q.
  unfold mkstruct. hsimpl.
  (* [hsimpl] first invokes [applys himpl_antisym].
     The right-to-left entailment is exactly [mkstruct_erase].
     The left-to-right entailment amounts to proving: 
     [F Q2 \* (Q2 \--* (Q1 \*+ \Top) \* (Q1 \--* (Q \*+ \Top))
      ==> \exists Q', F Q' \* (Q' \--* (Q \*+ \Top))]
     To conclude the proof, instantiate [Q'] as [Q2] and cancel
     out [Q1 \*+ \Top] (like done earlier in this section). *)
(* /SOLUTION *)
Qed.


(* ####################################################### *)
(** * Appendix: proofs for iterated substitution lemmas *)

(** Recall that [isubst E t] denotes the multi-substitution
    in the term [t] of all bindings form the association list [E].

    The soundness proof for [wpgen] relies on two properties
    of substitutions, [isubst_nil] and [isubst_rem], which we
    state and prove next: 
[[
    isubst nil t = t

    subst x v (isubst (rem x E) t) = isubst ((x,v)::E) t
]]
*)

(** The first lemma is straightforward by induction. *)

Lemma isubst_nil' : forall t,
  isubst nil t = t.
Proof using.
  intros t. induction t using trm_induct; simpl; fequals.
Qed.

(** The second lemma is much more involved to prove.

    We introduce the notion of "two equivalent contexts" 
    [E1] and [E2], and argue that substitution for two
    equivalent contexts yields the same result.

    We then introduce the notion of "equivalent contexts
    up to one binding", and reformulate the desired lemma
    in the form [subst x v (isubst E1 t) = isubst E2 t]
    when [E1] and [E2] differ only in the binding on [x],
    with [E1] not binding it while [E2] binding it to [v]. *)

(** Before we start, we introduce the tactic [case_var] to
    help with the case_analyses on variable equalities,
    and we prove an auxiliary lemma that describes the
    result of a lookup on a context from which a binding
    has been removed. *)

Tactic Notation "case_var" := 
  repeat rewrite var_eq_spec in *; repeat case_if.
  (* LATER: use a case_if that performs substitution *)

Tactic Notation "case_var" "~" := 
  case_var; auto.

Lemma lookup_rem : forall x y E,
  lookup x (rem y E) = if var_eq x y then None else lookup x E.
Proof using.
  intros. induction E as [|(z,v) E'].
  { simpl. case_var~. }
  { simpl. case_var~; simpl; case_var~. }
Qed.

(** The definition of equivalent contexts, the fact that
    equivalent contexts yield equivalent contexts after
    removing a binding, and the fact that equivalent contexts
    yield equivalent substitutions appear next. *)

Definition ctx_equiv E1 E2 :=
  forall x, lookup x E1 = lookup x E2.

Lemma ctx_equiv_rem : forall x E1 E2,
  ctx_equiv E1 E2 ->
  ctx_equiv (rem x E1) (rem x E2).
Proof using.
  introv M. unfolds ctx_equiv. intros y.
  do 2 rewrite lookup_rem. case_var~.
Qed.

Lemma isubst_ctx_equiv : forall t E1 E2,
  ctx_equiv E1 E2 ->
  isubst E1 t = isubst E2 t.
Proof using.
  hint ctx_equiv_rem.
  intros t. induction t using trm_induct; introv EQ; simpl; fequals~.
  { rewrite EQ. auto. }
Qed.

(** The definition of equivalent contexts up to one binding on [x],
    written [ctx_differ_one x v E1 E2], captures that [E1] and [E2]
    have the same bindings, except for [x] which [E1] binds to [v]
    and [E2] does not bind. *)

Definition ctx_differ_one x v E1 E2 :=
     (forall y, y <> x -> lookup y E1 = lookup y E2)
  /\ (lookup x E1 = Some v)
  /\ (lookup x E2 = None).

(** Assume [ctx_differ_one x v E1 E2].
    If the binding [x] is removed from [E1] and [E2], then 
    they become equivalent.
    If a binding other than [x] is removed from the two contexts, 
    then they remain equivalent up to the binding on [x]. *)

Lemma ctx_differ_one_rem_same : forall x v E1 E2,
  ctx_differ_one x v E1 E2 ->
  ctx_equiv (rem x E1) (rem x E2).
Proof using.
  introv (M0&_&_). intros y. do 2 rewrite lookup_rem. case_var~.
Qed.

Lemma ctx_differ_one_rem_neq : forall y x v E1 E2,
  ctx_differ_one x v E1 E2 ->
  x <> y ->
  ctx_differ_one x v (rem y E1) (rem y E2).
Proof using.
  introv (M1&M2&M3) N. splits; try intros z Hz;
  repeat rewrite lookup_rem; case_var~.
Qed.

(** The key induction is set up as follows. *)

Section IsubstRemInd.

Hint Resolve isubst_ctx_equiv 
  ctx_equiv_rem ctx_differ_one_rem_same ctx_differ_one_rem_neq.

Lemma isubst_rem_ind : forall y v E1 E2 t,
  ctx_differ_one y v E1 E2 ->
  isubst E1 t = subst y v (isubst E2 t).
Proof using.
  intros. gen E1 E2. induction t using trm_induct; introv M; simpl; rew_trm.
  { fequals. }
  { destruct M as (M0&M1&M2). tests C: (x = y).
    { rewrite M2, M1. simpl. case_var~. }
    { rewrite~ <- M0. case_eq (lookup x E1).
      { intros v' R'. auto. }
      { simpl. case_var~. } } }
  { fequals. case_var; rew_logic in *; subst*. }
  { fequals. case_var; rew_logic in *; subst*. }
  { fequals*. }
  { fequals*. }
  { fequals*. case_var~. subst*. }
  { fequals*. }
Qed.

End IsubstRemInd.

(** As a corollary, we get the desired property of [isubst]. *)

Lemma isubst_rem' : forall x v E t,
  isubst ((x, v)::E) t = subst x v (isubst (rem x E) t).
Proof using.
  intros. applys isubst_rem_ind. splits.
  { intros y K. simpl. rewrite lookup_rem. case_var~. }
  { simpl. case_var~. }
  { rewrite lookup_rem. case_var~. }
Qed.

(** Another useful corollary reformulates [subst] in terms of [isubst].
    This result is exploited, e.g., in the proof of [xcf_lemma]. *)

Lemma subst_eq_isubst' : forall x v t,
  subst x v t = isubst ((x,v)::nil) t.
Proof using. intros. rewrite isubst_rem. simpl. rewrite~ isubst_nil. Qed.


(* ####################################################### *)
(** * Appendix: non-structural induction and recursion *)

(* ******************************************************* *)
(** ** Size of a term *)

(** Definition of the size of a term. Note that all values count for one unit,
    even functions. *)

Fixpoint size (t:trm) : nat :=
  match t with
  | (* [trm_val v] => *)  trm_val v =>
       1
  | (* [trm_var x] => *)  trm_var x =>
       1
  | (* [trm_fun x t1] => *)  trm_fixs bind_anon (x::nil) t1 =>
       1
  | (* [trm_fix f x t1] => *)  trm_fixs (bind_var f) (x::nil) t1 =>
       1
  | (* [trm_if v0 t1 t2] => *)  trm_if (trm_val v0) t1 t2 =>
       1 + (size t1) + (size t2)
  | (* [trm_seq t1 t2] => *)  trm_let bind_anon t1 t2 =>
       1 + (size t1) + (size t2)
  | (* [trm_let x t1 t2] => *)  trm_let (bind_var x) t1 t2 =>
       1 + (size t1) + (size t2)
  | (* [trm_app t1 t2] => *)  trm_apps t1 (t2::nil) => 
       1 + (size t1) + (size t2)
  | (* other terms are outside of the sub-language that we consider,
       so let us here pretend that they are no such terms. *)
    _ => 1
  end.


(* ******************************************************* *)
(** ** An induction principle modulo substitution *)

(** We show how to prove [trm_induct_subst] used earlier to justify the
    soundness of the non-structurally-decreasing definition of [wpgen].
    First, we show that substitution preserves the size.
    Second, we show how to prove the desired induction principle.

    For the proofs, we assume the standard case-analysis principle,
    which would be given directly by [destruct t] if our grammar
    of terms was restricted to the sublanguage considered.
    Thereafter, we'll invoke [destruct t using trm_case]. *)

Parameter trm_case : forall (P : trm -> Prop),
  (forall v, P (trm_val v)) ->
  (forall x, P (trm_var x)) ->
  (forall x t1 , P (trm_fun x t1)) ->
  (forall (f:var) x t1, P (trm_fix f x t1)) ->
  (forall t1 t2, P (trm_app t1 t2)) ->
  (forall t1 t2, P (trm_seq t1 t2)) ->
  (forall (x:var) t1 t2, P (trm_let x t1 t2)) ->
  (forall v t1 t2, P (trm_if v t1 t2)) ->  
  (forall t, P t).

(** First, we show that substitution preserves the size.
    Here, we exploit [trm_induct], the structural induction principle
    for our sublanguage, to carry out the proof. *)

Lemma size_subst : forall x v t,
  size (subst x v t) = size t.
Proof using.
  intros. induction t using trm_induct; intros; simpl; repeat case_if; auto.
Qed.

(** Remark: the same proof can be carried out by induction on size. *)

Lemma size_subst' : forall x v t,
  size (subst x v t) = size t.
Proof using.
  intros. induction_wf IH: size t. unfolds measure.
  destruct t using trm_case; simpls; 
  repeat case_if; simpls;
  repeat rewrite IH; try math.
Qed.

(** Second, we prove the desired induction principle by induction on
    the size of the term. *)

Section TrmInductSubst1.

Hint Extern 1 (_ < _) => math.

Lemma trm_induct_subst : forall (P : trm -> Prop),
  (forall v, P (trm_val v)) ->
  (forall x, P (trm_var x)) ->
  (forall x t1 , P (trm_fun x t1)) ->
  (forall (f:var) x t1,P (trm_fix f x t1)) ->
  (forall t1, P t1 -> forall t2, P t2 -> P (trm_app t1 t2)) ->
  (forall t1, P t1 -> forall t2, P t2 -> P (trm_seq t1 t2)) ->
  (forall (x:var) t1, P t1 -> forall t2, (forall v, P (subst x v t2)) -> P (trm_let x t1 t2)) ->
  (forall v t1, P t1 -> forall t2, P t2 -> P (trm_if v t1 t2)) ->  
  (forall t, P t).
Proof using.
  introv M1 M2 M3 M4 M5 M6 M7 M8. 
  (** Next line applies [applys well_founded_ind (wf_measure trm_size)] *)
  intros t. induction_wf IH: size t. unfolds measure.
  (** We perform a case analysis according to the grammar of our sublanguage *)
  destruct t using trm_case; simpls; auto.
  (** Only the case for let-binding is not automatically discharged. We give details. *)
  { applys M7. { applys IH. math. } { intros v. applys IH. rewrite size_subst. math. } }
Qed.

End TrmInductSubst1.

(** Remark: the general pattern for proving such induction principles with a more concise,
    more robust proof script leverages a custom hint to treat the side conditions
    of the form [measure size t1 t2], which are equivalent to [size t1 < size t2]. *)

Section TrmInductSubst2.

Hint Extern 1 (measure size _ _) => (* the custom hint *)
  unfold measure; simpls; repeat rewrite size_subst; math.

Lemma trm_induct_subst' : forall (P : trm -> Prop),
  (forall v, P (trm_val v)) ->
  (forall x, P (trm_var x)) ->
  (forall x t1 , P (trm_fun x t1)) ->
  (forall (f:var) x t1,P (trm_fix f x t1)) ->
  (forall t1, P t1 -> forall t2, P t2 -> P (trm_app t1 t2)) ->
  (forall t1, P t1 -> forall t2, P t2 -> P (trm_seq t1 t2)) ->
  (forall (x:var) t1, P t1 -> forall t2, (forall v, P (subst x v t2)) -> P (trm_let x t1 t2)) ->
  (forall v t1, P t1 -> forall t2, P t2 -> P (trm_if v t1 t2)) ->  
  (forall t, P t).
Proof using.
  intros. induction_wf IH: size t.
  destruct t using trm_case; simpls; eauto. (* the fully automated proof *)
Qed.

End TrmInductSubst2.


(* ******************************************************* *)
(** ** Fixedpoint equation for the non-structural definition of [wpgen] *)

Module WPgenFix.
Import WPgenSubst.

(** Recall the definition of [wpgen t] using the functional [Wpgen],
    whose fixed point was constructed using the "optimal fixed point
    combinated" (module LibFix from TLC) as:
[[
    Definition wpgen := FixFun Wpgen.
]]
    We next show how to prove the fixed point equation, which enables
    to "unfold" the definition of [wpgen]. The proof requires establishing
    a "contraction condition", a notion defined in the theory of the
    optimal fixed point combinator. In short, we must justify that:
[[
    forall f1 f2 t,
    (forall t', size t' < size t -> f1 t' = f2 t') ->
    Wpgen f1 t = Wpgen f2 t
]]
*)

Section WPgenfix1.

Hint Extern 1 (_ < _) => math.

Lemma wpgen_fix : forall t, 
  wpgen t = Wpgen wpgen t.
Proof using.
  applys~ (FixFun_fix (measure size)). { applys wf_measure. } 
  unfolds measure. intros f1 f2 t IH. (* The goal here is the contraction condition. *)
  unfold Wpgen. fequal. destruct t using trm_case; simpls; try solve [ fequals; auto ].
  (* Only the case of the let-binding is not automatically proved. We give details.  *)
  { fequal.
    { applys IH. math. }
    { applys fun_ext_1. intros v. applys IH. rewrite size_subst. math. } }
Qed.

End WPgenfix1.

(** Here again, using the same custom hint as earlier on, and registering
    functional extensionality as hint, we can shorten the proof script. *)

Section WPgenfix2.

Hint Extern 1 (measure size _ _) => (* the custom hint *)
  unfold measure; simpls; repeat rewrite size_subst; math.

Hint Resolve fun_ext_1.

Lemma wpgen_fix' : forall t, 
  wpgen t = Wpgen wpgen t.
Proof using.
  applys~ (FixFun_fix (measure size)). { applys wf_measure. } 
  intros f1 f2 t IH. unfold Wpgen. fequal.
  destruct t using trm_case; simpls; fequals; auto.
Qed.

End WPgenfix2.

End WPgenFix.
