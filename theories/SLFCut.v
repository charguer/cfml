
(* ####################################################### *)
(** * Appendix: non-structural induction and recursion *)

(* ******************************************************* *)
(** ** Size of a term *)

(** Definition of the size of a term. Note that all values count for one unit,
    even functions. *)

Fixpoint size (t:trm) : nat :=
  match t with
  | trm_val v =>
       1
  | trm_var x =>
       1
  | trm_fun x t1 =>
       1
  | trm_fix f x t1 =>
       1
  | trm_app t1 t2 =>
       1 + (size t1) + (size t2)
  | trm_seq t1 t2 =>
       1 + (size t1) + (size t2)
  | trm_let x t1 t2 =>
       1 + (size t1) + (size t2)
  | trm_if t0 t1 t2 =>
       1 + (size t0) + (size t1) + (size t2)
  end.


(* ******************************************************* *)
(** ** An induction principle modulo substitution *)

(** We show how to prove [trm_induct_subst] used earlier to justify the
    soundness of the non-structurally-decreasing definition of [wpgen].
    First, we show that substitution preserves the size.
    Second, we show how to prove the desired induction principle. *)

(** First, we show that substitution preserves the size.
    Here, we exploit [trm_induct], the structural induction principle
    for our sublanguage, to carry out the proof. *)

Lemma size_subst : forall x v t,
  size (subst x v t) = size t.
Proof using.
  intros. induction t; intros; simpl; repeat case_if; auto.
Qed.

(** Remark: the same proof can be carried out by induction on size. *)

Lemma size_subst' : forall x v t,
  size (subst x v t) = size t.
Proof using.
  intros. induction_wf IH: size t. unfolds measure.
  destruct t; simpls;
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
  (forall t0, P t0 -> forall t1, P t1 -> forall t2, P t2 -> P (trm_if t0 t1 t2)) ->
  (forall t, P t).
Proof using.
  introv M1 M2 M3 M4 M5 M6 M7 M8.
  (** Next line applies [applys well_founded_ind (wf_measure trm_size)] *)
  intros t. induction_wf IH: size t. unfolds measure.
  (** We perform a case analysis according to the grammar of our sublanguage *)
  destruct t; simpls; auto.
  (** Only the case for let-binding is not automatically discharged. We give details. *)
  { applys M7. { applys IH. math. } { intros v'. applys IH. rewrite size_subst. math. } }
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
  (forall t0, P t0 -> forall t1, P t1 -> forall t2, P t2 -> P (trm_if t0 t1 t2)) ->
  (forall t, P t).
Proof using.
  intros. induction_wf IH: size t.
  destruct t; simpls; eauto. (* the fully automated proof *)
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
  unfold Wpgen. fequal. destruct t; simpls; try solve [ fequals; auto ].
  (* Only the case of the let-binding is not automatically proved. We give details.  *)
  { fequal.
    { applys IH. math. }
    { applys fun_ext_1. intros v'. applys IH. rewrite size_subst. math. } }
  { destruct t1; fequals~. }
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
  destruct t; simpls; fequals; auto.
  { destruct t1; fequals~. }
Qed.

End WPgenfix2.

End WPgenFix.





(* ******************************************************* *)
(** ** A simple yet non-structurally recursive definition of [wpgen] *)

Module WPgenSubst.

(** We are almost ready to formally define our function [wpgen].
    There is one Coq-specific caveat on our way, however.
    The definition of [wpgen] is not structurally recursive.
    Thus, we'll have to play some tricks to first define it as a functional,
    and then take the fixed point of this functional.

    The details of this fixed point construction are not essential
    for the moment; they are explained further in this chapter.
    In any case, we will shortly afterwards present an alternative definition
    to [wpgen] which is slightly more complex yet structurally recursive. *)

Definition Wpgen wpgen (t:trm) : formula :=
  mkstruct
  match t with
  | trm_val v =>
       wpgen_val v
  | trm_var x =>
       wpgen_fail
  | trm_fun x t1 =>
       wpgen_val (val_fun x t1)
  | trm_fix f x t1 =>
       wpgen_val (val_fix f x t1)
  | trm_app t1 t2 =>
       wp t
  | trm_seq t1 t2 =>
       wpgen_seq (wpgen t1) (wpgen t2)
  | trm_let x t1 t2 =>
       wpgen_let (wpgen t1) (fun v => wpgen (subst x v t2))
  | trm_if (trm_val v0) t1 t2 =>
       wpgen_if v0 (wpgen t1) (wpgen t2)
  | (* terms [trm_if t0 t1 t2] where [t0] is not a value or a variable
       fall outside of the sub-language that we consider,
       so let us here pretend that they are no such terms. *)
    _ => wpgen_fail
  end.

(** To build the fixed point, we need to show the result type inhabited. *)

Global Instance Inhab_formula : Inhab formula.
Proof using. apply (Inhab_of_val (fun _ => \[])). Qed.

(** [wpgen] is the fixed point of [Wpgen]. *)

Definition wpgen := FixFun Wpgen.

(** The fixed point equation, which enables unfolding the definition
    of [wpgen], is proved further in this file. To establish it, we
    essentially need to justify the termination of the recursive function. *)

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
  (forall t0, P t0 -> forall t1, P t1 -> forall t2, P t2 -> P (trm_if t0 t1 t2)) ->
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
  (forall t0, P t0 -> forall t1, P t1 -> forall t2, P t2 -> P (trm_if t0 t1 t2)) ->
  (forall t, P t).

(** The soundness lemma asserts: [forall t, formula_sound t (wpgen t)].
    The proof is carried out by induction on [t]. For each term
    construct, the proof consists of invoking the lemma [mkstruct_sound]
    to justify soundness of the leading [mkstruct], then invoking
    the soundness lemma specific to that term construct. *)

Lemma wpgen_sound : forall t,
  formula_sound t (wpgen t).
Proof using.
  intros. induction t using trm_induct_subst;
   rewrite wpgen_fix; applys mkstruct_sound; simpl.
  { applys wpgen_val_sound. }
  { applys wpgen_fail_sound. }
  { applys wpgen_fun_val_sound. }
  { applys wpgen_fix_val_sound. }
  { applys wp_sound. }
  { applys wpgen_seq_sound. { applys IHt1. } { applys IHt2. } }
  { applys wpgen_let_sound. { applys IHt1. } { intros v. applys H. } }
  { destruct t1; try applys wpgen_fail_sound.
    { applys wpgen_if_sound. { applys IHt2. } { applys IHt3. } } }
Qed.

Theorem triple_of_wpgen : forall t H Q,
  H ==> wpgen t Q ->
  triple t H Q.
Proof using. introv M. rewrite wp_equiv. xchange M. applys wpgen_sound. Qed.

End WPgenSubst.

========================================================


val_of_function t =
  trm_fun => 
  trm_fix => 
  _ => arbitrary

fun Q => Q (val_of_function (isubst E t))
fun Q => Q (val_of_function (isubst E t))


wpgen_function t =
  | trm_fun x t1 => fun Q => val_fun x t1
  | trm_fix f x t1 => fun Q => val_fix f x t1
  | _ => \[]

  | trm_fun x t1 => wpgen_function (isubst E t)
  | trm_fix f x t1 => wpgen_function (isubst E t)




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
  (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).

(** If [wpgen] were to satisfy this same property like [wp], then it would
    also capture the expressive power of all the structural rules of
    Separation Logic. In other words, we would like to have: *)

Parameter wpgen_ramified : forall t Q1 Q2,
  (wpgen t Q1) \* (Q1 \--* Q2) ==> (wpgen t Q2).

End WpgenOverview.

(** We have set up [wpgen] so that [wpgen t] is always of the form [mkstruct F]
    for some formula [F]. Thus, to ensure the above entailment, it suffices
    for the definition of [mkstruct] to be a "formula transformer" (more generally
    known as a "predicate transformer") of type [formula->formula] such that:
[[
    Parameter mkstruct_ramified : forall F Q1 Q2,
      (mkstruct F Q1) \* (Q1 \--* Q2) ==> (mkstruct F Q2).
]]
    At the same time, in a situation where we do not need to apply any structural
    rule, we'd like to be able to get rid of the leading [mkstruct] in the formula
    produced by [wpgen]. Concretely, we need:

[[
    Lemma mkstruct_erase : forall F Q,
      F Q ==> mkstruct F Q.
]] *)

(** The following definition of [mkstruct] satisfy the above two properties.
    The tactic [xsimpl] trivializes the proofs. Details are discussed further on. *)

Definition mkstruct (F:formula) : formula := fun (Q:val->hprop) =>
  \exists Q', F Q' \* (Q' \--* Q).

Lemma mkstruct_ramified : forall Q1 Q2 F,
  (mkstruct F Q1) \* (Q1 \--* Q2) ==> (mkstruct F Q2).
Proof using. unfold mkstruct. xsimpl. Qed.

Lemma mkstruct_erase : forall Q F,
  F Q ==> mkstruct F Q.
Proof using. unfolds mkstruct. xsimpl. Qed.

Arguments mkstruct_erase : clear implicits.
Arguments mkstruct_ramified : clear implicits.

(* TODO integrate
Module MkstructAlt.

Definition mkstruct (F:formula) : formula := fun (Q:val->hprop) =>
  \exists Q' H', F Q' \* H' \* \[Q' \*+ H' ===> Q].

Lemma mkstruct_erase : forall Q F,
  F Q ==> mkstruct F Q.
Proof using. unfolds mkstruct. intros. xsimpl \[] Q. xsimpl. Qed.

Lemma mkstruct_ramified : forall Q1 Q2 F,
  (mkstruct F Q1) \* (Q1 \--* Q2) ==> (mkstruct F Q2).
Proof using.
  unfold mkstruct. intros. xpull ;=> Q' H' M.
  applys himpl_hexists_r Q'.
  applys himpl_hexists_r (H' \* (Q1 \--* Q2)).
  rew_heap.
  applys himpl_frame_r.
  applys himpl_frame_r.
  xsimpl. xchange M.
Qed.

Definition equiv_mkstruct :
  mkstruct = Top.mkstruct.
Proof using.
  intros. apply fun_ext_2 ;=> F Q. unfold mkstruct, Top.mkstruct.
  applys himpl_antisym.
  { xpull ;=> Q' H' M. xsimpl Q'. xchanges M. }
  { xpull ;=> Q'. xsimpl Q'. xsimpl. }
Qed.


End MkstructAlt.
 *)



(* ####################################################### *)
(** * Appendix: details on the definition of [mkstruct] *)

(** Recall the definition of [mkstruct].
[[
    Definition mkstruct (F:formula) : formula := fun (Q:val->hprop) =>
      \exists Q', F Q' \* (Q' \--* Q).
]]

    Let us first explain in more details why this definition satisfies
    the required properties, namely [mkstruct_erase] and [mkstruct_ramified],
    whose proofs were trivialized by [xsimpl].

    For the lemma [mkstruct_erase], we want to prove [F Q ==> mkstruct F Q].
    This is equivalent to [F Q ==> \exists Q', F Q' \* (Q' \--* Q)].
    Taking [Q'] to be [Q] and cancelling [F Q] from both sides leaves
    [\[] ==> Q \--* Q)], which is equivalent to [Q ==> Q].

    For the lemma [mkstruct_ramified], we want to prove
    [(mkstruct F Q1) \* (Q1 \--* Q2) ==> (mkstruct F Q2)],
    which is equivalent to
    [\exists Q', F Q' \* (Q' \--* Q1) \* (Q1 \--* Q2) ==>
     \exists Q', F Q' \* (Q' \--* Q2)].
    By instantiatiating the LHS [Q'] with the value of the RHS [Q'], and
    cancelling [F Q'] form both sides, the entailment simplifies to:
    [(Q' \--* Q1) \* (Q1 \--* Q2) ==> (Q' \--* Q2)].
    We conclude by cancelling out [Q1] accross the two magic wands
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
  introv M W. xchange W. xchange M.
  lets N: mkstruct_ramified Q1 Q F. xchanges N.
Qed.

(** An interesting property of [mkstruct] is its idempotence:
    [mkstruct (mkstruct F) = mkstruct F].
    Concretely, applying this predicate transformer more than
    once does not increase expressiveness. *)

(* EX3! (mkstruct_idempotent) *)
(** Prove the idempotence of [mkstruct]. Hint: use [xsimpl]. *)

Lemma mkstruct_idempotent : forall F,
  mkstruct (mkstruct F) = mkstruct F.
Proof using.
  (* SOLUTION *)
  intros. apply fun_ext_1. intros Q.
  unfold mkstruct. xsimpl.
  (* [xsimpl] first invokes [applys himpl_antisym].
     The right-to-left entailment is exactly [mkstruct_erase].
     The left-to-right entailment amounts to proving:
     [F Q2 \* (Q2 \--* Q1) \* (Q1 \--* Q))
      ==> \exists Q', F Q' \* (Q' \--* Q))]
     To conclude the proof, instantiate [Q'] as [Q2] and cancel
     out [Q1] (as done in an earlier proof from this section). *)
(* /SOLUTION *)
Qed.

==============



Parameter wpgen_sound_seq : forall E t1 t2 Q,
  wpgen E (trm_seq t1 t2) Q ==> wp (isubst E (trm_seq t1 t2)) Q.

    

Parameter  : forall E t1 t2,
  (forall Q, wpgen E t1 Q ==> wp (isubst E t1) Q) ->
  (forall Q, wpgen E t2 Q ==> wp (isubst E t2) Q) ->
  (forall Q, wpgen E (trm_seq t1 t2) Q
             ==> wp (trm_seq (isubst E t1) (isubst E t2))) Q).

(** To make this proof obligation more readable, let us abstract
    
    - [wpgen E t1] as [F1]
    - [wpgen E t2] as [F2]
    - [isubst E t1] as [t1']
    - [isubst E t2] as [t2']

    and observe that [wpgen E (trm_seq t1 t2) Q] is
    
    wpgen E (trm_seq t1 t2) Q

    The proof obligation then reformulates as: *)


Parameter wpgen_sound_seq'' : forall E t1 t2,
  (forall Q, F1 Q ==> wp (isubst E t2) Q) ->
  (forall Q, F2 Q ==> wp (isubst E t1) Q) ->
  (forall Q, wpgen E (trm_seq t1 t2) Q
             ==> wp (trm_seq (isubst E t1) (isubst E t2))) Q).



  formula_sound (trm_val v) (wpgen_val v).

  formula_sound t1 F1 ->
  formula_sound t2 F2 ->
  formula_sound (trm_seq t1 t2) (wpgen_seq F1 F2).





(* ******************************************************* *)

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
  | trm_val v =>
       wpgen_val v
  | trm_var x =>
       wpgen_var E x
  | trm_fun x t1 =>
       wpgen_val (val_fun x (isubst (rem x E) t1))
  | trm_fix f x t1 =>
       wpgen_val (val_fix f x (isubst (rem x (rem f E)) t1))
  | trm_app t1 t2 =>
       wp (isubst E t)
  | trm_seq t1 t2 =>
       wpgen_seq (wpgen E t1) (wpgen E t2)
  | trm_let x t1 t2 =>
       wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
  | trm_if t0 t1 t2 =>
      match isubst E t0 with
      | trm_val v0 => wpgen_if v0 (wpgen E t1) (wpgen E t2)
      | _ => wpgen_fail
      end
  end.



(* ******************************************************* *)
(** ** Making proof obligations more readable *)


Lemma triple_mysucc_with_notations : forall n,
  triple (trm_app mysucc n)
    \[]
    (fun v => \[v = n+1]).
Proof using.
  intros. applys xwp_lemma. { reflexivity. } simpl.
  (* Obseve the goal here, which is of the form [H ==> "t" Q],
     where "t" reads just like the source code.
     Thus, compared with a goal of the form [triple t H Q],
     we have not lost readability.
     Yet, compared with [triple t H Q], our goal does not mention
     any program variable at all. *)
Abort.


===========================================


Module ProgDef.

Import NotationForVariables.
Open Scope val_scope.
Open Scope trm_scope.
Implicit Types n : int.

(** Recall the definition of [incr]. *)

Definition incr : val :=
  VFun 'p :=
    Let 'n := '! 'p in
    Let 'm := 'n '+ 1 in
   'p ':= 'm.

(** Recall the definition of [mysucc], which allocates a reference
    with contents [n], increments its contents, then reads the output. *)

Definition mysucc : val :=
  VFun 'n :=
    Let 'r := val_ref 'n in
    incr 'r ';
    Let 'x := '! 'r in
    val_free 'r ';
    'x.

End ProgDef.






(* ******************************************************* *)
[[
    Fixpoint wpgen (t:trm) : formula :=
      mkstruct (match t with
      | trm_val v => fun Q => Q v
      | trm_fun x t1 => fun Q => Q (val_fun x t)
      | trm_fix f x t1 => fun Q => Q (val_fix f x t)
      | trm_seq t1 t2 => fun Q => wpgen t1 (fun v => wpgen t2 Q)
      | trm_let x t1 t2 => fun Q => wpgen t1 (fun v => wpgen (subst x v t2) Q)
      | trm_var x => fun Q => \[False]
      | trm_app v1 v2 => fun Q => wp t Q
      | trm_if t0 t1 t2 => fun Q => 
          \exists (b:bool), \[t0 = trm_val (val_bool b)]
            \* (if b then (wpgen t1) Q else (wpgen t2) Q)
      end).
]]

(* ******************************************************* *)



(* ******************************************************* *)
(** ** Extension of [wpgen] to handle structural rules *)

(*
    However, this definition lacks support for conveniently exploiting
    the structural rules of the logic. We are going to fix this next.
*)


(* ------------------------------------------------------- *)
(** *** Introduction of [mkstruct] in the definition of [wpgen] *)

(** Recall from the previous chapter the statement of the 
    frame rule in [wp]-style. *)

Parameter wp_frame : forall t H Q,
  (wp t Q) \* H ==> wp t (Q \*+ H).

(** We would like [wpgen] to satisfy the same rule, so that we can
    exploit the frame rule while reasoning about a program using
    the heap predicate produced by [wpgen]. 
    
    With the definition of [wpgen] set up so far, it is possible
    to prove, for any concrete term [t], that the frame property
    [(wpgen t Q) \* H ==> wpgen t (Q \*+ H)] holds.
    However, establishing this result requires an induction over
    the entire structure of the term [t]---a lot of tedious work.

    Instead, we are going to tweak the definition of [wpgen] so as to
    produce, at every step of the recursion, a special token to capture
    the property that "whatever the details of the output predicate 
    produced, it does satisfy the frame property". *)

(** We achieve this magic in three steps. First, we rewrite the 
    prototype of the function [wpgen] so as to make it explicitly
    a function of the postcondition [Q].

[[
    Fixpoint wpgen (t:trm) : (val->hprop)->hprop :=
      fun (Q:val->hprop) =>   
        match t with
        | trm_val v => Q v
        | .. => ..
        end.

]]

    Second, we introduce a predicate called [mkstruct], and insert 
    it at the head of the output produced by [wpgen] (and all of 
    its recursive invokation) as follows:

[[
    Fixpoint wpgen (t:trm) : (val->hprop)->hprop :=
      mkstruct (
        fun (Q:val->hprop) =>   
          match t with
          | trm_val v => Q v
          | .. => ..
          end).
]]

    The interest of the insertion of [mkstruct] above is that every result 
    of a computation of [wpgen t] on a concrete term [t] is, by construction, 
    of the form [mkstruct F] for some argument [F].

    Third, to enable the function [wpgen] to compute well in Coq,
    we need to swap the [fun Q] with the [match t], so that the
    pattern matching on [t] is visible enough for Coq to simplify it.

[[
    Fixpoint wpgen (t:trm) : (val->hprop)->hprop :=
      mkstruct (
        match t with
        | trm_val v => (fun Q => Q v)
        | .. => (fun Q => ..)
        end).
]]

    There remains to investigate how [mkstruct] should be defined. 
*)


====================


Lemma wpgen_if_sound : forall F1 F2 v0 t1 t2,
  formula_sound t1 F1 ->
  formula_sound t2 F2 ->
  formula_sound (trm_if v0 t1 t2) (wpgen_if v0 F1 F2).
Proof using.
  introv S1 S2. intros Q. unfold wpgen_if. xpull. intros b ->.
  applys himpl_trans wp_if. case_if. { applys S1. } { applys S2. }
Qed.

(* TODO: move *)


===========================




(** [xapp_lemma] reformulates the ramified frame rule, with a goal
    as a [wp] (which is produced by [wpgen] on an application),
    and a premise as a triple (because triples are used to state
    specification lemmas. Observe that the rule includes an identity
    function called [protect], which is used to prevent [xsimpl]
    from performing too aggressive simplifications. *)

(** TODO: explain magic wand !! *)

Lemma xapp_lemma : forall t Q1 H1 H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  H ==> wp t Q.
Proof using. introv M W. rewrite <- wp_equiv. applys~ triple_ramified_frame M. Qed.

(** The [xsimpl'] tactic is a variant of [xsimpl] that clears the
    identity tag [protect] upon completion. *)

Tactic Notation "xsimpl'" := xsimpl; unfold protect.




Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1))).
Proof using.
  intros.
  applys xwp_lemma. { reflexivity. }
  (* Here the [wpgen] function computes. *)
  simpl.
  (* Observe how each node begin with [mkstruct].
     Observe how program variables are all eliminated. *)
  applys xstruct_lemma.
  applys xlet_lemma.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_get. }
  xsimpl'. intros ? ->.
  applys xstruct_lemma.
  applys xlet_lemma.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_add. }
  xsimpl'. intros ? ->.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_set. }
  xsimpl'. intros ? ->.
  xsimpl'. auto.
Qed.

(* EX2! (triple_mysucc_with_xlemmas) *)
(** Using x-lemmas, verify the proof of [triple_mysucc].
    (The proof was carried out using triples in chapter [SLFRules].) *)

Lemma triple_mysucc_with_xlemmas : forall (n:int),
  triple (trm_app mysucc n)
    \[]
    (fun v => \[v = n+1]).
Proof using.
(* SOLUTION *)
  intros.
  applys xwp_lemma. { reflexivity. }
  simpl; unfold wpgen_var; simpl. 
  applys xstruct_lemma.
  applys xlet_lemma.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_ref. }
  xsimpl'. intros ? l ->.
  applys xstruct_lemma.
  applys xseq_lemma.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_incr. }
  xsimpl'. intros ? ->.
  applys xstruct_lemma.
  applys xlet_lemma.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_get. }
  xsimpl'. intros ? ->.
  applys xstruct_lemma.
  applys xseq_lemma.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_free. }
  xsimpl'. intros ? ->.
  applys xstruct_lemma.
  applys xval_lemma.
  xsimpl'. auto.
(* /SOLUTION *)
Qed.

End ProofsWithXlemmas.

Tactic Notation "xapp" :=
  xseq_xlet_if_needed; xstruct_if_needed; applys xapp_lemma.


Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1))).
Proof using.
  xwp.
  xapp. { apply triple_get. } xsimpl' ;=> ? ->.
  xapp. { apply triple_add. } xsimpl' ;=> ? ->.
  xapp. { apply triple_set. } xsimpl' ;=> ? ->.
  xsimpl. auto.
Qed.

(* EX2! (triple_mysucc_with_xtactics) *)
(** Using x-tactics, verify the proof of [mysucc]. *)

Lemma triple_mysucc_with_xtactics : forall (n:int),
  triple (trm_app mysucc n)
    \[]
    (fun v => \[v = n+1]).
Proof using.
(* SOLUTION *)
  xwp.
  xapp. { apply triple_ref. } xsimpl' ;=> ? l ->.
  xapp. { apply triple_incr. } xsimpl' ;=> ? ->.
  xapp. { apply triple_get. } xsimpl' ;=> ? ->.
  xapp. { apply triple_free. } xsimpl' ;=> ? ->.
  xval.
  xsimpl. auto.
(* /SOLUTION *)
Qed.


============================

Lemma xapp_lemma_wand : forall t Q1 H1 H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  H ==> wp t Q.
Proof using. introv M W. rewrite <- wp_equiv. applys~ triple_ramified_frame M. Qed.


(** The [xsimpl'] tactic is a variant of [xsimpl] that clears the
    identity tag [protect] upon completion. *)

Tactic Notation "xsimpl'" := xsimpl; unfold protect.

Observe that the rule includes an identity
    function called [protect], which is used to prevent [xsimpl]
    from performing too aggressive simplifications. *)



(** We further improve [xapp] in two ways.

    First, we introduce the variant [xapp' E] which mimics the
    proof pattern: [xapp. { apply E. } xsimpl'.]. Concretely,
    [xapp' E] directly exploits the specification [E] rather
    than requiring an explicit [apply E], and a subsequent [xsimpl']. *)

Tactic Notation "xapp_pre" :=
  xseq_xlet_if_needed; xstruct_if_needed.

Tactic Notation "xapp" constr(E) :=
  xapp_pre; applys xapp_lemma E; xsimpl'.

(** Second, we introduce the variant [xapps E] to mimic the
    pattern [xapp. { apply E. } xsimpl' ;=> ? ->]. Concretely,
    the tactic [xapps E] exploits a specification [E] whose conclusion
    is of the form [fun r => \[r = v] \* H] or [fun r => \[r = v]],
    and for which the user wishes to immediately substitute [r] away. *)

Lemma xapps_lemma0 : forall t v H1 H Q,
  triple t H1 (fun r => \[r = v]) ->
  H ==> H1 \* (protect (Q v)) ->
  H ==> wp t Q.
Proof using. introv M W. applys xapp_lemma M. xchanges W. intros ? ->. auto. Qed.

Lemma xapps_lemma1 : forall t v H1 H2 H Q,
  triple t H1 (fun r => \[r = v] \* H2) ->
  H ==> H1 \* (H2 \-* protect (Q v)) ->
  H ==> wp t Q.
Proof using. introv M W. applys xapp_lemma M. xchanges W. intros ? ->. auto. Qed.

Tactic Notation "xapps" constr(E) :=
  xapp_pre; first
  [ applys xapps_lemma0 E
  | applys xapps_lemma1 E ];
  xsimpl'.

(** Third, we instrument [eauto] to automatically figure out the
    specification lemma that should be provided as argument to [xapp] or [xapps].
    To that end, we set up a data base of hints gathering all the
    specification triples established for functions that we might call. *)

Hint Resolve triple_get triple_set triple_ref triple_free triple_add : triple.

Ltac xapp_using lemma :=
  applys lemma; [ solve [ eauto with triple ] | xsimpl' ].

Tactic Notation "xapp" :=
   xapp_pre; xapp_using xapp_lemma.

Tactic Notation "xapps" :=
  xapp_pre; first [ xapp_using xapps_lemma0 
                  | xapp_using xapps_lemma1 ].








(* ####################################################### *)
(** Appendix *)

(** Remark: recall that [\[P]] can be encoded as [\exists (p:P), \[]].
    One may exploit this equivalence to show that [hoare_hpure]
    is derivable from [hoare_hexists], as illustrated next. *)

Lemma triple_hpure_derived_from_triple_exists : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  introv M. rewrite hpure_eq_hexists_proof. (* TODO: fix display *)
  rewrite hstar_hexists. applys triple_hexists.
  rewrite hstar_hempty_l. apply M.
Qed.
