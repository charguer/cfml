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

(** In the previous chapter, we have introduced a predicate called [wp]
    to describe the weakest precondition of a term [t] with respect to
    a given postcondition [Q]. The weakest precondition [wp] is defined
    by the equivalence [H ==> wp t Q] if and only if [triple t H Q].

    This definition gives a "semantics" to [wp], for which reasoning
    rules can be proved. For example, [wp (trm_seq t1 t2) Q] is
    entailed by [wp t1 (fun r => wp t2 Q)], as captured by lemma [wp_seq].

    In this chapter, we introduce a function to "compute" [wpgen t Q]
    recursively over the structure of the term [t]. For example,
    [wpgen t Q] is essentially defined as [wpgen t1 (fun r => wpgen t2 Q)].

    The intention is for [wpgen t Q] to recursively construct a heap predicate
    that has the same interpretation [wp t Q], but that can be directly
    used for interactive reasoning about a concrete term [t].

    The predicate [wpgen t Q] enables convenient interactive reasoning
    about a concrete term [t]. Contrary to [wp t Q], the manipulation of
    [wpgen t Q]:

    - does not require manipulating the concrete syntax (AST) of the term [t],
    - does not require manipulating substitutions of the form [subst x v t1],
    - does not require manual invokation of the reasoning rules such as [wp_seq],
      because these rules are "pre-applied" in the formula [wpgen t Q].

    The matter of the present chapter is to show:

    - how to define [wpgen t Q] as a recursive function that computes in Coq,
    - how to integrate support for the frame rule in this recursive definition,
    - how to carry out practical proofs using [wpgen t Q].

    A bonus section explains how to establish the soundness theorem for [wpgen].
*)


(* ******************************************************* *)
(** ** Summary *)

(** The "chapter in a rush" overview that comes next is fairly short.
    It only gives a bird-eye tour of the steps of the construction.
    All the explanations are provided in the main body of the chapter. *)

(** At first, [wpgen t Q] is presented as a recursive function
    that pattern matches on its argument [t] and produces the
    appropriate heap predicate in each case.

[[
    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => Q v
      | trm_var x => \[False]
      | trm_app v1 v2 => wp t Q
      | trm_let x t1 t2 => wpgen t1 (fun v => wpgen (subst x v t2) Q)
      ...
      end.
]]

    In a second step, the definition is modified to make it structurally
    recursive. It is changed to the form [wpgen E t Q], where [E] denotes
    an association list bindings values to variables. The intention is that
    [wpgen E t Q] computes the weakest precondition for [isubst E t], which
    is the result of substituting bindings from [E] inside [t].

[[
    Fixpoint wpgen (E:ctx) (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => Q v
      | trm_var x =>
           match lookup x E with
           | Some v => Q v
           | None => \[False]
           end
      | trm_app v1 v2 => wp (isubst E t) Q
      | trm_let x t1 t2 => wpgen E t1 (fun v => wpgen ((x,v)::E) t2 Q)
      ...
      end.
]]

    In a third step, the argument [Q] is moved below the [match t with].
    The type of [wpgen E t] is [(val->hprop)->hprop], which is abbreviated
    as [formula].

[[
    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      match t with
      | trm_val v =>  fun (Q:val->hprop) => Q v
      | trm_var x =>  fun (Q:val->hprop) =>
           match lookup x E with
           | Some v => Q v
           | None => \[False]
           end
      | trm_app v1 v2 => fun (Q:val->hprop) =>  wp (isubst E t) Q
      | trm_let x t1 t2 => fun (Q:val->hprop) =>
                              wpgen E t1 (fun v => wpgen ((x,v)::E) t2 Q)
      ...
      end.
]]

    In a fourth step, auxiliary definitions, e.g. [wpgen_val], [wpgen_var],
    are [wpgen_let] are introduced, to improve the readability of the output.

[[
    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      match t with
      | trm_val v => wpgen_val v
      | trm_var x => wpgen_var E x
      | trm_app t1 t2 => wp (isubst E t)
      | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
      ...
      end.
]]

    For example, [wpgen_let] is defined as:

[[
    Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := fun Q =>
      F1 (fun v => F2of v Q).
]]

    And this definition comes with a custom notation:

[[
    Notation "'Let'' x ':=' F1 'in' F2" :=
      ((wpgen_let F1 (fun x => F2))).
]]

    The result of invoking [wpgen] on a let-binding is a formula that displays
    in the form [Let' x := F1 in F2], where [F1] and [F2] denote the result of
    [wpgen] for the subterms of that let-binding.


    In a fifth step, a predicate [mkstruct] is inserted at the head of the
    output of [wpgen] (and of all its recursive invokation), to enable capturing
    the structural rules of the logic.

[[
    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct (match t with
                | trm_val v => ...
                | ...
                end).
]]

    In a sixth step, tactics are introduced to manipulate the elements from
    the output of [wpgen]. For example, [xstruct_lemma] enables dropping
    [mkstruct] when it is not needed, and [xlet_lemma] reveals the definition
    of [wpgen_let]. These lemmas are exploited by the implementation of the
    x-tactics, for example [xlet].

[[

    Lemma xstruct_lemma : forall F H Q,
      H ==> F Q ->
      H ==> mkstruct F Q.

    Lemma xlet_lemma : forall H F1 F2of Q,
      H ==> F1 (fun v => F2of v Q) ->
      H ==> mkstruct (wpgen_let F1 F2of Q).

    Tactic Notation "xlet" :=
      applys xstruct_lemma; applys xlet_lemma.
]]

    The benefits of using the x-tactics is well illustrated by the demo
    contained in this file. Search for the tag "THE_DEMO" in this file,
    and contemplate the proof scripts at that location.

*)


(* ####################################################### *)
(** * Additional contents *)


(* ******************************************************* *)
(** ** Definition of [wpgen] for term rules *)

(** [wpgen] computes a heap predicate that has the same meaning as [wp].
    In essence, [wpgen] takes the form of a recursive function that,
    like [wp], expects a term [t] and a postcondition [Q], and produces
    a heap predicate. The function is recursively defined and its result
    is guided by the structure of the term [t].

    In essence, the definition of [wpgen] admits the following shape:

[[
    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => ..
      | trm_seq t1 t2 => ..
      | trm_let x t1 t2 => ..
      | trm_var x => ..
      | trm_app t1 t2 => ..
      | trm_fun x t1 => ..
      | trm_fix f x t1 => ..
      | trm_if v0 t1 t2 => ..
      end).
]]

    Our first target is to figure out how to fill in the dots for each of the
    term constructors.

    The intention that guides us for filling the dot is the soundness theorem
    for [wpgen], which takes the following form:

[[
    wpgen t Q ==> wp t Q
]]

    This entailement asserts in particular that, if we are able to establish
    a statement of the form [H ==> wpgen t Q], then we can derive from it
    [H ==> wp t Q]. The latter is also equivalent to [triple t H Q].
    Thus, [wpgen] can be viewed as a practical tool to establish triples.

    Remark: the main difference between [wpgen] and a "traditional" weakest
    precondition generator (as the reader might have seen for Hoare logic)
    is that here we compute the weakest precondition of a raw term,
    not annotated with any invariant or specification.

*)


(* ------------------------------------------------------- *)
(** *** Definition of [wpgen] for values *)

(** Consider first the case of a value [v]. Recall the reasoning
    rule for values in weakest-precondition style. *)

Parameter wp_val : forall v Q,
  Q v ==> wp (trm_val v) Q.

(** The soundness theorem for [wpgen] requires us to have:
    [wpgen (trm_val v) Q ==> wp (trm_val v) Q].

    To satisfy this entailement, according to the rule [wp_val],
    it suffices to define [wpgen (trm_val v) Q] as [Q v].

    Concretely, we fill in the first dots as follows:

[[
    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => Q v
      ...
]]

*)


(* ------------------------------------------------------- *)
(** *** Definition of [wpgen] for functions *)

(** Consider the case of a function definition [trm_fun x t].
    Recall that the [wp] reasoning rule for functions is very similar
    to that for values: *)

Parameter wp_fun : forall x t1 Q,
  Q (val_fun x t1) ==> wp (trm_fun x t1) Q.

(** So, likewise, we can define [wpgen] for functions and for
    recursive functions as follows:

[[
    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_fun x t1   => Q (val_fun x t1)
      | trm_fix f x t1 => Q (val_fix f x t1)
      ...
]]

*)

(** An important observation is that we here do not attempt to
    to recursively compute [wpgen] over the body of the function.
    This is something that we could do, and that we will see how
    to achiever further on, but postpone it for now because it is
    relatively technical. In practice, if the program feature a
    local function definition, the user can easily request the
    computation of [wpgen] over the body of that function. Thus,
    the fact that we do not recursively traverse functions bodies
    does not harm expressivity. *)


(* ------------------------------------------------------- *)
(** *** Definition of [wpgen] for sequence *)

(** Recall the [wp] reasoning rule for a sequence [trm_seq t1 t2]: *)

Parameter wp_seq : forall t1 t2 Q,
  wp t1 (fun v => wp t2 Q) ==> wp (trm_seq t1 t2) Q.

(** The intention is for [wpgen] to admit the same semantics as [wp].
    We thus expect the definition of [wpgen (trm_seq t1 t2) Q] to have a
    similar shape as [wp t1 (fun v => wp t2 Q)].

    We therefore define [wpgen (trm_seq t1 t2) Q] as
    [wpgen t1 (fun r => wpgen t2 Q)]. Concretely:

[[
    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_seq t1 t2 => wpgen t1 (fun v => wpgen t2 Q)
      ...
]]

*)

(* ------------------------------------------------------- *)
(** *** Definition of [wpgen] for let-bindings *)

(** The case of let bindings is similar to that of sequences,
    yet it involves a substitution. Recall the [wp] rule: *)

Parameter wp_let : forall x t1 t2 Q,
  wp t1 (fun v => wp (subst x v t2) Q) ==> wp (trm_let x t1 t2) Q.

(** We fill in the dots as follows:

[[
    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_let x t1 t2 => wpgen t1 (fun v => wpgen (subst x v t2) Q)
      ...
]]

    One important observation to make at this point is that the
    function [wpgen] is no longer structurally recursive. Indeed,
    while the first recursive call to [wpgen] is invoked on [t1], which
    is a strict subterm of [t], the second call is invoked on [subst x v t2],
    which is not a strict subterm of [t].

    It is possible to  convince Coq that the function [wpgen] nevertheless
    terminates, or, more simply, to circumvent the problem altogether by
    casting the function in a form that makes it structurally recursive.
    Concretely, we will see further on how to add as argument to [wpgen]
    a substitution context (written [E]) to delay the computation of
    substitutions until the leaves of the recursion. *)


(* ------------------------------------------------------- *)
(** *** Definition of [wpgen] for variables *)

(** There are no reasoning rules to establish a triple or a [wp]-entailment
    for a program variable. In other words, there are no rules to prove
    [triple (trm_var x) H Q] or prove concludes [H ==> wp (trm_var x) Q].
    Indeed, [trm_var x] is a stuck term---its execution does not produce
    an output.

    While a source term may contain program variables, all these variables
    should have been substituted away before the execution reaches them.
    In the case of the function [wpgen], the variables bound by a "let"
    get substituted while traversing the let-binding construct.
    If a free variable is reached by [wpgen], it means that this variable
    was a dandling free variable, and therefore that the initial source term
    was invalid.

    Although there are no rules to introduce [wp (trm_var x) Q], we
    nevertheless have to provide some meaningful definition for
    [wpgen (trm_var x) Q]. This definition should capture the fact
    that this case must not happen. The heap predicate [\[False]] captures
    this intention perfectly.

[[
    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_var x => \[False]
      ...
]]

*)

(** Remark: the definition of \[False] translates the fact that,
    technically, we could have stated a Separation Logic rule
    for free variables, using [False] as a premise, either as a triple: *)

Lemma triple_var : forall x H Q,
  False ->
  triple (trm_var x) H Q.
Proof using. intros. false. Qed.

(** or as a [wp]-entailemnt with [\[False]] as precondition: *)

Lemma wp_var : forall x Q,
  \[False] ==> wp (trm_var x) Q.
Proof using. intros. intros h Hh. destruct (hpure_inv Hh). false. Qed.

(** These two rules are correct, albeit totally useless in practice. *)


(* ------------------------------------------------------- *)
(** *** Definition of [wpgen] for function applications *)

(** Consider an application in A-normal form, that is,
    an application of the form [trm_app v1 v2].

    We have [wp]-style rules to reason about the application of
    a known function, e.g. [trm_app (val_fun x t1) v2].
    However, if [v1] is an abstrat value (e.g., a Coq variable
    of type [var]), we have no reasoning rule at hand that applies.

    Thus, we will simply define [wpgen (trm_app v1 v2) Q] as
    [wp (trm_app v1 v2) Q]. In other words, to define [wpgen] for
    a function application, we fall back to the semantic definition of [wp].

[[
    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_app v1 v2 => wp (trm_app v1 v2) Q
      ...
]]

    As we carry out verification proofs in practice, when reaching
    an application we will face a goal of the form:
[[
    H ==> wpgen (trm_app v1 v2) Q
]]
    By revealing the definition of [wpgen] on applications, we get:
[[
    H ==> wp (trm_app v1 v2) Q
]]
    Then by exploiting the equivalence with triples, we obtain:
[[
    triple (trm_app v1 v2) H Q
]]
    which can be proved by invoking a specification triple for
    the function [v1].

    In other words, by falling back to the semantics definition
    when reaching a function application, we allow the user to choose
    which specification lemma to exploit for reasoning about this
    particular function application. *)

(** Remark: we assume throughout the course that terms are written
    in A-normal form. Nevertheless, we need to define [wpgen] even
    on terms that are not in A-normal form. One possibility is
    to map all these terms to [\[False]]. In the specific case of an
    application of the form [trm_app t1 t2] where [t1] and [t2] are
    not both values, it is still correct to define [wpgen (trm_app t1 t2))
    as [wp (trm_app t1 t2)]. So, we need not bother checking here
    that the arguments of [trm_app] are actually values.

    Thus, the most concise definition for [wpgen] on applications is:

[[
    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      ...
      | trm_app t1 t2 => wp t Q
      ...
]]

*)


(* ------------------------------------------------------- *)
(** *** Definition of [wpgen] for conditionals *)

(** The last remaining case is that for conditionals.
    Recall the [wp]-style reasoning rule stated using
    a Coq conditional. *)

Parameter wp_if : forall (b:bool) t1 t2 Q,
  (if b then (wp t1 Q) else (wp t2 Q)) ==> wp (trm_if b t1 t2) Q.

(** The statement above actually features hidden coercions.
    The right-hand side of the entailment only applies to a term
    of the form [trm_if (trm_val (val_bool b)) t1 t2].

    Yet, we need to define [wpgen] for all conditionals in A-normal
    form, i.e., all terms of the form [trm_if (trm_val v0) t1 t2], where
    [v0] could a value of unknown shape. Typically, a program may feature
    a conditional [trm_if (trm_var x) t1 t2] that, after substitution
    for [x], becomes [trm_if (trm_val v) t1 t2], for some abstract
    [v] of type [val] that might not yet be know to be a boolean value.

    To handle the problem, we pattern match a conditional as [trm_if t0 t1 t2],
    and define its [wpgen] as a heap predicate that requires the existence
    of a boolean [b] such that [t0 = trm_val (val_bool b)].
    This way, we delay the moment at which the argument of the conditional
    needs to be shown to be a boolean value. The formal definition is:

[[
    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_if t0 t1 t2 =>
          \exists (b:bool), \[t0 = trm_val (val_bool b)]
            \* (if b then (wpgen t1) Q else (wpgen t2) Q)
      ...
]]

*)

(* ------------------------------------------------------- *)
(** *** Summary of the definition of [wpgen] for term rules *)

(** In summary, we have defined:

[[
    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => Q v
      | trm_fun x t1 => Q (val_fun x t)
      | trm_fix f x t1 => Q (val_fix f x t)
      | trm_seq t1 t2 => wpgen t1 (fun v => wpgen t2 Q)
      | trm_let x t1 t2 => wpgen t1 (fun v => wpgen (subst x v t2) Q)
      | trm_var x => \[False]
      | trm_app v1 v2 => wp t Q
      | trm_if t0 t1 t2 =>
          \exists (b:bool), \[t0 = trm_val (val_bool b)]
            \* (if b then (wpgen t1) Q else (wpgen t2) Q)
      end.
]]

    As pointed out earlier, this definition is not structurally recursive
    and thus not accepted by Coq, due to the recursive call
    [wpgen (subst x v t2) Q]. Our next step is to fix this recursion issue. *)


(* ******************************************************* *)
(** ** Computating with [wpgen] *)

(** [wpgen] is not structurally recursive because of the substitutions
    that takes places in-between recursive calls. To fix this, we are
    going to delay the substitutions until the leaves of the recursion.
    To that end, we introduce a substitution context, written [E], to
    record the substitutions that should have been performed.

    Concretely, we modify the function to take the form [wpgen E t],
    where [E] denotes a set of bindings from variables to values.
    The intention is that [wpgen E t] computes the weakest precondition
    for the term [isubst E t], which denotes the result of substituting
    all bindings from E inside the term [t]. *)


(* ------------------------------------------------------- *)
(** *** Definition of contexts and operations on them *)

(** The simplest way to define a context [E] is as an association
    list relating variables to values. *)

Definition ctx : Type := list (var*val).

(** Before we present how the introduction of a context impacts
    the definition of [wpgen], we need to formalize the "iterated
    substitution" operation, written [isubst E t]. The definition
    is relatively standard: the substitution traverses the term
    recursively and, when reaching a variable, performs a lookup
    in the term [E].

    The definition of the [lookup] operation on association lists
    is standard. *)

Fixpoint lookup (x:var) (E:ctx) : option val :=
  match E with
  | nil => None
  | (y,v)::E1 => if var_eq x y
                   then Some v
                   else lookup x E1
  end.

(** One additional technicality is the need to respect variable shadowing,
    which imposes to remove bindings on a variable [x] when entering
    through the scope of a bound variable named [x]. The removal operation
    on a context represented as an association list is also standard. *)

Fixpoint rem (x:var) (E:ctx) : ctx :=
  match E with
  | nil => nil
  | (y,v)::E1 =>
      let E1' := rem x E1 in
      if var_eq x y then E1' else (y,v)::E1'
  end.

(* The definition of the operation [isubst] can then be expressed as a
   recursive function over the term [t]. *)

Fixpoint isubst (E:ctx) (t:trm) : trm :=
  match t with
  | trm_val v =>
       v
  | trm_var x =>
       match lookup x E with
       | None => t
       | Some v => v
       end
  | trm_fun x t1 =>
       trm_fun x (isubst (rem x E) t1)
  | trm_fix f x t1 =>
       trm_fix f x (isubst (rem x (rem f E)) t1)
  | trm_app t1 t2 =>
       trm_app (isubst E t1) (isubst E t2)
  | trm_seq t1 t2 =>
       trm_seq (isubst E t1) (isubst E t2)
  | trm_let x t1 t2 =>
       trm_let x (isubst E t1) (isubst (rem x E) t2)
  | trm_if t0 t1 t2 =>
       trm_if (isubst E t0) (isubst E t1) (isubst E t2)
  end.

(** Remark: it would be also possible to define the substitution by
    iterating the unary substitution [subst] over the list of bindings
    from [E], however doing so is much less efficient and would
    complicate proofs. *)


(* ------------------------------------------------------- *)
(** *** [wpgen]: the let-binding case *)

(** When [wpgen] traverses a let-binding, rather than eargerly
    performing a substitution, it simply extends the current context.
    Concretely, a call to [wpgen E (trm_let x t1 t2)] triggers a recursive
    call to [wpgen ((x,v)::E) t2]. The corresponding definition is:

[[
  Fixpoint wpgen (E:ctx) (t:trm) : formula :=
    mkstruct (match t with
      ...
      | trm_let x t1 t2 => fun Q =>
           (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
      ...
      ) end.
]]

*)


(* ------------------------------------------------------- *)
(** *** [wpgen]: the variable case *)

(** When [wpgen] reaches a variable, it lookups for a binding
    on the variable [x] inside the context [E]. Concretely, the evaluation
    of [wpgen E (trm_var x)] triggers a call to [lookup x E].

    If the context [E] binds the variable [x] to some value [v], then
    the operation [lookup x E] returns [Some v]. In that case,
    [wpgen] returns the weakest precondition for that value [v],
    that is, [Q v].

    Otherwise, if [E] does not bind [x], the lookup operation returns [None].
    In that case, [wpgen] returns [\[False]], which we have explained to be
    the weakest precondition for a stuck program.

[[
  Fixpoint wpgen (E:ctx) (t:trm) : formula :=
    mkstruct (match t with
      ...
      | trm_var x => fun Q =>
           match lookup x E with
           | Some v => Q v
           | None => \[False]
           end
      ...
      ) end.
]]

*)


(* ------------------------------------------------------- *)
(** *** [wpgen]: the application case *)

(** In the previous definition of [wpgen] with contexts, the argued
    that the result of [wpgen t Q] in the case where [t] is an application
    should be simply [wp t Q]. In other words, we resort to the semantics
    interpretation for an application.

    In the definition of [wpgen] with contexts, the intepretation of
    [wpgen E t] is the weakest precondition of the term [isubst E t],
    which denotes the result of substituting variables from [E] in [t].

    When [t] is an application, we thus define [wpgen E t] as the formula
    [fun Q => wp (isubst E t) Q], or simply [wp (isubst E t)] by eliminating
    the useless eta-expansion.

[[
  Fixpoint wpgen (t:trm) : formula :=
    mkstruct (match t with
      ...
      | trm_app v1 v2 => wp (isubst E t)
      ..
]]

*)


(* ------------------------------------------------------- *)
(** *** [wpgen]: the function definition case *)

(** Consider the case where [t] is a function definition, for example
    [trm_fun x t1]. The formula [wpgen E t] is interpreted as the weakest
    precondition of [isubst E t].

    By unfolding the definition of [isubst] in the case where [t] is
    [trm_fun x t1], we obtain [trm_fun x (isubst (rem x E) t1)].

    The weakest precondition for that value is
    [fun Q => Q (val_fun x (isubst (rem x E) t1))].
    Thus, [wpgen E t] handles functions, and recursive functions, as follows:

[[
  Fixpoint wpgen (E:ctx) (t:trm) : formula :=
    mkstruct (match t with
      ...
      | trm_fun x t1 => fun Q => Q (val_fun x (isubst (rem x E) t1))
      | trm_fix f x t1 => fun Q => Q (val_fix f x (isubst (rem x (rem f E)) t1))
      ...
      ) end.
]]

*)


(* ------------------------------------------------------- *)
(** *** [wpgen]: at last, an executable function *)

Module WpgenExec1.

(** At last, we arrive to a definition of [wpgen] that typechecks in Coq,
    and that can be used to effectively compute weakest preconditions in
    Separation Logic. *)

Fixpoint wpgen (E:ctx) (t:trm) (Q:val->hprop) : hprop :=
  match t with
  | trm_val v => Q v
  | trm_fun x t1 => Q (val_fun x (isubst (rem x E) t1))
  | trm_fix f x t1 => Q (val_fix f x (isubst (rem x (rem f E)) t1))
  | trm_seq t1 t2 => wpgen E t1 (fun v => wpgen E t2 Q)
  | trm_let x t1 t2 => wpgen E t1 (fun v => wpgen ((x,v)::E) t2 Q)
  | trm_var x =>
       match lookup x E with
       | Some v => Q v
       | None => \[False]
       end
  | trm_app v1 v2 => wp (isubst E t) Q
  | trm_if t0 t1 t2 =>
      \exists (b:bool), \[t0 = trm_val (val_bool b)]
        \* (if b then (wpgen E t1) Q else (wpgen E t2) Q)
  end.

(** Compared with the presentation using the form [wpgen t], the
    new presentation using the form [wpgen E t] has the main benefits
    that it is structurally recursive, thus easy to define in Coq.
    Moreover, it is algorithmically more efficient in general, because
    it performs substitutions easily rather than eagerly. *)

(** Let us state the soundness theorem and its corollary for establishing
    triples for functions. *)

Parameter wpgen_sound : forall E t Q,
   wpgen E t Q ==> wp (isubst E t) Q.

(** The entailement above asserts in particular that if we can derive
    [triple t H Q] by proving [H ==> wpgen t Q]. *)

(** There is a corrolary of the soundness theorem that is particularly
    useful for establishing triples for functions. Recall for [SLFRules]: *)

Parameter triple_app_fun : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (v1 v2) H Q.

(** If we rewrite the premise [triple (subst x v2 t1) H Q] as a [wp],
    we get [H ==> wp (subst x v2 t1) Q].

    The term [subst x v2 t1] is equal to [isubst ((x,v2)::nil) t1].
    Thus, the heap predicate [wp (subst x v2 t1) Q] is equivalent to
    [wp (isubst ((x,v2)::nil) t1)].

    According to [wpgen_sound], that predicate [wp (isubst ((x,v2)::nil) t1)]
    is entailed by [wpgen ((x,v2)::nil) t1]. Thus, we derive the corollary: *)

Parameter triple_app_fun_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.


(* ------------------------------------------------------- *)
(** *** Executing [wpgen] on a concrete program *)

Import ExamplePrograms.

(** Using [triple_app_fun_from_wpgen], we can demonstrate the
    computation of a [wpgen] on a practical program.

    Recall the function [incr] (defined in SLFRules), and its
    specification, whose statement appears below. *)

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1))).
Proof using.
  intros. applys triple_app_fun_from_wpgen. { reflexivity. }
  simpl. (* Read the goal here... *)
Abort.

(** The goal takes the form [H ==> wpgen body Q],
    where [H] denotes the precondition, [Q] the postcondition,
    and [body] the body of the function [incr].

    Observe the invokations of [wp] on the application of primitive
    operations.

    Observe that the goal is nevertheless somewhat hard to relate
    to the original program...

    In what follows, we explain how to remedy the situation, and
    set up [wpgen] is such a way that its output is human-readable,
    moreover resembles the original source code. *)

End WpgenExec1.



(* ******************************************************* *)
(** ** Optimizing the readability of [wpgen] output *)

(** To improve there readability, we transform the function is three steps:

    - first, we modify the presentation of [wpgen] so that the
      [fun (Q:val->hprop) =>] appears insides the branches of the
      [match t with] rather than around it;
    - second, we introduce one auxiliary definition for each branch
      of the [match t with],
    - third, we introduce one piece of notation for each of these
      auxiliary definitions. *)


(* ------------------------------------------------------- *)
(** *** Reability Step 1: moving the function below the branches. *)

(** We change from:

[[
    Fixpoint wpgen (E:ctx) (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v     =>  Q v
      | trm_fun x t1  =>  Q (val_fun x (isubst (rem x E) t1))
      ...
      end.
]]

    to the equivalent form:

[[
    Fixpoint wpgen (E:ctx) (t:trm) : (val->hprop)->hprop :=
      match t with
      | trm_val v     =>  fun (Q:val->hprop) => Q v
      | trm_fun x t1  =>  fun (Q:val->hprop) => Q (val_fun x (isubst (rem x E) t1))
      ...
      end.
]]

*)

(** The result type of [wpgen E t] is [(val->hprop)->hprop].
    Thereafter, we let [formula] be a shorthand for this type. *)

Definition formula : Type := (val->hprop)->hprop.


(* ------------------------------------------------------- *)
(** *** Reability Steps 2 and 3, illustrated on the case of sequences *)

(** In step 2, we change from:

[[
    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      match t with
      ...
      | trm_seq t1 t2 =>  fun Q => (wpgen E t1) (fun v => wpgen E t2 Q)
      ...
      end.
]]

    to the equivalent form:

[[
    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      match t with
      ...
      | trm_seq t1 t2 =>  wpgen_seq (wpgen E t1) (wpgen E t2)
      ...
     end.
]]

    where [wpgen_seq] is defined as: *)


Definition wpgen_seq (F1 F2:formula) : formula := fun Q =>
  F1 (fun v => F2 Q).

(** Remark: above, [F1] and [F2] denote the results of the recursive calls,
    [wpgen E t1] and [wpgen E t2], respectively.

    With the above definitions, [wgpen E (trm_seq t1 t2)]
    evaluates to [wp_seq (wpgen E t1) (wpgen E t2)]. *)


(** In step 3, we introduce a piece of notation so that any formula
    of the form [wpgen_seq F1 F2] displays as [Seq F1 ; F2 ].  *)

Notation "'Seq' F1 ; F2" :=
  ((wpgen_seq F1 F2))
  (at level 68, right associativity,
   format "'[v' 'Seq'  '[' F1 ']'  ';'  '/'  '[' F2 ']' ']'").

(** Thanks to this notation, the [wpgen] of a sequence [t1 ; t2] displays as
    [Seq F1 ; F2] where [F1] and [F2] denote the [wpgen] of [t1] and [t2],
    respectively. *)


(* ------------------------------------------------------- *)
(** *** Reability Step 2: Auxiliary definitions for other constructs *)

(** We generalize the approach illustrated for sequences to every other
    term construct. The corresponding definitions are stated below.
    It is not required to understand the details from this subsection. *)

Definition wpgen_val (v:val) : formula := fun Q =>
  Q v.

Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := fun Q =>
  F1 (fun v => F2of v Q).

Definition wpgen_if (t:trm) (F1 F2:formula) : formula := fun Q =>
  \exists (b:bool), \[t = trm_val (val_bool b)] \* (if b then F1 Q else F2 Q).

Definition wpgen_fail : formula := fun Q =>
  \[False].

Definition wpgen_var (E:ctx) (x:var) : formula :=
  match lookup x E with
  | None => wpgen_fail
  | Some v => wpgen_val v
  end.

(** The new definition of [wpgen] reads as follows. *)

Module WpgenExec2.

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpgen_var E x
  | trm_fun x t1 => wpgen_val (val_fun x (isubst (rem x E) t1))
  | trm_fix f x t1 => wpgen_val (val_fix f x (isubst (rem x (rem f E)) t1))
  | trm_app t1 t2 => wp (isubst E t)
  | trm_seq t1 t2 => wpgen_seq (wpgen E t1) (wpgen E t2)
  | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
  | trm_if t0 t1 t2 => wpgen_if (isubst E t0) (wpgen E t1) (wpgen E t2)
  end.

(** This definition is, up to unfolding of the new intermediate definitions,
    totally equivalent to the previous one. We will prove the soundness
    result and its corrolary further on. *)

Parameter wpgen_sound : forall E t Q,
   wpgen E t Q ==> wp (isubst E t) Q.

Parameter triple_app_fun_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.

End WpgenExec2.


(* ------------------------------------------------------- *)
(** *** Reability Step 3: Notation for auxiliary definitions *)

(** We generalize the notation introduced for sequences to every other
    term construct. The corresponding notation is defined below.
    It is not required to understand the details from this subsection.

    To avoid conflicts with other existing notation, we write
    [Let'] and [If'] in place of [Let] and [If]. *)

Notation "'Val' v" :=
  ((wpgen_val v))
  (at level 69).

Notation "'Let'' x ':=' F1 'in' F2" :=
  ((wpgen_let F1 (fun x => F2)))
  (at level 69, x ident, right associativity,
  format "'[v' '[' 'Let''  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'").

Notation "'If'' b 'Then' F1 'Else' F2" :=
  ((wpgen_if b F1 F2))
  (at level 69).

Notation "'Fail'" :=
  ((wpgen_fail))
  (at level 69).

(** In addition, we introduce handy notation of the result of [wpgen t]
    where [t] denotes an application. *)

Notation "'App' f v1 " :=
  ((wp (trm_app f v1)))
  (at level 68, f, v1 at level 0).


(* ------------------------------------------------------- *)
(** *** Test of [wpgen] with notation. *)

(** Consider again the example of [incr]. *)

Module WPgenWithNotation.
Import ExamplePrograms WpgenExec2.

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1))).
Proof using.
  intros. applys triple_app_fun_from_wpgen. { reflexivity. }
  simpl. (* Read the goal here... It is of the form [H ==> F Q],
            where [F] vaguely looks like the code of the body of [incr]. *)

  (** Up to proper tabulation, alpha-renaming, and removal of
      parentheses (and dummy quotes after [Let] and [If]), [F] reads as:
[[
  Let n := `(App val_get p) in
  Let m := `(App (val_add n) 1) in
  App (val_set p) m
]]

*)
Abort.

(** Throught the introduction of intermediate definitions for
    [wpgen] and of associated notations for each term construct,
    the output of [wpgen] is human readable and resembles the
    input source code. *)

(* LATER: add an example that shows the lack of support for structural rules. *)

End WPgenWithNotation.


(* ******************************************************* *)
(** ** Extension of [wpgen] to handle structural rules *)

(** The definition of [wpgen] proposed so far integrates the logic of
    the reasoning rules for terms, however it lacks support for
    conveniently exploiting the structural rules of the logic.

    We fix this next, by showing how to tweak the definition of [wpgen]
    in such a way that, by construction, it satisfies both
    - the frame rule [(wpgen t Q) \* H ==> wpgen t (Q \*+ H)]
    - and the rule of consequence [wpgen t Q1 ==> wpgen t Q2] when [Q1 ===> Q2].

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
    the idea that whatever the details of the output predicate produced
    by [wpgen], this predicate does satisfy the frame property. *)

(** We achieve this magic by introducing a predicate called [mkstruct],
    and inserting it at the head of the output produced by [wpgen]
    (and all of its recursive invokation) as follows:

[[
    Fixpoint wpgen (E:ctx) (t:trm) : (val->hprop)->hprop :=
      mkstruct (
        match t with
        | trm_val v => wpgen_val v
        ...
        end).
]]

    The interest of the insertion of [mkstruct] above is that every result
    of a computation of [wpgen t] on a concrete term [t] is, by construction,
    of the form [mkstruct F] for some argument [F].

    Third, to enable the function [wpgen] to compute well in Coq,
    we need to swap the [fun Q] with the [match t], so that the
    pattern matching on [t] is visible enough for Coq to simplify it.



    There remains to investigate how [mkstruct] should be defined.
*)


(* ------------------------------------------------------- *)
(** *** Properties of [mkstruct] *)

Module MkstructProp.

(** Let us state the properties that [mkstruct] should satisfy. *)

(** Because [mkstruct] appears between the prototype and the
    [match] in the body of [wpgen], the predicate [mkstruct]
    has type [formula->formula]. *)

Parameter mkstruct : formula->formula.

(** There remains to find a suitable definition for [mkstruct] that enables
    the frame property and the consequence property. These properties can
    be stated by mimicking the rules [wp_frame] and [wp_conseq]. *)

Parameter mkstruct_frame : forall (F:formula) H Q,
  (mkstruct F Q) \* H ==> mkstruct F (Q \*+ H).

Parameter mkstruct_conseq : forall (F:formula) Q1 Q2,
  Q1 ===> Q2 ->
  mkstruct F Q1 ==> mkstruct F Q2.

(** In addition, it should be possible to erase [mkstruct] from the head
    of the output produced [wpgen t] when we do not need to apply any
    structural rule. In other words, we need to be able to prove
    [H ==> mkstruct F Q] by proving [H ==> F Q], for any [H].
    This erasure property is captured by the following entailment. *)

Parameter mkstruct_erase : forall (F:formula) Q,
  F Q ==> mkstruct F Q.

End MkstructProp.


(* ------------------------------------------------------- *)
(** *** Realization of [mkstruct] *)

(** Fortunately, it turns out that there exists a predicate [mkstruct] satisfying
    the three required properties. Let us pull out of our hat a definition that works. *)

Definition mkstruct (F:formula) : formula :=
  fun (Q:val->hprop) => \exists Q1 H, F Q1 \* H \* \[Q1 \*+ H ===> Q].

(** We postpone to a bonus section the discussion of why it works and of how
    one could have guessed this definition. Again, it really does not matter
    the details of the definition, as long as it satisfies the three required
    properties: [mkstruct_frame], [mkstruct_conseq], and [mkstruct_erase],
    as established below. *)

Lemma mkstruct_frame : forall (F:formula) H Q,
  (mkstruct F Q) \* H ==> mkstruct F (Q \*+ H).
Proof using.
  intros. unfold mkstruct. xpull ;=> Q' H' M. xsimpl. xchange M.
Qed.

Lemma mkstruct_conseq : forall (F:formula) Q1 Q2,
  Q1 ===> Q2 ->
  mkstruct F Q1 ==> mkstruct F Q2.
Proof using.
  introv WQ. unfold mkstruct. xpull ;=> Q' H' M. xsimpl. xchange M. xchange WQ.
 Qed.

Lemma mkstruct_erase : forall (F:formula) Q,
  F Q ==> mkstruct F Q.
Proof using. intros. unfold mkstruct. xsimpl. xsimpl. Qed.

(** Remark: an interesting property of [mkstruct] is its idempotence:
    [mkstruct (mkstruct F) = mkstruct F].

    Idempotence asserts that applying the predicate [mkstruct] more than
    once does provide more expressiveness than applying it just once.

    Intuitively, idempotence reflects in particular the fact that two nested
    applications of the rule of consequence can always be combined into a
    single application of that rule (due to the transitivity of entailement)
    and that, similarly, two nested applications of the frame rule can always
    be combined into a single application of that rule (framing on [H1] then
    framing on [H2] is equivalent to framing on [H1 \* H2]). *)

(* EX3! (mkstruct_idempotent) *)
(** Prove the idempotence of [mkstruct].
    Hint: leverage [xpull] and [xsimpl]. *)

Lemma mkstruct_idempotent : forall F,
  mkstruct (mkstruct F) = mkstruct F.
Proof using.
  intros. apply fun_ext_1. intros Q. applys himpl_antisym.
  (* SOLUTION *)
  { unfold mkstruct. xpull ;=> Q1 H1 Q2 H2 M1 M2.
    xsimpl Q2 (H1 \* H2). xchanges* M1. }
  { applys mkstruct_erase. }
(* /SOLUTION *)
Qed.


(* ------------------------------------------------------- *)
(** *** Definition of [wpgen] featuring [mkstruct] *)

(** Our final definition of [wpgen] is the same as before, except with
    the [mkstruct] predicate appearing before the [match t with]. *)

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  mkstruct (match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpgen_var E x
  | trm_fun x t1 => wpgen_val (val_fun x (isubst (rem x E) t1))
  | trm_fix f x t1 => wpgen_val (val_fix f x (isubst (rem x (rem f E)) t1))
  | trm_app t1 t2 => wp (isubst E t)
  | trm_seq t1 t2 => wpgen_seq (wpgen E t1) (wpgen E t2)
  | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
  | trm_if t0 t1 t2 => wpgen_if (isubst E t0) (wpgen E t1) (wpgen E t2)
  end).

(** Again, we assert soundness and postpone the proof. *)

Parameter wpgen_sound : forall E t Q,
   wpgen E t Q ==> wp (isubst E t) Q.

Parameter triple_app_fun_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.


(* ------------------------------------------------------- *)
(** *** Notation for [mkstruct] and test *)

(** To avoid clutter in reading the output of [wpgen],
    we introduce a tiny shorthand to denote [mkstruct F],
    allowing it to display simply as [`F]. *)

Notation "` F" := (mkstruct F) (at level 10, format "` F").


(** Let us test the output. *)

Module WPgenWithMkstruct.
Import ExamplePrograms.

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1))).
Proof using.
  intros. applys triple_app_fun_from_wpgen. { reflexivity. }
  simpl.
  (** Up to proper tabulation, alpha-renaming, and removal of
      parentheses (and dummy quotes after [Let] and [If]),
     [F] reads as:
[[
  `Let n := `(App val_get p) in
  `Let m := `(App (val_add n) 1) in
  `App (val_set p) m
]]

*)

Abort.

End WPgenWithMkstruct.



(* ####################################################### *)
(** * Practical proofs using [wpgen] *)

(** The last major step consists in introducing lemmas and
    tactics to assist in the processing of formulas produced
    by [wpgen]. *)


(* ******************************************************* *)
(** ** Lemmas for handling [wpgen] goals *)

(** For each term construct, and for [mkstruct], we introduce
    a dedicated lemma, called "x-lemma", to help with the
    elimination of the construct. *)

(** [xstruct_lemma] is a reformulation of [mkstruct_erase]. *)

Lemma xstruct_lemma : forall F H Q,
  H ==> F Q ->
  H ==> mkstruct F Q.
Proof using. introv M. xchange M. applys mkstruct_erase. Qed.

(** [xval_lemma] reformulates the definition of [wpgen_val].
    It just unfolds the definition. *)

Lemma xval_lemma : forall v H Q,
  H ==> Q v ->
  H ==> wpgen_val v Q.
Proof using. introv M. applys M. Qed.

(** [xlet_lemma] reformulates the definition of [wpgen_let].
    It just unfolds the definition. *)

Lemma xlet_lemma : forall H F1 F2of Q,
  H ==> F1 (fun v => F2of v Q) ->
  H ==> wpgen_let F1 F2of Q.
Proof using. introv M. xchange M. Qed.

(** Likewise, [xseq_lemma] reformulates [wpgen_seq]. *)

Lemma xseq_lemma : forall H F1 F2 Q,
  H ==> F1 (fun v => F2 Q) ->
  H ==> wpgen_seq F1 F2 Q.
Proof using. introv M. xchange M. Qed.

(** [xapp_lemma] reformulates the frame rule, with a conclusion
    as a [wp] and a premise as a triple.

    The conclusion is a [wp] to match what is produced by [wpgen]
    on an application. The premise is a [triple] to match the
    statement of specification lemmas. *)

Lemma xapp_lemma : forall t Q1 H1 H2 H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  H ==> wp t Q.
Proof using.
  introv M WH WQ. rewrite <- wp_equiv. applys* triple_conseq_frame M. Qed.

(** [xwp_lemma] is a variant of [wpgen_of_triple] specialized for
    establishing a triple for a function application. The rule reformulates
    [triple_app_fun] with a premise of the form [wpgen E t]. *)

Lemma xwp_lemma : forall v1 v2 x t H Q,
  v1 = val_fun x t ->
  H ==> wpgen ((x,v2)::nil) t Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
  introv M1 M2. applys triple_app_fun M1.
  asserts_rewrite (subst x v2 t = isubst ((x,v2)::nil) t).
  { rewrite isubst_rem. rewrite~ isubst_nil. }
  rewrite wp_equiv. xchange M2. applys wpgen_sound.
Qed.


(* ******************************************************* *)
(** ** An example proof *)

Module ProofsWithXlemmas.
Import ExamplePrograms.

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
  applys xapp_lemma. { apply triple_get. } { xsimpl. }
  xpull ;=> ? ->.
  applys xstruct_lemma.
  applys xlet_lemma.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_add. } { xsimpl. }
  xpull ;=> ? ->.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_set. } { xsimpl. }
  xpull ;=> ? ->.
  xsimpl. auto.
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
  applys xapp_lemma. { apply triple_ref. } { xsimpl. }
  xpull ;=> ? l ->.
  applys xstruct_lemma.
  applys xseq_lemma.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_incr. } { xsimpl. }
  xpull ;=> ? ->.
  applys xstruct_lemma.
  applys xlet_lemma.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_get. } { xsimpl. }
  xpull ;=> ? ->.
  applys xstruct_lemma.
  applys xseq_lemma.
  applys xstruct_lemma.
  applys xapp_lemma. { apply triple_free. } { xsimpl. }
  xpull ;=> ? ->.
  applys xstruct_lemma.
  applys xval_lemma.
  xsimpl. auto.
(* /SOLUTION *)
Qed.

End ProofsWithXlemmas.


(* ******************************************************* *)
(** ** Making proof scripts more concise *)

(** For each term construct, and for [mkstruct] goals, we introduce
    a dedicated tactic to apply the corresponding x-lemma, plus
    performs some basic preliminary work. *)

(** [xstruct] eliminates the leading [mkstruct]. *)

Tactic Notation "xstruct" :=
  applys xstruct_lemma.

(** [xseq] and [xlet] invoke the corresponding lemma, after
    calling [xstruct] if necessary. *)

Tactic Notation "xstruct_if_needed" :=
  try match goal with |- ?H ==> mkstruct ?F ?Q => xstruct end.

Tactic Notation "xval" :=
  xstruct_if_needed; applys xval_lemma.

Tactic Notation "xlet" :=
  xstruct_if_needed; applys xlet_lemma.

Tactic Notation "xseq" :=
  xstruct_if_needed; applys xseq_lemma.

(** [xapp] invokes [xapp_lemma], after calling [xseq] or [xlet]
    if necessary. *)

Tactic Notation "xseq_xlet_if_needed" :=
  try match goal with |- ?H ==> mkstruct ?F ?Q =>
  match F with
  | wpgen_seq ?F1 ?F2 => xseq
  | wpgen_let ?F1 ?F2of => xlet
  end end.

Tactic Notation "xapp" constr(E) :=
  xseq_xlet_if_needed; xstruct_if_needed;
  applys xapp_lemma E; [ xsimpl | xpull ].

(** [xwp] applys [xwp_lemma], then computes [wpgen] to begin the proof. *)

Tactic Notation "xwp" :=
  intros; applys xwp_lemma; [ reflexivity | simpl; unfold wpgen_var; simpl ].

(** The proof script becomes much more succint. *)

Module ProofsWithXtactics.
Import ExamplePrograms.

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1))).
Proof using.
  xwp.
  xapp triple_get. intros ? ->.
  xapp triple_add. intros ? ->.
  xapp triple_set. intros ? ->.
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
  xapp triple_ref. intros ? l ->.
  xapp triple_incr. intros ? ->.
  xapp triple_get. intros ? ->.
  xapp triple_free. intros ? ->.
  xval.
  xsimpl. auto.
(* /SOLUTION *)
Qed.

End ProofsWithXtactics.


(* ******************************************************* *)
(** ** Further improvements to the [xapp] tactic. *)

(** 1. The pattern [xapp E. intros ? ->.] appears frequently in the above proofs.
    This pattern is typically useful whenever the specification [E] features
    a postcondition of the form [fun v => \[v = ..]] or of the form
    [fun v => \[v = ..] \* ..].

    It therefore makes sense to introduce a specific variant of [xapp] to
    handle these case. It is called [xapps E]. *)

Tactic Notation "xapps" constr(E) :=
  xapp E; intros ? ->.

(** 2. Providing arguments to [xapp] or [xapps] is tedious. To avoid that
    effort, we can set up the tactics to automatically look up for the
    relevant specification.

    To that end, we instrument [eauto] to exploit a database of already-established
    specification triples. The database is populated, e.g., as follows: *)

Hint Resolve triple_get triple_set triple_ref triple_free triple_add : triple.

(** The argument-free variants [xapp] and [xapps] are then available. *)

Tactic Notation "xapp" :=
  xseq_xlet_if_needed; xstruct_if_needed;
  applys xapp_lemma; [ solve [eauto with triple] | xsimpl | xpull ].

Tactic Notation "xapps" :=
  xapp; intros ? ->.


(* ******************************************************* *)
(** ** Demo of a practical proof using x-tactics. *)

Module ProofsWithAdvancedXtactics.
Import ExamplePrograms.

(** "THE_DEMO" begins here. *)

(** The proof script for the verification of [incr] using the
    tactic [xapps] with implicit argument. *)

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1))).
Proof using.
  xwp. xapps. xapps. xapps. xsimpl~.
 Qed.

(* Proof details:
    xwp.
    xapps triple_get.
    xapps triple_add.
    xapps triple_set.
    xsimpl~.
  *)


(** In order to enable automatically exploiting the specification
    of [triple] in the verification of [mysucc], which includes a
    function call to [triple], we add it to the hint database. *)

Hint Resolve triple_incr : triple.

(* EX2! (triple_mysucc_with_xapps) *)
(** Using the improved x-tactics, verify the proof of [mysucc]. *)

Lemma triple_mysucc_with_xapps : forall (n:int),
  triple (trm_app mysucc n)
    \[]
    (fun v => \[v = n+1]).
Proof using.
(* SOLUTION *)
  xwp. xapp ;=> ? l ->. xapps. xapps. xapps. xval. xsimpl~.
(* /SOLUTION *)
Qed.

(** In summary, thanks to [wpgen] and its associated x-tactics,
    we are able to verify concrete programs in Separation Logic
    with concise proof scripts. *)

End ProofsWithAdvancedXtactics.


(* ####################################################### *)
(** * Bonus contents (optional reading) *)

(* ******************************************************* *)
(** ** Tactics [xconseq] and [xframe] *)

(** The tactic [xconseq] enables weakening the current postcondition.
    The syntax [xconseq] and [conseq Q] are available.
    The tactic is implemented by applying the lemma [xconseq_lemma],
    stated below. *)

(* EX1? (xconseq_lemma) *)
(** Prove the [xconseq_lemma]. *)

Lemma xconseq_lemma : forall Q1 Q2 H F,
  H ==> mkstruct F Q1 ->
  Q1 ===> Q2 ->
  H ==> mkstruct F Q2.
Proof using.
(* SOLUTION *)
  introv M WQ. xchange M. applys mkstruct_conseq WQ.
(* /SOLUTION *)
Qed.

Tactic Notation "xconseq" :=
  applys xconseq_lemma.

Tactic Notation "xconseq" constr(Q) :=
  applys xconseq_lemma Q.

(* LATER: add an example use case for xconseq *)


(** The tactic [xframe] enables applying the frame rule on a formula
    produced by [wpgen]. The syntax [xframe H] is used to specify
    the heap predicate to keep, and the syntax [xframe - H] is used to specify
    the heap predicate to frame out---everything else is kept. *)

(* EX2? (xframe_lemma) *)
(** Prove the [xframe_lemma]. *)

Lemma xframe_lemma : forall H1 H2 H Q Q1 F,
  H ==> H1 \* H2 ->
  H1 ==> mkstruct F Q1 ->
  Q1 \*+ H2 ===> Q ->
  H ==> mkstruct F Q.
Proof using.
(* SOLUTION *)
  introv WH M WQ. xchange WH. xchange M.
  lets R: mkstruct_frame F H2 Q1. xchange R.
  applys mkstruct_conseq WQ.
(* /SOLUTION *)
Qed.

Tactic Notation "xframe" constr(H) :=
  applys xframe_lemma H; [ xsimpl | | ].

Tactic Notation "xframe" "-" constr(H) :=
  applys xframe_lemma __ H; [ xsimpl | | ].

(** Let's illustrate the use of [xframe] on an example. *)

Module ProofsWithStructuralXtactics.
Import ExamplePrograms.

Lemma triple_incr_frame : forall (p q:loc) (n m:int),
  triple (trm_app incr p)
    (p ~~~> n \* q ~~~> m)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1)) \* (q ~~~> m)).
Proof using.
  xwp.
  (* Instead of calling [xapp], let's put aside [q ~~~> m] and focus on [p ~~~> n]. *)
  xframe (p ~~~> n). (* equivalent to [xframe - (q ~~~> m)]. *)
  (* Then we can work in a smaller state that mentions only [p ~~~> n]. *)
  xapps. xapps. xapps.
  (* Finally we check the check that the current state augmented with
     the framed predicate [q ~~~> m] matches with the claimed postcondition. *)
  xsimpl~.
Qed.

End ProofsWithStructuralXtactics.


(* ******************************************************* *)
(** ** Soundness proof for [wpgen] *)

Module WPgenSound.

(* ------------------------------------------------------- *)
(** *** Introduction of the predicate [formula_sound] *)

(** The soundness theorem that we aim to establish for [wpgen] is:
[[
  Parameter wpgen_sound : forall E t Q,
    wpgen E t Q ==> wp (isubst E t) Q.
]]
*)

(** Before we enter the details of the proof, let us reformulate the
    soundness statement of the soundness theorem in a way that will
    make proof obligations and induction hypotheses easier to read.
    To that end, we introduce the predicate [formula_sound t F],
    which asserts that [F] is a weakest-precondition style formula
    that entails [wp t]. Formally: *)

Definition formula_sound (t:trm) (F:formula) : Prop :=
  forall Q, F Q ==> wp t Q.

(** Using [formula_sound], the soundness theorem reformulates as: *)

Parameter wpgen_sound' : forall E t,
  formula_sound (isubst E t) (wpgen E t).


(* ------------------------------------------------------- *)
(** *** Soundness for the case of sequences *)

(** Let us forget about the existence of [mkstruct] for a minute,
    that is, pretend that [wpgen] is defined without [mkstruct].

    In that setting, [wpgen E (trm_seq t1 t2)] evaluates to
    [wpgen_seq (wpgen E t1) (wpgen E t2)].

    Recall the definition of [wpgen_seq]:

[[
  Definition wpgen_seq (F1 F2:formula) : formula := fun Q =>
    F1 (fun v => F2 Q).
]]

*)

(** Consider the soundness theorem [wpgen_sound] and in the
    particular case where [t] is of the form [trm_seq t1 t2].
    The corresponding statement is: *)

Parameter wpgen_sound_seq : forall E t1 t2,
  formula_sound (isubst E (trm_seq t1 t2)) (wpgen E (trm_seq t1 t2)).

(** In that statement:

    - [wpgen E (trm_seq t1 t2)] evaluates to
      [wpgen_seq (wpgen E t1) (wpgen E t2)].
    - [isubst E (trm_seq t1 t2)] evaluates to
      [trm_seq (isubst E t1) (isubst E t2)].

    Moreover, by induction hypothesis, we will be able to assume
    the soundness result to already hold for the subterms [t1] and [t2].

    Thus, to establish the soundness of [wpgen] for sequences, we
    have to prove the following result: *)

Parameter wpgen_sound_seq' : forall E t1 t2,
  formula_sound (isubst E t1) (wpgen E t1) ->
  formula_sound (isubst E t2) (wpgen E t2) ->
  formula_sound (trm_seq (isubst E t1) (isubst E t2))
                (wpgen_seq (wpgen E t1) (wpgen E t2)).

(** In the above, let us abstract [isubst E t1] as [t1'] and
    [wpgen t1] as [F1], and similarly [isubst E t2] as [t2']
    and [wpgen t2] as [F2]. We obtain: *)

Lemma wpgen_seq_sound : forall t1' t2' F1 F2,
  formula_sound t1' F1 ->
  formula_sound t2' F2 ->
  formula_sound (trm_seq t1' t2') (wpgen_seq F1 F2).

(** This statement captures the essence of the correctness of
    the definition of [wpgen_seq]. Let's prove it. *)

Proof using.
  introv S1 S2.
  (* Reveal the soundness statement *)
  unfolds formula_sound.
  (* Consider a postcondition [Q] *)
  intros Q.
  (* Reveal [wpgen_seq F1 F2], which is defined as [F1 (fun v => F2 Q)]. *)
  unfolds wpgen_seq.
  (* By transitivity of entailement *)
  applys himpl_trans.
  (* Apply the soundness result for [wp] on sequences:
     [wp t1 (fun v => wp t2 Q) ==> wp (trm_seq t1 t2) Q]. *)
  2:{ applys wp_seq. }
  (* Exploit the induction hypotheses to conclude *)
  { applys himpl_trans.
    { applys S1. }
    { applys wp_conseq. intros v. applys S2. } }
Qed.


(* ------------------------------------------------------- *)
(** *** Soundness of [wpgen] for the other term constructs *)

Lemma wpgen_val_sound : forall v,
  formula_sound (trm_val v) (wpgen_val v).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_val. Qed.

Lemma wpgen_fun_val_sound : forall x t,
  formula_sound (trm_fun x t) (wpgen_val (val_fun x t)).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_fun. Qed.

Lemma wpgen_fix_val_sound : forall f x t,
  formula_sound (trm_fix f x t) (wpgen_val (val_fix f x t)).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_fix. Qed.

Lemma wpgen_let_sound : forall F1 F2of x t1 t2,
  formula_sound t1 F1 ->
  (forall v, formula_sound (subst x v t2) (F2of v)) ->
  formula_sound (trm_let x t1 t2) (wpgen_let F1 F2of).
Proof using.
  introv S1 S2. intros Q. unfolds wpgen_let. applys himpl_trans wp_let.
  applys himpl_trans S1. applys wp_conseq. intros v. applys S2.
Qed.

Lemma wpgen_if_sound : forall F1 F2 t0 t1 t2,
  formula_sound t1 F1 ->
  formula_sound t2 F2 ->
  formula_sound (trm_if t0 t1 t2) (wpgen_if t0 F1 F2).
Proof using.
  introv S1 S2. intros Q. unfold wpgen_if. xpull. intros b ->.
  applys himpl_trans wp_if. case_if. { applys S1. } { applys S2. }
Qed.

Lemma wpgen_fail_sound : forall t,
  formula_sound t wpgen_fail.
Proof using. intros. intros Q. unfold wpgen_fail. xpull. Qed.

(** Remark: the formula [wpgen_fail] is a sound formula not just
    for a variable [trm_var x], but in fact for any term [t].
    Indeed, if [\[False] ==> wp t Q] is always true. *)

Lemma wp_sound : forall t,
  formula_sound t (wp t).
Proof using. intros. intros Q. applys himpl_refl. Qed.

(** Remark: the formula [wp t] is a sound formula for a term [t],
    not just when [t] is an application, but for any term [t]. *)


(* ------------------------------------------------------- *)
(** *** Soundness of [mkstruct] *)

(** To carry out the soundness proof, we also need to justify
    that the addition of [mkstruct] to the head of every call to
    [wpgen] preserves the entailment [wpgen t Q ==> wp t Q].

    Consider a term [t]. The result of [wpgen t] takes the form
    [mkstruct F], where [F] denotes the main pattern matching
    on [t] that occurs in the definition of [wpgen].

    Our goal is to show that if the formula [F] is a valid
    weakest precondition for [t], then so is [mkstruct F].
    Formally: *)

Lemma mkstruct_sound : forall t F,
  formula_sound t F ->
  formula_sound t (mkstruct F).
Proof using.
  introv M. unfolds formula_sound.
  (* Consider a postcondition [Q] *)
  intros Q.
  (* Reveal the definition of [mkstruct] *)
  unfolds mkstruct.
  (* Extract the [Q'] quantified in the definition of [mkstruct] *)
  xsimpl ;=> Q' H N.
  (* Instantiate the assumption on [F] with that [Q'], and exploit it. *)
  lets M': M Q'. xchange M'.
  (* Conclude using the structural rules for [wp]. *)
  applys wp_conseq_frame. applys N.
Qed.


(* ------------------------------------------------------- *)
(** *** Lemmas capturing properties of iterated substitutions *)

(** In the proof of soundness for [wpgen], we need to exploit two
    basic properties of the iterated substitution function [isubst].

    The first property asserts that the substitution for the empty
    context is the identity. This result is needed to cleanly state
    the final statement of the soundness theorem. *)

Parameter isubst_nil : forall t,
  isubst nil t = t.

(** The second property asserts that the substitution for a context
    [(x,v)::E] is the same as the substitution for the context [rem x E]
    followed with the substitution of [x] by [v] using the basic
    substitution function [subst]. This second property is needed to
    handle the case of let-bindings. *)

Parameter isubst_rem : forall x v E t,
  isubst ((x,v)::E) t = subst x v (isubst (rem x E) t).

(** The proof of these lemmas is technical and of little interest.
    They can be found in appendix near the end of this chapter. *)


(* ------------------------------------------------------- *)
(** *** Main induction for the soundness proof of [wpgen] *)

(** We prove the soundness of [wpgen E t] by structural induction on [t].

    As explaiend previously, the soundness lemma is stated with help
    of the predicate [formula_sound], in the form:
    [formula_sound (isubst E t) (wpgen t)].

    For each term construct, the proof case consists of two steps:

    - first, invoke the lemma [mkstruct_sound] to justify soundness
      of the leading [mkstruct] produced by [wpgen],
    - second, invoke the the soundness lemma specific to that term
      construct, e.g. [wpgen_seq_sound] for sequences.

*)

Lemma wpgen_sound_induct : forall E t,
  formula_sound (isubst E t) (wpgen E t).
Proof using.
  intros. gen E. induction t; intros; simpl;
   applys mkstruct_sound.
  { applys wpgen_val_sound. }
  { rename v into x. unfold wpgen_var. case_eq (lookup x E).
    { intros v EQ. applys wpgen_val_sound. }
    { intros N. applys wpgen_fail_sound. } }
  { applys wpgen_fun_val_sound. }
  { applys wpgen_fix_val_sound. }
  { applys wp_sound. }
  { applys wpgen_seq_sound. { applys IHt1. } { applys IHt2. } }
  { rename v into x. applys wpgen_let_sound.
    { applys IHt1. }
    { intros v. rewrite <- isubst_rem. applys IHt2. } }
  { applys wpgen_if_sound. { applys IHt2. } { applys IHt3. } }
Qed.


(* ------------------------------------------------------- *)
(** *** Statement of soundness of [wpgen] for closed terms *)

(** For a closed term [t], the context [E] is instantiated as [nil],
    and [isubst nil t] simplifies to [t]. We obtain the statement: *)

Lemma wpgen_sound : forall t Q,
  wpgen nil t Q ==> wp t Q.
Proof using.
  introv M. lets N: (wpgen_sound nil t). rewrite isubst_nil in N. applys* N.
Qed.

(** A corollary can be derived for deriving a triple of the
    form [triple t H Q] from [wpgen nil t]. *)

Lemma triple_of_wpgen : forall t H Q,
  H ==> wpgen nil t Q ->
  triple t H Q.
Proof using. introv M. rewrite wp_equiv. xchange M. applys wpgen_sound. Qed.

(** The lemma [xwp_lemma], used by the tactic [xwp], is a variant of
    [wpgen_of_triple] specialized for establishing a triple for a
    function application. In essence, this lemma, stated below,
    reformulates the reasoning rule [triple_app_fun] with a premise
    of the form [wpgen E t1], where [t1] denotes the body of the function. *)

Lemma xwp_lemma : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
  introv M1 M2. applys triple_app_fun M1.
  asserts_rewrite (subst x v2 t1 = isubst ((x,v2)::nil) t1).
  { rewrite isubst_rem. rewrite~ isubst_nil. }
  rewrite wp_equiv. xchange M2. applys wpgen_sound_induct.
Qed.

End WPgenSound.


(* ******************************************************* *)
(** ** Guessing the definition of [mkstruct] *)

Module MkstructGuess.

(** How could we have possibly guessed the definition of [mkstruct]?

    This predicate should satisfy the three properties:
    [mkstruct_frame], [mkstruct_conseq] and [mkstruct_erase].

    Recall the property [mkstruct_conseq]: *)

Parameter mkstruct_conseq : forall F Q1 Q2,
  Q1 ===> Q2 ->
  mkstruct F Q1 ==> mkstruct F Q2.

(** Let us reformulate this as an introduction rule for [mkstruct]. *)

Parameter mkstruct_conseq' : forall F Q2,
  \exists Q1, \[Q1 ===> Q2] \* (mkstruct F Q1) ==> mkstruct F Q2.

(** From there, it would tempting to define [mkstruct F Q2] as
    [\exists Q1, \[Q1 ===> Q2] \* (mkstruct F Q1)].
    Yet, this definition of [mkstruct] is circular: it refers to itself.
    Let's overcome the circularity in a radical manner, by getting rid
    of the occurence of [mkstruct] inside its definition.

    Doing so, it turns out, leads to a definition that does satisfy
    the property [mkstruct_conseq] as required. *)

Definition mkstruct1 (F:formula) : formula :=
  fun (Q2:val->hprop) => \exists Q1, F Q1 \* \[Q1 ===> Q2].

Lemma mkstruct1_conseq : forall F Q1 Q2,
  Q1 ===> Q2 ->
  mkstruct1 F Q1 ==> mkstruct1 F Q2.
Proof using. introv M. unfolds mkstruct1. xsimpl. intros Q' N. xchange* N. Qed.

(** The second task is to extend the definition in order to also support
    not just [mkstruct_conseq], but also [mkstruct_frame]. *)

Parameter mkstruct_frame : forall F H Q,
  (mkstruct F Q) \* H ==> mkstruct F (Q \*+ H).

(** Taking inspiration from the rule [wp_conseq_frame] which combines
    the frame rule and the rule of consequence into a single rule, we
    can state a property of [mkstruct] that captures at once the two
    required properties. *)

Parameter mkstruct_conseq_frame : forall F Q1 Q2 H,
  Q1 \*+ H ===> Q2 ->
  H \* (mkstruct F Q1) ==> mkstruct F (Q2 \*+ H).

(** Again, let us reformulate this as an introduction rule for [mkstruct]. *)

Parameter mkstruct_conseq'' : forall F Q2,
  \exists Q1 H, \[Q1 \*+ H ===> Q2] \* H \* (mkstruct F Q1) ==> mkstruct F Q2.

(** Again, eliminating the reference to [mkstruct] on the left-hand side of
    the entailment suggests the following definition. *)

Definition mkstruct (F:formula) : formula :=
  fun (Q2:val->hprop) => \exists Q1 H, F Q1 \* H \* \[Q1 \*+ H ===> Q2].

(** As we have proved earlier in this chapter, this definition indeed satisfies
    all the required properties. In particular, recall [mkstruct_erase]: *)

Parameter mkstruct_erase : forall (F:formula) Q,
  F Q ==> mkstruct F Q.

(** To prove it, instantiate [Q2] from the definition of [mkstruct] as [Q],
    and [H] as the empty heap predicate. *)

End MkstructGuess.


(* ******************************************************* *)
(** ** Proof of properties of iterated substitution *)

Module IsubstProp.

Open Scope liblist_scope.

Implicit Types E : ctx.

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

Lemma isubst_nil : forall t,
  isubst nil t = t.
Proof using.
  intros t. induction t; simpl; fequals.
Qed.

(** The second lemma is much more involved to prove.

    We introduce the notion of "two equivalent contexts"
    [E1] and [E2], and argue that substitution for two
    equivalent contexts yields the same result.

    We then introduce the notion of "contexts with disjoint
    domains", and argue that if [E1] and [E2] are disjoint then
    [isubst (E1 ++ E2) t = isubst E1 (isubst E2 t)]. *)

(** Before we start, we describe the tactic [case_var], which
    helps with the case_analyses on variable equalities,
    and we prove an auxiliary lemma that describes the
    result of a lookup on a context from which a binding
    has been removed. It is defined in file [Var.v] as:
[[
    Tactic Notation "case_var" :=
      repeat rewrite var_eq_spec in *; repeat case_if.
]]
*)

(** On key auxiliary lemma relates [subst] and [isubst]. *)

Lemma subst_eq_isubst_one : forall x v t,
  subst x v t = isubst ((x,v)::nil) t.
Proof using.
  intros. induction t; simpl.
  { fequals. }
  { case_var~. }
  { fequals. case_var~. { rewrite~ isubst_nil. } }
  { fequals. case_var; try case_var; simpl; try case_var; try rewrite isubst_nil; auto. }
  { fequals*. }
  { fequals*. }
  { fequals*. case_var~. { rewrite~ isubst_nil. } }
  { fequals*. }
Qed.

(** A lemma about the lookup in a removal. *)

Lemma lookup_rem : forall x y E,
  lookup x (rem y E) = if var_eq x y then None else lookup x E.
Proof using.
  intros. induction E as [|(z,v) E'].
  { simpl. case_var~. }
  { simpl. case_var~; simpl; case_var~. }
Qed.

(** A lemma about the removal over an append. *)

Lemma rem_app : forall x E1 E2,
  rem x (E1 ++ E2) = rem x E1 ++ rem x E2.
Proof using.
  intros. induction E1 as [|(y,w) E1']; rew_list; simpl. { auto. }
  { case_var~. { rew_list. fequals. } }
Qed.

(** The definition of equivalent contexts. *)

Definition ctx_equiv E1 E2 :=
  forall x, lookup x E1 = lookup x E2.

(** The fact that removal preserves equivalence. *)

Lemma ctx_equiv_rem : forall x E1 E2,
  ctx_equiv E1 E2 ->
  ctx_equiv (rem x E1) (rem x E2).
Proof using.
  introv M. unfolds ctx_equiv. intros y.
  do 2 rewrite lookup_rem. case_var~.
Qed.

(** The fact that substitution for equivalent contexts
    yields equal results. *)

Lemma isubst_ctx_equiv : forall t E1 E2,
  ctx_equiv E1 E2 ->
  isubst E1 t = isubst E2 t.
Proof using.
  hint ctx_equiv_rem.
  intros t. induction t; introv EQ; simpl; fequals~.
  { rewrite EQ. auto. }
Qed.

(** The definition of disjoint contexts. *)

Definition ctx_disjoint E1 E2 :=
  forall x v1 v2, lookup x E1 = Some v1 -> lookup x E2 = Some v2 -> False.

(** Removal preserves disjointness. *)

Lemma ctx_disjoint_rem : forall x E1 E2,
  ctx_disjoint E1 E2 ->
  ctx_disjoint (rem x E1) (rem x E2).
Proof using.
  introv D. intros y v1 v2 K1 K2. rewrite lookup_rem in *.
  case_var~. applys* D K1 K2.
Qed.

(** Lookup in the concatenation of two disjoint contexts *)

Lemma lookup_app : forall x E1 E2,
  lookup x (E1 ++ E2) = match lookup x E1 with
                        | None => lookup x E2
                        | Some v => Some v
                        end.
Proof using.
  introv. induction E1 as [|(y,w) E1']; rew_list; simpl; intros.
  { auto. }
  { case_var~. }
Qed.

(** The key induction shows that [isubst] distributes over
    context concatenation. *)

Lemma isubst_app : forall t E1 E2,
  isubst (E1 ++ E2) t = isubst E2 (isubst E1 t).
Proof using.
  hint ctx_disjoint_rem.
  intros t. induction t; simpl; intros.
  { fequals. }
  { rename v into x. rewrite~ lookup_app.
    case_eq (lookup x E1); introv K1; case_eq (lookup x E2); introv K2; auto.
    { simpl. rewrite~ K2. }
    { simpl. rewrite~ K2. } }
  { fequals. rewrite* rem_app. }
  { fequals. do 2 rewrite* rem_app. }
  { fequals*. }
  { fequals*. }
  { fequals*. { rewrite* rem_app. } }
  { fequals*. }
Qed.

(** The next lemma asserts that the concatenation order is irrelevant
    in a substitution if the contexts have disjoint domains. *)

Lemma isubst_app_swap : forall t E1 E2,
  ctx_disjoint E1 E2 ->
  isubst (E1 ++ E2) t = isubst (E2 ++ E1) t.
Proof using.
  introv D. applys isubst_ctx_equiv. applys~ ctx_disjoint_equiv_app.
Qed.

(** We are ready to derive the desired property of [isubst]. *)

Lemma isubst_rem : forall x v E t,
  isubst ((x, v)::E) t = subst x v (isubst (rem x E) t).
Proof using.
  intros. rewrite subst_eq_isubst_one. rewrite <- isubst_app.
  rewrite isubst_app_swap.
  { applys isubst_ctx_equiv. intros y. rew_list. simpl. case_var~.
    { rewrite lookup_rem. case_var~. } }
  { intros y v1 v2 K1 K2. simpls. case_var.
    { subst. rewrite lookup_rem in K1. case_var~. } }
Qed.

End IsubstProp.

