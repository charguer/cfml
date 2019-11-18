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
    
    Contrary to [wp t Q], with [wpgen t Q] one can carry out practical 
    reasoning on a concrete term [t]:

    - without having to manually invoke the reasoning rules such as [wp_seq],
    - without having to manipulate the concrete syntax (AST) of the term [t],
    - without having to manually simplify substitutions of the form [subst x v t1].

    The matter of the present chapter is to show:

    - how to define [wpgen t Q] as a recursive function that computes in Coq,
    - how to integrate support for the frame rule in this recursive definition,
    - how to carry out practical proofs using [wpgen t Q].

    A bonus section explains how to establish the soundness theorem for [wpgen].
*)


(* ******************************************************* *)
(** ** Definition of [wpgen] for term rules *)

(** [wpgen] computes a heap predicate that has the same meaning as [wp].
    In essence, [wpgen] takes the form of a recursive function that,
    like [wp], expects a term [t] and a postcondition [Q], and produces
    a heap predicate. The function is recursively defined and its result
    is guided by the structure of the term [t].
    
    Thus, in essence, the definition of [wpgen] admits the following shape:

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

    Our first goal is to fill in the dots for each of the term constructors.

    The intention that guides us for filling the dot is the soundness theorem
    for [wpgen], which takes the following form:
    
[[
    wpgen t Q ==> wp t Q
]]

    This entailement asserts in particular that if we are able to establish 
    [H ==> wpgen t Q], then we have proved [H ==> wp t Q], and thus also
    proved [triple t H Q].

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

(** The soundness theorem requires us to have:
    [wpgen (trm_val v) Q ==> wp (trm_val v) Q].
    To satisfy this entailement, it suffices to define [wpgen (trm_val v) Q] 
    as [Q v]. 

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
    For this reason, we define [wpgen (trm_seq t1 t2) Q] as
    [wpgen t1 (fun r => wpgen t2 Q)].

[[
    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
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

(** We thus fill in the dots as follows:

[[
    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_let x t1 t2 => wpgen t1 (fun v => wpgen (subst x v t2) Q)
      ...
]]

    One important observation to make at this point is that the 
    function [wpgen] is no longer structurally recursive. 
    While the first recursive call to [wpgen] is invoked on [t1], which
    is a strict subterm of [t], the second call is invoked on [subst x v t2],
    which is not a strict subterm of [t].

    We'll come back later to the issue later and explain how it is possible:
    - either to convince Coq that the function [wpgen] nevertheless terminates,
    - or to circumvent the problem by adding as argument to [wpgen] a substitution 
      context that avoids computing substitution before making recursive calls.

*)

(* ------------------------------------------------------- *)
(** *** Definition of [wpgen] for variables *)

(** There are no reasoning rule that concludes [H ==> wp (trm_var x) Q]
    of [triple (trm_var x) H Q]. Indeed, [trm_var x] is a stuck term.

    While a term may feature variables, all these variables should have
    been substituted away before we reach them, through substitutions
    such as the one described above in the treatment of let-bindings.
    If a variable is reached, it means that it is a dandling free 
    variable, and that the program is broken. 
    
    Although there are no rules to introduce [wp (trm_var x) Q], we 
    nevertheless need to provide some meaningful definition for 
    [wpgen (trm_var x) Q]. This definition should capture the fact
    that this case must not happen. The predicate [\[False]] captures
    this well.

[[
    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_var x => \[False]
      ...
]]

*)

(** Remark: this definition suggests that, in fact, we could technically
    have stated a Separation Logic rule free variables, using [False]
    as a premise. *)

Lemma triple_var : forall x H Q,
  False ->
  triple (trm_var x) H Q.
Proof using. intros. false. Qed.

(** Likewise, a [wp] reasoning rule with [\[False]] as precondition
    would be technically correct, albeit totally useless. *)

Lemma wp_var : forall x Q,
  \[False] ==> wp (trm_var x) Q.
Proof using. intros. intros h Hh. destruct (hpure_inv Hh). false. Qed.


(* ------------------------------------------------------- *)
(** *** Definition of [wpgen] for function applications *)

(** Consider an application in A-normal form, that is,  
    an application of the form [trm_app v1 v2].
    
    We have [wp]-style rules to reason about the application of
    a known function, e.g. [trm_app (val_fun x t1) v2].
    However, if [v1] is an abstrat value (e.g., a Coq variable
    of type [var]), we have no specific reasoning rule at hand.

    Thus, we will simply define [wpgen (trm_app v1 v2) Q] as
    [wp (trm_app v1 v2) Q]. In other words, we fall back to the
    semantic definition of [wp].

[[
    Fixpoint wpgen (t:trm) (Q:val->hprop) : hprop :=
      match t with
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
    Then by exploiting the equivalence with triples, we get:
[[
    triple (trm_app v1 v2) H Q
]]
    which can be proved by invoking a specification triple for 
    the function [v1].

    In other words, we falling back to the semantics definition
    when reaching a function application, we allow the user to choose 
    which specification lemma to exploit for reasoning about this 
    particular function application. Remark: with some degree of tactic 
    automation, we will avoid the user having to explicitly provide
    the name of the specification lemma, as this would be cumbersome.

*)

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

    To handle the problem, we pattern match [t] as [trm_if t0 t1 t2],
    and define its [wpgen] as a heap predicate that requires the 
    existence of a boolean [b] such that [t0 = trm_val (val_bool b)]. 
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


    This definition accounts for the reasoning rules for terms.

    However, this definition lacks support for conveniently exploiting
    the structural rules of the logic. We are going to fix this next.
*)


(* ******************************************************* *)
(** ** Extension of [wpgen] to handle structural rules *)

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


(* ------------------------------------------------------- *)
(** *** Properties and realization of [mkstruct] *)

(** Before we state the properties that [mkstruct] should satisfy,
    let us first figure out the type of [mkstruct].
    
    Let us call [formula] the type of [wpgen t], that is, the type
    [(val->hprop)->hprop]. Then, because [mkstruct] appears between
    the prototype and the prior body of [wpgen], it must have type
    [formula->formula]. *)

Definition formula : Type := (val->hprop)->hprop.

Module MkstructProp.

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


(* ******************************************************* *)
(** ** Computating with [wpgen] *)

(* ------------------------------------------------------- *)
(** *** A structurally recursive version of [wpgen] *)

(** Consider the current proposal for [wpgen].

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

    This definition is not accepted by Coq because, as mentioned earlier,
    it is not structurally recursive, due to the recursive call 
    [wpgen (subst x v t2)]. 
    
    The problem is associated with the substitution. The fix that we
    consider next consists in delaying the substitutions until the
    end of the recursive calls.
    
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

----TODO: essayer  lookup swap with fun Q.
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

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  mkstruct (match t with
  | trm_val v => fun Q => Q v
  | trm_fun x t1 => fun Q => Q (val_fun x (isubst (rem x E) t1))
  | trm_fix f x t1 => fun Q => Q (val_fix f x (isubst (rem x (rem f E)) t1))
  | trm_seq t1 t2 => fun Q => wpgen E t1 (fun v => wpgen E t2 Q)
  | trm_let x t1 t2 => fun Q => wpgen E t1 (fun v => wpgen ((x,v)::E) t2 Q)
  | trm_var x => fun Q =>
       match lookup x E with
       | Some v => Q v
       | None => \[False]
       end
  | trm_app v1 v2 => fun Q => wp (isubst E t) Q
  | trm_if t0 t1 t2 => fun Q => 
      \exists (b:bool), \[t0 = trm_val (val_bool b)]
        \* (if b then (wpgen E t1) Q else (wpgen E t2) Q)
  end).

(** Compared with the presentation using the form [wpgen t], the 
    new presentation using the form [wpgen E t] has the main benefits
    that it is structurally recursive, thus easy to define in Coq.
    Moreover, it is algorithmically more efficient in general, because 
    it performs substitutions easily rather than eagerly. *)

(** Let us state the soundness theorem and its corollary for establishing
    triples for functions. *)

Parameter wpgen_sound : forall E t Q,
   wpgen E t Q ==> wp (isubst E t) Q.

(** This entailement asserts in particular that if we can derive
    [triple t H Q] by proving [H ==> wpgen t Q]. If we exploit
    this result to the case of the application of a function,
    we obtain the lemma shown below. *)

Parameter triple_app_fun_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.

(* -- TODO: missing details *)


(* ******************************************************* *)
(** ** Testing [wpgen] and optimizing the readability of its output *)


(* ------------------------------------------------------- *)
(** *** Executing [wpgen] on a concrete program *)

(** Using [triple_app_fun_from_wpgen], we can demonstrate the
    computation of a [wpgen] on a practical program, for example [incr]. *)

Import NotationForVariables.
Open Scope val_scope.
Open Scope trm_scope.
Implicit Types n : int.

(** Recall the definition of [incr]. *)

Definition incr :=
  VFun 'p :=
    Let 'n := '! 'p in
    Let 'm := 'n '+ 1 in
   'p ':= 'm.

(** Recall the specification of [incr]. *)

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

    Observe the nested calls to [mkstruct].

    Observe the invokations of [wp] on the application of primitive
    operations.

    Observe that the goal is nevertheless somewhat hard to relate
    to the original program... 

    In what follows, we explain how to remedy the situation. *)

End WpgenExec1.


(* ------------------------------------------------------- *)
(** *** Improving readability using intermediate definitions *)

Module WpgenExec2.

(** We reformulate the definition of [wpgen E t] by introducing
    intermediate definitions, one per term construct. For each
    of these intermediate definition, we introduce an ad-hoc 
    notation that enables displaying the [wpgen] of a term [t] in
    a way that resembles the source code of [t]. *)

(** Consider for example the case of a sequence. The definition
    of [wpgen E (trm_seq t1 t2)] is [fun Q => wpgen E t1 (fun v => wpgen E t2 Q)].
    Let [F1] and [F2] denote the results of the recursive calls,
    [wpgen E t1] and [wpgen E t2], respectively.
    Then [wpgen E (trm_seq t1 t2)] reformulates as [fun Q => F1 (fun v => F2 Q)].

    We introduce definition a combinator named [wpgen_seq F1 F2] to capture
    the logic of [fun Q => F1 (fun v => F2 Q)], in such a way that
    [wgpen E (trm_seq t1 t2)] can be defined as [wp_seq (wpgen E t1) (wpgen E t2)]. *)

Definition wpgen_seq (F1 F2:formula) : formula := fun Q =>
  F1 (fun v => F2 Q).

(** The definition of [wpgen E t] may then be rewritten as follows:

[[
  Fixpoint wpgen (E:ctx) (t:trm) : formula :=
    mkstruct (match t with
    ...
    | trm_seq t1 t2 => wpgen_seq (wpgen E t1) (wpgen E t2 Q)
    ... 
    end).
]]
*)

(** Next, we introduce a piece of notation so as to display any formula 
    of the form [wpgen_seq F1 F2] as [Seq F1 '; F2 ].  *)

Notation "'Seq' F1 '; F2" :=
  ((wpgen_seq F1 F2))
  (at level 68, right associativity,
   format "'[v' 'Seq'  '[' F1 ']'  '';'  '/'  '[' F2 ']' ']'").

(** Thanks to this notation, the [wpgen] of a sequence [t1 '; t2] displays as 
    [Seq F1 '; F2] where [F1] and [F2] denote the [wpgen] of [t1] and [t2],
    respectively.
    
    By generalizing this approach to every term constructs, we obtain the
    property that the [wpgen] of a term [t] displays "pretty much" like
    the source term [t] itself---up to alpha-renaming of local variables. 
    
    Let us assume the other definitions without looking at the details,
    and read again the output of [wpgen] on [incr]. *)


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

(** The new definition of [wpgen] reads as follows *)

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

(** The corresonding pieces of notation are defined next. 
    Details can be skipped. *)

Notation "'Val' v" :=
  ((wpgen_val v))
  (at level 69).

Notation "'`Let' x ':=' F1 'in' F2" :=
  ((wpgen_let F1 (fun x => F2)))
  (at level 69, x ident, right associativity,
  format "'[v' '[' '`Let'  x  ':='  F1  'in' ']'  '/'  '[' F2 ']' ']'").

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

(** We also introduce a tiny shorthand to denote [mkstruct F], writing
    [`F], so that it does not clutter the display. *)

Notation "` F" := (mkstruct F) (at level 10, format "` F").



(* ------------------------------------------------------- *)
(** *** Test of [wpgen] with improved readability. *)

(** Assume again the soundness corollary *)

Parameter triple_app_fun_from_wpgen : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  H ==> wpgen ((x,v2)::nil) t1 Q ->
  triple (trm_app v1 v2) H Q.

(** Consider again the example of [incr]. *)

Import NotationForVariables.
Open Scope val_scope.
Open Scope trm_scope.
Implicit Types n : int.

Definition incr :=
  VFun 'p :=
    Let 'n := '! 'p in
    Let 'm := 'n '+ 1 in
   'p ':= 'm.

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1))).
Proof using.
  intros. applys triple_app_fun_from_wpgen. { reflexivity. }
  simpl. (* Read the goal here... It is of the form [H ==> F Q],
            where [F] vaguely looks like the code of the body of [incr]. *)

  (** Up to proper tabulation, alpha-renaming, and removal of
      parentheses, [F] reads as:
[[ 
  `Let n := `(App val_get p) in
  ``Let m := `(App (val_add n) 1) in
  `App (val_set p) m)
*)
Abort.







(* ******************************************************* *)
(** ** Extension of [wpgen] to handle structural rules *)




Module WpgenOverview.

Parameter wpgen : trm -> formula.

(** The soundness theorem that we aim for establishes that [wpgen] can be used
    to establish a judgment [triple t H Q] by proving [H ==> wpgen t Q].
    In this premise, [wpgen t] can be computed using Coq's [simpl] tactic.
    In the process, tthe expression [wpgen t] gets replace by a logical formula
    that no longer refers to the syntax of the term [t]. *)

Parameter triple_of_wpgen : forall H t Q,
  H ==> wpgen t Q ->
  triple t H Q.



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
(** ** Case of values *)

(*    this suggests the definition of [wpgen_val v Q] as [Q v]. *)


(** Let us check the desired soundness property. *)

Lemma wpgen_val_sound : forall v,
  formula_sound_for (trm_val v) (wpgen_val v).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_val. Qed.


(* ******************************************************* *)
(** ** Case of functions *)

.

(** The value of [wpgen (trm_fun x t) Q] may be computed as
    [wpgen_val (val_fun x t)]. Formally: *)

Lemma wpgen_fun_val_sound : forall x t,
  formula_sound_for (trm_fun x t) (wpgen_val (val_fun x t)).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_fun. Qed.

(** Likewise for recursive functions. *)

Lemma wpgen_fix_val_sound : forall f x t,
  formula_sound_for (trm_fix f x t) (wpgen_val (val_fix f x t)).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_fix. Qed.


(* ******************************************************* *)
(** ** Case of sequences and let-bindings *)

(** Consider a sequence [trm_seq t1 t2]. Recall the rule. *)
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


(** The expression [wpgen (trm_if (val_bool b) t1 t2) Q] should

    This discussion leads us to define [wpgen (trm_if v0 t1 t2)] as
    [wpgen_if v0 F1 F2], where [F1] denotes [wpgen t1] and [F2] denotes
    [wpgen t2] and [wpgen_if] is defined as: *)

(** The soundness proof extracts the information from the hypothesis
    [\exists (b:bool), \[v = val_bool b] ] and concludes using [wp_if]. *)

Lemma wpgen_if_sound : forall F1 F2 v0 t1 t2,
  formula_sound_for t1 F1 ->
  formula_sound_for t2 F2 ->
  formula_sound_for (trm_if v0 t1 t2) (wpgen_if v0 F1 F2).
Proof using.
  introv S1 S2. intros Q. unfold wpgen_if. xpull. intros b ->.
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
Proof using. intros. intros Q. unfold wpgen_fail. xpull. Qed.


(* ******************************************************* *)
(** ** Case of applications *)


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
  introv M. intros Q. unfold mkstruct. xsimpl ;=> Q'.
  lets N: M Q'. xchange N. applys wp_ramified.
Qed.



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

(** In order to establish the soundness of this new definition of [wpgen],
    we need to exploit two basic properties of substitution.
    First, the substitution for the empty context is the identity.
    Second, the substitution for [(x,v)::E] is the same as the
    substitution for [rem x E] followed with a substitution of [x] by [v].
    The proof of these technical lemmas is given in appendix. *)

Parameter isubst_nil : forall t,
  isubst nil t = t.

Parameter isubst_rem : forall x v E t,
  isubst ((x,v)::E) t = subst x v (isubst (rem x E) t).

(** We prove the soundness of [wpgen E t] by structural induction on [t].

    The soundness lemma asserts that [H ==> wpgen t Q] implies
    [triple (isubst E t) H Q]. Equivalently, it can be formulated as:
    [forall t, formula_sound_for (isubst E t) (wpgen t)].

    Appart from the induction that is now structural, the proof script
    is relatively similar to before. Only the treatment of the variable
    case and of the binding traversal differ. *)

Lemma wpgen_sound : forall E t,
  formula_sound_for (isubst E t) (wpgen E t).
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
  { case_eq (isubst E t1); intros; try applys wpgen_fail_sound.
    { applys wpgen_if_sound. { applys IHt2. } { applys IHt3. } } }
Qed.

(** The final result for a closed term asserts that [wpgen nil t]
    computes a weakest precondition for [t], in the sense that
    [H ==> wpgen nil t Q] implies [triple t H Q]. *)

Theorem triple_of_wpgen : forall t H Q,
  H ==> wpgen nil t Q ->
  triple t H Q.
Proof using.
  introv M. rewrite wp_equiv. xchange M.
  lets N: (wpgen_sound nil t). rewrite isubst_nil in N. applys N.
  (* same as: [applys_eq wpgen_sound 1. rewrite~ isubst_nil.] *)
Qed.


(* ####################################################### *)
(** * Practical proofs using [wpgen] *)

Module ExampleProofs.

Import NotationForVariables.
Open Scope val_scope.
Open Scope trm_scope.

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

(** [xapp_lemma] reformulates the ramified frame rule, with a goal
    as a [wp] (which is produced by [wpgen] on an application),
    and a premise as a triple (because triples are used to state
    specification lemmas. Observe that the rule includes an identity
    function called [protect], which is used to prevent [xsimpl]
    from performing too aggressive simplifications. *)

Lemma xapp_lemma : forall t Q1 H1 H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* protect Q) ->
  H ==> wp t Q.
Proof using. introv M W. rewrite <- wp_equiv. applys~ triple_ramified_frame M. Qed.

(** The [xsimpl'] tactic is a variant of [xsimpl] that clears the
    identity tag [protect] upon completion. *)

Tactic Notation "xsimpl'" := xsimpl; unfold protect.

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

Definition mysucc : val :=
  VFun 'n :=
    Let 'r := val_ref 'n in
    incr 'r ';
    Let 'x := '! 'r in
    val_free 'r ';
    'x.

(** Let us specify and prove this function using the x-lemmas. *)

Lemma triple_mysucc_with_xlemmas : forall n,
  triple (trm_app mysucc n)
    \[]
    (fun v => \[v = n+1]).
Proof using.
  intros.
  applys xwp_lemma. { reflexivity. }
  (* Here the [wpgen] function computes. 
     For technical reasons, we need to help it a little bit with the unfolding. *)
  simpl; unfold wpgen_var; simpl. 
  (* Observe how each node begin with [mkstruct].
     Observe how program variables are all eliminated. *)
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
Qed.


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

Tactic Notation "xapp" :=
  xseq_xlet_if_needed; xstruct_if_needed; applys xapp_lemma.

(** [xwp] applys [xwp_lemma], then computes [wpgen] to begin the proof. *)

Tactic Notation "xwp" :=
  intros; applys xwp_lemma; [ reflexivity | simpl; unfold wpgen_var; simpl ].

(** The proof script becomes much more succint. *)

Lemma triple_mysucc_with_xtactics : forall (n:int),
  triple (trm_app mysucc n)
    \[]
    (fun v => \[v = n+1]).
Proof using.
  xwp.
  xapp. { apply triple_ref. } xsimpl' ;=> ? l ->.
  xapp. { apply triple_incr. } xsimpl' ;=> ? ->.
  xapp. { apply triple_get. } xsimpl' ;=> ? ->.
  xapp. { apply triple_free. } xsimpl' ;=> ? ->.
  xval.
  xsimpl. auto.
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
  xwp.
  xapp. { apply triple_get. } xsimpl' ;=> ? ->.
  xapp. { apply triple_add. } xsimpl' ;=> ? ->.
  xapp. { apply triple_set. } xsimpl' ;=> ? ->.
  xsimpl. auto.
(* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Further improvements to the [xapp] tactic. *)

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


(* ******************************************************* *)
(** ** Here is the demo of a practical proof based on x-tactics. *)

(** "THE_DEMO" begins here. *)

(** The proof script for the verification of [incr] looks like this. *)

Lemma triple_incr_with_xapps : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1))).
Proof using.
  xwp.
  xapps triple_get.
  xapps triple_add.
  xapps triple_set.
  xsimpl~.
Qed.

(** The proof script for the verification of [mysucc] is now shorter. *)

Lemma triple_mysucc_with_xapps : forall n,
  triple (trm_app mysucc n)
    \[]
    (fun v => \[v = n+1]).
Proof using.
  xwp.
  xapp triple_ref ;=> ? l ->.
  xapps triple_incr.
  xapps triple_get.
  xapps triple_free.
  xval.
  xsimpl~.
Qed.

(* TODO: add a few exercises here *)

End ExampleProofs.



(* ####################################################### *)
(** * Recursive treatment of local function definitions *)

(** As mentioned in the section on the treatment of function definitions,
    it is possible to recursively invoke [wpgen] on the body of local
    function definitions. We next explain how. *)

Implicit Types vf vx : val.


(* ******************************************************* *)
(** ** WP for non-recursive functions *)

(** The definition of [wpgen] is modified so that [wpgen (trm x t1)]
    is no longer expressed in terms of [t1], but rather in terms of
    the formula produced by recursively computing [wpgen] on [t1].

    Recall that [wpgen (trm_fun x t1) Q] was previously defined as
    [wpgen_val (val_fun x t1) Q], that is, as [Q (val_fun x t1)].
    Here, we'd like to eliminate the reference to the code [t1].
    Let us introduce [vf], a variable that stands for [val_fun x t1],
    and reformulae the heap predicate [wpgen (trm_fun x t1) Q] from
    [Q (val_fun x t1)] to  [\forall vf, \[P vf] \-* (Q vf)], where
    [P vf] denotes some proposition that characterizes the function
    [val_fun x t1] in terms of its weakest precondition.

    The proposition [P vf] characterizes the function [vf] extensionally:
    it provides an hypothesis sufficient for reasoning about an application
    of the function [vf] to any argument [vx]. In other words, it provides
    a [wp] for [trm_app vf vx]. This [wp] is expressed in terms of the
    [wpgen] for [t1]. Concretely, [P vf] is defined as:
    [forall vx Q', (wpgen ((x,v)::E) t1) Q' ==> wp (trm_app vf vx) Q']. *)

(** Similarly to what is done for other constructs, we introduce an auxiliary
    function called [wpgen_fun] to isolate the logic of the definition from
    the recursive call on [t1]. The function of [wpgen] becomes:

[[
  Fixpoint wpgen (E:ctx) (t:trm) : formula :=
    mkstruct match t with
    | ..
    | trm_fun x t1 =>
        wpgen_fun (fun v => wpgen ((x,v)::E) t1)
    | ..
    end
]]

   The definition of [wpgen_fun] appears next. *)

Definition wpgen_fun (Fof:val->formula) : formula := fun Q =>
  \forall vf, \[forall vx Q', Fof vx Q' ==> wp (trm_app vf vx) Q'] \-* Q vf.

(*
   \exists H, H \* \[forall vf, 
                     (forall vx Q', Fof vx Q' ==> wp (trm_app vf vx) Q') ->
                      H ==> Q vf].


  Goal:   H0 ==> wpgen (trm_fun x t)
  unfolds to: 
      H0 ==> \exists H, H \* \[forall vf, 
                     (forall vx Q', Fof vx Q' ==> wp (trm_app vf vx) Q') ->
                      H ==> Q vf].
  simplifies to:

      forall vf, 
      (forall vx H' Q', 
          H' ==> Fof vx Q' ->
          triple (trm_app vf vx) H' Q') ->
      H0 ==> Q vf

  xfun_lemma: 
      S vf => specification for the functoin

      (forall vf, (forall H' Q', H' ==> Fof vx Q' -> triple (trm_app vf vx) H' Q') -> S vf) ->
      (fun r => H0 \* \[S r]) ===> Q ->
      H0 ==> wpgen (trm_fun x t) Q 

*)

(** The soundness lemma for this construct is as follows. *)

Lemma wpgen_fun_sound : forall x t1 Fof,
  (forall vx, formula_sound_for (subst x vx t1) (Fof vx)) ->
  formula_sound_for (trm_fun x t1) (wpgen_fun Fof).
Proof using.
  introv M. intros Q. unfolds wpgen_fun. applys himpl_hforall_l (val_fun x t1).
  xchange hwand_hpure_l_intro.
  { intros. applys himpl_trans_r. { applys* wp_app_fun. } { applys* M. } }
  { applys wp_fun. }
Qed.

(** When we carry out the proof of soundness for the presented of [wpgen]
    suggested above (this proof may be found in file [SLFDirect.v]), we
    obtain the following proof obligation, whose proof exploits [wpgen_fun_sound]
    and exploits the same substitution lemma as for the let-binding case. *)

Lemma wpgen_fun_proof_obligation : forall E x t1,
  (forall E, formula_sound_for (isubst E t1) (wpgen E t1)) ->
  formula_sound_for (trm_fun x (isubst (rem x E) t1)) (wpgen_fun (fun v => wpgen ((x,v)::E) t1)).
Proof using.
  introv IH. applys wpgen_fun_sound.
  { intros vx. rewrite <- isubst_rem. applys IH. }
Qed.


(* ******************************************************* *)
(** ** Generalization to recursive functions *)

(** The discussion above generalizes almost directly to recursive functions.
    To compute [wpgen] of [trm_fix f x t1] in a context [E], the recursive
    call to [wpgen] extends the context [E] with two bindings, one for [f]
    and one for [x].

[[
  Fixpoint wpgen (E:ctx) (t:trm) : formula :=
    mkstruct match t with
    | ..
    | trm_fun x t1 =>
        wpgen_fix (fun vf v => wpgen ((f,vf)::(x,v)::E) t1)
    | ..
    end
]]

   The auxiliary function [wpgen_fix] is defined as follows.
   Observe how [vf] now occurs not only in [trm_app vf vx], but also
   in the formula [Fof vf vx] which describes the behavior of the
   recursive function. *)

Definition wpgen_fix (Fof:val->val->formula) : formula := fun Q =>
  \forall vf, \[forall vx Q', Fof vf vx Q' ==> wp (trm_app vf vx) Q'] \-* Q vf.

(** The corresponding soundness lemma for this construct appears next. *)

Lemma wpgen_fix_sound : forall f x t1 Fof,
  (forall vf vx, formula_sound_for (subst x vx (subst f vf t1)) (Fof vf vx)) ->
  formula_sound_for (trm_fix f x t1) (wpgen_fix Fof).
Proof using.
  introv M. intros Q. unfolds wpgen_fix. applys himpl_hforall_l (val_fix f x t1).
  xchange hwand_hpure_l_intro.
  { intros. applys himpl_trans_r. { applys* wp_app_fix. } { applys* M. } }
  { applys wp_fix. }
Qed.

(** When we carry out the proof of soundness (again, details for this proof
    may be found in file [SLFDirect.v]), we obtain a proof obligation for
    which we need a little generalization of [isubst_rem], called [isubst_rem_2]
    and stated next. (Its proof appears in [SLFDirect.v].) *)

Parameter isubst_rem_2 : forall f x vf vx E t,
  isubst ((f,vf)::(x,vx)::E) t = subst x vx (subst f vf (isubst (rem x (rem f E)) t)).

(** The proof of soundness is otherwise similar to that of non-recursive functions. *)

Lemma wpgen_fix_proof_obligation : forall E f x t1,
  (forall E, formula_sound_for (isubst E t1) (wpgen E t1)) ->
  formula_sound_for (trm_fix f x (isubst (rem x (rem f E)) t1))
                    (wpgen_fix (fun vf vx => wpgen ((f,vf)::(x,vx)::E) t1)).
Proof using.
  introv IH. applys wpgen_fix_sound.
  { intros vf vx. rewrite <- isubst_rem_2. applys IH. }
Qed.


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


(* ####################################################### *)
(** * Appendix: proofs for iterated substitution lemmas *)

Section IsubstProp.

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

Lemma isubst_nil' : forall t,
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

Lemma isubst_rem' : forall x v E t,
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
(** ** Chapter's notes *)

(** The definition of [mkstruct] was suggested by Jacques-Henri Jourdan. *)



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
