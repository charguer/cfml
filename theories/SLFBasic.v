(**

Separation Logic Foundations

Chapter: "Basic".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import Example.
Generalizable Variables A B.

Implicit Types n m : int.
Implicit Types p q : loc.

(** Tweak to make the logic appear linear instead of affine. *)
Ltac xwp_xtriple_handle_gc ::= xwp_xtriple_remove_gc.


(* ####################################################### *)
(** * The chapter in a rush,
      nested with exercises as additional contents *)

(** This chapter gives a quick overview of how to state specifications and
    carry out basic proofs in Separation Logic using CFML tactics.

    In this chapter, we will present:

    - "Heap predicates", which are used to describe memory states in
       Separation Logic.
    - "Specification triples", of the form [TRIPLE _ PRE _ POST _].
      Such specification relate a term, a precondition, and a postcondition.
    - "Verification proof obligations", of the form [PRE _ CODE _ POST _].
      These proof obligations also correspond to specification triples, yet
      they feature the description of the current state as first argument
      to improve readability of proof obligations.
    - "Entailement proof obligations", of the form [_ ==> _] or [_ ===> _].
      Such entailments require proving that a description of a state implies
      another one.
    - Practical verification proofs, using CFML "x-tactics" to demonstrate
      that a given program satisfies a given specification.

    The "heap predicates" used to describe memory states include:
    - [p ~~> n], which describes a memory cell at location [p] with contents [n],
    - [\[]], which describes an empty state,
    - [\[P]], which asserts that a proposition [P] is true (in an empty state),
    - [H1 \* H2], which describes a state made of two disjoint parts: [H1] and [H2],
    - [\exists x, H], which is used to quantify variables in postconditions.

    All these heap predicates admit the type [hprop], which consists of predicate
    over memory states. In other words, [hprop] is defined as [state->Prop].

    The verification proofs are carried out using CFML "x-tactics", as their
    name begins with the letter "x". These tactics include:
    - [xwp] or [xtriple] to being a proof (in case of failure, try [xwp_debug]),
    - [xapp] to reason about an application (in case of failure, try [xapp_debug]),
    - [xval] to reason about a return value,
    - [xsimpl] to simplify or prove entailments ([_ ==> _] or [_ ===> _]). *)

(** In addition to x-tactics, the verification proof scripts exploit standard
    Coq tactics, as well as tactics from the TLC library. The relevant TLC tactics,
    which are described when first use, include:
    - [math], which is a variant of [omega] for proving mathematical goals,
    - [induction_wf], which sets up proofs by well-founded induction,
    - [gen], which is a shorthand for [generalize dependent].

*)


(* ******************************************************* *)
(** ** The increment function *)

(** As first example, consider the function [incr], which increments
    the contents of a mutable cell that stores an integer.
    In OCaml syntax, this function is defined as:

[[
  let incr p =
    p := !p + 1
]]

    The actual CFML tool features a parser able to process OCaml syntax.
    Yet, throughout this course, to avoid dependency on external tools,
    we will input all programs using a custom set of Coq notation for
    describing imperative programs. There is no need to learn to write
    programs in this funny syntax: the source code for all the programs
    involved in this course will be provided.

    Below is the code for [incr], which is a value. In the present framework,
    all values admit the type [val]. The quotes that appear in the source code
    are used to disambiguate the keywords and variables associated with the
    source code, from the corresponding Coq keywords and variables.
    The [VFun] keyword should be read like the [fun] keyword.
*)

Definition incr : val :=
  VFun 'p :=
   'p ':= '! 'p '+ 1.

(** Let [p] be the address in memory of a reference cell, that is,
    the "location" of a reference cell. [p] admits type [loc].

    The heap predicate [p ~~> n] describes a memory state in which the
    contents of the location [p] is the value [n]. In the present
    example [p] denotes an integer value.

    The behavior of the operation [incr p] consists of updating the memory
    state by incrementing the contents of the cell at location [p], so that
    its new contents is [n+1]. Thus, the subsequent memory state is described
    by the heap predicate [p ~~> (n+1)].

    The result value returned by [incr p] is simply the [unit] value.
    There is not much to specify about the result value, beyond the fact
    that it has type [unit].

    The specification of [incr p] can be expressed using a
    "Separation Logic triple" using the custom notation
    [TRIPLE _ PRE _ POST _], whose compontents are explained next. *)


Lemma Triple_incr : forall (p:loc) (n:int),
  TRIPLE (incr p)
    PRE (p ~~> n)
    POST (fun (r:unit) => (p ~~> (n+1))).

(** The components form this specification are as follows:

    - [forall (p:loc) (n:int)] quantifies the argument of the function
      (here, [p]), as well as the "ghost argument" (here, [n]) which is used
      to describe the input state.
    - The keyword [TRIPLE] introduces the expression [incr p], which is the
      function being specified.
    - The keyword [PRE] introduces the "precondition", which describes the
      input state that the function expects, here [p ~~> n].
    - The keyword [POST] introduces the "postcondition", which describes
      both the output value and the output state produced by the call.
      The pattern [fun (r:unit) => _] binds the name [r] to denote the result
      value; here [r] has type unit, reflecting the type of [incr p].
      The expression [p ~~> (n+1)] describes the output state. *)

(** Remark: we need to write [p ~~> (n+1)] instead of [p ~~> n+1], because the
    latter would parse as [(p ~~> n) + 1] and therefore fail to type-check. *)

(** Our next step is to prove the specification lemma [Triple_incr] which
    specifies the behavior of [incr]. We conduct the verification proof
    using CFML tactics.

    The CFML tooling will transform on-the-fly the code so that all
    intermediate expressions are named (that is, by putting the code
    in "A-normal form"). In OCaml syntax, the A-normal could be written:

[[
  let incr p =
    let m =
      let n = !p in
      n + 1 in
    p := m
]]

    The transformation into A-normal form is performed by the tactic [xwp],
    which begins every CFML verification proof script, and sets up a
    verification triple that exploits a mechanism of "characteristic formulae".
    These characteristic formulae can be manipulated using CFML x-tactics
    without knowledge on how they are constructed. (Details of the construction
    are the matter of the chapter [SLFWPgen].)
*)

Proof using.
  xwp.     (* Begin the verification proof. The proof obligation is
              displayed using the custom notation [PRE _ CODE _ POST _].
              The [CODE] part does not look very nice, but one should
              be able to somehow recognize the body of [incr]. Indeed,
              ignorining the details, and after alpha-renaming,
              it looks like:
[[
              Let m :=
                  Let n := App val_get p in
                  App val_add n 1
                  in
               App val_set p m
]]
   *)

 (*  The remaining of the proof performs some form of symbolic
     execution. One should not attempt to read the full proof
     obligation at each step, but instead only look at the current
     state (the [PRE] part, which is [p ~~> n]), and at the first
     line only of the [CODE] part, where one can read the code of
     the next operation to reason about. *)

  xapp.    (* Reason about the the operation [!p] that reads into [p];
              the read operation returns the value [n]. *)
  xapp.    (* Reason about the addition operation [n+1]. *)
  xapp.    (* Reason about the update operation [p := n+1],
              thereby updating the state to [p ~~> (n+1)]. *)
  xsimpl.  (* At this stage, the proof obligation takes the form [_ ==> _],
              which require checking that the final state matches what
              is claimed in the postcondition. *)
Qed.

(** The command below associates the specification lemma [Triple_incr]
    with the function [incr] in a database, so that if we subsequently
    verify a program that features a call to [incr], the [xapp] tactic
    is able to automatically invoke the lemma [Triple_incr]. *)

Hint Extern 1 (Register_Spec incr) => Provide Triple_incr.

(** Remark: there is no need to understand the internal magic of how
    this database of specification is implemented by hacking Coq's
    [Hint] mechanism. *)


(* ******************************************************* *)
(** *** A function with a return value *)

(** As second example, we describe a function that performs simple
    arithmetic computations. The function, whose code appears below,
    expects an integer argument [n], computes [a] as [n+1], then
    computes [b] as [n-1], then returns [a+b]. The function thus
    always returns [2*n].

[[
  let example_let n =
    let a = n + 1 in
    let b = n - 1 in
    a + b
]]
*)

Definition example_let : val :=
  VFun 'n :=
    Let 'a := 'n '+ 1 in
    Let 'b := 'n '- 1 in
    'a '+ 'b.

(** We specify this function using the the triple notation, in the form
    [TRIPLE (example_let n) PRE _ POST (fun (r:int) => _ )], where [r]
    denotes the output value---this time, a value of type [int].

    To denote the fact that the input state is empty, we write [\[]]
    in the precondition, that is, after the [PRE] keyword.

    To denote the fact that the output state is empty, we could use [\[]].
    Yet, if we write [fun (r:int) => \[]] as postcondition, we would have
    said nothing about the output value [r] produced by a call [example_let].
    Instead, we would like to specify that the result [r] is equal to [2*n].
    To that end, we write [fun (r:int) => \[2*n]] after the [POST] keyword. *)

Lemma Triple_example_let : forall (n:int),
  TRIPLE (example_let n)
    PRE \[]
    POST (fun (r:int) => \[r = 2*n]).

(** The verification proof script is very similar to the previous one.
    The x-tactics [xapp] perform symbolic execution of the code.
    Ultimately, we need to check that the expression computed,
    [(n + 1) + (n - 1)] is equal to the specified result, that is, [2*n].
    We exploit the tactics [xsimpl] and [math] to prove this result. *)

Proof using.
  xwp. xapp. xapp. xapp. xsimpl. math.
Qed.

(** In the proof above, we have eargerly substituted [a] with [n+1],
    then substituted [b] with [n-1]. Such eager substitutions generally
    work well for small programs, yet in larger programs doing so can lead
    to exponential blow-ups in the size of the terms being manipulated.
    To avoid such a blow-up, it may be necessary to preserve explicit
    equalities, such as [a = n+1] and [b = n-1], in the proof context.

    In general, it is desirable to let the user control when substitutions
    should or should not be performed. The [xapp] tactic does perfom the
    substitution, whereas its variant [xapp_nosubst] instead introduces an
    explicit equality, as illustrated next. *)

Lemma Triple_example_let_with_nosubst : forall (n:int),
  TRIPLE (example_let n)
    PRE \[]
    POST (fun (r:int) => \[r = 2*n]).
Proof using.
  xwp.
  xapp_nosubst. intros a Ha.  (* introduces [Ha: a = n + 1] *)
  xapp_nosubst. intros b Hb.  (* introduces [Hb: b = n - 1] *)
  xapp_nosubst. intros r Hr.  (* introduces [Hb: r = a + b] *)
  xsimpl. math. (* check that, under these hypotheses, [r = 2 * n]. *)
Qed.

(** Throughout this chapter and the next one, we only consider programs
    that are simple enough that one may use the tactic [xapp] everywhere. *)


(* ******************************************************* *)
(** ** Exercise: function [quadruple] *)

(** Consider the function [quadruple], which expects an integer [n]
    and returns its quadruple, that is, the value [4 * n].

[[
  let quadruple n =
    n + n + n + n
]]
*)

Definition quadruple : val :=
  VFun 'n :=
    Let 'm := 'n '+ 'n in
    'm '+ 'm.

(* EX1! (Triple_quadruple) *)
(** Specify and verify the function [quadruple] to express that
    it returns [4*n].
    Hint: follow the template of [Triple_example_let]. *)

(* SOLUTION *)
Lemma Triple_quadruple : forall (n:int),
  TRIPLE (quadruple n)
    PRE \[]
    POST (fun (r:int) => \[r = 4 * n]).
Proof using.
  xwp. xapp. xapp. xsimpl. math.
Qed.
(* /SOLUTION *)

(** [] *)


(* ******************************************************* *)
(** ** Exercise: function [inplace_double] *)

(** Consider the function [inplace_double], which expects a reference
    on an integer, reads twice in that reference, then updates the
    reference with the sum of the two values that have been read. *)

[[
  let inplace_double p =
    p := !p + !p
]]
*)

Definition inplace_double : val :=
  VFun 'p :=
    'p ':= ('!'p '+ '!'p).

(* EX1! (Triple_inplace_double) *)
(** Specify and verify the function [inplace_double].
    Hint: follow the template of [Triple_incr]. *)

(* SOLUTION *)
Lemma Triple_inplace_double : forall (p:loc) (n:int),
  TRIPLE (inplace_double p)
    PRE (p ~~> n)
    POST (fun (_:unit) => p ~~> (2*n)).
Proof using.
  xwp. xapp. xapp. xapp. xapp. xsimpl. math.
Qed.
(* /SOLUTION *)

(** [] *)


(* ******************************************************* *)
(** *** Increment of two references *)

(** Consider the following function, which expects the addresses
    of two reference cells, and increments both of them.

[[
  let incr_two p q =
    incr p;
    incr q
]]
*)

Definition incr_two : val :=
  VFun 'p 'q :=
    incr 'p ';
    incr 'q.

(** The specificaiton of this function takes the form
    [TRIPLE (incr_two p q) PRE _ POST (fun (r:unit) => _ )],
    where [r] denotes the result value of type unit.

    The precondition describes two references cells: [p ~~> n]
    and [q ~~> m]. To assert that the two cells are distinct from
    each other, we separate the two with the token [\*], which is
    called "separating conjunction" in Separation Logic, and is
    also known as the "star" operator. Thus, the precondition
    is [(p ~~> n) \* (q ~~> m)], or simply [p ~~> n \* q ~~> m].

    The postcondition describes the final state as
    is [p ~~> (n+1) \* q ~~> (m+1)], where the contents of both
    cells increased by one unit.

    The specification triple for [incr_two] is thus: *)

Lemma Triple_incr_two : forall (p q:loc) (n m:int),
  TRIPLE (incr_two p q)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (r:unit) => p ~~> (n+1) \* q ~~> (m+1)).

(** The proof follow the usual pattern. *)

Proof using.
  xwp. xapp. xapp. xsimpl.
Qed.

(** We register the specification [Triple_incr_two] in the
    database, to enable reasoning about calls to [incr_two]. *)

Hint Extern 1 (Register_Spec incr_two) => Provide Triple_incr_two.


(* ******************************************************* *)
(** *** Aliased arguments *)

(** The specification [Triple_incr_two] correctly describes calls to the
    function [incr_two] when providing it with two distinct reference cells.

    But it says nothing about a call of the form [incr_two p p].
    Indeed, in Separation Logic, a state described by [p ~~> n] cannot
    be matched against a state described by [p ~~> n \* p ~~> n], because
    the star operator requires its operand to correspond to disjoint pieces
    of state.

    What happens if we nevertheless try to exploit [Triple_incr_two]
    to reason about a call of the form [incr_two p p], that is, with
    aliased arguments?

    Let's try, by considering the operation [aliased_call p], which does
    execute such a call. *)

Definition aliased_call : val :=
  VFun 'p :=
    incr_two 'p 'p.

(** A call to [aliased_call p] should increase the contents of [p] by [2].
    This property can be specified as follows. *)

Lemma Triple_aliased_call : forall (p:loc) (n:int),
  TRIPLE (aliased_call p)
    PRE (p ~~> n)
    POST (fun (r:unit) => p ~~> (n+2)).

(** If we attempt the proof, we get stuck. Observe how [xapp] reports its
    failure to make progress. *)

Proof using.
  xwp. xapp.
Abort.

(** We get stuck with a proof obligation of the form:
    [\[] ==> (p ~~> ?m) \* _], which requires showing that
    from an empty state one can extract a reference [p ~~> ?m]
    for some integer [?m].

    What happened is that when matching the current state [p ~~> n]
    against [p ~~> ?n \* p ~~> ?m] (which corresponds to the precondition
    of [Triple_incr_two] with [q = p]), the internal simplification tactic
    was able to cancel out [p ~~> n] in both expressions, but then got
    stuck with matching the empty state against [p ~~> ?m]. *)

(** The issue here is that the specification [Triple_incr_two] is
    specialized for the case of non-aliased references.

    It is possible to state and prove an alternative specification for
    the function [incr_two], to cover the case of aliased arguments.
    Its precondition mentions only one reference, [p ~~> n], and its
    postcondition asserts that its contents gets increased by two units. *)

Lemma Triple_incr_two_aliased : forall (p:loc) (n:int),
  TRIPLE (incr_two p p)
    PRE (p ~~> n)
    POST (fun (r:unit) => p ~~> (n+2)).
Proof using.
  xwp. xapp. xapp. xsimpl. math.
Qed.

(** By exploiting this specification, we are able to verify the
    specification of [aliased_call p], which invokes [incr_two p p].
    In order to indicate to the [xapp] tactic that it should invoke
    the lemma [Triple_incr_two_aliased] and not [Triple_incr_two],
    we pass that lemma as argument to [xapp], by writing
    [xapp Triple_incr_two_aliased]. *)

Lemma Triple_aliased_call : forall (p:loc) (n:int),
  TRIPLE (aliased_call p)
    PRE (p ~~> n)
    POST (fun (r:unit) => p ~~> (n+2)).
Proof using.
  xwp. xapp Triple_incr_two_aliased. xsimpl.
Qed.


(* ******************************************************* *)
(** *** A function that takes two references, and increments one *)

(** Consider the following function, which expects the addresses
    of two reference cells, and increments only the first one.

[[
  let incr_first p q =
    incr p
]]
*)

Definition incr_first : val :=
  VFun 'p 'q :=
    incr 'p.

(** We can specify this function by describing its input state
    as [p ~~> n \* q ~~> m], and describing its output state
    as [p ~~> (n+1) \* q ~~> m]. Formally: *)

Lemma Triple_incr_first : forall (p q:loc) (n m:int),
  TRIPLE (incr_first p q)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (r:unit) => p ~~> (n+1) \* q ~~> m).
Proof using.
  xwp. xapp. xsimpl.
Qed.

(** Observe, however, that the second reference plays absolutely
    no role in the execution of the function. In fact, we might
    equally well have described in the precondition and in the
    postcondition only the first reference, the one that the code
    manipulates. *)

Lemma Triple_incr_first' : forall (p q:loc) (n:int),
  TRIPLE (incr_first p q)
    PRE (p ~~> n)
    POST (fun (r:unit) => p ~~> (n+1)).
Proof using.
  xwp. xapp. xsimpl.
Qed.

(** Interestingly, the former specification is "derivable" from the latter,
    as illustrated next. The tactic [xtriple] turns a specification triple
    of the form [TRIPLE _ PRE _ POST _] into one introduced by
    [PRE _ CODE _ POST _], enabling it to be processed by [xapp] to
    exploit a previously-established specification. *)

Lemma Triple_incr_first'_derived : forall (p q:loc) (n m:int),
  TRIPLE (incr_first p q)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (r:unit) => p ~~> (n+1) \* q ~~> m).
Proof using.
  xtriple. xapp Triple_incr_first. xsimpl.
Qed.

(** More generally, in Separation Logic, if a specification triple holds,
    then this specification triple remains valid by adding a same predicate
    in both the precondition and the postcondition. This is the "frame"
    principle, a key modularity feature that we'll come back to later on. *)


(* ******************************************************* *)
(** ** Exercise: transfer from one reference to another *)

(** Consider the [transfer] function, whose code appears below.

[[
  let transfer p q =
    p := !p + !q;
    q := 0
]]
*)

Definition transfer : val :=
  VFun 'p 'q :=
   'p ':= ('!'p '+ '!'q) ';
   'q ':= ``0.

(* EX1! (Triple_transfer) *)
(** State and prove a lemma called [Triple_transfer] specifying
    the behavior of [transfer p q] covering the case where [p]
    and [q] denote two distinct references. *)

(* SOLUTION *)
Lemma Triple_transfer : forall (p q:loc) (n m:int),
  TRIPLE (transfer p q)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (_:unit) => p ~~> (n + m) \* q ~~> 0).
Proof using.
  xwp. xapp. xapp. xapp. xapp. xapp. xsimpl.
Qed.
(* /SOLUTION *)

(** [] *)

(* EX1! (Triple_transfer_aliased) *)
(** State and prove a lemma called [Triple_transfer_aliased] specifying
    the behavior of [transfer] when it is applied twice to the same argument.
    It should take the form [TRIPLE (transfer p p) PRE _ POST _]. *)

(* SOLUTION *)
Lemma Triple_transfer_aliased : forall (p:loc) (n:int),
  TRIPLE (transfer p p)
    PRE (p ~~> n)
    POST (fun (_:unit) => p ~~> 0).
Proof using.
  xwp. xapp. xapp. xapp. xapp. xapp. xsimpl.
Qed.
(* /SOLUTION *)

(** [] *)


(* ******************************************************* *)
(** *** Existential quantification in heap predicates *)

(** Assume that the programming language includes a builtin
    random generator function, which expects an integer [n]
    and outputs an unspecified number between [0] and [n-1]
    inclusive. *)

Parameter random_int : val.

(** The function [random_int] can be specified as follows.

    Its precondition describes the empty state: [\[]].

    Its postcondition describes an integer [m], whose value
    is specified to lie in the expected range: [0 <= m < n].

    Formally:
*)

Parameter Triple_random_int : forall (n:int),
  TRIPLE (random_int n)
    PRE \[]
    POST (fun (m:int) => \[0 <= m < n]).

Hint Extern 1 (Register_Spec random_int) => Provide Triple_random_int.

(** Consider now the following function, which expects an
    integer [n], then invokes the random number generator
    with argument [n], places the result into a fresh
    reference cell, and returns the address of that reference.

[[
  let ref_random_int p =
    ref (random_int n)
]]
*)

Definition ref_random_int : val :=
  VFun 'n :=
    'ref (random_int 'n).

(** How can we specify the function [ref_random_int]?

    Its precondition should describe the empty state: [\[]].

    Its postcondition should bind the result value [(p:loc)],
    which describes the address of the freshly allocated cell.
    Moreover, it should assert that the memory state is of
    the form [p ~~> m], for some [m] such that [0 <= m < n].

    We can use the star operator to join the two pieces of
    information [p ~~> m] and [0 <= m < n] in the postcondition.
    Doing so, we would obtain:

[[
  Lemma Triple_ref_random_int : forall (n:int),
   TRIPLE (ref_random_int n)
      PRE \[]
      POST (fun (p:loc) => (p ~~> m) \* \[0 <= m < n]).
]]

    Yet, this statement does not typecheck because [m] is unbound.

    To fix the issue appropriately, we need to introduce a new
    Separation Logic operator: the existential quantifier for
    postconditions (and possibly also preconditions).
    The syntax is [\exists x, _], with a leading backslash to
    distinguish it from the Coq's standard existential quantifier. *)

Lemma Triple_ref_random_int : forall (n:int),
  TRIPLE (ref_random_int n)
    PRE \[]
    POST (fun (p:loc) => \exists m, (p ~~> m) \* \[0 <= m < n]).

(** Let's comment the proof of this lemma step by step. *)

Proof using.
  xwp.
  xapp. intros m Hm.
  (* [m] denotes the result of [random_int n].
     This variable is not substituted away because there is no equality
     of the form [m = _], but instead a constraint [Hm: 0 <= m < n]. *)
  xapp. intros q.
  (* [q] denotes the result of [ref m]. *)
  (* There remains to justify that the current state
     [q ~~> m] matches the postcondition, which is
     [\exists m0, q ~~> m0 \* \[0 <= m0 < n]].
     The simplification tactic [xsimpl] is able to instantiate [m0] as [m]. *)
  xsimpl.
  (* There remains to justify the constraint [0 <= m < n], which
     matches exactly the assumption [Hm] obtained earlier. *)
  auto.
Qed.


(* ******************************************************* *)
(** *** Exercise: allocate a reference with greater contents *)

(** Consider the following function.
[[
  let ref_greater p =
    ref (!p + 1)
]]
*)

Definition ref_greater : val :=
  VFun 'p :=
    'ref ('!'p '+ 1).

(* EX1! (Triple_ref_greater) *)
(** State a specification for the function [ref_greater], describing
    precisely the contents of the allocated reference.

    Hint: the postcondition takes the form [POST (fun (q:loc) => _)],
    where [q] denotes the location of the freshly allocated reference. *)

(* SOLUTION *)
Lemma Triple_ref_greater : forall (p:loc) (n:int),
  TRIPLE (ref_greater p)
    PRE (p ~~> n)
    POST (fun (q:loc) => p ~~> n \* q ~~> (n+1)).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl.
Qed.
(* /SOLUTION *)

(** [] *)

(* EX1! (Triple_ref_greater_abstract) *)
(** State another specification for the function [ref_greater],
    with a postcondition that does not reveal the contents of
    the freshly reference [q], but instead only asserts that the
    contents of it is greater than the contents of the argument [p].

    Then, derive the new specification from the former one, by
    invoking the tactics [xtriple] and [xapp Triple_ref_greater]. *)

(* SOLUTION *)
Lemma Triple_ref_greater_abstract : forall (p:loc) (n:int),
  TRIPLE (ref_greater p)
    PRE (p ~~> n)
    POST (fun (q:loc) => \exists m, \[m > n] \* q ~~> m \* p ~~> n).
Proof using.
  xtriple. xapp Triple_ref_greater. xsimpl. math.
Qed.
(* /SOLUTION *)

(** [] *)


(* ******************************************************* *)
(** *** Deallocation in Separation Logic *)

(** Separation Logic tracks allocated data. In its standard setup,
    Separation Logic enforces that all allocated data be eventually
    deallocated. (Technically, the logic is said to "linear" as opposed
    to "affine".) *)

(** Let us illustrate what happens when we forget to deallocate data.
    To that end, consider the following program, which computes
    the successor of a integer [n] by storing it into a reference cell,
    then incrementing that reference, and finally returning its contents.

[[
  let succ_using_incr_attempt n =
    let p = ref n in
    incr p;
    !p
]]
*)

Definition succ_using_incr_attempt :=
  VFun 'n :=
    Let 'p := 'ref 'n in
    incr 'p ';
    '! 'p.

(** The operation [succ_using_incr_attempt n] admits an empty
    precondition, and a postcondition asserting that the final
    result is [n+1]. Yet, if we try to prove this specification,
    we get stuck. *)

Lemma Triple_succ_using_incr_attempt : forall (n:int),
  TRIPLE (succ_using_incr_attempt n)
    PRE \[]
    POST (fun r => \[r = n+1]).
Proof using.
  xwp. xapp. intros p. xapp. xapp. xsimpl. { auto. }
Abort.

(** In the above script, we are stuck with the entailment
    [p ~~> (n+1) ==> \[]], which indicates that the current state contains
    a reference, whereas the postcondition describes an empty state. *)

(** We could attempt to patch the specification to account for the left-over
    reference. This yields a provable yet ususable specification. *)

Lemma Triple_succ_using_incr_attempt' : forall (n:int),
  TRIPLE (succ_using_incr_attempt n)
    PRE \[]
    POST (fun r => \[r = n+1] \* \exists p, (p ~~> (n+1))).
Proof using.
  xwp. xapp. intros p. xapp. xapp. xsimpl. { auto. }
Qed.

(** Indeed, the specification above features a piece of postcondition
    [\exists p, p ~~> (n+1)] that is of absolutely no use to the caller
    of the function. Worse, the caller will have its state polluted with
    [\exists p, p ~~> (n+1)] and will have no way to get rid of it appart
    from returning it into its own postcondition. *)

(** The right solution is to patch the code, to free the reference once
    it is no longer needed, as shown below.

[[
  let succ_using_incr n =
    let p = ref n in
    incr p;
    let x = !p in
    free p;
    x
]]
*)

Definition succ_using_incr :=
  VFun 'n :=
    Let 'p := 'ref 'n in
    incr 'p ';
    Let 'x := '! 'p in
    'free 'p ';
    'x.

(** This program may now be proved correct with respect to the intended
    specification. Observe in particular the last call to [xapp] below,
    which corresponds to the [free] operation. *)

Lemma Triple_succ_using_incr : forall n,
  TRIPLE (succ_using_incr n)
    PRE \[]
    POST (fun r => \[r = n+1]).
Proof using.
  xwp. xapp. intros p. xapp. xapp. xapp. xval. xsimpl. auto.
Qed.


(* ******************************************************* *)
(** *** Axiomatization of the mathematical factorial function *)

(** Our next example consists of a program that evaluate the
    factorial function. To specify this function, we consider
    a Coq axiomatization of the mathematical factorial function,
    which is called [facto]. *)

Parameter facto : int -> int.

Parameter facto_init : forall n,
  0 <= n <= 1 ->
  facto n = 1.

Parameter facto_step : forall n,
  n > 1 ->
  facto n = n * (facto (n-1)).

(** Remark: throught this axiomatization, we purposely do not specify
    the value of [facto] on negative arguments. *)


(* ******************************************************* *)
(** *** A partial recursive function, without state *)

(** In the rest of the chapter, we will consider recursive
    functions that manipulate the state. To gently introduce
    the necessary technique for reasoning about recursive
    functions, we first consider a recursive function that does
    not involve any mutable state.

    The function [factorec] computes the factorial of its argument.

[[
  let rec factorec n =
    if n <= 1 then 1 else n * factorec (n-1)
]]

*)

Definition factorec : val :=
  VFix 'f 'n :=
    If_ 'n '<= 1 Then 1 Else 'n '* 'f ('n '- 1).

(** A call [factorec n] can be specified as follows:

    - the initial state is empty
    - the final state is empty
    - the result value [r] is such that [r = facto n] when [n >= 0].

    In case the argument is negative (i.e., [n < 0]), we have two choices:

    - either we explicitly specify that the result is [1] in this case
    - or we rule out this possibility by requiring [n >= 0].

    Let us follow the second approach, in order to illustrate the
    specification of partial functions. There are yet two possibilities
    for expressing the constraint [n >= 0]:

    - either we use as precondition [\[n >= 0]],
    - or we place an asssumption [(n >= 0) -> _] to the front of the triple.

    The two presentations are totally equivalent. By convention, we follow
    the second presentation, which tends to improve the readability of
    specifications and the conciseness of proof scripts.

    The specification of [factorec] is thus stated as follows. *)

Lemma Triple_factorec : forall n,
  n >= 0 ->
  TRIPLE (factorec n)
    PRE \[]
    POST (fun (r:int) => \[r = facto n]).

(** We next go through the proof script in details, to explain in particular
    how to set up the induction, how to reason about the recursive call,
    and how to deal with the precondition [n >= 0]. *)

Proof using.
  (* We set up a proof by induction on [n] to obtain an induction
     hypothesis for the recursive calls, the last one being
     made on [n = 1]. The tactic [induction_wf] is provided by the TLC
     library to assist in setting up well-founded inductions. *)
  intros n. induction_wf IH: (downto 1) n.
  (* Observe the induction hypothesis [IH]. By unfolding [downto]
     as done in the next step, this hypothesis asserts that the
     specification that we are trying to prove already holds for
     arguments that are smaller than the current argument [n],
     and that are greater than or equal to [1]. *)
  unfold downto in IH.
  (* We may then begin the interactive verification proof. *)
  intros Hn. xwp.
  (* We reason about the evaluation of the boolean condition [n <= 1]. *)
  xapp.
  (* The result of the evaluation of [n <= 1] in the source program
     is described by the boolean value [isTrue (n <= 1)], which appears
     in the [CODE] section after [Ifval]. The operation [isTrue] is
     provided by the TLC library as a conversion function from [Prop]
     to [bool]. The use of such a conversion function (which leverages
     classical logic) greatly simplifies the process of automatically
     performing substitutions after calls to [xapp]. *)
  (* We next perform the case analysis on the test [n <= 1]. *)
  xif.
  (* Doing so gives two cases. *)
  { (* In the "then" branch, we can assume [n <= 1]. *)
    intros C.
    (* Here, the return value is [1]. *)
    xval. xsimpl.
    (* We check that [1 = facto n] when [n <= 1]. *)
    rewrite facto_init; math. }
  { (* In the "else" branch, we can assume [n > 1]. *)
    intros C.
    (* We reason about the evaluation of [n-1] *)
    xapp.
    (* We reason about the recursive call, implicitly exploiting
       the induction hypothesis [IH] with [n-1]. *)
    xapp.
    (* We justify that the recursive call is indeed made on a smaller
       argument than the current one, that is, [n]. *)
    { math. }
    (* We justify that the recursive call is made to a nonnegative argument,
       as required by the specification. *)
    { math. }
    (* We reason about the multiplication [n * facto(n-1)]. *)
    xapp.
    (* We check that [n * facto (n-1)] matches [facto n]. *)
    xsimpl. rewrite (@facto_step n); math. }
Qed.

(** Let's revisit the proof script without comments. *)

Lemma Triple_factorec' : forall n,
  n >= 0 ->
  TRIPLE (factorec n)
    PRE \[]
    POST (fun (r:int) => \[r = facto n]).
Proof using.
  intros n. induction_wf IH: (downto 1) n. unfold downto in IH.
  intros Hn. xwp. xapp. xif; intros C.
  { xval. xsimpl. rewrite facto_init; math. }
  { xapp. xapp. { math. } { math. } xapp. xsimpl.
    rewrite (@facto_step n); math. }
Qed.


(* ******************************************************* *)
(** *** A recursive function with state *)

(** The example of [factorec] was a warmup: a recursive function without
    mutable state. Let's now tackle a recursive function involving mutable
    state.

    The function [repeat_incr p m] makes [m] times a call to [incr p].
    Here, [m] is assumed to be a nonnegative value.

[[
  let rec repeat_incr p m =
    if m > 0 then (
      incr p;
      repeat_incr p (m-1)
    )
]]
*)

Definition repeat_incr : val :=
  VFix 'f 'p 'm :=
    If_ 'm '> 0 Then
      incr 'p ';
      'f 'p ('m '- 1)
    End.

(** The specification for [repeat_incr p] requires that the initial
    state contains a reference [p] with some integer contents [n],
    that is, [p ~~> n]. Its postcondition asserts that the resulting
    state is [p ~~> (n+m)], which is the result after incrementing
    [m] times the reference [p]. Observe that this postcondition is
    only valid under the assumption that [m >= 0]. *)

Lemma Triple_repeat_incr : forall (m n:int) (p:loc),
  m >= 0 ->
  TRIPLE (repeat_incr p m)
    PRE (p ~~> n)
    POST (fun (r:unit) => p ~~> (n + m)).

(* EX2! (Triple_repeat_incr) *)
(** Prove the function [Triple_repeat_incr].
    Hint: the structure of the proof resembles that of [Triple_factorec']. *)

Proof using. (* ADMITTED *)
  intros m. induction_wf IH: (downto 0) m. unfold downto in IH.
  intros n p Hm. xwp. xapp. xif; intros C.
  { xapp. xapp. xapp. { math. } { math. } xsimpl. math. }
  { xval. xsimpl. math. }
Qed. (* /ADMITTED *)

(** [] *)

(** In the previous examples of recursive functions, the induction
    was always performed on the first argument quantified in the
    specification. When the decreasing argument is not the first one,
    additional manipulations are required for re-generalizing into
    the goal the variables that may change during the course of the
    induction. Here is an example illustrating how to deal with such
    a situation. *)

Lemma Triple_repeat_incr' : forall (p:loc) (n m:int),
  m >= 0 ->
  TRIPLE (repeat_incr p m)
    PRE (p ~~> n)
    POST (fun (r:unit) => p ~~> (n + m)).
Proof using.
  (* First, introduces all variables and hypotheses. *)
  intros n m Hm.
  (* Next, generalize those that are not constant during the recursion. *)
  gen n Hm.
  (* Then, set up the induction. *)
  induction_wf IH: (downto 0) m. unfold downto in IH.
  (* Finally, re-introduce the generalized hypotheses. *)
  intros.
Abort.


(* ******************************************************* *)
(** *** Exercise: one-by-one transfer from a reference to another *)

(** Consider the function [step_transfer p q], which repeatedly increment
    a reference [p] and decrement a reference [q], until the contents
    of [q] reaches zero.

[[
  let rec step_transfer p q =
    if !q > 0 then (
      incr p;
      decr q;
      step_transfer p q
    )
]]
*)

Definition step_transfer :=
  VFix 'f 'p 'q :=
    If_ '! 'q '> 0 Then
      incr 'p ';
      decr 'q ';
      'f 'p 'q
    End.

(** The specification of [step_transfer] is essentially the same as
    that of the function [transfer], presented previously, with the
    only difference that we here assume the contents of [q] to be
    nonnegative. *)

Lemma Triple_step_transfer : forall p q n m,
  m >= 0 ->
  TRIPLE (step_transfer p q)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (_:unit) => p ~~> (n + m) \* q ~~> 0).

(* EX2! (Triple_step_transfer) *)
(** Verify the function [step_transfer].
    Hint: to set up the induction, follow the pattern from
    [Triple_repeat_incr'] presented just above. *)

Proof using. (* ADMITTED *)
  intros q p n m Hm.
  revert n Hm. induction_wf IH: (downto 0) m. unfold downto in IH.
  intros. xwp. xapp. xapp. xif; intros C.
  { xapp. xapp. xapp. { math. } { math. } xsimpl. math. }
  { xval. xsimpl. math. math. }
Qed. (* /ADMITTED *)

(** [] *)


(* ####################################################### *)
(** * Optional contents *)

(* ******************************************************* *)
(** *** Optimized scripts *)

(** The CFML tool features a number of tricks:
    - a call to [intros] in front of an [xwp] is always optional,
    - a single [xapp] in front of an [xif] is generally optional.

    Moreover, the TLC library offers a number of useful features:
    - writing [*] after a tactic name, such as in [xsimpl*],
      combines the tactic with a call to automation
      (in short, a combination of [intuition eauto] and [math]),
    - [unfold downto in IH] is not required because [math] can take care of it,
    - [introv] is a variant of [intros] that automatically introduces
      variables, and allows naming only actual hypotheses.

    Here is an example of a compact proof script for [factorec]. *)

Lemma Triple_factorec'' : forall n,
  n >= 0 ->
  TRIPLE (factorec n)
    PRE \[]
    POST (fun (r:int) => \[r = facto n]).
Proof using.
  introv Hn. gen Hn. induction_wf IH: (downto 1) n.
  xwp. xif; intros C.
  { xval. xsimpl. rewrite* facto_init. }
  { xapp. xapp*. xapp. xsimpl. rewrite* (@facto_step n). }
Qed.


(* ******************************************************* *)
(** *** Trying to prove incorrect specifications *)

(** Recall the function [repeat_incr p n], which invokes [n]
    times [incr p].

[[
  let rec repeat_incr p m =
    if m > 0 then (
      incr p;
      repeat_incr p (m-1)
    )
]]
*)

(** We proved for this function a specification with the constraint
    [m >= 0]. What if did omit it? Where would we get stuck in the proof?

    Clearly, something should break in the proof, because when [m < 0],
    the call [repeat_incr p m] terminates immediately. Thus, the final
    state should be like the initial state, that is [p ~~> n], and it
    should not be [p ~~> (n + m)]. Let us investigate. *)

Lemma Triple_repeat_incr_incorrect : forall (p:loc) (n m:int),
  TRIPLE (repeat_incr p m)
    PRE (p ~~> n)
    POST (fun (_:unit) => p ~~> (n + m)).
Proof using.
  intros. revert n. induction_wf IH: (downto 0) m. unfold downto in IH.
  intros. xwp. xapp. xif; intros C.
  { (* then branch: [m > 0] *)
    xapp. xapp. xapp. { math. } xsimpl. math. }
  { (* else branch: [m <= 0] *)
    xval.
    (* Here, we are requested to justify that the current state
       [p ~~> n] matches the postcondition [p ~~> (n + m)], which
       amounts to proving [n = n + m]. *)
    xsimpl.
    (* When the specification features the assumption [m >= 0],
       we can prove this equality because the fact that we are
       in the else branch means that [m <= 0], thus [m = 0].
       However, without [m >= 0], the value of [m] could be negative. *)
Abort.

(** Note that there exists a valid specification for [repeat_incr] that
    does not constraint [m], but instead specifies that the state evolves
    from [p ~~> n] to [p ~~> (n + max 0 m)]. Formally: *)

Lemma Triple_repeat_incr' : forall (p:loc) (n m:int),
  TRIPLE (repeat_incr p m)
    PRE (p ~~> n)
    POST (fun (_:unit) => p ~~> (n + max 0 m)).

(** Let's prove the above specification, which is the most-general
    specification for the function [repeat_incr].

    The proof scripts exploits two properties of the [max] function.

[[
   max_l : forall n m, (n >= m) -> (max n m = n).
   max_r : forall n m, (n <= m) -> (max n m = m).
]]
*)

Proof using.
  intros. gen n. induction_wf IH: (downto 0) m. unfold downto.
  xwp. xapp. xif; intros C.
  { xapp. xapp. xapp. { math. }
    xsimpl. repeat rewrite max_r; math. }
  { xval. xsimpl. rewrite max_l; math. }
Qed.


(* ******************************************************* *)
(** *** Incorrect quantification of existential variables *)

(** Recall the function [ref_random_int n], defined as
    [ref (random_int n)].

    Consider the following specification, which quantifies [m]
    outside of the triple, rather than using a [\exists] in the
    postcondition. *)

Parameter Triple_ref_random_int_incorrect : forall (n:int) (m:int),
  TRIPLE (ref_random_int n)
    PRE \[]
    POST (fun (p:loc) => (p ~~> m) \* \[0 <= m < n]).

(** What does this specification mean? It is useful? Is it provable?

    ...

    Answer: no function can admit this specification, because it
    could be instantiated, say, with [m=0] to prove that the output
    reference contains the integer [0]; and also with [m1] to prove
    that the output reference contains the integer [1]; the two
    instantiations contradict each other. *)

(** As a general rule, variables that are not arguments of the function,
    nor variables used in the preconditions (i.e., "ghost arguments"),
    should be bound in the postcondition, either as the return value
    (like [fun (p:loc) => _], or using a Separation Logic existential
    quantifier (e.g., [\exists m, _]). *)

