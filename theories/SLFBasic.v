(**

Separation Logic Foundations

Chapter: "Basic".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import Example. (* TODO: depend on CFML ? *)
Generalizable Variables A B.

Implicit Types n m : int.
Implicit Types p q : loc.



(* TODO: tune to make it linear by default ;
    there will be no need to explain \GC then . *)


(* ####################################################### *)
(** * The chapter in a rush & Additional contents *)

(** This chapter gives a quick overview of how to state specifications and 
    carry out basic proofs in Separation Logic using CFML tactics.

    In this chapter, we will present:
  
    - "Specification triples", of the form [TRIPLE _ PRE _ POST _],
      relating a term, a precondition, and a postcondition.
    - "Verification proof obligations", of the form [PRE _ CODE _ POST _],
      which is a variant of the [TRIPLE] notation that puts the current
      state as first argument.
    - "Entailement proof obligations", of the form [_ ==> _] or [_ ===> _],
      which require proving that a description of a state implies another one.

    The "heap predicates" used to describe the current memory state include:
    - [p ~~> n], which describes a memory cell at location [p] with contents [n],
    - [\[]], which describes an empty state,
    - [\[P]], which asserts that a proposition [P] is true (in an empty state),
    - [H1 \* H2], which describes a state made of two disjoint parts: [H1] and [H2],
    - [\exists x, H], which is used to quantify variables in postconditions.

    The proofs are carried out using CFML "x-tactics", including:
    - [xwp] to being a proof,
    - [xapp] to reason about an application,
    - [xval] to reason about a returned value,
    - [xsimpl] to simplify or prove entailments ([_ ==> _] or [_ ===> _]).

    In addition, the proof script exploit standard Coq tactics as well as
    tactics from the TLC library, including:
    - [unfold] to reveal a definition,
    - [introv H1 H2] as a variant of [intros] that skips variables
      and names only hypotheses,
    - [tactic ;=> x y] as a shorthand for [tactic; intros x y],
    - [math] to prove purely mathematical goals,
    - [gen] and [induction_wf] to set up (non-structural) inductions.

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
  
    In the real CFML tools, programs can be provided as input in
    OCaml syntax. However, throughout this course, to avoid unnecessary 
    tooling, we will input programs using a custom set of Coq notation.

    It is no needed to learn how to write programs in that funny syntax.
    All that matters is to be able to recognize that the Coq definition
    somehow matches the intended OCaml source code. 

    Below is the code for [incr]. The quotes are used to disambiguate
    with Coq syntax; the [VFun] token reads like [fun].
    
*)

Definition incr : val :=
  VFun 'p :=
   'p ':= '! 'p '+ 1.

(** Let [p] be the address of a reference cell, that is, a "location". 
    
    The expression [p ~~> n] describes a memory state in which the
    contents of the location [p] is the value [n], in this case an 
    integer value.

    The behavior of [incr p] is to update the memory state by incrementing
    the contents of the cell at location [p], so that its new contents is [n+1].
    The new memory state is described by the expression [p ~~> (n+1)].

    The result value returned by [incr p] is simply the "unit" value,
    so there is not much to specify about the result value, appart from
    the fact that it has type unit.

    The specification of [incr p] can be expressed using a 
    "Separation Logic triple"  using the custom notation
    [TRIPLE _ PRE _ POST _], as follows. *)

Lemma Triple_incr : forall (p:loc) (n:int),
  TRIPLE (incr p)
    PRE (p ~~> n)
    POST (fun (r:unit) => (p ~~> (n+1))).

(** Let us describe the components:

    - The [forall (p:loc) (n:int)] quantifies the argument of the function
      ([p]), as well as the ghost argument ([n]) which is used to describe
      the input state.
    - The keyword [TRIPLE] introduces the expression [incr p], which is the
      function call being specified.
    - The keyword [PRE] introduces the "precondition", which describes the
      input state that the function expects, here [p ~~> n].
    - The keyword [POST] introduces the "postcondition", which describes 
      both the output value and the output state produced by the call.
      The pattern [fun (r:unit) => _] binds the name [r] to denote the result 
      value; here [r] has type unit, reflecting the type of [incr p].
      The expression [p ~~> (n+1)] describes the output state.

      Important remark: [p ~~> n+1] would parse as [(p ~~> n) + 1] and fail
      to typecheck, so please beware that parentheses are required. *)

(** Let us now prove that specification, by conducting a verification proof 
    using CFML tactics. *)

(** The CFML tooling will transform on-the-fly the code so that all 
    intermediate expressions are named (that is, in "A-normal form").
    In OCaml syntax, this would be:
    
[[
  let incr p =
    let m = 
      let n = !p in
      n + 1 in
    p := m
]]

  This transformation is performed by the tactic [xwp], which begins every
  CFML verification proof script.
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

             The remaining of the proof performs some form of symbolic 
             execution. One should not attempt to read all the proof 
             obligation at each step, but instead look at the current
             state (the [PRE] part, which is [p ~~> n]), and the first
             line only of the [CODE] part.
 *)
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
    is able to automatically invoke the lemma [Triple_incr]. 

    (There is no need to understand the internal magic of how the
    database is implemented by hacking Coq's [Hint] mechanism.) *)

Hint Extern 1 (Register_Spec incr) => Provide Triple_incr.


(* ******************************************************* *)
(** *** A function with a return value *)

(** As second example, we describe a function that performs some simple
    computations, and features no mutation---working in an empty memory state.

    The function, whose code appears below, expects an integer argument [n],
    computes [a] as [n+1], computes [b] as [n-1], then returns [a+b].
    The function thus always returns [2*n].

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
    in the precondition (after the [PRE] keyword).

    To denote the fact that the output state is empty, we could use [\[]].
    Yet, if we write [fun (r:int) => \[]] as postcondition, we would have 
    said nothing about the output value [r] produced by a call [example_let].
    Instead, we would like to specify that the result [r] is equal to [2*n].
    To that end, we write [fun (r:int) => \[2*n]] as postcondition. *)

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
    work well for small programs, yet in some programs can lead to
    exponential blow-up in the terms being manipulated. To avoid the
    blow-up, it may be necessary to preserve explicit equalities, 
    such as [a = n+1] and [b = n-1] in the context.

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


(* ******************************************************* *)
(** ** Exercise: function [double] *)

(** Consider the function [double] that expects an integer [n]
    and returns its double, that is, the value [2 * n].

[[
  let double n =
    n + n
]]
*)

Definition double : val :=
  VFun 'n :=
    'n '+ 'n.

(* EX1! (Triple_double) *)
(** Complete the postcondition of [Triple_double] to express that
    it returns [2*n], then prove it. *)

Lemma Triple_double : forall (n:int),
  TRIPLE (double n)
    PRE \[]
    POST (fun (r:int) => (* SOLUTION *) \[r = 2 * n] (* /SOLUTION *)).
Proof using.
  (* SOLUTION *) xwp. xapp. xsimpl. math. (* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Exercise: function [inplace_double] *)

(** Consider the function [inplace_double] that expects a reference
    on an integer, reads twice in that reference, and updates the
    reference with the sum of the two values that have been read.

[[
  let inplace_double p =
    p := !p + !p
]]
*)

(* EX1! (Triple_inplace_double) *)
(** Complete the precondition and the postcondition of
    [Triple_inplace_double] to express that it returns [2*n],
    then prove the specification. *)

Definition inplace_double : val :=
  VFun 'p :=
    'p ':= ('!'p '+ '!'p).

Lemma Triple_inplace_double : forall (p:loc) (n:int),
  TRIPLE (inplace_double p)
    PRE ((* SOLUTION *) p ~~> n (* /SOLUTION *))
    POST (fun (_:unit) => (* SOLUTION *) p ~~> (2*n) (* /SOLUTION *)).
Proof using.
  (* SOLUTION *) xwp. xapp. xapp. xapp. xapp. xsimpl. math. (* /SOLUTION *)
Qed.


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

    The precondition describes two references cells:
    [p ~~> n] for the first one, and [q ~~> m]. To assert
    that the two cells are distinct from each other, we
    separate the two with the token [\*], which is called
    "separating conjunction" in Separation Logic, and is
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

(** Let us register the specification [Triple_incr_one_of_two] in 
    the database of specifications. *)

Hint Extern 1 (Register_Spec incr_two) => Provide Triple_incr_two.

(** The specification above correctly describes calls to the function
    [incr_two] when providing it with two distinct reference cells.
    But it says nothing about a call of the form [incr_two p p].
    Indeed, in Separation Logic, if we have a state described by [p ~~> n], 
    we cannot possibly match it with [p ~~> n \* p ~~> n], because the
    star operator requires its operand to correspond to disjoint pieces
    of heap. 

    What happens if we nevertheless try to exploit [Triple_incr_one_of_two]
    on a call of the form [incr_two p p]? Let's try, by considering a 
    function [aliased_call p] that execute precisely this call. *)

Definition aliased_call : val :=
  VFun 'p :=
    incr_two 'p 'p.

Lemma Triple_aliased_call : forall (p:loc) (n:int),
  TRIPLE (aliased_call p)
    PRE (p ~~> n)
    POST (fun (r:unit) => p ~~> (n+2)).

(** The proof follow the usual pattern. *)

Proof using.
  xwp. xapp.
Abort.

(** We get stuck with a proof obligation of the form:
    [\[] ==> (p ~~> ?m) \* _], which requires showing that
    from an empty state one can extract a reference [p ~~> ?m]
    for some integer [?m].
  
    What happened in that when matching the current state
    [p ~~> n] against [p ~~> ?n \* p ~~> ?m]
    (that is, the precondition of [Triple_incr_one_of_two]
    when [q = p]), the internal simplification tactic could cancel 
    out [p ~~> n] in both expressions, but then got stuck with
    matching the empty state against [q ~~> ?m]. *)

(** It is, however, possible to state and prove an alternative
    specification for the function [incr_two], specifically covering 
    the case where the two arguments are equal. In that case, the
    specification is totally different: the precondition mentions
    only one reference, [p ~~> n], and the postcondition asserts
    that its contents gets increased by two units. *)

Lemma Triple_incr_two_aliased : forall (p:loc) (n:int),
  TRIPLE (incr_two p p)
    PRE (p ~~> n)
    POST (fun (r:unit) => p ~~> (n+2)).

(** The proof follow the usual pattern. *)

Proof using.
  xwp. xapp. xapp. xsimpl. math.
Qed.


(* ******************************************************* *)
(** *** A function that takes two references, and increment one *)

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

(** Interestingly, the former definition is "derivable" from the latter.
    To illustrate this, let us register the specification [Triple_incr_first]
    in the database, and use the tactic [xapp] to exploit it to derive
    [Triple_incr_first']. *)

Hint Extern 1 (Register_Spec incr_first) => Provide Triple_incr_first.

Lemma Triple_incr_first'_derived : forall (p q:loc) (n m:int),
  TRIPLE (incr_first p q)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (r:unit) => p ~~> (n+1) \* q ~~> m).
Proof using.
  intros. xapp. xsimpl.
Qed.

(** More generally, in Separation Logic, if a specification triple holds,
    then this specification triple remains valid by adding a same predicate
    in both the precondition and the postcondition. This is the "frame"
    principle, a key modularity feature that we'll discuss later. *)


(* ******************************************************* *)
(** ** Exercise: transfer from one reference to another *)

(** Consider the following function.

[[
  let transfer p q =
    p := !p + !q;
    q := 0
]]

    Remark: for technical reasons, the constant [0] needs to be
    written [``0] in the code below. --  TODO: fix this.
*)

Definition transfer : val :=
  VFun 'p 'q :=
   'p ':= ('!'p '+ '!'q) ';
   'q ':= ``0.

(* EX2! (Triple_transfer) *)
(** State and prove a lemma called [Triple_transfer] specifying
    the behavior of [transfer] when its arguments consists of two
    distinct references. *)

(* SOLUTION *)
Lemma Triple_transfer : forall (p q:loc) (n m:int),
  TRIPLE (transfer p q)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (_:unit) => p ~~> (n + m) \* q ~~> 0).
Proof using.
  xwp. xapp. xapp. xapp. xapp. xapp. xsimpl.
Qed.
(* /SOLUTION *)

(* EX2! (Triple_transfer_aliased) *)
(** State and prove a lemma called [Triple_transfer_aliased] 
    specifying the behavior of [transfer] when it is applied
    twice to the same argument, that is, [transfer p p]. *)

(* SOLUTION *)
Lemma Triple_transfer_aliased : forall (p:loc) (n:int),
  TRIPLE (transfer p p)
    PRE (p ~~> n)
    POST (fun (_:unit) => p ~~> 0).
Proof using.
  xwp. xapp. xapp. xapp. xapp. xapp. xsimpl.
Qed.
(* /SOLUTION *)


(* ******************************************************* *)
(** *** Existential quantifier to introduce abstraction *)

(** Assume that the programming language includes a builtin
    random generator function, which expects an integer [n]
    and outputs an unspecified number between [0] and [n-1]
    inclusive. *)

Parameter random_int : val.

(** The function [random_int] can be specified as follows.

    The precondition describes the empty state: [\[]]. 

    The postcondition describes an integer [m], whose value
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
    with argument [n], and places the result into a fresh
    reference cell, which it returns.

[[
  let ref_random_int p =
    ref (random_int n)
]]
*)

Definition ref_random_int : val :=
  VFun 'n :=
    'ref (random_int 'n).

(** How can we specify the function [ref_random_int]?
    The precondition describes the empty state: [\[]].
    The postcondition should bind the result value [(p:loc)],
    which describes the address of the freshly allocated cell.
    Moreover, it should assert that the memory state is of
    the form [p ~~> m], for some [m] such that [0 <= m < n].

    We can use the star operator to join the two pieces of
    information [p ~~> m] and [0 <= m < n] in the postcondition:

[[    
    POST (fun (p:loc) => (p ~~> m) \* \[0 <= m < n]).
]]

    Yet, this statement does not typecheck because [m] is unbound.
    To fix the issue appropriately, we need to introduce a new
    Separation Logic operator: the existential quantifier for
    postconditions (and possibly also preconditions).
    The syntax is [\exists x, _], with a leading backslash. *)

Lemma Triple_ref_random_int : forall (n:int),
  TRIPLE (ref_random_int n)
    PRE \[]
    POST (fun (p:loc) => \exists m, (p ~~> m) \* \[0 <= m < n]).

(** The proof of this lemma is interesting. *)

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
     The simplification tactic is able to instantiate [m0] as [m]. *)
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

(* EX2! (Triple_ref_greater) *)
(** State a specification for the function [ref_greater].
    Hint: the postcondition takes the form [POST (fun (q:loc) => _)],
    where [q] denotes the location of the freshly allocated reference. *)

Lemma Triple_ref_greater : forall (p:loc) (n:int),
  TRIPLE (ref_greater p)
(* SOLUTION *)
    PRE (p ~~> n)
    POST (fun (q:loc) => p ~~> n \* q ~~> (n+1)).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl.
Qed.
(* /SOLUTION *)

Hint Extern 1 (Register_Spec ref_greater) => Provide Triple_ref_greater.

(* EX2! (Triple_ref_greater_abstract) *)
(** State another specification for the function [ref_greater],
    with a postcondition that does not reveal the contents of 
    the freshly reference [q], but instead only asserts that the
    contents of it is greater than the contents of the argument [p].

    Then, derive the new specification from the former one. 
    Hint: invoke [xapp]. *)

Lemma Triple_ref_greater_abstract : forall (p:loc) (n:int),
(* SOLUTION *)
  TRIPLE (ref_greater p)
    PRE (p ~~> n)
    POST (fun (q:loc) => \exists m, \[m > n] \* q ~~> m \* p ~~> n).
Proof using.
  intros. xapp. xsimpl. math.
Qed.
(* /SOLUTION *)


(* ******************************************************* *)
(** *** Axiomatization of the mathematical factorial function *)

(** Throughout the rest of the course, we will see several
    examples of programs that evaluate the factorial function.

    We specify and verify these functions with respect to a Coq
    axiomatization of the corresponding mathematical function,
    called [facto]. Observe that we purposely do not specify
    the value of [facto] on negative arguments. *)

Parameter facto : int -> int.

Parameter facto_init : forall n, 
  0 <= n <= 1 ->
  facto n = 1.

Parameter facto_step : forall n, 
  n > 1 ->
  facto n = n * (facto (n-1)).


(* ******************************************************* *)
(** *** A partial recursive function, without state *)

(** In the rest of the chapter, we will consider recursive 
    functions that manipulate the state. To gently introduce
    the necessary technique for reasoning about recursive 
    functions, we first consider one that does not involve  
    any mutable state.

    To that end, consider the [factorec] function, which
    recursively computes the factorial of its argument [n].

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

    The specification thus looks as follows. *)

Lemma Triple_factorec : forall n, 
  n >= 0 ->
  TRIPLE (factorec n)
    PRE \[]
    POST (fun (r:int) => \[r = facto n]).
Proof using.
  (* Set up a proof by induction on [n] to obtain an induction 
     hypothesis for the recursive calls, the last one being
     made on [n = 1]. *)
  intros n. induction_wf IH: (downto 1) n.
  (* Observe the induction hypothesis [IH]. By unfolding [downto]
     as done in the next step, this hypothesis asserts that the
     specification that we are trying to prove already holds for
     arguments that are smaller than the current argument [n]
     (and greater than or equal to [1]). *)
  unfolds downto.
  (* Begin the interactive verification proof. *)
  intros Hn. xwp. 
  (* Reason about the evaluation of the boolean condition [n <= 1]. *)
  xapp. 
  (* Perform a case analysis. *)
  xif.
  (* This gives two branches. *)
  { (* In the "then" branch, [n <= 1]. *)
    intros C.
    (* The return value is [1]. *)
    xval. xsimpl. 
    (* Check that [1 = facto n] when [n <= 1]. *)
    rewrite facto_init; math. }
  { (* In the "else" branch, [n > 1]. *)
    intros C.
    (* Reason about the evaluation of [n-1] *)
    xapp.
    (* Reason about the recursive call, implicitly exploiting 
       the induction hypothesis [IH] with [n-1]. *)
    xapp.
    (* Justify that the recursive call is indeed made on a smaller
       argument than the current one, that is, [n]. *)
    { math. }
    (* Justify that the recursive call is made to a nonnegative argument,
       as required by the specification. *)
    { math. }
    (* Reason about the multiplication [n * facto(n-1)]. *)
    xapp.
    (* Check that [n * facto (n-1)] matches [facto n]. *)
    xsimpl. rewrite (@facto_step n); math. }  
Qed.

(** Let's revisit the proof script without comments, and by skipping
    the superfluous tactics, such as [xapp] before [xif]. *)

Lemma Triple_factorec' : forall n,
  n >= 0 ->
  TRIPLE (factorec n)
    PRE \[]
    POST (fun (r:int) => \[r = facto n]).
Proof using.
  intros n. induction_wf IH: (downto 1) n. unfolds downto.
  intros Hn. xwp. xif; intros C.
  { xval. xsimpl.
    rewrite facto_init; math. }
  { xapp. xapp. { math. } { math. } xapp. xsimpl. 
    rewrite (@facto_step n); math. }
Qed.


(* ******************************************************* *)
(** *** A recursive function with state *)

(** We now tackle a recursive function involving mutable state.
    
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

(** The specification for [repeat_incr] requires that the initial
    state contains a reference [p] with some integer contents [n], 
    that is, [p ~~> n]. Its postcondition asserts that the resulting
    state is [p ~~> (n+m)], which is the result after incrementing
    [m] times the reference [p]. This specification holds under the 
    assumption that [m >= 0]. *)

Lemma Triple_repeat_incr : forall (m n:int) (p:loc),
  m >= 0 ->
  TRIPLE (repeat_incr p m)
    PRE (p ~~> n)
    POST (fun (r:unit) => p ~~> (n + m)).

(* EX2! (Triple_repeat_incr) *)
(** Prove the function [Triple_repeat_incr].
    Hint: it resembles the proof [Triple_factorec']. *)

Proof using.
(* SOLUTION *)
  intros m. induction_wf IH: (downto 0) m. unfolds downto.
  intros n p Hm. xwp. xif; intros C.
  { xapp. xapp. xapp. { math. } { math. } xsimpl. math. }
  { xval. xsimpl. math. }
(* /SOLUTION *)
Qed.

(** In the previous examples of recursive functions, the induction
    was always performed on the first argument quantified in the
    specification. When the decreasing argument is not the first one,
    additional manipulations are required for re-generalizing into
    the goal the variables that may change during the course of the
    induction.

    Here is an exmaple. *)

Lemma Triple_repeat_incr' : forall (p:loc) (n m:int),
  m >= 0 ->
  TRIPLE (repeat_incr p m)
    PRE (p ~~> n)
    POST (fun (r:unit) => p ~~> (n + m)).
Proof using.
  (* First, introduces all variables and hypotheses. *)
  introv Hm.  (* equivalent to [intros n m Hm] *)
  (* Next, generalize those that are not constant during the recursion. *)
  revert n Hm.
  (* Then, set up the induction. *)
  induction_wf IH: (downto 0) m. 
  (* Finally, re-introduce the generalized hypotheses. *)
  intros.
Abort.


(* ******************************************************* *)

(** Hints:
    - [xwp] to begin the proof
    - [xapp] for applications, or [xappn] to repeat
    - [xif] for a case analysis
    - [xval] for a value
    - [xsimpl] to prove entailments
    - [auto], [math], [rew_list] to prove pure facts
      or just [*] after a tactic to invoke automation.
*)



(* ******************************************************* *)
(** *** A recursive function (yellow belt) *)

(** Here, we will assume [!p > 0].

[[
  let rec slow_transfer p q =
    if !p > 0 then (
      decr p;
      incr q;
      transfer p q
    )
]]
*)

Definition slow_transfer :=
  VFix 'f 'p 'q :=
    If_ '! 'p '> 0 Then
      decr 'p ';
      incr 'q ';
      'f 'p 'q
    End.

Lemma Triple_slow_transfer : forall p q n m,
  n >= 0 ->
  TRIPLE (slow_transfer p q)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (_:unit) => (* SOLUTION *) p ~~> 0 \* q ~~> (n + m) (* /SOLUTION *)).
Proof using.
  introv N. gen m N. induction_wf IH: (downto 0) n. intros.
  (* SOLUTION *)
  xwp. xapp. xapp. xif ;=> C.
  { xapp. xapp. xapp. { hnf. math. } { math. }
    xsimpl. math. }
  { xval. xsimpl. math. math. }
  (* /SOLUTION *)
Qed.

End ExoBasic.





(* ******************************************************* *)
(** *** Facto *)

(**
[[
  let rec facto n f =
    ...
    
]]
*)









(* ####################################################### *)
(** * Optional contents *)


(* ******************************************************* *)
(** *** Optimized scripts *)

Module OptimizedScripts.

(** The CFML tool features the tactic [xappn] that iterates calls to [xapp],
    and the tactic [xsimpl*] that combines [xsimpl] with call to automation. 
    Using these tactics, proofs scripts for simple functions can be greatly
    shortened. *)

Lemma Triple_incr : forall (p:loc) (n:int),
  TRIPLE (incr p)
    PRE (p ~~> n)
    POST (fun (r:unit) => (p ~~> (n+1))).
Proof using. xwp. xappn. xsimpl*. Qed.

Lemma Triple_example_let : forall n,
  TRIPLE (example_let n)
    PRE \[]
    POST (fun (r:int) => \[r = 2*n]).
Proof using. xwp. xappn. xsimpl*. Qed.

Lemma Triple_factorial : forall n,
  TRIPLE (factorial n)
    PRE \[]
    POST (fun (r:int) => \[r = facto n]).
Proof using.
  intros. induction_wf IH: (downto 1) n. xwp. xif ;=> C.
  { xval. xsimpl. rewrite* facto_init. }
  { xapp. xapp*. xapp. xsimpl. rewrite* (@facto_step n). }
Qed.

(** The use of such advanced tactics is beyond the scope of this course.
    In general, the overhead of executing the steps one by one is acceptable,
    and it helps better reflecting the structure of the program in the proof.
    Moreover, for complex programs, the advanced tactics are generally of 
    limited benefits, because at each step there are many side-conditions
    that need to be justified. *)

End OptimizedScripts.

(** Remark: [fun (r:unit)] could also be written [fun (_:unit)]. *)


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


(* ******************************************************* *)
(** *** Deallocation in Separation Logic *)

(** By default, Separation Logic treats allocated resources 
    ---it is a "linear" logic as opposed to an "affine" logic.
    Remark: it is possible to tweak Separation Logic to make it
    affine and enable throwing away. *)

(*

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
    '! 'p.

Lemma Triple_succ_using_incr : forall n,
  TRIPLE (succ_using_incr ``n)
    PRE \[]
    POST (fun r => \[r = n+1]).
Proof using.
  xwp. xapp ;=> p. (* xapp. intros p. *)
  xapp. xapp. xsimpl*.
Qed.

(** Note: [decr] is similarly defined in the library. *)





(* ******************************************************* *)
(** *** Trying to prove incorrect specifications *)


(** Let's try to prove a false specification *)

Lemma Triple_repeat_incr : forall p n m,
  TRIPLE (repeat_incr p m)
    PRE (p ~~> n)
    POST (fun (_:unit) => p ~~> (n + m)).
Proof using.
  intros. gen n. induction_wf IH: (downto 0) m. intros.
  xwp. xapp. xif ;=> C.
  { (* then branch *)
    xapp. xapp. xapp. { unfold downto. math. } xsimpl. math. }
  { (* else branch *)
    xval. xsimpl.
Abort.


(** Let's try yet another time *)

Lemma Triple_repeat_incr' : forall p n m,
  TRIPLE (repeat_incr p m)
    PRE (p ~~> n)
    POST (fun (_:unit) => p ~~> (n + max 0 m)).
Proof using.
  intros. gen n. induction_wf IH: (downto 0) m; intros.
  xwp. xapp. xif; intros C.
  { xapp. xapp. xapp. { hnf. math. }
    xsimpl. repeat rewrite max_nonneg; math. }
  { xval. xsimpl. rewrite max_nonpos; math. }
Qed.




(* ******************************************************* *)
(** *** Specification of a higher-order function: repeat *)

(**
[[
  let rec repeat n f =
    if n > 0 then begin
      f ();
      repeat (n-1) f
    end
]]
*)




(* ******************************************************* *)
(** *** Call to a higher-order function *)

(**
[[
  let add_to p n =
    let f = (fun () -> incr p) in 
    repeat f n
]]
*)



(* ******************************************************* *)
(** *** Exercise: square *)

(**
[[
  let square n =
    let p = ref 0 in
    let f = (fun () -> add_to p n) in 
    repeat f n;
    !p
]]

*)





