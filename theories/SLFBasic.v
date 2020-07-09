(**

Foundations of Separation Logic

Chapter: "Basic".

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Import SLFDirect SLFExtra.
Import SLFProgramSyntax DemoPrograms ExtraDemoPrograms.

Implicit Types n m : int.
Implicit Types p q : loc.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Chapter in a rush, nested with exercises as additional contents *)

(** This chapter gives an overview of how the key features of Separation
    Logic, and presents through a series of example a practical verification
    framework, whose construction is presented throughout this course.

    This chapter introduces the following notions:

    - "Heap predicates", which are used to describe memory states in
      Separation Logic.
    - "Specification triples", of the form [triple t H Q], which relate
      a term [t], a precondition [H], and a postcondition [Q].
    - "Entailment proof obligations", of the form [H ==> H'] or [Q ===> Q'],
      which assert that a pre- or post-condition is weaker than another one.
    - "Verification proof obligations", of the form [PRE H CODE F POST Q],
      which internally leverage a form of weakest-precondition.
    - Custom proof tactics, called "x-tactics", which are specialized tactics
      for carrying out the verification proofs.

    The "heap predicates" used to describe memory states are presented
    throughout the chapter. They include:
    - [p ~~> n], which describes a memory cell at location [p] with contents [n],
    - [\[]], which describes an empty state,
    - [\[P]], which also describes an empty state, and moreover asserts that
      the proposition [P] is true,
    - [H1 \* H2], which describes a state made of two disjoint parts: [H1] and [H2],
    - [\exists x, H], which is used to quantify variables in postconditions.

    All these heap predicates admit the type [hprop], which consists of predicate
    over memory states. Technically, [hprop] is defined as [state->Prop].

    The verification of practical programs is carried out using x-tactics,
    identified by the leading "x" letter in their name. These tactics include:
    - [xwp] or [xtriple] to begin a proof,
    - [xapp] to reason about an application,
    - [xval] to reason about a return value,
    - [xif] to reason about a conditional,
    - [xsimpl] to simplify or prove entailments ([H ==> H'] or [Q ===> Q']).

    In addition to x-tactics, the proof scripts exploit standard Coq tactics,
    as well as tactics from the TLC library. The relevant TLC tactics, which
    are described when first use, include:
    - [math], which is a variant of [omega] for proving mathematical goals,
    - [induction_wf], which sets up proofs by well-founded induction,
    - [gen], which is a shorthand for [generalize dependent], a tactic
      also useful to set up induction principles.

    For simplicity, we assume all programs to be written in A-normal form,
    that is, with all intermediate expressions being named by a let-binding.
    For each program, we first show its code using OCaml-style syntax, then
    formally define the code in Coq using an ad-hoc notation system,
    featuring variable names and operators all prefixed by a quote symbol. *)


(* ########################################################### *)
(** ** The increment function *)

(** As first example, consider the function [incr], which increments
    the contents of a mutable cell that stores an integer. In OCaml
    syntax, this function is defined as:

[[
   let incr p =
       let n = !p in
       let m = n + 1 in
       p := m
]]

    We describe this program in Coq using a custom set of notation for the
    syntax of imperative programs. There is no need to learn how to write
    programs in this ad-hoc syntax: source code is provided for all the
    programs involved in this course.

    The definition for the function [incr] appears below. This function is a
    value, so it admits, like all values in our framework, the type [val]. *)

Definition incr : val :=
  Fun 'p :=
    Let 'n := '! 'p in
    Let 'm := 'n '+ 1 in
    'p ':= 'm.

(** The quotes that appear in the source code are used to disambiguate
    between the keywords and variables associated with the source code,
    and those from the corresponding Coq keywords and variables.
    The [Fun] keyword should be read like the [fun] keyword from OCaml.

    The reader may blindly trust that it corresponds to the OCaml code
    shown previously. *)

(** The specification of [incr p], shown below, is expressed using a
    "Separation Logic triple". A triple is formally expressed by a proposition
    of the form [triple t H Q]. By convention, we write the precondition [H]
    and the postcondition [Q] on separate lines. Details are explained next. *)

Lemma triple_incr : forall (p:loc) (n:int),
  triple (incr p)
    (p ~~> n)
    (fun _ => (p ~~> (n+1))).

(** Above, [p] denotes the address in memory of the reference cell provided
    as argument to the increment function. In technical vocabulary, [p]
    is the "location" of a reference cell. All locations have type [loc],
    thus the argument [p] of [incr] has type [loc].

    In Separation Logic, the "heap predicate" [p ~~> n] describes a memory
    state in which the contents of the location [p] is the value [n].
    In the present example, [n] denotes an integer value.

    The behavior of the operation [incr p] consists of updating the memory
    state by incrementing the contents of the cell at location [p], so that
    its new contents is [n+1]. Thus, the memory state posterior to the
    increment operation can be described by the heap predicate [p ~~> (n+1)].

    The result value returned by [incr p] is the unit value, which does not
    carry any useful information. In the specification of [incr], the
    postcondition is of the form [fun _ => ...] to indicate that there is
    no need to bind a name for the result value. *)

(** The general pattern of a specification thus includes:

    - Quantification of the arguments of the functions---here, the variable [p].
    - Quantification of the "ghost variables" used to describe the input
      state---here, the variable [n].
    - The application of the predicate [triple] to the function application
      [incr p], which is the term being specified by the triple.
    - The precondition describing the input state---here, the predicate [p ~~> n].
    - The postcondition describing both the output value and the output state.
      The general pattern is [fun r => H'], where [r] denotes the name of
      the result, and [H'] describes the final state. Here, the final
      state is described by [p ~~> (n+1)]. *)

(** Remark: we have to write [p ~~> (n+1)] using parentheses around [n+1],
    because [p ~~> n+1] would get parsed as [(p ~~> n) + 1]. *)

(** Our next step is to prove the specification lemma [triple_incr] which
    specifies the behavior of the function [incr]. We conduct the
    verification proof using x-tactics. *)

Proof using.
  xwp.     (* [xwp] begins the verification proof. The proof obligation is
              displayed using the custom notation [PRE H CODE F POST Q].
              The [CODE] part does not look very nice, but one should
              be able to somehow recognize the body of [incr]. Indeed,
              if we ignoring the details, and perform the alpha-renaming
              from [v] to [n] and [v0] to [m], the [CODE] section reads like:
[[
              Let' n := (App val_get p) in
              Let' m := (App val_add n 1) in
              App val_set p m
]]
              which is somewhat similar to the original source code.
           *)

 (*  The remaining of the proof performs some form of symbolic
     execution. One should not attempt to read the full proof
     obligation at each step, but instead only look at the current
     state, described by the [PRE] part (here, [p ~~> n]), and at
     the first line only of the [CODE] part, where one can read
     the code of the next operation to reason about.

     Each function call is handled using the tactic [xapp]. *)

  xapp.    (* We reason about the operation [!p] that reads into [p];
              this read operation returns the value [n]. *)
  xapp.    (* We reason about the addition operation [n+1]. *)
  xapp.    (* We reason about the update operation [p := n+1],
              thereby updating the state to [p ~~> (n+1)]. *)
  xsimpl.  (* At this stage, the proof obligation takes the form [_ ==> _],
              which require checking that the final state matches what
              is claimed in the postcondition. We discharge it using
              the tactic [xsimpl]. *)
Qed.

(** The command below associates the specification lemma [triple_incr]
    with the function [incr] in a hint database, so that if we subsequently
    verify a program that features a call to [incr], the [xapp] tactic
    is able to automatically invoke the lemma [triple_incr]. *)

Hint Resolve triple_incr : triple.

(** Remark: the proof framework can be used without any knowledge about
    the implementation of the notation [PRE H CODE F POST Q] nor about
    the implementation of the x-tactics.

    A reader with prior knowledge in program verification might
    nevertheless be interested to know that [PRE H CODE F POST Q]
    is defined as the entailment [H ==> F Q], where [F] is a form of
    weakest-precondition that describes the behavior of the code. *)


(* ########################################################### *)
(** ** A function with a return value *)

(** As second example, we describe a function that performs simple
    arithmetic computations. The function, whose code appears below,
    expects an integer argument [n], computes [a] as [n+1], then
    computes [b] as [n-1], and finally returns [a+b]. The function
    thus always returns [2*n].

[[
    let example_let n =
      let a = n + 1 in
      let b = n - 1 in
      a + b
]]
*)

Definition example_let : val :=
  Fun 'n :=
    Let 'a := 'n '+ 1 in
    Let 'b := 'n '- 1 in
    'a '+ 'b.

(** We specify this function using the the triple notation, in the form
    [triple (example_let n) H (fun r => H')], where [r], of type [val],
    denotes the output value.

    To denote the fact that the input state is empty, we write [\[]]
    in the precondition.

    To denote the fact that the output state is empty, we could use [\[]].
    Yet, if we write just [fun r => \[]] as postcondition, we would have
    said nothing about the output value [r] produced by a call [example_let].
    Instead, we would like to specify that the result [r] is equal to [2*n].
    To that end, we write the postcondition [fun r => \[r = 2*n]], which
    actually stands for [fun (r:val) => [r = val_int (2*n)], where the
    coercion [val_int] translates the integer value [2*n] into the
    corresponding value of type [val] from the programming language. *)

Lemma triple_example_let : forall (n:int),
  triple (example_let n)
    \[]
    (fun r => \[r = 2*n]).

(** The verification proof script is very similar to the previous one.
    The x-tactics [xapp] performs symbolic execution of the code.
    Ultimately, we need to check that the expression computed,
    [(n + 1) + (n - 1)], is equal to the specified result, that is, [2*n].
    We exploit the TLC tactics [math] to prove this mathematical result. *)

Proof using.
  xwp. xapp. xapp. xapp. xsimpl. math.
Qed.


(* ########################################################### *)
(** ** Exercise: function [quadruple] *)

(** Consider the function [quadruple], which expects an integer [n]
    and returns its quadruple, that is, the value [4*n].

[[
    let quadruple n =
      n + n + n + n
]]
*)

Definition quadruple : val :=
  Fun 'n :=
    Let 'm := 'n '+ 'n in
    'm '+ 'm.

(* EX1! (triple_quadruple) *)
(** Specify and verify the function [quadruple] to express that
    it returns [4*n].
    Hint: follow the template of [triple_example_let]. *)

(* SOLUTION *)
Lemma triple_quadruple : forall (n:int),
  triple (quadruple n)
    \[]
    (fun r => \[r = 4 * n]).
Proof using.
  xwp. xapp. xapp. xsimpl. math.
Qed.
(* /SOLUTION *)

(** [] *)


(* ########################################################### *)
(** ** Exercise: function [inplace_double] *)

(** Consider the function [inplace_double], which expects a reference
    on an integer, reads twice in that reference, then updates the
    reference with the sum of the two values that were read.

[[
    let inplace_double p =
      let n = !p in
      let m = n + n in
      p := m
]]
*)

Definition inplace_double : val :=
  Fun 'p :=
    Let 'n := '!'p in
    Let 'm := 'n '+ 'n in
    'p ':= 'm.

(* EX1! (triple_inplace_double) *)
(** Specify and verify the function [inplace_double].
    Hint: follow the template of [triple_incr]. *)

(* SOLUTION *)
Lemma triple_inplace_double : forall (p:loc) (n:int),
  triple (inplace_double p)
    (p ~~> n)
    (fun _ => p ~~> (2*n)).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl. math.
Qed.
(* /SOLUTION *)

(** [] *)


(* ########################################################### *)
(** ** Increment of two references *)

(** Consider the following function, which expects the addresses
    of two reference cells, and increments both of them.

[[
    let incr_two p q =
      incr p;
      incr q
]]
*)

Definition incr_two : val :=
  Fun 'p 'q :=
    incr 'p ';
    incr 'q.

(** The specification of this function takes the form
    [triple (incr_two p q) H (fun _ => H')],
    where [r] denotes the result value of type unit.

    The precondition describes two references cells: [p ~~> n]
    and [q ~~> m]. To assert that the two cells are distinct from
    each other, we separate their description with the operator [\*].
    This operator called "separating conjunction" in Separation Logic,
    and is also known as the "star" operator. Thus, the precondition
    is [(p ~~> n) \* (q ~~> m)], or simply [p ~~> n \* q ~~> m].

    The postcondition describes the final state as
    is [p ~~> (n+1) \* q ~~> (m+1)], where the contents of both
    cells is increased by one unit compared with the precondition.

    The specification triple for [incr_two] is thus as follows. *)

Lemma triple_incr_two : forall (p q:loc) (n m:int),
  triple (incr_two p q)
    (p ~~> n \* q ~~> m)
    (fun _ => p ~~> (n+1) \* q ~~> (m+1)).

(** The verification proof follows the usual pattern. *)

Proof using.
  xwp. xapp. xapp. xsimpl.
Qed.

(** We register the specification [triple_incr_two] in the
    database, to enable reasoning about calls to [incr_two]. *)

Hint Resolve triple_incr_two : triple.


(* ########################################################### *)
(** ** Aliased arguments *)

(** The specification [triple_incr_two] correctly describes calls to the
    function [incr_two] when providing it with two distinct reference cells.
    Yet, it says nothing about a call of the form [incr_two p p].

    Indeed, in Separation Logic, a state described by [p ~~> n] cannot
    be matched against a state described by [p ~~> n \* p ~~> n], because
    the star operator requires its operand to correspond to disjoint pieces
    of state.

    What happens if we nevertheless try to exploit [triple_incr_two]
    to reason about a call of the form [incr_two p p], that is, with
    aliased arguments?

    Let's find out, by considering the operation [aliased_call p],
    which does execute such a call. *)

Definition aliased_call : val :=
  Fun 'p :=
    incr_two 'p 'p.

(** A call to [aliased_call p] should increase the contents of [p] by [2].
    This property can be specified as follows. *)

Lemma triple_aliased_call : forall (p:loc) (n:int),
  triple (aliased_call p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).

(** If we attempt the proof, we get stuck. Observe how [xapp] reports its
    failure to make progress. *)

Proof using.
  xwp. xapp.
Abort.

(** In the above proof, we get stuck with a proof obligation of the form:
    [\[] ==> (p ~~> ?m) \* _], which requires showing that
    from an empty state one can extract a reference [p ~~> ?m]
    for some integer [?m].

    What happened is that when matching the current state [p ~~> n]
    against [p ~~> ?n \* p ~~> ?m] (which corresponds to the precondition
    of [triple_incr_two] with [q = p]), the internal simplification tactic
    was able to cancel out [p ~~> n] in both expressions, but then got
    stuck with matching the empty state against [p ~~> ?m]. *)

(** The issue here is that the specification [triple_incr_two] is
    specialized for the case of non-aliased references.

    It is possible to state and prove an alternative specification for
    the function [incr_two], to cover the case of aliased arguments.
    Its precondition mentions only one reference, [p ~~> n], and its
    postcondition asserts that its contents gets increased by two units.

    This alternative specification can be stated and proved as follows. *)

Lemma triple_incr_two_aliased : forall (p:loc) (n:int),
  triple (incr_two p p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp. xapp. xapp. xsimpl. math.
Qed.

(** By exploiting the alternative specification, we are able to verify
    the specification of [aliased_call p], which invokes [incr_two p p].
    In order to indicate to the [xapp] tactic that it should invoke the
    lemma [triple_incr_two_aliased] and not [triple_incr_two], we provide that
    lemma as argument to [xapp], by writing [xapp triple_incr_two_aliased]. *)

Lemma triple_aliased_call : forall (p:loc) (n:int),
  triple (aliased_call p)
    (p ~~> n)
    (fun _ => p ~~> (n+2)).
Proof using.
  xwp. xapp triple_incr_two_aliased. xsimpl.
Qed.


(* ########################################################### *)
(** ** A function that takes two references, and increments one *)

(** Consider the following function, which expects the addresses
    of two reference cells, and increments only the first one.

[[
    let incr_first p q =
      incr p
]]
*)

Definition incr_first : val :=
  Fun 'p 'q :=
    incr 'p.

(** We can specify this function by describing its input state
    as [p ~~> n \* q ~~> m], and describing its output state
    as [p ~~> (n+1) \* q ~~> m]. Formally: *)

Lemma triple_incr_first : forall (p q:loc) (n m:int),
  triple (incr_first p q)
    (p ~~> n \* q ~~> m)
    (fun _ => p ~~> (n+1) \* q ~~> m).
Proof using.
  xwp. xapp. xsimpl.
Qed.

(** Observe, however, that the second reference plays absolutely
    no role in the execution of the function. In fact, we might
    equally well have described in the specification only the
    existence of the reference that the code manipulates. *)

Lemma triple_incr_first' : forall (p q:loc) (n:int),
  triple (incr_first p q)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  xwp. xapp. xsimpl.
Qed.

(** Interestingly, the specification [triple_incr_first], which
    mentions the two references, is derivable from the specification
    [triple_incr_first'], which mentions only the first reference.

    The corresponding proof appears next. It leverages the tactic
    [xtriple], which turns a specification triple of the form
    [triple t H Q] into the form [PRE H CODE t POST Q], thereby
    enabling this proof obligation to be processed by [xapp].

    Here, we invoke the tactic [xapp triple_incr_first'], to
    exploit the specification [triple_incr_first']. *)

Lemma triple_incr_first_derived : forall (p q:loc) (n m:int),
  triple (incr_first p q)
    (p ~~> n \* q ~~> m)
    (fun _ => p ~~> (n+1) \* q ~~> m).
Proof using.
  xtriple. xapp triple_incr_first'. xsimpl.
Qed.

(** More generally, in Separation Logic, if a specification triple holds,
    then this specification triple remains valid by adding a same heap
    predicate in both the precondition and the postcondition. This is the
    "frame" principle, a key modularity feature that we'll come back to
    later on in the course. *)


(* ########################################################### *)
(** ** Exercise: transfer from one reference to another *)

(** Consider the [transfer] function, whose code appears below.

[[
    let transfer p q =
      p := !p + !q;
      q := 0
]]
*)

Definition transfer : val :=
  Fun 'p 'q :=
   Let 'n := '!'p in
   Let 'm := '!'q in
   Let 's := 'n '+ 'm in
   'p ':= 's ';
   'q ':= 0.

(* EX1! (triple_transfer) *)
(** State and prove a lemma called [triple_transfer] specifying
    the behavior of [transfer p q] covering the case where [p]
    and [q] denote two distinct references. *)

(* SOLUTION *)
Lemma triple_transfer : forall (p q:loc) (n m:int),
  triple (transfer p q)
    (p ~~> n \* q ~~> m)
    (fun _ => p ~~> (n + m) \* q ~~> 0).
Proof using.
  xwp. xapp. xapp. xapp. xapp. xapp. xsimpl.
Qed.
(* /SOLUTION *)

(** [] *)

(* EX1! (triple_transfer_aliased) *)
(** State and prove a lemma called [triple_transfer_aliased] specifying
    the behavior of [transfer] when it is applied twice to the same
    argument. It should take the form [triple (transfer p p) H Q]. *)

(* SOLUTION *)
Lemma triple_transfer_aliased : forall (p:loc) (n:int),
  triple (transfer p p)
    (p ~~> n)
    (fun _ => p ~~> 0).
Proof using.
  xwp. xapp. xapp. xapp. xapp. xapp. xsimpl.
Qed.
(* /SOLUTION *)

(** [] *)


(* ########################################################### *)
(** ** Specification of allocation *)

(** Consider the operation [ref v], which allocates a memory cell with
    contents [v]. How can we specify this operation using a triple?

    The precondition of this triple should be the empty heap predicate,
    written [\[]], because the allocation can execute in an empty state.

    The postcondition should assert that the output value is a pointer
    [p], such that the final state is described by [p ~~> v].

    It would be tempting to write the postcondition [fun p => p ~~> v].
    Yet, the triple would be ill-typed, because the postcondition of a
    triple must be of type [val->hprop], and [p] is an address of type [loc].

    Instead, we need to write the postcondition in the form [fun (r:val) => H'],
    where [r] denotes the result value, and somehow we need to assert
    that [r] is a value of the form [val_loc p], for some location [p],
    where [val_loc] is the constructor that injects locations into the
    grammar of program values.

    To formally quantify the variable, we use an existential quantifier
    for heap predicates, written [\exists]. The correct postcondition for
    [ref v] is [fun (r:val) => \exists (p:loc), \[r = val_loc p] \* (p ~~> v)].

    The complete statement of the specification appears below. Note that the
    primitive operation [ref v] is written ['ref v] in the Coq syntax. *)

Parameter triple_ref : forall (v:val),
  triple ('ref v)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* p ~~> v).

(** The pattern [fun r => \exists p, \[r = val_loc p] \* H)] occurs
    whenever a function returns a pointer. Thus, this pattern appears
    pervasively. To improve conciseness, we introduce a specific
    notation for this pattern, shortening it to [funloc p => H]. *)

Notation "'funloc' p '=>' H" :=
  (fun r => \exists p, \[r = val_loc p] \* H)
  (at level 200, p ident, format "'funloc'  p  '=>'  H").

(** Using this notation, the specification [triple_ref] can be reformulated
    more concisely, as follows. *)

Parameter triple_ref' : forall (v:val),
  triple ('ref v)
    \[]
    (funloc p => p ~~> v).

(** Remark: the CFML tool features a technique that generalizes the
    notation [funloc] to all return types, by leveraging type-classes.
    Yet, the use of type-classes involves a number of technicalities
    that we wish to avoid in this course. For that reason, we employ only
    the [funloc] notation, and use existential quantifiers explicitly
    for other types. *)


(* ########################################################### *)
(** ** Exercise: allocate a reference with greater contents *)

(** Consider the following function, which takes as argument the
    address [p] of a memory cell with contents [n], allocates a
    fresh memory cell with contents [n+1], then returns the address
    of that fresh cell.

[[
    let ref_greater p =
      let n = !p in
      let m = n + 1 in
      ref m
]]
*)

Definition ref_greater : val :=
  Fun 'p :=
    Let 'n := '!'p in
    Let 'm := 'n '+ 1 in
    'ref 'm.

(** The precondition of [ref_greater] asserts the existence of a cell
    [p ~~> n]. The postcondition of [ref_greater] asserts the existence
    of two cells, [p ~~> n] and [q ~~> (n+1)], where [q] denotes the
    location returned by the function. The postcondition is thus written
    [funloc q => p ~~> n \* q ~~> (n+1)], which is a shorthand for
    [fun (r:val) => \exists (q:loc), \[r = val_loc q] \* p ~~> n \* q ~~> (n+1)].

    The complete specification of [ref_greater] is thus as follows. *)

Lemma triple_ref_greater : forall (p:loc) (n:int),
  triple (ref_greater p)
    (p ~~> n)
    (funloc q => p ~~> n \* q ~~> (n+1)).
Proof using.
  xwp. xapp. xapp. xapp. intros q. xsimpl. auto.
Qed.

(** [] *)

(* EX2! (triple_ref_greater_abstract) *)
(** State another specification for the function [ref_greater],
    called [triple_ref_greater_abstract], with a postcondition that
    does not reveal the contents of the freshly reference [q], but
    instead only asserts that its contents is greater than the contents
    of [p]. To that end, introduce in the postcondition an existentially-
    quantified variable called [m], and specified to satisfy [m > n].

    Then, derive the new specification from the former one, following
    the proof pattern employed in the proof of [triple_incr_first_derived]. *)

(* SOLUTION *)
Lemma triple_ref_greater_abstract : forall (p:loc) (n:int),
  triple (ref_greater p)
    (p ~~> n)
    (funloc q => \exists m, \[m > n] \* q ~~> m \* p ~~> n).
Proof using.
  xtriple. xapp triple_ref_greater. xsimpl. { auto. } { math. }
Qed.
(* /SOLUTION *)

(** [] *)


(* ########################################################### *)
(** ** Deallocation in Separation Logic *)

(** Separation Logic tracks allocated data. In its simplest form,
    Separation Logic enforces that all allocated data be eventually
    deallocated. Technically, the logic is said to "linear" as opposed
    to "affine". *)

(** Let us illustrate what happens if we forget to deallocate a reference.

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
  Fun 'n :=
    Let 'p := 'ref 'n in
    incr 'p ';
    '! 'p.

(** The operation [succ_using_incr_attempt n] admits an empty
    precondition, and a postcondition asserting that the final
    result is [n+1]. Yet, if we try to prove this specification,
    we get stuck. *)

Lemma triple_succ_using_incr_attempt : forall (n:int),
  triple (succ_using_incr_attempt n)
    \[]
    (fun r => \[r = n+1]).
Proof using.
  xwp. xapp. intros p. xapp. xapp. xsimpl. { auto. }
Abort.

(** In the above proof script, we get stuck with the entailment
    [p ~~> (n+1) ==> \[]], which indicates that the current state contains
    a reference, whereas the postcondition describes an empty state. *)

(** We could attempt to patch the specification to account for the left-over
    reference. This yields a provable specification. *)

Lemma triple_succ_using_incr_attempt' : forall (n:int),
  triple (succ_using_incr_attempt n)
    \[]
    (fun r => \[r = n+1] \* \exists p, (p ~~> (n+1))).
Proof using.
  xwp. xapp. intros p. xapp. xapp. xsimpl. { auto. }
Qed.

(** While the above specification is provable, it is not quite usable.

    Indeed, the above specification features a piece of postcondition
    [\exists p, p ~~> (n+1)] that is of absolutely no use to the caller
    of the function. Worse, the caller will have its state polluted with
    [\exists p, p ~~> (n+1)] and will have no way to get rid of it apart
    from returning it into its own postcondition. *)

(** The right solution is to patch the code, to free the reference once
    it is no longer needed, as shown below. We assume the source language
    to include a deallocation operation written [free p]. This operation
    does not exist in OCaml, but let us nevertheless continue using OCaml
    syntax for writing programs.

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
  Fun 'n :=
    Let 'p := 'ref 'n in
    incr 'p ';
    Let 'x := '! 'p in
    'free 'p ';
    'x.

(** This program may now be proved correct with respect to the intended
    specification. Observe in particular the last call to [xapp] below,
    which corresponds to the [free] operation.

    The final result is the value of the variable [x]. To reason about it,
    we exploit the tactic [xval], as illustrated below. *)

Lemma triple_succ_using_incr : forall n,
  triple (succ_using_incr n)
    \[]
    (fun r => \[r = n+1]).
Proof using.
  xwp. xapp. intros p. xapp. xapp. xapp. xval. xsimpl. auto.
Qed.

(** Remark: if we verify programs written in a language equipped with
    a garbage collector (like, e.g., OCaml), we need to tweak the
    Separation Logic to account for the fact that some heap predicates
    can be freely discarded from postconditions. This variant of
    Separation Logic will be described in the chapter [SLFAffine]. *)


(* ########################################################### *)
(** ** Axiomatization of the mathematical factorial function *)

(** Our next example consists of a program that evaluates the factorial
    function. To specify this function, we consider a Coq axiomatization
    of the mathematical factorial function, named [facto]. *)

Parameter facto : int -> int.

Parameter facto_init : forall n,
  0 <= n <= 1 ->
  facto n = 1.

Parameter facto_step : forall n,
  n > 1 ->
  facto n = n * (facto (n-1)).

(** Note that, throught this axiomatization, we purposely do not specify
    the value of [facto] on negative arguments. *)


(* ########################################################### *)
(** ** A partial recursive function, without state *)

(** In the rest of the chapter, we consider recursive functions that
     manipulate the state. To gently introduce the necessary techniques
    for reasoning about recursive functions, we first consider a recursive
    function that does not involve any mutable state.

    The function [factorec] computes the factorial of its argument.

[[
    let rec factorec n =
      if n <= 1 then 1 else n * factorec (n-1)
]]

    The corresonding code in A-normal form is slightly more verbose.
*)

Definition factorec : val :=
  Fix 'f 'n :=
    Let 'b := 'n '<= 1 in
    If_ 'b
      Then 1
      Else Let 'x := 'n '- 1 in
           Let 'y := 'f 'x in
           'n '* 'y.

(** A call [factorec n] can be specified as follows:

    - the initial state is empty,
    - the final state is empty,
    - the result value [r] is such that [r = facto n], when [n >= 0].

    In case the argument is negative (i.e., [n < 0]), we have two choices:

    - either we explicitly specify that the result is [1] in this case,
    - or we rule out this possibility by requiring [n >= 0].

    Let us follow the second approach, in order to illustrate the
    specification of partial functions.

    There are two possibilities for expressing the constraint [n >= 0]:

    - either we use as precondition [\[n >= 0]],
    - or we place an assumption [(n >= 0) -> _] to the front of the triple,
      and use an empty precondition, that is, [\[]].

    The two presentations are totally equivalent. By convention, we follow
    the second presentation, which tends to improve both the readability of
    specifications and the conciseness of proof scripts.

    The specification of [factorec] is thus stated as follows. *)

Lemma triple_factorec : forall n,
  n >= 0 ->
  triple (factorec n)
    \[]
    (fun r => \[r = facto n]).

(** We next go through the proof script in details, to explain in particular
    how to set up the induction, how to reason about the recursive call,
    and how to deal with the precondition [n >= 0]. *)

Proof using.
  (* We set up a proof by induction on [n] to obtain an induction
     hypothesis for the recursive calls. Recursive calls are made
     each time on smaller values, and the last recursive call is
     made on [n = 1]. The well-founded relation [downto 1] captures
     this recursion pattern. The tactic [induction_wf] is provided
     by the TLC library to assist in setting up well-founded inductions.
     It is exploited as follows. *)
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

(** Let's revisit the proof script without comments, to get a global
    picture of the proof structure. *)

Lemma triple_factorec' : forall n,
  n >= 0 ->
  triple (factorec n)
    \[]
    (fun r => \[r = facto n]).
Proof using.
  intros n. induction_wf IH: (downto 1) n. unfold downto in IH.
  intros Hn. xwp. xapp. xif; intros C.
  { xval. xsimpl. rewrite facto_init; math. }
  { xapp. xapp. { math. } { math. } xapp. xsimpl.
    rewrite (@facto_step n); math. }
Qed.


(* ########################################################### *)
(** ** A recursive function with state *)

(** The example of [factorec] was a warmup. Let's now tackle a recursive
    function involving mutable state.

    The function [repeat_incr p m] makes [m] times a call to [incr p].
    Here, [m] is assumed to be a nonnegative value.

[[
    let rec repeat_incr p m =
      if m > 0 then (
        incr p;
        repeat_incr p (m - 1)
      )
]]
*)

Definition repeat_incr : val :=
  Fix 'f 'p 'm :=
    Let 'b := 'm '> 0 in
    If_ 'b Then
      incr 'p ';
      Let 'x := 'm '- 1 in
      'f 'p 'x
    End.

(** The specification for [repeat_incr p] requires that the initial
    state contains a reference [p] with some integer contents [n],
    that is, [p ~~> n]. Its postcondition asserts that the resulting
    state is [p ~~> (n+m)], which is the result after incrementing
    [m] times the reference [p]. Observe that this postcondition is
    only valid under the assumption that [m >= 0]. *)

Lemma triple_repeat_incr : forall (m n:int) (p:loc),
  m >= 0 ->
  triple (repeat_incr p m)
    (p ~~> n)
    (fun _ => p ~~> (n + m)).

(* EX2! (triple_repeat_incr) *)
(** Prove the function [triple_repeat_incr].
    Hint: the structure of the proof resembles that of [triple_factorec']. *)

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

Lemma triple_repeat_incr' : forall (p:loc) (n m:int),
  m >= 0 ->
  triple (repeat_incr p m)
    (p ~~> n)
    (fun _ => p ~~> (n + m)).
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


(* ########################################################### *)
(** ** Trying to prove incorrect specifications *)

(** We established for [repeat_incr p n] a specification with the constraint
    [m >= 0]. What if did omit it? Where would we get stuck in the proof?

    Clearly, something should break in the proof, because when [m < 0],
    the call [repeat_incr p m] terminates immediately. Thus, when [m < 0]
    the final state is like the initial state [p ~~> n], and not equal
    to [p ~~> (n + m)]. Let us investigate how the proof breaks. *)

Lemma triple_repeat_incr_incorrect : forall (p:loc) (n m:int),
  triple (repeat_incr p m)
    (p ~~> n)
    (fun _ => p ~~> (n + m)).
Proof using.
  intros. revert n. induction_wf IH: (downto 0) m. unfold downto in IH.
  intros. xwp. xapp. xif; intros C.
  { (* In the 'then' branch: [m > 0] *)
    xapp. xapp. xapp. { math. } xsimpl. math. }
  { (* In the 'else' branch: [m <= 0] *)
    xval.
    (* Here, we are requested to justify that the current state
       [p ~~> n] matches the postcondition [p ~~> (n + m)], which
       amounts to proving [n = n + m]. *)
    xsimpl.
    (* When the specification features the assumption [m >= 0],
       we can prove this equality because the fact that we are
       in the else branch means that [m <= 0], thus [m = 0].
       However, without the assumption [m >= 0], the value of
       [m] could very well be negative. *)
Abort.

(** Note that there exists a valid specification for [repeat_incr] that
    does not constraint [m], but instead specifies that the state
    always evolves from [p ~~> n] to [p ~~> (n + max 0 m)]. *)

(** The proof scripts exploits two properties of the [max] function. *)

Lemma max_l : forall n m,
  n >= m ->
  max n m = n.
Proof using. introv M. unfold max. case_if; math. Qed.

Lemma max_r : forall n m,
  n <= m ->
  max n m = m.
Proof using. introv M. unfold max. case_if; math. Qed.

(** Let's prove most-general specification for the function [repeat_incr]. *)

Lemma triple_repeat_incr' : forall (p:loc) (n m:int),
  triple (repeat_incr p m)
    (p ~~> n)
    (fun _ => p ~~> (n + max 0 m)).
Proof using.
  intros. gen n. induction_wf IH: (downto 0) m.
  xwp. xapp. xif; intros C.
  { xapp. xapp. xapp. { math. }
    xsimpl. repeat rewrite max_r; math. }
  { xval. xsimpl. rewrite max_l; math. }
Qed.


(* ########################################################### *)
(** ** A recursive function involving two references *)

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
  Fix 'f 'p 'q :=
    Let 'm := '!'q in
    Let 'b := 'm '> 0 in
    If_ 'b Then
      incr 'p ';
      decr 'q ';
      'f 'p 'q
    End.

(** The specification of [step_transfer] is essentially the same as
    that of the function [transfer] presented previously, with the
    only difference that we here assume the contents of [q] to be
    nonnegative. *)

Lemma triple_step_transfer : forall p q n m,
  m >= 0 ->
  triple (step_transfer p q)
    (p ~~> n \* q ~~> m)
    (fun _ => p ~~> (n + m) \* q ~~> 0).

(* EX2! (triple_step_transfer) *)
(** Verify the function [step_transfer].
    Hint: to set up the induction, follow the pattern shown in
    the proof of [triple_repeat_incr']. *)

Proof using. (* ADMITTED *)
  intros q p n m Hm.
  revert n Hm. induction_wf IH: (downto 0) m. unfold downto in IH.
  intros. xwp. xapp. xapp. xif; intros C.
  { xapp. xapp. xapp. { math. } { math. } xsimpl. math. }
  { xval. xsimpl. { math. } { math. } }
Qed. (* /ADMITTED *)

(** [] *)


(* ########################################################### *)
(** ** Formalization of the list representation predicate *)

(** This section assumes a language with records, allocated as blocks
    of consecutive cells. *)

Module ExampleLists.

(** A mutable list cell is a two-cell record, featuring a head field and a
    tail field. We define the field indices as follows. *)

Definition head : field := 0%nat.
Definition tail : field := 1%nat.

(** The heap predicate [p ~~~>`{ head := x; tail := q}] describes a
    record allocated at location [p], with a head field storing [x]
    and a tail field storing [q]. *)

(** A mutable list consists of a chain of cells, terminated by [null].

    The heap predicate [MList L p] describes a list whose head cell is
    at location [p], and whose elements are described by the list [L].

    This predicate is defined recursively on the structure of [L]:

    - if [L] is empty, then [p] is the null pointer,
    - if [L] is of the form [x::L'], then [p] is not null, and the
      head field of [p] contains [x], and the tail field of [p]
      contains a pointer [q] such that [MList L' q] describes the
      tail of the list.

*)

Fixpoint MList (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists q, (p ~~~>`{ head := x; tail := q}) \* (MList L' q)
  end.

(** The following reformulations of the definition are helpful in proofs,
    allowing to fold or unfold the definition using a tactic called
    [xchange]. *)

Lemma MList_nil : forall p,
  (MList nil p) = \[p = null].
Proof using. auto. Qed.

Lemma MList_cons : forall p x L',
  MList (x::L') p =
  \exists q, (p ~~~>`{ head := x; tail := q}) \* (MList L' q).
Proof using.  auto. Qed.

(** Another characterization of [MList L p] is useful for proofs. Whereas
    the original definition is by case analysis on whether [L] is empty,
    the alternative one is by case analysis on whether [p] is null:

    - if [p] is null, then [L] is empty,
    - otherwise, [L] decomposes as [x::L'], the head field of [p] contains [x],
      and the tail field of [p] contains a pointer [q] such that [MList L' q]
      describes the tail of the list.

    The lemma below is stated using an entailment. The reciprocal entailment
    is also true, but we do not need it so we do not bother proving it here.
*)

Lemma MList_if : forall (p:loc) (L:list val),
      (MList L p)
  ==> (If p = null
        then \[L = nil]
        else \exists x q L', \[L = x::L']
             \* (p ~~~>`{ head := x; tail := q}) \* (MList L' q)).
Proof using.
  (* Let's prove this result by case analysis on [L]. *)
  intros. destruct L as [|x L'].
  { (* Case [L = nil]. By definition of [MList], we have [p = null]. *)
    xchange MList_nil. intros M.
    (* We have to justify [L = nil], which is trivial.
       The TLC [case_if] tactic performs a case analysis on the argument
       of the first visible [if] conditional. *)
    case_if. xsimpl. auto. }
  { (* Case [L = x::L']. *)
  (* One possibility is to perform a rewrite operation using [MList_cons]
     on its first occurrence. Then using CFML the tactic [xpull] to extract
     the existential quantifiers out from the precondition:
     [rewrite MList_cons. xpull. intros q.]
     A more efficient approach is to use the dedicated CFML tactic [xchange],
     which is specialized for performing updates in the current state. *)
    xchange MList_cons. intros q.
    (* Because a record is allocated at location [p], the pointer [p]
       cannot be null. The lemma [hrecord_not_null] allows us to exploit
       this property, extracting the hypothesis [p <> null]. We use again
       the tactic [case_if] to simplify the case analysis. *)
    xchange hrecord_not_null. intros N. case_if.
    (* To conclude, it suffices to correctly instantiate the existential
       quantifiers. The tactic [xsimpl] is able to guess the appropriate
       instantiations. *)
     xsimpl. auto. }
Qed.

Opaque MList.


(* ########################################################### *)
(** ** In-place concatenation of two mutable lists *)

(** The function [append] shown below expects a nonempty list [p1] and a list
    [p2], and updates [p1] in place so that its tail gets extended by the
    cells from [p2].

[[
    let rec append p1 p2 =
      if p1.tail == null
        then p1.tail <- p2
        else append p1.tail p2
]]

*)

Definition append : val :=
  Fix 'f 'p1 'p2 :=
    Let 'q1 := 'p1'.tail in
    Let 'b := ('q1 '= null) in
    If_ 'b
      Then Set 'p1'.tail ':= 'p2
      Else 'f 'q1 'p2.

(** The append function is specified and verified as follows. The proof
    pattern is representative of that of many list-manipulating functions,
    so it is essential to follow through every step of that proof. *)

Lemma Triple_append : forall (L1 L2:list val) (p1 p2:loc),
  p1 <> null ->
  triple (append p1 p2)
    (MList L1 p1 \* MList L2 p2)
    (fun _ => MList (L1++L2) p1).
Proof using.
  (* The induction principle provides an hypothesis for the tail of [L1],
      i.e., for the list [L1'] such that the relation [list_sub L1' L1] holds. *)
  introv K. gen p1. induction_wf IH: (@list_sub val) L1. introv N. xwp.
  (* To begin the proof, we reveal the head cell of [p1].
     We let [q1] denote the tail of [p1], and [L1'] the tail of [L1]. *)
  xchange (MList_if p1). case_if. xpull. intros x q1 L1' ->.
  (* We then reason about the case analysis. *)
  xapp. xapp. xif; intros Cq1.
  { (* If [q1'] is null, then [L1'] is empty. *)
    xchange (MList_if q1). case_if. xpull. intros ->.
    (* In this case, we set the pointer, then we fold back the head cell. *)
    xapp. xchange <- MList_cons. }
  { (* If [q1'] is not null, we reason about the recursive call using
       the induction hypothesis, then we fold back the head cell. *)
    xapp. xchange <- MList_cons. }
Qed.



(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Additional contents *)

(* ####################################################### *)
(** ** Smart constructors for linked lists *)

Implicit Types x : val.

(** This section introduces two smart constructors for linked lists,
    called [mnil] and [mcons].

    The operation [mnil()] is intended to create an empty list.
    Its implementation simply returns the value [null]. Its
    specification asserts that the return value is a pointer [p]
    such that [MList nil p] holds.

[[
    let rec mnil () =
      null
]]
*)

Definition mnil : val :=
  Fun 'u :=
    null.

Lemma triple_mnil :
  triple (mnil '())
    \[]
    (funloc p => MList nil p).
Proof using. xwp. xval. xchanges* <- (MList_nil null). Qed.

Hint Resolve triple_mnil : triple.

(** Observe that the specification [triple_mnil] does not mention
    the [null] pointer anywhere. This specification may thus be
    used to specify the behavior of operations on mutable lists
    without having to reveal low-level implementation details that
    involve the [null] pointer. *)

(** The operation [mcons x q] is intended to allocate a fresh list cell,
    with [x] in the head field and [q] in the tail field. The implementation
    of this operation allocates and initializes a fresh record made of
    two fields, using an operation called [val_new_hrecord_2], which we
    here view as a primitive. The chapter [SLFStruct] describes an encoding
    of this function in terms of the allocation and write operations. *)

Definition mcons : val :=
  val_new_hrecord_2 head tail.

(** The operation [mcons] admits two specifications: one that describes only
    the fresh record allocated, and one that combines it with a list
    representation of the form [Mlist q L] to produce as postcondition
    an extended list of the form [Mlist p (x::L)].

    The first specification is as follows. *)

Lemma triple_mcons : forall x q,
  triple (mcons x q)
    \[]
    (funloc p => p ~~~> `{ head := x ; tail := q }).
Proof using. intros. applys* triple_new_hrecord_2. Qed.

(** The second specification is derived from the first. *)

Lemma triple_mcons' : forall L x q,
  triple (mcons x q)
    (MList L q)
    (funloc p => MList (x::L) p).
Proof using.
  intros. xtriple. xapp triple_mcons.
  intros p. xchange <- MList_cons. xsimpl*.
Qed.

Hint Resolve triple_mcons' : triple.


(* ####################################################### *)
(** ** Copy function for lists *)

(** The function [mcopy] takes a mutable linked list and builds
    an independent copy of it.

    This program illustrates the use the of functions [mnil] and
    [mcons].

[[
    let rec mcopy p =
      if p == null
        then mnil ()
        else mcons (p.head) (mcopy p.tail)
]]
*)

Definition mcopy : val :=
  Fix 'f 'p :=
    Let 'b := ('p '= null) in
    If_ 'b
      Then mnil '()
      Else
        Let 'x := 'p'.head in
        Let 'q := 'p'.tail in
        Let 'q2 := 'f 'q in
        mcons 'x 'q2.

(** The precondition of [mcopy] requires a linked list [MList L p].
    Its postcondition asserts that the function returns a pointer [p']
    and a list [MList L p'], in addition to the original list [MList L p].
    The two lists are totally disjoint and independent, as captured by
    the separating conjunction symbol (the star). *)

Lemma triple_mcopy : forall L p,
  triple (mcopy p)
    (MList L p)
    (funloc p' => (MList L p) \* (MList L p')).

(** The proof script is very similar in structure to the previous ones.
    While playing the script, try to spot the places where:

    - [mnil] produces an empty list of the form [MList nil p'],
    - the recursive call produces a list of the form [MList L' q'],
    - [mcons] produces a list of the form [MList (x::L') p'].

*)

Proof using.
  intros. gen p. induction_wf IH: list_sub L.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros ->. xapp. xsimpl*. subst. xchange* <- MList_nil. }
  { intros x q L' ->. xapp. xapp. xapp. intros q'.
    xapp. intros p'. xchange <- MList_cons. xsimpl*. }
Qed.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Bonus contents (optional reading) *)

(* ########################################################### *)
(** ** A continuation-passing style in-place concatenation function *)

(** The following program was proposed in the original article on
    Separation Logic by John Reynolds as a challenge for verification.

    This function, called [cps_append], is similar to the function [append]
    presented previously: it also performs in-place concatenation of two lists.
    It differs in that it is implemented using a recursive, continuation-passing
    style function to perform the work.

    The presentation of [cps_append p1 p2] is also slightly different: this
    operation returns a pointer [p3] that describes the head of the result
    of the concatenation, and it works even if [p1] corresponds to an empty list.

    The code of [cps_append] involves an auxiliary function [cps_append_aux].
    This code appears at first like a puzzle: it takes a good drawing and several
    minutes to figure out how it works. Observe in particular how the recursive
    call is invoked as part of the continuation. *)

(**
[[
    let rec cps_append_aux p1 p2 k =
      if p1 == null
        then k p2
        else cps_append_aux p1.tail p2 (fun r => (p1.tail <- r); k p1)

    let cps_append p1 p2 =
      aux p1 p2 (fun r => r)
]]
*)

Definition cps_append_aux : val :=
  Fix 'f 'p1 'p2 'k :=
    Let 'b := ('p1 '= null) in
    If_ 'b
      Then 'k 'p2
      Else
        Let 'q1 := 'p1'.tail in
        Let 'k2 := (Fun_ 'r := (Set 'p1'.tail ':= 'r '; 'k 'p1)) in
        'f 'q1 'p2 'k2.

Definition cps_append : val :=
  Fun 'p1 'p2 :=
    Let 'f := (Fun_ 'r := 'r) in
    cps_append_aux 'p1 'p2 'f.

(** Most of the complexity appears in the proof of [cps_append_aux]. *)

Lemma triple_cps_append_aux : forall H Q (L1 L2:list val) (p1 p2:loc) (k:val),
  (forall (p3:loc), triple (k p3) (MList (L1 ++ L2) p3 \* H) Q) ->
  triple (cps_append_aux p1 p2 k)
    (MList L1 p1 \* MList L2 p2 \* H)
    Q.
Proof using.
  introv Hk. gen H p1 p2 L2 k. induction_wf IH: (@list_sub val) L1.
  xwp. xapp. xchange (MList_if p1). xif; intros C; case_if; xpull.
  { intros ->. xapp. xsimpl*. }
  { intros x p1' L1' ->. xapp. xfun. intros f Hf.
    xapp (>> IH (H \* p1 ~~~> `{ head := x ; tail := p1' }) p1').
    { auto. }
    { intros p3. xtriple. xapp. xapp. xapp. xchanges <- MList_cons. }
    { xsimpl. } }
Qed.

Hint Resolve triple_cps_append_aux : triple.

(** The main function [cps_append] simply invokes [cps_append_aux]
    with a trivial continuation. *)

Lemma Triple_cps_append : forall (L1 L2:list val) (p1 p2:loc),
  triple (cps_append p1 p2)
    (MList L1 p1 \* MList L2 p2)
    (funloc p3 => MList (L1++L2) p3).
Proof using.
  xwp. xfun. intros f Hf.
  set (Q := funloc p3 => MList (L1++L2) p3).
  xapp (@triple_cps_append_aux \[] Q).
  { intros p3. xtriple. xapp. xval. unfold Q. xsimpl*. }
  { xsimpl. }
Qed.

(** This concludes the formal verification of Reynolds' verification challenge. *)

End ExampleLists.
