(**

This file provides the Coq definitions associated with a 1-hour talk
that gives an overview of the contents of the course.

The corresponding slides appear in the file [SLFSummary.pdf].

Many definitions from this file are only sketched or assumed without
proofs. All the corresponding definitions are formalized and proofs
in the file [SLFDirect.v]. Detailed explanations may be found
throughout the other course files [SLF*.v], listed in [SLFPreface.v].

Author: Arthur Charguéraud.
License: CC-by.

*)

Set Implicit Arguments.
From Sep Require SLFExtra SLFRules SLFWPgen SLFBasic.
Import SLFDirect.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Motivation for Separation Logic in a proof assistant *)

(** To begin with, please read the section titled "About Separation Logic"
    from the file [SLFPreface.v]. *)


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Formalization of the syntax and semantics of the language *)


(* ########################################################### *)
(** ** Syntax *)

Module Language.

(** We consider a ML-style programming language. Programs are represented as
    terms of type [trm], and terms evaluate to values of type [val].

    Let us describe the grammar of terms and values, which correspond to
    what is called a "deep embedding of the programming language".

    The grammar of values includes:

    - basic values, such as [unit], [bool], or [int],
    - locations, of type [loc], representing memory addresses as natural numbers,
    - (closed) functions (written [fun]), and recursive functions (written [fix]),
    - primitive operations, either for manipulating the memory state, or for
      performing arithmetic operations.

    The grammar of terms includes:

    - closed values (i.e., values without free variables in them),
    - variables, of type [var], represented as [strings],
    - function definitions, which may include free variables in the source code,
    - control structures: conditions, sequence, let-bindings,
    - and function application. *)

Definition var : Type := string.

Definition loc : Type := nat.

Inductive val : Type :=
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_fun : var -> trm -> val
  | val_fix : var -> var -> trm -> val
  | val_ref : val
  | val_get : val
  | val_set : val
  | val_free : val
  | val_add : val

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fun : var -> trm -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_seq : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm.

End Language.


(* ########################################################### *)
(** ** Parsing of concrete programs *)

Module Parsing.
Import SLFExtra SLFBasic SLFProgramSyntax.

(** Consider the following program, which computes the length of a C-style
    mutable list. If the pointer [p] is null, it returns zero, else it
    returns one plus the length of the tail. In pseudo-Caml, this reads:

[[
    let rec mlength p =
      if p == null
        then 0
        else 1 + mlength p.tail
]]

    The corresponding Coq definition using the grammar that we just defined
    is as follows. *)


Definition mlength : val :=
  val_fix "f" "p" (
     trm_if (trm_app (trm_app val_eq (trm_var "p")) (val_loc null))
            (val_int 0)
            (trm_app (trm_app val_add (val_int 1)) (trm_app (trm_var "f")
             (trm_app (val_get_field tail) (trm_var "p"))))).

(** Obviously, we do not wish to manually write programs in this form.

    One possibility is to use an external tool, namely a parser, to read
    the pseudo-code above, and generate the Coq definition.

    Another possibility is to exploit Coq notation and coercions facilities
    for writing the program using an ad-hoc program syntax. For example,
    the syntax that we consider features quote symbols everywhere to
    distinguish between Coq keywords and program keywords, as shown below. *)

Definition mlength' : val :=
  VFix 'f 'p :=
    If_ 'p '= null
      Then 0
      Else 1 '+ 'f ('p'.tail).

(** The result is arguably not very pretty, yet very convenient because it
    enables presenting demos without a dependency on an external parser. *)

End Parsing.


(* ########################################################### *)
(** ** Semantics *)

Module Semantics.
Implicit Types t : trm.
Implicit Types v : val.

(** The semantics of an imperative programming language involves a
    description of a memory state. A memory state is described as a finite
    map location to values. *)

Definition state : Type := fmap loc val.

(** Remark: the file [Fmap.v] provides a formalization of finite maps. *)

(** The capture-avoiding substitution (not shown) is defined in a
    standard way. [subst x v t] replaces all occurrences of the variable
    [x] with the value [v] inside the term [t]. *)

Parameter subst : forall (x:var) (v:val) (t:trm), trm.

(** The big-step evaluation judgement, written [eval s t s' v], asserts
    that from the initial state [s], the evaluation of the term [t]
    terminates in a final state [s'], and produces the result [v]. *)

Inductive eval : state -> trm -> state -> val -> Prop :=

  (** A value evaluates to itself. *)

  | eval_val : forall s v,
      eval s (trm_val v) s v

  (** To evaluate a let-binding [let x = t1 in t2] in a state [s1],
      first evaluate [t1], which produces a state [s2] and a value
      [v1], then evaluate the result of substituting [v1] for [x] in [t2]
      to obtain the final result. *)

  | eval_let : forall s1 s2 s3 x t1 t2 v1 r,
      eval s1 t1 s2 v1 ->
      eval s2 (subst x v1 t2) s3 r ->
      eval s1 (trm_let x t1 t2) s3 r

  (** To evaluate a read operation at a location [l], first check that
      [l] indeed belongs to the domain of the state [s], then return
      the value bound to [l] in the state [s]. *)

  | eval_get : forall s l,
      Fmap.indom s l ->
      eval s (val_get (val_loc l)) s (Fmap.read s l).

  (** ... *)

  (** The other evaluation rules are standard. We omit them here.
     Details may be found in [SLFRules.v]. *)

End Semantics.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Formalization of Separation Logic predicates *)

Module Hprop.
Import SLFDirect.


(* ########################################################### *)
(** ** Core Separation Logic predicates *)

(** Separation Logic predicates are called "heap predicates".
    They are represented by the type [hprop], which is defined as
    predicate over states (technically, over pieces of state). *)

Definition hprop : Type := state -> Prop.

(** Thereafter, we let [H] range over heap predicates, and we let
    [h] range over pieces of state. *)

Implicit Type H : hprop.
Implicit Type h : state.

(** The 5 most important heap predicates are defined next. *)

(** The empty heap predicate, written [\[]], characterizes an empty
    sate. *)

Definition hempty : hprop :=
  fun h => (h = Fmap.empty).

Notation "\[]" := (hempty) (at level 0).

(** The pure heap predicate, written [[\P]], also characterizes an
    empty state, but moreover asserts that the proposition [P] is
    true. We will see example usage of this predicate further on. *)

Definition hpure (P:Prop) : hprop :=
  fun h => (h = Fmap.empty) /\ P.

Notation "\[ P ]" := (hpure P) (at level 0, format "\[ P ]").

(** The singleton heap predicate, written [p ~~> v], characterizes
    a singleton state, that is, a state made of a single memory cell,
    at location [p], and with contents [v]. *)

Definition hsingle (p:loc) (v:val) : hprop :=
  fun h => (h = Fmap.single p v).

Notation "p '~~>' v" := (hsingle p v) (at level 32).

(** The key Separation Logic operator is the star, a.k.a, separating
    conjunction, written [H1 \* H2]. This predicate characterizes a
    heap [h] that decomposes as the union of two disjoints parts:
    one that satisfies [H1], and one that satisfies [H2]. *)

Definition hstar (H1 H2 : hprop) : hprop :=
  fun h => exists h1 h2, H1 h1
                      /\ H2 h2
                      /\ Fmap.disjoint h1 h2
                      /\ h = Fmap.union h1 h2.

Notation "H1 '\*' H2" := (hstar H1 H2) (at level 41, right associativity).

(** Finally, the existential quantifier, written [\exists x, H], lifts
    the existential quantifier on propositions into an existential
    quantifier on predicates. The reader may skip over the technical details
    of the corresponding definition, and simply read [\exists] as the casual
    existential quantifier, simply taking into account that it operates over
    the type [hprop] instead of [Prop]. *)

Definition hexists A (J:A->hprop) : hprop :=
  fun h => exists x, J x h.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'").


(* ########################################################### *)
(** ** Order relation on heap predicates: entailment *)

(** The entailment relation, written [H1 ==> H2], asserts that the heap
    predicate [H2] is weaker than the heap predicate [H1], in the sense
    that any heap [h] satisfying [H1] also satisfies [H2]. *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall h, H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55).

(** The entailment relation defines an order on the set of heap predicates.
    It is reflexive, transitive, and antisymmetric. *)

Parameter himpl_refl : forall H,
  H ==> H.

Parameter himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).

Parameter himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  H1 = H2.

(** The antisymmetry property asserts an equality between two predicates.
    It is a direct consequence of a principle called "predicate
    extensionality", which asserts that if two predicates yields equivalent
    propositions when applied to any argument, then these two predicates
    can be considered equal in the logic. The principle of predicate
    extensionality comes builtin in several proof assistant. In Coq, it may
    be safely added as an axiom. *)

Axiom predicate_extensionality : forall A (P Q:A->Prop),
  (forall x, P x <-> Q x) ->
  P = Q.

(** The ability to write equalities between heap predicates is essential
    to concisely state and efficiently exploit the properties of the
    Separation Logic operators. These properties are presented next. *)


(* ########################################################### *)
(** ** Fundamental properties of the Separation Logic operators *)

(** There are five fundamental properties from which almost every other
    useful properties can be derived. *)

(** (1) The star operator is associative. *)

Parameter hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).

(** (2) The star operator is commutative. *)

Parameter hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.

(** (3) The empty heap predicate is a neutral for the star. *)

Parameter hstar_hempty_l : forall H,
  \[] \* H = H.

(** (4) Existentials can be "extruded" out of stars, that is:
    [(\exists x, H1) \* H2  =  \exists x, (H1 \* H2)].
    when [x] does not occur in [H2]. *)

Parameter hstar_hexists : forall A (J:A->hprop) H,
    (\exists x, J x) \* H
  = \exists x, (J x \* H).

(** (5) The star operator is monotone with respect to entailment.
    This rule can be read as follows: if you have to prove an
    entailment from [H1 \* H2] to [H1' \* H2], you can cancel out
    [H2] on both sides, then there remains to prove that [H1]
    entails [H1']. *)

Parameter himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).

End Hprop.


(* ########################################################### *)
(** ** Description of postconditions *)

Module Qprop.

(** A precondition [H] describes an input state. It has type [state]
    to [Prop]. *)

Implicit Types H : state -> Prop. (* [= hprop] *)

(** A postcondition [Q] describes not just an output state, but also an
    output value. It is thus a binary relation, of type [val] to [state]
    to [Prop]. *)

Implicit Types Q : val -> state -> Prop. (* [= val->hprop] *)

(** It is useful to generalize the star operator and the entailment
    relation to operate over postconditions. *)

(** The operation [Q \*+ H] denotes the extension of a postcondition
    with a heap predicate [H]. *)

Notation "Q \*+ H" := (fun x => (Q x) \* H) (at level 40).

(** The entailment relation [Q1 ===> Q2] denotes the entailment between
    two postconditions, asserting that [Q1 v] entails [Q2 v] for any
    result value [v]. *)

Definition qimpl (Q1 Q2:val->hprop) : Prop :=
  forall (v:val), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55).

(** The generalization of these two operators to postconditions is
    necessary to formally state reasoning rules in a concise way.
    That said, in first approximation, one may read [\*+] as [\*]
    and read [===>] as [==>], to get the intuition for the rules. *)

End Qprop.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Definition of triples, statements and proofs of reasoning rules *)


(* ########################################################### *)
(** ** Triples *)

Module Triple.
Import DemoPrograms.

(** A Hoare triple, written [hoare t H Q], describes the behavior of
    a term [t] using a precondition [H] and a postcondition [Q] that
    describe the whole memory state.

    In total correctness, such a triple asserts that, for any initial
    state [s] satisfying the precondition, there exists a final state
    [s'] and an output value [v] such that the term [t] evaluates to
    [s'] and [v], and such that [v] and [s'] together satisfy the
    postcondition. *)

Definition hoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (s:state), H s ->
  exists (s':state) (v:val), eval s t s' v /\ Q v s'.

(** A Separation Logic triple, written [triple t H Q], describes the
    behavior of a term [t] using a precondition [H] and a postcondition
    [Q] that describe only a fragemnt of the memory state.

    The notion of Separation Logic triple can be derived from that of
    a Hoare triple by quantifying over the "rest of the state", described
    by a heap predicate [H']. This predicate [H'] appears universally
    quantified in the definition shown below. *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), hoare t (H \* H') (Q \*+ H').

(** For example, using a Separation Logic triple, one may specify
    the operation [incr p], with a precondition that describes a
    singleton heap [p ~~> n], and a postcondition that describes
    a result value that we ignore (it is [unit]), and a state
    described by [p ~~> (n+1)]. *)

Parameter triple_incr : forall (p:loc) (n:int),
  triple (incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).

(** To establish Separation Logic triples, the program logic includes
    three kind of rules:

    - structural rules, which do not depend on the programming language,
    - one rule for each language construct,
    - one rule for each primitive operation.

    We next present these three kind of rules. *)

End Triple.


(* ########################################################### *)
(** ** Structural rues*)

Module Rules.

(** The rule of consequence is like in Hoare logic. It asserts that one
    may strengthen the precondition, or weaken the postcondition.

    Observe the use of an entailment between postconditions in the
    third premise. *)

Parameter triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.

(** The frame rule is specific to Separation Logic. It asserts that the
    precondition and the postcondition may be extended using the star
    with an arbitrary heap predicate.

    Observe the use of the star operator for postconditions [\*+] in
    the conclusion. *)

Parameter triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').

(** In addition, two extraction rules are also useful for extracting
    pure facts and existential quantifiers out of preconditions.
    We'll show further on an example use case. *)

Parameter triple_hpure : forall (P:Prop) t H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.

Parameter triple_hexists : forall (A:Type) (J:A->hprop) t Q,
  (forall (x:A), triple t (J x) Q) ->
  triple t (\exists x, J x) Q.


(* ########################################################### *)
(** ** Reasoning rules for terms, e.g., the rule for sequences *)

(** The Hoare logic rule for sequences can be used to establish a
    Hoare triple for a sequence [t1 ; t2]. To apply it, one needs
    to provide a heap predicate [H'] that describes the state between
    the evaluation of [t1] and that of [t2].

[[
      {H} t1 {fun v => H'}     {H'} t2 {Q}
      ------------------------------------
              {H} (t1;t2) {Q}
]]

    Remark: the value [v] below denotes the return value of [t1],
    which is ignored in the semantics.

    The corresponding Coq statement is as follows. *)

Parameter hoare_seq : forall t1 t2 H Q H',
  hoare t1 H (fun v => H') ->
  hoare t2 H' Q ->
  hoare (trm_seq t1 t2) H Q.

(** The Separation Logic rule for sequence admits a similar statement,
    only using the [triple] instead of [hoare]. *)

Parameter triple_seq : forall t1 t2 H Q H',
  triple t1 H (fun v => H') ->
  triple t2 H' Q ->
  triple (trm_seq t1 t2) H Q.

(** The Separation Logic rule can be proved as a direct consequence of
    its Hoare Logic counterpart. *)

(** For every other language construct, we have a reasoning rule in
    Separation Logic that mimics its counterpart in Hoare Logic.
    For details, we refer to [SLFRules.v]. *)


(* ########################################################### *)
(** ** Rules specifying primitive operations *)

Implicit Types p : loc.
Implicit Types v : val.

(** There remains to describe the rules specifying the behavior of the
    primitive operations of the language. We focus here on the primitive
    operations that act on the memory state. *)

(** The read operation assumes a singleton state described by [p ~~> v].
    It produces as result a value [r], specified in the postcondition to
    be equal to [v] by the pure predicate [\[r = v]]. The state remains
    unchanged, as specified by the second part of the postcondition [p ~~> v]. *)

Parameter triple_get : forall v p,
  triple (val_get p)
    (p ~~> v)
    (fun r => \[r = v] \* (p ~~> v)).

(** Consider now a write operation that updates a location [p] with a new
    contents [v]. The precondition, like for a read, requires the location
    [p] to be allocated, with some contents [v'], described by [p ~~> v'].
    The postcondition describes the final state as [p ~~> v], reflecting the
    update to the contents. Note that the postcondition needs not bind a name,
    because the result value is [unit]. *)

Parameter triple_set : forall p v v',
  triple (val_set p v)
    (p ~~> v')
    (fun _ => p ~~> v).

(** Consider the operation that allocates a new cell with contents [v].
    The precondition consists of the empty heap predicate [\[]], reflecting
    the fact that this allocation operation can be executed in an empty state.
    The postcondition asserts that the result value [r] is of the form
    [val_loc p], for some location [p], such that [p ~~> v] describes the
    final state.

    Observe how the location [p] is existentially quantified in the
    postcondition. *)

Parameter triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* p ~~> v).

(** Consider the free operation that deallocates the cell at a location [p].
    The precondition [p ~~> v] asserts that the cell is currently allocated,
    with some contents [v]. The postcondition is empty, reflecting for the
    fact that the cell is no longer accessible. *)

Parameter triple_free : forall p v,
  triple (val_free p)
    (p ~~> v)
    (fun _ => \[]).

End Rules.


(* ########################################################### *)
(** ** Example of a verification proof "by hand" *)

Module ProveIncr.
Import SLFRules SLFProgramSyntax SLFExtra.

(** The rules presented so far suffice to carry out verification proofs.

    To illustrate this claim, consider the increment function, which
    augments by one unit the contents of a cell with integer contents.

    In OCaml syntax, this function is written:

[[
     let incr p =
        let n = !p in
        let m = n+1 in
        p := m
]]

*)

(** The same function can be defined in the embedded language as follows. *)

Definition incr : val :=
  val_fun "p" (
    trm_let "n" (trm_app val_get (trm_var "p")) (
    trm_let "m" (trm_app (trm_app val_add
                             (trm_var "n")) (val_int 1)) (
    trm_app (trm_app val_set (trm_var "p")) (trm_var "m")))).

(** Alternatively, it may be written using notations and coercions. *)

Definition incr' : val :=
  VFun 'p :=
    Let 'n := '! 'p in
    Let 'm := 'n '+ 1 in
    'p ':= 'm.

(** Let us check that the two definitions are indeed equivalent. *)

Lemma incr_eq_incr' : incr = incr'.
Proof using. reflexivity. Qed.

(** The specification of the function [incr] was presented previously,
    as an illustration of a Separation Logic triple. *)

Lemma triple_incr : forall (p:loc) (n:int),
  triple (incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).

(** We next show a detailed proof for this specification. It exploits:

    - the structural reasoning rules,
    - the reasoning rules for terms,
    - the specification of the primitive functions,
    - the [xsimpl] tactic, which provides some degree of automation
      for simplifying entailments.
*)

Proof using.
  intros.
  (* unfold the body of the function *)
  applys triple_app_fun_direct. simpl.
  (* reason about [let n = ..] *)
  applys triple_let.
  (* reason about [!p] *)
  { apply triple_get. }
  (* name [n'] the result of [!p] *)
  intros n'. simpl.
  (* substitute away the equality [n' = n] *)
  apply triple_hpure. intros ->.
  (* reason about [let m = ..] *)
  applys triple_let.
  (* apply the frame rule to put aside [p ~~> n] *)
  { applys triple_conseq_frame.
    (* reason about [n+1] in the empty state *)
    { applys triple_add. }
    (* simplify the entailment *)
    { xsimpl. }
    (* check the postcondition *)
    { xsimpl. } }
  (* name [m'] the result of [n+1] *)
  intros m'. simpl.
  (* substitute away the equality [m' = m] *)
  apply triple_hpure. intros ->.
  (* reason about [p := m] *)
  applys triple_conseq.
  { applys triple_set. }
  { xsimpl. }
  { xsimpl. }
Qed.

(** This proof script shows that a practical verification proof can
    be conducted by applying the reasoning rule of the logic.

    At the same time, it appears that manually invoking the rules
    in such a way is fairly verbose.

    To enhance the user experience and allow for more concise proof
    scripts, we need to set up additional infrastructure.

    Developing such an infrastructure is the matter of the remaining
    of this presentation. *)

End ProveIncr.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Infrastructure for more concise proof scripts *)

(* ########################################################### *)
(** ** Notion of characteristic formula *)

(** In Hoare logic, the "weakest precondition calculus" computes,
    given a term [t] and a postcondition [Q], the weakest heap predicate
    [H] (weakest in the sense of the entailment relation [==>]) such that
    the Hoare triple [hoare t H Q] holds.

    Traditionnaly, a weakest precondition calculus operates on a term
    [t] annotated with function specification and invariants (e.g.,
    loop invariants).

    The framework that presented next builds upon a variant of the
    weakest precondition calculus, called "characteristic formula".
    This technique targets Separation Logic, and in particular it is
    able to smoothly integrate support for the frame rule. In addition,
    it targets unannotated code, that is, plain source code without
    any specification not annotation.

    The formula built by the "characteristic formula generator" applied
    to a term [t] is a predicate from higher-order logic that thus depends
    only on the source code of [t], and not on its specifications. This
    formula is thus "characteristic" of the source term [t]. *)


(* ########################################################### *)
(** ** Oveview of the characteristic formula generator *)

(** The characteristic formula generator is implemented as a Coq function
    named [wpgen]. To define this function, two specific challenges have
    to be addressed.

    - First, [wpgen] should be a function that is recognized by Coq as
      structurally recursive, and that computes well within Coq.
    - Second, the output of [wpgen], i.e., the formulae that it produces,
      should be human readable. Indeed, the formulae are intended to be used
      in interactive proofs guided by the user.

    Before diving into the details, let us describe at a high level the
    key ingredients of the generator.

    - To cope with the lack of annotations in the source term, in
      particular for handling the case of function applications,
      [wpgen] leverages the notion of "semantic weakest precondition",
      a notion defined further on.
    - To acccomodate for the frame rule, which is not syntax directed,
      [wpgen] integrates a predicate named [mkstruct] that is introduced
      at every node of the characteristic formula. This predicate may
      be used to invoke the frame rule if the user wishes to, otherwise
      it may be freely discarded from the formula.
    - To appear as a structurally-recursive function, [wpgen] does not
      compute substitution eagerly using [subst], but instead delay the
      substitutions by accumulating them in a context provided as extra
      argument to [wpgen].
    - To ensure a human-readable output, the definition of [wpgen] features
      auxiliary definitions, with a set of corresponding notation that
      enable to display the characteristic formula of a term [t] in a way
      that reads almost exactly like the source code of [t]. This feature
      will be illustrated through a demo.

    In what follows, we begin with the definition of the notion of "semantic
    weakest precondition". We then present the definition of [wpgen] through
    a series of refinements, introducing the key ingredients one at a time. *)


(* ########################################################### *)
(** ** Definition of semantic weakest precondition *)

Module Wpsem.

(** The weakest precondition for a term [t] with respect to a postcondition
    [Q] is written [wp t Q]. It consists of a heap predicate, of type [hprop].

[[
    Definition wp (t:trm) (Q:val->hprop) : hprop := ...
]]

    The predicate [wp t Q] is called "weakest precondition" for a combination
    of two reasons.

    First, it is a valid precondition of a triple for the term [t] with
    postcondition [Q]. *)

Parameter wp_pre : forall t Q,
  triple t (wp t Q) Q.

(** Second, it is the weakest precondition [H] such that [triple t H Q] holds,
    in the sense that any [H] satisfying this triple entails [wp t Q]. *)

Parameter wp_weakest : forall t H Q,
  triple t H Q ->
  H ==> wp t Q.

(** An alternative, equivalent characterization of [wp] is captured by the
    following equivalence, which asserts that [H] entails [wp t Q] if and
    only if [triple t H Q] holds. *)

Parameter wp_equiv : forall t H Q,
  (H ==> wp t Q) <-> (triple t H Q).

(** These two axiomatizations proposed above characterize without ambiguity
    the weakest precondition predicate [wp]. However, they do not guarantee
    the existence of such a predicate [wp]. To remedy the problem, let us
    present a third, equivalent characterization of [wp], as a direct
    definition expressed using the operators of Separation Logic. *)

Definition wp (t:trm) (Q:val->hprop) : hprop :=
  \exists (H:hprop), H \* \[triple t H Q].

(** At this stage, the details of the definition do not matter much.
    All that matters is that [wp] is well-defined and that one can prove
    that this last definition satisfies the properties associated with
    the other two characterizations. *)


(* ########################################################### *)
(** ** Separation Logic in weakest precondition style *)

(** Using the predicate [wp], we can reformulate the reasoning rule
    for sequences as shown below. This rule reads as follows:
   "If I have at hand the resources for executing [t1] and producing
    a postcondition from which I can execute [t2] and produce [Q],
    then I have the resources for executing the sequence [t1 ; t2]
    and produce [Q]". *)

Parameter wp_seq : forall t1 t2 Q,
  wp t1 (fun v => wp t2 Q) ==> wp (trm_seq t1 t2) Q.

(** Using [wp], the consequence rule reformulates as a monotony
    property (a.k.a., covariance property) of the [wp] predicate.
    The corresponding statement, shown below, reads as follows:
    "If I have at hand the resources for executing [t] and producing
    [Q1], and besides I know that [Q1] entails [Q2], then I have at
    hand the resouces for executing [t] and producing [Q2]". *)

Parameter wp_conseq : forall t Q1 Q2,
  Q1 ===> Q2 ->
  wp t Q1 ==> wp t Q2.

(** Using [wp], the frame rule reformulates as an "absorption rule"
    for the star. The corresponding statement, shown below, reads
    as follows: "If I have on one hand the resources for executing [t]
    and producing [Q], and I have in my other hand the resource [H],
    then I have in my hands the resouces for executing [t] and
    producing both [Q] and [H]". *)

Parameter wp_frame : forall t H Q,
  (wp t Q) \* H ==> wp t (Q \*+ H).

(** Remark: in the [wp] presentation, no extraction rule is needed,
    because the extraction rules are subsumed by the corresponding
    rules on entailment. For example, recall the extraction rule for
    pure facts: *)

Parameter triple_hpure : forall t (P:Prop) H Q,
  (P  ->  triple t H Q) ->
  triple t (\[P] \* H) Q.

(** This rule, when writing [triple t H Q] in the form [H ==> wp t Q],
    becomes a special instance of the rule for extracting pure facts
    out of the right-hand side of an entailment: *)

Parameter himpl_hstar_hpure_l : forall (P:Prop) H H',
  (P  ->  H ==> H') ->
  (\[P] \* H) ==> H'.

End Wpsem.


(* ########################################################### *)
(** ** Definition of the characteristic formula generator (1/5) *)

Module Wpgen.

(** As first approximation, [wpgen t Q] is defined as a recursive function
    that pattern matches on its argument [t], and produces the appropriate
    heap predicate in each case. The definitions somewhat mimic the wp-style
    reasoning rules. Let us show the first lines of the definition, and
    comment them next.

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

    The weakest precondition of a value [v] with respect to a postcondition
    [Q] is [Q v].

    The weakest precondition of a free variable [x], which corresponds to
    a stuck program, is [\[False]].

    For computing [wpgen] of an application, because we have no specifications
    at hand, we just fall back on the notion of semantics weakest precondition.
    In other words, when [t] denotes an application, we define [wpgen t] just
    as [wp t]. During the course of a proof, the corresponding proof obligation
    can be discharged by the user by invoking a specification for the function
    being applied.

    Last, the weakest precondition of a let-binding mimics the corresponding
    reasoning rule in weakest-precondition style. Consider the reasoning rule
    [wp_let] for let-bindings, which generalizes [wp_seq] shown earlier on. *)

Parameter wp_seq : forall x t1 t2 Q,
  wp t1 (fun v => wp (subst x v t2) Q)  ==>  wp (trm_let x t1 t2) Q.

(** The generator [wpgen] is such that [wpgen (trm_let x t1 t2) Q] is defined
    to be [wpgen t1 (fun v => wpgen (subst x v t2) Q)]. *)


(* ########################################################### *)
(** ** Definition of the characteristic formula generator (2/5) *)

(** The definition of [wpgen] proposed above is not structurally recursive,
    due to the recursive call of the form [wpgen (subst x v t2)], which is
    not being made to a strict subterm of [trm_let x t1 t2]. As a result,
    Coq would refuse the definition as it stands.

    To fix the issue, we reformulate the definition by introducing a context,
    written [E], to delay the substitution operations. The function [wpgen]
    now takes as argument the context, i.e., it takes the form [wpgen E t Q].
    The context [E] is implemented as a standard association list, binding
    values to variables.

    The revised definition is as shown below. When traversing a let-binding
    [trm_let x t1 t2], we extend the context from [E] to [(x,v)::E]. When
    reaching a variable [x], we perform a lookup for [x] in the context [E],
    to find the value associated with [x].

[[
    Fixpoint wpgen (E:ctx) (t:trm) (Q:val->hprop) : hprop :=
      match t with
      | trm_val v => Q v
      | trm_var x =>
           match lookup x E with
           | Some v => Q v
           | None => \[False]
           end
      | trm_app v1 v2 => wp t Q
      | trm_let x t1 t2 => wpgen E t1 (fun v => wpgen ((x,v)::E) t2 Q)
      ...
      end.
]]

    The revised definition is now clearly structurally recursive.

    Coq is happy, and so are we.
*)


(* ########################################################### *)
(** ** Definition of the characteristic formula generator (3/5) *)

(** There remains to make the output of [wpgen] human-readable and
    to integrate support for the frame rule. Before we can addresse
    both of these goals, we first need to perform a small tweak to
    the definition of [wpgen].

    We are going to swap the input of the argument [Q] with the
    pattern matching on the term [t]. As a result, each of the
    branches of the pattern matching will take the form [fun Q => ...].

[[
    Fixpoint wpgen (E:ctx) (t:trm) : (val->hprop)->hprop :=
      match t with
      | trm_val v =>  fun Q => Q v
      | trm_var x =>  fun Q =>
           match lookup x E with
           | Some v => Q v
           | None => \[False]
           end
      | trm_app v1 v2 => fun Q => wp (isubst E t) Q
      | trm_let x t1 t2 => fun Q =>
                              wpgen E t1 (fun v => wpgen ((x,v)::E) t2 Q)
      ...
      end.
]]

    One effect of this transformation is to make it more obvious that
    [wpgen E t] is something that does not depend on [Q].

    The type of [wpgen E t] is [(val->hprop)->hprop]. We thereafter name
    this type "formula". *)

Definition formula : Type := (val->hprop)->hprop.


(* ########################################################### *)
(** ** Definition of the characteristic formula generator (4/5) *)

(** To make the output of [wpgen] human-readable, we introduce one
    auxiliary definition for each of the branches of the pattern
    matching that defines [wpgen]. For example, for the first branch,
    we replace [fun Q => Q v] with [wpgen_val v], for the appropriate
    definition of the auxiliary function [wpgen_val].

[[
    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      match t with
      | trm_val v => wpgen_val v
      | trm_var x => wpgen_var E x
      | trm_app t1 t2 => wp t
      | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
      ...
      end.
]]

    An interesting case is that of the let-binding.

    We let [wpgen_let F F'] be a definition for [fun Q => F (fun v => F' v Q)].

    We let [Let v := F1 in F2] be a notation for [wpgen_let F1 (fun v => F2)].

    As a result, [wpgen (trm_let x t1 t2)] displays in the form [Let x := F1 in F2],
    where [F1] and [F2] correspond to the [wpgen] of [t1] and [t2], respectively.

    This suggests how the result computed by [wpgen t] can look like the
    source term of [t]. By the way, this guarantees that the output produced
    by [wpgen] is linear in the size of its input.

*)

(* ########################################################### *)
(** ** Definition of the characteristic formula generator (5/5) *)

(** There remains to integrate support for the frame rule. To that end, we
    insert to the head of the body of the function [wpgen], just in front
    of the [match t with], a predicate named [mkstruct], as follows.

[[
    Fixpoint wpgen (E:ctx) (t:trm) : formula :=
      mkstruct (match t with
        | trm_val v => wpgen_val v
        | trm_var x => wpgen_var E x
        | trm_app t1 t2 => wp t
        | trm_let x t1 t2 => wpgen_let (wpgen E t1) (fun v => wpgen ((x,v)::E) t2)
        ...
        end).
]]

    The predicate [mkstruct] applies to a [formula] and produces [formula],
    it is thus a "formula transformer", of type [formula->formula]. *)

(** The predicate [mkstruct] should satisfy three properties.

    Firstly, it should be possible to discard it if we do not need to exploit it.
    This first property is captured by the following erasure lemma. *)

Parameter mkstruct_erase : forall (F:formula) Q,
  F Q ==> mkstruct F Q.

(** Secondly, [mkstruct] should enable applying the frame rule and the
    consequence rule, by validating the same structural rules as the [wp]
    predicate (namely [wp_frame] and [wp_conseq]). *)

Parameter mkstruct_frame : forall (F:formula) H Q,
  (mkstruct F Q) \* H ==> mkstruct F (Q \*+ H).

Parameter mkstruct_conseq : forall (F:formula) Q1 Q2,
  Q1 ===> Q2 ->
  mkstruct F Q1 ==> mkstruct F Q2.

(** It really does not matter how [mkstruct] is defined. All that we care
    about is that there exists a predicate [mkstruct] satisfying the above
    three properties. *)

(** It turns out that we can exhibit such a predicate. One definition that
    works appears below---at this stage, no need to undertand the details. *)

Definition mkstruct (F:formula) : formula :=
  fun (Q:val->hprop) => \exists H Q',(F Q') \* H \* \[Q' \*+ H ===> Q].



(* ########################################################### *)
(** ** Soundness of the characteristic formula generator *)

(** By integrating the predicate [mkstruct] into [wpgen], we reach the last
    refinement of the definition of the characteristic formula generator.

    Once the generator is defined, it is not hard to prove its soundness,
    because the generator merely mimics the wp-style reasoning rules.

    The soudness theorem asserts that the formulae computed by [wpgen]
    entail the semantic weakest precondition [wp]. This result applied
    to a closed term [t], hence the context [E] is instantiated as [nil]. *)

Parameter wp_of_wpgen : forall t Q,
  wpgen nil t Q ==> wp t Q.

(** For another way to interpret the soundness theorem, recall the
    equivalence that characterizes [wp]. *)

Parameter wp_equiv :
  (H ==> wp t Q) <-> (triple t H Q).

(** By exploiting this equivalence, the soundness theorem reformulates as
    shown below: to establish a triple of the form [triple t H Q], it
    suffices to prove that [H] entails the result of [wpgen] applied to
    [t] and [Q], in the empty context. *)

Parameter triple_of_wpgen : forall t H Q,
  H ==> wpgen nil t Q ->
  triple t H Q.

(** The result above is the one that is invoked to begin the proof that
    a particular term satisfies its specification. It introduces the
    [wpgen] function, which may be evaluated using the Coq tactic [simpl]. *)

End Wpgen.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Technical zoom: the magic wand *)

(** In this short overview, we are not going to look in detail at
    the implementation of the various tactics that help processing
    the characteristic formulae in proofs.

    We will only focus on one particular ingredient that is very
    helpful for setting up these tactics: the "magic wand". *)


(* ########################################################### *)
(** ** Definition of magic wand *)

(** The magic wand is a heap predicate combinator, written [H1 \-* H2],
    formalized as [hwand H1 H2].

[[
    Definition hwand (H1 H2:hprop) : hprop := ...
]]

    The predicate "H1 wand H2" describes a heap predicate such that,
    if we augment it with [H1], we obtain [H2]. This intuition is
    captured by the following simplification lemma. *)

Parameter hwand_elim : H1 \* (H1 \-* H2)  ==> H2.

(** There are several ways to define the magic wand. One possible
    definition is the following: it describes some predicate [H0],
    such that, if we star it with [H1], we obtain [H2]. *)

Definition hwand (H1 H2:hprop) : hprop :=
   \exists H0, H0 \* \[ H1 \* H0 ==> H2].

(** It is useful to generalize the magic wand to postconditions,
    through a predicate written [Q1 \--* Q2]. Again, there are
    several possible definitions. Here is one that is a simple
    generalization of the previous one. *)

Definition qwand (Q1 Q2:val->hprop) : hprop :=
   \exists H0, H0 \* \[ Q1 \*+ H0 ===> Q2].


(* ########################################################### *)
(** ** Structural rules revisited with the magic wand *)

(** Without the magic wand, the rule that combines the consequence rule
    and the frame rule is stated as follows. *)

Parameter triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.

(** One caveat with this rule is that it requires instantiating [H2],
    the part of the heap being "framed out". Providing [H2] by hand
    in the proofs would be way too tedious. Setting up a tactic that
    computes [H2] as the difference between [H] and [H1] (as suggested
    by the second premise) would work well in the simples cases, however
    it becomes very tricky to implement when [H] contains existential
    quantifiers. Indeed, one has to figure out which quantifiers should
    go into [H1], and which one should go into [H2]. *)

(** With the magic wand, we can bypass the problem altogether by
    eliminating [H2]. To that end, consider the third premise. It
    asserts that [H2] is such that, when added to [Q1], yields [Q].
    Thus [H2] may be expressed as [Q1 \--* Q], the magic wand between
    [Q1] and [Q].

    Substituting [H2] with [Q1 \--* Q leads to a more concise and more
    practical reasoning rule, called the "ramified frame rule". *)

Parameter triple_ramified_frame : forall H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* (Q1 \--* Q) ->
  triple t H Q.

(** .. *)

Parameter wp_ramified :
  (wp t Q1) \* (Q1 \--* Q2) ==> (wp t Q2).




(* ============

(*
    For conducting proofs in practice, there remains to state lemmas and
    define tactics to assist the user in the manipulation of the formula
    produced by [wpgen]. Ultimately, the end-user only manipulates CFML's
    "x-tactics" (recall the first two chapters), without ever being
    required to understand how [wpgen] is defined.

    In other words, the contents of this chapter reveals the details
    that we work very hard to make completely invisible to the end user. *)




(* ########################################################### *)
(** ** Ramified frame rule *)

(** Recall combined rule *)

(** New formulation using the magic wand to eliminate [H2]. *)


(** Note: [H1 \* H2 ==> H1 \* (Q1 \--* Q)] simplifies to
          [H2 ==> (Q1 \--* Q)] which simplifies to
          [Q1 \*+ H2 ===> Q]. *)

End Wand.



(* ########################################################### *)
(** ** Verification of the increment function, using x-tactics *)

Module ProveIncrWithTactics.

Import DemoPrograms.

Import SLFWPgen.
Open Scope wpgen_scope.

Lemma triple_incr' : forall (p:loc) (n:int),
  triple (incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl.
Qed.

End ProveIncrWithTactics.


(* ########################################################### *)
(** ** Verification of in-place concatenation of two mutable lists *)

Module ProveAppend.
Import SLFExtra SLFProgramSyntax.
Implicit Types p q : loc.

(** A mutable list cell is a two-cell record, featuring a head field and a
    tail field. We define the field indices as follows. *)

Definition head : field := 0%nat.
Definition tail : field := 1%nat.

(** A mutable list consists of a chain of cells, terminated by [null].

    The heap predicate [MList L p] describes a list whose head cell is
    at location [p], and whose elements are described by the list [L].

    This predicate is defined recursively on the structure of [L]:

    - if [L] is empty, then [p] is the null pointer,
    - if [L] is of the form [x::L'], then the head field of [p]
      contains [x], and the tail field of [p] contains a pointer
      [q] such that [MList L' q] describes the tail of the list.

*)

Fixpoint MList (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists q, (p`.head ~~> x) \* (p`.tail ~~> q)
                     \* (MList L' q)
  end.

(** The following reformulations of the definition are helpful in proofs. *)

Lemma MList_cons : forall p x L',
  p ~> MList (x::L') =
  \exists q, (p`.head ~~> x) \* (p`.tail ~~> q) \* MList L' q.
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

Parameter MList_if : forall (p:loc) (L:list val),
      (MList L p)
  ==> (If p = null
      then \[L = nil]
      else \exists x q L', \[L = x::L']
           \* (p`.head ~~> x) \* (p`.tail ~~> q)
           \* (MList L' q)).
(* Proof in [SLFBasic]. *)


(** The following function expects a nonempty list [p1] and a list [p2],
    and updates [p1] in place so that its tail gets extended by the
    cells from [p2].

[[
    let rec append p1 p2 =
      if p1.tail == null
        then p1.tail <- p2
        else append p1.tail p2
]]

*)

Definition append : val :=
  VFix 'f 'p1 'p2 :=
    Let 'q1 := 'p1'.tail in
    Let 'b := ('q1 '= null) in
    If_ 'b
      Then Set 'p1'.tail ':= 'p2
      Else 'f 'q1 'p2.

(** The append function is specified and verified as follows. *)

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

End ProveAppend.



*)