
Parameter example_trm_red : forall m,
  red m (trm_app example_trm' (val_bool false)) m (val_int 1).



Definition assertion := state -> Prop.
Definition Hoare_triple (H:assertion) (t:trm) (Q:val->assertion) : Prop :=
  forall h, H h ->
  exists v h', red h t h' v /\ Q v h'.
Parameter val_div : prim.



(** * Hprop: Heap Predicates *)

(** ** Definition of Separation Logic triples *)

(** We will give a definition of the separating conjunction operator (star)
    shortly afterwards. For the moment, let us assume a definition of [star]
    to exist, and let us exploit it to define the semantics of a SL triple. *)

Parameter star : assertion -> assertion -> assertion.

Notation "H1 '\*' H2" := (star H1 H2)
  (at level 41, right associativity).

(** Recall the definition of Separation Logic triples from the introduction.

[[
  Definition SL_triple (H:assertion) (t:trm) (Q:assertion) :=
    forall (H':assertion), Hoare_triple (H \* H') t (Q \* H').
]]

    To adapt it to a language where terms output values, we need to
    define what it means to compute the star of a postcondition [Q] of
    type [val->assertion] and of an assertion [H].

    To that end, we let [Q \*+ H'] denote [fun x => (Q x \* H')].
    This postcondition characterizes the same output value as [Q],
    but in an output heap extended with [H'].
*)

Notation "Q \*+ H" := (fun x => (Q x) \* H)
  (at level 40).

(** Using this piece of notation, the definition of triples from the
    introduction is easily adapted. *)

Definition triple_1 (H:assertion) (t:trm) (Q:val->assertion) :=
  forall (H':assertion), Hoare_triple (H \* H') t (Q \*+ H').

(** The definition above defines SL triples in terms of Hoare triples.
    While this indirect definition is helpful for providing intuition,
    a direct definition is better suited for conducting proofs.
    If we unfold the intermediate definition of Hoare triples and
    perform minor simplification, we obtain the definition shown below. *)

Definition triple_2 (H:assertion) (t:trm) (Q:val->assertion) : Prop :=
  forall H' h, (H \* H') h ->
  exists v h', red h t h' v /\ (Q v \* H') h'.

(** This definition reads as follows: for any input heap [h], and any
    heap predicate [H'] describing the part of the heap not covered
    by the precondition [H], there exists an output value [v] and an
    output heap [h'] to which the term [t] evaluates starting from the
    input heap [h], and such that a subset of the final heap is described
    by the postcondition [Q] applied to the value [v], while the remaining
    subset of the output heap corresponds is described by [H']. *)

(** ** Slight change in terminology *)

(** In Separation Logic, we usually manipulate only pieces of states,
    as opposed to complete state. It is convenient to keep track of
    the intention by using two distinct types:
    - [state] denotes a complete state,
    - [heap] denotes a piece of state.


    In our formalism, both [state] and [heap] are represented as
    finite maps from locations to values, so the distinction might
    appear a bit artificial. Nevertheless, this distinction proves
    very useful when extending Separation Logic with additional features,
    such as "time credits" or "read-only permissions".
    Thus, we introduce the following alias. *)

Definition heap : Type := state. (* intended to represent a piece of state *)

(** In practice, we use type [state] when defining the evaluation rules,
    and we use the type [heap] to denote the argument of an assertion.
    In the rare cases where an entity is used at the same time in an
    evaluation rule and as argument of an assertion, we use type [heap]. *)

(** A Separation Logic assertion is a predicate over a piece of state.
    Thus, it has type [heap -> Prop]. The type of such _heap predicates_
    is written [hprop]. *)

Definition hprop := heap -> Prop.

(** With the new terminology, and with placing the term [t] as first
    argument, the definition of SL triples becomes: *)

Definition triple_3 (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall H' h, (H \* H') h ->
  exists v h', red h t h' v /\ (Q v \* H') h'.

Notation "'triple'" := triple_3.

(** By convention, we let [H] range over heap predicates (of type [hprop]),
    and [Q] range over postconditions (of type [val->hprop]). *)


(** * Fundamental heap predicates *)

(** We next present the definitions of the fundamental building blocks for
    constructing heap predicates. These building blocks are:

    - [\[]] denotes the empty heap predicate.
    - [\[P]] denotes the empty heap predicate and asserts that [P] is true.
    - [l ~~> v] describes a single memory cell, at location [l], with
      contents [v].
    - [H1 \* H2] denotes the separating conjunction of two heap predicates.
    - [\exists x, H] denotes an existential quantification at the level of
      heap predicates.

    As we will see through this section, each of these heap predicates is
    defined as a function of the form [fun (h:heap) -> (...:Prop)].

    What makes Separation Logic works so smoothly in practice is that
    the aforementioned fundamental heap predicates are the only ones that are
    defined directly as functions from heap to propositions. All user-defined
    heap predicates are then defined as combination of these fundamental
    heap predicates. It is thus essential to have a deep understanding of
    the meaning of the fundamental heap predicates. *)

(* SLIDE: grammar-of-basic-heap-predicates *)

(** ** Points-to predicate *)

(** The points-to heap predicate is written [l ~~> v], which is a notation for
    [hsingle l v]. This heap predicate characterizes a heap [h] that is made
    of a single memory cell, at location [l], with contents [v]. In addition,
    [hsingle l v] captures the property that [l] is not the [null] location.
    The formal definition is as follows: *)

Definition hsingle (l:loc) (v:val) : hprop :=
  fun h => h = fmap_single l v /\ l <> null.

Notation "l '~~>' v" := (hsingle l v)
  (at level 32, no associativity).

(** For example, the following specification of [incr r] indicates
    that it executes safely assuming that location [r] is allocated
    with contents [2], and that it updates this location to contain [3].
    The evaluation of [incr r] returns some value [v], which as we will
    see soon afterwards, may be specified to be the unit value. *)

Parameter (incr:val) (r:loc).

Parameter hsingle_demo :
  triple (incr r)
    (r ~~> 2) (* precondition *)
    (fun v => r ~~> 3). (* postcondition *)

(** The general specification of the [incr] function involves a universal
    quantification over the initial contents of the cell, as shown below. *)

Parameter triple_incr : forall (n:int),
  triple (incr r)
    (r ~~> n)
    (fun v => r ~~> (n+1)).

(* EX1! (triple_augment) *)
(** State a specification for the term [val_augment r m], which takes
    as arguments a location [r] and an integer [m], and updates the cell
    at location [r] by adding [m] to its original contents. *)

Parameter val_augment : val.

(* SOLUTION *)
Parameter triple_augment : forall (r:loc) (n m:int),
  triple (val_augment r m)
    (r ~~> n)
    (fun v => r ~~> (n + m)).
(* /SOLUTION *)

(** [] *)


(** ** Star predicate *)

(** The star predicate is written [H1 \* H2], which is a notation for
    [hstar H1 H2]. This heap predicate characterizes a heap [h] that
    is composed of two disjoint parts, call them [h1] and [h2], such that
    the first one satisfies [H1] and the second one satisfies [H2].
    Together, the propositions [state_disjoint h1 h2] and [h = state_union h1 h2]
    assert that [h1] and [h2] really constitute a partition of [h] in two
    disjoint parts. *)

Definition hstar (H1 H2:hprop) : hprop :=
  fun h => exists (h1 h2:heap),
       H1 h1
    /\ H2 h2
    /\ fmap_disjoint h1 h2
    /\ h = fmap_union h1 h2.

Notation "H1 '\*' H2" := (hstar H1 H2)
  (at level 41, right associativity).

(** Consider for example the following specification of [incr r] which captures
    the fact that it does not modify the contents of another reference [s]. *)

Parameter hstar_demo : forall (s:loc) (n m:int),
  triple (incr r)
    (r ~~> n \* s ~~> m)
    (fun v => r ~~> (n+1) \* s ~~> m).

(* EX2! (triple_swap) *)
(** State a specification for the term [val_swap r s], which takes as argument
    two distinct locations [r] and [s], with respective contents two integers [n]
    and [m], and that swaps the contents of the two locations. *)

Parameter val_swap : val.

(* SOLUTION *)
Parameter triple_swap : forall (r s:loc) (n m:int),
  triple (val_swap r s)
    (r ~~> n \* s ~~> m)
    (fun v => r ~~> m \* s ~~> n).
(* /SOLUTION *)

(** [] *)

(* EX1! (hstar_comm) *)
(** Prove that separating conjunction is commutative, in the sense that any
    heap satisfying [H1 \* H2] also satisfies [H2 \* H1]. The proof involves
    the two following results on finite maps: symmetry of the disjointness
    predicate, and commutativity of the union of disjoint heaps. *)

Parameter fmap_disjoint_sym : forall (h1 h2:heap),
  fmap_disjoint h1 h2 ->
  fmap_disjoint h2 h1.

Parameter fmap_union_comm_of_disjoint : forall (h1 h2:heap),
  fmap_disjoint h1 h2 ->
  fmap_union h1 h2 = fmap_union h2 h1.

Lemma hstar_comm : forall (H1 H2:hprop) (h:heap),
  ((H1 \* H2) h) ->
  ((H2 \* H1) h).
Proof.
  (* ADMITTED *)
  introv (h1&h2&P1&P2&D&E). exists h2 h1. splits.
  { apply P2. }
  { apply P1. }
  { apply fmap_disjoint_sym. auto. }
  { rewrite fmap_union_comm_of_disjoint. auto. auto. }
Qed.
  (* /ADMITTED *)

(** [] *)

(** An essential property of Separation Logic is that it is never possible
    to construct a heap satisfying a heap predicate of the form
    [(r ~~> ..) \* (r ~~> ..)]. Indeed, there is no way to exhibit two
    disjoint heaps that both have [r] in their domain. *)

Lemma hstar_hsingle_same_loc_inv : forall (l:loc) (v1 v2:val) (h:heap),
  ((l ~~> v1) \* (l ~~> v2)) h ->
  False.
Proof.
  introv (h1&h2&P1&P2&D&E). destruct P1 as (E1&N1). destruct P2 as (E2&N2).
  subst. applys* fmap_disjoint_single_single_same_inv.
Qed.

(** Now that the separating conjunction is properly defined,
    we update the definition of [triple] to use that definition,
    instead of the abstract [star] operator that assumed previously. *)

Definition triple_4 (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall H' h, (H \* H') h ->
  exists v h', red h t h' v /\ (Q v \* H') h'.

(** Thereafter, [triple] is a shorthand for [triple_4]. *)

Notation "'triple'" := triple_4.

(* QUIZ *)
(** Is the following triple true or false? *)
Parameter triple_cell_twice : forall (r:loc) (n:int),
  triple (val_unit)
    (r ~~> n \* r ~~> n)
    (fun v => r ~~> (n+1) \* r ~~> (n+1)).
(* INSTRUCTORS: The triple is true because its precondition is equivalent
   to false, i.e. it cannot be satisfied by any input heap. *)
(* /QUIZ *)

(* EX2! (triple_cell_twice) *)
(** Prove the above lemma.
    Hint: unfold the definition of [triple], a.k.a. [triple_4],
    and decompose the assumption on the input heap in order to
    derive a contradiction using lemma [hstar_hsingle_same_loc_inv]. *)

Lemma triple_cell_twice' : forall (r:loc) (n:int),
  triple (val_unit)
    (r ~~> n \* r ~~> n)
    (fun v => r ~~> (n+1) \* r ~~> (n+1)).
Proof.
  (* ADMITTED *)
  intros. unfold triple_4. intros H' h M. destruct M as (h1&h2&P1&P2&D&E).
  false. eapply hstar_hsingle_same_loc_inv. apply P1.
Qed.
  (* /ADMITTED *)

(** [] *)


(** ** Pure heap predicate *)

(** The _empty heap predicate_ is written [ \[] ], which is a notation for
    [hempty]. It characterizes exactly heaps that are empty. *)

Definition hempty : hprop :=
  fun h => h = fmap_empty.

Notation "\[]" := (hempty)
  (at level 0).

(** The _pure heap predicate_ extends the empty heap predicate by capturing
    not just the fact that its argument is the heap is empty, but also that
    some proposition [P] is true. The pure heap predicate is written [ \[P] ],
    which is a notation for [hpure P]. It is defined as follows: *)

Definition hpure (P:Prop) : hprop :=
  fun h => (h = fmap_empty /\ P).

Notation "\[ P ]" := (hpure P)
  (at level 0, P at level 99, format "\[ P ]").

(** The empty heap predicate and the pure heap predicate are systematically
    involved in the precondition and the postcondition of pure functions, i.e.
    functions that do not involve side effects. Consider for example the
    specification of the successor function. The precondition assumes
    an empty input heap. The postcondition asserts an empty input heap, and
    moreover asserts that the output value is one unit greater than the
    input argument. *)

Parameter triple_succ : forall (n:int),
  triple (val_add (val_int n))
    \[]
    (fun (r:val) => \[r = val_int (n + 1)]).

(** Observe by executing [Print triple_succ] that the [val_int] constructor
    is in fact not displayed by Coq. Indeed, it is declared as a coercion.
    In fact, we do not need to write [val_int] in the triple, as Coq is
    able to infer its occurences. Thus, we may write more concisely: *)

Parameter triple_succ' : forall (n:int),
  triple (val_add n)
    \[]
    (fun (r:val) => \[r = n + 1]).

(** As another example, consider the specification of the addition primitive
    function. The precondition assumes an empty input heap. The postcondition
    asserts an empty input heap, and moreover asserts that the output value
    is the sum of the two arguments. *)

Parameter triple_add : forall (n1 n2:int),
  triple (val_add n1 n2)
    \[]
    (fun (r:val) => \[r = n1 + n2]).

(** Note that the specification tells nothing about the behavior of
    addition in the case where the two arguments are not both integer values. *)

(** Symmetrically to its use in postconditions, the pure heap predicate may
    appear in preconditions to describe requirements on the arguments.
    For example, division expects a nonzero integer as second argument. *)

Parameter triple_div : forall (n1 n2:int),
  triple (val_div n1 n2)
    \[n2 <> 0]
    (fun (r:val) => \[r = n1 + n2]).

(** While the above formulation is perfectly valid, it is more convenient in
    practice to follow an alternative, logically equivalent presentation,
    whereby the pure preconditions appear as Coq hypotheses outside the triple.
    In the case of the division, this alternative presentation amounts to
    asserting [n2 <> 0] as hypothesis prior to the triple: *)

Parameter triple_div' : forall (n1 n2:int),
  n2 <> 0 ->
  triple (val_div n1 n2)
    \[]
    (fun (r:val) => \[r = n1 + n2]).

(** Throughout the course, we will follow the convention that pure preconditions
    appear as hypotheses prior to the triple. Thus, preconditions will only
    be used to describe the shape of the heap. *)

(** DEPRECATED !!

    The pure heap predicate is useful not just for specifying pure functions,
    but also for specifying effectful functions, to assert properties about
    the output value or the output heap. For example, in the specification
    of [incr r] shown below, the pure heap predicate [ \[v = val_unit] ] asserts
    that the evaluation of [incr r] returns the unit value. This heap predicate
    comes in addition to the points-to heap predicate that describes the output
    heap. *)

Parameter hpure_demo :
  triple (incr r)
    (r ~~> 2)
    (fun v => (r ~~> 3)).

(** Above, observe that the two heap predicates from the postcondition
    are separated by the star operator. This operator asserts that the output
    heap decomposes into two disjoint parts: an empty heap, which satisfies
    the predicate [ \[v = val_unit] ], and a singleton heap, which satisfies
    the assertion [r ~~> 3]. Such use of the separating conjunction, where one
    part corresponds to the empty heap, may appear somewhat unexpected at
    first, but it is perfectly well-defined and corresponds to a specification
    pattern that we will see over and over again.

    As another example, consider the specification below for the primitive
    [val_get], used to read in a memory cell. Assuming the argument [l] to
    correspond to a location at which some value [v] is stored, the read
    operation executes safely and returns an output value, call it [x],
    which is such that [x = v]. The piece of heap, described by [l ~~> v],
    is returned unchanged in the postcondition. *)

Parameter triple_get : forall (v:val) (l:loc),
  triple (val_get l)
    (l ~~> v)
    (fun (r:val) => \[r = v] \* (l ~~> v)).

(** Remark: above, [val_get l] is interpreted using coercions, and stands for
    [trm_app (trm_val (val_prim val_get)) (trm_val (val_loc l))]. *)

(* EX2! (triple_set) *)
(** State a specification for the term [val_set l v], which updates the
    location [l] with the value [v]. Make sure to specify that the update
    operation returns the unit value. *)

(* SOLUTION *)
Parameter triple_set : forall (v w:val) (l:loc),
  triple (val_set l v)
    (l ~~> w)
    (fun (r:val) => l ~~> v).
(* /SOLUTION *)

(** [] *)

(* EX2! (triple_free) *)
(** State a specification for the term [val_free l], which assumes a
    location [l] to be allocated, and explicitly disposes this location.
    Note that such a free operation usually does not appear in programming
    languages featuring a GC, but is commonplace in other languages.
    The postcondition should  assert that the return value is unit, and
    not mention the location [l] anymore, effectively banning any subsequent
    access to this location. *)

Parameter val_free : val.

(* SOLUTION *)
Parameter triple_free : forall (v:val) (l:loc),
  triple (val_free l)
    (l ~~> v)
    (fun (r:val) => \[r = val_unit]).
(* /SOLUTION *)

(** [] *)

(* EX1? (hpure_true_iff_hempty) *)
(** Prove that a heap satisfies the heap predicate [\[True]] if and only
    if it satisfies the empty heap predicate. *)

Lemma hpure_true_iff_hempty : forall (h:heap),
  (\[True] h) <-> (\[] h).
Proof.
  (* ADMITTED *)
  intros. split.
  { intros (M&N). hnf. auto. }
  { intros M. split. { hnf in M. auto. } { auto. } }
Qed.
  (* /ADMITTED *)

(** [] *)

(** The next lemma establishes that the heap predicate [H \* \[]]
    is equivalent to [H]. Its proof relies on two handy tactics,
    that will be useful for proving numerous metatheory results.
    - The tactic [fmap_eq] proves equality between finite maps,
      e.g. [fmap_union h fmap_empty = h].
    - The tactic [fmap_disjoint] proves obvious disjointness results,
      e.g. [fmap_disjoint h fmap_empty], or [fmap_disjoint h1 h2]
      when [fmap_disjoint h2 h1] appears in the context.

    The proof is as follows. *)

Lemma hstar_hempty_iff : forall (H:hprop) (h:heap),
  ((H \* \[]) h) <-> (H h).
Proof.
  intros. split.
  { intros (h1&h2&P1&P2&D&E). hnf in P2. subst. fmap_eq. auto. }
  { intros M. exists h (fmap_empty:heap). splits.
    { auto. }
    { hnf. auto. }
    { fmap_disjoint. }
    { fmap_eq. } }
Qed.

(** Observe that we need to provide an explicit type annotation in
    [(fmap_empty:heap)], because [fmap_empty] is a polymorphic
    constructor, and the "exists" tactic is too limited to figure out
    by itself the required types from the current proof obligation. *)

(* EX2? (hstar_hpure_iff) *)
(** Establish a generalization of the above lemma, proving that the heap
    predicate [H \* \[P]] is equivalent to [H] when proposition [P] holds. *)

Lemma hstar_hpure_iff : forall (H:hprop) (P:Prop) (h:heap),
  ((H \* \[P]) h) <-> ((H h) /\ P).
Proof.
  (* ADMITTED *)
  intros. split.
  { intros (h1&h2&P1&(P2&P2')&D&E). subst. fmap_eq. auto. }
  { intros (M&N). exists h (fmap_empty:heap). splits.
    { auto. }
    { hnf. auto. }
    { fmap_disjoint. }
    { fmap_eq. } }
Qed.
  (* /ADMITTED *)

(** [] *)


(** ** Existential heap predicate *)

(** The _existential heap predicate_ provides existential quantification
    at the level of heap predicates. It is written [\exists x, H], which
    is a notation for [hexists (fun x => H)]. It is the counterpart of the
    normal existential quantification on propositions, which is written
    [exists x, P], a notation for [ex (fun x => P)].

    The Coq definition of [hexists] is polymorphic in the type of [x].
    The type of [x] is called [A] below. The argument of [hexists], called [J]
    below, is typically of the form [fun x => H]. It has type [A->hprop]. *)

Definition hexists (A:Type) (J:A->hprop) : hprop :=
  fun h => exists x, J x h.

Notation "'\exists' x1 , H" := (hexists (fun x1 => H))
  (at level 39, x1 ident, H at level 50).

(** The notation [\exists x1 x2 x3, H] shows useful to quantify several
    arguments at once. *)

Notation "'\exists' x1 x2 , H" := (\exists x1, \exists x2, H)
  (at level 39, x1 ident, x2 ident, H at level 50).
Notation "'\exists' x1 x2 x3 , H" := (\exists x1, \exists x2, \exists x3, H)
  (at level 39, x1 ident, x2 ident, x3 ident, H at level 50).
(** The notation [\exists (x:T), H] allows us to provide an explicit
    type annotation. *)

Notation "'\exists' ( x1 : T1 ) , H" := (hexists (fun x1:T1 => H))
  (at level 39, x1 ident, H at level 50, only parsing).

Notation "'\exists' ( '_' : T1 ) , H" := (hexists (fun _:T1 => H))
  (at level 39, H at level 50). (* useful when quantifying over proof terms *)

(** The main role of existential quantification is to introduce abstraction.
    For example, assume that we want to specify the increment function
    by saying that it updates the contents of its target location to
    some greater contents, without revealing that the new contents is exactly
    one unit greater. Then, for a precondition [r ~~> n], we would consider
    the postcondition [\exists m, (r ~~> m) \* \[m > n]]. *)

Parameter hexists_demo : forall (n:int),
  triple (incr r)
    (r ~~> n)
    (fun v => \[v = val_unit] \* \exists (m:int), (r ~~> m) \* \[m > n]).

(** Existential quantification is also useful to specify output values
    when they have a specific shape. For example, consider the operation
    called [val_ref], which allocates and initializes one memory cell
    with some contents [v]. A call to [val_ref] executes safely in the
    empty heap. The output value of its evaluation is a value, call it [r],
    which is of the form [val_loc l] for _some_ location [l]. The output
    heap satisfies [l ~~> v] for that particular [l]. As shown below, the
    location [l] gets existentially quantified in the postcondition. *)

Parameter triple_ref : forall (v:val),
  triple (val_ref v)
    \[]
    (fun (r:val) => \exists (l:loc), \[r = val_loc l] \* (l ~~> v)).

(* EX2! (triple_ref_of_ref) *)
(** Consider the term [val_ref (val_ref 3)], which allocates a memory
    cell with contents [3], at some location [l], then allocates a
    another memory cell with contents [l], at some location [l'], and
    finally returns the location [l']. State a specification for that
    term. *)

(* SOLUTION *)
Parameter triple_ref_of_ref :
  triple (val_ref (val_ref 3))
    \[]
    (fun (r:val) =>
        \exists (l:loc), \[r = val_loc l] \* \exists (l':loc),
                         (l ~~> l') \* (l' ~~> 3)).
(* /SOLUTION *)

(** [] *)

(* EX1? (hexists_permut) *)
(** Prove that [\exists x, \exists y, K x y] is equivalent to
    [\exists y, \exists x, K x y]. *)

Lemma hexists_permut : forall (A B:Type) (K:A->B->hprop) (h:heap),
  ((\exists x, \exists y, K x y) h) ->
  ((\exists y, \exists x, K x y) h).
Proof.
  (* ADMITTED *)
  introv (x&y&M). exists y x. apply M.
Qed.
  (* /ADMITTED *)

(** [] *)

(* EX2? (hpure_iff_hexists_prop) *)
(** Prove that a heap satisfies the heap predicate [\[P]] for some
    proposition [P] if and only if it satisfies the heap predicate
    [\exists (p:P), \[]]. The latter describes a empty heap and
    asserts the existence of a proof term [p] of type [P]. In Coq,
    asserting the existence of such a proof term of type [P] is
    equivalent to asserting that [P] is a true proposition. *)

Lemma hpure_iff_hexists_proof : forall (P:Prop) (h:heap),
  (\[P] h) <-> ((\exists (p:P), \[]) h).
Proof.
  (* ADMITTED *)
  intros. split.
  { intros (M&p). exists p. hnf. auto. }
  { intros (p&M). hnf in M. split. { auto. } { auto. } }
Qed.
  (* /ADMITTED *)

(** [] *)


(** ** Summary *)

(** The fundamental heap predicates are written:
    - [\[]]
    - [\[P]]
    - [l ~~> v]
    - [H1 \* H2]
    - [\exists x, H].

    and they are defined as follows. *)

(* SLIDE: definition-of-basic-heap-predicates *)

Module Type Fundamental.

Definition hempty : hprop :=
  fun h => h = fmap_empty.

Definition hpure (P:Prop) : hprop :=
  fun h => h = fmap_empty /\ P.

Definition hsingle (l:loc) (v:val) : hprop :=
  fun h => h = fmap_single l v /\ l <> null.

Definition hstar (H1 H2:hprop) : hprop :=
  fun h => exists h1 h2,
       H1 h1
    /\ H2 h2
    /\ fmap_disjoint h1 h2
    /\ h = fmap_union h1 h2.

Definition hexists (A:Type) (J:A->hprop) : hprop :=
  fun h => exists x, J x h.

End Fundamental.



(** * Triples adapted for languages with garbage collection *)

(** ** Motivating example *)

(** Consider the program [Let x := val_ref 3 in 5], abbreviated below
    as [t]. This program allocates a memory cell with contents [3], at some
    location [x], and then returns [5]. In this program, the address
    of the allocated memory cell is not returned, so it cannot be
    subsequently accessed. Thus, one may argue that a natural specification
    for this program is the same as that of a program that simply returns
    the value [5], that is: *)

Parameter t : trm. (* := [Let x := val_ref 3 in 5]. *)

Parameter htop_example_1 :
  triple t
    \[]
    (fun (r:val) => \[r = 5]).

(** However, it turns out that the above triple cannot be derived with
    respect to the definition of triples that we have considered so far.
    The reason is simple: the memory cell that is allocated by the term
    belongs to the heap structure, thus it must be described in the
    postcondition. As a result, with the current definition, only the
    following triple may be established: *)

Parameter htop_example_2 :
  triple t
    \[]
    (fun (r:val) => \[r = 5] \* \exists l, l ~~> 3).

(** The remaining of this chapter describes a simple patch to the
    definition of triple that would allow establishing the first
    specification, which is much more natural. In short, we introduce
    a mechanism that allows to discard any desired piece of state
    from the postcondition. *)

(** ** Patching triples using the top predicate *)

(** To allow discarding any desired piece of state, we introduce a handy
    heap predicate called "top", which is a predicate that holds of any
    heap. This predicate is written [\Top], and defined as follows. *)

Definition htop : hprop :=
  fun (h:heap) => True.

Notation "\Top" := (htop).

(** In the definition of triples, we modify the specification of the
    output heap from [(Q v \* H') h'] to [(Q v \* \Top \* H') h'].
    Adding a [\Top] component effectively allows to _not describe_
    in the postcondition pieces of state that have been allocated
    during the execution of the term. *)

Definition triple_5 (H:hprop) (t:trm) (Q:val->hprop) : Prop :=
  forall H' h, (H \* H') h ->
  exists v h', red h t h' v /\ (Q v \* \Top \* H') h'.

(** Throughout the remaining of this course, the definition of
    the predicate [triple] corresponds to the above definition.
    It is defined in file [LambdaSep.v]. *)

(* EX2! (htop_hstar_htop) *)
(** Prove that [\Top \* \Top] is equivalent to [\Top], i.e., that
    [\Top] is idempotent. Tactics [fmap_disjoint] and [fmap_eq]
    are useful to complete the proof. *)

Lemma htop_hstar_htop : forall (h:heap),
  ((\Top \* \Top) h) <-> (\Top h).
Proof.
  (* ADMITTED *)
  intros. split.
  { intros (h1&h2&P1&P2&D&E). hnf. auto. }
  { intros M. exists h (fmap_empty:heap). splits.
    { hnf. auto. }
    { hnf. auto. }
    { fmap_disjoint. }
    { fmap_eq. } }
Qed.
  (* /ADMITTED *)

(** [] *)

(* EX2? (htop_iff_hexists_heap) *)
(** Prove that a heap satisfies the heap predicate [\[Top]] if and
    only if it satisfies the predicate [\exists (H:hprop), H]. *)

Lemma htop_iff_hexists_hprop : forall (P:Prop) (h:heap),
  (\Top h) <-> (\exists H, H) h.
Proof.
  (* ADMITTED *)
  intros. split.
  { intros M. exists (= h). auto. }
  { intros (H&M). hnf. auto. }
Qed.
  (* /ADMITTED *)

(** [] *)




(*

(** * Heap entailment *)

Set Implicit Arguments.
Require Import LibCore TLCbuffer Fmap.
Require Import Semantics SepBase.


(** * Heap entailment *)

CHANGE

Notation "P ==> Q" := (pred_incl P Q)
  (at level 55, right associativity) : heap_scope.

(* [rel_incl'] is like TLC's [rel_incl] but defined in terms of [pred_incl]
   so that after [intros r] we get an entailment. *)

Definition rel_incl' A B (P Q:A->B->Prop) :=
  forall r, pred_incl (P r) (Q r).

Notation "P ===> Q" := (rel_incl' P Q)
  (at level 55, right associativity) : heap_scope.

Open Scope heap_scope.


(* ---------------------------------------------------------------------- *)
(* ** Examples of entailment *)


r -> 6 * s -> 3 ==> s -> 3 * r -> 6

FALSE : r -> 3 ==> s -> 4 * r -> 3

negation: H1 h /\ ~ H2 h
  ~ (s -> 4 * r -> 3)
  forall h1 h2, ~ .. \/ ~ .. \/ ~ ...

  ~ A \/ ~ B \/ ~ C
  equiv to A -> B -> C -> False.

  r -> 3 means h1 has domain r
  s -> 4 means h2 has domain s

  if r = s, then disjoint entails false
  if r <> s, then h = h1 \u h2 = {r} \u {s}
    dom h = {r}



\[False] ==> r -> 6

FALSE:   r -> 3 \* s -> 4 ==> \[False]

r -> 3 \* r -> 4 ==> \[False]
r -> 3 \* r -> 3 ==> \[False]






(* ---------------------------------------------------------------------- *)
(* ** Properties of entailment *)


Section HimplProp.
Variable A : Type.
Implicit Types H : A -> Prop.

Hint Unfold pred_incl.

(** Entailment is reflexive, symmetric, transitive *)

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. intros h. auto. Qed.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using. introv M1 M2. intros h H1h. eauto. Qed.

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  (H1 = H2).
Proof using. introv M1 M2. applys pred_ext_1. intros h. iff*. Qed.

(** Paragraphe of the definition, used by tactics *)

Lemma himpl_inv : forall H1 H2 (h:A),
  (H1 ==> H2) ->
  (H1 h) ->
  (H2 h).
Proof using. auto. Qed.


Lemma refl_rel_incl' : forall A B (Q:A->B->Prop),
  Q ===> Q.
Proof using. apply refl_rel_incl. Qed.



(* ---------------------------------------------------------------------- *)
(* ** A detour : extensionality *)

(* SLIDE: extensionality *)






(* ---------------------------------------------------------------------- *)
(* ** Fundamental properties of hprop *)

Lemma hstar_comm : forall H1 H2,
   H1 \* H2 = H2 \* H1.
Proof using.
  intros H1 H2. unfold hprop, hstar. extens. intros h.
  iff (h1&h2&M1&M2&D&U); rewrite~ heap_union_comm in U; exists* h2 h1.
Qed.

Lemma hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof using.
  intros H1 H2 H3. applys hprop_extens. intros h. split.
  { intros (h'&h3&(h1&h2&M3&M4&D'&U')&M2&D&U). subst h'.
    exists h1 (h2 \+ h3). splits~. { exists* h2 h3. } }
  { intros (h1&h'&M1&(h2&h3&M3&M4&D'&U')&D&U). subst h'.
    exists (h1 \+ h2) h3. splits~. { exists* h1 h2. } }
Qed.

Lemma hstar_hempty_l : forall H,
  hempty \* H = H.
Proof using.
  intros. applys hprop_extens. intros h.
  iff (h1&h2&M1&M2&D&U) M.
  { forwards E: hempty_inv M1. subst.
    rewrite~ heap_union_empty_l. }
  { exists~ heap_empty h. }
Qed.


Lemma hstar_hexists : forall A (J:A->hprop) H,
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof using.
  intros. applys hprop_extens. intros h. iff M.
  { destruct M as (h1&h2&(x&M1)&M2&D&U). exists~ x h1 h2. }
  { destruct M as (x&(h1&h2&M1&M2&D&U)). exists h1 h2. splits~. exists~ x. }
Qed.

Lemma himpl_frame_l : forall H2 H1 H1',
  H1 ==> H1' ->
  (H1 \* H2) ==> (H1' \* H2).
Proof using. introv W (h1&h2&?). exists* h1 h2. Qed.



lemma transitive + frame
  h1 ==> h2
  x ==> h1 * r
  h2 \* x => y
  x==> y

(* SLIDE: heap-entailment-properties *)


(* ---------------------------------------------------------------------- *)
(* ** example with instantiation and extrusion *)


check out the "derived" states from previous chapter,
and insert them here as exercises

unfolding/folding of lists/trees give exercises

split rule on segments


r -> 6 ==> hexists n, r -> n \* even n

hexists n, r -> n  ==> r --> 3   [FALSE]




illustration for tactics:

exists n , r -> n \* n > 0  ==>  exists n, n > 1 \* r -> (n-1)

r -> 3 * s -> r ==> hexists n, r -> n * s -> n





illustration for hchange

lemma : r -> a \* r -> b = false.

exists n, n > 0 \* n < 0 \* r -> n ==> r -> n * r -> n





(* SLIDE: structural-rules *)


(*--cover all structural rules*)
(*--cover splitting rules for segments *)

(* SLIDE: splitting-rule-for-list-segments *)





(** * Separation algebra *)

(** ** Entailment between heap predicates *)


(** ** Equality between heap predicates *)



(** ** [rew_heap] tactic *)

(** ** Algebra of heap predicates *)

(** ** Frame for heap predicates *)

(* + simplification rule *)


(** ** Extraction rules *)

(** ** Examples of heap entailment *)

(* + quiz *)


(** ** Simplification tactic [himpl] *)

(** ** Rewriting tactic [hchange] *)




(* ---------------------------------------------------------------------- *)
(* ** Frame and consequence *)

Lemma triple_conseq : forall t H' Q' H Q,
  H ==> H' ->
  triple t H' Q' ->
  Q' ===> Q ->
  triple t H Q.
Proof using.
  introv MH M MQ. intros HF h N.
  forwards (h'&v&R&K): (rm M) HF h. { hhsimpl~. }
  exists h' v. splits~. { hhsimpl. hchanges (MQ v). }
Qed.

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using.
  introv M. intros HF h N. rewrite hstar_assoc in N.
  forwards (h'&v&R&K): (rm M) (H' \* HF) h. { hhsimpl~. }
  exists h' v. splits~. { hhsimpl~. }
Qed.


check out the "derived" triples from previous chapter,
and insert them here as exercises




(* ---------------------------------------------------------------------- *)
(* ** Extraction rules *)

Lemma triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall x, triple t (J x) Q) ->
  triple t (hexists J) Q.
Proof using.
  introv M. intros HF h N. rewrite hstar_hexists in N.
  destruct N as (x&N). applys* M.
Qed.

Lemma triple_hprop : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.
Proof using.
  intros t. applys (triple_hprop_from_hexists (triple t)).
  applys triple_hexists.
Qed.

independent proofs

as exercise, proof via the equivalence.


(* ---------------------------------------------------------------------- *)
(* ** Combined structural rule *)

exercise

(* ---------------------------------------------------------------------- *)
(* ** Garbage collection *)

support in hsimpl for \Top

Lemma triple_htop_post : forall t H Q,
  triple t H (Q \*+ \Top) ->
  triple t H Q.
Proof using.
  introv M. intros HF h N. forwards* (h'&v&R&K): (rm M) HF h.
  exists h' v. splits~. { rewrite <- htop_hstar_htop. hhsimpl. }
Qed.

Lemma triple_htop_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \Top) Q.
Proof using.
  introv M. applys triple_htop_post. applys~ triple_frame.
Qed.






*)