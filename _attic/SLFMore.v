
Parameter example_trm_red : forall m,
  eval m (trm_app example_trm' (val_bool false)) m (val_int 1).



Definition assertion := state -> Prop.
Definition Hoare_triple (H:assertion) (t:trm) (Q:val->assertion) : Prop :=
  forall h, H h ->
  exists v h', eval h t h' v /\ Q v h'.
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
  exists v h', eval h t h' v /\ (Q v \* H') h'.

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
  exists v h', eval h t h' v /\ (Q v \* H') h'.

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
  exists v h', eval h t h' v /\ (Q v \* H') h'.

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
  exists v h', eval h t h' v /\ (Q v \* \Top \* H') h'.

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




(** The lemma below provides an alternative presentation of the
    same result. Prove that it is derivable from [triple_htop_post]. *)

(* EX2! (triple_any_post) *)

Lemma triple_any_post : forall t H Q Q',
  triple t H (fun v => Q v \* Q' v) ->
  triple t H Q. (* i.e., [triple t H (fun v => Q v)] *)
Proof using.
(* SOLUTION *)
  introv M. applys triple_htop_post. applys triple_conseq M.
  { applys himpl_refl. }
  { intros v. applys himpl_frame_r. apply himpl_htop_r. }
(* /SOLUTION *)
Qed.

(** Reciprocally, [triple_htop_post] is derivable from [triple_any_post].
    Thus, the two lemmas are really equivalent. *)

Lemma triple_htop_post_derived_from_triple_any_post : forall t H Q,
  triple t H (Q \*+ \Top) ->
  triple t H Q.
Proof using.
  introv M. applys triple_conseq.
  applys triple_any_post M. (* instantiate Q' as [(fun (v:val) => \Top)] *)
  { applys himpl_refl. }
  { applys qimpl_refl. } 
Qed.



(** * Syntax and semantics *)

(** In order to give a formal presentation of assertions (a.k.a.
    heap predicates) and triples, we need to introduce the syntax
    and semantics of the source language used throughout this course. *)

(** ** Syntax of the source language *)

(** To begin with, we load appropriate definitions from the TLC library. *)

Set Implicit Arguments.
Require Import LibCore TLCbuffer Fmap.
Close Scope fmap_scope.

(** Program variables are represented using natural numbers. *)

Definition var := nat.

(** Locations are also represented as natural numbers. The [null] pointer
    corresponds to the address zero. *)

Definition loc := nat.
Definition null : loc := 0%nat.

(** The language includes a number of basic primitive functions.
    The list of such builtin functions appears next. *)

Inductive prim : Type :=
  | val_get : prim      (* read in a memory cell *)
  | val_set : prim      (* write in a memory cell *)
  | val_ref : prim      (* allocate a single memory cell *)
  | val_alloc : prim    (* allocate a range of cells *)
  | val_eq : prim       (* comparison *)
  | val_add : prim      (* addition *)
  | val_sub : prim      (* substraction *)
  | val_mul : prim      (* multiplication *)
  | val_div : prim      (* division *)
  | val_ptr_add : prim. (* pointer addition *)

(** Values of the programming language include:
    - the unit value (like in OCaml, similar to [void] type in C);
    - the boolean values (true and false);
    - integer values, which are assumed for simplicity to be idealized
      (unbounded) integers, without arithmetic overflow---the [int] type
      is provided by the TLC library, as an alias for the type [Z], which
      is the integer type provided by Coq's standard library;
    - locations, a.k.a. pointer values,
    - primitive functions, whose grammar was shown above,
    - functions, of the form [val_fun x t], with argument [x] and body [t],
    - and recursive functions, of the form [val_fix f x t], where [f]
      denotes the name of the function in recursive calls.

    Due to the presence of functions, the grammars of values is mutually
    recursive with the grammar of terms. A term may be:
    - a value, i.e. one object from the above grammar of values;
    - a program variable, i.e. a token that may get replaced by a value
      during a substitution operation;
    - a function definition, of the form [trm_fun x t]; such functions
      are intended to become values of the form [val_fun x t], once
      substitutions of the free variables of the function have been performed;
    - a recursive function definition, of the form [trm_fix f x t];
    - a conditional, of the form [trm_if t1 t2 t3], written in concrete
      syntax as [If t1 Then t2 Else t3];
    - a sequence, of the form [trm_seq t1 t2], also written [t1 ;; t2];
    - a let-binding, of the form [trm_let x t1 t2], also written
      [Let x := t1 in t2];
    - an application, of the form [trm_app t1 t2], which may be written
      simply as [t1 t2], thanks to the coercion mechanism introduced further;
    - a while loop, of the form [trm_while t1 t2], also written
      [While t1 Do t2 Done];
    - a for loop, of the form [trm_for x t1 t2 t3], also written
      [For x := t1 To t2 Do t3 Done].


    The corresponding grammar appears next.
*)

Inductive val : Type :=
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_prim : prim -> val
  | val_fun : var -> trm -> val
  | val_fix : var -> var -> trm -> val

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fun : var -> trm -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm
  | trm_seq : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_while : trm -> trm -> trm
  | trm_for : var -> trm -> trm -> trm -> trm.


(** ** Coercions for terms and values *)

(** _Coercions_ help writing concrete terms more succinctly.
    For example, thanks to the coercions defined further below,
    instead of writing:
[[
  trm_app (trm_val (val_prim val_ref)) (trm_val (val_int 3))
]]
    it suffices to write:
[[
  val_ref 3
]]
    Coq is able to automatically insert the appropriate constructors where
    required for the term to type-check correctly.

    The list of coercions in use appears next.
*)

Coercion val_prim : prim >-> val.
Coercion val_bool : bool >-> val.
Coercion val_int : Z >-> val.
Coercion val_loc : loc >-> val.
Coercion trm_val : val >-> trm.
Coercion trm_var : var >-> trm.
Coercion trm_app : trm >-> Funclass.

(** Given an expression, we may ask Coq to display the coercions that it
    has automatically inferred. For example, consider the definition
    shown below. Activate the [Set Printing Coercions] option, and observe
    the result of making the query [Print coercion_example]. *)

Example coercion_example : trm :=
  val_ref 3.


(** ** Representation of the heap *)

(** The mutable state of a program is represented as a finite map from location
    to values. *)

Definition state := fmap loc val.

(** The details of the implementation of finite maps (type [fmap]) is not
    relevant to the present course. The curious reader may find the definition
    in the file [Fmap.v]. In this chapter, we only need to know about the
    main operations for manipulating finite maps.

    - [state_empty] describes the empty finite map.

    - [state_single l v] describes a finite map with a single entry
      that binds location [l] to value [v].

    - [state_union h1 h2] describes the union of two finite maps;
      in case of overlap, bindings from the first argument are kept.

    - [state_disjoint h1 h2] asserts that two finite maps have disjoint
      domains, i.e. that they do not overlap.

*)

(** ** Evaluation predicate *)

(** The evaluation rules are standard. They define an evaluation
    judgment, written [eval h t h' v], which asserts that the
    evaluation of the term [t] starting in memory state [h] does
    terminate and produces the value [v] in the final state [h'].
    Note that the arguments [h] and [h'] of [eval] describe the full
    memory state. *)

Parameter eval : state -> trm -> state -> val -> Prop.

(** Rather than reproducing here pages of standard definitions, we will
    present the evaluation rules as we need them. Details may be found in
    the file [Semantics.v], which contains the recursive definition of
    capture-avoiding substitution and the inductive definition of the
    evaluation rules. *)


(** * From Hoare triples to Separation Logic triples *)

(** ** Hoare triples for terms with an output value **)

(** In what follows, we adapt Hoare triples to terms, which, unlike
    commands, always produce an output value.

    Recall the grammar of assertions: *)

Definition assertion := state -> Prop.

(** Recall the definition of a partial correctness Hoare triple for a
    programming language based on commands (i.e. with statements that
    do not return an output value) from Volume 2. It asserts that if the
    precondition is satisfied, and if the program terminates, then the
    postcondition holds:

[[
  Definition Hoare_triple_com_partial (H:assertion) (c:com) (Q:assertion) : Prop :=
    forall h h', H h -> ceval h c h' -> Q h'.
]]

    In this course, we focus on total correctness, which brings stronger
    guarantees, as it enforces termination. The definition of Hoare triple
    may be easily adapted to total correctness, to assert the following:
    if the precondition is satisfied, then the program terminates, and
    the postcondition holds. In the formal definition below, observe
    that the output heap [h'] now gets quantified existentially in the
    conclusion.

[[
  Definition Hoare_triple_com_total (H:assertion) (c:com) (Q:assertion) : Prop :=
    forall h, H h ->
    exists h', ceval h c h' /\ Q h'.
]]

   The definition above assumes a language of commands, in which terms do not
   produce any output value. How should the definition of Hoare triple be adapted
   to handle terms that produce an output value?

   The output value, call it [v], needs to be quantified existentially
   like the output heap. The evaluation predicate becomes [eval h t h' v].
   The postcondition [Q h'] also needs to be extended, so that Hoare triple
   may be used to specify the output value of the term [t]. We achieve this
   by passing [v] as first argument to the postcondition [Q]. In other words,
   we update the type of the postcondition from [assertion] to
   [val -> assertion].

   In summary, the definition of Hoare triples gets adapted as follows.

*)

Definition Hoare_triple (H:assertion) (t:trm) (Q:val->assertion) : Prop :=
  forall h, H h ->
  exists v h', eval h t h' v /\ Q v h'.




(** The proof will also requires evaluating variable comparisons.
    Indeed, the rules for let bindings and the rule for function
    application ([triple_let] and [triple_app_fun]) involves 
    substitutions (function [subst]), which is defined in terms
    of variable comparisons. For technical reasons, these 
    comparisons are not computable by default, so we need an
    explicit rewriting step in order to make them compute in Coq.
    The tactic [simpl_subst] defined next is a generalization
    of [simpl] that takes care of these details. *)

Lemma If_eq_bind_var : forall x y t1 t2,
    (If bind_var x = bind_var y then t1 else t2) 
  = (if var_eq x y then t1 else t2).
Proof using.
  intros. rewrite var_eq_spec. do 2 case_if; auto.
Qed.

Lemma If_eq_var : forall x y t1 t2,
    (If x = y then t1 else t2) 
  = (if var_eq x y then t1 else t2).
Proof using.
  intros. rewrite var_eq_spec. do 2 case_if; auto.
Qed.

Ltac simpl_subst :=
  simpl; unfold string_to_var;
   repeat rewrite If_eq_bind_var;
   repeat rewrite If_eq_var; simpl.






(** Because we are working with heap predicates, and that "negative"
    heap predicates don't quite make sense, we have to be careful.
    Essentially, our arithmetic interpretation [ -H1 + H2] should be
    intrepreted on natural numbers (N) and not on integers (Z).
    We are only allowed to reason about a subtraction [ -H1 + H2]
    if we can somehow justify that H1 is "not smaller than" H2.

    When working on natural numbers, it is not correct to replace
    a number [n] with [(n-m)+m] for some arbitrary [m]. As counter-
    example, take any value [m] greater than [n]. *)

Section TestSubtractionNat.
Open Scope nat_scope.

Lemma counterexample : exists n m, 
  n <> (n-m)+m.
Proof using. exists 0 1. intros N. simpl in N. false. Qed.

End TestSubtractionNat.






(** The pattern of the above lemma will be repeated for all terms.
    To capture this pattern, let us say that a formula [F] is sound
    for a term [t] iff [H ==> F Q] entails [triple t H Q]. *)

Definition formula_complete_for (t:trm) (F:formula) : Prop :=
  forall H Q, triple t H Q -> H ==> F Q .

Definition formula_complete_for' (t:trm) (F:formula) : Prop :=
  forall Q, wp t Q ==> F Q .

(** We can reformulate the lemma above as: *)

Lemma wpgen_val_complete : forall v,
  formula_complete_for (trm_val v) (wpgen_val v).
Proof using.
  introv M. unfold wpgen_val. unfolds triple, hoare.
Qed.


Lemma wp_htop_pre : forall t Q,
  (wp t Q) \* \Top ==> wp t Q.
Proof using.
  intros. rewrite <- wp_equiv.
  applys triple_htop_pre. rewrite~ wp_equiv.
Qed.


Lemma wp_htop_post : forall t Q ,
  wp t (Q \*+ \Top) ==> wp t Q.
Proof using.
  intros. rewrite <- wp_equiv.
  applys triple_htop_post. rewrite~ wp_equiv.
Qed.



Search List.fold_left.
Axiom List_fold_left_eq : forall A B (f:B->A->B) (i:B) (l:list A),
  List.fold_left f l i = LibList.fold_left (fun x a => f a x) i l.

Lemma msubst_let : forall (x:var) t1 t2 E,
     msubst E (trm_let x t1 t2)
  = trm_let x (msubst E t1) (msubst (rem_var x E) t2).
Proof using.
  intros. unfold msubst at 1. rewrite List_fold_left_eq.
  gen t1 t2; induction E as [|[y v] E']; intros.
  { rew_listx. auto. }
  { rew_listx. simpl. rewrite var_eq_spec. case_if.
    { subst. applys IHE'. }
    { applys IHE'. } }
Qed.



Definition ctx : Type := list (var*val).

Definition msubst (E:ctx) (t:trm) :=
  List.fold_left (fun ti '(x,v) => subst x v ti) E t.

Fixpoint rem_var (x:var) (E:ctx) : ctx :=
  match E with
  | nil => nil
  | (y,v)::E' =>
      let E'' := rem_var x E' in
      if var_eq x y then E'' else (y,v)::E''
  end.

Fixpoint lookup (x:var) (E:ctx) : option val :=
  match E with
  | nil => None
  | (y,v)::E' => if var_eq x y
                   then Some v
                   else lookup x E'
  end.


Definition wpgen_var (E:ctx) (x:var) : formula :=
  match lookup x E with
  | None => wpgen_fail
  | Some v => wpgen_val v
  end.

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
 match t with

  | (* [trm_val v] => *)  trm_val v =>
       wpgen_val v

  | (* [trm_var x] => *)  trm_var x =>
       wpgen_var E x

  | (* [trm_fun x t1] => *)  trm_fixs bind_anon (x::nil) t1 =>
       wpgen_val (val_fun x (msubst (Ctx.rem_var x E) t1))

  | (* [trm_fix f x t1] => *)  trm_fixs (bind_var f) (x::nil) t1 =>
       wpgen_val (val_fix f x (msubst (Ctx.rem_var x (Ctx.rem_var f E)) t1))

  | (* [trm_if v0 t1 t2] => *)  trm_if (trm_val v0) t1 t2 =>
       wpgen_if v0 (wpgen E t1) (wpgen E t2)

  | (* [trm_seq t1 t2] => *)  trm_let bind_anon t1 t2 =>
       wpgen_seq (wpgen E t1) (wpgen E t2)

  | (* [trm_let x t1 t2] => *)  trm_let (bind_var x) t1 t2 =>
       wpgen_let (wpgen E t1) (fun X => wpgen (Ctx.add x X E) t2)

  | (* [trm_app t1 t2] => *)  trm_apps t1 (t2::nil) => 
       wp (msubst E t)

  | (* other terms are outside of the sub-language that we consider,
       so let us here pretend that they are no such terms. *)
    _ => wpgen_fail
  end.

(** We establish the soundness of [wpgen] by structural induction on [t].
    The induction principle that we wish to use is that associated
    with the sublanguage presented in [SLFRules], whose inductive
    definition comes with the following induction principle. *)

Parameter trm_induct : forall (P : trm -> Prop),
  (forall v, P (trm_val v)) ->
  (forall x, P (trm_var x)) ->
  (forall x t1 , P t1 -> P (trm_fun x t1)) ->
  (forall (f:var) x t1, P t1 -> P (trm_fix f x t1)) ->
  (forall t1, P t1 -> forall t2, P t2 -> P (trm_app t1 t2)) ->
  (forall t1, P t1 -> forall t2, P t2

 (trm_seq t1 t2)) ->
  (forall (x:var) t1, P t1 -> forall t2, P t2 -> P (trm_let x t1 t2)) ->
  (forall v t1, P t1 -> forall t2, P t2 -> P (trm_if v t1 t2)) ->  
  (forall t, P t).

(** The soundness lemma asserts that [H ==> wpgen t Q] implies
    [triple t H Q]. Equivalently, it can be formulated as:
    [forall t, formula_sound_for t (wpgen t)]. The proof consists
    of invoking all the soundness lemmas which we have proved
    previously. *)

Lemma isubst_rem_var : forall x v E t,
  subst x v (isubst (Ctx.rem_var x E) t) = isubst ((x, v) :: E) t.
Admitted.


Theorem wpgen_sound : forall E t,
  formula_sound_for (msubst E t) (wpgen E t).
Proof using.
  intros. gen E. induction t using trm_induct; intros.
  { skip. } (*  applys wpgen_val_sound. } *)
  { skip. }
(*   { simpl. applys wpgen_fun_sound. } *)
  { applys wpgen_fix_sound. }
  { applys wp_sound. }
  { applys wpgen_seq_sound.
    { applys IHt1. } 
    { applys IHt2. } }
  { applys wpgen_let_sound.
    { applys IHt1. }
    { intros v. rewrite isubst_rem_var. applys IHt2. } }
  { applys wpgen_if_sound. { applys IHt1. } { applys IHt2. } }
Qed.
Lemma ctx_equiv_refl : forall E,
  ctx_equiv E E.
Proof using. intros. hnf. auto. Qed.

Lemma ctx_equiv_nil_inv : forall E,
  ctx_equiv nil E ->
  E = nil.
Proof using.
  introv M. destruct E as [|(x,v) E'].
  { auto. } 
  { specializes M x. simpls. rewrite var_eq_spec in M.
    case_if; tryfalse. }
Qed.


Lemma ctx_equiv_refl : forall E,
  ctx_equiv E E.
Proof using. intros. hnf. auto. Qed.

Lemma ctx_equiv_nil_inv : forall E,
  ctx_equiv nil E ->
  E = nil.
Proof using.
  introv M. destruct E as [|(x,v) E'].
  { auto. } 
  { specializes M x. simpls. rewrite var_eq_spec in M.
    case_if; tryfalse. }
Qed.


------------
(*
Lemma msubst_rem_var : forall x v E t,
  msubst ((x, v) :: (Ctx.rem_var x E)) t = msubst ((x, v) :: E) t.
Proof using.
  intros. simpl. unfold msubst at 1. 
  gen t1 t2; induction E as [|[y v] E']; intros.
  { auto. }
  { simpl. rewrite var_eq_spec. case_if.
    { subst. applys IHE'. }
    { applys IHE'. } }
Qed.


Lemma msubst_rem_var : forall (x:var) t1 t2 E,
    msubst E (trm_let x t1 t2)
  = trm_let x (msubst E t1) (msubst (rem_var x E) t2).
Proof using.
  intros. unfold msubst at 1. 
  gen t1 t2; induction E as [|[y v] E']; intros.
  { auto. }
  { simpl. rewrite var_eq_spec. case_if.
    { subst. applys IHE'. }
    { applys IHE'. } }
Qed.




Lemma msubst_let : forall (x:var) t1 t2 E,
    msubst E (trm_let x t1 t2)
  = trm_let x (msubst E t1) (msubst (rem_var x E) t2).
Proof using.
  intros. unfold msubst at 1. 
  gen t1 t2; induction E as [|[y v] E']; intros.
  { auto. }
  { simpl. rewrite var_eq_spec. case_if.
    { subst. applys IHE'. }
    { applys IHE'. } }
Qed.
*)



(*
  | (* [trm_let x t1 t2] => *)  trm_let (bind_var x) t1 t2 =>
       wpgen_let (wpgen E t1) (fun X => wpgen (Ctx.add x X E) t2)

  subst x v (isubst (Ctx.rem_var x E) t) = isubst ((x, v) :: E) t.
*)

(** context 

Definition ctx : Type := list (var * val).

Check Ctx.empty : ctx.
Check Ctx.add : var -> val -> ctx -> ctx
Check Ctx.rem_var : var -> ctx -> ctx
Check Ctx.lookup : var -> ctx -> val

Check isubst : ctx -> trm -> trm.

Lemma isubst_empty : forall t,
  isubst Ctx.empty t = t.

Lemma isubst_add : forall x v E t,
  isubst (Ctx.add x v E) t = isubst E (subst x v t).

*)

Definition wpgen_var (E:ctx) (x:var) : formula :=
  match Ctx.lookup x E with
  | None => wpgen_fail
  | Some v => wpgen_val v
  end.


(* 
Import SyntaxAndSemantics. 
*)



Fixpoint wpgen (E:ctx) (t:trm) : formula :=
 match t with

  | (* [trm_val v] => *)  trm_val v =>
       wpgen_val v

  | (* [trm_var x] => *)  trm_var x =>
       wpgen_var E x

  | (* [trm_fun x t1] => *)  trm_fixs bind_anon (x::nil) t1 =>
       wpgen_val (val_fun x (isubst (Ctx.rem_var x E) t1))

  | (* [trm_fix f x t1] => *)  trm_fixs (bind_var f) (x::nil) t1 =>
       wpgen_val (val_fix f x (isubst (Ctx.rem_var x (Ctx.rem_var f E)) t1))

  | (* [trm_if v0 t1 t2] => *)  trm_if (trm_val v0) t1 t2 =>
       wpgen_if v0 (wpgen E t1) (wpgen E t2)

  | (* [trm_seq t1 t2] => *)  trm_let bind_anon t1 t2 =>
       wpgen_seq (wpgen E t1) (wpgen E t2)

  | (* [trm_let x t1 t2] => *)  trm_let (bind_var x) t1 t2 =>
       wpgen_let (wpgen E t1) (fun X => wpgen (Ctx.add x X E) t2)

  | (* [trm_app t1 t2] => *)  trm_apps t1 (t2::nil) => 
       wp (isubst E t)

  | (* other terms are outside of the sub-language that we consider,
       so let us here pretend that they are no such terms. *)
    _ => wpgen_fail
  end.

(** We establish the soundness of [wpgen] by structural induction on [t].
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
    [triple t H Q]. Equivalently, it can be formulated as:
    [forall t, formula_sound_for t (wpgen t)]. The proof consists
    of invoking all the soundness lemmas which we have proved
    previously. *)

Lemma isubst_rem_var : forall x v E t,
  subst x v (isubst (Ctx.rem_var x E) t) = isubst ((x, v) :: E) t.
Admitted.


Theorem wpgen_sound : forall E t,
  formula_sound_for (isubst E t) (wpgen E t).
Proof using.
  intros. gen E. induction t using trm_induct; intros.  
3: { simpl wpgen. simpl. }
  { applys wpgen_val_sound. }
  { skip. }
  { applys wpgen_fun_sound. }
  { applys wpgen_fix_sound. }
  { applys wp_sound. }
  { applys wpgen_seq_sound.
    { applys IHt1. } 
    { applys IHt2. } }
  { applys wpgen_let_sound.
    { applys IHt1. }
    { intros v. rewrite isubst_rem_var. applys IHt2. } }
  { applys wpgen_if_sound. { applys IHt1. } { applys IHt2. } }
Qed.

Corollary triple_of_wpgen : forall t H Q,
  H ==> wpgen Ctx.empty t Q ->
  triple t H Q.
Proof using. introv M. lets: wpgen_sound M. Admitted.








details...
[[
Fixpoint wpgen (t:trm) : formula :=
  match t with
  | trm_val v => mkflocal (fun Q => Q v)
  | trm_var x => mkflocal (fun Q => \[False])
  | trm_fun x t1 => mkflocal (fun Q => Q (val_fun x ))
  | trm_fix f x t1 => mkflocal (fun Q => Q (val_fix f x t1))
  | trm_if v0 t1 t2 => mkflocal (fun Q =>
       \exists (b:bool), \[v0 = val_bool b]
         \* (if b then (wpgen t1) Q else (wpgen t2) Q))
  | trm_seq t1 t2 => mkflocal (fun Q =>
       (wpgen t1) (fun X => (wpgen t2) Q))
  | trm_let x t1 t2 => mkflocal (fun Q =>
       (wpgen t1) (fun X => (wpgen (subst x X t2)) Q))
  | trm_app t1 t2 => mkflocal (fun Q => wp t)
  end.
]]



(** The reciprocal implication from [wp] to [wpgen] would be
    interesting to have, as it would justify the completeness of [wpgen].
    Completeness would show that any Separation Logic proof can be carried 
    out using [wpgen]. Yet, it is not a priority to try to formalize this 
    result in Coq for now. *)


    which is equivalent to:
[[
    forall v H Q,
    H ==> wpgen_val v Q ->
    triple (trm_val v) H Q.
]]

    The pattern is similar for all term constructs.



    To capture this pattern, let us say that a formula [F] is sound
    for a term [t] iff [H ==> F Q] entails [triple t H Q]. *)



    
Lemma mkflocal_erase' : forall F Q,
  F Q ==> mkflocal F Q.
Proof using. 
  intros. unfolds mkflocal.
  (* [hsimpl] solves the goal, but let's give more details.
     To prove [F Q ==> \exists Q', F Q' \* (Q' \--* Q \*+ \Top)],
     first instantiate [Q'] as [Q]. *)
  applys himpl_hexists_r Q.
  (* Then cancel out [F Q]. *)
  rewrite <- (hstar_hempty_r (F Q)) at 1.
  applys himpl_frame_r.
  (* Then the goal becomes equivalent to [Q \*+ \[] ===> Q \*+ \Top] *)
  apply qwand_intro. 
  (* Cancelling out [Q] on both sides *)
  intros x. applys himpl_frame_r.
  (* Remains [\[] ==> \Top] *)
  rewrite hgc_eq_htop. applys himpl_htop_r. (* TODO: [hgc] should not be exposed *)
Qed.

Lemma mkflocal_ramified' : forall F Q1 Q2,
  (mkflocal F Q1) \* (Q1 \--* Q2 \*+ \Top) ==> (mkflocal F Q2).
Proof using.
  intros. unfold mkflocal. 
  (* [hsimpl] solves the goal, but let's give more details. The goal is:
     [\exists Q', F Q' \* (Q' \--* Q1 \*+ \Top) \* (Q1 \--* Q2 \*+ \Top) ==>
      \exists Q', F Q' \* (Q' \--* Q2 \*+ \Top)].
  The [mkflocal] on the LHS existentially quantifies some [Q']. *)
  rewrite hstar_hexists. applys himpl_hexists_l. intros Q'.
  (* Let us use that same [Q'] to instantiate the existential quantifier
     from the [mkflocal] on the RHS. *)
  applys himpl_hexists_r Q'.
  (* There remains:
     [F Q' \* (Q' \--* Q1 \*+ \Top) \* (Q1 \--* Q2 \*+ \Top) ==>
      F Q' \* (Q' \--* Q2 \*+ \Top)]. We cancel out [F Q']. *)
  rewrite hstar_assoc. applys himpl_frame_r.
  (* From [Q' \--* (Q1 \*+ \Top)) \* (Q1 \--* (Q2 \*+ \Top)) ==> Q' \--* (Q2 \*+ \Top)]
     we could rewrite [(Q1 \--* Q2 \*+ \Top)] to [(Q1 \*+ \Top) \--* (Q2 \*+ \Top))]
     and conclude by cancelling out [Q1 \*+ \Top] *)
  apply qwand_intro. intros x.
  hchange (qwand_specialize x Q1 (Q2 \*+ \Top)).
  

  
(** Let us now explain how, to a goal of the form [H ==> mkflocal F Q],
    one can apply the structural rules of Separation Logic.
    Consider for example consequence-frame. *)

Parameter triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.

(** Reformulating this lemma in weakest precondition form gives us: *)

Lemma himpl_mkflocal_conseq_frame : forall H Q H1 H2 Q1 F,
  H1 ==> mkflocal F Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  H ==> mkflocal F Q.

(** Let us prove this lemma. *)

Arguments mkflocal_ramified : clear implicits.

Proof using.
  introv M WH WQ. hchange WH. hchange M. 
  applys himpl_trans. 2:{ applys mkflocal_ramified Q1. }
  applys himpl_frame_r. applys qwand_intro. hchanges WQ.
Qed.

Lemma mkflocal_ramified : forall F Q1 Q2,
  
Proof using. unfold mkflocal. hsimpl. Qed.



Lemma texan_triple_equiv' : forall t H A (Hof:val->A->hprop) (vof:A->val),
      (triple t H (fun r => \exists x, \[r = vof x] \* Hof r x))
  <-> (forall Q, H \* (\forall x, Hof (vof x) x \-* Q (vof x)) ==> wp t Q).
Proof using.
  intros. iff M.
  { intros Q. rewrite <- wp_equiv. applys triple_conseq_frame M.
    hsimpl. hsimpl. intros r x ->. hchanges (hforall_specialize x). }
  { match goal with |- triple _ _ ?Q => specializes M Q end.
    rewrite <- wp_equiv in M. applys triple_conseq_frame M. hsimpl.
  skip. hsimpl~. }
Qed.


Lemma wp_iff_hoare : forall t H Q,
      H ==> wp t Q
  <-> (forall H', hoare t (H \* H') (Q \*+ H' \*+ \Top)).
Proof using. intros. rewrite <- wp_equiv. unfold triple. iff*. Qed.



(** And derive an introduction rule for [formula_sound_for] in 
    terms of [hoare]. *)

Lemma formula_sound_for_of_hoare : forall t F,
  (forall Q H', hoare t ((F Q) \* H') (Q \*+ H' \*+ \Top)) ->
  formula_sound_for t F.
Proof using. 
  introv M. rewrite formula_sound_for_iff_wp.
  intros Q. rewrite wp_def. hsimpl (F Q). applys M.
Qed.


(* ####################################################### *)
(** * Additional contents *)

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

    To factorize statements and improve readibility during the
    inductive proof, let us introduce the following definition.
*)

Definition formula_sound_for (t:trm) (F:formula) : Prop :=
  forall H Q, H ==> F Q -> triple t H Q.

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

(** First, consider a value [v]. The formula [wpgen (trm_val v)]
    should be such that [H ==> wpgen (trm_val v) Q] entails
    [triple (trm_val v) H Q]. Recall rule [triple_val]. *)

Parameter triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.

(** [H ==> Q v] is a sufficient condition for [triple (trm_val v) H Q].
    Thus, we wish [H ==> wpgen (trm_val v) Q] to imply [H ==> Q v],
    for any [H]. To achieve this implication, it suffices to define
    [wpgen (trm_val v) Q] as [Q v].

    Recall that [wpgen_val v] describes the value of [wpgen (trm_val v)].
    Thus, [wpgen_val v] is a function that takes [Q] as argument,
    and returns the heap predicate [Q v]. *)

Definition wpgen_val (v:val) : formula := fun Q =>
  Q v.

(** Just to be sure, let us check the desired property. *)

Lemma triple_of_wpgen_val : forall v H Q,
  H ==> wpgen_val v Q ->
  triple (trm_val v) H Q.
Proof using.
  introv M. applys triple_val. unfolds wpgen_val. applys M.
Qed.

(** We can reformulate the lemma above using [formula_sound_for] as: *)

Lemma wpgen_val_sound : forall v,
  formula_sound_for (trm_val v) (wpgen_val v).
Proof using. introv M. applys triple_of_wpgen_val M. Qed.

(** Remark: ultimately, what we'd like to show for [wpgen] is:
    [forall t, formula_sound_for t (wpgen t)]. *)


(* ******************************************************* *)
(** ** Case of functions *)

(** Recall the rule for functions. It is almost exactly like
    that for values, the only difference beeing that the
    conclusion in on [trm_fun x t1] and the premise on [val_fun x t1]. *)

Parameter triple_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  triple (trm_fun x t1) H Q.

(** To handle functions in [wpgen], we can reuse the definition
    of [wpgen_val], and simply adapt the statement of soundness
    as follows. *)

Lemma wpgen_fun_sound : forall x t,
  formula_sound_for (trm_fun x t) (wpgen_val (val_fun x t)).
Proof using. introv M. unfolds wpgen_val. applys triple_fun M. Qed.

(** Likewise for recursive functions. *)

Parameter triple_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triple (trm_fix f x t1) H Q.

Lemma wpgen_fix_sound : forall f x t,
  formula_sound_for (trm_fix f x t) (wpgen_val (val_fix f x t)).
Proof using. introv M. unfolds wpgen_val. applys triple_fix M. Qed.


(* ******************************************************* *)
(** ** Case of sequences *)

(** Second, consider a sequence [trm_seq t1 t2].
    The formula [wpgen (trm_seq t1 t2)] should be such that
    [H ==> [wpgen (trm_seq t1 t2)] Q] entails
    [triple (trm_seq t1 t2) H Q].

    Recall that [wpgen (trm_seq t1 t2)] evaluates to
    [wpgen_seq (wpgen t1) (wpgen t2)]. The definition of
    [wpgen_seq] can be derived from that of [triple_seq]. 
    Recall that rule. *)

Parameter triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.

(** By induction hypothesis on the subterms, a [triple] for 
    [t1] or [t2] is equivalent to a [wpgen] entailment. 
    Replacing [triple t H Q] with [H ==> wpgen t Q] throughout
    the rule [triple_seq] gives us: 

[[
      H ==> wpgen t1 (fun v => H1) ->
      H1 ==> wpgen t2 Q ->
      H ==> wpgen_seq (wpgen t1) (wpgen t2) Q.
]]

    From there, let [F1] denote [wpgen t1] and [F2] denote [wpgen t2].
    Moreover, let us substitute away [H1], by presuming that [wpgen]
    is covariant in its second argument (just like [wp] is).
    We obtain:

[[
      H => F1 (fun r => F2 Q) ->
      H => wpgen_seq F1 F2
]]

    which simplifies to [F1 (fun v => F2 Q) ==> wpgen_seq F1 F2].
    This leads us to the following definition of [wpgen_seq]. *)

Definition wpgen_seq (F1 F2:formula) : formula := fun Q =>
  F1 (fun v => F2 Q).

(** Again, let us verify that we obtain the desired implication
    for [trm_seq t1 t2], assuming that we have sound formulae
    for the two subterms. *)

Lemma wpgen_seq_sound : forall F1 F2 t1 t2,
  formula_sound_for t1 F1 ->
  formula_sound_for t2 F2 ->
  formula_sound_for (trm_seq t1 t2) (wpgen_seq F1 F2).
Proof using.
  introv S1 S2 M. unfolds wpgen_seq. applys triple_seq.
  { applys S1. applys M. }
  { applys S2. applys himpl_refl. }
Qed.


(* ******************************************************* *)
(** ** Case of let-bindings *)

(** Consider now the case of a let-binding [trm_let x t1 t2].
    Handling this construct is a bit more involved due to the
    binding of the variable [x] in [t2].

    The formula [wpgen (trm_let x t1 t2)] should be such that
    [H ==> [wpgen (trm_let x t1 t2)] Q] entails
    [triple (trm_let x t1 t2) H Q]. 

    Recall the rule [triple_let]. *)

Parameter triple_let : forall x t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall v, triple (subst x v t2) (Q1 v) Q) ->
  triple (trm_let x t1 t2) H Q.

(** Replacing triples using [wpgen] entailements yields:

[[
      H ==> wpgen t1 Q1 ->
      (forall v, (Q1 v) ==> wpgen (subst x v t2) Q) ->
      H ==> wpgen (trm_let x t1 t2) Q.
]]

   The second premise can be reformuled as an entailment
   between [Q1] and another postcondition, as follows:
   [Q1 ===> (fun v => wpgen (subst x v t2) Q)].

   From there, by covariante of [wpgen], we can replace [Q1]
   with [fun v => wpgen (subst x v t2) Q] into the first premise
   [H ==> wpgen t1 Q1]. We obtain the implication:

[[
      H ==> (wpgen t1) (fun v => wpgen (subst x v t2) Q) ->
      H ==> wpgen (trm_let x t1 t2) Q.
]]

  Let [F1] denote [wpgen t1] and let [F2of] denote
  [fun v => wpgen (subst x v t2)). In other words,
  [F2of v Q] denotes [wpgen (subst x v t2) Q].
  After eliminating [H], the implication above thus simplifies to:
    [F1 (fun v => F2of v Q) ==> wpgen (trm_let x t1 t2) Q].
  This discussion suggests the following definitions:

[[
    Fixpoint wpgen (t:trm) : formula :=
      mkstruct 
      match t with
      | trm_let x t1 t2 => wpgen_let (wpgen t1) (fun v => wpgen (subst x v t2))
      ...
      end.
]]
    where [wgen_let] is defined as:
*)

Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := fun Q =>
  F1 (fun v => F2of v Q).

(** The soundness result takes the following form.
    It assumes that [F1] is a sound formula for [t1] and that
    [F2of v] is a sound formula for [subst x v t2], for any [v]. *)

Lemma wpgen_let_sound : forall F1 F2of x t1 t2,
  formula_sound_for t1 F1 ->
  (forall v, formula_sound_for (subst x v t2) (F2of v)) ->
  formula_sound_for (trm_let x t1 t2) (wpgen_let F1 F2of).
Proof using.
  introv S1 S2 M. unfolds wpgen_let. applys triple_let.
  { applys S1. applys M. }
  { intros v. applys S2. applys himpl_refl. }
Qed.


(* ******************************************************* *)
(** ** Case of variables *)

(** What should be the weakest precondition of a free variable [x]?
    There is no reasoning rule of the form [triple (trm_var x) H Q].
    Indeed, if a program execution reaches a dandling free variable,
    then the program is stuck.

    Yet, the weakest precondition for a variable needs to be defined,
    somehow. If we really need to introduce a reasoning rule for free
    variables, it could be one with the premise [False]:
[[
              False
      ----------------------
      triple (trm_var x) H Q
]]

    To mimic [False -> triple x H Q] using [wpgen], we would like:
    [False -> H ==> wp x Q]. This implication is equivalent to
    [\[False] \* H ==> wp x Q], or just [\[False] ==> wp x Q].
    This discussion suggests to define [wp x] as the formula
    [fun Q => \False].  Let us name [wpgen_fail] this formula. *)

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
    a variable [x], but in fact for any term [t].
    Indeed, if [H ==> \[False]], then [triple t H Q] is always true. *)

Lemma wpgen_fail_sound : forall t,
  formula_sound_for t wpgen_fail.
Proof using.
  intros. introv M. unfolds wpgen_fail.
  applys triple_conseq Q M.
  { rewrite <- (hstar_hempty_r \[False]). applys triple_hpure.
    intros N. false. }
  { applys qimpl_refl. }
Qed.


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

    "Obviously", [wp t] is always a sound formula for a term [t].
    Indeed, by definition of [wp], [H ==> wp t] implies [triple t H Q].
*)

Lemma wp_sound : forall t,
  formula_sound_for t (wp t).
Proof using. intros. introv M. rewrite wp_equiv. applys M. Qed.

(** Remark: recall that we consider terms in A-normal form, thus [t1]
    and [t2] are assumed to be variables at the point where [wgpen]
    reaches the application [trm_app t1 t2]. If [t1] and [t2] could
    be general terms, we would need to call [wpgen] recursively,
    essentially encoding [let x1 = t1 in let x2 = t2 in trm_app x1 x2]. *)


(* ******************************************************* *)
(** ** Case of conditionals *)

(** Consider a conditional in A-normal form: [trm_if v0 then t1 else t2],
    where [v0] denotes either a variable of a value. If [v0] is a variable,
    by the time the [wpgen] function reaches it, it should already have
    been substituted in by a value (recall the [subst] in the treatment
    of let-bindings). Thus, we may assume here [v0] to be a value.

    Moreover, in the expression [trm_if v0 then t1 else t2], if [v0] denotes
    anything else than a boolean value, then the term would be stuck.
    Thus, we may in fact assume that [exists b, v0 = val_bool b].

    Note, however, that the [wpgen] function could see a term of the form
    [trm_if v0 then t1 else t2] where [v0] denotes a Coq variable of type
    [val], for which there is not yet any fact available to assert that it
    is a boolean value. Thus, the [wpgen] function must not be restricted
    to handling only terms of the form [trm_if (val_bool b) then t1 else t2].

    Recall the reasoning rule for conditionals, more precisely the version
    expressed using a Coq if-then-else. *)

Parameter triple_if_case : forall b t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if (val_bool b) t1 t2) H Q.

(** Replacing triples using [wpgen] entailements yields:

[[
    H ==> wpgen (if b then t1 else t2) Q ->
    H ==> wpgen (trm_if (val_bool b) t1 t2) Q.
]]

    which simplifies to 

[[
    wpgen (if b then t1 else t2) Q ==> wpgen (trm_if (val_bool b) t1 t2) Q
]]

    We need to make appear [wpgen t1] and [wpgen t2] in the formula, so as
    to compute recursively the weakest preconditions for the subterm.
    To that end, we expand the Coq conditional as follows:

[[
    (if b then wpgen t1 Q else wpgen t2 Q) ==> wpgen (trm_if (val_bool b) t1 t2) Q
]]

    As explained earlier, we are actually seeking for a definition of
    [wpgen (trm_if v0 t1 t2) Q] and not just for [trm_if (val_bool b) t1 t2].
    We thus reformulate the above entailment as follows:

[[
        (\exists b, \[v0 = val_bool b]  (if b then wpgen t1 Q else wpgen t2 Q)
    ==> wpgen (trm_if v0 t1 t2) Q
]]

    This lattest entailment leads us the definition of [wpgen] for conditionals.
*)

Definition wpgen_if (v:val) (F1 F2:formula) : formula := fun Q =>
  \exists (b:bool), \[v = val_bool b] \* (if b then F1 Q else F2 Q).

(** With just a little work to extract the information captured in the
    [\exists (b:bool), \[v = val_bool b] ], we can prove [wpgen_if] 
    to be a sound formula for a conditional. *)

Lemma wpgen_if_sound : forall F1 F2 v0 t1 t2,
  formula_sound_for t1 F1 ->
  formula_sound_for t2 F2 ->
  formula_sound_for (trm_if v0 t1 t2) (wpgen_if v0 F1 F2).
Proof using.
  introv S1 S2 M. unfolds wpgen_if. 
  applys triple_conseq Q M; [|applys qimpl_refl].
  applys triple_hexists. intros b.
  applys triple_hpure. intros ->.
  applys triple_if_case. case_if.
  { applys S1. applys himpl_refl. }
  { applys S2. applys himpl_refl. }
Qed.



(* ####################################################### *)
(** * Appendix: direct soundness proofs [wpgen] *)

Module DirectSoundness.

(** In our construction, we have proved reasoning rules for
    [hoare], derived reasoning rules for [triple], then used
    the latter for proving the soundness of [wpgen].
    Yet, if our goal was only to set up [wpgen], we wouldn't
    need any result on [triple]. How much simpler would the
    construction be if we were to directly prove [wpgen] w.r.t.
    the weakest preconditions style reasoning rules from [SLFWPsem]?
    Let us investigate. *)

(** We next give an introduction rule for [formula_sound_for] in
    term of [wp]. *)

Lemma formula_sound_for_iff_wp : forall t F,
      formula_sound_for t F
  <-> (forall Q, F Q ==> wp t Q).
Proof using.
  intros. iff N.
  { intros Q. rewrite <- wp_equiv. applys N. hsimpl. }
  { introv M. rewrite wp_equiv. hchange M. applys N. }
Qed.

(** Let us now tackle the main lemmas for the soundness of [wpgen].
    We begin with the soundness of [mkstruct]. *)

Lemma mkstruct_sound : forall t F,
  formula_sound_for t F ->
  formula_sound_for t (mkstruct F).
Proof using.
  introv M. rewrite formula_sound_for_iff_wp in *. intros Q.
  unfold mkstruct. hsimpl. intros Q'. hchange M. applys wp_ramified.
Qed.

(** We next show that [wp] is sound. *)

Lemma wp_sound : forall t,
  formula_sound_for t (wp t).
Proof using. intros. rewrite formula_sound_for_iff_wp. hsimpl. Qed.

(** We also show that [wpgen_fail] is sound. *)

Lemma wpgen_fail_sound : forall t,
  formula_sound_for t wpgen_fail.
Proof using.
  intros. rewrite formula_sound_for_iff_wp.
  unfolds wpgen_fail. hsimpl.
Qed.

(** We now turn to treat each term construct. *)

Lemma wpgen_val_sound : forall v,
  formula_sound_for (trm_val v) (wpgen_val v).
Proof using.
  intros. rewrite formula_sound_for_iff_wp. intros Q H'.
  unfolds wpgen_val. applys wp_val. hsimpl.
Qed.

Lemma wpgen_fun_sound : forall x t,
  formula_sound_for (trm_fun x t) (wpgen_val (val_fun x t)).
Proof using.
wp_fun
Qed.

Lemma wpgen_fix_sound : forall f x t,
  formula_sound_for (trm_fix f x t) (wpgen_val (val_fix f x t)).
Proof using.
wp_fix
Qed.



Lemma wpgen_seq_sound : forall F1 F2 t1 t2,
  formula_sound_for t1 F1 ->
  formula_sound_for t2 F2 ->
  formula_sound_for (trm_seq t1 t2) (wpgen_seq F1 F2).
Proof using.
  introv S1 S2. rewrite formula_sound_for_iff_wp in *. intros Q.
  unfold wpgen_seq. applys himpl_trans wp_seq. hchange S1.
  applys wp_conseq. intros _. applys S2.
Qed.

Lemma wpgen_let_sound : forall F1 F2of x t1 t2,
  formula_sound_for t1 F1 ->
  (forall v, formula_sound_for (subst x v t2) (F2of v)) ->
  formula_sound_for (trm_let x t1 t2) (wpgen_let F1 F2of).
Proof using.
  introv S1 S2. rewrite formula_sound_for_iff_wp in *. intros Q.
  unfold wpgen_let. applys himpl_trans wp_let. hchange S1.
  applys wp_conseq. intros v. specializes S2 v.
  rewrite formula_sound_for_iff_wp in S2. applys S2.
Qed.

Lemma wpgen_if_sound : forall F1 F2 v0 t1 t2,
  formula_sound_for t1 F1 ->
  formula_sound_for t2 F2 ->
  formula_sound_for (trm_if v0 t1 t2) (wpgen_if v0 F1 F2).
Proof using.
  introv S1 S2. rewrite formula_sound_for_iff_wp in *. intros Q.
  unfold wpgen_if. hsimpl ;=> b ->. applys himpl_trans wp_if.
  case_if. { applys S1. } { applys S2. }
Qed.

End DirectSoundness.


(* EX2! (himpl_mkstruct_htop) *)
(** Prove the following reformulation of the garbage collection
    rule for postcondition in weakest-precondition style. *)

Lemma himpl_mkstruct_htop : forall H Q F,
  H ==> mkstruct F (Q \*+ \Top) ->
  H ==> mkstruct F Q.
Proof using.
(* SOLUTION *)
  introv M. hchange M. 
  lets N: mkstruct_ramified (Q \*+ \Top) Q F. hchanges N.
(* /SOLUTION *)
Qed.






Parameter repr : forall A, (A->hprop) -> A -> hprop.

Parameter Id : forall A, A -> A -> hprop.
Notation "x '~>' S" := (repr S x)
  (at level 33, no associativity) : heap_scope.


Parameter repr_id : forall A (x X:A),
  (x ~> Id X) = \[x = X].


  
Parameter himpl : hprop -> hprop -> Prop.

Definition qimpl A (Q1 Q2:A->hprop) :=
  forall r, himpl (Q1 r) (Q2 r).

Notation "H1 ==> H2" := (himpl H1 H2)
  (at level 55) : heap_scope.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2)
  (at level 55) : heap_scope.

  
(* ---------------------------------------------------------------------- *)
(** Auxiliary tactics used by many tactics *)

(* [xprecondition tt] returns the current precondition. *)

Ltac xprecondition tt :=
  match goal with |- ?R ?H ?Q => constr:(H) end.

(* [xpostcondition tt] returns the current postcondition. *)

Ltac xpostcondition tt :=
  match goal with |- ?E =>
  match get_fun_arg E with (_,?Q) => constr:(Q)
  end end.
  (* LATER: is this now equivalent to:
     match goal with |- ?J ?Q => constr:(Q) end. *)

(** [xpostcondition_is_evar tt] returns a boolean indicating
    whether the postcondition of the current goal is an evar. *)

Ltac xpostcondition_is_evar tt :=
  let Q := xpostcondition tt in
  is_evar_as_bool Q.

  
(* not needed *)
Lemma hwand_cancel_part : forall H1 H2 H3,
  H1 \* ((H1 \* H2) \-* H3) ==> (H2 \-* H3).
Proof using.
  intros. hsimpl.
  (* intros. unfold hwand. hsimpl. hsimpl ;=> H4 M. hchanges M. *)
Qed.

Arguments hwand_cancel_part : clear implicits.

(* not needed *)
Lemma himpl_hwand_r_inv_part_r : forall H1 H2 H3 H4,
  H2 ==> ((H1 \* H3) \-* H4) ->
  H1 \* H2 ==> (H3 \-* H4).
Proof using.
  introv M. hchanges M.
  (* hchange (>> himpl_frame_r H1 M).
  rew_heap. apply hwand_cancel_part.*)
Qed.

(* not needed *)
Lemma himpl_hwand_r_part_l : forall H1 H2 H3 H4,
  H1 \* H2 ==> (H3 \-* H4) ->
  H2 ==> ((H1 \* H3) \-* H4).
Proof using.
  introv M. hsimpl. hchanges M.
  (* unfold hwand. hsimpl. hchanges (himpl_hwand_r_inv M). *)
Qed.



Module Type HeapType.

Parameter heap : Type.
Definition hprop := heap -> Prop.

End HeapType.

Module EntailFunctor (HT:HeapType).
Import HT.

(** [H1 ==> H2] is defined as [forall h, H1 h -> H2 h]. *)

Definition himpl (H1 H2:hprop) : Prop :=
  forall (h:heap), H1 h -> H2 h.

Notation "H1 ==> H2" := (himpl H1 H2) (at level 55) : heap_scope.

Open Scope heap_scope.

Lemma himpl_refl : forall H,
  H ==> H.
Proof using. intros h. hnf. auto. Qed.

Lemma himpl_trans : forall H2 H1 H3,
  (H1 ==> H2) ->
  (H2 ==> H3) ->
  (H1 ==> H3).
Proof using. introv M1 M2. intros h H1h. eauto. Qed.

Lemma himpl_antisym : forall H1 H2,
  (H1 ==> H2) ->
  (H2 ==> H1) ->
  H1 = H2.
Proof using. introv M1 M2. applys pred_ext_1. intros h. iff*. Qed.

(** [Q1 ===> Q2] is defined as [forall x h, Q1 x h -> Q2 x h].
    It is thus equivalent to [forall x, Q1 x ==> Q2 x].
    Thus, invoking [intro] on a [===>] goal leaves a [==>] goal. *)

Definition qimpl A (Q1 Q2:A->hprop) : Prop :=
  forall (v:A), Q1 v ==> Q2 v.

Notation "Q1 ===> Q2" := (qimpl Q1 Q2) (at level 55) : heap_scope.

Open Scope heap_scope.

End EntailFunctor.



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


(* ---------------------------------------------------------------------- *)
(* ** Tactic [fmap_red] for proving [eval] goals
      (reduction according to a big-step semantics)
      modulo equalities between fmaps *)

(** [fmap_red] proves a goal of the form [eval h1 t h2 v]
    using an hypothesis of the shape [eval h1' t h2' v],
    generating [h1 = h1'] and [h2 = h2'] as subgoals, and
    attempting to solve them using the tactic [fmap_eq].
    The tactic should be configured depending on [eval].
    For example:

       Ltac fmap_red_base tt :=
        match goal with H: eval _ ?t _ _ |- eval _ ?t _ _ =>
          applys_eq H 2 4; try fmap_eq end.

    The default implementation is a dummy one.
*)

Ltac fmap_red_base tt := fail.

Tactic Notation "fmap_red" :=
  fmap_red_base tt.

Tactic Notation "fmap_red" "~" :=
  fmap_red; auto_tilde.

Tactic Notation "fmap_red" "*" :=
  fmap_red; auto_star.

  (* ---------------------------------------------------------------------- *)
(* ** Tactics for reductions *)

Ltac fmap_red_base tt ::=
  match goal with H: eval _ _ ?t _ _ |- eval _ _ ?t _ _ =>
    applys_eq H 2 4; try fmap_eq end.



(* ---------------------------------------------------------------------- *)
(* ** Tactic [fmap_red], defined in file [Fmap] for proving [eval] goals
      modulo equalities between states, gets instantiated here. *)

Ltac fmap_red_base tt ::=
  match goal with H: eval _ ?t _ _ |- eval _ ?t _ _ =>
    applys_eq H 2 4; try fmap_eq end.




Definition ctx_disjoint : ctx -> ctx -> Prop := 
  @LibListAssoc.disjoint var val.

(** [ctx_equiv E1 E2] asserts that the two contexts bind same
    keys to same values. *)

Definition ctx_equiv : ctx -> ctx -> Prop := 
  @LibListAssoc.equiv var val.


(** Basic properties of context operations follow. *)

Section CtxOps.

Lemma is_beq_var_eq :
  LibListAssocExec.is_beq var_eq.
Proof using. applys var_eq_spec. Qed.

Hint Resolve is_beq_var_eq.

Lemma ctx_equiv_eq : forall E1 E2,
  ctx_equiv E1 E2 = (forall x, lookup x E1 = lookup x E2).
Proof using.
  intros. extens. unfold lookup. iff M.
  { intros x. repeat rewrite LibListAssocExec.get_opt_eq; auto.  }
  { intros x. specializes M x. do 2 rewrite~ LibListAssocExec.get_opt_eq in M.  }
Qed.

Lemma ctx_disjoint_inv : forall E1 E2,
  ctx_equiv E1 E2 ->
  forall x, lookup x E1 = lookup x E2.
Proof using.
  introv M. intros x. unfold lookup. repeat rewrite~ LibListAssocExec.get_opt_eq.
Qed.

M : forall (x : var) (v1 v2 : val),
    LibListAssoc.get_opt x E1 = Some v1 -> LibListAssoc.get_opt x E2 = Some v2 -> False

Lemma ctx_disjoint_rem : forall x E1 E2,
  ctx_disjoint E1 E2 ->
  ctx_disjoint (rem x E1) (rem x E2).
Proof using.
  introv M. intros y v1 v2 M1 M2. unfolds in M.

Lemma wpgen_if_trm_sound : forall F0 F1 F2 t0 t1 t2,
  formula_sound_for t0 F0 ->
  formula_sound_for t1 F1 ->
  formula_sound_for t2 F2 ->
  formula_sound_for (trm_if t0 t1 t2) (wpgen_if_trm F0 F1 F2).
Proof using.
  introv S0 S1 S2. intros Q. unfold wpgen_if_trm, wpgen_let.
lets: wp_if.
  applys himpl_trans wp_if.
  applys S0.
  
  applys himpl_trans. applys wpgen_let_sound.

  applys himpl_trans wp_if. case_if. { applys S1. } { applys S2. }
Qed.


wpgen_if_trm (wpgen E t1) (wpgen E t2) (wpgen E t3) Q ==>
wp (trm_if (isubst E t1) (isubst E t2) (isubst E t3)) Q


unfolds in M.
  repeat rewrite LibListAssocExec.get_opt_eq in *.
Qed.





(** It would be equivalent to place the assumption [n2 <> 0] in the
    precondition, as shown below. *)

Parameter triple_div' : forall n1 n2,
  triple (val_div n1 n2)
    \[n2 <> 0]
    (fun r => \[r = val_int (Z.quot n1 n2)]).

(** In practice, we prefer placing pure assumptions outside of the triples,
    as it reduces the number of proof steps when exploiting the specification. *)



Lemma himpl_hwand_hpure_l : forall (P:Prop) H1 H2,
  P ->
  H1 ==> H2 ->
  \[P] \-* H1 ==> H2.
Proof using.
  introv HP M. applys himpl_trans M. applys~ hwand_hpure_l_intro.
Qed.

Arguments himpl_hwand_hpure_l : clear implicits.



(* DEPRECATED
Lemma wpgen_fun_sound : forall x t,
  formula_sound_for (trm_fun x t) (wpgen_val (val_fun x t)).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_fun. Qed.

Lemma wpgen_fix_sound : forall f x t,
  formula_sound_for (trm_fix f x t) (wpgen_val (val_fix f x t)).
Proof using. intros. intros Q. unfolds wpgen_val. applys wp_fix. Qed.
*)


       (* DEPRECATED wpgen_val (val_fun x (isubst (rem x E) t1)) *)


       (* wpgen_val (val_fix f x (isubst (rem x (rem f E)) t1)) *)

Lemma xcase_false_lemma : forall A (x:A) (G:Prop),
  x <> x -> G.
Proof using. introv N. false* N. Qed.

