(**

Separation Logic Foundations

Chapter: "Hprop".

This chapter introduces heap predicates, Separation Logic triples,
and the frame rule.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Export SLFExtra.

(** Configuration of Fmap.v *)

Arguments Fmap.single {A} {B}.
Arguments Fmap.union {A} {B}.
Arguments Fmap.disjoint {A} {B}.
Arguments Fmap.union_comm_of_disjoint {A} {B}.
Arguments Fmap.union_empty_l {A} {B}.
Arguments Fmap.union_empty_r {A} {B}.
Arguments Fmap.union_assoc {A} {B}.
Arguments Fmap.disjoint_union_eq_l {A} {B}.
Arguments Fmap.disjoint_union_eq_r {A} {B}.

Local Close Scope fmap_scope.
Local Open Scope string_scope.
Local Open Scope val_scope.
Local Open Scope trm_scope.
Local Coercion string_to_var (x:string) : var := x.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Chapter in a rush *)

(** In the programming language that we consider, a concrete
    memory state is described as a finite map from locations
    to values.

    - A location has type [loc].
    - A value has type [val].
    - A state has type [state].

    Details will be presented in the chapter [SLFRules].

    To help distinguish between full states and pieces of state,
    we let the type [heap] be a synonymous for [state] but with
    the intention of representing only a piece of state.
    Throughout the course, we write [s] for a full memory state
    (of type [state]), and we write [h] for a piece of memory state
    (of type [heap]).

    In Separation Logic, a piece of state is described by a
    "heap predicate", i.e., a predicate over heaps.
    A heap predicate has type [hprop], defined as [heap->Prop],
    which is equivalent to [state->Prop].

    By convention, throughout the course:

    - [H] denotes a heap predicate of type [hprop]; it describes a
      piece of state,
    - [Q] denotes a postcondition, of type [val->hprop]; it describes
      both a result value and a piece of state. Observe that
      [val->hprop] is equivalent to [val->state->Prop]. *)

(** This chapter presents the definition of the key heap predicate
    operators from Separation Logic:

    - [\[]] denotes the empty heap predicate,
    - [\[P]] denotes a pure fact,
    - [l ~~~> v] denotes a singleton heap,
    - [H1 \* H2] denotes the separating conjunction,
    - [Q1 \*+ H2] denotes the separating conjunction,
                   between a postcondition and a heap predicate,
    - [\exists x, H] denotes an existential.

   This chapter also introduces the formal definition of triples:

   - a Hoare triple, written [hoare t H Q], features a precondition [H] and
     a postcondition [Q] that describe the whole memory state in which the
     execution of the term [t] takes place.
   - a Separation Logic triple, written [triple t H Q], features a pre- and
     a postcondition that describes only the piece of the memory state
     in which the execution of the term [t] takes place.
 *)

(** This chapter and the following ones exploit a few additional TLC tactics
   to enable concise proofs.

   - [applys] is an enhanced version of [eapply].
   - [applys_eq] is a variant of [applys] that enables matching the
     arguments of the predicate that appears in the goal "up to equality"
     rather than "up to conversion".
   - [specializes] is an enhanced version of [specialize].
   - [lets] and [forwards] are forward-chaining tactics that
     enable instantiating a lemma.

   What these tactics do should be fairly intuitive where they are used.
   Note that all exercises can be carried out without using TLC tactics.
   For details, the chapter [UseTactics.v] from the "Programming Language
   Foundations" volume explains the behavior of these tactics.

*)


(* ########################################################### *)
(** ** Syntax and semantics *)

(** We assume an imperative programming language with a formal semantics.
    We do not need to know about the details of the language construct for now.
    All we need to know is that there exists:

    - a type of terms, written [trm],
    - a type of values, written [val],
    - a type of states, written [state] (i.e., finite map from [loc] to [val]),
    - a big-step evaluation judgment, written [eval h1 t h2 v], asserting that,
      starting from state [s1], the evaluation of the term [t] terminates in
      the state [s2] and produces the value [v].

[[
    Check eval : state -> trm -> state -> val -> Prop.
]]

    Remark: the corresponding definitions are described later in the chapter
    [SLFRules].
*)

(** At this point, we don't need to know the exact grammar of terms and values.
    Let's just give one example to make things concrete. Consider the function:
    [fun x => if x then 0 else 1].

    In the language that we consider, it can be written in raw syntax as
    follows. *)

Definition example_val : val :=
  val_fun "x" (trm_if (trm_var "x") (trm_val (val_int 0)) (trm_val (val_int 1))).

(** Thanks to a set of coercions and notation, this term can be written in a
    somewhat more readable way, as follows. *)

Definition example_val' : trm :=
  VFun "x" :=
    If_ "x" Then 0 Else 1.


(* ########################################################### *)
(** ** Description of the state *)

(** Locations, of type [loc], denote the addresses of allocated objects.
    Locations are a particular kind of values.

    A state is a finite map from locations to values.

    The file [Fmap] provides a self-contained formalization of
    finite maps, and of the associated operations on maps useful
    in Separation Logic reasoning. The file [SLFules] includes
    the following definition of [state].

[[
    Definition state : Type := fmap loc val.
]]
*)

(** By convention, we use the type [state] describes a full state of memory,
    and introduce the type [heap] to describe just a piece of state. *)

Definition heap : Type := state.

(** In particular, the library [Fmap.v] exports the following definitions.

    - [Fmap.empty] denotes the empty state,
    - [Fmap.single l v] denotes a singleton state, that is, a unique cell
      at location [l] with contents [v],
    - [Fmap.union h1 h2] denotes the union of the two states [h1] and [h2].
    - [Fmap.disjoint h1 h2] asserts that [h1] and [h2] have disjoint domains.

    The types of these definitions are as follows.

[[
    Check Fmap.empty : heap.

    Check Fmap.single : loc -> val -> heap.

    Check Fmap.union : heap -> heap -> heap.

    Check Fmap.disjoint : heap -> heap -> Prop.
]]

    Note that the union operation is commutative only when its two arguments
    have disjoint domains. Throughout the Separation Logic course, we will
    only consider disjoint unions, for which commutativity holds.

*)


(* ########################################################### *)
(** ** Heap predicates *)

(** In Separation Logic, the state is described using "heap predicates".
    A heap predicate is a predicate over a piece of state.
    Let [hprop] denote the type of heap predicates. *)

Definition hprop := heap -> Prop.

(** Thereafter, let [H] range over heap predicates. *)

Implicit Type H : hprop.

(** An essential aspect of Separation Logic is that all heap predicates
    defined and used in practice are built using a few basic combinators.
    In other words, except for the definition of the combinators themselves,
    we will never define a custom heap predicate directly as a function
    of the state. *)

(** We next describe the most important combinators of Separation Logic.
    Their use will be illustrated subsequently. For those who followed
    the "practical Separation Logic course" (files [CF*.v]), the combinators
    and the associated notation should already be familiar. *)

(** The heap predicate, written [\[]], characterizes an empty state. *)

Definition hempty : hprop :=
  fun (h:heap) => (h = Fmap.empty).

Notation "\[]" := (hempty) (at level 0).

(** The pure fact predicate, written [\[P]], characterizes an empty state
    and moreover asserts that the proposition [P] is true. *)

Definition hpure (P:Prop) : hprop :=
  fun (h:heap) => (h = Fmap.empty) /\ P.

Notation "\[ P ]" := (hpure P) (at level 0, format "\[ P ]").

(** The singleton heap predicate, written [l ~~> v], characterizes a
    state with a single allocated cell, at location [l], storing the
    value [v]. *)

Definition hsingle (l:loc) (v:val) : hprop :=
  fun (h:heap) => (h = Fmap.single l v).

Notation "l '~~~>' v" := (hsingle l v) (at level 32).

(** Remark: in the course of the proof of [MList_if] in chapter [SLFList],
    we have exploited the property that no data can be allocated at the
    [null] location. This invariant can be enforced in either of two manners:

    - The first possibility is to bake this invariant directly into the
      definition of [hsingle l v], as follows:
      [fun (h:heap) => (h = Fmap.single l v) /\ (l <> null)].
    - The second possibility is to enforce this invariant at a deeper level,
      in the type of [heap], a.k.a. [state], to ensure that a value of that
      type can never bind the [null] location.

    For simplicity, we will ignore throughout the rest of this course
    the requirement that allocated locations are not null. *)

(* LATER: check how much more complicated it would be to handle this formally. *)

(** The "separating conjunction", written [H1 \* H2], characterizes a
    state that can be decomposed in two disjoint parts, one that
    satisfies [H1], and another that satisfies [H2].
    In the definition below, the two parts are named [h1] and [h2]. *)

Definition hstar (H1 H2 : hprop) : hprop :=
  fun (h:heap) => exists h1 h2, H1 h1
                              /\ H2 h2
                              /\ Fmap.disjoint h1 h2
                              /\ h = Fmap.union h1 h2.

Notation "H1 '\*' H2" := (hstar H1 H2) (at level 41, right associativity).

(** The existential quantifier for heap predicates, written [\exists x, H]
    characterizes a heap that satisfies [H] for some [x].
    The variable [x] has type [A], for some arbitrary type [A].

    The notation [\exists x, H] stands for [hexists (fun x => H)].
    The generalized notation [\exists x1 ... xn, H] is also available.

    The definition of [hexists] is a bit technical. It is not essential
    to master it at this point. Additional explanations are provided
    near the end of this chapter. *)

Definition hexists (A:Type) (J:A->hprop) : hprop :=
  fun (h:heap) => exists x, J x h.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'").


(* ########################################################### *)
(** ** Extensionality for heap predicates *)

(** To work in Separation Logic, it is extremely convenient to be
    able to state equalities between heap predicates. For example,
    in the next chapter, we will establish the associativity property
    for the star operator, that is: *)

Parameter hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).

(** How can we prove a goal of the form [H1 = H2] when [H1] and [H2]
    have type [hprop], that is, [heap->Prop]?

    Intuitively, [H] and [H'] are equal if and only if they
    characterize exactly the same set of heaps, that is, if
    [forall (h:heap), H1 h <-> H2 h].

    This reasoning principle, a specific form of extensionality
    property, is not available by default in Coq. Yet, we can safely
    assume it if we extend the logic of Coq with a standard axiom
    called "predicate extensionality". *)

Axiom predicate_extensionality : forall (A:Type) (P Q:A->Prop),
  (forall x, P x <-> Q x) ->
  P = Q.

(** By specializing [P] and [Q] above to the type [hprop], we obtain
    exactly the desired extensionality principle. *)

Lemma hprop_eq : forall (H1 H2:hprop),
  (forall (h:heap), H1 h <-> H2 h) ->
  H1 = H2.
Proof using. applys predicate_extensionality. Qed.


(* ########################################################### *)
(** ** Type and syntax for postconditions *)

(** A postcondition characterizes both an output value and an output state.
    In Separation Logic, a postcondition is thus a relation of type
    [val -> state -> Prop], which is equivalent to [val -> hprop].

    Thereafter, we let [Q] range over postconditions. *)

Implicit Type Q : val -> hprop.

(** One common operation is to augment a postcondition with a piece of state.
    This operation is described by the operator [Q \*+ H], which is just a
    convenient notation for [fun x => (Q x \* H)]. *)

Notation "Q \*+ H" := (fun x => hstar (Q x) H) (at level 40).

(** Intuitively, in order to prove that two postconditions [Q1]
    and [Q2] are equal, it suffices to show that the heap predicates
    [Q1 v] and [Q2 v] (both of type [hprop]) are equal for any value [v].

    Again, the extensionality property that we need is not builtin in Coq.
    We need the axiom called "functional extensionality", stated next. *)

Axiom functional_extensionality : forall A B (f g:A->B),
  (forall x, f x = g x) ->
  f = g.

(** The desired equality property for postconditions follows directly
    from that axiom. *)

Lemma qprop_eq : forall (Q1 Q2:val->hprop),
  (forall (v:val), Q1 v = Q2 v) ->
  Q1 = Q2.
Proof using. applys functional_extensionality. Qed.


(* ########################################################### *)
(** ** Separation Logic triples and the frame rule *)

(** A Separation Logic triple is a generalization of a Hoare triple
    that integrate builtin support for an essential rule called
    "the frame rule". Before we give the definition of a Separation
    Logic triple, let us first give the definition of a Hoare triple
    and state the much-desired frame rule. *)

(** A (total correctness) Hoare triple, written [{H} t {Q}] on paper,
    and here written [hoare t H Q], asserts that starting from a state
    [s] satisfying the precondition [H], the term [t] evaluates to a
    value [v] and to a state [s'] that, together, satisfy the
    postcondition [Q]. It is formalized in Coq as shown below. *)

Definition hoare (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (s:state), H s ->
  exists (s':state) (v:val), eval s t s' v /\ Q v s'.

(** Remark: [Q] has type [val->hprop], thus [Q v] has type [hprop].
    Recall that [hprop = heap->Prop]. Thus [Q v s'] has type [Prop]. *)

(** The frame rule asserts that if one can derive a specification of
    the form [triple H t Q] for a term [t], then one should be able
    to automatically derive [triple (H \* H') t (Q \*+ H')] for any [H'].

    Intuitively, if [t] executes safely in a heap [H], it should behave
    similarly in any extension of [H] with a disjoint part [H']. Moreover,
    its evaluation should leave this piece of state [H'] unmodified
    throughout the execution of [t].

    The following definition of a Separation Logic triple builds upon
    that of a Hoare triple by "baking in" the frame rule. *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), hoare t (H \* H') (Q \*+ H').

(** This definition inherently satisfies the frame rule, as we show
    below. The proof only exploits the associativity of the star
    operator. *)

Lemma triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using.
  introv M. unfold triple in *. rename H' into H1. intros H2.
  specializes M (H1 \* H2).
  (* [M] matches the goal up to rewriting for associativity. *)
  applys_eq M 1 2.
  { rewrite hstar_assoc. auto. }
  { applys qprop_eq. intros v. rewrite hstar_assoc. auto. }
Qed.

(* INSTRUCTORS *)
(** The proof above exploits the functional extensionality property,
    but technically it is not needed (see the proof in [SLFExtra.v].) *)
(* /INSTRUCTORS *)


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Additional contents *)


(* ########################################################### *)
(** ** Example of a triple: the increment function *)

(** Assume a function called [incr] that increments the contents
    of a memory cell. *)

Parameter incr : val.

(** An application of [incr] is technically a term of the form
    [trm_app (trm_val incr) (trm_val (val_loc p))], where
    [trm_val] injects values in the grammar of terms, and
    [val_loc] injects locations in the grammar of locations.

    That said, because [trm_app], [trm_val], and [val_loc]
    are registered as coercions, an application of [incr] to a
    location [p] may be abbreviated as just [incr p]. *)

Lemma incr_applied : forall (p:loc) (n:int),
    trm_app (trm_val incr) (trm_val (val_loc p))
  = incr p.
Proof using. reflexivity. Qed.

(** A specification lemma for [incr] takes the form [triple (incr p) H Q].
    Recall from the first chapter ([SLFBasic]) the specification of [incr]:

[[
    Parameter Triple_incr : forall (p:loc) (n:int),
      TRIPLE (trm_app incr p)
        PRE (p ~~> n)
        POST (fun (v:unit) => p ~~> (n+1)).
]]

    The specification that we will write in this chapter (and the
    following ones) will differ in three ways from the one above.

    - First, the heap predicates will now be written [p ~~~> n],
      instead of [p ~~> n], for technical reasons that we won't
      detail here.
    - Second, the postcondition will now be of the form
      [fun (v:val) => \[v = val_unit] \* ...] instead of
      [fun (v:unit) => ...], for similar reasons.
    - Third, we won't use the notation [TRIPLE _ PRE _ POST _],
      but rather stick to applying the [triple] predicate directly,
      for the sake of clarity.

    The motivation for these differences is beyond the scope of this
    course. Details are provided in the bonus chapter [SLFLift]. *)

(* INSTRUCTORS *)
(** [p ~~~> n] technically stands for [p ~~~> (val_int n)], where
    [val_int] is a coercion. It is an instance of a predicate of
    the form [p ~~~> v] for a value [v] of type [val]. In constrast,
    [p ~~> n] stands for [p ~~~> (enc n)], where [enc] is a typeclass
    function that for translating Coq values into the type [val].
    The typeclass mechanism is more complex than the coercion mechanism,
    yet much more general, hence its use in the actual CFML tool. *)
(* /INSTRUCTORS *)

(** Taking for granted these three differences in presentation, the
    specification of [incr] is stated as shown below. *)

Parameter triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun (v:val) => \[v = val_unit] \* (p ~~~> (n+1))).


(* ########################################################### *)
(** ** Example of applications of the frame rule *)

(** The frame rule asserts that a triple remains true in any
    extended heap.

    Calling [incr p] in a state where the memory consists of
    two memory cells, one at location [p] storing an integer [n]
    and one at location [q] storing an integer [m] has the effect
    of updating the contents of the cell [p] to [n+1], while
    leaving the contents of [q] unmodified. *)

Lemma triple_incr_2 : forall (p q:loc) (n m:int),
  triple (incr p)
    ((p ~~~> n) \* (q ~~~> m))
    (fun v => \[v = val_unit] \* (p ~~~> (n+1)) \* (q ~~~> m)).

(** The above specification lemma is derivable from the specification
    lemma [triple_incr] by applying the frame rule to augment
    both the precondition and the postcondition with [q ~~~> m]. *)

Proof using.
  intros. lets M: triple_incr p n.
  lets N: triple_frame (q ~~~> m) M.
  applys_eq N 1 2.
  { auto. }
  { apply qprop_eq. intros v. rewrite hstar_assoc. auto. }
Qed.

(** Here, we have framed on [q ~~~> m], but we could similarly
   frame on any heap predicate [H], as captured by the following
   specification lemma. *)

Parameter triple_incr_3 : forall (p:loc) (n:int) (H:hprop),
  triple (incr p)
    ((p ~~~> n) \* H)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1)) \* H).

(** Remark: in practice, we always prefer writing
    "small-footprint specifications", such as [triple_incr],
    that describe the minimal piece of state necessary for
    the function to execute. Indeed, other specifications that
    describe a larger piece of state can be derived by application
    of the frame rule. *)


(* ########################################################### *)
(** ** Power of the frame rule with respect to allocation *)

(** Consider the specification lemma for an allocation operation.
    This rule states that, starting from the empty heap, one
    obtains a single memory cell at some location [l] with
    contents [v].*)

Parameter triple_ref : forall (v:val),
  triple (val_ref v)
    \[]
    (fun (r:val) => \exists (l:loc), \[r = val_loc l] \* l ~~~> v).

(** Applying the frame rule to the above specification, and to
    another memory cell, say [l' ~~~> v'], we obtain: *)

Parameter triple_ref_with_frame : forall (l':loc) (v':val) (v:val),
  triple (val_ref v)
    (l' ~~~> v')
    (fun (r:val) => \exists (l:loc), \[r = val_loc l] \* l ~~~> v \* l' ~~~> v').

(** This derived specification captures the fact that the newly
    allocated cell at address [l] is distinct from the previously
    allocated cell at address [l'].

    More generally, through the frame rule, we can derive that
    any piece of freshly allocated data is distinct from any
    piece of previously existing data.

    This independence principle is extremely powerful. It is an
    inherent strength of Separation Logic. *)


(* ########################################################### *)
(** ** Notation for heap union *)

(** Thereafter, to improve readability of statements in proofs,
    we introduce the following notation for heap union. *)

Notation "h1 \u h2" := (Fmap.union h1 h2) (at level 37, right associativity).


(* ########################################################### *)
(** ** Introduction and inversion lemmas for basic operators *)

(** The following lemmas help getting a better understanding of the meaning
    of the Separation Logic combinators. For each operator, we present one
    introduction lemma and one inversion lemma. *)

Implicit Types P : Prop.

(** The introduction lemmas show how to prove goals of the form [H h],
    for various forms of the heap predicate [H]. *)

Lemma hempty_intro :
  \[] Fmap.empty.
Proof using. hnf. auto. Qed.

Lemma hpure_intro : forall P,
  P ->
  \[P] Fmap.empty.
Proof using. introv M. hnf. auto. Qed.

Lemma hsingle_intro : forall l v,
  (l ~~~> v) (Fmap.single l v).
Proof using. intros. hnf. auto. Qed.

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  Fmap.disjoint h1 h2 ->
  (H1 \* H2) (h1 \u h2).
Proof using. intros. exists* h1 h2. Qed.

Lemma hexists_intro : forall A (x:A) (J:A->hprop) h,
  J x h ->
  (\exists x, J x) h.
Proof using. introv M. hnf. eauto. Qed.

(** The inversion lemmas show how to extract information from hypotheses
    of the form [H h], for various forms of the heap predicate [H].*)

Lemma hempty_inv : forall h,
  \[] h ->
  h = Fmap.empty.
Proof using. introv M. hnf in M. auto. Qed.

Lemma hpure_inv : forall P h,
  \[P] h ->
  P /\ h = Fmap.empty.
Proof using. introv M. hnf in M. autos*. Qed.

Lemma hsingle_inv: forall l v h,
  (l ~~~> v) h ->
  h = Fmap.single l v.
Proof using. introv M. hnf in M. auto. Qed.

Lemma hstar_inv : forall H1 H2 h,
  (H1 \* H2) h ->
  exists h1 h2, H1 h1 /\ H2 h2 /\ Fmap.disjoint h1 h2 /\ h = h1 \u h2.
Proof using. introv M. hnf in M. eauto. Qed.

Lemma hexists_inv : forall A (J:A->hprop) h,
  (\exists x, J x) h ->
  exists x, J x h.
Proof using. introv M. hnf in M. eauto. Qed.

(* EX3! (hstar_hpure_iff) *)

(** Prove that a heap [h] satisfies [\[P] \* H] if and only if
    [P] is true and [h] it satisfies [H]. The proof requires
    two lemmas on finite maps from [Fmap.v]:

[[
  Lemma Fmap.union_empty_l : forall h,
    Fmap.empty \u h = h.

  Lemma Fmap.disjoint_empty_l : forall h,
    Fmap.disjoint Fmap.empty h.
]]
*)

Lemma hstar_hpure_iff : forall P H h,
  (\[P] \* H) h <-> (P /\ H h).
Proof using. (* ADMITTED *)
  iff M.
  { hnf in M. destruct M as (h1&h2&M1&M2&D&U).
    hnf in M1. destruct M1 as (M1&HP). subst.
    rewrite Fmap.union_empty_l. auto. }
  { destruct M as (HP&Hh). hnf.
    exists (Fmap.empty:heap) h. splits.
    { hnf. auto. }
    { auto. }
    { apply Fmap.disjoint_empty_l. }
    { rewrite Fmap.union_empty_l. auto. } }
Qed. (* /ADMITTED *)

(** [] *)


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Bonus contents (optional reading) *)

(* ########################################################### *)
(** ** Alternative, equivalent definitions for Separation Logic triples *)

(** We have previously defined [triple] on top of [hoare],
    with the help of the separating conjunction operator, as:
    [forall (H':hprop), hoare (H \* H') t (Q \*+ H')].
    In what follows, we give an equivalent characterization,
    expressed directly in terms of heaps and heap unions.

    The alternative definition of [triple t H Q] asserts that if
    [h1] satisfies the precondition [H] and [h2] describes the rest
    of the state, then the evaluation of [t] produces a value [v] in
    a final state made that can be decomposed between a part [h1']
    and [h2] unchanged, in such a way that [v] and [h1'] together
    satisfy the poscondition [Q]. Formally: *)

Definition triple_lowlevel (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall h1 h2,
  Fmap.disjoint h1 h2 ->
  H h1 ->
  exists h1' v,
       Fmap.disjoint h1' h2
    /\ eval (h1 \u h2) t (h1' \u h2) v
    /\ Q v h1'.

(** Let us establish the equivalence between this alternative
    definition of [triple] and the original one. *)

(* EX3! (triple_iff_triple_lowlevel) *)
(** Prove the equivalence between [triple] and [triple_low_level].
    Warning: this is probably a very challenging exercise. *)

Lemma triple_iff_triple_lowlevel : forall t H Q,
  triple t H Q <-> triple_lowlevel t H Q.
Proof using. (* ADMITTED *)
  unfold triple, triple_lowlevel, hoare. iff M.
  { introv D P1.
    forwards (h'&v&HR&HQ): M (=h2) (h1 \u h2). { hnf. eauto 8. }
    destruct HQ as (h1'&h2'&N0&N1&N2&N3). subst.
    exists h1' v. auto. }
  { intros H' h. introv (h1&h2&N1&N2&D&U).
    forwards (h1'&v&D'&HR&HQ): M h1 h2; auto. subst.
    exists (h1' \u h2) v. split. { eauto. } { hnf. eauto 8. } }
Qed. (* /ADMITTED *)

(** [] *)


(* ########################################################### *)
(** ** Alternative definitions for heap predicates *)

(** In what follows, we discuss alternative, equivalent definitions for
    the fundamental heap predicates. We write these equivalence using
    equalities of the form [H1 = H2]. Recall that lemma [hprop_eq] enables
    deriving such equalities by invoking predicate extensionality. *)

(** The empty heap predicate [\[]] is equivalent to the pure fact predicate
    [\[True]]. *)

Lemma hempty_eq_hpure_true :
  \[] = \[True].
Proof using.
  unfold hempty, hpure. apply hprop_eq. intros h. iff Hh.
  { auto. }
  { jauto. }
Qed.

(** Thus, [hempty] could be defined in terms of [hpure], as [hpure True],
    written [\[True]]. *)

Definition hempty' : hprop :=
  \[True].

(** The pure fact predicate [[\P]] is equivalent to the existential
    quantification over a proof of [P] in the empty heap, that is,
    to the heap predicate [\exists (p:P), \[]]. *)

Lemma hpure_eq_hexists_proof : forall P,
  \[P] = (\exists (p:P), \[]).
Proof using.
  unfold hempty, hpure, hexists. intros P.
  apply hprop_eq. intros h. iff Hh.
  { destruct Hh as (E&p). exists p. auto. }
  { destruct Hh as (p&E). auto. }
Qed.

(** Thus, [hpure] could be defined in terms of [hexists] and [hempty], as
    [hexists (fun (p:P) => hempty)], also written [\exists (p:P), \[]]. *)

Definition hpure' (P:Prop) : hprop :=
  \exists (p:P), \[].

(** It is useful to minimize the number of combinators, both for elegance
    and to reduce the proof effort.

    Since we cannot do without [hexists], we have a choice between
    considering either [hpure] or [hempty] as primitive, and the other
    one as derived. The predicate [hempty] is simpler and appears as
    more fundamental.

    Hence, in the subsequent chapters (and in the CFML tool),
    we define [hpure] in terms of [hexists] and [hempty],
    like in the definition of [hpure'] shown above.
    In other words, we assume the definition:

[[
  Definition hpure (P:Prop) : hprop :=
    \exists (p:P), \[].
]]

*)


(* ########################################################### *)
(** ** Additional explanations for the definition of [\exists] *)

(** The heap predicate [\exists (n:int), l ~~~> (val_int n)]
    characterizes a state that contains a single memory cell,
    at address [l], storing the integer value [n], for "some"
    (unspecified) integer [n].

[[
  Parameter (l:loc).
  Check (\exists (n:int), l ~~~> (val_int n)) : hprop.
]]

    The type of [\exists], which operates on [hprop], is very similar
    to that of [exists], which operates on [Prop].

    The notation [exists x, P] stands for [ex (fun x => P)],
    where [ex] has the following type:

[[
    Check ex : forall A : Type, (A -> Prop) -> Prop.
]]

    Likewise, [\exists x, H] stands for [hexists (fun x => H)],
    where [hexists] has the following type:

[[
    Check hexists : forall A : Type, (A -> hprop) -> hprop.
]]

*)

(** Remark: the notation for [\exists] is directly adapted from that
    of [exists], which supports the quantification an arbitrary number
    of variables, and is defined in [Coq.Init.Logic] as follows.

[[
    Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
      (at level 200, x binder, right associativity,
       format "'[' 'exists' '/ ' x .. y , '/ ' p ']'").
]]

*)

(* ########################################################### *)
(** ** Formulation of the extensionality axioms *)

Module Extensionality.

(** To establish extensionality of entailment, we have used
    the predicate extensionality axiom. In fact, this axiom
    can be derived by combining the axiom of "functional extensionality"
    with another one called "propositional extensionality". *)

(** The axiom of "propositional extensionality" asserts that
    two propositions that are logically equivalent (in the sense
    that they imply each other) can be considered equal. *)

Axiom propositional_extensionality : forall (P Q:Prop),
  (P <-> Q) ->
  P = Q.

(** The axiom of "functional extensionality" asserts that
    two functions are equal if they provide equal result
    for every argument. *)

Axiom functional_extensionality : forall A B (f g:A->B),
  (forall x, f x = g x) ->
  f = g.

(* EX1! (predicate_extensionality_derived) *)
(** Using the two axioms [propositional_extensionality]
    and [functional_extensionality], show how to derive
    [predicate_extensionality]. *)

Lemma predicate_extensionality_derived : forall A (P Q:A->Prop),
  (forall x, P x <-> Q x) ->
  P = Q.
Proof using. (* ADMITTED *)
  introv M. applys functional_extensionality.
  intros x. applys propositional_extensionality.
  applys M.
Qed. (* /ADMITTED *)

(** [] *)

End Extensionality.

