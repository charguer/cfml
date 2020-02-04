(**

Separation Logic Foundations

Chapter: "Struct".

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Import SLFExtra TLCbuffer.

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.
Implicit Type p q : loc.
Implicit Type k : nat.
Implicit Type i n : int.
Implicit Type v : val.
Implicit Type L : list val.

(* TODO: rename VFun *)
(* TODO : limitation of xapp for lemmas with premises... *)



(* ####################################################### *)
(* ####################################################### *)
(* ####################################################### *)
(** * Chapter in a rush *)

(** This chapter introduces support for reasoning about

    - mutable records,
    - mutable arrays,
    - n-ary functions (i.e., functions of several arguments).

    To allocate records and arrays, we introduce a new primitive operation,
    named [val_alloc], that allocates at once a set of memory cells with
    consecutive addresses.

    For example, applying [val_alloc] to the integer value [3] would return
    a pointer [p] together with the ownership of three cells: one at
    location [p], one at location [p+1], and one atlocation [p+2].
    This allocation model that exposes pointer arithmetics provides a way
    to model both records and arrays with minimal extension to the semantics
    of the programming language that we consider for the course.

    The cells allocated using [val_alloc] are assigned as contents a special
    value, named [val_uninit], to reflect for the fact that their contents has
    never been set. Remark: in OCaml, one must provide an initialization
    value explicitly, so there is no such thing as [val_uninit]; in JavaScript,
    [val_uninit] is called [undefined]; in Java, arrays are initialized with
    zeros; in C, uninitialized data should not be read---we could implement
    this policy in our languageby restricting the evaluation rule for the read
    operation, adding a premise of the form [v <> val_uninit] to the rule.

    Regarding n-ary functions, that is, there are three possible approaches:

    - native n-ary functions, e.g., [function(x, y) { t } ] in C syntax.
    - curried functions, e.g., [fun x => fun y => t] in OCaml syntax.
    - tupled functions, e.g., [fun (x,y) => t] in OCaml syntax.

    In this chapter, we present reasoning rules for curried functions,
    again because this choice requires minimal extension to the syntax and
    semantics of our language. We discuss in the bonus section the treatment
    of native n-ary functions, which is the most practical solution from an
    engineering point of view.

*)


(* ####################################################### *)
(** ** Representation of a set of consecutive cells *)

Module Cells.

(** An array of length [k] allocated at location [p] can be represented
    as a set of [k] consecutive cells starting from location [p]. In other
    words, the array cells have addresses from [p] inclusive to [p+k]
    inclusive. Just like records, arrays can be allocated using the
    [val_alloc] primitive operation, and read and write operations on
    array cells can be derived. *)

(** The contents of an array of length [k] can be represented by a list
    of values of length [k].

    The heap predicate [hcells L p] represents a consecutive set of cells
    starting at location [p] and whose elements are described by the list [L].

    On paper, we could write something along the lines of:
    [\bigstar_{x at index i in L} { (p+i) ~~> x }].

    In Coq, we can define this predicate by induction on the list [L], with
    the pointer being incremented by one unit at each cell, as follows.
*)

Fixpoint hcells (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[]
  | x::L' => (p ~~> x) \* (hcells L' (S p))
  end.

(** Given a heap predicate [hcells L p], one can deduce that [p] is not
    null, but only if the list [L] is not empty. In order to avoid in
    proofs the need to treat specially the case empty arrays, it is
    convenient to pack together with [hcells L p] the information [p <> null],
    reflecting the fact that no data can be allocated at the null location,
    not even an empty array.

    The heap predicate [harray L p] packs together [hcells L p] with the
    information that [p] is not null.
*)

Definition harray (L:list val) (p:loc) : hprop :=
  hcells L p \* \[p <> null].

Lemma harray_not_null : forall p L,
  L <> nil ->
  harray L p ==> harray L p \* \[p <> null].
Proof using. introv N. unfold harray. xsimpl*. Qed.

(** The description of an array, that is, a set of consecutive cells,
    can be split in two parts, at an arbitrary index. Concretely, if
    we have [harray (L1++L2) p], then we can separate the left part
    [harray L1 p] from the right part [harray L2 q], where the address
    [q] is equal to [p + length L1]. Reciprocally, the two parts can
    be merged back into the original form at any time. *)

Parameter harray_concat_eq : forall p L1 L2,
  harray (L1++L2) p = (harray L1 p \* harray L2 (length L1 + p)%nat).

(** The proof of this lemma appears may be found in the bonus section of
    this chapter. *)

(** Remark: this "splitting lemma for arrays" is useful to carry out local
    reasoning on arrays, by focusing on the segment of the array involved
    in each recursive call, and obtaining for free the fact that the
    cells outside of the segment remain unmodified. *)


(* ####################################################### *)
(** ** Specification of the allocation of consecutive cells *)

(** The operation [val_alloc k] allocates [k] consecutive cells. Let [p]
    denote the pointer returned. The allocated cells have addresses in
    the range from [p] inclusive to [p+k] exclusive. These cells have for
    contents is the special value [val_uninit], which we assume to be part
    of the grammar of values. *)

Parameter val_uninit : val.

(** The heap produced by [val_alloc k] can be described by [harray L p],
    for a list [L] that consists of [k] occurences of the value [val_uninit].
    Such a list is formally described by [LibList.make k val_uninit].

    We introduce the heap predicate [harray_uninit k p] to denote the
    specialization of [harray] to that list. This predicate will appear
    in the postcondition of [val_alloc], as explained in the next section. *)

Definition harray_uninit (k:nat) (p:loc) : hprop :=
  harray (LibList.make k val_uninit) p.

(** Let us specify the behavior of the allocation function using a
    triple. We first state a specification with an argument of type [nat],
    then reformulate the specification with an argument of type [int].

    Consider a natural number [k]. Thanks to coercions, it may also be
    viewed as an integer value of type [val].

    The operation [val_alloc k] admits an empty precondition. Its
    postcondition asserts that the return value [r] is of the form
    [val_loc p] for some location [p], and that the final state
    satisfies the heap predicate [harray_uninit k p]. Recall that this
    predicate describes [k] cells at consecutive addresses starting from
    location [p], with uninitialized contents. *)

Parameter triple_alloc_nat : forall k,
  triple (val_alloc k)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* harray_uninit k p).

(** We next generalize this specification so that it can handle applications
    of the form [val_alloc n], where [n] is of type [int], and can be proved
    to be nonnegative. (Such a formulation avoids the need to exhibit the
    natural number that corresponds to the value [n].)

    The new specification, shown below, features the premise [n >= 0]. Its
    postcondition involves the predicate [hcells (abs n) p], where [abs]
    converts a nonnegative [int] value into the corresponding [nat] value. *)

Lemma triple_alloc : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* harray_uninit (abs n) p).
Proof using.
  introv N. rewrite <- (@abs_nonneg n) at 1; [|auto].
  xtriple. xapp triple_alloc_nat. xsimpl*.
Qed.

(** The specification of the allocation function can be specialized to
    allocate arrays. To that end, we reformulate the postcondition of
    [val_alloc n] so that it exhibits a predicate of the form [harray L p],
    where [L] is of length [n]. We could specify that the values in [L]
    are all equal to [val_uninit], but for most applications it suffices
    to drop this information, and simply quantifying over an abstract list
    [L] of length [n]. *)

Lemma triple_alloc_array : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (fun r => \exists p L, \[r = val_loc p] \* \[n = length L] \* harray L p).
Proof using.
  introv N. xtriple. xapp triple_alloc. { auto. }
  { xpull. intros p. unfold harray_uninit. xsimpl*.
    { rewrite length_make. rewrite* abs_nonneg. } }
Qed.


(* ####################################################### *)
(** ** Specification of the deallocation of consecutive cells *)

(** The deallocation operation [val_dealloc n p] deallocates [n]
    consecutive cells starting from the location [p]. It admits the
    precondition [harray L p], where [L] can be any list of length [n],
    and its postcondition is empty. *)

Parameter triple_dealloc_harray : forall L n p,
  n = length L ->
  triple (val_dealloc n p)
    (harray L p)
    (fun _ => \[]).

(** Remark: in the C programming language, the argument [n] needs not be
    provided, because the system keeps track of the size of allocated blocks.
    One aspect that our simple semantics does not take into account is that
    in C one can invoke the deallocation function on pointers that were
    produced by the allocation function. We discuss further in this chapter
    a possible refinement of the specification to enforce this policy. *)

(** Above, the precondition [harray L p] is stronger than it needs to be.
    It would suffices to take [hcells L p] in the precondition. Depending
    on the use case, it may be easier for the user to not carry around the
    information that [p <> null]. *)

Parameter triple_dealloc_hcells : forall L n p,
  n = length L ->
  triple (val_dealloc n p)
    (hcells L p)
    (fun _ => \[]).

(** This second specification is still somewhat inconvenient for practical
    proofs. The reason is that it requires explicitly providing the list
    describing the contents of the deallocated cells. (An example illustrating
    the issue is given further on, in lemma [triple_dealloc_mcell].)

    We therefore consider an alternative deallocation rule that avoids the
    quantification over thie list [L]. It is based on a new heap predicate,
    written [hcells_any k p], which describes the contents of [k] cells,
    each of which with an arbitrary contents described through an existential
    quantifier. *)

Fixpoint hcells_any (k:nat) (p:loc) : hprop :=
  match k with
  | O => \[]
  | S k' => (\exists v, p ~~> v) \* (hcells_any k' (S p))
  end.

(** We can prove that the predicate [hcells_any k p] entails [hcells L p]
    for some list [L]. The list [L] is obtained by gathering the [k] existentially
    quantified values that appear recursively in the definition of [hcells_any]. *)

Lemma himpl_hcells_any_hcells : forall p k,
  hcells_any k p ==> \exists L, \[length L = k] \* hcells L p.
Proof using.
  intros. gen p. induction k as [|k']; simpl; intros.
  { xsimpl (@nil val). { auto. } { simpl. xsimpl. } }
  { xpull. intros v. xchange IHk'. intros L' EL'.
    xsimpl (v::L'). { rew_list. math. } { simpl. xsimpl. } }
Qed.

(** The specification of the operation [val_dealloc k] can then be reformulated
    using a precondition of the forme [harray_any k p]. *)

Lemma triple_dealloc_hcells_any : forall p k,
  triple (val_dealloc k p)
    (hcells_any k p)
    (fun _ => \[]).
Proof using.
  intros. xtriple. xchange himpl_hcells_any_hcells. intros L EL.
  xapp triple_dealloc_hcells. { auto. } { xsimpl. }
Qed.


(* ####################################################### *)
(** ** Specification of array access operations *)

Module Arrays.

(** The operation [val_array_get p i] returns the contents of the [i]-th
    cell of the array at location [p]. *)

Parameter val_array_get : val.

(** The specification of [val_array_get] is as follows. The precondition
    describes the array in the form [harray L p], with a premise that
    requires the index [i] to be in the valid range, that is, between
    zero (inclusive) and the length of [L] (exclusive). The postcondition
    asserts that the result value is [nth (abs i) L], and mentions
    the unmodified array, still described by [harray L p]. *)

Parameter triple_array_get : forall L p i,
  0 <= i < length L ->
  triple (val_array_get p i)
    (harray L p)
    (fun r => \[r = LibList.nth (abs i) L] \* harray L p).

(** The operation [val_array_set p i v] updates the contents of the [i]-th
    cell of the array at location [p]. *)

Parameter val_array_set : val.

(** Again, for stating the specification, we axiomatize the corresponding
    operation on lists: [list_update L i v] describes the update to the
    list [L] by replacing the value at index [i] with the value [v]. *)

(** The specification of [val_array_set] admits the same precondition as
    [val_array_get], with [harray L p] and the constraint [0 <= i < length L].
    Its postcondition describes the updated array using a predicate of the
    form [harray L' p], where [L'] corresponds to [update (abs i) v L]. *)

Parameter triple_array_set : forall L p i v,
  0 <= i < length L ->
  triple (val_array_set p i v)
    (harray L p)
    (fun _ => harray (LibList.update (abs i) v L) p).

Hint Resolve triple_array_get triple_array_set : triple.

End Arrays.


(* ########################################################### *)
(** ** Representation of a record field *)

(** A record can be represented as a set of fields stored in consecutive
    addresses.

    For example, consider a mutable list cell allocated at location [p].
    It consists of a record with a [head] field storing a value [x], and
    a tail field storing a value [q]. This list cell an be represented by
    the heap predicate [(p ~~> x) \* ((p+1) ~~> q)].

    If we define [head := 0] and [tail := 1], the same heap predicate can
    be written [((p+head) ~~> x) \* ((p+tail) ~~> q)].

    To better suggest that we are talking about record fields, and also to
    abstract away from the details of pointer arithmetics, we introduce the
    notation [p`.k ~~> v] to denote [(p+k) ~~> v]. Here, [k] denotes by
    convention a field name, where field names correspond to a natural
    numbers. In first approximation, the definition is shown below. *)

Definition field : Type := nat.

Definition hfield' (p:loc) (k:field) (v:val) : hprop :=
  (p+k)%nat ~~> v.

(** It is convenient in verification proofs to be able to assume that
    whenever we write [p`.k ~~> v], we refer to a location [p] that is
    not null. For an example, see the use of the lemma [hfield_not_null]
    inside the proof of the lemma [MList_if] in file [SLFBasic.v].

    To enable justifying this lemma [hfield_not_null], whose statement
    appears below, we bake in the definition of [p`.k ~~> v] the fact that
    [p] is not null, using the assertion [\[p <> null]]. *)

Definition hfield (p:loc) (k:field) (v:val) : hprop :=
  (p+k)%nat ~~> v \* \[p <> null].

Notation "p `. k '~~>' v" := (hfield p k v)
  (at level 32, k at level 0, no associativity,
   format "p `. k  '~~>'  v").

(** The lemma [hfield_not_null] asserts that the heap predicate [p`.k ~~> v]
    always ensures [p <> null]. *)

Lemma hfield_not_null : forall p k v,
  (p`.k ~~> v) ==> (p`.k ~~> v) \* \[p <> null].
Proof using. intros. unfold hfield. xsimpl*. Qed.

(** To prevent undesirable simplifications, we set the definition [hfield]
    to be opaque. Then, we provide a lemma for unfolding its definition.
    We replace the addition [p+k] with the addition [k+p], because the later
    simplifies better in Coq when [k] is a constant. *)

Lemma hfield_eq : forall p k v,
  hfield p k v = ((k+p)%nat ~~> v \* \[p <> null]).
Proof using. intros. math_rewrite (k+p = p+k)%nat. auto. Qed.

Global Opaque hfield.

End Cells.


(* ########################################################### *)
(** ** Allocation and deallocation of record fields *)

(** We can allocate a fresh mutable list cell by invoking the primitive
    operation [val_alloc] with argument [2]. Let us prove that the result,
    described by [hcell 2 p], can be also be viewed as the heap predicate
    [(p`.head ~~> val_uninit) \* (p`.tail ~~> val_uninit)],
    which describes the two fields of the record, with uninitialized
    contents. *)

Definition head : field := 0%nat.
Definition tail : field := 1%nat.

Lemma triple_alloc_mcell :
  triple (val_alloc 2%nat)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* (p`.head ~~> val_uninit)
                                          \* (p`.tail ~~> val_uninit)).
Proof using.
  xtriple. xapp triple_alloc_nat. xpull. intros p.
  unfold harray_uninit, harray. simpl.
  xpull. intros N. xsimpl p; auto.
  do 2 rewrite hfield_eq. xsimpl; auto.
Qed.

(** Reciprocally, we can deallocate a mutable list cell at location [p]
    by invoking the primitive operation [val_dealloc] with argument [2].
    The precondition describes the two fields [p`.head ~~> x] and
    [p`.tail ~~> q]. The postcondition is empty: the fields are lost. *)

Lemma triple_dealloc_mcell : forall x q p,
  triple (val_dealloc 2%nat p)
    ((p`.head ~~> x) \* (p`.tail ~~> q))
    (fun _ => \[]).

(** For the proof, we exploit the rule [triple_dealloc_hcells_any].
    If we used instead the rule  [triple_dealloc_hcells], we would have
    to provide explicitly the list of the contents of the cells, by invoking
    [xapp (@triple_dealloc_hcells (x::(val_loc q)::nil))]. Instead,
    thanks to [hcells_any], the existentially-quantified associated with each
    of the cells get automatically inferred by [xsimpl]. *)

Proof using.
  xtriple. xapp triple_dealloc_hcells_any.
  unfold hcells_any. do 2 rewrite hfield_eq. xsimpl.
Qed.


(* ########################################################### *)
(** ** Reading and writing in record fields *)

(** For reading and writing in record fields, we introduce the operations
    [val_get_field] and [val_set_field]. As we show in the bonus section
    of this chapter, these functions can be defined in terms of the
    operations [val_get] and [val_set], if we assume available a pointer
    addition operation.

    For the moment, let us simply axiomatize these operations, and state
    their specifications.

    The expression [val_get_field] has type [field -> val]. Given a field
    name [f] (of type [field], which is defined as [nat]), the expression
    [val_get_field f] denotes a value of type [val] that can be applied to
    an argument [p]. The specification of [val_get_field f p] follows the
    pattern of the specification of [val_get]. The precondition and the
    postcondition describe a field [p`.k ~~> v], and the result value [r]
    is specified to be equal to [v].
*)

Module FieldAccesses.

Parameter val_get_field : field -> val.

Parameter triple_get_field : forall p k v,
  triple (val_get_field k p)
    (p`.k ~~> v)
    (fun r => \[r = v] \* (p`.k ~~> v)).

(** Likewise for [val_set_field], the operation that writes into a record
    field. *)

Parameter val_set_field : field -> val.

Parameter triple_set_field : forall v p k v',
  triple (val_set_field k p v)
    (p`.k ~~> v')
    (fun _ => p`.k ~~> v).

(** We introduce the syntax [t'.f] for reading from a field using
    [val_get_field], and [Set t1'.f := t2] for writing into a field
    using [val_set_field]. *)

Notation "t1 ''.' f" :=
  (val_get_field f t1)
  (at level 56, f at level 0, format "t1 ''.' f" ).

Notation "'Set' t1 ''.' f '':=' t2" :=
  (val_set_field f t1 t2)
  (at level 65, t1 at level 0, f at level 0, format "'Set' t1 ''.' f  '':=' t2").

(** We register these specifications so that they may be exploited by the
    tactic [xapp]. *)

Hint Resolve triple_get_field triple_set_field : triple.

End FieldAccesses.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Additional contents *)

(* ####################################################### *)
(** ** Allocation of records: example of list cells *)

Module Lists.
Import SLFProgramSyntax.
Implicit Types x : val.

(** Recall from [SLFBasic] the definition of [MList]. *)

Fixpoint MList (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists q, (p`.head ~~> x) \* (p`.tail ~~> q)
                     \* (MList L' q)
  end.

Lemma MList_nil : forall p,
  (MList nil p) = \[p = null].
Proof using. auto. Qed.

Lemma MList_cons : forall p x L',
  MList (x::L') p =
  \exists q, (p`.head ~~> x) \* (p`.tail ~~> q) \* MList L' q.
Proof using.  auto. Qed.

(** Consider the function [mcell x q], which allocates a fresh mutable
    list cell with [x] as head and [q] as tail.

[[
    let mcell x q =
      { head = x; tail = q }
]]

    In our programming language, the creation of such a record can
    encoded by allocating of a 2-cell record, and setting its two fields. *)

Definition mcell : val :=
  VFun 'x 'q :=
    Let 'p := val_alloc 2%nat in
    Set 'p'.head ':= 'x ';
    Set 'p'.tail ':= 'q ';
    'p.

(** The specification of [mcell x q] appears next. Its precondition is empty.
    Its postcondition describes the two fields [p`.head ~~> x] and [p`.tail ~~> q]. *)

Lemma triple_mcell : forall x q,
  triple (mcell x q)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* (p`.head ~~> x) \* (p`.tail ~~> q)).
Proof using.
  xwp. xapp triple_alloc_mcell. intros p. xapp. xapp. xval. xsimpl*.
Qed.

(** The function [mcons] is an alias for [mcell]. Whereas [mcell x q]
    is intended to allocate a fresh cell on its own, [mcons x q] is
    intended to extend an existing list [MList L q] by appending to it
    a freshly-allocated cell. The specification of [mcons] requires
    a list [MList L q] in its precondition, and produces a list
    [MList (x::L) p] in its postcondition. *)

Definition mcons : val :=
  mcell.

Lemma triple_mcons : forall L x q,
  triple (mcons x q)
    (MList L q)
    (fun r => \exists p, \[r = val_loc p] \* MList (x::L) p).
Proof using.
  intros. xtriple. xapp triple_mcell.
  intros p. xchange <- MList_cons. xsimpl*. (* fold back the list *)
Qed.

Hint Resolve triple_mcons : triple.

(** The operation [mnil()] returns the [null] value, which is
    a representation for the empty list [nil]. Thus, [mnil]
    can be specified using a postcondition asserting it produces
    [MList nil p], where [p] denotes the location returned.

[[
    let rec mnil () =
      null
]]
*)

Definition mnil : val :=
  VFun 'u :=
    null.

(** The precondition of [mnil] is empty. Its postcondition of [mnil]
    asserts that the return value [p] is a pointer such that
    [MList nil p]. Because [p] is [null], the proof requires us to
    introduce [null ~> MList nil] out of thin air. For this task, we
    can use the following specialization of the lemma [MList_nil]. *)

Lemma MList_nil_intro :
  \[] ==> (MList nil null).
Proof using. intros. rewrite* MList_nil. xsimpl*. Qed.

Lemma triple_mnil :
  triple (mnil '())
    \[]
    (fun r => \exists p, \[r = val_loc p] \* MList nil p).
Proof using.
  xwp. xval. xchange MList_nil_intro. xsimpl*.
Qed.

Hint Resolve triple_mnil : triple.

(** Remark: the tactic [xchange MList_nil_intro] can also be
    replaced with [xchange <- (MList_nil null)], if one wishes
    to save the need to state the lemma [xchange MList_nil_intro]. *)

(** Observe that the specification [triple_mnil] does not mention
    the [null] pointer anywhere. This specification can thus be
    used to specify the behavior of operations on mutable lists
    without having to reveal low-level implementation details. *)

(** In the remaining of this section, we present an example program
    that uses the functions [mnil] and [mcons] for allocating an
    entire list. *)

(** Consider the function [mcopy], which constructs an independent
    copy of a given mutable linked list.

    We'll thereby put to practice the lemma [MList_if] as well as
    the allocation functions [mnil] and [mcons] for verifying the
    function [mcopy]

[[
    let rec mcopy p =
      if p == null
        then mnil ()
        else mcons (p.head) (mcopy p.tail)
]]
*)

Definition mcopy : val :=
  VFix 'f 'p :=
    Let 'b := ('p '= null) in
    If_ 'b
      Then mnil '()
      Else
        Let 'x := 'p'.head in
        Let 'q := 'p'.tail in
        Let 'q2 := 'f 'q in
        mcons 'x 'q2.

(** For the proof, recall from chapter [SLFBasic] the lemma [MList_if],
    which reformulates the definition of [MList L p] using a case analysis
    on whether the pointer [p] is null, instead of on whether the
    list [L] is empty. *)

Parameter MList_if : forall p L,
      (MList L p)
  ==> (If p = null
        then \[L = nil]
        else \exists x q L', \[L = x::L']
             \* (p`.head ~~> x) \* (p`.tail ~~> q)
             \* (MList L' q)).

(** The precondition of [mcopy] requires a linked list [MList L p].
    Its postcondition asserts that the function returns a pointer [p']
    and a list [MList L p'], in addition to the original list
    [MList L p]. The two lists are totally disjoint and independent,
    as captured by the separating conjunction symbol (the star). *)

Lemma triple_mcopy : forall L p,
  triple (mcopy p)
    (MList L p)
    (fun r => \exists p', \[r = val_loc p'] \* (MList L p) \* (MList L p')).

(** The proof script is very similar in structure to the previous ones.
    While playing the script, try to spot the places where:

    - [mnil] produces an empty list of the form [MList nil p'],
    - the recursive call produces a list of the form [MList L' q'],
    - [mcons] produces a list of the form [MList (x::L') p'].

*)

Proof using.
  intros. gen p. induction_wf IH: list_sub L.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros ->. xapp. xsimpl*. subst. applys MList_nil_intro. }
  { intros x q L' ->. xapp. xapp. xapp. intros q'.
    xapp. intros p'. xchange <- MList_cons. xsimpl*. }
Qed.


(* ########################################################### *)
(** ** Deallocation of records: example of list cells *)

(** Recall that our Separation Logic set up enforces that all allocated
    data eventually gets properly deallocated. In what follows, we describe
    a function for deallocating one cell, then a function for deallocating
    an entire mutable list. *)

(** The operation [mfree_cell p] deallocates the two fields associated
    with the cell at location [p]. *)

Definition mfree_cell : val :=
  VFun 'p :=
    val_dealloc 2%nat 'p.

(** The precondition of this operation thus requires the two fields
    [p`.head ~~> x] and [p`.tail ~~> q], and the postcondition is empty. *)

Lemma triple_mfree_cell : forall x q p,
  triple (mfree_cell p)
    ((p`.head ~~> x) \* (p`.tail ~~> q))
    (fun _ => \[]).
Proof using. xwp. xapp triple_dealloc_mcell. xsimpl. Qed.

Hint Resolve triple_mfree_cell : triple.

(** The operation [mfree_list] deallocates all the cells in a given list.
    It is implemented as a recursive function that invokes [mfree_cell]
    on every cell that it traverses.

[[
    let rec mfree_list p =
      if p != null then begin
        let q = p.tail in
        mfree_cell p;
        mfree_list q
      end
]]

*)

Definition mfree_list : val :=
  VFix 'f 'p :=
    Let 'b := ('p '<> null) in
    If_ 'b Then
      Let 'q := 'p'.tail in
      mfree_cell 'p ';
      'f 'q
    End.

(** The precondition of [mfree_list p] requires a full list [p ~> MList L].
    The postcondition is empty: the entire list is destroyed. *)

(* EX1! (Triple_mfree_list) *)
(** Verify the function [mfree_list].
    Hint: follow the pattern of the proof of the function [mlength]. *)

Lemma triple_mfree_list : forall L p,
  triple (mfree_list p)
    (MList L p)
    (fun _ => \[]).
Proof using. (* ADMITTED *)
  intros. gen p. induction_wf IH: list_sub L. intros.
  xwp. xchange MList_if. xapp. xif; intros C; case_if; xpull.
  { intros x p' L' ->. xapp. xapp. xapp. xsimpl. }
  { intros ->. xval. xsimpl. }
Qed. (* /ADMITTED *)

(** [] *)

End Lists.


(* ####################################################### *)
(** ** Grouped representation of record fields *)

Module GroupedFields.

(** In our presentation of record fields, one has to write the
    fields one by one, for example a list cell takes the form:
    [p`.head ~~> x \* p`.tail ~~> q].

    It may be convenient to exploit a more compact description
    that factorizes the location [p]. The same list cell may be
    described as [hrecord `{ head := x; tail := p'} p].

    This factorized form has at least two practical benefits:

    - it is shorter when the location [p] is not a very short
      identifier;
    - it significantly decreases the number of star-separated
      items in the heap predicates, thereby increasing the speed
      of proof processing.

    It what follows, we present the generic definition of
    [p ~> Record L], and suggest how the specification of
    the record field operations are set up.
*)

(** Recall that a field identifier corresponds to an offset,
    represented as a natural number. *)

Definition field : Type := nat.

(** A record field is described as the pair of a a field and
    a value stored at this field. *)

Definition hrecord_field : Type := (field * val).

(** A record consists is made of a list of record fields. *)

Definition hrecord_fields : Type := list hrecord_field.

Implicit Types kvs : hrecord_fields.

(** The heap predicate [hrecord L p] asserts that at location [p]
    one fields the list of fields [L], where [L] has type
    [hrecord_fields], that is [list (field * val)].

    This predicate is defined by recursion on the list [L].
    If [L] is empty, it describes the empty heap predicate.
    Otherwise, a first field, at offset [f] and with contents [v],
    is describes by the predicate [p`.f ~~> v], then the remaining
    fields are described recursively. *)

Fixpoint hrecord (kvs:hrecord_fields) (r:loc) : hprop :=
  match kvs with
  | nil => \[]
  | (k,v)::kvs' => (r`.k ~~> v) \* (r ~> hrecord kvs')
  end.

(** To use [hrecord] in practice, let us introduce record-style
    notation for list of pairs of fields and values.
    Setting up an arity-generic notation is quite tricky,
    let us simply support up to 3 fields for now. *)

Notation "`{ k1 := v1 }" :=
  ((k1,(v1:val))::nil)
  (at level 0, k1 at level 0)
  : val_scope.

Notation "`{ k1 := v1 ; k2 := v2 }" :=
  ((k1,(v1:val))::(k2,(v2:val))::nil)
  (at level 0, k1, k2 at level 0)
  : val_scope.

Notation "`{ k1 := v1 ; k2 := v2 ; k3 := v3 }" :=
  ((k1,(v1:val))::(k2,(v2:val))::(k3,(v3:val))::nil)
  (at level 0, k1, k2, k3 at level 0)
  : val_scope.

Open Scope val_scope.

(** For example, the definition of the representation predicate
    [MList] can be revisited using the heap predicate [hrecord],
    applied to a list with the [head] and the [tail] fields.. *)

Fixpoint MList (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists p', (hrecord `{ head := x; tail := p'} p)
                      \* (MList L' p')
  end.

(** There remains to explain how to access the fields. Recall the
    specification of the operation [val_get_field] for reading in
    a field standing by itself. *)

Parameter triple_get_field : forall p k v,
  triple (val_get_field k p)
    (p`.k ~~> v)
    (fun r => \[r = v] \* (p`.k ~~> v)).

(** Let us derive from this specification another one that operates
    on the heap predicate [hrecord kvs p]. *)

Fixpoint hrecord_lookup (k:field) (kvs:hrecord_fields) : option val :=
  match kvs with
  | nil => None
  | (f,v)::kvs' => if Nat.eq_dec k f
                   then Some v
                   else hrecord_lookup k kvs'
  end.

Lemma triple_get_field_hrecord : forall kvs p k v,
  hrecord_lookup k kvs = Some v ->
  triple (val_get_field k p)
    (hrecord kvs p)
    (fun r => \[r = v] \* hrecord kvs p).
Proof using.
  intros L. induction L as [| [f v] L']; simpl; introv E.
  { inverts E. }
  { case_if.
    { inverts E. subst f. applys triple_conseq_frame.
      { applys triple_get_field. } { xsimpl. } { xsimpl*. } }
    { applys triple_conseq_frame. { applys IHL' E. } { xsimpl. } { xsimpl*. } } }
Qed.

(** Likewise, we can specify [val_set_field] in terms of the heap
    predicate [hrecord]. To that end, we introduce an auxiliary
    function for computing the updated list of fields following an
    write operation. *)

Fixpoint hrecord_udpate (k:field) (w:val) (kvs:hrecord_fields)
                        : option hrecord_fields :=
  match kvs with
  | nil => None
  | (f,v)::kvs' => if Nat.eq_dec k f
                   then Some ((f,w)::kvs')
                   else match hrecord_udpate k w kvs' with
                        | None => None
                        | Some LR => Some ((f,v)::LR)
                        end
  end.

Lemma triple_set_field_hrecord : forall kvs kvs' k p w,
  hrecord_udpate k w kvs = Some kvs' ->
  triple (val_set_field k p w)
    (hrecord kvs p)
    (fun _ => hrecord kvs' p).
Proof using.
  intros kvs. induction kvs as [| [f v] kvs']; simpl; introv E.
  { inverts E. }
  { case_if.
    { inverts E. subst f. applys triple_conseq_frame.
      { applys triple_set_field. } { xsimpl. } { xsimpl*. } }
    { cases (hrecord_udpate k w kvs') as C2; tryfalse. inverts E.
      applys triple_conseq_frame. { applys IHkvs' C2. }
      { xsimpl. } { simpl. xsimpl*. } } }
Qed.

End GroupedFields.


(* ####################################################### *)
(** ** Curried functions of several arguments *)

Module CurriedFun.
Open Scope liblist_scope.
Implicit Types f : var.

(** We next give a quick presentation of the notation, lemmas and
    tactics involved in the manipulation of functions of several
    arguments. We focus here on the particular case of recursive
    functions with two arguments, to illustrate the principles.

    The lemmas for other arities can be found in the file [SLFExtra].
    One may attempt to generalize these definitions to handle
    arbitrary arities. Yet, to obtain an arity-generic treatment of
    functions, it is much simpler to work with primitive n-ary functions
    (i.e., functions that expects a list of variables, and that may be
    applied to a list of values). The treatment of these n-ary functions
    is beyond the scope of (the current version of) the course.

    So, let us focus on curried recursive functions of arity two.

    [val_fix f x1 (trm_fun x2 t)] describes a value that corresponds to
    a recursive function [t] that expects two arguments [x1] and [x2].
    Observe that the inner function, the one that expects [x2], is not
    recursive, and that it is not a value but a term, because it may
    refer to the variable [x1] bound outside of it.

    We introduce the notation [VFix f x1 x2 := t] to generalize
    [VFix f x := t] to the case of functions of two arguments. *)

Notation "'VFix' f x1 x2 ':=' t" :=
  (val_fix f x1 (trm_fun x2 t))
  (at level 69, f, x1, x2 at level 0,
  format "'VFix'  f  x1  x2  ':='  t").

(** An application of a function of two arguments takes the form
    [f v1 v2], which is actually parsed as [trm_app (trm_app f v1) v2].

    This expression is an application of a term to a value, and not of
    a value to a value. Thus, this expression cannot be evaluated using
    the rule [eval_app_fun]. We need a distinct rule for first evaluating
    the arguments of a function application to values, before we can
    evaluate the application of a value to a value.

    The rule [eval_app_arg] serves that purpose. To state it, we first
    need to characterize whether a term is a value or not, using the
    predicate [trm_is_val t] defined next. *)

Definition trm_is_val (t:trm) : Prop :=
  match t with trm_val v => True | _ => False end.

(** The statement of [eval_app_arg] then takes the following form.
    For an expression [trm_app t1 t2] where either [t1] or [t2] is
    not a value, it enables reducing both [t1] and [t2] to values,
    leaving a premise of the form [trm_app v1 v2], which is subject
    to the rule [eval_app_fun] for evaluating functions. *)

Parameter eval_app_arg : forall s1 s2 s3 s4 t1 t2 v1 v2 r,
  (~ trm_is_val t1 \/ ~ trm_is_val t2) ->
  eval s1 t1 s2 v1 ->
  eval s2 t2 s3 v2 ->
  eval s3 (trm_app v1 v2) s4 r ->
  eval s1 (trm_app t1 t2) s4 r.

(** Using this rule, we can establish an evaluation rule for the
    term [v0 v1 v2]. There, [v0] is a recursive function of two
    arguments named [x1] and [x2], the values [v1] and [v2] denote
    the corresponding arguments, and [f] denotes the name of the
    function available for making recursive calls from the body [t1].

    The key idea is that the behavior of [v0 v1 v2] is similar to
    that of the term [subst x2 v2 (subst x1 v1 (subst f v0 t1))].
    We state this property using the predicate [eval_like], introduced
    in the chapter [SLFRules]. *)

Lemma eval_like_app_fix2 : forall v0 v1 v2 f x1 x2 t1,
  v0 = val_fix f x1 (trm_fun x2 t1) ->
  (x1 <> x2 /\ f <> x2) ->
  eval_like (subst x2 v2 (subst x1 v1 (subst f v0 t1))) (v0 v1 v2).
Proof using.
  introv E (N1&N2). introv R. applys* eval_app_arg.
  { applys eval_app_fix E. simpl. do 2 (rewrite var_eq_spec; case_if).
    applys eval_fun. }
  { applys* eval_val. }
  { applys* eval_app_fun. }
Qed.

(** From this result, we can easily prove the specification triple
    for applications of the form [v0 v1 v2]. *)

Lemma triple_app_fix2 : forall f x1 x2 v0 v1 v2 t1 H Q,
  v0 = val_fix f x1 (trm_fun x2 t1) ->
  (x1 <> x2 /\ f <> x2) ->
  triple (subst x2 v2 (subst x1 v1 (subst f v0 t1))) H Q ->
  triple (v0 v1 v2) H Q.
Proof using.
  introv E N M1. applys triple_eval_like M1. applys* eval_like_app_fix2.
Qed.

(** We can exploit the same result to esablish the corresponding
    weakest-precondition style version of the reasoning rule. *)

Lemma wp_app_fix2 : forall f x1 x2 v0 v1 v2 t1 Q,
  v0 = val_fix f x1 (trm_fun x2 t1) ->
  (x1 <> x2 /\ f <> x2) ->
  wp (subst x2 v2 (subst x1 v1 (subst f v0 t1))) Q ==> wp (trm_app v0 v1 v2) Q.
Proof using. introv EQ1 N. applys wp_eval_like. applys* eval_like_app_fix2. Qed.

(** We can then reformulate this wp-style rule in a way that suits
    the needs of the [xwp] tactic, using a conclusion expressed
    using a [triple], and using a premise expressed using [wpgen].
    Observe the substitution context, which is instantiated as
    [(f,v0)::(x1,v1)::(x2,v2)::nil]. Note also how the side-conditions
    expressing the fact that the variables are distinct are stated
    using a comparison function for variables that computes in Coq. *)

Lemma xwp_lemma_fix2 : forall f v0 v1 v2 x1 x2 t H Q,
  v0 = val_fix f x1 (trm_fun x2 t) ->
  (var_eq x1 x2 = false /\ var_eq f x2 = false) ->
  H ==> wpgen ((f,v0)::(x1,v1)::(x2,v2)::nil) t Q ->
  triple (v0 v1 v2) H Q.
Proof using.
  introv M1 N M2. repeat rewrite var_eq_spec in N. rew_bool_eq in *.
  rewrite <- wp_equiv. xchange M2.
  xchange (>> wpgen_sound (((f,v0)::nil) ++ ((x1,v1)::nil) ++ ((x2,v2)::nil)) t Q).
  do 2 rewrite isubst_app. do 3 rewrite <- subst_eq_isubst_one.
  applys* wp_app_fix2.
Qed.

(** Finally, we can generalize the [xwp] tactic by integrating in
    its implementation an attempt to invoke the above lemma. *)

Tactic Notation "xwp" :=
  intros;
  first [ applys xwp_lemma_fun; [ reflexivity | ]
        | applys xwp_lemma_fix; [ reflexivity | ]
        | applys xwp_lemma_fix2; [ reflexivity | splits; reflexivity | ] ];
  xwp_simpl.

(** The generalized version of [xwp] following this line is
    formalized in the file [SLFExtra.v] and was put to practice
    in several examples from the chapter [SLFBasic]. *)

End CurriedFun.


(* ####################################################### *)
(** ** Primitive n-ary functions *)

Module PrimitiveNaryFun.

(** We next present an alternative treatment to functions of several
    arguments. The idea is to represent arguments using lists.

    On the one hand, the manipulation of lists adds a little bit of
    boilerplate. On the other hand, when using this representation, all
    the definitions and lemmas are inherently arity-generic, that is, they
    work for any number of arguments.

    We introduce the following short names for the lists types involved:
    [vars], [vals] and [trms]. These names are not only useful to improve
    conciseness, they also enable the set up of useful coercions, as we
    will detail shortly afterwards. *)

Definition vars : Type := list var.
Definition vals : Type := list val.
Definition trms : Type := list trm.

Implicit Types xs : vars.
Implicit Types vs : vals.
Implicit Types ts : trms.

(** We assume the grammar of terms and values to include primitive n-ary
    functions and n-ary applications, featuring list of arguments. Thereafter,
    for conciseness, we describe only the case of recursive functions. *)

Parameter val_fixs : var -> vars -> trm -> val.
Parameter trm_fixs : var -> vars -> trm -> trm.
Parameter trm_apps : trm -> trms -> trm.

(** The substitution function is a bit tricky to update for dealing with
    list of variables. A definition along the following lines works well.
    On the one hand, it prevents variables capture. On the other hand,
    it traverses recursively the list of arguments, in a way that is
    recognized as structurally recursive.

[[
    Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
      let aux t := (subst y w t) in
      let aux_no_captures xs t := (If List.In y xs then t else aux t) in
      match t with
      | trm_fixs f xs t1 => trm_fixs f xs (If f = y then t1 else
                                            aux_no_captures xs t1)
      | trm_apps t0 ts => trm_apps (aux t0) (List.map aux ts)
      ...
     end.
]]

    For additional details, we refer to the implementation of CFML.
*)

(** The evaluation rules need to be updated accordingly. A n-ary function
    from the grammar of terms evaluates to the corresponding n-ary
    function from the grammar of values. For technical reasons, we
    need to ensure that the program is well-formed and that the list
    of arguments to the function is nonempty. Indeed, a function of
    zero arguments is not considered a function in our language.
    (Otherwise, such a function [f] would beta-reduce to its body
    as soon as it is defined, because it waits for no arguments.) *)

Parameter eval_fixs : forall m f xs t1,
  xs <> nil ->
  eval m (trm_fixs f xs t1) m (val_fixs f xs t1).

(** A n-ary application of a function to values takes the form
    [trm_apps (trm_val v0) ((trm_val v1):: .. ::(trm_val vn)::nil)].
    If the function [v0] is defined as [val_fixs f xs t1], where [xs]
    denotes the list [x1::x2::...::xn::nil], then the beta-reduction
    of the function application triggers the evaluation of the
    substitution [subst xn vn (... (subst x1 v1 (subst f v0 t1)) ...)].

    To describe the evaluation rule in an arity-generic way, we need to
    introduce the list [vs] made of the values provided as arguments,
    that is, the list [v1::v2::..::vn::nil].

    With this list [vs], the n-ary application can then be written as the
    term [trm_apps (trm_val v0) (trms_vals vs)], where the operation
    [trms_vals] a list of terms into a list of values. *)

Coercion trms_vals (vs:vals) : trms :=
  LibList.map trm_val vs.

(** Note that we declare the operation [trms_vals] as a coercion, just
    like [trm_val] is a coercion. Doing so enables us to write a n-ary
    application in the form [v0 vs]. *)

(** To describe the iterated substitution
    [subst xn vn (... (subst x1 v1 (subst f v0 t1)) ...)], we introduce
    the operation [substn xs vs t], which substitutes the variables [xs]
    with the values [vs] inside the [t]. It is defined recursively. *)

Fixpoint substn (xs:list var) (vs:list val) (t:trm) : trm :=
  match xs,vs with
  | x::xs', v::vs' => substn xs' vs' (subst x v t)
  | _,_ => t
  end.

(** This substitution operation is well-behaved only if the list [xs]
    and the list [vs] have the same lengths. It is also desirable for
    reasoning about the evaluation rule to guarantee that the list of
    variables [xs] contains variables distinct from each others and
    distinct from [f], and that the list [xs] is not empty.

    To formally capture all these invariants, we introduce the predicate
    [var_fixs f xs n], [n] denotes the number of arguments the function
    is being applied to (i.e., the length of the list [vs]). *)

Definition var_fixs (f:var) (xs:vars) (n:nat) : Prop :=
     LibList.noduplicates (f::xs)
  /\ length xs = n
  /\ xs <> nil.

(** The evaluation of a recursive function [v0] defined as [val_fixs f xs t1]
    on a list of arguments [vs] triggers the evaluation of the term
    [substn xs vs (subst f v0 t1)], same as [substn (f::xs) (v0::vs) t1].
    The evaluation rule is stated as follows, using the predicate [var_fixs]
    to enforce the appropriate invariants on the variable names. *)

Parameter eval_apps_fixs : forall v0 vs f xs t1 s1 s2 r,
  v0 = val_fixs f xs t1 ->
  var_fixs f xs (LibList.length vs) ->
  eval s1 (substn xs vs (subst f v0 t1)) s2 r ->
  eval s1 (trm_apps v0 (trms_vals vs)) s2 r.

(** The corresponding reasoning rule has a somewhat similar statement. *)

Lemma triple_apps_fixs : forall v0 vs f xs t1 H Q,
  v0 = val_fixs f xs t1 ->
  var_fixs f xs (LibList.length vs)->
  triple (substn (f::xs) (v0::vs) t1) H Q ->
  triple (trm_apps v0 vs) H Q.
Proof using.
  introv E N M. applys triple_eval_like M.
  introv R. applys* eval_apps_fixs.
Qed.

(** The statement of the above lemma applies only to terms that are
    of the form [trm_apps (trm_val v0) (trms_vals vs)]. Yet, in practice,
    goals are generally of the form
    [trm_apps (trm_val v0) ((trm_val v1):: .. :: (trm_val vn)::nil)].
    The two forms are convertible, yet Coq is not able to synthetize
    the list [vs] by unification.

    Fortunately, it is possible to reformulate the lemma using an auxiliary
    conversion function named [trms_to_vals], whose evaluation by Coq's
    unification process is able to synthetize the list [vs]. *)

Fixpoint trms_to_vals (ts:trms) : option vals :=
  match ts with
  | nil => Some nil
  | (trm_val v)::ts' =>
      match trms_to_vals ts' with
      | None => None
      | Some vs' => Some (v::vs')
      end
  | _ => None
  end.

Lemma trms_to_vals_spec : forall ts vs,
  trms_to_vals ts = Some vs ->
  ts = trms_vals vs.
Proof using.
  intros ts. induction ts as [|t ts']; simpl; introv E.
  { inverts E. auto. }
  { destruct t; inverts E as E. cases (trms_to_vals ts') as C; inverts E.
    rename v0 into vs'. rewrite* (IHts' vs'). }
Qed.

Lemma demo_trms_to_vals : forall v1 v2 v3,
  exists vs,
     trms_to_vals ((trm_val v1)::(trm_val v2)::(trm_val v3)::nil) = Some vs
  /\ vs = vs.
Proof using. intros. esplit. split. simpl. eauto. (* [vs] was inferred. *) Abort.

(** Using [trms_to_vals], we can reformulate [triple_apps_fixs'] in such
    a way that the rule can be smoothly applied on practical goals. *)

Lemma triple_apps_fixs' : forall v0 ts vs f xs t1 H Q,
  v0 = val_fixs f xs t1 ->
  trms_to_vals ts = Some vs ->
  var_fixs f xs (LibList.length vs)->
  triple (substn (f::xs) (v0::vs) t1) H Q ->
  triple (trm_apps v0 ts) H Q.
Proof using.
  introv E T N M. rewrites (@trms_to_vals_spec _ _ T).
  applys* triple_apps_fixs.
Qed.

(** To set up the tactic [xwp] to handle n-ary applications, we reformulate
    the lemma above by making two changes.

    The first change is to replace the predicate [var_fixs] which checks
    the well-formedness properties of the list of variables [xs] by an
    executable version of this predicate, with a result in [bool]. This way,
    the tactic [reflexivity] can prove all the desired facts, when the lemma
    in invoked on a concrete function. We omit the details, and simply
    state the type of the boolean function [var_fixs_exec]. *)

Parameter var_fixs_exec : var -> vars -> nat -> bool.

(** The second change is to introduce the [wpgen] function in place of
    the triple for the evaluation of the body of the function. The
    substitution [substn (f::xs) (v0::vs)] then gets described by the
    substitution context [List.combine (f::xs) (v0::vs)], which describes
    a list of pairs of type [list (var * val)].

    The statement of the lemma for [xwp] is as follows. We omit the proof
    details---they may be found in the implementation of the CFML tool. *)

Parameter xwp_lemma_fixs : forall v0 ts vs f xs t1 H Q,
  v0 = val_fixs f xs t1 ->
  trms_to_vals ts = Some vs ->
  var_fixs_exec f xs (LibList.length vs) ->
  H ==> (wpgen (combine (f::xs) (v0::vs)) t1) Q ->
  triple (trm_apps v0 ts) H Q.

End PrimitiveNaryFun.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Bonus contents (optional reading) *)

(* ########################################################### *)
(** ** Formalization of allocation and deallocation operations *)

Module AllocSpec.

(** Earlier in this chapter, we have axiomatized the specification
    of the allocation function through the lemma [triple_alloc_nat]. *)

Parameter triple_alloc_nat' : forall k,
  triple (val_alloc k)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* harray_uninit k p).

(* TODO: rename l for p everywhere in the semantics *)

(** Like for other operations, this specification can be proved
    correct with respect to the semantics of the programming
    language. The allocation operation [val_alloc n] can be
    described as extending the state with a range of fresh
    consecutive cells.

    The evaluation rule below describes the behavior of [val_alloc].
    We write [LibList.make k val_uninit] for a list that repeats
    [k] times the value [val_uninit]. We write [Fmap.conseq p L]
    for a heap made of consecutive cells, starting at location [p],
    whose contents are described by the elements from the list [L].
    This heap is named [mb], and it extends the existing heap,
    which is named [ma]. *)

Parameter eval_alloc : forall k n ma mb p,
  mb = Fmap.conseq p (LibList.make k val_uninit) ->
  n = nat_to_Z k ->
  p <> null ->
  Fmap.disjoint ma mb ->
  eval ma (val_alloc (val_int n)) (Fmap.union mb ma) (val_loc p).

(** To verify the specification of allocation, the crux of the proof
    is to establish the lemma [harray_uninit_intro], which establishes
    that the heap built by [Fmap.conseq] in the rule [eval_alloc]
    satisfies the predicate [harray_uninit] that appears in the
    postcondition of [triple_alloc_nat].

    This lemma itself relies on an introduction lemma for [hcells],
    asserting that [Fmap.conseq p L] satisfies [hcells L p].

    The two lemmas involved are stated and proved below. It is not
    needed to follow through the proof details. *)

(* TODO fix order of L and p. *)

Lemma hcells_intro : forall L p,
  p <> null ->
  hcells L p (Fmap.conseq p L).
Proof using.
  intros L. induction L as [|L']; introv N; simpl.
  { applys hempty_intro. }
  { applys hstar_intro.
    { applys* hsingle_intro. }
    { applys IHL. unfolds loc, null. math. }
    { applys Fmap.disjoint_single_conseq. left. math. } }
Qed.

Lemma harray_uninit_intro : forall p k,
  p <> null ->
  harray_uninit k p (Fmap.conseq p (LibList.make k val_uninit)).
Proof using.
  introv N. unfold harray_uninit, harray.
  rewrite hstar_comm. rewrite hstar_hpure. split.
  { auto. } { applys* hcells_intro. }
Qed.

(** Using this lemma, we can prove the specification of [val_alloc].
    As usual, we first derive a Hoare logic statement, then the
    corresponding Separation Logic judgment. *)

Lemma hoare_alloc_nat : forall H k,
  hoare (val_alloc k)
    H
    (fun r => \exists p, \[r = val_loc p] \* harray_uninit k p \* H).
Proof using.
  intros. intros h Hh.
  forwards~ (p&Dp&Np): (Fmap.conseq_fresh null h k val_uninit).
  match type of Dp with Fmap.disjoint ?hc _ => sets h1': hc end.
  exists (h1' \u h) (val_loc p). split.
  { applys~ (eval_alloc k). }
  { applys hexists_intro p. rewrite hstar_hpure. split*.
    { applys* hstar_intro. applys* harray_uninit_intro. } }
Qed.

Lemma triple_alloc_nat : forall k,
  triple (val_alloc k)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* harray_uninit k p).
Proof using.
  intros. intros H'. applys hoare_conseq.
  { applys hoare_alloc_nat H'. } { xsimpl. } { xsimpl*. }
Qed.

(** Similarly, we can formalize the behavior and the specification of
    the deallocation operation [val_dealloc n p].

    This time, the initial state is of the union of a heap [mb],
    describing the part to be deallocated, and a disjoint heap [ma],
    describing the part of the state that remains. The heap [mb]
    must correspond to [n] consecutive cells, starting at location [p]. *)

Parameter eval_dealloc : forall n vs ma mb p,
  mb = Fmap.conseq p vs ->
  n = LibList.length vs ->
  Fmap.disjoint ma mb ->
  eval (Fmap.union mb ma) (val_dealloc (val_int n) (val_loc p)) ma val_unit.

(** To verify the specification of deallocation, the crux of the proof
    is to establish that if a heap satisfies [hcells L p], then this
    heap is described by [Fmap.conseq p L].

    This technical lemma is stated as follows. The proof is by induction
    on the list [L]. (No need to follow throught the proof details.) *)

Lemma hcells_inv : forall p L h,
  hcells L p h ->
  h = Fmap.conseq p L.
Proof using.
  introv N. gen p h. induction L as [|x L']; simpl; intros.
  { applys hempty_inv N. }
  { lets (h1&h2&N1&N2&N3&->): hstar_inv N. fequal.
    { applys hsingle_inv N1. }
    { applys IHL' N2. } }
Qed.

(** Using this lemma, we can prove the specification of [val_dealloc]. *)

Lemma hoare_dealloc_hcells : forall H L p n,
  n = length L ->
  hoare (val_dealloc n p)
    (hcells L p \* H)
    (fun _ => H).
Proof using.
  introv N. intros h Hh. destruct Hh as (h1&h2&N1&N2&N3&N4). subst h.
  exists h2 val_unit. split; [|auto].
  applys* (@eval_dealloc n L). applys hcells_inv N1.
Qed.

Lemma triple_dealloc_hcells : forall L n p,
  n = length L ->
  triple (val_dealloc n p)
    (hcells L p)
    (fun _ => \[]).
Proof using.
  introv E. intros H'. applys hoare_conseq.
  { applys hoare_dealloc_hcells H' E. } { xsimpl. } { xsimpl. }
Qed.

(** It is straightforward to derive the alternative specification
    stated using [harray L p] in place of [hcells L p]. *)

Lemma triple_dealloc_harray : forall L n p,
  n = length L ->
  triple (val_dealloc n p)
    (harray L p)
    (fun _ => \[]).
Proof using.
  introv E. xtriple. unfold harray. xpull. intros N.
  xapp triple_dealloc_hcells. { auto. } { xsimpl. }
Qed.

End AllocSpec.


(* ########################################################### *)
(** ** Specification of pointer arithmetic *)

Module PointerAdd.

(** Pointer arithmetic can be useful in particular to define access
    operations an arrays and on records in terms of the primitive
    operations [val_get] and [val_set]. Let us describe the semantics
    and specification of the operation that adds on offset to a pointer.

    The operation [val_ptr p n] applies to a pointer [p] and an integer [n].
    The integer [n] may be negative, as long as [p+n] corresponds to a
    valid location, i.e., [p+n] must be nonnegative. *)

Parameter eval_ptr_add : forall p' p n s,
  (p':int) = p + n ->
  eval s (val_ptr_add (val_loc p) (val_int n)) s (val_loc p').

Lemma triple_ptr_add : forall p n,
  p + n >= 0 ->
  triple (val_ptr_add p n)
    \[]
    (fun r => \[r = val_loc (abs (p + n))]).
Proof using.
  intros. applys* triple_binop. applys* evalbinop_ptr_add.
  { rewrite~ abs_nonneg. }
Qed.

(** The following lemma specializes the specification for the case
    where the argument [n] is equal to a natural number [k]. This
    reformulation avoids the [abs] function, and is more practical for
    the encodings that we consider further in the subsequent sections. *)

Lemma triple_ptr_add_nat : forall p k,
  triple (val_ptr_add p k)
    \[]
    (fun r => \[r = val_loc (p+k)%nat]).
Proof using.
  intros. applys triple_conseq triple_ptr_add. { math. } { xsimpl. }
  { xsimpl. intros. subst. fequals.
    applys eq_nat_of_eq_int. rewrite abs_nonneg; math. }
Qed.

End PointerAdd.


(* ########################################################### *)
(** ** Definition of record operations using pointer arithmetics *)

Module FieldOps.
Import SLFProgramSyntax.
Transparent hfield.

(** Most real-world programming languages include primitive operations
    for reading and writing in record cells. Yet, in a simple language
    like ours, record cells can be accessed by means of pointer arithmetic.
    It is interesting to see how one may formally reason about this kind
    of encoding. *)

(** For example, the read operation on record fields can be implemented
    within our language, as the combination of a pointer addition and
    a read operation. More precisely, reading in [p`.f] using
    [val_get_field] is like reading at address [p+f] using [val_get],
    where [p+f] is computed by invoking [val_ptr_add p k]. *)

Definition val_get_field (k:field) : val :=
  VFun 'p :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_get 'q.

(** The specification of [val_get_field] can be established just like
    for any other function. *)

Lemma triple_get_field : forall p f v,
  triple ((val_get_field f) p)
    (p`.f ~~> v)
    (fun r => \[r = v] \* (p`.f ~~> v)).
Proof using.
  xwp. xapp. unfold hfield. xpull. intros N. xapp. xsimpl*.
Qed.

(** A similar construction applies to the write operation on record
    fields. *)

Definition val_set_field (k:field) : val :=
  VFun 'p 'v :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_set 'q 'v.

Lemma triple_set_field : forall v1 p f v2,
  triple ((val_set_field f) p v2)
    (p`.f ~~> v1)
    (fun _ => p`.f ~~> v2).
Proof using.
  xwp. xapp. unfold hfield. xpull. intros N. xapp. xsimpl*.
Qed.

End FieldOps.


(* ########################################################### *)
(** ** Definition of array operations using pointer arithmetics *)

(** Lemmas for distributing [hcells] over a [nil], over a [cons],
    and over a list concatenation. *)

Lemma hcells_nil_eq : forall p,
  hcells nil p = \[].
Proof using. auto. Qed.

Lemma hcells_cons_eq : forall p x L,
  hcells (x::L) p = (p ~~> x) \* hcells L (S p).
Proof using. intros. simpl. xsimpl*. Qed.

Lemma hcells_concat_eq : forall p L1 L2,
  hcells (L1++L2) p = (hcells L1 p \* hcells L2 (length L1 + p)%nat).
Proof using.
  intros. gen p. induction L1; intros; rew_list; simpl.
  { xsimpl. }
  { rewrite IHL1. math_rewrite (length L1 + S p = S (length L1 + p))%nat.
    xsimpl. }
Qed.

(** Similar lemmas for [harray]. *)

Lemma harray_nil_eq : forall p,
  harray nil p = \[p <> null].
Proof using. intros. unfold harray. rewrite hcells_nil_eq. xsimpl*. Qed.

Lemma harray_cons_eq : forall p x L,
  harray (x::L) p = (p ~~> x) \* harray L (S p).
Proof using.
  intros. unfold harray. applys himpl_antisym.
  { rewrite hcells_cons_eq. xsimpl. unfolds loc, null. intros. math. }
  { xchange hsingle_not_null. intros N. rewrite hcells_cons_eq. xsimpl*. }
(* TODO *)
Qed.

Lemma harray_concat_eq : forall p L1 L2,
  harray (L1++L2) p = (harray L1 p \* harray L2 (length L1 + p)%nat).
Proof using.
  intros. unfold harray, null, loc. rewrite hcells_concat_eq.
  applys himpl_antisym; xsimpl*. math.
Qed.


(* ########################################################### *)
(** ** Definition of array operations using pointer arithmetics *)

Module ArrayOps.
Import SLFProgramSyntax.

(** For example, an array operation on the [i]-th cell of an array at
    location [p] can be implemented within our language, as the application
    of a read or write operation at the address [p+i].

    In order to reason about the read or write operation on a specific
    cell, we need to isolate this cell from the other cells of the array.
    Then, after the operation, we need to fold back to the view on the
    entire array.

    The isolation process is captured in a general way by the following
    "focus lemma". It reads as follows. Assume [harray L p] to initially
    describe the full array. The, the [k]-th cell can be isolated as a
    predicate [(p+k) ~~> v], where [v] denotes the [k]-th item of [L],
    that is [LibList.nth k L].

    What remains can be described using the magic wand operator as
    [((p+k) ~~> v) \-* (harray L p)], which captures the idea that when
    providing back the cell at location [p+k], one would regain the
    ownership of the full array. *)

Parameter harray_focus_read : forall k p v L,
  k < length L ->
  v = LibList.nth k L ->
  harray L p ==>
       ((p+k)%nat ~~> v)
    \* ((p+k)%nat ~~> v \-* harray L p).

(** The above focus lemma works for read operations but falls short for
    a write operation, because it imposes the array to be put back in
    its original form. It does not take into account the possibility
    to fold back the array with a modified contents for the cell at [p+k].

    This observation leads us to generalize the magic wand describing
    the rest of the array into the form:
    [\forall w, ((p+k)%nat ~~> w) \-* harray (LibList.update k w L) p],
    which indicates that for any new contents [w], the array can be folded
    back into [harray L' p], where [L'] denotes the update of the list [L]
    with [w] at location [k] (instead of [v]).

    We state and prove this general focus lemma as follows. *)

Lemma harray_focus : forall k p L,
  k < length L ->
  harray L p ==>
       ((p+k)%nat ~~> LibList.nth k L)
    \* (\forall w, ((p+k)%nat ~~> w) \-* harray (LibList.update k w L) p).
Proof using.
  introv E. gen k p. induction L as [|x L']; rew_list; intros.
  { false. math. }
  { simpl. rewrite nth_cons_case. case_if.
    { subst. math_rewrite (p + 0 = p)%nat.
       rewrite harray_cons_eq. xsimpl. intros w.
       rewrite LibList.update_zero. rewrite harray_cons_eq. xsimpl*. }
    { rewrite harray_cons_eq.
      forwards R: IHL' (k-1)%nat (S p). { math. }
      math_rewrite (S p + (k - 1) = p + k)%nat in R. xchange R.
      xsimpl. intros w. xchange (hforall_specialize w).
      rewrite update_cons_pos; [|math]. rewrite harray_cons_eq. xsimpl. } }
Qed.

(** In the proofs below, the following mathematical lemma is useful to
    verify that indices remain in the bounds. *)

Lemma abs_lt_length : forall i L,
  0 <= i < nat_to_Z (length L) ->
  (abs i < length L).
Proof using.
  introv N. apply lt_nat_of_lt_int. rewrite abs_nonneg; math.
Qed.

(** Consider the read operation in an array, written [val_array_get p i].
    We can define it as [val_get (val_ptr_add p i)], then prove its
    specification expressed in terms of [LibList.nth (abs i) L]. *)

Definition val_array_get : val :=
  VFun 'p 'i :=
    Let 'n := val_ptr_add 'p 'i in
    val_get 'n.

Lemma triple_array_get : forall p i L,
  0 <= i < length L ->
  triple (val_array_get p i)
    (harray L p)
    (fun r => \[r = LibList.nth (abs i) L] \* harray L p).
Proof using.
  introv N. xwp. xapp triple_ptr_add. { math. }
  xchange (@harray_focus (abs i) p L). { applys* abs_lt_length. }
  sets v: (LibList.nth (abs i) L).
  rewrite abs_nat_plus_nonneg; [|math].
  xapp triple_get. xchange (hforall_specialize v). subst v.
  rewrite update_nth_same. xsimpl*. { applys* abs_lt_length. }
Qed.

(** Consider now a write operation, written [val_array_set p i v].
    We can define it as [val_set (val_ptr_add p i) v], then prove its
    specification expressed in terms of [LibList.update (abs i) v L]. *)

Definition val_array_set : val :=
  VFun 'p 'i 'x :=
    Let 'n := val_ptr_add 'p 'i in
    val_set 'n 'x.

Lemma triple_array_set : forall p i v L,
  0 <= i < length L ->
  triple (val_array_set p i v)
    (harray L p)
    (fun _ => harray (LibList.update (abs i) v L) p).
Proof using.
  introv N. xwp. xapp triple_ptr_add. { math. }
  xchange (@harray_focus (abs i) p L). { applys* abs_lt_length. }
  rewrite abs_nat_plus_nonneg; [|math].
  xapp triple_set. xchange (hforall_specialize v).
Qed.

End ArrayOps.

