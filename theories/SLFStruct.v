(**

Foundations of Separation Logic

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
Implicit Types nb : nat.


(* TODO *)

Definition mem_assoc A B (x:A) (l:list (A*B)) : Prop :=
  LibList.mem x (LibList.map fst l).


(* ####################################################### *)
(* ####################################################### *)
(* ####################################################### *)
(** * Chapter in a rush *)

(** This chapter introduces support for reasoning about mutable records
    and mutable arrays,

    To allocate records and arrays, we introduce two new primitive operations,
    named [val_alloc] and [val_dealloc], for allocating and deallocating
    at once a range of consecutive memory cells.

    In the first part of this chapter, we present the specification of
    the operations on arrays and records. In the second part of this chapter,
    we show how these operations can be implemented with heap of pointer
    arithmetic operations, and specified with respect to a memory model
    that exposes a particular representation of headers for allocated blocks.

    This memory model is somewhat artificial, in the sense that it does not
    perfectly match the memory model of an existing language----it is somewhere
    between the memory model of C and that of OCaml. Nevertheless, this
    memory model has the benefits of its simplicity, and it suffices to
    illustrate formal proofs involving block headers and pointer arithmetics. *)


(* ####################################################### *)
(** ** Representation of a set of consecutive cells *)

(** The cells from an array of length [k] can be represented as a range of [k]
    consecutive cells, starting at some location [p]. In other words, the
    array cells have addresses from [p] inclusive to [p+k] exclusive.

    The contents of an array of length [k] can be represented by a list
    of values of length [k]. This idea is formalized by the predicate [hcells].

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

(** The description of an array, that is, a set of consecutive cells,
    can be split in two parts, at an arbitrary index. Concretely, if
    we have [harray (L1++L2) p], then we can separate the left part
    [harray L1 p] from the right part [harray L2 q], where the address
    [q] is equal to [p + length L1]. Reciprocally, the two parts can
    be merged back into the original form at any time. *)

Parameter hcells_concat_eq : forall p L1 L2,
  hcells (L1++L2) p = (hcells L1 p \* hcells L2 (length L1 + p)%nat).

(** This "splitting lemma for arrays" is useful to carry out local
    reasoning on arrays, by focusing on the segment of the array involved
    in each recursive call, and obtaining for free the fact that the
    cells outside of the segment remain unmodified. *)


(* ####################################################### *)
(** ** Representation of an array with a block header *)

(** An array consists of a "header", and of the description of its cells.
    The header is a heap predicate that describes the length of the array.

    - In OCaml, the header consists of a physical memory cell at the
      head of the array. This cell may be queried to obtain the length
      of the array.
    - In C, the header is a logical notion. It describes the length of
      the allocated block, and it used in Separation Logic to specify
      the behavior of the deallocation function, which can only be called
      on the address of an allocated block, deallocating the full block
      at once.

   In this course, we follow the OCaml view, with phyiscal headers.
   However, the definitions could be easily adapted to follow the C view.

   The predicate [hheader k p] asserts the existence of an allocated
   block at location [p], such that the contents of the block is made
   of [k] cells (not counting the header cell). For the moment, we leave
   its definition abstract. *)

Parameter hheader : forall (k:nat) (p:loc), hprop.

(** The heap predicate [hheader k p] should capture the information 
    that [p] is not null---blocks cannot be allocated at the null location. *)

Parameter hheader_not_null : forall p k,
  hheader k p ==> hheader k p \* \[p <> null].

(** An array is described by the predicate [harray L p], where the list
    [L] describes the contents of the cells. This heap predicate covers
    both the header, which describes a block of length equal to [length L],
    and the contents of the cells, described by [hcells L (p+1)].
    Indeed, [p+1] is the first cell of the array, located next to the
    header cell at location [p]. *)

Definition harray (L:list val) (p:loc) : hprop :=
  hheader (length L) p \* hcells L (p+1)%nat.


(* ####################################################### *)
(** ** Specification of allocation *)

(** The primitive operation [val_alloc k] allocates a block made of
    [k] consecutive cells. *)

Parameter val_alloc : prim.

(** The operation [val_alloc k] is specified as producing an array
    whose cells contain the special "uninitialized value", written
    [val_uninit]. *)

Parameter val_uninit : val.

(** More precisely, the postcondition of [val_alloc k] is of the form
   [funloc p => harray L p], where the list [L] is defined as the
   repetition of [k] times the value [val_uninit]. *)

Parameter triple_alloc_nat : forall k,
  triple (val_alloc k)
    \[]
    (funloc p => harray (LibList.make k val_uninit) p).

(** In practice, the operation [val_alloc] is applied to a non-negative
    integer, that may not necessarily be syntactically a natural number.
    Hence, the following lemma, which specifies [val_alloc n] for [n >= 0],
    is more handy to use. *)

Parameter triple_alloc : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (funloc p => harray (LibList.make (abs n) val_uninit) p).

(** The specification above turns out to be often unncessarily precise.
    For most applications, it is sufficient for the postcondition to
    describe the array as [harray L p] for some unspecified list [L]
    of length [n]. This weaker specification is stated and proved next. *)

Parameter triple_alloc_array : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (funloc p => \exists L, \[n = length L] \* harray L p).


(* ####################################################### *)
(** ** Specification of the deallocation *)

(** The deallocation operation [val_dealloc p] deallocates the block
    allocated at location [p]. *)

Parameter val_dealloc : prim.

(** The specification of [val_dealloc p] features a precondition that
    requires an array of the form [harray L p], and an empty postcondition. *)

Parameter triple_dealloc : forall L p,
  triple (val_dealloc p)
    (harray L p)
    (fun _ => \[]).

(** Observe that the [harray L p] predicate includes a header of the form
    [hheader k p], ensuring that the corresponding allocated block is
    deallocated exactly once. *)


(* ####################################################### *)
(** ** Specification of array operations *)

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

(** The specification of [val_array_set] admits the same precondition as
    [val_array_get], with [harray L p] and the constraint [0 <= i < length L].
    Its postcondition describes the updated array using a predicate of the
    form [harray L' p], where [L'] corresponds to [update (abs i) v L]. *)

Parameter triple_array_set : forall L p i v,
  0 <= i < length L ->
  triple (val_array_set p i v)
    (harray L p)
    (fun _ => harray (LibList.update (abs i) v L) p).

(** The operation [val_array_length p] returns the length of the array
    allocated at location [p]. *)

Parameter val_array_length : val.

(** There are two useful specifications for [val_array_length]. The first
    one operates with the heap predicate [harray L p]. The return value is
    then the length of the list [L]. *)

Parameter triple_array_length : forall L p,
  triple (val_array_length p)
    (harray L p)
    (fun r => \[r = length L] \* harray L p).

(** The second specification for [val_array_length] operates only on the
    header of the array. This small-footprint specification is useful to
    read the length of an array whose cells are described by separated
    segments, that is, after [hcells_concat_eq] has been exploited. *)

Parameter triple_array_length_header : forall k p,
  triple (val_array_length p)
    (hheader k p)
    (fun r => \[r = (k:int)] \* hheader k p).

Hint Resolve triple_array_get triple_array_set triple_array_length : triple.


(* ########################################################### *)
(** ** Representation of individual records fields *)

(** A record can be represented just like an array, with the field names
    corresponding to offsets in that array.

    We let [field] denote the type of field names, an alias for [nat]. *)

Definition field : Type := nat.

(** For example, consider a mutable list cell allocated at location [p].
    It is represented in memory as:

    - a header at location [p], storing the number of fields, that is,
      the value [2];
    - a cell at location [p+1], storing the contents of the head field,
    - a cell at location [p+2], storing the contents of the tail field.

    Concretely, the record can be represented by the heap predicate:
    [(hheader 2 p) \* ((p+1) ~~> x) \* ((p+2) ~~> q)]. *)

(** To avoid exposing pointer arithmetic to the end-user, let us introduce
    the "record field" notation [p`.k ~~> v] to denote [(p+1+k) ~~> v].
    For example, with the definition of the field offsets [head := 0]
    and [tail := 1], the same record as before can be represented as:
    [(hheader 2 p) \* (p`.head ~~> x) \* (p`.tail ~~> q)]. *)

Definition hfield (p:loc) (k:field) (v:val) : hprop :=
  (p+1+k)%nat ~~> v.

Notation "p `. k '~~>' v" := (hfield p k v)
  (at level 32, k at level 0, no associativity,
   format "p `. k  '~~>'  v").


(* ########################################################### *)
(** ** Representation of records *)

(** Describing, e.g., a list cell record in the form
    [(hheader 2 p) \* (p`.head ~~> x) \* (p`.tail ~~> q)]
    in particularly verbose and cumbersome to manipulate.

    To improve the situation, we next introduce generic representation
    predicate for records that allows to describe the same list cell
    much more concisely, as [p ~~~>`{ head := x; tail := q }].

    It what follows, we show how to implement this notation by introducing
    the heap predicates [hfields] and [hrecords], and rpesent the
    specification of record operations with respect to those predicates. *)

(** A record field is described as the pair of a field and a value
    stored in this field. *)

Definition hrecord_field : Type := (field * val).

(** A record consists of of a list of fields. *)

Definition hrecord_fields : Type := list hrecord_field.

(** We let the meta-variable [kvs] denote such lists. *)

Implicit Types kvs : hrecord_fields.

(** A list cell with head field [x] and tail field [q] is represented
    by the list [(head,x)::(tail,q)::nil]. To support the syntax
    [`{ head := x; tail := q }], we introduce the following notation. *)

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

Notation "`{ k1 := v1 }" :=
  ((k1,v1)::nil)
  (at level 0, k1 at level 0, only printing)
  : val_scope.

Notation "`{ k1 := v1 ; k2 := v2 }" :=
  ((k1,v1)::(k2,v2)::nil)
  (at level 0, k1, k2 at level 0, only printing)
  : val_scope.

Notation "`{ k1 := v1 ; k2 := v2 ; k3 := v3 }" :=
  ((k1,v1)::(k2,v2)::(k3,v3)::nil)
  (at level 0, k1, k2, k3 at level 0, only printing)
  : val_scope.

Open Scope val_scope.

(** The heap predicate [hfields kvs p] asserts that at location [p]
    one finds the representation of the fields described by the list [kvs].
    This predicate is defined recursively on the list [kvs].
    If [kvs] is empty, the predicate describes the empty heap predicate.
    Otherwise, it describes a first field, at offset [k] and with contents
    [v], as the predicate [p`.k ~~> v], and it describes the remaining
    fields recursively. *)

Fixpoint hfields (kvs:hrecord_fields) (p:loc) : hprop :=
  match kvs with
  | nil => \[]
  | (k,v)::kvs' => (p`.k ~~> v) \* (hfields kvs' p)
  end.

(** The heap predicate [hrecord kvs p] describes a record: it covers
    not just all the fields of the record, but also the header.
    The cells are described by [hfields kvs p], and the header is
    described by [hheader nb p], where [nb] should be such that the
    keys in the list [kvs] are between [0] inclusive and [nb] exclusive.
    This latter property is captured by the auxiliary predicate
    [all_fields nb kvs]. *)

Definition all_fields (nb:nat) (kvs:hrecord_fields) : Prop :=
  forall k, 0 <= k < nb <-> mem_assoc k kvs.

Definition hrecord (kvs:hrecord_fields) (p:loc) : hprop :=
  \exists nb, hheader nb p \* hfields kvs p \* \[all_fields nb kvs].

(** The heap predicate [hrecord kvs p] captures in particular the 
    invariant that the location [p] is not null. *)

Lemma hrecord_not_null : forall p kvs,
  hrecord kvs p ==> hrecord kvs p \* \[p <> null].
Proof using.
  intros. unfold hrecord. xpull. intros nb M.
  xchanges* hheader_not_null.
Qed.

(** We introduce the notation [p ~~~> kvs] for [hrecord kvs p],
    allowing to write, e.g., [p ~~~>`{ head := x; tail := q }]. *)

Notation "p '~~~>' kvs" := (hrecord kvs p)
  (at level 32) : hprop_scope.

(** For example, the definition of the representation predicate [MList]
    can be revisited using the heap predicate for records. *)

Definition head : field := 0%nat.
Definition tail : field := 1%nat.

Fixpoint MList (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists q, (p ~~~>`{ head := x; tail := q}) \* (MList L' q)
  end.


(* ########################################################### *)
(** ** Reading in record fields *)

(** The read operation is described by an expression of the form
    [val_get_field k p], where [k] denotes a field name, and where [p]
    denotes the location of a record. Technically, [val_get_field k]
    is a value, and this value is applied to the pointer [p]. Hence,
    [val_get_field] has type [field -> val]. *)

Parameter val_get_field : field -> val.

(** The read operation [val_get_field k p] can be abbreviated as [p'.k]. *)

Notation "t1 ''.' k" :=
  (val_get_field k t1)
  (at level 56, k at level 0, format "t1 ''.' k" ).

(** The operation [val_get_field k p] can be specified at three levels.
    First, its small-footprint specification operates at the level of
    a single field, described by [p`.k ~~> v]. The specification is
    very similar to that of [val_get]: the return value is exactly [v]. *)

Parameter triple_get_field : forall p k v,
  triple (val_get_field k p)
    (p`.k ~~> v)
    (fun r => \[r = v] \* (p`.k ~~> v)).

(** Second, this operation can be specified with respect to a list of
    fields, described in the form [hfields kvs p]. To that end, we introduce
    a function called [hfields_lookup] for extracting the value [v]
    associated with a field [k] in a list of record fields [kvs].
    The opeation [hfields_lookup k kvs] returns a result of type [option val],
    because we cannot presume that the field [k] occurs in [kvs], even though
    it is always the case in practice. *)

Fixpoint hfields_lookup (k:field) (kvs:hrecord_fields) : option val :=
  match kvs with
  | nil => None
  | (ki,vi)::kvs' => if Nat.eq_dec k ki
                       then Some vi
                       else hfields_lookup k kvs'
  end.

(** Under the assumption that [hfields_lookup k kvs] returns [Some v],
    the read operation [val_get_field k p] is specified to return [v].
    The corresponding specification appears below. *)

Parameter triple_get_field_hfields : forall kvs p k v,
  hfields_lookup k kvs = Some v ->
  triple (val_get_field k p)
    (hfields kvs p)
    (fun r => \[r = v] \* hfields kvs p).

(** Third and last, the read operation can be specified with respect
    to the predicate [hrecord kvs p], describing the full record, including
    its header. The specification is similar to the previous one. *)

Parameter triple_get_field_hrecord : forall kvs p k v,
  hfields_lookup k kvs = Some v ->
  triple (val_get_field k p)
    (hrecord kvs p)
    (fun r => \[r = v] \* hrecord kvs p).


(* ########################################################### *)
(** ** Writing in record fields *)

(** The write operation is described by an expression of the form
    [val_get_field k p v], where [k] denotes a field name, and where [p]
    denotes the location of a record, and [v] is the new value for the field. *)

Parameter val_set_field : field -> val.

(** The write operation [val_get_field k p v] can be abbreviated as
    [Set p'.k ':= v]. *)

Notation "'Set' t1 ''.' k '':=' t2" :=
  (val_set_field k t1 t2)
  (at level 65, t1 at level 0, k at level 0, format "'Set' t1 ''.' k  '':=' t2").

(** Like for the read operation, the write operation can be specified at three
    levels. First, at the level of an individual field. *)

Parameter triple_set_field : forall v p k v',
  triple (val_set_field k p v)
    (p`.k ~~> v')
    (fun _ => p`.k ~~> v).

(** Then, at the level of [hfields] and [hrecord]. To that end, we
    introduce an auxiliary function called [hrecord_update] for computing
    the updated list of fields following an write operation.
    Concretely, [hrecord_update k w kvs] replaces the contents of the field named
    [k] with the value [w]. It returns some description [kvs'] of the record fields,
    provided the update operation succeeded, i.e., provided that the field [k]
    on which the update is to be performed actually occurs in the list [kvs]. *)

Fixpoint hfields_update (k:field) (v:val) (kvs:hrecord_fields)
                        : option hrecord_fields :=
  match kvs with
  | nil => None
  | (ki,vi)::kvs' => if Nat.eq_dec k ki
                   then Some ((k,v)::kvs')
                   else match hfields_update k v kvs' with
                        | None => None
                        | Some LR => Some ((ki,vi)::LR)
                        end
  end.

(** The specification in terms of [hfields] is as follows. *)

Parameter triple_set_field_hfields : forall kvs kvs' k p v,
  hfields_update k v kvs = Some kvs' ->
  triple (val_set_field k p v)
    (hfields kvs p)
    (fun _ => hfields kvs' p).

(** The specification in terms of [hrecord] is similar. *)

Parameter triple_set_field_hrecord : forall kvs kvs' k p v,
  hfields_update k v kvs = Some kvs' ->
  triple (val_set_field k p v)
    (hrecord kvs p)
    (fun _ => hrecord kvs' p).


(* ########################################################### *)
(** ** Allocation and deallocation of records *)

(** Because records are internally described like arrays, records may
    be allocated and deallocated using the operations [val_alloc] and
    [val_dealloc], just like for arrays. That said, it is useful to
    express derived specifications for these two operations stated in
    terms of representation predicate [hrecord], which describes a
    full record in terms of the list of its fields. *)

(** Deallocation of a record, written [val_dealloc_record p] is the simplest.
    This operation is implemented simply as [val_dealloc p]. *)

Definition val_dealloc_record : val := val_dealloc.

(** The specification of this operation simply requires as precondition
    the full record description, in the form [hrecord kvs p], and yields
    the empty postcondition. *)

Parameter triple_dealloc_record : forall kvs p,
  triple (val_dealloc_record p)
    (hrecord kvs p)
    (fun _ => \[]).

(** To improve readability, we introduce the notation [Delete p]
    for record deallocation. *)

Notation "'Delete' p" := (val_dealloc_record p)
  (at level 65) : trm_scope.

(** For example, this lemma can be used to reason about deallocation
    of a list cell. *)

Lemma triple_dealloc_mcell : forall p x q,
  triple (val_dealloc_record p)
    (p ~~~> `{ head := x ; tail := q })
    (fun _ => \[]).
Proof using. intros. applys* triple_dealloc_record. Qed.

(** Allocation is a bit trickier, because one needs to introduce the
    fields names for the record to be allocated. These fields names
    may be described by a list of field names of type [list field].
    This list, written [ks], should be equivalent to a list of
    consecutive natural numbers [0 :: 1 :: ... :: n-1], where [n] 
    denotes the number of fields. The interest of introducing the list
    [ks] is to provide readable names in place of numbers.

    The operation [val_alloc_record ks] is implemented by invoking
    [val_alloc] on the length of [ks]. *)

Definition val_alloc_record (ks:list field) : trm :=
  val_alloc (length ks).

(** The specification of [val_alloc_record ks] involves an empty
    precondition and a postcondition of the form [hrecord kvs p],
    where the list [kvs] maps the fields names from [ks] to the
    value [val_uninit]. The premise expressed in terms of [nat_seq]
    ensures that the list [ks] contains consecutive offsets starting
    from zero. *)

Parameter triple_alloc_record : forall ks,
  ks = nat_seq 0 (LibListExec.length ks) ->
  triple (val_alloc_record ks)
    \[]
    (funloc p => hrecord (LibListExec.map (fun k => (k,val_uninit)) ks) p).

Hint Resolve triple_alloc_record triple_dealloc_record : triple.

(** For example, the allocation of a list cell is specified as follows. *)

Lemma triple_alloc_mcell :
  triple (val_alloc_record (head::tail::nil))
    \[]
    (funloc p => p ~~~> `{ head := val_uninit ; tail := val_uninit }).
Proof using. applys* triple_alloc_record. Qed.



(* ########################################################### *)
(** ** Combined record allocation and initialization *)

(** It is often useful to allocate a record and immediately initialize
    its fields. To that end, we introduce the operation [val_new_record],
    which applies to a list of fields and to values for these fields.
    This operation can be defined in an arity-generic way, yet to begin
    with let us present its specifialization to the arity 2. *)

Module RecordInit.
Import SLFProgramSyntax.

Definition val_new_record_2 (k1:field) (k2:field) : val :=
  Fun 'x1 'x2 :=
    Let 'p := val_alloc_record (k1::k2::nil) in
    Set 'p'.k1 ':= 'x1 ';
    Set 'p'.k2 ':= 'x2 ';
    'p.

(** To improve readability, we introduce notation to allow writing, e.g.,
    [New`{ head := x; tail := q }] for the allocation and initialization
    of a list cell. *)

Notation "'New' `{ k1 := v1 ; k2 := v2 }" :=
  (val_new_record_2 k1 k2 v1 v2)
  (at level 65, k1, k2 at level 0) : trm_scope.

(** This operation is specified as follows. *)

Lemma triple_new_record_2 : forall k1 k2 v1 v2,
  k1 = 0%nat ->
  k2 = 1%nat ->
  triple (New `{ k1 := v1; k2 := v2 })
    \[]
    (funloc p => p ~~~> `{ k1 := v1 ; k2 := v2 }).
Proof using.
  introv -> ->. xwp. xapp triple_alloc_record. { auto. } intros p. simpl.
  xapp triple_set_field_hrecord. { reflexivity. }
  xapp triple_set_field_hrecord. { reflexivity. }
  xval. xsimpl*.
Qed.

(** For example, the operation [mcell x q] allocates a list cell with
    head value [x] and tail pointer [q]. *)

Definition mcell : val :=
  val_new_record_2 head tail.

Lemma triple_mcell : forall (x q:val),
  triple (mcell x q)
    \[]
    (funloc p => p ~~~> `{ head := x ; tail := q }).
Proof using. intros. applys* triple_new_record_2. Qed.

End RecordInit.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Additional contents *)

(* ########################################################### *)
(** ** Extending [xapp] to support record access operations *)

(** The tactic [xapp] can be refined to automatically invoke the 
    lemmas [triple_get_field_hrecord] and [triple_set_field_hrecord],
    which involve preconditions of the form
    [hfields_lookup k kvs = Some v] and
    [hfields_update k v kvs = Some ks'], respectively. 

    The auxiliary lemmas reformulate the specification triples in
    weakest-precondition form. The premise takes the form
    [H ==> \exists kvs, (hrecord kvs p) \* match ... with Some .. => ..].
    This presentation enables using [xsimpl] to extract the description
    of the record, named [kvs], before evaluating the [lookup] or
    [update] function for producing the suitable postcondition. *)

Lemma xapp_get_field_lemma : forall H k p Q,
  H ==> \exists kvs, (hrecord kvs p) \*
     match hfields_lookup k kvs with
     | None => \[False]
     | Some v => ((fun r => \[r = v] \* hrecord kvs p) \--* protect Q) end ->
  H ==> wp (val_get_field k p) Q.
Proof using.
  introv N. xchange N. intros kvs. cases (hfields_lookup k kvs).
  { rewrite wp_equiv. applys* triple_conseq_frame triple_get_field_hrecord.
    xsimpl. intros r ->. xchange (qwand_specialize v). rewrite* hwand_hpure_l. }
  { xpull. }
Qed.

Lemma xapp_set_field_lemma : forall H k p v Q,
  H ==> \exists kvs, (hrecord kvs p) \*
     match hfields_update k v kvs with
     | None => \[False]
     | Some kvs' => ((fun _ => hrecord kvs' p) \--* protect Q) end ->
  H ==> wp (val_set_field k p v) Q.
Proof using.
  introv N. xchange N. intros kvs. cases (hfields_update k v kvs).
  { rewrite wp_equiv. applys* triple_conseq_frame triple_set_field_hrecord.
    xsimpl. intros r. xchange (qwand_specialize r). }
  { xpull. }
Qed.

Ltac xapp_nosubst_for_records tt ::=
  first [ applys xapp_set_field_lemma; xsimpl; simpl; xapp_simpl
        | applys xapp_get_field_lemma; xsimpl; simpl; xapp_simpl ].


(* ####################################################### *)
(** ** Deallocation function for lists *)

(** Recall that our Separation Logic set up enforces that all allocated
    data eventually gets properly deallocated. In what follows, we describe
    a function for deallocating an entire mutable list. *)

Module ListDealloc.
Import SLFProgramSyntax RecordInit.

(** Recall the statement of [MList_if], which reformulates the
    definition of [MList] using a case analysis on [p = null]. *)

Lemma MList_if : forall (p:loc) (L:list val),
      (MList L p)
  ==> (If p = null
        then \[L = nil]
        else \exists x q L', \[L = x::L']
             \* (p ~~~> `{ head := x ; tail := q }) \* (MList L' q)).
Proof using.
  intros. destruct L as [|x L']; simpl.
  { xpull. intros M. case_if. xsimpl*. }
  { xpull. intros q. xchange hrecord_not_null. intros N.
    case_if. xsimpl*. }
Qed.

Opaque MList.

(** The operation [mfree_list] deallocates all the cells in a given list.
    It is implemented as a recursive function that invokes [mfree_cell]
    on every cell that it traverses.

[[
    let rec mfree_list p =
      if p != null then begin
        let q = p.tail in
        delete p;
        mfree_list q
      end
]]

*)

Definition mfree_list : val :=
  Fix 'f 'p :=
    Let 'b := ('p '<> null) in
    If_ 'b Then
      Let 'q := 'p'.tail in
      Delete 'p ';
      'f 'q
    End.

(** The precondition of [mfree_list p] requires a full list [p ~> MList L].
    The postcondition is empty: the entire list is destroyed. *)

(* EX2! (Triple_mfree_list) *)
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

End ListDealloc.




(*
(* ########################################################### *)




Parameter harray_eq_hrecord : forall p kvs,
  hrecord kvs p = \exists L, harray L p.


Lemma triple_dealloc_hrecord' : forall kvs p,
  triple (val_dealloc p)
    (hrecord kvs p)
    (fun _ => \[]).
Proof using.
  intros. xtriple. xchange harray_eq_hrecord. intros L.
  xapp triple_dealloc. xsimpl.
Qed.



Parameter harray_uninit_eq_hrecord : forall p (nb:nat),
  harray (LibList.make nb val_uninit) p =
  hrecord (LibList.map (fun k => (k,val_uninit)) (nat_seq 0 nb)) p.


Lemma triple_alloc_hrecord' : forall ks,
  ks = nat_seq 0 (LibListExec.length ks) ->
  triple (val_alloc_record ks)
    \[]
    (funloc p => hrecord (LibListExec.map (fun k => (k,val_uninit)) ks) p).
Proof using.
  introv E. xtriple. xapp triple_alloc_nat. intros p.
  xsimpl p. { auto. } rewrite E. rewrite length_nat_seq.
  rewrite LibListExec.map_eq. xchange harray_uninit_eq_hrecord.
Qed.


(*
Import LibListExec.RewListExec.

Hint Rewrite length_make make_zero make_succ : rew_listx.
 (* TODO: rewrite lemmas for nat_seq *)

Lemma hcells_uninit_eq_hfields : forall (i nb:nat) p,
  hcells (LibList.make nb val_uninit) (i+(p+1))%nat =
  hfields (LibList.map (fun k => (k,val_uninit)) (nat_seq i nb)) p.
Proof using.
  intros. gen i p. induction nb as [|nb']; intros; simpl nat_seq; rew_listx.
  { xsimpl. }
  { simpl. unfold hfield. math_rewrite (i+(p+1) = p+1+i)%nat. fequals.
    math_rewrite (S (p+1+i) = ((S i)+(p+1)))%nat. applys IHnb'. }
Qed.

Lemma harray_uninit_eq_hrecord : forall p (nb:nat),
  harray (LibList.make nb val_uninit) p =
  hrecord (LibList.map (fun k => (k,val_uninit)) (nat_seq 0 nb)) p.
Proof using.
  intros. unfold harray, hrecord.
  rew_list_exec. rew_listx. rewrite length_nat_seq. fequals.
  applys (@hcells_uninit_eq_hfields 0%nat).
Qed.


Qed.
*)



(* ########################################################### *)


Lemma triple_alloc_array : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (funloc p => \exists L, \[n = length L] \* harray L p).
Parameter triple_dealloc : forall L p,
  triple (val_dealloc p)
    (harray L p)
    (fun _ => \[]).





Lemma triple_set_field_hfields : forall kvs kvs' k p v,
  hfields_update k v kvs = Some kvs' ->
  triple (val_set_field k p v)
    (hfields kvs p)
    (fun _ => hfields kvs' p).
Proof using.
  intros kvs. induction kvs as [| [ki vi] kvs']; simpl; introv E.
  { inverts E. }
  { case_if.
    { inverts E. subst ki. applys triple_conseq_frame.
      { applys triple_set_field. } { xsimpl. } { xsimpl*. } }
    { cases (hfields_update k v kvs') as C2; tryfalse. inverts E.
      applys triple_conseq_frame. { applys IHkvs' C2. }
      { xsimpl. } { simpl. xsimpl*. } } }
Qed.


Lemma triple_get_field_hrecord : forall kvs p k v,
  hfields_lookup k kvs = Some v ->
  triple (val_get_field k p)
    (p ~~~> kvs)
    (fun r => \[r = v] \* p ~~~> kvs).
Proof using.
  introv M. unfold hrecord.
  applys* triple_conseq_frame triple_get_field_hfields; xsimpl*.
Qed.





(** There remains to explain how to reason about accesses to record
    fields when the fields are described using the predicate [hrecord].

    Recall the specification of the operation [val_get_field] for
    reading in a field standing by itself. *)

Lemma triple_get_field_hfields : forall kvs p k v,
  hfields_lookup k kvs = Some v ->
  triple (val_get_field k p)
    (hfields kvs p)
    (fun r => \[r = v] \* hfields kvs p).
Proof using.
  intros L. induction L as [| [ki vi] L']; simpl; introv E.
  { inverts E. }
  { case_if.
    { inverts E. subst ki. applys triple_conseq_frame.
      { applys triple_get_field. } { xsimpl. } { xsimpl*. } }
    { applys triple_conseq_frame. { applys IHL' E. } { xsimpl. } { xsimpl*. } } }
Qed.



Lemma length_hfields_update : forall kvs kvs' k v,
  hfields_update k v kvs = Some kvs' ->
  length kvs' = length kvs.
Proof using.
  intros kvs. induction kvs as [|[ki vi] kvs1]; simpl; introv E.
  { introv _ H. inverts H. }
  { case_if.
    { inverts E. rew_list*. }
    { cases (hfields_update k v kvs1).
      { inverts E. rew_list*. }
      { inverts E. } } }
Qed.





(* ####################################################### *)
(** ** Grouped representation of record fields *)

Module GroupedFields.
Export FieldAccesses.



(** The specification of the write operation [val_set_field k p v]
    describes an update of the state from [hrecord kvs p] to [hrecord kvs' p],
    where [kvs'] is the result of [hrecord_update k v kvs]. *)


Lemma triple_get_field_hrecord' : forall kvs p k v,
  triple (val_get_field k p)
    (p ~~~> kvs \* \[hfields_lookup k kvs = Some v])
    (fun r => \[r = v] \* p ~~~> kvs).
Admitted.

Lemma triple_set_field_hrecord : forall kvs kvs' k p v,
  hfields_update k v kvs = Some kvs' ->
  triple (val_set_field k p v)
    (p ~~~> kvs)
    (fun _ => p ~~~> kvs').
Proof using.
  introv M. unfold hrecord.
  applys* triple_conseq_frame triple_set_field_hfields; xsimpl*.
  rewrites* (>> length_hfields_update M).
Qed.



Lemma triple_alloc_mcell' :
  triple (val_alloc 2%nat)
    \[]
    (funloc p => p ~~~> `{ head := val_uninit ; tail := val_uninit }).
Proof using.
  xtriple. xapp triple_alloc_mcell. intros p.
  unfold hrecord, hfields. rew_list. simpl. xsimpl*.
Qed.

Opaque hfields.

End GroupedFields.





(** To prevent undesirable simplifications, we set the definition [hfield]
    to be opaque. Still, it is useful in places to be able to unfold the
    definition. To that end, we state a lemma for unfolding the definition.
    In its statement, we replace the addition [p+1+k] with the addition [k+S p],
    because the later simplifies better in Coq when [k] is a constant. *)

Lemma hfield_eq : forall p k v,
  hfield p k v = ((k+S p)%nat ~~> v \* \[p <> null]).
Proof using. intros. math_rewrite (k+S p = p+1+k)%nat. auto. Qed.

Global Opaque hfield.




Lemma triple_alloc : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (funloc p => harray (LibList.make (abs n) val_uninit) p).
Proof using.
  introv N. rewrite <- (@abs_nonneg n) at 1; [|auto].
  xtriple. xapp triple_alloc_nat. xsimpl*.
Qed.

(** The specification above turns out to be often unncessarily precise.
    For most applications, it is sufficient for the postcondition to
    describe the array as [harray L p] for some unspecified list [L]
    of length [n]. This weaker specification is stated and proved next. *)

Lemma triple_alloc_array : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (funloc p => \exists L, \[n = length L] \* harray L p).
Proof using.
  introv N. xtriple. xapp triple_alloc. { auto. }
  { xpull. intros p. unfold harray_uninit. xsimpl*.
    { rewrite length_make. rewrite* abs_nonneg. } }
Qed.

(* ########################################################### *)
(** ** Updated source language *)


    For example, applying [val_alloc] to the integer value [3] would return
    a pointer [p] together with the ownership of three cells: one at
    location [p], one at location [p+1], and one atlocation [p+2].

    This allocation model, which exposes pointer arithmetics, provides a way
    to model both records and arrays with minimal extension to the semantics
    of the programming language that we have considered sor far in the course.

    The cells allocated using [val_alloc] are assigned as contents a special
    value, named [val_uninit], to reflect for the fact that their contents has
    never been set. Remark: in OCaml, one must provide an initialization
    value explicitly, so there is no such thing as [val_uninit]; in JavaScript,
    [val_uninit] is called [undefined]; in Java, arrays are initialized with
    zeros; in C, uninitialized data should not be read---we could implement
    this policy in our language by restricting the evaluation rule for the read
    operation, adding a premise of the form [v <> val_uninit] to the rule.


(** The language is assumed to not include [val_ref] and [val_free],
    but instead include primitive [val_alloc] and [val_dealloc] for
    allocating blocks of cells.

    The grammar of values is extended with two constructors:

    - [val_uninit] describes the contents of an uninitialized cell.
    - [val_header k] describes the contents of a header block for an
      array or a record.

*)

Parameter val_uninit : val.
Parameter val_header : nat -> val.

Parameter val_uninit_neq_header :
  forall k, val_uninit <> val_header k.
(* Would be free if constructors were part of the inductive definition of [val] *)

(** New primitive operations:

    - [val_get_header p] to read a header, e.g., to get the length of an array,
    - [val_alloc k] to allocate a block of [k] consecutive cells,
    - [val_dealloc p] to deallocate the block at location [p].

*)

Parameter val_get_header : prim.
Parameter val_alloc : prim.
Parameter val_dealloc : prim.

(** Semantics of allocation, deallocation, and reading of headers *)

Parameter eval_alloc : forall k n ma mb p,
  mb = Fmap.conseq (val_header k :: LibList.make k val_uninit) p ->
  n = nat_to_Z k ->
  p <> null ->
  Fmap.disjoint ma mb ->
  eval ma (val_alloc (val_int n)) (mb \+ ma) (val_loc p).

Parameter eval_dealloc : forall k vs ma mb p,
  mb = Fmap.conseq (val_header k :: vs) p ->
  k = LibList.length vs ->
  Fmap.disjoint ma mb ->
  eval (mb \+ ma) (val_dealloc (val_loc p)) ma val_unit.

Parameter eval_get_header : forall s p k,
  Fmap.indom s p ->
  (val_header k) = Fmap.read s p ->
  eval s (val_get_header (val_loc p)) s (val_int k).

Arguments eval_alloc : clear implicits.



Definition hheader (k:nat) (p:loc) : hprop :=
  fun h => (h = Fmap.single p (val_header k)) /\ (p <> null).

Parameter harray_not_null : forall p L,
  harray L p ==> harray L p \* \[p <> null].



(*

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
    (funloc p => harray_uninit k p).

(** Like for other operations, this specification can be proved correct
    with respect to the semantics of the programming language.

    The allocation operation [val_alloc n] can be described as extending
    the state with a range of fresh consecutive cells. The corresponding
    evaluation rule appears below.

    In this rule, we write [LibList.make k val_uninit] for a list that
    repeats [k] times the value [val_uninit]. We write [Fmap.conseq L p]
    for a heap made of consecutive cells, starting at location [p], and
    whose contents are described by the elements from the list [L]. This
    heap is named [mb], and it extends the existing heap, which is named [ma]. *)

Parameter eval_alloc : forall k n ma mb p,
  mb = Fmap.conseq (LibList.make k val_uninit) p ->
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

Lemma hcells_intro : forall L p,
  p <> null ->
  hcells L p (Fmap.conseq L p).
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
  harray_uninit k p (Fmap.conseq (LibList.make k val_uninit) p).
Proof using.
  introv N. unfold harray_uninit, harray.
  rewrite hstar_comm. rewrite hstar_hpure. split.
  { auto. } { applys* hcells_intro. }
Qed.

(** Using the lemma above, we can prove the specification of [val_alloc].
    As usual, we first derive a Hoare logic statement, then the
    corresponding Separation Logic judgment. *)

Lemma hoare_alloc_nat : forall H k,
  hoare (val_alloc k)
    H
    (funloc p => harray_uninit k p \* H).
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
    (funloc p => harray_uninit k p).
Proof using.
  intros. intros H'. applys hoare_conseq.
  { applys hoare_alloc_nat H'. } { xsimpl. } { xsimpl*. }
Qed.

(** Similarly, we can formalize the behavior and the specification of
    the deallocation operation [val_dealloc n p].

    This time, the initial state is of the union of a heap [mb], describing
    the part to be deallocated, and a disjoint heap [ma], describing the
    part of the state that remains. The heap [mb] must correspond to [n]
    consecutive cells, starting at location [p]. This heap is described by
    [Fmap.conseq vs p], for a list of values [vs]. *)

Parameter eval_dealloc : forall n vs ma mb p,
  mb = Fmap.conseq vs p ->
  n = LibList.length vs ->
  Fmap.disjoint ma mb ->
  eval (Fmap.union mb ma) (val_dealloc (val_int n) (val_loc p)) ma val_unit.

(** To verify the specification of deallocation, the crux of the proof
    is to establish that if a heap satisfies [hcells L p], then this
    heap is described by [Fmap.conseq L p].

    This inversion lemma, reciprocal to [hcells_intro], is stated as
    follows. The proof is by induction on the list [L]. (It is not
    needed to follow throught the proof details.) *)

Lemma hcells_inv : forall p L h,
  hcells L p h ->
  h = Fmap.conseq L p.
Proof using.
  introv N. gen p h. induction L as [|x L']; simpl; intros.
  { applys hempty_inv N. }
  { lets (h1&h2&N1&N2&N3&->): hstar_inv N. fequal.
    { applys hsingle_inv N1. }
    { applys IHL' N2. } }
Qed.

(** Using this lemma, we can prove the specification of [val_dealloc],
    first for Hoare triples, then for Separation Logic triples. *)

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

(** It is then straightforward to derive the alternative specification
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
    valid location, i.e., [p+n] must be nonnegative. The evaluation rule
    for pointer addition is stated as follows. *)

Parameter eval_ptr_add : forall p1 p2 n s,
  (p2:int) = p1 + n ->
  eval s (val_ptr_add (val_loc p1) (val_int n)) s (val_loc p2).

(** The specification directly reformulates the evaluation rule. *)

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
(** ** Definition of record operations using pointer arithmetic *)

Module FieldOps.
Import SLFProgramSyntax.
Transparent hfield.

(** Most real-world programming languages include primitive operations
    for reading and writing in record cells. Yet, in our simple language,
    record cells can be accessed by means of pointer arithmetic. It is
    interesting to see how one may formally reason about this kind of
    encoding. *)

(** For example, the read operation on record fields can be implemented
    within our language, as the combination of a pointer addition and
    a read operation. More precisely, reading in [p`.f] using [val_get_field]
    is like reading in the cell at address [p+f] using [val_get], where [p+f]
    is computed by invoking [val_ptr_add p k]. *)

Definition val_get_field (k:field) : val :=
  Fun 'p :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_get 'q.

(** The specification of [val_get_field] can be proved with respect
    to the specifications of [val_ptr_add] and that of [val_get]. *)

Lemma triple_get_field : forall p k v,
  triple ((val_get_field k) p)
    (p`.k ~~> v)
    (fun r => \[r = v] \* (p`.k ~~> v)).
Proof using.
  xwp. xapp. unfold hfield. xpull. intros N. xapp. xsimpl*.
Qed.

(** A similar construction applies to the write operation on record
    fields. *)

Definition val_set_field (k:field) : val :=
  Fun 'p 'v :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_set 'q 'v.

Lemma triple_set_field : forall v1 p k v2,
  triple ((val_set_field k) p v2)
    (p`.k ~~> v1)
    (fun _ => p`.k ~~> v2).
Proof using.
  xwp. xapp. unfold hfield. xpull. intros N. xapp. xsimpl*.
Qed.

End FieldOps.


(* ########################################################### *)
(** ** Properties of the [hcells] and [harray] predicates *)

(** Before we describe the encoding of array operations using pointer
    arithmetic, we need to establish a few properties of the representation
    predicate [harray]. These properties describe the distribution of
    the predicate [harray L p] in the case where [L] is [nil], or is a
    [cons], or is a concatenation.

    Because [harray] is defined in terms of [hcells], we first state
    and prove the corresponding lemmas for [hcells]. *)

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
  { xchange hsingle_not_null. intros N1 N2. rewrite hcells_cons_eq. xsimpl*. }
Qed.

Lemma harray_concat_eq : forall p L1 L2,
  harray (L1++L2) p = (harray L1 p \* harray L2 (length L1 + p)%nat).
Proof using.
  intros. unfold harray, null, loc. rewrite hcells_concat_eq.
  applys himpl_antisym; xsimpl*. math.
Qed.



(* ########################################################### *)
(** ** Focus lemma *)

(** Another useful lemma

Parameter hcells_focus : forall k p L,
  k < length L ->
  hcells L p ==>
       ((p+k)%nat ~~> LibList.nth k L)
    \* (\forall w, ((p+k)%nat ~~> w) \-* hcells (LibList.update k w L) p).




(* ########################################################### *)
(** ** Definition of array operations using pointer arithmetic *)

Module ArrayOps.
Import SLFProgramSyntax.

(** As we show, array operations can be encoded using pointer arithmetic.
    For example, an array operation on the [i]-th cell of an array at
    location [p] can be implemented within our language, as the application
    of a read or write operation at the address [p+i].

    In order to reason about the read or write operation on a specific
    cell, we need to isolate this cell from the other cells of the array.
    Then, after the operation, we need to fold back to the view on the
    entire array.

    The isolation process is captured in a general way by the following
    "focus lemma". It reads as follows. Assume [harray L p] to initially
    describe the full array. Then, the [k]-th cell can be isolated as a
    predicate [(p+k) ~~> v], where [v] denotes the [k]-th item of [L],
    that is [LibList.nth k L].

    What remains of the heap can be described using the magic wand operator
    as [((p+k) ~~> v) \-* (harray L p)], which captures the idea that when
    providing back the cell at location [p+k], one would regain the
    ownership of the full array. *)

Parameter harray_focus_read : forall k p v L,
  k < length L ->
  v = LibList.nth k L ->
  harray L p ==>
       ((p+k)%nat ~~> v)
    \* ((p+k)%nat ~~> v \-* harray L p).

(** The above lemma works for read operations but falls short for a
    write operation, because it imposes the array to be put back in
    its original form. It does not take into account the possibility
    to fold back the array with a modified contents for the cell at [p+k].

    This observation leads us to generalize the magic wand that describes
    the rest of the array into the form:
    [\forall w, ((p+k)%nat ~~> w) \-* harray (LibList.update k w L) p].
    This predicate indicates that, for any new contents [w], the array can
    be folded back into [harray L' p], where [L'] denotes the update of
    the list [L] with [w] at location [k] (instead of [v]).

    Note that this form is strictly more general than the previous one,
    because [w] may be instantiated as [v] in case the array is unmodified.

    We state and prove the more general focus lemma as follows. *)

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

(** Using the focus lemma, we are able to verify the operations on
    arrays encoded using pointer arithmetic.

    In the proofs below, the following mathematical lemma is useful to
    verify that indices remain in the bounds. It is proved in [SLFExtra]. *)

Parameter abs_lt_inbound : forall i k,
  0 <= i < nat_to_Z k ->
  (abs i < k).

(** Consider the read operation in an array, written [val_array_get p i].
    We can define it as [val_get (val_ptr_add p i)], then prove its
    specification expressed in terms of [LibList.nth (abs i) L]. *)

Definition val_array_get : val :=
  Fun 'p 'i :=
    Let 'n := val_ptr_add 'p 'i in
    val_get 'n.

Lemma triple_array_get : forall p i L,
  0 <= i < length L ->
  triple (val_array_get p i)
    (harray L p)
    (fun r => \[r = LibList.nth (abs i) L] \* harray L p).
Proof using.
  introv N. xwp. xapp triple_ptr_add. { math. }
  xchange (@harray_focus (abs i) p L). { applys* abs_lt_inbound. }
  sets v: (LibList.nth (abs i) L).
  rewrite abs_nat_plus_nonneg; [|math].
  xapp triple_get. xchange (hforall_specialize v). subst v.
  rewrite update_nth_same. xsimpl*. { applys* abs_lt_inbound. }
Qed.

(** Consider now a write operation, written [val_array_set p i v].
    We can define it as [val_set (val_ptr_add p i) v], then prove its
    specification expressed in terms of [LibList.update (abs i) v L]. *)

Definition val_array_set : val :=
  Fun 'p 'i 'x :=
    Let 'n := val_ptr_add 'p 'i in
    val_set 'n 'x.

Lemma triple_array_set : forall p i v L,
  0 <= i < length L ->
  triple (val_array_set p i v)
    (harray L p)
    (fun _ => harray (LibList.update (abs i) v L) p).
Proof using.
  introv N. xwp. xapp triple_ptr_add. { math. }
  xchange (@harray_focus (abs i) p L). { applys* abs_lt_inbound. }
  rewrite abs_nat_plus_nonneg; [|math].
  xapp triple_set. xchange (hforall_specialize v).
Qed.

End ArrayOps.


*)
*)

Lemma hheader_not_null : forall p k,
  hheader k p ==> hheader k p \* \[p <> null].
Proof using.
  intros. intros h (N&M). rewrite hstar_comm, hstar_hpure.
  split~. split~.
Qed.

