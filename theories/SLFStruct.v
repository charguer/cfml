(**

Separation Logic Foundations

Chapter: "Struct".

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Import SLFExtra.

Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.
Implicit Type p : loc.
Implicit Type k : field.
Implicit Type v : val.


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

    This predicate can be defined by induction on the list [L], with the
    pointer being incremented by one unit at each cell, as follows.
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


(* ####################################################### *)
(** ** Specification of the allocation of consecutive cells *)

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

Parameter triple_alloc_nat : forall (k:nat),
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

Lemma triple_alloc : forall (n:int),
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

(** The deallocation operation [val_dealloc n p] deallocates [n] 
    consecutive cells starting from the location [p]. It admits the
    precondition [harray L p], where [L] can be any list of length [n],
    and its postcondition is empty.*)

Parameter triple_dealloc : forall (L:list val) (n:int) (p:loc),
  n = length L ->
  triple (val_dealloc n p)
    (harray L p)
    (fun _ => \[]).

(* TODO
Lemma triple_dealloc_hcells : forall (L:list val) (n:int) (p:loc),
  n = length L ->
  triple (val_dealloc n p)
    (hcells L p)
    (fun _ => \[]).
Admitted.
*)

(** Remark: in the C programming language, the argument [n] needs not be
    provided, because the system keeps track of the size of allocated blocks.
    One aspect that our simple semantics does not take into account is that
    in C one can invoke the deallocation function on pointers that were
    produced by the allocation function. We discuss further in this chapter
    a possible refinement of the specification to enforce this policy. *)


(* ########################################################### *)
(** ** Definition of record fields *)

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
    numbers.

    It is convenient in verification proofs to be able to assume that
    whenever we write [p`.k ~~> v], we refer to a location [p] that is
    not null. For an example, see the use of the lemma [hfield_not_null]
    inside the proof of the lemma [MList_if] in file [SLFBasic.v].

    To enable justifying this lemma [hfield_not_null], whose statement
    appears below, we bake in the definition of [p`.k ~~> v] the fact that
    [p] is not null, using the assertion [\[p <> null]].

    In the definition of [hfield] shown below, note that we write [k+p]
    instead of [p+k] to enable smoother simplications via the [simpl] tactic. *)

Definition field : Type := nat.

Definition hfield (p:loc) (k:field) (v:val) : hprop :=
  (k+p)%nat ~~> v \* \[p <> null].

Notation "p `. k '~~>' v" := (hfield p k v)
  (at level 32, k at level 0, no associativity,
   format "p `. k  '~~>'  v").

(** The lemma [hfield_not_null] asserts that the heap predicate [p`.k ~~> v]
    always ensures [p <> null]. *)

Lemma hfield_not_null : forall p k v,
  (p`.k ~~> v) ==> (p`.k ~~> v) \* \[p <> null].
Proof using. intros. unfold hfield. xsimpl*. Qed.

(** To prevent undesirable simplifications, we set the definition [hfield] 
    to be opaque, and we provide a lemma for unfolding its definition where
    necessary. *)

Lemma hfield_eq : forall l k v,
  hfield l k v = ((k+l)%nat ~~> v \* \[l <> null]).
Proof using. auto. Qed.

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

Lemma triple_dealloc_cell : forall (x:val) (p q:loc),
  triple (val_dealloc 2%nat p)
    ((p`.head ~~> x) \* (p`.tail ~~> q))
    (fun _ => \[]).
Proof using.
  xtriple. xchange (@hfield_not_null p). intros N. (* TODO @ *)
  xapp (@triple_dealloc 2%nat p (x::(val_loc q)::nil)). (* TODO *)  auto.
  xsimpl. unfold harray, hcells. do 2 rewrite hfield_eq. xsimpl. auto. 
Qed.
(* TODO: simplify *)


(* ########################################################### *)
(** ** Reading and writing in record fields *)

(** For reading and writing in record fields, we introduce the operations
    [val_get_field] and [val_set_field]. As we show further in this chapter,
    these functions can be defined in terms of the operations [val_get]
    and [val_set], if we assume available a pointer addition operation.
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

(** Consider the function [mcell x q], which allocates a fresh mutable
    list cell with [x] as head and [q] as tail.

[[
    let mcell x q =
      { head = x; tail = q }
]]

    In our programming language, the creation of such a record can
    encoded by allocating of a 2-cell record, and setting its two fields. *)

Import SLFProgramSyntax.

Definition mcell : val :=
  VFun 'x 'q :=
    Let 'p := val_alloc 2%nat in
    Set 'p'.head ':= 'x ';
    Set 'p'.tail ':= 'q ';
    'p.

(** The specification of [mcell x q] appears next. Its precondition is empty. 
    Its postcondition describes the two fields [p`.head ~~> x] and [p`.tail ~~> q]. *)

Lemma triple_mcell : forall (x:val) (q:loc),
  triple (mcell x q)
    \[]
    (fun r => \exists p, \[r = val_loc p] \* (p`.head ~~> x) \* (p`.tail ~~> q)).
Proof using.
  xwp. xapp triple_alloc_mcell. intros p. xapp. xapp. xval. xsimpl*.
Qed.


(* ####################################################### *)
(** ** Local reasoning on arrays *)

(** Consider the function [array_incr], which increments all the cells of
    an array of integer by one unit.

    An efficient, parallel version of this function can be implemented using
    a divide-and-conquer approach: if the array has length more than [1],
    then split in two parts and make a recursive call on each of the two parts.
    The two recursive calls can be safely executed in parallel, because they
    act over disjoint pieces of the array. Our programming language does not
    enable us to express this form of parallelism, yet it would be possible
    to do so using a simple extension based on the "fork-join" parallel construct.

[[
    let rec array_incr n p =
      if n = 1 then incr p
      else if n > 1 then 
        let m = n/2 in
        array_incr x m;
        array_incr x (n-m) (p+m)
]]

    Our concern here is to show how the description of an array can be split
    in two parts in the course of a recursive function. *)

(** The description of an array, that is, a set of consecutive cells, 
    can be split in two parts, at an arbitrary index. Concretely, if
    we have [harray (L1++L2) p], then we can separate the left part
    [harray L1 p] from the right part [harray L2 q], where the address
    [q] is equal to [p + length L1]. Reciprocally, the two parts can
    be merged back into the original form at any time. *)

Lemma hcells_concat_eq : forall p L1 L2,
  hcells (L1++L2) p = (hcells L1 p \* hcells L2 (length L1 + p)%nat).
Proof using.
  intros. gen p. induction L1; intros; rew_list; simpl.
  { xsimpl. } 
  { rewrite IHL1. math_rewrite (length L1 + S p = S (length L1 + p))%nat.
    xsimpl. } 
Qed.

Lemma harray_concat_eq : forall p L1 L2,
  harray (L1++L2) p = (harray L1 p \* harray L2 (length L1 + p)%nat).
Proof using.
  intros. unfold harray, null, loc. rewrite hcells_concat_eq. 
  applys himpl_antisym; xsimpl*. math.
Qed.

(** To deal with the base cases, the following two lemmas are helpul. *)

Lemma hcells_nil_eq : forall p,
  hcells nil p = \[].
Proof using. auto. Qed.

Lemma hcells_one_eq : forall p x,
  hcells (x::nil) p = (p ~~> x).
Proof using. intros. simpl. xsimpl*. Qed.

Lemma harray_nil_eq : forall p,
  harray nil p = \[p <> null].
Proof using. intros. unfold harray. rewrite hcells_nil_eq. xsimpl*. Qed.

Lemma harray_one_eq : forall p x,
  harray (x::nil) p = (p ~~> x).
Proof using.
  intros. unfold harray. rewrite hcells_one_eq. applys himpl_antisym.
  { xsimpl. } { xchanges hsingle_not_null. }
Qed.

(** Let us put this lemma to practice on our example program. *)

Import DemoPrograms.

Definition array_incr : val :=
  VFix 'f 'n 'p :=
    Let 'b1 := ('n '= 1) in
    If_ 'b1 Then incr 'p Else
    Let 'b2 := ('n '> 1) in
    If_ 'b2 Then
      Let 'm := 'n '/ 2 in
      Let 'n2 := ('n '- 'm) in
      Let 'p2 := (val_ptr_add 'p 'm) in
      'f 'm 'p ';
      'f 'n2 'p2
    End.

Definition vals_of_ints (L:list int) : list val :=
  LibList.map val_int L.

Lemma length_one_inv : forall A (L:list A),
  length L = 1%nat ->
  exists x, L = x::nil.
Proof using.
  introv N. destruct L as [|x [|]]; rew_list in *; tryfalse. eauto.
Qed.

Lemma length_zero_inv : forall A (L:list A),
  length L = 0%nat ->
  L = nil.
Proof using.
  introv N. destruct L as [|]; rew_list in *; tryfalse. eauto.
Qed.

Lemma range_split : forall n,
  n > 1 ->
  0 < Z.quot n 2 < n.
Admitted. (* TODO *)

Parameter triple_div : forall n1 n2 : int,
  triple (val_div n1 n2)
    \[n2 <> 0]
    (fun r => \[r = val_int (Z.quot n1 n2)]).

Hint Resolve triple_div : triple.

Definition harray_int (L:list int) (p:loc) : hprop :=
  harray (LibList.map val_int L) p.

Lemma harray_int_nil_eq : forall p,
  harray_int nil p = \[p <> null].
Proof using. intros. unfold harray_int. rew_listx. rewrite* harray_nil_eq. Qed.

Lemma harray_int_one_eq : forall p n,
  harray_int (n::nil) p = (p ~~> (val_int n)).
Proof using. intros. unfold harray_int. rew_listx. rewrite* harray_one_eq. Qed.

Lemma harray_int_concat_eq : forall p L1 L2,
  harray_int (L1++L2) p = (harray_int L1 p \* harray_int L2 (length L1 + p)%nat).
Proof using. intros. unfold harray_int. rew_listx. rewrite* harray_concat_eq. rew_listx*. Qed.

Import LibListZ.
Open Scope liblist_scope.
Lemma take_app_drop_spec_nonneg : forall A (n:int) (l:list A),
  0 <= n <= length l ->
  exists f r,
      l = f ++ r
   /\ length f = n
   /\ length r = length l - n.
Proof using. 
  introv M. exists (take n l) (drop n l).
  forwards* (R&_): take_app_drop_spec n l.
Qed.


Lemma triple_array_incr : forall (n:int) L p,
  n = LibListZ.length L ->
  triple (array_incr n p)
    (harray_int L p)
    (fun _ => harray_int (LibList.map (fun x => x + 1) L) p).
Proof using.
  intros n. induction_wf IH: (wf_downto 0) n.
  introv E. xwp. xapp. xif; intros C1.
  { forwards (x&Hx): length_one_inv L. math. (* TODO math *) subst.
    rewrite harray_int_one_eq. xapp. rewrite <- harray_one_eq. xsimpl. }
  { asserts C1': (n <> 1). { intros N. applys C1. fequals. } clear C1. (* TODO cleanup *)
    xapp. xif; intros C2.
    { forwards R: range_split n. { math. }
      xapp. { math. } sets m: (Z.quot n 2).
      xapp. xapp triple_ptr_add. { math. } 
      forwards (L1&L2&EL&LL1&LL2): take_app_drop_spec_nonneg m L. { math. }
      rewrite EL. rewrite harray_int_concat_eq.
      xapp (>> IH L1). { math. } { math. }
      rew_listx. asserts_rewrite (abs (p + m) = (LibList.length L1 + p)%nat).
      { apply eq_nat_of_eq_int. rewrite abs_nonneg; math. }
      xapp (>> IH L2). { math. } { math. }
      rewrite harray_int_concat_eq. rew_listx. xsimpl. }
    { asserts En: (n = 0). { math. }
      forwards HL: (length_zero_inv L). { math. }
      xval. subst. do 2 rewrite harray_int_nil_eq. xsimpl*. } }
Qed.

Lemma triple_array_incr' : forall (n:int) L p,
  n = LibListZ.length L ->
  triple (array_incr n p)
    (harray (vals_of_ints L) p)
    (fun _ => harray (vals_of_ints (LibList.map (fun x => x + 1) L)) p).
Proof using.
  intros n. induction_wf IH: (wf_downto 0) n.
  introv E. xwp. xapp. xif; intros C1.
  { forwards (x&Hx): length_one_inv L. math. (* TODO math *) subst.
    unfold vals_of_ints. rew_listx. rewrite harray_one_eq. xapp.
    rewrite <- harray_one_eq. xsimpl. }
  { asserts C1': (n <> 1). { intros N. applys C1. fequals. } clear C1. (* TODO cleanup *)
    xapp. xif; intros C2.
    { forwards R: range_split n. { math. }
      xapp. { math. } sets m: (Z.quot n 2).
      xapp. xapp triple_ptr_add. { math. } 
      forwards (L1&L2&EL&LL1&LL2): take_app_drop_spec_nonneg m L. { math. }
      rewrite EL. unfold vals_of_ints. rew_listx. rewrite harray_concat_eq.
      xapp (>> IH L1). { math. } { math. }
      rew_listx. asserts_rewrite (abs (p + m) = (LibList.length L1 + p)%nat).
      { apply eq_nat_of_eq_int. rewrite abs_nonneg; math. }
      xapp (>> IH L2). { math. } { math. }
      rewrite harray_concat_eq. rew_listx. unfold vals_of_ints. xsimpl. }
    { asserts En: (n = 0). { math. }
      forwards HL: (length_zero_inv L). { math. }
      xval. subst. unfold vals_of_ints; rew_listx. xsimpl. } }
Qed.



(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Additional contents *)




(*

(* ####################################################### *)
(** ** Not null information *)

Lemma harray_not_null : forall p L,
  L <> nil -> 
  harray L p ==> harray L p \* \[p <> null].
Proof using.
  introv N. destruct L as [|x L']; tryfalse. simpl.
  xchanges* hsingle_not_null.
Qed.

(* TODO *)
Lemma length_pos_inv_not_nil : forall A (l : list A),
  (length l > 0%nat) ->
  l <> nil.
Admitted.


Lemma hcells_not_null : forall p k,
  k > 0%nat -> 
  hcells k p ==> hcells k p \* \[p <> null].
Proof using.
  introv N. unfold hcells. xchanges* harray_not_null.
  applys length_pos_inv_not_nil. rewrite* length_make.
Qed.


(* ####################################################### *)
(** ** Proof of operation on list cells *)

(** *)

Fixpoint MList (L:list val) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists q, (p`.head ~~> x) \* (p`.tail ~~> q)
                     \* (MList L' q)
  end.

Lemma MList_nil : forall p,
  (p ~> MList nil) = \[p = null].
Proof using. auto. Qed.

Lemma MList_cons : forall p x L',
  p ~> MList (x::L') =
  \exists q, (p`.head ~~> x) \* (p`.tail ~~> q) \* MList L' q.
Proof using.  auto. Qed.


(** The function [mcons] is an alias for [mcell].

    Whereas [mcell] is intended to allocate a fresh cell on its own,
    [mcons] is intended to extend an existing list by appending to
    it a freshly-allocated cell. *)

Definition mcons : val := mcell.

(** The specification of [mcons] thus requires a list [q ~> MList L]
    in its precondition, and produces a list [p ~> MList (x::L)] in
    its postcondition. *)

Lemma Triple_mcons : forall (x:int) (q:loc) (L:list int),
  TRIPLE (mcons x q)
    PRE (q ~> MList L)
    POST (fun (p:loc) => p ~> MList (x::L)).
Proof using.
  intros. unfold mcons. xtriple. xapp Triple_mcell.
  intros p. xchange <- MList_cons. (* Fold back the list *)
Qed.

Hint Extern 1 (Register_Spec mcons) => Provide Triple_mcons.




(** The operation [mnil()] returns the [null] value.
    The intention is to produce a representation for the empty list.

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
    [p ~> MList nil]. *)

Lemma Triple_mnil :
  TRIPLE (mnil '())
    PRE \[]
    POST (fun (p:loc) => p ~> MList nil).
Proof using.
  (* The proof requires introducing [null ~> MList nil] from nothing. *)
  xwp. xval. xchange <- (MList_nil null). { auto. }
Qed.

Hint Extern 1 (Register_Spec mnil) => Provide Triple_mnil.

(** Observe that the specification [Triple_mnil] does not mention
    the [null] pointer anywhere. This specification can thus be
    used to specify the behavior of operations on mutable lists
    without having to reveal low-level implementation details. *)

(** Remark: in the proof of [Triple_mnil], the call to
    [xchange <- (MList_nil null)] can be replaced to a simpler
    tactic invokation: [xchange MList_nil_intro], where
    [MList_nil_intro] corresponds to the lemma stated next. *)

Lemma MList_nil_intro :
  \[] ==> (null ~> MList nil).
Proof using. intros. xchange <- (MList_nil null). auto. Qed.

Lemma Triple_mnil' :
  TRIPLE (mnil '())
    PRE \[]
    POST (fun (p:loc) => p ~> MList nil).
Proof using.
  xwp. xval. xchange MList_nil_intro.
Qed.



(* ########################################################### *)
(** ** List copy *)

(** Let's put to practice the function [mnil] and [mcons] for
    verifying the function [mcopy], which constructs an independent
    copy of a given linked list.

[[
    let rec mcopy p =
      if p == null
        then mnil ()
        else mcons (p.head) (mcopy p.tail)
]]
*)

Definition mcopy : val :=
  VFix 'f 'p :=
    If_ 'p  '= null
      Then mnil '()
      Else mcons ('p'.head) ('f ('p'.tail)).

(** The precondition of [mcopy] requires a linked list [p ~> MList L].
    Its postcondition asserts that the function returns a pointer [p']
    and a list [p' ~> MList L], in addition to the original list
    [p ~> MList L]. The two lists are totally disjoint and independent,
    as captured by the separating conjunction symbol (the star). *)

Lemma Triple_mcopy : forall (p:loc) (L:list int),
  TRIPLE (mcopy p)
    PRE (p ~> MList L)
    POST (fun (p':loc) => (p ~> MList L) \* (p' ~> MList L)).

(** The proof script is very similar in structure to the previous ones.
    While playing the script, try to spot the places where:

    - [mnil] produces an empty list of the form [p' ~> MList nil],
    - the recursive call produces a list of the form [q' ~> MList L'],
    - [mcons] produces a list of the form [p' ~> MList (x::L')]. *)

Proof using.
  intros. gen p. induction_wf IH: list_sub L.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros ->. xapp. xsimpl. xchange* <- (MList_nil p). }
  { intros x q L' ->. xapp. xapp. xapp*. intros q'.
    xapp. intros p'. xchange <- MList_cons. }
Qed.

Hint Extern 1 (Register_Spec mcopy) => Provide Triple_mcopy.

(* ########################################################### *)
(** ** Deallocation of a cell: [mfree_cell] *)

(** Separation Logic can be set up to enforce that all allocated data
    eventually gets properly deallocated. In what follows, we describe
    a function for deallocating one cell, and a function for deallocating
    an entire mutable list. *)

(** There is no explicit deallocation in OCaml, which is equipped with
    a garbage collector, but let's pretend that there is a [delete]
    operation for deallocating records.

[[
    let mfree_cell p =
      delete p
]]

    For technical reasons (because our source language is untyped and our
    formal semantics does not keep track of the size of allocated block),
    we require in our ad-hoc program syntax the delete operation to
    be annotated with the names of the fields of the record to be deleted,
    as shown below.
*)

(** The operation [mfree_list] deallocates all the cells in a given list.
    It can be implemented as the following tail-recursive function.

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
    If_ 'p '<> null Then
      Let 'q := 'p'.tail in
      mfree_cell 'p ';
      'f 'q
    End.

(** The precondition of [mfree_list p] requires a full list [p ~> MList L].
    The postcondition is empty: the entire list is destroyed. *)

(* EX1! (Triple_mfree_list) *)
(** Verify the function [mfree_list].
    Hint: follow the pattern of the proof of the function [mlength]. *)

Lemma Triple_mfree_list : forall (p:loc) (L: list int),
  TRIPLE (mfree_list p)
    PRE (p ~> MList L)
    POST (fun (r:unit) => \[]).
Proof using. (* ADMITTED *)
  intros. gen p. induction_wf IH: list_sub L. intros.
  xwp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros x p' L' ->. xapp. xapp. xapp. { auto. } xsimpl. }
  { intros ->. xval. xsimpl. }
Qed. (* /ADMITTED *)

(** [] *)

Hint Extern 1 (Register_Spec mfree_list) => Provide Triple_mfree_list.

(** This concludes our quick tour of functions on mutable lists.
    Additional functions are presented further in the file,
    as exercises. *)




(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Bonus contents (optional reading) *)



(* ########################################################### *)
(** ** Iterated star operation *)


(** The definition above can be recognized as an instance of an
    "indexed fold" operation, applied to the "Separation Logic
    commutative monoid" made of the star operator [\*] and its
    neutral element [\[]], and applied to the list [L].

    On paper, we would write the "big star" operator, with subscript
    "[x] at index [i] in [L]", applied to the expression [(p+i) ~~> x].

    In Coq, we can formalize this using a recursive function as follows. *)

Fixpoint hfoldi_list A (F:nat->A->hprop) (L:list A) (i:nat) : hprop :=
  match L with
  | nil => \[]
  | x::L' => (F i x) \* (hfoldi_list F L' (S i))
  end.

Definition harray (L:list val) (p:loc) : hprop :=
  hfoldi_list (fun q x => q ~~> x) L p.


(* TODO Remark: *)

Fixpoint list_foldi A B (F:nat->A->B->B) (L:list A) (i:nat) (b:B) : B :=
  match L with
  | nil => b
  | x::L' => F i x (list_foldi F L' (S i) b)
  end.

Definition harray'' (L:list val) (p:loc) : hprop :=
  list_foldi (fun q x acc => q ~~> x \* acc) L p \[].




(* ########################################################### *)
(** ** Semantics of the allocation operations *)


  | eval_alloc : forall k n ma mb l,
      mb = Fmap.conseq l (LibList.make k val_uninit) ->
      n = nat_to_Z k ->
      l <> null ->
      Fmap.disjoint ma mb ->
      eval ma (val_alloc (val_int n)) (mb \+ ma) (val_loc l)
  | eval_dealloc : forall n vs ma mb l,
      mb = Fmap.conseq l vs ->
      n = LibList.length vs ->
      Fmap.disjoint ma mb ->
      eval (mb \+ ma) (val_dealloc (val_int n) (val_loc l)) ma val_unit.


Lemma Alloc_fmap_conseq : forall l k,
  l <> null ->
  (Alloc k l) (Fmap.conseq l (LibList.make k val_uninit)).
Proof using.
  Transparent loc null.
  introv N. gen l. induction k; intros; rew_Alloc.
  { rewrite LibList.make_zero, Fmap.conseq_nil. applys~ hempty_intro. }
  { rewrite LibList.make_succ, Fmap.conseq_cons. applys hstar_intro.
    { split~. }
    { applys IHk. unfolds loc, null. math. }
    { applys~ Fmap.disjoint_single_conseq. } }
Qed.

Lemma triple_alloc : forall (k:nat),
  triple (val_alloc k)
    \[]
    (fun r => \exists l, \[r = val_loc l /\ l <> null] \* hcells k l).
Proof using.
  intros. applys triple_of_hoare. intros HF.
  esplit; split. { applys~ hoare_alloc. } { xsimpl*. }
Qed.

Lemma triple_alloc : forall n,
  n >= 0 ->
  triple (val_alloc n)
    \[]
    (fun r => \exists l, \[r = val_loc l /\ l <> null] \* Alloc (abs n) l).
Proof using.
  intros. applys triple_of_hoare. intros HF.
  esplit; split. { applys~ hoare_alloc. } { xsimpl*. }
Qed.

Lemma triple_dealloc : forall n l,
  n >= 0 ->
  triple (val_dealloc n l)
    (Dealloc (abs n) l)
    (fun r => \[r = val_unit]).
Proof using.
  intros. applys triple_of_hoare. intros HF.
  esplit; split. { applys~ hoare_dealloc. } { xsimpl*. }
Qed.



(* ########################################################### *)
(** ** Definition of record operations using pointer arithmetics *)

Definition val_get_field (k:field) : val :=
  VFun 'p :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_get 'q.

Definition val_set_field (k:field) : val :=
  VFun 'p 'v :=
    Let 'q := val_ptr_add 'p (nat_to_Z k) in
    val_set 'q 'v.

End FieldAccessDef.


Lemma triple_get_field : forall l f v,
  triple ((val_get_field f) l)
    (l`.f ~~> v)
    (fun r => \[r = v] \* (l`.f ~~> v)).
Proof using.
  xwp. xapp. unfold hfield. xpull. intros N. xapp. xsimpl*.
Qed.

Lemma triple_set_field : forall v1 l f v2,
  triple ((val_set_field f) l v2)
    (l`.f ~~> v1)
    (fun _ => l`.f ~~> v2).
Proof using.
  xwp. xapp. unfold hfield. xpull. intros N. xapp. xsimpl*.
Qed.


(* ########################################################### *)
(** ** Definition of array operations using pointer arithmetics *)


(* -------------------------------------------------------------------------- *)
(** Accesses *)

Import LibListZ.
Implicit Types i ofs len : int.


(* ---------------------------------------------------------------------- *)
(** Array get *)

Definition val_array_get : val :=
  ValFun 'p 'i :=
    Let 'n := val_ptr_add 'p 'i in
    val_get 'n.

Lemma triple_array_get : forall p i L,
  index L i ->
  triple (val_array_get p i)
    (Array L p)
    (fun r => \[r = L[i]] \* Array L p).
Proof using.
  introv N. rewrite index_eq_inbound in N.
  xcf. xapps. { math. }
  rewrites (>> Array_middle_eq i). { math. }
  xtpull ;=> L1 x L2 EL HL.
  xapp. xpull ;=> r. intro_subst.
  xsimpl; auto. { subst. rewrite~ read_middle. }
Qed.

Hint Extern 1 (Register_spec val_array_get) => Provide triple_array_get.

Notation "'Array'' p `[ i ]" := (trm_app (trm_app (trm_val val_array_get) p) i)
  (at level 69, p at level 0, no associativity,
   format "'Array''  p `[ i ]") : charac.


(* ---------------------------------------------------------------------- *)
(** Array set *)

Definition val_array_set : val :=
  ValFun 'p 'i 'x :=
    Let 'n := val_ptr_add 'p 'i in
    val_set 'n 'x.

Lemma triple_array_set : forall p i v L,
  index L i ->
  triple (val_array_set p i v)
    (Array L p)
    (fun r => \[r = val_unit] \* Array (L[i:=v]) p).
Proof using.
  introv N. rewrite index_eq_inbound in N.
  xcf. xapps. { math. }
  rewrites (>> Array_middle_eq i). { math. }
  xtpull ;=> L1 x L2 EL HL.
  xapp triple_set. xpull ;=> r. intro_subst.
  rewrites (>> Array_middle_eq i (L[i := v])).
   { rewrite <- length_eq in *. rew_array. math. }
  xsimpl; auto. { subst. rewrite~ update_middle. rew_list~. }
Qed.

Hint Extern 1 (Register_spec val_array_set) => Provide triple_array_set.

Notation "'Array'' p `[ i ] `<- x" := (trm_app (trm_app (trm_app (trm_val val_array_set) p) i) x)
  (at level 69, p at level 0, no associativity,
   format "'Array''  p `[ i ]  `<-  x") : charac.


(* ---------------------------------------------------------------------- *)
(** Array make *)

Definition val_array_make : val :=
  ValFun 'n 'v :=
    Let 'p := val_alloc 'n in
    Let 'b := 'n '- 1 in
    For 'i := 0 To 'b Do
      Array' 'p`['i] `<- 'v
    Done;;;
    'p.

(* ####################################################### *)
(** ** Grouped representation of record fields *)


(** Representation predicate [r ~> Record L], where [L]
    is an association list from fields to values. *)

Definition Record_field : Type := field * dyn.
Definition Record_fields : Type := list Record_field.

Bind Scope fields_scope with Record_fields.

Fixpoint Record (L:Record_fields) (r:loc) : hprop :=
  match L with
  | nil => \[]
  | (f, Dyn V)::L' => (r`.f ~~> V) \* (r ~> Record L')
  end.

(* --TODO: currently restricted due to [r `. f ~> V] not ensuring [r<>null] *)
(* --TODO: rename *)
Lemma hRecord_not_null : forall (r:loc) (L:Record_fields),
  (* L <> nil -> *)
  mem (0%nat:field) (List.map fst L) ->
  (r ~> Record L) ==> (r ~> Record L) \* \[r <> null].
Proof using.
  introv M. induction L as [|(f,[A EA v]) L'].
  { inverts M. }
  { xunfold Record. inverts M.
    { xchange~ (Hfield_not_null r). xsimpl~. }
    { xchange~ IHL'. xsimpl~. } }
Qed.

(** Lemmas for unfolding the definition *)

Lemma Record_nil : forall p,
  p ~> Record nil = \[].
Proof using. auto. Qed.

Lemma Record_cons : forall p x (V:dyn) L,
  (p ~> Record ((x, V)::L)) =
  (p`.x ~~> ``V \* p ~> Record L).
Proof using. intros. destruct~ V. Qed.

Hint Rewrite Record_nil Record_cons enc_dyn_make : Record_to_HField.


Local Open Scope heap_scope_ext.

Lemma Record_not_null : forall (r:loc) (L:Record_fields),
  L <> nil ->
  (r ~> Record L) ==+> \[r <> null].
Proof using.
  intros. destruct L as [|(f,v) L']. { false. }
  rewrite Record_cons. xchanges~ Hfield_not_null.
Qed.



(* ####################################################### *)
(** ** Treatment of uncurried functions *)

  | trm_fixs : var -> list var -> trm -> trm
  | trm_apps : trm -> list trm -> trm


Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
  let aux t :=
    subst y w t in
  let aux_no_captures xs t :=
    If LibList.mem y xs then t else aux t in
  match t with
  | trm_fixs f xs t1 => trm_fixs f xs (If f = y then t1 else
                                        aux_no_captures xs t1)
  | trm_apps t0 ts => trm_apps (aux t0) (List.map aux ts)
  ...
 end.


Lemma subst_trm_fixs : forall y w f xs t,
  var_fresh y (f::xs) ->
  subst1 y w (trm_fixs f xs t) = trm_fixs f xs (subst1 y w t).
Proof using.
  introv N. simpls. case_var.
  { false* var_fresh_mem_inv. }
  { auto. }
Qed.


  | eval_fixs : forall m f xs t1,
      xs <> nil ->
      eval m (trm_fixs f xs t1) m (val_fixs f xs t1)

  | eval_apps_fixs : forall m1 m2 f xs t3 v0 vs r,
      v0 = val_fixs f xs t3 ->
      var_fixs f (length vs) xs ->
      eval m1 (substn xs vs (subst1 f v0 t3)) m2 r ->
      eval m1 (trm_apps v0 vs) m2 r


Fixpoint var_distinct (xs:vars) : Prop :=
  match xs with
  | nil => True
  | x::xs' => var_fresh x xs' /\ var_distinct xs'
  end.

Fixpoint var_fresh (y:var) (xs:vars) : bool :=
  match xs with
  | nil => true
  | x::xs' => if var_eq x y then false else var_fresh y xs'
  end.


(** [noduplicates L] asserts that [L] does not contain any
    duplicated item. *)

Inductive noduplicates A : list A -> Prop :=
  | noduplicates_nil : noduplicates nil
  | noduplicates_cons : forall x l,
      ~ (mem x l) ->
      noduplicates l ->
      noduplicates (x::l).



Definition var_fixs (f:var) (n:nat) (xs:vars) : Prop :=
     var_distinct (f::xs)
  /\ length xs = n
  /\ xs <> nil.

Definition var_fixs_exec (f:bind) (n:nat) (xs:vars) : bool := ..

Lemma var_fixs_exec_eq : forall f (n:nat) xs,
  var_fixs_exec f n xs = isTrue (var_fixs f n xs).


Lemma triple_apps_fixs : forall xs (f:var) F (Vs:vals) t1 H Q,
  F = (val_fixs f xs t1) ->
  var_fixs f (length Vs) xs ->
  triple (substn (f::xs) (F::Vs) t1) H Q ->
  triple (trm_apps F Vs) H Q.
Proof using.
  introv E N M. intros H' h Hf. forwards (h'&v&R&K): (rm M) Hf.
  exists h' v. splits~. { subst. applys* eval_apps_fixs. }
Qed.


Fixpoint trms_to_vals_rec (acc:vals) (ts:trms) : option vals :=
  match ts with
  | nil => Some (List.rev acc)
  | trm_val v :: ts' => trms_to_vals_rec (v::acc) ts'
  | _ => None
  end.

Definition trms_to_vals (ts:trms) : option vals :=
  trms_to_vals_rec nil ts.


Lemma xwp_lemma_fixs : forall F f vs ts xs t H Q,
  F = val_fixs f xs t ->
  trms_to_vals ts = Some vs ->
  var_fixs_exec f (length vs) xs ->
  H ==> (wpgen (combine (f::xs) (F::vs)) t) Q ->
  triple (trm_apps F ts) H Q.


(* ####################################################### *)
(** ** Coercion for uncurried functions *)

Coercion trm_to_pat : trm >-> pat.

(** Parsing facility: coercions for turning [t1 t2 t3]
    into [trm_apps t1 (t2::t3::nil)] *)

Inductive combiner :=
  | combiner_nil : trm -> trm -> combiner
  | combiner_cons : combiner -> trm -> combiner.

Coercion combiner_nil : trm >-> Funclass.
Coercion combiner_cons : combiner >-> Funclass.

Fixpoint combiner_to_trm (c:combiner) : trm :=
  match c with
  | combiner_nil t1 t2 => trm_apps t1 (t2::nil)
  | combiner_cons c1 t2 =>
      match combiner_to_trm c1 with
      | trm_apps t1 ts => trm_apps t1 (List.app ts (t2::nil))
      | t1 => trm_apps t1 (t2::nil)
      end
  end.

Coercion combiner_to_trm : combiner >-> trm.



=========

Fixpoint Alloc (k:nat) (l:loc) : hprop :=
  match k with
  | O => \[]
  | S k' => l ~~~> val_uninit \* (Alloc k' (S l)%nat)
  end.

Lemma Alloc_zero_eq : forall l,
  Alloc O l = \[].
Proof using. auto. Qed.

Lemma Alloc_succ_eq : forall l k,
  Alloc (S k) l = l ~~~> val_uninit \* Alloc k (S l)%nat.
Proof using. auto. Qed.

Global Opaque Alloc.

Hint Rewrite Alloc_zero_eq Alloc_succ_eq : rew_Alloc.

Tactic Notation "rew_Alloc" :=
  autorewrite with rew_Alloc.



Lemma harray_of_hcells : forall (k:nat) (p:loc),
  hcells k l ==>
  \exists (L:list val), \[k = length L] \* harray L p.
Proof using. auto. Qed.

(* ####################################################### *)
(** ** Semantics of the allocation of consecutive cells *)

(** The operation [val_alloc n] allocates [n] consecutive cells, where
    [n] is a nonnegative integer. Let [p] denote the pointer returned.
    The allocated cells have addresses in the range from [p] inclusive
    to [p+n] exclusive.

    To formally describe this range of locations, let [k] denote the
    natural number (of type [nat]) that corresponds to the nonnegative
    integer [n].

    The list [nat_seq k p] describes the list of locations from [p]
    inclusive to [p+k] exclusive. The definition is recursive on [k].
    Recall that [O] denotes zero and [S] denotes the successor on [nat]. *)

Fixpoint nat_seq (k:nat) (p:nat) : nat :=
  match k with
  | O => []
  | S k' => p :: (nat_seq k' (S p))
  end.

(** Assume the special value [val_uninit] to be part of the
    grammar of values, i.e., to be a constructor from the type [val].

    Let us now define a heap predicate [hcells k p] that describes
    the ownership of [k] consecutive cells, starting from location [p],
    and whose contents is [val_uninit]. The definition is,
    again, recursive on [k]. *)

Fixpoint hcells' (k:nat) (p:loc) : hprop :=
  match k with
  | O => \[]
  | S k' => (p ~~> val_uninit) \* (hcells k' (S p))
  end.

(** The definition above can be recognized as an instance of a "fold"
    pattern, applied to the "Separation Logic commutative monoid" made
    of the star operator [\*] and its neutral element [\[]], and
    applied to the list of locations [seq k p].

    Indeed, if we let [F] denote [fun q => q ~~> val_uninit]
    and let [L] denote [seq k p], then [hcells' k p] is equivalent to
    [hfold_list' F L], for the function [hfold_list'] defined below. *)

Fixpoint hfold_list' A (F:A->hprop) (L:list A) : hprop :=
  match L with
  | [] => \[]
  | x::L' => (F x) \* (hfold_list' F L')
  end.

(** The above function happens to be a particular instance of
    [List.fold_right]. Thus, rather than defining [hfold_list] as a
    recursive function, let us reuse the fold operation on lists. *)

Definition hfold_list A (F:A->hprop) (L:list A) : hprop :=
  LibList.fold_right (fun acc x => F x \* acc) \[] L.

(** Using [hfold_list], the heap predicate [hcells k p] that describes
    a set of [k] consecutive cells with uninitialized contents,
    starting at location [p]. *)

Definition hcells (k:nat) (p:loc) : hprop :=
  hfold_list (fun q => q ~~> val_uninit) (seq k p).

(** Remark: the function [hfold_list] provides a general "fold of the
    separation logic monoid over a list of values" that will prove useful
    later on also for other purposes. *)

(** Consider the function [count], which counts the number of occurences
    of a integer [x] in an array of [n] integers, at location [p].

    An efficient, parallel version of this function can be implemented using
    a divide-and-conquer approach: if the array has length more than [1],
    then split in two parts, make a recursive call on each part, then sum up
    the results. The two recursive calls can be safely executed in parallel,
    
     *)

[[
    let rec count x n p =
      if n = 0 then 0 else
      if n = 1 then (if !p = x then 1 else 0)
      else 
        let m = n/2 in
        count x m + count x (n-m) (p+m)
]]

*)



*)

