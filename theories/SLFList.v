(**

Separation Logic Foundations

Chapter: "List".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import Example.
Generalizable Variables A B.

Implicit Types x n m : int.
Implicit Types p q : loc.
Implicit Types L : list int.

(** Tweak to make the Separation Logic appear linear instead of affine. *)
Ltac xwp_xtriple_handle_gc ::= xwp_xtriple_remove_gc.

(** Tweak for record allocation to expose fields individually instead of grouped. *)
Ltac xnew_post ::= xnew_post_exploded.



(* ####################################################### *)
(** * The chapter in a rush,
      nested with exercises as additional contents *)

(** The previous chapter has introduced the notation for specification
    triples, the entailements relation, and the grammar for heap predicates,
    with: [p ~~> n] and [\[]] and [\[P]] and [H1 \* H2] and [\exists x, H].

    The proofs are carried out using CFML "x-tactics", including:
    [xwp] and [xapp] and [xval] and [xsimpl], and with help of TLC tactics
    [math] for mathematical goals, and [induction_wf] and [gen] for inductions.

    The present chapter focuses on the specification and verification
    in Separation Logic of linked lists. Specifically, we consider a
    representation of lists where each cell consists of a two-cell record,
    storing a head value and a tail pointer, the empty list being represented
    by the null value.

    To avoid unnecessary complications with polymorphism, we restrict ourselves
    throughout the chapter to mutable lists that store integer values.

    This chapter presents:

    - a simple technique for representing mutable records such as list cells.
    - the definition of the "representation predicate" [p ~> MList L] which
      describes a (null-terminated) mutable list, whose elements are those
      from the Coq list [L].
    - examples of specifications and proofs for programs manipulating mutable lists,
    - how to use specify and verify an implementation of imperative stacks
      implemented as a reference on a linked list, using a representation predicate
      of the form [q ~> Stack L]
    - how Separation Logic supports reasoning about deallocation.

    This chapter exploits a few additional tactics:
    - [xunfold], a CFML tactic for unfolding the definition of [MList],
    - [xchange], a CFML tactic to transform the precondition by exploiting
      entailments or equalities,
    - [rew_listx], a TLC tactic to normalize list expressions, e.g.,
      [(x::L1)++L2] or [length (x::L)] or [map f (x::L)] or [filter f (x::L)].

*)


(* ******************************************************* *)
(** *** Representation of a list cell as a two-field record *)

(** In the previous chapter, we have only manipulated OCaml-style
    references, which correspond to a mutable record with a single
    field, storing the contents of the reference.

    A two-field record can be described in Separation Logic as the
    separating conjunction of two cells at consecutive addresses.

    A list cell allocated at address [p], featuring a head value [x]
    and a tail pointer [q], can be represented as:
    [(p+0) ~~> x \* (p+1) ~~> q].

    Throughout this file, to improve clarity, we write:

    - [p`.head] as short for [p+0], where we intend to describe the
      address of the head field;
    - [p`.tail] as short for [p+1], where we intend to describe the
      address of the tail field.

    Using these notation, the list cell considered can be represented as:
    [p`.head ~~> x  \*  p`.tail ~~> q], which looks more symmetric.
*)

Definition head : field := 0%nat.
Definition tail : field := 1%nat.


(* ******************************************************* *)
(** *** Representation of a mutable list *)

(** Our goal is to define a custom heap predicate, written
    [MList L p] or, more conveniently [p ~> MList L], to
    describe a mutable linked lists, that is, a set of list cells with
    each one pointing to the next until reaching a null tail pointer.

    The simple arrow [p ~> R] is just a generic notation for [R p]
    that increases readability and helps [xsimpl] spotting items
    that should be identified when simplifying entailments. *)

(** If [p ~> MList L] could be defined as an inductive predicate,
    its definition would consists of the following two rules:

[[

  -----------------
  null ~> MList nil

  p`.head ~~> x   \*   p`.tail ~~> q    \*   q ~> MList L'
  --------------------------------------------------------
                       p ~> MList (x::L')

]]

    - The [null] pointer represents the empty list, that is, [L = nil].
    - A non-null pointer [p] represents a list [L] of the form [n::L'],
      if the head field of [p] contains [n] and the tail field of [p]
      contains some pointer [q] that is the head of a linked list
      that represents the list [L'].

    For reasons that we won't detail here, the definition of the predicate
    [p ~> MList L] cannot take the form of an inductive predicate in Coq.
    Fortunately, it can very well be defined as a recursive function.

    A tentative definition would thus be the following, which defines
    [MList L p], that is [p ~> MList L], by case analysis on the
    condition [p = null] (using a classical-logic test [If P then X else Y]
    where [P] is a proposition of type [Prop]).

[[
    Fixpoint MList (L:list int) (p:loc) : hprop :=
      If p = null
        then \[L = nil]
        else \exists x q L', \[L = x::L']
             \* (p`.head ~~> x) \* (p`.tail ~~> q) \* (MList L' q).
]]

    Yet, this definition is rejected by Coq, which does not recorgnize the
    structural recursion, even though the recursive call is made to a list [L']
    which is a strict sublist of the argument [L]. *)

(** To circumvent the problem, we present the definition of [MList] using a
    pattern matching on the structure of the list [L]. The logic is as follows:

    - if [L] is [nil], then [p] should be [null]
    - if [L] decomposes as [n::L'], then the head field of [p] should store
      the value [n], the tail field of [p] should store some pointer [q]
      (which is existentially quantified), and [q ~> MList L'] should
      describe the remaining of the list structure.
*)

Fixpoint MList (L:list int) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists q, (p`.head ~~> x) \* (p`.tail ~~> q) \* (q ~> MList L')
  end.

(** Above, observe the existential quantification of the tail pointer [q]. *)


(* ******************************************************* *)
(** *** Basic properties of the mutable list predicate *)

(** To begin with, we prove two lemmas that will be helpful for manipulating
    the definition. *)

Lemma MList_nil : forall p,
  (p ~> MList nil) = \[p = null].
Proof using. xunfold MList. auto. Qed.

Lemma MList_cons : forall p x L',
  p ~> MList (x::L') =
  \exists q, (p`.head ~~> x) \* (p`.tail ~~> q) \* q ~> MList L'.
Proof using. xunfold MList. auto. Qed.

(** We then set [MList] as opaque to ensure that the [simpl] tactic never
    attempts to unfold the definition in an uncontrolled manner. *)

Global Opaque MList.

(** At this stage, we can prove that the definition of [MList] that performs
    a pattern matching on [L] is equivalent to a characterization of [MList]
    based on testing test condition [p = null]. *)

Lemma MList_if : forall (p:loc) (L:list int),
  p ~> MList L ==>
  If p = null
    then \[L = nil]
    else \exists x q L', \[L = x::L']
         \* (p`.head ~~> x) \* (p`.tail ~~> q) \* (q ~> MList L').
Proof using.
  (* Let's prove this by case analysis on [L]. *)
  intros. destruct L as [|x L'].
  { (* case [L = nil]. By definition of [MList], we have [p = null]. *)
    xchange MList_nil. intros M.
    (* we have to justify [L = nil], which is trivial. *)
    case_if. xsimpl. auto. }
  { (* case [L = x::L']. *)
    xchange MList_cons. intros q. case_if.
    { (* case [p = null]. Contradiction because nothing can be allocated at
         the null location, as captured by lemma [Hfield_not_null]. *)
      subst. xchange Hfield_not_null. }
    { (* case [p <> null]. The 'else' branch corresponds to the definition
         of [MList] in the [cons] case, it suffices to instantiate the existentials. *)
      xsimpl. auto. } }
Qed.

(** The lemma [MList_if] stated above will prove to be very handy for
    reasoning about list-manipulating programs, whose code generally
    begins by testing whether the list pointers are null. *)


(* ******************************************************* *)
(** *** Function [mhead] *)

(** Consider first the function [mhead p], which expects a pointer [p]
    on a nonempty mutable list and returns the value of the head element.

[[
    let rec mhead p =
      p.head
]]
*)

Definition mhead : val :=
  VFun 'p :=
    'p'.head.

(** One way to capture in the specification that the list should be
    nonempty is to state a precondition of the form [p ~> MList (x::L)].
    With such a precondition, the postcondition asserts that the
    result of reading the head value yields exactly the value [x]. *)

Lemma Triple_mhead : forall (p:loc) (x:int) (L:list int),
  TRIPLE (mhead p)
    PRE (p ~> MList (x::L))
    POST (fun (r:int) => \[r = x] \* (p ~> MList (x::L))).
Proof using.
  xwp.
  (* In order to read in [p.head], we must make visible in the current
     state the head field, that is [p`.head ~~> x]. We achieve this by
     unfolding the definition of [MList], using lemma [MList_cons]. *)
  (* One possibility is to perform a rewrite operation using [MList_cons]
     on its first occurence. Then using CFML the tactic [xpull] to extract
     the existential quantifiers out from the precondition:
[[
  rewrite MList_cons at 1. xpull. intros q.
]]
  *)
  (* A more efficient approach is to use the dedicated CFML tactic [xchange],
     which is specialized for performing updates in the current state. *)
  xchange MList_cons. intros q.
  (* Here, the name [q] introduced comes from the existentially quantified
     variable [q] in the definition of [MList]. *)
  (* At this stage, we are ready to read the value [x] in the head field. *)
  xapp.
  (* To conclude, there remains to fold back the definition of [MList].
     This task is achieved by means of the [xchange <-] tactic, which
     exploits the equality [MList_cons] backwards. *)
  xchange <- MList_cons.
  (* There remains to check that the final state matches the postcondition. *)
  xsimpl. auto.
Qed.

Hint Extern 1 (Register_Spec mhead) => Provide Triple_mhead.

(** An alternative statement for the specification of [mhead] features a
    precondition of the form [p ~> MList L], accompanied with a pure
    side-condition asserting that the list is nonempty, that is, [L <> nil].

    In that specification, the postcondition asserts that the result value
    [x] is the head of the list [L]. This can be written
    [\[exists L', L = x::L']], or equivalently, [\exists L', \[L = x::L']].
*)

Lemma Triple_mhead_notnil : forall (p:loc) (L:list int),
  L <> nil ->
  TRIPLE (mhead p)
    PRE (p ~> MList L)
    POST (fun (x:int) => \exists L', \[L = x::L'] \* (p ~> MList L)).
Proof using.
  introv HL.
  (* By case analysis on [L], we eliminiate the case [L = nil]. *)
  destruct L as [|x L']. { contradiction. }
  (* Then, the proof script is the same as in the previous lemma.
     Rather than copy-pasting it, we can invoke [Triple_mhead]. *)
  xapp. xsimpl. eauto.
Qed.


(* ******************************************************* *)
(** *** Function [mtail] *)

(** Second, consider the function [mtail], which returns the pointer on the
    tail of a mutable list. As we are going to see, it is quite interesting
    from a Separation Logic perspective.

[[
    let rec mtail p =
      p.tail
]]
*)

Definition mtail : val :=
  VFun 'p :=
   'p'.tail.

(** In a context [p ~> MList (x::L)], a call to [mtail p] returns
    a pointer [q] to a mutable list such that [q ~> MList L].
    However, it would be incorrect to pretend that both
    [p ~> MList (x::L)] and [q ~> MList L] coexist, because the
    two heap predicates describe overlapping pieces of memory.

    The following lemma is thus incorrect. If we play the same script
    as for [Triple_mhead], we end up stuck. *)

Lemma Triple_mtail_incorrect : forall (p:loc) (x:int) (L:list int),
  TRIPLE (mtail p)
    PRE (p ~> MList (x::L))
    POST (fun (q:loc) => (p ~> MList (x::L)) \* (q ~> MList L)).
Proof using.
  xwp. xchange MList_cons. intros q. xapp.
  (* With [xchange <- MList_cons. xsimpl.]
     we can satisfy [p ~> MList (x::L)] but not [q ~> MList L]. *)
  (* With [xsimpl.]
     we can satisfy [q ~> MList L] but not [p ~> MList (x::L)]. *)
Abort.

(** As suggested by the execution of the above proof script, a valid
    postcondition for [mtail] is:
    [p`.tail ~~> q \* p`.head ~~> x \* q ~> MList L]. *)

Lemma Triple_mtail : forall (p:loc) (x:int) (L:list int),
  TRIPLE (mtail p)
    PRE (p ~> MList (x::L))
    POST (fun (q:loc) => (p`.head ~~> x) \* (p`.tail ~~> q) \* (q ~> MList L)).
Proof using.
  xwp. xchange MList_cons. intros q. xapp. xsimpl.
Qed.

Hint Extern 1 (Register_Spec mtail) => Provide Triple_mtail.

(** Again, an equivalent specification can be stated with a precondition
    of the form [p ~> MList L] accompanied with [L <> nil]. In that case,
    the variables [x] and [L'] such that [L = x::L'] are existentially
    quantified in the postcondition. *)

Lemma Triple_mtail_notnil : forall (p:loc) (L:list int),
  L <> nil ->
  TRIPLE (mtail p)
    PRE (p ~> MList L)
    POST (fun (q:loc) => \exists x L', \[L = x::L']
             \* (p`.head ~~> x) \* (p`.tail ~~> q) \* (q ~> MList L')).
Proof using.
  introv HL. destruct L as [|x L']. { contradiction. }
  xapp. xsimpl. eauto. (* invoking the specification [Triple_mtail]. *)
Qed.

(** In fact, the minimal specification of [mtail] is one that only
    mentions the field [p.head] both in the precondition and the
    postcondition. *)

Lemma Triple_mtail_minimal : forall (p:loc) (q:loc),
  TRIPLE (mtail p)
    PRE (p`.tail ~~> q)
    POST (fun (r:loc) => \[r = q] \* (p`.tail ~~> q)).
Proof using.
  xwp. xapp. xsimpl. eauto.
Qed.


(* ******************************************************* *)
(** *** Length of a mutable list *)

(** The function [mlength] computes the length of a linked list
    by recursively traversing through its cells.

[[
    let rec mlength p =
      if p == null
        then 0
        else 1 + mlength (tail p)
]]
*)

Definition mlength : val :=
  VFix 'f 'p :=
    If_ 'p '= ``null
      Then 0
      Else 1 '+ 'f ('p'.tail).

(** The precondition of [mlength p] requires the description of the
    linked list that it traverses, that is, [p ~> MList L].
    The postcondition asserts that the result is equal to [length L],
    and that the list predicate [p ~> MList L] is returned unmodified. *)

Lemma Triple_mlength : forall (p:loc) (L:list int),
  TRIPLE (mlength p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).

(** The proof goes by induction on the length of the list [L].
    Each time the code traverses a cell, this cell is isolated
    from the tail of the list. The recursive call is applied to
    the tail, then the original list is restored. *)

Proof using.
  (* We use the tactic [induction_wf] like in the previous chapter,
     but this time instantiated with the [list_sub] relation,
     which provides an induction hypothesis for the tail of the current list.
     More precisely, the induction hypothesis asserts that the specification
     holds for the list [L'] when [L'] is the tail of [L].
     Technically [list_sub L' L] is inductive defined with a single
     constructor [list_sub L' (x::L')]. *)
  intros. gen p. induction_wf IH: list_sub L. intros.
  (* Once the induction is set up, we are ready to verify the code. *)
  xwp. xapp.
  (* The critical step is to reformulate [MList] using lemma [MList_if]
     so as to make the case analysis on the condition [p = null] visible. *)
  xchange MList_if.
  (* The [xif] tactics performs the case analysis on the condition [p = null]
     that occurs in the code, while the [case_if] tactic performs the case analysis
     on the (similar) condition [p = null] that occurs in the precondition
     (the condition that was just introduced by [MList_if]. *)
  xif; intros C; case_if; xpull.
  { (* Case [p = null]. *)
    intros ->. xval. xchange <- (MList_nil p). { auto. }
    (* Justify that [length nil = 0] *)
    xsimpl. rew_listx. math. }
  { (* Case [p <> null]. *)
     intros x q L' ->. xapp.
     (* Recursive call, exploit [IH] applied to the sublist [q ~> MList L'].
        Observe that, during this call, the head cell described by
        [p`.tail ~~> q \* p`.head ~~> x] remain unchanged---the two fields
        fields are said to be "framed", in the Separation Logic jargon. *)
     xapp.
     (* Justify that [L'] is a sublist of [x::L']. *)
     { auto. }
     (* Add one unit to the result of the recursive call. *)
     xapp.
     (* Fold back the list into [p ~> MList(x::L')] *)
     xchange <- MList_cons.
     (* Justify that [length (x::L') = 1 + length L'] *)
     xsimpl. rew_listx. math. }
Qed.

(** Same proof, more concisely. *)

Lemma Triple_mlength_concise : forall (p:loc) (L:list int),
  TRIPLE (mlength p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  intros. gen p. induction_wf IH: list_sub L. intros.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros ->. xval. xchanges* <- MList_nil. }
  { intros x q L' ->. xapp. xapp*. xapp. xchanges* <- MList_cons. }
Qed.

Hint Extern 1 (Register_Spec mlength) => Provide Triple_mlength.


(* ******************************************************* *)
(** *** Exercise: increment through a mutable list *)

(** The function [mlist_incr] expects a linked list of integers
    and updates the list in place by augmenting every item
    in the list by one unit.

[[
    let rec mlist_incr p =
      if p != null then begin
        p.head <- p.head + 1;
        mlist_incr p.tail
      end
]]
*)

Definition mlist_incr : val :=
  VFix 'f 'p :=
    If_ 'p '<> null Then (
      Set 'p'.head ':= 'p'.head '+ 1 ';
      'f ('p'.tail)
    ) End.

(** The precondition of [mlist_incr] requires a linked list [p ~> MList L].
    The postcondition asserts that the updated list takes the form [p ~> MList L2],
    where [L2 = LibList.map (fun x => x+1) L], that is, the result of mapping
    the successor function onto every item from [L].  *)

Lemma Triple_mlist_incr : forall (p:loc) (L:list int),
  TRIPLE (mlist_incr p)
    PRE (p ~> MList L)
    POST (fun (r:unit) => p ~> MList (LibList.map (fun x => x+1) L)).

(* EX2! (Triple_mlist_incr) *)
(** Prove [Triple_mlist_incr], following the pattern of [Triple_mlength].
    Hint: it need, you can use the tactic [rew_listx] to rewrite using
    [LibList.map_nil] and [LibList.map_cons], e.g., for normalizing
    [LibList.map f (x::l)] into [f x :: LibList.map f l]. *)

Proof using.
  (* SOLUTION *)
  intros. gen p. induction_wf IH: list_sub L.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros x p' L' ->. xapp. xapp. xapp. xapp. xapp. { auto. }
    xchange <- MList_cons. }
  { intros ->. xval. xchange <- (MList_nil p). { auto. } }
  (* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** *** Allocation of a new cell: [mcell] and [mcons] *)

(** Next, we consider functions for constructing mutable lists.
    We begin with the function that allocates one cell.
    The function [mcell] takes as arguments the values to be
    stored in the head and the tail fields of the new cell.

[[
    let rec mcell x q =
      { head = x; tail = q }
]]

    In the embedded language, the [New] construct denotes record allocation.
*)

Definition mcell : val :=
  VFun 'x 'q :=
    New`{ head := 'x ; tail := 'q }.

(** The precondition of [mcell x q] is empty. The postcondition
    asserts that the return value is a location [p] such that
    two fields are allocated: [p`.head ~~> x] and [p`.tail ~~> q]. *)

Lemma Triple_mcell : forall (x:int) (q:loc),
  TRIPLE (mcell x q)
    PRE \[]
    POST (fun (p:loc) => (p`.head ~~> x) \* (p`.tail ~~> q)).
Proof using.
  (* The tactic [xapp] handles the reasoning on the [New] construct. *)
  xwp. xapp. xsimpl.
Qed.

Hint Extern 1 (Register_Spec mcell) => Provide Triple_mcell.

(** The function [mcons] is an alias for [mcell].
    Whereas [mcell] is intended to allocate a fresh cell on its own,
    [mcons] is intended to extend an existing list by appending
    to it a fresh cell. *)

Definition mcons : val := mcell.

(** The specification of [mcons] thus requires a list [q ~> MList L]
    in the precondition, and produces a list [p ~> MList (x::L)] in
    the postcondition. *)

Lemma Triple_mcons : forall (x:int) (q:loc) (L:list int),
  TRIPLE (mcons x q)
    PRE (q ~> MList L)
    POST (fun (p:loc) => p ~> MList (x::L)).
Proof using.
  intros. unfold mcons. xapp. (* invoke [Triple_mcell] *)
  intros p. xchange <- MList_cons. (* fold back the list *)
Qed.

Hint Extern 1 (Register_Spec mcons) => Provide Triple_mcons.


(* ******************************************************* *)
(** *** Function [mnil] *)

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

(** The precondition of [mnil] is empty. The postcondition of [mnil]
    asserts that the return value [p] is a pointer such that
    [p ~> MList nil]. Note that, although the postcondition implies
    that [p = null], there is no explicit mention of [null] in the
    specification---implementation details are not revealed. *)

Lemma Triple_mnil :
  TRIPLE (mnil '())
    PRE \[]
    POST (fun (p:loc) => p ~> MList nil).
Proof using.
  (* The proof requires introducing [null ~> MList nil] from nothing. *)
  xwp. xval. xchange <- (MList_nil null). { auto. }
Qed.

Hint Extern 1 (Register_Spec mnil) => Provide Triple_mnil.


(** Remark: the call to [xchange <- (MList_nil null)] can here
    be replaced by [rewrite MList_nil] or, even better, by a call
    to [xchange] on a specific lemma capturing the entailement
    [\[] ==> (null ~> MList nil)], as demonstrated next. *)

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


(* ******************************************************* *)
(** *** List copy *)

(** Let's put to practice the function [mnil] and [mcons] for
    verifying a function that constructs an independent copy
    of a given linked list.

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
  { intros ->. xapp. xsimpl. xchanges* <- MList_nil. }
  { intros x q L' ->. xapp. xapp. xapp*. intros q'.
    xapp. intros p'. xchanges <- MList_cons. }
Qed.

Hint Extern 1 (Register_Spec mcopy) => Provide Triple_mcopy.

(** This concludes our quick tour of functions on mutable lists.
    Additional functions are presented further in the file:
    [append], and [filter_nonneg]. *)


(* ******************************************************* *)
(** *** Deallocation of a cell: [mfree_cell] *)

(** Separation Logic can be set up to enforce that all allocated data
    eventually gets properly deallocated. In what follows, we describe
    a function for deallocating one cell, and a function for deallocating
    an entire mutable list. *)

(** There is no explicit deallocation in OCaml, which is equipped with
    a garbage collector, but let's pretend that there is such a
    [delete] operation.

    For technical reasons (because our source language is untyped and our
    formal semantics does not keep track of the size of allocated block),
    we require the delete operation to be annotated the names of the fields
    of the record to be deleted. Assuming [delete] to exist, we would write:

[[
    let mfree_cell p =
      delete (p: {head:_; tail:_})
]]

    In the embedded language, the [Delete] construct denotes record
    deallocation.
*)

Definition mfree_cell : val :=
  VFun 'p :=
    Delete`{ head; tail } 'p.

(** The precondition of [mfree_cell p] describes the two fields
    associated with the cell: [p`.head ~~> x] and [p`.tail ~~> q].
    The postcondition is empty: the fields are destroyed. *)

Lemma Triple_mfree_cell : forall (x:int) (p q:loc),
  TRIPLE (mfree_cell p)
    PRE ((p`.head ~~> x) \* (p`.tail ~~> q))
    POST (fun (r:unit) => \[]).
Proof using.
  (* The tactic [xapp] handles the reasoning on the [Delete] construct. *)
  xwp. xapp. xsimpl.
Qed.

Hint Extern 1 (Register_Spec mfree_cell) => Provide Triple_mfree_cell.


(* ******************************************************* *)
(** *** Exercise: deallocation of a list: [mfree_list] *)

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
Proof using.
  (* SOLUTION *)
  intros. gen p. induction_wf IH: list_sub L. intros.
  xwp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros x p' L' ->. xapp. xapp. xapp. { auto. } xsimpl. }
  { intros ->. xval. xsimpl. }
  (* /SOLUTION *)
Qed.

Hint Extern 1 (Register_Spec mfree_list) => Provide Triple_mfree_list.


(* ******************************************************* *)
(** *** Representation of a mutable stack *)

(** We now move on to using linked lists for implementing stacks.
    Thereafter, a stack is represented as a reference on a linked
    list.

    We first introduce the heap predicate [q ~> Stack L] to describe
    stacks. For example, the empty stack is represented as a reference
    whose contents is null, that is, [q ~~> null], while a nonempty
    stack is represented as a reference whose contents is a pointer
    on a proper linked list, that is, [(q ~~> p) \* (p ~> MList L)]
    for some pointer [p].

    The definition of [q ~> Stack L], that is [Stack L q], is thus
    as follows. *)

Definition Stack (L:list int) (q:loc) : hprop :=
  \exists p, (q ~~> p) \* (p ~> MList L).

(** The following lemma reformulates the definition of [Stack]
    as an equality. The tactic [xchange Stack_eq] is handy to
    unfold the definition of [Stack], while the tactic
    [xchange <- Stack_eq] performs the reciprocal operation of
    folding back the definition. *)

Lemma Stack_eq : forall (q:loc) (L:list int),
  (q ~> Stack L) = (\exists p, (q ~~> p) \* (p ~> MList L)).
Proof using. xunfold* Stack. Qed.


(* ******************************************************* *)
(** *** Operation [create] *)

(** The operation [create ()] allocates an empty stack.
[[
    let create () =
      ref (mnil())
]]
*)

Definition create : val :=
  VFun 'u :=
    'ref (mnil '()).

(** The precondition of [create] is empty. Its postcondition asserts
    that the result value is a pointer [q] such that [q ~> Stack nil],
    i.e. a pointer onto the representation of an empty stack. *)

Lemma Triple_create :
  TRIPLE (create '())
    PRE \[]
    POST (fun (q:loc) => q ~> Stack nil).
Proof using.
  xwp.
  (* [mnil()] creates an empty linked list: [p ~> MList nil]. *)
  xapp. intros p.
  (* [ref p] allocates a reference with contents [q]: i.e, [q ~~> p]. *)
  xapp. intros q.
  (* Folding the definition of [Stack] gives [p ~> Stack nil]. *)
  xchange <- Stack_eq.
Qed.

Hint Extern 1 (Register_Spec create) => Provide Triple_create.


(* ******************************************************* *)
(** *** Operation [push] *)

(** The operation [push q x] modifies the stack [q] in place by
    inserting the element [x] at the top of the stack.
[[
    let push q x =
      q := mcons x !q
]]
*)

Definition push : val :=
  VFun 'q 'x :=
    'q ':= mcons 'x ('!'q).

(** The precondition of [push] requires a stack [q ~> Stack L].
    The postcondition describes the updated stack as [q ~> Stack (x::L)]. *)

Lemma Triple_push : forall (q:loc) (x:int) (L:list int),
  TRIPLE (push q x)
    PRE (q ~> Stack L)
    POST (fun (r:unit) => q ~> Stack (x::L)).
Proof using.
  xwp.
  (* The first step is to unfold the definition of [Stack].
     It is necessary to reveal the reference [q ~~> p] that
     the code manipulates. *)
  xchange Stack_eq. intros p.
  (* The read operation [!q] returns the value [p]. *)
  xapp.
  (* The operation [mcons x p] allocates a list cell with head field [x]
     and tail field [q], and packs this cell together with [p ~> MList L]
     to form [p' ~> MList (x::L)], where [p'] denotes the result of [mcons x p]. *)
  xapp. intros p'.
  (* The operation [q := p'] updates the reference implementing the queue. *)
  xapp.
  (* The new state [q ~~> p' \* p' ~> MList (x::L')] can be folded into a [Stack]. *)
  xchange <- Stack_eq.
Qed.

(* Note: shorter version for the last line: [xchanges <- Stack_eq]. *)

Hint Extern 1 (Register_Spec push) => Provide Triple_push.


(* ******************************************************* *)
(** *** Operation [is_empty] *)

(** The operation [is_empty p] returns a boolean value indicating
    whether the stack is empty.
[[
    let is_empty q =
      !q == null
]]
*)

Definition is_empty : val :=
  VFun 'q :=
    '!'q '= null.

Lemma Triple_is_empty : forall (q:loc) (L:list int),
  TRIPLE (is_empty q)
    PRE (q ~> Stack L)
    POST (fun (b:bool) => \[b = isTrue (L = nil)] \* q ~> Stack L).

(** A naive attempt at the proof leaves a final proof obligation
    [p = null <-> L = nil] with absolutely no hypothesis to prove it. *)

Proof using.
  xwp. xchange Stack_eq. intros p. xapp. xapp. xchange <- Stack_eq. xsimpl.
Abort.

(** What is needed here is a lemma asserting that whenever [p ~> MList L]
    is valid, it is the case that [p = null <-> L = nil]. This result
    is captured by the following entailment, which can be used by [xchange]. *)

Lemma MList_null_iff_nil : forall (p:loc) (L:list int),
  p ~> MList L ==> p ~> MList L \* \[p = null <-> L = nil].
Proof using.
  intros. xchange MList_if. case_if.
  { xpull. intros HL. xchanges* <- (MList_nil p). }
  { xpull. intros x q L' HL'. xchanges* <- MList_cons. }
Qed.

(** Equipped with this lemma, let's revisit the verification proof of [is_empty]. *)

Lemma Triple_is_empty : forall (q:loc) (L:list int),
  TRIPLE (is_empty q)
    PRE (q ~> Stack L)
    POST (fun (b:bool) => \[b = isTrue (L = nil)] \* q ~> Stack L).

(** A naive attempt at the proof leaves a final proof obligation
    [p = null <-> L = nil] with absolutely no hypothesis to prove it. *)

Proof using.
  xwp. xchange Stack_eq. intros p.
  (* At this stage, from [p ~> MList L] we extract the equivalence
     [p = null <-> L = nil]. *)
  xchange MList_null_iff_nil. intros Hp.
  (* Then we continue the proof as before *)
  xapp. xapp. xchange <- Stack_eq. xsimpl.
  (* Finally, we can conclude using the extracted equivalence. *)
  auto.
Qed.


(* ******************************************************* *)
(** *** Operation [pop] *)

(** The operation [pop p] applies to a nonempty stack.
    It returns the element at the top of the stack,
    and removes it from the stack.
[[
    let pop q =
      let p = !q in
      let x = mhead p in
      q := mtail p;
      x
]]
*)

Definition pop : val :=
  VFun 'q :=
    Let 'p := '!'q in
    Let 'x := mhead 'p in
    'q ':= mtail 'p ';
    mfree_cell 'p ';
    'x.

(** Again, there are two ways to specify a nonempty stack:
    either using [q ~> Stack (x::L)], or using [q ~> Stack L]
    with [L <> nil]. In practice, the second presentation turns
    out to be almost always preferable. Indeed, a typical
    programming idiom is:
[[
   while not (Stack.is_empty q) do
      let x = Stack.pop q in
      ...
   done
]]
    where the operation [is_empty] is testing whether [L = nil]
    or [L <> nil]. Thus, at the entrance of the loop body, the
    information available is [L <> nil], which is thus a natural
    precondition for [Stack.pop].

    For this reason, we formulate the specification of [pop]
    as follows. *)

Lemma Triple_pop : forall (q:loc) (L:list int),
  L <> nil ->
  TRIPLE (pop q)
    PRE (q ~> Stack L)
    POST (fun (x:int) => \exists L', \[L = x::L'] \* q ~> Stack L').
Proof using.
  introv HL. destruct L as [|x L']; [contradiction|].
  xwp. xchange Stack_eq. intros p. xapp. xapp.
  xapp. intros p'. xapp. xapp. xval.
  xchange <- Stack_eq. xsimpl. auto.
Qed.

Hint Extern 1 (Register_Spec pop) => Provide Triple_pop.

(** This concludes our investigation of the representation in
    Separation Logic of a mutable stack. Additional functions
    are presented further in this file: [clear], [concat],
    and [push_back]. *)


(* ####################################################### *)
(** * Additional contents *)


(* ******************************************************* *)
(** *** Exercise: out-of-place append of two mutable lists *)

(** The operation [mappend_copy p1 p2] assumes two independent lists
    at location [p1] and [p2], and constructs a third, independent list
    whose items are the concatenation of those from the two input lists.

[[
    let rec mappend_copy p1 p2 =
      if p1 == null then mcopy p2 else begin
        let p = mappend_copy p1.tail p2 in
        mcons p1.head p
      end
]]
*)

Definition mappend_copy : val :=
  VFix 'f 'p1 'p2 :=
    If_ 'p1 '= null Then mcopy 'p2 Else (
      Let 'p := 'f ('p1'.tail) 'p2 in
      mcons ('p1'.head) 'p
    ).

(* EX3! (Triple_mappend_copy) *)
(** Specify and verify the function [mappend_copy].
    Hint: perform the induction on the list [L1] after generalizing [p1],
    and use [xchange (MList_if p1)] to unfold the list predicate for [p1]. *)

(* SOLUTION *)
Lemma Triple_mappend_copy : forall (p1 p2:loc) (L1 L2:list int),
  TRIPLE (mappend_copy p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (p:loc) => p ~> MList (L1++L2)
                      \* p1 ~> MList L1 \* p2 ~> MList L2).
Proof using.
  intros. gen p1. induction_wf IH: list_sub L1.
  xwp. xapp. xchange (MList_if p1). xif; intros C; case_if; xpull.
  { intros ->. xapp. xsimpl. xchanges* <- MList_nil. }
  { intros x q L' ->. xapp. xapp. { auto. } intros q'.
    xapp. xapp. intros p'. xchanges <- MList_cons. }
Qed.
(* /SOLUTION *)


(* ******************************************************* *)
(** *** Exercise: out-of-place filter on list *)

(** The function [copy_nonneg] expects a list of integers,
    and produces an independent copy of that list from which
    the zero values have been filetered out.

[[
    let rec mcopy_nonneg p =
      if p == null then
        mnil ()
      else begin
        let x = p.head in
        let q2 = mcopy_nonneg p.tail in
        if x = 0 then q2 else mcons x q2
      end
]]
*)

Definition mcopy_nonneg : val :=
  VFix 'f 'p :=
    If_ 'p '= null Then mnil '() Else (
      Let 'x := 'p'.head in
      Let 'q2 := 'f ('p'.tail) in
      If_ 'x '= 0 Then 'q2 Else (mcons 'x 'q2)
    ).

(* EX3! (Triple_mcopy_nonneg) *)
(** Specify and verify the function [mcopy_nonneg],
    using [LibList.filter (<> 0) L] to describe the resulting list.

    The tactic [rew_listx] simplifies expressions involving [filter].
    It invokes the lemmas [LibList.filter_nil] and [LibList.filter_cons]
    for simplifying [filter f nil] and [filter f (x::L)]. *)

(* SOLUTION *)
Lemma Triple_mcopy_nonneg : forall (p:loc) (L:list int),
  TRIPLE (mcopy_nonneg p)
    PRE (p ~> MList L)
    POST (fun (p2:loc) => p ~> MList L \* p2 ~> MList (LibList.filter (<> 0) L)).
Proof using.
  intros. gen p. induction_wf IH: list_sub L. intros.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros ->. xapp. xsimpl. xchanges* <- MList_nil. }
  { intros x q L' ->. xapp. xapp. xapp. { auto. } intros q'.
    xchange <- MList_cons. xapp.
    rew_listx. xif; intros Cx; case_if as Cx'.
    { xval. xsimpl. }
    { xapp. intros p2. xsimpl. } }
Qed.
(* /SOLUTION *)


(* ******************************************************* *)
(** *** Exercise: length of a mutable list using a reference *)

(** The operation [mlength_acc p] computes the length of a list [p]
    by traversing the cells of the list and incrementing a reference
    by one unit at each step. If the reference cell is initialized
    with zero, then at the end of the traversal, it contains the
    length of the list.

[[
    let rec mlength_acc_rec a p =
      if p <> null then
        incr a;
        mlength_acc_rec a (tail p)
      end

   let mlength_acc p =
      let a = ref 0 in
      mlength_acc_rec a p;
      let n = !a in
      free a;
      n
]]
*)

Definition mlength_acc_rec : val :=
  VFix 'f 'a 'p :=
    If_ 'p '<> ``null Then
      incr 'a ';
      'f 'a ('p'.tail)
   End.

Definition mlength_acc : val :=
  VFun 'p :=
    Let 'a := 'ref 0 in
    mlength_acc_rec 'a 'p ';
    Let 'n := '! 'a in
    'free 'a ';
    'n.

(* EX3? (Triple_mlength_acc_rec) *)
(** Specify and verify the function [mlength_acc_rec].
    Hint: make sure to generalize the relevant variables in the script
    pattern [gen ????. induction_wf IH: list_sub L.], so that your
    induction principle is strong enough to complete the proof. *)
(* SOLUTION *)
Lemma Triple_mlength_acc_rec : forall (a:loc) (n:int) (p:loc) (L:list int),
  TRIPLE (mlength_acc_rec a p)
    PRE (a ~~> n \* p ~> MList L)
    POST (fun (r:unit) => a ~~> (n + length L) \* p ~> MList L).
Proof using.
  intros. gen n p. induction_wf IH: list_sub L.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros x q L' ->. xapp. xapp. xapp. { auto. }
     xchange <- MList_cons. xsimpl. rew_listx. math. }
  { intros ->. xval. xchange <- (MList_nil p). { auto. }
    xsimpl. rew_listx. math.  }
Qed.
(* /SOLUTION *)

Hint Extern 1 (Register_Spec mlength_acc_rec) => Provide Triple_mlength_acc_rec.

(** Make sure to include the following command to enable reasoning
    about the call to [mrev_append] from the proof of [mrev].
[[
  Hint Extern 1 (Register_Spec mlength_acc_rec) => Provide Triple_mlength_acc_rec.
]]
*)

(* INSTRUCTORS *)

(** Remark: the proof script of [Triple_mlength_acc_rec] revisited with
    some automation. *)
Lemma Triple_mlength_acc_ind' : forall (a:loc) (n:int) (p:loc) (L:list int),
  TRIPLE (mlength_acc_rec a p)
    PRE (a ~~> n \* p ~> MList L)
    POST (fun (r:unit) => a ~~> (n + length L) \* p ~> MList L).
Proof using.
  intros. gen n p. induction_wf IH: list_sub L.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros x q L' ->. xapp. xapp. xapp*. xchanges* <- MList_cons. }
  { intros ->. xval. xchanges* <- (MList_nil p). }
Qed.

(* /INSTRUCTORS *)

(* EX2? (Triple_mlength_acc) *)
(** Prove that [mlength_acc] satisfies the same specification as [mlength]. *)

Lemma Triple_mlength_acc : forall (p:loc) (L:list int),
  TRIPLE (mlength_acc p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
(* SOLUTION *)
  xwp. xapp. intros a. xapp. xapp. xapp. xval. xsimpl. math.
(* /SOLUTION *)
Qed.

(* ******************************************************* *)
(** *** Exercise: operation [delete] on stack *)

(** The function [delete] deallocates a stack and its contents.
    The linked list is deallocated using the function [mfree_list].
    The reference cell is deallocated using a primitive function
    called [free], which does not exist in OCaml, but we assume here
    to be the deallocation function associated with the allocation
    function [ref].

[[
    let delete q =
      mfree_list !q;
      free q
]]
*)

Definition delete : val :=
  VFun 'q :=
    mfree_list ('!'q) ';
    'free 'q.

(* EX1! (Triple_delete) *)
(** Specify and verify the function [delete]. *)

(* SOLUTION *)
Lemma Triple_delete : forall (q:loc) (L:list int),
  TRIPLE (delete q)
    PRE (q ~> Stack L)
    POST (fun (r:unit) => \[]).
Proof using.
  xwp. xchange Stack_eq. intros p. xapp. xapp. xapp. xsimpl.
Qed.
(* /SOLUTION *)


(* ******************************************************* *)
(** *** Exercise: operation [clear] on stack *)

(** The function [clear] removes all elements from a mutable stack.

[[
    let clear q =
      mfree_list !q;
      q := mnil()
]]
*)

Definition clear : val :=
  VFun 'q :=
    mfree_list ('!'q) ';
    'q ':= mnil '().

(* EX2! (Triple_clear) *)
(** Specify and verify the function [clear]. *)

(* SOLUTION *)
Lemma Triple_clear : forall (q:loc) (L:list int),
  TRIPLE (clear q)
    PRE (q ~> Stack L)
    POST (fun (r:unit) => q ~> Stack nil).
Proof using.
  xwp. xchange Stack_eq. intros p. xapp. xapp.
  xapp. intros p'. xapp. xchange <- Stack_eq.
Qed.
(* /SOLUTION *)


(* ####################################################### *)
(** * Optional contents *)


(* ******************************************************* *)
(** *** In-place append on lists *)

(** The operation [mappend p1 p2] performs in-place append of two
    independent mutable lists. The operation returns a pointer [p]
    on a list that stores all the items from [p1] followed by all
    the items from [p2]. The operation does not allocate any list
    cell; Instead, it reuses the cells from the two input lists.

    The function [mappend] treats specially the case where [p1]
    is null, by directly returning [p2]. Otherwise, if [p1] is not
    null, it invokes an auxiliary function called [mappend_aux],
    which expects pointers [p1] and [p2] on two lists, and traverses
    the first list until reaching its last cell. At that point, it
    sets the tail field of the last cell to point on [p2].
    Subsequently to a call to [mappend p1 p2], the pointer [p1]
    points to a list that stores the result of the concatenation
    of the two input lists.

    The implementation is as follows.

[[
    let mappend_aux p1 p2 =
      if p1.tail == null
        then p1.tail <- p2
        else mappend p1.tail p2

    let mappend p1 p2 =
      if p1 == null
        then p2
        else mappend_aux p1 p2
]]
*)

Definition mappend_aux : val :=
  VFix 'f 'p1 'p2 :=
    If_ 'p1'.tail '= null
      Then Set 'p1'.tail ':= 'p2
      Else 'f ('p1'.tail) 'p2.

Definition mappend : val :=
  VFun 'p1 'p2 :=
    If_ 'p1 '= null Then 'p2 Else (
      mappend_aux 'p1 'p2 ';
      'p1
    ).

(* EX3! (Triple_mappend_aux) *)
(** [Verify the implementation of [mappend_aux].
    Hint: use [xchange (MList_if p1)] to exploit [MList_if] for
    the first list.
    Hint: use [rew_listx] (or [rewrite app_cons_l]) to normalize
    the list expression [(x::L1')++L2]. *)

Lemma Triple_mappend_aux : forall (p1 p2:loc) (L1 L2:list int),
  p1 <> null ->
  TRIPLE (mappend_aux p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (r:unit) => p1 ~> MList (L1++L2)).
Proof using.
(* SOLUTION *)
  intros. gen p1. induction_wf IH: list_sub L1.
  xwp. xchange (MList_if p1). case_if. xpull. intros x q L1' ->.
  xapp. xapp. xif; intros Cq.
  { xchange (MList_if q). case_if. xpull. intros ->.
    xapp. xchange <- MList_cons. }
  { xapp. xapp. { auto. } { auto. }
    rew_listx. xchange <- MList_cons. }
(* /SOLUTION *)
Qed.

Hint Extern 1 (Register_Spec mappend_aux) => Provide Triple_mappend_aux.

(* EX2! (Triple_mappend) *)
(** Verify the function implementation of [mappend]. *)

Lemma Triple_mappend : forall (p1 p2:loc) (L1 L2:list int),
  TRIPLE (mappend p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (p:loc) => p ~> MList (L1++L2)).
Proof using.
(* SOLUTION *)
  xwp. xapp. xif; intros C.
  { xchange (MList_if p1). case_if. xpull. intros ->.
    xval. xsimpl. }
  { xapp. { auto. } xval. xsimpl. }
(* /SOLUTION *)
Qed.

Hint Extern 1 (Register_Spec mappend) => Provide Triple_mappend.


(* ******************************************************* *)
(** *** Exercise: concatenation on stacks *)

(** The operation [concat q1 q2] expects two imperative stacks,
    and migrate the contents of the second into the first first
    stacks. The elements from the first stack are placed near the
    top of the stack, while the elements from the second stack are
    placed near the bottom.

    The operation is implemented by exploiting the function [mappend],
    which performs in-place concatenation of two mutable lists.
    The operation [concat q1 q2] also reinitialize the contents of [q2]
    to be empty.

[[
    let concat q1 q2 =
      q1 := mappend !q1 !q2;
      q2 := mnil ()
]]
*)

Definition concat : val :=
  VFun 'q1 'q2 :=
    'q1 ':= mappend ('!'q1) ('!'q2) ';
    'q2 ':= mnil '().

(* EX2! (Triple_concat) *)
(** Specify and verify the function [concat]. *)

(* SOLUTION *)
Lemma Triple_concat : forall (q1 q2:loc) (L1 L2:list int),
  TRIPLE (concat q1 q2)
    PRE (q1 ~> Stack L1 \* q2 ~> Stack L2)
    POST (fun (r:unit) => q1 ~> Stack (L1 ++ L2) \* q2 ~> Stack nil).
Proof using.
  xwp. do 2 xchange Stack_eq. intros p1 p2. xapp. xapp.
  xapp. intros p1'. xapp.
  xapp. intros p2'. xapp.
  do 2 xchange <- Stack_eq. xsimpl.
Qed.

Hint Extern 1 (Register_Spec concat) => Provide Triple_concat.
(* /SOLUTION *)

(* INCLASS *)
(** Question: what would be the issue for verifying the function [concat]
    if the second line [q2 := mnil()] was written instead [clear q2]?
    How could it be handled if we nevertheless wanted to verify such an
    alternative code? *)
(* /INCLASS *)

(* INSTRUCTORS *)
(** Answer: the precondition of [clear q2] requires [q2 ~> Stack L]
    for some list [L], yet when reasoning about the second line from
    the body of [concat], all we have at hand is [q2 ~~> p2] for some
    pointer [p2] that points to a list that we longer have at hand.
    The only way out is to prove an alternative, more relaxed
    specification for [clear], which accepts a precondition of the
    form [q ~~> p]. Note that the original specification for [clear]
    would be derivable from that relaxed specification. *)
(* /INSTRUCTORS *)


(* ******************************************************* *)
(** *** Exercise: push back on stacks *)

(** The operation [push_back q x] adds an item [x] to the bottom
    of the queue [q]. This operation is also implemented using
    [mappend], which performs in place concatenation of two lists.  *)

(**
[[
  let push_back q x =
    let p2 = mcell x (mnil()) in
    q := mappend !q p2
]]
*)

Definition push_back : val :=
  VFun 'q 'x :=
    Let 'p2 := mcell 'x (mnil '()) in
    'q ':= mappend ('!'q) 'p2.

(* EX2? (Triple_push_back) *)
(** Specify and verify the function [push_back].
    Remark: TLC provides the notation [L&x] as short for [L++x::nil]. *)

(* SOLUTION *)
Lemma Triple_push_back : forall (q:loc) (x:int) (L:list int),
  TRIPLE (push_back q x)
    PRE (q ~> Stack L)
    POST (fun (_:unit) => q ~> Stack (L++x::nil)).
Proof using.
  xwp. xchange Stack_eq. intros p.
  xapp. intros p0. xapp. intros p1.
  xapp. xchange <- MList_cons. xapp. intros p2.
  xapp. xchange <- Stack_eq.
Qed.

Hint Extern 1 (Register_Spec push_back) => Provide Triple_push_back.
(* /SOLUTION *)


(* ******************************************************* *)
(** *** Exercise: in-place reversal for mutable lists *)

(** The operation [mrev p] reverses a list "in place": it does not allocate
    any list cell, but instead reuses the list cells from its input to
    construct the output list.

    The operation is implemented by means of an auxiliary function:
    [mrev_append p1 p2] constructs the reverse of the list [p2] appended
    to the list [p1]. In other words, [p1] represents the accumulator
    storing the portion of the list already reversed, while [p2]
    represents the portion of the list that remains to be reversed.

[[
    let mrev_append p1 p2 =
      if p2 == null then p1 else begin
        let q = p2.tail in
        p2.tail <- p1;
        mrev_append p2 q
      end

    let mrev p =
      mrev_append null p
]]
*)

Definition mrev_append : val :=
  VFix 'f 'p1 'p2 :=
    If_ 'p2 '= null Then 'p1 Else (
      Let 'q := 'p2'.tail in
      Set 'p2'.tail ':= 'p1 ';
      'f 'p2 'q
    ).

Definition mrev : val :=
  VFun 'p :=
    mrev_append null 'p.


(* EX3! (Triple_ref_greater_abstract) *)
(** Specify and verify [mrev_append].
    Hint: use [gen p1 p2 L1. induction_wf IH: list_sub L2.]
    to set up an induction on the structure of [L2] while
    generalizing [p1], [p2] and [L1], whose value evolves
    throughout the recursive calls.
    Hint: use [xchange (MList_if p2)] to exploit the lemma
    [MList_if] for the second list.
    Hint: use [rew_listx] (or [rewrite rev_cons,app_last_l]) to
    normalize the expression [rev (x::L2')++L1]. *)

(* SOLUTION *)
Lemma Triple_mrev_append : forall (p1 p2:loc) (L1 L2:list int),
  TRIPLE (mrev_append p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (r:loc) => r ~> MList (rev L2 ++ L1)).
Proof using.
  intros. gen p1 p2 L1. induction_wf IH: list_sub L2.
  xwp. xchange (MList_if p2). xif; intros C; case_if; xpull.
  { intros ->. xval. rew_listx. xsimpl. }
  { intros x q L2' ->. xapp. xapp.
    xchange <- MList_cons. xapp. { auto. }
    intros r. rew_listx. xsimpl. }
Qed.

Hint Extern 1 (Register_Spec mrev_append) => Provide Triple_mrev_append.
(* /SOLUTION *)

(** Make sure to include the following command to enable reasoning
    about the call to [mrev_append] from the proof of [mrev].
[[
  Hint Extern 1 (Register_Spec mrev_append) => Provide Triple_mrev_append.
]]
*)

(* EX2! (Triple_mrev) *)
(** Verify [mrev]. *)

Lemma Triple_mrev : forall (p:loc) (L:list int),
  TRIPLE (mrev p)
    PRE (p ~> MList L)
    POST (fun (r:loc) => r ~> MList (rev L)).
Proof using.
(* SOLUTION *)
  intros. xwp. xchange MList_nil_intro. xapp. rew_listx. xsimpl.
(* /SOLUTION *)
Qed.

Hint Extern 1 (Register_Spec mrev) => Provide Triple_mrev.


