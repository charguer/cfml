(**

Foundations of Separation Logic

Chapter: "List".

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Import Example.
Generalizable Variables A B.

Implicit Types x n m : int.
Implicit Types p q : loc.
Implicit Types L : list int.

(** Tweak to make the Separation Logic appear linear instead of affine. *)
Ltac xwp_xtriple_handle_gc ::= xwp_xtriple_remove_gc.

(** Tweak for record allocation to expose individual fields. *)
Ltac xnew_post ::= xnew_post_exploded.

(** Tweak to bind "rew_list" to the normalization tactic for lists. *)
Tactic Notation "rew_list" :=
  autorewrite with rew_listx.


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Chapter in a rush, nested with exercises as additional contents *)

(** The previous chapter has introduced the notation for specification
    triples, the entailment relations, and the grammar for heap predicates,
    and CFML's x-tactics for conducting proofs.

    Recall the heap predicates: [p ~~> n] and [\[]] and [\[P]] and [H1 \* H2]
    and [\exists x, H].

    Recall the x-tactics: [xwp], [xtriple], [xapp], [xval], and [xsimpl].

    Recall the TLC tactics used: [math] for mathematical goals,
    and [induction_wf] and [gen] for inductions. *)

(** The present chapter focuses on the specification and verification
    in Separation Logic of mutable linked lists. Specifically, we consider
    a representation of linked lists where each cell consists of a two-cell
    record, storing a head value and a tail pointer. The empty list is
    represented by the null pointer.

    To avoid unnecessary complications with polymorphism, we restrict
    ourselves in this chapter to mutable lists storing integer values.

    The present chapter describes:

    - how to represent mutable records, such as list cells, in Separation Logic;
    - the definition of the "representation predicate" [p ~> MList L], which
      describes a null-terminated linked list whose first cell has address [p],
      and whose integers elements are described by the Coq list [L];
    - examples of specifications and proofs for programs manipulating mutable lists;
    - how to specify and verify an implementation of imperative stacks implemented
      as a reference on a linked list, using a representation predicate of the form
      [q ~> Stack L].

    This chapter exploits a few additional tactics:
    - [xunfold] is a CFML tactic for unfolding the definition of [MList],
    - [xpull] is a CFML tactic to extract existentials and pure facts from
      the left-hand side of an entailment, or from a precondition of a triple.
    - [xchange] is a CFML tactic to transform the precondition by exploiting
      entailments or equalities,
    - [case_if] is a TLC tactic to perform a case analysis on the argument
      of the first visible [if] that appears in the current proof obligation.
    - [rew_list] is a TLC tactic to normalize list expressions, such as
      [(x::L1)++L2] into [x::(L1++L2)], or [length (x::L)] into [1 + length L],
      and likewise for operations [map] and [filter] on Coq lists.

    Remark: the list operations [++], [map] and [filter] are not those from
    the standard Coq library, but instead those from TLC's [LibList] library.

*)

(* ########################################################### *)
(** ** Representation of a list cell as a two-field record *)

(** In the previous chapter, we have manipulated OCaml-style references,
    which correspond to mutable records with a single field.

    A two-field record can be described in Separation Logic as the
    separating conjunction of two cells at consecutive addresses.

    Concretely, a list cell allocated at address [p], featuring a head
    value [x] and a tail pointer [q], can be represented as:
    [(p+0) ~~> x \* (p+1) ~~> q].

    Throughout this file, to improve clarity, we write:

    - [p`.head] as short for [p+0], to denote the address of the head field,
    - [p`.tail] as short for [p+1], to denote the address of the tail field.

    Using these notation, the same list cell can be represented as
    [p`.head ~~> x  \*  p`.tail ~~> q].

*)

Definition head : field := 0%nat.
Definition tail : field := 1%nat.


(* ########################################################### *)
(** ** Representation of a mutable list of length two *)

(** Consider an example linked list that stores two integers, [8] and [5],
    in two cells, the first one at location [p1], and the second one at
    location [p2].

    The first cell, at location [p1], stores [8] and its tail pointer
    points to [p2]. The second cell, at location [p2], stores [5] and
    its tail pointer is [null], indicating the end of the list.
    The corresponding state can be described as: *)

Definition example_mlist_1 (p1 p2:loc) : hprop :=
  p1`.head ~~> 8  \*  p1`.tail ~~> p2 \*
  p2`.head ~~> 5  \*  p2`.tail ~~> null.

(** What we are seeking for is a general definition of [p ~> MList L].
    This definition should exhibit a regular pattern, so that we can
    characterize it using a recursive or inductive definition.

    In particular, for our two-cell list, the heap predicate should
    take the form [p1 ~> MList (8::5::nil)]. Let us reformulate
    the statement of [example_mlist_1] to make it exhibit a recursive
    pattern, and using an existential quantifier to bind the addresses
    of all the tail pointers that occur in the list. *)

Definition example_mlist_2 (p1:loc) : hprop :=
  \exists (p2:loc), p1`.head ~~> 8  \*  p1`.tail ~~> p2 \*
  \exists (p3:loc), p2`.head ~~> 5  \*  p2`.tail ~~> p3 \*
  \[p3 = null].

(** In that formulation, we can spot the recursive pattern, which is:

[[
  p ~> MList (x::L') = \exists (q:loc), (p`.head ~~> x) \* (p`.tail ~~> q)
                                        \* q ~> MList L'

  p ~> MList nil     = \[p = null]
]]

*)

(* ########################################################### *)
(** ** Representation of a mutable list *)

(** Our goal is to define a heap predicate, written [p ~> MList L], or
    equivalently [MList L p], to describe a mutable linked lists.

    The simple arrow notation, written [p ~> R], is a generic piece
    of notation for the application [R p]. This arrow notation increases
    readability in heap predicates, and it is helpful for [xsimpl] to
    cancel out items when simplifying entailment relations. *)

(** The heap predicate [MList] can be defined recursively over the structure
    of [L]. The logic is as follows:

    - if [L] is [nil], then [p] should be [null];
    - if [L] decomposes as [x::L'], then the head field of [p] should store
      the value [x], the tail field of [p] should store a pointer [q],
      and [q ~> MList L'] should describe the remaining of the list
      structure. In this case, the variable [q] is existentially quantified.

    The definition of [MList] is thus formalized as follows.
*)

Fixpoint MList (L:list int) (p:loc) : hprop := (* defines [p ~> MList L] *)
  match L with
  | nil => \[p = null]
  | x::L' => \exists q, (p`.head ~~> x) \* (p`.tail ~~> q) \* (q ~> MList L')
  end.

(** It is useful to reformulate the definition of [MList] by stating
    two lemmas characterizing [p ~> MList L]. These lemmas will be very
    handy for folding or unfolding the definition of [MList].

    These two lemmas are proved with help of the [xunfold] tactic, which
    is a variant of [unfold] that provides appropriate support for unfolding
    the arrow notation ([~>]). (Indeed, the definition of the arrow is
    purposely set opaque to prevent unintended simplifications.) *)

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


(* ########################################################### *)
(** ** Alternative characterization of [MList] *)

(** Most functions that manipulate a mutable list begin by testing
    whether their argument is the [null] pointer, in order to determine
    whether the list is empty.

    For this reason, it is very useful to reformulate the definition
    of [p ~> MList L] using a test on the condition [p = null],
    as opposed to using a test on the condition [L = nil].

    In a state described by [p ~> MList L], the following is true:

    - if [p = null], then [L = nil];
    - if [p <> null], then the list [L] must have the form [x::L'],
      the head field of [p] contains the value [x], and the tail field
      of [p] contains some pointer [q] such that [q ~> MList L'] is
      a representation of the tail list.

    This logic is captured by the lemma [MList_if] stated below.
    The statement exploits TLC's classical-logic test, written
    [If P then X else Y], where [P] is a proposition of type [Prop],
    to perform the case distinction on the condition [p = null]. *)

Lemma MList_if : forall (p:loc) (L:list int),
  p ~> MList L ==>
    If p = null
      then \[L = nil]
      else \exists x q L', \[L = x::L']
           \* (p`.head ~~> x) \* (p`.tail ~~> q) \* (q ~> MList L').
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
    xchange MList_cons. intros q. case_if.
    { (* Case [p = null]. Contradiction because nothing can be allocated at
         the null location, as captured by lemma [Hfield_not_null],
         which states: [(l`.f ~~> V) ==> (l`.f ~~> V) \* \[l <> null]]. *)
      subst. lets: Hfield_not_null. xchange Hfield_not_null. }
    { (* Case [p <> null]. The 'else' branch corresponds to the definition
         of [MList] in the [cons] case. It suffices to correctly instantiate
         the existential quantifiers. *)
      xsimpl. auto. } }
Qed.

(** Remark: the reciprocal implication to [MList_if] is also true.
    However, its statement is much less useful, because in practice
    one may easily exploit the lemmas [MList_nil] and [MList_cons] directly.
    We nevertheless state and prove the reciprocal below. *)

Lemma MList_if_reciprocal : forall (p:loc) (L:list int),
   (If p = null
      then \[L = nil]
      else \exists x q L', \[L = x::L']
           \* (p`.head ~~> x) \* (p`.tail ~~> q) \* (q ~> MList L'))
 ==> p ~> MList L.
Proof using.
  intros. case_if.
  { xpull. intros ->. xchange <- (MList_nil p). { auto. } }
  { xpull. intros x q L' ->. xchange <- MList_cons. }
Qed.

(** Remark: one might be tempted to consider the characterization
    provided by [MList_if] directly as a definition for [MList], that is:

[[
    Fixpoint MList (L:list int) (p:loc) : hprop :=
      If p = null
        then \[L = nil]
        else \exists x q L', \[L = x::L']
             \* (p`.head ~~> x) \* (p`.tail ~~> q) \* (q ~> MList L').
]]

    However, this definition is rejected by Coq, because Coq does not
    recognize the structural recursion, even though the recursive call
    is made with a list [L'] being a strict sublist of the argument [L]. *)


(* EX1! (MList_null_iff_nil) *)
(** Prove the following lemma, which asserts that in a predicate
    [p ~> MList L], the pointer [p] is null iff the list [L] is empty. *)

Lemma MList_null_iff_nil : forall (p:loc) (L:list int),
  (p ~> MList L) ==> (p ~> MList L) \* \[p = null <-> L = nil].
Proof using.
(* ADMITTED *)
  intros. xchange MList_if. case_if; xpull.
  { intros ->. rewrite MList_nil. xsimpl*. }
  { intros x q L' ->. rewrite MList_cons. xsimpl*. }
Qed. (* /ADMITTED *)

(** [] *)


(* ########################################################### *)
(** ** Function [mhead] *)

(** Consider the function [mhead p], which expects a pointer [p] on a
    nonempty mutable list, and returns the value of its head element.

[[
    let rec mhead p =
      p.head
]]
*)

Definition mhead : val :=
  Fun 'p :=
    'p'.head.

(** One way to capture in the specification that the list should be
    nonempty is to state a precondition of the form [p ~> MList (x::L)].
    With such a precondition, the postcondition asserts that the
    result of reading the head value yields exactly the value [x]. *)

Lemma Triple_mhead : forall (p:loc) (x:int) (L:list int),
  TRIPLE (mhead p)
    PRE (p ~> MList (x::L))
    POST (fun (r:int) => \[r = x] \* (p ~> MList (x::L))).

(** The proof of this simple function is interesting because it shows
    how to unfold the definition of [MList], then fold it back. *)

Proof using.
  xwp.
  (* In order to read in [p.head], we must make visible in the current
     state the head field, that is [p`.head ~~> x]. We achieve this by
     unfolding the definition of [MList], using lemma [MList_cons].
     Here [xchange MList_cons] performs [rewrite MList_cons at 1; xpull]. *)
  xchange MList_cons. intros q.
  (* Here, the name [q] introduced comes from the existentially quantified
     variable [q] in the definition of [MList]. *)
  (* At this stage, we are ready to read the value [x] in the head field. *)
  xapp.
  (* To conclude, there remains to fold back the definition of [MList].
     This task is achieved by means of the [xchange <-] tactic, which
     exploits the equality [MList_cons] backwards. *)
  xchange <- MList_cons.
  (* Finally, we check that the final state matches the postcondition. *)
  xsimpl. auto.
Qed.

Hint Extern 1 (Register_Spec mhead) => Provide Triple_mhead.

(** An alternative statement for the specification of [mhead] features a
    precondition of the form [p ~> MList L], accompanied with a pure
    side-condition asserting that the list is nonempty, that is, [L <> nil].

    In that specification, the postcondition asserts that the result value
    [x] is the head of the list [L]. This can be written
    [\[exists L', L = x::L']], or equivalently, [\exists L', \[L = x::L']].
    By convention, we prefer using Separation Logic quantifiers in
    postconditions, as they tend to reduce the number of proof steps. *)

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
     Rather than copy-pasting it, we can invoke [Triple_mhead].
     Recall from the previous chapter that the [xtriple] tactic
     combined with [xapp] enables to derive a specification from
     an existing one. *)
  xtriple. xapp Triple_mhead. xsimpl. eauto.
Qed.


(* ########################################################### *)
(** ** Function [mtail] *)

(** Consider the function [mtail], which returns the pointer on the
    tail of a mutable list. As we are going to see, specifying this
    function is quite interesting from a Separation Logic perspective.

[[
    let rec mtail p =
      p.tail
]]
*)

Definition mtail : val :=
  Fun 'p :=
   'p'.tail.

(** In a context [p ~> MList (x::L)], a call to [mtail p] returns
    a pointer [q] to a mutable list such that [q ~> MList L].
    However, it would be incorrect to pretend that both
    [p ~> MList (x::L)] and [q ~> MList L] coexist, because the
    two heap predicates describe overlapping pieces of memory.

    The following lemma is thus incorrect. If we play the same script
    as for [Triple_mhead], we indeed end up stuck. *)

Lemma Triple_mtail_incorrect : forall (p:loc) (x:int) (L:list int),
  TRIPLE (mtail p)
    PRE (p ~> MList (x::L))
    POST (fun (q:loc) => (p ~> MList (x::L)) \* (q ~> MList L)).
Proof using.
  xwp. xchange MList_cons. intros q. xapp.
  (* With the script [xchange <- MList_cons. xsimpl.]
     we can satisfy [p ~> MList (x::L)] but not [q ~> MList L]. *)
  (* With the script [xsimpl.]
     we can satisfy [q ~> MList L] but not [p ~> MList (x::L)]. *)
  (* There is no way to satisfy both pieces of the postcondition. *)
Abort.

(** As suggested by the execution of the above proof script, a valid
    postcondition for [mtail] is:
    [p`.tail ~~> q \* p`.head ~~> x \* q ~> MList L]. *)

Lemma Triple_mtail_cons : forall (p:loc) (x:int) (L:list int),
  TRIPLE (mtail p)
    PRE (p ~> MList (x::L))
    POST (fun (q:loc) => (p`.head ~~> x) \* (p`.tail ~~> q) \* (q ~> MList L)).
Proof using.
  xwp. xchange MList_cons. intros q. xapp. xsimpl.
Qed.

(** Again, an equivalent specification can be stated with a precondition
    of the form [p ~> MList L] accompanied with [L <> nil]. In that case,
    the variables [x] and [L'] such that [L = x::L'] are existentially
    quantified in the postcondition. *)

Lemma Triple_mtail : forall (p:loc) (L:list int),
  L <> nil ->
  TRIPLE (mtail p)
    PRE (p ~> MList L)
    POST (fun (q:loc) => \exists x L', \[L = x::L']
             \* (p`.head ~~> x) \* (p`.tail ~~> q) \* (q ~> MList L')).
Proof using.
  introv HL. destruct L as [|x L']. { contradiction. }
  xtriple. xapp Triple_mtail_cons. xsimpl. eauto.
Qed.

Hint Extern 1 (Register_Spec mtail) => Provide Triple_mtail.

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

(** Is there a "better" specifications among [Triple_mtail],
    [Triple_mtail_notnil] and [Triple_mtail_minimal]?

    [Triple_mtail_minimal] is only useful for reasoning about
    invocations of [mtail] on lists whose representation predicate
    is already unfolded. When, however, the list is represented
    by a predicate of the form [p ~> MList _], the other two
    specifications are more appropriate.

    The specification [Triple_mtail_cons] only applies to states that
    are described in the form [p ~> MList (x::L')]. In contrast,
    [Triple_mtail] applies more generally, to any predicate
    [p ~> MList L], even if [L] is not syntactically of the form
    [x::L'], as long as [L] can be somehow proved to be nonempty.

    For this reason, a list library would preferably expose
    the specification [Triple_mtail]. *)


(* ########################################################### *)
(** ** Length of a mutable list *)

(** The function [mlength] computes the length of a linked list
    by recursively traversing through its cells, and counting
    one unit for each cell.

[[
    let rec mlength p =
      if p == null
        then 0
        else 1 + mlength (tail p)
]]
*)

Definition mlength : val :=
  Fix 'f 'p :=
    If_ 'p '= null
      Then 0
      Else 1 '+ 'f ('p'.tail).

(** The precondition of [mlength p] requires the description of the
    linked list that it traverses, that is, [p ~> MList L].
    Its postcondition asserts that the result is equal to [length L],
    and that the list predicate [p ~> MList L] is returned unmodified. *)

Lemma Triple_mlength : forall (p:loc) (L:list int),
  TRIPLE (mlength p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).

(** The proof goes by induction on the length of the list [L].
    Each time the function traverses a cell, this cell is isolated
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
  (* The critical step is to reformulate [MList] using the lemma [MList_if],
     so as to make the case analysis on the condition [p = null] visible. *)
  xchange MList_if.
  (* The [xif] tactics performs the case analysis on the condition [p = null]
     that occurs in the code, while the [case_if] tactic performs the case analysis
     on the (similar) condition [p = null] that occurs in the precondition
     (the condition that was just introduced by [MList_if]. *)
  xif.
  { (* Case [p = null]. *)
    intros C.
    (* We simplify the precondition exploiting [p = null]. *)
    case_if. xpull. intros ->.
    (* We reason about the result value, and fold back [p ~> List nil]. *)
    xval. xchange <- (MList_nil p). { auto. }
    (* We justify that [length nil = 0]. *)
    xsimpl. rew_list. math. }
  { (* Case [p <> null]. *)
    intros C.
    (* We simplify the precondition exploiting [p <> null]. *)
    case_if. xpull. intros x q L' ->.
    (* We reason about the read in the tail field. *)
    xapp.
    (* For the recursive call, we exploit [IH] applied to the sublist
       [q ~> MList L']. Observe that, during this call, the head cell described
       by [p`.tail ~~> q \* p`.head ~~> x] remain unchanged---the two fields
       fields are said to be "framed", in the Separation Logic jargon. *)
    xapp.
    (* We justify that [L'] is a sublist of [x::L']. *)
    { auto. }
    (* We reason about the [+ 1] operation. *)
    xapp.
    (* We fold back the list into [p ~> MList(x::L')] *)
    xchange <- MList_cons.
    (* We justify that [length (x::L') = 1 + length L'] *)
    xsimpl. rew_list. math. }
Qed.

(** Let us rewrite the same proof, more concisely. This proof script
    will serve us as template for all the list-manipulating functions
    verified throughout the rest of this chapter.

    Recall that the [*] symbol placed after a tactic indicates a call
    to automation (technically, a combination of the tactics
    [intuition eauto] and [math]). *)

Lemma Triple_mlength_concise : forall (p:loc) (L:list int),
  TRIPLE (mlength p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  intros. gen p. induction_wf IH: list_sub L. intros.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros ->. xval. xchange* <- (MList_nil p). xsimpl*. }
  { intros x q L' ->. xapp. xapp*. xapp. xchange <- MList_cons. xsimpl*. }
Qed.

Hint Extern 1 (Register_Spec mlength) => Provide Triple_mlength.


(* ########################################################### *)
(** ** Exercise: increment through a mutable list *)

(** The function [mlist_incr] expects a linked list of integers
    and updates the list in place by augmenting every item in the
    list by one unit.

[[
    let rec mlist_incr p =
      if p != null then begin
        p.head <- p.head + 1;
        mlist_incr p.tail
      end
]]
*)

Definition mlist_incr : val :=
  Fix 'f 'p :=
    If_ 'p '<> null Then (
      Set 'p'.head ':= 'p'.head '+ 1 ';
      'f ('p'.tail)
    ) End.

(** The precondition of [mlist_incr p] requires a linked list
    [p ~> MList L]. Its postcondition asserts that the updated list
    takes the form [p ~> MList L2], where
    [L2 = LibList.map (fun x => x+1) L], that is, the result of
    mapping the successor function onto every item from [L].  *)

Lemma Triple_mlist_incr : forall (p:loc) (L:list int),
  TRIPLE (mlist_incr p)
    PRE (p ~> MList L)
    POST (fun (r:unit) => p ~> MList (LibList.map (fun x => x+1) L)).

(* EX2! (Triple_mlist_incr) *)
(** Prove [Triple_mlist_incr], following the pattern of [Triple_mlength].
    Hint: it need, you can use the tactic [rew_list] for normalizing
    [LibList.map f (x::l)] into [f x :: LibList.map f l].
    (Alternatively, use lemmas [LibList.map_nil] and [LibList.map_cons].) *)

Proof using. (* ADMITTED *)
  intros. gen p. induction_wf IH: list_sub L.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros x p' L' ->. xapp. xapp. xapp. xapp. xapp. { auto. }
    xchange <- MList_cons. }
  { intros ->. xval. xchange <- (MList_nil p). { auto. } }
Qed. (* /ADMITTED *)

(** [] *)


(* ########################################################### *)
(** ** Allocation of a new cell: [mcell] and [mcons] *)

(** Next, we consider functions for constructing mutable lists.
    We begin with the function that allocates one cell.
    The function [mcell] takes as arguments the values to be
    stored in the head and the tail fields of the new cell.

[[
    let rec mcell x q =
      { head = x; tail = q }
]]

    In our ad-hoc program syntax, the [New] construct denotes record
    allocation. *)

Definition mcell : val :=
  Fun 'x 'q :=
    New`{ head := 'x ; tail := 'q }.

(** The precondition of [mcell x q] is empty. Its postcondition
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


(* ########################################################### *)
(** ** Function [mnil] *)

(** The operation [mnil()] returns the [null] value.
    The intention is to produce a representation for the empty list.

[[
    let rec mnil () =
      null
]]
*)

Definition mnil : val :=
  Fun 'u :=
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
  Fix 'f 'p :=
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

Definition mfree_cell : val :=
  Fun 'p :=
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


(* ########################################################### *)
(** ** Exercise: deallocation of a list: [mfree_list] *)

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
  Fix 'f 'p :=
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
(** ** Representation of a mutable stack *)

(** We now move on to using linked lists for implementing stacks.
    Thereafter, a stack is represented as a reference on a mutable
    linked list.

    We first introduce the heap predicate [q ~> Stack L] to describe
    mutable stacks.

    - An empty stack is represented as a reference whose contents
      is null, that is, by the heap predicate [q ~~> null].
    - A nonempty stack is represented as a reference whose contents
      is a pointer on a proper linked list, that is, by the heap
      predicate [(q ~~> p) \* (p ~> MList L)], for some pointer [p].

    The definition of [q ~> Stack L], equivalent to [Stack L q], is
    thus as follows. *)

Definition Stack (L:list int) (q:loc) : hprop :=
  \exists p, (q ~~> p) \* (p ~> MList L).

(** The following lemma reformulates the definition of [q ~> Stack L]
    as an equality. Invoking the tactic [xchange Stack_eq] is handy to
    unfold the definition of [Stack]. Reciprocally, invoking the tactic
    [xchange <- Stack_eq] performs the reciprocal operation of folding
    back the definition. *)

Lemma Stack_eq : forall (q:loc) (L:list int),
  (q ~> Stack L) = (\exists p, (q ~~> p) \* (p ~> MList L)).

(** Again, the tactic [xunfold] is used to prove the reformulation lemma. *)

Proof using. xunfold Stack. auto. Qed.


(* ########################################################### *)
(** ** Operation [create] *)

(** The operation [create ()] allocates an empty stack.
[[
    let create () =
      ref (mnil())
]]
*)

Definition create : val :=
  Fun 'u :=
    'ref (mnil '()).

(** The precondition of [create] is empty. Its postcondition asserts
    that the result value is a pointer [q] such that [q ~> Stack nil],
    that is, a pointer onto the representation of an empty stack. *)

Lemma Triple_create :
  TRIPLE (create '())
    PRE \[]
    POST (fun (q:loc) => q ~> Stack nil).
Proof using.
  xwp.
  (* [mnil()] creates an empty linked list: [p ~> MList nil]. *)
  xapp. intros p.
  (* [ref p] allocates a reference with contents [q], that is, [q ~~> p]. *)
  xapp. intros q.
  (* Folding the definition of [Stack] gives [p ~> Stack nil]. *)
  xchange <- Stack_eq.
Qed.

Hint Extern 1 (Register_Spec create) => Provide Triple_create.


(* ########################################################### *)
(** ** Operation [push] *)

(** The operation [push q x] modifies the stack [q] in place by
    inserting the element [x] at the top of the stack.

[[
    let push q x =
      q := mcons x !q
]]
*)

Definition push : val :=
  Fun 'q 'x :=
    'q ':= mcons 'x ('!'q).

(** The precondition of [push q x] requires a stack [q ~> Stack L].
    Its postcondition describes the updated stack as [q ~> Stack (x::L)]. *)

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
  (* The operation [q := p'] updates the reference implementing the stack. *)
  xapp.
  (* The new state [q ~~> p' \* p' ~> MList (x::L')] can be folded into
     a [q ~> Stack (x::L')]. *)
  xchange <- Stack_eq.
Qed.

Hint Extern 1 (Register_Spec push) => Provide Triple_push.


(* ########################################################### *)
(** ** Operation [is_empty] *)

(** The operation [is_empty q] returns a boolean value indicating
    whether the stack at address [q] is empty.

[[
    let is_empty q =
      !q == null
]]
*)

Definition is_empty : val :=
  Fun 'q :=
    '!'q '= null.

(** The precondition of [is_empty q] requires a stack [q ~> Stack L].
    Its postcondition asserts that the stack is returned unmodified,
    and that the result is a boolean value [b] such that [b = true]
    if and only if [L = nil]. *)

Lemma Triple_is_empty : forall (q:loc) (L:list int),
  TRIPLE (is_empty q)
    PRE (q ~> Stack L)
    POST (fun (b:bool) => \[b = true <-> L = nil] \* q ~> Stack L).

(** A naive attempt at the proof leaves a final proof obligation
    [p = null <-> L = nil] with absolutely no hypothesis to prove it. *)

Proof using.
  xwp. xchange Stack_eq. intros p. xapp. xapp. xchange <- Stack_eq. xsimpl.
Abort.

(** What is needed here is a lemma asserting that whenever [p ~> MList L]
    is valid, it is the case that [p = null <-> L = nil]. This result
    is captured by the lemma [MList_null_iff_nil], proved earlier as an
    exercise.

[[
    Lemma MList_null_iff_nil : forall (p:loc) (L:list int),
      p ~> MList L ==> p ~> MList L \* \[p = null <-> L = nil].
]]

    This lemma can be used by [xchange]. *)

(** Equipped with this lemma, let's attempt againt the verification
    of the function [is_empty]. *)

Lemma Triple_is_empty : forall (q:loc) (L:list int),
  TRIPLE (is_empty q)
    PRE (q ~> Stack L)
    POST (fun (b:bool) => \[b = true <-> L = nil] \* q ~> Stack L).
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

Hint Extern 1 (Register_Spec is_empty) => Provide Triple_is_empty.


(* ########################################################### *)
(** ** Operation [pop] *)

(** The operation [pop p] applies to a nonempty stack.
    It returns the element at the top of the stack,  and removes it
    from the stack. Note that the implementation takes care of
    deallocating the top list cell, which is no longer needed.

[[
    let pop q =
      let p = !q in
      let x = mhead p in
      q := mtail p;
      mfree_cell p;
      x
]]
*)

Definition pop : val :=
  Fun 'q :=
    Let 'p := '!'q in
    Let 'x := mhead 'p in
    'q ':= mtail 'p ';
    mfree_cell 'p ';
    'x.

(** Again, there are two ways to specify a nonempty stack:
    either using [q ~> Stack (x::L)], or using [q ~> Stack L]
    with [L <> nil]. In practice, the second presentation turns
    out to be almost always preferable. The reason is that the
    typical programming idiom is:

[[
   while not (Stack.is_empty q) do
      let x = Stack.pop q in
      ...
   done
]]

    where the operation [is_empty q] is testing whether [L = nil]
    or [L <> nil]. Thus, at the entrance of the loop body, the
    information available is [L <> nil]. The latter is therefore
    a natural precondition for [Stack.pop], which is the first
    operation inside the loop body.

    Thus, we formulate the specification of [pop] as follows. *)

Lemma Triple_pop : forall (q:loc) (L:list int),
  L <> nil ->
  TRIPLE (pop q)
    PRE (q ~> Stack L)
    POST (fun (x:int) => \exists L', \[L = x::L'] \* q ~> Stack L').

(** The proof begins by deconstructing the list [L] as [x::L'],
    like it was done in lemma [Triple_mtail]. *)

Proof using.
  introv HL. destruct L as [|x L']; [contradiction|].
  xwp. xchange Stack_eq. intros p. xapp. xapp.
  (* alternative here: [xapp Triple_mtail_cons. intros p'.] *)
  xapp. { auto. } intros p' ? ? E. inverts E.
  xapp. xapp. xval.
  xchange <- Stack_eq. xsimpl. auto.
Qed.

Hint Extern 1 (Register_Spec pop) => Provide Triple_pop.

(** This concludes our investigation of the representation in
    Separation Logic of a mutable stack. Additional functions
    are presented further in this file, as exercises. *)


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Additional contents *)


(* ########################################################### *)
(** ** Exercise: out-of-place append of two mutable lists *)

(** The operation [mappend_copy p1 p2] assumes two independent lists
    at location [p1] and [p2], and constructs a third, independent list
    whose items are the concatenation of those from the two input lists.
    Observe how the implementation invokes [copy p2] in the base case.

[[
    let rec mappend_copy p1 p2 =
      if p1 == null then mcopy p2 else begin
        let p = mappend_copy p1.tail p2 in
        mcons p1.head p
      end
]]
*)

Definition mappend_copy : val :=
  Fix 'f 'p1 'p2 :=
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
  { intros ->. xapp. xsimpl. xchange* <- (MList_nil p1). }
  { intros x q L' ->. xapp. xapp. { auto. } intros q'.
    xapp. xapp. intros p'. xchange <- MList_cons. xsimpl. }
Qed.
(* /SOLUTION *)

(** [] *)


(* ########################################################### *)
(** ** Exercise: out-of-place filter on list *)

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
  Fix 'f 'p :=
    If_ 'p '= null Then mnil '() Else (
      Let 'x := 'p'.head in
      Let 'q2 := 'f ('p'.tail) in
      If_ 'x '= 0 Then 'q2 Else (mcons 'x 'q2)
    ).

(* EX3! (Triple_mcopy_nonneg) *)
(** Specify and verify the function [mcopy_nonneg],
    using [LibList.filter (<> 0) L] to describe the resulting list.

    The tactic [rew_list] simplifies expressions involving [filter].
    Alternatively, use [LibList.filter_nil] and [LibList.filter_cons]. *)

(* SOLUTION *)
Lemma Triple_mcopy_nonneg : forall (p:loc) (L:list int),
  TRIPLE (mcopy_nonneg p)
    PRE (p ~> MList L)
    POST (fun (p2:loc) => p ~> MList L \* p2 ~> MList (LibList.filter (<> 0) L)).
Proof using.
  intros. gen p. induction_wf IH: list_sub L. intros.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros ->. xapp. xsimpl. xchange* <- (MList_nil p). }
  { intros x q L' ->. xapp. xapp. xapp. { auto. } intros q'.
    xchange <- MList_cons. xapp.
    rew_list. xif; intros Cx; case_if as Cx'.
    { xval. xsimpl. }
    { xapp. intros p2. xsimpl. } }
Qed.
(* /SOLUTION *)

(** [] *)


(* ########################################################### *)
(** ** Exercise: length of a mutable list using a reference *)

(** The operation [mlength_acc p] computes the length of a list [p]
    by traversing the cells of the list and incrementing a reference
    by one unit at each step. If the reference cell is initialized
    with zero, then, at the end of the traversal, it contains the
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
  Fix 'f 'a 'p :=
    If_ 'p '<> null Then
      incr 'a ';
      'f 'a ('p'.tail)
   End.

Definition mlength_acc : val :=
  Fun 'p :=
    Let 'a := 'ref 0 in
    mlength_acc_rec 'a 'p ';
    Let 'n := '! 'a in
    'free 'a ';
    'n.

(* EX3? (Triple_mlength_acc_rec) *)
(** Specify and verify the function [mlength_acc_rec].
    Hint: make sure to generalize the relevant variables in the script
    pattern [gen ? ?. induction_wf IH: list_sub L.], so that your
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
     xchange <- MList_cons. xsimpl. rew_list. math. }
  { intros ->. xval. xchange <- (MList_nil p). { auto. }
    xsimpl. rew_list. math.  }
Qed.

Hint Extern 1 (Register_Spec mlength_acc_rec) => Provide Triple_mlength_acc_rec.
(* /SOLUTION *)

(** [] *)

(** Make sure to include the following command to enable reasoning
    about the call to [mrev_append] from the proof of [mrev].
[[
  Hint Extern 1 (Register_Spec mlength_acc_rec) => Provide Triple_mlength_acc_rec.
]]
*)

(* EX2? (Triple_mlength_acc) *)
(** Prove that [mlength_acc] satisfies the same specification as [mlength]. *)

Lemma Triple_mlength_acc : forall (p:loc) (L:list int),
  TRIPLE (mlength_acc p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using. (* ADMITTED *)
  xwp. xapp. intros a. xapp. xapp. xapp. xval. xsimpl. math.
Qed. (* /ADMITTED *)

(** [] *)


(* ########################################################### *)
(** ** Exercise: operation [delete] on stack *)

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
  Fun 'q :=
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

(** [] *)


(* ########################################################### *)
(** ** Exercise: operation [clear] on stack *)

(** The function [clear] removes all elements from a mutable stack.

[[
    let clear q =
      mfree_list !q;
      q := mnil()
]]
*)

Definition clear : val :=
  Fun 'q :=
    mfree_list ('!'q) ';
    'q ':= mnil '().

(* EX1! (Triple_clear) *)
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

(** [] *)


(* ########################################################### *)
(* ########################################################### *)
(* ########################################################### *)
(** * Optional contents *)


(* ########################################################### *)
(** ** In-place append on lists *)

(** The operation [mappend p1 p2] performs in-place append of two
    independent mutable lists. The operation returns a pointer [p]
    on a list that stores all the items from [p1] followed by all
    the items from [p2]. The operation does not allocate any list
    cell. Instead, it reuses the cells from the two input lists.

    The function [mappend] treats specially the case where [p1]
    is null, by directly returning [p2]. Otherwise, if [p1] is not
    null, it invokes an auxiliary function called [mappend_aux],
    which expects pointers [p1] and [p2] on two lists, and traverses
    the first list until reaching its last cell. At that point, it
    sets the tail field of the last cell to point on [p2].

    Subsequently to a call to [mappend_aux p1 p2], the pointer [p1]
    points to a list that stores the result of the concatenation
    of the two input lists.

    The two functions are implemented as follows.

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
  Fix 'f 'p1 'p2 :=
    If_ 'p1'.tail '= null
      Then Set 'p1'.tail ':= 'p2
      Else 'f ('p1'.tail) 'p2.

Definition mappend : val :=
  Fun 'p1 'p2 :=
    If_ 'p1 '= null Then 'p2 Else (
      mappend_aux 'p1 'p2 ';
      'p1
    ).

(* EX3! (Triple_mappend_aux) *)
(** Verify the implementation of [mappend_aux].
    Hint: use [xchange (MList_if p1)] to exploit [MList_if] for
    the first list.
    Hint: use [rew_list] to normalize the list expression
    [(x::L1')++L2]. (Alternatively, use [rewrite app_cons_l].) *)

Lemma Triple_mappend_aux : forall (p1 p2:loc) (L1 L2:list int),
  p1 <> null ->
  TRIPLE (mappend_aux p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (r:unit) => p1 ~> MList (L1++L2)).
Proof using. (* ADMITTED *)
  introv N. gen p1. induction_wf IH: list_sub L1.
  xwp. xchange (MList_if p1). case_if. xpull. intros x q L1' ->.
  xapp. xapp. xif; intros Cq.
  { xchange (MList_if q). case_if. xpull. intros ->.
    xapp. xchange <- MList_cons. }
  { xapp. xapp. { auto. } { auto. }
    rew_list. xchange <- MList_cons. }
Qed. (* /ADMITTED *)

(** [] *)

Hint Extern 1 (Register_Spec mappend_aux) => Provide Triple_mappend_aux.

(* EX2! (Triple_mappend) *)
(** Verify the function implementation of [mappend]. *)

Lemma Triple_mappend : forall (p1 p2:loc) (L1 L2:list int),
  TRIPLE (mappend p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (p:loc) => p ~> MList (L1++L2)).
Proof using. (* ADMITTED *)
  xwp. xapp. xif; intros C.
  { xchange (MList_if p1). case_if. xpull. intros ->.
    xval. xsimpl. }
  { xapp. { auto. } xval. xsimpl. }
Qed. (* /ADMITTED *)

(** [] *)

Hint Extern 1 (Register_Spec mappend) => Provide Triple_mappend.


(* ########################################################### *)
(** ** Exercise: concatenation on stacks *)

(** The operation [concat q1 q2] expects two imperative stacks,
    and migrates the contents of the second into the first first
    stacks. The elements from the first stack are placed near the
    top of the stack, while the elements from the second stack are
    placed near the bottom.

    The operation is implemented by exploiting the function [mappend],
    which performs in-place concatenation of two mutable lists.
    The operation [concat q1 q2] also reinitialize the contents
    of [q2] to be empty.

[[
    let concat q1 q2 =
      q1 := mappend !q1 !q2;
      q2 := mnil ()
]]
*)

Definition concat : val :=
  Fun 'q1 'q2 :=
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

(** [] *)

(* QUIZ *)
(** Question: what would be the issue for verifying the function [concat]
    if the second line [q2 := mnil()] was written instead [clear q2]?
    How could it be handled if we nevertheless wanted to verify such an
    alternative code? *)
(* /QUIZ *)

(* INSTRUCTORS *)
(** Answer: the precondition of [clear q2] requires [q2 ~> Stack L]
    for some list [L], yet when reasoning about the second line from
    the body of [concat], all we have at hand is [q2 ~~> p2] for some
    pointer [p2] that points to a list that we longer have at hand.
    The only way out is to prove an alternative, more minimalistic
    specification for [clear], which accepts a precondition of the
    form [q ~~> p]. Note that the original specification for [clear]
    would be derivable from that minimalistic specification, similarly
    to how [Triple_mtail] is derivable from [Triple_mtail_minimal]. *)
(* /INSTRUCTORS *)


(* ########################################################### *)
(** ** Exercise: push back on stacks *)

(** The operation [push_back q x] adds an item [x] to the bottom
    of the stack [q]. This operation is also implemented using
    [mappend], which performs in place concatenation of two lists.  *)

(**
[[
  let push_back q x =
    let p2 = mcell x (mnil()) in
    q := mappend !q p2
]]
*)

Definition push_back : val :=
  Fun 'q 'x :=
    Let 'p2 := mcell 'x (mnil '()) in
    'q ':= mappend ('!'q) 'p2.

(* EX2? (Triple_push_back) *)
(** Specify and verify the function [push_back].
    Remark: when the TLC is loaded, [L++x::nil] gets displayed as [L&x] . *)

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

(** [] *)


(* ########################################################### *)
(** ** Exercise: in-place reversal for mutable lists *)

(** The operation [mrev p] reverses a list "in place": it does not
    allocate any list cell, but instead reuses the list cells from
    its input to construct the output list.

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
  Fix 'f 'p1 'p2 :=
    If_ 'p2 '= null Then 'p1 Else (
      Let 'q := 'p2'.tail in
      Set 'p2'.tail ':= 'p1 ';
      'f 'p2 'q
    ).

Definition mrev : val :=
  Fun 'p :=
    mrev_append null 'p.

(* EX3! (Triple_mrev_append) *)
(** Specify and verify [mrev_append].

    Hint: use [gen p1 p2 L1. induction_wf IH: list_sub L2.]
    to set up an induction on the structure of [L2] while
    generalizing [p1], [p2] and [L1], whose value evolves
    throughout the recursive calls.

    Hint: use [xchange (MList_if p2)] to exploit the lemma
    [MList_if] for the second list.

    Hint: use [rew_list] to normalize the expression [rev (x::L2')++L1].
    (Alternatively, use [rewrite rev_cons,app_last_l].) *)

(* SOLUTION *)
Lemma Triple_mrev_append : forall (p1 p2:loc) (L1 L2:list int),
  TRIPLE (mrev_append p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (r:loc) => r ~> MList (rev L2 ++ L1)).
Proof using.
  intros. gen p1 p2 L1. induction_wf IH: list_sub L2.
  xwp. xchange (MList_if p2). xif; intros C; case_if; xpull.
  { intros ->. xval. rew_list. xsimpl. }
  { intros x q L2' ->. xapp. xapp.
    xchange <- MList_cons. xapp. { auto. }
    intros r. rew_list. xsimpl. }
Qed.

Hint Extern 1 (Register_Spec mrev_append) => Provide Triple_mrev_append.
(* /SOLUTION *)

(** [] *)

(** Make sure to include the following command to enable reasoning
    about the call to [mrev_append] from the proof of [mrev].
[[
  Hint Extern 1 (Register_Spec mrev_append) => Provide Triple_mrev_append.
]]
*)

(* EX1! (Triple_mrev) *)
(** Verify [mrev]. *)

Lemma Triple_mrev : forall (p:loc) (L:list int),
  TRIPLE (mrev p)
    PRE (p ~> MList L)
    POST (fun (r:loc) => r ~> MList (rev L)).
Proof using. (* ADMITTED *)
  intros. xwp. xchange MList_nil_intro. xapp. rew_list. xsimpl.
Qed. (* /ADMITTED *)

(** [] *)

Hint Extern 1 (Register_Spec mrev) => Provide Triple_mrev.
