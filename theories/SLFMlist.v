(**

Separation Logic Foundations

Chapter: "Mlist".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import Example.
Generalizable Variables A B.

Implicit Types x n m : int.
Implicit Types p q : loc.
Implicit Types L : list int.


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
    - [xunfold], a CFML tactic for unfolding the definition of [MList].
    - examples of specifications and proofs for programs manipulating mutable lists.

*)

 
(* ******************************************************* *)
(** *** Representation of a list cell as a two-field record *)

(** In the previous chapter, we have only manipulated OCaml-style
    references, which correspond to a mutable record with a single 
    field (its "contents"). 

    A two-field record can be described in Separation Logic as the
    separating conjunction of two cells at consecutive addresses.

    A list cell allocated at address [p], featuring a head value [x] 
    and a tail pointer [q], can be represented as:
    [p ~~> x \* (p+1) ~~> q].

    Throughout this file, to improve clarity, we write:

    - [p`.head] as short for [p], where we intend to describe the 
      address of the head field;
    - [p`.tail] as short for [p+1], where we intend to describe the 
      address of the tail field.

    Using these notation, the list cell considered can be represented as:
    [(p`.head) ~~> x  \*  (p`.tail) ~~> q], which looks more symmetric.
*)

Definition field_head (p:loc) := (p+0)%nat.
Definition field_tail (p:loc) := (p+1)%nat.

Notation "p '`.head'" := (field_head p) 
  (at level 65, format "p '`.head'") : fields_scope.
Notation "p '`.tail'" := (field_tail p)
  (at level 65, format "p '`.tail'") : fields_scope.

(** Thus, to read in the head field of a list at address [p],
    we would write ['! p`.head], like if [p`.head] was the
    address of an individual reference cell. Likewise, 
    ['! p`.tail] denotes the contents of the tail field.

    Remark: [p`.tail] by itself denotes the address of the
    tail field, like the expression [&p->tail] in the C language. *)


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

    - The [null] pointer represents the empty list, that is, [nil].
    - A non-null pointer [p] represents a list of the form [n::L'],
      if the head field of [p] contains [n] and the tail field of [p]
      contains some pointer [q] that is the head of a linked list
      that represents the list [L'].

    For reasons that we won't detail here, the definition of the predicate
    [p ~> MList L] cannot take the form of an inductive predicate in Coq.
    Fortunately, it can very well be defined as a recursive function.

    The definition of [MList L p], a.k.a. [p ~> MList L], appears below.
    It is defined as a fixpoint over the structure of the list [L].

    - if [L] is [nil], then [p] should be [null]
    - if [L] decomposes as [n::L'], then the head field of [p] should store
      the value [n], the tail field of [p] should store some pointer [q]
      (which is existentially quantified), and [q ~> MList L'] should
      describe the remaining of the list structure.
*)

Fixpoint MList (L:list int) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists q, (p`.head ~~> x) \* (p`.tail ~~> q) \* (p' ~> MList L')
  end.


(* ******************************************************* *)
(** *** Basic properties of the mutable list predicate *)

(** To begin with, we prove two lemmas that will be helpful for manipulating
    the definition. *)

Lemma MList_nil : forall p,
  (p ~> MList nil) = \[p = null].
Proof using. intros. xunfold~ MList. Qed.

Lemma MList_cons : forall p x L',
  p ~> MList (x::L') =
  \exists p', p ~> MCell x p' \* p' ~> MList L'.
Proof using. intros. xunfold~ MList. Qed.

(** We then set [MList] as opaque to ensure that the [simpl] tactic never
    attempts to unfold the definition in an uncontrolled manner. *)

Global Opaque MList.


(* ******************************************************* *)
(** *** Allocation of a new cell *)

(**
[[
    let rec mcell x q =
      { head = x; tail = q }
]]
*)

Definition mcell : val :=
  VFfun 'x 'q :=
    Let p := val_alloc ((2%nat):int) in
    'p`.head ':= 'x ';
    'p`.tail ':= 'q ';
    'p.

Lemma Triple_mcell : forall (x:int) (q:loc),
  TRIPLE (mcell ``x ``q)
    PRE \[] 
    POST (fun (p:loc) => (p`.head ~~> x) \* (p`.tail ~~> q)).
Proof using.
  xwp. xapp. xapp. xapp. xval.
Qed.

Hint Extern 1 (Register_Spec mcell) => Provide Triple_mcell.



(* ******************************************************* *)
(** *** Functions [mcons] and [mnil] *)

Definition mcons : val := mcell.

Lemma Triple_mcons : forall (x:int) (q:loc) (L:list int),
  TRIPLE (mcons ``x ``q)
    PRE (q ~> MList L)
    POST (fun (p:loc) => p ~> MList (x::L)).
Proof using.
  unfold mcons. xapp. xchange <- (MList_cons p).
Qed.

Hint Extern 1 (Register_Spec mcons) => Provide Triple_mcons.

(**
[[
    let rec mnil () =
      null
]]
*)

Definition mnil : val :=
  VFfun 'u :=
    null.

Lemma Triple_mnil :
  TRIPLE (mnil '())
    PRE \[] 
    POST (fun (p:loc) => p ~> MList nil).
Proof using.
  xwp. xval. xchange <- (MList_nil p).
Qed.

Hint Extern 1 (Register_Spec mnil) => Provide Triple_mnil.


(* ******************************************************* *)
(** *** Exercise: specialization of [mcons] to a [null] tail *)

(* exo : *)

Lemma Triple_mcons_null : forall (x:int),
  TRIPLE (mcons ``x ``null)
    PRE \[] 
    POST (fun (p:loc) => p ~> MList (x::nil)).
Proof using.
  intros. xapp. .
Qed.



(* ******************************************************* *)
(** *** Functions [mhead] and [mtail] *)

(**
[[
    let rec mhead p =
      p.head
]]
*)

Definition mhead : val :=
  VFfun 'p :=
  '! p`.head.

Lemma Triple_mhead : forall (x:int) (L:list int),
  TRIPLE (mhead p)
    PRE (p ~> MList (x::L))
    POST (fun (r:int) => \[r = x] \* (p ~> MList (x::L)).
Proof using.
  xwp. xchange MList_cons. xapp. xapp. xapp. xval. xchange <- MList_cons. 
Qed.

Hint Extern 1 (Register_Spec mhead) => Provide Triple_mhead.

(**
[[
    let rec mtail p =
      p.tail
]]
*)

Definition mtail : val :=
  VFfun 'p :=
  '! p`.tail.

Lemma Triple_mtail : forall (x:int) (L:list int),
  TRIPLE (mtail p)
    PRE (p ~> MList (x::L))
    POST (fun (q:loc) => (p`.head ~~> x) \* (p`.tail ~~> q) \* (q ~> MList L)).
Proof using.
  xwp. xchange MList_cons. xapp. 
Qed.

Hint Extern 1 (Register_Spec mtail) => Provide Triple_mtail.


(* ******************************************************* *)
(** *** Exercises: alternative specifications for [mhead] and [mtail] *)

(* exo *)

Lemma Triple_mhead' : forall (x:int) (L:list int),
  L <> nil ->
  TRIPLE (mhead p)
    PRE (p ~> MList L)
    POST (fun (x:int) => \exists L', \[L = x::L'] \* (p ~> MList L)).
Proof using.
  intros. xapp. xapp. xapp. xval.
Qed.

Lemma Triple_mtail' : forall (x:int) (L:list int),
  L <> nil ->
  TRIPLE (mtail p)
    PRE (p ~> MList L)
    POST (fun (q:loc) => \exists x L', (p`.head ~~> x) \* (p`.tail ~~> q) \* (q ~> MList L')).
Proof using.
  xwp. xchange MList_cons. xapp. 
Qed.



(* ******************************************************* *)
(** *** Unfolding lemma [MList_if] to reason about testing against [null] *)

(** The definition of [MList] performs a case analysis on whether 
    the logical list [L] is [nil] or not. Yet, programs perform a 
    case analysis on whether the pointer [p] on the list is [null] or not. 

    The following lemma reformulates the definition of [MList] using
    a case analysis on whether [MList] is null on not. It turns out
    to be very handy for reasoning about list-manipulating programs. *)

Lemma MList_if : forall p L,
  p ~> MList L ==>
  If p = null
    then \[L = nil]
   else \exists x p' L', \[L = x::L'] \* p ~> MCell x p' \* p' ~> MList L'.
Proof using.
  intros. destruct L as [|x L'].
  { xchanges MList_nil ;=> M. case_if. xsimpl~. }
  { xchange MList_cons ;=> p'. case_if.
    { subst. xchange MCell_null. }
    { xsimpl~. } }
Qed.



(* ******************************************************* *)
(** *** Length of a mutable list *)

(**
[[
    let rec mlength p =
      if p == null
        then 0
        else 1 + mlength (tail p)
]]
*)

Definition mlength : val :=
  VFix 'f 'p :=
    If_ 'p '= null
      Then 0
      Else 1 '+ 'f ('!'p`.tail).

Lemma Triple_mlength : forall A `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (mlength ``p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  intros. gen p. induction_wf: list_sub_wf L; intros. xwp.
  xapp~. xchange MList_if. xif ;=> C; case_if; xpull.
  { intros ->. xval. xchanges* <- (MList_nil p). }
  { intros x q L' ->. xapp. xapp~. xapp. xchanges* <- (MList_cons p). }
Qed.

Hint Extern 1 (Register_Spec mlength) => Provide Triple_mlength.


(* ******************************************************* *)
(** *** Increment through a mutable list *)

(**
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
      ('!'p`.head) ':= ('!'p`.head) '+ 1 ';
      'f ('!'p`.tail)
    ) End.

Lemma Triple_mlist_incr : forall (p:loc) (L:list int),
  TRIPLE (mlist_incr ``p)
    PRE (p ~> MList L)
    POST (fun (r:unit) => p ~> MList (LibList.map (fun x => x+1) L)).
Proof using.
  intros. gen p. induction_wf: list_sub_wf L.
  xwp. xapps~. xif ;=> C.
  { xtchanges~ (MList_not_null_inv_cons p) ;=> x p' L' EL.
    xapps. xapps. xapps. xapps. xapps~.
    xchanges~ (>> MList_cons p Enc_int). }
  { subst. xtchanges MList_null_inv ;=> EL. xvals~. }
Qed.


(* ******************************************************* *)
(** *** List Copy *)

(**
[[
    let rec mcopy p =
      if p == null
        then mnil ()
        else mcons (p.head) (mcopy p.tail)
]]
*)

Definition copy : val :=
  VFix 'f 'p :=
    If_ 'p  '= null
      Then mnil '()
      Else mcons ('!'p'`.head) ('f ('!'p'`.tail)).

Lemma Triple_copy : forall (p:loc) (L:list int),
  TRIPLE (copy ``p)
    PRE (p ~> MList L)
    POST (fun (p':loc) => (p ~> MList L) \* (p' ~> MList L)).
Proof using.
  intros. gen p. induction_wf IH: list_sub_wf L. xwp.
  xapp~. xchange MList_if. xif ;=> C; case_if; xpull.
  { intros ->. xval. xchanges~ <- (MList_nil p). xchanges* <- (MList_nil null). }
  { intros x q L' ->. xapp. xapp. xapp~ ;=> q'. xapp ;=> p'.
    xchanges <- (MList_cons p). xchanges* <- (MList_cons p'). }
Qed.

Hint Extern 1 (Register_Spec copy) => Provide Triple_copy.



(* ******************************************************* *)
(** *** Representation of a mutable stack *)

(** The predicate [q ~> Stack L]  

*)

Definition Stack (L:list int) (q:loc) : hprop :=
  \exists p, (q ~~> p) \* (p ~> MList L).

Lemma Stack_eq : forall (q:loc) (L:list int),
  (q ~> Stack L) = (\exists p, (q ~~> p) \* (p ~> MList L)).
Proof using. xunfold* Stack. Qed.


(* ******************************************************* *)
(** *** Operations [create] *)

(**
[[
    let create () =
      ref (mnil())
]]
*)

Definition create : val :=
  VFun 'u :=
    ref (mnil '()).

Lemma Triple_create :
  TRIPLE (create '())
    PRE \[]
    POST (fun (q:loc) => (q ~> Stack nil).
Proof using.
  xwp. xapp. xapp. xchange <- Stack_eq.
Qed.

Hint Extern 1 (Register_Spec create) => Provide Triple_create.



(* ******************************************************* *)
(** *** Operations [push] *)

(**
[[
    let push q x =
      q := mcons x !q
]]
*)

Definition push : val :=
  VFun 'q :=
    'q ':= mcons x ('!'q).

Lemma Triple_push : forall (q:loc) (L:list int)
  TRIPLE (push q x)
    PRE (q ~> Stack L)
    POST (fun (r:unit) => q ~> Stack (x::L)).
Proof using.
  xwp. xchange Stack_eq. xapp. xapp. xchange <- Stack_eq.
Qed.

Hint Extern 1 (Register_Spec push) => Provide Triple_push.


(* ******************************************************* *)
(** *** Operations [pop] *)

(**
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
    x

Lemma Triple_pop_from_cons : forall (q:loc) (L:list int)
  TRIPLE (pop q)
    PRE (q ~> Stack (x::L))
    POST (fun (r:int) => \[r = x] \* q ~> Stack L).
Proof using.
  xwp. xchange Stack_eq. xapp. xapp. xchange <- Stack_eq.
Qed.

Lemma Triple_pop : forall (q:loc) (L:list int)
  L <> nil ->
  TRIPLE (pop q)
    PRE (q ~> Stack L)
    POST (fun (x:int) => \exists L', \[L = x::L'] \* q ~> Stack L').
Proof using.
  xwp. xchange Stack_eq. xapp. xapp. xchange <- Stack_eq.
Qed.

Hint Extern 1 (Register_Spec pop) => Provide Triple_pop.





(* ####################################################### *)
(** * Additional contents *)


(* ******************************************************* *)
(** *** Exercise: operation [clear] on stack *)

(**
[[
    let rec clear q =
      q := mnil()
]]
*)

Definition clear : val :=
  VFun 'q :=
    'q ':= mnil '().

Lemma Triple_clear : forall (q:loc) (L:list int)
  TRIPLE (clear '())
    PRE (q ~> Stack L)
    POST (fun (r:unit) => q ~> Stack nil).
Proof using.
  xwp. xchange Stack_eq. xapp. xapp. xchange <- Stack_eq.
Qed.

Hint Extern 1 (Register_Spec clear) => Provide Triple_clear.


(* ******************************************************* *)
(** *** Exercise: out-of-place filter on list *)

(**
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
      Let 'x := '!'p`.head in
      Let 'q2 := 'f ('!'p`.tail) in
      If_ 'x '= 0 Then 'q2 Else (mcons 'x 'q2)
    ).

Lemma Triple_mcopy_nonneg : forall (p:loc) (L:list int),
  TRIPLE (mcopy_nonneg p)
    PRE (p ~> MList L)
    POST (fun (p2:loc) => p ~> MList L \* p2 ~> MList (LibList.filter (<> 0) L)).
Proof using.
  intros. gen p1. induction_wf IH: (@list_sub A) L1. intros.
  xwp. xif ;=> C.
  { xchanges (MList_eq p1) ;=> v1. xchanges (MList_eq p2) ;=> v2.
    xapp. xapp. xchanges* <- (MList_eq p1). }
  { xchanges~ (MList_not_nil p1) ;=> x L1' p1' ->.
    xapp. xapp*. xchanges <- (MList_cons p1). }
Qed.

Hint Extern 1 (Register_Spec mcopy_nonneg) => Provide Triple_mcopy_nonneg.


(* ******************************************************* *)
(** *** In-place append on lists *)

(**
[[
    let rec mappend p1 p2 =
      if p1 == null then 
        p2
      else if p1.tail == null then  
        p1.tail <- p2
      else
        mappend p1.tail p2
]]
*)

Definition mappend : val :=
  VFix 'f 'p1 'p2 :=
    If_ 'p1 '= null
      Then 'p1 ':= '! 'p2
      Else 'f (tail 'p1) 'p2.

Lemma Triple_mappend : forall (p1 p2:loc) L1 L2:list int),
  TRIPLE (mappend p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (_:unit) => p1 ~> MList (L1++L2)).
Proof using.
  intros. gen p1. induction_wf IH: (@list_sub A) L1. intros.
  xwp. xif ;=> C.
  { xchanges (MList_eq p1) ;=> v1. xchanges (MList_eq p2) ;=> v2.
    xapp. xapp. xchanges* <- (MList_eq p1). }
  { xchanges~ (MList_not_nil p1) ;=> x L1' p1' ->.
    xapp. xapp*. xchanges <- (MList_cons p1). }
Qed.

Hint Extern 1 (Register_Spec mappend) => Provide @Triple_mappend.


(* ******************************************************* *)
(** *** Exercise: optimized in-place append on lists *)

(** exo :
[[
    let mappend_aux p1 p2 =
      if p1.tail == null  
        then p1.tail <- p2
        else mappend p1.tail p2

    let mappend' p1 p2 =
      if p1 == null 
        then p2 
        else mappend_aux p1 p2
]]
*)


(* ******************************************************* *)
(** *** Exercise: in-place concatenation on stacks *)

(**
[[
    let rec concat q1 q2 =
      q1 := mappend q1 q2;
      q2 := mnil ()
]]
*)

Definition concat : val :=
  VFun 'q1 'q2 :=
    'q1 ':= mappend ('!'q1) ('!'q2) ';
    'q2 ':= mnil '().

Lemma Triple_concat : forall (q1 q2:loc) (L1 L2:list int)
  TRIPLE (concat q1 q2)
    PRE (q1 ~> Stack L1 \* q2 ~> Stack L2)
    POST (fun (r:unit) => q1 ~> Stack (L1 ++ L2) \* q2 ~> Stack nil).
Proof using.
  xwp. xchange Stack_eq. xapp. xapp. xchange <- Stack_eq.
Qed.

Hint Extern 1 (Register_Spec concat) => Provide Triple_concat.


(* ******************************************************* *)
(** *** Exercise: in-place reverse on lists *)

(**
[[
    let mrev_aux p1 p2 =
      if p1 == null then p2 else begin
        let q = p1.tail in
        p1.tail <- p2;
        mrev_aux q p1
      end

    let mrev p =
      mrev_aux p null
]]
*)

Definition mrev_aux : val :=
  VFix 'f 'p1 'p2 :=
    If_ 'p1 '= null Then 'p2 Else (
      Let 'q := '!'p1`.tail in
      'p1`.tail ':= 'p2 ';
      'f 'q 'p1
    ).

Definition mrev : val :=
  VFun 'p :=
    mrev_aux 'p null.

Lemma Triple_mrev_aux : forall (p1 p2:loc) (L1 L2:list int),
  TRIPLE (Triple_mrev_aux ``p1 ``p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (r:loc) => r ~> MList (rev L1 ++ L2)).
Proof using.
Qed.

Hint Extern 1 (Register_Spec mrev_aux) => Provide Triple_mrev_aux.

Lemma Triple_mrev : forall (p:loc) (L:list int),
  TRIPLE (Triple_mrev ``p)
    PRE (p ~> MList L)
    POST (fun (r:loc) => r ~> MList (rev L)).
Proof using.
Qed.

Hint Extern 1 (Register_Spec mrev) => Provide Triple_mrev.


(* ******************************************************* *)


(**---prove as we go--

Lemma MList_null : forall (L:list int),
  (null ~> MList L) = \[L = nil].
Proof using.
  intros. destruct L.
  { rewrite MList_nil. xsimpl*. }
  { rewrite MList_cons. applys himpl_antisym. (* todo xsimpl. too much *)
    { xpull ;=> p'. xchange MCell_null. }
    { xpull. (* TODO xsimpl. pb *) } }
Qed.

Lemma MList_nil_intro :
  \[] = (null ~> MList nil).
Proof using. intros. rewrite MList_null. xsimpl*. Qed.

Lemma MList_null_inv : forall (L:list int),
  null ~> MList L ==>
  null ~> MList L \* \[L = nil].
Proof using. intros. rewrite MList_null. xsimpl*. Qed.
*)


(*

Lemma MList_not_null_inv_not_nil : forall p (L:list int),
  p <> null ->
  p ~> MList L ==> p ~> MList L \* \[L <> nil].
Proof using.
  intros. destruct L. { xchanges MList_nil. } { xsimpl*. }
Qed.

Lemma MList_not_null_inv_cons : forall p (L:list int),
  p <> null ->
  p ~> MList L ==> \exists x p' L',
       \[L = x::L']
    \* p ~> MCell x p'
    \* p' ~> MList L'.
Proof using.
  intros. xchange~ MList_not_null_inv_not_nil ;=> M.
  destruct L; tryfalse. xchanges~ MList_cons.
Qed.

Lemma MList_eq : forall (p:loc) (L:list int),
  p ~> MList L =
  match L with
  | nil => \[p = null]
  | x::L' => \exists (p':loc), (p ~> Record`{ head := x; tail := p' }) \* (p' ~> MList L')
  end.
Proof using. intros. xunfold~ MList. destruct~ L. Qed.

*)


(* ********************************************************************** *)
(* * Towards a representation *)

(* ---------------------------------------------------------------------- *)
(** ** C-style datatype *)

(** Let's try to first formalize the C representation:
[[
    typedef struct node {
      item  head;
      node* tail;
    };
    // with node = null for the empty list
]]
*)

(* ---------------------------------------------------------------------- *)
(** ** Inductive presentation (does not work) *)


(* ---------------------------------------------------------------------- *)
(** ** Recursive presentation *)

Module MListVal.


End MListVal.





(* ********************************************************************** *)
(* * Formalization of list cells *)

Notation "'MCell' x q" :=
  (Record`{ head := x; tail := q })
  (at level 19, x at level 0, q at level 0).


Lemma MCell_null : forall A `{EA:Enc A} (x:A) (p':loc),
  null ~> MCell x p' = \[False].
Proof using.
  intros. applys himpl_antisym.
  { xchange hRecord_not_null. simpl. unfold head. auto. } (* todo simplify *)
  { xpull. }
Qed.

Lemma MCell_not_null : forall (p:loc) A `{EA:Enc A} (x:A) (p':loc),
  p ~> MCell x p' ==+> \[p <> null].
Proof using.
  intros. tests C: (p = null). { xchange MCell_null. } { xsimpl~. }
Qed.

Lemma MCell_conflict : forall p1 p2 `{EA1:Enc A1} `{EA2:Enc A2} (x1 x2:A1) (y1 y2:A2),
  p1 ~> MCell x1 y1 \* p2 ~> MCell x2 y2 ==+> \[p1 <> p2].
(* TODO: two records with one common field have disjoint addresses *)
Admitted.

Arguments MCell_null : clear implicits.
Arguments MCell_not_null : clear implicits.
Arguments MCell_conflict : clear implicits.


Arguments MList_eq : clear implicits.
Arguments MList_nil : clear implicits.
Arguments MList_cons : clear implicits.
Arguments MList_null : clear implicits.
Arguments MList_nil_intro : clear implicits.
Arguments MList_null_inv : clear implicits.
Arguments MList_not_null_inv_not_nil : clear implicits.
Arguments MList_not_null_inv_cons : clear implicits.







(* ********************************************************************** *)
(* * Out-of-place append of two mutable lists *)

Definition val_mlist_append : val :=
  ValFix 'f 'p1 'p2 :=
    If_ val_eq 'p1 null Then (
      val_mlist_copy 'p2
    ) Else (
      Let 'x := val_get_hd 'p1 in
      Let 'c1 := val_get_tl 'p1 in
      Let 'p := 'f 'c1 'p2 in
      val_new_cell 'x 'p
    ).

Lemma Triple_mlist_append : forall (L1 L2:list int) (p1 p2:loc),
  TRIPLE (val_mlist_append ``p1 ``p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (p:loc) =>
         p ~> MList (L1++L2) \* p1 ~> MList L1 \* p2 ~> MList L2).
Proof using.
  intros. gen p1. induction_wf: list_sub_wf L1; intros. xcf.
  xapps~. xif ;=> C.
  { subst. xtchanges MList_null_inv ;=> EL. xapp.
    intros p. subst. rew_list. xsimpl. }
  { xtchanges~ (MList_not_null_inv_cons p1) ;=> x p1' L' EL.
    xapps. xapps. xapp~ as p'. xapps. intros p. subst. rew_list.
    xchange~ (>> MList_cons p Enc_int).
    xchanges~ (>> MList_cons p1 Enc_int). }
Qed.




Module ExoList.
Import ExampleList.MList.


(* ******************************************************* *)
(** ** Create one element *)

(**
[[
  let mk_one x =
    mk_cons x (create())
]]
*)

Definition mk_one : val :=
  VFun 'x :=
     mk_cons 'x (create '()).

Lemma Triple_mk_one : forall A `{EA:Enc A} (x:A),
  TRIPLE (mk_one ``x)
    PRE \[]
    POST (fun p => p ~> MList (x::nil)).
Proof using.
  (* SOLUTION *) intros. xwp. xapp ;=> q. xapp. xsimpl. (* /SOLUTION *)
Qed.

Hint Extern 1 (Register_Spec (mk_one)) => Provide @Triple_mk_one.


(* ******************************************************* *)
(** ** Push back using append *)

(** Note: [L&x] is a notation for [L++x::nil]. *)

(**
[[
  let push_back p x =
    inplace_append p (mk_one x)
]]
*)

(** Recall:
[[
  TRIPLE (inplace_append p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (_:unit) => p1 ~> MList (L1++L2)).
]]
*)

Definition push_back : val :=
  VFun 'p 'x :=
    inplace_append 'p (mk_one 'x).

Lemma Triple_push_back : forall `{EA:Enc A} (L:list A) (x:A) (p:loc),
  TRIPLE (push_back ``p ``x)
    PRE (p ~> MList L)
    POST (fun (_:unit) => p ~> MList (L++x::nil)).
Proof using.
  (* SOLUTION *) xwp. xapp ;=> q. xapp. xsimpl. (* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Push back not using append (blue belt) *)

(** Hint: the following function is a specialization of
    [inplace_append] for the case where the second list
    consists of a single element. Its proof is similar. *)

(**
[[
  let rec push_back' p x =
    if is_empty p
      then set_cons p x (create())
      else push_back' (tail p) x
]]
*)

Definition push_back' : val :=
  VFix 'f 'p 'x :=
    If_ is_empty 'p
      Then set_cons 'p 'x (create '())
      Else 'f (tail 'p) 'x.

Lemma Triple_push_back' : forall `{EA:Enc A} (L:list A) (x:A) (p:loc),
  TRIPLE (push_back' ``p ``x)
    PRE (p ~> MList L)
    POST (fun (_:unit) => p ~> MList (L++x::nil)).
Proof using.
  intros. gen p. induction_wf IH: (@list_sub A) L. intros.
  (* SOLUTION *)
  xwp. xif ;=> C.
  { subst. xchanges (MList_eq p) ;=> v1.
    xapp ;=> q. xapp. xchanges <- (MList_cons p). }
  { xchanges~ (MList_not_nil p) ;=> y L' p' ->.
    xapp. xapp. { auto. } xchanges <- MList_cons. }
  (* /SOLUTION *)
Qed.




