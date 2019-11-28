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

Definition head : field := 0%nat.
Definition tail : field := 1%nat.


Notation "l `. f '~~>' V" := ((l,f) ~> Hfield V)
  (at level 32, f at level 0, no associativity,
   format "l `. f  '~~>'  V") : heap_scope.

(*
Definition loc_field (p:loc) (k:field) : loc :=
  (p+k)%nat.

Notation "p `. k" := (loc_field p k) 
  (at level 31, format "p `. k") : fields_scope.

Definition val_field (k:field) : val :=
  VFun 'p :=
    val_ptr_add 'p (nat_to_Z k).

(*
Notation "p ''`.' k" := (trm_app (val_field k) p) 
  (at level 31, format "p ''`.' k") : trm_scope.
*)

Notation "t ''.' k" := (trm_app (val_field k) t)
  (at level 66, k at level 0, format "t ''.' k" ) : trm_scope.
*)



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
  | x::L' => \exists q, (p`.head ~~> x) \* (p`.tail ~~> q) \* (q ~> MList L')
  end.


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


(* ******************************************************* *)
(** *** Allocation of a new cell *)

(**
[[
    let rec mcell x q =
      { head = x; tail = q }
]]
*)

Definition mcell : val :=
  VFun 'x 'q :=
    Let 'p := val_alloc ((2%nat):int) in
    Set 'p'.head ':= 'x ';
    Set 'p'.tail ':= 'q ';
    'p.

(*
Ltac xwp_simpl ::= (* todo *)
  cbn beta delta [
  LibList.combine
  List.rev Datatypes.app List.fold_right List.map
  Wpgen Wpaux_getval Wpaux_getval_typed
  Wpaux_apps Wpaux_constr Wpaux_var Wpaux_match
  hforall_vars forall_vars
  trm_case trm_to_pat patvars patsubst combiner_to_trm
  Ctx.app Ctx.empty Ctx.lookup Ctx.add
  Ctx.rem Ctx.rem_var Ctx.rem_vars isubst
  var_eq eq_var_dec
  string_dec string_rec string_rect
  sumbool_rec sumbool_rect
  Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
  Bool.bool_dec bool_rec bool_rect  Wpaux_getval ] iota zeta; simpl.
*)


Hint Extern 1 (Register_Spec (val_get_field _)) => Provide Triple_get_field.
Hint Extern 1 (Register_Spec (val_set_field _)) => Provide Triple_set_field.
Ltac xapp_record tt ::= fail.

Lemma Triple_mcell : forall (x:int) (q:loc),
  TRIPLE (mcell ``x ``q)
    PRE \[] 
    POST (fun (p:loc) => (p`.head ~~> x) \* (p`.tail ~~> q)).
Proof using.
  (* TODO: cleanup alloc *)
  xwp. xapp. { math. } intros p _. rewrite abs_nat.
  do 2 rewrite Alloc_succ_eq. rewrite Alloc_zero_eq. xpull ;=> v1 v2.
  xapp. 
Admitted.

Hint Extern 1 (Register_Spec mcell) => Provide Triple_mcell.



(* ******************************************************* *)
(** *** Functions [mcons] and [mnil] *)

Definition mcons : val := mcell.

Lemma Triple_mcons : forall (x:int) (q:loc) (L:list int),
  TRIPLE (mcons ``x ``q)
    PRE (q ~> MList L)
    POST (fun (p:loc) => p ~> MList (x::L)).
Proof using.
  intros. unfold mcons. xapp ;=> p. xchange <- MList_cons. xsimpl.
Qed.

Hint Extern 1 (Register_Spec mcons) => Provide Triple_mcons.

(**
[[
    let rec mnil () =
      null
]]
*)

Definition mnil : val :=
  VFun 'u :=
    null.

Lemma Triple_mnil :
  TRIPLE (mnil '())
    PRE \[] 
    POST (fun (p:loc) => p ~> MList nil).
Proof using.
  xwp. xval. rewrite MList_nil. xsimpl. auto.
  (* alternative: xchange <- (MList_nil null). auto. xsimpl. *)
Qed.

Hint Extern 1 (Register_Spec mnil) => Provide Triple_mnil.


(* ******************************************************* *)
(** *** Functions [mhead] and [mtail] *)

(**
[[
    let rec mhead p =
      p.head
]]
*)

Definition mhead : val :=
  VFun 'p :=
    'p'.head.

Lemma Triple_mhead : forall (p:loc) (x:int) (L:list int),
  TRIPLE (mhead p)
    PRE (p ~> MList (x::L))
    POST (fun (r:int) => \[r = x] \* (p ~> MList (x::L))).
Proof using.
  xwp. xchange MList_cons. intros q.
  xapp. xchange <- MList_cons. xsimpl. auto.
Qed.

Hint Extern 1 (Register_Spec mhead) => Provide Triple_mhead.

(**
[[
    let rec mtail p =
      p.tail
]]
*)

Definition mtail : val :=
  VFun 'p :=
   'p'.tail.

Lemma Triple_mtail : forall (p:loc) (x:int) (L:list int),
  TRIPLE (mtail p)
    PRE (p ~> MList (x::L))
    POST (fun (q:loc) => (p`.head ~~> x) \* (p`.tail ~~> q) \* (q ~> MList L)).
Proof using.
  xwp. xchange MList_cons. intros q. xapp. xsimpl. 
Qed.

Hint Extern 1 (Register_Spec mtail) => Provide Triple_mtail.


(* ******************************************************* *)
(** *** Exercises: alternative specifications for [mhead] and [mtail] *)

(* exo *)

Lemma Triple_mhead' : forall (p:loc) (L:list int),
  L <> nil ->
  TRIPLE (mhead p)
    PRE (p ~> MList L)
    POST (fun (x:int) => \exists L', \[L = x::L'] \* (p ~> MList L)).
Proof using.
  introv HL. 
  (* Case analysis on [L]. The tactic [tryfalse] is short for [try contradiction] *)
  destruct L as [|x L']. { contradiction. }
  dup. (* let's duplicate the proof obligation to see two ways to prove it *) 
  { (* proof by invoking [Triple_mhead] *)
  xapp. xsimpl. eauto. }
  { (* proof by unfolding the code *) 
    xwp. xchange MList_cons. intros q. xapp. xchange <- MList_cons. xsimpl. eauto. }
Qed.

Lemma Triple_mtail' : forall (p:loc) (L:list int),
  L <> nil ->
  TRIPLE (mtail p)
    PRE (p ~> MList L)
    POST (fun (q:loc) => \exists x L', (p`.head ~~> x) \* (p`.tail ~~> q) \* (q ~> MList L')).
Proof using.
  introv HL. destruct L as [|x L']. { contradiction. }
  xapp. xsimpl. (* invoking the specification of [Triple_mtail]. *)
  (* alternative: xwp. xchange MList_cons. intros q. xapp. xsimpl. *)
Qed.



(* ******************************************************* *)
(** *** Unfolding lemma [MList_if] to reason about testing against [null] *)

(** The definition of [MList] performs a case analysis on whether 
    the logical list [L] is [nil] or not. Yet, programs perform a 
    case analysis on whether the pointer [p] on the list is [null] or not. 

    The following lemma reformulates the definition of [MList] using
    a case analysis on whether [MList] is null on not. It turns out
    to be very handy for reasoning about list-manipulating programs. *)

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


(* ******************************************************* *)
(** *** Length of a mutable list *)

(* TODO *)

Lemma Triple_eq_loc : forall (v1 v2 : loc),
  Triple (val_eq ``v1 ``v2)
    \[]
    (fun (b:bool) => \[b = isTrue (v1 = v2)]).
Proof using. intros. xapp~ (@Triple_eq loc). xsimpl*. Qed.

Hint Extern 1 (Register_Spec (val_prim val_eq)) => Provide Triple_eq_loc.

Lemma Triple_neq_loc : forall (v1 v2 : loc),
  Triple (val_neq ``v1 ``v2)
    \[]
    (fun (b:bool) => \[b = isTrue (v1 <> v2)]).
Proof using. intros. xapp~ (@Triple_neq loc). xsimpl*. Qed.

Hint Extern 1 (Register_Spec (val_prim val_neq)) => Provide Triple_neq_loc.



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
    If_ 'p '= ``null
      Then 0
      Else 1 '+ 'f ('p'.tail).

Lemma Triple_mlength : forall (p:loc) (L:list int),
  TRIPLE (mlength p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  (* Well-founded induction over the structure of the list [L],
     which provides an induction principle for the tail of [L].
     More precisely, the induction principle holds for a list 
     [L'] such that [list_sub L' L], where [list_sub] is 
     an inductive defined with a single constructor [list_sub L' (x::L')]. *)
  intros. gen p. induction_wf: list_sub_wf L. intros.
  xwp. xapp.
  (* Critical step is to reformulate [MList] using lemma [MList_if] to make
     the case analysis on the condition [p = null] visible. *)
  xchange MList_if. xif; intros C; case_if; xpull.
  { (* case [p = null]. *)
    intros ->. xval. xchange <- (MList_nil p). { auto. }
    (* justify that [length nil = 0] *)
    xsimpl. rew_list. math. }
  { (* case [p <> null]. *)
     intros x q L' ->. xapp.
     (* recursive call, exploit [IH], justifying [L'] sublist of [x::L']. *)
     xapp. { auto. } 
     (* justify that [length (x::L') = 1 + length L'] *)
     xapp. xchanges <- MList_cons. rew_list. math. }
Qed.

Lemma Triple_mlength_concise : forall (p:loc) (L:list int),
  TRIPLE (mlength p)
    PRE (p ~> MList L)
    POST (fun (r:int) => \[r = length L] \* p ~> MList L).
Proof using.
  intros. gen p. induction_wf: list_sub_wf L. intros.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros ->. xval. xchanges* <- MList_nil. }
  { intros x q L' ->. xapp. xapp*. xapp. xchanges* <- MList_cons. }
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
      Set 'p'.head ':= (('p'.head) '+ 1) '; (* todo : fix parsing *)
      'f ('p'.tail)
    ) End.

Lemma Triple_mlist_incr : forall (p:loc) (L:list int),
  TRIPLE (mlist_incr ``p)
    PRE (p ~> MList L)
    POST (fun (r:unit) => p ~> MList (LibList.map (fun x => x+1) L)).
Proof using.
  intros. gen p. induction_wf: list_sub_wf L.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull. 
  { intros x p' L' ->. xapp. xapp. xapp. xapp. xapp. { auto. }
    xchange <- MList_cons. xsimpl.
    (* short version: [xchanges* <- MList_cons] *) }
  { intros ->. xval.
    xchange <- (MList_nil p). { auto. } xsimpl. 
    (* short version: [xchanges* <- MList_nil] *)  }
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
      Else mcons ('p'.head) ('f ('p'.tail)).

Lemma Triple_copy : forall (p:loc) (L:list int),
  TRIPLE (copy ``p)
    PRE (p ~> MList L)
    POST (fun (p':loc) => (p ~> MList L) \* (p' ~> MList L)).
Proof using.
  intros. gen p. induction_wf IH: list_sub_wf L.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros ->. xapp. xsimpl. xchanges* <- MList_nil. }
  { intros x q L' ->. xapp. xapp. xapp. { auto. } intros q'.
    xapp. intros p'. xchanges <- MList_cons. }
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
    'ref (mnil '()).

Lemma Triple_create :
  TRIPLE (create '())
    PRE \[]
    POST (fun (q:loc) => q ~> Stack nil).
Proof using.
  xwp. xapp. intros p. xapp.
  intros q. xchange <- Stack_eq. xsimpl.
Qed.

(* Note: shorter version for the last line: [xchanges <- Stack_eq]. *)

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
  VFun 'q 'x :=
    'q ':= mcons 'x ('!'q).

Lemma Triple_push : forall (q:loc) (x:int) (L:list int),
  TRIPLE (push q x)
    PRE (q ~> Stack L)
    POST (fun (r:unit) => q ~> Stack (x::L)).
Proof using.
  xwp. xchange Stack_eq. intros p.
  xapp. xapp. intros p'. xapp.
  xchange <- Stack_eq. xsimpl.
Qed.

(* Note: shorter version for the last line: [xchanges <- Stack_eq]. *)

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
    'x.

Lemma Triple_pop_from_cons : forall (q:loc) (x:int) (L:list int),
  TRIPLE (pop q)
    PRE (q ~> Stack (x::L))
    POST (fun (r:int) => \[r = x] \* q ~> Stack L).
Proof using.
  xwp. xchange Stack_eq. intros p.
  xapp. xapp. xapp. intros p'. xapp. xval.
  xchange <- Stack_eq. xsimpl. auto.
Qed.

(* Note: shorter version for the last line: [xchanges* <- Stack_eq]. *)

Lemma Triple_pop : forall (q:loc) (L:list int),
  L <> nil ->
  TRIPLE (pop q)
    PRE (q ~> Stack L)
    POST (fun (x:int) => \exists L', \[L = x::L'] \* q ~> Stack L').
Proof using.
  introv HL. destruct L as [|x L']; [contradiction|].
  xwp. xchange Stack_eq. intros p. xapp. xapp.
  xapp. intros p'. xapp. xval.
  xchange <- Stack_eq. xsimpl. auto.
Qed.

Hint Extern 1 (Register_Spec pop) => Provide Triple_pop.



(* ####################################################### *)
(** * Additional contents *)

(* ******************************************************* *)
(** *** Exercise: specialization of [mcons] to a [null] tail *)

(* exo : *)

Lemma Triple_mcons_null : forall (x:int),
  TRIPLE (mcons x null)
    PRE \[] 
    POST (fun (p:loc) => p ~> MList (x::nil)).
Proof using.
  intros. xtriple. xchange <- (MList_nil null). { auto. }
  xapp. intros p. xsimpl.
Qed.


(* ******************************************************* *)
(** *** Exercise: out-of-place append of two mutable lists *)

(**
[[
    let rec mappend_copy p1 p2 =
      if p1 == null then copy p2 else begin
        let p = mappend_copy p1.tail p2 in
        mcons p1.head p
      end
]]
*)

Definition mappend_copy : val :=
  VFix 'f 'p1 'p2 :=
    If_ 'p1 '= null Then copy 'p2 Else (
      Let 'p := 'f ('p1'.tail) 'p2 in
      mcons ('p1'.head) 'p
    ).

Lemma Triple_mappend_copy : forall (p1 p2:loc) (L1 L2:list int),
  TRIPLE (mappend_copy p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (p:loc) => p ~> MList (L1++L2) 
                      \* p1 ~> MList L1 \* p2 ~> MList L2).
Proof using.
  intros. gen p1. induction_wf: list_sub_wf L1.
  xwp. xapp. xchange (MList_if p1). xif; intros C; case_if; xpull.
  { intros ->. xapp. xsimpl. xchanges* <- MList_nil. }
  { intros x q L' ->. xapp. xapp. { auto. } intros q'.
    xapp. xapp. intros p'. xchanges <- MList_cons. }
Qed.


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
      Let 'x := 'p'.head in
      Let 'q2 := 'f ('p'.tail) in
      If_ 'x '= 0 Then 'q2 Else (mcons 'x 'q2)
    ).

Lemma Triple_mcopy_nonneg : forall (p:loc) (L:list int),
  TRIPLE (mcopy_nonneg p)
    PRE (p ~> MList L)
    POST (fun (p2:loc) => p ~> MList L \* p2 ~> MList (LibList.filter (<> 0) L)).
Proof using.
  intros. gen p. induction_wf IH: list_sub_wf L. intros.
  xwp. xapp. xchange MList_if. xif; intros C; case_if; xpull.
  { intros ->. xapp. xsimpl. xchanges* <- MList_nil. }
  { intros x q L' ->. xapp. xapp. xapp. { auto. } intros q'.
    xchange <- MList_cons.
    xapp (@Triple_eq int). auto. (* TODO: fix *) 
    rewrite filter_cons. xif; intros Cx; case_if as Cx'. 
    { xval. xsimpl. }
    { xapp. intros p2. xsimpl. } }
Qed.

(* TODO: allow induction_wf to take [list_sub] as argument *)

Hint Extern 1 (Register_Spec mcopy_nonneg) => Provide Triple_mcopy_nonneg.


(* ******************************************************* *)
(** *** In-place append on lists *)

(* hard exercise *)

(**
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

Lemma Triple_mappend_aux : forall (p1 p2:loc) (L1 L2:list int),
  p1 <> null ->
  TRIPLE (mappend_aux p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (r:unit) => p1 ~> MList (L1++L2)).
Proof using.
  intros. gen p1. induction_wf IH: list_sub_wf L1.
  xwp. xchange (MList_if p1). case_if. xpull. intros x q L' ->.
  xapp. xapp. xif; intros Cq.
  { xchange (MList_if q). case_if. xpull. intros ->.
    xapp (>> (@Triple_set_field loc) q). (* TODO fix *) 
    xchange <- MList_cons. xsimpl. }
  { xapp. xapp. { auto. } { auto. }
    xchange <- MList_cons. rew_list. xsimpl. }
Qed.

Hint Extern 1 (Register_Spec mappend_aux) => Provide Triple_mappend_aux.

Lemma Triple_mappend : forall (p1 p2:loc) (L1 L2:list int),
  TRIPLE (mappend p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (p:loc) => p ~> MList (L1++L2)).
Proof using.
  xwp. xapp. xif; intros C.
  { xchange (MList_if p1). case_if. xpull. intros ->.
    xval. xsimpl. }
  { xapp. { auto. } xval. xsimpl. }
Qed.

Hint Extern 1 (Register_Spec mappend) => Provide Triple_mappend.


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

Lemma Triple_clear : forall (q:loc) (L:list int),
  TRIPLE (clear q)
    PRE (q ~> Stack L)
    POST (fun (r:unit) => q ~> Stack nil).
Proof using.
  xwp. xchange Stack_eq. intros p. xapp. intros p'.
  xapp. xchange <- Stack_eq. xsimpl.
Qed.

Hint Extern 1 (Register_Spec clear) => Provide Triple_clear.

(* Note: [\GC] plays a role here *)


(* ******************************************************* *)
(** *** Exercise: concatenation on stacks *)

(**
[[
    let rec concat q1 q2 =
      q1 := mappend !q1 !q2;
      q2 := mnil ()
]]
*)

Definition concat : val :=
  VFun 'q1 'q2 :=
    'q1 ':= mappend ('!'q1) ('!'q2) ';
    'q2 ':= mnil '().

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


(* ******************************************************* *)
(** *** Exercise: push back on stacks *)

(** Note: [L&x] is a notation for [L++x::nil]. *)

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

Lemma Triple_push_back : forall (q:loc) (x:int) (L:list int),
  TRIPLE (push_back q x)
    PRE (q ~> Stack L)
    POST (fun (_:unit) => q ~> Stack (L++x::nil)).
Proof using.
  xwp. xchange Stack_eq. intros p. 
  xapp. intros p0. xapp. intros p1. 
  xapp. xchange <- MList_cons. xapp. intros p2.
  xapp. xchange <- Stack_eq. xsimpl.
Qed.


(* ******************************************************* *)
(** *** Exercise: in-place reverse on lists *)

(* hard *)

(** [p1] denotes cells already reversed, [p2] the ones remaining to reverse 
[[
    let mrev_aux p1 p2 =
      if p2 == null then p1 else begin
        let q = p2.tail in
        p2.tail <- p1;
        mrev_aux p2 q
      end

    let mrev p =
      mrev_aux null p
]]
*)

Definition mrev_aux : val :=
  VFix 'f 'p1 'p2 :=
    If_ 'p2 '= null Then 'p1 Else (
      Let 'q := 'p2'.tail in
      Set 'p2'.tail ':= 'p1 ';
      'f 'p2 'q
    ).

Definition mrev : val :=
  VFun 'p :=
    mrev_aux null 'p.

Lemma Triple_mrev_aux : forall (p1 p2:loc) (L1 L2:list int),
  TRIPLE (mrev_aux p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (r:loc) => r ~> MList (rev L2 ++ L1)).
Proof using.
  (* important: need to generalize p1 and p2 *)
  intros. gen p1 p2 L1. induction_wf IH: list_sub_wf L2.
  xwp. xchange (MList_if p2). xif; intros C; case_if; xpull.
  { intros ->. xval. rew_list. xsimpl. }
  { intros x q L' ->. xapp.
    xapp (>> (@Triple_set_field loc) q). (* TODO fix ; previous contents should be at type val *) 
    xchange <- MList_cons. xapp. { auto. }
    intros r. rew_list. xsimpl. }
Qed.

Hint Extern 1 (Register_Spec mrev_aux) => Provide Triple_mrev_aux.

Lemma Triple_mrev : forall (p:loc) (L:list int),
  TRIPLE (mrev p)
    PRE (p ~> MList L)
    POST (fun (r:loc) => r ~> MList (rev L)).
Proof using.
  xwp. xchange <- (MList_nil null). { auto. } xapp. rew_list. xsimpl.
Qed.

Hint Extern 1 (Register_Spec mrev) => Provide Triple_mrev.


