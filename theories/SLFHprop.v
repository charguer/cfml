(**

Separation Logic Foundations

Chapter: "Hprop".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From TLC Require Import LibCore.
From Sep Require Import Semantics.
(* TODO move *)
  Module CoercionsFromStrings.
  Coercion string_to_var (x:string) : var := x.
  End CoercionsFromStrings.
  Arguments fmap_single {A} {B}.
  Arguments fmap_union {A} {B}.
  Arguments fmap_disjoint {A} {B}.

  Import NotationForVariables NotationForTerms CoercionsFromStrings.

Close Scope fmap_scope.


(* ####################################################### *)
(** * The chapter in a rush *)

(* ******************************************************* *)
(** ** Syntax and semantics *)

(** We here assume an imperative programming language with a formal semantics.
    Such a language is described in file [Semantics.v], but we do not need to
    know about the details for now. All we need to know is that there exists:
  
    - a type of terms, written [trm],
    - a type of values, written [val],
    - a type of states, written [heap],
    - a big-step evaluation judgment, written [red h1 t h2 v], asserting that,
      starting from state [s1], the evaluation of the term [t] terminates in
      the state [s2] and produces the value [v]. *)

Check red : state -> trm -> state -> val -> Prop.

(** At this point, we don't need to know the exact grammar of terms and values.
    Let's just give one example to make things concrete. Consider the function:
      [fun x => if x then 0 else 1]. 

    In the language described in the file [Semantics.v], it can be
    written in raw syntax as: *)

Definition example_trm : trm :=
  trm_fun "x" (trm_if (trm_var "x") (trm_val (val_int 0)) (trm_val (val_int 1))).

(** Thanks to a set of coercions and notation, this term can be written in a
    more readable way: *)

Definition example_trm' : trm :=
  Fun "x" :=
    If_ "x" Then 0 Else 1.


(* ******************************************************* *)
(** ** Description of the state *)

(** By convention, we use the type [state] describes a full state of memory,
    and introduce the type [heap] to describe just a piece of state. *) 

Definition heap := state.

(** The file [Fmap.v] contains a self-contained formalization of
    finite maps and the associated operations needed for Separation Logic.

    Locations, of type [loc], denote the addresses of allocated objects.
    Locations are a particular kind of values.

    A state is a finite map from locations to values.
      [Definition state := fmap loc val.] *)

(** The main operations and predicates on the state are as follows. *)

Check fmap_empty : heap.

Check fmap_single : loc -> val -> heap.

Check fmap_union : heap -> heap -> heap.

Check fmap_disjoint : heap -> heap -> Prop.


(* ******************************************************* *)
(** ** Heap predicates *)

(** In Separation Logic (SL), the state is described using "heap predicates",
    which are predicate over pieces of state.
    We let [hprop] denote the type of heap predicates. *)

Definition hprop := heap -> Prop.

(** Thereafter, we use the words "heap" and "state" interchangeably,
    and let [H] range over heap predicates. *)

Implicit Type H : hprop.

(** An essential aspect of Separation Logic is that all heap predicates
    defined and used in practice are built using a few basic combinators.
    In other words, except for the definition of the combinators themselves,
    we will never define a custom heap predicate directly as a function 
    of the state. *)

(** We next describe the most important combinators of Separation Logic. *)

(** The heap predicate, written [\[]], characterizes an empty state. *)

Definition hempty : hprop :=
  fun (h:heap) => (h = fmap_empty).

Notation "\[]" := (hempty) (at level 0).

(** The pure fact predicate, written [\[P]], characterizes an empty state
    and moreover asserts that the proposition [P] is true. *)

Definition hpure (P:Prop) : hprop :=
  fun (h:heap) => (h = fmap_empty) /\ P.

Notation "\[ P ]" := (hpure P) (at level 0, format "\[ P ]").

(** The singleton heap predicate, written [l ~~> v], characterizes a
    state with a single allocated cell, at location [l], storing the
    value [v]. *)

Definition hsingle (l:loc) (v:val) : hprop :=
  fun (h:heap) => (h = fmap_single l v).

Notation "l '~~~>' v" := (hsingle l v) (at level 32).

(** The "separating conjunction", written [H1 \* H2], characterizes a
    state that can be decomposed in two disjoint parts, one that
    satisfies [H1], and another that satisfies [H2].
    In the definition below, the two parts are named [s1] and [s2]. *)

Definition hstar (H1 H2 : hprop) : hprop :=
  fun (h:heap) => exists h1 h2, H1 h1
                              /\ H2 h2
                              /\ fmap_disjoint h1 h2
                              /\ h = fmap_union h1 h2.

Notation "H1 '\*' H2" := (hstar H1 H2) (at level 41, right associativity).

(** The existential quantifier for heap predicates, written [\exists x, H]
    characterizes a heap that satisfies [H] for some [x].
    The variable [x] has type [A], for some arbitrary type [A].

    The notation [\exists x, H] stands for [hexists (fun x => H)].
    The generalized notation [\exists x1 ... xn, H] is also available.

    The definition of [hexists] is a bit technical. It may be skipped 
    in first reading. additional explanations are given further on. *)

Definition hexists A (J:A->hprop) : hprop :=
  fun (h:heap) => exists x, J x h.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ ' x1  ..  xn , '/ ' H ']'").

(** The "top" heap predicate, written [\Top], holds of any heap predicate.
    It plays a useful role for denoting pieces of state that needs to be discarded,
    to reflect in the logic the action of the garbage collector. *)

Definition htop : hprop :=
  fun (h:heap) => True.

Notation "\Top" := (htop).


(* ******************************************************* *)
(** ** Type and syntax for postconditions *)

(** A postcondition characterizes both an output value and an output state.
    In SL, a postcondition is thus a relation of type [val -> state -> Prop],
    which is equivalent to [val -> hprop]. 

    Thereafter, we let [Q] range over postconditions. *)

Implicit Type Q : val -> hprop.

(** One common operation is to augment a postcondition with a piece of state.
    This operation is described by the operator [Q \*+ H], which is just a
    convenient notation for [fun x => (Q x \* H)]. *)

Notation "Q \*+ H" := (fun x => hstar (Q x) H) (at level 40).


(* ******************************************************* *)
(** ** Separation Logic triples and the frame rule *)

(** A Separation Logic triple is a generalization of a Hoare triple
    that integrate builtin support for the "frame rule". Before we give
    the definition of a Separation Logic triple, let us first give
    the definition of a Hoare triple and state the much-desired frame rule. *)

(** A Hoare triple, written [{H}t{Q}] on paper, and here written
    [Hoare_triple t H Q], asserts that starting from a state [s] satisfying
    the precondition [H], the term [t] evaluates to a value [v] and to
    a state [s'] that, together, satisfy the postcondition [Q]. Formally: *)

Definition Hoare_triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (s:state), H s ->
  exists v s', red s t s' v /\ Q v s'.

(** Remark: [Q] has type [val->hprop], thus [Q v] has type [hprop].
    Recall that [hprop = heap->Prop], thus [Q v s'] has type [Prop]. *)

(** The frame rule asserts that if one can derive a specification of
    the form [triple H t Q] for a term [t], then one should be able
    to automatically derive [triple (H \* H') t (Q \*+ H')] for any [H'].
    Intuitively, if [t] executes safely in a heap [H], it should behave
    similarly in any extension of [H] with a disjoint part [H'], moreover
    its evaluation should leave this piece of state [H'] unmodified until
    the end. 

    The following definition of a Separation Logic triple builds upon
    that of a Hoare triple by "baking in" the frame rule. *)

Definition SL_triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), Hoare_triple t (H \* H') (Q \*+ H').

(** This definition inherently satisfies the frame rule.
    To carry out the proof, the only fact that we need to exploit
    is the associativity of the star operator, which we will 
    establish in the next chapter. *)

Parameter hstar_assoc : forall H1 H2 H3,
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).

Lemma SL_frame_rule : forall t H Q H', 
  SL_triple t H Q ->
  SL_triple t (H \* H') (Q \*+ H').
Proof using.
  introv M. unfold SL_triple in *. rename H' into H1. intros H2.
  specializes M (H1 \* H2).
  (* [M] matches the goal up to rewriting for associativity. *)
  applys_eq M 1 2.
  { rewrite hstar_assoc. auto. }
  { applys fun_ext_1. intros v. rewrite hstar_assoc. auto. }
Qed.

(** The actual definition of a Separation Logic triple accounts
    for the fact that pieces of heap may need to get discarded.
    To that end, we augment the postcondition with a [\Top], 
    which can capture any piece of state that we do not wish to
    mention explicitly in the postcondition. *)

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall (H':hprop), Hoare_triple t (H \* H') (Q \*+ H' \*+ \Top).

(** Depending on the exact set up of the Separation Logic,
    this [\Top] predicate may be replaced by a finer-grained
    definition (so as to obtain a linear or partially-linear,
    logic, instead of a fully affine logic). This distinction 
    is the matter of a more advanced chapter. *)

(* EX1! (rule_frame) *)
(** Prove the frame rule for the actual definition of [triple]. *)

Lemma rule_frame : forall t H Q H', 
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').
Proof using.
(* SOLUTION *)
  introv M. unfold SL_triple in *. rename H' into H1. intros H2.
  specializes M (H1 \* H2). applys_eq M 1 2.
  { rewrite hstar_assoc. auto. }
  { applys fun_ext_1. intros v. repeat rewrite hstar_assoc. auto. }
(* /SOLUTION *)
Qed.


(* ####################################################### *)
(** * Additional notation, explanations and lemmas *)

(* ******************************************************* *)
(** ** Notation for heap union *)

Notation "h1 \u h2" := (fmap_union h1 h2) (at level 37, right associativity).


(* ******************************************************* *)
(** ** Introduction and inversion lemmas for basic operators *)

(** The following lemmas help getting a better understanding
    of the meaning of the Separation Logic combinators. *)

Implicit Types P : Prop.

(** Introduction lemmas: how to prove goals of the form [H h]. *)

Lemma hempty_intro :
  \[] fmap_empty.
Proof using. hnf. auto. Qed.

Lemma hpure_intro : forall P,
  P ->
  \[P] fmap_empty.
Proof using. introv M. hnf. auto. Qed.

Lemma hsingle_intro : forall l v,
  (l ~~~> v) (fmap_single l v).
Proof using. intros. hnf. auto. Qed.

Lemma hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  fmap_disjoint h1 h2 ->
  (H1 \* H2) (h1 \u h2).
Proof using. intros. exists~ h1 h2. Qed.

Lemma hexists_intro : forall A (x:A) (J:A->hprop) h,
  J x h ->
  (\exists x, J x) h.
Proof using. introv M. hnf. eauto. Qed.

Lemma htop_intro : forall h,
  \Top h.
Proof using. intros. hnf. auto. Qed.

(** Inversion lemmas: how to extract information from hypotheses
    of the form [H h].*)

Lemma hempty_inv : forall h,
  \[] h ->
  h = fmap_empty.
Proof using. introv M. hnf in M. auto. Qed.

Lemma hpure_inv : forall P h,
  \[P] h ->
  P /\ h = fmap_empty.
Proof using. introv M. hnf in M. autos*. Qed.

Lemma hsingle_inv: forall l v h,
  (l ~~~> v) h ->
  h = fmap_single l v.
Proof using. introv M. hnf in M. auto. Qed.

Lemma hstar_inv : forall H1 H2 h,
  (H1 \* H2) h ->
  exists h1 h2, H1 h1 /\ H2 h2 /\ fmap_disjoint h1 h2 /\ h = h1 \u h2.
Proof using. introv M. hnf in M. eauto. Qed.

Lemma hexists_inv : forall A (J:A->hprop) h,
  (\exists x, J x) h ->
  exists x, J x h.
Proof using. introv M. hnf in M. eauto. Qed.

Lemma htop_inv : forall h, (* lemma with no interest *)
  \Top h ->
  True.
Proof using. intros. auto. Qed.


(* ******************************************************* *)
(** ** Additional explanations for the definition of [\exists] *)

(** The heap predicate [\exists (n:int), l ~~~> (val_int n)] characterizes
    a state that contains a single memory cell, at address [l], storing
    the integer value [n], for "some" (unspecified) integer [n]. *)

Module HexistsExample.
  Parameter (l:loc).
  Check (\exists (n:int), l ~~~> (val_int n)) : hprop.
End HexistsExample.

(** The type of [\exists], which operates on [hprop], is very similar 
    to that of [exists], which operates on [Prop]. 

    The notation [exists x, P] stands for [ex (fun x => P)],
    where [ex] admits the following type: *)

Check ex : forall A : Type, (A -> Prop) -> Prop.

(** Likewise, [\exists x, H] stands for [hexists (fun x => H)],
    where [hexists] admits the following type: *)

Check hexists : forall A : Type, (A -> hprop) -> hprop.

(** Remark: the notation for [\exists] is directly adapted from that 
    of [exists], which supports the quantification an arbitrary number
    of variables, and is defined in [Coq.Init.Logic] as follows. *)

Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists' '/ ' x .. y , '/ ' p ']'").


(* ******************************************************* *)
(** ** Example of triples *)

(** Assume a function called [incr] that increments the contents
    of a memory cell. *)

Parameter incr : val.

(** An application of [incr] is a term of the form 
    [trm_app (trm_val incr) (trm_val (val_loc p))].
    Because [trm_app], [trm_val], and [val_loc] are registered as
    coercions, it may be abbreviated as just [incr p].  *)

Lemma incr_applied : forall (p:loc) (n:int),
    trm_app (trm_val incr) (trm_val (val_loc p))
  = incr p.
Proof using. reflexivity. Qed.

(** A specification lemma for [incr] takes the form [triple (incr p) H Q].
    The precondition [H] is of the form [p ~~~> n], describing the 
    existence of a single memory cell at location [p] with contents [n].
    The postcondition is of the form [fun v => H'], where [v] denotes
    the result and [H'] the output state.

    Here, the result value is unit, written [val_unit]. We employ the pure
    fact predicate [\[v = val_unit]] to assert this equality. 
  
    The output state is described by [p ~~~> (n+1)], describing the
    updated contents of the memory cell at location [p]. *)

Parameter triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1))).


(* ******************************************************* *)
(** ** Example of application of the frame rule *)

(** The frame rule asserts that a triple that is true remains
    true in any extended heap.

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
  lets N: rule_frame (q ~~~> m) M.
  applys_eq N 1 2.
  { auto. }
  { apply fun_ext_1. intros v. rewrite hstar_assoc. auto. }
Qed.

(* Here, we have framed on [q ~~~> m], but we could similarly
   frame on any heap predicate [H], as captured by the following
   specification lemma. *)

Parameter rule_incr_3 : forall (p:loc) (n:int) (H:hprop),
  triple (incr p)
    ((p ~~~> n) \* H)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1)) \* H).

(** Remark: in practice, we always prefer writing
    "small-footprint specifications" (such as [triple_incr])
    that describe the minimal piece of state necessary for
    the function to execute. Indeed, other specifications that 
    describe a larger piece of state can be derived by simple
    application of the frame. *)


(* ####################################################### *)
(** * Alternative definitions *)

(* ******************************************************* *)
(** ** Alternative definitions for heap predicates *)

(** In what follows, we discuss alternative, equivalent defininitions for
    the fundamental heap predicates. We write these equivalence using 
    equalities of the form [H1 = H2]. We will justify later the use of 
    the equal sign for relating predicates. *)

(** The empty heap predicate [\[]] is equivalent to the pure fact predicate
    [\[True]]. Thus, [hempty] could be defined in terms of [hpure]. *)

Parameter hempty_eq_hpure_true :
  \[] = \[True].

Definition hempty' : hprop :=
  \[True].

(** The pure fact predicate [[\P]] is equivalent to the existential
    quantification over a proof of [P] in the empty heap, that is,
    to the heap predicate [\exists (p:P), \[]]. Thus, [hpure] could
    be defined in terms of [hexists] and [hempty]. *)

Parameter hpure_eq_hexists_proof : forall P,
  \[P] = \[True].

Definition hpure' (P:Prop) : hprop :=
  \exists (p:P), \[].

(** We like to reduce the number of combinators to the minimum number,
    both for elegance and to reduce the subsesquent proof effort.
    Since we cannot do without [hexists], we have a choice between
    considering either [hpure] or [hempty] as primitive, and the other
    one as derived. The predicate [hempty] is simpler and appears as
    more fundamental. Hence, in practice we define [hpure] in terms of
    [hexists] and [hempty], as done in the definition [hpure'] above. *)

(** The top heap predicate [\Top] is equivalent to [\exists H, H], 
    which is a heap predicate that also characterizes any state.
    Again, because we need [hexists] anyway, we prefer in practice
    to define [\Top] in terms of [hexists], as done in the definition
    of [htop'] shown below. *)

Parameter htop_eq_hexists_hprop :
  \Top = (\exists (H:hprop), H).

Definition htop' : hprop :=
  \exists (H:hprop), H.


(* ******************************************************* *)
(** ** Alterative definitions for SL triples *)

(** We have previously defined [SL_triple] on top of [Hoare_triple],
    with the help of the separating conjunction operator, as:
    [forall (H':hprop), Hoare_triple (H \* H') t (Q \*+ H')].

    In what follows, we give an equivalent characterization, 
    expressed directly in terms of heaps and heap unions. 
    It asserts that if [h1] satisfies the precondition [H]
    and [h2] describes the rest of the state, then the evaluation
    of [t] produces a value [v] in a final state made that 
    can be decomposed between a part [h1'] and [h2] unchanged,
    in such a way that [v] and [h1'] together satisfy the 
    poscondition [Q]. *)

Definition SL_triple_lowlevel (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall h1 h2,
  fmap_disjoint h1 h2 ->
  H h1 ->
  exists v h1',
       fmap_disjoint h1' h2
    /\ red (h1 \u h2) t (h1' \u h2) v
    /\ Q v h1'.

(** Let us establish the equivalence between this alternative definition
    of [SL_triple] and the original one. *)

(* EX3! (SL_triple_iff_SL_triple_lowlevel) *)
Lemma SL_triple_iff_SL_triple_lowlevel : forall t H Q,
  SL_triple t H Q <-> SL_triple_lowlevel t H Q.
Proof using.
(* SOLUTION *)
  unfold SL_triple, SL_triple_lowlevel, Hoare_triple. iff M.
  { introv D P1.
    forwards~ (v&h'&HR&HQ): M (=h2) (h1 \u h2). { hnf. eauto 8. }
    destruct HQ as (h1'&h2'&N0&N1&N2&N3). subst.
    exists v h1'. eauto. }
  { intros H' h. introv (h1&h2&N1&N2&D&U).
    forwards~ (v&h1'&D'&HR&HQ): M h1 h2. subst.
    exists v (h1' \u h2). split. { eauto. } { hnf. eauto 8. } }
(* /SOLUTION *)
Qed.

(** Recall the final definition of [triple], as:
    [forall (H':hprop), Hoare_triple (H \* H') t (Q \*+ H' \*+ \Top)].

    This definition can also be reformulated directly in terms of union 
    of heaps. All we need to do is introduce an additional piece of 
    state to describe the part covered by new [\Top] predicate.

    In order to describe disjointness of the 3 pieces of heap that 
    describe the final state, we first introduce an auxiliary definition:
    [fmap_disjoint_3 h1 h2 h3] asserts that the three arguments denote
    pairwise disjoint heaps. *)

Definition fmap_disjoint_3 (h1 h2 h3:heap) :=
     fmap_disjoint h1 h2
  /\ fmap_disjoint h2 h3
  /\ fmap_disjoint h1 h3.

(** We then generalize the result heap from [h1' \u h2] to
    [h1' \u h2 \u h3'], where [h3'] denotes the piece of the
    final state that is described by the [\Top] heap predicate
    that appears in the definition of [triple]. *) 

Definition triple_lowlevel t H Q :=
  forall h1 h2,
  fmap_disjoint h1 h2 ->
  H h1 ->
  exists v h1' h3',
       fmap_disjoint_3 h1' h2 h3'
    /\ red (h1 \u h2) t (h1' \u h2 \u h3') v
    /\ (Q v) h1'.

(** One can proove the equivalence of [triple] and [triple_lowlevel]
    following a similar proof pattern as previously. The proof is a bit 
    more technical and requires additional tactic support to deal with
    the tedious disjointness conditions, so we omit the details. *)

Parameter triple_iff_triple_lowlevel : forall t H Q,
  triple t H Q <->triple_lowlevel t H Q.













