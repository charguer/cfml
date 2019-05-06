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
    - a type of states, written [state],
    - a big-step evaluation judgment, written [red s1 t s2 v], asserting that,
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

(** The file [Fmap.v] contains a self-contained formalization of
    finite maps and the associated operations needed for Separation Logic.

    Locations, of type [loc], denote the addresses of allocated objects.
    Locations are a particular kind of values.

    A state is a finite map from locations to values.
      [Definition state := fmap loc val.] *)

(** The main operations and predicates on the state are as follows. *)

Check fmap_empty : state.

Check fmap_single : loc -> val -> state.

Check fmap_union : state -> state -> state.

Check fmap_disjoint : state -> state -> Prop.


(* ******************************************************* *)
(** ** Heap predicates *)

(** In Separation Logic (SL), the state is described using "heap predicates",
    which are predicate over pieces of state.
    We let [hprop] denote the type of heap predicates. *)

Definition hprop := state -> Prop.

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
  fun (s:state) => (s = fmap_empty).

Notation "\[]" := (hempty) (at level 0).

(** The pure fact predicate, written [\[P]], characterizes an empty state
    and moreover asserts that the proposition [P] is true. *)

Definition hpure (P:Prop) : hprop :=
  fun (s:state) => (s = fmap_empty) /\ P.

Notation "\[ P ]" := (hpure P) (at level 0, format "\[ P ]").

(** The singleton heap predicate, written [l ~~> v], characterizes a
    state with a single allocated cell, at location [l], storing the
    value [v]. *)

Definition hsingle (l:loc) (v:val) : hprop :=
  fun (s:state) => (s = fmap_single l v).

Notation "l '~~~>' v" := (hsingle l v) (at level 32).

(** The "separating conjunction", written [H1 \* H2], characterizes a
    state that can be decomposed in two disjoint parts, one that
    satisfies [H1], and another that satisfies [H2].
    In the definition below, the two parts are named [s1] and [s2]. *)

Definition hstar (H1 H2 : hprop) : hprop :=
  fun (s:state) => exists s1 s2, H1 s1
                              /\ H2 s2
                              /\ fmap_disjoint s1 s2
                              /\ s = fmap_union s1 s2.

Notation "H1 '\*' H2" := (hstar H1 H2) (at level 41, right associativity).

(** The existential quantifier for heap predicates, written [\exists x, H]
    characterizes a heap that satisfies [H] for some [x].
    The variable [x] has type [A], for some arbitrary type [A].

    The notation [\exists x, H] stands for [hexists (fun x => H)].
    The generalized notation [\exists x1 ... xn, H] is also available.

    The definition of [hexists] is a bit technical. It may be skipped 
    in first reading. additional explanations are given further on. *)

Definition hexists A (J:A->hprop) : hprop :=
  fun (s:state) => exists x, J x s.

Notation "'\exists' x1 .. xn , H" :=
  (hexists (fun x1 => .. (hexists (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ ' x1  ..  xn , '/ ' H ']'").

(** The "top" heap predicate, written [\Top], holds of any heap predicate.
    It plays a useful role for denoting pieces of state that needs to be discarded,
    to reflect in the logic the action of the garbage collector. *)

Definition htop : hprop :=
  fun (s:state) => True.

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







(* ####################################################### *)
(** * Additional explanations for the definition of [\exists] *)

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



(* ####################################################### *)
(** * Alterative definitions for heap predicates *)

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

*)