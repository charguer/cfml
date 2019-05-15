(**

Separation Logic Foundations

Chapter: "Wand".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import SepBase.
Notation "'\Top''" := hgc.



(* ####################################################### *)
(** * The chapter in a rush *)

(** This chapter introduces additional Separation Logic operators,
    most notably the "magic wand", written [H1  \-* H2].
    
    Magic wand does not only have a cool name, and it is not only
    a fascinating operator for logicians: it turns out that the 
    magic wand is a key ingredient to streamlining the process of
    practical program verification in Separation Logic. 
    
    In this chapter, we first introduce the new operators, then
    explain how they can be used to reformulate the frame rule
    and give a different presentation to Separation Logic triples. *)


(* ******************************************************* *)
(** ** The magic wand *)

(* ------------------------------------------------------- *)
(** *** A subtraction operator *)

(** At a high level, [H1 \* H2] describes the "addition" of a
    heap satisfying [H1] with a heap satisfying [H2]. 
    Think of it as [H1 + H2].

    As a counterpart to this addition operator, we introduce
    a subtraction operator, written [H1 \-* H2]. 
    Think of it as [ -H1 + H2].

    A heap [h] satisfies [H1 \-* H2] if and only if, when we augment
    it with a disjoint heap [h'] satisfying [H1], we recover [H2].
    Think of it as [(-H1 + H2) + H1] simplifying to [H2].

    The definition of [hwand] follows. *)

Definition hwand (H1 H2:hprop) : hprop :=
  fun h => forall h', fmap_disjoint h h' -> H1 h' -> H2 (h \u h').

Notation "H1 \-* H2" := (hwand H1 H2) (at level 43).

(** The definition of [hwand] is not easy to make sense of at first.
    To better grasp its meaning, we next present two alternative
    definitions of [hwand], and detail its introduction and elimination
    lemmas. *)

(** The operator [H1 \-* H2] is uniquely defined by the followig
    equivalence. In other words, any operator that satisfies this
    equivalence for all arguments is provably equal to the definition 
    of [hwand] given above. (We proof this fact further in the chapter.) *)

Parameter hwand_characterization : forall H0 H1 H2,
  (H0 ==> H1 \-* H2) <-> (H0 \* H1 ==> H2).

(** The right-to-left direction is an introduction rule: it tells
    what needs to be proved to introduce a magic wand [H1 \-* H2]
    when starting from a state described by [H0]. What needs to
    be proved is that [H0], if augmented with [H1], yields [H2]. *)

Lemma hwand_intro : forall H0 H1 H2,
  (H0 \* H1) ==> H2 ->
  H0 ==> (H1 \-* H2).
Proof using. intros. applys hwand_characterization. Qed.

(** The left-to-right direction is an elimination rule: it tells
    what can be deduced from [H0 ==> (H1 \-* H2)]. What can be
    deduced is that if [H0] is augmented with [H1], then [H2]
    can be recovered. *)

Lemma hwand_elim : forall H1 H2 H3,
  H0 ==> (H1 \-* H2) ->
  (H0 \* H1) ==> H2.
Proof using. intros. applys hwand_characterization. Qed.

(** This elimination rule can be equivalently reformulated in the
    following form, which makes it perhaps even clearer that 
    [H1 \-* H2], when augmented with [H1], yields [H2]. 
    Think of it as [H1 + (-H1 + H2)] simplifying to [H2]. *)

Lemma hwand_elim' : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.
Proof using. intros. applys hwand_elim. Qed.

(** Another possible definition of [H1 \-* H2] can be stated
    without refering to heaps at all, by reusing the basic
    Separation Logic operators that we have already introduced. 
    [H1 \-* H2] denotes some heap, described as [H0], such 
    that [H0] augmented with [H1] yields [H2]. 
    
    In the alternative definition of [hwand] shown below,
    the heap [H0] is existentially quantified using [\exists], 
    and the entailment assertion is described as the pure heap
    predicate [\[ H0 \* H1 ==> H2 ]]. *)

Definition hwand' (H1 H2:hprop) : hprop :=
  \exists H0, H0 \* \[ (H0 \* H1) ==> H2].

(** In practice, [SepBase] relies on the definition of [hwand'],
    which has the benefit that all properties of [hwand] can be
    established with help of the tactic [hsimpl]. In other words,
    we reduce the amount of work by conducting all the reasoning
    at the level of [hprop] and avoiding the need to work with
    explicit heaps (of type [heap]). *)


(* ------------------------------------------------------- *)
(** *** Equivalence between the definitions of magic wand *)

(** In what follows we prove the equivalence between the three
    characterizations of [hwand H1 H2] that we have presented:

    1. [fun h => forall h', fmap_disjoint h h' -> H1 h' -> H2 (h \u h')]

    2. [\exists H0, H0 \* \[ (H0 \* H1) ==> H2]]

    3. [forall H0 H1 H2, (H0 ==> hwand H1 H2) <-> (H0 \* H1 ==> H2)].

    To prove the 3-way equivalence, we first prove the equivalence
    between (1) and (2), then prove the equivalence between (2) and (3).
*)

(** Prove that [hwand] is equivalent to [hwand']. *)

Lemma hwand_eq_hwand' :
  hwand = hwand'.
Proof using. Qed.


(** Prove that [hwand'] satisfies the lemma 
    [hwand_characterization]. *)

Lemma hwand'_satisfies_hwand_characterization : forall H0 H1 H2,
  (H0 ==> hwand' H1 H2) <-> (H0 \* H1 ==> H2).
Proof using. Qed.

Lemma hwand'_satisfies_hwand_characterization' : forall op,
  op = hwand ->
  (forall H0 H1 H2, (H0 ==> op H1 H2) <-> (H0 \* H1 ==> H2)).
Proof using. intros. subst. applys hwand'_satisfies_hwand_characterization. Qed.

(** Reciprocally, show that any operator satisfying
    [hwand] characterization is equal to [hwand']. *)

Lemma hwand_characterization_eq_hwand' : forall op,
  (forall H0 H1 H2, (H0 ==> op H1 H2) <-> (H0 \* H1 ==> H2)) ->
  op = hwand'.
Proof using. Qed.









(* ------------------------------------------------------- *)
(** *** Intuitive interpretation for [hwand] *)

(** In first approximation, [H1 \-* H2] is like [H2] but with 
    the [H1] part missing. If we were to compare with arithmetics,
    it would correspond to [ -H1 + H2 ]. 

    If you own the resource [H1 \-* H2], and you also own the
    resource [H1], then you can trade the two for [H2].
    The formal statement, shown below, is reminiscent of the arithmetic
    operation [H1 + (-H1 + H2) = H2]. *)

Parameter hwand_elim : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.

(** The magic wand satisfies a number of other properties that also
    work just like the arithmetic operations would suggest.
    For example: [(-H1 + H2) + (-H2 + H3) = (-H1 + H3)]. 
    The formal statement, shown below, captures that if you own a
    resource asserting that you can trade it with [H1] for [H2], and own
    a resource asserting that you can trade it with [H2] for [H3], then
    you essentially own a resource asserting that you can trade it
    with [H1] for [H3] directly. *)

Parameter hwand_trans_elim : forall H1 H2 H3,
  (H1 \-* H2) \* (H2 \-* H3) ==> (H1 \-* H3).

(** Intuitively, it is safe to replace a heap predicate by another
    one, if the inequalities required to justified that the first
    heap predicate makes sense (i.e. that is does not contain 
    "negative values") are sufficient to justify that the second
    heap predicate also makes sense.
    
    For example, in [(H1 \-* H2) \* (H2 \-* H3) ==> (H1 \-* H3)]
    the LHS requires [H1 <= H2] and [H2 <= H3], from which we can
    deduce [H1 <= H3], as required to justify to RHS. 
  
    But the reciprocal entailment does not hold: from [H1 <= H3], 
    we could not possibly justify [H1 <= H2] not [H2 <= H3].

    Likewise, we can prove:
*)

Lemma hempty_himpl_hwand_self : forall H,
  \[] ==> (H \-* H).
Proof using. hsimpl. Qed.

(* FALSE! 
Lemma hwand_self_himpl_hempty : forall H,
  (H \-* H) ==> \[].
Proof using.
  intros. intros h M. rewrite hwand_eq_hexists_hstar_hpure in M.
  lets (H'&R): hexists_inv M.
Qed.
*)


(** Because we are working with heap predicates, and that "negative"
    heap predicates don't quite make sense, we have to be careful.
    Essentially, our arithmetic interpretation [ -H1 + H2] should be
    intrepreted on natural numbers (N) and not on integers (Z).
    We are only allowed to reason about a subtraction [ -H1 + H2]
    if we can somehow justify that H1 is "not smaller than" H2.

    When working on natural numbers, it is not correct to replace
    a number [n] with [(n-m)+m] for some arbitrary [m]. As counter-
    example, take any value [m] greater than [n]. *)

Section TestSubtractionNat.
Open Scope nat_scope.

Lemma counterexample : exists n m, 
  n <> (n-m)+m.
Proof using. exists 0 1. intros N. simpl in N. false. Qed.

End TestSubtractionNat.

(** Likewise, it is not the case that from a heap [H2] we can
    replace it with [H1 \* (H1 \-* H2)]. As counter-example,
    consider [H2 = \[]] and [H1 = \[False]]. *)

Lemma hwand_elim_reciprocal_false : exists H1 H2,
  ~ (H2 ==> H1 \* (H1 \-* H2)).
Proof using. 
  exists \[False] \[]. intros N. forwards K: N (fmap_empty:heap).
  applys hempty_intro. rewrite hstar_hpure in K. destruct K. auto.
Qed.


(* ------------------------------------------------------- *)

intro rule

  H1 \* H2 ==> H3 ->
  H1 ==> H2 \-* H3

elim rule

   H1 ==> H2 \-* H3 ->
   H1 \* H2 ==> H3

equivalence of elim rule

  H1 \* (H1 \-* H2) ==> H2.



-----------------------------

not that reciprocal is false!

  H2 ==> H1 \* (H1 \-* H2) 




(* ------------------------------------------------------- *)
(** *** Frame expressed with [hwand]: the ramified frame rule *)






  H ==> H1 \* H2 ->
  triple t H1 Q1 ->
  Q1 \* H2 ==> Q \*+ \GC ->
  triple t H Q


  H ==> H1 \* H2 ->
  triple t H1 Q1 ->
  Q1 \* H2 ==> Q \*+ \GC ->
  triple t H Q



  H ==> H1 \* H2 ->
  triple t H1 Q1 ->
  H2 ==> Q1 \*- (Q \*+ \GC) ->
  triple t H Q


  H ==> H1 \* (Q1 \*- (Q \*+ \GC)) ->
  triple t H1 Q1 ->
  triple t H Q

reciprocally frame derivable

  H ==> H1 \* H2 ->
  triple t H1 Q1 ->
  H2 ==> Q1 \*- (Q \*+ \GC) ->
  triple t H Q


  MQ. H ==> H1 \* (Q1 \*- (Q \*+ \GC))
  MQ. H1 \* H2  ==> H1 \* (Q1 \*- (Q \*+ \GC))
  MQ. H2  ==> (Q1 \*- (Q \*+ \GC))
  MQ. Q1 \* H2  ==> (Q \*+ \GC)
  done.




(* ------------------------------------------------------- *)
(** *** Formal definitions for [hwand] *)



(*
    [H1 \-* H2] is a heap predicate that holds of a heap [h] if,
    when augmenting [h] with a heap [h'] that satisfies [H1],

*)


Lemma flocal_elim : forall F H Q,
  H ==> wp t Q' \* (Q' \--* (Q \*+ \GC)) ->
  H ==> wp t Q.
Proof using. introv L M. lets N: (L Q). applys* himpl_trans N. Qed.





  prove1: 
    F Q ==> mklocal F Q
    (take Q1 = Q)

  prove 2:
    (mkflocal (mkflocal F)) Q := mkflocal F
    right-to-left : instance of (1)
    left-to-right: ...

    (mkflocal (mkflocal F)) Q
  = \exists Q1, mkflocal F Q1 \* (Q1 \--* (Q \*+ \GC))
  = \exists Q1, (\exists Q2, F Q2 \* (Q2 \--* (Q1 \*+ \GC))) \* (Q1 \--* (Q \*+ \GC))
  = \exists Q1 Q2, F Q2 \* (Q2 \--* (Q1 \*+ \GC) \* (Q1 \--* (Q \*+ \GC))
  = \exists Q1 Q2, F Q2 \* (Q2 \--* (Q1 \*+ \GC) \* ((Q1 \*+ \GC) \--* ((Q \*+ \GC) \*+ \GC))
  ==> \exists Q1 Q2, F Q2 \* (Q2 \--* (Q1 \*+ \GC) \* ((Q1 \*+ \GC) \--* (Q \*+ \GC \*+ \GC))
  = \exists Q1 Q2, F Q2 \* (Q2 \--* (Q \*+ \GC \*+ \GC))
  = \exists Q2, F Q2 \* (Q2 \--* (Q \*+ \GC))
  = mkflocal F


  mkflocal F Q := \exists Q1, F Q1 \* (Q1 \--* (Q \*+ \GC)).

  \exists Q1, F Q1 \* (Q1 \--* (Q \*+ \GC)) ==> F Q


  F Q1 \* (Q1 \--* (Q \*+ \GC)) ==> F Q



  wp t Q1 \* (Q1 \--* (Q \*+ \GC)) ==> wp t Q


  H ==> wp t Q1 \* (Q1 \--* (Q \*+ \GC)) ->
  H ==> wp t Q.


let H1 := wp t Q1
let H2 := (Q1 \--* (Q \*+ \GC)) 


  H ==> H1 \* H2 ->
  H1 ==> wp t Q1 ->
  Q1 \* H2 ==> Q \*+ \GC ->
  H ==> wp t Q.


  H ==> H1 \* H2 ->
  triple t H1 Q1 ->
  Q1 \* H2 ==> Q \*+ \GC ->
  triple t H Q


reciprocally, with 
   forall Q1,   wp t Q1 \* (Q1 \--* (Q \*+ \GC)) ==> wp t Q
we can simulate frame


  H ==> H1 \* H2 ->
  H1 ==> wp t Q1 ->
  Q1 \* H2 ==> Q \*+ \GC ->
  H ==> wp t Q.

exploit fact

  H ==> H1 \* H2 ->
  H1 ==> wp t Q1 ->
  Q1 \* H2 ==> Q \*+ \GC ->
  H ==> wp t Q1 \* (Q1 \--* (Q \*+ \GC))

suffices (hchange 1 and 2)

  H1 \* H2 ==> wp t Q1 \* (Q1 \--* (Q \*+ \GC))
  wp t Q1 \* H2 ==> wp t Q1 \* (Q1 \--* (Q \*+ \GC))
  H2 ==> (Q1 \--* (Q \*+ \GC))

done.





