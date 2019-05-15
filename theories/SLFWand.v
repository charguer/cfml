(**

Separation Logic Foundations

Chapter: "Wand".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import SLFRules.

Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.


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
(** ** Definition of the magic wand *)

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

Notation "H1 \-* H2" := (hwand H1 H2) (at level 43, right associativity).

(** The definition of [hwand] is not easy to make sense of at first.
    To better grasp its meaning, we next present two alternative
    definitions of [hwand], and detail its introduction and elimination
    lemmas. *)

(** The operator [H1 \-* H2] is uniquely defined by the followig
    equivalence. In other words, any operator that satisfies this
    equivalence for all arguments is provably equal to the definition 
    of [hwand] given above. (We proof this fact further in the chapter.) *)

Parameter hwand_equiv : forall H0 H1 H2,
  (H0 ==> H1 \-* H2) <-> (H0 \* H1 ==> H2).

(** The right-to-left direction is an introduction rule: it tells
    what needs to be proved to introduce a magic wand [H1 \-* H2]
    when starting from a state described by [H0]. What needs to
    be proved is that [H0], if augmented with [H1], yields [H2]. *)

Lemma hwand_intro : forall H0 H1 H2,
  (H0 \* H1) ==> H2 ->
  H0 ==> (H1 \-* H2).
Proof using. introv M. applys hwand_equiv. applys M. Qed.

(** The left-to-right direction is an elimination rule: it tells
    what can be deduced from [H0 ==> (H1 \-* H2)]. What can be
    deduced is that if [H0] is augmented with [H1], then [H2]
    can be recovered. *)

Lemma hwand_elim : forall H0 H1 H2,
  H0 ==> (H1 \-* H2) ->
  (H0 \* H1) ==> H2.
Proof using. introv M. applys hwand_equiv. applys M. Qed.

(** This elimination rule can be equivalently reformulated in the
    following form, which makes it perhaps even clearer that 
    [H1 \-* H2], when augmented with [H1], yields [H2].
    Think of it as [H1 + (-H1 + H2)] simplifying to [H2]. *)

Lemma hwand_cancel : forall H1 H2,
  H1 \* (H1 \-* H2) ==> H2.
Proof using.
  intros. rewrite hstar_comm.
  applys hwand_elim. applys himpl_refl.
Qed.

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

(** As we prove further in this file, we can prove that [hwand']
    defines the same operator as [hwand]. *)

Parameter hwand_eq_hwand' :
  hwand = hwand'.

(** In practice, [SepBase] relies on the definition of [hwand'],
    which has the benefit that all properties of [hwand] can be
    established with help of the tactic [hsimpl]. In other words,
    we reduce the amount of work by conducting all the reasoning
    at the level of [hprop] and avoiding the need to work with
    explicit heaps (of type [heap]). *)


(* ******************************************************* *)
(** ** Magic wand for postconditions *)

(** For entailment, written [H1 ==> H2], we introduced its extension
    to postconditions, written [Q1 ===> Q2], and defined as
    [forall x, (Q1 x) ==> (Q2 x)].

    Likewise, for magic wand, written [H1 \-* H2], we introduce
    its extension to postconditions, written [Q1 \--* Q2], and 
    defined (in first approximation) as [forall x, (Q1 x) \-* (Q2 x)].

    Like [H1 \-* H2], the expression [Q1 \--* Q2] should denote a heap
    predicate, of type [hprop]. Thus, writing [forall x, (Q1 x) \-* (Q2 x)]
    makes no sense, because [forall] applies to propositions of type [Prop],
    and not to heap predicates of type [hprop].

    In order to define [Q1 \--* Q2], we thus need to introduce the
    operation [\forall], which lifts the universal quantifier from
    [Prop] to [hprop]. In other words, [\forall] is to [forall]
    what [\exists] is to [exists]. 

    The definition of [\forall x, H], a notation for [hforall (fun x => H)],
    follows exactly the same pattern as that of [\exists x, H], with only
    the [exists] quantifier being replaced with a [forall] in the definition. *)

Definition hforall (A : Type) (J : A -> hprop) : hprop :=
  fun h => forall x, J x h.

Notation "'\forall' x1 .. xn , H" :=
  (hforall (fun x1 => .. (hforall (fun xn => H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : heap_scope.

(** We are now read to formally define [Q1 \--* Q2], a notation that stands
    for [qwand Q1 Q2], and which is defined as [\forall x, (Q1 x) \-* (Q2 x)]. *)

Definition qwand A (Q1 Q2:A->hprop) :=
  \forall x, (Q1 x) \-* (Q2 x).

Notation "Q1 \--* Q2" := (qwand Q1 Q2) (at level 43).

(** As a sanity check of our definition, let us prove that [Q1 \--* Q2]
    indeed entails [(Q1 x) \-* (Q2 x)] for any [x]. *)

Lemma qwand_specialize : forall A (x:A) (Q1 Q2:A->hprop),
  (Q1 \--* Q2) ==> (Q1 x \-* Q2 x).
Proof using. intros. unfold qwand. intros h K. applys K. Qed.





(* ******************************************************* *)
(** ** Frame expressed with [hwand]: the ramified frame rule *)



(*

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



*)





(* ####################################################### *)
(** * Additional contents *)


(* ******************************************************* *)
(** ** Properties of [hwand] *)

(** We next present the most important properties of [H1 \-* H2].
    The tactic [hsimpl] provides dedicated support for
    simplifying expressions involving magic wand. So,
    in most proofs, it is not required to manually manipulate
    the lemmas capturing properties of the magic wand.
    Nevertheless, there are a few situations where [hsimpl]
    won't automatically perform the desired manipulation.
    Morover, reading the properties of [hwand] may help providing
    a better understanding of this operator. *)

(* ------------------------------------------------------- *)
(** *** Structural properties of [hwand] *)

(** [H1 \-* H2] is covariant in [H2], and contravariant in [H1]
    (like an implication). *)

Lemma hwand_himpl : forall H1 H1' H2 H2',
  H1' ==> H1 ->
  H2 ==> H2' ->
  (H1 \-* H2) ==> (H1' \-* H2').
Proof using.
  introv M1 M2. applys hwand_intro. hchange M1.
  hchange (@hwand_cancel H1 H2). applys M2.
Qed.

(** Two predicates [H1 \-* H2] ans [H2 \-* H3] may simplify
    to [H1 \-* H3]. This simplification is reminiscent of the
    arithmetic operation [(-H1 + H2) + (-H2 + H3) = (-H1 + H3)]. *)

Lemma hwand_trans_elim : forall H1 H2 H3,
  (H1 \-* H2) \* (H2 \-* H3) ==> (H1 \-* H3).
Proof using.
  intros. applys hwand_intro. hchange (@hwand_cancel H1 H2).
  hchange (@hwand_cancel H2 H3).
Qed.

(** The predicate [H \-* H] holds of the empty heap.
    Intuitively [(-H + H)] can be replaced with zero. *)

Lemma himpl_hempty_hwand_same : forall H,
  \[] ==> (H \-* H).
Proof using. intros. apply hwand_intro. hsimpl. Qed.


(* ------------------------------------------------------- *)
(** *** Tempting but false properties for [hwand] *)

(** The reciprocal entailment to the above lemma, that is
    [(H \-* H) ==> \[]], does not hold.

    For example, [\Top \-* \Top] is a heap predicate that
    holds of any heap, and not just of the empty heap. *)

Lemma not_hwand_self_himpl_hempty : exists H,
  ~ ((H \-* H) ==> \[]).
Proof using.
  exists \Top. intros M.
  lets (h&N): (@fmap_exists_not_empty val). { typeclass. }
  forwards K: M h. { hnf. intros h' D K'. applys htop_intro. }
  false* (hempty_inv K).
Qed.

(** Likewise, the reciprocal entailment to the elimination 
    lemma, that is, [H2 ==> H1 \* (H1 \-* H2)] does not hold.

    As counter-example, consider [H2 = \[]] and [H1 = \[False]]. 
    We can prove that the empty heap does not satisfies 
    [\[False] \* (\[False] \-* \[])]. *)

Lemma not_hwand_elim_reciprocal : exists H1 H2,
  ~ (H2 ==> H1 \* (H1 \-* H2)).
Proof using. 
  exists \[False] \[]. intros N. forwards K: N (fmap_empty:heap).
  applys hempty_intro. rewrite hstar_hpure in K. destruct K. auto.
Qed.

(** More generally, one has to be suspicious of any entailment
    that introduces wands out of nowhere.

    The entailment [hwand_trans_elim]:
    [(H1 \-* H2) \* (H2 \-* H3) ==> (H1 \-* H3)]
    is correct because, intuitively, the left-hand-side captures
    that [H1 <= H2] and that [H1 <= H3] (for some vaguely-defined
    notion of [<=]), from which one derive [H1 <= H3] and justify
    that the right-hand-side makes sense.

    On the contrary, the reciprocal entailment
    [(H1 \-* H3) ==> (H1 \-* H2) \* (H2 \-* H3)]
    is certainly false, because from [H1 <= H3] there is no way
    to justify [H1 <= H2] nor [H2 <= H3]. *)


(* ------------------------------------------------------- *)
(** *** Interaction of [hwand] with [hempty] and [hpure] *)

(** [\[] \-* H] is the same as [H]. *)

Lemma hwand_hempty_l : forall H,
  (\[] \-* H) = H.
Proof using.
  intros. rewrite hwand_eq_hwand'. unfold hwand'. hsimpl.
  { intros H0 M. hchange M. }
  { hsimpl. }
Qed.

(** Assume that [\[P] \-* H] holds of a heap.
    To show that [H] holds of this same heap, it suffices
    ot justify that the proposition [P] is true. Formally: *)

Lemma hwand_hpure_l_intro : forall P H,
  P ->
  (\[P] \-* H) ==> H.
Proof using.
  introv HP. rewrite hwand_eq_hwand'. unfold hwand'. hsimpl.
  intros H0 M. hchange M. applys HP.
Qed.
   (* Note: here is an alterntive proof w.r.t. [hwand]:
    introv HP. unfold hwand. intros h K.
    forwards M: K (fmap_empty:heap).
    { apply fmap_disjoint_empty_r. }
    { applys hpure_intro HP. }
    { rewrite fmap_union_empty_r in M. applys M. } *)

(** [\[P] \-* H] can be proved of a heap if [H] can be proved
   of this heap under the assumption [P]. Formally: *)

Lemma hwand_hpure_r_intro : forall H1 H2 P,
  (P -> H1 ==> H2) ->
  H1 ==> (\[P] \-* H2).
Proof using. introv M. applys hwand_intro. hsimpl. applys M. Qed.


(* ------------------------------------------------------- *)
(** *** Interaction of [hwand] with [hstar] *)

(** The heap predicates [(H1 \* H2) \-* H3] and [H1 \-* (H2 \-* H3)]
    and [H2 \-* (H1 \-* H3)] are all equivalent. Intuitively, they all 
    describe the predicate [H3] with the missing pieces [H1] and [H2]. 

    The equivalence between the uncurried form [(H1 \* H2) \-* H3]
    and the curried form [H1 \-* (H2 \-* H3)] is formalized by the
    lemma shown below. The third form [H2 \-* (H1 \-* H3)] follows
    directly by exploiting the commutativity [H1 \* H2 = H2 \* H1]. *)

Lemma hwand_curry_eq : forall H1 H2 H3,
  (H1 \* H2) \-* H3 = H1 \-* (H2 \-* H3).
Proof using.
  intros. applys himpl_antisym.
  { apply hwand_intro. apply hwand_intro.
    hchange (@hwand_cancel (H1 \* H2) H3). }
  { apply hwand_intro. hchange (@hwand_cancel H1 (H2 \-* H3)).
    hchange (@hwand_cancel H2 H3). }
Qed.

(** If a heap satisfies [H1 \-* H2] and another heap
    satisfies [H3], then their disjoint union satisfies
    [H1 \-* (H2 \* H3)]. In both views, if [H1] is provided,
    then both [H2] and [H3] can be obtained. *)

Lemma hstar_hwand : forall H1 H2 H3,
  (H1 \-* H2) \* H3 ==> H1 \-* (H2 \* H3).
Proof using.
  intros. applys hwand_intro. hsimpl. hchange (@hwand_cancel H1 H2).
Qed.


(* ------------------------------------------------------- *)
(** *** Exercises on [hwand] *)

(* EX1! (himpl_hwand_hstar_same_r) *)
(** Prove that [H1] entails [H2 \-* (H2 \* H1)]. *)

Lemma himpl_hwand_hstar_same_r : forall H1 H2,
  H1 ==> (H2 \-* (H2 \* H1)).
Proof using.
(* SOLUTION *)
  intros. applys hwand_intro. hsimpl.
(* /SOLUTION *)
Qed.

(* EX2! (hwand_cancel_part) *)
(** Prove that [H1 \* ((H1 \* H2) \-* H3)] simplifies to [H2 \-* H3]. *)

Lemma hwand_cancel_part : forall H1 H2 H3,
  H1 \* ((H1 \* H2) \-* H3) ==> (H2 \-* H3).
Proof using.
(* SOLUTION *)
  intros. applys hwand_intro. hchange (@hwand_cancel (H1 \* H2)).
(* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Properties of [hforall] *)

(** To prove that a heap satisfies [\forall x, J x], one must
    show that, for any [x], this heap satisfies [J x]. *)

Lemma himpl_hforall_r : forall A (J:A->hprop) H,
  (forall x, H ==> J x) ->
  H ==> (\forall x, J x).
Proof using. introv M. intros h K x. apply~ M. Qed.

(** Assuming a heap satisfies [\forall x, J x], one can derive
    that the same heap satisfies [J v] for any desired value [v]. *)

Lemma hforall_specialize : forall A (v:A) (J:A->hprop),
  (\forall x, J x) ==> (J v).
Proof using. intros. intros h K. apply~ K. Qed.

(** The lemma above can equivalently be formulated in the following way. *)

Lemma himpl_hforall_l : forall A (v:A) (J:A->hprop) H,
  J v ==> H ->
  (\forall x, J x) ==> H.
Proof using. introv M. applys himpl_trans M. applys hforall_specialize. Qed.


(* ******************************************************* *)
(** ** Properties of [qwand] *)

(* ------------------------------------------------------- *)
(** *** Structural properties of [qwand] *)

(** We first state the introduction and elimination lemmas
    analogous to [hwand_intro], [hwand_elim], and [hwand_cancel]. *)

Lemma qwand_intro : forall H Q1 Q2,
  (Q1 \*+ H) ===> Q2 ->
  H ==> (Q1 \--* Q2).
Proof using. 
  introv M. applys himpl_hforall_r. intros x.
  applys hwand_intro. rewrite hstar_comm. applys M.
Qed.

Lemma qwand_elim : forall H Q1 Q2,
  H ==> (Q1 \--* Q2) ->
  (Q1 \*+ H) ===> Q2.
Proof using. 
  introv M. intros x. rewrite hstar_comm. apply hwand_elim.
  hchange M. applys hforall_specialize x.
Qed.

Lemma qwand_cancel : forall Q1 Q2,
  Q1 \*+ (Q1 \--* Q2) ===> Q2.
Proof using. intros. applys qwand_elim. applys himpl_refl. Qed.

(** Like [hwand], [qwand] is covariant in its second argument,
    and contravariant in its first argument. *)

Lemma qwand_himpl : forall Q1 Q1' Q2 Q2',
  Q1' ===> Q1 ->
  Q2 ===> Q2' ->
  (Q1 \--* Q2) ==> (Q1' \--* Q2').
Proof using.
  introv M1 M2. applys himpl_hforall_r. intros x.
  applys himpl_hforall_l x. applys hwand_himpl.
  { applys M1. } { applys M2. }
Qed.

(** If a heap satisfies [Q1 \--* Q2] and another heap
    satisfies [H], then their disjoint union satisfies
    [Q1 \--* (Q2 \*+ H)]. In both views, if [Q1] is provided,
    then both [Q2] and [H] can be obtained. *)

Lemma hstar_qwand : forall Q1 Q2 H,
  (Q1 \--* Q2) \* H ==> Q1 \--* (Q2 \*+ H).
Proof using.
  intros. applys qwand_intro. hchange (@qwand_cancel Q1).
Qed.


(* ------------------------------------------------------- *)
(** *** Exercices on [qwand] *)

(* EX1! (himpl_qwand_hstar_same_r) *)
(** Prove that [H] entails [Q \--* (Q \*+ H)]. *)

Lemma himpl_qwand_hstar_same_r : forall H Q,
  H ==> Q \--* (Q \*+ H).
Proof using.
(* SOLUTION *)
  intros. applys qwand_intro. hsimpl.
(* /SOLUTION *)
Qed.

(* EX2! (qwand_cancel_part) *)
(** Prove that [H \* ((Q1 \*+ H) \--* Q2)] simplifies to [Q1 \--* Q2]. *)

Lemma qwand_cancel_part : forall H Q1 Q2,
  H \* ((Q1 \*+ H) \--* Q2) ==> (Q1 \--* Q2).
Proof using.
(* SOLUTION *)
  intros. applys qwand_intro. intros x.
  hchange (qwand_specialize x).
  hchange (@hwand_cancel (Q1 x \* H)).
(* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Equivalence between the definitions of magic wand *)

(** In what follows we prove the equivalence between the three
    characterizations of [hwand H1 H2] that we have presented:

    1. [fun h => forall h', fmap_disjoint h h' -> H1 h' -> H2 (h \u h')]

    2. [\exists H0, H0 \* \[ (H0 \* H1) ==> H2]]

    3. [forall H0 H1 H2, (H0 ==> hwand H1 H2) <-> (H0 \* H1 ==> H2)].

    To prove the 3-way equivalence, we first prove the equivalence
    between (1) and (2), then prove the equivalence between (2) and (3).
*)

(** Let us first prove that [hwand] is equivalent to [hwand'],
    i.e., that (1) and (2) are equivalent definitions. *)

Lemma hwand_eq_hwand'_details :
  hwand = hwand'.
Proof using.
  apply pred_ext_3. intros H1 H2 h. unfold hwand, hwand'. iff M.
  { exists (=h). rewrite hstar_comm. rewrite hstar_hpure. split.
    { intros h3 K3. destruct K3 as (h1&h2&K1&K2&D&U).
      subst h1 h3. applys M D K2. }
    { auto. } }
  { intros h1 D K1. destruct M as (H0&M).
    destruct M as (h0&h2&K0&K2&D'&U).
    lets (N&E): hpure_inv (rm K2). subst h h2.
    rewrite fmap_union_empty_r in *.
    applys N. applys hstar_intro K0 K1 D. }
Qed.

(** According to definition (3), an operator [op] is a magic wand
   if and only if, for any [H0], [H1], [H2], it satisfies the
   equivalence [(H0 ==> op H1 H2) <-> (H0 \* H1 ==> H2)]. Formally: *)

Definition hwand_characterization (op:hprop->hprop->hprop) :=
  forall H0 H1 H2, (H0 ==> op H1 H2) <-> (H0 \* H1 ==> H2).

(** Let us now prove that [hwand'] satisfies the lemma
    [hwand_characterization]. *)

Lemma hwand_characterization_hwand' : 
  hwand_characterization hwand'.
Proof using. 
  intros H0 H1 H2. unfold hwand'. iff M. { hchange M. } { hsimpl~ H0. }
Qed.

(** The above proof seems too easy. It's because [hsimpl] is doing
    all the work for us. Here is a detailed proof not using [hsimpl]. *)

Lemma hwand_characterization_hwand'_details : forall H0 H1 H2,
  (H0 ==> hwand' H1 H2) <-> (H0 \* H1 ==> H2).
Proof using. 
  intros. unfold hwand'. iff M.
  { applys himpl_trans. applys himpl_frame_l M.
    rewrite hstar_hexists. applys himpl_hexists_l. intros H3.
    rewrite (hstar_comm H3). rewrite hstar_assoc.
    applys himpl_hstar_hpure_l. intros N. applys N. }
  { applys himpl_hexists_r H0. rewrite hstar_comm.
    applys himpl_hstar_hpure_r. applys M. applys himpl_refl. }
Qed.

(** Reciprocally, show that any operator satisfying
    [hwand] characterization is equal to [hwand']. *)

Lemma hwand_characterization_eq_hwand' : forall op,
  hwand_characterization op -> 
  op = hwand'.
Proof using.
  introv Ch. unfolds in Ch. apply fun_ext_2. intros H1 H2.
  unfold hwand'. apply himpl_antisym.
  { lets (M&_): (Ch (op H1 H2) H1 H2). hsimpl (op H1 H2).
    applys M. applys himpl_refl. }
  { hsimpl. intros H0 M. rewrite Ch. applys M. }
Qed.



(* ******************************************************* *)
(** ** Conjuction and disjunction operators on [hprop] *)

(** For some advanced applications, it is useful to lift the
    disjunction operation [P1 \/ P2] from [Prop] to [hprop].

    The heap predicate [hor H1 H2] describes a heap that 
    satisfies [H1] or [H2] (possibly both). 

    An obvious definition for it is: *)

Definition hor (H1 H2 : hprop) : hprop :=
  fun h => H1 h \/ H2 h.

(** An alternative definition leverages [\exists] to quantify
    over a boolean indicating whether [H1] or [H2] should hold. *)

Definition hor' (H1 H2 : hprop) : hprop :=
  \exists (b:bool), if b then H1 else H2.

(* EX2! (hor_eq_hor') *)
(** Prove the equivalence of the definitions [hor] and [hor']. *)

Lemma hor_eq_hor' : 
  hor = hor'.
Proof using.
(* SOLUTION *)
  applys fun_ext_2. intros H1 H2. unfold hor, hor'. applys himpl_antisym.
  { intros h K. destruct K. { exists* true. } { exists* false. } }
  { hsimpl. intros b h K. destruct b. { left*. } { right*. } }
(* /SOLUTION *)
Qed.


(** Likewise, we lift the conjunction operation [P1 /\ P2] from
    [Prop] to [hprop].

    The heap predicate [hand H1 H2], called the "non-separating
    conjunction", describes a heap that satisfies both [H1] and [H2]
    at the same time.

    An obvious definition for it is: *)

Definition hand (H1 H2 : hprop) : hprop :=
  fun h => H1 h /\ H2 h.

(** An alternative definition leverages [\forall] to 
    non-deterministically quantify over a boolean indicating
    whether [H1] or [H2] should hold. This the quantification
    is over all booleans, both must hold. *)

Definition hand' (H1 H2 : hprop) : hprop :=
  \forall (b:bool), if b then H1 else H2.

(* EX3! (hand_eq_hand') *)
(** Prove the equivalence of the definitions [hand] and [hand']. *)

Lemma hand_eq_hand' : 
  hand = hand'.
Proof using.
(* SOLUTION *)
  applys fun_ext_2. intros H1 H2. unfold hand, hand'. applys himpl_antisym.
  { intros h K b. destruct b. { autos*. } { autos*. } }
  { intros h N. split. { applys N true. } { applys N false. } }
(* /SOLUTION *)
Qed.

