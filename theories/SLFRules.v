(**

Separation Logic Foundations

Chapter: "Rules".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.

(** The file [SepBase] contains definitions that are essentially similar
    to those from [SLFHprop] and [SLFHimpl], with just a few differences:

    - The predicate [Hoare_triple] is abbreviated as [hoare],
    - The predicate [triple] is defined not using [\Top] to handle discarded
      pieces of heap, but using a specific instance of a general predicate 
      called [\GC]. For the instance considered in [SepBase], it turns out 
      that [\GC = \Top]. To help forgeting about this difference, we define
      the notation [\Top'] to pretty-print [\GC]. 
    - [SepBase] uses a definition of [l ~~~> v] which enforces [l] to not
      be the [null] location. In this file, we will completely ignore this
      extra requirement.

    In addition, we consider as definition of substitution on term the
    version that computes in Coq (with just a call to [simpl]). To that
    end, we define [subst] as a shorthand for [subst_exec].
*)

From Sep Require Import SepBase SubstExec.
Notation "'\Top''" := hgc.
Definition subst := subst_exec.

(** Implicit Types *)

Implicit Types x f : var.
Implicit Types b : bool.
Implicit Types l : loc.
Implicit Types n : int.
Implicit Types v w r : val.
Implicit Types t : trm.
Implicit Types h : heap.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ####################################################### *)
(** * The chapter in a rush *)

(* ******************************************************* *)
(** ** Structural rules *)

(** We have already introduced in the first two chapters all the
    essential structural rules. *)

(** The frame rule asserts that the precondition and the postcondition
    can be extended together by an arbitrary heap predicate. *)

Parameter triple_frame : forall t H Q H',
  triple t H Q ->
  triple t (H \* H') (Q \*+ H').

(** The consequence rule enables to strengthen the precondition
    and weaken the postcondition. *)

Parameter triple_conseq : forall t H' Q' H Q,
  triple t H' Q' ->
  H ==> H' ->
  Q' ===> Q ->
  triple t H Q.

(** The two extraction rules enable to extract pure facts and
    existentially quantified variables from the precondition
    into the Coq context. *)

Parameter triple_hpure : forall t (P:Prop) H Q,
  (P -> triple t H Q) ->
  triple t (\[P] \* H) Q.

Parameter triple_hexists : forall t (A:Type) (J:A->hprop) Q,
  (forall (x:A), triple t (J x) Q) ->
  triple t (hexists J) Q.

(** The garbage collection rules enable to discard any desired
    piece of heap from the precondition or the postcondition. 
    (As we have seen, it is equivalent to state these two rules
    by writing [H'] instead of [\Top].) *)

Parameter triple_htop_pre : forall t H Q,
  triple t H Q ->
  triple t (H \* \Top) Q.

Parameter triple_htop_post : forall t H Q,
  triple t H (Q \*+ \Top) ->
  triple t H Q.


(* ******************************************************* *)
(** ** Rules for terms *)

(** In this chapter, for simplicity, we assume that all terms
    are written in "A-normal form": the arguments of applications
    and of conditionals are restricted to variables and value.
    Such a requirement does not limit expressiveness.
    For example, [if t0 then t1 else t2] can be encoded as 
    [let x = t0 in if x then t1 else t2]. *)

(** The reasoning rule for a sequence [t1;t2] is similar to that
    from Hoare logic. The rule is:
[[
      {H} t1 {fun r => H1}     {H1} t2 {Q}
      ------------------------------------
              {H} (t1;t2) {Q}
]]
    Remark: the variable [r] denotes the result of the evaluation
    of [t1]. For well-typed programs, this result is always [val_unit]. *)

Parameter triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun r => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.

(** The reasoning rule for a let binding [let x = t1 in t2] could
    be stated, in informal writing, in the form:
[[
      {H} t1 {Q1}     (forall x, {Q1 x} t2 {Q})
      -----------------------------------------
            {H} (let x = t1 in t2) {Q}
]]
  Yet, such a presentation makes a confusion between the [x] that
  denotes a program variable in [let x = t1 in t2], and the [x]
  that denotes a value when quantified as [forall x]. 
  The correct statement involves a substitution from the variable
  [x] to a value quantified as [forall v].
[[
      {H} t1 {Q1}     (forall v, {Q1 v} (subst x v t2) {Q})
      -----------------------------------------------------
                {H} (let x = t1 in t2) {Q}
]]
*)

Parameter triple_let : forall x t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall v, triple (subst x v t2) (Q1 v) Q) ->
  triple (trm_let x t1 t2) H Q.

(** The rule for a conditional is exactly like in Hoare logic.
[[
      b = true -> {H} t1 {Q}     b = false -> {H} t2 {Q}
      --------------------------------------------------
               {H} (if b then t1 in t2) {Q}
]]
*)

Parameter triple_if : forall b t1 t2 H Q,
  (b = true -> triple t1 H Q) ->
  (b = false -> triple t2 H Q) ->
  triple (trm_if (val_bool b) t1 t2) H Q.

(** The rule for a value [v] can be written as a triple with an
    empty precondition and a postcondition asserting that the
    result value [x] is equal to [v], in the empty heap.
[[
     ----------------------------
      {\[]} v {fun r => \[r = v]}
]]
    Yet, it is more convenient in practice to work with a judgment
    whose conclusion is of the form [{H}v{Q}], for an arbitrary
    [H] and [Q]. For this reason, we prever the following rule for 
    values:
  
      H ==> Q v
      ---------
      {H} v {Q}

    It may not be completely obvious at first sight why this 
    alternative rule is equivalent to the former. We will prove
    the equivalence further in this chapter. *)

Parameter triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.

(** A function definition [trm_fun x t1], expressed as a subterm in a 
    program, evaluates to a value, more precisely to [val_fun x t1].
    Again, we could consider a rule with an empty precondition:

[[
     ------------------------------------------------------
      {\[]} (trm_fun x t1) {fun r => \[r = val_fun x t1]}
]]
   However, we prefer a conclusion of the form [{H}(trm_fun x t1){Q}].
   We thus consider the following rule, very similar to [triple_val]:
*)

Parameter triple_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  triple (trm_fun x t1) H Q.

(** Last but not least, we need a reasoning rule to reason about a
    function application. Consider an application [(v1 v2)].
    Assume [v1] to be a function, that is, to be of the form
    [val_fun x t1]. Then, according to the beta-reduction rule,
    the semantics of [(v1 v2)] is the same as that of [subst x v2 t1].
    Thus, the triple [{H}(v1 v2){Q}] holds if the triple 
    [{H}(subst x v2 t1){Q}] holds. This logic is captured by the
    following rule. *)

Parameter triple_app_fun : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.

(** The generalization to recursive functions is straightforward.
    It is discussed further in this chapter. 
    
    The generalization to functions of several arguments follows
    a similar pattern, although with a few additional technicalities.
    N-ary functions and other language extensions such as records,
    arrays, loops, data constructor and pattern matching are discussed
    in the file [SLFExt.v]. *)


(* ******************************************************* *)
(** ** Specification of primitive operations *)

(** For a complete set of reasoning rules, there remains to present
    the specification for builtin functions. The most interesting
    functions are those that manipulate the state. *)

(** Assume [val_get] to denote the operation for reading a memory cell.
    A call of the form [val_get v'] executes safely if [v'] is of the 
    form [val_loc l] for some location [l], in a state that features
    a memory cell at location [l] with some contents [v]. Such a state
    is described as [l ~~~> v]. The read operation returns a value [r]
    such that [r = v], and the memory state of the operation remains
    unchanged. The specification of a read may is be expressed as: *)

Parameter triple_get : forall v l,
  triple (val_get (val_loc l))
    (l ~~~> v)
    (fun r => \[r = v] \* (l ~~~> v)).

(** Remark: [val_loc] is registered as a coercion, so the triple could
    also be written [triple (val_get l) ...]. *)

(** Assume [val_set] to denote the operation for writing a memory cell.
    A call of the form [val_set v' w] executes safely if [v'] is of the 
    form [val_loc l] for some location [l], in a state [l ~~~> v].
    The write operation updates this state to [l ~~~> w], and returns
    the unit value. In other words, it returns a value [r] such that
    [r = val_unit]. Hence the following specification. *)

Parameter triple_set : forall w l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => \[r = val_unit] \* l ~~~> w).

(** Assume [val_ref] to denote the value that corresponds to the
    builtin operation for allocating a cell with a given contents. 
    A call to [val_ref v] may execute in the empty state and 
    augment the state with a singleton cell, allocated at some 
    location [l], with contents [v]. This new cell is described 
    by the heap predicate [l ~~~> v]. 
    
    The value returned by the operation is the location [val_loc l], 
    that is, the location [l] viewed as a value. Thus, if [r] denotes
    the result value, we have [r = val_loc l] for some [l]. The 
    location [l] needs to be existentially quantified. *)
 
Parameter triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists l, \[r = val_loc l] \* l ~~~> v).

(** The programming language targeted may include other builtin 
    functions, for example arithmetic operations. We here present
    just two examples: addition and division. Others follow a
    similar pattern. 
    
    Assume [val_add] to denote the value that corresponds to the
    builtin operation [+]. A call to an addition [val_add n1 n2] 
    executes in a empty state, and produces an empty state. It
    returns the value [n1+n2]. Formally: *)

Parameter triple_add : forall n1 n2,
  triple (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).

(** A division [val_div n1 n2] is similar, with the only extra
    requirement that the divisor [n2] must be nonzero. *)

Parameter triple_div : forall n1 n2,
  n2 <> 0 ->
  triple (val_div n1 n2)
    \[]
    (fun r => \[r = val_int (Z.quot n1 n2)]).


(* ******************************************************* *)
(** ** Verification proof in Separation Logic *)

(** We have at hand all the necessary rules for carrying out
    actual verification proofs in Separation Logic.
    
    To illustrate this possibility, we next present a verification
    proof for the increment function. *)

(** The proof will use the rule that combines the frame rule
    and the consequence rule (introduced in the previous chapter). *)

Parameter triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.




Module ExampleProof.

Import NotationForVariables NotationForTerms CoercionsFromStrings.


(** The definition in OCaml syntax is: [fun p => p := (!p + 1)].
    In A-normal form syntax, this definition becomes: 
[[
   fun p => 
        let n = !p in
        let m = n+1 in
        p := m
]]
    Using the construct from our embedded language, this 
    definition reformulates as: *)

Definition incr :=
  val_fun "p" (
    trm_let "n" (val_get "p") (
    trm_let "m" (val_add "n" 1) (
    val_set "p" "m"))).

(** Alternatively, using notation, the same program can be written: *)

Definition incr' :=
  VFun 'p :=
    Let 'n := '! 'p in
    Let 'm := 'n '+ 1 in
   'p ':= 'm.

(** Recall from the first chapter the specification of the
    increment function. *)

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1))).
Proof using.
  intros. applys triple_app_fun. { reflexivity. }
  simpl.
  applys triple_let.
  { apply triple_get. }
  intros n'. simpl.
  apply triple_hpure. intros ->.
  applys triple_let. 
  { applys triple_conseq_frame.
    { applys triple_add. }
    { hsimpl. }
    { hsimpl. } }
  intros m'. simpl.
  apply triple_hpure. intros ->.
  applys triple_conseq_frame.
  { applys triple_set. }
  { hsimpl. }
  hsimpl. auto.
Qed.

End ExampleProof.

(** The matter of the next chapter is to streamline is to
    introduce additional technology to streamline the proof
    process, notably by
    - automating the application of the frame rule
    - eliminating the need to manipulate program variables
      and substitutions during the verification proof. *)


(* ####################################################### *)
(** * Additional contents *)

(* ******************************************************* *)
(** ** The combined let-frame rule rule *)

(** Recall the Separation Logic let rule. *)

Parameter triple_let' : forall x t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall v, triple (subst x v t2) (Q1 v) Q) ->
  triple (trm_let x t1 t2) H Q.

(** At first sight, it seems that, to reason about [let x = t1 in t2] 
    in a state described by precondition [H], we need to first reason 
    about [t1] in that same state. Yet, [t1] may well require only a
    subset of that state to evaluate. 

    The "let-frame" rule combines the rule for let-bindings with the
    frame rule to make it more explicit that the precondition [H]
    may be decomposed in the form [H1 \* H2], where [H1] is the part
    needed by [t1], and [H2] denotes the rest of the state. The part
    of the state covered by [H2] remains unmodified during the evaluation
    of [t1], and appears as part of the precondition of [t2].
    The formal statement follows. *)

Lemma triple_let_frame : forall x t1 t2 H H1 H2 Q Q1,
  triple t1 H1 Q1 ->
  H ==> H1 \* H2 ->
  (forall v, triple (subst x v t2) (Q1 v \* H2) Q) ->
  triple (trm_let x t1 t2) H Q.

(* EX2! (rule_conseq) *)
(** Prove the let-frame rule. *)

Proof using.
(* SOLUTION *)
  introv M1 WH M2.
  applys triple_conseq WH.
  { applys triple_let.
    { applys triple_frame. applys M1. }
    { applys M2. } }
  { applys qimpl_refl. }
(* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Alternative presentation for the specifications of builtin functions *)

(** 1. Recall the specification for division. *)

Parameter triple_div' : forall n1 n2,
  n2 <> 0 ->
  triple (val_div n1 n2)
    \[]
    (fun r => \[r = val_int (Z.quot n1 n2)]).

(** Equivalently, we could place the requirement [n2 <> 0] in the 
    precondition: *)

Parameter triple_div'' : forall n1 n2,
  triple (val_div n1 n2)
    \[n2 <> 0]
    (fun r => \[r = val_int (Z.quot n1 n2)]).

(** Yet, placing pure preconditions outside of the triples makes
    it slightly more convient to exploit specifications, so we
    adopt the style that precondition only contain the description
    of heap-allocated data structures. *)

(** 2. Recall the specification for allocation. *)

Parameter triple_ref' : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists l, \[r = val_loc l] \* l ~~~> v).

(** Remark: the postcondition could be equivalently stated using
    a pattern matching instead of an existential. *)

Parameter triple_ref'' : forall v,
  triple (val_ref v)
    \[]
    (fun r => match r with 
              | val_loc l => (l ~~~> v)
              | _ => \[False] 
              end).

(** However, this presentation is less readable and would be 
    fairly cumbersome to work with in practice. *)


(* ******************************************************* *)
(** ** Reasoning rules for recursive functions *)

(** This reasoning rules for functions immediately generalizes 
    to recursive functions. A term describing a recursive 
    function is written [trm_fix f x t1], and the corresponding
    value is written [val_fix f x t1]. *)

Parameter triple_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triple (trm_fix f x t1) H Q.

(** The reasoning rule that corresponds to beta-reduction for
    a recursive function involves two substitutions: a first
    substitution for recursive occurences of the function,
    followed with a second substitution for the argument 
    provided to the call. *)

Parameter triple_app_fix : forall v1 v2 f x t1 H Q,
  v1 = val_fix f x t1 ->
  triple (subst x v2 (subst f v1 t1)) H Q ->
  triple (trm_app v1 v2) H Q.


(* ******************************************************* *)
(** ** Alternative rule for values *)

(** When discussing the reasoning rule for values, we mention
    that the rule could be expressed with an empty precondition,
    as shown next:
[[
     ----------------------------
      {\[]} v {fun r => \[r = v]}
]]
    Let us prove that this rule is equivalent to [triple_val]. *)

(* EX1! (triple_val_minimal) *)
(** Prove the alternative rule for values derivable from [triple_val]. *)

Lemma triple_val_minimal : forall v,
  triple (trm_val v) \[] (fun r => \[r = v]).
Proof using.
(* SOLUTION *)
  intros. applys triple_val. hsimpl. auto.
(* /SOLUTION *)
Qed.

(* EX2! (triple_val_minimal) *)
(** More interestingly, prove that [triple_val] is derivable
    from [triple_val_minimal]. *)

Lemma triple_val' : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using.
(* SOLUTION *)
  introv M. applys triple_conseq_frame.
  { applys triple_val_minimal. }
  { hsimpl. }
  { intros r. hsimpl. intros ->. applys M. }
(* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Proofs for the rules for terms *)

Module Proofs.

(** The proofs for the Separation Logic reasoning rules all follow
    a similar pattern: first establish a corresponding rule for
    Hoare triples, then generalize it to a Separation Logic triple,
    following the definition:
[[  
      Definition triple t H Q :=
       forall H', hoare t (H \* H') ((Q \*+ H') \*+ \Top')
]]
    To establish a reasoning rule w.r.t. a Hoare triple, we reveal
    the definition expressed in terms of the big-step semantics.
[[
      Definition Hoare_triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
        forall s, H s ->
        exists s' v, red s t s' v /\ Q v s'.
]]
    Concretely, we consider a given initial state [s] satisfying the
    precondition, and we have to provide witnesses for the output
    value [v] and output state [s'] such that the reduction holds and
    the postcondition holds.

    Recall that we already employed this two-step scheme in the
    previous chapter, e.g. to establish [rule_conseq]. *)


(* ------------------------------------------------------- *)
(** *** Proof of [triple_val] *)

(** The big-step evaluation rule for values asserts that a value [v]
    evaluates to itself, without modification to the current state [s]. *)

Parameter red_val : forall s v,
  red s v s v.

(** The Hoare version of the reasoning rule for values is as follows. *)

Lemma hoare_val : forall v H Q,
  H ==> Q v ->
  hoare (trm_val v) H Q.
Proof using.
  (* 1. We unfold the definition of [hoare]. *)
  introv M. intros h Hh. 
  (* 2. We provide the witnesses for the output value and heap.
        These witnesses are dictated by the statement of [red_val]. *)
  exists h v. splits.
  { (* 3. We invoke the big-step rule [red_val] *)
    applys red_val. }
  { (* 4. We establish the postcondition, exploiting the entailment hypothesis. *)
    applys M. auto. }
Qed.

(** The Separation Logic version of the rule then follows. *)

Lemma triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using.
  (* 1. We unfold the definition of [triple] to reveal a [hoare] judgment. *) 
  introv M. intros H'.
  (* 2. We invoke the reasoning rule [hoare_val] that we have just established. *)
  applys hoare_val.
  (* 3. We exploit the assumption and conclude using [hsimpl]. *)
  hchange M. hsimpl.
Qed.

(** Remark: in the proof of [hoare_val], the witnesses [h] and [v] are 
    contrained by the rule [red_val]. It is thus not needed to provide
    them explicitly: we can let Coq inference figure them out. *)

Lemma hoare_val' : forall v H Q,
  H ==> Q v ->
  hoare (trm_val v) H Q.
Proof using.
  introv M. intros h Hh. exists __ __. split.
  { applys red_val. }
  { applys* M. }
Qed.

(** Nevertheless, considering that these witnesses are just single-letter
    variables, to improve readability of proofs in this chapter, we will
    thereafter provide the witnesses explicitly. *)


(* ------------------------------------------------------- *)
(** *** Proof of [triple_fun] *)

(** The proof of [triple_fun] is essentially identical to that
    of [triple_val], so we do not include it here. *)


(* ------------------------------------------------------- *)
(** *** Proof of [triple_seq] *)

(** The big-step evaluation rule for a sequence is given next. *)

Parameter red_seq : forall s1 s2 s3 t1 t2 r1 r,
  red s1 t1 s2 r1 ->
  red s2 t2 s3 r ->
  red s1 (trm_seq t1 t2) s3 r.

(** The Hoare triple version of the reasoning rule is proved as follows. *)

Lemma hoare_seq : forall t1 t2 H Q H1,
  hoare t1 H (fun r => H1) ->
  hoare t2 H1 Q ->
  hoare (trm_seq t1 t2) H Q.
Proof using.
  (* 1. We unfold the definition of [hoare]. Let [K0] describe the initial state. *)
  introv M1 M2 K0. (* optional: *) unfolds hoare.
  (* 2. We exploit the first hypothesis to obtain information about
        the evaluation of the first subterm [t1].
        The state before [t1] executes is described by [K0].
        The state after [t1] executes is described by [K1]. *)
  forwards (h1'&v1&R1&K1): (rm M1) K0.
  (* 3. We exploit the second hypothesis to obtain information about
        the evaluation of the first subterm [t2].
        The state before [t2] executes is described by [K1].
        The state after [t2] executes is described by [K2]. *)
  forwards (h2'&v2&R2&K2): (rm M2) K1.
  (* 4. We provide witness for the output value and heap.
        They correspond to those produced by the evaluation of [t2]. *)
  exists h2' v2. split.
  { (* 5. We invoke the big-step rule. *) 
    applys red_seq R1 R2. } 
  { (* 6. We establish the final postcondition, which is directly 
       inherited from the reasoning on [t2]. *) 
    apply K2. }
Qed.

(** The Separation Logic reasoning rule is proved as follows. *)

Lemma triple_seq' : forall t1 t2 H Q H1,
  triple t1 H (fun r => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof using.
  (* 1. We unfold the definition of [triple] to reveal a [hoare] judgment. *)
  introv M1 M2. intros H'. (* optional: *) unfolds triple.
  (* 2. We invoke the reasoning rule [hoare_seq] that we have just established. *)
  applys hoare_seq.
  { (* 3. For the hypothesis on the first subterm [t1], 
       we can invoke directly our first hypothesis. *)
    applys M1. }
  { (* 4. For the hypothesis on the first subterm [t2], 
       we need a little more work to exploit our second hypothesis.
       Indeed, the precondition features an extra [\Top'].
       To handle it, we need to instantiate [M2] with [H' \* \Top'],
       then merge the two [\Top'] that appear into a single one.
       We could begin the proof script with:
         [specializes M2 (H' \* \Top'). rewrite <- hstar_assoc in M2.]
       However, it is simpler to directly invoke the consequence rule,
       and let [hsimpl] do all the tedious work for us. *)
    applys hoare_conseq. { applys M2. } { hsimpl. } { hsimpl. } }
Qed.


(* ------------------------------------------------------- *)
(** *** Proof of [triple_let] *)

(** Following the same proof scheme as for [triple_seq], establish
    the reasoning rule for [triple_let]. Make sure to first state
    and prove [hoare_let]. *)

(** The starting point is the big-step evaluation rule for a let-binding. *)

Parameter red_let : forall s1 s2 s3 x t1 t2 v1 r,
  red s1 t1 s2 v1 ->
  red s2 (subst x v1 t2) s3 r ->
  red s1 (trm_let x t1 t2) s3 r.

(* EX1! (triple_let) *)

Lemma triple_let : forall x t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall v, triple (subst x v t2) (Q1 v) Q) ->
  triple (trm_let x t1 t2) H Q.
Proof using.
(* SOLUTION *)

  Lemma hoare_let : forall x t1 t2 H Q Q1,
    hoare t1 H Q1 ->
    (forall v, hoare (subst x v t2) (Q1 v) Q) ->
    hoare (trm_let x t1 t2) H Q.
  Proof using.
    introv M1 M2 K0.
    forwards (h1'&v1&R1&K1): (rm M1) K0.
    forwards (h2'&v2&R2&K2): (rm M2) K1.
    exists h2' v2. split. { applys red_let R1 R2. } { apply K2. }
  Qed.

  unfold triple. introv M1 M2. intros H'. applys hoare_let.
  { applys M1. }
  { intros v. applys hoare_conseq.
    { applys M2. } { hsimpl. } { hsimpl. } }
(* /SOLUTION *)
Qed.


(* ------------------------------------------------------- *)
(** *** Proof of [triple_if] *)

(** The treatment of conditional can be handled in a similar way. *)

Parameter red_if_bool : forall s1 s2 b r t1 t2,
  (b = true -> red s1 t1 s2 r) ->
  (b = false -> red s1 t2 s2 r) ->
  red s1 (trm_if b t1 t2) s2 r.

Lemma hoare_if : forall b t1 t2 H Q,
  (b = true -> hoare t1 H Q) ->
  (b = false -> hoare t2 H Q) ->
  hoare (trm_if b t1 t2) H Q.
Proof using.
  introv M1 M2. intros h K0. destruct b.
  { forwards* (h1'&v1&R1&K1): (rm M1) K0.
    exists h1' v1. split*. { applys* red_if. } }
  { forwards* (h1'&v1&R1&K1): (rm M2) K0.
    exists h1' v1. split*. { applys* red_if. } }
Qed.

Lemma triple_if' : forall b t1 t2 H Q,
  (b = true -> triple t1 H Q) ->
  (b = false -> triple t2 H Q) ->
  triple (trm_if (val_bool b) t1 t2) H Q.
Proof using.
  unfold triple. introv M1 M2. intros H'. 
  applys hoare_if; intros Eb.
  { applys* M1. }
  { applys* M2. }
Qed.

(** Observe that the above proofs contain a fair amount of duplication,
    due to the symmetry between the [b=true] and [b=false] branches.
    One way to conveniently factorize the proof arguments is to employ
    Coq's conditional to express the semantics of a term conditional. 
    
    First, we establish a corrolary to [red_if], expressed using a 
    single premise. *)

Lemma red_if_bool_case : forall m1 m2 b r t1 t2,
  red m1 (if b then t1 else t2) m2 r ->
  red m1 (trm_if b t1 t2) m2 r.
Proof using.
  intros. case_if; applys red_if_bool; auto_false.
Qed.

(** Then, we are able to establish the Hoare triple and the Separation
    Logic triple with much less effort. *)

Lemma hoare_if_case : forall (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros h K0. 
  forwards (h'&v&R1&K1): (rm M1) K0.
  exists h' v. split. { applys red_if R1. } { applys K1. }
Qed.

Lemma triple_if_case : forall b t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if (val_bool b) t1 t2) H Q.
Proof using.
  unfold triple. introv M1. intros H'.
  applys hoare_if_case. applys M1.
Qed.


(* ------------------------------------------------------- *)
(** *** Proof of [triple_app_fun] *)

(** The reasoning rule for an application asserts that the
    a pre- and poscondition hold for a beta-redex [(val_fun x t1) v2] 
    provided that they hold for the term [subst x v2 t1].

    This result follows directly from the big-step evaluation rule
    for applications. *)

Parameter red_app_fun : forall s1 s2 v1 v2 x t1 r,
  v1 = val_fun x t1 ->
  red s1 (subst x v2 t1) s2 r ->
  red s1 (trm_app v1 v2) s2 r.

(* EX2! (hoare_app_fun) *)

Lemma hoare_app_fun : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  hoare (subst x v2 t1) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof using.
(* SOLUTION *)
  introv E M. intros h K0. forwards (h'&v&R1&K1): (rm M) K0.
  exists h' v. splits. { applys red_app_fun E R1. } { applys K1. }
(* /SOLUTION *)
Qed.

(* EX2! (triple_app_fun) *)

Lemma triple_app_fun : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
(* SOLUTION *)
  unfold triple. introv E M1. intros H'.
  applys hoare_app_fun E. applys M1.
(* /SOLUTION *)
Qed.


(* ------------------------------------------------------- *)
(** *** Triple for terms with same semantics *)

(** The proofs above can in fact be obtained by invoking a general
    result: if [t2] has the same semantics as [t1], then any triple
    valid for [t1] is also valid for [t2]. *)

Lemma hoare_same_semantics : forall t1 t2 H Q,
  (forall s s' r, red s t1 s' r -> red s t2 s' r) ->
  hoare t1 H Q ->
  hoare t2 H Q.
Proof using.
  introv E M1 K0. forwards (s'&v&R1&K1): M1 K0.
  exists s' v. split. { applys E R1. } { applys K1. }
Qed.

Lemma triple_same_semantics : forall t1 t2 H Q,
  (forall s s' r, red s t1 s' r -> red s t2 s' r) ->
  triple t1 H Q ->
  triple t2 H Q.
Proof using.
  introv E M1. intros H'. applys hoare_same_semantics E. applys M1.
Qed.

(** Using this general result, we can revisit the proof of 
    [triple_app_fun] in a much more succint way. *)

Lemma triple_app_fun' : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
  introv E M1. applys triple_same_semantics M1.
  introv R. applys red_app_fun E R.
Qed.


(* ******************************************************* *)
(** ** Proofs for the specification of primitive operations *)

(** The proofs for establishing the Separation Logic reasoning rules
    for [ref], [get] and [set] follow a similar proof pattern,
    that is, they go through the proofs of rules for Hoare triples.

    Unlike before, however, the Hoare triples are not directly
    established with respect to the big-step evaluation rules.
    Instead, we start by proving corrolaries to the big-step rules
    to reformulate them in a way that give already them a flavor
    of "Separation Logic". Concretely, we reformulate the evaluation
    rules, which are expressed in terms of read and updates in finite 
    maps, to be expressed instead entirely in terms of disjoint unions. 

    The introduction of these disjoint union operations then 
    significantly eases the justification of the separating 
    conjunctions that appear in the targeted Separation Logic triples. *)


(* ------------------------------------------------------- *)
(** *** Read in a reference *)

(** The big-step rule for [get l] requires that [l] be in the
    domain of the current state [s], and returns the result of
    reading in [s] at location [l]. *)

Parameter red_get : forall s l,
  fmap_indom s l ->
  red s (val_get (val_loc l)) s (fmap_read s l).

(** We reformulate this lemma by isolating from the current state [s]
    the singleon heap made of the cell at location [l], and let [s2]
    denote the rest of the heap. When the singleton heap is described
    as [fmap_single l v], then [v] is the result value returned by
    [get l]. *)

Lemma red_get_sep : forall s s2 l v, 
  s = (fmap_single l v) \u s2 ->
  red s (val_get (val_loc l)) s v.

(** The proof of this lemma is of little interest. We show it only to
   demonstrate that it relies only a basic facts related to finite maps. *)

Proof using.
  introv ->. forwards Dv: fmap_indom_single l v.
  applys_eq red_get 1.
  { applys~ fmap_indom_union_l. }
  { rewrite~ fmap_read_union_l. rewrite~ fmap_read_single. }
Qed.

(** Remark: the acute reader may have noticed that the lemma above
    seems to be missing an hypothesis [fmap_disjoint (fmap_single l v) s2],
    or, equivalently, [~ fmap_indom s2 l]. But in fact, the lemma
    holds without this assumption. Indeed, the read in [fmap_union s1 s2]
    at a location [l] from the domain of [s1] provides the result of
    reading at [l] in [s1], regardless of whether [s2] rebinds or not
    the same key [l]. *)

(** Our goal is to establish the triple:
[[
  triple (val_get l)
    (l ~~~> v)
    (fun r => \[r = v] \* (l ~~~> v)).
]]
    Establishing this lemma will requires us to reason about
    propositions of the form [(\[P] \* H) h] and [(l ~~~> v) h].
    To that end, recall from the first chapter the following two
    lemmas. *)

Parameter hsingle_inv: forall l v h,
  (l ~~~> v) h ->
  h = fmap_single l v.

Parameter hstar_hpure_iff : forall P H h, 
  (\[P] \* H) h <-> (P /\ H h).

(** First, we establish the desired result on the [hoare] judgment. *)

Lemma hoare_get : forall H v l,
  hoare (val_get l)
    ((l ~~~> v) \* H)
    (fun r => \[r = v] \* (l ~~~> v) \* H).
Proof using.
  intros. intros h K0. exists h v. split.
  { destruct K0 as (h1&h2&P1&P2&D&U).
    lets E1: hsingle_inv P1. subst h1.
    applys red_get_sep U. }
  { rewrite hstar_hpure. auto. }
Qed.

Lemma triple_get : forall v l,
  triple (val_get l)
    (l ~~~> v)
    (fun r => \[r = v] \* (l ~~~> v)).
Proof using.
  intros. intros H'. applys hoare_conseq.
  { applys hoare_get. } 
  { hsimpl. }
  { hsimpl. auto. }
Qed.




(* ------------------------------------------------------- *)
(** *** Allocation of a reference *)

(** Reduction rule for reference *)

Parameter red_ref : forall s1 s2 v l,
  ~ fmap_indom s1 l ->
  s2 = fmap_update s1 l v ->
  red s1 (val_ref v) s2 (val_loc l).

(** Derived reduction rule, reformulated without the "fmap update"
    operationusing only singleton union of disjoint heaps. *)

Lemma red_ref_sep : forall s1 s2 v l,
  s2 = fmap_single l v ->
  fmap_disjoint s2 s1 ->
  red s1 (val_ref v) (fmap_union s2 s1) (val_loc l).

(** It is not needed to follow through the proof. *)

Proof using.
  introv -> D. forwards Dv: fmap_indom_single l v.
  rewrite <- fmap_update_eq_union_single. applys~ red_ref.
  { intros N. applys~ fmap_disjoint_inv_not_indom_both D N. }
Qed.

(** We need the existence of fresh locations *)



Parameter fmap_exists_not_indom : forall h,
  exists l, ~ fmap_indom h l.

Parameter fmap_single_fresh : forall h v,
  exists l, \# (fmap_single l v) h.

(** Recall also *)


Parameter hstar_intro : forall H1 H2 h1 h2,
  H1 h1 ->
  H2 h2 ->
  fmap_disjoint h1 h2 ->
  (H1 \* H2) (h1 \u h2).

Parameter hsingle_intro : forall l v,
  (l ~~~> v) (fmap_single l v).


(** Using this rule, we can state a Hoare triple for the [ref]
    operation. *)

Lemma hoare_ref : forall H v,
  hoare (val_ref v)
    H
    (fun r => (\exists l, \[r = val_loc l] \* l ~~~> v) \* H).
Proof using.
  (* 1. We unfold the definition of [hoare]. *)
  intros. intros s1 K0.
  (* 2. We claim the disjointness relation 
       [fmap_disjoint (fmap_single l v) s1]. *)
  forwards~ (l&D): (fmap_single_fresh s1 v).
  (* 3. We provide the witnesses for the reduction,
        as dictated by [red_ref_sep]. *)
  exists ((fmap_single l v) \u s1) (val_loc l). split.
  { (* 4. We exploit [red_ref_sep], which has exactly the desired shape! *)
    applys red_ref_sep D. auto. }
  { (* 5. We establish the postcondition 
       [(\exists l, \[r = val_loc l] \* l ~~~> v) \* H]
       by providing [p] and the relevant pieces of heap. *)
    applys hstar_intro.
    { exists l. rewrite hstar_hpure.
      split. { auto. } { applys hsingle_intro. } }
    { applys K0. }
    { applys D. } }
Qed.

(** Then, we can derive the result on Separation Logic triple
    by simply invoking the previous result with the rule of
    consequence. *)

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists l, \[r = val_loc l] \* l ~~~> v).
Proof using.
  intros. intros H'. applys hoare_conseq.
  { applys hoare_ref. } 
  { hsimpl. }
  { hsimpl. auto. }
Qed.



(* TODO: deactivate disjointness notation *)

(* ------------------------------------------------------- *)
(** *** Write in a reference *)

Parameter red_set : forall m l v,
   fmap_indom m l ->
   red m (val_set (val_loc l) v) (fmap_update m l v) val_unit.

Lemma red_set_sep : forall s1 s2 h2 l v1 v2,
  s1 = fmap_union (fmap_single l v1) h2 ->
  s2 = fmap_union (fmap_single l v2) h2 ->
  fmap_disjoint (fmap_single l v1) h2 ->
  red s1 (val_set (val_loc l) v2) s2 val_unit.
Proof using.
  introv -> -> D. forwards Dv: fmap_indom_single l v1.
  applys_eq red_set 2.
  { applys~ fmap_indom_union_l. }
  { rewrite~ fmap_update_union_l. fequals.
    rewrite~ fmap_update_single. }
Qed.


Parameter fmap_disjoint_single_set : forall l v1 v2 h2,
  fmap_disjoint (fmap_single l v1) h2 ->
  fmap_disjoint (fmap_single l v2) h2.

Lemma hoare_set : forall H w l v,
  hoare (val_set (val_loc l) w)
    ((l ~~~> v) \* H)
    (fun r => \[r = val_unit] \* (l ~~~> w) \* H).
Proof using. 
  intros. intros h K0. destruct K0 as (h1&h2&P1&P2&D&U). 
  lets E1: hsingle_inv P1.
  sets h1': (fmap_single l w).
  exists (h1' \u h2) val_unit. split.
  { subst h1 h1'. applys red_set_sep U D. auto. }
  { rewrite hstar_hpure. split~. applys hstar_intro.
    { applys hsingle_intro. }
    { auto. }
    { subst h1. applys fmap_disjoint_single_set D. } }
Qed.

Lemma triple_set' : forall w l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => \[r = val_unit] \* l ~~~> w).
Proof using.
  intros. intros H'. applys hoare_conseq.
  { applys hoare_set. } 
  { hsimpl. }
  { hsimpl. auto. }
Qed.

End Proofs.


