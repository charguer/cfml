(**

Separation Logic Foundations

Chapter: "Rules".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.

(** The file [SepBase.v] contains definitions that are essentially similar
    to those from [SLFHprop.v] and [SLFHimpl.v], with just a few differences:

    - [SepBase] makes the definition of Separation Logic operators opaque.
      Thus, one cannot unfold the definition of [hstar], [hpure], [htop], etc...
      To carry out reasoning, one must use the introduction and elimination
      lemmas (e.g. [hstar_intro], [hstar_elim]). These lemmas enforce abstraction:
      they ensure that the proofs do not depend on which of the several possible 
      set of definitions is chosen to construct the Separation Logic.

    - The predicate [Hoare_triple] is abbreviated as [hoare],

    - The predicate [triple] is defined not using [\Top] to handle discarded
      pieces of heap, but using a specific instance of a general predicate
      called [\GC]. For the instance considered in [SepBase.v], it turns out
      that [\GC = \Top]. Thus, the difference is irrelevant. To help forget
      about this irrelevant difference, we overload the notation [\Top] for [\GC],
      so that everything looks the same as in [SLFHprop.v].

    - [SepBase.v] uses a definition of [l ~~~> v] which moreover enforces [l] to 
      not be the [null] location. In this file, we will completely ignore this
      extra requirement.

    - [Semantics.v] exports a definition of substitution on terms that does
      not compute in Coq. Yet, to present examples in this file, we need a
      version that computes. Thus, we import the one defined in the file
      [SubstExec.v], under the name [subst_exec]. We then overload [subst] 
      to mean [subst_exec].

All the necessary tweaks are set up in the few lines that follow. *)

From Sep Require Export SepBase SubstExec.

Notation "\Top" := hgc.

Definition triple_conseq_frame_htop := triple_conseq_frame_hgc.

Definition subst := subst_exec.

Parameter htop_intro : forall h,
  \Top h.

Parameter hsingle_intro : forall l v,
  (l ~~~> v) (fmap_single l v).

Parameter hsingle_inv: forall l v h,
  (l ~~~> v) h ->
  h = fmap_single l v.


(* ####################################################### *)
(** * The chapter in a rush *)

(** This chapter first summarizes the structural rules from
    Separation Logic. It then recall the syntax and semantics
    of the programming language considered, and presents the 
    statement and proofs for the reasoning rules for terms
    and primitive operations. *)


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
(** ** Semantic of terms *)

(** In order to establish reasoning rule for terms (e.g., a
    rule for a let-binding), it is useful to briefly review
    the grammar of terms and the formal (big-step) semantics
    associated with the language that we consider. 

    Remark: the language presented here is a simplified language
    compared with that defined in [Semantics.v]. *)

Module SyntaxAndSemantics.

(** The grammar for values includes unit, boolean, integers,
    locations, functions, recursive functions, and primitive 
    operations. For the latter, we here only include a few: 
    [ref], [get], and [set], [add] and [div]. *)

Inductive val : Type :=
  | val_unit : val
  | val_bool : bool -> val
  | val_int : int -> val
  | val_loc : loc -> val
  | val_fun : var -> trm -> val
  | val_fix : var -> var -> trm -> val
  | val_ref : val
  | val_get : val
  | val_set : val
  | val_add : val
  | val_div : val

(** The grammar for terms includes values, variables, 
    function definitions, recursive function definitions,
    function applications, sequences, let-bindings, and
    conditionals. *)

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_fun : var -> trm -> trm
  | trm_fix : var -> var -> trm -> trm
  | trm_app : trm -> trm -> trm
  | trm_seq : trm -> trm -> trm
  | trm_let : var -> trm -> trm -> trm
  | trm_if : trm -> trm -> trm -> trm.

(** Note that the grammar of values is mutually inductive with that
    of terms. The type [val] is intented to denote only closed 
    values. In particular, a [val_fun x t] or a [val_fix f x t]
    should not contain any free variable. *)

(** The beta-reduction rule involves a substitution function.

    The substitution function, written [subst y w t], replaces all
    occurences of a variable [y] with a value [w] inside a term [t].
    This definition exploits the comparison function [var_eq x y], 
    which produces a boolean indicating whether [x] and [y] denote
    the same variable. 

    Because [trm_val v] denotes a closed value, any substitution on
    it should behave like the identity. For the remaining constructs,
    substitution is essentially structural: it traverses through all 
    subterms until reaching a variable. The only specific care is to
    ensure that substitution is capture-avoiding: an operation 
    [subst y w t] does not recurse below the scope of binders whose
    name is also [y]. *)

Fixpoint subst (y:var) (w:val) (t:trm) : trm :=
  let aux t := subst y w t in
  let if_y_eq x t1 t2 := if var_eq x y then t1 else t2 in
  let aux_no_capt x t := if_y_eq x t (aux t) in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if_y_eq x (trm_val w) t
  | trm_fun x t1 => trm_fun x (aux_no_capt x t1)
  | trm_fix f x t1 => trm_fix f x (if_y_eq f t1 (aux_no_capt x t1))
  | trm_app t1 t2 => trm_app (aux t1) (aux t2)
  | trm_seq t1 t2 => trm_seq  (aux t1) (aux t2)
  | trm_let x t1 t2 => trm_let x (aux t1) (aux_no_capt x t2)
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  end.

(** The evaluation rules involves the state. Recall that a state is
    a finite map from location to values. *)

Definition state := fmap loc val.

(** For technical reasons, to enable reading in a state, we need
    to justify that the grammar of values is inhabited. *)

Instance Inhab_val : Inhab val.
Proof using. apply (Inhab_of_val val_unit). Qed.

(** To improve the readability of the evaluation rules, we take 
    advantage of both implicit types and coercions. *)

Implicit Types v r : val.
Implicit Types t : trm.
Implicit Types s : state.

(** We declare [trm_val] as a coercion, so that we may freely write
    [v] wherever a term is expected, to mean [trm_val v]. *)

Coercion trm_val : val >-> trm.

(** We declare [trm_app] as a coercion, so that we may write 
    [t1 t2] as a shorthand for [trm_app t1 t2]. *)

Coercion trm_app : trm >-> Funclass.

(** The big-step evaluation judgment takes the form [eval s t s' v],
    describing that, starting from state [s], the evaluation of the 
    term [t] terminates in a state [s'], producing an output value [v].
    
    For simplicity, in this chapter, we assume terms in "A-normal form":
    the arguments of applications and of conditionals are restricted to 
    variables and value. Such a requirement does not limit expressiveness.

    For example, a source program may not use the general form
    [trm_if t0 t1 t2], but only the form [trm_if v0 t1 t2], 
    where [v0] denotes a variable or a value. This is not a 
    restriction, because [trm_if t0 t1 t2] can be encoded as 
    [let x = t0 in if x then t1 else t2]. *)
    
Inductive eval : state -> trm -> state -> val -> Prop :=

  (* [eval] for values and function definitions *)

  | eval_val : forall s v,
      eval s (trm_val v) s v
  | eval_fun : forall s x t1,
      eval s (trm_fun x t1) s (val_fun x t1)
  | eval_fix : forall s f x t1,
      eval s (trm_fix f x t1) s (val_fix f x t1)

  (* [eval] for function applications *)

  | eval_app_fun : forall s1 s2 v1 v2 x t1 v,
      v1 = val_fun x t1 ->
      eval s1 (subst x v2 t1) s2 v ->
      eval s1 (trm_app v1 v2) s2 v
  | eval_app_fix : forall s1 s2 v1 v2 f x t1 v,
      v1 = val_fix f x t1 ->
      eval s1 (subst x v2 (subst f v1 t1)) s2 v ->
      eval s1 (trm_app v1 v2) s2 v

  (* [eval] for structural constructs *)

  | eval_seq : forall s1 s2 s3 t1 t2 v1 v,
      eval s1 t1 s2 v1 ->
      eval s2 t2 s3 v ->
      eval s1 (trm_seq t1 t2) s3 v
  | eval_let : forall s1 s2 s3 x t1 t2 v1 r, 
      eval s1 t1 s2 v1 ->
      eval s2 (subst x v1 t2) s3 r ->
      eval s1 (trm_let x t1 t2) s3 r
  | eval_if : forall s1 s2 b v t1 t2,
      (b = true -> eval s1 t1 s2 v) ->
      (b = false -> eval s1 t2 s2 v) ->
      eval s1 (trm_if (val_bool b) t1 t2) s2 v

  (* [eval] for primitive operations *)

  | eval_add : forall s n1 n2,
      eval s (val_add (val_int n1) (val_int n2)) s (val_int (n1 + n2))
  | eval_div : forall s n1 n2,
      n2 <> 0 ->
      eval s (val_div (val_int n1) (val_int n2)) s (val_int (Z.quot n1 n2))
  | eval_ref : forall s v l,
      ~ fmap_indom s l ->
      eval s (val_ref v) (fmap_update s l v) (val_loc l)
  | eval_get : forall s l,
      fmap_indom s l ->
      eval s (val_get (val_loc l)) s (fmap_read s l)
  | eval_set : forall s l v,
      fmap_indom s l ->
      eval s (val_set (val_loc l) v) (fmap_update s l v) val_unit.

End SyntaxAndSemantics.

(** In the rest of this file, we technically depend on the definitions 
    from [Semantics.v] and [SepBase.v]. For our purposes, these
    definitions are equivalent to the ones given above. *)

Implicit Types x f : var.
Implicit Types b : bool.
Implicit Types l : loc.
Implicit Types n : int.
Implicit Types v w r : val.
Implicit Types t : trm.
Implicit Types h : heap.
Implicit Types s : state.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.


(* ******************************************************* *)
(** ** Rules for terms *)

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


Module ExampleProofs.

Import NotationForVariables NotationForTerms CoercionsFromStrings.


(* ------------------------------------------------------- *)
(** *** Proof of [incr] *)

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
  intros. applys triple_app_fun. { reflexivity. } simpl.
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


(* ------------------------------------------------------- *)
(** *** Proof of [mysucc] *)

(** Recall from the previous chapter the combined structural
    rule [triple_conseq_frame_htop], which generalizes the rule
    [triple_conseq_frame] with the possibility to discard
    undesired heap predicate. This rule will be handy at
    some point in the exercise that follows. *)

Parameter triple_conseq_frame_htop : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q \*+ \Top ->
  triple t H Q.

(** Consider the following function, written in OCaml syntax:
[[
     fun n => 
        let r = ref n in
        incr r;
        !r
]]
    Using the notation for our embedded language, we write: *)

Definition mysucc :=
  VFun 'n :=
    Let 'r := val_ref 'n in
    incr 'r ';
    '! 'r.

(* EX3! (triple_incr) *)
(** Specify and verify the function [mysucc]. *)

(* SOLUTION *)
Lemma triple_mysucc : forall (n:int),
  triple (trm_app mysucc n)
    \[]
    (fun v => \[v = n+1]).
Proof using.
  intros. applys triple_app_fun. { reflexivity. } simpl.
  applys triple_let.
  { apply triple_ref. }
  intros r. simpl.
  apply triple_hexists. intros l.
  apply triple_hpure. intros ->.
  applys triple_seq.
  { applys triple_conseq_frame.
    { applys triple_incr. }
    { hsimpl. }
    { hsimpl. } }
  applys triple_conseq_frame_htop.
  { applys triple_get. }
  { hsimpl. }
  { hsimpl. auto. }
Qed.
(* /SOLUTION *)

End ExampleProofs.

(** The matter of the next chapter is to introduce additional
    technology to streamline the proof process, notably by
    - automating the application of the frame rule
    - eliminating the need to manipulate program variables
      and substitutions during the verification proof. *)

(** The rest of this chapter is concerned with alternative
    statements of the reasoning rules, and the proofs of the
    reasoning rules. *)


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
       forall H', hoare t (H \* H') ((Q \*+ H') \*+ \Top)
]]
    To establish a reasoning rule w.r.t. a Hoare triple, we reveal
    the definition expressed in terms of the big-step semantics.
[[
      Definition Hoare_triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
        forall s, H s ->
        exists s' v, eval s t s' v /\ Q v s'.
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

Parameter eval_val : forall s v,
  eval s v s v.

(** The Hoare version of the reasoning rule for values is as follows. *)

Lemma hoare_val : forall v H Q,
  H ==> Q v ->
  hoare (trm_val v) H Q.
Proof using.
  (* 1. We unfold the definition of [hoare]. *)
  introv M. intros s K0. 
  (* 2. We provide the witnesses for the output value and heap.
        These witnesses are dictated by the statement of [red_val]. *)
  exists s v. splits.
  { (* 3. We invoke the big-step rule [red_val] *)
    applys eval_val. }
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
  { applys eval_val. }
  { applys* M. }
Qed.

(** Nevertheless, considering that these witnesses are just single-letter
    variables, to improve readability of proofs in this chapter, we will
    thereafter provide the witnesses explicitly. *)


(* ------------------------------------------------------- *)
(** *** Proof of [triple_fun] and [triple_fix] *)

(** The proofs for [triple_fun] and [triple_fix] are essentially 
    identical to that of [triple_val], so we do not include them
    here. *)


(* ------------------------------------------------------- *)
(** *** Proof of [triple_seq] *)

(** The big-step evaluation rule for a sequence is given next. *)

Parameter eval_seq : forall s1 s2 s3 t1 t2 v1 v,
  eval s1 t1 s2 v1 ->
  eval s2 t2 s3 v ->
  eval s1 (trm_seq t1 t2) s3 v.

(** The Hoare triple version of the reasoning rule is proved as follows. *)

Lemma hoare_seq : forall t1 t2 H Q H1,
  hoare t1 H (fun v => H1) ->
  hoare t2 H1 Q ->
  hoare (trm_seq t1 t2) H Q.
Proof using.
  (* 1. We unfold the definition of [hoare]. Let [K0] describe the initial state. *)
  introv M1 M2. intros s K0. (* optional: *) unfolds hoare.
  (* 2. We exploit the first hypothesis to obtain information about
        the evaluation of the first subterm [t1].
        The state before [t1] executes is described by [K0].
        The state after [t1] executes is described by [K1]. *)
  forwards (s1'&v1&R1&K1): (rm M1) K0.
  (* 3. We exploit the second hypothesis to obtain information about
        the evaluation of the first subterm [t2].
        The state before [t2] executes is described by [K1].
        The state after [t2] executes is described by [K2]. *)
  forwards (s2'&v2&R2&K2): (rm M2) K1.
  (* 4. We provide witness for the output value and heap.
        They correspond to those produced by the evaluation of [t2]. *)
  exists s2' v2. split.
  { (* 5. We invoke the big-step rule. *) 
    applys eval_seq R1 R2. } 
  { (* 6. We establish the final postcondition, which is directly 
       inherited from the reasoning on [t2]. *) 
    apply K2. }
Qed.

(** The Separation Logic reasoning rule is proved as follows. *)

Lemma triple_seq : forall t1 t2 H Q H1,
  triple t1 H (fun v => H1) ->
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
       Indeed, the precondition features an extra [\Top].
       To handle it, we need to instantiate [M2] with [H' \* \Top],
       then merge the two [\Top] that appear into a single one.
       We could begin the proof script with:
         [specializes M2 (H' \* \Top). rewrite <- hstar_assoc in M2.]
       However, it is simpler to directly invoke the consequence rule,
       and let [hsimpl] do all the tedious work for us. *)
    applys hoare_conseq. { applys M2. } { hsimpl. } { hsimpl. } }
Qed.


(* ------------------------------------------------------- *)
(** *** Proof of [triple_let] *)

(** Recall the big-step evaluation rule for a let-binding. *)

Parameter eval_let : forall s1 s2 s3 x t1 t2 v1 v,
  eval s1 t1 s2 v1 ->
  eval s2 (subst x v1 t2) s3 v ->
  eval s1 (trm_let x t1 t2) s3 v.

(* EX1! (triple_let) *)
(** Following the same proof scheme as for [triple_seq], establish
    the reasoning rule for [triple_let]. Make sure to first state
    and prove [hoare_let]. *)

(* SOLUTION *)
Lemma hoare_let : forall x t1 t2 H Q Q1,
  hoare t1 H Q1 ->
  (forall v, hoare (subst x v t2) (Q1 v) Q) ->
  hoare (trm_let x t1 t2) H Q.
Proof using.
  introv M1 M2 K0.
  forwards (s1'&v1&R1&K1): (rm M1) K0.
  forwards (s2'&v2&R2&K2): (rm M2) K1.
  exists s2' v2. split. { applys eval_let R1 R2. } { apply K2. }
Qed.

Lemma triple_let : forall x t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall v, triple (subst x v t2) (Q1 v) Q) ->
  triple (trm_let x t1 t2) H Q.
Proof using.
  unfold triple. introv M1 M2. intros H'. applys hoare_let.
  { applys M1. }
  { intros v. applys hoare_conseq.
    { applys M2. } { hsimpl. } { hsimpl. } }
Qed.
(* /SOLUTION *)


(* ------------------------------------------------------- *)
(** *** Proof of [triple_if] *)

(** The treatment of conditional can be handled in a similar way. *)

Parameter eval_if_bool : forall s1 s2 b v t1 t2,
  (b = true -> eval s1 t1 s2 v) ->
  (b = false -> eval s1 t2 s2 v) ->
  eval s1 (trm_if b t1 t2) s2 v.

Lemma hoare_if : forall b t1 t2 H Q,
  (b = true -> hoare t1 H Q) ->
  (b = false -> hoare t2 H Q) ->
  hoare (trm_if b t1 t2) H Q.
Proof using.
  introv M1 M2. intros s K0. destruct b.
  { forwards* (s1'&v1&R1&K1): (rm M1) K0.
    exists s1' v1. split*. { applys* eval_if. } }
  { forwards* (s1'&v1&R1&K1): (rm M2) K0.
    exists s1' v1. split*. { applys* eval_if. } }
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

    First, we establish a corollary to [red_if], expressed using a 
    single premise. *)

Lemma eval_if_case : forall s1 s2 b v t1 t2,
  eval s1 (if b then t1 else t2) s2 v ->
  eval s1 (trm_if b t1 t2) s2 v.
Proof using.
  intros. case_if; applys eval_if_bool; auto_false.
Qed.

(** Then, we are able to establish the Hoare triple and the Separation
    Logic triple with much less effort. *)

Lemma hoare_if_case : forall (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros s K0. 
  forwards (s'&v&R1&K1): (rm M1) K0.
  exists s' v. split. { applys eval_if R1. } { applys K1. }
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

Parameter eval_app_fun : forall s1 s2 v1 v2 x t1 v,
  v1 = val_fun x t1 ->
  eval s1 (subst x v2 t1) s2 v ->
  eval s1 (trm_app v1 v2) s2 v.

(* EX2! (hoare_app_fun) *)

Lemma hoare_app_fun : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  hoare (subst x v2 t1) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof using.
(* SOLUTION *)
  introv E M. intros s K0. forwards (s'&v&R1&K1): (rm M) K0.
  exists s' v. splits. { applys eval_app_fun E R1. } { applys K1. }
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
  (forall s s' v, eval s t1 s' v -> eval s t2 s' v) ->
  hoare t1 H Q ->
  hoare t2 H Q.
Proof using.
  introv E M1 K0. forwards (s'&v&R1&K1): M1 K0.
  exists s' v. split. { applys E R1. } { applys K1. }
Qed.

Lemma triple_same_semantics : forall t1 t2 H Q,
  (forall s s' v, eval s t1 s' v -> eval s t2 s' v) ->
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
  introv R. applys eval_app_fun E R.
Qed.


(* ******************************************************* *)
(** ** Proofs for the arithmetic primitive operations *)

(* ------------------------------------------------------- *)
(** *** Addition *)

(** Recall the evaluation rule for addition. *)

Parameter eval_add : forall s n1 n2,
  eval s (val_add (val_int n1) (val_int n2)) s (val_int (n1 + n2)).

(** In the proof, we will need to use the following result,
    established in the first chapter. *)

Parameter hstar_hpure_iff : forall P H h, 
  (\[P] \* H) h <-> (P /\ H h).

(** As usual, we first establish a Hoare triple. *)

Lemma hoare_add : forall H n1 n2,
  hoare (val_add n1 n2)
    H
    (fun r => \[r = val_int (n1 + n2)] \* H).
Proof using.
  intros. intros s K0. exists s (val_int (n1 + n2)). split.
  { applys eval_add. }
  { rewrite hstar_hpure_iff. split.
    { auto. }
    { applys K0. } }
Qed.

(** Deriving [triple_add] is straightforward. *)

Lemma triple_add : forall n1 n2,
  triple (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).
Proof using.
  intros. intros H'. applys hoare_conseq. 
  { applys hoare_add. } { hsimpl. } { hsimpl. auto. }
Qed.


(* ------------------------------------------------------- *)
(** *** Division *)

(** Recall the evaluation rule for division. *)

Parameter eval_div : forall s n1 n2,
  n2 <> 0 ->
  eval s (val_div (val_int n1) (val_int n2)) s (val_int (Z.quot n1 n2)).

(* EX1! (triple_div) *)
(** Following the same proof scheme as for [triple_add], establish
    the reasoning rule for [triple_div]. Make sure to first state
    and prove [hoare_div]. *)

(* SOLUTION *)
Lemma hoare_div : forall H n1 n2,
  n2 <> 0 ->
  hoare (val_div n1 n2)
    H
    (fun r => \[r = val_int (Z.quot n1 n2)] \* H).
Proof using.
  introv N. intros s K0. exists s (val_int (Z.quot n1 n2)). split.
  { applys eval_div N. }
  { rewrite hstar_hpure_iff. split.
    { auto. }
    { applys K0. } }
Qed.

Lemma triple_div : forall n1 n2,
  n2 <> 0 ->
  triple (val_div n1 n2)
    \[]
    (fun r => \[r = val_int (Z.quot n1 n2)]).
Proof using.
  introv N. intros H'. applys hoare_conseq. 
  { applys hoare_div N. } { hsimpl. } { hsimpl. auto. }
Qed.
(* /SOLUTION *)


(* ******************************************************* *)
(** ** Proofs for primitive operations operating on the state *)

(** The proofs for establishing the Separation Logic reasoning rules
    for [ref], [get] and [set] follow a similar proof pattern,
    that is, they go through the proofs of rules for Hoare triples.

    Unlike before, however, the Hoare triples are not directly
    established with respect to the big-step evaluation rules.
    Instead, we start by proving corollaries to the big-step rules
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

Parameter eval_get : forall s l,
  fmap_indom s l ->
  eval s (val_get (val_loc l)) s (fmap_read s l).

(** We reformulate this rule by isolating from the current state [s]
    the singleon heap made of the cell at location [l], and let [s2]
    denote the rest of the heap. When the singleton heap is described
    as [fmap_single l v], then [v] is the result value returned by
    [get l]. *)

Lemma eval_get_sep : forall s s2 l v, 
  s = (fmap_single l v) \u s2 ->
  eval s (val_get (val_loc l)) s v.

(** The proof of this lemma is of little interest. We show it only to
   demonstrate that it relies only a basic facts related to finite maps. *)

Proof using.
  introv ->. forwards Dv: fmap_indom_single l v.
  applys_eq eval_get 1.
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

Parameter hstar_hpure_iff' : forall P H h, 
  (\[P] \* H) h <-> (P /\ H h).

(** First, we establish the desired result on the [hoare] judgment. *)

Lemma hoare_get : forall H v l,
  hoare (val_get l)
    ((l ~~~> v) \* H)
    (fun r => \[r = v] \* (l ~~~> v) \* H).
Proof using.
  (* 1. We unfold the definition of [hoare]. *)
  intros. intros s K0. 
  (* 2. We provide the witnesses for the reduction,
        as dictated by [red_get_sep]. *)
  exists s v. split.
  { (* 3. To justify the reduction using [red_get_sep], we need to
          argue that the state [s] decomposes as a singleton heap
          [fmap_single l v] and the rest of the state [s2]. This is
          obtained by eliminating the star in hypothesis [K0]. *)
    destruct K0 as (s1&s2&P1&P2&D&U).
    (*    and subsequently inverting [(l ~~~> v) h1]. *)
    lets E1: hsingle_inv P1. subst s1.
    (* 4. At this point, the goal matches exactly [red_get_sep]. *)
    applys eval_get_sep U. }
  { (* 5. To establish the postcondition, we reuse justify the
          pure fact \[v = v], and check that the state, which
          has not changed, satisfy the same heap predicate as
          in the precondition. *)
    rewrite hstar_hpure. auto. }
Qed.

(** Deriving the Separation Logic triple follows the usual pattern. *)

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
(** *** Write in a reference *)

(** The big-step evaluation rule for [set l v] updates the initial
    state [s] by re-binding the location [l] to the value [v].
    The location [l] must already belong to the domain of [s]. *)

Parameter eval_set : forall m l v,
   fmap_indom m l ->
   eval m (val_set (val_loc l) v) (fmap_update m l v) val_unit.

(** As for [get], we first reformulate this lemma, to replace 
   references to [fmap_indom] and [fmap_update] with references
   to [fmap_union], [fmap_single], and [fmap_disjoint], to
   prepare for the introduction of separating conjuntions. *)

Lemma eval_set_sep : forall s1 s2 h2 l v1 v2,
  s1 = fmap_union (fmap_single l v1) h2 ->
  s2 = fmap_union (fmap_single l v2) h2 ->
  fmap_disjoint (fmap_single l v1) h2 ->
  eval s1 (val_set (val_loc l) v2) s2 val_unit.
Proof using.
  (** It is not needed to follow through this proof. *)
  introv -> -> D. forwards Dv: fmap_indom_single l v1.
  applys_eq eval_set 2.
  { applys~ fmap_indom_union_l. }
  { rewrite~ fmap_update_union_l. fequals.
    rewrite~ fmap_update_single. }
Qed.

(** The proof of the Hoare rule for [set] makes use of the following
    fact (from [Fmap.v]) about [fmap_disjoint]: when one of its argument is
    a singleton map, the value stored in that singleton map is irrelevant. *)

Parameter fmap_disjoint_single_set : forall l v1 v2 h2,
  fmap_disjoint (fmap_single l v1) h2 ->
  fmap_disjoint (fmap_single l v2) h2.

(** We willmake use of three lemmas, all introduced in the first chapter:

    - the lemma [hstar_hpure_iff], already used earlier in this chapter 
      to reformulate [(\[P] \* H) h] as [P /\ H h],
    - the lemma [hsingle_intro], to prove [(l ~~~> v) (fmap_single l v)], 
    - and the lemma [hstar_intro], to prove [(H1 \* H2) (h1 \u h2)]. *)

(** Let's now dive in the proof of the Hoare triple for [set]. *)

Lemma hoare_set : forall H w l v,
  hoare (val_set (val_loc l) w)
    ((l ~~~> v) \* H)
    (fun r => \[r = val_unit] \* (l ~~~> w) \* H).
Proof using. 
  (* 1. We unfold the definition of [hoare]. *)
  intros. intros s1 K0.
  (* 2. We decompose the star from the precondition. *)
  destruct K0 as (h1&h2&P1&P2&D&U).
  (* 3. We also decompose the singleton heap predicate from it. *)
  lets E1: hsingle_inv P1.
  (* 4. We provide the witnesses as guided by [red_set_sep]. *)
  exists ((fmap_single l w) \u h2) val_unit. split.
  { (* 5. The evaluation subgoal matches the statement of [red_set_sep]. *)
    subst h1. applys eval_set_sep U D. auto. }
  { (* 6. To establish the postcondition, we first isolate the pure fact. *)
    rewrite hstar_hpure. split.
    { auto. }
    { (* 7. Then establish the star. *)
      applys hstar_intro.
      { (* 8. We establish the heap predicate [l ~~~> w] *) 
        applys hsingle_intro. }
      { applys P2. }
      { (* 9. Finally, we justify disjointness using the lemma 
              [fmap_disjoint_single_set] introduced earlier. *)
        subst h1. applys fmap_disjoint_single_set D. } } }
Qed.

(** We then derive the Separation Logic triple as usual. *)

Lemma triple_set : forall w l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => \[r = val_unit] \* l ~~~> w).
Proof using.
  intros. intros H'. applys hoare_conseq.
  { applys hoare_set. } 
  { hsimpl. }
  { hsimpl. auto. }
Qed.


(* ------------------------------------------------------- *)
(** *** Allocation of a reference *)

(** Last but not least, the reasoning rule for operation [ref]
    involves a proof yet slightly more trickier than that
    for [get] and [set]. *)

(** The big-step evaluation rule for [ref v] extends the initial
    state [s] with an extra binding from [l] to [v], for some
    fresh location [l]. *)

Parameter eval_ref : forall s v l,
  ~ fmap_indom s l ->
  eval s (val_ref v) (fmap_update s l v) (val_loc l).

(** Let us reformulate [red_ref] to replace references to [fmap_indom]
    and [fmap_update] with references to [fmap_single] and [fmap_disjoint].
    Concretely, [ref v] extends the state from [s1] to [s1 \u s2],
    where [s2] denotes the singleton heap [fmap_single l v], and with
    the requirement that [fmap_disjoint s2 s1], to capture freshness. *)

Lemma eval_ref_sep : forall s1 s2 v l,
  s2 = fmap_single l v ->
  fmap_disjoint s2 s1 ->
  eval s1 (val_ref v) (fmap_union s2 s1) (val_loc l).
Proof using.
  (** It is not needed to follow through this proof. *)
  introv -> D. forwards Dv: fmap_indom_single l v.
  rewrite <- fmap_update_eq_union_single. applys~ eval_ref.
  { intros N. applys~ fmap_disjoint_inv_not_indom_both D N. }
Qed.

(** In order to apply the rules [red_ref] or [red_ref_sep], we need
    to be able to synthetize fresh locations. The following lemma
    (from [Fmap.v]) captures the existence, for any state [s], of 
    a location [l] not already bound in [s]. *)

Parameter fmap_exists_not_indom : forall s,
  exists l, ~ fmap_indom s l.

(** For invokation in relation to rule [red_ref_sep], we actually
    will exploit the following corollary, which asserts, for any [h],
    the existence of a location [l] such that the singleton heap
    [fmap_single l v] is disjoint from [h]. *)

Lemma fmap_single_fresh : forall h v,
  exists l, fmap_disjoint (fmap_single l v) h.
Proof using.
  (** It is not needed to follow through this proof. *)
  intros. forwards (l&F): fmap_exists_not_indom h.
  exists l. applys* fmap_disjoint_single_of_not_indom.
Qed.

(** The proof of the Hoare triple for [ref] is as follows. *)

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
    applys eval_ref_sep D. auto. }
  { (* 5. We establish the postcondition 
       [(\exists l, \[r = val_loc l] \* l ~~~> v) \* H]
       by providing [p] and the relevant pieces of heap. *)
    applys hstar_intro.
    { exists l. rewrite hstar_hpure.
      split. { auto. } { applys hsingle_intro. } }
    { applys K0. }
    { applys D. } }
Qed.

(** We then derive the Separation Logic triple as usual. *)

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


(* ******************************************************* *)
(** *** Proofs revisited using the [triple_of_hoare] lemma *)

(** The proof that, e.g., [triple_add] is a consequence of 
   [hoare_add] follows the same pattern as many other similar
   proofs, each time invoking the lemma [hoare_conseq].
   Thus, we could attempt at factorizing this proof pattern.
   The following lemma corresponds to such an attempt. *)

(* EX2! (triple_of_hoare) *)
(** Prove the lemma [triple_of_hoare] stated below. *)

Lemma triple_of_hoare : forall t H Q,
  (forall H', exists Q', hoare t (H \* H') Q' 
                     /\  Q' ===> Q \*+ H' \*+ \Top) ->
  triple t H Q.
Proof using.
(* SOLUTION *)
  introv M. intros H'. lets (Q'&N&WQ): M H'. applys hoare_conseq N.
  { applys himpl_refl. } { applys WQ. }
(* /SOLUTION *)
Qed.

(* EX2! (triple_add') *)
(** Prove that [triple_add] is a consequence of [hoare_add] by
    exploiting [triple_of_hoare]. *)

Lemma triple_add' : forall n1 n2,
  triple (val_add n1 n2)
    \[]
    (fun r => \[r = val_int (n1 + n2)]).
Proof using.
(* SOLUTION *)
  intros. applys triple_of_hoare. intros H'. esplit. split.
  applys hoare_add. hsimpl. auto.
(* /SOLUTION *)
Qed.


End Proofs.


(* ******************************************************* *)
(** *** Rules for naming heaps *)

(* EX2! (hoare_named_heap) *)
(** Prove that to establish a [hoare t H Q], it is sufficient
    to establish [hoare t (=h) Q] for any heap [h] satisfying [H].
    (This reformulation can be useful when one needs to gets his
    hand on a concrete heap [h].) *)

Lemma hoare_named_heap : forall t H Q,
  (forall h, H h -> hoare t (= h) Q) ->
  hoare t H Q.
Proof using. 
(* SOLUTION *)
  introv M. intros h K. applys M K. auto.
(* /SOLUTION *)
Qed.

(* EX3! (triple_named_heap) *)
(** Prove the counterpart of [hoare_named_heap] for Separation
    Logic triples.

    Hint: unfold the definition of [triple], exploit [hstar_inv]
    and [hstar_intro] to reason about the separating conjunction
    that appears, and use [hoare_named_heap] and [hoare_conseq]
    to structure the proof. It is not needed to unfold the 
    definition of [hoare]. *)

Lemma triple_named_heap : forall t H Q,
  (forall h, H h -> triple t (= h) Q) ->
  triple t H Q.
Proof using.
(* SOLUTION *)
  introv M. unfolds triple. intros H'.
  applys hoare_named_heap. intros h K.
  lets (h1&h2&K1&K2&D&U): hstar_inv K. subst h.
  lets N: M h1 (=h2). applys K1.
  applys hoare_conseq N.
  { intros ? ->. applys~ hstar_intro. }
  { intros x. applys himpl_frame_l. applys himpl_frame_r.
    intros ? ->. applys K2. }
(* /SOLUTION *)
Qed.




