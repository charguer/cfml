(**

Separation Logic Foundations

Chapter: "Rules".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import SepBase.

(** Implicit Types *)

Implicit Types x f : var.
Implicit Types b : bool.
Implicit Types n : int.
Implicit Types v w r : val.
Implicit Types t : trm.
Implicit Types H : hprop.
Implicit Types Q : val->hprop.

(** TODO work-in-progress: 
    [subst_exec] is an executable version of [subst] on terms,
    but not yet fully executable... *)

Fixpoint subst_exec (y:var) (w:val) (t:trm) : trm :=
  let aux t := 
    subst_exec y w t in
  let aux_no_capture z t := 
    match z with
    | bind_anon => aux t
    | bind_var x => if var_eq x y then t else aux t 
    end in
  let aux_no_captures xs t := 
    If LibList.mem y xs then t else aux t in
  match t with
  | trm_val v => trm_val v
  | trm_var x => if var_eq x y then trm_val w else t
  | trm_fixs f xs t1 => 
      trm_fixs f xs (
        match xs with
        | x::nil => if var_eq x y then t1 else aux t1
        | _ => If f = y then t1 else aux_no_captures xs t1
        end)
  | trm_constr id ts => trm_constr id (List.map aux ts)
  | trm_if t0 t1 t2 => trm_if (aux t0) (aux t1) (aux t2)
  | trm_let z t1 t2 => trm_let z (aux t1) (aux_no_capture z t2)
  | trm_apps t0 ts => trm_apps (aux t0) (List.map aux ts)
  | trm_while t1 t2 => trm_while (aux t1) (aux t2)
  | trm_for x t1 t2 t3 => trm_for x (aux t1) (aux t2) (aux_no_capture x t3)
  | trm_match t0 pts => trm_match (aux t0) (List.map (fun '(pi,ti) =>
       (pi, aux_no_captures (patvars pi) ti)) pts)
  | trm_fail => trm_fail
  end.

Definition subst := subst_exec.


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

(* ------------------------------------------------------- *)
(** *** Proof of [triple_val] *)

Parameter red_val : forall s v,
  red s v s v.

Lemma hoare_val : forall v H Q,
  H ==> Q v ->
  hoare (trm_val v) H Q.
Proof using.
  introv M. intros h Hh. exists h v. splits.
  { applys red_val. }
  { applys M. auto. (* hhsimpl~. *) }
Qed.

Notation "'\Top''" := hgc. (* TODO: explain *)

Lemma triple_val'' : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using.
  introv M. intros H'. applys hoare_val.
  hchange M. hsimpl. (* hchanges M *)
Qed.

(** The proof of [triple_fun] is essentially identical to that
    of [triple_val], so we do not include it. *)


(* ------------------------------------------------------- *)
(** *** Proof of [triple_seq] *)

Parameter red_seq : forall s1 s2 s3 t1 t2 r1 r,
  red s1 t1 s2 r1 ->
  red s2 t2 s3 r ->
  red s1 (trm_seq t1 t2) s3 r.

Lemma hoare_seq : forall t1 t2 H Q H1,
  hoare t1 H (fun r => H1) ->
  hoare t2 H1 Q ->
  hoare (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2 K0.
  forwards (h1'&v1&R1&K1): (rm M1) K0.
  forwards (h2'&v2&R2&K2): (rm M2) K1.
  exists h2' v2. split. { applys red_seq R1 R2. } { apply K2. }
Qed.

Lemma triple_seq' : forall t1 t2 H Q H1,
  triple t1 H (fun r => H1) ->
  triple t2 H1 Q ->
  triple (trm_seq t1 t2) H Q.
Proof using.
  unfold triple. introv M1 M2. intros H'. applys hoare_seq.
  { applys M1. }
  { applys hoare_conseq. { applys M2. } { hsimpl. } { hsimpl. } }
Qed.


(* ------------------------------------------------------- *)
(** *** Proof of [triple_let] *)

Parameter red_let : forall s1 s2 s3 x t1 t2 v1 r,
  red s1 t1 s2 v1 ->
  red s2 (subst x v1 t2) s3 r ->
  red s1 (trm_let x t1 t2) s3 r.

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

Lemma triple_let'' : forall x t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall v, triple (subst x v t2) (Q1 v) Q) ->
  triple (trm_let x t1 t2) H Q.
Proof using.
  unfold triple. introv M1 M2. intros H'. applys hoare_let.
  { applys M1. }
  { intros v. applys hoare_conseq.
    { applys M2. } { hsimpl. } { hsimpl. } }
Qed.


(* ------------------------------------------------------- *)
(** *** Proof of [triple_if] *)

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

(** Variant *)

Lemma red_if_bool_case : forall m1 m2 b r t1 t2,
  red m1 (if b then t1 else t2) m2 r ->
  red m1 (trm_if b t1 t2) m2 r.
Proof using.
  intros. case_if; applys red_if_bool; auto_false.
Qed.

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

Parameter red_app_fun : forall s1 s2 v1 v2 x t1 r,
  v1 = val_fun x t1 ->
  red s1 (subst x v2 t1) s2 r ->
  red s1 (trm_app v1 v2) s2 r.

Lemma hoare_app_fun : forall v1 v2 x t1 H Q,
  v1 = val_fun x t1 ->
  hoare (subst x v2 t1) H Q ->
  hoare (trm_app v1 v2) H Q.
Proof using.
  introv E M. intros h K0. forwards (h'&v&R1&K1): (rm M) K0.
  exists h' v. splits. { applys red_app_fun E R1. } { applys K1. }
Qed.

Lemma triple_app_fun' : forall x v1 v2 t1 H Q,
  v1 = val_fun x t1 ->
  triple (subst x v2 t1) H Q ->
  triple (trm_app v1 v2) H Q.
Proof using.
  unfold triple. introv E M1. intros H'.
  applys hoare_app_fun E. applys M1.
Qed.


(* ******************************************************* *)
(** ** Proofs for the specification of primitive operations *)

Lemma hoare_ref : forall H v,
  hoare (val_ref v)
    H
    (fun r => (\exists l, \[r = val_loc l] \* l ~~~> v) \* H).
Lemma hoare_get : forall H v l,
  hoare (val_get (val_loc l))
    ((l ~~~> v) \* H)
    (fun x => \[x = v] \* (l ~~~> v) \* H).
Proof using.
  intros. intros h Hh. exists h v. splits~.
  { applys red_get. destruct Hh as (h1&h2&(N1a&N1b)&N2&N3&N4).
    subst h. applys~ fmap_union_single_l_read. }
  { hhsimpl~. }
Qed.

Lemma hoare_set : forall H w l v,
  hoare (val_set (val_loc l) w)
    ((l ~~~> v) \* H)
    (fun r => \[r = val_unit] \* (l ~~~> w) \* H).

Lemma triple_ref : forall v,
  triple (val_ref v)
    \[]
    (fun r => \exists l, \[r = val_loc l] \* l ~~~> v).
Proof using.
  intros. applys triple_of_hoare. intros HF. rew_heap.
  esplit; split. { applys hoare_ref. } { hsimpl*. }
Qed.

Lemma triple_get : forall v l,
  triple (val_get (val_loc l))
    (l ~~~> v)
    (fun x => \[x = v] \* (l ~~~> v)).
Proof using.
  intros. applys triple_of_hoare. intros HF.
  esplit; split. { applys hoare_get. } { hsimpl*. }
Qed.

Lemma triple_set : forall w l v,
  triple (val_set (val_loc l) w)
    (l ~~~> v)
    (fun r => \[r = val_unit] \* l ~~~> w).
Proof using.
  intros. applys triple_of_hoare. intros HF.
  esplit; split. { applys hoare_set. } { hsimpl*. }
Qed.




