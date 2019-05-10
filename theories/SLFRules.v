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

(** The reasoning rule for a sequence [t1;t2] resembles that of 
    Hoare logic. The rule is:
[[
      {H} t1 {Q1}     {Q1 val_unit} t2 {Q}
      -----------------------------------
              {H} (t1;t2) {Q}
]]
    The application of [Q1] to [val_unit] is necessary because
    [Q1] is the postcondition of [t1] so it has type [val->hprop], 
    whereas the precondition of [t2] must have type [hprop].
    By applying [Q1] to the expected result of [t1], which is
    [val_unit] when [t1] has type [unit], we obtain the
    expression [Q1 val_unit] which indeed has type [hprop]. *)

Parameter triple_seq : forall t1 t2 H Q Q1,
  triple t1 H Q1 ->
  triple t2 (Q1 val_unit) Q ->
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

Parameter triple_if_bool_case : forall b t1 t2 H Q,
  (b = true -> triple t1 H Q) ->
  (b = false -> triple t2 H Q) ->
  triple (trm_if (val_bool b) t1 t2) H Q.

(** The rule for a value [v] can be written as a triple with an
    empty precondition and a postcondition asserting that the
    result value [x] is equal to [v], in the empty heap.
[[
     ----------------------------
      {\[]} v {fun v' => \[v' = v]}
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
      {\[]} (trm_fun x t1) {fun v' => \[v' = val_fun x t1]}
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

Lemma triple_conseq_frame : forall H2 H1 Q1 t H Q,
  triple t H1 Q1 ->
  H ==> H1 \* H2 ->
  Q1 \*+ H2 ===> Q ->
  triple t H Q.
Proof using.
  introv M WH WQ. applys triple_conseq WH WQ.
  applys triple_frame M.
Qed.



Module ExampleProof.

Import NotationForVariables NotationForTerms CoercionsFromStrings.

(** We have at hand all the necessary rules for carrying out
    actual verification proofs in Separation Logic. 
    For example, consider the increment function.

    The definition in OCaml syntax is: [fun p => p := (!p + 1)].
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


Implicit Types t : trm.

Lemma bind_var_eq : forall x t1 t2,
  (If bind_var x = bind_var x then t1 else t2) = t1.
Proof using. intros. case_if*. Qed.

Lemma bind_var_neq : forall x y t1 t2,
  var_eq x y = false ->
  (If bind_var x = bind_var y then t1 else t2) = t2.
Proof using.
  introv M. rewrite var_eq_spec in M.
  rew_bool_eq in M. case_if*. 
Qed.

Lemma If_eq_bind_var : forall x y t1 t2,
    (If bind_var x = bind_var y then t1 else t2) 
  = (if var_eq x y then t1 else t2).
Proof using.
  intros. rewrite var_eq_spec. do 2 case_if; auto.
Qed.

Lemma If_eq_var : forall x y t1 t2,
    (If x = y then t1 else t2) 
  = (if var_eq x y then t1 else t2).
Proof using.
  intros. rewrite var_eq_spec. do 2 case_if; auto.
Qed.

Ltac simpl_subst :=
  simpl; unfold string_to_var;
   repeat rewrite If_eq_bind_var;
   repeat rewrite If_eq_var; simpl.





Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun v => \[v = val_unit] \* (p ~~~> (n+1))).
Proof using.
  intros. applys triple_app_fun. { reflexivity. }
  simpl_subst.
  applys triple_let.
  { apply triple_get. }
  intros n'. simpl_subst.
  apply triple_hpure. intros ->.
  applys triple_let. 
  { applys triple_conseq_frame. 
    { applys triple_add. }
    { hsimpl. }
    { hsimpl. } }
  intros m'. simpl_subst.
  apply triple_hpure. intros ->.
  applys triple_conseq_frame.
  { applys triple_set. }
  { hsimpl. }
  hsimpl. auto.
Qed.

End ExampleProof.


(* ####################################################### *)
(** * The chapter in a rush *)

(* ******************************************************* *)
(** ** The combined let-frame rule rule *)

(** The "let-frame" rule combines the rule for let-bindings
    with the frame rule. *)

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
(** ** Reasoning rules for recursive functions *)

(** This reasoning rules for functions immediately generalizes 
    to recursive functions. *)

Parameter triple_fix : forall f x t1 H Q,
  H ==> Q (val_fix f x t1) ->
  triple (trm_fix f x t1) H Q.

Lemma triple_app_fix : forall (f:bind) x F V t1 H Q,
  F = (val_fix f x t1) ->
  triple (subst2 f F x V t1) H Q ->
  triple (trm_app F V) H Q.

(** In fact, our language is set up in such a way that a non-recursive
    function is just a special case of a (potentially-recursive) function.
    The term [trm_fix z x t1] denotes a potentially-recursive function, 
    where [z] is a binder. This binder may be either a variable [f],
    in the case of a recursive function, or the special anonymous binder
    written [bind_anon] to denote a non-recursive function. *)
    
Check trm_fix : bind -> var -> trm -> trm.

Definition trm_fun' x t1 := trm_fix bind_anon x t1.


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
(** ** Proofs for the rules for terms *)



Lemma hoare_val : forall v H Q,
  H ==> Q v ->
  hoare (trm_val v) H Q.
Proof using.
  introv M. intros h Hh. exists h v. splits.
  { applys red_val. }
  { hhsimpl~. }
Qed.

Lemma hoare_fixs : forall (f:bind) xs t1 H Q,
  xs <> nil ->
  H ==> Q (val_fixs f xs t1) ->
  hoare (trm_fixs f xs t1) H Q.
Proof using.
  introv N M. intros h Hh. exists___. splits.
  { applys~ red_fixs. }
  { hhsimpl~. }
Qed.
Lemma hoare_let : forall z t1 t2 H Q Q1,
  hoare t1 H Q1 ->
  (forall v, hoare (subst1 z v t2) (Q1 v) Q) ->
  hoare (trm_let z t1 t2) H Q.
Proof using.
  introv M1 M2 Hh.
  forwards* (h1'&v1&R1&K1): (rm M1).
  forwards* (h2'&v2&R2&K2): (rm M2).
  exists h2' v2. splits~. { applys~ red_let_trm R2. }
Qed.Lemma hoare_if_bool : forall (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros h Hh. forwards* (h1'&v1&R1&K1): (rm M1).
  exists h1' v1. splits~. { applys* red_if. }
Qed.

Lemma hoare_if_trm : forall Q1 t0 t1 t2 H Q, (* TODO needed? *)
  hoare t0 H Q1 ->
  (forall v, hoare (trm_if v t1 t2) (Q1 v) Q) ->
  hoare (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. applys* hoare_evalctx (fun t0 => trm_if t0 t1 t2).
  { constructor. }
Qed.
Lemma hoare_apps_funs : forall xs F (Vs:vals) t1 H Q,
  F = (val_funs xs t1) ->
  var_funs (length Vs) xs ->
  hoare (substn xs Vs t1) H Q ->
  hoare (trm_apps F Vs) H Q.
Proof using.
  introv E N M. intros h Hh. forwards* (h'&v&R&K): (rm M).
  exists h' v. splits~. { subst. applys* red_apps_funs. }
Qed.

Lemma triple_fun : forall x t1 H Q,
  H ==> Q (val_fun x t1) ->
  triple (trm_fun x t1) H Q.
Proof using.
  introv M. intros HF h N. exists___. splits.
  { applys red_fun. }
  { hhsimpl. hchanges M. }
Qed.


Lemma triple_val : forall v H Q,
  H ==> Q v ->
  triple (trm_val v) H Q.
Proof using.
  introv M. intros HF. applys hoare_val. { hchanges M. }
Qed.

Lemma triple_fixs : forall f xs t1 H Q,
  xs <> nil ->
  H ==> Q (val_fixs f xs t1) ->
  triple (trm_fixs f xs t1) H Q.
Proof using.
  introv N M. intros HF. applys~ hoare_fixs. { hchanges M. }
Qed.

Lemma triple_constr : forall id vs H Q,
  H ==> Q (val_constr id vs) ->
  triple (trm_constr id vs) H Q.
Proof using.
  introv M. intros HF. applys hoare_constr. { hchanges M. }
Qed.

Lemma triple_constr_trm : forall id ts t1 vs H Q Q1,
  triple t1 H Q1 -> 
  (forall (X:val), triple (trm_constr id ((trms_vals vs)++(trm_val X)::ts)) (Q1 X) Q) ->
  triple (trm_constr id ((trms_vals vs)++t1::ts)) H Q.
Proof using.
  introv M1 M2. intros HF. applys~ hoare_constr_trm.
  { intros v. applys* hoare_of_triple. }
Qed.

Lemma triple_let : forall z t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall (X:val), triple (subst1 z X t2) (Q1 X) Q) ->
  triple (trm_let z t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF. applys hoare_let.
  { applys M1. }
  { intros v. applys* hoare_of_triple. }
Qed.

Lemma triple_seq : forall t1 t2 H Q Q1,
  triple t1 H Q1 ->
  (forall (X:val), triple t2 (Q1 X) Q) ->
  triple (trm_seq t1 t2) H Q.
Proof using.
  introv M1 M2. applys* triple_let. (* BIND intros. rewrite* subst1_anon. *)
Qed.

Lemma triple_if_bool : forall (b:bool) t1 t2 H Q,
  triple (if b then t1 else t2) H Q ->
  triple (trm_if b t1 t2) H Q.
Proof using.
  introv M1. intros HF. applys hoare_if_bool. applys M1.
Qed.

Lemma triple_if_bool_case : forall (b:bool) t1 t2 H Q,
  (b = true -> triple t1 H Q) ->
  (b = false -> triple t2 H Q) ->
  triple (trm_if b t1 t2) H Q.
Proof using.
  introv M1 M2. applys triple_if_bool. case_if*.
Qed.

Lemma triple_if_trm : forall Q1 t0 t1 t2 H Q,
  triple t0 H Q1 ->
  (forall v, triple (trm_if v t1 t2) (Q1 v) Q) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2. intros HF. applys* hoare_if_trm.
  { intros v. applys* hoare_of_triple. }
Qed.

Lemma triple_if : forall Q1 t0 t1 t2 H Q, (* not very useful *)
  triple t0 H Q1 ->
  (forall (b:bool), triple (if b then t1 else t2) (Q1 b) Q) ->
  (forall v, ~ is_val_bool v -> (Q1 v) ==> \[False]) ->
  triple (trm_if t0 t1 t2) H Q.
Proof using.
  introv M1 M2 M3. applys* triple_if_trm.
  { intros v. tests C: (is_val_bool v).
    { destruct C as (b&E). subst. applys* triple_if_bool. }
    { xchange* M3. xpull ;=>. false. } }
Qed.

Lemma triple_apps_funs : forall xs F (Vs:vals) t1 H Q,
  F = (val_funs xs t1) ->
  var_funs (length Vs) xs ->
  triple (substn xs Vs t1) H Q ->
  triple (trm_apps F Vs) H Q.
Proof using.
  introv E N M. intros H' h Hf. forwards (h'&v&R&K): (rm M) Hf.
  exists h' v. splits~. { subst. applys* red_apps_funs. }
Qed.

Lemma triple_apps_fixs : forall xs (f:var) F (Vs:vals) t1 H Q,
  F = (val_fixs f xs t1) ->
  var_fixs f (length Vs) xs ->
  triple (substn (f::xs) (F::Vs) t1) H Q ->
  triple (trm_apps F Vs) H Q.
Proof using.
  introv E N M. intros H' h Hf. forwards (h'&v&R&K): (rm M) Hf.
  exists h' v. splits~. { subst. applys* red_apps_fixs. }
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




