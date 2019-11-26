(**

Separation Logic Foundations

Chapter: "Basic".

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
From Sep Require Import Example. (* TODO: depend on CFML ? *)
Generalizable Variables A B.

Implicit Types n m : int.
Implicit Types p q : loc.


(* ####################################################### *)
(** * The chapter in a rush *)

(** This chapter gives a quick overview of how to state specifications and 
    carry out basic proofs in Separation Logic using CFML tactics.

    In this chapter, we will present:
  
    - "Specification triples", of the form [TRIPLE _ PRE _ POST _],
      relating a term, a precondition, and a postcondition.
    - "Verification proof obligations", of the form [PRE _ CODE _ POST _],
      which is a variant of the [TRIPLE] notation that puts the current
      state as first argument.
    - "Entailement proof obligations", of the form [_ ==> _] or [_ ===> _],
      which require proving that a description of a state implies another one.

    The "heap predicates" used to describe the current memory state include:
    - [p ~~> n], which describes a memory cell at location [p] with contents [n],
    - [\[]], which describes an empty state,
    - [\[P]], which asserts that a proposition [P] is true (in an empty state),
    - [H1 \* H2], which describes a state made of two disjoint parts: [H1] and [H2],
    - [\exists x, H], which is used to quantify variables in postconditions.

    The proofs are carried out using CFML "x-tactics", including:
    - [xwp] to being a proof,
    - [xapp] to reason about an application,
    - [xval] to reason about a returned value,
    - [xsimpl] to simplify or prove entailments ([_ ==> _] or [_ ===> _]).

    In addition, the proof script exploit standard Coq tactics as well as
    tactics from the TLC library, including:
    - [unfold] to reveal a definition,
    - [introv H1 H2] as a variant of [intros] that skips variables
      and names only hypotheses,
    - [tactic ;=> x y] as a shorthand for [tactic; intros x y],
    - [math] to prove purely mathematical goals,
    - [gen] and [induction_wf] to set up (non-structural) inductions.
 *)


(* ******************************************************* *)
(** ** The increment function *)

(** As first example, consider the function [incr], which increments
    the contents of a mutable cell that stores an integer. 
    In OCaml syntax, this function is defined as:

[[
  let incr p =
    p := !p + 1
]]
  
    In the real CFML tools, programs can be provided as input in
    OCaml syntax. However, throughout this course, to avoid unnecessary 
    tooling, we will input programs using a custom set of Coq notation.

    It is no needed to learn how to write programs in that funny syntax.
    All that matters is to be able to recognize that the Coq definition
    somehow matches the intended OCaml source code. 

    Below is the code for [incr]. The quotes are used to disambiguate
    with Coq syntax; the [VFun] token reads like [fun].
    
*)

Definition incr : val :=
  VFun 'p :=
   'p ':= '! 'p '+ 1.

(** Let [p] be the address of a reference cell, that is, a "location". 
    
    The expression [p ~~> n] describes a memory state in which the
    contents of the location [p] is the value [n], in this case an 
    integer value.

    The behavior of [incr p] is to update the memory state by incrementing
    the contents of the cell at location [p], so that its new contents is [n+1].
    The new memory state is described by the expression [p ~~> (n+1)].

    The result value returned by [incr p] is simply the "unit" value,
    so there is not much to specify about the result value, appart from
    the fact that it has type unit.

    The specification of [incr p] can be expressed using a 
    "Separation Logic triple"  using the custom notation
    [TRIPLE _ PRE _ POST _], as follows. *)

Lemma Triple_incr : forall (p:loc) (n:int),
  TRIPLE (incr p)
    PRE (p ~~> n)
    POST (fun (r:unit) => (p ~~> (n+1))).

(** Let us describe the components:

    - The [forall (p:loc) (n:int)] quantifies the argument of the function
      ([p]), as well as the ghost argument ([n]) which is used to describe
      the input state.
    - The keyword [TRIPLE] introduces the expression [incr p], which is the
      function call being specified.
    - The keyword [PRE] introduces the "precondition", which describes the
      input state that the function expects, here [p ~~> n].
    - The keyword [POST] introduces the "postcondition", which describes 
      both the output value and the output state produced by the call.
      The pattern [fun (r:unit) => _] binds the name [r] to denote the result 
      value; here [r] has type unit, reflecting the type of [incr p].
      The expression [p ~~> (n+1)] describes the output state.

      Important remark: [p ~~> n+1] would parse as [(p ~~> n) + 1] and fail
      to typecheck, so please beware that parentheses are required. *)

(** Let us now prove that specification, by conducting a verification proof 
    using CFML tactics. *)

(** The CFML tooling will transform on-the-fly the code so that all 
    intermediate expressions are named (that is, in "A-normal form").
    In OCaml syntax, this would be:
    
[[
  let incr p =
    let m = 
      let n = !p in
      n + 1 in
    p := m
]]

  This transformation is performed by the tactic [xwp], which begins every
  CFML verification proof script.
*)

Proof using.
  xwp.     (* Begin the verification proof. The proof obligation is 
              displayed using the custom notation [PRE _ CODE _ POST _]. 
              The [CODE] part does not look very nice, but one should
              be able to somehow recognize the body of [incr]. Indeed,
              ignorining the details, and after alpha-renaming,
              it looks like:
[[
              Let m := 
                  Let n := App val_get p in
                  App val_add n 1 
                  in
               App val_set p m
]]

             The remaining of the proof performs some form of symbolic 
             execution. One should not attempt to read all the proof 
             obligation at each step, but instead look at the current
             state (the [PRE] part, which is [p ~~> n]), and the first
             line only of the [CODE] part.
 *)
  xapp.    (* Reason about the the operation [!p] that reads into [p];
              the read operation returns the value [n]. *)
  xapp.    (* Reason about the addition operation [n+1]. *)
  xapp.    (* Reason about the update operation [p := n+1],
              thereby updating the state to [p ~~> (n+1)]. *)
  xsimpl.  (* At this stage, the proof obligation takes the form [_ ==> _],
              which require checking that the final state matches what 
              is claimed in the postcondition. *)
Qed.

(** The command below associates the specification lemma [Triple_incr]
    with the function [incr] in a database, so that if we subsequently
    verify a program that features a call to [incr], the [xapp] tactic
    is able to automatically invoke the lemma [Triple_incr]. 

    (There is no need to understand the internal magic of how the
    database is implemented by hacking Coq's [Hint] mechanism.) *)

Hint Extern 1 (Register_Spec incr) => Provide Triple_incr.


(* ******************************************************* *)
(** *** A function with a return value *)

(** As second example, we describe a function that performs some simple
    computations, and features no mutation---working in an empty memory state.

    The function, whose code appears below, expects an integer argument [n],
    computes [a] as [n+1], computes [b] as [n-1], then returns [a+b].
    The function thus always returns [2*n].

[[
  let example_let n =
    let a = n + 1 in
    let b = n - 1 in
    a + b
]]
*)

Definition example_let : val :=
  VFun 'n :=
    Let 'a := 'n '+ 1 in
    Let 'b := 'n '- 1 in
    'a '+ 'b.

(** We specify this function using the the triple notation, in the form
    [TRIPLE (example_let n) PRE _ POST (fun (r:int) => _ )], where [r] 
    denotes the output value---this time, a value of type [int].

    To denote the fact that the input state is empty, we write [\[]]
    in the precondition (after the [PRE] keyword).

    To denote the fact that the output state is empty, we could use [\[]].
    Yet, if we write [fun (r:int) => \[]] as postcondition, we would have 
    said nothing about the output value [r] produced by a call [example_let].
    Instead, we would like to specify that the result [r] is equal to [2*n].
    To that end, we write [fun (r:int) => \[2*n]] as postcondition. *)

Lemma Triple_example_let : forall (n:int),
  TRIPLE (example_let n)
    PRE \[]
    POST (fun (r:int) => \[r = 2*n]).

(** The verification proof script is very similar to the previous one. 
    The x-tactics [xapp] perform symbolic execution of the code.
    Ultimately, we need to check that the expression computed,
    [(n + 1) + (n - 1)] is equal to the specified result, that is, [2*n].
    We exploit the tactics [xsimpl] and [math] to prove this result. *)

Proof using.
  xwp. xapp. xapp. xapp. xsimpl. math.
Qed.

(** In the proof above, we have eargerly substituted [a] with [n+1], 
    then substituted [b] with [n-1]. Such eager substitutions generally
    work well for small programs, yet in some programs can lead to
    exponential blow-up in the terms being manipulated. To avoid the
    blow-up, it may be necessary to preserve explicit equalities, 
    such as [a = n+1] and [b = n-1] in the context.

    In general, it is desirable to let the user control when substitutions
    should or should not be performed. The [xapp] tactic does perfom the
    substitution, whereas its variant [xapp_nosubst] instead introduces an
    explicit equality, as illustrated next. *)

Lemma Triple_example_let_with_nosubst : forall (n:int),
  TRIPLE (example_let n)
    PRE \[]
    POST (fun (r:int) => \[r = 2*n]).
Proof using.
  xwp. 
  xapp_nosubst. intros a Ha.  (* introduces [Ha: a = n + 1] *)
  xapp_nosubst. intros b Hb.  (* introduces [Hb: b = n - 1] *)
  xapp_nosubst. intros r Hr.  (* introduces [Hb: r = a + b] *)
  xsimpl. math. (* check that, under these hypotheses, [r = 2 * n]. *)
Qed.


(* ******************************************************* *)
(** ** Exercise: function [double] *)

(** Consider the function [double] that expects an integer [n]
    and returns its double, that is, the value [2 * n].

[[
  let double n =
    n + n
]]
*)

Definition double : val :=
  VFun 'n :=
    'n '+ 'n.

(* EX1! (Triple_double) *)
(** Complete the postcondition of [Triple_double] to express that
    it returns [2*n], then prove it. *)

Lemma Triple_double : forall (n:int),
  TRIPLE (double n)
    PRE \[]
    POST (fun (r:int) => (* SOLUTION *) \[r = 2 * n] (* /SOLUTION *)).
Proof using.
  (* SOLUTION *) xwp. xapp. xsimpl. math. (* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Exercise: function [inplace_double] *)

(** Consider the function [inplace_double] that expects a reference
    on an integer, reads twice in that reference, and updates the
    reference with the sum of the two values that have been read.

[[
  let inplace_double p =
    p := !p + !p
]]
*)

(* EX1! (Triple_inplace_double) *)
(** Complete the precondition and the postcondition of
    [Triple_inplace_double] to express that it returns [2*n],
    then prove the specification. *)

Definition inplace_double : val :=
  VFun 'p :=
    'p ':= ('!'p '+ '!'p).

Lemma Triple_inplace_double : forall (p:loc) (n:int),
  TRIPLE (inplace_double p)
    PRE ((* SOLUTION *) p ~~> n (* /SOLUTION *))
    POST (fun (_:unit) => (* SOLUTION *) p ~~> (2*n) (* /SOLUTION *)).
Proof using.
  (* SOLUTION *) xwp. xapp. xapp. xapp. xapp. xsimpl. math. (* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** *** Increment of two references *)

(** Consider the following function, which expects the addresses
    of two reference cells, and increments both of them.

[[
  let incr_two p q =
    incr p;
    incr q
]]
*)

Definition incr_two : val :=
  VFun 'p 'q :=
    incr 'p ';
    incr 'q.

(** The specificaiton of this function takes the form
    [TRIPLE (incr_two p q) PRE _ POST (fun (r:unit) => _ )], 
    where [r] denotes the result value of type unit. 

    The precondition describes two references cells:
    [p ~~> n] for the first one, and [q ~~> m]. To assert
    that the two cells are distinct from each other, we
    separate the two with the token [\*], which is called
    "separating conjunction" in Separation Logic, and is
    also known as the "star" operator. Thus, the precondition
    is [(p ~~> n) \* (q ~~> m)], or simply [p ~~> n \* q ~~> m].

    The postcondition describes the final state as
    is [p ~~> (n+1) \* q ~~> (m+1)], where the contents of both
    cells increased by one unit. 

    The specification triple for [incr_two] is thus: *)

Lemma Triple_incr_one_of_two : forall (p q:loc) (n m:int),
  TRIPLE (incr_two p q)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (r:unit) => p ~~> (n+1) \* q ~~> (m+1)).

(** The proof follow the usual pattern. *)

Proof using.
  xwp. xapp. xapp. xsimpl.
Qed.

(** Let us register the specification [Triple_incr_one_of_two] in 
    the database of specifications. *)

Hint Extern 1 (Register_Spec incr_two) => Provide Triple_incr_one_of_two.

(** The specification above correctly describes calls to the function
    [incr_two] when providing it with two distinct reference cells.
    But it says nothing about a call of the form [incr_two p p].
    Indeed, in Separation Logic, if we have a state described by [p ~~> n], 
    we cannot possibly match it with [p ~~> n \* p ~~> n], because the
    star operator requires its operand to correspond to disjoint pieces
    of heap. 

    What happens if we nevertheless try to exploit [Triple_incr_one_of_two]
    on a call of the form [incr_two p p]? Let's try, by considering a 
    function [aliased_call p] that execute precisely this call. *)

Definition aliased_call : val :=
  VFun 'p :=
    incr_two 'p 'p.

Lemma Triple_aliased_call : forall (p:loc) (n:int),
  TRIPLE (aliased_call p)
    PRE (p ~~> n)
    POST (fun (r:unit) => p ~~> (n+2)).

(** The proof follow the usual pattern. *)

Proof using.
  xwp. xapp.
Abort.

(** We get stuck with a proof obligation of the form:
    [\[] ==> (p ~~> ?m) \* _], which requires showing that
    from an empty state one can extract a reference [p ~~> ?m]
    for some integer [?m].
  
    What happened in that when matching the current state
    [p ~~> n] against [p ~~> ?n \* p ~~> ?m]
    (that is, the precondition of [Triple_incr_one_of_two]
    when [q = p]), the internal simplification tactic could cancel 
    out [p ~~> n] in both expressions, but then got stuck with
    matching the empty state against [q ~~> ?m]. *)

(** It is, however, possible to state and prove an alternative
    specification for the function [incr_two], specifically covering 
    the case where the two arguments are equal. In that case, the
    specification is totally different: the precondition mentions
    only one reference, [p ~~> n], and the postcondition asserts
    that its contents gets increased by two units. *)

Lemma Triple_incr_one_of_two' : forall (p:loc) (n:int),
  TRIPLE (incr_two p p)
    PRE (p ~~> n)
    POST (fun (r:unit) => p ~~> (n+2)).

(** The proof follow the usual pattern. *)

Proof using.
  xwp. xapp. xapp. xsimpl. math.
Qed.


(* ******************************************************* *)
(** *** A function that takes two references, and increment one *)

(** Consider the following function, which expects the addresses
    of two reference cells, and increments only the first one.

[[
  let incr_first p q =
    incr p
]]
*)

Definition incr_first : val :=
  VFun 'p 'q :=
    incr 'p.

(** We can specify this function by describing its input state
    as [p ~~> n \* q ~~> m], and describing its output state
    as [p ~~> (n+1) \* q ~~> m]. Formally: *)

Lemma Triple_incr_first : forall (p q:loc) (n m:int),
  TRIPLE (incr_first p q)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (r:unit) => p ~~> (n+1) \* q ~~> m).
Proof using.
  xwp. xapp. xsimpl.
Qed.

(** Observe, however, that the second reference plays absolutely
    no role in the execution of the function. In fact, we might
    equally well have described in the precondition and in the
    postcondition only the first reference, the one that the code
    manipulates. *)

Lemma Triple_incr_first' : forall (p q:loc) (n:int),
  TRIPLE (incr_first p q)
    PRE (p ~~> n)
    POST (fun (r:unit) => p ~~> (n+1)).
Proof using.
  xwp. xapp. xsimpl.
Qed.

(** Interestingly, the former definition is "derivable" from the latter.
    The tactic [xweaken] can be used to derive a specification from another. *)

Lemma Triple_incr_first_derived : forall (p q:loc) (n m:int),
  TRIPLE (incr_first p q)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (r:unit) => p ~~> (n+1) \* q ~~> m).
Proof using.
  intros.
  (* TODO: will be [xweaken Triple_incr_first'],
      implemented as [applys Triple_conseq_frame Triple_incr_first']. *)
  xtriple. xapp Triple_incr_first'. xsimpl.
Qed.

(** More generally, in Separation Logic, if a specification triple holds, 
    then this specification triple remains valid by adding a same predicate 
    in both the precondition and the postcondition. This is the "frame"
    principle, a key modularity feature that we'll discuss later. *)


(* ******************************************************* *)
(** ** Basic imperative function with two arguments (white belt) *)

(**
[[
  let decr_and_incr p q =
    decr p;
    incr q
]]
*)

Definition decr_and_incr :=
  VFun 'p 'q :=
    decr 'p ';
    incr 'q.

(* TODO: solution as part of a def... *)
Lemma Triple_decr_and_incr : forall p q n m,
  (* SOLUTION *)
  TRIPLE (decr_and_incr p q)
    PRE  (p ~~> n \* q ~~> m)
    POST (fun (_:unit) => p ~~> (n-1) \* q ~~> (m+1) ).
  (* /SOLUTION *)
Proof using.
  (* SOLUTION *) xwp. xapp. xapp. xsimpl. (* /SOLUTION *)
Qed.




(* ******************************************************* *)
(** *** Increment and allocate a copy *)

(**
[[
  let incr_and_ref p =
    incr p;
    ref !p
]]
*)

Definition incr_and_ref : val :=
  VFun 'p :=
    incr 'p ';
    'ref ('! 'p).

Lemma Triple_incr_and_ref : forall (p:loc) (n:int),
  TRIPLE (incr_and_ref p)
    PRE (p ~~> n)
    POST (fun (q:loc) => q ~~> (n+1) \* p ~~> (n+1)).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl.
Qed.

Hint Extern 1 (Register_Spec (incr_and_ref)) => Provide Triple_incr_and_ref.

Lemma Triple_incr_and_ref' : forall (p:loc) (n:int),
  TRIPLE (incr_and_ref p)
    PRE (p ~~> n)
    POST (fun (q:loc) =>
        \exists m, \[m > n] \* q ~~> m \* p ~~> (n+1)).
Proof using.
  xtriple. xapp. intros q. xsimpl. math.
Qed.

(* ******************************************************* *)
(** *** Deallocation in Separation Logic *)

(* TODO: tune to make it linear by default *)

(** By default, Separation Logic treats allocated resources 
    ---it is a "linear" logic as opposed to an "affine" logic.
    Remark: it is possible to tweak Separation Logic to make it
    affine and enable throwing away. *)

(*

[[
  let succ_using_incr n =
    let p = ref n in
    incr p;
    let x = !p in
    free p;
    x
]]
*)

Definition succ_using_incr :=
  VFun 'n :=
    Let 'p := 'ref 'n in
    incr 'p ';
    '! 'p.

Lemma Triple_succ_using_incr : forall n,
  TRIPLE (succ_using_incr ``n)
    PRE \[]
    POST (fun r => \[r = n+1]).
Proof using.
  xwp. xapp ;=> p. (* xapp. intros p. *)
  xapp. xapp. xsimpl*.
Qed.

(** Note: [decr] is similarly defined in the library. *)




(* ####################################################### *)
(** * Additional contents *)


(* ******************************************************* *)
(** *** Optimized scripts *)

Module OptimizedScripts.

(** The CFML tool features the tactic [xappn] that iterates calls to [xapp],
    and the tactic [xsimpl*] that combines [xsimpl] with call to automation. 
    Using these tactics, proofs scripts for simple functions can be greatly
    shortened. *)

Lemma Triple_incr : forall (p:loc) (n:int),
  TRIPLE (incr p)
    PRE (p ~~> n)
    POST (fun (r:unit) => (p ~~> (n+1))).
Proof using. xwp. xappn. xsimpl*. Qed.

Lemma Triple_example_let : forall n,
  TRIPLE (example_let n)
    PRE \[]
    POST (fun (r:int) => \[r = 2*n]).
Proof using. xwp. xappn. xsimpl*. Qed.

(** The use of such advanced tactics is beyond the scope of this course.
    In general, the overhead of executing the steps one by one is acceptable,
    and it helps better reflecting the structure of the program in the proof.
    Moreover, for complex programs, the advanced tactics are generally of 
    limited benefits, because at each step there are many side-conditions
    that need to be justified. *)

End OptimizedScripts.

(** Remark: [fun (r:unit)] could also be written [fun (_:unit)]. *)


(* ******************************************************* *)
(** *** A simple recursion *)

(**
[[
  let rec repeat_incr p m =
    if m > 0 then (
      incr p;
      repeat_incr p (m-1)
    )
]]
*)

Definition repeat_incr :=
  VFix 'f 'p 'm :=
    If_ 'm '> 0 Then
      incr 'p ';
      'f 'p ('m '- 1)
    (* Else '() *) End.

(** Let's try to prove a false specification *)

Lemma Triple_repeat_incr : forall p n m,
  TRIPLE (repeat_incr p m)
    PRE (p ~~> n)
    POST (fun (_:unit) => p ~~> (n + m)).
Proof using.
  intros. gen n. induction_wf IH: (downto 0) m. intros.
  xwp. xapp. xif ;=> C.
  { (* then branch *)
    xapp. xapp. xapp. { unfold downto. math. } xsimpl. math. }
  { (* else branch *)
    xval. xsimpl.
Abort.

(** Let's try again *)

Lemma Triple_repeat_incr : forall p n m,
  m >= 0 ->
  TRIPLE (repeat_incr p m)
    PRE (p ~~> n)
    POST (fun (_:unit) => p ~~> (n + m)).
Proof using.
  introv Hm. gen n Hm. induction_wf IH: (downto 0) m. intros.
  xwp. xapp. xif; intros C.
  { xapp. xapp. xapp. { hnf. math. } { math. }
    xsimpl. math. }
  { xval. xsimpl. math. }
Qed.

(** Let's try yet another time *)

Lemma Triple_repeat_incr' : forall p n m,
  TRIPLE (repeat_incr p m)
    PRE (p ~~> n)
    POST (fun (_:unit) => p ~~> (n + max 0 m)).
Proof using.
  intros. gen n. induction_wf IH: (downto 0) m; intros.
  xwp. xapp. xif; intros C.
  { xapp. xapp. xapp. { hnf. math. }
    xsimpl. repeat rewrite max_nonneg; math. }
  { xval. xsimpl. rewrite max_nonpos; math. }
Qed.

(** Note: [xif] calls [xapp] if necessary. *)

End Basics.


(* ******************************************************* *)

(** Hints:
    - [xwp] to begin the proof
    - [xapp] for applications, or [xappn] to repeat
    - [xif] for a case analysis
    - [xval] for a value
    - [xsimpl] to prove entailments
    - [auto], [math], [rew_list] to prove pure facts
      or just [*] after a tactic to invoke automation.
*)



(* ******************************************************* *)
(** *** A recursive function (yellow belt) *)

(** Here, we will assume [!p > 0].

[[
  let rec transfer p q =
    if !p > 0 then (
      decr p;
      incr q;
      transfer p q
    )
]]
*)

Definition transfer :=
  VFix 'f 'p 'q :=
    If_ '! 'p '> 0 Then
      decr 'p ';
      incr 'q ';
      'f 'p 'q
    End.

Lemma Triple_transfer : forall p q n m,
  n >= 0 ->
  TRIPLE (transfer p q)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (_:unit) => (* SOLUTION *) p ~~> 0 \* q ~~> (n + m) (* /SOLUTION *)).
Proof using.
  introv N. gen m N. induction_wf IH: (downto 0) n. intros.
  (* SOLUTION *)
  xwp. xapp. xapp. xif ;=> C.
  { xapp. xapp. xapp. { hnf. math. } { math. }
    xsimpl. math. }
  { xval. xsimpl. math. math. }
  (* /SOLUTION *)
Qed.

End ExoBasic.





(* ******************************************************* *)
(** *** Facto *)

(**
[[
  let rec facto n f =
    ...
    
]]
*)




(* ******************************************************* *)
(** *** Repeat *)

(**
[[
  let rec repeat n f =
    if n > 0 then begin
      f ();
      repeat (n-1) f
    end
]]
*)




(* ******************************************************* *)
(** *** Add_to *)

(**
[[
  let add_to p n =
    let f = (fun () -> incr p) in 
    repeat f n
]]
*)



(* ******************************************************* *)
(** *** Square *)

(**
[[
  let square n =
    let p = ref 0 in
    let f = (fun () -> add_to p n) in 
    repeat f n;
    !p
]]

*)





