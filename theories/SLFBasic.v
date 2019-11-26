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

*)

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


(* ******************************************************* *)
(** *** A function with a return value *)

(** 
[[
  let example_let n =
    let a = n + 1 in
    let b = n - 1 in
    a + b
]]
*)

Definition example_let :=
  VFun 'n :=
    Let 'a := 'n '+ 1 in
    Let 'b := 'n '- 1 in
    'a '+ 'b.

Lemma Triple_example_let : forall n,
  TRIPLE (example_let n)
    PRE \[]
    POST (fun r => \[r = 2*n]).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl. math.
Qed.

(** Note: [xapp] calls [xlet] automatically when needed. *)

(** Note: [xappn] factorizes the [xapp] calls. *)

(** Note: [xsimpl*] does [xsimpl] but automation that can call [xmath]. *)




(* ####################################################### *)
(** * Additional contents *)




(* ******************************************************* *)
(** *** Increment *)

(**
[[
  let incr p =
    p := !p + 1
]]
*)

Definition incr : val :=
  VFun 'p :=
   'p ':= '! 'p '+ 1.

Lemma Triple_incr : forall (p:loc) (n:int),
  TRIPLE (incr p)
    PRE (p ~~> n)
    POST (fun (r:unit) => (p ~~> (n+1))).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl.
Qed.

Hint Extern 1 (Register_Spec (incr)) => Provide Triple_incr.


(* ******************************************************* *)
(** *** Successor using increment *)

(**
[[
  let succ_using_incr n =
    let p = ref n in
    incr p;
    !p
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



(* ******************************************************* *)
(** *** Increment with two references *)

(**
[[
  let incr_one_of_two p q =
    incr p
]]
*)

Definition incr_one_of_two : val :=
  VFun 'p 'q :=
    incr 'p.

Lemma Triple_incr_one_of_two :
  forall (p q:loc) (n m:int),
  TRIPLE (incr_one_of_two p q)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (r:unit) => p ~~> (n+1) \* q ~~> m).
Proof using.
  xwp. xapp. xsimpl.
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
(** ** Basic pure function (warm up) *)

(**
[[
  let double n =
    n + n
]]
*)

Definition double :=
  VFun 'n :=
    'n '+ 'n.

Lemma Triple_double : forall n,
  TRIPLE (double n)
    PRE \[]
    POST (fun m => (* SOLUTION *) \[m = 2 * n] (* /SOLUTION *)).
Proof using.
  (* SOLUTION *) xwp. xapp. xsimpl. math. (* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Basic imperative function with one argument *)

(**
[[
  let inplace_double p =
    p := !p + !p
]]
*)

Definition inplace_double :=
  VFun 'p :=
    'p ':= ('!'p '+ '!'p).

Lemma Triple_inplace_double : forall p n,
  TRIPLE (inplace_double p)
    PRE ((* SOLUTION *) p ~~> n (* /SOLUTION *))
    POST (fun (_:unit) => (* SOLUTION *) p ~~> (2 * n) (* /SOLUTION *)).
Proof using.
  (* SOLUTION *) xwp. xapp. xapp. xapp. xapp. xsimpl. math. (* /SOLUTION *)
Qed.


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

Lemma Triple_decr_and_incr : forall p q n m,
  TRIPLE (decr_and_incr p q)
    PRE ((* SOLUTION *) p ~~> n \* q ~~> m (* /SOLUTION *))
    POST ((* SOLUTION *) fun (_:unit) => p ~~> (n-1) \* q ~~> (m+1) (* /SOLUTION *)).
Proof using.
  (* SOLUTION *) xwp. xapp. xapp. xsimpl. (* /SOLUTION *)
Qed.


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





