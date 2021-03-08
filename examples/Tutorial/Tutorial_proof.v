

Set Implicit Arguments.
From Sep Require Import Example.
From Sep Require ExampleStack ExampleList.
Generalizable Variables A.

Implicit Types n m : int.
Implicit Types p q : loc.


(* ####################################################### *)
(** * Basic programs *)

Module Basics.


(* ******************************************************* *)
(** *** Let computation *)

(**
[[
  let example_let n =
    let a = n + 1 in
    let b = n - 1 in
    a + b
]]
*)

Definition example_let :=
  Fun 'n :=
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


(* ******************************************************* *)
(** *** Increment *)

(**
[[
  let incr p =
    p := !p + 1
]]
*)

Definition incr : val :=
  Fun 'p :=
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
  Fun 'n :=
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
  Fun 'p 'q :=
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
  Fun 'p :=
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
  Fix 'f 'p 'm :=
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


(* ####################################################### *)
(** * Entailment tactic *)

Module XsimplDemo.

(* ******************************************************* *)
(** *** [xpull] to extract from LHS *)

Lemma xpull_demo_hpure : forall H1 H2 n,
  H1 \* \[n = 3] ==> H2.
Proof using.
  intros. xpull. intros Hn.
Abort.

Lemma xpull_demo_hexists : forall H1 H2 p,
  H1 \* \exists (n:int), (p ~~> n) ==> H2.
Proof using.
  intros. xpull. intros n.
Abort.

Lemma xpull_demo_lhs_several : forall H1 H2 H3 H4 p q,
  H1 \* \exists (n:int), (p ~~~> n \* \[n > 0] \* H2) \* \[p <> q] \* H3 ==> H4.
Proof using.
  intros. xpull. intros n Hn Hp. (* or [xpull ;=> n Hn Hp] *)
Abort.


(* ******************************************************* *)
(** *** [xsimpl] to cancel out heap predicates from LHS and RHS *)

(** For example, [H2] occurs on both sides, so it can be cancelled out. *)

Lemma xsimpl_demo_cancel_one : forall H1 H2 H3 H4 H5 H6 H7,
  H1 \* H2 \* H3 \* H4 ==> H5 \* H6 \* H2 \* H7.
Proof using.
  intros. xsimpl.
Abort.

(** [xsimpl] can cancel several predicates, here [H2], [H3], and [H4]. *)

Lemma xsimpl_demo_cancel_many : forall H1 H2 H3 H4 H5,
  H1 \* H2 \* H3 \* H4 ==> H4 \* H3 \* H5 \* H2.
Proof using.
  intros. xsimpl.
Abort.

(** If all the pieces get cancelled out, then the goal is discharged. *)

Lemma xsimpl_demo_cancel_all : forall H1 H2 H3 H4,
  H1 \* H2 \* H3 \* H4 ==> H4 \* H3 \* H1 \* H2.
Proof using.
  intros. xsimpl.
Qed.

(** [xsimpl] cancels what remains with the [\GC] from the RHS. *)

Lemma xsimpl_demo_rhs_hgc : forall H1 H2 H3 H4,
  H1 \* H2 \* H3 \* H4 ==> H3 \* H2 \* \GC.
Proof using.
  intros. xsimpl.
Abort.


(* ******************************************************* *)
(** *** [xsimpl] to instantiate pure facts and quantifiers in RHS *)

(** [xsimpl] instantiates existential quantifiers, pure facts,
    and [\Top] in the RHS. *)

Lemma xsimpl_demo_rhs_hpure : forall H1 H2 H3 (n:int),
  H1 ==> H2 \* \[n > 0] \* H3.
Proof using.
  intros. xsimpl.
Abort.

(** For existentials, [xsimpl] introduces an evar. *)

Lemma xsimpl_demo_rhs_hexists : forall H1 H2 H3 H4 (p:loc),
  H1 ==> H2 \* \exists (n:int), (p ~~> n \* H3) \* H4.
Proof using.
  intros. xsimpl. (* here, [p ~~> n] becomes [p ~~> ?x] *)
Abort.

(** The evar often gets subsequently instantiated during cancellation. *)

Lemma xsimpl_demo_rhs_hexists_unify : forall H1 H2 H3 H4 (p:loc),
  H1 \* (p ~~> 3) ==>
  H2 \* \exists (n:int), (p ~~> n \* H3) \* H4.
Proof using.
  intros. xsimpl. (* [p ~~~> n] becomes [p ~~~> ?x],
                     which then cancels out with [p ~~~> 3] *)
Abort.


(* ******************************************************* *)
(** ** The [xchange] tactic *)

(** [xchange] is to entailment what [rewrite] is to equality. *)

(** Assume an entailment goal of the form [H1 \* H2 \* H3 ==> H4].
    Assume an entailment assumption [M], say [H2 ==> H2'].
    Then [xchange M] turns the goal into [H1 \* H2' \* H3 ==> H4],
    effectively replacing [H2] with [H2']. *)

Lemma xchange_demo_base : forall H1 H2 H2' H3 H4,
  H2 ==> H2' ->
  H1 \* H2 \* H3 ==> H4.
Proof using.
  introv M. xchange M. (* Note that freshly produced items appear to the front *)
Abort.

(** The tactic [xchange] can also take as argument equalities.
    Use [xchange M] to exploit the left-to-right direction
    and [xchange <- M] to exploit the right-to-left direction . *)

Lemma xchange_demo_eq : forall H1 H2 H3 H4 H5,
  H1 \* H3 = H5 ->
  H1 \* H2 \* H3 ==> H4.
Proof using.
  introv M. xchange M.
  xchange <- M.
Abort.

(** The tactic [xchanges M] is a shorthand for [xchange M; xsimpl]. *)

End XsimplDemo.



(* ####################################################### *)
(** * Hands-on: basic functions *)

Module ExoBasic.

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
  Fun 'n :=
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
  Fun 'p :=
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
  Fun 'p 'q :=
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
  Fix 'f 'p 'q :=
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