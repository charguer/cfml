Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From TLC Require Import LibOrder.
Generalizable Variables A.

Implicit Types n m : int.
Implicit Types p q : loc.

From EXAMPLES Require Import Tutorial_ml.


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

Lemma example_let_spec : forall n,
  SPEC (example_let n)
    PRE \[]
    POST (fun r => \[r = 2*n]).
Proof using.
  xcf. xlet. xlet. xval. xsimpl. math.
Qed.


(** Note: [xapp] calls [xlet] automatically when needed. *)

(** Note: [xsimpl*] does [xsimpl] but automation that can call [xmath]. *)


(* ******************************************************* *)
(** *** Increment *)

(**
[[
  let incr p =
    let n = !p in
    let m = n + 1 in
    p := m
]]
*)

Lemma incr_spec : forall (p:loc) (n:int),
  SPEC (incr p)
    PRE (p ~~> n)
    POSTUNIT (p ~~> (n+1)).
Proof using.
  xcf. xapp. xapp. xsimpl.
Qed.

Hint Extern 1 (RegisterSpec incr) => Provide incr_spec.


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

Lemma succ_using_incr_spec : forall n,
  SPEC (succ_using_incr n)
    PRE \[]
    POST (fun r => \[r = n+1]).
Proof using.
  xcf. xapp ;=> p. (* xapp. intros p. *)
  xapp. xapp. xsimpl*.
Qed.


(* ******************************************************* *)
(** *** Increment with two references *)

(**
[[
  let incr_one_of_two p q =
    incr p
]]
*)

Lemma incr_one_of_two_spec :
  forall (p q:loc) (n m:int),
  SPEC (incr_one_of_two p q)
    PRE (p ~~> n \* q ~~> m)
    POSTUNIT (p ~~> (n+1) \* q ~~> m).
Proof using.
  xcf. xapp. xsimpl.
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


Lemma incr_and_ref_spec : forall (p:loc) (n:int),
  SPEC (incr_and_ref p)
    PRE (p ~~> n)
    POST (fun (q:loc) => q ~~> (n+1) \* p ~~> (n+1)).
Proof using.
  xcf. xapp. xapp. xapp. xsimpl.
Qed.

#[global]
Hint Extern 1 (RegisterSpec incr_and_ref) => Provide incr_and_ref_spec.

Lemma incr_and_ref'_spec : forall (p:loc) (n:int),
  SPEC (incr_and_ref p)
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
      let r = m-1 in
      repeat_incr p r
    )
]]
*)

(** Let's try to prove a false specification *)

Lemma repeat_incr_spec : forall p n m,
  SPEC (repeat_incr p m)
    PRE (p ~~> n)
    POSTUNIT (p ~~> (n + m)).
Proof using.
  intros. gen n. induction_wf IH: (downto 0) m. intros.
  xcf. xif ;=> C.
  { (* then branch *)
    xapp. xapp. { unfold downto. math. } xsimpl. math. }
  { (* else branch *)
    xval. xsimpl.
Abort.

(** Let's try again *)

Lemma repeat_incr_spec : forall p n m,
  m >= 0 ->
  SPEC (repeat_incr p m)
    PRE (p ~~> n)
    POSTUNIT (p ~~> (n + m)).
Proof using.
  introv Hm. gen n Hm. induction_wf IH: (downto 0) m. intros.
  xcf. xif; intros C.
  { xapp. xapp. { hnf. math. } { math. }
    xsimpl. math. }
  { xval. xsimpl. math. }
Qed.

(** Let's try yet another time *)

Lemma max_l : forall n m,
  n >= m ->
  max n m = n.
Proof using. introv M. unfold max. case_if; math. Qed.

Lemma max_r : forall n m,
  n <= m ->
  max n m = m.
Proof using. introv M. unfold max. case_if; math. Qed.

Lemma repeat_incr'_spec : forall p n m,
  SPEC (repeat_incr p m)
    PRE (p ~~> n)
    POSTUNIT (p ~~> (n + max 0 m)).
Proof using.
  intros. gen n. induction_wf IH: (downto 0) m; intros.
  xcf. xif; intros C.
  { xapp. xapp. { hnf. math. }
    xsimpl. repeat rewrite max_r; math. }
  { xval. xsimpl. rewrite max_l; math. }
Qed.

(** Note: [xif] calls [xapp] if necessary. *)

End Basics.


(* ####################################################### *)
(** * Hands-on: basic functions *)

Module ExoBasic.
Import Basics.

(** Hints:
    - [xcf] to begin the proof
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

Lemma double_spec : forall n,
  SPEC (double n)
    PRE \[]
    POST (fun m => (* SOLUTION *) \[m = 2 * n] (* /SOLUTION *)).
Proof using.
  (* SOLUTION *) xcf. xval. xsimpl. math. (* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Basic imperative function with one argument *)

(**
[[
  let inplace_double p =
    let n1 = !p in
    let n2 = !p in
    p := n1 + n2
]]
*)

Lemma inplace_double_spec : forall p n,
  SPEC (inplace_double p)
    PRE ((* SOLUTION *) p ~~> n (* /SOLUTION *))
    POSTUNIT ((* SOLUTION *) p ~~> (2 * n) (* /SOLUTION *)).
Proof using.
  (* SOLUTION *) xcf. xapp. xapp. xapp. xsimpl. math. (* /SOLUTION *)
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

Lemma decr_and_incr_spec : forall p q n m,
  SPEC (decr_and_incr p q)
    PRE ((* SOLUTION *) p ~~> n \* q ~~> m (* /SOLUTION *))
    POSTUNIT ((* SOLUTION *) p ~~> (n-1) \* q ~~> (m+1) (* /SOLUTION *)).
Proof using.
  (* SOLUTION *) xcf. xapp. xapp. xsimpl. (* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** *** A recursive function (yellow belt) *)

(** Here, we will assume [!p > 0].

[[
  let rec transfer p q =
    let n = !p in
    let b = (n > 0) in
    if b then (
      decr p;
      incr q;
      transfer p q
    )
]]
*)

Lemma transfer_spec : forall p q n m,
  n >= 0 ->
  SPEC (transfer p q)
    PRE (p ~~> n \* q ~~> m)
    POSTUNIT ((* SOLUTION *) p ~~> 0 \* q ~~> (n + m) (* /SOLUTION *)).
Proof using.
  introv N. gen m N. induction_wf IH: (downto 0) n. intros.
  (* SOLUTION *)
  xcf. xapp. xif ;=> C.
  { xapp. xapp. xapp. { hnf. math. } { math. }
    xsimpl. math. }
  { xval. xsimpl. math. math. }
  (* /SOLUTION *)
Qed.

End ExoBasic.



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
  H1 \* \exists (n:int), (p ~~> n \* \[n > 0] \* H2) \* \[p <> q] \* H3 ==> H4.
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
