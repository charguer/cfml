(**

This file formalizes basic examples in lifted Separation Logic,
both using lifted characteristic formulae.

Author: Arthur Charguéraud.
License: CC-by 4.0.

*)

Set Implicit Arguments.
From Sep Require Import Example ExampleBasicNonlifted.
Generalizable Variables A B.

Implicit Type p q : loc.
Implicit Types n : int.


(* ********************************************************************** *)
(* * Basic functions *)


(* ---------------------------------------------------------------------- *)
(** Swap function *)

(** [val_swap] defined in [ExampleBasicNonlifted.v] *)

Lemma Triple_swap_neq : forall A1 A2 `{EA1:Enc A1} `{EA2:Enc A2} (v:A1) (w:A2) p q,
  Triple (val_swap ``p ``q)
    PRE (p ~~> v \* q ~~> w)
    POST (fun (r:unit) => p ~~> w \* q ~~> v).
Proof using.
  xcf. xapps. xapps. xapps. xapps. xsimpl~.
Qed.

Lemma Triple_swap_eq : forall A1 `{EA1:Enc A1} (v:A1) p,
  Triple (val_swap ``p ``p)
    PRE (p ~~> v)
    POST (fun (r:unit) => p ~~> v).
Proof using.
  xcf. xapps. xapps. xapps. xapps. xsimpl~.
Qed.


(* ---------------------------------------------------------------------- *)
(** Basic two references *)

(** [val_example_let] defined in [ExampleBasicNonlifted.v] *)

Lemma Triple_val_example_let : forall n,
  Triple (val_example_let n)
    PRE \[]
    POST (fun r => \[r = 2*n]).
Proof using.
  xcf. xapps. xapps. xapp. xsimpl. math.
Qed.


(* ---------------------------------------------------------------------- *)
(** Basic let-binding example *)

(** [val_example_one_ref] defined in [ExampleBasicNonlifted.v] *)

Lemma Triple_val_example_one_ref : forall n,
  Triple (val_example_one_ref n)
    PRE \[]
    POST (fun r => \[r = n+2]).
Proof using.
  xcf. xapps. xapps ;=> r. xapp~. xapp~. xsimpl. math.
Qed.


(* ---------------------------------------------------------------------- *)
(** Basic let-binding two ref *)

(** [val_example_two_ref] defined in [ExampleBasicNonlifted.v] *)

Lemma Triple_val_example_two_ref : forall n,
  Triple (val_example_two_ref n)
    PRE \[]
    POST (fun r => \[r = n+1]).
Proof using.
  xcf. xapp ;=> i. xapp ;=> r.
  xapp~. xapp~. xapps. xapps. xapps. xapps~.
  xapps. xapps. xapps.
  xsimpl. math.
Qed.



(*


  (***********************************************************************)
  (** Mathematical definitions *)

  (** Factorial *)

  Parameter facto : int -> int.
  Parameter facto_zero : facto 0 = 1.
  Parameter facto_one : facto 1 = 1.
  Parameter facto_succ : forall n, n >= 1 -> facto n = n * facto(n-1).

  (** Fibonnaci *)

  Parameter fib : int -> int.
  Parameter fib_base : forall n, n <= 1 -> fib n = n.
  Parameter fib_succ : forall n, n > 1 -> fib n = fib(n-1) + fib(n-2).

  (** Primes *)

  Parameter prime : int -> Prop.
  Parameter divide_not_prime : forall n d,
    1 < d < n ->
    Z.rem n d = 0 ->
    ~ (prime n).
  Parameter not_divide_prime : forall n,
    (forall d, 1 < d < n -> Z.rem n d <> 0) ->
    (prime n).
  Parameter not_divide_prime_sqrt : forall n r,
    (forall d, 1 < d < r -> Z.rem n d <> 0) ->
    (r * r > n) ->
    (prime n).


  (***********************************************************************)
  (** Automation for mathematical subgoals *)

  Ltac auto_tilde ::= try solve [ intuition eauto with maths ].

  Hint Extern 1 (index ?M _) => subst M : maths.
  Hint Resolve index_zmake : maths.
  Hint Resolve index_bounds_impl : maths.
  Hint Resolve index_length_unfold int_index_prove : maths.
  Hint Resolve index_update : maths.

  (** Tactic [rew_maths] for simplifying math expressions *)

  Lemma math_plus_one_twice : forall n, ((n+1)+1) = n+2.
  Proof using. math. Qed.
  Lemma math_minus_same : forall n, n-n = 0.
  Proof using. math. Qed.
  Lemma math_two_minus_one : 2-1 = 1.
  Proof using. math. Qed.
  Lemma math_plus_minus_same : forall n m, (n+m)-m = n.
  Proof using. math. Qed.
  Hint Rewrite math_plus_one_twice math_minus_same
    math_two_minus_one math_plus_minus_same : rew_maths.






  (***********************************************************************)
  (** For loops *)

  let facto_for n =
    let r = ref 1 in
    for i = 1 to n do
      r := !r * i;
    done;
    !r

  let fib_for n =
    let a = ref 0 in
    let b = ref 1 in
    for i = 0 to n-1 do
      let c = !a + !b in
      a := !b;
      b := c;
    done;
    !a


  (***********************************************************************)
  (** While loops *)

  let example_while n =
    let i = ref 0 in
    let r = ref 0 in
    while !i < n do
      incr i;
      incr r;
    done;
    !r

  let facto_while n =
    let r = ref 1 in
    let i = ref 2 in
    while !i <= n do
      r := !i * !r;
      incr i;
    done;
    !r

  let is_prime n =
    let i = ref 2 in
    let p = ref true in
    while !p && (!i * !i <= n) do
      if (n mod !i) = 0
        then p := false;
      incr i;
    done;
    !p


  (***********************************************************************)
  (** Recursion *)

  let rec facto_rec n =
    if n <= 1
      then 1
      else n * facto_rec(n-1)

  let rec fib_rec n =
    if n <= 1
      then n
      else fib_rec(n-1) + fib_rec(n-2)


  (***********************************************************************)
  (** For loops *)

  (*---------------------------------------------------------------------*)
  (*----
  let facto_for n =
    let r = ref 1 in
    for i = 1 to n do
      r := !r * i;
    done;
    !r
  ----*)

  Lemma facto_for_spec : forall n,
    n >= 1 ->
    app facto_for [n]
      PRE \[]
      POST (fun (v:int) => \[v = facto n]).
  Proof using.
    =>> Hn. xcf. xapps.
    xfor_inv (fun i => r ~~> (facto (i-1))).
    { math. }
    { oldxsimpl. forwards: facto_zero. easy. }
    { =>> Hi. xapps. xapps. oldxsimpl.
      rew_maths. rewrite (@facto_succ i). ring.  math. }
    xapps.  oldxsimpl. rew_maths. auto.
  Qed.


  (* Remark: reasoning principle for the loop [for i = a to b to t done] when [b+1>=a]

    I a               initial invariant

    I i -> I (i+1)    when executing [t] on some [i] in the range from [a] to [b]

    I (b+1)           final invariant

  *)


  (*---------------------------------------------------------------------*)
  (*----
  let fib_for n =
    let a = ref 0 in
    let b = ref 1 in
    for i = 0 to n-1 do
      let c = !a + !b in
      a := !b;
      b := c;
    done;
    !a
  ----*)

  Lemma fib_for_spec : forall n,
    n >= 1 ->
    app fib_for [n]
      PRE \[]
      POST (fun (v:int) => \[v = fib n]).
  Proof using.


    (* <EXO> *)
    =>> Hn. xcf. xapps. xapps.
    xfor_inv (fun i => a ~~> (fib i) \* b ~~> (fib (i+1)) ).
    { math. }
    { oldxsimpl. rewrite fib_base. math. math. rewrite~ fib_base. (*math. math.*) }
    { =>> Hi. xapps. xapps. xrets. xapps. xapps. xapps. oldxsimpl.
      rew_maths. rewrite~ (@fib_succ (i+2)). rew_maths. math_rewrite ((i + 2)-1 = i+1). math. }
    xapps.  oldxsimpl~.
    (* </EXO> *)
  Qed.


  (*----Alternative script:

    =>> Hn. xcf. xapps. xapps.
    xfor_inv (fun i => a ~~> (fib i) \* b ~~> (fib (i+1))).
    { math. }
    { oldxsimpl.
      { forwards~: fib_base. math. }
      { forwards~: fib_base. math. } }
    { introv Hi. xapps. xapps. xret. intros. xapps. xapps. xapps. oldxsimpl.
      rewrite fib_succ. rew_maths. math. math. }
    xapps. oldxsimpl. auto.
  *)



  (***********************************************************************)
  (** While loops *)

  (*---------------------------------------------------------------------*)
  (*----
  let example_while n =
    let i = ref 0 in
    let r = ref 0 in
    while !i < n do
      incr i;
      incr r;
    done;
    !r
  ----*)

  Lemma example_while_spec : forall n,
    n >= 0 ->
    app example_while [n]
      PRE \[]
      POST (fun (v:int) => \[v = n]).
  Proof using.
    introv Hn. xcf. xapps. xapps.
    xwhile_inv_basic (fun b k => \[b = isTrue (k < n)] \* \[k <= n] \* i ~~> k \* r ~~> k)
      (upto n).
    { oldxsimpl. eauto. eauto. }
    { => b k. xtpull. => Hb Hk. xapps. xrets. auto. autos*. } (* short for: xret; oldxsimpl. *)
    { => k. xtpull. => Hb Hk. xapps. xapps. oldxsimpl.
      { math. }
      { eauto. }
      { hnf. math. } }
    =>> Hb Hk. xclean. xapps. oldxsimpl. subst. math.
  Qed.


  (*---------------------------------------------------------------------*)
  (*----
  let facto_while n =
    let r = ref 1 in
    let i = ref 1 in
    while !i <= n do
      r := !i * !r;
      incr i;
    done;
    !r
  ----*)

  Lemma facto_while_spec : forall n,
    n >= 2 ->
    app facto_while [n]
      PRE \[]
      POST (fun (v:int) => \[v = facto n]).
  Proof using.
    (* <EXO> *)
    introv Hn. xcf. xapps. xapps.
    xwhile_inv_basic (fun b k => \[b = isTrue (k <= n)] \* \[2 <= k <= n+1]
                                 \* i ~~> k \* r ~~> (facto (k-1)))
      (upto (n+1)).
    { oldxsimpl. rew_maths. rewrite~ facto_one. math. eauto. }
    { => b k. xtpull. => Hb Hk. xapps. xrets. auto. autos*. } (* short for: xret; oldxsimpl. *)
    { => k. xtpull. => Hb Hk. xapps. xapps. xapps. xapps. oldxsimpl.
      { rew_maths. rewrite (@facto_succ k). ring. math. }
      { math. }
      { eauto. }
      { math. } }
    =>> Hb Hk. xclean. xapps. oldxsimpl. subst. fequal. math.
    (* </EXO> *)
  Qed.


  (*---------------------------------------------------------------------*)
  (*----
  let is_prime n =
    let i = ref 2 in
    let p = ref true in
    while !p && (!i * !i <= n) do
      if (n mod !i) = 0
        then p := false;
      incr i;
    done;
    !p
  ----*)

  Lemma is_prime_spec : forall n,
    n >= 2 ->
    app is_prime [n]
      PRE \[]
      POST (fun (b:bool) => \[b = isTrue (prime n)]).
  Proof using.
    introv Hn. xcf. xapps. xapps.
    xwhile_inv_basic (fun b k => \exists vp,
            \[b = isTrue (vp = true /\ k*k <= n)]
         \* \[if vp then (forall d, 1 < d < k -> Z.rem n d <> 0) else (~ prime n)]
         \* \[2 <= k]
         \* i ~~> k
         \* p ~~> vp)
      (upto n).
    { oldxsimpl. math. math. eauto. }
    { => b k. xtpull ;=> vp Hb Hp Hk. xapps. xand.
      { xapps. xapps. xrets*. }
      { oldxsimpl*. } }
    { => k. xtpull ;=> vp Hb Hp Hk.
      (* TODO: xclean. *) xclean. destruct Hb as (Hvp&Hkk).
      xapps. xapps. math.
      xrets. xseq. xif (# \exists (vp':bool), i ~~> k \* p ~~> vp' \*
         \[if vp' then (forall d, 1 < d < (k+1) -> Z.rem n d <> 0) else (~ prime n)]).
        (* TODO: remove xseq *)
        { xapps. oldxsimpl. applys~ divide_not_prime. math_nia. }
        { xrets. rewrite Hvp in *. =>> Hd. tests: (d = k). auto. applys~ Hp. }
      xtpull ;=> vp' Hvp'. xapps. oldxsimpl.
      { math. }
      { auto. }
      { eauto. }
      { math_nia. } }
    => k vp Hb Hvp Hk. xclean. rew_logic in Hb.
    xapps. oldxsimpl. subst. case_if.
    { destruct Hb; tryfalse. applys* not_divide_prime_sqrt. math. }
    { auto. }
  Qed.


  (***********************************************************************)
  (** Recursion *)

  (*---------------------------------------------------------------------*)
  (*----
  let rec facto_rec n =
    if n <= 1
      then 1
      else n * facto_rec(n-1)
  ----*)

  Lemma facto_rec_spec : forall n,
    n >= 1 ->
    app facto_rec [n]
      PRE \[]
      POST (fun (v:int) => \[v = facto n]).
  Proof using.
    => n. induction_wf IH: (downto 0) n. unfolds downto. => Hn.
    xcf. xif.
    { xrets. math_rewrite (n=1). rewrite~ facto_one. }
    { xapps. math. math. (* could be written [xapps~] *)
      xrets. rewrite~ (@facto_succ n). }
  Qed.


  (*---------------------------------------------------------------------*)
  (*----
  let rec fib_rec n =
    if n <= 1
      then 1
      else fib_rec(n-1) + fib_rec(n-2)
  ----*)

  Lemma fib_rec_spec : forall n,
    n >= 0 ->
    app fib_rec [n]
      PRE \[]
      POST (fun (v:int) => \[v = fib n]).
  Proof using.
    (* <EXO> *)
    => n. induction_wf IH: (downto 0) n. => Hn.
    xcf. xif.
    { xrets. rewrite~ fib_base. }
    { xapps~. xapps~. xrets. rewrite~ (@fib_succ n). }
    (* </EXO> *)
  Qed.

*)
