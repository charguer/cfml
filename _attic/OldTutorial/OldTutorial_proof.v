Set Implicit Arguments.
Require Import CFML.CFLib.
Require Import Stdlib.
Require Import Array_proof.
Require Import Tuto_ml.
Require Import TLC.LibListZ.


(***********************************************************************)
(** Cheat list *)

(**
Specification syntax:
   - [TRIPLE (f x y)
        PRE H
        POST (fun (r:T) => H']

Heap syntax H :  heap -> Prop ::=
   - \[]
   - \[P]
   - H \* H'
   - r ~~> v        r ~> Ref v       Ref v r
   - r ~~> (v+1)
   - \exists x, H
   - r ~> Stack L       Stack L r

Coq tactics:
   - [=> x], [=>> H], [exists v]
   - [rew_maths] for normalizing math expressions
   - [rew_list] for normalizing list operations
   - [autos], [math], [ring], [math_nia]

CFML tactics:
   - [xwp]
   - [xsimpl], or [xsimpl X1 .. X2] (to instantiate Hexists)
   - [xpull]
   - [xclean] sometimes needed to do simplifications (TODO:update)
   - [xret], or [xrets] for substitution/simplification
   - [xapp], or [xapps] for substitution
   - [xfor_inv (fun i => H)]
   - [xwhile_inv_basic (fun b k => [b = isTrue(..)] \* H) (downto n)]
   - [xif Q]
   - [xmatch]

Shortcut:  (TODO: update)
   - [xpulls] like [xpull; intros x; subst x]
   - [xrets] like [xret; xsimpl]
   - [xapps] like [xapp; xpulls]
   - [tactic~] like [tactic; eauto with maths]
*)


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
  (* TODO: try to use jauto *)

Hint Extern 1 (index ?M _) => subst M : maths.
Hint Resolve LibListZ.index_make : maths.
Hint Resolve index_of_inbound : maths.
Hint Resolve index_of_index_length int_index_prove : maths.
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
(** Basic operations *)

(*---------------------------------------------------------------------*)

(**
[[
  let example_let n =
    let a = n+1 in
    let b = n-1 in
    a + b
]]
*)

Lemma example_let_spec : forall n,
  TRIPLE (example_let n)
    PRE \[]
    POST (fun (v:int) => \[v = 2*n]).
   (* post-condition also written: POST \[= (2 * n)]  *)
Proof using.
  (* Hint: the proof uses [xcf], [xret], [xsimpl], [math].
     [xlet] is optional; if used then [xpull] is also needed. *)
  dup 3.
  { (* detailed proof *)
    xcf.
    xlet. xret. simpl. xpull. intros Ha.
    xlet. xret. simpl. xpull. intros Hb.
    xret. (*hnf.*) xsimpl. math. }
  { (* shorter proof *)
    xcf. xret ;=> Ha. xret ;=> Hb. xret. xsimpl. math. }
  { (* real proof *)
    xcf. xrets. xrets. xrets. math. }
Qed.


(*---------------------------------------------------------------------*)

(**
[[
  let example_incr r =
    r := !r + 1
]]

normalized to:

[[
  let example_incr r =
    let x0__ := get r in
    set r (x0__ + 1)
]]
*)

Lemma example_incr_spec : forall r n,
  TRIPLE (example_incr r)
    PRE (r ~~> n)
    POST (fun (_:unit) => (r ~~> (n+1))).
    (* post-condition also written: POST (# r ~~> (n+1)). *)
Proof using.
  (* Hint: the proof uses [xcf], [xapp].
     [xapps] is a shortand for [xapp] followed with [subst]. *)
  dup 3.
  { xcf. xlet. xapp. simpl. xpull. intros. subst. xapp. }
  { xcf. xapp. intros. subst. xapp. }
  { xcf. xapps. xapp. }
Qed.

(* Note: recall the specifications of get and set from Pervasives_proof:

  Lemma get_spec : forall A (v:A) r,
    app get [r]
      PRE (r ~~> v)
      POST (fun x => \[x = v] \* r ~~> v)

  Lemma set_spec : forall A (v w:A) r,
    app set [r w] (r ~~> v) (# r ~~> w).

*)

(*---------------------------------------------------------------------*)

(**
[[
let example_two_ref n =
  let i = ref 0 in
  let r = ref n in
  decr r;
  incr i;
  r := !i + !r;
  !i + !r
]]
*)

Lemma example_two_ref_spec : forall n: int,
  (* <EXO> *)
  TRIPLE (example_two_ref n)
     PRE \[]
     POST (fun x: int => \[ x = n+1 ]).
  (* </EXO *)
Proof using.
  (* Hint: the proof uses [xcf], [xapp], [xapps], and [xret] or [xrets]. *)
  dup 3.
  { (* detailed proof *)
    xcf.
    xapp. (* details: xlet. xapp. simpl. *)
    xapp. xapp. xapp.
    xapps. (* details: xapp. intro. subst. *)
    xapps. xapps. xapps. xapps.
    xrets. (* details: xret. xsimpl. *)
    math. }
  { (* shorter proof, not recommended for nontrivial code *)
    xcf. xgo. subst. math. }
  { (* real proof *)
    xcf. xgo~. }
Qed.



(***********************************************************************)
(** For loops *)

(*---------------------------------------------------------------------*)

(**
[[
  let facto_for n =
    let r = ref 1 in
    for i = 1 to n do
      r := !r * i;
    done;
    !r
]]
*)

(* Reasoning principle for the loop [for i = a to b to t done] when [b+1>=a]
   implemented by tactic [xfor_inv I].

  I a               initial invariant

  I i -> I (i+1)    when executing [t] on some [i] in the range from [a] to [b]

  I (b+1)           final invariant

*)

Lemma facto_for_spec : forall n,
  n >= 1 ->
  TRIPLE (facto_for n)
    PRE \[]
    POST (fun (v:int) => \[v = facto n]).
Proof using.
  =>> Hn. xcf. xapps.
  xfor_inv (fun i => r ~~> (facto (i-1))).
  { math. }
  { xsimpl. forwards: facto_zero. easy. }
  { =>> Hi. xapps. xapps. xsimpl.
    rew_maths. rewrite (@facto_succ i). ring. math. }
  xapps. xsimpl. rew_maths. auto.
Qed.



(*---------------------------------------------------------------------*)

(**
[[
  let fib_for n =
    let a = ref 0 in
    let b = ref 1 in
    for i = 0 to n-1 do
      let c = !a + !b in
      a := !b;
      b := c;
    done;
    !a
]]
*)

Lemma fib_for_spec : forall n,
  n >= 1 ->
  TRIPLE (fib_for n)
    PRE \[]
    POST (fun (v:int) => \[v = fib n]).
Proof using.
  (* Hint: follow the pattern from the previous example *)
  (* <EXO> *)
  =>> Hn. xcf. xapps. xapps.
  xfor_inv (fun i => a ~~> (fib i) \* b ~~> (fib (i+1)) ).
  { math. }
  { xsimpl.
    rewrite~ fib_base. (* details: math. math. rewrite fib_base. *)
    rewrite~ fib_base. }
  { =>> Hi. xapps. xapps. xrets. xapps. xapps. xapps. xsimpl.
    rew_maths. rewrite~ (@fib_succ (i+2)). rew_maths.
    math_rewrite ((i + 2)-1 = i+1). math. }
  xapps. xsimpl~.
  (* </EXO> *)
Qed.


(*----Alternative script:

  =>> Hn. xcf. xapps. xapps.
  xfor_inv (fun i => a ~~> (fib i) \* b ~~> (fib (i+1))).
  { math. }
  { xsimpl.
    { forwards~: fib_base. math. }
    { forwards~: fib_base. math. } }
  { introv Hi. xapps. xapps. xret. intros. xapps. xapps. xapps. xsimpl.
    rewrite fib_succ. rew_maths. math. math. }
  xapps. xsimpl. auto.
*)



(***********************************************************************)
(** While loops *)

(*---------------------------------------------------------------------*)

(**
[[
  let example_while n =
    let i = ref 0 in
    let r = ref 0 in
    while !i < n do
      incr i;
      incr r;
    done;
    !r
]]
*)

(* Reasoning principle for the loop [while t1 do t2] using an invariant
   implemented by tactic [xwhile_inv_basic J W].

  J b i             true for some boolean [b] and some initial index [k]

  J b i             when executing [t1] on some [i]
   ->
  J b' i

  J true i          when executing [t2] on some [i], should restablish the
   ->               invariant for some [b'] and some [i'] smaller than [i]
  J b' i'           w.r.t. [W], that is [W i' i].

  J false i         for some [i] describes the final state

*)


Lemma example_while_spec : forall n,
  n >= 0 ->
  TRIPLE (example_while n)
    PRE \[]
    POST (fun (v:int) => \[v = n]).
Proof using.
  introv Hn. xcf. xapps. xapps.
  xwhile_inv_basic (fun b k => \[b = isTrue (k < n)] \* \[k <= n] \* i ~~> k \* r ~~> k)
    (upto n).
  { xsimpl. eauto. eauto. }
  { => b k. xpull. => Hb Hk. xapps. xrets. auto. autos*. } (* short for: xret; xsimpl. *)
  { => k. xpull. => Hb Hk. xapps. xapps. xsimpl.
    { math. }
    { eauto. }
    { hnf. math. } }
  =>> Hb Hk. xclean. xapps. xsimpl. subst. math.
Qed.


(*---------------------------------------------------------------------*)

(**
[[
  let facto_while n =
    let r = ref 1 in
    let i = ref 1 in
    while !i <= n do
      r := !i * !r;
      incr i;
    done;
    !r
]]
*)

Lemma facto_while_spec : forall n,
  n >= 2 ->
  TRIPLE (facto_while n)
    PRE \[]
    POST (fun (v:int) => \[v = facto n]).
Proof using.
  (* Hint: follow the pattern from previous example *)
  (* <EXO> *)
  introv Hn. xcf. xapps. xapps.
  xwhile_inv_basic (fun b k => \[b = isTrue (k <= n)] \* \[2 <= k <= n+1]
                               \* i ~~> k \* r ~~> (facto (k-1)))
    (upto (n+1)).
  { xsimpl. rew_maths. rewrite~ facto_one. math. eauto. }
  { => b k. xpull. => Hb Hk. xapps. xrets. auto. autos*. } (* short for: xret; xsimpl. *)
  { => k. xpull. => Hb Hk. xapps. xapps. xapps. xapps. xsimpl.
    { rew_maths. rewrite (@facto_succ k). ring. math. }
    { math. }
    { eauto. }
    { math. } }
  =>> Hb Hk. xclean. xapps. xsimpl. subst. fequal. math.
  (* </EXO> *)
Qed.


(*---------------------------------------------------------------------*)

(* TODO: add demos using the other xfor and xwhile approach *)

(*---------------------------------------------------------------------*)

(**
[[
  let is_prime n =
    let i = ref 2 in
    let p = ref true in
    while !p && (!i * !i <= n) do
      if (n mod !i) = 0
        then p := false;
      incr i;
    done;
    !p
]]
*)

Require Import Psatz.
Tactic Notation "math_nia" := math_setup; nia.

Lemma is_prime_spec : forall n,
  n >= 2 ->
  TRIPLE (is_prime n)
    PRE \[]
    POST (fun (b:bool) => \[b = isTrue (prime n)]).
Proof using.
  introv Hn. xcf. xapps. xapps.
  xwhile_inv_basic (fun b k => Hexists vp,
          \[b = isTrue (vp = true /\ k*k <= n)]
       \* \[if vp then (forall d, 1 < d < k -> Z.rem n d <> 0) else (~ prime n)]
       \* \[2 <= k]
       \* i ~~> k
       \* p ~~> vp)
    (upto n).
  { xsimpl. math. math. eauto. }
  { => b k. xpull ;=> vp Hb Hp Hk. xapps. xand.
    { xapps. xapps. xrets*. }
    { xsimpl*. } }
  { => k. xpull ;=> vp Hb Hp Hk.
    xclean. (* cleans up results of boolean tests *)
    destruct Hb as (Hvp&Hkk).
    xapps. xapps. math.
    xrets.
    xseq. (* TODO: later try to change xif to remove xseq *)
    xif (# Hexists (vp':bool), i ~~> k \* p ~~> vp' \*
       \[if vp' then (forall d, 1 < d < (k+1) -> Z.rem n d <> 0) else (~ prime n)]).
      { xapps. xsimpl. applys~ divide_not_prime. math_nia. }
      { xrets. rewrite Hvp in *. =>> Hd. tests: (d = k). auto. applys~ Hp. }
    xpull ;=> vp' Hvp'. xapps. xsimpl.
    { math. }
    { auto. }
    { eauto. }
    { math_nia. } }
  => k vp Hb Hvp Hk. xclean. rew_logic in Hb.
  xapps. xsimpl. subst. case_if; rew_bool_eq.
  { destruct Hb; tryfalse. applys* not_divide_prime_sqrt. math. }
  { auto. }
Qed.


(***********************************************************************)
(** Recursion *)

(*---------------------------------------------------------------------*)

(**
[[
  let rec facto_rec n =
    if n <= 1
      then 1
      else n * facto_rec(n-1)
]]
*)

Lemma facto_rec_spec : forall n,
  n >= 1 ->
  TRIPLE (facto_rec n)
    PRE \[]
    POST (fun (v:int) => \[v = facto n]).
Proof using.
  => n. induction_wf IH: (downto 0) n. unfolds downto. => Hn.
  xcf. xif.
  { xrets. math_rewrite (n=1). rewrite~ facto_one. }
  { xapps. math. math. (* optimization: could be written [xapps~] *)
    xrets. rewrite~ (@facto_succ n). }
Qed.


(*---------------------------------------------------------------------*)

(**
[[
  let rec fib_rec n =
    if n <= 1
      then 1
      else fib_rec(n-1) + fib_rec(n-2)
]]
*)

Lemma fib_rec_spec : forall n,
  n >= 0 ->
  TRIPLE (fib_rec n)
    PRE \[]
    POST (fun (v:int) => \[v = fib n]).
Proof using.
  (* Hint: follow the pattern for the previous example *)
  (* <EXO> *)
  => n. induction_wf IH: (downto 0) n. => Hn.
  xcf. xif.
  { xrets. rewrite~ fib_base. }
  { xapps~. xapps~. xrets. rewrite~ (@fib_succ n). }
  (* </EXO> *)
Qed.



(***********************************************************************)
(** Stack *)

(*---------------------------------------------------------------------*)

(*
[[
  module StackList = struct

    type 'a t = {
       mutable items : 'a list;
       mutable size : int }

    let create () =
      { items = [];
        size = 0 }

    let size s =
      s.size

    let is_empty s =
      s.size = 0

    let push x s =
      s.items <- x :: s.items;
      s.size <- s.size + 1

    let pop s =
      match s.items with
      | hd::tl ->
          s.items <- tl;
          s.size <- s.size - 1;
          hd
      | [] -> assert false

  end
]]
*)

Module StackListProof.

Import StackList_ml.


(** Definition of [r ~> Stack L], which is a notation for [Stack L r] of type [hprop] *)

Definition Stack A (L:list A) r :=
  Hexists n,
      r ~> `{ items' := L; size' := n }
   \* \[ n = length L ].

(** Unfolding and folding lemmas paraphrasing the definition of [Stack] *)

Lemma Stack_open : forall r A (L:list A),
  r ~> Stack L ==>
  Hexists n, r ~> `{ items' := L; size' := n } \* \[ n = length L ].
Proof using. dup 2.
  { intros. xunfold Stack. hpull. intros. hcancel. auto.
    (* Try [hcancel 3] to see how it works *) }
  { intros. xunfolds~ Stack. }
Qed.


Lemma Stack_close : forall r A (L:list A) (n:int),
  n = length L ->
  r ~> `{ items' := L; size' := n } ==>
  r ~> Stack L.
Proof using. intros. xunfolds~ Stack. Qed.

Arguments Stack_close : clear implicits.


(** Customization of [xopen] and [xclose] tactics for [Stack].
    These tactics avoid the need to call [hchange] or [xchange]
    by providing explicitly the lemmas [Stack_open] and [Stack_close].
    Note that the number of underscores avec [Stack] after the [RegisterOpen]
    needs to match the number of arguments of the representation predicate
    [Stack], excluding the pointer. (Here, we have one underscore for [L].) *)

Hint Extern 1 (RegisterOpen (Stack _)) =>
  Provide Stack_open.
Hint Extern 1 (RegisterClose (record_repr _)) =>
  Provide Stack_close.


(** Verification of the code *)

Lemma create_spec : forall (A:Type),
  app create [tt]
    PRE \[]
    POST (fun r => r ~> Stack (@nil A)).
Proof using.
  xcf. dup 2.
  { xapp. intros r.  (* or just [xapp. => r] *)
    xclose r. auto. xsimpl. }
  { xapp ;=> r. xclose~ r. }
Qed.

Lemma size_spec : forall (A:Type) (L:list A) (s:loc),
  app size [s]
    INV (s ~> Stack L)
    POST (fun n => \[n = length L]).
(* Remark: the above is a notation for:
  app size [s]
    PRE (s ~> Stack L)
    POST (fun n => \[n = length L] \* s ~> Stack L).
*)
Proof using.
  xcf. (* TODO: add xopens to do xpull *)
  xopen s. (* details: xchange (@Stack_open s). *)
  xpull ;=> n Hn.
  (* interesting: do [unfold tag] here, to unfold this identity
     function used to decorate the file. *)
  xapp. (* computes on-the-fly the record_get specification *)
  intros m.
  xpull ;=> ->. (* details: [xpull. intros E. subst E.] *)
  xclose s. (* details: xchange (@Stack_close s). *)
  auto. xsimpl. math.
  (* Here we have an issue because Coq is a bit limited.
     Workaround to discharge the remaining type: *)
  Unshelve. solve_type. (* TODO: support [xcf A] in the beginning *)
Qed.

Lemma length_zero_iff_nil : forall A (L:list A),
  length L = 0 <-> L = nil.
Proof using.
  intros. destruct L; rew_list. (* [rew_list] normalizes list expressions *)
  { autos*. (* [intuition eauto] *) }
  { iff M; false; math. (* [iff M] is [split; intros M] *) }
Qed.

Lemma is_empty_spec : forall (A:Type) (L:list A) (s:loc),
  (* <EXO> *)
  app is_empty [s]
    INV (s ~> Stack L)
    POST (fun b => \[b = isTrue (L = nil)]).
  (* </EXO> *)
Proof using.
  (* Hint: use [xopen] then [xclose] like in [size_spec].
     Also use [xcf], [xpull], [xapps], [xrets],
     and lemma [length_zero_iff_nil] from above. *)
  (* <EXO> *)
  xcf.
  (* Note that the boolean expression [n = 0] from Caml
     was automatically translated into [isTrue (x0__ = 0)];
     Indeed, [Ret_ P] is notation for [Ret (isTrue P)]. *)
  xopen s. xpull ;=> n Hn. xapps. xclose~ s.
  dup 2.
  { xret_no_clean.
    reflect_clean tt. (* automatically called by [hsimpl] *)
    hsimpl.
    subst. apply length_zero_iff_nil. }
  { xrets. subst. apply length_zero_iff_nil. }
  (* </EXO> *)
  Unshelve. solve_type.
Qed.

Lemma push_spec : forall (A:Type) (L:list A) (s:loc) (x:A),
  app push [x s]
    PRE (s ~> Stack L)
    POST (# s ~> Stack (x::L)).
Proof using.
  (* Hint: use [xcf], [xapp], [xapps], [xpull], [xsimpl],
     [xopen], [xclose] and [rew_list] *)
  (* <EXO> *)
  xcf.
  xopen s. (* details: xchange (@Stack_open s) *)
  xpull ;=> n Hn.
  xapps. xapp.
  xapps. xapp.
  xclose s. (* details: xchange (@Stack_close s) *)
  rew_list. (* normalizes expression on lists *)
  math.
  xsimpl.
  (* </EXO> *)
Qed.

Hint Extern 1 (RegisterSpec push) => Provide push_spec.

(* [xapp] on a call to push.
   Otherwise, need to do [xapp_spec push_spec]. *)

Lemma pop_spec : forall (A:Type) (L:list A) (s:loc),
  L <> nil ->
  app pop [s]
    PRE (s ~> Stack L)
    POST (fun x => Hexists L', \[L = x::L'] \* s ~> Stack L').
Proof using.
  (* Hint: also use [rew_list in H] *)
  (* <EXO> *)
  =>> HL. xcf. xopen s. xpull ;=> n Hn. xapps. xmatch.
  xapps. xapps. xapps. xret. xclose~ s. rew_list in Hn. math.
  (* </EXO> *)
Qed.



(***********************************************************************)
(** Array *)

(*---------------------------------------------------------------------*)
(*
[[
  let demo_array () =
    let t = Array.make 3 true in
    t.(0) <- false;
    t.(1) <- false;
    t
]]
*)

Lemma demo_array_spec :
  app demo_array [tt]
    PRE \[]
    POST (fun (t:loc) => Hexists M, (t ~> Array M)
       \* \[forall k, 0 <= k < 3 -> M[k] = isTrue(k > 1)]).
Proof using.
  dup 2.
  { (* Detailed proof: *)
    xcf.
    xapp. math. => M EM.
    xapp. autos.
    xapp. autos.
    xret. xsimpl. =>> Hk. subst M. rew_array; autos.
     case_ifs. math. math. math. }
  { (* Shorter proof *)
    xcf. xapp~. => M EM. xapp~. xapp~. xrets.
    =>> Hk. subst M. rew_array~. case_ifs; math. }
Qed.



(*---------------------------------------------------------------------*)
(*
[[
  let exercise_array () =
    let t = Array.make 3 true in
    t.(2) <- false;
    t.(1) <- t.(2);
    t
]]
*)

Lemma exercise_array_spec :
  App exercise_array tt;
    \[]
    (fun (t:loc) => Hexists M, (t ~> Array M) \*
      \[length M = 3
    /\ forall k, 0 <= k < 3 -> M[k] = isTrue(k<1)]).
Proof using.
  xcf.
  xapp. autos. intros M EM. subst M.
  xapp. autos.
  xapp~ as v. intros Ev.
  xapp~.
  xret.
  xsimpl. split.
    rew_array~.
    introv Hk. rew_array~. case_ifs.
      subst v. rew_array~. case_if~. math.
      math.
      math.
  (* Optional forward reasoning after [intros Ev]:
    asserts Ev': (v = false).
      subst. rew_array~. case_if~.
      clear Ev. subst v. *)
Qed.





(***********************************************************************)
(***********************************************************************)
(***********************************************************************)

End StackListProof.



(* LATER
  Hint Resolve length_nonneg : maths.
  Hint Extern 1 (length (?l[?i:=?v]) = _) => rewrite length_update.
  Hint Resolve length_make : maths.
  Hint Extern 1 (length ?M = _) => subst M : maths.
  Hint Constructors Forall.
  Global Opaque Z.mul.
*)