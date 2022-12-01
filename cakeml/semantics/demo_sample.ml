open Coq_from_hol

(* Example input in HOL syntax:

  Definition fib_def:
    fib (n:num) = if n < 2 then n else fib (n-1) + fib (n-2)

Expected output in Coq syntax:

  Fixpoint fib (n:nat) =
    If n < 2 then n else fib (n-1) + fib (n-2)

or

  Axiom fib : nat->nat.
  Lemma fib_def : forall (n:nat),
    fib n =
      If n < 2 then n else fib (n-1) + fib (n-2).


Below is an example for the lemma presentation,
which avoids issues with justifying termination.
*)

(* Variant with explicit calls to mk_app everywhere:

let defs =
  mk_define(
    "fib",
    "fib_def",
    [("n", mk_typ_nat)],
    mk_typ_nat,
    mk_eq(
      mk_app(mk_var("fib"), [mk_var("n")]),
      mk_if(
        mk_app(mk_var("Coq.Init.Peano.lt"), [mk_var("n"); mk_nat(2)]),
        mk_var("n"),
        mk_app(mk_var("Coq.Init.Nat.add"),
          [mk_app(mk_var("fib"), [mk_app(mk_var "Coq.Init.Nat.sub", [mk_var("n"); mk_nat(1)])]);
           mk_app(mk_var("fib"), [mk_app(mk_var "Coq.Init.Nat.sub", [mk_var("n"); mk_nat(2)])])]))))
*)

(* Variant using more smart constructors *)

let defs =
  mk_define(
    "fib",
    "fib_def",
    [("n", mk_typ_nat)],
    mk_typ_nat,
    mk_eq(
      mk_app(mk_var("fib"), [mk_var("n")]),
      mk_if(
        mk_lt(mk_var("n"), mk_nat(3)),
        mk_var("n"),
        mk_add(
          mk_app(mk_var("fib"), [mk_sub(mk_var("n"), mk_nat(1))]),
          mk_app(mk_var("fib"), [mk_sub(mk_var("n"), mk_nat(2))])))))


let _ = out_prog "demo.v" defs

