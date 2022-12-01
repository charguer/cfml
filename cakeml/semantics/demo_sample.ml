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

(* Example: fib *)

let defs1 =
  mk_define
    "fib"
    "fib_def"
    [("n", mk_typ_nat)]
    mk_typ_nat
    (mk_eq
      (mk_app (mk_var "fib") [mk_var "n"])
      (mk_if
        (mk_app nat_lt [mk_var "n"; mk_nat 2])
        (mk_var "n")
        (mk_app
          nat_add
          [mk_app (mk_var "fib") [mk_app nat_sub [mk_var "n"; mk_nat 1]];
           mk_app (mk_var "fib") [mk_app nat_sub [mk_var "n"; mk_nat 2]]])));;


(* More demos *)

let defs2 =
    mk_define_val "demo_placeholder" mk_typ_nat (mk_todo "placeholder")
  @ mk_typedef_abbrev "demo_abbrev" (mk_prod [mk_typ_nat; mk_typ_nat])
  @ mk_typedef_record "demo_record" ["A"] [ ("f1", mk_typ_nat); ("f2", mk_tvar "A"); ]
  @ mk_typedef_inductive "demo_induct" ["A B"] [ ("C1", [mk_typ_nat; mk_tvar "A"]); ("C2", []); ("C3", [mk_tvar "B"])]
  (*  works, up to a missing type annotation
  @ mk_define_val "demo_match" mk_wild (
      mk_match_simple (mk_var "C2") [
        ("C1", ["x";"y"], mk_int 3);
        ("C2", [], mk_int 4);
        ("C3", ["x"], mk_int 5); ]) *)

let _ = out_prog "demo.v" (defs1 @ defs2)
