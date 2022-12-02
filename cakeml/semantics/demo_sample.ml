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
    [("n", coq_typ_nat)]
    coq_typ_nat
    (coq_app_eq
      (coq_apps (coq_var "fib") [coq_var "n"])
      (coq_if_prop
        (coq_apps coq_nat_lt [coq_var "n"; coq_nat 2])
        (coq_var "n")
        (coq_apps
          coq_nat_add
          [coq_apps (coq_var "fib") [coq_apps coq_nat_sub [coq_var "n"; coq_nat 1]];
           coq_apps (coq_var "fib") [coq_apps coq_nat_sub [coq_var "n"; coq_nat 2]]])));;


(* More demos *)

let defs2 =
    mk_define_val "demo_placeholder" coq_typ_nat (coq_todo "placeholder")
  @ mk_typedef_abbrev "demo_abbrev" (coq_tuple [coq_typ_nat; coq_typ_nat])
  @ mk_typedef_record "demo_record" ["A"] [ ("f1", coq_typ_nat); ("f2", coq_tvar "A"); ]
  @ mk_typedef_inductive "demo_induct" ["A B"] [ ("C1", [coq_typ_nat; coq_tvar "A"]); ("C2", []); ("C3", [coq_tvar "B"])]
  (*  works, up to a missing type annotation
  @ mk_define_val "demo_match" coq_wild (
      mk_match_simple (coq_var "C2") [
        ("C1", ["x";"y"], coq_int 3);
        ("C2", [], coq_int 4);
        ("C3", ["x"], coq_int 5); ]) *)

let _ = out_prog "demo.v" (defs1 @ defs2)
