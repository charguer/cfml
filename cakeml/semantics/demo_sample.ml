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

let bool = coq_typ_bool
let nat = coq_typ_nat
let nzero = coq_nat 0

let defs2 =
    mk_define_val "demo_placeholder" nat (coq_todo "placeholder")
  @ mk_typedef_abbrev "demo_typ_abbrev" (coq_tuple [nat; nat])
  @ mk_typedef_record "demo_typ_record" ["A"] [ ("f1", nat); ("f2", coq_tvar "A"); ]
  @ mk_mutual_inductive_type [
      mk_coqind_type "ind0" ["A B"] [ ("C1", [nat; coq_tvar "A"]); ("C2", []); ("C3", [coq_tvar "B"])] ]
  @ mk_mutual_inductive_type [
      mk_coqind_type "ind1" ["A"] [ ("D1", [nat; coq_apps_vars "ind2" ["A"]]); ("D2", [])];
      mk_coqind_type "ind2" ["A"] [ ("E1", [nat; coq_tvar "A"]); ("E2", [coq_apps_vars "ind1" ["A"]])] ]
  @ let targs = [coq_typ_int; coq_typ_int] in
    mk_define_val "demo_match" coq_wild (
      coq_match (coq_cstr "C2" targs []) [
        ((coq_apps_vars "C1" ["x";"y"]), coq_int 3);
        ((coq_apps_vars "C2" []), coq_int 4);
        ((coq_apps_vars "C3" ["x"]), coq_int 5); ])

  @ mk_define_val "demo_record" (coq_wild) (coq_record [("f1",nzero); ("f2",coq_bool_true)])
  @ mk_define_val "demo_record_proj" (coq_wild) (coq_record_proj (coq_var "demo_record") "f2")
  @ mk_define_val "demo_tuple" (coq_typ_tuple [nat; nat; bool]) (coq_tuple [nzero; nzero; coq_bool_true])
  @ mk_define_val "demo_sum" (coq_sums [bool; nat; bool]) (coq_inl (coq_inr nzero))
  @ mk_define_val "demo_sum_annot" (coq_wild) (coq_inr ~typ_left:nat (coq_inl ~typ_right:bool nzero))
  @ mk_define_val "demo_option_none" (coq_typ_option nat) (coq_none())
  @ mk_define_val "demo_option_none_annot" (coq_wild) (coq_none ~typ:nat ())
  @ mk_define_val "demo_option_sone" (coq_wild) (coq_some nzero)
  @ mk_define_val "demo_option_sone_annot" (coq_wild) (coq_some ~typ:nat nzero)
  @ mk_define_val "demo_list_nil" (coq_wild) (coq_nil ~typ:nat ())
  @ mk_define_val "demo_list_cons" (coq_wild) (coq_cons ~typ:nat nzero (coq_nil()))
  @ mk_define_val "demo_list_list" (coq_wild) (coq_list [nzero; nzero])
  @ mk_define_val "demo_list_list_annot" (coq_wild) (coq_list ~typ:nat [nzero; nzero])
  @ mk_mutual_inductive_pred [
      mk_coqind_pred "foo" (coq_types ["A"]) (coq_preds [coq_typ_list (coq_tvar "A")])
        [ ("F1", coq_apps (coq_var_at "foo") [coq_tvar "A"; coq_nil()]);
          ("F2", coq_foralls
                   [ ("x", coq_wild);
                     ("l", coq_wild);
                     ("_", coq_apps (coq_var "foo") [coq_var "l"]) ]
                   (coq_apps (coq_var "foo") [coq_cons (coq_var "x") (coq_var "l")])) ]
    ]

let _ = out_prog "demo.v" (defs1 @ defs2)
