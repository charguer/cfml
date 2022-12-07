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

(* Examples of function definitions *)

let defs1 : coqtopss =
  [ (* Axiomatized fib *)
    mk_define_fun_via_lemma
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
           coq_apps (coq_var "fib") [coq_apps coq_nat_sub [coq_var "n"; coq_nat 2]]])));

    (* Non recursive function: test for empty list *)
    mk_define_fun ("isempty",
      [("A",coq_typ_type); ("l",coq_typ_list (coq_var "A"))],
      coq_typ_bool,
      coq_match (coq_var "l") [
        ((coq_apps_vars "nil" []), coq_bool_true);
        ((coq_apps_vars "cons" ["x";"t"]), coq_bool_false) ]);

    (* Recursive function: length of a list *)
    mk_define_fix [
      ("length",
      [("A",coq_typ_type); ("l",coq_typ_list (coq_var "A"))],
      coq_typ_nat,
      coq_match (coq_var "l") [
        ((coq_apps_vars "nil" []), coq_nat 0);
        ((coq_apps_vars "cons" ["x";"t"]),
          coq_apps coq_nat_add [coq_apps_vars "length" ["t"]; coq_nat 1]) ])];

    (* Mutually recursive function over lists of lists
     TODO: this currently generates valid code,
      but the example is not truely mutually recursive, so coq complains
    mk_define_fix [
      ("length2",
       [("A",coq_typ_type); ("l",coq_typ_list (coq_typ_list (coq_var "A")))],
       coq_typ_nat,
       coq_match (coq_var "l") [
        ((coq_apps_vars "nil" []), coq_nat 0);
        ((coq_apps_vars "cons" ["x";"t"]),
          coq_apps coq_nat_add [coq_apps_vars "length2" ["t"]; coq_apps_vars "length1" ["x"] ]) ] );
       ("length1",
       [("A",coq_typ_type); ("l",coq_typ_list (coq_var "A"))],
       coq_typ_nat,
       coq_match (coq_var "l") [
        ((coq_apps_vars "nil" []), coq_nat 0);
        ((coq_apps_vars "cons" ["x";"t"]),
          coq_apps coq_nat_add [coq_apps_vars "length1" ["t"]; coq_nat 1]) ])
      ];
      *)
   ]


(* More demos *)

let bool = coq_typ_bool
let nat = coq_typ_nat
let nzero = coq_nat 0

let defs2 : coqtopss =
  [ mk_define_val "demo_placeholder" nat (coq_todo "placeholder");
    mk_typedef_abbrev "demo_typ_abbrev" (coq_tuple [nat; nat]);
    mk_typedef_record "demo_typ_record" ["A"] [ ("f1", nat); ("f2", coq_tvar "A"); ];
    mk_mutual_inductive_type [
      mk_coqind_type "ind0" ["A B"] [ ("C1", [nat; coq_tvar "A"]); ("C2", []); ("C3", [coq_tvar "B"])] ];
    mk_mutual_inductive_type [
      mk_coqind_type "ind1" ["A"] [ ("D1", [nat; coq_apps_vars "ind2" ["A"]]); ("D2", [])];
      mk_coqind_type "ind2" ["A"] [ ("E1", [nat; coq_tvar "A"]); ("E2", [coq_apps_vars "ind1" ["A"]])] ];

    (let targs = [coq_typ_int; coq_typ_int] in
    mk_define_val "demo_match" coq_wild (
      coq_match (coq_cstr "C2" targs []) [
        ((coq_apps_vars "C1" ["x";"y"]), coq_int 3);
        ((coq_apps_vars "C2" []), coq_int 4);
        ((coq_apps_vars "C3" ["x"]), coq_int 5); ]));

    mk_define_val "demo_record" (coq_wild) (coq_record [("f1",nzero); ("f2",coq_bool_true)]);
    mk_define_val "demo_record_proj" (coq_wild) (coq_record_proj (coq_var "demo_record") "f2");
    mk_define_val "demo_tuple" (coq_typ_tuple [nat; nat; bool]) (coq_tuple [nzero; nzero; coq_bool_true]);
    mk_define_val "demo_sum" (coq_sums [bool; nat; bool]) (coq_inl (coq_inr nzero));
    mk_define_val "demo_sum_annot" (coq_wild) (coq_inr ~typ_left:nat (coq_inl ~typ_right:bool nzero));
    mk_define_val "demo_option_none" (coq_typ_option nat) (coq_none());
    mk_define_val "demo_option_none_annot" (coq_wild) (coq_none ~typ:nat ());
    mk_define_val "demo_option_sone" (coq_wild) (coq_some nzero);
    mk_define_val "demo_option_sone_annot" (coq_wild) (coq_some ~typ:nat nzero);
    mk_define_val "demo_list_nil" (coq_wild) (coq_nil ~typ:nat ());
    mk_define_val "demo_list_cons" (coq_wild) (coq_cons ~typ:nat nzero (coq_nil()));
    mk_define_val "demo_list_list" (coq_wild) (coq_list [nzero; nzero]);
    mk_define_val "demo_list_list_annot" (coq_wild) (coq_list ~typ:nat [nzero; nzero]);
    mk_mutual_inductive_pred [
      mk_coqind_pred "foo" (coq_types ["A"]) (coq_preds [coq_typ_list (coq_tvar "A")])
        [ ("F1", coq_apps (coq_var_at "foo") [coq_tvar "A"; coq_nil()]);
          ("F2", coq_foralls
                   [ ("x", coq_wild);
                     ("l", coq_wild);
                     ("_", coq_apps (coq_var "foo") [coq_var "l"]) ]
                   (coq_apps (coq_var "foo") [coq_cons (coq_var "x") (coq_var "l")])) ]
      ];
    mk_define_axioms [
      ("mycases", coq_impls [coq_typ_list nat] nat);
      ("mycases_nil", coq_app_eq (coq_apps (coq_var "mycases") [coq_nil()]) (coq_nat 0));
      ("mycases_cons", coq_foralls [("x",coq_wild);("t",coq_wild)]
         (coq_app_eq (coq_apps (coq_var "mycases") [coq_cons (coq_var "x") (coq_var "t")])
           (coq_apps coq_nat_add [coq_nat 1; coq_apps (coq_var "mycases") [coq_var "t"]])));
      ]
   ]

let defs3 : coqtopss =
  [ (* Definition f x y = x + y *)
    mk_define_val "f" (coq_impls [nat; nat] nat)
      (coq_funs [("x",nat); ("y",nat)]
        (coq_apps coq_nat_add [coq_var "x"; coq_var "y"]));

    (* Definition g x = f x (x+1) *)
    mk_define_val "g" (coq_impls [nat] nat)
      (coq_funs [("x",nat)]
        (coq_apps (coq_var "f") [coq_var "x"; coq_apps coq_nat_add [coq_var "x"; coq_nat 1]]))
  ]

let transfos =
  [ (* Replace definition of [f] with [Definition f a b c = ((a+c)+b)-c],
       and replace calls to [f x y] with calls to [f y x x] *)
    Transfo_alternative ("f",
      mk_custom "Definition f (a b c:nat) := ((a+c)+b)-c.",
      [ Transfo_replace("f", 2,
         coq_apps (coq_var "f") [mk_meta 1; mk_meta 0; mk_meta 0]) ])
  ]

(* Deprecated:
   mk_define_val "f"
    (coq_impls [nat; nat; nat] nat)
    (coq_funs [("a",nat); ("b",nat); ("c",nat)]
      (coq_apps coq_nat_sub
        [coq_apps coq_nat_add [
          coq_apps coq_nat_add [coq_var "a"; coq_var "c"];
          coq_var "b"];
        coq_var "c"])),*)

let _ = out_prog "Demo" transfos (defs1 @ defs2 @ defs3)
