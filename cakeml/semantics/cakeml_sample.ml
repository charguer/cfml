open Coq_from_hol

let defs : coqtopss =
  [ (* Definition f x y = x + y *)
    mk_define_val "f" (coq_impls [nat; nat] nat)
      (coq_funs [("x",nat); ("y",nat)]
        (coq_apps coq_nat_add [coq_var "x"; coq_var "y"]));

    (* Definition g x = f x (x+1) *)
    mk_define_val "g" (coq_impls [nat] nat)
      (coq_funs [("x",nat)]
        (coq_apps (coq_var "f") [coq_var "x"; coq_apps coq_nat_add [coq_var "x"; coq_nat 1]]))
  ]

let _ = out_prog "Cakeml" [] defs
