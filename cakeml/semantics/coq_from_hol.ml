
(*****************************************************************)
(* Smart constructors for Coq AST *)

open Coq

(* Types *)

let mk_typ_nat =
  coq_nat

let mk_arrow (c1,c2) =
  coq_impl c1 c2

(* Constants *)

let mk_var x =
  coq_var x

let mk_nat n =
  Coq_nat n

(* Structures *)

let mk_if (c0, c1, c2) =
  coq_classical_if c0 c1 c2

let mk_app (c0, cs) =
  coq_apps c0 cs

(* Top-level definitions *)

let mk_define(fun_name, lemma_name, typed_args_name, ret_typ, body) =
  let args_name, args_typ = List.split typed_args_name in
  let fun_typ = coq_impls args_typ ret_typ in
  [ Coqtop_param (fun_name, fun_typ);
    Coqtop_param (lemma_name, coq_foralls typed_args_name body) ]

(* Usual functions *)

let mk_var_eq =
  mk_var("Coq.Init.Logic.eq")

let mk_var_lt =
  mk_var("Coq.Init.Peano.lt")

let mk_var_eq =
  mk_var("Coq.Init.Logic.eq")

let mk_var_add =
  mk_var("Coq.Init.Nat.add")

let mk_var_sub =
  mk_var("Coq.Init.Nat.sub")

let mk_app2 (c0, c1, c2) =
  mk_app (c0, [c1; c2])

let mk_lt (c1, c2) =
  mk_app2 (mk_var_lt, c1, c2)

let mk_eq (c1, c2) =
  mk_app2 (mk_var_eq, c1, c2)

let mk_add (c1, c2) =
  mk_app2 (mk_var_add, c1, c2)

let mk_sub (c1, c2) =
  mk_app2 (mk_var_sub, c1, c2)

let mk_eq (c1, c2) =
  mk_app2 (mk_var_eq, c1, c2)


(*****************************************************************)
(* Generation of output *)

(* function copied from generator/Mytools.ml *)
let file_put_contents filename text =
   try
      let handle = open_out filename in
      output_string handle text;
      close_out handle
   with Sys_error s ->
     failwith ("Could not write in file: " ^ filename ^ "\n" ^ s)

let out_prog filename defs =
  let defs = (Coqtop_require_import ["Prelude"]) :: defs in
  let text = Print_coq.tops defs in
  file_put_contents filename text
