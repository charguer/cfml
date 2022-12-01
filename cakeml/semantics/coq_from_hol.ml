

open Coq


(*****************************************************************)
(* Placeholder *)

let mk_todo (msg:string) =
  coq_app_var "Prelude.COQ_HOLE" (coq_string_val msg)

let mk_wild =  (* [_] in Coq, can be written e.g. where a type is expected *)
  Coq_wild


(*****************************************************************)
(* Types *)

(* Representation of [Type] in Coq *)

let mk_typ_type =
  Coq_type

let mk_typ_nat =
  coq_nat

let mk_arrow (c1,c2) =
  coq_impl c1 c2

let mk_tvar (x:string) =
  Coq_var x

let mk_prod cs = (* [c1 * c2 * c3] product type *)
  coq_prod cs


(*****************************************************************)
(* Constants *)

let mk_var x =
  coq_var x

let mk_nat n =
  Coq_nat n

(*****************************************************************)
(* Structures *)

let mk_if (c0, c1, c2) =
  coq_classical_if c0 c1 c2

let mk_app (c0, cs) =
  coq_apps c0 cs


(*****************************************************************)
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


(*****************************************************************)
(* TODO: deprecated? *)

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
(* Value definitions *)

(* Function definition --> see doc in demo_sample.ml *)

(* TODO : rename to mk_def_fun *)
let mk_define(fun_name, lemma_name, typed_args_name, ret_typ, body) =
  let args_name, args_typ = List.split typed_args_name in
  let fun_typ = coq_impls args_typ ret_typ in
  [ Coqtop_param (fun_name, fun_typ);
    Coqtop_param (lemma_name, coq_foralls typed_args_name body) ]

(* Value definition (val_typ can be mk_wild) *)

let mk_define_val (val_name:string) (val_typ:coq) (val_body:coq) =
  [ Coqtop_def ((val_name,val_typ),val_body) ]


(*****************************************************************)
(* Type definitions *)

(* Type abbreviation [type name = typ_body]
   Note: for polymorphism, you can instantiate [typ_body] as
   a function taking types as arguments using [coq_fun_types] *)

let mk_typedef_abbrev (name:string) (typ_body:coq) : coqtops =
  [ Coqtop_def ((name,Coq_wild), typ_body) ]

(* Auxiliary function, takes as input [name] and [a, b], and returns
   a list [(a:Coq_type),(b:Coq_type)]. *)

let build_algebraic_targs (name:string) (typvars:string list) =
  List.map (fun x -> (x,mk_typ_type)) typvars

(* Record definition [type 'a name = { f1 : t1; f2 : t2 } *)

let mk_typedef_record (name:string) (typvars:string list) (fields:(string*coq) list) : coqtops =
  let targs = build_algebraic_targs name typvars in
  [ Coqtop_record {
   coqind_name = name;
   coqind_constructor_name = ("make_" ^ name);
   coqind_targs = targs;
   coqind_ret = mk_typ_type;
   coqind_branches = fields; } ]

(* Algebraic definition
   [type 'a name = C1 of t11 * t12 | C2 of t21 * t22 * t33]

   TODO: generalize to mutual inductive definitions *)

let mk_typedef_inductive (name:string) (typvars:string list) (cstrs:(string*(coq list)) list) : coqtops =
  let targs = build_algebraic_targs name typvars in
  let ret = coq_apps (coq_var name) (coq_vars typvars) in
  [ Coqtop_ind [ {
   coqind_name = name;
   coqind_constructor_name = "__dummy__";
   coqind_targs = targs;
   coqind_ret = mk_typ_type;
   coqind_branches =
     List.map (fun (cstr,args_typ) -> (cstr, coq_impls args_typ ret)) cstrs; } ] ]



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
