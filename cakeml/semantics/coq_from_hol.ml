
include Coq

(* Remark: [type var = string] *)


(*****************************************************************)
(** Complement to coq.ml *)

(* Placeholder for missing Coq subterms: [COQ_HOLE] admits any type. *)

let coq_todo (msg:string) =
  coq_app_var "Prelude.COQ_HOLE" (coq_string msg)

(* Alias [coq_tvar] to record references to type variables, as opposed to program variables *)

let coq_tvar (x:string) =
  coq_var x


(*****************************************************************)
(* Encoding for programming language constructs *)

(* Simplified pattern matching
     match scrunity with
     | C1 x1 x2 => body1
     | C2 x1 x2 x3 => body2
     end
  *)

let mk_match_simple (scrunity:coq) (branches:(var*(var list)*coq) list) =
  let mk_branch (cstr_name, pat_vars, body) =
    let pattern = coq_apps (coq_var cstr_name) (coq_vars pat_vars) in
    (pattern,body) in
  coq_match scrunity (List.map mk_branch branches)


(*****************************************************************)
(* Toplevel value definitions *)

(* Function definition --> see doc in demo_sample.ml *)

(* TODO : rename to mk_def_fun *)
let mk_define fun_name lemma_name typed_args_name ret_typ body =
  let args_name, args_typ = List.split typed_args_name in
  let fun_typ = coq_impls args_typ ret_typ in
  [ Coqtop_param (fun_name, fun_typ);
    Coqtop_param (lemma_name, coq_foralls typed_args_name body) ]

(* Value definition (val_typ can be mk_wild) *)

let mk_define_val (val_name:var) (val_typ:coq) (val_body:coq) =
  [ Coqtop_def ((val_name,val_typ),val_body) ]


(*****************************************************************)
(* Toplevel type definitions *)

(* Type abbreviation [type name = typ_body]
   Note: for polymorphism, you can instantiate [typ_body] as
   a function taking types as arguments using [coq_fun_types] *)

let mk_typedef_abbrev (name:var) (typ_body:coq) : coqtops =
  [ Coqtop_def ((name,Coq_wild), typ_body) ]

(* Auxiliary function, takes as input [name] and [a, b], and returns
   a list [(a:Coq_type),(b:Coq_type)]. *)

let build_algebraic_targs (name:var) (typvars:var list) =
  List.map (fun x -> (x,coq_typ_type)) typvars

(* Record definition [type 'a name = { f1 : t1; f2 : t2 } *)

let mk_typedef_record (name:var) (typvars:var list) (fields:(var*coq) list) : coqtops =
  let targs = build_algebraic_targs name typvars in
  [ Coqtop_record {
   coqind_name = name;
   coqind_constructor_name = ("make_" ^ name);
   coqind_targs = targs;
   coqind_ret = coq_typ_type;
   coqind_branches = fields; } ]

(* Algebraic definition
   [type 'a name = C1 of t11 * t12 | C2 of t21 * t22 * t33]

   TODO: generalize to mutual inductive definitions *)

let mk_typedef_inductive (name:var) (typvars:var list) (cstrs:(var*(coq list)) list) : coqtops =
  let targs = build_algebraic_targs name typvars in
  let ret = coq_apps (coq_var name) (coq_vars typvars) in
  [ Coqtop_ind [ {
   coqind_name = name;
   coqind_constructor_name = "__dummy__";
   coqind_targs = targs;
   coqind_ret = coq_typ_type;
   coqind_branches =
     List.map (fun (cstr,args_typ) -> (cstr, coq_impls args_typ ret)) cstrs; } ] ]
  @ (List.map (fun (cstr,args) ->
        Coqtop_implicit (cstr,
             List.map (fun x -> (x, Coqi_maximal)) typvars
           @ List.mapi (fun i _ -> ("x" ^ string_of_int i, Coqi_explicit) ) args ))
      cstrs)


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
  let defs =
       (Coqtop_require_import ["Prelude"])
    :: (Coqtop_set_implicit_args)
    :: (Coqtop_custom "Require Import ZArith.")
    :: defs in
  let text = Print_coq.tops defs in
  file_put_contents filename text
