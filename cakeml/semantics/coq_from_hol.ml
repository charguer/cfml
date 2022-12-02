
include Coq

(* Remark: [type var = string] *)

(* Compatibility OCaml: *)
let list_concat_map f l =
  List.concat (List.map f l)

(*****************************************************************)
(** Complement to coq.ml *)

(* Placeholder for missing Coq subterms: [COQ_HOLE] admits any type. *)

let coq_todo (msg:string) =
  coq_app_var "Prelude.COQ_HOLE" (coq_string msg)

(* Alias [coq_tvar] to record references to type variables, as opposed to program variables *)

let coq_tvar (x:string) =
  coq_var x

(* [coq_cstr x cs1 cs2] applies the potentially-polymorphic data constructor [x]
   to the type arguments [cs1] and to the arguments [cs2]. Thoses lists may be empty. *)

let coq_cstr x cs1 cs2 =
  coq_apps (coq_var_at x) (cs1 @ cs2)



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

(* Record definition [type 'a name = { f1 : t1; f2 : t2 }]
   Note: Coq does not have support for mutual recursion between records, or between
   records and type abbreviation and inductive. Encodings into mutual-inductive
   are needed in such cases, let's postpone if we can. *)

let mk_typedef_record (name:var) (typvars:var list) (fields:(var*coq) list) : coqtops =
  let targs = coq_types typvars in
  [ Coqtop_record {
   coqind_name = name;
   coqind_constructor_name = ("make_" ^ name);
   coqind_targs = targs;
   coqind_ret = coq_typ_type;
   coqind_branches = fields; } ]

(* Auxiliary function to build a [coqind] record (defined in coq.ml), which corresponds
   to one among several mutually-inductive definitions part of a [Coqtop_ind],
   for the case of a type definition.
   Here we process one algebraic definition, e.g.
   [type 'a name = C1 of t11 * t12 | C2 of t21 * t22 * t33]
   Note that this is a particular case of the constructor [mk_coind_pred]. *)

let mk_coqind_type (name:var) (typvars:var list) (cstrs:(var*(coq list)) list) : coqind =
  let targs = coq_types typvars in
  let ret = coq_apps (coq_var name) (coq_vars typvars) in
  { coqind_name = name;
    coqind_constructor_name = "__dummy__"; (* only useful for records; TODO: make this an option? *)
    coqind_targs = targs;
    coqind_ret = coq_typ_type;
    coqind_branches =
      List.map (fun (cstr,args_typ) -> (cstr, coq_impls args_typ ret)) cstrs; }

(* Auxiliary function for building commants such as [Arguments C1 {A1} {A2}] for
   maximally-inserted arguments. *)
let mk_arguments_for_constructors cstr typvars : coqtop =
  let args_mode = List.map (fun x -> (x, Coqi_maximal)) typvars in
  (* DEPRECATED @ List.mapi (fun i _ -> ("x" ^ string_of_int i, Coqi_explicit) ) args *)
  Coqtop_implicit (cstr, args_mode)

(* Function to build a mutual inductive definition;
   one should use [mk_coind_type] for building arguments. *)

let mk_mutual_inductive_type (defs:coqind list) : coqtops =
  let mk_arguments def =
    let cstrs = List.map fst def.coqind_branches in
    let typvars = List.map fst def.coqind_targs in
    List.map (fun cstr -> mk_arguments_for_constructors cstr typvars) cstrs
    in
  (Coqtop_ind defs) :: (list_concat_map mk_arguments defs)

(* Auxiliary function to build a [coqind], for a predicate definition.
   [Inductive foo (A:Type) : list A -> Prop :=
      | F1 : foo nil
      | F2 : forall x l, foo l -> foo (x::l)]
   In this example,
   - [name] is [foo],
   - [params] is the singleton list [(A,Type)]
   - [ret_type] is [list A -> Prop]
   - [cstrs] is a list whose second item is the pair [("F1",c)],
     where [c] denotes the encoding of the coq_statement [forall x l, foo l -> foo (x::l)]. *)

let mk_coqind_pred (name:var) (params:(var*coq) list) (ret_type:coq) (cstrs:(var*coq) list) : coqind =
  { coqind_name = name;
    coqind_constructor_name = "__dummy__"; (* only useful for records *)
    coqind_targs = params;
    coqind_ret = ret_type;
    coqind_branches = cstrs; }

(* Function to build a mutual inductive predicates;
   one should use [mk_coind_pred] for building arguments. *)

let mk_mutual_inductive_pred (defs:coqind list) : coqtops =
  [ Coqtop_ind defs ]



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




(*****************************************************************)
(* Encoding for programming language constructs *)

(* TODO : DEPRECATED *)

(* Simplified pattern matching
     match scrunity with
     | C1 x1 x2 => body1
     | C2 x1 x2 x3 => body2
     end

let mk_match_simple (scrunity:coq) (branches:(var*(var list)*coq) list) =
  let mk_branch (cstr_name, pat_vars, body) =
    let pattern = coq_apps (coq_var cstr_name) (coq_vars pat_vars) in
    (pattern,body) in
  coq_match scrunity (List.map mk_branch branches)
  *)
