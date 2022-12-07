
include Coq

(* Remark: [type var = string] *)

(*****************************************************************)
(** Tools *)

(* Compatibility OCaml: *)
let list_concat_map f l =
  List.concat (List.map f l)

(* Function copied from generator/Mytools.ml *)
let file_put_contents filename text =
   try
      let handle = open_out filename in
      output_string handle text;
      close_out handle
   with Sys_error s ->
     failwith ("Could not write in file: " ^ filename ^ "\n" ^ s)


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

let mk_custom (s:string) : coqtops =
  [ Coqtop_custom s ]

(* Value definition (val_typ can be mk_wild) *)

let mk_define_val (val_name:var) (val_typ:coq) (val_body:coq) : coqtops =
  [ Coqtop_def ((val_name,val_typ),val_body) ]

(* Axiom definition *)

let mk_define_axiom (val_name:var) (val_typ:coq) : coqtops =
  [ Coqtop_param (val_name,val_typ) ]

(* List of axioms *)

let mk_define_axioms (names_and_types : (var*coq) list) : coqtops =
  coqtop_params names_and_types

(* Function definition axiomatized an specified using an equality
   --> see example in demo_sample.ml *)

let mk_define_fun_via_lemma fun_name lemma_name typed_args_name ret_typ body =
  let args_name, args_typ = List.split typed_args_name in
  let fun_typ = coq_impls args_typ ret_typ in
  [ Coqtop_param (fun_name, fun_typ);
    Coqtop_param (lemma_name, coq_foralls typed_args_name body) ]

(* Function definition (non-recursive).
   def is a tuple of (fname : var) (xcs : typed_vars) (cret : coq) (cbody : coq). *)

let mk_define_fun def : coqtops =
  [ coqtop_fundef def ]

(* Function definition (mutually-recursive)
   List items of the form [(fun_name,typed_args,ret_typ,body)]. *)

let mk_define_fix (defs : (var * typed_vars * coq * coq) list) : coqtops =
  [ coqtop_fixdefs defs ]


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
(* Postprocessing of translated AST *)

(* Constructor of meta-variables to be used in templates for
   replacement patterns. *)

let mk_meta (i:int) : coq =
  Coq_metavar (string_of_int i)

type transfo =
  | Transfo_replace of var * int * coq
    (* Transfo_replace(fun_name, arity, template)
       to replace [fun_name x0 .. x_{arity-1}],
       with [template] in which [mk_meta i] is used to refer to the [x_i] arguments *)
  | Transfo_alternative of var * coqtops * transfos
    (* Transfo_alternative(def_name, alt_def, transfos)
       to replace the top-level definition of [def_name] with an alternative definition
       in the main output file, and introduce the transformation listed in [transfos]
       past the point of this definition.
       An equality between the old definition and the new one
       is generated in the file containing proof obligations. For example, it
       generates the statement of a proof obligation
       [Def f_obligation := forall x y, f x y = f2 y x], and
       adds to the module interface [Module Type Obligations] the entry
       [ Parameter f_obligation_proof : f_obligation.] This module type
       can be realized in a separate file, by solving all obligations. *)

and transfos = transfo list

type coqtopss = coqtops list (* = coqtop list list *)

(* Take a template [c] (i.e., a last argument of Transfo_replace), and instantiate its
   meta-variables (built using mk_meta) using the list of coq terms provided. *)

let rec instantiate_template (args : coqs) (c : coq) : coq =
  match c with
  | Coq_metavar x ->
      let i =
        try int_of_string x
        with _ -> failwith "Coq_metavar in template with a variable that is not an integer" in
      if not (0 <= i && i < List.length args)
        then failwith "invalid index in template meta-variable";
      List.nth args i
  | _ -> coq_mapper (instantiate_template args) c


(* Apply a set of transformations over an AST *)
let apply_transfos (module_name : var) (transfos : transfos) (coqtopss : coqtopss) : coqtopss * coqtopss =

  (* Hashtables for transformations *)
  let hash_replace = Hashtbl.create 100 in
  let hash_alternative = Hashtbl.create 100 in
  let add_transfo (transfo : transfo) : unit =
    match transfo with
    | Transfo_replace (f,_,_) -> Hashtbl.add hash_replace f transfo
    | Transfo_alternative (f,_,_) -> Hashtbl.add hash_alternative f transfo
    in
  List.iter add_transfo transfos;

  (* Contents of the proof obligations file *)
  let wrapper_module_counter_ref = ref 0 in
  let wrapper_module_counter () : int =
    incr wrapper_module_counter_ref;
    !wrapper_module_counter_ref in
  let obligations = ref [] in
  let add_obligation basename wrapper_module_name olddefs statement =
    obligations := (basename, wrapper_module_name, olddefs, statement)::!obligations;
    in
  let get_obligations () =
    let obligations = List.rev !obligations in
      [ [ Coqtop_custom ("Require Export " ^ module_name ^ ".") ] ]
    @ (List.map (fun (name,wrapper_module_name,olddefs,stmt) ->
           [ Coqtop_custom ("Module " ^ wrapper_module_name ^ ".") ]
         @ olddefs
         @ [ Coqtop_custom ("End " ^ wrapper_module_name ^ ".") ]
         @ [ Coqtop_def ((name^"_obligation",Coq_prop),stmt)])
       obligations)
    @ [ [ Coqtop_custom "Module Type Obligations." ];
        (List.map (fun (name,_,_,_) ->
          let axiom_name = name ^ "_obligation_proof" in
          let axiom_type = coq_var (name ^ "_obligation") in
          Coqtop_param (axiom_name, axiom_type)) obligations);
        [Coqtop_custom "End Obligations."] ]
    in

  (* Perform replacements recursively in terms *)
  let rec apply_replace (c:coq) : coq =
    match c with
    | Coq_app _ ->
        let cf,cs = coq_apps_inv c in
        let arity = List.length cs in
        let rs = List.map apply_replace cs in
        let fname = match cf with
          | Coq_var fname -> fname
          | _ -> failwith "applied function is not a variable; case to investigate"
          in
          (*DEBUG: Printf.printf "serach %s\n" fname;*)
        begin match Hashtbl.find_opt hash_replace fname with
        | None -> coq_apps cf rs
        | Some (Transfo_replace (f,exp_arity,template)) ->
            if arity <> exp_arity
              then failwith "Not the expected arity for replacement; case to investigate";
            instantiate_template rs template
        | Some _ -> assert false (* only Transfo_replace stored in hash_replace *)
        end
    | _ -> coq_mapper apply_replace c
    in

  (* Process top-level definitions from input AST *)
  let process coqtops =
    match coqtops with
    | [] -> []
    | [old_def] ->
      begin match old_def with
      | Coqtop_def ((name,typ),body) when Hashtbl.mem hash_alternative name ->
          let m = Hashtbl.find hash_alternative name in
          begin match m with
          | Transfo_alternative(fname, alt_def, extra_transfos) ->
              assert (name = fname);

              (* get the structure of the old function *)
              let typed_args, fun_body = coq_funs_inv body in
              if typed_args = []
                then failwith ("no arguments could be extracted from function definition of: " ^ fname);
              let var_args = List.map (fun (arg_name,arg_typ) -> coq_var arg_name) typed_args in

              (* register new transfos associated with the replaced function *)
              List.iter add_transfo extra_transfos;

              (* generate a proof obligation relating the old and new definitions *)
              let wrapper_module_name = "OLD" ^ string_of_int (wrapper_module_counter()) in
              let old_application = coq_apps (coq_var (wrapper_module_name ^ "." ^ fname)) var_args in
              let new_application = apply_replace (coq_apps (coq_var fname) var_args) in
              let equiv_statement = coq_foralls typed_args (coq_app_eq old_application new_application) in
              add_obligation fname wrapper_module_name [old_def] equiv_statement;

              (* provide the alternative definition for the result file *)
              alt_def
          | _ -> assert false (* only Transfo_alternative should be stored in hash_alternative *)
          end
       | coqtop -> (* other definition than a coqdef *)
          [coq_mapper_in_coqtop apply_replace coqtop]
       end
    | _ -> (* TODO "handle mutually recursive definitions" *)
            coqtops
    in

  (* Output *)
  let coqtopss_result = List.map process coqtopss in
  let coqtopss_obligations = get_obligations() in
  coqtopss_result, coqtopss_obligations



(*****************************************************************)
(* Generation of output *)

let headers =
    [ Coqtop_require_import ["Prelude"];
      Coqtop_set_implicit_args;
      Coqtop_custom "Require Import ZArith."]

let ast_with_header_to_file (filename : string) (coqtopss : coqtopss) : unit =
  let coqtops = List.concat (headers :: coqtopss) in
  let text = Print_coq.tops coqtops in
  file_put_contents filename text

let out_prog (basename : string) (transfos : transfos) (coqtopss : coqtopss) : unit =
  (*let basename = Filename chop_suffix filename ".v" in*)
  ast_with_header_to_file (basename ^ "_pretransfo.v") coqtopss;
  let module_name = String.capitalize_ascii basename in
  let coqtopss_result, coqtopss_obligations = apply_transfos module_name transfos coqtopss in
  ast_with_header_to_file (basename ^ ".v") coqtopss_result;
  ast_with_header_to_file (basename ^ "_obligations.v") coqtopss_obligations


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
