open Mytools
open Asttypes
open Typedtree
open Printf

(* LATER: add a mli file *)

(**


NAMING SCHEME OVERVIEW:

- trailing underscores are forbidden in variable, constructor and type names;
- any variable name that ends with a quote, or results in a clash with
  a Coq keyword, or is a freshly generated name, gets suffixed with "__".
- all type names (except builtin ones) are suffixed with a underscore character;
- all field names are suffixed with a quote character;
- module names are suffixed with "_ml";
- infix function names are encoded, e.g. (++) becomes "infix_plus_plus__".



TRANSLATION

- var             x        x
- infix fun       (++)     infix_plus_plus__
- fresh var                x3__
- fresh fun                f3__
- fresh pat                p3__
- clashing var    exists   exists__
- clashing var    array    array__
- var quote       x'       x'__       // Same rule as clashing var
- var rejected    x_                  // Cannot end with underscore

- constructor     C        C
- constructor     C'       C'         // Same rule as above (not special).
- rejected cstr   C_                  // Cannot end with underscore

- builtin type    t        t
- type            t        t_         // Cannot end with underscore
- type quote      t'       t'_        // Same rule as above (not special).
- type rejected   t_
- type var        'a       A_

- field name      f        f'         // Short field names are convenient
- field quote     f'       f''        // Same rule as above (not special).
- field under     f_       f_'        // Same rule as above (not special).

- module          M        M_ml


INTERPRETATION

  M_ml             module name (in Coq module scope)
  X                constructor
  X_               type variable
  t_               builtin type
  f'               field name

  x__              escaped name for variable x, where x is a keyword
  x1__             name for a fresh variable
  infix..__        name for infix symbol

  x'__             escaped name for variable x' (general rule for escaped name)
  t'_              name for type t' (general rule for types)
  f''              name for field name f' (general rule for fields)

  EncDef_t_         section name for encoder definitions
  enc_impl_t_       name for an encoder definition
  injective_enc_impl_t_   name for the injectivity lemma for the encoder
  Enc_t_            name for an encoder instance


*)


(*#########################################################################*)
(* ** Reserved keywords  *)

let coq_keywords =
  [ "as"; "at"; "cofix"; "else"; "end"; "exists"; "exists2"; "fix";
    "for"; "forall"; "fun"; "if"; "IF"; "in"; "let"; "match";
    "mod"; "return"; "Set"; "then"; "Type"; "using"; "where"; "with" ]

let builtin_type_constructors =
  [ "int"; "char"; "unit"; "bool"; "float"; "list"; "string"; "array"; "option" ]

let used_as_notation =
  [ "mod"; "abs" ]

let infix_named_functions =
  [ "mod"; "land"; "lor"; "lxor"; "lnot"; "lsl"; "lsr"; "asr" ]

let non_rebindable_names =
    [ "/"; "&&"; "||"; "="; "<>"; "<="; ">="; "<"; ">" ]
  @ infix_named_functions
  @ [ "ignore"; "abs"; "not"; "fst"; "snd"; "pred"; "succ"; "min"; "max";]
  (* Remark: items from the second list, we could allow rebinding them,
     at the expense of systematically introducing a let-binding when we
     see them; else, we need the normalization to apply to a typed tree. *)

let reserved_variable_names =
  builtin_type_constructors @ coq_keywords @ used_as_notation



(*#########################################################################*)
(* ** Checking of variables names *)

let has_trailing_underscore x =
   let n = String.length x in
   (n > 0 && x.[n-1] = '_')

let has_trailing_double_underscore x =
   let n = String.length x in
   (n > 0 && x.[n-1] = '_' && x.[n-2] = '_')

let has_trailing_quote x =
   let n = String.length x in
   (n > 0 && x.[n-1] = '\'')

let check_not_ending_underscore str loc x =
   if has_trailing_underscore x
      then unsupported loc (str ^ " should not end with an underscore: " ^ x)

let check_var_name loc x =
   check_not_ending_underscore "variable" loc x;
   if   (not !Clflags.nopervasives)
     && (List.mem x non_rebindable_names)
      then unsupported loc ("CFML requires -nopervasives to allow binding of operator: " ^ x)

let check_constr_name loc x =
   check_not_ending_underscore "constructor" loc x

let check_type_constr_name loc x =
   check_not_ending_underscore "type" loc x




(*#########################################################################*)
(* ** Renaming of infix function names, and special names *)
(* TODO: rename "infix" into something more general *)

(** [infix_name_encode name] encodes an infix function name,
    e.g. for "+^+" it produces "infix_plus_hat_plus_",
    and for "mod" it produces "infix_mod__" *)

let infix_name_symbols =
  ['!', "emark";
   '$', "dollar";
   '%', "percent";
   '&', "amp";
   '*', "star";
   '+', "plus";
   '-', "minus";
   '.', "dot";
   '/', "slash";
   ':', "colon";
   '<', "lt";
   '=', "eq";
   '>', "gt";
   '?', "qmark";
   '@', "at";
   '^', "hat";
   '|', "bar";
   '~', "tilde" ]

let infix_name_encode name =
  if name = "mod" then name ^ "__"
  else if List.mem name infix_named_functions then name else begin (* old: "infix_" ^ name ^ "__" *)
     let gen = Buffer.create 20 in
     String.iter (fun c ->
        let s =
          try List.assoc c infix_name_symbols
          with Not_found -> failwith ("infix_name_encode: cannot encode name: " ^ name)
          in
         Buffer.add_string gen s;
         Buffer.add_string gen "_";
       ) name;
     "infix_" ^ (Buffer.contents gen) ^ "_"
  end

  (*DEPRECATED
  let gen = String.map (fun c ->
     try List.assoc c infix_name_symbols
     with Not_found -> failwith ("infix_name_encode: cannot encode name: " ^ name))
    name in *)

(** Convention for renaming infix function names *)

let is_infix_name name =
  name = "mod" ||
  (      String.length name > 0
      && List.mem_assoc name.[0] infix_name_symbols)


(*#########################################################################*)
(* Protect names, including infix *)

(** Convention for naming variable names *)

let var_name name =
   if is_infix_name name
      then infix_name_encode name
   else if (List.mem name reserved_variable_names)
      then name ^ "__"
   else if (has_trailing_double_underscore name)
      then name (* generated name from normalization phase *)
   else if (has_trailing_quote name)
      then name ^ "__"
   else
      name

(** Same extended to paths;
    TODO: this breaks identities of variables, maybe not an issue? *)

let rec var_path p =
  Path.(
     match p with
     | Pident id -> Pident (Ident.create (var_name (Ident.name id)))
     | Pdot(p, s, pos) -> Pdot(p, var_name s, pos)
     | Papply(p1, p2) -> Papply(p1, var_path p2)  (* TODO: is this correct? *)
   )


(*#########################################################################*)
(* ** Fresh name generation *)

(** Remark: we use a double underscore as suffix, to avoid clashes
    with type constructors, which we make end with a single slash. *)

(** Fresh pattern variable name *)

let pattern_generated_name i =
   "p" ^ string_of_int i ^ "__"

(** Fresh function variable name *)

let function_generated_name i =
   "f" ^ string_of_int i ^ "__"

(** Fresh variable name *)

let variable_generated_name i =
   "x" ^ string_of_int i ^ "__"


(*#########################################################################*)
(* ** Type lifting *)

(** Convention for naming type variables;
    Here, the argument [name] is that provided by the OCaml type-checker. *)

let type_variable_name name =
   (String.uppercase_ascii name) ^ "_"

(** Convention for naming type constructors *)

let type_constr_builtin_name name =
   if name = "float" then unsupported_noloc "float not yet supported";
   try List.assoc name
      [ ("int", "Coq.ZArith.BinInt.Z");
        ("unit", "Coq.Init.Datatypes.unit");
        ("bool", "Coq.Init.Datatypes.bool");
        ("option", "Coq.Init.Datatypes.option");
        ("list", "Coq.Init.Datatypes.list");
        ("string", "Coq.Strings.String.string");
        ("array", "CFML.WPBuiltin.array");
      ]
   with Not_found -> failwith ("type_constr_builtin_name: missing name for " ^ name)

let type_constr_name name =
  if List.mem name builtin_type_constructors
    then type_constr_builtin_name name
    else name ^ "_"

(** Note: see function [lift_btyp] in characteristic.ml
    for the mapping of array types, tuple types and arrow types. *)


(*#########################################################################*)
(* ** List of primitive data constructors *)

(** Data constructors from the following lists are mapped to particular
    inductive data constructors in Coq. Indicating the arity as well. *)

let builtin_constructors_table =
  [ "[]", ("Coq.Lists.List.nil", 1);
    "::", ("Coq.Lists.List.cons", 1);
    "()", ("Coq.Init.Datatypes.tt", 0);
    "true", ("Coq.Init.Datatypes.true", 0);
    "false", ("Coq.Init.Datatypes.false", 0);
    "None", ("Coq.Init.Datatypes.None", 0);
    "Some", ("Coq.Init.Datatypes.Some", 1);
    ]
    (* --todo: add [Pervasives] as prefix *)


(** [find_builtin_constructor p] finds the primitive data-constructor associated
    with the argument [p], and return an optional result.
    For example, given "::" it gives "Coq.Lists.List.cons" and 1,
    where 1 is the number of type arguments to cons in Coq. *)

let find_builtin_constructor p =
   list_assoc_option p builtin_constructors_table

(** [get_builtin_constructor p] finds the primitive data-constructor associated
    with the argument [p], and return the Coq name associated with it. *)

let get_builtin_constructor p =
   match find_builtin_constructor p with
   | Some (coq_name, arity) -> coq_name
   | _ -> failwith ("get_builtin_constructor could not find: " ^ p)


(*#########################################################################*)
(* ** Helper functions for functions *)


let simplify_apply_args loc oargs =
  List.map (function (lab, Some e, Typedtree.Required) -> e | _ -> unsupported loc "optional arguments") oargs


(*#########################################################################*)
(* ** List of inlined primitive functions *)

(** Fully-applied "inlined primitive" are translated directly as a
    Coq application, and does not involve the "AppReturns" predicate. *)


(* for the mli file:
   (** [primitive_special] is NOT CURRENTLY USED
       (optimized lifting of Zdiv and Zmod operations) *)
   val primitive_special : int
*)


type primitive_arity =
  | Primitive_unary
  | Primitive_binary
  | Primitive_binary_lazy
  | Primitive_binary_div_or_mod
  | Primitive_binary_only_numbers

let cfml_prim x =
  sprintf "(CFML.Semantics.val_prim CFML.Semantics.%s)" x

let cfml_prim_derived (x:string) =
  sprintf "CFML.Semantics.%s" x

  (*   sprintf "(CFML.Semantics.val_prim_derived %s CFML.Semantics.%s)" x x *)
let inlined_primitives_table =
  [
   "Pervasives.ignore", (Primitive_unary, ("(@CFML.WPBuiltin.ignore _)", cfml_prim_derived "val_ignore"));
   "Pervasives.+", (Primitive_binary, ("Coq.ZArith.BinInt.Z.add", cfml_prim "val_add"));
   "Pervasives.-", (Primitive_binary, ("Coq.ZArith.BinInt.Z.sub", cfml_prim "val_sub"));
   "Pervasives.*", (Primitive_binary, ("Coq.ZArith.BinInt.Z.mul", cfml_prim "val_mul"));
   "Pervasives.~-", (Primitive_unary, ("Coq.ZArith.BinInt.Z.opp", cfml_prim "val_opp"));
   "Pervasives.abs", (Primitive_unary, ("Coq.ZArith.BinInt.Z.abs", cfml_prim_derived "val_abs"));
   "Pervasives.not", (Primitive_unary, ("TLC.LibBool.neg", cfml_prim "val_neg"));
   "Pervasives.fst", (Primitive_unary, ("(@Coq.Init.Datatypes.fst _ _)", cfml_prim_derived "TODO"));
   "Pervasives.snd", (Primitive_unary, ("(@Coq.Init.Datatypes.snd _ _)", cfml_prim_derived "TODO"));
   "Pervasives.pred", (Primitive_unary, ("(fun x__ => Coq.ZArith.BinInt.Zminus x__ (1)%Z)", cfml_prim_derived "TODO"));
   "Pervasives.succ", (Primitive_unary, ("(fun x__ => Coq.ZArith.BinInt.Zplus x__ (1)%Z)", cfml_prim_derived "TODO"));
   (* DEPRECATED
   "Pervasives.pred", (Primitive_unary, "CFML.WPBuiltin.pred");
   "Pervasives.succ", (Primitive_unary, "CFML.WPBuiltin.succ");
   *)
   "Pervasives./", (Primitive_binary_div_or_mod, ("Coq.ZArith.BinInt.Z.quot", cfml_prim "val_div"));
   "Pervasives.mod", (Primitive_binary_div_or_mod, ("Coq.ZArith.BinInt.Z.rem", cfml_prim "val_mod"));
   "Pervasives.&&", (Primitive_binary_lazy, ("TLC.LibBool.and", cfml_prim_derived "val_and"));
   "Pervasives.||", (Primitive_binary_lazy, ("TLC.LibBool.or", cfml_prim_derived "val_or"));
   "Pervasives.=", (Primitive_binary_only_numbers, ("(fun x__ y__ : Coq.ZArith.BinInt.Z => TLC.LibReflect.isTrue (Coq.Init.Logic.eq x__ y__))", cfml_prim "val_eq"));
   "Pervasives.<>", (Primitive_binary_only_numbers, ("(fun x__ y__ : Coq.ZArith.BinInt.Z => TLC.LibReflect.isTrue (Coq.Init.Logic.not (Coq.Init.Logic.eq x__ y__)))", cfml_prim "val_neq"));
   "Pervasives.<", (Primitive_binary_only_numbers, ("(fun x__ y__ : Coq.ZArith.BinInt.Z => TLC.LibReflect.isTrue (@TLC.LibOrder.lt _ (@TLC.LibOrder.lt_of_le Coq.ZArith.BinInt.Z TLC.LibInt.le_int_inst) x__ y__))", cfml_prim "val_lt"));
   "Pervasives.<=", (Primitive_binary_only_numbers, ("(fun x__ y__ : Coq.ZArith.BinInt.Z => TLC.LibReflect.isTrue (@TLC.LibOrder.le _ TLC.LibInt.le_int_inst x__ y__))", cfml_prim "val_le"));
   "Pervasives.>", (Primitive_binary_only_numbers, ("(fun x__ y__ : Coq.ZArith.BinInt.Z => TLC.LibReflect.isTrue (@TLC.LibOrder.gt _ (@TLC.LibOrder.gt_of_le _ TLC.LibInt.le_int_inst) x__ y__))", cfml_prim "val_gt"));
     "Pervasives.>=", (Primitive_binary_only_numbers, ("(fun x__ y__ : Coq.ZArith.BinInt.Z => TLC.LibReflect.isTrue (@TLC.LibOrder.ge _ (@TLC.LibOrder.ge_of_le _ TLC.LibInt.le_int_inst) x__ y__))", cfml_prim "val_ge"));
   "Pervasives.max", (Primitive_binary_only_numbers, ("Coq.ZArith.BinInt.Z.max", cfml_prim_derived "val_max"));
   "Pervasives.min", (Primitive_binary_only_numbers, ("Coq.ZArith.BinInt.Z.min", cfml_prim_derived "val_min"));
   "List.length", (Primitive_unary, ("(@TLC.LibListZ.length _)", cfml_prim_derived "TODO"));
   "List.rev", (Primitive_unary, ("(@TLC.LibList.rev _)", cfml_prim_derived "TODO"));
   "List.concat", (Primitive_unary, ("(@TLC.LibList.concat _)", cfml_prim_derived "TODO"));
   "List.append", (Primitive_binary, ("(@TLC.LibList.app _)", cfml_prim_derived "TODO"));
   "Pervasives.@", (Primitive_binary, ("(@TLC.LibList.app _)", cfml_prim_derived "TODO"));
   ]


(* DEPRECATED
      "List.rev", (1, "LibList.rev");
      "List.length", (1, "LibList.length");
      "List.append", (2, "LibList.append");
      "OkaStream.++", (2, "LibList.append");
      "OkaStream.reverse", (1, "LibList.rev");
      "StrongPointers.cast", (1, "")
      "Lazy.force", (1, "");
      "Okasaki.!$", (1, ""); (* i.e., @LibLogic.id _*)
*)


(** Find the inlined primitive associated with [p];
    returns eithe [None], or [Some (n,y)] where [n]
    is a descriptor of type [primitive_arity] and
    [y] is the name of the corresponding Coq value.

    For example, for [Pervasives.+] we would get
    [Some (Primitive_binary, "Coq.ZArith.BinInt.Zplus"]. *)

let find_inlined_primitive p =
   (* Printf.printf "find_inlined_primitive: %s %d\n" p arity; *)
   list_assoc_option p inlined_primitives_table



(*#########################################################################*)
(* ** Helper functions for primitive functions *)

let get_qualified_pervasives_name f =
   let name = Path.name f in
   if !Clflags.nopervasives
      then "Pervasives." ^ name  (* unqualified name when from inside Pervasives *)
      else name  (* qualified name otherwise *)


let exp_find_inlined_primitive e oargs =
   let loc = e.exp_loc in
   let args = simplify_apply_args loc oargs in
   match e.exp_desc with
   | Texp_ident (f,d) ->
      let name = get_qualified_pervasives_name f in

      let _debug() =
         Printf.printf "exp_find_inlined_primitive: %s\n arity: %d\n name: %s\n" (Path.name f) (List.length args) name
         in
      (* _debug(); *)

      begin match args with

      | [n; {exp_desc = Texp_constant (Const_int m)}]
           when m <> 0
             && List.mem name ["Pervasives.mod"; "Pervasives./"] ->
           begin match find_inlined_primitive name with
           | Some (Primitive_binary_div_or_mod, names) -> Some names
           | _ -> None
           end

       | [e1; e2]
           when List.mem name ["Pervasives.&&"; "Pervasives.||"] ->
           begin match find_inlined_primitive (Path.name f) with
           | Some (Primitive_binary_lazy, names) -> Some names
           | _ -> None
           end

       | [e1; e2]
           when List.mem name ["Pervasives.="; "Pervasives.<>"; "Pervasives.<=";
                               "Pervasives.>="; "Pervasives.<"; "Pervasives.>";
                               "Pervasives.min"; "Pervasives.max"; ] ->
           let is_number =
              try Ctype.unify e1.exp_env e1.exp_type ((*instance*) Predef.type_int); true
              with _ -> false
              (*begin match btyp_of_typ_exp e1.exp_type with
              | Btyp_constr (id,[]) when Path.name id = "int" -> true
              | _ -> false
              end *)
              in
             (* Remark: by typing, [e2] has the same type as [e1] *)
           if not is_number then begin
             if List.mem name [ "Pervasives.="; "Pervasives.<>"; ]
               then None
               (* TODO: improve using type unification *)
               else (* warning loc *)
               unsupported loc (Printf.sprintf "comparison operators on non integer arguments") (* (here, %s) (string_of_type_exp e1.exp_type)) *)
           end else begin match find_inlined_primitive name with
              | Some (Primitive_binary_only_numbers, names) -> Some names
              | _ -> failwith ("in exp_find_inlined_primitive, could not find the coq translation of the function: " ^ name)
           end

       | _ ->
           let arity = List.length args in
           begin match find_inlined_primitive name with
           | Some (Primitive_unary, names) when arity = 1 -> Some names
           | Some (Primitive_binary, names) when arity = 2 -> Some names
           | _ -> None
           end
           (* debug: Printf.printf "exp_find_inlined_primitive: %s %d\n"  (Path.name f)  (List.length args);
           if r = None then Printf.printf "failed\n"; *)

       end

    | _ -> None

let is_inlined_function e =
   match e.exp_desc with
   | Texp_apply (funct, oargs) when (exp_find_inlined_primitive funct oargs <> None) -> true
   | _ -> false




(*#########################################################################*)
(* ** List of all primitive functions *)

(** Primitive functions from the following list are mapped to special
    Coq constants whose specification is axiomatized. *)

let all_primitives_table =
  [
  (* DEPRECATED
   "Pervasives.=", "ml_eqb";
    "Pervasives.<>", "ml_neq";
    "Pervasives.==", "ml_phy_eq";
    "Pervasives.!=", "ml_phy_neq";
    "Pervasives.+", "ml_plus";
    "Pervasives.-", "ml_minus";
    "Pervasives.~-", "ml_opp";
    "Pervasives.*", "ml_mul";
    "Pervasives./", "ml_div";
    "Pervasives.mod", "ml_mod";
    "Pervasives.<=", "ml_leq";
    "Pervasives.<", "ml_lt";
    "Pervasives.>", "ml_gt";
    "Pervasives.>=", "ml_geq";
    "Pervasives.&&", "ml_and";
    "Pervasives.||", "ml_or";
    "Pervasives.@", "ml_append";
    "Pervasives.raise", "ml_raise";
    "Pervasives.asr", "ml_asr";
    "Pervasives.ref", "ml_ref";
    "Pervasives.!", "ml_get";
    "Pervasives.:=", "ml_set";
    "Pervasives.incr", "ml_incr";
    "Pervasives.decr", "ml_decr";
    "Pervasives.fst", "ml_fst";
    "Pervasives.snd", "ml_snd";
    "Pervasives.max_int", "ml_max_int";
    "Pervasives.min_int", "ml_min_int";
    "Pervasives.read_int", "ml_read_int";
    "Pervasives.print_int", "ml_print_int";
    "Array.make", "ml_array_make";
    "Array.get", "ml_array_get";
    "Array.set", "ml_array_set";
    "Array.init", "ml_array_init";
    "Array.length", "ml_array_length";
    "Random.int", "ml_rand_int";
    "List.nth", "ml_list_nth";
    "List.hd", "ml_list_hd";
    "List.tl", "ml_list_tl";
    "List.iter", "ml_list_iter";
    "List.fold_left", "ml_list_fold_left";
    "List.fold_right", "ml_list_fold_right";
    "List.rev", "ml_rev";
    "List.append", "ml_append";
    "Stack.create", "ml_stack_create";
    "Stack.is_empty", "ml_stack_is_empty";
    "Stack.push", "ml_stack_push";
    "Stack.pop", "ml_stack_pop";
    "OkaStream.append", "ml_append";
    "OkaStream.take", "ml_take";
    "OkaStream.drop", "ml_drop";
    "NullPointers.null", "null";
    "NullPointers.is_null", "ml_is_null";
    "NullPointers.free", "ml_free";
    "StrongPointers.sref", "ml_ref";
    "StrongPointers.sget", "ml_get";
    "StrongPointers.sset", "ml_sset";
    *)
   ]
    (* ---todo: add not, fst, snd *)



(* for the mli file:

   (** [find_primitive] finds the primitive functions associated with the
       argument, and return an optional result.
       For example, given "Pervasives.ref" it gives "ml_ref" *)

   val find_primitive : string -> string option

*)


(** Find the primitive associated with [p]. This partial function
    returns an option. *)

let find_primitive p =
   list_assoc_option p all_primitives_table




(*#########################################################################*)
(* ** Identifier renaming conventions *)

(** Convention for characteristic formulae *)

let cf_axiom_name name =
  name ^ "_cf__"

let cf_statement_name name =
  name ^ "_cf_def__"

(** Convention for naming module names *)

let module_name name =
   name ^ "_ml"
   (* Remark: because we add a suffix, we cannot have clash with
      the module names to protect, namely: "CFML", "TLC", "Coq". *)

(** Convention for naming record types,
    i.e. the one that is bound to "loc" *)

let record_type_name name =
  type_constr_name name (* TODO: inline *)

(** Convention for naming the axiom for polymorphic equality
    on constructors *)

let polymorphic_eq_arg_name name =
  "polymorphic_eq_arg_" ^ name ^ "__"

(** Convention for naming the coq record structure
    used to describe a record in the heap *)

let record_structure_name name =
  type_constr_name name (* DEPRECATED ^ "__struct" *)

let algebraic_constructor_name name =
  name ^ "_make__"   (* todo: clash *)

(** Convention for naming record constructors,
    in the coq record structure *)

let record_constructor_name name =
  name ^ "_make__"

let record_constructor_name_from_type type_name =
  record_constructor_name type_name

(** Convention for naming record field *)

(* FIXME unused
let record_field_name name =
  name
  (* ^ "__" *) (* TODO: modify? *)
 *)

(** Convention for naming record accessor function *)

let record_field_name name =
   let n = String.length name in
   if n > 0 && name.[n-1] = '\''
      then unsupported_noloc ("field name should not end with a quote (not yet supported): " ^ name);
  name ^ "'"
  (* TODO: avoid names ending with a quote in caml code *)

let record_field_get_name name = (* DEPRECATED *)
  name ^ "__get"

let record_field_set_name name = (* DEPRECATED *)
  name ^ "__set"

(** Convention for naming record accessor function specifications *) (* DEPRECATED *)

let record_get_spec_name name =
  name ^ "__get_spec"

let record_set_spec_name name =
  name ^ "__set_spec"


(* TODO: use above, and also focus/unfocus etc *) (* DEPRECATED *)

(** Convention for naming the representation predicate for a record *)

let record_repr_name name =
  str_capitalize_1 name ^ "_"
  (* this should not clash with types because types being with a lowercase *)

let record_convert_name name =
  record_repr_name name ^ "_convert"

let record_focus_name name =
  record_repr_name name ^ "_focus"

let record_unfocus_name name =
  record_repr_name name ^ "_unfocus"

let record_convert_field_name name =
  record_field_name name ^ "__convert"

let record_focus_field_name name =
  record_field_name name ^ "__focus"

let record_unfocus_field_name name =
  record_field_name name ^ "__unfocus"


(* Naming for encoders *)

let encoder_section name =
  "EncDef_" ^ (type_constr_name name)

let encoder_impl name =
  "enc_impl_" ^ (type_constr_name name)

let encoder_injective name =
  "injective_enc_impl_" ^ (type_constr_name name)

let encoder_instance name =
  "Enc_" ^ (type_constr_name name)



(*#########################################################################*)


(* Auxiliary functions (excerpt)
  for renaming.mli, used by characteristic.ml and trm_to_coq.ml

val pattern_ident : Typedtree.pattern -> Ident.t
val pattern_name : Typedtree.pattern -> string
val pattern_name_protect_infix : Typedtree.pattern -> string
val lift_path : Path.t -> Path.t
val lift_path_name : Path.t -> string

*)





(*#########################################################################*)
(* ** Helper functions for names *)


(** Takes a pattern that is expected to be reduced simply to an identifier,
    and returns this identifier *)

let rec pattern_ident p =
   match p.pat_desc with
   | Tpat_var s -> s
   | Tpat_alias (p1,_) -> pattern_ident p1
   | _ -> unsupported p.pat_loc ("pattern_ident: the pattern is not a name")
   (* (Print_tast.string_of_pattern false p) *)

(** Takes a pattern that is expected to be reduced simply to an identifier,
    and returns the name of this identifier *)

let pattern_name p =
   Ident.name (pattern_ident p)

(** Takes a function name and encodes its name in case of an infix operator *)

let pattern_name_protect_infix p =
   var_name (pattern_name p)


(*#########################################################################*)
(* ** List of external modules that need to be required *)

let external_modules = ref []

let external_modules_add name =
   if not (List.mem name !external_modules)
     then external_modules := name::!external_modules
   (* TODO: use a structure more efficient than lists *)

let external_modules () =
  !external_modules

(* FIXME unused
let external_modules_reset () =
   external_modules := []
 *)

(* If [-nostdlib] is set, the list of external modules is left unchanged.
   Otherwise, the modules that appear to be part of the standard library
   are removed from this list; they do not need to be explicitly listed,
   because we emit [Require CFML.Stdlib.Stdlib]. *)

let is_stdlib_module = function
| "Array_ml"
| "List_ml"
| "Pervasives_ml"
| "Sys_ml"
    -> true
| _ -> false

let is_not_stdlib_module m =
  not (is_stdlib_module m)

let filter no_mystd_include modules =
  if no_mystd_include then
    modules
  else
    List.filter is_not_stdlib_module modules


(*#########################################################################*)
(* ** Lifting of paths *)

open Path

(* Take a module name and add "_ml" suffix to it;
   Moreover, insert a "Require" directive in case the module
   corresponds to a file (i.e. a compilation unit. *)

let lift_module_name id =
   let name = Ident.name id in
   let coqname = module_name name in
   if Ident.persistent id then external_modules_add coqname;
   coqname

   (* -- old:
     if Ident.persistent id
      then (let result = name ^ "_ml" in external_modules_add result; result)
      else "ML" ^ name
   *)
   (* -- old: if name = "OkaStream" then "CFPrim" else  *)

(* Function for adding "_ml" to the modules in a path,
   including the last constant which is assumed to a module name.
   For example, "Foo.Bar" becomes "Foo_ml.Bar_ml".

   TODO: rename this function *)


let rec lift_full_path = function
  | Pident id -> Pident (Ident.create (lift_module_name id))
  | Pdot(p, s, pos) -> Pdot(lift_full_path p, (module_name s), pos)
  | Papply(p1, p2) -> assert false

(* Function for adding "_ml" to the modules in a path,
   but not changing the last constant in the path.
   For example, "Foo.x" becomes "Foo_ml.x". *)

let lift_path = function
  | Pident id -> Pident id
  | Pdot(p, s, pos) -> Pdot(lift_full_path p, s, pos)
  | Papply(p1, p2) -> assert false

(** Translates a path into a string. A module called "Test"
    becomes "Test_ml". *)

let lift_full_path_name p =
  Path.name (lift_full_path p)

(** Translates a path into a string --todo: why not full? *)

let lift_path_name p =
  Path.name (lift_path p)



(*#########################################################################*)
(* ** Helper functions for records *)

open Asttypes
open Types


(* TODO: rewrite this function by using a normalization function that returns p *)
let rec prefix_for_label typ =
  match typ.desc with
  | Tconstr (p, _, _) -> lift_path_name p
  | Tlink t -> prefix_for_label t
  | _ -> failwith "string_of_label: type of a record should be a Tconstr or Tlink"
  (*
  | Tvar -> failwith "x1"
  | Tarrow _ -> failwith "x2"
  | Ttuple  _ -> failwith "x3"
  | Tconstr _ -> failwith "x4"
  | Tobject  _ -> failwith "x5"
  | Tfield _ -> failwith "x6"
  | Tnil _ -> failwith "x7"
  | Tsubst  _ -> failwith "x9"
  | Tvariant  _ -> failwith "x10"
  | Tunivar -> failwith "x11"
  | Tpoly  _ -> failwith "x12"
  *)

(* DEPRECATED
let string_of_label_with prefix lbl =
  prefix ^ "_" ^ lbl.lbl_name

let string_of_label typ lbl =
  string_of_label_with (prefix_for_label typ) lbl
*)


(** A variant of the function [Typecore.extract_label_names], for obtaining
    the names of the fields associated with a record type. Returns a list of
    field names, and a boolean indication on whether all fields are immutable *)

let record_field_names_and_immutability_of_type env ty =
  let ty = Ctype.repr ty in
  match ty.desc with
  | Tconstr (path, _, _) ->
      let td = Env.find_type path env in
      begin match td.type_kind with
      | Type_record (fmts, _) ->
            (List.map (fun (f,m,t) -> f) fmts,
             List.for_all (fun (f,m,t) -> m = Immutable) fmts)
      | Type_abstract when td.type_manifest <> None ->
          unsupported_noloc "building of a record with abstract type"
      | _ -> assert false
      end
  | _ -> assert false

(** Find all label associated with a record operation (get, set, new-record, record-with) *)

let record_field_names_and_immutability_of_label lbl =
  let all_labels = lbl.lbl_all in
  (List.map (fun lbli -> lbli.lbl_name) (Array.to_list all_labels),
   Array.for_all (fun lbli -> lbli.lbl_mut = Immutable) all_labels)

let record_field_names_and_immutability_of_labels lbls =
  match lbls with
  | [] -> failwith "record creation must include at least one label"
  | lbl::_ -> record_field_names_and_immutability_of_label lbl


