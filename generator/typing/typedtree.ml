(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the Q Public License version 1.0.               *)
(*                                                                     *)
(***********************************************************************)

(* $Id: typedtree.ml 10860 2010-11-25 21:43:08Z lefessan $ *)

(* Abstract syntax tree after typing *)

open Misc
open Asttypes
open Types

(* Value expressions for the core language *)

type partial = Partial | Total
type optional = Required | Optional

type pattern =
  { pat_desc: pattern_desc;
    pat_loc: Location.t;
    pat_type: type_expr;
    pat_env: Env.t }

and alias_kind =
  TPat_alias of Ident.t
| TPat_constraint of core_type
| TPat_type of Path.t

and pattern_desc =
    Tpat_any
  | Tpat_var of Ident.t
  | Tpat_alias of pattern * alias_kind
  | Tpat_constant of constant
  | Tpat_tuple of pattern list
  | Tpat_construct of Path.t * constructor_description * pattern list
  | Tpat_variant of label * pattern option * row_desc ref
  | Tpat_record of (Path.t * label_description * pattern) list * closed_flag
  | Tpat_array of pattern list
  | Tpat_or of pattern * pattern * row_desc option
  | Tpat_lazy of pattern

and expression =
  { exp_desc: expression_desc;
    exp_loc: Location.t;
    exp_type: type_expr;
    exp_env: Env.t }

(* CFML *)
and free_vars = type_expr list

and expression_desc =
    Texp_ident of Path.t * Types.value_description
  | Texp_constant of constant
  | Texp_let of rec_flag * free_vars * (pattern * expression) list * expression (* CFML *)
  | Texp_function of label * (pattern * expression) list * partial
  | Texp_apply of expression * (label * expression option * optional) list
  | Texp_match of expression * (pattern * expression) list * partial
  | Texp_try of expression * (pattern * expression) list
  | Texp_tuple of expression list
  | Texp_construct of Path.t * constructor_description * expression list
  | Texp_variant of label * expression option
  | Texp_record of (Path.t * label_description * expression) list * expression option
  | Texp_field of expression * Path.t * label_description
  | Texp_setfield of expression * Path.t * label_description * expression
  | Texp_array of expression list
  | Texp_ifthenelse of expression * expression * expression option
  | Texp_sequence of expression * expression
  | Texp_while of expression * expression
  | Texp_for of
      Ident.t * expression * expression * direction_flag * expression
  | Texp_constraint of expression * core_type option * core_type option
  | Texp_when of expression * expression
  | Texp_send of expression * meth * expression option
  | Texp_new of Path.t * Types.class_declaration
  | Texp_instvar of Path.t * Path.t
  | Texp_setinstvar of Path.t * Path.t * expression
  | Texp_override of Path.t * (Path.t * expression) list
  | Texp_letmodule of Ident.t * module_expr * expression
  | Texp_assert of expression
  | Texp_assertfalse
  | Texp_lazy of expression
  | Texp_poly of expression * core_type option
  | Texp_object of class_structure * string list
  | Texp_newtype of string * expression
  | Texp_pack of module_expr
  | Texp_open of Path.t * expression

and meth =
    Tmeth_name of string
  | Tmeth_val of Ident.t

(* Value expressions for the class language *)

and class_expr =
  { cl_desc: class_expr_desc;
    cl_loc: Location.t;
    cl_type: Types.class_type;
    cl_env: Env.t }

and class_expr_desc =
    Tcl_ident of Path.t * core_type list
  | Tcl_structure of class_structure
  | Tcl_fun of label * pattern * (Ident.t * expression) list * class_expr * partial
  | Tcl_apply of class_expr * (label * expression option * optional) list
  | Tcl_let of rec_flag *  (pattern * expression) list *
                  (Ident.t * expression) list * class_expr
  | Tcl_constraint of class_expr * class_type option * string list * string list * Concr.t
    (* Visible instance variables, methods and concretes methods *)

and class_structure =
  { cstr_pat : pattern;
    cstr_fields: class_field list;
    cstr_type : Types.class_signature;
    cstr_meths: Ident.t Meths.t }

and class_field =
   {
    cf_desc : class_field_desc;
    cf_loc : Location.t;
  }

and class_field_kind =
  Tcfk_virtual of core_type
| Tcfk_concrete of expression

and class_field_desc =
  Tcf_inher of override_flag * class_expr * string option * (string * Ident.t) list * (string * Ident.t) list
    (* Inherited instance variables and concrete methods *)
  | Tcf_val of string * mutable_flag * Ident.t * class_field_kind * bool
        (* None = virtual, true = override *)
  | Tcf_meth of string * private_flag * class_field_kind * bool
  | Tcf_constr of core_type * core_type
  | Tcf_let of rec_flag * (pattern * expression) list *
              (Ident.t * expression) list
  | Tcf_init of expression

(* Value expressions for the module language *)

and module_expr =
  { mod_desc: module_expr_desc;
    mod_loc: Location.t;
    mod_type: Types.module_type;
    mod_env: Env.t }

and module_type_constraint =
  Tmodtype_implicit
| Tmodtype_explicit of module_type

and module_expr_desc =
    Tmod_ident of Path.t
  | Tmod_structure of structure
  | Tmod_functor of Ident.t * module_type * module_expr
  | Tmod_apply of module_expr * module_expr * module_coercion
  | Tmod_constraint of module_expr * Types.module_type * module_type_constraint * module_coercion
  | Tmod_unpack of expression * Types.module_type

and structure = {
  str_items : structure_item list;
  str_type : Types.signature;
}

and structure_item =
  { str_desc : structure_item_desc;
    str_loc : Location.t;
  }

and structure_item_desc =
    Tstr_eval of expression
  | Tstr_value of rec_flag * free_vars * (pattern * expression) list (* CFML *)
  | Tstr_primitive of Ident.t * value_description
  | Tstr_type of (Ident.t * type_declaration) list
  | Tstr_exception of Ident.t * exception_declaration
  | Tstr_exn_rebind of Ident.t * Path.t
  | Tstr_module of Ident.t * module_expr
  | Tstr_recmodule of (Ident.t * module_type * module_expr) list
  | Tstr_modtype of Ident.t * module_type
  | Tstr_open of Path.t
  | Tstr_class of (class_declaration * string list * virtual_flag) list
  | Tstr_class_type of (Ident.t * class_type_declaration) list
  | Tstr_include of module_expr * Ident.t list

and module_type =
  { mty_desc: module_type_desc;
    mty_type : Types.module_type;
    mty_loc: Location.t }

and module_type_desc =
    Tmty_ident of Path.t
  | Tmty_signature of signature
  | Tmty_functor of Ident.t * module_type * module_type
  | Tmty_with of module_type * (Path.t * with_constraint) list
  | Tmty_typeof of module_expr


and signature = {
  sig_items : signature_item list;
  sig_type : Types.signature;
}

and signature_item =
  { sig_desc: signature_item_desc;
    sig_loc: Location.t }

and signature_item_desc =
    Tsig_value of Ident.t * value_description
  | Tsig_type of (Ident.t * type_declaration) list
  | Tsig_exception of Ident.t * exception_declaration
  | Tsig_module of Ident.t * module_type
  | Tsig_recmodule of (Ident.t * module_type) list
  | Tsig_modtype of Ident.t * modtype_declaration
  | Tsig_open of Path.t
  | Tsig_include of module_type
  | Tsig_class of class_description list
  | Tsig_class_type of class_type_declaration list

and modtype_declaration =
    Tmodtype_abstract
  | Tmodtype_manifest of module_type

and with_constraint =
    Twith_type of type_declaration
  | Twith_module of Path.t
  | Twith_typesubst of type_declaration
  | Twith_modsubst of Path.t

and module_coercion =
    Tcoerce_none
  | Tcoerce_structure of (int * module_coercion) list
  | Tcoerce_functor of module_coercion * module_coercion
  | Tcoerce_primitive of Primitive.description

and core_type =
  { mutable ctyp_desc : core_type_desc;
    mutable ctyp_type : type_expr;
    ctyp_loc : Location.t }

and core_type_desc =
    Ttyp_any
  | Ttyp_var of string
  | Ttyp_arrow of label * core_type * core_type
  | Ttyp_tuple of core_type list
  | Ttyp_constr of Path.t * core_type list
  | Ttyp_object of core_field_type list
  | Ttyp_class of Path.t * core_type list * label list
  | Ttyp_alias of core_type * string
  | Ttyp_variant of row_field list * bool * label list option
  | Ttyp_poly of string list * core_type
  | Ttyp_package of package_type

and package_type = {
  pack_name : Path.t;
  pack_fields : (string * core_type) list;
  pack_type : Types.module_type;
}

and core_field_type =
  { field_desc: core_field_desc;
    field_loc: Location.t }

and core_field_desc =
    Tcfield of string * core_type
  | Tcfield_var

and row_field =
    Ttag of label * bool * core_type list
  | Tinherit of core_type

and value_description =
  { val_desc : core_type;
    val_val : Types.value_description;
    val_prim : string list;
    val_loc : Location.t;
    }

and type_declaration =
  { typ_params: string list;
    typ_type : Types.type_declaration;
    typ_cstrs: (core_type * core_type * Location.t) list;
    typ_kind: type_kind;
    typ_private: private_flag;
    typ_manifest: core_type option;
    typ_variance: (bool * bool) list;
    typ_loc: Location.t }

and type_kind =
    Ttype_abstract
  | Ttype_variant of (string * core_type list * Location.t) list
  | Ttype_record of
      (string * mutable_flag * core_type * Location.t) list

and exception_declaration = core_type list

and class_type =
  { cltyp_desc: class_type_desc;
    cltyp_type : Types.class_type;
    cltyp_loc: Location.t }

and class_type_desc =
    Tcty_constr of Path.t * core_type list
  | Tcty_signature of class_signature
  | Tcty_fun of label * core_type * class_type

and class_signature = {
    csig_self : core_type;
    csig_fields : class_type_field list;
    csig_type : Types.class_signature;
    csig_loc : Location.t;
  }

and class_type_field = {
    ctf_desc : class_type_field_desc;
    ctf_loc : Location.t;
  }

and class_type_field_desc =
    Tctf_inher of class_type
  | Tctf_val of (string * mutable_flag * virtual_flag * core_type)
  | Tctf_virt  of (string * private_flag * core_type)
  | Tctf_meth  of (string * private_flag * core_type)
  | Tctf_cstr  of (core_type * core_type)

and class_declaration =
  class_expr class_infos

and class_description =
  class_type class_infos

and class_type_declaration =
  class_type class_infos

and 'a class_infos =
  { ci_virt: virtual_flag;
    ci_params: string list * Location.t;
    ci_id_class: Ident.t;
    ci_id_class_type : Ident.t;
    ci_id_object : Ident.t;
    ci_id_typesharp : Ident.t;
    ci_expr: 'a;
    ci_decl: Types.class_declaration;
    ci_type_decl : Types.class_type_declaration;
    ci_variance: (bool * bool) list;
    ci_loc: Location.t }




type saved_type =
| Saved_implementation of structure
| Saved_structure of structure
| Saved_structure_item of structure_item
| Saved_signature of signature
| Saved_signature_item of signature_item
| Saved_expression of expression
| Saved_module_type of module_type
| Saved_pattern of pattern
| Saved_class_expr of class_expr

let saved_types = ref []
let get_saved_types () = !saved_types
let set_saved_types list = saved_types := list
let add_saved_type s = saved_types := s :: !saved_types


(* Auxiliary functions over the a.s.t. *)

let iter_pattern_desc f = function
  | Tpat_alias(p, id) -> f p
  | Tpat_tuple patl -> List.iter f patl
  | Tpat_construct(_, cstr, patl) -> List.iter f patl
  | Tpat_variant(_, pat, _) -> may f pat
  | Tpat_record (lbl_pat_list, _) ->
      List.iter (fun (_, lbl, pat) -> f pat) lbl_pat_list
  | Tpat_array patl -> List.iter f patl
  | Tpat_or(p1, p2, _) -> f p1; f p2
  | Tpat_lazy p -> f p
  | Tpat_any
  | Tpat_var _
  | Tpat_constant _ -> ()

let map_pattern_desc f d =
  match d with
  | Tpat_alias (p1, id) ->
      Tpat_alias (f p1, id)
  | Tpat_tuple pats ->
      Tpat_tuple (List.map f pats)
  | Tpat_record (lpats, closed) ->
      Tpat_record (List.map (fun ( lid, l,p) -> lid, l, f p) lpats, closed)
  | Tpat_construct (lid, c,pats) ->
      Tpat_construct (lid, c, List.map f pats)
  | Tpat_array pats ->
      Tpat_array (List.map f pats)
  | Tpat_lazy p1 -> Tpat_lazy (f p1)
  | Tpat_variant (x1, Some p1, x2) ->
      Tpat_variant (x1, Some (f p1), x2)
  | Tpat_or (p1,p2,path) ->
      Tpat_or (f p1, f p2, path)
  | Tpat_var _
  | Tpat_constant _
  | Tpat_any
  | Tpat_variant (_,None,_) -> d

(* List the identifiers bound by a pattern or a let *)

let idents = ref([]: Ident.t list)

let rec bound_idents pat =
  match pat.pat_desc with
  | Tpat_var id -> idents := id :: !idents
  | Tpat_alias(p, TPat_alias id) ->
      bound_idents p; idents := id :: !idents
  | Tpat_alias(p, _) ->
      bound_idents p
  | Tpat_or(p1, _, _) ->
      (* Invariant : both arguments binds the same variables *)
      bound_idents p1
  | d -> iter_pattern_desc bound_idents d

(* FIXME unused
let pat_bound_idents pat =
  idents := []; bound_idents pat; let res = !idents in idents := []; res
 *)

let rev_let_bound_idents pat_expr_list =
  idents := [];
  List.iter (fun (pat, expr) -> bound_idents pat) pat_expr_list;
  let res = !idents in idents := []; res

let let_bound_idents pat_expr_list =
  List.rev(rev_let_bound_idents pat_expr_list)

let alpha_var env id = List.assoc id env

let rec alpha_pat env p = match p.pat_desc with
| Tpat_var id -> (* note the ``Not_found'' case *)
    {p with pat_desc =
     try Tpat_var (alpha_var env id) with
     | Not_found -> Tpat_any}
| Tpat_alias (p1, TPat_alias id) ->
    let new_p =  alpha_pat env p1 in
    begin try
      {p with pat_desc = Tpat_alias (new_p, TPat_alias (alpha_var env id))}
    with
    | Not_found -> new_p
    end
| d ->
    {p with pat_desc = map_pattern_desc (alpha_pat env) d}




module type IteratorArgument = sig

    val enter_structure : structure -> unit
    val enter_value_description : value_description -> unit
    val enter_type_declaration : type_declaration -> unit
    val enter_exception_declaration :
      exception_declaration -> unit
    val enter_pattern : pattern -> unit
    val enter_expression : expression -> unit
    val enter_package_type : package_type -> unit
    val enter_signature : signature -> unit
    val enter_signature_item : signature_item -> unit
    val enter_modtype_declaration : modtype_declaration -> unit
    val enter_module_type : module_type -> unit
    val enter_module_expr : module_expr -> unit
    val enter_with_constraint : with_constraint -> unit
    val enter_class_expr : class_expr -> unit
    val enter_class_signature : class_signature -> unit
    val enter_class_description : class_description -> unit
    val enter_class_type_declaration :
      class_type_declaration -> unit
    val enter_class_infos : 'a class_infos -> unit
    val enter_class_type : class_type -> unit
    val enter_class_type_field : class_type_field -> unit
    val enter_core_type : core_type -> unit
    val enter_core_field_type : core_field_type -> unit
    val enter_class_structure : class_structure -> unit
    val enter_class_field : class_field -> unit
    val enter_structure_item : structure_item -> unit


    val leave_structure : structure -> unit
    val leave_value_description : value_description -> unit
    val leave_type_declaration : type_declaration -> unit
    val leave_exception_declaration :
      exception_declaration -> unit
    val leave_pattern : pattern -> unit
    val leave_expression : expression -> unit
    val leave_package_type : package_type -> unit
    val leave_signature : signature -> unit
    val leave_signature_item : signature_item -> unit
    val leave_modtype_declaration : modtype_declaration -> unit
    val leave_module_type : module_type -> unit
    val leave_module_expr : module_expr -> unit
    val leave_with_constraint : with_constraint -> unit
    val leave_class_expr : class_expr -> unit
    val leave_class_signature : class_signature -> unit
    val leave_class_description : class_description -> unit
    val leave_class_type_declaration :
      class_type_declaration -> unit
    val leave_class_infos : 'a class_infos -> unit
    val leave_class_type : class_type -> unit
    val leave_class_type_field : class_type_field -> unit
    val leave_core_type : core_type -> unit
    val leave_core_field_type : core_field_type -> unit
    val leave_class_structure : class_structure -> unit
    val leave_class_field : class_field -> unit
    val leave_structure_item : structure_item -> unit

    val enter_bindings : rec_flag -> unit
    val enter_binding : pattern -> expression -> unit
    val leave_binding : pattern -> expression -> unit
    val leave_bindings : rec_flag -> unit

      end

module MakeIterator(Iter : IteratorArgument) : sig

    val iter_structure : structure -> unit
    val iter_signature : signature -> unit

  end = struct

    let may_iter f v =
      match v with
        None -> ()
      | Some x -> f x


    open Asttypes

    let rec iter_structure str =
      Iter.enter_structure str;
      List.iter iter_structure_item str.str_items;
      Iter.leave_structure str


    and iter_binding (pat, exp) =
      Iter.enter_binding pat exp;
      iter_pattern pat;
      iter_expression exp;
      Iter.leave_binding pat exp

    and iter_bindings rec_flag list =
      Iter.enter_bindings rec_flag;
      List.iter iter_binding list;
      Iter.leave_bindings rec_flag

    and iter_structure_item item =
      Iter.enter_structure_item item;
      begin
        match item.str_desc with
          Tstr_eval exp -> iter_expression exp
        | Tstr_value (rec_flag, fvs, list) -> (* CFML *)
            iter_bindings rec_flag list
        | Tstr_primitive (id, v) -> iter_value_description v
        | Tstr_type list ->
            List.iter (fun (id, decl) -> iter_type_declaration decl) list
        | Tstr_exception (id, decl) -> iter_exception_declaration decl
        | Tstr_exn_rebind (id, p) -> ()
        | Tstr_module (id, mexpr) ->
            iter_module_expr mexpr
        | Tstr_recmodule list ->
            List.iter (fun (id, mtype, mexpr) ->
                iter_module_type mtype;
                iter_module_expr mexpr) list
        | Tstr_modtype (id, mtype) ->
            iter_module_type mtype
        | Tstr_open path -> ()
        | Tstr_class list ->
            List.iter (fun (ci, _, _) ->
                Iter.enter_class_infos ci;
                iter_class_expr ci.ci_expr;
            ) list
        | Tstr_class_type list ->
            List.iter (fun (id, ct) ->
                Iter.enter_class_infos ct;
                iter_class_type ct.ci_expr;
            ) list
        | Tstr_include (mexpr, _) ->
            iter_module_expr mexpr
      end;
      Iter.leave_structure_item item

    and iter_value_description v =
      Iter.enter_value_description v;
      iter_core_type v.val_desc;
      Iter.leave_value_description v

    and iter_type_declaration decl =
      Iter.enter_type_declaration decl;
      List.iter (fun (ct1, ct2, loc) ->
          iter_core_type ct1;
          iter_core_type ct2
      ) decl.typ_cstrs;
      begin match decl.typ_kind with
          Ttype_abstract -> ()
        | Ttype_variant list ->
            List.iter (fun (s, cts, loc) ->
                List.iter iter_core_type cts
            ) list
        | Ttype_record list ->
            List.iter (fun (s, mut, ct, loc) ->
                iter_core_type ct
            ) list
      end;
      begin match decl.typ_manifest with
          None -> ()
        | Some ct -> iter_core_type ct
      end;
      Iter.leave_type_declaration decl

    and iter_exception_declaration decl =
      Iter.enter_exception_declaration decl;
      List.iter iter_core_type decl;
      Iter.leave_exception_declaration decl;

    and iter_pattern pat =
      Iter.enter_pattern pat;
      begin
        match pat.pat_desc with
          Tpat_any -> ()
        | Tpat_var id -> ()
        | Tpat_alias (pat1, kind) ->
            iter_pattern pat1;
            begin
              match kind with
                TPat_alias _ -> ()
              | TPat_type ct -> ()
              | TPat_constraint ct -> iter_core_type ct
            end
        | Tpat_constant cst -> ()
        | Tpat_tuple list ->
            List.iter iter_pattern list
        | Tpat_construct (path, _, args) ->
            List.iter iter_pattern args
        | Tpat_variant (label, pato, _) ->
            begin match pato with
                None -> ()
              | Some pat -> iter_pattern pat
            end
        | Tpat_record (list, closed) ->
            List.iter (fun (path, _, pat) -> iter_pattern pat) list
        | Tpat_array list -> List.iter iter_pattern list
        | Tpat_or (p1, p2, _) -> iter_pattern p1; iter_pattern p2
        | Tpat_lazy p -> iter_pattern p
      end;
      Iter.leave_pattern pat

    and iter_expression exp =
      Iter.enter_expression exp;
      begin
        match exp.exp_desc with
          Texp_ident (path, _) -> ()
        | Texp_constant cst -> ()
        | Texp_let (rec_flag, fvs, list, exp) -> (* CFML *)
            iter_bindings rec_flag list;
            iter_expression exp
        | Texp_function (label, cases, _) ->
            iter_bindings Nonrecursive cases
        | Texp_apply (exp, list) ->
            iter_expression exp;
            List.iter (fun (label, expo, _) ->
                match expo with
                  None -> ()
                | Some exp -> iter_expression exp
            ) list
        | Texp_match (exp, list, _) ->
            iter_expression exp;
            iter_bindings Nonrecursive list
        | Texp_try (exp, list) ->
            iter_expression exp;
            iter_bindings Nonrecursive list
        | Texp_tuple list ->
            List.iter iter_expression list
        | Texp_construct (path, _, args) ->
            List.iter iter_expression args
        | Texp_variant (label, expo) ->
            begin match expo with
                None -> ()
              | Some exp -> iter_expression exp
            end
        | Texp_record (list, expo) ->
            List.iter (fun (path, _, exp) ->
                iter_expression exp
            ) list;
            begin match expo with
                None -> ()
              | Some exp -> iter_expression exp
            end
        | Texp_field (exp, path, label) ->
            iter_expression exp
        | Texp_setfield (exp1, path , label, exp2) ->
            iter_expression exp1;
            iter_expression exp2
        | Texp_array list ->
            List.iter iter_expression list
        | Texp_ifthenelse (exp1, exp2, expo) ->
            iter_expression exp1;
            iter_expression exp2;
            begin match expo with
                None -> ()
              | Some exp -> iter_expression exp
            end
        | Texp_sequence (exp1, exp2) ->
            iter_expression exp1;
            iter_expression exp2
        | Texp_while (exp1, exp2) ->
            iter_expression exp1;
            iter_expression exp2
        | Texp_for (id, exp1, exp2, dir, exp3) ->
            iter_expression exp1;
            iter_expression exp2;
            iter_expression exp3
        | Texp_when (exp1, exp2) ->
            iter_expression exp1;
            iter_expression exp2
        | Texp_send (exp, meth, _) ->
            iter_expression exp
        | Texp_new (path, _) -> ()
        | Texp_instvar (_, path) -> ()
        | Texp_setinstvar (_, path, exp) ->
            iter_expression exp
        | Texp_override (_, list) ->
            List.iter (fun (path, exp) ->
                iter_expression exp
            ) list
        | Texp_letmodule (id, mexpr, exp) ->
            iter_module_expr mexpr;
            iter_expression exp
        | Texp_assert exp -> iter_expression exp
        | Texp_assertfalse -> ()
        | Texp_lazy exp -> iter_expression exp
        | Texp_object (cl, _) ->
            iter_class_structure cl
        | Texp_pack (mexpr) ->
            iter_module_expr mexpr
        | Texp_poly (exp, None) -> iter_expression exp
        | Texp_poly (exp, Some ct) ->
            iter_expression exp; iter_core_type ct
        | Texp_open (path, exp) ->
            iter_expression exp
        | Texp_newtype (s, exp) ->
            iter_expression exp
        | Texp_constraint (exp, cto1, cto2) ->
            iter_expression exp;
            may_iter iter_core_type cto1;
            may_iter iter_core_type cto2
      end;
      Iter.leave_expression exp;

    and iter_package_type pack =
      Iter.enter_package_type pack;
      List.iter (fun (s, ct) -> iter_core_type ct) pack.pack_fields;
      Iter.leave_package_type pack;

    and iter_signature sg =
      Iter.enter_signature sg;
      List.iter iter_signature_item sg.sig_items;
      Iter.leave_signature sg;

    and iter_signature_item item =
      Iter.enter_signature_item item;
      begin
        match item.sig_desc with
          Tsig_value (id, v) ->
            iter_value_description v
        | Tsig_type list ->
            List.iter (fun (id, decl) ->
                iter_type_declaration decl
            ) list
        | Tsig_exception (id, decl) ->
            iter_exception_declaration decl
        | Tsig_module (id, mtype) ->
            iter_module_type mtype
        | Tsig_recmodule list ->
            List.iter (fun (id, mtype) -> iter_module_type mtype) list
        | Tsig_modtype (id, mdecl) ->
            iter_modtype_declaration mdecl
        | Tsig_open path -> ()
        | Tsig_include mty -> iter_module_type mty
        | Tsig_class list ->
            List.iter iter_class_description list
        | Tsig_class_type list ->
            List.iter iter_class_type_declaration list
      end;
      Iter.leave_signature_item item;

    and iter_modtype_declaration mdecl =
      Iter.enter_modtype_declaration mdecl;
      begin
        match mdecl with
          Tmodtype_abstract -> ()
        | Tmodtype_manifest mtype -> iter_module_type mtype
      end;
      Iter.leave_modtype_declaration mdecl;


    and iter_class_description cd =
      Iter.enter_class_description cd;
      iter_class_type cd.ci_expr;
      Iter.leave_class_description cd;

    and iter_class_type_declaration cd =
      Iter.enter_class_type_declaration cd;
      iter_class_type cd.ci_expr;
        Iter.leave_class_type_declaration cd;

    and iter_module_type mty =
      Iter.enter_module_type mty;
      begin
        match mty.mty_desc with
          Tmty_ident path -> ()
        | Tmty_signature sg -> iter_signature sg
        | Tmty_functor (id, mtype1, mtype2) ->
            iter_module_type mtype1; iter_module_type mtype2
        | Tmty_with (mtype, list) ->
            iter_module_type mtype;
            List.iter (fun (path, withc) ->
                iter_with_constraint withc
            ) list
        | Tmty_typeof mexpr ->
            iter_module_expr mexpr
      end;
      Iter.leave_module_type mty;

    and iter_with_constraint cstr =
      Iter.enter_with_constraint cstr;
      begin
        match cstr with
          Twith_type decl -> iter_type_declaration decl
        | Twith_module path -> ()
        | Twith_typesubst decl -> iter_type_declaration decl
        | Twith_modsubst path -> ()
      end;
      Iter.leave_with_constraint cstr;

    and iter_module_expr mexpr =
      Iter.enter_module_expr mexpr;
      begin
        match mexpr.mod_desc with
          Tmod_ident p -> ()
        | Tmod_structure st -> iter_structure st
        | Tmod_functor (id, mtype, mexpr) ->
            iter_module_type mtype;
            iter_module_expr mexpr
        | Tmod_apply (mexp1, mexp2, _) ->
            iter_module_expr mexp1;
            iter_module_expr mexp2
        | Tmod_constraint (mexpr, _, Tmodtype_implicit, _ ) ->
            iter_module_expr mexpr
        | Tmod_constraint (mexpr, _, Tmodtype_explicit mtype, _) ->
            iter_module_expr mexpr;
            iter_module_type mtype
        | Tmod_unpack (exp, mty) ->
            iter_expression exp
(*          iter_module_type mty *)
      end;
      Iter.leave_module_expr mexpr;

    and iter_class_expr cexpr =
      Iter.enter_class_expr cexpr;
      begin
        match cexpr.cl_desc with
        | Tcl_constraint (cl, None, _, _, _ ) ->
            iter_class_expr cl;
        | Tcl_structure clstr -> iter_class_structure clstr
        | Tcl_fun (label, pat, pv, cl, partial) ->
            iter_pattern pat;
            iter_class_expr cl

        | Tcl_apply (cl, args) ->
            iter_class_expr cl;
            List.iter (fun (label, expo, _) ->
                match expo with
                  None -> ()
                | Some exp -> iter_expression exp
            ) args

        | Tcl_let (rec_flat, bindings, ivars, cl) ->
            iter_bindings Nonrecursive bindings;
            iter_class_expr cl

        | Tcl_constraint (cl, Some clty, vals, meths, concrs) ->
            iter_class_expr cl;
            iter_class_type clty

        | Tcl_ident (_, tyl) ->
            List.iter iter_core_type tyl
      end;
      Iter.leave_class_expr cexpr;

    and iter_class_type ct =
      Iter.enter_class_type ct;
      begin
        match ct.cltyp_desc with
          Tcty_signature csg -> iter_class_signature csg
        | Tcty_constr (path, list) ->
            List.iter iter_core_type list
        | Tcty_fun (label, ct, cl) ->
            iter_core_type ct;
            iter_class_type cl
      end;
      Iter.leave_class_type ct;

    and iter_class_signature cs =
      Iter.enter_class_signature cs;
      iter_core_type cs.csig_self;
      List.iter iter_class_type_field cs.csig_fields;
      Iter.leave_class_signature cs


    and iter_class_type_field ctf =
      Iter.enter_class_type_field ctf;
      begin
        match ctf.ctf_desc with
          Tctf_inher ct -> iter_class_type ct
        | Tctf_val (s, mut, virt, ct) ->
            iter_core_type ct
        | Tctf_virt  (s, priv, ct) ->
            iter_core_type ct
        | Tctf_meth  (s, priv, ct) ->
            iter_core_type ct
        | Tctf_cstr  (ct1, ct2) ->
            iter_core_type ct1;
            iter_core_type ct2
      end;
      Iter.leave_class_type_field ctf

    and iter_core_type ct =
      Iter.enter_core_type ct;
      begin
        match ct.ctyp_desc with
          Ttyp_any -> ()
        | Ttyp_var s -> ()
        | Ttyp_arrow (label, ct1, ct2) ->
            iter_core_type ct1;
            iter_core_type ct2
        | Ttyp_tuple list -> List.iter iter_core_type list
        | Ttyp_constr (path, list) ->
            List.iter iter_core_type list
        | Ttyp_object list ->
            List.iter iter_core_field_type list
        | Ttyp_class (path, list, labels) ->
            List.iter iter_core_type list
        | Ttyp_alias (ct, s) ->
            iter_core_type ct
        | Ttyp_variant (list, bool, labels) ->
            List.iter iter_row_field list
        | Ttyp_poly (list, ct) -> iter_core_type ct
        | Ttyp_package pack -> iter_package_type pack
      end;
      Iter.leave_core_type ct;

    and iter_core_field_type cft =
      Iter.enter_core_field_type cft;
      begin match cft.field_desc with
          Tcfield_var -> ()
        | Tcfield (s, ct) -> iter_core_type ct
      end;
      Iter.leave_core_field_type cft;

    and iter_class_structure cs =
      Iter.enter_class_structure cs;
      iter_pattern cs.cstr_pat;
      List.iter iter_class_field cs.cstr_fields;
      Iter.leave_class_structure cs;


    and iter_row_field rf =
      match rf with
        Ttag (label, bool, list) ->
          List.iter iter_core_type list
      | Tinherit ct -> iter_core_type ct

    and iter_class_field cf =
      Iter.enter_class_field cf;
      begin
        match cf.cf_desc with
          Tcf_inher (ovf, cl, super, _vals, _meths) ->
          iter_class_expr cl
      | Tcf_constr (cty, cty') ->
          iter_core_type cty;
          iter_core_type cty'
      | Tcf_val (lab, mut, _, Tcfk_virtual cty, override) ->
          iter_core_type cty
      | Tcf_val (lab, mut, _, Tcfk_concrete exp, override) ->
          iter_expression exp
      | Tcf_meth (lab, priv, Tcfk_virtual cty, override) ->
          iter_core_type cty
      | Tcf_meth (lab, priv, Tcfk_concrete exp, override) ->
          iter_expression exp
      | Tcf_let (rec_flag, bindings, _) ->
          iter_bindings Nonrecursive bindings
      | Tcf_init exp ->
          iter_expression exp
      end;
      Iter.leave_class_field cf;

  end

module DefaultIteratorArgument = struct

      let enter_structure _ = ()
      let enter_value_description _ = ()
      let enter_type_declaration _ = ()
      let enter_exception_declaration _ = ()
      let enter_pattern _ = ()
      let enter_expression _ = ()
      let enter_package_type _ = ()
      let enter_signature _ = ()
      let enter_signature_item _ = ()
      let enter_modtype_declaration _ = ()
      let enter_module_type _ = ()
      let enter_module_expr _ = ()
      let enter_with_constraint _ = ()
      let enter_class_expr _ = ()
      let enter_class_signature _ = ()
      let enter_class_description _ = ()
      let enter_class_type_declaration _ = ()
      let enter_class_infos _ = ()
      let enter_class_type _ = ()
      let enter_class_type_field _ = ()
      let enter_core_type _ = ()
      let enter_core_field_type _ = ()
      let enter_class_structure _ = ()
    let enter_class_field _ = ()
    let enter_structure_item _ = ()


      let leave_structure _ = ()
      let leave_value_description _ = ()
      let leave_type_declaration _ = ()
      let leave_exception_declaration _ = ()
      let leave_pattern _ = ()
      let leave_expression _ = ()
      let leave_package_type _ = ()
      let leave_signature _ = ()
      let leave_signature_item _ = ()
      let leave_modtype_declaration _ = ()
      let leave_module_type _ = ()
      let leave_module_expr _ = ()
      let leave_with_constraint _ = ()
      let leave_class_expr _ = ()
      let leave_class_signature _ = ()
      let leave_class_description _ = ()
      let leave_class_type_declaration _ = ()
      let leave_class_infos _ = ()
      let leave_class_type _ = ()
      let leave_class_type_field _ = ()
      let leave_core_type _ = ()
      let leave_core_field_type _ = ()
      let leave_class_structure _ = ()
    let leave_class_field _ = ()
    let leave_structure_item _ = ()

    let enter_binding _ _ = ()
    let leave_binding _ _ = ()

    let enter_bindings _ = ()
    let leave_bindings _ = ()

  end
