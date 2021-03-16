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

(* $Id: typedtree.mli 10860 2010-11-25 21:43:08Z lefessan $ *)

(* Abstract syntax tree after typing *)

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

(* Instead of adding two new constructs (Tpat_constraint and Tpat_type),
we chose to change Tpat_alias, so that we don't have to modify too much
the pattern matching engine, and don't introduce bugs. *)

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
  {
    cstr_pat : pattern;
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
(*      (Ident.t * int * string list * class_expr * virtual_flag) list *)
  | Tstr_class_type of (Ident.t * class_type_declaration) list
  | Tstr_include of module_expr * Ident.t list

and module_type =
  { mty_desc : module_type_desc;
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
(* mutable because of [Typeclass.declare_method] *)
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

(* Auxiliary functions over the a.s.t. *)

val iter_pattern_desc : (pattern -> unit) -> pattern_desc -> unit
val map_pattern_desc : (pattern -> pattern) -> pattern_desc -> pattern_desc

val let_bound_idents: (pattern * expression) list -> Ident.t list
val rev_let_bound_idents: (pattern * expression) list -> Ident.t list

(* Alpha conversion of patterns *)
val alpha_pat : (Ident.t * Ident.t) list -> pattern -> pattern



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

val get_saved_types : unit -> saved_type list
val set_saved_types : saved_type list -> unit
val add_saved_type : saved_type -> unit


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

module MakeIterator :
  functor
  (_ : IteratorArgument) ->
           sig
             val iter_structure : structure -> unit
             val iter_signature : signature -> unit
           end

module DefaultIteratorArgument : IteratorArgument
