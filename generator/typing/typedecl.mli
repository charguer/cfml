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

(* $Id: typedecl.mli 10795 2010-11-11 22:41:03Z lefessan $ *)

(* Typing of type definitions and primitive definitions *)

open Types
open Format

val transl_type_decl:
    Env.t -> (string * Parsetree.type_declaration) list ->
  (Ident.t * Typedtree.type_declaration) list * Env.t

val transl_exception:
    Env.t -> Parsetree.exception_declaration -> Typedtree.exception_declaration

val transl_exn_rebind:
    Env.t -> Location.t -> Longident.t -> Path.t * exception_declaration

val transl_value_decl:
    Env.t -> Parsetree.value_description -> Typedtree.value_description

val transl_with_constraint:
    Env.t -> Ident.t -> Path.t option ->
    Parsetree.type_declaration -> Typedtree.type_declaration

val abstract_type_decl: int -> type_declaration
val approx_type_decl:
    Env.t -> (string * Parsetree.type_declaration) list ->
                                  (Ident.t * type_declaration) list
val check_recmod_typedecl:
    Env.t -> Location.t -> Ident.t list -> Path.t -> type_declaration -> unit

(* for fixed types *)
val is_fixed_type : Parsetree.type_declaration -> bool

(* for typeclass.ml *)
val compute_variance_decls:
    Env.t ->
    (Ident.t * type_declaration * type_declaration * class_declaration *
       class_type_declaration * 'a Typedtree.class_infos) list ->
    (type_declaration * type_declaration * class_declaration *
       class_type_declaration) list

type error =
    Repeated_parameter
  | Duplicate_constructor of string
  | Too_many_constructors
  | Duplicate_label of string
  | Recursive_abbrev of string
  | Definition_mismatch of type_expr * Includecore.type_mismatch list
  | Constraint_failed of type_expr * type_expr
  | Unconsistent_constraint of (type_expr * type_expr) list
  | Type_clash of (type_expr * type_expr) list
  | Parameters_differ of Path.t * type_expr * type_expr
  | Null_arity_external
  | Missing_native_external
  | Unbound_type_var of type_expr * type_declaration
  | Unbound_exception of Longident.t
  | Not_an_exception of Longident.t
  | Bad_variance of int * (bool*bool) * (bool*bool)
  | Unavailable_type_constructor of Path.t
  | Bad_fixed_type of string
  | Unbound_type_var_exc of type_expr * type_expr

exception Error of Location.t * error

val report_error: formatter -> error -> unit
