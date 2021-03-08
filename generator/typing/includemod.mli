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

(* $Id: includemod.mli 10795 2010-11-11 22:41:03Z lefessan $ *)

(* Inclusion checks for the module language *)

open Types
open Format

val modtypes: Env.t -> module_type -> module_type -> Typedtree.module_coercion
val signatures: Env.t -> signature -> signature -> Typedtree.module_coercion
val compunit: string -> signature -> string -> signature -> Typedtree.module_coercion
val type_declarations:
      Env.t -> Ident.t -> type_declaration -> type_declaration -> unit

type error =
    Missing_field of Ident.t
  | Value_descriptions of Ident.t * value_description * value_description
  | Type_declarations of Ident.t * type_declaration
        * type_declaration * Includecore.type_mismatch list
  | Exception_declarations of
      Ident.t * exception_declaration * exception_declaration
  | Module_types of module_type * module_type
  | Modtype_infos of Ident.t * modtype_declaration * modtype_declaration
  | Modtype_permutation
  | Interface_mismatch of string * string
  | Class_type_declarations of
      Ident.t * class_type_declaration * class_type_declaration *
      Ctype.class_match_failure list
  | Class_declarations of
      Ident.t * class_declaration * class_declaration *
      Ctype.class_match_failure list
  | Unbound_modtype_path of Path.t

exception Error of error list

val report_error: formatter -> error list -> unit
