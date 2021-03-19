
(** Simple grammar of types *)

type btyp =
    Btyp_alias of btyp * string
  | Btyp_arrow of btyp * btyp
  | Btyp_constr of Path.t * btyp list
  | Btyp_tuple of btyp list
  | Btyp_var of string * Types.type_expr 
      (* - string: name of variable
         - type_expr: for internal use to track which variables are used *)
  | Btyp_poly of string list * btyp
  | Btyp_val

(** Mark a variable as used at least once. *)

val typvar_mark_used : Types.type_expr -> unit

(** Test if a variable has been used at least once. *)

val typvar_is_used : Types.type_expr -> bool

(** Translates a type expression [t] into a [btyp]. *)

val btyp_of_typ_exp : Types.type_expr -> btyp

(** Translates of a type scheme [t] into a [btyp], *)

val btyp_of_typ_sch_simple : Types.type_expr -> btyp

(** Return the name of a type variable *) 

val name_of_type_var : Types.type_expr -> string

(** Function to reset the fresh name generator for type variables *)

val reset_names : unit -> unit

(** Pretty printer for a type *)

val print_out_type : btyp -> string

(** Convert a type into a string *)

val string_of_type_exp : Types.type_expr -> string

(** Convert a type scheme into a string *)

val string_of_type_sch : Types.type_expr list -> Types.type_expr -> string


(** Customization of the type renaming function;
    The identity function by default. 
    (Reference set by Characteristic.cfg_file.) *)

val type_rename : (string -> string) ref
