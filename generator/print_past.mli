(* TEMPORARY

(** Printing of the parse tree *)

val string_of_pattern : 'a -> Parsetree.pattern -> string
val string_of_expression : bool -> Parsetree.expression -> string
val string_of_module : Parsetree.module_expr -> string
val string_of_structure : Parsetree.structure -> string
val string_of_structure_item : Parsetree.structure_item -> string
val string_of_toplevel_phrase : Parsetree.toplevel_phrase -> string
val string_of_source : Parsetree.toplevel_phrase list -> string

*)