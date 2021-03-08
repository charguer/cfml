
(** Printing of the typed tree *)

val string_of_typed_var : string -> Types.type_expr -> string
val string_of_path : Path.t -> string
val string_of_pattern : 'a -> Typedtree.pattern -> string
val string_of_let_pattern : 'a -> Types.type_expr list -> Typedtree.pattern -> string
val string_of_expression : bool -> Typedtree.expression -> string
val string_of_module : Typedtree.module_expr -> string
val string_of_structure : Typedtree.structure -> string
val string_of_structure_item : Typedtree.structure_item -> string
