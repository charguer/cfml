(*
val external_modules : string list ref
val external_modules_add : string -> unit
val external_modules_get_coqtop : unit -> Coq.coqtop list
val external_modules_reset : unit -> unit
val lift_ident_name : Ident.t -> string
val lift_full_path : Path.t -> Path.t
val lift_path : Path.t -> Path.t
val lift_full_path_name : Path.t -> string
val lift_path_name : Path.t -> string
val record_type_name : string -> string
val record_constructor : string -> string
val fv_btyp : ?through_arrow:bool -> Print_type.btyp -> string list
val lift_btyp : Print_type.btyp -> Coq.coq
val lift_typ_exp : Types.type_expr -> Coq.coq
val lift_typ_sch : Types.type_expr -> string list * Coq.coq
val coq_typ : Typedtree.expression -> Coq.coq
val coq_typ_pat : Typedtree.pattern -> Coq.coq
val path_decompose : Path.t -> string * string
val get_record_decomposed_name_for_exp :
  Typedtree.expression -> string * string
val typ_arity_var : int Ident.tbl -> Path.t -> int
val typ_arity_constr : Types.constructor_description -> int
val coq_of_constructor : Path.t -> Types.constructor_description -> Coq.coq
val pattern_variables : Typedtree.pattern -> Coq.typed_vars
val lift_pat : ?through_aliases:bool -> Typedtree.pattern -> Coq.coq
val pattern_aliases : Typedtree.pattern -> (Coq.typed_var * Coq.coq) list
val register_cf : Coq.var -> Coq.coqtop
val register_spec : Coq.var -> Coq.var -> Coq.coqtop
val prefix_for_label : Types.type_expr -> string
val string_of_label_with : string -> Types.label_description -> string
val name_for_record_new : string -> string
val name_for_record_get : Types.label_description -> string
val name_for_record_set : Types.label_description -> string
val string_of_label : Types.type_expr -> Types.label_description -> string
val simplify_apply_args :
  ('a * 'b option * Typedtree.optional) list -> 'b list
val exp_find_inlined_primitive :
  Typedtree.expression ->
  ('a * Typedtree.expression option * Typedtree.optional) list ->
  string option
val exp_is_inlined_primitive :
  Typedtree.expression ->
  ('a * Typedtree.expression option * Typedtree.optional) list -> bool
val exp_get_inlined_primitive :
  Typedtree.expression ->
  ('a * Typedtree.expression option * Typedtree.optional) list -> string
val lift_exp_path : int Ident.tbl -> Path.t -> Coq.coq
val lift_val : int Ident.tbl -> Typedtree.expression -> Coq.coq
val counter_local_label : int ref
val get_next_local_label : unit -> string
val reset_local_labels : unit -> unit
val used_labels : Coq.var list ref
val reset_used_labels : unit -> unit
val add_used_label : Coq.var -> unit
val cfg_extract_labels : unit -> Formula.cftop list
val pattern_ident : Typedtree.pattern -> Ident.t
val pattern_name : Typedtree.pattern -> string
val extract_label_names_simple : Env.t -> Types.type_expr -> string list
val cfg_exp : int Ident.tbl -> Typedtree.expression -> Formula.cf
val cfg_func :
  int Ident.tbl ->
  Typedtree.free_vars ->
  Typedtree.pattern -> Typedtree.expression -> Formula.cf
val is_algebraic : 'a * Typedtree.type_declaration -> bool
val is_type_abbrev : 'a * Typedtree.type_declaration -> bool
val is_type_record : 'a * Typedtree.type_declaration -> bool
val cfg_structure_item : Typedtree.structure_item -> Formula.cftops
val cfg_type_abbrev :
  Ident.t * Typedtree.type_declaration -> Coq.coqtop list * Coq.coqtop list
val cfg_type_record :
  Ident.t * Typedtree.type_declaration -> Coq.coqtop list * Coq.coqtop list
val record_functions :
  string ->
  string ->
  Coq.var -> Coq.var list -> string list -> Coq.coq list -> Coq.coqtop list
val cfg_algebraic :
  (Ident.t * Typedtree.type_declaration) list ->
  Coq.coqtop list * Coq.coqtop list
val cfg_type_decls :
  (Ident.t * Typedtree.type_declaration) list -> Coq.coqtops
val cfg_structure : Typedtree.structure -> Formula.cftop list
val cfg_signature_item : Typedtree.signature_item -> Coq.coqtops
val cfg_signature : Typedtree.signature -> Coq.coqtop list
val cfg_modtype : Ident.t -> Typedtree.module_type -> Formula.cftops
val cfg_module : Ident.t -> Typedtree.module_expr -> Formula.cftops

*)

(* The Boolean parameter is [no_mystd_include]; it is [true] if
   -nostdlib was supplied on the command line. *)
val cfg_file : bool -> Typedtree.structure -> Formula.cftop list

