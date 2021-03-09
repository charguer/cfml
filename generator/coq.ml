open Mytools

(** This file contains facilities for representing Coq expressions. Most of
    the core language is supported. A subset of the top-level declarations
    are supported. *)

(*#########################################################################*)
(* ** Syntax of Coq expressions *)

(** Coq variables and paths *)

type var = string
and vars = var list

and typed_var = var * coq
and typed_vars = typed_var list

and coq_path =
  | Coqp_var of var
  | Coqp_dot of coq_path * string

(** Coq expressions *)

and coq =
  | Coq_var of var
  | Coq_nat of int
  | Coq_int of int
  | Coq_app of coq * coq
  | Coq_impl of coq * coq
  | Coq_lettuple of coqs * coq * coq
  | Coq_forall of typed_var * coq
  | Coq_fun of typed_var * coq
  | Coq_wild
  | Coq_prop
  | Coq_type
  | Coq_tuple of coqs
  | Coq_record of (var * coq) list
  | Coq_tag of string * coq list * string option * coq
  | Coq_annot of coq * coq
(* DEPRECATED ; maybe future ?  | Coq_list of coq list *)

and coqs = coq list

(** Toplevel declarations *)

type coqtop =
  | Coqtop_def of typed_var * coq
  | Coqtop_param of typed_var
  | Coqtop_instance of typed_var * bool
  | Coqtop_lemma of typed_var
  | Coqtop_proof of string
  | Coqtop_ind of coqind list
  | Coqtop_record of coqind
  | Coqtop_label of var * int
  | Coqtop_implicit of var * (var * implicit) list
  | Coqtop_register of string * var * var
  (* todo: factorize the 3 type of hints into a single constructor *)
  | Coqtop_hint_constructors of vars * var
  | Coqtop_hint_resolve of vars * var
  | Coqtop_hint_unfold of vars * var
  | Coqtop_require of vars
  | Coqtop_import of vars
  | Coqtop_require_import of vars
  | Coqtop_set_implicit_args
  | Coqtop_text of string
  | Coqtop_declare_module of var * mod_typ
  | Coqtop_module of var * mod_bindings * mod_cast * mod_def
  | Coqtop_module_type of var * mod_bindings * mod_def
  | Coqtop_module_type_include of var
  | Coqtop_end of var
  | Coqtop_custom of string

and coqtops = coqtop list

(** Modules and signatures *)

and mod_cast =
   | Mod_cast_exact of mod_typ
   | Mod_cast_super of mod_typ
   | Mod_cast_free

and mod_def =
   | Mod_def_inline of mod_expr
   | Mod_def_declare

and mod_typ =
   | Mod_typ_var of var
   | Mod_typ_app of vars
   | Mod_typ_with_def of mod_typ * var * coq
   | Mod_typ_with_mod of mod_typ * var * var

and mod_expr = vars

and mod_binding = vars * mod_typ

and mod_bindings = mod_binding list

(** Inductive definitions *)

and coqind = {
   coqind_name : var;
   coqind_constructor_name : var;
   coqind_targs : typed_vars;
   coqind_ret : coq;
   coqind_branches : typed_vars; }

(** Implicit Arguements declarations *)

and implicit =
  | Coqi_maximal
  | Coqi_implicit
  | Coqi_explicit


(*#########################################################################*)
(* ** Helper functions to construct expressions *)

(** Several Coq constants *)

let coq_false =
  Coq_var "Coq.Init.Logic.False"

let coq_true =
  Coq_var "Coq.Init.Logic.True"

let coq_bool_false =
  Coq_var "Coq.Init.Datatypes.false"

let coq_bool_true =
  Coq_var "Coq.Init.Datatypes.true"

let coq_tt =
  Coq_var "Coq.Init.Datatypes.tt"

let coq_unit =
  Coq_var "Coq.Init.Datatypes.unit"

let coq_int =
  Coq_var "Coq.ZArith.BinInt.Z"

let coq_nat =
  Coq_var "Coq.Init.Datatypes.nat"

let coq_bool =
  Coq_var "Coq.Init.Datatypes.bool"

(** Identifier [x] *)

let coq_var x =
  Coq_var x

(** Disable implicit [@c] *)

let coq_at c =
  "@" ^ c

(** Identifier [@x] *)

let coq_var_at x =
  coq_at (coq_var x)

(** List of identifiers [x1 x2 .. xn] *)

let coq_vars xs =
  List.map coq_var xs

(** List of names [(A1:Type)::(A2::Type)::...::(AN:Type)::nil] *)

let coq_types names =
   List.map (fun n -> (n, Coq_type)) names

(** Application to a list of arguments [c e1 e2 .. eN] *)

let coq_app c1 c2 =
  Coq_app (c1, c2)

let coq_apps c args =
  List.fold_left coq_app c args

(** Application to wildcards [c _ _ .. _] *)

let coq_app_wilds c n =
   coq_apps c (list_make n Coq_wild)

(** Applications of an identifier to wildcars [x _ _ .. _] *)

let coq_app_var_wilds x n =
   if n = 0 then Coq_var x else coq_app_wilds (coq_var_at x) n

(** Applications of an at-identifier to arguments *)

let coq_app_var_at x args =
  if args = [] then Coq_var x else coq_apps (coq_var_at x) args

(** Function [fun (x1:T1) .. (xn:Tn) => c] *)

let coq_fun arg c =
  Coq_fun (arg, c)

let coq_funs args c =
  List.fold_right coq_fun args c

(** Function [fun (x1:Type) .. (xn:Type) => c] *)

let coq_fun_types names c =
  coq_funs (coq_types names) c

(** Let binding [let (x:T) := t1 in t2]
TODO
let coq_foralls args c =
  List.fold_right (fun ci acc -> Coq_forall (ci, acc)) args c

 *)

(** Universal [forall (x1:T1) .. (xn:Tn), c] *)

let coq_forall arg c =
  Coq_forall (arg, c)

let coq_foralls args c =
  List.fold_right coq_forall args c

(** Universal [forall (x1:Type) .. (xn:Type), c] *)

let coq_forall_types names c =
  coq_foralls (coq_types names) c

(** Universal [forall (x1:_) .. (xn:_), c] *)

let coq_foralls_wild names c =
  coq_foralls (List.map (fun n -> (n, Coq_wild)) names) c

(** Implication [c1 -> c2 -> .. -> cn -> c] *)

let coq_impl c1 c2 =
  Coq_impl (c1,c2)

let coq_impls cs c =
  List.fold_right (fun ci acc -> Coq_impl (ci, acc)) cs c

(** Implication [Type -> Type -> .. -> Type] *)

let coq_impl_types n =
   coq_impls (list_make n Coq_type) Coq_type

(** Predicate type [A->Prop] *)

let coq_pred c =
  Coq_impl (c, Coq_prop)

(** Product type [(c1 * c2 * .. * cN)%type] *)

let coq_prod cs =
  match cs with
  | [] -> coq_unit
  | [c] -> c
  | c0::cs' -> List.fold_left (fun acc c -> coq_apps (Coq_var "Coq.Init.Datatypes.prod") [acc;c]) c0 cs'

(** List [c1 :: c2 :: .. :: cN] *)

let coq_list xs =
   let ccons = Coq_var (Renaming.get_builtin_constructor "::") in
   let cnil = Coq_var (Renaming.get_builtin_constructor "[]") in
   List.fold_right (fun arg acc ->
      coq_apps ccons [arg; acc]) xs cnil
   (* DEPRECATED ; maybe future ?
   let coq_list xs =
     Coq_list xs
   *)
   (* DEPRECATED
   let ccons = get_builtin_constructor "::" in
   let cnil = get_builtin_constructor "[]" in
   let cnil = "Coq.Lists.List.nil" in
   let ccons = "Coq.Lists.List.cons" in
   *)

(** Logic combinators *)

let coq_eq c1 c2 =
  coq_apps (Coq_var "Coq.Init.Logic.eq") [ c1; c2 ]

let coq_neq c1 c2 =
  coq_apps (Coq_var "Coq.Init.Logic.not") [coq_eq c1 c2]

let coq_disj c1 c2 =
  coq_apps (Coq_var "Coq.Init.Logic.or") [c1; c2]

let coq_conj c1 c2 =
  coq_apps (Coq_var "Coq.Init.Logic.and") [c1; c2]

let coq_neg c =
  Coq_app (Coq_var "TLC.LibBool.neg", c)

let coq_exist x c1 c2 =
  coq_apps (Coq_var "Coq.Init.Logic.ex") [Coq_fun ((x, c1), c2)]

(** Iterated logic combinators *)

let coq_conjs cs =
  match List.rev cs with
  | [] -> Coq_var "true"
  | c::cs -> List.fold_left (fun acc ci -> coq_conj ci acc) c cs

let coq_exists xcs c2 =
  List.fold_right (fun (x,c) acc -> coq_exist x c acc) xcs c2

(** Arithmetic operations *)

let coq_le c1 c2 =
  coq_apps (Coq_var "TLC.LibOrder.le") [ c1; c2 ]

let coq_ge c1 c2 =
  coq_apps (Coq_var "TLC.LibOrder.ge") [ c1; c2 ]

let coq_lt c1 c2 =
  coq_apps (Coq_var "TLC.LibOrder.lt") [ c1; c2 ]

let coq_gt c1 c2 =
  coq_apps (Coq_var "TLC.LibOrder.gt") [ c1; c2 ]

let coq_plus c1 c2 =
  coq_apps (Coq_var "Coq.ZArith.BinInt.Zplus") [ c1; c2 ]

let coq_minus c1 c2 =
  coq_apps (Coq_var "Coq.ZArith.BinInt.Zminus") [ c1; c2 ]

(** Toplevel *)

let coqtop_def_untyped x c =
   Coqtop_def ((x,Coq_wild), c)

let coqtop_noimplicit x =
   Coqtop_implicit (x,[])

let coqtop_register db x v =
   Coqtop_register (db, x, v)


(*#########################################################################*)
(* ** Representation of labels (notation of the form "'x" := `1`0`1`0) *)

(** --todo: deprecated *)

type label = string

let var_bits_of_int n =
   let rec repr n =
     if n < 2 then [] else (1+(n mod 2))::(repr (n/2)) in
   List.rev (0::(repr n))

let string_of_var_bits vb =
  show_listp (fun b -> string_of_int b) "`" vb

let value_variable n =
  string_of_var_bits (var_bits_of_int n)

let coq_tag (tag : string) ?args ?label (term : coq) =
   let args = match args with | None -> [] | Some args -> args in
   Coq_tag ("CFML.CFPrint." ^ tag, args, label, term)
   (* TODO DEPRECATED *)

let coq_annot (term : coq) (term_type : coq)  =
   Coq_annot (term, term_type)

