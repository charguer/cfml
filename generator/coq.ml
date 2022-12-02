
let list_make n v =
  List.init n (fun _ -> v)

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
  | Coq_string of string
  | Coq_app of coq * coq
  | Coq_impl of coq * coq
  | Coq_lettuple of coqs * coq * coq
  | Coq_forall of typed_var * coq
  | Coq_fun of typed_var * coq
  | Coq_fix of var * int * coq * coq
     (* the int is the number of "fun" in the body,
        the first coq is the return type,
        the second coq is the body *)
  | Coq_wild
  | Coq_prop
  | Coq_type
  | Coq_tuple of coqs
  | Coq_record of (var * coq) list
  | Coq_proj of var * coq
  | Coq_if of bool(*classical or not*) * coq * coq * coq
  | Coq_match of coq * (coq * coq) list
  | Coq_tag of string * coq list * string option * coq
  | Coq_annot of coq * coq
  | Coq_par of coq
(* DEPRECATED ; maybe future ?  | Coq_list of coq list *)

and coqs = coq list

(** Toplevel declarations *)

type coqtop =
  | Coqtop_def of typed_var * coq
  | Coqtop_param of typed_var
  | Coqtop_instance of typed_var * coq option * bool
  | Coqtop_lemma of typed_var
  | Coqtop_proof of string
  | Coqtop_ind of coqind list
  | Coqtop_record of coqind
  (* DEPRECATED? | Coqtop_label of var * int *)
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
  | Coqtop_section of var
  | Coqtop_context of typed_vars

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
(* ** Smart constructors for toplevel definitions *)

(** Toplevel *)

let coqtop_def_untyped x c =
   Coqtop_def ((x,Coq_wild), c)

let coqtop_noimplicit x =
   Coqtop_implicit (x,[])

let coqtop_register db x v =
   Coqtop_register (db, x, v)

let coqtops_section_context sname xs ts =
    [ Coqtop_section sname;
      Coqtop_context xs ]
  @ ts
  @ [ Coqtop_end sname ]


(*#########################################################################*)
(* ** Smart constructors for variables *)

(** Identifier [x] *)

let coq_var x =
  Coq_var x

(** List of identifiers [x1 x2 .. xn] *)

let coq_vars xs =
  List.map coq_var xs

(** Identifier [@x] *)

let coq_var_at x =
  coq_var ("@" ^ x)

(** Identifier [@c], where [c] is a [Coq_var] *)

let coq_at c =
  match c with
  | Coq_var x -> Coq_var ("@" ^ x)
  | _ -> failwith "coq_at applied to a non-variable"

(** Wildcard [_] *)

let coq_wild =
  Coq_wild

(* CFML Identifier ---TODO: move elsewhere? *)

let coq_cfml_var x = (* TODO: there are places where it's not yet used *)
  coq_var ("CFML." ^ x)



(*#########################################################################*)
(* ** Smart constructors for applications *)

(** Application [c1 c2] *)

let coq_app c1 c2 =
  Coq_app (c1, c2)

(** Application [c c1 c2 ... cn] *)

let coq_apps c args =
  List.fold_left coq_app c args

(** Application [c0 c1 c2] *)

let coq_app_2 c0 c1 c2 =
  coq_apps c0 [ c1; c2 ]

(** Application [x c] *)

let coq_app_var x c =
  coq_app (coq_var x) c

(** Application [x c1 c2 .. cn] *)

let coq_apps_var x args =
  coq_apps (coq_var x) args

(** Application to wildcards [c _ _ .. _] *)

let coq_app_wilds c n =
   coq_apps c (list_make n Coq_wild)

(** Applications of an identifier to wildcars [x _ _ .. _] *)

let coq_app_var_wilds x n =
   if n = 0 then Coq_var x else coq_app_wilds (coq_var_at x) n

(** Applications of an at-identifier to arguments [@x c1 .. cn] *)

let coq_app_var_at x args =
  if args = [] then Coq_var x else coq_apps (coq_var_at x) args


(*#########################################################################*)
(* ** Helper functions *)

(** List of types [(A1:Type)::(A2::Type)::...::(AN:Type)::nil] *)

let coq_types names =
   List.map (fun n -> (n, Coq_type)) names


(*#########################################################################*)
(* ** Smart constructors for structure *)

(** Annotation *)

let coq_annot (term : coq) (term_type : coq)  =
   Coq_annot (term, term_type)

(** Function [fun (x:t) => c] where [arg] is the pair [(x,t)] *)

let coq_fun arg c =
  Coq_fun (arg, c)

(** Function [fun (x1:T1) .. (xn:Tn) => c] *)

let coq_funs args c =
  List.fold_right coq_fun args c

(** Recursive function [fix f (x1:T1) .. (xn:Tn) : Tr => c]
    represented as [Coq_fix f n Tr body] where [body] is the
    representation of [fun (x1:T1) .. (xn:Tn) => c]. *)

let coq_fixs f args crettype c =
  Coq_fix (f, List.length args, crettype, coq_funs args c)

(* Matching [match v with p1 => c1 | .. | pn => cn *)

let coq_match carg branches =
  Coq_match (carg, branches)

(** Function [fun (x1:Type) .. (xn:Type) => c] *)

let coq_fun_types names c =
  coq_funs (coq_types names) c

(** Conditionals *)

let coq_if_bool c0 c1 c2 =
  Coq_if (false, c0, c1, c2)

let coq_if_prop c0 c1 c2 =
  Coq_if (true, c0, c1, c2)


(** Let binding [let (x:T) := t1 in t2]
TODO
let coq_foralls args c =
  List.fold_right (fun ci acc -> Coq_forall (ci, acc)) args c

 *)

(*#########################################################################*)
(* ** Smart constructors for quantifiers *)

(** Existential [exists (x:c1), c2] *)

let coq_exist x c1 c2 =
  coq_apps (Coq_var "Coq.Init.Logic.ex") [coq_fun (x, c1) c2]

(** Existential [exists (x1:T1) .. (xn:Tn), c] *)

let coq_exists xcs c2 =
  List.fold_right (fun (x,c) acc -> coq_exist x c acc) xcs c2

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

(** Implication [c1 -> c2] *)

let coq_impl c1 c2 =
  Coq_impl (c1,c2)

(** Implication [c1 -> c2 -> .. -> cn -> c] *)

let coq_impls cs c =
  List.fold_right (fun ci acc -> Coq_impl (ci, acc)) cs c


(*#########################################################################*)
(* ** Smart constructors for types *)

let coq_typ_type =
  Coq_type

let coq_typ_unit =
  Coq_var "Coq.Init.Datatypes.unit"

let coq_typ_bool =
  Coq_var "Coq.Init.Datatypes.bool"

let coq_typ_int =
  Coq_var "Coq.ZArith.BinInt.Z"

let coq_typ_z =
  coq_typ_int

let coq_typ_string =
  Coq_var "Coq.Strings.String.string"

let coq_typ_nat =
  Coq_var "Coq.Init.Datatypes.nat"

(** Predicate type [A->Prop] *)

let coq_pred c =
  Coq_impl (c, Coq_prop)

(** Product type [(c1 * c2)%type] *)

let coq_prod c1 c2 =
  coq_apps (Coq_var "Coq.Init.Datatypes.prod") [c1;c2]

(** Product type [(c1 * c2 * .. * cN)%type], or [unit] if the list is empty *)

let coq_prods cs =
  match cs with
  | [] -> coq_typ_unit
  | [c] -> c
  | c0::cs' -> List.fold_left (fun acc c -> coq_prod acc c) c0 cs'

let coq_tuple =
  coq_prods

(** Implication [Type -> Type -> .. -> Type] *)

let coq_impl_types n =
   coq_impls (list_make n Coq_type) Coq_type


(*#########################################################################*)
(* ** Smart constructors for constants *)

let coq_prop_false =
  Coq_var "Coq.Init.Logic.False"

let coq_prop_true =
  Coq_var "Coq.Init.Logic.True"

let coq_tt =
  Coq_var "Coq.Init.Datatypes.tt"

let coq_bool_false =
  Coq_var "Coq.Init.Datatypes.false"

let coq_bool_true =
  Coq_var "Coq.Init.Datatypes.true"

let coq_nat n =
  Coq_nat n

let coq_int n =
  Coq_int n

let coq_string s =
  Coq_string s

(** List [c1 :: c2 :: .. :: cN :: nil], with constructors optionally annotated with a type *)

let coq_list ?(typ : coq option) xs =
   let ccons = Coq_var ("Coq.Lists.List.cons") in
   let ccons, targs =
     match typ with
     | None -> ccons, []
     | Some typ -> (coq_at ccons), [typ]
     in
   let cnil = Coq_var ("Coq.Lists.List.nil") in
   List.fold_right (fun arg acc ->
      coq_apps ccons (targs@[arg; acc])) xs cnil


(*#########################################################################*)
(* ** Smart constructors for logical operators *)

let coq_eq =
  coq_var "Coq.Init.Logic.eq"

let coq_app_eq c1 c2 =
  coq_app_2 coq_eq c1 c2

let coq_neq = (* propositional negation *)
  coq_var "Coq.Init.Logic.not"

let coq_app_neq c1 c2 =
  coq_app_2 coq_neq c1 c2

let coq_disj =
  coq_var "Coq.Init.Logic.or"

let coq_app_disj c1 c2 =
  coq_app_2 coq_disj c1 c2

(* Iterated disjunction [c1 \/ c2 \/ .. \/ cn] or [False] if empty list of args *)

let coq_app_disjs cs =
  match List.rev cs with
  | [] -> coq_prop_false
  | c::cs -> List.fold_left (fun acc ci -> coq_app_disj ci acc) c cs

let coq_conj =
  coq_var "Coq.Init.Logic.and"

let coq_app_conj c1 c2 =
  coq_app_2 coq_conj c1 c2

(* Iterated conjunction [c1 /\ c2 /\ .. /\ cn] or [True] if empty list of args *)

let coq_app_conjs cs =
  match List.rev cs with
  | [] -> coq_prop_true
  | c::cs -> List.fold_left (fun acc ci -> coq_app_conj ci acc) c cs

let coq_neg = (* boolean negation *)
  coq_var "TLC.LibBool.neg"

let coq_app_neg c =
  coq_app coq_neg c


(*#########################################################################*)
(* ** Smart constructors for arithmetic operations *)

(* Nat operators *)

let coq_nat_succ =
  coq_var "Coq.Init.Datatypes.S"

let coq_nat_add =
  coq_var "Coq.Init.Nat.add"

let coq_nat_sub =
  coq_var "Coq.Init.Nat.sub"

let coq_nat_lt =
  coq_var "Coq.Init.Peano.lt"

let coq_nat_le =
  coq_var "Coq.Init.Peano.le"

let coq_nat_gt =
  coq_var "Coq.Init.Peano.gt"

let coq_nat_ge =
  coq_var "Coq.Init.Peano.ge"

(* Z operators *)

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


(*#########################################################################*)
(* ** Smart constructors for the [Semantics] file *)
(* TODO: move to some other file? *)

let pat_type = coq_cfml_var "Semantics.pat"

let trm_type = coq_cfml_var "Semantics.trm"

let val_type = coq_cfml_var "Semantics.val"

let val_constr = coq_cfml_var "Semantics.val_constr"


(*#########################################################################*)
(* ** Inversion functions *)
(* TODO: where is it used? *)

let rec coq_apps_inv c =
  (* LATER could reimplement using an accumulator *)
  match c with
  | Coq_app (c1,c2) ->
      let c0, cs = coq_apps_inv c1 in
      c0, (cs @ [c2])
  | _ -> c, []


(*#########################################################################*)
(* ** Representation of labels (notation of the form "'x" := `1`0`1`0) *)
(* TODO: DEPRECATED? *)
(** --

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
 *)

