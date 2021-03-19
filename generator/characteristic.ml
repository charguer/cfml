open Misc
open Asttypes
open Types
open Typedtree
open Mytools
open Longident
open Print_tast
open Print_type
open Formula
open Coq
open Path
open Renaming
open Printf


(*#########################################################################*)
(* ** Aux *)

(** [list_is_included l1 l2] returns true if any item in [l1] also belongs to [l2] *)

let list_is_included l1 l2 =
   List.for_all (fun x -> List.mem x l2) l1

(** [is_value_let_binding bod] tests if [bod] can be reflected as
    a LetVal or if it should be a LetTrm *)

let rec is_array exp =
  match exp.exp_desc with
  | Texp_array [] -> true
  | Texp_constraint (e, _, _) -> is_array e
  | _ -> false

let is_value_let_binding exp =
  Typecore.is_nonexpansive exp &&
  not (is_array exp)


(*#########################################################################*)
(* ** Error messages *)

exception Not_in_normal_form of Location.t * string

let not_in_normal_form loc s =
   raise (Not_in_normal_form (loc, s))


(*#########################################################################*)
(* ** List of external modules that need to be required *)

let external_modules = ref []

let external_modules_add name =
   if not (List.mem name !external_modules)
     then external_modules := name::!external_modules
   (* TODO: use a structure more efficient than lists *)

let external_modules_get_coqtop () =
   List.map (fun name -> Coqtop_require [name]) !external_modules

let external_modules_reset () =
   external_modules := []



(*#########################################################################*)
(* ** Lifting of paths *)

(* Take a module name and add "_ml" suffix to it;
   Moreover, insert a "Require" directive in case the module
   corresponds to a file (i.e. a compilation unit. *)

let lift_module_name id =
   let name = Ident.name id in
   let coqname = module_name name in
   if Ident.persistent id then external_modules_add coqname;
   coqname

   (* -- old:
     if Ident.persistent id
      then (let result = name ^ "_ml" in external_modules_add result; result)
      else "ML" ^ name
   *)
   (* -- old: if name = "OkaStream" then "CFPrim" else  *)

(* Function for adding "_ml" to the modules in a path,
   including the last constant which is assumed to a module name.
   For example, "Foo.Bar" becomes "Foo_ml.Bar_ml".

   TODO: rename this function *)


let rec lift_full_path = function
  | Pident id -> Pident (Ident.create (lift_module_name id))
  | Pdot(p, s, pos) -> Pdot(lift_full_path p, (module_name s), pos)
  | Papply(p1, p2) -> assert false

(* Function for adding "_ml" to the modules in a path,
   but not changing the last constant in the path.
   For example, "Foo.x" becomes "Foo_ml.x". *)

let lift_path = function
  | Pident id -> Pident id
  | Pdot(p, s, pos) -> Pdot(lift_full_path p, s, pos)
  | Papply(p1, p2) -> assert false

(** Translates a path into a string. A module called "Test"
    becomes "Test_ml". *)

let lift_full_path_name p =
  Path.name (lift_full_path p)

(** Translates a path into a string --todo: why not full? *)

let lift_path_name p =
  Path.name (lift_path p)


(*#########################################################################*)
(* ** Lifting of types *)

(** Computes the free variables of a [btyp] *)

let rec fv_btyp ?(through_arrow = true) t =
   let aux = fv_btyp in
   match t with
   | Btyp_val -> []
   | Btyp_arrow (t1,t2) -> if through_arrow then aux t1 @ aux t2 else []
   | Btyp_constr (id,ts) -> list_concat_map aux ts
   | Btyp_tuple ts -> list_concat_map aux ts
   | Btyp_var (s,ty) -> typvar_mark_used ty; [s]
   | Btyp_poly (ss,t) -> unsupported_noloc "poly-types"
   | Btyp_alias (t,s) -> s :: aux t

(** Translates a [btyp] into a Coq type *)

let rec lift_btyp loc t =
   let aux = lift_btyp loc in
   match t with
   | Btyp_val ->
      func_type
   | Btyp_arrow (t1,t2) ->
      func_type
   (* DEPRECATED
   | Btyp_constr (id,[t]) when Path.name id = "array" ->
      loc_type *)
   | Btyp_constr (id,ts) ->
      coq_apps (Coq_var (type_constr_name (lift_path_name id))) (List.map aux ts)
   | Btyp_tuple ts ->
      coq_prod (List.map aux ts)
   | Btyp_var (s,ty) ->
      typvar_mark_used ty;
      Coq_var s
      (* DEPRECATED
      if b then unsupported loc ("non-generalizable free type variables (of the form '_a); please add a type annotation if the type is not polymorphic; if it is, then ask to get the typechecker patched for propagating the annotation. var=" ^ s);
       let s = if b then "__" ^ s else s in *)
   | Btyp_poly (ss,t) ->
      unsupported_noloc "poly-types"
   | Btyp_alias (t1,s) ->
      let occ = fv_btyp ~through_arrow:false t1 in
      if List.mem s occ
        then unsupported_noloc ("found a recursive type that is not erased by an arrow:" ^ (print_out_type t));
      aux t1

(* TEMPORARILY DEPRECATED

   | Btyp_constr (id,[t]) when Path.name id = "ref" || Path.name id = "Pervasives.ref" ->
      loc_type

   | Btyp_constr (id,[t]) when Path.name id = "heap" || Path.name id = "Heap.heap" ->
      loc_type

   | Btyp_constr (id,[t]) when Path.same id Predef.path_lazy_t || Path.name id = "Lazy.t" ->
      aux t
   | Btyp_constr (id,[t]) when Path.name id = "Stream.stream" || Path.name id = "stream" ->
      Coq_app (Coq_var "list", aux t)
   | Btyp_constr (id,[t]) when Path.name id = "Stream.stream_cell" || Path.name id = "stream_cell" ->
      Coq_app (Coq_var "list", aux t)
*)
(* REMARK: les Lazy provenant des patterns ne sont pas identique Predef.path_lazy_t *)


(** Translates a Caml type into a Coq type *)

let lift_typ_exp loc ty =
  lift_btyp loc (btyp_of_typ_exp ty)

(** Translates a Caml type scheme into a Coq type *)

let lift_typ_sch loc ty =
   let t = btyp_of_typ_sch_simple ty in
   let fv = fv_btyp ~through_arrow:false t in
   fv, lift_btyp loc t

let lift_typ_sch_as_forall loc ty =
   let fv, typ = lift_typ_sch loc ty in
   coq_forall_types fv typ

(** Translates the type of a Caml expression into a Coq type *)

let coq_typ loc e =
   lift_typ_exp loc (e.exp_type)

(** Translates the type of a Caml pattern into a Coq type *)

let coq_typ_pat loc p =
   lift_typ_exp loc (p.pat_type)

(** Decompose "A.B.s" as ("A.B","s") *)

let rec path_decompose = function
    Pident id -> ("", Ident.name id)
  | Pdot(p, s, pos) ->
      let (f,r) = path_decompose p in
      (f ^ r ^ ".", s)
  | Papply(p1, p2) -> unsupported_noloc "application in paths"


(** Extracts a record path_name / path from a type *)

let get_record_decomposed_name_for_exp e =
   let b = btyp_of_typ_exp (e.exp_type) in
   match b with
   | Btyp_constr (p,_) -> path_decompose (lift_path p)
   | _ -> failwith "illegal argument for get_record_decomposed_name_for_exp"



(*#########################################################################*)
(* ** Type arity functions *)

(** Get the number of type arguments of a (polymorphic) free variable *)

let typ_arity_var env x =
   match x with
   | Path.Pident id ->
      begin try Ident.find_same id env
      with Not_found -> 0 end
   | _ -> 0

(** Get the number of type arguments of a (polymorphic) data constructor *)

let typ_arity_constr c =
   match (c.cstr_res).desc with
   | Tconstr (_,ts,_) -> List.length ts
   | _ -> failwith "typ_arity_constr: result type of constructor is not a type constructor"

(** Translate a Caml data constructor into a Coq expression *)

(* DEPRECATED: attempt to type the constructor is problematic,
   because the type [ty] might not have a type constructor
   that is the one from the definition of the constructor. E.g.
     type 'a t = A of 'a
     type 'a mylist = 'a t list
     let empty : 'a mylist = []  ---> this is not 'a list.

  let coq_of_constructor_DEPRECATED loc p c ty =
     let typs =
        match btyp_of_typ_exp ty with
        | Btyp_constr (id,ts) -> List.map (lift_btyp loc) ts
        | _ -> failwith "coq_of_constructor: constructor has a type that is not a type constructor"
        in
     let x = string_of_path p in
     (* TODO: fixme, this can be hacked by rebinding None, Some, or :: ..*)
     let coq_name, arity =
        match find_builtin_constructor x with
        | None -> lift_path_name p, (typ_arity_constr c)
        | Some (coq_name,arity) -> coq_name, arity
        in
      if typs = []
        then coq_var coq_name
        else coq_apps (coq_var_at coq_name) typs
     (* DEPRECATED: coq_app_var_wilds coq_name arity *)

   | Tpat_construct (path, c, ps) ->
      coq_apps (coq_of_constructor loc path c p.pat_type) (List.map aux ps)
   | Texp_construct (p, c, es) ->
      coq_apps (coq_of_constructor loc p c e.exp_type) (List.map aux es)

*)

let coq_of_constructor loc p c args ty =
   let x = string_of_path p in
   let coq_name, _arity =
      match find_builtin_constructor x with
      | None -> lift_path_name p, (typ_arity_constr c)
      | Some (coq_name,arity) -> coq_name, arity
      in
  let constr = coq_var coq_name in
  let typ = lift_typ_exp loc ty in
  coq_annot (coq_apps constr args) typ


(*#########################################################################*)
(* ** Lifting of patterns *)

(** Compute the free variables of a pattern *)

let rec pattern_variables p : typed_vars = (* ignores aliases *)
   let loc = p.pat_loc in
   let aux = pattern_variables in
   match p.pat_desc with
   | Tpat_any -> not_in_normal_form loc "wildcard patterns remain after normalization"
   | Tpat_var s -> [var_name (Ident.name s), coq_typ_pat loc p]
   | Tpat_alias (p, s) -> aux p
   | Tpat_constant c -> []
   | Tpat_tuple l -> list_concat_map aux l
   | Tpat_construct (p, c, ps) -> list_concat_map aux ps
   | Tpat_lazy p1 -> aux p1
   | Tpat_variant (_,_,_) -> unsupported loc "variant patterns"
   | Tpat_record _ -> unsupported loc "record patterns"
   | Tpat_array pats -> unsupported loc "array patterns"
   | Tpat_or (_,p1,p2) -> unsupported loc "or patterns"

(** Translate a Caml pattern into a Coq expression, and
    ignores the aliases found in the pattern *)

let rec lift_pat ?(through_aliases=true) p : coq =
   let loc = p.pat_loc in
   let aux = lift_pat ~through_aliases:through_aliases in
   match p.pat_desc with
   | Tpat_var s ->
      Coq_var (var_name (Ident.name s))
   | Tpat_constant (Const_int n) ->
      Coq_int n
   | Tpat_tuple l ->
      Coq_tuple (List.map aux l)
   | Tpat_construct (path, c, ps) ->
      coq_of_constructor loc path c (List.map aux ps) p.pat_type
   | Tpat_alias (p, ak) ->
      begin match ak with
      | TPat_alias id ->
          if through_aliases then aux p else Coq_var (var_name (Ident.name id))
      | TPat_constraint ty ->
          let typ = lift_typ_exp loc ty.ctyp_type in
          Coq_annot (aux p, typ)
      | TPat_type pp -> aux p
      end
   | Tpat_lazy p1 ->
      aux p1
   | Tpat_record _ -> unsupported loc "record patterns" (* todo! *)
   | Tpat_array pats -> unsupported loc "array patterns" (* todo! *)
   | Tpat_constant _ -> unsupported loc "only integer constant are supported"
   | Tpat_any -> not_in_normal_form loc "wildcard patterns remain after normalization"
   | Tpat_variant (_,_,_) -> unsupported loc "variant patterns"
   | Tpat_or (_,p1,p2) -> unsupported loc "or patterns in depth"

(** Extracts the aliases from a Caml pattern, in the form of an
    association list mapping variables to Coq expressions *)

let pattern_aliases p : (typed_var*coq) list =
   let loc = p.pat_loc in
   let rec aux p =
      match p.pat_desc with
      | Tpat_var s -> []
      | Tpat_constant (Const_int n) -> []
      | Tpat_tuple l -> list_concat_map aux l
      | Tpat_construct (p, c, ps) -> list_concat_map aux ps
      | Tpat_alias (p1, ak) ->
          begin match ak with
          | TPat_alias id ->
             ((Ident.name id, coq_typ_pat loc p), lift_pat ~through_aliases:false p1) :: (aux p1)
          | TPat_constraint _ -> aux p1
          | TPat_type pp -> aux p1
         end
      | Tpat_lazy p1 ->  aux p1
      | Tpat_record _ -> unsupported loc "record patterns" (* todo! *)
      | Tpat_array pats -> unsupported loc "array patterns" (* todo! *)
      | Tpat_constant _ -> unsupported loc "only integer constant are supported"
      | Tpat_any -> not_in_normal_form loc "wildcard patterns remain after normalization"
      | Tpat_variant (_,_,_) -> unsupported loc "variant patterns"
      | Tpat_or (_,p1,p2) -> unsupported loc "or patterns"
      in
   List.rev (aux p)


(*#########################################################################*)
(* ** Helper functions for various things *)

let register_cf x =
   Coqtop_custom (sprintf "Hint Extern 1 (WPHeader_Register_CF %s) => WPHeader_Provide %s." x (cf_axiom_name x))
   (* DEPRECATED
      Coqtop_register ("CFML.CFPrint.database_cf", x, cf_axiom_name x)
    *)

let register_spec x v =
   Coqtop_register ("CFML.WPHeader.database_spec", x, v)


(* TODO: rewrite this function by using a normalization function that returns p *)
let rec prefix_for_label typ =
  match typ.desc with
  | Tconstr (p, _, _) -> lift_path_name p
  | Tlink t -> prefix_for_label t
  | _ -> failwith "string_of_label: type of a record should be a Tconstr or Tlink"
  (*
  | Tvar -> failwith "x1"
  | Tarrow _ -> failwith "x2"
  | Ttuple  _ -> failwith "x3"
  | Tconstr _ -> failwith "x4"
  | Tobject  _ -> failwith "x5"
  | Tfield _ -> failwith "x6"
  | Tnil _ -> failwith "x7"
  | Tsubst  _ -> failwith "x9"
  | Tvariant  _ -> failwith "x10"
  | Tunivar -> failwith "x11"
  | Tpoly  _ -> failwith "x12"
  *)

(* DEPRECATED
let string_of_label_with prefix lbl =
  prefix ^ "_" ^ lbl.lbl_name

let string_of_label typ lbl =
  string_of_label_with (prefix_for_label typ) lbl
*)


(*#########################################################################*)
(* ** Helper functions for primitive functions *)

let simplify_apply_args loc oargs =
  List.map (function (lab, Some e, Required) -> e | _ -> unsupported loc "optional arguments") oargs

let get_qualified_pervasives_name f =
   let name = Path.name f in
   if !Clflags.nopervasives
      then "Pervasives." ^ name  (* unqualified name when from inside Pervasives *)
      else name  (* qualified name otherwise *)

let exp_find_inlined_primitive e oargs =
   let loc = e.exp_loc in
   let args = simplify_apply_args loc oargs in
   match e.exp_desc with
   | Texp_ident (f,d) ->
      let name = get_qualified_pervasives_name f in

      let _debug() =
         Printf.printf "exp_find_inlined_primitive: %s\n arity: %d\n name: %s\n" (Path.name f) (List.length args) name
         in
      (* _debug(); *)

      begin match args with

      | [n; {exp_desc = Texp_constant (Const_int m)}]
           when m <> 0
             && List.mem name ["Pervasives.mod"; "Pervasives./"] ->
           begin match find_inlined_primitive name with
           | Some (Primitive_binary_div_or_mod, coq_name) -> Some coq_name
           | _ -> None
           end

       | [e1; e2]
           when List.mem name ["Pervasives.&&"; "Pervasives.||"] ->
           begin match find_inlined_primitive (Path.name f) with
           | Some (Primitive_binary_lazy, coq_name) -> Some coq_name
           | _ -> None
           end

       | [e1; e2]
           when List.mem name ["Pervasives.="; "Pervasives.<>"; "Pervasives.<=";
                               "Pervasives.>="; "Pervasives.<"; "Pervasives.>";
                               "Pervasives.min"; "Pervasives.max"; ] ->
           let is_number =
              try Ctype.unify e1.exp_env e1.exp_type ((*instance*) Predef.type_int); true
              with _ -> false
              (*begin match btyp_of_typ_exp e1.exp_type with
              | Btyp_constr (id,[]) when Path.name id = "int" -> true
              | _ -> false
              end *)
              in
             (* Remark: by typing, [e2] has the same type as [e1] *)
           if not is_number then begin
             if List.mem name [ "Pervasives.="; "Pervasives.<>"; ]
               then None
               (* TODO: improve using type unification *)
               else (* warning loc *)
               unsupported loc (Printf.sprintf "comparison operators on non integer arguments (here, %s)" (string_of_type_exp e1.exp_type));
           end else begin match find_inlined_primitive name with
              | Some (Primitive_binary_only_numbers, coq_name) -> Some coq_name
              | _ -> failwith ("in exp_find_inlined_primitive, could not find the coq translation of the function: " ^ name)
           end

       | _ ->
           let arity = List.length args in
           begin match find_inlined_primitive name with
           | Some (Primitive_unary, coq_name) when arity = 1 -> Some coq_name
           | Some (Primitive_binary, coq_name) when arity = 2 -> Some coq_name
           | _ -> None
           end
           (* debug: Printf.printf "exp_find_inlined_primitive: %s %d\n"  (Path.name f)  (List.length args);
           if r = None then Printf.printf "failed\n"; *)

       end

    | _ -> None



(*#########################################################################*)
(* ** Lifting of values *)

(** Translate a Caml identifier into a Coq identifier, possibly
    applied to wildcards for taking type applications into account *)

let lift_exp_path env p =
   match find_primitive (Path.name p) with
   | None ->
      let x = lift_path_name (var_path p) in
      coq_app_var_wilds x (typ_arity_var env p)
   | Some y ->
      Coq_var y

(** Translate a Caml value into a Coq value. Fails if the Coq
    expression provided is not a value. *)

let rec lift_val env e =
   let loc = e.exp_loc in
   let aux = lift_val env in
   let fail () =
     not_in_normal_form loc ("in liftval: " ^ Print_tast.string_of_expression false e) in
   match e.exp_desc with
   | Texp_ident (p,d) ->
     lift_exp_path env p
   | Texp_open (p, _) ->
     assert false
   | Texp_constant (Const_int n) ->
      Coq_int n
   | Texp_constant _ ->
      unsupported loc "only integer constant are supported"
   | Texp_tuple el ->
      Coq_tuple (List.map aux el)
   | Texp_construct (p, c, es) ->
      coq_of_constructor loc p c (List.map aux es) e.exp_type
   | Texp_record (l, opt_init_expr) ->
       if opt_init_expr <> None then unsupported loc "record-with expression"; (* todo *)
       if List.length l < 1 then failwith "record should have at least one field";
       let labels = ((fun (p,li,ei) -> li) (List.hd l)).lbl_all in
       let args = Array.make (Array.length labels) (Coq_var "dummy") in
       let register_arg lbl v =
          Array.iteri (fun i lbli -> if lbl.lbl_name = lbli.lbl_name then args.(i) <- v) labels in
       List.iter (fun (p,lbl,v) -> register_arg lbl (aux v)) l;
       let constr = record_constructor_name_from_type (prefix_for_label (e.exp_type)) in
       let typ_args =
          match btyp_of_typ_exp e.exp_type with
          | Btyp_constr (id,ts) -> List.map (lift_btyp loc) ts
          | _ -> failwith "record should have a type-constructor as type"
          in
       coq_apps (coq_var_at constr) (typ_args @ Array.to_list args)
   | Texp_apply (funct, oargs) ->
      let fo = exp_find_inlined_primitive funct oargs in
      let f = match fo with
         | Some f -> f
         | _ -> fail()
         in
      let args = simplify_apply_args loc oargs in
      coq_apps (Coq_var f) (List.map aux args)
   | Texp_lazy e ->
      aux e
   | Texp_constraint (e, Some ty, None) ->
      let typ = lift_typ_exp loc ty.ctyp_type in
      Coq_annot (aux e, typ)
   | _ -> fail()

   (* --uncomment for debugging
   | Texp_function _ -> not_in_normal_form loc "function"
   | Texp_apply _ -> not_in_normal_form loc "apply"
   | Texp_assertfalse -> not_in_normal_form loc "assert false"
   | Texp_try(body, pat_expr_list) -> not_in_normal_form loc "try expression"
   | Texp_variant(l, arg) ->  not_in_normal_form loc "variant expression"
   | Texp_setfield(arg, p, lbl, newval) -> not_in_normal_form loc "set-field expression"
   | Texp_array expr_list -> not_in_normal_form loc "array expressions"
   | Texp_ifthenelse(cond, ifso, None) -> not_in_normal_form loc "if-then-without-else expressions"
   | Texp_sequence(expr1, expr2) -> not_in_normal_form loc "sequence expressions"
   | Texp_while(cond, body) -> not_in_normal_form loc "while expressions"
   | Texp_for(param, low, high, dir, body) -> not_in_normal_form loc "for expressions"
   | Texp_when(cond, body) -> not_in_normal_form loc "when expressions"
   | Texp_send(_ , _, _) -> not_in_normal_form loc "send expressions"
   | Texp_new (cl, _) -> not_in_normal_form loc "new expressions"
   | Texp_instvar(path_self, path) -> not_in_normal_form loc "inst-var expressions"
   | Texp_setinstvar(path_self, path, expr) -> not_in_normal_form loc "set-inst-var expressions"
   | Texp_override(path_self, modifs) -> not_in_normal_form loc "override expressions"
   | Texp_letmodule(id, modl, body) -> not_in_normal_form loc "let-module expressions"
   | Texp_assert (cond) -> not_in_normal_form loc "assert expressions"
   | Texp_object (_, _) -> not_in_normal_form loc "object expressions"
   | Texp_poly _  -> not_in_normal_form loc "object expressions"
   | Texp_newtype _  -> not_in_normal_form loc "object expressions"
   | Texp_pack _  -> not_in_normal_form loc "object expressions"
   | Texp_let _ -> not_in_normal_form loc "let"
   | Texp_match _ -> not_in_normal_form loc "match"
   | Texp_field _ -> not_in_normal_form loc "field"
   *)

   (* --todo: could be a value in a purely-functional setting
   | Texp_field (e, lbl) ->
       let typ = e.exp_type in
       Coq_app (Coq_var (string_of_label typ lbl), aux e) *)


(*#########################################################################*)
(* ** Helper functions for producing label names *)

(* FOR FUTURE USE *)

let counter_local_label =
   ref 0
let get_next_local_label () =
   incr counter_local_label;
   "_m" ^ (string_of_int !counter_local_label)
let reset_local_labels() =
   counter_local_label := 0

let used_labels : (var list) ref =
   ref []
let reset_used_labels () =
   used_labels := []
let add_used_label x =
   if not (List.mem x !used_labels)
      then used_labels := x :: !used_labels

let cfg_extract_labels () =
   let labs = List.rev !used_labels in
   let cft = [ Cftop_coqs (list_mapi (fun i x -> Coqtop_label (x,i+1)) labs) ] in
   reset_used_labels();
   cft


(*#########################################################################*)
(* ** Helper functions for names *)

(** Takes a pattern that is expected to be reduced simply to an identifier,
    and returns this identifier *)

let rec pattern_ident p =
   match p.pat_desc with
   | Tpat_var s -> s
   | Tpat_alias (p1,_) -> pattern_ident p1
   | _ -> failwith ("pattern_ident: the pattern is not a name: " ^ (Print_tast.string_of_pattern false p))

(** Takes a pattern that is expected to be reduced simply to an identifier,
    and returns the name of this identifier *)

let pattern_name p =
   Ident.name (pattern_ident p)

(** Takes a function name and encodes its name in case of an infix operator *)

let pattern_name_protect_infix p =
   var_name (pattern_name p)

(** An alternative version of function extract_label_names, for obtaining record labels *)

let rec extract_label_names_simple env ty =
  let ty = Ctype.repr ty in
  match ty.desc with
  | Tconstr (path, _, _) ->
      let td = Env.find_type path env in
      begin match td.type_kind with
      | Type_record (fields, _) ->
          List.map (fun (name, _, _) -> name) fields
      | Type_abstract when td.type_manifest <> None ->
          unsupported_noloc "building of a record with abstract type"
      | _ -> assert false
      end
  | _ -> assert false


(*#########################################################################*)
(* ** Helper functions for fvs (type variables) *)


let show_fvs title fvs =
   Format.fprintf Format.err_formatter "%s = %s\n" title (show_list show_str " , " fvs)

(* needs to be called only after typing the body of the definition
   associated with the pattern, so as to know which names are actually used. *)

let get_fvs_typ loc fvs typ =
  let typ = lift_typ_exp loc typ in
  let fvs = List.map name_of_type_var (List.filter typvar_is_used fvs) in
  (fvs, [], typ)

  (* DEPRECATED
  let fvs_typ, typ = lift_typ_sch loc typ in
  let fvs = List.map name_of_type_var (List.filter typvar_is_used fvs) in
  if Settings.debug_generic then begin
     show_fvs "fvs_typ" fvs_typ;
     show_fvs "fvs" fvs;
  end;
  if not (list_is_included fvs_typ fvs)
    then failwith "fvs_typ not included in fvs for let binding";
  let fvs_strict = fvs_typ in
  let fvs_others = list_minus fvs fvs_strict in
  (fvs_strict, fvs_others, typ)
  *)


(*#########################################################################*)
(* ** Characteristic formulae for expressions *)

(** Translate a Caml expression into its Coq characteristic formula *)

let rec cfg_exp env e =
   let loc = e.exp_loc in
   let aux = cfg_exp env in
   let lift e = lift_val env e in
   let ret e = Cf_val (lift e) in
   let not_normal ?s:(s="") () =
      not_in_normal_form loc (s ^ Print_tast.string_of_expression false e) in
   match e.exp_desc with
   | Texp_ident (x,d) -> ret e
   | Texp_open (p, {exp_desc = Texp_ident _}) -> assert false
   | Texp_constant cst -> ret e
   | Texp_tuple el -> ret e
   | Texp_construct(p, cstr, args) -> ret e
   (* TODO: only in purely function setting:   | Texp_record (lbl_expr_list, opt_init_expr) -> ret e*)

   | Texp_record (_, _) ->
     cfg_record env e

   | Texp_apply (funct, oargs) when (exp_find_inlined_primitive funct oargs <> None) -> ret e

   | Texp_function (_, pat_expr_list, partial) -> not_normal ~s:"The function involved has not been lifted properly during normalization;\n check the normalized file in _output folder.\n" ()

   | Texp_let(rf, fvs, pat_expr_list, body) ->

      let is_let_fun =
         match (snd (List.hd pat_expr_list)).exp_desc with
         | Texp_function (_,_,_) -> true
         | Texp_constraint ({exp_desc = Texp_function (_,_,_)},_,_) -> true (* todo: generalize *)
         | _ -> false in

      let is_let_record_new =
         match (snd (List.hd pat_expr_list)).exp_desc with
         | Texp_record (_,_) -> true
         | Texp_constraint ({exp_desc = Texp_record (_,_)},_,_) -> true (* todo: generalize *)
         | _ -> false in

      (* binding of functions, possibly mutually-recursive *)
      if is_let_fun then begin
        let env' = match rf with
           | Nonrecursive -> env
           | Recursive -> env
              (* --todo: add better support for local polymorphic recursion
              List.fold_left (fun (pat,bod) acc -> Ident.add (pattern_ident pat) 0 acc) env pat_expr_list *)
           | Default -> unsupported loc "Default recursion mode"
           in
        let ncs = List.map (fun (pat,bod) -> (pattern_name_protect_infix pat, cfg_func env' fvs pat bod)) pat_expr_list in
        let cf_body = cfg_exp env' body in
        add_used_label (fst (List.hd ncs));
        Cf_let_fun (ncs, cf_body)
        (* --todo: check what happens with recursive types *)

      (* let-binding of a single value *)
      end else begin
        if (List.length pat_expr_list <> 1) then not_normal();
        let (pat,bod) = List.hd pat_expr_list in
        let x = pattern_name_protect_infix pat in

        (* value let-binding *)
        if is_value_let_binding bod then begin

           let v =
             try lift_val env bod
             with Not_in_normal_form (loc2, s) ->
                raise (Not_in_normal_form (loc2, s ^ " (only value can satisfy the value restriction TODO1)"))
             in
           let (fvs_strict, fvs_others, typ) = get_fvs_typ loc fvs pat.pat_type in
           if fvs_others != []
              then unsupported loc "polymorphic let-value binding whose type-checking involves type variables that are not contained in the result type.";
           let env' = Ident.add (pattern_ident pat) (List.length fvs_strict) env in
           let cf = cfg_exp env' body in
           add_used_label x;
           Cf_let_val (x, fvs_strict, typ, v, cf)

        (* term let-binding *)
        end else begin

           (* DEPRECATED
              if fvs = [] then begin
                 (* Simple form without polymorphism *)
                 let cf1 = cfg_exp env bod in
                 let typ = lift_typ_exp loc pat.pat_type in
                 let env' = Ident.add (pattern_ident pat) 0 env in
                 let cf2 = cfg_exp env' body in
                 add_used_label x;
                 Cf_let ((x,typ), cf1, cf2)
              end else
              (* General form with polymorphism *)
           *)

            begin

              let cf1 =
                (* Recursive record term let-binding *)
                if is_let_record_new && rf = Recursive then
                  cfg_record ~record_name:x env bod
                else
                  cfg_exp env bod
              in
              let fvs_typ, typ = lift_typ_sch loc pat.pat_type in
              (* fvs_typ contains all free type variables in the type;
                 and thus too many w.r.t. to the ones of interest here *)
              let fvs = List.map name_of_type_var (List.filter typvar_is_used fvs) in
              let fvs_strict = list_intersect fvs fvs_typ in
              let fvs_others = list_minus fvs fvs_strict in
              let env' = Ident.add (pattern_ident pat) (List.length fvs_strict) env in
              let cf2 = cfg_exp env' body in
              add_used_label x;
              if fvs_strict = [] && fvs_others = []
                then Cf_let ((x,typ), cf1, cf2)
                else Cf_let_poly (x, fvs_strict, fvs_others, typ, cf1, cf2)

                  (* DEPRECATED
                     Printf.printf "fvs_strict = %s\n" (show_list show_str " , " fvs_strict);
                     Printf.printf "fvs_others = %s\n" (show_list show_str " , " fvs_others);
                     unsupported loc "relaxed value restriction";
                     not_in_normal_form loc ("(un value restriction) "
                        ^ (Print_tast.string_of_expression false e));*)
           end;


        end
      end

   | Texp_ifthenelse (cond, ifso, Some ifnot) ->
      (* old: Cf_if (aux cond, aux ifso, aux ifnot) *)
      Cf_if (lift cond, aux ifso, aux ifnot)

   | Texp_apply (funct, oargs) ->
      let args = simplify_apply_args loc oargs in
      let tr = coq_typ loc e in
      let ts = List.map (coq_typ loc) args in
      Cf_app (ts, tr, lift funct, List.map lift args)

   | Texp_match (arg, pat_expr_list, partial) ->
      let tested = lift arg in
      let conclu = match partial with Partial -> Cf_fail | Total -> Cf_done in
      let cfg_case (pat,body) acc =
         let whenopt, cfbody =
            match body.exp_desc with
            | Texp_when (econd, ebody) ->
                let w =
                   try lift_val env econd
                   with Not_in_normal_form (loc2, s) ->
                      raise (Not_in_normal_form (loc2, s ^ " (Only total expressions are allowed in when clauses)"))
                   in
                Some w, aux ebody
            | _ -> None, aux body
            in
         Cf_case (tested, pattern_variables pat, lift_pat pat, whenopt, pattern_aliases pat, cfbody, acc) in
      let label = get_next_local_label() in
      add_used_label label;
      Cf_match (label, List.length pat_expr_list, List.fold_right cfg_case pat_expr_list conclu)

   | Texp_assert e ->
      Cf_assert (aux e)

   | Texp_assertfalse ->
      Cf_fail

   | Texp_lazy e ->
      aux e

   | Texp_sequence(expr1, expr2) ->
      Cf_seq (aux expr1, aux expr2)

   | Texp_while(cond, body) ->
      Cf_while (aux cond, aux body)

   | Texp_for(param, low, high, caml_dir, body) ->
      let dir =
        match caml_dir with
        | Upto -> For_loop_up
        | Downto -> For_loop_down
      in
      let cf_body = aux body in
      let cf_body = if !Mytools.use_credits then Cf_pay cf_body else cf_body in
      Cf_for (dir, Ident.name param, lift low, lift high, cf_body)

   | Texp_array args ->
      let arg = coq_list (List.map lift args) in
      let targ = (* ['a], obtained by extraction from ['a array]. *)
         match btyp_of_typ_exp e.exp_type with
         | Btyp_constr (id,[t]) when Path.name id = "array" -> lift_btyp loc t
         | _ -> failwith "Texp_array should always have type ['a array]"
         in
      let ts = coq_apps (Coq_var "Coq.Init.Datatypes.list") [targ] in
      let tr = coq_typ loc e in (* 'a array *)
      let func = Coq_var "Array_ml.of_list" in
      Cf_app ([ts], tr, func, [arg])

   | Texp_field (arg, p, lbl) ->
      let tr = coq_typ loc e in
      let ts = coq_typ loc arg in (* todo: check it is always 'loc' *)
      let func = coq_cfml_var "WPRecord.val_get_field" in
      let op = coq_app func (coq_var (record_field_name lbl.lbl_name)) in
      Cf_app ([ts], tr, op, [lift arg])

   | Texp_setfield(arg, p, lbl, newval) ->
      let ts1 = coq_typ loc arg in (* todo: check it is always 'loc' *)
      let ts2 = coq_typ loc newval in
      let func = coq_cfml_var "WPRecord.val_set_field" in
      let op = coq_app func (coq_var (record_field_name lbl.lbl_name)) in
      Cf_app ([ts1; ts2], coq_unit, op, [lift arg; lift newval])

   | Texp_try(body, pat_expr_list) -> unsupported loc "try expression"
   | Texp_variant(l, arg) ->  unsupported loc "variant expression"
   | Texp_ifthenelse(cond, ifso, None) -> unsupported loc "if-then-without-else expressions should have been normalized"
   | Texp_when(cond, body) -> unsupported loc "when expressions outside of pattern matching"
   | Texp_send(_, _, _) -> unsupported loc "send expressions"
   | Texp_new (cl, _) -> unsupported loc "new expressions"
   | Texp_instvar(path_self, path) -> unsupported loc "inst-var expressions"
   | Texp_setinstvar(path_self, path, expr) -> unsupported loc "set-inst-var expressions"
   | Texp_override(path_self, modifs) -> unsupported loc "override expressions"
   | Texp_letmodule(id, modl, body) -> unsupported loc "let-module expressions"
   | Texp_object _ -> unsupported loc "object expressions"
   | Texp_poly (_,_) -> unsupported loc "poly"
   | Texp_newtype (_,_) -> unsupported loc "newtype"
   | Texp_pack _ -> unsupported loc "pack"
   | Texp_open (_,_) -> unsupported loc "open in term"
   | Texp_constraint (e, Some ty, None) -> aux e
      (* LATER: see if it is needed
      let typ = lift_typ_exp loc ty.ctyp_type in
      CF_annot (aux e, typ)
      *)
   | Texp_constraint (e, _, _) -> unsupported loc "advanced type constraint"


and cfg_func env fvs pat bod =
   let rec get_typed_args acc e =
      let loc = e.exp_loc in
      match e.exp_desc with
      | Texp_function (_,[p1,e1],partial)
      | Texp_constraint ({exp_desc = Texp_function (_,[p1,e1],partial)},_,_) ->
         if partial <> Total
            then not_in_normal_form loc (Print_tast.string_of_expression false e);
         get_typed_args ((pattern_name p1, coq_typ_pat loc p1)::acc) e1
      | _ -> List.rev acc, e
      in
   let loc = pat.pat_loc in
   let f = pattern_name_protect_infix pat in
   let targs, body = get_typed_args [] bod in
   let typ = lift_typ_exp loc body.exp_type in
   let cf_body = cfg_exp env body in
   let cf_body = if !Mytools.use_credits then Cf_pay cf_body else cf_body in
   (* fvs computation must come after cf_body *)
   let fvs = List.map name_of_type_var (List.filter typvar_is_used fvs) in
   Cf_body (f, fvs, targs, typ, cf_body)
   (* --todo: check if the set of type variables quantified is not too
      conservative. Indeed, some type variables may no longer occur. *)

and cfg_record ?(record_name = "_") env e =
  let loc = e.exp_loc in
  match e.exp_desc with
  | Texp_record (lbl_expr_list, opt_init_expr) ->
    let named_args = List.map (fun (p,li,ei) -> (li.lbl_name,ei)) lbl_expr_list in
    let build_arg (name, arg) =
      (record_field_name name, coq_typ loc arg, lift_val env arg) in
    let cargs = List.map build_arg named_args in
    begin match opt_init_expr with
    | None -> Cf_record_new (record_name, cargs)
    | Some v -> Cf_record_with (lift_val env v, cargs)
    end

  | _ -> assert false

(*#########################################################################*)
(* ** Characteristic formulae for modules *)

(** Helper functions to find out the kind of a type declaration *)

let is_algebraic (name,dec) =
   match dec.typ_type.type_kind with Type_variant _ -> true | _ -> false

let is_type_abbrev (name,dec) =
   match dec.typ_type.type_kind with Type_abstract -> true | _ -> false

let is_type_record (name,dec) =
   match dec.typ_type.type_kind with Type_record _ -> true | _ -> false

let rec is_ignored_str_value (pat,exp) =
  is_ignored_exp exp

and is_ignored_exp exp =
   match exp.exp_desc with
   | Texp_constraint (e, _, _) ->
      is_ignored_exp e
   | Texp_sequence(expr1, expr2) ->
      is_ignored_exp expr1
   | Texp_function (_, pat_expr_list, _) ->
      List.exists is_ignored_str_value pat_expr_list
   | Texp_apply ({exp_desc = Texp_ident (f,_d)},
                [_, Some {exp_desc = Texp_constant (Const_string "CFML")}, _])
      when get_qualified_pervasives_name f = "Pervasives.ignore"
     -> true
   | _ -> false

(** Generate the top-level Coq declarations associated with
    a top-level declaration from a module.

    If a toplevel definition begins with [ignore "CFML"] in its body,
    then the toplevel definition is ignored by CFML altogether. *)

let rec cfg_structure_item s : cftops =
  let loc = s.str_loc in
  match s.str_desc with
  | Tstr_value(rf, fvs, pat_expr_list) ->
      reset_local_labels();

      if List.exists is_ignored_str_value pat_expr_list then [] (* ignore *) else begin

        (* --todo: improve code sharing between local bindings and top-level bindings *)
        let is_let_fun (pat,exp) =
           match exp.exp_desc with
           | Texp_function (_,_,_) -> true
           | Texp_constraint({exp_desc = Texp_function (_,_,_)},_,_) -> true
           | _ -> false in

        if List.for_all is_let_fun pat_expr_list then begin
          let env' = match rf with
             | Nonrecursive -> Ident.empty
             | Recursive -> Ident.empty
                 (* --todo: better support for polymorphic recursion
                List.fold_left (fun (pat,bod) acc -> Ident.add (pattern_ident pat) 0 acc) env pat_expr_list *)
             | Default -> unsupported loc "Default recursion mode"
             in
          let ncs = List.map (fun (pat,bod) -> (pattern_name_protect_infix pat, cfg_func env' fvs pat bod)) pat_expr_list in
            (List.map (fun (name,_) -> Cftop_val (name, func_type)) ncs)
          @ (List.map (fun (name,cf_body) -> Cftop_fun_cf (name, cf_body)) ncs)
          @ [Cftop_coqs (List.map (fun (name,_) -> register_cf name) ncs)]

        (* let-binding of a single value *)
        end else if (List.length pat_expr_list = 1) then begin (* later: check it is not a function *)
          let (pat,bod) = List.hd pat_expr_list in
          let x = pattern_name_protect_infix pat in
          (* DEPRECATED if (hack_recognize_okasaki_lazy x) then [] else *)
          begin

          (* value let-binding *)
          if is_value_let_binding bod then begin

             let v =
               try lift_val (Ident.empty) bod
               with Not_in_normal_form (loc2, s) ->
                  (* TODO: here and elsewhere, use a wrapper for extending the errors *)
                  raise (Not_in_normal_form (loc2, s ^ " (only value can satisfy the value restriction)"))
              in

             let fvs_typ, typ = lift_typ_sch loc pat.pat_type in
             let fvs = List.map name_of_type_var (List.filter typvar_is_used fvs) in
             if not (list_is_included fvs_typ fvs)
               then failwith "fvs_typ not included in fvs for let binding";
             let fvs_strict = fvs_typ in
             let fvs_others = list_minus fvs fvs_strict in

             let v_typed = coq_annot v typ in
             let implicits =
                match fvs_strict with
                | [] -> []
                | _ ->  [ Coqtop_implicit (x, List.map (fun t -> (t,Coqi_maximal)) fvs_strict) ]
                in
             [ Cftop_val (x, coq_forall_types fvs_strict typ);
               Cftop_coqs implicits;
               Cftop_val_cf (x, fvs_strict, fvs_others, v_typed);
               Cftop_coqs [register_cf x]; ]

          (* term let-binding -- later *)
          end else begin

             unsupported loc "top-level binding of terms that are not values";
             (* let (fvs_strict, fvs_others, typ) = get_fvs_typ loc fvs pat.pat_type in*)

             (* if fvs_strict <> [] || fvs_others <> []
                 then not_in_normal_form loc ("(unsatisfied value restriction) "
                                          ^ (Print_tast.string_of_expression false e));
             let cf1 = cfg_exp env bod in
             let env' = Ident.add (pattern_ident pat) (List.length fvs_strict) env in
             let cf2 = cfg_exp env' body in
             add_used_label x;
             Cf_let ((x,typ), cf1, cf2) *)

          end

        end (* for skip_cf *)

       end else
          unsupported loc ("mutually-recursive values that are not all functions");

     end (* for ignored toplevel item *)

  | Tstr_type(decls) -> [ Cftop_coqs (cfg_type_decls loc decls) ]

  | Tstr_module(id, modl) -> cfg_module id modl

  | Tstr_modtype(id, decl) -> cfg_modtype id decl

  | Tstr_open path ->
      (* TEMPORARILY DEPRECATED if is_primitive_module (Path.name path) then [] else *)
      [ Cftop_coqs [ Coqtop_require_import [ lift_full_path_name path ] ] ]

  | Tstr_primitive(id, descr) ->
      let id = var_name (Ident.name id) in
      let fvs, typ = lift_typ_sch loc descr.val_desc.ctyp_type in
      let typ = coq_fun_types fvs typ in
      [ Cftop_val (id, typ) ]

  | Tstr_exception(id, decl) ->
      [] (* unsupported "exceptions" ; could be raise CFML_ignore *)
  | Tstr_exn_rebind(id, path) ->
      [] (* unsupported "exceptions" ; could be raise CFML_ignore *)

  | Tstr_recmodule bindings -> unsupported loc "recursive modules"
  | Tstr_class _ -> unsupported loc "objects"
  | Tstr_class_type _ -> unsupported loc "objects"
  | Tstr_include (m,ids) -> unsupported loc "module-include"
  | Tstr_eval expr -> unsupported loc "top level eval expression (let _)"

(** Generate the top-level Coq declarations associated with
    a type abbreviation. *)

and cfg_type_abbrev (name,dec) =
   let loc = dec.typ_loc in
   let x = Ident.name name in
   check_type_constr_name loc x;
   let name = type_constr_name x in
   let args = List.map name_of_type_var dec.typ_type.type_params in
   let sort = coq_impl_types (List.length args) in
   let coqs = match dec.typ_type.type_manifest with
      | None -> [Coqtop_param (name, sort)]
      | Some t -> [Coqtop_def ((name, sort), coq_fun_types args (lift_typ_exp loc t));
                   Coqtop_hint_unfold ([name],"typeclass_instances") ] in
   coqs

(** Generate the top-level Coq declarations associated with
    a record definition. *)

and cfg_type_record (name,dec) =
   let loc = dec.typ_loc in
   let x = Ident.name name in
   check_type_constr_name loc x;
   let name_of_field lbl =
      record_field_name lbl in
   let fields = match dec.typ_type.type_kind with Type_record (l,_) -> l | _ -> assert false in
   (* let fields_base_names = List.map (fun (lbl,_,_) -> lbl) fields in *)
   let declared_params = List.map name_of_type_var dec.typ_type.type_params in
   let branches, branches_params = List.split (List.map (fun (lbl, mut, typ) ->
      let btyp = btyp_of_typ_exp typ in
      ((name_of_field lbl, lift_btyp loc btyp), fv_btyp ~through_arrow:false btyp)) fields) in
          (* todo: use a function to factorize above work *)

   (* deprecated sorting: let branches = list_ksort str_cmp branches in *)
   let fields_names, fields_types = List.split branches in
   (* let remaining_params = List.concat branches_params in *)
   (* todo: assert remaining_params included in declared_params *)
   (* TODO: enlever le polymorphisme inutile : list_intersect remaining_params declared_params *)
   let params = declared_params in
   let _top = {
      coqind_name = record_structure_name x;
      coqind_constructor_name = record_constructor_name x;
      coqind_targs = coq_types params;
      coqind_ret = Coq_type;
      coqind_branches = branches } in
   let _implicit_decl =
      match params with
      | [] -> []
      | _ -> List.map (fun field -> Coqtop_implicit (field, List.map (fun p -> p, Coqi_maximal) params)) fields_names
      in
   let type_abbrev = Coqtop_def ((type_constr_name x, Coq_wild), coq_fun_types params loc_type) in
   [ type_abbrev ] @
   (* DEPRECATED BUT KEEP FOR FUTURE USE
   [ Coqtop_record top ]
   @ (implicit_decl)
   @ [ Coqtop_hint_constructors ([record_structure_name x], "typeclass_instances") ]
   @
   *)
   record_functions x (record_constructor_name x) (record_repr_name x) params fields_names fields_types
  (*  todo: move le "_of" *)

(** Auxiliary function to generate stuff for records *)

and record_functions name record_constr repr_name params fields_names fields_types =
   let build_field_name_def i field_name =
      Coqtop_def ((field_name, field_type), Coq_nat i)
      in
   let fields_names_def = list_mapi build_field_name_def fields_names in
   fields_names_def

   (* DEPRECATED BUT KEEP FOR FUTURE USE
   let nth i l = List.nth l i in
   let n = List.length fields_names in
   let indices = list_nat n in
   let for_indices f = List.map f indices in

   let new_name = record_make_name name in
   let get_names = for_indices (fun i -> record_field_get_name (nth i fields_names)) in
   let set_names = for_indices (fun i -> record_field_set_name (nth i fields_names)) in
   let new_decl = Coqtop_param (new_name, func_type) in
   let get_set_decl i =
      [ Coqtop_param (nth i get_names, func_type);
        Coqtop_param (nth i set_names, func_type) ] in

   let logicals = List.map str_capitalize_1 fields_names in
   let reprs = for_indices (fun i -> sprintf "_T%d" (i+1)) in
   let abstracts = for_indices (fun i -> sprintf "_X%d" (i+1)) in
   let concretes = for_indices (fun i -> sprintf "x%d" (i+1)) in
   let loc = "l" in

   let vparams = coq_vars params in
   let vlogicals = coq_vars logicals in
   let vreprs = coq_vars reprs in
   let vabstracts = coq_vars abstracts in
   let vconcretes = coq_vars concretes in
   let vloc = coq_var "l" in

   let tparams = coq_types params in
   let tlogicals = coq_types logicals in
   let treprs = List.map (fun i -> nth i reprs, htype (nth i vlogicals) (nth i fields_types)) indices in
   let tabstracts = List.map (fun i -> nth i abstracts, nth i vlogicals) indices in
   let tconcretes = List.map (fun i -> nth i concretes, nth i fields_types) indices in
   let tloc = (loc, loc_type) in


   let repr_args = tparams @ tlogicals @ treprs @ tabstracts @ [tloc] in
   let hcore = hsingle vloc (coq_apps (coq_var_at record_constr) (vparams @ vconcretes)) in
   let helems_items = for_indices (fun i -> hdata (nth i vconcretes) (Coq_app (nth i vreprs, nth i vabstracts))) in
   let helems = hstars helems_items in
   let repr_body = hstar hcore helems in
   let repr_def = coqtop_def_untyped repr_name (coq_funs repr_args (hexistss tconcretes repr_body)) in

   let repr_folded = hdata vloc (coq_apps (coq_var_at repr_name) (vparams @ vlogicals @ vreprs @ vabstracts)) in
   let repr_unfolded = hdata vloc (coq_apps (coq_var_at repr_name) (vparams @ fields_types @ (list_make n id_repr) @ vconcretes)) in
   let repr_elems = helems in
   let repr_convert_body = coq_eq repr_folded (hexistss tconcretes (hstar repr_unfolded repr_elems)) in
   let repr_focus_body =himpl repr_folded (hexistss tconcretes (hstar repr_unfolded repr_elems)) in
   let repr_unfocus_body =himpl (hstar repr_unfolded repr_elems) repr_folded in
   let repr_convert_quantif = [tloc] @ tparams @ tlogicals @ treprs @ tabstracts in
   let repr_focus_quantif = repr_convert_quantif in
   let repr_unfocus_quantif = [tloc] @ tparams @ tconcretes @ tlogicals @ treprs @ tabstracts in
   let convert_name = record_convert_name name in
   let focus_name = record_unfocus_name name in
   let unfocus_name = record_focus_name name in
   let repr_convert = Coqtop_param (convert_name, coq_foralls repr_convert_quantif repr_convert_body) in
   let repr_focus = Coqtop_param (focus_name, coq_foralls repr_focus_quantif repr_focus_body) in
   let repr_unfocus = Coqtop_param (unfocus_name, coq_foralls repr_unfocus_quantif repr_unfocus_body) in
   let repr_convert_focus_unfocus = [ repr_convert; repr_focus; repr_unfocus;
      coqtop_noimplicit convert_name; coqtop_noimplicit focus_name; coqtop_noimplicit unfocus_name ] in
   let field_convert_focus_unfocus i =
      let field_name = nth i fields_names in
      let field_convert_name = record_convert_field_name field_name in
      let field_focus_name = record_focus_field_name field_name in
      let field_unfocus_name = record_unfocus_field_name field_name in
      let tconcretei = nth i tconcretes in
      let helemi = nth i helems_items in
      let field_folded = hdata vloc (coq_apps (coq_var_at repr_name) (vparams @ vlogicals @ vreprs @ vabstracts)) in
      let field_unfolded = hdata vloc (coq_apps (coq_var_at repr_name) (vparams @ (list_replace_nth i fields_types vlogicals) @ (list_replace i id_repr vreprs) @ (list_replace_nth i vconcretes vabstracts))) in
      let field_convert_body = coq_eq field_folded (hexists_one tconcretei (hstar field_unfolded helemi)) in
      let field_focus_body =himpl field_folded (hexists_one tconcretei (hstar field_unfolded helemi)) in
      let field_unfocus_body =himpl (hstar field_unfolded helemi) field_folded in
      let field_convert_quantif = [tloc] @ tparams @ tlogicals @ treprs @ tabstracts in
      let field_focus_quantif = field_convert_quantif in
      let field_unfocus_quantif = [tloc] @ tparams @ [ tconcretei ] @ tlogicals @ treprs @ tabstracts in
      let field_convert = Coqtop_param (field_convert_name, coq_foralls field_convert_quantif field_convert_body) in
      let field_focus = Coqtop_param (field_focus_name, coq_foralls field_focus_quantif field_focus_body) in
      let field_unfocus = Coqtop_param (field_unfocus_name, coq_foralls field_unfocus_quantif field_unfocus_body) in
      [ field_convert; field_focus; field_unfocus;
        coqtop_noimplicit field_convert_name; coqtop_noimplicit field_focus_name; coqtop_noimplicit field_unfocus_name ]
      in
   let fields_convert_focus_unfocus = List.concat (List.map (fun i -> field_convert_focus_unfocus i) indices) in

   let _new_spec =
      let new_name_spec = new_name ^ "_spec" in
      let r = "R" in
      let vr = coq_var r in
      let tr = (r, formula_type_of loc_type) in
      let x = "_X" in
      let tx = (x, coq_prod fields_types) in
      let data_targs = vparams @ fields_types @ (for_indices (fun _ -> id_repr)) in
      let post = coq_funs [(loc, loc_type)] (hdata vloc (coq_apps (coq_var_at repr_name) (data_targs @ vabstracts))) in
      let body = coq_funs [tx; tr] (Coq_lettuple (coq_vars abstracts, Coq_var x, coq_apps vr [heap_empty; post])) in
      let spec = coq_foralls tparams (coq_apps (Coq_var "spec_1") [body; coq_var new_name]) in
      [ Coqtop_param (new_name_spec, spec);
        register_spec new_name new_name_spec; ]
      in
   let _get_set_spec i =
      let get_name = nth i get_names in
      let set_name = nth i set_names in
      let get_name_spec = get_name ^ "_spec" in
      let set_name_spec = set_name ^ "_spec" in
      let r = "R" in
      let vr = coq_var r in
      let trget = (r, formula_type_of (nth i fields_types)) in
      let trset = (r, formula_type_of coq_unit) in
      let x' = sprintf "_X%d'" i in
      let vx' = coq_var x' in
      let tx' = (x', nth i fields_types) in
      let selected_tlogicals = list_remove i tlogicals in
      let replaced_vlogicals = list_replace i (nth i fields_types) vlogicals in
      let replaced_vreprs = list_replace i id_repr vreprs in
      let selected_treprs = list_remove i treprs in
      let replaced_tabstracts = list_replace i (nth i abstracts, nth i fields_types) tabstracts in
      let update_vabstracts = list_replace i vx' vabstracts in
      let data_targs = vparams @ replaced_vlogicals @ replaced_vreprs in
      let data_initial = hdata vloc (coq_apps (coq_var_at repr_name) (data_targs @ vabstracts)) in
      let data_updated = hdata vloc (coq_apps (coq_var_at repr_name) (data_targs @ update_vabstracts)) in
      let post_get = coq_funs [("x", Coq_wild)] (hstar (hpure (coq_eq (Coq_var "x") (nth i vabstracts))) data_initial) in
      let post_set = post_unit data_updated in
      let body_quantif = replaced_tabstracts @ selected_treprs in
      let body_get = coq_funs [tloc; trget] (coq_foralls body_quantif (coq_apps vr [data_initial; post_get])) in
      let body_set = coq_funs [tloc; tx'; trset] (coq_foralls body_quantif (coq_apps vr [data_initial; post_set])) in
      let spec_get = coq_foralls (tparams @ selected_tlogicals) (coq_apps (Coq_var "spec_1") [body_get; coq_var get_name]) in
      let spec_set = coq_foralls (tparams @ selected_tlogicals) (coq_apps (Coq_var "spec_2") [body_set; coq_var set_name]) in
      [ Coqtop_param (get_name_spec, spec_get);
        register_spec get_name get_name_spec;
        Coqtop_param (set_name_spec, spec_set);
        register_spec set_name set_name_spec; ]
      in

   let _get_spec_focus i =
      let get_name = nth i get_names in
      let get_name_spec = get_name ^ "_spec_focus" in
      let r = "R" in
      let vr = coq_var r in
      let trget = (r, formula_type_of (nth i fields_types)) in
      let replaced_vlogicals = list_replace i (nth i fields_types) vlogicals in
      let replaced_vreprs = list_replace i id_repr vreprs in
      let replaced_vabstracts = list_replace i (Coq_var "x") vabstracts in
      let data_initial = hdata vloc (coq_apps (coq_var_at repr_name) (vparams @ vlogicals @ vreprs @ vabstracts)) in
      let data_focused = hdata (Coq_var "x") (Coq_app (nth i vreprs, nth i vabstracts)) in
      let data_final = hdata vloc (coq_apps (coq_var_at repr_name) (vparams @ replaced_vlogicals @ replaced_vreprs @ replaced_vabstracts)) in
      let post_get = coq_funs [("x", Coq_wild)] (hstar data_focused data_final) in
      let body_quantif = tabstracts @ treprs in
      let body_get = coq_funs [tloc; trget] (coq_foralls body_quantif (coq_apps vr [data_initial; post_get])) in
      let spec_get = coq_foralls (tparams @ tlogicals) (coq_apps (Coq_var "spec_1") [body_get; coq_var get_name]) in
      [ Coqtop_param (get_name_spec, spec_get);
        coqtop_register "database_spec_focus" get_name get_name_spec; ]
      in

   let _set_spec_unfocus i =
      let set_name = nth i set_names in
      let set_name_spec = set_name ^ "_spec_unfocus" in
      let r = "R" in
      let vr = coq_var r in
      let trset = (r, formula_type_of coq_unit) in
      let x_concrete = "x0" in
      let tx_concrete = (x_concrete, nth i fields_types) in
      let vlogical0 = Coq_var "_A0" in
      let tlogical0 = ("_A0", Coq_type) in
      let vabstract0 = Coq_var "_X0" in
      let tabstract0 = ("_X0", vlogical0) in
      let vrepr0 = Coq_var "_T0" in
      let trepr0 = ("_T0", htype vlogical0 (nth i fields_types)) in
      let updated_vlogicals = list_replace i vlogical0 vlogicals in
      let updated_vreprs = list_replace i vrepr0 vreprs in
      let update_vabstracts = list_replace i vabstract0 vabstracts in
      let data_initial = hdata vloc (coq_apps (coq_var_at repr_name) (vparams @ vlogicals @ vreprs @ vabstracts)) in
      let data_updated = hdata vloc (coq_apps (coq_var_at repr_name) (vparams @ updated_vlogicals @ updated_vreprs @ update_vabstracts)) in
      let data_focused = hdata (Coq_var x_concrete) (Coq_app (vrepr0, vabstract0)) in
      let post_set = post_unit data_updated in
      let body_quantif = [tabstract0] @ tabstracts @ [trepr0] @ treprs in
      let body_set = coq_funs [tloc; tx_concrete; trset] (coq_foralls body_quantif (coq_apps vr [(hstar data_initial data_focused); post_set])) in
      let spec_set = coq_foralls (tparams @ [tlogical0] @ tlogicals) (coq_apps (Coq_var "spec_2") [body_set; coq_var set_name]) in
      [ Coqtop_param (set_name_spec, spec_set);
        coqtop_register "database_spec_unfocus" set_name set_name_spec; ]
      in

     [ new_decl ]
   @ (List.concat (List.map get_set_decl indices))
   @ [ repr_def ]
   @ repr_convert_focus_unfocus
   @ fields_convert_focus_unfocus
   @ new_spec
   @ (List.concat (List.map get_set_spec indices))
   @ (List.concat (List.map get_spec_focus indices))
   @ (List.concat (List.map set_spec_unfocus indices))

   END DEPRECATED *)



(** Generate the top-level Coq declarations associated with
    a algebraic data type definition. *)

and cfg_algebraics decls =
   (* -- todo: data constructor type arity may be reduced when types are erased *)
   (* -- todo: Caml types often clash with Caml program variables, since in Coq
         they get put in the same namespace *)
    let trans_ind (name,dec) =
      let loc = dec.typ_loc in
      let x = Ident.name name in
      check_type_constr_name loc x;
      let branches = match dec.typ_type.type_kind with Type_variant l -> l | _ -> assert false in
      let params = List.map name_of_type_var dec.typ_type.type_params in
      let ret_typ = coq_apps (Coq_var (type_constr_name x)) (coq_vars params) in
      let get_typed_constructor (c,ts) =
         check_constr_name loc c;
         (c, coq_impls (List.map (lift_typ_exp loc) ts) ret_typ) in
      let coqind_decl =
         if List.length decls = 1 then
            {  coqind_name = type_constr_name x;
               coqind_constructor_name = algebraic_constructor_name x;
               coqind_targs = coq_types params;
               coqind_ret = Coq_type;
               coqind_branches = List.map get_typed_constructor branches; }
          else
            {  coqind_name = type_constr_name x;
               coqind_constructor_name = algebraic_constructor_name x;
               coqind_targs = [];
               coqind_ret = coq_impl_types (List.length params);
               coqind_branches = List.map
                  (fun tc -> let (c,t) = get_typed_constructor tc in
                             (c, coq_foralls (coq_types params) t)
                     ) branches; }
          in
      let implicit_decl =
         match params with
         | [] -> []
         | _ -> List.map (fun (cname,_) -> Coqtop_implicit (cname, List.map (fun p -> p,Coqi_maximal) params)) branches
         in
      let build_polyeq_axioms (c,ts) =
        let axiom_name = polymorphic_eq_arg_name c in
        let axiom_type =
          let pred = coq_cfml_var "WPBuiltin.polymorphic_eq_arg" in
          let arg_names_typs = list_mapi (fun i t ->
            (variable_generated_name i, lift_typ_exp loc t)) ts in
          let arg_names = List.map fst arg_names_typs in
          let hyps = List.map (fun x -> Coq_app(pred, Coq_var x)) arg_names in
          let conc_value = coq_app_var_at c ((List.map coq_var params) @ (List.map coq_var arg_names)) in
          (* let conc_value = Coq_annot(coq_apps (Coq_var c) (List.map coq_var arg_names) , ret_typ) *)
          let conc = Coq_app (pred, conc_value) in
          coq_forall_types params (coq_foralls arg_names_typs (coq_impls hyps conc))
          in
        [ Coqtop_param (axiom_name, axiom_type);
          Coqtop_hint_resolve ([axiom_name], "polymorphic_eq"); ] in
          (* Example for "Some":
            Axiom polymorphic_eq_arg_some : forall A (v:A),
              polymorphic_eq_arg v ->
              polymorphic_eq_arg (Some v).
            Hint Resolve polymorphic_eq_arg_some : polymorphic_eq.
          *)
      let polyeq_axioms = List.map build_polyeq_axioms branches in
      (coqind_decl, (implicit_decl @ List.concat polyeq_axioms))
      in
   let inds,tops = List.split (List.map trans_ind decls) in
     [ Coqtop_ind inds ]
   @ (List.concat tops)
   @ [ Coqtop_hint_constructors (List.map (fun i -> i.coqind_name) inds, "typeclass_instances") ]


(** Generate the top-level Coq declarations associated with
    a type definition. *)

and cfg_type_decls loc (decls : (Ident.t * Typedtree.type_declaration) list) =
   let has_abbrev = List.exists is_type_abbrev decls in
   (*let all_abbrev = List.for_all is_type_abbrev decls in*)
   let nb_decls = List.length decls in
   if has_abbrev && nb_decls <> 1 then begin
      warning loc "relying on a best-effort support for mutually-recursive type definitions going through type abbreviations; if the Coq output does not compile, you will need to inline the type abbreviation at its places of occurences."
    end;
    let decls_abbrev = List.filter is_type_abbrev decls in
    let decls_records = List.filter is_type_record decls in
    let decls_algebraic = List.filter is_algebraic decls in
    let records_def = list_concat_map cfg_type_record decls_records in
    let abbrev_def = list_concat_map cfg_type_abbrev decls_abbrev in
    let algebraics_def = if decls_algebraic = [] then [] else cfg_algebraics decls_algebraic in
    abbrev_def @ records_def @ algebraics_def

   (* DEPRECATED
       experimental support: simply break circularity; might stack overflow!
          let (a,b) = List.split (List.map aux (List.map (fun x -> [x]) decls)) in
          (List.concat a, List.concat b)  *)

(** Generate the top-level Coq declarations associated with
    the content of a module. *)

and cfg_structure s =
   reset_used_labels();
   let body = list_concat_map (fun si -> reset_names(); cfg_structure_item si) s.str_items in
   (* cfg_extract_labels() @ *)
   body

(** Generate the top-level Coq declarations associated with
    a Caml signature definition. *)

and cfg_modtype id mt =
   let loc = mt.mty_loc in
   let id = lift_module_name id in
   let rec aux (bindings:mod_bindings) mt =
      match mt.mty_desc with
      | Tmty_ident p -> Coqtop_module_type (id, bindings, Mod_def_inline [lift_full_path_name p]), None
      | Tmty_signature s -> Coqtop_module_type (id, bindings, Mod_def_declare), Some (cfg_signature s)
      | Tmty_functor (x,mtx,mtr) ->
          begin match mtx.mty_desc with
          | Tmty_ident p -> aux (bindings @ [([lift_module_name x], Mod_typ_var (lift_full_path_name p))]) mtr (* TODO: use List.rev *)
          | _ -> unsupported loc "functor with on-the-fly signature for its argument"
          end
      | Tmty_with _ -> unsupported loc "module sig with"
      | Tmty_typeof _ -> unsupported loc "type of module"
      in
   let mod_typ_dec, sign_opt = aux [] mt in
   match sign_opt with
   | None -> [ Cftop_coqs [ mod_typ_dec ] ]
   | Some sign -> [ Cftop_coqs ( [mod_typ_dec] @ sign @ [Coqtop_end id] ) ]

(** Generate the top-level Coq declarations associated with
    a top-level declaration from a signature. *)

and cfg_signature_item s =
  let loc = s.sig_loc in
  match s.sig_desc with

  | Tsig_value (id,vd) ->
     if vd.val_val.val_kind <> Val_reg then unsupported loc "value in signature which is not a regular value";
     let fv, typ = lift_typ_sch loc vd.val_val.val_type in
     let x = Ident.name id in
     let implicit_decl =
         match fv with
         | [] -> []
         | _ -> [ Coqtop_implicit (x, List.map (fun p -> p, Coqi_maximal) fv) ]
         in
     [Coqtop_param (x, coq_forall_types fv typ)] @ implicit_decl

  | Tsig_type decls ->
     cfg_type_decls loc decls
(* deprecated
     List.iter (fun (id,decl) -> printf "%s\n" (Ident.name id)) decls;  print_newline();
     assert false
*)
      (* -- old
 (Ident.t * type_declaration) list
      if rs <> Trec_not then unsupported loc "recursive type definitions in signatures";
      begin match td.type_kind with
      | Type_abstract -> cfg_type_abbrev (id,td)
      | Type_variant _ -> cfg_algebraics [id,td]
      | Type_record _ -> unsupported loc "record types"
      end
      *)

  | Tsig_module (id,mt) ->
      let x = lift_module_name id in
      let mt' =
         match mt.mty_desc with
         | Tmty_ident p -> Mod_typ_var (lift_full_path_name p)
         | Tmty_signature s ->
            (*
            Printf.printf "%d\n" (List.length s);
             begin match List.hd s with
              | Tsig_value (id,vd) -> unsupported loc "u"
              | Tsig_type (id, td, rs) -> unsupported loc "x"
              | Tsig_module (id,mt,rs) ->   unsupported loc "y"
              | Tsig_modtype (id,decl) ->   unsupported loc "z"
              | Tsig_exception _ -> unsupported loc "exceptions"
              | Tsig_class _ -> unsupported loc "objects"
              | Tsig_cltype _ -> unsupported loc "objects"
              end;
             *)
            unsupported loc "module constraint is not just a name (4) -- todo: should be supported"
         | _ -> unsupported loc "module constraint is not just a name (2)"
         in
      [Coqtop_declare_module (x, mt')]

  | Tsig_modtype (id,decl) ->
      unsupported loc "module types declared in module signatures"
      (*
      begin match decl with
      | Tmodtype_abstract -> unsupported loc "abstract module types"
      | Tmodtype_manifest mt -> cfg_modtype id mt
      end
      *)
  | Tsig_exception _ -> unsupported loc "exceptions"
  | Tsig_class _ -> unsupported loc "objects"
  | Tsig_class_type _ -> unsupported loc "objects"
  | Tsig_recmodule _ -> unsupported loc "recursive module signature"
  | Tsig_open _ -> (* todo ? *) []
  | Tsig_include mty ->
      begin match mty.mty_desc with
      | Tmty_ident p ->  [Coqtop_module_type_include (lift_full_path_name p)]
      | Tmty_signature s ->
         unsupported loc "sig include is not just a name"
      | _ -> unsupported loc "sig include is not just a name"
      end


(** Generate the top-level Coq declarations associated with
    a signature. Handles mutually-recursive type definitions
    for algebraic data types. *)

and cfg_signature s =
   list_concat_map cfg_signature_item s.sig_items

(** Generate the top-level Coq declarations associated with
    a Caml module. *)

and cfg_module id m =
   let loc = m.mod_loc in
   let id = lift_module_name id in
   let rec aux bindings cast m =
      let return def =
         Coqtop_module (id, bindings, cast, def) in
      match m.mod_desc with
      | Tmod_ident p -> return (Mod_def_inline [lift_full_path_name p]), None
      | Tmod_structure str -> return Mod_def_declare, Some (cfg_structure str)
      | Tmod_functor (x, mt, m1) ->
          let x = lift_module_name x in
          if cast <> Mod_cast_free then unsupported loc "cast before arguments in module declaration";
          begin match mt.mty_desc with
          | Tmty_ident p -> aux (([x], Mod_typ_var (lift_full_path_name p))::bindings) cast m1
          | _ ->
             (* hack for Dijkstra   Printf.printf "-->%s %s\n" (lift_module_name x) id; Pident (Ident.create ("PqueueSig") *)
             if id = "MLDijkstra" && x = "MLPqueue"
             then
               aux (([x], Mod_typ_with_mod (Mod_typ_var "MLPqueueSig", "MLElement", "MLNextNode"))::bindings) cast m1
             else unsupported loc "functor with on-the-fly signature for its argument"

          end
      | Tmod_apply (m1, m2, coercion) ->
          let rec get_apps acc m0 =
             match m0.mod_desc with
             | Tmod_ident p -> lift_full_path_name p :: List.rev acc
             | Tmod_apply (m1, m2, coercion) ->
                 begin match m2.mod_desc with
                 | Tmod_ident p -> get_apps (lift_full_path_name p :: acc) m1
                 | _ -> unsupported loc "module application can only be made between module paths"
                 end
             | _ -> unsupported loc "module application can only be made between module paths"
             in
          return (Mod_def_inline (get_apps [] m)), None
      | Tmod_constraint(m1, _, mtd, coercion) ->
          begin match mtd with
          | Tmodtype_implicit -> unsupported loc "implicit module type constraint"
          | Tmodtype_explicit mt ->
              begin match mt.mty_desc with
              | Tmty_ident p -> aux bindings (Mod_cast_super (Mod_typ_var (lift_full_path_name p))) m1
              | Tmty_signature s ->
                unsupported loc "module constraint is not just a name (3) -- todo: should be supported"
               (*Printf.printf "%d\n" (List.length s);
                begin match List.hd s with
                 | Tsig_value (id,vd) -> unsupported loc "u"
                 | Tsig_type (id, td, rs) -> unsupported loc "x"
                 | Tsig_module (id,mt,rs) ->   unsupported loc "y"
                 | Tsig_modtype (id,decl) ->   unsupported loc "z"
                 | Tsig_exception _ -> unsupported loc "exceptions"
                 | Tsig_class _ -> unsupported loc "objects"
                 | Tsig_cltype _ -> unsupported loc "objects"
                 end
                  *)
              | Tmty_with _ -> unsupported loc "module sig with"
              | Tmty_typeof _ -> unsupported loc "type of module"
              | _ -> unsupported loc "module constraint is not just a name (1)"
              end
           end
      | Tmod_unpack _ -> unsupported loc "unpack"
      in
   let mod_dec, str_opt = aux [] Mod_cast_free m in
   match str_opt with
   | None -> [ Cftop_coqs [ mod_dec ] ]
   | Some str -> [ Cftop_coqs [ mod_dec ] ] @ str @ [ Cftop_coqs [ Coqtop_end id ] ]

(** Generate the top-level Coq declarations associated with
    a Caml file. *)

let cfg_file str =
   Print_type.type_rename := Renaming.type_variable_name;
   [ Cftop_coqs ([
      Coqtop_set_implicit_args;
      Coqtop_require [ "Coq.ZArith.BinInt"; "TLC.LibLogic"; "TLC.LibRelation"; "TLC.LibInt"; "TLC.LibListZ" ];
      Coqtop_require [ "CFML.SepBase"; "CFML.SepLifted"; "CFML.WPLifted"; "CFML.WPRecord"; "CFML.WPArray"; "CFML.WPBuiltin" (* *) ]; (* TODO: factorize the prefix using List.map *)
      Coqtop_require_import [ "Coq.ZArith.BinIntDef"; "CFML.Semantics"; "CFML.WPHeader" ];
      (* TODO: check binintdef needed *)
      Coqtop_custom "Delimit Scope Z_scope with Z.";
      Coqtop_custom "Existing Instance WPHeader.Enc_any | 99.";
      (* DEPRECATED Coqtop_custom "Local Open Scope cfheader_scope."; *)
      (*DEPRECATED Coqtop_custom "Open Scope list_scope.";*)
      (*DEPRECATED Coqtop_custom "Local Notation \"'int'\" := (Coq.ZArith.BinInt.Z).";*)
      ]
      @ (external_modules_get_coqtop())) ]
   @ cfg_structure str


      (*deprecated: (if !pure_mode then "FuncPrim" else "CFHeader") *)


      (* TODO: prevent "let int = 3" to work *)
