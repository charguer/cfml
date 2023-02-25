open Asttypes
open Typedtree
open Mytools
open Print_tast
open Coq
open Renaming
open Types


(*#########################################################################*)
(* ** Helper functions *)

(* later?
prefix_for_label
coq_record loc typ fields assigns optbase
record_field_names_and_immutability_of_labels
*)

let coq_sem cstr args =
  coq_apps (coq_var ("Semantics." ^ cstr)) args

let coq_trms (ts : coq list) : coq =
  coq_list ~typ:trm_type ts

let coq_pats (ts : coq list) : coq =
  coq_list ~typ:pat_type ts

let trm_val arg =
  coq_sem "trm_val" [arg]


(*#########################################################################*)
(* ** Environments to keep track of local variables *)

(* The environment binds local variables.
   These variables are to be represented by a "trm_var", whereas other
   "global variables" are directly represeted as a "coq_var". *)

type env = unit Ident.tbl

let env_extend env idents =
  List.fold_left (fun acc id -> Ident.add id () acc) env idents


let is_local_var (env:env) id =
  begin try
    let () = Ident.find_same id env in
    true
  with Not_found -> false end

(* extract identifiers from a pattern *)

let rec pattern_idents p =
   let loc = p.pat_loc in
   let aux = pattern_idents in
   match p.pat_desc with
   | Tpat_any -> []
   | Tpat_var s -> [s]
   | Tpat_alias (p, s) -> unsupported loc "alias patterns" (* s::(aux p)*)
   | Tpat_constant c -> []
   | Tpat_tuple l -> list_concat_map aux l
   | Tpat_construct (p, c, ps) -> list_concat_map aux ps
   | Tpat_variant (_,_,_) -> unsupported loc "variant patterns"
   | Tpat_record (l,_) -> unsupported loc "record patterns" (* list_concat_map (fun (li,pi) -> aux pi) l *)
   | Tpat_array pats -> unsupported loc "array patterns"
   | Tpat_or (p1,p2,_) -> unsupported loc "or patterns are only supported at pattern root"
   | Tpat_lazy p1 -> aux p1


(* Special mapping of builtin constructor names *)

let constr_rename_builtin x =
  match x with (* we assume no shadowing of these constructors *)
  | "[]" -> "nil"
  | "::" -> "cons"
  | "None" -> "none"
  | "Some" -> "some"
  | _ -> x


(*#########################################################################*)
(* ** Translation of patterns *)

(* LATER: to support aliases, see how it's done in characteristic.ml *)

let rec tr_pat p : coq =
   let loc = p.pat_loc in
   let aux = tr_pat in
   let auxs = List.map aux in
   match p.pat_desc with
   | Tpat_var s ->
        let x = var_name (Ident.name s) in
        coq_sem "pat_var" [Coq_string x]
   | Tpat_constant (Const_int n) ->
        coq_sem "pat_int" [Coq_int n]
   | Tpat_tuple ps ->
        coq_sem "pat_constr" [Coq_string "tuple"; coq_pats (auxs ps)]
   | Tpat_construct (p, c, ps) ->
      let x = string_of_path p in
      begin match x with
      | "()" -> coq_sem "pat_unit" []
      | "true" -> coq_sem "pat_bool" [coq_bool_true]
      | "false" -> coq_sem "pat_bool" [coq_bool_false]
      | _ ->
          let x = constr_rename_builtin x in
          coq_sem "pat_constr" [Coq_string x; coq_pats (auxs ps)]
      end

   | Tpat_alias (p, ak) -> unsupported loc "alias patterns" (* todo! *)
      (* LATER
      begin match ak with
      | TPat_alias id ->
          if through_aliases then aux p else Coq_var (var_name (Ident.name id))
      | TPat_constraint ty ->
          let typ = lift_typ_exp loc ty.ctyp_type in
          Coq_annot (aux p, typ)
      | TPat_type pp -> aux p
      end *)
   | Tpat_lazy p1 -> aux p1
   | Tpat_record _ -> unsupported loc "record patterns" (* todo! *)
   | Tpat_array pats -> unsupported loc "array patterns" (* todo! *)
   | Tpat_constant _ -> unsupported loc "only integer constant are supported"
   | Tpat_any -> not_in_normal_form loc "wildcard patterns remain after normalization"
   | Tpat_variant (_,_,_) -> unsupported loc "variant patterns"
   | Tpat_or (_,p1,p2) -> unsupported loc "or patterns in depth"





(*#########################################################################*)
(* ** Translation of variables *)

let tr_path (p : Path.t) : string =
  lift_path_name p (* (var_path p)*)


(*#########################################################################*)
(* ** Translation of expressions *)

let rec tr_exp env e =
   let loc = e.exp_loc in
   let aux = tr_exp env in
   let auxs = List.map aux in
   let not_normal ?s:(s="") () =
      not_in_normal_form loc (s ^ Print_tast.string_of_expression false e) in
   match e.exp_desc with

   | Texp_ident (p,d) ->
      let x = tr_path (var_path p) in
      if is_local_var env (Path.head p)
        then coq_sem "trm_var" [Coq_string x]
        else coq_var x

   | Texp_constant (Const_int n) ->
       trm_val (coq_sem "val_int" [Coq_int n])

   | Texp_constant _ ->
       unsupported loc "only integer constant are supported"

   | Texp_sequence(expr1, expr2) ->
      (* coq_sem "trm_seq" [aux expr1; aux expr2] *)
      coq_apps (coq_sem "trm_let" [coq_var "LibSepBind.bind_anon"]) [aux expr1; aux expr2]

   | Texp_ifthenelse (cond, ifso, Some ifnot) ->
      coq_sem "trm_if" [aux cond; aux ifso; aux ifnot]

   | Texp_apply (funct, oargs) ->
      let args = simplify_apply_args loc oargs in
      (*let fo = exp_find_inlined_primitive funct oargs in
      let f = match fo with
         | Some (coq_name,emb_name) -> coq_var coq_name
         | None -> aux funct
         in*)
      coq_sem "trm_apps" [aux funct; coq_trms (auxs args)]

   | Texp_constraint (e, Some ty, None) ->
      aux e

   | Texp_construct(p, cstr, args) ->
      let x = string_of_path p in
      begin match x with
      | "()" -> trm_val (coq_sem "val_unit" [])
      | "true" -> trm_val (coq_sem "val_bool" [coq_bool_true])
      | "false" -> trm_val (coq_sem "val_bool" [coq_bool_false])
      | _ -> let x = constr_rename_builtin x in
          coq_sem "trm_constr" [Coq_string x; coq_trms (auxs args)]
      end

   | Texp_let(rf, fvs, pat_expr_list, body) ->

      let is_let_fun =
         match (snd (List.hd pat_expr_list)).exp_desc with
         | Texp_function (_,_,_) -> true
         | Texp_constraint ({exp_desc = Texp_function (_,_,_)},_,_) -> true (* todo: generalize *)
         | _ -> false in

      (* binding of functions, possibly mutually-recursive *)
      if is_let_fun then begin
        if (List.length pat_expr_list <> 1) then unsupported loc "deep_embedding: mutually recursive functions";
        let (pat,bod) = List.hd pat_expr_list in
        tr_func env rf pat bod

      (* let-binding of a single term *)
      end else begin
        if (List.length pat_expr_list <> 1) then not_normal();
        let (pat,bod) = List.hd pat_expr_list in
        let x = pattern_name_protect_infix pat in
        let arg1 = tr_exp env bod in
        let env' = Ident.add (pattern_ident pat) () env in
        let arg2 = tr_exp env' body in
        coq_sem "trm_let" [Coq_string x; arg1; arg2]

     end

   | Texp_tuple ts ->
        coq_sem "trm_constr" [Coq_string "tuple"; coq_trms (auxs ts)]

   | Texp_match (arg, pat_expr_list, partial) ->
      let tested = aux arg in (* TODO: assert that this is a value; normalization should ensure so *)
      let build_branch (pat,body) =
        begin match body.exp_desc with
        | Texp_when (econd, ebody) -> unsupported loc "when clauses"
        | _ -> ()
        end;
        let env' = env_extend env (pattern_idents pat) in
        Coq_tuple [tr_pat pat; tr_exp env' body]
        in
        coq_sem "trm_match" [ tested; coq_list ~typ:(coq_prods [pat_type; trm_type]) (List.map build_branch pat_expr_list) ]
              (* FUTURE USE:
              let w =
                 try lift_val env econd
                 with Not_in_normal_form (loc2, s) ->
                    raise (Not_in_normal_form (loc2, s ^ " (Only total expressions are allowed in when clauses)"))
                 in
              Some w, aux ebody *)
              (* FUTURE USE:
                 pattern_variables pat
                pattern_aliases pat *)

   | Texp_assertfalse ->
      coq_sem "trm_fail" []

   | Texp_field (arg, p, lbl) ->
      let _fields, immutable = record_field_names_and_immutability_of_label lbl in
      if immutable then unsupported loc "unsupported expression for deep embedding: pure records";
      let f = record_field_name lbl.lbl_name in
      let func = coq_app (coq_var "WPRecord.val_get_field") (coq_var f) in
      coq_sem "trm_apps" [func; coq_trms [aux arg]]

   | Texp_setfield(arg, p, lbl, newval) ->
      (* TODO: factorize better with Texp_field *)
      let _fields, immutable = record_field_names_and_immutability_of_label lbl in
      if immutable then unsupported loc "unsupported expression for deep embedding: pure records";
      let f = record_field_name lbl.lbl_name in
      let func = coq_app (coq_var "WPRecord.val_set_field") (coq_var f) in
      coq_sem "trm_apps" [func; coq_trms [aux arg; aux newval]]

   | Texp_record (l, opt_init_expr) ->
      let lbls = List.map (fun (p,li,ei) -> li) l in
      let args = List.map (fun (p,li,ei) -> ei) l in
      let fields, immutable = record_field_names_and_immutability_of_labels lbls in
      if immutable then unsupported loc "unsupported expression for deep embedding: pure records";
      if opt_init_expr <> None then unsupported loc "unsupported expression for deep embedding: record with";
      let fs = List.map record_field_name fields in
      let func = coq_app (coq_var "WPRecord.val_record_init") (coq_list ~typ:Formula.field_type (coq_vars fs)) in
      coq_sem "trm_apps" [func; coq_trms (auxs args)]

(* LATER

   | Texp_record (_, _) ->
       cfg_record env e


   | Texp_assert e ->
      Cf_assert (aux e)

   | Texp_lazy e ->
      aux e

   | Texp_while(cond, body) ->
      Cf_while (aux cond, cf_pay (aux body))

   | Texp_for(param, low, high, caml_dir, body) ->
      let dir =
        match caml_dir with
        | Upto -> For_loop_up
        | Downto -> For_loop_down
      in
      Cf_for (dir, Ident.name param, lift low, lift high, cf_pay (aux body))

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
      let _fields, immutable = record_field_names_and_immutability_of_label lbl in
      let f = record_field_name lbl.lbl_name in
      let carg = lift arg in
      if immutable then begin
        (* For pure records, generate a Coq projection operation *)
        Cf_val (Coq_proj (f, carg))
      end else begin
        (* For impure records, generate a [Cf_app] *)
        let tr = coq_typ loc e in
        let ts = coq_typ loc arg in (* todo: check it is always 'loc' *)
        let func = coq_cfml_var "WPRecord.val_get_field" in
        let op = coq_app func (coq_var f) in
        Cf_app ([ts], tr, op, [carg])
      end

   | Texp_setfield(arg, p, lbl, newval) -> (* only for impure records *)
      let _fields, immutable = record_field_names_and_immutability_of_label lbl in
      assert (not immutable);
      let ts1 = coq_typ loc arg in (* todo: check it is always 'loc' *)
      let ts2 = coq_typ loc newval in
      let func = coq_cfml_var "WPRecord.val_set_field" in
      let op = coq_app func (coq_var (record_field_name lbl.lbl_name)) in
      Cf_app ([ts1; ts2], coq_typ_unit, op, [lift arg; lift newval])

*)
   | Texp_function (_, pat_expr_list, partial) -> not_normal ~s:"The function involved has not been lifted properly during normalization;\n check the normalized file in _output folder.\n" ()
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
      (* LATER: see if it is needed
      let typ = lift_typ_exp loc ty.ctyp_type in
      CF_annot (aux e, typ)
      *)
   | _ -> unsupported loc "unsupported expression for deep embedding"


and tr_func env rf pat bod =
  let is_value = (env = Ident.empty) in
  let fname = pattern_name_protect_infix pat in
  let is_recursive = match rf with
     | Nonrecursive -> false
     | Recursive -> true
     | Default -> unsupported pat.pat_loc "Default recursion mode"
     in
  let fident = pattern_ident pat in
  let env' = env_extend env (if is_recursive then [fident] else []) in
  let rec args_with_idents_and_body acc e =
      let loc = e.exp_loc in
      match e.exp_desc with
      | Texp_function (_,[p1,e1],partial)
      | Texp_constraint ({exp_desc = Texp_function (_,[p1,e1],partial)},_,_) ->
         if partial <> Total
            then not_in_normal_form loc (Print_tast.string_of_expression false e);
         args_with_idents_and_body ((pattern_name p1, pattern_ident p1)::acc) e1
      | _ -> List.rev acc, e
      in
   (*let loc = pat.pat_loc in *)
   let args_with_idents, body = args_with_idents_and_body [] bod in
   let args, idents = List.split args_with_idents in
   let env' = env_extend env' idents in
   let body' = tr_exp env' body in
   let cstr = if is_value then "val_fixs" else "trm_fixs" in
   let farg = if is_recursive then Coq_string fname else coq_var "LibSepBind.bind_anon" in
   coq_sem cstr [farg; (coq_list (List.map coq_string args)); body']


(** Generate the deep embedding of a top-level OCaml function [fun pat -> body] *)

let tr_func_top rf pat bod =
  tr_func Ident.empty rf pat bod
