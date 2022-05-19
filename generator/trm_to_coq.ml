open Asttypes
open Typedtree
open Mytools
open Print_tast
open Coq
open Renaming



(*#########################################################################*)
(* ** Helper functions *)

(* later?
prefix_for_label
coq_record loc typ fields assigns optbase
record_field_names_and_immutability_of_labels
*)

let coq_sem cstr args =
  coq_apps (coq_var ("Semantics." ^ cstr)) args


(*#########################################################################*)
(* ** Environments to keep track of local variables *)

(* The environment binds local variables.
   These variables are to be represented by a "trm_var", whereas other
   "global variables" are directly represeted as a "coq_var". *)

type env = unit Ident.tbl

let is_local_var (env:env) id =
  begin try
    let () = Ident.find_same id env in
    true
  with Not_found -> false end


(*#########################################################################*)
(* ** Lifting of patterns *)

(* LATER

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

*)


(*#########################################################################*)
(* ** Lifting of variables *)

let tr_path (p : Path.t) : string =
  lift_path_name p (* (var_path p)*)


(*#########################################################################*)
(* ** Characteristic formulae for expressions *)


(** Translate a Caml expression into its Coq characteristic formula *)

let rec tr_exp env e =
   let loc = e.exp_loc in
   let aux = tr_exp env in
   let not_normal ?s:(s="") () =
      not_in_normal_form loc (s ^ Print_tast.string_of_expression false e) in
   match e.exp_desc with

   | Texp_ident (p,d) ->
      let x = tr_path (var_path p) in
      if is_local_var env (Path.head p)
        then coq_sem "trm_var" [Coq_string x]
        else coq_var x

   | Texp_constant (Const_int n) ->
       coq_sem "val_int" [Coq_int n]
   | Texp_constant _ ->
       unsupported loc "only integer constant are supported"

   | Texp_sequence(expr1, expr2) ->
      (* coq_sem "trm_seq" [aux expr1; aux expr2] *)
      coq_apps (coq_sem "trm_let" [coq_var "LibSepBind.bind_anon"]) [aux expr1; aux expr2]

   | Texp_ifthenelse (cond, ifso, Some ifnot) ->
      coq_sem "trm_if" [aux cond; aux ifso; aux ifnot]

   | Texp_apply (funct, oargs) ->
      let args = simplify_apply_args loc oargs in
      coq_sem "trm_apps" [aux funct; coq_list ~typ:trm_type (List.map aux args)]

   | Texp_constraint (e, Some ty, None) ->
      aux e

   | Texp_construct(p, cstr, args) ->
      let x = string_of_path p in
      begin match x with
      | "()" -> coq_sem "val_unit" []
      | "true" -> coq_sem "val_bool" [coq_bool_true]
      | "false" -> coq_sem "val_bool" [coq_bool_false]
      | _ ->  unsupported loc "only unit and boolean constructors are supported"
      end
      (* LATER
        lift_path_name p
        coq_of_constructor loc p c (List.map aux es) e.exp_type
        val_constr : idconstr -> list val -> val *)


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

(* LATER
   | Texp_tuple el -> ret e

   | Texp_record (_, _) ->
       cfg_record env e


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
      Cf_app ([ts1; ts2], coq_unit, op, [lift arg; lift newval])

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
  let env' = match rf with
     | Nonrecursive -> env
     | Recursive -> Ident.add (pattern_ident pat) () env
     | Default -> unsupported pat.pat_loc "Default recursion mode"
     in
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
   let env' = List.fold_left (fun acc id -> Ident.add id () acc) env' idents in
   let body' = tr_exp env' body in
   let cstr = if is_value then "val_fixs" else "trm_fixs" in
   let farg = if is_value then coq_var "LibSepBind.bind_anon" else Coq_string fname in
   coq_sem cstr [farg; (coq_list (List.map coq_string_val args)); body']


(** Generate the deep embedding of a top-level OCaml function [fun pat -> body] *)

let tr_func_top rf pat bod =
  tr_func Ident.empty rf pat bod
