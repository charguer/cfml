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

(* $Id: typemod.ml 10860 2010-11-25 21:43:08Z lefessan $ *)

open Misc
open Path
open Asttypes
open Parsetree
open Types
open Format

type error =
    Cannot_apply of module_type
  | Not_included of Includemod.error list
  | Cannot_eliminate_dependency of module_type
  | Signature_expected
  | Structure_expected of module_type
  | With_no_component of Longident.t
  | With_mismatch of Longident.t * Includemod.error list
  | Repeated_name of string * string
  | Non_generalizable of type_expr
  | Non_generalizable_class of Ident.t * class_declaration
  | Non_generalizable_module of module_type
  | Implementation_is_required of string
  | Interface_not_compiled of string
  | Not_allowed_in_functor_body
  | With_need_typeconstr
  | Not_a_packed_module of type_expr
  | Incomplete_packed_module of type_expr

open Typedtree

exception Error of Location.t * error

let rec path_concat head p =
  match p with
    Pident tail -> Pdot (Pident head, Ident.name tail, 0)
  | Pdot (pre, s, pos) -> Pdot (path_concat head pre, s, pos)
  | Papply _ -> assert false

(* Extract a signature from a module type *)

let extract_sig env loc mty =
  match Mtype.scrape env mty with
    Mty_signature sg -> sg
  | _ -> raise(Error(loc, Signature_expected))

let extract_sig_open env loc mty =
  match Mtype.scrape env mty with
    Mty_signature sg -> sg
  | _ -> raise(Error(loc, Structure_expected mty))

(* Compute the environment after opening a module *)

let type_open env loc lid =
  let (path, mty) = Typetexp.find_module env loc lid in
  let sg = extract_sig_open env loc mty in
  path, Env.open_signature path sg env

(* Record a module type *)
let rm node =
  Stypes.record (Stypes.Ti_mod node); (* moved to genannot *)
  node

(* Forward declaration, to be filled in by type_module_type_of *)
let type_module_type_of_fwd
  : (Env.t -> Parsetree.module_expr -> Typedtree.module_expr) ref
  = ref (fun env m -> assert false)

(* Merge one "with" constraint in a signature *)

let rec add_rec_types env = function
    Sig_type(id, decl, Trec_next) :: rem ->
      add_rec_types (Env.add_type id decl env) rem
  | _ -> env

let check_type_decl env id row_id newdecl decl rs rem =
  let env = Env.add_type id newdecl env in
  let env =
    match row_id with None -> env | Some id -> Env.add_type id newdecl env in
  let env = if rs = Trec_not then env else add_rec_types env rem in
  Includemod.type_declarations env id newdecl decl

(* FIXME unused
let rec make_params n = function
    [] -> []
  | _ :: l -> ("a" ^ string_of_int n) :: make_params (n+1) l

let wrap_param s = {ptyp_desc=Ptyp_var s; ptyp_loc=Location.none}

let sig_item desc typ loc = {
  sig_desc = desc; sig_loc = loc;
}
 *)

let merge_constraint initial_env loc sg lid constr =
  let real_id = ref None in
  let rec merge env sg namelist row_id =
    match sg with
      [] -> raise(Error(loc, With_no_component lid))
    | item :: rem ->
    match (item, namelist, constr) with
    | (Sig_type(id, decl, rs) , [s],
       Pwith_type ({ptype_kind = Ptype_abstract} as sdecl))
      when Ident.name id = s && Typedecl.is_fixed_type sdecl ->
        let decl_row =
          { type_params =
              List.map (fun _ -> Btype.newgenvar()) sdecl.ptype_params;
            type_arity = List.length sdecl.ptype_params;
            type_kind = Type_abstract;
            type_private = Private;
            type_manifest = None;
            type_variance =
              List.map (fun (c,n) -> (not n, not c, not c))
              sdecl.ptype_variance }
        and id_row = Ident.create (s^"#row") in
        let initial_env = Env.add_type id_row decl_row initial_env in
        let tdecl = Typedecl.transl_with_constraint
                initial_env id (Some(Pident id_row)) sdecl in
            let newdecl = tdecl.typ_type in
        check_type_decl env id row_id newdecl decl rs rem;
        let decl_row = {decl_row with type_params = newdecl.type_params} in
        let rs' = if rs = Trec_first then Trec_not else rs in
            (Pident id, Twith_type tdecl),
        Sig_type(id_row, decl_row, rs') :: Sig_type(id, newdecl, rs) :: rem
    | (Sig_type(id, decl, rs) , [s], Pwith_type sdecl)
      when Ident.name id = s ->
        let tdecl =
              Typedecl.transl_with_constraint initial_env id None sdecl in
            let newdecl = tdecl.typ_type in
            check_type_decl env id row_id newdecl decl rs rem;
            (Pident id, Twith_type tdecl),
        Sig_type(id, newdecl, rs) :: rem
    | (Sig_type(id, decl, rs), [s], (Pwith_type _ | Pwith_typesubst _))
      when Ident.name id = s ^ "#row" ->
        merge env rem namelist (Some id)
    | (Sig_type(id, decl, rs), [s], Pwith_typesubst sdecl)
      when Ident.name id = s ->
        (* Check as for a normal with constraint, but discard definition *)
        let tdecl =
              Typedecl.transl_with_constraint initial_env id None sdecl in
            let newdecl = tdecl.typ_type in
        check_type_decl env id row_id newdecl decl rs rem;
        real_id := Some id;
        (Pident id, Twith_typesubst tdecl), rem
    | (Sig_module(id, mty, rs), [s], Pwith_module lid)
      when Ident.name id = s ->
        let (path, mty') = Typetexp.find_module initial_env loc lid in
        let newmty = Mtype.strengthen env mty' path in
            ignore(Includemod.modtypes env newmty mty);
            (Pident id, Twith_module path),
        Sig_module(id, newmty, rs) :: rem
    | (Sig_module(id, mty, rs), [s], Pwith_modsubst lid)
      when Ident.name id = s ->
        let (path, mty') = Typetexp.find_module initial_env loc lid in
        let newmty = Mtype.strengthen env mty' path in
        ignore(Includemod.modtypes env newmty mty);
        real_id := Some id;
        (Pident id, Twith_modsubst path), rem
    | (Sig_module(id, mty, rs), s :: namelist, _)
      when Ident.name id = s ->
            let ((path, tcstr), newsg) =
              merge env (extract_sig env loc mty) namelist None in

            (path_concat id path, tcstr),
            Sig_module(id, Mty_signature newsg, rs) :: rem
        | (item, _, _) ->
            let (cstr, items) = merge (Env.add_item item env) rem namelist row_id
            in
        cstr, item :: items in
  try
    let names = Longident.flatten lid in
    let (tcstr, sg) = merge initial_env sg names None in
    let sg =
    match names, constr with
      [s], Pwith_typesubst sdecl ->
        let id =
          match !real_id with None -> assert false | Some id -> id in
        let lid =
          try match sdecl.ptype_manifest with
          | Some {ptyp_desc = Ptyp_constr (lid, stl)} ->
              let params =
                List.map
                  (function {ptyp_desc=Ptyp_var s} -> s | _ -> raise Exit)
                  stl in
              if params <> sdecl.ptype_params then raise Exit;
              lid
          | _ -> raise Exit
          with Exit -> raise (Error (sdecl.ptype_loc, With_need_typeconstr))
        in
        let (path, _) =
          try Env.lookup_type lid initial_env with Not_found -> assert false
        in
        let sub = Subst.add_type id path Subst.identity in
        Subst.signature sub sg
    | [s], Pwith_modsubst lid ->
        let id =
          match !real_id with None -> assert false | Some id -> id in
        let (path, _) = Typetexp.find_module initial_env loc lid in
        let sub = Subst.add_module id path Subst.identity in
        Subst.signature sub sg
    | _ ->
          sg
    in
    (tcstr, sg)
  with Includemod.Error explanation ->
    raise(Error(loc, With_mismatch(lid, explanation)))

(* Add recursion flags on declarations arising from a mutually recursive
   block. *)

let map_rec fn decls rem =
  match decls with
  | [] -> rem
  | d1 :: dl -> fn Trec_first d1 :: map_end (fn Trec_next) dl rem

let rec map_rec' fn decls rem =
  match decls with
  | (id,_ as d1) :: dl when Btype.is_row_name (Ident.name id) ->
      fn Trec_not d1 :: map_rec' fn dl rem
  | _ -> map_rec fn decls rem

(* Auxiliary for translating recursively-defined module types.
   Return a module type that approximates the shape of the given module
   type AST.  Retain only module, type, and module type
   components of signatures.  For types, retain only their arity,
   making them abstract otherwise. *)

let rec approx_modtype env smty =
  match smty.pmty_desc with
    Pmty_ident lid ->
      let (path, info) = Typetexp.find_modtype env smty.pmty_loc lid in
      Mty_ident path
  | Pmty_signature ssg ->
      Mty_signature(approx_sig env ssg)
  | Pmty_functor(param, sarg, sres) ->
      let arg = approx_modtype env sarg in
      let (id, newenv) = Env.enter_module param arg env in
      let res = approx_modtype newenv sres in
      Mty_functor(id, arg, res)
  | Pmty_with(sbody, constraints) ->
      approx_modtype env sbody
  | Pmty_typeof smod ->
      (!type_module_type_of_fwd env smod).mod_type

and approx_sig env ssg =
  match ssg with
    [] -> []
  | item :: srem ->
      match item.psig_desc with
      | Psig_type sdecls ->
          let decls = Typedecl.approx_type_decl env sdecls in
          let rem = approx_sig env srem in
          map_rec' (fun rs (id, info) -> Sig_type(id, info, rs)) decls rem
      | Psig_module(name, smty) ->
          let mty = approx_modtype env smty in
          let (id, newenv) = Env.enter_module name mty env in
          Sig_module(id, mty, Trec_not) :: approx_sig newenv srem
      | Psig_recmodule sdecls ->
          let decls =
            List.map
              (fun (name, smty) ->
                (Ident.create name, approx_modtype env smty))
              sdecls in
          let newenv =
            List.fold_left (fun env (id, mty) -> Env.add_module id mty env)
            env decls in
          map_rec (fun rs (id, mty) -> Sig_module(id, mty, rs)) decls
                  (approx_sig newenv srem)
      | Psig_modtype(name, sinfo) ->
          let info = approx_modtype_info env sinfo in
          let (id, newenv) = Env.enter_modtype name info env in
          Sig_modtype(id, info) :: approx_sig newenv srem
      | Psig_open lid ->
          let (path, mty) = type_open env item.psig_loc lid in
          approx_sig mty srem
      | Psig_include smty ->
          let mty = approx_modtype env smty in
          let sg = Subst.signature Subst.identity
                     (extract_sig env smty.pmty_loc mty) in
          let newenv = Env.add_signature sg env in
          sg @ approx_sig newenv srem
      | Psig_class sdecls | Psig_class_type sdecls ->
          let decls = Typeclass.approx_class_declarations env sdecls in
          let rem = approx_sig env srem in
          List.flatten
            (map_rec
              (fun rs (i1, d1, i2, d2, i3, d3, _) ->
                [Sig_class_type(i1, d1, rs);
                 Sig_type(i2, d2, rs);
                 Sig_type(i3, d3, rs)])
              decls [rem])
      | _ ->
          approx_sig env srem

and approx_modtype_info env sinfo =
  match sinfo with
    Pmodtype_abstract ->
      Modtype_abstract
  | Pmodtype_manifest smty ->
      Modtype_manifest(approx_modtype env smty)

(* Additional validity checks on type definitions arising from
   recursive modules *)

let check_recmod_typedecls env sdecls decls =
  let recmod_ids = List.map fst decls in
  List.iter2
    (fun (_, smty) (id, mty) ->
       let mty = mty.mty_type in
      List.iter
        (fun path ->
          Typedecl.check_recmod_typedecl env smty.pmty_loc recmod_ids
                                         path (Env.find_type path env))
        (Mtype.type_paths env (Pident id) mty))
    sdecls decls

(* Auxiliaries for checking uniqueness of names in signatures and structures *)

module StringSet = Set.Make(struct type t = string let compare = compare end)

let check cl loc set_ref name =
  if StringSet.mem name !set_ref
  then raise(Error(loc, Repeated_name(cl, name)))
  else set_ref := StringSet.add name !set_ref

let check_sig_item type_names module_names modtype_names loc = function
    Sig_type(id, _, _) ->
      check "type" loc type_names (Ident.name id)
  | Sig_module(id, _, _) ->
      check "module" loc module_names (Ident.name id)
  | Sig_modtype(id, _) ->
      check "module type" loc modtype_names (Ident.name id)
  | _ -> ()

let rec remove_values ids = function
    [] -> []
  | Sig_value (id, _) :: rem when List.exists (Ident.equal id) ids -> rem
  | f :: rem -> f :: remove_values ids rem

let rec get_values = function
    [] -> []
  | Sig_value (id, _) :: rem -> id :: get_values rem
  | f :: rem -> get_values rem

(* Check and translate a module type expression *)

let transl_modtype_longident loc env lid =
  let (path, info) = Typetexp.find_modtype env loc lid in
  path

let mkmty desc typ loc =
  let mty = {
    mty_desc = desc;
    mty_type = typ;
    mty_loc = loc;
    } in
  Typedtree.add_saved_type (Saved_module_type mty);
  mty

let mksig desc loc =
  let sg = { sig_desc = desc; sig_loc = loc } in
  Typedtree.add_saved_type (Saved_signature_item sg);
  sg

(* let signature sg = List.map (fun item -> item.sig_type) sg *)

let rec transl_modtype env smty =
  let loc = smty.pmty_loc in
  match smty.pmty_desc with
    Pmty_ident lid ->
      let path = transl_modtype_longident loc env lid in
      mkmty (Tmty_ident path) (Mty_ident path) loc
  | Pmty_signature ssg ->
      let sg = transl_signature env ssg in
      mkmty (Tmty_signature sg) (Mty_signature sg.sig_type) loc
  | Pmty_functor(param, sarg, sres) ->
      let arg = transl_modtype env sarg in
      let (id, newenv) = Env.enter_module param arg.mty_type env in
      let res = transl_modtype newenv sres in
      mkmty (Tmty_functor (id, arg, res))
      (Mty_functor(id, arg.mty_type, res.mty_type)) loc
  | Pmty_with(sbody, constraints) ->
      let body = transl_modtype env sbody in
      let init_sg = extract_sig env sbody.pmty_loc body.mty_type in
      let (tcstrs, final_sg) =
        List.fold_left
          (fun (tcstrs,sg) (lid, sdecl) ->
            let (tcstr, sg) = merge_constraint env smty.pmty_loc sg lid sdecl
            in
            (tcstr :: tcstrs, sg)
        )
        ([],init_sg) constraints in
      mkmty (Tmty_with ( body, tcstrs))
      (Mtype.freshen (Mty_signature final_sg)) loc
  | Pmty_typeof smod ->
      let tmod = !type_module_type_of_fwd env smod in
      mkmty (Tmty_typeof tmod) tmod.mod_type loc


and transl_signature env sg =
  let type_names = ref StringSet.empty
  and module_names = ref StringSet.empty
  and modtype_names = ref StringSet.empty in
  let rec transl_sig env sg =
    Ctype.init_def(Ident.current_time());
    match sg with
      [] -> [], []
    | item :: srem ->
	let loc = item.psig_loc in
        match item.psig_desc with
        | Psig_value(name, sdesc) ->
            let tdesc = Typedecl.transl_value_decl env sdesc in
            let desc = tdesc.val_val in
            let (id, newenv) = Env.enter_value name desc env in
            let (trem, rem) = transl_sig newenv srem in
            mksig (Tsig_value (id, tdesc)) loc :: trem,
            if List.exists (Ident.equal id) (get_values rem) then rem
            else Sig_value(id, desc) :: rem
        | Psig_type sdecls ->
            List.iter
              (fun (name, decl) -> check "type" item.psig_loc type_names name)
              sdecls;
            let (decls, newenv) = Typedecl.transl_type_decl env sdecls in
            let (trem, rem) = transl_sig newenv srem in
            mksig (Tsig_type decls) loc :: trem,
            map_rec' (fun rs (id, info) ->
                Sig_type(id, info.typ_type, rs)) decls rem
        | Psig_exception(name, sarg) ->
            let targ = Typedecl.transl_exception env sarg in
            let arg = List.map (fun cty -> cty.ctyp_type) targ in
            let (id, newenv) = Env.enter_exception name arg env in
            let (trem, rem) = transl_sig newenv srem in
            mksig (Tsig_exception (id, targ)) loc :: trem,
            Sig_exception(id, arg) :: rem
        | Psig_module(name, smty) ->
            check "module" item.psig_loc module_names name;
            let tmty = transl_modtype env smty in
            let mty = tmty.mty_type in
            let (id, newenv) = Env.enter_module name mty env in
            let (trem, rem) = transl_sig newenv srem in
            mksig (Tsig_module (id, tmty)) loc :: trem,
            Sig_module(id, mty, Trec_not) :: rem
        | Psig_recmodule sdecls ->
            List.iter
              (fun (name, smty) ->
                 check "module" item.psig_loc module_names name)
              sdecls;
            let (decls, newenv) =
              transl_recmodule_modtypes item.psig_loc env sdecls in
            let (trem, rem) = transl_sig newenv srem in
            mksig (Tsig_recmodule decls) loc :: trem,
            map_rec (fun rs (id, tmty) -> Sig_module(id, tmty.mty_type, rs)) decls rem
        | Psig_modtype(name, sinfo) ->
            check "module type" item.psig_loc modtype_names name;
            let (tinfo, info) = transl_modtype_info env sinfo in
            let (id, newenv) = Env.enter_modtype name info env in
            let (trem, rem) = transl_sig newenv srem in
            mksig (Tsig_modtype (id, tinfo)) loc :: trem,
            Sig_modtype(id, info) :: rem
        | Psig_open lid ->
            let (path, newenv) = type_open env item.psig_loc lid in
            let (trem, rem) = transl_sig newenv srem in
            mksig (Tsig_open path) loc :: trem, rem
        | Psig_include smty ->
            let tmty = transl_modtype env smty in
            let mty = tmty.mty_type in
            let sg = Subst.signature Subst.identity
                       (extract_sig env smty.pmty_loc mty) in
            List.iter
              (check_sig_item type_names module_names modtype_names
                              item.psig_loc)
              sg;
            let newenv = Env.add_signature sg env in
            let (trem, rem) = transl_sig newenv srem in
            mksig (Tsig_include tmty) loc :: trem,
            remove_values (get_values rem) sg @ rem
        | Psig_class cl ->
            List.iter
              (fun {pci_name = name} ->
                 check "type" item.psig_loc type_names name)
              cl;
            let (classes, newenv) = Typeclass.class_descriptions env cl in
            let (trem, rem) = transl_sig newenv srem in
              mksig (Tsig_class (List.map2 (fun pcl tcl ->
				       let (_, _, _, _, _, _, _, _, _, _, tcl) = tcl in
					 tcl
				    ) cl classes)) loc :: trem,
            List.flatten
              (map_rec
                 (fun rs (i, d, i', d', i'', d'', i''', d''', _, _, _) ->
                    [Sig_class(i, d, rs);
                     Sig_class_type(i', d', rs);
                     Sig_type(i'', d'', rs);
                     Sig_type(i''', d''', rs)])
                 classes [rem])
        | Psig_class_type cl ->
            List.iter
              (fun {pci_name = name} ->
                 check "type" item.psig_loc type_names name)
              cl;
            let (classes, newenv) = Typeclass.class_type_declarations env cl in
            let (trem, rem) = transl_sig newenv srem in
              mksig (Tsig_class_type (List.map2 (fun pcl tcl ->
					    let (_, _, _, _, _, _, tcl) = tcl in
					      tcl
				       ) cl classes)) loc :: trem,
            List.flatten
              (map_rec
                 (fun rs (i, d, i', d', i'', d'', _) ->
                    [Sig_class_type(i, d, rs);
                     Sig_type(i', d', rs);
                     Sig_type(i'', d'', rs)])
                 classes [rem])
  in
  let previous_saved_types = Typedtree.get_saved_types () in
  let (trem, rem) = transl_sig env sg in
  let sg = { sig_items = trem; sig_type =  rem } in
  Typedtree.set_saved_types ( (Saved_signature sg) :: previous_saved_types );
  sg

and transl_modtype_info env sinfo =
  match sinfo with
    Pmodtype_abstract ->
      Tmodtype_abstract, Modtype_abstract
  | Pmodtype_manifest smty ->
      let tmty = transl_modtype env smty in
      Tmodtype_manifest tmty, Modtype_manifest tmty.mty_type

and transl_recmodule_modtypes loc env sdecls =
  let make_env curr =
    List.fold_left
      (fun env (id, mty) -> Env.add_module id mty env)
      env curr in
  let make_env2 curr =
    List.fold_left
      (fun env (id, mty) -> Env.add_module id mty.mty_type env)
      env curr in
  let transition env_c curr =
    List.map2
      (fun (_, smty) (id, mty) -> (id, transl_modtype env_c smty))
      sdecls curr in
  let init =
    List.map
      (fun (name, smty) ->
        (Ident.create name, approx_modtype env smty))
      sdecls in
  let env0 = make_env init in
  let dcl1 = transition env0 init in
  let env1 = make_env2 dcl1 in
  check_recmod_typedecls env1 sdecls dcl1;
  let dcl2 = transition env1 dcl1 in
(*
  List.iter
    (fun (id, mty) ->
      Format.printf "%a: %a@." Printtyp.ident id Printtyp.modtype mty)
    dcl2;
*)
  let env2 = make_env2 dcl2 in
  check_recmod_typedecls env2 sdecls dcl2;
  (dcl2, env2)

(* Try to convert a module expression to a module path. *)

exception Not_a_path

let rec path_of_module mexp =
  match mexp.mod_desc with
    Tmod_ident p -> p
  | Tmod_apply(funct, arg, coercion) when !Clflags.applicative_functors ->
      Papply(path_of_module funct, path_of_module arg)
  | _ -> raise Not_a_path

(* Check that all core type schemes in a structure are closed *)

let rec closed_modtype = function
    Mty_ident p -> true
  | Mty_signature sg -> List.for_all closed_signature_item sg
  | Mty_functor(id, param, body) -> closed_modtype body

and closed_signature_item = function
    Sig_value(id, desc) -> Ctype.closed_schema desc.val_type
  | Sig_module(id, mty, _) -> closed_modtype mty
  | _ -> true

let check_nongen_scheme env str =
  match str.str_desc with
    Tstr_value(rec_flag, fvs, pat_exp_list) -> (* CFML *)
      List.iter
        (fun (pat, exp) ->
          if not (Ctype.closed_schema exp.exp_type) then
            raise(Error(exp.exp_loc, Non_generalizable exp.exp_type)))
        pat_exp_list
  | Tstr_module(id, md) ->
      if not (closed_modtype md.mod_type) then
        raise(Error(md.mod_loc, Non_generalizable_module md.mod_type))
  | _ -> ()

let check_nongen_schemes env str =
  List.iter (check_nongen_scheme env) str

(* Extract the list of "value" identifiers bound by a signature.
   "Value" identifiers are identifiers for signature components that
   correspond to a run-time value: values, exceptions, modules, classes.
   Note: manifest primitives do not correspond to a run-time value! *)

let rec bound_value_identifiers = function
    [] -> []
  | Sig_value(id, {val_kind = Val_reg}) :: rem ->
      id :: bound_value_identifiers rem
  | Sig_exception(id, decl) :: rem -> id :: bound_value_identifiers rem
  | Sig_module(id, mty, _) :: rem -> id :: bound_value_identifiers rem
  | Sig_class(id, decl, _) :: rem -> id :: bound_value_identifiers rem
  | _ :: rem -> bound_value_identifiers rem

(* Helpers for typing recursive modules *)

let anchor_submodule name anchor =
  match anchor with None -> None | Some p -> Some(Pdot(p, name, nopos))
let anchor_recmodule id anchor =
  Some (Pident id)

let enrich_type_decls anchor decls oldenv newenv =
  match anchor with
    None -> newenv
  | Some p ->
      List.fold_left
        (fun e (id, info) ->
          let info' =
            Mtype.enrich_typedecl oldenv (Pdot(p, Ident.name id, nopos)) info.typ_type
          in
            Env.add_type id info' e)
        oldenv decls

let enrich_module_type anchor name mty env =
  match anchor with
    None -> mty
  | Some p -> Mtype.enrich_modtype env (Pdot(p, name, nopos)) mty

let check_recmodule_inclusion env bindings =
  (* PR#4450, PR#4470: consider
        module rec X : DECL = MOD  where MOD has inferred type ACTUAL
     The "natural" typing condition
        E, X: ACTUAL |- ACTUAL <: DECL
     leads to circularities through manifest types.
     Instead, we "unroll away" the potential circularities a finite number
     of times.  The (weaker) condition we implement is:
        E, X: DECL,
           X1: ACTUAL,
           X2: ACTUAL{X <- X1}/X1
           ...
           Xn: ACTUAL{X <- X(n-1)}/X(n-1)
        |- ACTUAL{X <- Xn}/Xn <: DECL{X <- Xn}
     so that manifest types rooted at X(n+1) are expanded in terms of X(n),
     avoiding circularities.  The strengthenings ensure that
     Xn.t = X(n-1).t = ... = X2.t = X1.t.
     N can be chosen arbitrarily; larger values of N result in more
     recursive definitions being accepted.  A good choice appears to be
     the number of mutually recursive declarations. *)

  let subst_and_strengthen env s id mty =
    Mtype.strengthen env (Subst.modtype s mty)
                         (Subst.module_path s (Pident id)) in

  let rec check_incl first_time n env s =
    if n > 0 then begin
      (* Generate fresh names Y_i for the rec. bound module idents X_i *)
      let bindings1 =
        List.map
          (fun (id, mty_decl, modl, mty_actual) ->
             (id, Ident.rename id, mty_actual))
          bindings in
      (* Enter the Y_i in the environment with their actual types substituted
         by the input substitution s *)
      let env' =
        List.fold_left
          (fun env (id, id', mty_actual) ->
             let mty_actual' =
               if first_time
               then mty_actual
               else subst_and_strengthen env s id mty_actual in
             Env.add_module id' mty_actual' env)
          env bindings1 in
      (* Build the output substitution Y_i <- X_i *)
      let s' =
        List.fold_left
          (fun s (id, id', mty_actual) ->
             Subst.add_module id (Pident id') s)
          Subst.identity bindings1 in
      (* Recurse with env' and s' *)
      check_incl false (n-1) env' s'
    end else begin
      (* Base case: check inclusion of s(mty_actual) in s(mty_decl)
         and insert coercion if needed *)
      let check_inclusion (id, mty_decl, modl, mty_actual) =
        let mty_decl' = Subst.modtype s mty_decl.mty_type
        and mty_actual' = subst_and_strengthen env s id mty_actual in
        let coercion =
          try
            Includemod.modtypes env mty_actual' mty_decl'
          with Includemod.Error msg ->
            raise(Error(modl.mod_loc, Not_included msg)) in
        let modl' =
            { mod_desc = Tmod_constraint(modl, mty_decl.mty_type,
                Tmodtype_explicit mty_decl, coercion);
            mod_type = mty_decl.mty_type;
            mod_env = env;
            mod_loc = modl.mod_loc } in
        (id, mty_decl, modl') in
      List.map check_inclusion bindings
    end
  in check_incl true (List.length bindings) env Subst.identity

(* Helper for unpack *)

let modtype_of_package env loc p nl tl =
  try match Env.find_modtype p env with
  | Modtype_manifest mty when nl <> [] ->
      let sg = extract_sig env loc mty in
      let ntl = List.combine nl tl in
      let sg' =
        List.map
          (function
              Sig_type (id, ({type_params=[]} as td), rs)
              when List.mem (Ident.name id) nl ->
                let ty = List.assoc (Ident.name id) ntl in
                Sig_type (id, {td with type_manifest = Some ty}, rs)
            | item -> item)
          sg in
      Mty_signature sg'
  | _ ->
      if nl = [] then Mty_ident p
      else raise(Error(loc, Signature_expected))
  with Not_found ->
    raise(Typetexp.Error(loc, Typetexp.Unbound_modtype (Ctype.lid_of_path p)))

let wrap_constraint env arg mty explicit =
  let coercion =
    try
      Includemod.modtypes env arg.mod_type mty
    with Includemod.Error msg ->
      raise(Error(arg.mod_loc, Not_included msg)) in
  { mod_desc = Tmod_constraint(arg, mty, explicit, coercion);
    mod_type = mty;
    mod_env = env;
    mod_loc = arg.mod_loc }

(* Type a module value expression *)

let mkstr desc loc =
  let str = { str_desc = desc; str_loc = loc } in
  Typedtree.add_saved_type (Saved_structure_item str);
  str

let rec type_module sttn funct_body anchor env smod =
  match smod.pmod_desc with
    Pmod_ident lid ->
      let (path, mty) = Typetexp.find_module env smod.pmod_loc lid in
      rm { mod_desc = Tmod_ident path;
           mod_type = if sttn then Mtype.strengthen env mty path else mty;
           mod_env = env;
           mod_loc = smod.pmod_loc }
  | Pmod_structure sstr ->
      let (str, sg, finalenv) =
        type_structure funct_body anchor env sstr smod.pmod_loc in
      rm { mod_desc = Tmod_structure str;
           mod_type = Mty_signature sg;
           mod_env = env;
           mod_loc = smod.pmod_loc }
  | Pmod_functor(name, smty, sbody) ->
      let mty = transl_modtype env smty in
      let (id, newenv) = Env.enter_module name mty.mty_type env in
      let body = type_module sttn true None newenv sbody in
      rm { mod_desc = Tmod_functor(id, mty, body);
           mod_type = Mty_functor(id, mty.mty_type, body.mod_type);
           mod_env = env;
           mod_loc = smod.pmod_loc }
  | Pmod_apply(sfunct, sarg) ->
      let arg = type_module true funct_body None env sarg in
      let path = try Some (path_of_module arg) with Not_a_path -> None in
      let funct =
        type_module (sttn && path <> None) funct_body None env sfunct in
      begin match Mtype.scrape env funct.mod_type with
        Mty_functor(param, mty_param, mty_res) as mty_functor ->
          let coercion =
            try
              Includemod.modtypes env arg.mod_type mty_param
            with Includemod.Error msg ->
              raise(Error(sarg.pmod_loc, Not_included msg)) in
          let mty_appl =
            match path with
              Some path ->
                Subst.modtype (Subst.add_module param path Subst.identity)
                              mty_res
            | None ->
                try
                  Mtype.nondep_supertype
                    (Env.add_module param arg.mod_type env) param mty_res
                with Not_found ->
                  raise(Error(smod.pmod_loc,
                              Cannot_eliminate_dependency mty_functor))
          in
          rm { mod_desc = Tmod_apply(funct, arg, coercion);
               mod_type = mty_appl;
               mod_env = env;
               mod_loc = smod.pmod_loc }
      | _ ->
          raise(Error(sfunct.pmod_loc, Cannot_apply funct.mod_type))
      end
  | Pmod_constraint(sarg, smty) ->
      let arg = type_module true funct_body anchor env sarg in
      let mty = transl_modtype env smty in
      rm {(wrap_constraint env arg mty.mty_type (Tmodtype_explicit mty)) with mod_loc = smod.pmod_loc}

  | Pmod_unpack sexp ->
      if funct_body then
        raise (Error (smod.pmod_loc, Not_allowed_in_functor_body));
      if !Clflags.principal then Ctype.begin_def ();
      let exp = Typecore.type_exp env sexp in
      if !Clflags.principal then begin
        Ctype.end_def ();
        Ctype.generalize_structure exp.exp_type
      end;
      let mty =
        match Ctype.expand_head env exp.exp_type with
          {desc = Tpackage (p, nl, tl)} ->
            if List.exists (fun t -> Ctype.free_variables t <> []) tl then
              raise (Error (smod.pmod_loc,
                            Incomplete_packed_module exp.exp_type));
            if !Clflags.principal &&
              not (Typecore.generalizable (Btype.generic_level-1) exp.exp_type)
            then
              Location.prerr_warning smod.pmod_loc
                (Warnings.Not_principal "this module unpacking");
            modtype_of_package env smod.pmod_loc p nl tl
        | {desc = Tvar} ->
            raise (Typecore.Error
                     (smod.pmod_loc, Typecore.Cannot_infer_signature))
        | _ ->
            raise (Error (smod.pmod_loc, Not_a_packed_module exp.exp_type))
      in
      rm { mod_desc = Tmod_unpack(exp, mty);
           mod_type = mty;
           mod_env = env;
           mod_loc = smod.pmod_loc }

and type_structure funct_body anchor env sstr scope =
  let type_names = ref StringSet.empty
  and module_names = ref StringSet.empty
  and modtype_names = ref StringSet.empty in
  let rec type_struct env sstr =
    Ctype.init_def(Ident.current_time());
    match sstr with
      [] ->
        ([], [], env)
      | pstr :: srem ->
	  let loc = pstr.pstr_loc in
	    match pstr.pstr_desc with
	      | Pstr_eval sexpr ->
		  let expr = Typecore.type_expression env sexpr in
		  let (str_rem, sig_rem, final_env) = type_struct env srem in
		    (mkstr (Tstr_eval expr) loc :: str_rem, sig_rem, final_env)
	      | Pstr_value(rec_flag, sdefs) ->
        let scope =
          match rec_flag with
          | Recursive -> Some (Annot.Idef {scope with
                                 Location.loc_start = loc.Location.loc_start})
          | Nonrecursive ->
              let start = match srem with
                | [] -> loc.Location.loc_end
                | {pstr_loc = loc2} :: _ -> loc2.Location.loc_start
              in Some (Annot.Idef {scope with Location.loc_start = start})
          | Default -> None
        in
        Ctype.open_hook(); (* CFML *)
        let (defs, newenv) =
          Typecore.type_binding env rec_flag sdefs scope in

        let fvs = Ctype.close_hook ~showtyp:Typecore.cfml_showtyp ~gen_nonexpansive:false () in (* CFML *)

        let (str_rem, sig_rem, final_env) = type_struct newenv srem in
        let bound_idents = let_bound_idents defs in
        let make_sig_value id =
          Sig_value(id, Env.find_value (Pident id) newenv) in
        (mkstr (Tstr_value(rec_flag, fvs, defs)) loc :: str_rem, (* CFML *)
         map_end make_sig_value bound_idents sig_rem,
         final_env)
    | Pstr_primitive(name, sdesc) ->
        let desc = Typedecl.transl_value_decl env sdesc in
        let (id, newenv) = Env.enter_value name desc.val_val env in
        let (str_rem, sig_rem, final_env) = type_struct newenv srem in
        (mkstr (Tstr_primitive(id, desc)) loc :: str_rem,
         Sig_value(id, desc.val_val) :: sig_rem,
         final_env)
    | Pstr_type sdecls ->
        List.iter
          (fun (name, decl) -> check "type" loc type_names name)
          sdecls;
        let (decls, newenv) = Typedecl.transl_type_decl env sdecls in
        let newenv' =
          enrich_type_decls anchor decls env newenv in
        let (str_rem, sig_rem, final_env) = type_struct newenv' srem in
        (mkstr (Tstr_type decls) loc :: str_rem,
         map_rec' (fun rs (id, info) -> Sig_type(id, info.typ_type, rs)) decls sig_rem,
         final_env)
    | Pstr_exception(name, sarg) ->
        let targ = Typedecl.transl_exception env sarg in
	let arg = List.map (fun cty -> cty.ctyp_type) targ in
        let (id, newenv) = Env.enter_exception name arg env in
        let (str_rem, sig_rem, final_env) = type_struct newenv srem in
        (mkstr (Tstr_exception(id, targ)) loc :: str_rem,
         Sig_exception(id, arg) :: sig_rem,
         final_env)
    | Pstr_exn_rebind(name, longid) ->
        let (path, arg) = Typedecl.transl_exn_rebind env loc longid in
        let (id, newenv) = Env.enter_exception name arg env in
        let (str_rem, sig_rem, final_env) = type_struct newenv srem in
        (mkstr (Tstr_exn_rebind(id, path)) loc :: str_rem,
         Sig_exception(id, arg) :: sig_rem,
         final_env)
    | Pstr_module(name, smodl) ->
        check "module" loc module_names name;
        let modl =
          type_module true funct_body (anchor_submodule name anchor) env
            smodl in
        let mty = enrich_module_type anchor name modl.mod_type env in
        let (id, newenv) = Env.enter_module name mty env in
        let (str_rem, sig_rem, final_env) = type_struct newenv srem in
        (mkstr (Tstr_module(id, modl)) loc :: str_rem,
         Sig_module(id, modl.mod_type, Trec_not) :: sig_rem,
         final_env)
    | Pstr_recmodule sbind ->
        List.iter
          (fun (name, _, _) -> check "module" loc module_names name)
          sbind;
        let (decls, newenv) =
          transl_recmodule_modtypes loc env
            (List.map (fun (name, smty, smodl) -> (name, smty)) sbind) in
        let bindings1 =
          List.map2
            (fun (id, mty) (name, _, smodl) ->
              let modl =
                type_module true funct_body (anchor_recmodule id anchor) newenv
                  smodl in
              let mty' =
                enrich_module_type anchor (Ident.name id) modl.mod_type newenv
              in
              (id, mty, modl, mty'))
           decls sbind in
        let bindings2 =
          check_recmodule_inclusion newenv bindings1 in
        let (str_rem, sig_rem, final_env) = type_struct newenv srem in
        (mkstr (Tstr_recmodule bindings2) loc :: str_rem,
         map_rec (fun rs (id, _, modl) -> Sig_module(id, modl.mod_type, rs))
                 bindings2 sig_rem,
         final_env)
    | Pstr_modtype(name, smty) ->
        check "module type" loc modtype_names name;
        let mty = transl_modtype env smty in
        let (id, newenv) = Env.enter_modtype name (Modtype_manifest mty.mty_type) env in
        let (str_rem, sig_rem, final_env) = type_struct newenv srem in
        (mkstr (Tstr_modtype(id, mty)) loc :: str_rem,
         Sig_modtype(id, Modtype_manifest mty.mty_type) :: sig_rem,
         final_env)
    | Pstr_open lid ->
	let (path, newenv) = type_open env loc lid in
	let (str_rem, sig_rem, final_env) = type_struct newenv srem in
	  (mkstr (Tstr_open path) loc :: str_rem, sig_rem, final_env)
    | Pstr_class cl ->
         List.iter
           (fun {pci_name = name} -> check "type" loc type_names name)
           cl;
        let (classes, new_env) = Typeclass.class_declarations env cl in
        let (str_rem, sig_rem, final_env) = type_struct new_env srem in
        (mkstr (Tstr_class
           (List.map (fun (i, d, _,_,_,_,_,_, s, m, c) ->
              let vf = if d.cty_new = None then Virtual else Concrete in
              (* (i, s, m, c, vf) *) (c, m, vf)) classes)) loc ::
(* TODO: check with Jacques why this is here
           Tstr_class_type
           (List.map (fun (_,_, i, d, _,_,_,_,_,_,c) -> (i, c)) classes) ::
         Tstr_type
           (List.map (fun (_,_,_,_, i, d, _,_,_,_,_) -> (i, d)) classes) ::
         Tstr_type
           (List.map (fun (_,_,_,_,_,_, i, d, _,_,_) -> (i, d)) classes) ::
*)
         str_rem,
         List.flatten
           (map_rec
              (fun rs (i, d, i', d', i'', d'', i''', d''', _, _, _) ->
                 [Sig_class(i, d, rs);
                  Sig_class_type(i', d', rs);
                  Sig_type(i'', d'', rs);
                  Sig_type(i''', d''', rs)])
              classes [sig_rem]),
         final_env)
    | Pstr_class_type cl ->
        List.iter
          (fun {pci_name = name} -> check "type" loc type_names name)
          cl;
        let (classes, new_env) = Typeclass.class_type_declarations env cl in
        let (str_rem, sig_rem, final_env) = type_struct new_env srem in
        (mkstr (Tstr_class_type
           (List.map (fun (i, d, _, _, _, _, c) -> (i, c)) classes)) loc ::
(*  TODO: check with Jacques why this is here
       Tstr_type
           (List.map (fun (_, _, i, d, _, _) -> (i, d)) classes) ::
         Tstr_type
           (List.map (fun (_, _, _, _, i, d) -> (i, d)) classes) :: *)
         str_rem,
         List.flatten
           (map_rec
              (fun rs (i, d, i', d', i'', d'', _) ->
                 [Sig_class_type(i, d, rs);
                  Sig_type(i', d', rs);
                  Sig_type(i'', d'', rs)])
              classes [sig_rem]),
         final_env)
    | Pstr_include smodl ->
        let modl = type_module true funct_body None env smodl in
        (* Rename all identifiers bound by this signature to avoid clashes *)
        let sg = Subst.signature Subst.identity
                   (extract_sig_open env smodl.pmod_loc modl.mod_type) in
        List.iter
          (check_sig_item type_names module_names modtype_names loc) sg;
        let new_env = Env.add_signature sg env in
        let (str_rem, sig_rem, final_env) = type_struct new_env srem in
        (mkstr (Tstr_include (modl, bound_value_identifiers sg)) loc :: str_rem,
         sg @ sig_rem,
         final_env)
  in
  if !Clflags.annotations
  then List.iter (function {pstr_loc = l} -> Stypes.record_phrase l) sstr; (* moved to genannot *)
  let previous_saved_types = Typedtree.get_saved_types () in
  let (items, sg, finalenv) = type_struct env sstr in
  let str = { str_items = items; str_type = sg } in
  Typedtree.set_saved_types (( Saved_structure str) :: previous_saved_types);
  str, sg, finalenv

let type_module = type_module true false None
let type_structure = type_structure false None

(* Normalize types in a signature *)

let rec normalize_modtype env = function
    Mty_ident p -> ()
  | Mty_signature sg -> normalize_signature env sg
  | Mty_functor(id, param, body) -> normalize_modtype env body

and normalize_signature env = List.iter (normalize_signature_item env)

and normalize_signature_item env = function
    Sig_value(id, desc) -> Ctype.normalize_type env desc.val_type
  | Sig_module(id, mty, _) -> normalize_modtype env mty
  | _ -> ()

(* Simplify multiple specifications of a value or an exception in a signature.
   (Other signature components, e.g. types, modules, etc, are checked for
   name uniqueness.)  If multiple specifications with the same name,
   keep only the last (rightmost) one. *)

let rec simplify_modtype mty =
  match mty with
    Mty_ident path -> mty
  | Mty_functor(id, arg, res) -> Mty_functor(id, arg, simplify_modtype res)
  | Mty_signature sg -> Mty_signature(simplify_signature sg)

and simplify_signature sg =
  let rec simplif val_names exn_names res = function
    [] -> res
  | (Sig_value(id, descr) as component) :: sg ->
      let name = Ident.name id in
      simplif (StringSet.add name val_names) exn_names
              (if StringSet.mem name val_names then res else component :: res)
              sg
  | (Sig_exception(id, decl) as component) :: sg ->
      let name = Ident.name id in
      simplif val_names (StringSet.add name exn_names)
              (if StringSet.mem name exn_names then res else component :: res)
              sg
  | Sig_module(id, mty, rs) :: sg ->
      simplif val_names exn_names
              (Sig_module(id, simplify_modtype mty, rs) :: res) sg
  | component :: sg ->
      simplif val_names exn_names (component :: res) sg
  in
    simplif StringSet.empty StringSet.empty [] (List.rev sg)

(* Extract the module type of a module expression *)

let type_module_type_of env smod =
  let tmty = type_module env smod in
  let mty =
    match smod.pmod_desc with
    | Pmod_ident lid -> (* turn off strengthening in this case *)
        let (path, mty) = Typetexp.find_module env smod.pmod_loc lid in mty
    | _ -> tmty.mod_type in
  (* PR#5037: clean up inferred signature to remove duplicate specs *)
  let mty = simplify_modtype mty in
  (* PR#5036: must not contain non-generalized type variables *)
  if not (closed_modtype mty) then
    raise(Error(smod.pmod_loc, Non_generalizable_module mty));
    { tmty with mod_type = mty }

(* For Typecore *)

let rec get_manifest_types = function
    [] -> []
  | Sig_type (id, {type_params=[]; type_manifest=Some ty}, _) :: rem ->
      (Ident.name id, ty) :: get_manifest_types rem
  | _ :: rem -> get_manifest_types rem

let type_package env m p nl tl =
  let modl = type_module env m in
  if nl = [] then (wrap_constraint env modl (Mty_ident p) Tmodtype_implicit, []) else
  let msig = extract_sig env modl.mod_loc modl.mod_type in
  let mtypes = get_manifest_types msig in
  let tl' =
    List.map2
      (fun name ty -> try List.assoc name mtypes with Not_found -> ty)
      nl tl
  in
  let mty = modtype_of_package env modl.mod_loc p nl tl' in
  (wrap_constraint env modl mty Tmodtype_implicit, tl')

(* Fill in the forward declarations *)
let () =
  Typecore.type_module := type_module;
  Typetexp.transl_modtype_longident := transl_modtype_longident;
  Typetexp.transl_modtype := transl_modtype;
  Typecore.type_open := type_open;
  Typecore.type_package := type_package;
  type_module_type_of_fwd := type_module_type_of

(* Typecheck an implementation file *)

let type_implementation sourcefile outputprefix modulename initial_env ast =
  Typecore.reset_delayed_checks ();
  let (str, sg, finalenv) = type_structure initial_env ast Location.none in
  let simple_sg = simplify_signature sg in
  Typecore.force_delayed_checks ();
  if !Clflags.print_types then begin
    fprintf std_formatter "%a@." Printtyp.signature simple_sg;
    (str, Tcoerce_none)   (* result is ignored by Compile.implementation *)
  end else begin
    let sourceintf =
      Misc.chop_extension_if_any sourcefile ^ !Config.interface_suffix in
    if Sys.file_exists sourceintf then begin
      let intf_file =
        try
          find_in_path_uncap !Config.load_path (modulename ^ ".cmj")
        with Not_found ->
          raise(Error(Location.none, Interface_not_compiled sourceintf)) in
      let dclsig = Env.read_signature modulename intf_file in
      let coercion = Includemod.compunit sourcefile sg intf_file dclsig in
      (str, coercion)
    end else begin
      check_nongen_schemes finalenv str.str_items;
      normalize_signature finalenv simple_sg;
      let coercion =
        Includemod.compunit sourcefile sg
                            "(inferred signature)" simple_sg in
      if not !Clflags.dont_write_files then
        Env.save_signature simple_sg modulename (outputprefix ^ ".cmj_temp");
      (str, coercion)
    end
  end

let type_implementation sourcefile outputprefix modulename initial_env ast =
  try
    Typedtree.set_saved_types [];
    let (str, coercion) = type_implementation sourcefile outputprefix modulename initial_env ast in
    if !Clflags.annotations then begin
        Typedtree.set_saved_types [];
        let oc = open_out (outputprefix ^ ".types") in
        output_value oc [| Saved_implementation str |];
        close_out oc;

(*
        let oc = open_out (outputprefix ^ "_ast2src.ml") in
        let ppf = Format.formatter_of_out_channel oc in
        Pprintast.print_structure ppf ast;
        Format.pp_print_flush ppf ();
        close_out oc;


        let oc = open_out (outputprefix ^ "_typ2src.ml") in
        let ppf = Format.formatter_of_out_channel oc in
        Pprintast.print_structure ppf (Untypeast.untype_structure str);
        Format.pp_print_flush ppf ();
        close_out oc;
*)
      end;
    (str, coercion)
  with e ->
      if !Clflags.annotations then begin
          let oc = open_out (outputprefix ^ ".types") in
          output_value oc (Array.of_list (Typedtree.get_saved_types ()));
          close_out oc;
        end;
      Typedtree.set_saved_types  [];
      raise e

(* "Packaging" of several compilation units into one unit
   having them as sub-modules.  *)

let rec package_signatures subst = function
    [] -> []
  | (name, sg) :: rem ->
      let sg' = Subst.signature subst sg in
      let oldid = Ident.create_persistent name
      and newid = Ident.create name in
      Sig_module(newid, Mty_signature sg', Trec_not) ::
      package_signatures (Subst.add_module oldid (Pident newid) subst) rem

let package_units objfiles cmifile modulename =
  (* Read the signatures of the units *)
  let units =
    List.map
      (fun f ->
         let pref = chop_extensions f in
         let modname = String.capitalize_ascii(Filename.basename pref) in
         let sg = Env.read_signature modname (pref ^ ".cmj") in
         if Filename.check_suffix f ".cmj" &&
            not(Mtype.no_code_needed_sig Env.initial sg)
         then raise(Error(Location.none, Implementation_is_required f));
         (modname, Env.read_signature modname (pref ^ ".cmj")))
      objfiles in
  (* Compute signature of packaged unit *)
  Ident.reinit();
  let sg = package_signatures Subst.identity units in
  (* See if explicit interface is provided *)
  let mlifile =
    chop_extension_if_any cmifile ^ !Config.interface_suffix in
  if Sys.file_exists mlifile then begin
    if not (Sys.file_exists cmifile) then begin
      raise(Error(Location.in_file mlifile, Interface_not_compiled mlifile))
    end;
    let dclsig = Env.read_signature modulename cmifile in
    Includemod.compunit "(obtained by packing)" sg mlifile dclsig
  end else begin
    (* Determine imports *)
    let unit_names = List.map fst units in
    let imports =
      List.filter
        (fun (name, crc) -> not (List.mem name unit_names))
        (Env.imported_units()) in
    (* Write packaged signature *)
    Env.save_signature_with_imports sg modulename cmifile imports;
    Tcoerce_none
  end

(* Error report *)

open Printtyp

let report_error ppf = function
    Cannot_apply mty ->
      fprintf ppf
        "@[This module is not a functor; it has type@ %a@]" modtype mty
  | Not_included errs ->
      fprintf ppf
        "@[<v>Signature mismatch:@ %a@]" Includemod.report_error errs
  | Cannot_eliminate_dependency mty ->
      fprintf ppf
        "@[This functor has type@ %a@ \
           The parameter cannot be eliminated in the result type.@  \
           Please bind the argument to a module identifier.@]" modtype mty
  | Signature_expected -> fprintf ppf "This module type is not a signature"
  | Structure_expected mty ->
      fprintf ppf
        "@[This module is not a structure; it has type@ %a" modtype mty
  | With_no_component lid ->
      fprintf ppf
        "@[The signature constrained by `with' has no component named %a@]"
        longident lid
  | With_mismatch(lid, explanation) ->
      fprintf ppf
        "@[<v>\
           @[In this `with' constraint, the new definition of %a@ \
             does not match its original definition@ \
             in the constrained signature:@]@ \
           %a@]"
        longident lid Includemod.report_error explanation
  | Repeated_name(kind, name) ->
      fprintf ppf
        "@[Multiple definition of the %s name %s.@ \
           Names must be unique in a given structure or signature.@]" kind name
  | Non_generalizable typ ->
      fprintf ppf
        "@[The type of this expression,@ %a,@ \
           contains type variables that cannot be generalized@]" type_scheme typ
  | Non_generalizable_class (id, desc) ->
      fprintf ppf
        "@[The type of this class,@ %a,@ \
           contains type variables that cannot be generalized@]"
        (class_declaration id) desc
  | Non_generalizable_module mty ->
      fprintf ppf
        "@[The type of this module,@ %a,@ \
           contains type variables that cannot be generalized@]" modtype mty
  | Implementation_is_required intf_name ->
      fprintf ppf
        "@[The interface %s@ declares values, not just types.@ \
           An implementation must be provided.@]" intf_name
  | Interface_not_compiled intf_name ->
      fprintf ppf
        "@[Could not find the .cmj file for interface@ %s.@]" intf_name
  | Not_allowed_in_functor_body ->
      fprintf ppf
        "This kind of expression is not allowed within the body of a functor."
  | With_need_typeconstr ->
      fprintf ppf
        "Only type constructors with identical parameters can be substituted."
  | Not_a_packed_module ty ->
      fprintf ppf
        "This expression is not a packed module. It has type@ %a"
        type_expr ty
  | Incomplete_packed_module ty ->
      fprintf ppf
        "The type of this packed module contains variables:@ %a"
        type_expr ty
