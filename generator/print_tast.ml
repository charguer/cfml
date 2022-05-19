open Typedtree
open Mytools
open Format
open Print_type
open Print_common

(** Printing facility for typed abstract syntax trees produced by the
    type-checker*)


(** For extra verbosity on types, turn this flag on *)
(* TODO : extend this to all constructs of the language;
   currently it is only used for constructors. *)

let print_tast_with_all_types = ref true


(*#########################################################################*)
(* ** Printing of items *)

let string_of_typed_var s t =
   sprintf "(%s : %s)" s (string_of_type_exp t)

let string_of_path p =
   Path.name p

let string_of_fvs fvs =
   if fvs = []
      then ""
      else sprintf "[%s]" (show_list show_str " " (List.map string_of_type_exp fvs))


(*#########################################################################*)
(* ** Printing of patterns *)

let string_of_pattern par p =
   let rec aux par p =
     match p.pat_desc with
     | Tpat_any -> "_"
     | Tpat_var id -> string_of_typed_var (string_of_ident id) p.pat_type
     | Tpat_alias (p, ak) ->
         let sp = aux false p in
         begin match ak with
         | TPat_alias id -> show_par par (sprintf "%s as %s" (string_of_typed_var (string_of_ident id) p.pat_type) sp)
         | TPat_constraint _ -> sp
         | TPat_type pp -> sp (* ignore type *)
         end
     | Tpat_constant c ->
         sprintf "%s" (string_of_constant c)
     | Tpat_tuple l ->
         show_par true (sprintf "%s" (show_list (aux false) "," l))
     | Tpat_construct (p,cd,ps) ->
         let c = string_of_path p in
         if ps = []
            then c
         else if List.length ps = 1
            then show_par par (c ^ " " ^ aux true (List.hd ps))
         else
            show_par par (sprintf "%s (%s)" c (show_list (aux false) "," ps))
     | Tpat_or (p1,p2,_) ->
         show_par par (sprintf "%s | %s" (aux false p1) (aux false p2))
     | Tpat_lazy p1 ->
        show_par par (sprintf "lazy %s" (aux true p1))
     | Tpat_variant (_,_,_) -> unsupported_noloc "variant patterns"
     | Tpat_record _ -> unsupported_noloc "record patterns"
     | Tpat_array pats -> unsupported_noloc "array patterns"
     in
  aux false p

let string_of_let_pattern par fvs p =
   string_of_pattern par p
   (* let typ = p.pat_type in
   let styp = string_of_type_sch fvs typ in
   sprintf "%s : %s" (string_of_pattern par p) styp *)
   (*
   match p.pat_desc with
   | Tpat_var id ->
      let typ = p.pat_type in
      sprintf "%s : %s" (string_of_ident id) (string_of_type_sch fvs typ)
   | _ -> unsupported_noloc "let-pattern not reduced to a variable"
   *)


(*#########################################################################*)
(* ** Printing of expression *)

let rec string_of_expression par e =
   let show_par_and_type par s =
      if not !print_tast_with_all_types
        then show_par par s
        else sprintf "(%s : %s)" s (string_of_type_exp e.exp_type)
      in
   let aux ?par e =
      string_of_expression (bool_of_option par) e in
   let aux_pat ?par e =
      string_of_pattern (bool_of_option par) e in
   let string_of_branch (p,e) =
      Format.sprintf "@[@[%s@] ->@ @[%s@]@]" (aux_pat p) (aux e) in
   (*let typ = e.exp_type in*)
   match e.exp_desc with
   | Texp_ident (p,vd) -> string_of_path p (*  string_of_typed_var (string_of_path p) vd.val_type*)
   | Texp_constant c -> string_of_constant c
   | Texp_let (rf, fvs, l, e) ->
       let show_pe (p,e) =
          let sp = (string_of_let_pattern false fvs p) in
          let se = aux e in
          Format.sprintf "%s =@ @[%s@]" sp se in
       let sl = show_list show_pe " and " l in
       let se = aux e in
       Format.sprintf "@[let%s%s %s in@ @[%s@]@]" (string_of_recflag rf) (string_of_fvs fvs) sl se
   | Texp_function (_,(p1,e1)::[], pa) ->
       let rec explore pats e =
          match e.exp_desc with
          | Texp_function (_,(p1,e1)::[], pa) ->
             explore (p1::pats) e1
          | _ -> List.rev pats, e
          in
       let pats,body = explore [] e in
       let sp = show_list aux_pat " " pats in
       let sb = aux ~par:false body in
       let s = Format.sprintf "@[fun @[%s@] ->@ @[%s@]@]" sp sb in
      show_par par s
   | Texp_function (_,l, pa) ->
       Format.sprintf "@[function %s@]" (show_listp string_of_branch "\n  | " l)
   | Texp_apply (e, l) -> (* todo: afficher les infixes correctement *)
      let l = List.map (fun (lab,eo,opt) -> match eo with None -> unsupported_noloc "optional apply arguments" | Some ei -> ei) l in
      let se = aux ~par:true e in
      let show_arg ei =
         let s_ei = aux ~par:false ei in
         let t_ei = string_of_type_exp ei.exp_type in
         sprintf "(%s : %s)" s_ei t_ei in
      let sl = show_list show_arg " " l in
      let s = sprintf "%s %s" se sl in
      show_par par s
   | Texp_match (e, l, pa) ->
       let se = aux e in
       let s = Format.sprintf "@[match@ @[%s@] with@ @[%s@]@]"
          se (show_list string_of_branch " | " l) in
       show_par par s
   | Texp_try (e,l) -> unsupported_noloc "exceptions"
   | Texp_tuple l ->
       show_par true (show_list aux ", " l)
   | Texp_construct (p, cd, es) ->
       let c = string_of_path p in
       if es = [] then
          show_par_and_type false c
       else if List.length es = 1 then
          show_par_and_type par (c ^ " " ^ aux ~par:true (List.hd es))
       else
          show_par_and_type par (sprintf "%s (%s)" c (show_list aux "," es))
   | Texp_variant (l,eo) -> unsupported_noloc "variants"
   | Texp_record (l,eo) ->
       let print_item (p,li,ei) =
          Format.sprintf "%s = %s" (string_of_path p) (aux ei) in
       let sbase = match eo with
          | None -> ""
          | Some ebase -> " " ^ aux ebase ^ " with "
          in
       let s = Format.sprintf "@[{%s%s}@]" (sbase) (show_list print_item "; " l) in
       show_par par s
   | Texp_field (e,p,i) ->
       let s = Format.sprintf "@[%s.%s@]" (aux e) (string_of_path p) in
       show_par par s
   | Texp_setfield (e,p,i,e2) ->
       let s = Format.sprintf "@[%s.%s <- %s@]" (aux e) (string_of_path p) (aux e2) in
       show_par par s
   | Texp_array l ->
       Format.sprintf "[| %s |]" (show_list aux "; " l)
   | Texp_ifthenelse (e1, e2, None) ->
       let s = Format.sprintf "@[if %s@ then %s@]" (aux e1) (aux e2) in
       show_par par s
   | Texp_ifthenelse (e1, e2, Some e3) ->
       let s = Format.sprintf "@[if %s@ then %s@ else %s@]" (aux e1) (aux e2) (aux e3) in
       show_par par s
   | Texp_when (e1,e2) ->  (*todo:better printing so that compiles *)
       Format.sprintf "<< when %s >> %s" (aux e1) (aux e2)
   | Texp_sequence (e1,e2) ->
       let s = Format.sprintf "@[%s@ ; %s@]" (aux e1) (aux e2) in
       show_par par s
   | Texp_while (e1,e2) ->
       let s = Format.sprintf "@[while %s@ do %s@ done@]" (aux e1) (aux e2) in
       show_par par s
   | Texp_for (i,e1,e2,d,e3) ->
       let s = Format.sprintf "@[for %s = %s to %s do@ %s@ done@]" (Ident.name i) (aux e1) (aux e2) (aux e3) in
       show_par par s
   | Texp_send (_,_,_) -> unsupported_noloc "send expression"
   | Texp_new _ -> unsupported_noloc "new expression"
   | Texp_instvar (_,_) -> unsupported_noloc "inst-var expression"
   | Texp_setinstvar (_,_,_) -> unsupported_noloc "set-inst-var expression"
   | Texp_override _ -> unsupported_noloc "Pexp_override expression"
   | Texp_letmodule (_,_,_) -> unsupported_noloc "let-module expression"
   | Texp_assert e ->
       let s = Format.sprintf "@[assert %s@]" (aux e) in
       show_par par s
   | Texp_assertfalse ->
       show_par par "assert false"
   | Texp_lazy e ->
       let s = Format.sprintf "@[lazy %s@]" (aux e) in
       show_par par s
   | Texp_object _ -> unsupported_noloc "objects"
   | Texp_poly (_,_) -> unsupported_noloc "poly"
   | Texp_newtype (_,_) -> unsupported_noloc "newtype"
   | Texp_pack _ -> unsupported_noloc "pack"
   | Texp_open  (_,_) -> unsupported_noloc "open"
   | Texp_constraint (e,_,_) ->
       Format.sprintf "@[(%s@ : _)@]" (aux e)


(*#########################################################################*)
(* ** Printing of type declarations *)

(* TODO

let show_core_type par t =
  let rec aux par t =
     match t.ctyp_desc with
     | Ttyp_any -> "_"
     | Ttyp_var x -> "'"^x
     | Ttyp_arrow (_,t1,t2) -> show_par par (sprintf "%s -> %s" (aux false t1) (aux false t2))
     | Ttyp_tuple ts -> show_par true (show_list (aux true) " * " ts)
     | Ttyp_constr (p,ts) ->
         let args = match ts with
           | [] -> ""
           | [x] -> sprintf "%s" (aux true x)
           | l -> show_par true (show_list (aux false) ", " l)
           in
         sprintf "%s %s" args (string_of_path p)
     | Ttyp_object _ -> unsupported_noloc "object types"
     | Ttyp_class _ -> unsupported_noloc "class types"
     | Ttyp_alias _ -> unsupported_noloc "alias types"
     | Ttyp_variant  _ -> unsupported_noloc "variant types"
     | Ttyp_poly _ -> unsupported_noloc "poly types"
     | Ttyp_package _ -> unsupported_noloc "package types"
     in
  aux par t


let show_type_decl (name,decl) =
   let show_type t =
     show_core_type false t in
   let params =
      match decl.typ_params with
      | [] -> ""
      | [a] -> sprintf "'%s " a
      | l -> show_par true (show_list show_string ", " l) ^ " "
      in
   let header = sprintf " %s%s" params (string_of_ident name) in
   match decl.typ_kind with
   | Ttype_abstract ->
       begin match decl.typ_manifest with
       | None -> header
       | Some def -> sprintf "%s = %s" header (show_type def)
       end
   | Ttype_record _ (* (string * mutable_flag * core_type * Location.t) list *) ->
        unsupported_noloc "records type def (todo)"
   | Ttype_variant branches ->
       let show_branch (constr, args, _) =
          match args with
          | [] -> constr
          | [a] -> sprintf "%s of %s" constr (show_type a)
          | l -> sprintf "%s of %s" constr (show_par true (show_list show_type "* " l))
          in
       header ^ " = " ^ show_list show_branch " | " branches

let is_simple_type_decl (name,decl) =
  match decl.typ_kind with
    Ttype_record _ -> true
  | Ttype_abstract -> true
  | _ -> false

*)

(*#########################################################################*)
(* ** Printing of modules and top-level phrases *)

let rec string_of_module m =
   match m.mod_desc with
   | Tmod_ident p -> string_of_path p
   | Tmod_structure s -> sprintf "struct\n%s\nend\n" (string_of_structure s)
   | Tmod_functor (id,mt,me) -> sprintf "%s : _ ==>%s\n" (string_of_ident id) (string_of_module me)
   | Tmod_apply (me1,me2,mc) -> sprintf "%s %s" (string_of_module me1) (string_of_module me2)
   | Tmod_constraint (me,_,mt,mc) -> sprintf "(%s : _)" (string_of_module me)
   | Tmod_unpack (_,_) -> unsupported_noloc "unpack"

and string_of_structure (s:structure) =
  show_list string_of_structure_item lin2 s.str_items

and string_of_structure_item (si:structure_item) =
   Printtyp.reset();
   match si.str_desc with
   | Tstr_eval e -> sprintf "let _ = %s" (string_of_expression false e)
   | Tstr_value (r,fvs,l) ->
       let show_pe (p,e) =
          let sp = string_of_let_pattern false fvs p in
          let se = string_of_expression false e in
          Format.sprintf "%s =@ @[%s@]" sp se in
       let sl = show_list show_pe " and " l in
       Format.sprintf "@[let%s%s %s@]" (string_of_recflag r) (string_of_fvs fvs) sl
      (* Format.sprintf "@[let%s %s =@ @[<2>%s@]@]" *)
   | Tstr_primitive (id,v) -> sprintf "val %s : 'external" (string_of_ident id)
   | Tstr_type l -> sprintf "type _ = _"
   | Tstr_exception (id,e) -> sprintf "exception %s = _" (string_of_ident id)
   | Tstr_exn_rebind (id,p) -> unsupported_noloc "exception-rebind"
   | Tstr_module (id,m) -> Format.sprintf "@[module %s =@ @[<2>%s] @]" (string_of_ident id) (string_of_module m)
   | Tstr_recmodule _ -> unsupported_noloc "recursive modules"
   | Tstr_modtype (id,mt) -> sprintf "module type %s = _" (string_of_ident id)
   | Tstr_open p -> sprintf "open %s = _" (string_of_path p)
   | Tstr_class _ -> unsupported_noloc "objects"
   | Tstr_class_type _ -> unsupported_noloc "objects"
   | Tstr_include (m,ids) -> sprintf "include %s" (string_of_module m)
