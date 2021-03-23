open Asttypes
open Parsetree
open Mytools
open Longident
open Renaming

(* TODO: the field-get operations on pure records should be considered as values *)

(** This file takes as input an abstract syntax tree and produces
    an abstract syntax tree in "normal form", i.e. where intermediate
    expressions have been bound to a name. *)

(*#########################################################################*)
(* ** Management of identifiers *)

let name_of_lident idt =
  let words = Longident.flatten idt in
  let name = List.hd (List.rev words) in
  name

(* FIXME unused
let fullname_of_lident idt =
  let words = Longident.flatten idt in
  String.concat "." words

let check_lident loc idt = (* DEPRECATED *)
   check_var_name loc (name_of_lident idt)
 *)

(*#########################################################################*)
(* ** Control of evaluation order *)

let reverse_if_right_to_left_order args =
  if !Mytools.use_left_to_right_order then args else List.rev args



(*#########################################################################*)
(* ** Detection of primitive functions and exception-raising *)

let get_qualified_pervasives_name lident =
   let name = name_of_lident lident in
   if !Clflags.nopervasives
      then "Pervasives." ^ name  (* unqualified name when from inside Pervasives *)
      else "Pervasives." ^ name  (* name when from outside might be qualified or not; usually it is not, so we add the prefix; if it is already qualified, then we will miss it by prefixing once more.... maybe we need to check if the name already starts with Pervasives? TODO: fix this *)


let exp_is_inlined_primitive e largs =
    let args = List.map snd largs in (* todo: check no labels*)
    match e.pexp_desc with
    | Pexp_ident f ->
       let shortname = name_of_lident f in
       let name = get_qualified_pervasives_name f in
       begin match args with

       | [n; {pexp_desc = Pexp_constant (Const_int m)}]
           (* Remark: we impose elsewhere a check that the names "mod" and "/"
              and "&&" and "||" are not bound outside of Pervasives *)
             when m <> 0 && List.mem shortname ["mod"; "/"] ->
           begin match find_inlined_primitive name with
           | Some (Primitive_binary_div_or_mod, coq_name) -> true
           | _ -> false
          end

       | [e1; e2]
          when List.mem shortname ["&&"; "||"] -> true
          (* Remark: this check is not complete; it is only useful to ensure
             that values_variables won't fail *)

       | [e1; e2]
          when List.mem shortname ["<="; ">="; "<"; ">"; "min"; "max"] -> true
          (* Remark: here we don't check that the types of the arguments are numbers;
             we will catch this later in the characteristic formula generation *)

       | _ ->
           let arity = List.length args in
           begin match find_inlined_primitive name with
           | Some (Primitive_unary, coq_name) when arity = 1 -> true
           | Some (Primitive_binary, coq_name) when arity = 2 -> true
           (* remark: this case should have been caught earlier by [is_lazy_binary_op], so:
              | Some (Primitive_binary_lazy, coq_name) when arity = 2 -> assert false
           *)
           | _ -> false
           end

       end

    | _ -> false



let is_failwith_function e =
   match e.pexp_desc with
   | Pexp_ident li ->
      begin match Longident.flatten li with
        (* TODO: check that failwith/invalide_arg/raise indeed come from Pervasives *)
      | f::[] -> (f = "failwith") || (f = "invalid_arg") || (f = "raise")
      | _ -> false
      end
   | _ -> false

let is_lazy_binary_op e =
   match e.pexp_desc with
   | Pexp_ident f
     when let x = name_of_lident f in x = "&&" || x = "||" -> true
   | _ -> false



(*#########################################################################*)
(* ** Normalization of patterns *)

let normalize_pattern p =
   let i = ref (-1) in
   let next_name () =
      incr i; (pattern_generated_name !i) in
   let rec aux p =
     let loc = p.ppat_loc in
     { p with ppat_desc = match p.ppat_desc with
     | Ppat_any -> Ppat_var (next_name())
     | Ppat_var s ->
        (* hack to handle generated vars *)
        if loc <> Location.none then check_var_name loc s;
        Ppat_var s
     | Ppat_alias (p, s) -> check_var_name loc s; Ppat_alias (aux p, s)
     | Ppat_constant c -> Ppat_constant c
     | Ppat_tuple l -> Ppat_tuple (List.map aux l)
     | Ppat_construct (li, po, b) -> Ppat_construct (li, option_map aux po, b)
     | Ppat_variant (_,_) -> unsupported loc "variant patterns"
     | Ppat_record (l,f) -> Ppat_record (List.map (fun (li,pi) -> (li, aux pi)) l, f)
     | Ppat_array pats -> unsupported loc "array patterns"
     | Ppat_or (p1,p2) -> unsupported loc "or patterns are only supported at pattern root"
     | Ppat_constraint (p,t) -> Ppat_constraint (aux p,t)
     | Ppat_type t -> Ppat_type t
     | Ppat_lazy p1 -> Ppat_lazy (aux p1)
     | Ppat_unpack p1 -> unsupported loc "array unpack"
     } in
  aux p


(*#########################################################################*)
(* ** Free variables of patterns and values *)

let rec pattern_variables p =
   let loc = p.ppat_loc in
   let aux = pattern_variables in
   match p.ppat_desc with
   | Ppat_any -> []
   | Ppat_var s -> [s]
   | Ppat_alias (p, s) -> s::(aux p)
   | Ppat_constant c -> []
   | Ppat_tuple l -> list_concat_map aux l
   | Ppat_construct (li, po, b) -> option_app [] aux po
   | Ppat_variant (_,_) -> unsupported loc "variant patterns"
   | Ppat_record (l,_) -> unsupported loc "record patterns" (* list_concat_map (fun (li,pi) -> aux pi) l *)
   | Ppat_array pats -> unsupported loc "array patterns"
   | Ppat_or (p1,p2) -> unsupported loc "or patterns are only supported at pattern root"
   | Ppat_constraint (p,t) -> aux p
   | Ppat_type t -> []
   | Ppat_lazy p1 -> aux p1
   | Ppat_unpack p1 -> unsupported loc "array unpack"

let rec values_variables e =
   let aux = values_variables in
   match e.pexp_desc with
   | Pexp_ident (Lident x) -> [x]
   | Pexp_ident li -> []
   | Pexp_constant c -> []
   | Pexp_apply (e0, l) when exp_is_inlined_primitive e0 l ->
      list_concat_map aux (List.map snd l)
   | Pexp_tuple l ->
      list_concat_map aux l
   | Pexp_construct (li, eo, b) ->
      option_app [] aux eo
   | Pexp_field (e,i) ->
      aux e
   | Pexp_constraint (e,to1,to2) ->
      aux e
   | Pexp_assertfalse ->
      []
   | Pexp_lazy e ->
      aux e
   | _ -> failwith "Bug in normalization: values_variables called on a non-atomic value"
   (*
   | Pexp_record (l,None) ->
      let l',bi = List.split (List.map (fun (i,(e,b)) -> ((i,e),b)) (assoc_list_map (aux false) l)) in
      return (Pexp_record (l', None)), List.flatten bi
   | Pexp_array l -> unsupported loc "array expression" (* Pexp_array (List.map aux l)*)
   *)



(*#########################################################################*)
(* ** Auxiliary types *)

let get_unit_type ?(loc=Location.none) () =
   { ptyp_desc = Ptyp_constr (Lident "unit", []); ptyp_loc = loc }


(*#########################################################################*)
(* ** Normalization of expression *)

type bindings = (pattern*expression) list

let create_let loc (bs:bindings) (e:expression) =
   let rec aux = function
      | [] -> e
      | b::bs ->
         { pexp_loc = loc;
           pexp_desc = Pexp_let (Nonrecursive, [b], aux bs) } in
   aux bs

let create_match_one loc exp pat body =
   { pexp_loc = loc;
     pexp_desc = Pexp_match (exp,[pat,body]) }


(* See documentation of [wrap_as_value e' b] further below *)
let wrap_if_needed loc needs_wrapping new_name e b =
  (* : expression -> bindings -> expression * bindings *)
   if needs_wrapping
      then let x = new_name() in
           let p = { ppat_loc = loc; ppat_desc = Ppat_var x } in
           let e' = { pexp_loc = loc; pexp_desc = Pexp_ident (Lident x) } in
           e', b @ [ p, e ]
      else e,b

(* The main translation function takes an expression [e] and produces
   a translated expression [e'] and a set of bindings [b] in which [e']
   properly evaluates to a value. The bindings in [b] should in particular
   account for all side-effects performed by [e], in the right order.

   The argument [as_value] indicates whether the context in which [e] appears
   requires the production of a value. In this case, if the translation of
   [e] is not a value, then it is given as a fresh variable [x], together
   with an additional binding from [x] to [e].

   The argument [is_named] indicates whether the context in which [e] appears
   is already a [let x = ... in ..]. If this is the case and we
   encounter a function, then we don't need to introduce a fresh name
   for it. Otherwise, any occurence of [fun .. -> ..] will be turned
   into [let f = fun .. -> .. in f], for a fresh name f. *)

let normalize_expression ?is_named:(is_named=false) ?as_value:(as_value=false) e =
   let i = ref (-1) in (* TODO: use a gensym function *)
   let next_var () =
      incr i; (variable_generated_name !i) in
   let j = ref (-1) in
   let next_func () =
      incr j; (function_generated_name !j) in
   let rec aux ?is_named:(is_named=false) ?as_value:(as_value=false) (e:expression) : expression * bindings =
     let loc = e.pexp_loc in
     let return edesc' =
       { e with pexp_desc = edesc' } in
     let return_pat p =
       { ppat_loc = loc; ppat_desc = p } in
     let mk_bool bvalue =
       let svalue = if bvalue then "true" else "false" in
       let explicit_arity = false in (* todo: what does it mean? *)
       return (Pexp_construct (Lident svalue, None, explicit_arity)) in

     (* [wrap_as_value e' b] takes a a transformed expression and a list
        of bindings; and it returns a transformed expression and a list
        of bindings. If the parameter [named] is true, then this returns
        simply [(e',b)]. Otherwise, it returns a pair [(var x, b')],
        where [b'] extends [b] with the binding from [x] to [e'].
        This function should be called any time the translation
        produces a term that may not be a value.  *)
     let wrap_as_value e b =
        wrap_if_needed loc as_value next_var e b in

     match e.pexp_desc with
      | Pexp_ident li -> return (Pexp_ident li), []
      | Pexp_constant c -> return (Pexp_constant c), []
      | Pexp_let (Recursive, l, eb) ->
          let l' = List.map (protect_branch ~is_named:true) l in
          let eb' = protect eb in
          let e' = Pexp_let (Recursive, l', eb') in
          wrap_as_value (return e') []
      | Pexp_let (rf, [], e2) -> unsupported loc "let without any binding"
      | Pexp_let (rf, [p1,e1], e2) ->
         begin match p1.ppat_desc with
         | Ppat_var x
         | Ppat_constraint ({ ppat_desc = Ppat_var x}, _) ->
             let e1',b1 = aux ~is_named:true e1 in
             let e' = create_let loc b1 (
                      create_let loc [normalize_pattern p1, e1'] (
                       protect e2)) in
             wrap_as_value e' []
         | _ ->
            (* [let p1 = e1 in e2] is viewed as [match e1 with p1 -> e2] *)
             let e1',b1 = aux ~is_named:true ~as_value:true e1 in
             let e' = create_let loc b1 (
                      create_match_one loc e1' (normalize_pattern p1) (protect e2)) in
             wrap_as_value e' []
         end
      | Pexp_let (rf, l, e) -> unsupported loc "non-recursive let-and construct"
          (* DEPRECATED --seems   buggous
          let check_is_named_pat p =
             match p.ppat_desc with
             | Ppat_var x
             | Ppat_constraint ({ ppat_desc = Ppat_var x}, _) -> true
             | _ -> false
             in
          if not (List.for_all check_is_named_pat (List.map fst l))
             then unsupported loc "let-rec with patterns not reduced to names";
          aux true (List.fold_right (fun (pi,ei) eacc -> create_let loc [pi,ei] eacc) l e)
          *)
      | Pexp_function (lab, None, [_]) ->
          (* [function x1 p2 x3 p4 x5 -> e] is translated as
             [fun x1 x2 x3 x4 x5 ->
                match x2 with p2 ->
                match x4 with p4 -> e']
          *)
          let rec trans_func (ms : (expression * pattern) list) (e : expression) =
             match e.pexp_desc with
             | Pexp_function (lab, None, [p, e']) ->
                 let p' = normalize_pattern p in
                 begin match p'.ppat_desc with
                 | Ppat_var x
                 | Ppat_constraint ({ ppat_desc = Ppat_var x}, _) ->
                    return (Pexp_function (lab, None, [p', trans_func ms e']))
                 | Ppat_construct (li, None, b) when Longident.flatten li = ["()"] ->
                    let x = next_var() in
                    let px = return_pat (Ppat_var x) in
                    let tunit = get_unit_type ~loc:loc () in
                    let px_typ = return_pat (Ppat_constraint (px, tunit)) in
                    return (Pexp_function (lab, None, [px_typ, trans_func ms e']))
                 | _ ->
                    let x = next_var() in
                    let px = return_pat (Ppat_var x) in
                    let vx = return (Pexp_ident (Lident x)) in
                      (* DEPRECATED let vx = { pexp_loc = loc; pexp_desc = Pexp_ident (Lident x) } *)
                    let ms' = (vx, p')::ms in
                    return (Pexp_function (lab, None, [px, trans_func ms' e']))
                 end
             | _ ->
                let addmatch eacc (vi,pi) =
                   return (Pexp_match (vi, [pi,eacc])) in
                List.fold_left addmatch (protect ~is_named:is_named e) ms
            in
           (* here we force the wrapping whenever [is_named] or [as_value] is true *)
           wrap_if_needed loc (as_value || not is_named) next_func (trans_func [] e) []
      | Pexp_function (lab, None, l) ->
          (* [function p1 -> e1 | p2 -> e2] encoded as the translation of
             [function x_ match x_ with p1 -> e1 | p2 -> e2] *)
          let x = next_var() in  (* todo: factorize next three lines of code *)
          let px = { ppat_loc = Location.none (* hack to pass check-var *); ppat_desc = Ppat_var x } in (* todo: better hack to remember created var *)
          let vx = { pexp_loc = Location.none (* hack to pass check-var *); pexp_desc = Pexp_ident (Lident x) } in
          let e' = return (Pexp_match (vx, l)) in
          aux ~is_named:is_named (return (Pexp_function (lab, None, [px,e'])))
      | Pexp_function (p, Some _, l) ->
         unsupported loc "function with optional expression"
      | Pexp_apply (e0, l) when is_failwith_function e0 ->
         return Pexp_assertfalse, []
      | Pexp_apply (e0, [(l1,e1); (l2,e2)]) when is_lazy_binary_op e0 ->
         (* This case is for [e1 && e2] and [e1 || e2] *)
         (* TODO: assert that the labels are irrelevant here *)
         let e0',b0 = aux ~as_value:true e0 in
         let name = match e0.pexp_desc with
            | Pexp_ident f -> name_of_lident f
            | _ -> assert false (* could not be a lazy op otherwise *)
            in
         assert (b0 = []); (* since e0 should be "&&" or "||" *)
         let e1',b1 = aux ~as_value:true e1 in
         let e2',b2 = aux ~as_value:true e2 in
         if b2 = [] then begin
           if b1 = [] then begin
              (* produce: <e1> && <e2>
                          <e1> || <e2> *)
              return (Pexp_apply (e0', [(l1,e1'); (l2,e2')])), []
           end else begin
              (* produce: let <b1> in <e1> && <e2>
                          let <b1> in <e1> || <e2> *)
              wrap_as_value (return (Pexp_apply (e0', [(l1,e1'); (l2,e2')]))) b1
           end
         end else begin
           (* TODO: how to avoid the redundant computations of [aux e2]?
              We need to return two results, one as a value, one not as a value. *)
           let e2',b2 = aux ~as_value:false e2 in
           if name = "&&" then begin
             (* produce: let <b1> in if <e1'> then (let <b2> in <e2'>) else false *)
               wrap_as_value (return (
                  Pexp_ifthenelse (
                    e1',
                    create_let loc b2 e2',
                    Some (mk_bool false)))) b1
           end else if name = "||" then begin
             (* produce: let <b1> in if <e1'> then true else (let <b2> in <e2'>) *)
               wrap_as_value (return (
                  Pexp_ifthenelse (
                    e1',
                    mk_bool true,
                    Some (create_let loc b2 e2')))) b1
           end else assert false
         end
      | Pexp_apply (e0, l) ->
         let is_inlined = exp_is_inlined_primitive e0 l in
         let e0',b0 = aux ~as_value:true e0 in
         let ei',bi = List.split (List.map (fun (lk,ek) -> let ek',bk = aux ~as_value:true ek in (lk, ek'), bk) l) in
         let e' = return (Pexp_apply (e0', ei')) in
         let b' = List.flatten (reverse_if_right_to_left_order (b0::bi)) in
         if is_inlined
            then e', b'
            else wrap_as_value e' b'
      | Pexp_match (e0, l) ->
         let e0',b0 = aux ~as_value:true e0 in
         let l' =
            let rec or_pats (p,e) =
               match p.ppat_desc with
               | Ppat_or (p1,p2) -> or_pats (p1, e) @ or_pats (p2, e)
               | _ -> [(p,e)]
               in
            list_concat_map or_pats l in
         let pat_vars = list_concat_map pattern_variables (List.map fst l') in
         let is_naming_required =
            list_intersect pat_vars (values_variables e0') <> [] in
         let e0',b0 =
            if not is_naming_required then e0',b0 else begin
              let x = next_var() in
              let px = return_pat (Ppat_var x) in
              let vx = return (Pexp_ident (Lident x)) in
                (* DEPRECATED let vx = { pexp_loc = loc; pexp_desc = .. } *)
              vx, b0@[px,e0']
            end in
         let e' = Pexp_match (e0', List.map protect_branch l') in
         wrap_as_value (return e') b0
      | Pexp_try (e,l) -> unsupported loc "exceptions"
      | Pexp_tuple l ->
         let l',bi = List.split (List.map (aux ~as_value:true) l) in
         let b = List.flatten (reverse_if_right_to_left_order bi) in
         return (Pexp_tuple l'), b
      | Pexp_construct (li, None, b) ->
         return (Pexp_construct (li, None, b)), []
      | Pexp_construct (li, Some e, bh) ->
         let e',b = aux ~as_value:true e in
         return (Pexp_construct (li, Some e', bh)), b
      | Pexp_variant (l,eo) -> unsupported loc "variants"
      | Pexp_record (l,eo) ->
         let l',bi = List.split (List.map (fun (i,(e,b)) -> ((i,e),b)) (assoc_list_map (aux ~as_value:true) l)) in
         let b = List.flatten (reverse_if_right_to_left_order bi) in
         let eo',b'=
           match eo with
           | None -> None, []
           | Some ebase ->
                match ebase.pexp_desc with
                | Pexp_ident li -> (Some ebase, [])
                (* TODO: in practice it seems that the parser only accepts variables? *)
                | _ -> (* to avoid duplication during record-with elimination,
                          we name any base that is not already an identifier *)
                    let (ebase',b') = wrap_if_needed loc true next_var ebase [] in
                    (Some ebase',b')
           in
         wrap_as_value (return (Pexp_record (l', eo'))) (b' @ b)
      | Pexp_field (e,i) ->
          let e',b = aux ~as_value:true e in
          wrap_as_value (return (Pexp_field (e', i))) b
      | Pexp_setfield (e,i,e2) ->
          let e',b = aux ~as_value:true e in
          let e2',b2 = aux ~as_value:true e2 in
          wrap_as_value (return (Pexp_setfield (e', i, e2'))) (b2 @ b)
      | Pexp_array l ->
         let l',bi = List.split (List.map (aux ~as_value:true) l) in
         let b = List.flatten (reverse_if_right_to_left_order bi) in
         wrap_as_value (return (Pexp_array l')) b
      | Pexp_ifthenelse (e1, e2, None) ->
          (* old:
          let e1', b = aux true e1 in
          wrap_as_value (return (Pexp_ifthenelse (e1', protect named e2, Some (return (Pexp_construct (Lident "()", None, false)))))) b
          *)
          let e1', b = aux ~as_value:true e1 in
          wrap_as_value (return (Pexp_ifthenelse (e1', protect e2, Some (return (Pexp_construct (Lident "()", None, false)))))) b
      | Pexp_ifthenelse (e1, e2, Some e3) ->
          (* old
          let e1', b = aux true e1 in
          wrap_as_value (return (Pexp_ifthenelse (e1', protect named e2, Some (protect named e3)))) b
          *)
          let e1', b = aux ~as_value:true e1 in
          wrap_as_value (return (Pexp_ifthenelse (e1', protect e2, Some (protect e3)))) b
             (* todo:  tester: if then else fun x -> x *)
      | Pexp_sequence (e1,e2) ->
          let e1', b = aux e1 in
          (* DEPRECATED: enforcement strict-sequence here a type annotation
          let tunit = Some { ptyp_desc = Ptyp_constr (Lident "unit", []); ptyp_loc = loc } in
          let e1' = return (Pexp_constraint (e1', tunit, None)) in *)
          wrap_as_value (return (Pexp_sequence (e1', protect e2))) b
      | Pexp_while (e1,e2) ->
         wrap_as_value (return (Pexp_while (protect e1, protect e2))) []
      | Pexp_for (s,e1,e2,d,e3) ->
          let e1', b1 = aux ~as_value:true e1 in
          let e2', b2 = aux ~as_value:true e2 in
          wrap_as_value (return (Pexp_for (s, e1', e2', d, protect e3))) (b1 @ b2)
      | Pexp_constraint (e,Some t1,None) ->
         let e',b = aux e in
         return (Pexp_constraint (e',Some t1,None)), b
          (* LATER: check if it is enough constraint e', when e' is just a variable
             and everything happens inside b *)
      | Pexp_constraint (e,_,Some t2) ->
          unsupported loc "type annotation with a subtyping constraint"
      | Pexp_constraint (e,None,None) ->
          unsupported loc "type annotation without constraints"
      | Pexp_when (econd,ebody) ->
         let econd' = protect econd in
         let ebody' = protect ebody in
         return (Pexp_when (econd', ebody')), []
      | Pexp_send (_,_) -> unsupported loc "send expression"
      | Pexp_new _ -> unsupported loc "new expression"
      | Pexp_setinstvar (_,_) -> unsupported loc "set-inst-var expression"
      | Pexp_override _ -> unsupported loc "Pexp_override expression"
      | Pexp_letmodule (_,_,_) -> unsupported loc "let-module expression"
      | Pexp_assert e ->
          return (Pexp_assert (protect e)), []
      | Pexp_assertfalse ->
          wrap_as_value (return Pexp_assertfalse) []
      | Pexp_lazy e ->
          let e',b = aux ~is_named:is_named e in
          return (Pexp_lazy e'), b
      | Pexp_poly (_,_) -> unsupported loc "poly expression"
      | Pexp_object _ -> unsupported loc "objects"
      | Pexp_newtype _ -> unsupported loc "newtype"
      | Pexp_pack _ -> unsupported loc "pack"
      | Pexp_open (id,e) -> unsupported loc "open local" (* Pexp_open (id,aux e), b *)


   (* [protect is_named e] calls the translation function [aux is_named e],
       obtaining a transformed term [e'] under a list of bindings [b],
       and it returns the term [let x1 = v1 in .. let xn = vn in e']
       where the [b] gives the list of the [(xi,vi)] pairs. *)
   and protect ?is_named:(is_named=false) e =
      let (e',b) = aux ~is_named:is_named e in
      create_let e.pexp_loc b e'

   and protect_branch ?is_named:(is_named=false) (p,e) =
      (normalize_pattern p,
       protect ~is_named:is_named e)

   in
   protect ~is_named:true e


let normalize_pattern_expression (p,e) =
   (* TODO: is_named is true only if the pattern is trivial *)
   (normalize_pattern p,
    normalize_expression ~is_named:true e)


(*#########################################################################*)
(* ** Normalization of modules and top-level phrases *)

let rec normalize_module m =
   let loc = m.pmod_loc in
   { m with pmod_desc = match m.pmod_desc with
   | Pmod_ident li -> Pmod_ident li
   | Pmod_structure s -> Pmod_structure (normalize_structure s)
   | Pmod_functor (s,mt,me) -> Pmod_functor (s, mt, normalize_module me)
   | Pmod_apply (me1,me2) -> Pmod_apply (normalize_module me1, normalize_module me2)
   | Pmod_constraint (me,mt) -> Pmod_constraint (normalize_module me,mt)
   | Pmod_unpack e -> unsupported loc "module unpack"
   }

and normalize_structure s =
  List.map normalize_structure_item s

and normalize_structure_item si =
   let loc = si.pstr_loc in
   { si with pstr_desc = match si.pstr_desc with
   | Pstr_eval e -> Pstr_eval (normalize_expression ~is_named:true e)
   | Pstr_value (r,l) -> Pstr_value (r, List.map normalize_pattern_expression l)
   | Pstr_primitive (s,v) -> Pstr_primitive (s,v)
   | Pstr_type l -> Pstr_type l
   | Pstr_exception (s,e) -> Pstr_exception (s,e)
   | Pstr_exn_rebind (s,i) -> Pstr_exn_rebind (s,i)
   | Pstr_module (s,m) -> Pstr_module (s, normalize_module m)
   | Pstr_recmodule _ -> unsupported loc "recursive modules"
   | Pstr_modtype (s,mt) -> Pstr_modtype (s,mt)
   | Pstr_open li -> Pstr_open li
   | Pstr_class _ -> unsupported loc "objects"
   | Pstr_class_type _ -> unsupported loc "objects"
   | Pstr_include m -> Pstr_include (normalize_module m)
   }

(* FIXME unused
and normalize_toplevel_phrase p =
  match p with
  | Ptop_def s -> Ptop_def (normalize_structure s)
  | Ptop_dir (s,d) -> Ptop_dir (s,d)

and normalize_source s =
   List.map normalize_toplevel_phrase s
 *)

(*#########################################################################*)

(*
let make_fresh_ident is_used basename =
   let rec trysuffix i =
      if i > 1000 then failwith "but in make_fresh_ident";
      let name = basename ^ (string_of_int i) in
      if is_used name
          then trysuffix (i+1)
          else name
        in
   let name = trysuffix 0 in
   Ident.create name

let fresh_ident_pat is_used = make_fresh_ident is_used "_p"
let fresh_ident_fun is_used = make_fresh_ident is_used "_f"
let fresh_ident_loc is_used = make_fresh_ident is_used "_x"
*)
