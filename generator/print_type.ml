open Misc
open Types
open Mytools
open Format
open Btype
open Printtyp

(** This file contains a data structure for representing types in an
    explicit form, as well as an algorithm for extracting such types
    from the representation used by OCaml's compiler. *)


let type_rename = ref (fun s -> s)


(*#########################################################################*)
(* ** Simple representation of types, called [btyp] *)

type btyp =
   | Btyp_alias of btyp * string
   | Btyp_arrow of btyp * btyp
   | Btyp_constr of Path.t * btyp list
   | Btyp_tuple of btyp list
   | Btyp_var of string * type_expr
   | Btyp_poly of string list * btyp
   | Btyp_val

   (*--later:
   | Btyp_abstract
   | Btyp_stuff of string
   | Btyp_manifest of out_type * out_type
   | Btyp_record of (string * bool * out_type) list
   | Btyp_object of (string * out_type) list * bool option
   | Btyp_class of bool * out_ident * out_type list
   | Btyp_sum of (string * out_type list) list
   *)


(*#########################################################################*)
(* ** Used variables *)

let eliminate_unused_variables = true

(** Special level used to mark used variables *)

let used_level = 1_000_000_000 (* this constant fits in 31 bits *)

(** Mark a variable as used at least once. *)

let typvar_mark_used ty =
   let ty = repr ty in
   if eliminate_unused_variables then ty.level <- used_level

(** Test if a variable has been used at least once. *)

let typvar_is_used ty =
   if not eliminate_unused_variables then true else begin
      let ty = repr ty in
      ty.level = used_level
   end


(*#########################################################################*)
(* ** Helper functions *)

(** Gathering of free type variables of a btyp
DEPRECATED
*)

(* FIXME unused
type occ = Occ_gen of type_expr | Occ_alias of type_expr
let occured : (occ list) ref = ref []
let add_occured t =
  if not (List.memq t !occured)
     then occured := t :: !occured
let extract_occured () =
   let r = List.rev !occured in
   occured := [];
   r
 *)

(** Wrapper for functions from [Printtyp.ml] *)

let mark_loops = mark_loops

let name_of_type_var ty =
   let ty = proxy ty in
   let x = Printtyp.name_of_type ty in
   !type_rename x

let reset_names = reset_names


(*#########################################################################*)
(* ** Generation of simple type representations *)

(** Algorithm translating an OCaml's typechecker type into a btyp *)

(* ty.level <> used_level  *)


let rec btree_of_typexp ty =
  let ty = repr ty in
  let px = proxy ty in
  if List.mem_assq px !names (* && not (List.memq px !delayed) *) then
   (* let mark = is_non_gen ty in *)
   if is_aliased px && aliasable ty
      then Btyp_val (* todo: hack ok ? *)
      else Btyp_var (name_of_type_var px, ty) else
  let pr_typ () =
    match ty.desc with
    | Tvar | Tunivar ->
        Btyp_var (name_of_type_var ty, ty)
        (* add_occured (Occ_gen ty); *)
        (* is_non_gen ty,  *)
    | Tarrow(l, ty1, ty2, _) ->
        (* with labels
        let pr_arrow l ty1 ty2 =
          let lab =
            if !print_labels &&  l <> "" || is_optional l then l else ""
          in
          let t1 =
            if is_optional l then
              match (repr ty1).desc with
              | Tconstr(path, [ty], _)
                when Path.same path Predef.path_option ->
                  btree_of_typexp ty
              | _ -> Btyp_stuff "<hidden>"
            else btree_of_typexp ty1 in
          Btyp_arrow (lab, t1, btree_of_typexp ty2) in
        pr_arrow l ty1 ty2
        *)
        let b1 = btree_of_typexp ty1 in
        let b2 = btree_of_typexp ty2 in
        ignore (b1,b2);
         Btyp_arrow (b1, b2)
    | Ttuple tyl ->
        Btyp_tuple (btree_of_typlist tyl)
    | Tconstr(p, tyl, abbrev) ->
        Btyp_constr (p, btree_of_typlist tyl)
    | Tvariant row -> unsupported_noloc "variant"
    | Tobject (fi, nm) -> unsupported_noloc "object"
    | Tsubst ty ->
        btree_of_typexp ty
    | Tlink _ | Tnil | Tfield _ ->
        fatal_error "Printtyp.btree_of_typexp link/nil/field unsupported"
    | Tpoly (ty, []) ->
        btree_of_typexp ty
    | Tpoly (ty, tyl) ->
        (* TODO: use tyl? *)
        btree_of_typexp ty
    | Tpackage _ ->
        fatal_error "Printtyp.btree_of_typexp Tpackage unsupported"
  in
  (* if List.memq px !delayed then delayed := List.filter ((!=) px) !delayed; *)
  if is_aliased px && aliasable ty then begin
    check_name_of_type px;
    (* add_occured (Occ_alias ty); *)
    Btyp_alias (pr_typ (), name_of_type_var px) end
  else pr_typ ()

and btree_of_typlist tyl =
   List.map btree_of_typexp tyl


(*#########################################################################*)
(* ** Main functions *)

(** --todo: there is some redundancy with, e.g., [string_of_type_exp] *)

(** Translates a type expression [t] into a [btyp], including the call
    to [mark_loops]. *)

let btyp_of_typ_exp t =
   mark_loops t;
   btree_of_typexp t

(** Translates of a type scheme [t] into a [btyp], including the call
    to [mark_loops].
DEPRECATED *)

(* FIXME unused
let btyp_of_typ_sch t =
   mark_loops t;
   let typ = btree_of_typexp t in
   let fvt = extract_occured () in
   let fvtg = list_concat_map (function Occ_gen x -> [x] | _ -> []) fvt in
   let fvta = list_concat_map (function Occ_alias x -> [x] | _ -> []) fvt in
   (fvtg, fvta, typ)
 *)

(** Translates of a type scheme [t] into a [btyp], including the call
    to [mark_loops]. Returns the tree with head quantification of
    free type variables.

TO DEPRECATE: should use btyp_of_typ_exp instead *)

let btyp_of_typ_sch_simple ty =
   mark_loops ty;
   btree_of_typexp ty



(*#########################################################################*)
(* ** Printing of simple type representations *)

(** Helper functions *)

let ign f () = f

let print_list pr sep =
   show_list pr sep

let pr_vars s =
  print_list (fun s -> sprintf "'%s" s) " " s

(** Printing of paths and identifiers *)

let print_path s =
   Path.name s

(* FIXME unused
let rec print_ident =
  function
  | Oide_ident s -> sprintf "%s" s
  | Oide_dot (id, s) -> sprintf "%a.%s" (ign print_ident) id s
  | Oide_apply (id1, id2) ->
      sprintf "%a(%a)" (ign print_ident) id1 (ign print_ident) id2
 *)

(** Printing of types *)

let rec print_out_type =
  function
  | Btyp_val -> "Val"
  | Btyp_alias (ty, s) ->
      sprintf "@[%a as '%s]" (ign print_out_type) ty s
  | Btyp_poly (sl, ty) ->
      sprintf "@[<hov 2>%a.@ %a@]"
        (ign pr_vars) sl
        (ign print_out_type) ty
  | ty ->
      print_out_type_1 ty
and print_out_type_1 =
  function
    Btyp_arrow (ty1, ty2) ->
      sprintf "@[%a -> %a@]"
        (ign print_out_type_2) ty1 (ign print_out_type_1) ty2
  | ty -> print_out_type_2 ty
and print_out_type_2 =
  function
    Btyp_tuple tyl ->
      sprintf "@[<0>%a@]" (ign (print_typlist print_simple_out_type " *")) tyl
  | ty -> print_simple_out_type ty
and print_simple_out_type =
  function
  | Btyp_constr (id, tyl) ->
      sprintf "@[%a%a@]" (ign print_typargs) tyl (ign print_path) id
  | Btyp_var (s, ty) -> sprintf "'%s" s  (* %s (if ng then "_" else "")  *)
  | Btyp_val | Btyp_alias _ | Btyp_poly _ | Btyp_arrow _ | Btyp_tuple _ as ty ->
      sprintf "@[<1>(%a)@]" (ign print_out_type) ty
  (*| Btyp_abstract -> ""
    | Btyp_sum _ | Btyp_record _ | Btyp_manifest (_, _)*)
and print_typlist (print_elem : 'a -> string) (sep : string) (t:btyp list) : string =
  match t with
  | [] -> ""
  | [ty] -> print_elem ty
  | ty :: tyl ->
      sprintf "%a%s %a" (ign print_elem) ty sep (ign (print_typlist print_elem sep))
        tyl
and print_typargs =
  function
    [] -> ""
  | [ty1] -> sprintf "%a " (ign print_simple_out_type) ty1
  | tyl -> sprintf "@[<1>(%a)@]@ " (ign (print_typlist print_out_type ",")) tyl


(*#########################################################################*)
(* ** Main functions *)

(** Translates an OCaml's compiler type [t] into a string.
    Boolean parameter [sch] indicates whether free type variables
    should be quantified at head. The function [mark_loops] should
    be called on [t] first for recursive types to be handled correctly. *)

let show_typ t =
   print_out_type (btree_of_typexp t)

(** Translates a type expression [t] into a string, including the call
    to [mark_loops]. *)

let string_of_type_exp t =
   mark_loops t;
   show_typ t

(** Translates of a type scheme [t] into a string, including the call
    to [mark_loops]. *)

let string_of_type_sch fvs t =
   mark_loops t;
   let s = show_typ t in
   let gs = List.map (fun x -> "'" ^ name_of_type_var x) (List.rev fvs) in
   if gs <> []
      then sprintf "forall %s. %s" (show_list (fun x->x) " " gs) s
      else s
