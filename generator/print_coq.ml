open PPrint
open Coq

(* These functions could move to [PPrint]. *)

let sprintf format =
  Printf.ksprintf arbitrary_string format

let run (print : Buffer.t -> 'a -> unit) (x : 'a) : string =
  let b = Buffer.create 1024 in
  print b x;
  Buffer.contents b

(* -------------------------------------------------------------------------- *)

(* Global parameters. *)

let indentation =
  2

let width =
  ref 80

(* -------------------------------------------------------------------------- *)

(* Various fixed elements. *)

let arrow =
  string "->"

let doublearrow =
  string "=>"

let colonequals =
  string ":="

let spacecolon =
  string " :"

(* -------------------------------------------------------------------------- *)

(* Applications. *)

let app d1 d2 =
  (* The following definition would reject a large argument on a line of
     its own, indented: *)
  (* group (d1 ^^ nest indentation (break 1 ^^ d2)) *)
  (* However, that would be redundant with the fact that large arguments
     are usually parenthesized, and we already break lines and indent
     within the parentheses. So, the following suffices: *)
  group (d1 ^^ space ^^ d2)

let apps ds =
  match ds with
  | [] ->
      assert false
  | d :: ds ->
     List.fold_left app d ds

(* -------------------------------------------------------------------------- *)

(* A block with indentation. *)

let block n opening contents closing =
  group (opening ^^ nest n (contents) ^^ closing)

let block =
  block indentation

(* -------------------------------------------------------------------------- *)

(* Parentheses with indentation. *)

(* We allow breaking a parenthesized thing into several lines by leaving the
   opening and closing parentheses alone on a line and indenting the content. *)

let parens d =
  block
    lparen
    (break 0 ^^ d)
    (break 0 ^^ rparen)

(* Braces with spacing and indentation. *)

let braces d =
  block
    lbrace
    (break 1 ^^ d)
    (break 1 ^^ rbrace)

(* Brackets with spacing and indentation. *)

let brackets d =
  block
    lbracket
    (break 1 ^^ d)
    (break 1 ^^ rbracket)

(* -------------------------------------------------------------------------- *)

(* Tuples. *)

let tuple expr es =
  parens (separate_map (comma ^^ break 1) expr es)

(* -------------------------------------------------------------------------- *)

(* FOR FUTURE USE 
   Labels (part of [Coq_tag]). *)

let label = function
  | None ->
      string "_"
  | Some l ->
      parens (
        string "Label_create" ^/^ squote ^^ string l
      )

(* -------------------------------------------------------------------------- *)

(* Bindings, or annotations: [x : t]. *)

let binding x t =
  block (x ^^ spacecolon) (space ^^ t) empty

(* -------------------------------------------------------------------------- *)

(* Expressions. *)

let rec expr0 = function
  | Coq_var s ->
      string s
  | Coq_nat n ->
      parens (string (string_of_int n)) ^^ string "%nat"
  | Coq_int n ->
      parens (string (string_of_int n)) ^^ string "%Z"
   (* DEPRECATED ; maybe future ?
  | Coq_list cs ->
      if (cs = []) then string cnil else 
        parens ((separate_map (string "::" ^^ break 1) expr0 cs) ^^ string "::nil")
     *)
  | Coq_wild ->
      string "_"
  | Coq_prop ->
      string "Prop"
  | Coq_type ->
      string "Type"
  | Coq_tuple [] ->
      expr0 coq_tt
  | Coq_tuple es ->
      tuple expr es
  | Coq_record _les ->
      assert false (* TODO *)
  | Coq_annot (e1, e2) ->
      parens (binding (expr e1) (expr e2))
  | Coq_app _
  | Coq_tag _
  | Coq_impl _
  | Coq_lettuple _
  | Coq_forall _
  | Coq_fun _
    as e ->
      parens (expr e)

and expr1 = function
  | Coq_app (e1, e2) ->
      app (expr1 e1) (expr0 e2)
  | Coq_tag (tag, args, l, e) ->
      let stag =
        if args = [] 
           then string tag 
           else parens (apps ((string tag)::(List.map expr0 args)))
        in
      apps [
        string "CFML.CFPrint.tag"; (* @ *)
        stag;
        (* FUTURE USE: label l;*)
        (* string "_"; *)
        expr0 e
      ]
  | e ->
     expr0 e

and expr2 = function
  | Coq_impl (e1, e2) ->
      group (expr1 e1 ^^ space ^^ arrow ^/^ expr2 e2)
  | e ->
      expr1 e

and expr3 = function
  | Coq_lettuple (es, e1, e2) ->
      block
        (string "let '" ^^ tuple expr es ^^ space ^^ colonequals)
        (break 1 ^^ expr e1)
        (break 1 ^^ string "in")
      ^/^
      expr3 e2
  | Coq_forall ((x, e1), e2) ->
      block
        (string "forall " ^^ string x ^^ spacecolon)
        (break 1 ^^ expr e1 ^^ comma)
        empty
      ^/^
      expr3 e2
  | Coq_fun ((x, e1), e2) ->
      block
        (string "fun " ^^ string x ^^ spacecolon)
        (break 1 ^^ expr e1)
        (break 1 ^^ doublearrow)
      ^/^
      expr3 e2
  | e ->
      expr2 e

and expr e =
  expr3 e

(* -------------------------------------------------------------------------- *)

(* Module types. *)

let rec mod_typ0 = function
  | Mod_typ_var x ->
      string x
  | Mod_typ_app _
  | Mod_typ_with_def _
  | Mod_typ_with_mod _
    as mt ->
      parens (mod_typ mt)

and mod_typ1 = function
  | Mod_typ_app xs -> 
      separate_map space string xs
  | mt ->
      mod_typ0 mt

and mod_typ2 = function
  | Mod_typ_with_def (mt, x, e) ->
      mod_typ2 mt ^/^
      block
        (string "with Definition " ^^ string x ^^ space ^^ colonequals)
        (break 1 ^^ expr e)
        empty
  | Mod_typ_with_mod (mt, x, y) ->
      mod_typ2 mt ^/^
      sprintf "with Module %s := %s " x y
  | mt ->
      mod_typ1 mt

and mod_typ mt =
  mod_typ1 mt

(* Module bindings. *)

let mod_binding (xs, mt) = 
  binding (separate_map space string xs) (mod_typ mt)

let pmod_binding mb =
  space ^^ parens (mod_binding mb)

let pmod_bindings mbs = 
  group (concat_map pmod_binding mbs)

(* Module expressions. *)

let mod_expr xs =
  separate_map space string xs

(* Module definitions. *)

let mod_def = function
  | Mod_def_inline me ->
      block (space ^^ colonequals) (break 1 ^^ mod_expr me) dot
  | Mod_def_declare ->
      dot

(* Module casts. *)

let mod_cast = function
  | Mod_cast_exact mt ->
      spacecolon ^^ space ^^ mod_typ mt
  | Mod_cast_super mt ->
      space ^^ string "<:" ^^ space ^^ mod_typ mt
  | Mod_cast_free ->
      empty

(* -------------------------------------------------------------------------- *)

(* Typed variables: [x : t]. *)

(* Raw. *)

let var (x, t) =
  binding (string x) (expr t)

(* With parentheses and with a leading space. *)

let pvar xt =
  space ^^ parens (var xt)

let pvars xts =
  group (concat_map pvar xts)

(* A list of field declarations, separated with semicolons. *)

let fields xts =
  separate_map (semi ^^ break 1) var xts

(* -------------------------------------------------------------------------- *)

(* Tools for toplevel elements. *)

(* A definition, without a leading keyword, but with a leading space.
   [ x : d1 :=]. *)

let definition x d1 =
  block
    (space ^^ x ^^ spacecolon)
    (break 1 ^^ d1)
    (break 1 ^^ colonequals)

(* A parameter, without a leading keyword, but with a leading space.
   [ x : d1.]. *)

let parameter x d1 =
  block
    (space ^^ x ^^ spacecolon)
    (break 1 ^^ d1)
    dot

(* The right-hand side of a record declaration. [ Foo { ... }]. *)

let record_rhs r =
  space ^^
  string (r.coqind_constructor_name) ^^ space ^^
  braces (fields r.coqind_branches)

(* The right-hand side of a sum declaration. [| x1 : T1 | x2 : T2 ...]. *)

let sum_rhs r =
  concat_map (fun xt ->
    hardline ^^ block (string "| ") (var xt) empty
  ) r.coqind_branches

(* The left-hand side of a record or sum declaration. [ foo params : T := rhs]. *)

let inductive_lhs rhs r =
  definition
    (string r.coqind_name ^^ pvars r.coqind_targs)
    (expr r.coqind_ret)
  ^^
  rhs r

(* An implicit argument specification. *)

(* DEPRECATED
let deprecated_implicit (x, i) = 
  match i with
  | Coqi_maximal ->
      brackets (string x)
  | Coqi_implicit ->
      string x
  | Coqi_explicit ->
      sprintf "(* %s *)" x
*)

let implicit (x, i) = 
  match i with
  | Coqi_maximal ->
      braces (string x)
  | Coqi_implicit ->
      brackets (string x)
  | Coqi_explicit ->
      string x

(* -------------------------------------------------------------------------- *)

(* Toplevel elements. *)

let top = function
  | Coqtop_def ((x, e1), e2) ->
      string "Definition" ^^
      definition (string x) (expr e1) ^/^
      expr e2 ^^ dot
  | Coqtop_param (x, e1) ->
      string "Parameter" ^^
      parameter (string x) (expr e1)
  | Coqtop_instance ((x, e1), global) ->
      string ((if global then "Global " else "") ^ "Instance") ^^
      parameter (string x) (expr e1)
  | Coqtop_lemma (x, e1) ->
      string "Lemma" ^^
      parameter (string x) (expr e1)
  | Coqtop_proof s ->
      sprintf "Proof. %s Qed." s
  | Coqtop_record r ->
      string "Record" ^^
      inductive_lhs record_rhs r
      ^^ dot
  | Coqtop_ind rs ->
      string "Inductive" ^^
      separate_map
        (hardline ^^ hardline ^^ string "with")
        (inductive_lhs sum_rhs)
        rs
      ^^ dot
  | Coqtop_label (x, n) ->
      sprintf "Notation \"''%s'\" := (%s) (at level 0) : atom_scope."
        x (value_variable n)
  (* DEPRECATED
  | Coqtop_implicit (x, xs) -> 
      string "Implicit Arguments " ^^
      string x ^/^
      brackets (flow_map space deprecated_implicit xs)
      ^^ dot
  *)
  | Coqtop_implicit (x, xs) -> 
      string "Arguments " ^^
      string x ^/^
      (if xs = [] 
        then string ": clear implicits" 
        else (flow_map space implicit xs))
      ^^ dot
  | Coqtop_register (db, x, v) ->
      sprintf "Hint Extern 1 (Register %s %s) => CFHeader_Provide %s." db x v
  | Coqtop_hint_constructors (xs, base) ->
      string "Hint Constructors " ^^
      flow_map space string xs ^^
      spacecolon ^/^
      string base
      ^^ dot
  | Coqtop_hint_resolve (xs, base) ->
      string "Hint Resolve " ^^
      flow_map space string xs ^^
      spacecolon ^/^
      string base
      ^^ dot
  | Coqtop_hint_unfold (xs, base) ->
      string "Hint Unfold " ^^
      flow_map space string xs ^^
      spacecolon ^/^
      string base
      ^^ dot
  | Coqtop_require xs ->
      string "Require " ^^
      flow_map space string xs
      ^^ dot
  | Coqtop_import xs ->
      string "Import " ^^
      flow_map space string xs 
      ^^ dot
  | Coqtop_require_import xs ->
      string "Require Import " ^^
      flow_map space string xs 
      ^^ dot
  | Coqtop_set_implicit_args -> 
      sprintf "Set Implicit Arguments."
  | Coqtop_text s -> 
      sprintf "%s" s
  | Coqtop_declare_module (x, mt) ->
      string "Declare Module" ^^
      parameter (string x) (mod_typ mt)
  | Coqtop_module (x, bs, c, d) ->
      string "Module" ^^ space ^^
      string x ^^
      pmod_bindings bs ^^
      mod_cast c ^^
      mod_def d
  | Coqtop_module_type (x, bs, d) ->
      string "Module Type" ^^ space ^^
      string x ^^
      pmod_bindings bs ^^
      mod_def d
  | Coqtop_module_type_include x ->
      sprintf "Include Type %s." x
  | Coqtop_end x ->
      sprintf "End %s." x
  | Coqtop_custom x ->
      sprintf "%s" x


let top t =
  group (top t)

let tops ts =
  concat_map (fun t -> top t ^^ hardline ^^ hardline) ts

(* -------------------------------------------------------------------------- *)

(* The main entry point translates a list of toplevel elements to a string. *)

let tops ts : string =
  run (PPrintEngine.ToBuffer.pretty 0.9 !width) (tops ts)

