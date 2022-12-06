open HolKernel Parse boolLib bossLib arithmeticTheory integerTheory;
open astTheory namespaceTheory (* fromSexpTheory *);

val _ = new_theory "sample";

(* a few sample definitions *)

Definition fib_def:
  fib (n:num) = if n < 2 then n else fib (n-1) + fib (n-2)
End

Datatype:
  rose = Tree α (rose list)
End

Definition flatten_def:
  flatten (Tree x ts) = [x] ++ FLAT (MAP flatten ts)
Termination
  WF_REL_TAC ‘measure $ rose_size $ K 0’
End

Inductive add_rel:
[~zero:]
  (∀m:num.
    add_rel 0 m m) ∧
[~suc:]
  (∀m n k.
    add_rel n (SUC m) k ⇒
    add_rel (SUC n) m k)
End

(* a sanity lemma *)

Theorem add_rel_thm:
  ∀m n k. add_rel m n k ⇒ k = m + n
Proof
  Induct_on ‘add_rel’ \\ rw []
QED

(* sketch of some automation *)

val term_patterns =
  [(“arithmetic$+”,"coq_nat_add"),
   (“arithmetic$-”,"coq_nat_sub"),
   (“prim_rec$<”,"coq_nat_lt"),
   (“arithmetic$<=”,"coq_nat_le"),
   (“num$SUC”,"coq_nat_succ"),
   (“_m = _n:'a”,"coq_app_eq"),
   (“_m ⇒ _n:bool”,"coq_impl"),
   (“if _a then _b else _c”,"coq_if_prop")];

datatype output_type = FunApp of string | Tuple | List;
datatype output = String of string
                | App of bool * output_type * output list;

fun app x y = App (false,FunApp x,y);
fun list xs = App (false,List,xs);
fun tuple xs = App (false,Tuple,xs);
fun quote s =
  (* if s = "If" then quote "If_" else *)
    String ("\"" ^ s ^ "\"")

fun adjust_tyvar_name s =
  if String.isPrefix "'" s then
    (explode s |> tl (* |> map Char.toUpper *) |> implode)
  else s;

fun export_ty ty =
  if ty = “:bool” then String "coq_typ_bool" else
  if ty = “:unit” then String "coq_typ_unit" else
  if ty = “:num”  then String "coq_typ_nat" else
  if ty = “:int”  then String "coq_typ_int" else
  if ty = “:char” then app "coq_var" [quote "Prelude.char"] else
  if ty = “:word8”  then app "coq_var" [quote "Prelude.word8"] else
  if ty = “:word64” then app "coq_var" [quote "Prelude.word64"] else
  let val (t1,t2) = pairSyntax.dest_prod ty
  in app "coq_prod" [export_ty t1, export_ty t2] end handle HOL_ERR _ =>
  let val t = listSyntax.dest_list_type ty
  in app "coq_typ_list" [export_ty t] end handle HOL_ERR _ =>
  let val t = optionSyntax.dest_option ty
  in app "coq_typ_option" [export_ty t] end handle HOL_ERR _ =>
  let
    val n = dest_vartype ty
    val n = adjust_tyvar_name n
  in app "coq_tvar" [quote n] end handle HOL_ERR _ =>
  let
    val (n,tys) = dest_type ty
  in app "coq_apps_var" [quote n, list (map export_ty tys)] end

fun mk_app f x =
  case f of
    App (false,FunApp "coq_app",[g,App (false,List,xs)]) =>
      app "coq_app" [g,list (xs @ [x])]
  | _ => app "coq_app" [f,list [x]];

fun export tm =
  let
    val (v,ty) = dest_var tm
  in app "coq_var" [quote v] end handle HOL_ERR _ =>
  let
    val (v,x) = dest_abs tm
    val (s,ty) = dest_var v
  in app "coq_lam" [tuple [quote s, export_ty ty], export x] end handle HOL_ERR _ =>
  let
    val n = numSyntax.dest_numeral tm
  in app "coq_nat" [String (Arbnum.toString n)] end handle HOL_ERR _ =>
  let
    fun match_pat (pat,s) = let
      val (i,j) = match_term pat tm
      val xs = map (fn {redex = x, residue = y} => (fst (dest_var x),y)) i
      val ys = sort (fn (x,_) => fn (y,_) => String.compare(x,y) = LESS) xs
      in (s,map snd ys) end
    fun map_fst f [] = fail()
      | map_fst f (x::xs) = f x handle HOL_ERR _ => map_fst f xs
    val (s,args) = map_fst match_pat term_patterns
  in app s (map export args) end handle HOL_ERR _ =>
  let
    val (f,x) = dest_comb tm
  in mk_app (export f) (export x) end handle HOL_ERR _ =>
  let
    val (n,ty) = dest_const tm
  in app "coq_var" [quote n] end;

fun write_output print out =
  let
    val threshold = 60
    fun size_aux (FunApp s) = size s + 3 | size_aux _ = 2;
    fun annotate (String s) = (String s, size s)
      | annotate (App (_,s,xs)) =
          let val ys = map annotate xs
              val n = foldr (fn ((_,m),n) => n+m) 0 ys + size_aux s
              val zs = map fst ys
          in (App (n < threshold, s, zs), n) end
    fun needs_parens (App (b,FunApp s,xs)) = not (null xs)
      | needs_parens _ = false
    fun print_nil (FunApp s) = print s
      | print_nil Tuple = print "()"
      | print_nil List = print "[]"
    fun print_open (FunApp s) = print (s ^ " ")
      | print_open Tuple = print "("
      | print_open List = print "["
    fun print_close (FunApp s) = ()
      | print_close Tuple = print ")"
      | print_close List = print "]"
    fun get_sep (FunApp s) = " "
      | get_sep List = "; "
      | get_sep _ = ", "
    fun print_o indent (String s) = print s
      | print_o indent (App (b,s,xs)) =
          if null xs then print_nil s else
          if b then
            (print_open s; print_o_list (get_sep s) "" xs; print_close s)
          else
            let val new_indent = indent ^ (if needs_parens (App (b,s,xs))
                                           then "  " else " ")
            in print_open s;
               (if needs_parens (App (b,s,xs)) then print new_indent else print "");
               print_o_list (get_sep s) new_indent xs;
               print_close s
            end
    and print_o_list sep indent [] = ()
      | print_o_list sep indent [x] =
          if needs_parens x andalso sep = " " then
            (print "("; print_o indent x; print ")")
          else print_o indent x
      | print_o_list sep indent (x::y::xs) =
          (print_o_list sep indent [x];
           print (sep ^ indent);
           print_o_list sep indent (y::xs))
  val _ = print_o "\n  " (fst (annotate out))
  val _ = print "\n"
  in () end;

val print_output = write_output print;

fun export_def def =
  let
    val tm = def |> SPEC_ALL |> concl
    val (l,r) = tm |> dest_eq
    val c = l |> repeat rator
    fun dest_args tm =
      let val (f,x) = dest_comb tm in dest_args f @ [x] end handle HOL_ERR _ => [];
    val vs = l |> dest_args
    val (cname,cty) = dest_const c
    fun dest_arg v = let
      val (n,ty) = dest_var v
      in tuple [quote n, export_ty ty] end
    val args = list (map dest_arg vs)
    val ret_ty = export_ty (type_of l)
    val rhs_e = export tm
  in
    app "mk_define"
      [quote cname,
       quote (cname ^ "_def"),
       args,
       export_ty (type_of (tm |> dest_eq |> fst)),
       rhs_e]
  end;

val _ = print_output $ export_def fib_def;

Datatype:
  ind1 = D1 num ind2 | D2 ;
  ind2 = E1 num 'a | E2 ind1
End

Datatype:
  state = <| red : num; blue : 'a list |>
End

fun dest_fun_type ty = let
  val (name,args) = dest_type ty
  in if name = "fun" then (el 1 args, el 2 args) else failwith("not fun type") end

fun dest_curried_fun_type ty = let
  val (t1,t2) = dest_fun_type ty
  in t1 :: dest_curried_fun_type t2 end handle HOL_ERR _ => [ty]

fun find_mutrec_types ty = let (* e.g. input ``:v`` gives [``:exp``,``:v``]  *)
  fun is_pair_ty ty = fst (dest_type ty) = "prod"
  val xs = TypeBase.axiom_of ty |> SPEC_ALL  |> concl |> strip_exists |> #1 |> map (#1 o dest_fun_type o type_of) |> (fn ls => filter (fn ty => intersect ((#2 o dest_type) ty) ls = []) ls)
  in if is_pair_ty ty then [ty] else if length xs = 0 then [ty] else xs end

fun export_ty_def ty =
  if TypeBase.is_record_type ty then let
    val ty = TypeBase.case_const_of ty |> type_of |> dest_fun_type |> fst
    val ts = TypeBase.fields_of ty |> map (fn (b,{ty = ty, ...}) => (b,ty))
    val (ty_n,ts1) = dest_type ty
    val vs = ts1 |> map dest_vartype |> map adjust_tyvar_name
    in app "mk_typedef_record"
         [quote ty_n,
          list (map quote vs),
          list (map (fn (n,t) => tuple [quote n, export_ty t]) ts)] end
  else let
    val ty = TypeBase.case_const_of ty |> type_of |> dest_fun_type |> fst
    val tys = find_mutrec_types ty
    val css = map (fn ty => (ty,TypeBase.constructors_of ty)) tys
    fun process (ty,cs) = let
      val (ty_n,ts) = dest_type ty
      val vs = ts |> map dest_vartype |> map adjust_tyvar_name
      fun f c = let
        val (n,ct) = dest_const c
        val ctys = dest_curried_fun_type ct
        val xs = butlast ctys
        val x = last ctys
        val _ = (x = ty) orelse failwith "info from TypeBase is malformed"
        in (n,xs) end
      in (ty_n,vs,map f cs) end
    val xs = map process css
    fun export_case (n,vs,cs) =
      app "mk_coqind_type"
        [quote n,
         list (map quote vs),
         list (map (fn (n,tys) => tuple [quote n, list (map export_ty tys)]) cs)]
    in app "mk_mutual_inductive_type" [list (map export_case xs)] end

val _ = print_output $ export_ty_def “:'a ind2”;
val _ = print_output $ export_ty_def “:num state”;

fun append_print out = (print "  @ "; print_output out);

val _ = print "\n  []\n"
val _ = List.app (append_print o export_ty_def)

val es =
  map export_ty_def
  [“:('a,'b) id”,
   “:lit”, “:opn”, “:opb”, “:opw”, “:shift”, “:word_size”,
   “:fp_cmp”, “:fp_uop”, “:fp_bop”, “:fp_top”, “:fp_opt”,
   “:real_cmp”, “:real_uop”, “:real_bop”,
   “:op”,
   “:op_class”,
   “:lop”,
   “:ast_t”,
   “:pat”,
   “:locn”, “:locs”,
   “:exp”,
   “:dec”];

val ast_defs = list es;

(* write to file *)

val f = TextIO.openOut("demo.ml");
fun write s = (print s; TextIO.output(f,s));
fun writeln s = (write s; write "\n");
val _ = writeln "open Coq_from_hol";
val _ = writeln "";
val _ = writeln "let ast_defs =";
val _ = write "  ";
val _ = write_output write ast_defs;
val _ = writeln "";
val _ = writeln "let _ = out_prog \"Demo\" [] ast_defs";
val _ = TextIO.closeOut f;

(*

val tm =
  listsexp_thm
  |> DefnBase.one_line_ify NONE
  |> concl
  |> dest_eq |> snd

val tm = “case x of Var n => 3 | _ => 2”

  val (_,x,rows) = TypeBase.dest_case tm
  fun term_mem x [] = false
    | term_mem x (y::ys) = aconv x y orelse term_mem x ys
  fun subset [] ys = true
    | subset (x::xs) ys = term_mem x ys andalso subset xs ys
  fun disjoint [] ys = true
    | disjoint (x::xs) ys = not (term_mem x ys) andalso disjoint xs ys
  fun freevars_check pat tm = disjoint (free_vars pat) (free_vars tm)

  val rows1 = map (fn (pat,tm) => (pat,tm,term_size tm,freevars_check pat tm)) rows

Definition foo_def:
  foo x =
    case x of
    | SOME (INL (4:num) => SOME 1
    | SOME (INR (x,5:num)) => SOME (x:num)
    | _ => NONE
End




  “foo x = SOME y”
  |> SIMP_CONV (srw_ss()) [foo_def,CaseEq"option",CaseEq"sum",CaseEq"prod"]
  |> MATCH_MP (METIS_PROVE [] “x = y ⇒ (y ⇒ x)”)
  |> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV (srw_ss()) [PULL_EXISTS]))
  |> SIMP_RULE (srw_ss()) [PULL_EXISTS, SF DNF_ss]
  |> CONJUNCTS |> map GEN_ALL |> map (SIMP_RULE std_ss [])

  “foo x = NONE”
  |> SIMP_CONV (srw_ss()) [foo_def,AllCaseEqs()]
  |> MATCH_MP (METIS_PROVE [] “x = y ⇒ (y ⇒ x)”)
  |> CONV_RULE ((RATOR_CONV o RAND_CONV) (SIMP_CONV (srw_ss()) [PULL_EXISTS]))
  |> SIMP_RULE (srw_ss()) [PULL_EXISTS, SF DNF_ss]
  |> CONJUNCTS |> map GEN_ALL |> map (SIMP_RULE std_ss [])

  foo_def |>


*)

val _ = export_theory();
