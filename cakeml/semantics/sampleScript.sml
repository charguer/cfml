open HolKernel Parse boolLib bossLib arithmeticTheory integerTheory;

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
  (∀m:num.
    add_rel 0 m m) ∧
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
  [(“arithmetic$+”,"nat_add"),
   (“arithmetic$-”,"nat_sub"),
   (“prim_rec$<”,"nat_lt"),
   (“arithmetic$<=”,"nat_le"),
   (“num$SUC”,"nat_suc"),
   (“_m = _n:'a”,"mk_eq"),
   (“_m ⇒ _n:bool”,"mk_imp"),
   (“if _a then _b else _c”,"mk_if")];

datatype output_type = FunApp of string | Tuple | List;
datatype output = String of string
                | App of bool * output_type * output list;

fun app x y = App (false,FunApp x,y);
fun list xs = App (false,List,xs);
fun tuple xs = App (false,Tuple,xs);
fun quote s = String ("\"" ^ s ^ "\"")

fun export_ty ty =
  if ty = “:bool” then String "mk_typ_bool" else
  if ty = “:unit” then String "mk_typ_unit" else
  if ty = “:num”  then String "mk_typ_nat" else
  if ty = “:int”  then String "mk_typ_int" else
  let
    val n = dest_vartype ty
  in app "mk_var_type" [quote n] end handle HOL_ERR _ =>
  let
    val (n,tys) = dest_type ty
  in app "mk_type" (quote n :: map export_ty tys)  end

fun mk_app f x =
  case f of
    App (false,FunApp "mk_app",[g,App (false,List,xs)]) =>
      app "mk_app" [g,list (xs @ [x])]
  | _ => app "mk_app" [f,list [x]];

fun export tm =
  let
    val (v,ty) = dest_var tm
  in app "mk_var" [quote v] end handle HOL_ERR _ =>
  let
    val (v,x) = dest_abs tm
    val (s,ty) = dest_var v
  in app "mk_lam" [quote s, export x] end handle HOL_ERR _ =>
  let
    val n = numSyntax.dest_numeral tm
  in app "mk_nat" [String (Arbnum.toString n)] end handle HOL_ERR _ =>
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
  in app "mk_var" [quote n] end;

fun print_output out =
  let
    val threshold = 80
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
  val _ = print "\n\n  "
  val _ = print_o "\n  " (fst (annotate out))
  val _ = print ";;\n\n"
  in () end;

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

(*
let defs =
  mk_define(
    "fib",
    "fib_def",
    [("n", mk_typ_nat)],
    mk_typ_nat,
    mk_eq(
      mk_app(mk_var("fib"), [mk_var("n")]),
      mk_if(
        mk_lt(mk_var("n"), mk_nat(3)),
        mk_var("n"),
        mk_add(
          mk_app(mk_var("fib"), [mk_sub(mk_var("n"), mk_nat(1))]),
          mk_app(mk_var("fib"), [mk_sub(mk_var("n"), mk_nat(2))])))))
*)

val _ = export_theory();
