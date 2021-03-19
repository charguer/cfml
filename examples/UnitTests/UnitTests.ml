
(**
 *
 * This file contains unit tests for testing the generation of
 * characteristic formulae, their display, and their associated
 * tactics.
 *)


(********************************************************************)
(* ** Function call *)

let myincr n =
  n + 1

let app_myincr x =
  myincr x

let app_let_myincr x =
  let y = myincr x in
  y

let app_let_local_myincr x =
  let local_myincr n =
     n + 1 in
  local_myincr x

let app_let_local_myincr2 x =
  let local_myincr1 n =
     0  in
  let local_myincr n =
     n  in
  let local_myincr2 n =
     0  in
  local_myincr x



(********************************************************************)
(* ** Values *)

let val_unit x =
  ()

let val_int () =
  3

let val_int_pair () =
  (3,4)

let val_poly () =
  []

(* --Not yet supported:
   Error is: Cannot infer this placeholder of type Type
let val_poly_internal () =
  let x = ignore None in
  ()
 *)

(* --TODO:  BUG
   The reference A_ was not found in the current environment.*)

(*
let val_poly_internal () =
  let x = ignore (None : 'a option) in
  ()
*)

(********************************************************************)
(* ** Sequence *)

let seq_val_unit () =
   val_unit 1;
   val_unit 2;
   val_unit 3


(********************************************************************)
(* ** Let-value *)

let let_val_int () =
   let x = 3 in
   x

let let_val_pair_int () =
   let x = (3,4) in
   x

(* TODO LATER
let let_val_poly () =
   let _x = [] in
   3
   *)


(********************************************************************)
(* ** Let-pattern *)

let let_pattern_pair_int () =
   let (x,y) = (3,4) in
   x

let let_pattern_pair_int_wildcard () =
   let (x,_) = (3,4) in
   x


(********************************************************************)
(* ** Let-term *)

let let_term_nested_id_calls () =
   let f x = x in
   let a = f (f (f 2)) in
   a

let let_term_nested_pairs_calls () =
   let f x y = (x,y) in
   let a = f (f 1 2) (f 3 (f 4 5)) in
   a


(********************************************************************)
(* ** Let-function *)

let let_fun_const () =
  let f () = 3 in
  f()

let let_fun_poly_id () =
  let f x = x in
  f 3

let let_fun_poly_pair_homogeneous () =
  let f (x:'a) (y:'a) = (x,y) in
  f 3 3

let let_fun_on_the_fly () =
  (fun x f -> f x) 3 (fun x -> x+1)

let let_fun_in_let () =
  let f = (assert (true); fun x -> x) in
  f

let let_fun_rec m =
  let rec f n = if n <= 0 then 0 else f(n-1) in
  f m


(********************************************************************)
(* ** Polymorphic let bindings and value restriction *)

(* LATER

let let_poly_p0 () =
   let x = (None = None) in ()

let let_poly_p1 () =
   let f x = x in
   let _r = f None in
   ()

let let_poly_p2 () =
   let f x = x in
   let _r =
      let _s = f None in ()
      in
   ()

let let_poly_p3 () =
   let _r1 = (None = None) in
   let _r2 = (Some 3 = None) in
   let _r3 = ((Some 3, None) = (Some 3, None)) in
   let _r4 = (true = false) in
   ()


let let_poly_f0 () =
  let r = ref [] in
  !r

let let_poly_f1 () : 'a list =
  let r = ref ([] : 'a list) in
  !r

let let_poly_f2 () =
  let r : ('a ref) = ref [] in
  !r

let let_poly_f3 () =
  let r : (int list) ref = ref [] in
  !r

let let_poly_f4 () =
  let r = ref ([] : int list) in
  !r


let let_poly_g1 () : 'a list =
  let r = ref [] in
  r := [5];
  !r

let let_poly_g2 () =
  let r : ('a list) ref = ref [] in
  r := [4];
  !r


let let_poly_h0 () =
   let r = ref [] in
   r

let let_poly_h1 () =
  let g =
     let f () = ref [] in
     f in
  g

let let_poly_h2 () =
  let f () : 'a list ref = ref [] in
  f

let let_poly_h3 () =
  let f () = ref [] in
  f()


let let_poly_k1 () =
  []

let let_poly_k2 () =
  ref []

let let_poly_r1 () =
   let _x = ref [] in
   ()

let let_poly_r2 () =
   let _x = ref [] in
   let y = [] in
   y

let let_poly_r3 () =
   let r =
      let x = ref [] in
      [] in
   r
*)

(* ---Code not allowed because produces a ['_a list ref] at top level;
   i.e. rejected when using OCaml "-strict_value_restriction" flag
let h1 =
  let f () : 'a list ref = ref [] in
  f
*)



(********************************************************************)
(* ** Partial applications  -- TODO: later

let app_partial_2_1 () =
   let f x y = (x,y) in
   f 3

let app_partial_3_2 () =
   let f x y z = (x,z) in
   f 2 4

let app_partial_add () =
  let add x y = x + y in
  let g = add 1 in g 2

let app_partial_appto () =
  let appto x f = f x in
  let _r = appto 3 ((+) 1) in
  appto 3 (fun x -> x + 1)

let test_partial_app_arities () =
   let func4 a b c d = a + b + c + d in
   let f1 = func4 1 in
   let f2 = func4 1 2 in
   let f3 = func4 1 2 3 in
   f1 2 3 4 + f2 3 4 + f3 4

let app_partial_builtin_add () =
  let f = (+) 1 in
  f 2

let app_partial_builtin_and () =
  let f = (&&) true in
  f false
*)


(********************************************************************)
(* ** Over applications -- TODO: later

let app_over_id () =
   let f x = x in
   f f 3

*)


(********************************************************************)
(* ** Infix functions *)

let (+++) x y = x + y

let infix_aux x y = x +++ y

let (---) = infix_aux


(********************************************************************)
(* ** Lazy binary operators *)

let lazyop_val () =
  if true && (false || true) then 1 else 0

let lazyop_term () =
  let f x = (x = 0) in
  if f 1 || f 0 then 1 else 0

let lazyop_mixed () =
  let f x = (x = 0) in
  if true && (f 1 || (f 0 && true)) then 1 else 0


(********************************************************************)
(* ** Comparison operators and polymorphic equality *)

let compare_int () =
  (1 <> 0 && 1 <= 2) || (0 = 1 && 1 >= 2 && 1 < 2 && 2 > 1)

let compare_min () =
  (min 0 1)

(* TODO: not yet supported float
let compare_float () =
  (1. <> 0. && 1. <= 2.) || (0. = 1. && 1. >= 2. && 1. < 2. && 2. > 1.)
*)

let compare_poly () =
   let _r1 = (None = None) in
   let _r2 = (Some 3 = None) in
   let _r3 = ((Some 3, None) = (Some 3, None)) in
   let _r4 = (true = false) in
   ()
   (* -- not yet supported (does not seem very useful)
     let f () = 4 in
     let _r5 = ((Some f, None) = (None, Some f)) in *)

type 'a compare_poly_type =
  | CompCst
  | CompPoly of 'a
  | CompTuple of 'a * bool
  | CompFunc of ('a -> 'a)

let compare_poly_custom (x : 'a compare_poly_type) (y : int compare_poly_type) =
  let _r1 = (x = CompCst) in
  let _r2 = (y = CompPoly 3) in
  let _r3 = (y = CompPoly 3) in
  let _r4 = (y = CompTuple (3, true)) in
  ()

let compare_physical_loc_func () =
   let r1a = ref 1 in
   let r1b = ref 1 in
   let _r1 = (r1a == r1b) in
   let _r2 = (r1a != r1b) in
   let f () = 1 in
   let _r3 = if (f == f) then f() else 1 in
   ()

let compare_physical_algebraic () =
   let rec replace (k:int) (v:int) (l:(int*int) list) =
      match l with
      | [] -> l
      | (k2,v2)::t2 ->
         let t = replace k v t2 in
         if k = k2 then (k,v)::t
         else if t != t2 then (k2,v2)::t
         else l (* no change *)
      in
   replace 1 9 [(1,3); (4,2); (2,5)]


(********************************************************************)
(* ** List operators *)

let list_ops () =
  let x = [1] in
  List.length (List.rev (List.concat (List.append [x] [x; x])))


(********************************************************************)
(* ** Inlined total functions *)

let inlined_fun_arith () =
   let n = 2 in
   1 - (1 / n) + ((2 * 2) / 2) mod (- 3)

let inlined_fun_others n =
  fst (succ n, ignore (pred n))



(********************************************************************)
(* ** Polymorphic functions *)

let top_fun_poly_id x =
  x

let top_fun_poly_proj1 (x,y) =
  x

let top_fun_poly_proj2 x y =
  y

let top_fun_poly_pair_homogeneous (x:'a) (y:'a) =
  (x,y)


(********************************************************************)
(* ** Top-level values *)

let top_val_int = 5

let top_val_int_list : int list = []

let top_val_poly_list = []

let top_val_poly_list_pair = ([],[])

(* TODO: LATER top-level patterns

let (top_val_pair_int_1,top_val_pair_int_2) = (1,2)

let (top_val_pair_fun_1,top_val_pair_fun_2) =
  ((fun () -> 1), (fun () -> 1))
*)

(* problematic generalization
let (top_val_pair_fun_1,top_val_pair_fun_2) =
  ((fun x -> x), (fun x -> x))
*)


(********************************************************************)
(* ** Polymorphic let bindings *)

(*  TODO LATER

let let_poly_nil () =
  let x = [] in x

let let_poly_nil_pair () =
  let x = ([], []) in x

let let_poly_nil_pair_homogeneous () =
  let x : ('a list * 'a list) = ([], []) in x

let let_poly_nil_pair_heterogeneous () =
  let x : ('a list * int list) = ([], []) in x

*)

(* TODO: polymorphic recursion *)


(********************************************************************)
(* ** Type annotations *)

let annot_let () =
   let x : int = 3 in x

let annot_tuple_arg () =
   (3, ([] : int list))

let annot_pattern_var x =
   match (x : int list) with [] -> 1 | _ -> 0

let annot_pattern_constr () =
   match ([] : int list) with [] -> 1 | _ -> 0


(********************************************************************)
(* ** Pattern-matching *)

let match_fst (x,y) =
  x

let match_pair_as () =
   match (3,4) with (a, (b as c)) as p -> (c,p)

let match_list l =
  match l with
  | [] -> 0
  | x::l' -> 1

let match_aliases l =
  match l with
  | x1::(x2::(x3::t as t3) as t2) as t1 -> 0
  | _ -> 1

let match_complex () =
  let l = [ (1,1); (0,0); (2,2) ] in
  match l with
  | _::(0,0)::q -> q
  | _::_ -> [(2,2)]
  | _ -> assert false (* same as omiting branch *)

let match_term_when () =
   let f x = x + 1 in
   match f 3 with
   | 0 -> 1
   | n when n > 0 -> 2
   | _ -> 3

(* LATER
let match_or_clauses p =
   (* captures (Some x, _) or (_, Some x) with x > 0 *)
   match p with
   | (None, None) -> false
   | ((Some x, _) | (_, Some x)) when x > 0 -> true
   | (Some x, _) | (_, Some x) -> false
*)


(********************************************************************)
(* ** Advanced pattern matching *)

(* TODO
let match_term_when () =
   let f x = x + 1 in
   match f 3 with
   | 0 -> 1
   | n when n > 0 -> 2
   | _ -> 3

   (* captures (Some x, _) or (_, Some x) with x > 0 *)
let match_or_clauses p =
   match p with
   | (None, None) -> false
   | ((Some x, _) | (_, Some x)) when x > 0 -> true
   | (Some x, _) | (_, Some x) -> false
*)



(********************************************************************)
(* ** Fatal Exceptions *)

let exn_assert_false () =
   assert false

let exn_failwith () =
   failwith "ok"

exception My_exn

let exn_raise () =
   raise My_exn


(********************************************************************)
(* ** Assertions *)

let assert_true () =
  assert true;
  3

let assert_pos x =
  assert (x > 0);
  3

let assert_same (x:int) (y:int) =
  assert (x = y);
  3

let assert_let () =
  assert (let _x = true in true);
  3

let assert_seq () =
  let r = ref 0 in
  assert (incr r; true);
  !r

let assert_in_seq () =
  (assert (true); 3) + 1


(********************************************************************)
(* ** Conditionals *)

let if_true () =
   if true then 1 else 0

let if_term () =
   let f x = true in
   if f 0 then 1 else 0

let if_else_if () =
   let f x = false in
   if f 0 then 1
   else if f 1 then 2
   else 0

let if_then_no_else b =
  let r = ref 0 in
  if b
     then incr r;
  !r


(********************************************************************)
(* ** Records *)

type 'a sitems = {
  mutable nb : int;
  mutable items : 'a list; }

let sitems_build n =
  { nb = n; items = [] }

let sitems_get_nb r =
  r.nb

let sitems_incr_nb_let r =
  let x = r.nb in
  r.nb <- x + 1

let sitems_incr_nb r =
  r.nb <- r.nb + 1

let sitems_length_items_let r =
  let x = r.items in
  List.length x

let sitems_length_items r =
  List.length r.items

let sitems_push x r =
  r.nb <- r.nb + 1;
  r.items <- x :: r.items


(********************************************************************)
(* ** Record-with *)

type recordwith = {
  mutable mya : int;
  mutable myb : int;
  mutable myc : int; }

let recordwith () =
  let r = { mya = 1; myb = 2; myc = 3 } in
  { r with myb = 5; mya = 6 }


(********************************************************************)
(* ** Evaluation order *)

let order_app () =
  let r = ref 0 in
  let h () = assert (!r = 2); (fun a b -> a + b) in
  let f () = incr r; 1 in
  let g () = assert (!r = 1); incr r; 1 in
  (h()) (g()) (f())

let order_constr () =
  let r = ref 0 in
  let f () = incr r; 1 in
  let g () = assert (!r = 1); 1 in
  (g() :: f() :: [])

let order_list () =
  let r = ref 0 in
  let f () = incr r; 1 in
  let g () = assert (!r = 1); 1 in
  [ g() ; f() ]

let order_tuple () =
  let r = ref 0 in
  let f () = incr r; 1 in
  let g () = assert (!r = 1); 1 in
  (g(), f())

let order_record () : 'a sitems =
  let r = ref 0 in
  let g () : 'a list = incr r; [] in
  let f () = assert (!r = 1); 1 in
  { nb = f(); items = g() }

(* not yet supported : relaxed value restriction;
   (below, the call to g() results in a fresh type variable).
   The work around is to annotate a bit more, as done above;
   this avoids having a type for [g] that is too general.

let order_record () =
  let r = ref 0 in
  let g () = incr r; [] in
  let f () = assert (!r = 1); 1 in
  { nb = f(); items = g() }
*)

let order_array () =
  let r = ref 0 in
  let f () = incr r; 1 in
  let g () = assert (!r = 1); 1 in
  [| g() ; f() |]


(********************************************************************)
(* ** References *)

let ref_gc () =
  let r1 = ref 1 in
  let _r2 = ref 1 in
  let _r3 = ref 1 in
  let _r4 = ref 1 in
  let x =
     let r5 = ref 2 in
     !r5
     in
  x + !r1

let ref_gc_dep x =
  let r = ref x in
  let s = ref r in
  r


(********************************************************************)
(* ** Arrays *)

let array_ops () =
  let u1 = [|1|] in
  let u2 = ([||] : int array) in
  (* TODO: not yet supported let u3 = [||] in*)
  let t = Array.make 3 0 in
  let _x = t.(1) in
  t.(2) <- 4;
  let _y = t.(2) in
  let _z = t.(1) in
  Array.length t


(********************************************************************)
(* ** While loops *)

let while_decr () =
   let n = ref 3 in
   let c = ref 0 in
   while !n > 0 do
      incr c;
      decr n;
   done;
   !c

let while_false () =
   while false do () done


(********************************************************************)
(* ** For loops *)

let for_to_incr r =
   let n = ref 0 in
   for i = 1 to r do
      incr n;
   done;
   !n

let for_to_incr_pred r =
   let n = ref 0 in
   for i = 0 to pred r do
      incr n;
   done;
   !n

let for_downto r =
   let n = ref 0 in
   for i = pred r downto 0 do
      incr n;
   done;
   !n


(********************************************************************)
(* ** Recursive function *)

let rec rec_partial_half x =
  if x = 0 then 0
  else if x = 1 then assert false
  else 1 + rec_partial_half (x-2)

let rec rec_mutual_f x =
  if x <= 0 then x else 1 + rec_mutual_g (x-2)
and rec_mutual_g x =
  rec_mutual_f (x+1)


(********************************************************************)
(* ** External *)

(* TODO: ocaml file does not compile with it
external external_func : int -> 'a -> 'a array = "%external_func"
*)


(********************************************************************)
(* ** Type abbreviation *)

type type_intpair = (int * int)

type 'a type_homo_pair = ('a * 'a)

type ('a,'b) type_poly_pair = (('a * 'b) * ('a * 'b))

let type_clashing_with_var = 3
type type_clashing_with_var = int


(********************************************************************)
(* ** Type algebraic *)

type 'a alga_three =
  | Alga_A
  | Alga_B of int * int
  | Alga_C of (int * int)
  | Alga_D of 'a
  | Alga_E of 'a * ('a -> 'a)

type ('a,'b) algb_erase =
  | Algb_A of 'a
  | Algb_B of (int -> 'b)


(********************************************************************)
(* ** Type record *)

type recorda = {
   mutable recorda1 : int;
   mutable recorda2 : int }

(*----*)

type ('a,'b) recordb =
  { mutable recordb1 : 'a ;
    mutable recordb2 : 'b -> 'b }

(* not supported: record overloading of fields
  -- else would need to prefix all fields with the type... *)


(********************************************************************)
(* ** Recursive definitions are supported for heap-allocated records *)

type 'a node = {
  mutable data : 'a;
  mutable prev : 'a node;
  mutable next : 'a node;
}

let create_cyclic_node (data: 'a): 'a node =
  let rec node = { data; prev = node; next = node } in
  node

(********************************************************************)
(* ** Type mutual *)

(*----*)

type typereca1 = | Typereca_1 of typereca2
 and typereca2 = | Typereca_2 of typereca1

(*----*)

(* not supported: recursive definitions using abbreviation

type typerecb1 = | Typerecb_1 of typerecb2
 and typerecb2 = typerecb1 list

   --> the work around by inlining, e.g.:
*)

type typerecc1 = | Typerecc_1 of typerecc1 list
type typerecc2 = typerecc1 list

(*----*)

(* not supported: recursive definition of inductive and pure records
   -- technically could be supported, if the record was encoded
      on the fly into a coq mutual inductive
type typerecb1 = | Typerecb_1 of typerecb2
 and typerecb2 = { typerecb_2 : typerecb1 }

  --> the work around is to break circularity using polymorphism, e.g.:
*)

type 'a typerecb2 = { mutable typerecb_2 : 'a }
type typerecb1 = | Typerecb_1 of typerecb1 typerecb2

(*----*)

(* Circularity between mutable records and inductive is broken
   through the indirection at type loc *)

type 'a typerecd1 = { mutable typerecd1_f : 'a typerecd2 }
and 'a typerecd2 =
   | Typerecd_2a
   | Typerecd_2b of 'a typerecd1
   | Typerecd_2c of 'a typerecd3
and 'a typerecd3 = { mutable typerecd3_f : 'a typerecd2 }



(********************************************************************)
(* ** Local module *)

module ModFoo = struct

   type t = int
   let x : t = 3

end


(********************************************************************)
(* ** Local module signature *)

module type ModBarType = sig

   type t
   val x : t

end

module ModBar : ModBarType = struct

   type t = int
   let x : t = 3

end


(********************************************************************)
(* ** Functor *)

module ModFunctor (Bar : ModBarType) = struct

   type u = Bar.t
   let x : u = Bar.x

end

module ModFunctorTyped (Bar : ModBarType) : ModBarType = struct

   type t = Bar.t
   let x : t = Bar.x

end


(********************************************************************)
(* ** Notation for PRE/INV/POST *)

let notation_inv_post r =
  !r

let notation_inv_postunit r =
  ()

let notation_pre_inv_post r s =
  incr r; !s


(********************************************************************)
(* ** Encoding of names *)

(* type renaming_t_ = int   --rejected *)
(* type renaming_t__ = int  --rejected *)
(* type renaming_t1 = C_  --rejected *)

type renaming_t' = int
type renaming_t2 = C'
type 'a renaming_t3 = int
type 'a_ renaming_t4 = int

let renaming_demo () =
   (* let x_ = 3 in   --rejected *)
   (* let x__ = 3 in  --rejected *)
   let _x = 3 in
   let _x' = 3 in
   let _x_' = 3 in
   let _exists = 3 in
   let _array = 3 in
   ()


(********************************************************************)
(* ** Ignored definitions *)

let ignored_def =
  ignore "CFML";
  3

let ignored_fun x =
  ignore "CFML";
  2 * x

let not_ignored_fun x =
  ignore x;
  2 * x

let rec ignored_fun2a x =
  ignore "CFML";
  ignored_fun2b x
and ignored_fun2b x =
  ignored_fun2a x



(********************************************************************)
(********************************************************************)
(********************************************************************)
(* IN PROGRESS *)

(********************************************************************)
(* ** TODO: import of auxiliary files, like in examples/DemoMake *)


(********************************************************************)
(* ** Comparison operators *)

(* TODO


let compare_int () =
  (1 <> 0 && 1 <= 2) || (0 = 1 && 1 >= 2 && 1 < 2 && 2 > 1)

let compare_min () =
  (min 0 1)

*)


(********************************************************************)
(* ** List operators *)

(* TODO

let list_ops () =
  let x = [1] in
  List.length (List.rev (List.concat (List.append [x] [x; x])))

*)

