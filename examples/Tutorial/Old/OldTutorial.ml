


(***********************************************************************)
(** Basic operations *)

let example_let n =
  let a = n+1 in
  let b = n-1 in
  a + b

let example_incr r =
  r := !r + 1

let example_two_ref n =
  let i = ref 0 in
  let r = ref n in
  decr r;
  incr i;
  r := !i + !r;
  !i + !r


(***********************************************************************)
(** For loops *)

let facto_for n =
  let r = ref 1 in
  for i = 1 to n do
    r := !r * i;
  done;
  !r

let fib_for n =
  let a = ref 0 in
  let b = ref 1 in
  for i = 0 to n-1 do
    let c = !a + !b in
    a := !b;
    b := c;
  done;
  !a


(***********************************************************************)
(** While loops *)

let example_while n =
  let i = ref 0 in
  let r = ref 0 in
  while !i < n do
    incr i;
    incr r;
  done;
  !r

let facto_while n =
  let r = ref 1 in
  let i = ref 2 in
  while !i <= n do
    r := !i * !r;
    incr i;
  done;
  !r

let is_prime n =
  let i = ref 2 in
  let p = ref true in
  while !p && (!i * !i <= n) do
    if (n mod !i) = 0
      then p := false;
    incr i;
  done;
  !p


(***********************************************************************)
(** Recursion *)

let rec facto_rec n =
  if n <= 1
    then 1
    else n * facto_rec(n-1)

let rec fib_rec n =
  if n <= 1
    then n
    else fib_rec(n-1) + fib_rec(n-2)


(***********************************************************************)
(** Stack *)

module StackList = struct

  type 'a t = {
     mutable items : 'a list;
     mutable size : int }

  let create () =
    { items = [];
      size = 0 }

  let size s =
    s.size

  let is_empty s =
    s.size = 0

  let push x s =
    s.items <- x :: s.items;
    s.size <- s.size + 1

  let pop s =
    match s.items with
    | hd::tl ->
        s.items <- tl;
        s.size <- s.size   - 1;
        hd
    | [] -> assert false

end


(***********************************************************************)
(** Array *)

let demo_array () =
  let t = Array.make 3 true in
  t.(0) <- false;
  t.(1) <- false;
  t

let exercise_array () =
  let t = Array.make 3 true in
  t.(2) <- false;
  t.(1) <- t.(2);
  t


(***********************************************************************)
(** Vector *)

(* Futur work

module Vector = struct

  type 'a t = {
    mutable data : 'a array;
    mutable size : int;
    default: 'a; }

  let create size def =
    { data = Array.make size def;
      size = size;
      default = def; }

  let size t =
    t.size

  let get t i =
    t.data.(i)

  let set t i v =
    t.data.(i) <- v

  let double_size t =
    let src = t.data in
    let size = t.size in
    let size2 = 2 * size in
    let dst = Array.make size2 t.default in
    for i = 0 to pred size do
      dst.(i) <- src.(i);
    done

  let push t v =
    let size = t.size in
    let capa = Array.length t.data in
    if size = capa
      then double_size t;
    t.size <- size+1;
    t.data.(size) <- v

end

*)

(* Variants for double_size t:
   Array.iteri (fun i v <- dst.(i) <- v) src
   Array.init size2 (fun i -> if i < size then src.(i) else t.default)
*)


