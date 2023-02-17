
type 'a contents = Nil | Cons of 'a * 'a mlist
and 'a mlist = ('a contents) ref


let is_empty p =
  match !p with
  | Nil -> true
  | Cons (x,q) -> false

let create () =
  ref Nil

let head p =
  match !p with
  | Nil -> raise Not_found
  | Cons (x,q) -> x

let tail p =
  match !p with
  | Nil -> raise Not_found
  | Cons (x,q) -> q

let push p x =
  p := Cons (x, p)

let pop p =
  let x = head p in
  p := !(tail p);
  x

(*

let mk_cons x q =
  ref (Cons x q)

let set_nil p =
  p := Nil

let set_cons p x q =
  p := Cons x q
*)
