
type 'a contents = Nil | Cons of 'a * 'a mlist
and 'a mlist = ('a contents) ref

let is_empty p =
  match !p with
  | Nil -> true
  | Cons (x,q) -> false

let create () =
  ref Nil

let push p x =
  let q = ref !p in
  p := Cons (x, q)

let pop p =
  match !p with
  | Nil -> assert false
  | Cons (x,q) -> p := !q; x

let rec rev_aux acc l =
  match !l with
  | Nil -> acc
  | Cons(x, r) ->
    let k = !r in
    r := !acc;
    rev_aux l (ref k)

let rev_main p =
  rev_aux (ref Nil) p
