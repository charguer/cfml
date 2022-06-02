
let f r n =
  r := !r + n

let id x = x

let idapp () =
  let a = id 1 in
  let b = id true in
  2

let apply f x = f x

let rec g x =
  if x = 0 then 0 else
  let y = g (x-1) in
  y + 2

let v = 2

let bools b =
  if true then b || false else b && true

let pair_swap (x,y) =
  (y,x)

let rec map f l =
  match l with
  | [] -> []
  | x::t -> f x :: map f t

type 'a mylist = Nil | Cons of 'a * 'a mylist

let rec mymap f l =
  match l with
  | Nil -> Nil
  | Cons(x,t) -> Cons (f x, mymap f t)
