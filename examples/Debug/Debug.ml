
type 'a poly =
  | Empty of 'a
  | Pair of ('a * 'a) poly

let rec polydepth : 'a. 'a poly -> int = fun s ->
  match s with
  | Empty _ -> 0
  | Pair s2 -> 1 + polydepth s2

type 'a mylist = Nil | Cons of 'a * 'a mylist

let rec mymap f l =
  match l with
  | Nil -> Nil
  | Cons(x,t) -> Cons (f x, mymap f t)

type myintlist = int mylist


let rec listmap f l =
  match l with
  | [] -> []
  | x::t -> f x :: listmap f t

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

