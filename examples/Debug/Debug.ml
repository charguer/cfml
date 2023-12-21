(* THIS FILE IS USED FOR DEBUGGING PURPOSE ONLY *)


(* work-in-progress on testing validation *)

let prim a b x y =
  if (not b) && (a || b)
    then x + (y - (x - 1)) + y >= x
    else x < y


type 'a poly =
  | PEmpty of 'a
  | Pair of ('a * 'a) poly

let rec polydepth : 'a. 'a poly -> int = fun s ->
  match s with
  | PEmpty _ -> 0
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




(*=======================================
exception EmptyStructure
exception BrokenInvariant
exception OutOfBound



type color = Red | Black
type rbtree = Empty | Node of color * rbtree * int * rbtree

let balance t =
  match t with
  | (Black, Node (Red, Node (Red, a, x, b), y, c), z, d) ->
      Node (Red, Node (Black, a, x, b), y, Node (Black, c, z, d))
  (*| (Black, Node (Red, a, x, Node (Red, b, y, c)), z, d) ->
      Node (Red, Node (Black, a, x, b), y, Node (Black, c, z, d))
  | (Black, a, x, Node (Red, Node (Red, b, y, c), z, d)) ->
      Node (Red, Node (Black, a, x, b), y, Node (Black, c, z, d))
  | (Black, a, x, Node (Red, b, y, Node (Red, c, z, d))) ->
      Node (Red, Node (Black, a, x, b), y, Node (Black, c, z, d))*)
  | (c,a,x,y) -> Node (c,a,x,y)
*)

(*-----



type 'a tree = Leaf of 'a | Node of int * 'a tree * 'a tree
type 'a digit = Zero | One of 'a tree
type 'a rlist = 'a digit list


let size = function
  | Leaf x -> 1
  | Node (w, _, _) -> w


let rec lookup_tree i = function
  | Leaf x -> if i = 0 then x else raise OutOfBound
  | Node (w, t1, t2) ->
      if i < w/2
        then lookup_tree i t1
        else lookup_tree (i - w/2) t2

let rec lookup i = function
  | [] -> raise OutOfBound
  | Zero :: ts -> lookup i ts
  | One t :: ts ->
     if i < size t
        then lookup_tree i t
        else lookup (i - size t) ts

*)
(*---


--*)