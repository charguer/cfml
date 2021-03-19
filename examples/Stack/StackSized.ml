
(** Implementation of a stack using lists and storing the size *)

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
      s.size <- s.size - 1;
      hd
  | [] -> assert false

let clear p =
  p.items <- [];
  p.size <- 0

let concat p1 p2 =
  p1.items <- p1.items @ p2.items;
  p1.size <- p1.size + p2.size;
  clear p2
