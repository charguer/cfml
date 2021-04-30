
(** Implementation of a functional stack using lists and storing the size *)

type 'a t = {
   items : 'a list;
   size : int }

let empty =
  { items = [];
    size = 0 }

let size s =
  s.size

let is_empty s =
  s.size = 0

let push x s =
  { items = x :: s.items;
    size = s.size + 1 }

let pop s =
  match s.items with
  | hd::tl ->
      let s' = { items = tl; size = s.size -1 } in
      (hd, s')
  | [] -> assert false

let concat p1 p2 =
  { items = p1.items @ p2.items;
    size = p1.size + p2.size }
