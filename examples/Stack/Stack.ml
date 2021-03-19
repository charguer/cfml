
(** Implementation of a stack using lists *)

type 'a stack = ('a list) ref

let create () =
  ref []

let is_empty p =
  !p = []

let push p x =
  p := x :: !p

let pop p =
  match !p with
  | [] -> raise Not_found
  | x::r -> p := r; x

let clear p =
  p := []

let concat p1 p2 =
  p1 := !p1 @ !p2;
  clear p2

let rec rev_append p1 p2 =
  if not (is_empty p1) then begin
    let x = pop p1 in
    push p2 x;
    rev_append p1 p2
  end
