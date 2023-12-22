type t = unit ref

let create () =
  ref ()

let eq x y =
  x == y

let eq_opt x y =
  match x with
  | None -> false
  | Some x' -> x' == y
