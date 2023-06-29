type view = Front | Back

let view_index v =
  match v with
  | Front -> 0
  | Back -> 1

let view_swap v =
  match v with
  | Front -> Back
  | Back -> Front

let view_xor v1 v2 =
  match v1 with
  | Front -> v2
  | Back -> view_swap v2

let view_exchange v (x, y) =
  match v with
  | Front -> (x, y)
  | Back -> (y, x)
