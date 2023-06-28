type view = Front | Back

let view_index v =
  match v with Front -> 0 | Back -> 1

let view_swap v =
  match v with Front -> Back | Back -> Front

let view_xor v w =
  match v with Front -> w | Back -> view_swap w

let view_exchange v (a, b) =
  match v with Front -> (a, b) | Back -> (b, a)
