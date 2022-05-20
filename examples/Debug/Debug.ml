
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
