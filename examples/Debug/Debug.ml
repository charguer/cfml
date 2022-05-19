
let f r n =
  r := !r + n

let rec g x =
  if x = 0 then 0 else
  let y = g (x-1) in
  y + 2

let v = 2
