
let f n =
  n + n

let rec g n =
  if n > 0 then g (n-1)

let rec dup n =
  if n > 0
    then 2 + dup (n-1)
    else 0

(* loops not yet suported *)
let for_loop n =
  for i = 0 to n-1 do
    ()
  done

let while_loop n =
  while !n > 0 do
    decr n
  done
