


(***********************************************************************)
(** Demos *)

let example_let n =
  let a = n+1 in
  let b = n-1 in
  a + b

let incr r =
  r := !r + 1

let succ_using_incr n =
  let p = ref n in
  incr p;
  !p

let incr_one_of_two p q =
  incr p

let incr_and_ref p =
  incr p;
  ref !p

let rec repeat_incr p m =
  if m > 0 then (
    incr p;
    repeat_incr p (m-1)
  )


(***********************************************************************)
(** Hands-on *)

let double n =
  n + n

let inplace_double p =
    p := !p + !p

let decr_and_incr p q =
  decr p;
  incr q

let rec transfer p q =
  if !p > 0 then (
    decr p;
    incr q;
    transfer p q
  )


