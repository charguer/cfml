


(***********************************************************************)
(** Basic operations *)

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



(***********************************************************************)
(** Recursion *)

let rec facto_rec n =
  if n <= 1
    then 1
    else n * facto_rec(n-1)

let rec fib_rec n =
  if n <= 1
    then n
    else fib_rec(n-1) + fib_rec(n-2)


(***********************************************************************)
(** For loops *)

let facto_for n =
  let r = ref 1 in
  for i = 1 to n do
    r := !r * i;
  done;
  !r

let fib_for n =
  let a = ref 0 in
  let b = ref 1 in
  for i = 0 to n-1 do
    let c = !a + !b in
    a := !b;
    b := c;
  done;
  !a

(***********************************************************************)
(** While loops *)

let example_while n =
  let i = ref 0 in
  let r = ref 0 in
  while !i < n do
    incr i;
    incr r;
  done;
  !r

let facto_while n =
  let r = ref 1 in
  let i = ref 2 in
  while !i <= n do
    r := !i * !r;
    incr i;
  done;
  !r

let is_prime n =
  let i = ref 2 in
  let p = ref true in
  while !p && (!i * !i <= n) do
    if (n mod !i) = 0
      then p := false;
    incr i;
  done;
  !p


