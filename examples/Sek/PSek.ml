open Weighted
open PWSek

type 'a psek = 'a pwsek

let psek_default = pwsek_default

let psek_create d =
  pwsek_create d None

let psek_is_empty = pwsek_is_empty

let psek_pop v s =
  let s', x = pwsek_pop v None s in
  s', (unweighted x)

let psek_push pov s x =
  pwsek_push pov None s (mk_weighted x 1)

let psek_concat c0 c1 =
  pwsek_concat None c0 c1

let psek_split c i =
  pwsek_split None c i
