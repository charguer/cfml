open Weighted
open SWSek
open ESek

type 'a psek = 'a swsek

let psek_create d =
  swsek_create d None

let psek_is_empty = swsek_is_empty

let psek_pop v s =
  let s', x = swsek_pop v None s in
  s', (unweighted x)

let psek_push pov s x =
  swsek_push pov None s (mk_weighted x 1)

let psek_concat c0 c1 =
  swsek_concat None c0 c1

let psek_split c i =
  swsek_split None c i

let psek_of_esek = swsek_of_esek

let esek_of_psek = esek_of_swsek
