open PWSek
open Weighted
open View

let psek_push pov s x =
  pwsek_push pov s (mk_weighted x 1)

let psek_push_front s x =
  psek_push Front s x



