open PWSek
open Weighted

let psek_push pov s x =
  pwsek_push pov s (mk_weighted x 1)
