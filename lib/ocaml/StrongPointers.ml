
let magic = Obj.magic

let sref x = magic (ref x)
let sget p = !(magic p)
let sset p x = (magic p) := x
let cast p = magic p

