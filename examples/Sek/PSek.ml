open PChunk
open View

type 'a psek = {
  sides : 'a pchunk array;
  mid : 'a pchunk psek option
}

let psek_default c =
  pchunk_default c.sides.(0)

let psek_create d = {
  sides = [| pchunk_create d; pchunk_create d |];
  mid = None
}
