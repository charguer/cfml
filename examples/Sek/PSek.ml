open PChunk
open View

type 'a psek = {
  sides : 'a pchunk array;
  mid : 'a pchunk psek option
}

let psek_default =
  pchunk_default sides.(0)

let psek_create d = {
  sides = [| pchunk_create d; pchunk_create d |];
  mid = None
}

let psek_is_empty =
  match mid with
  | None -> pchunk_is_empty sides.(0) && pchunk_is_empty sides.(1)
  | Some _ -> false
