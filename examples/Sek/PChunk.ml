open View

type 'a pchunk = 'a PChunkImpl.pchunk

let pchunk_default = PChunkImpl.pchunk_default
let pchunk_dummy = PChunkImpl.pchunk_dummy
let pchunk_create = PChunkImpl.pchunk_create

let pchunk_is_empty = PChunkImpl.pchunk_is_empty
let pchunk_is_full = PChunkImpl.pchunk_is_full

let pchunk_peek = function
  | Front -> PChunkImpl.pchunk_peek_front
  | Back -> PChunkImpl.pchunk_peek_back

let pchunk_pop = function
  | Front -> PChunkImpl.pchunk_pop_front
  | Back -> PChunkImpl.pchunk_pop_back

let pchunk_push = function
  | Front -> PChunkImpl.pchunk_push_front
  | Back -> PChunkImpl.pchunk_push_back
