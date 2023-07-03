open View
open PChunkImpl

type 'a pchunk = 'a PChunkImpl.pchunk

let pchunk_default = pchunk_default
let pchunk_dummy = pchunk_dummy
let pchunk_create = pchunk_create

let pchunk_is_empty = pchunk_is_empty
let pchunk_is_full = pchunk_is_full
let pchunk_size = pchunk_size

let pchunk_peek v =
  match v with
  | Front -> pchunk_peek_front
  | Back -> pchunk_peek_back

let pchunk_pop v =
  match v with
  | Front -> pchunk_pop_front
  | Back -> pchunk_pop_back

let pchunk_push v =
  match v with
  | Front -> pchunk_push_front
  | Back -> pchunk_push_back

let pchunk_get = pchunk_get
let pchunk_set = pchunk_set

let pchunk_concat = pchunk_concat
let pchunk_split = pchunk_split

let pchunk_of_echunk = pchunk_of_echunk
let echunk_of_pchunk = echunk_of_pchunk
