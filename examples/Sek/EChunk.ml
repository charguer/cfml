open View
open EChunkImpl

type 'a echunk = 'a EChunkImpl.echunk

let echunk_default = echunk_default
let echunk_dummy = echunk_dummy
let echunk_create = echunk_create

let echunk_is_empty = echunk_is_empty
let echunk_is_full = echunk_is_full
let echunk_size = echunk_size

let echunk_peek v =
  match v with
  | Front -> echunk_peek_front
  | Back -> echunk_peek_back

let echunk_pop v =
  match v with
  | Front -> echunk_pop_front
  | Back -> echunk_pop_back

let echunk_push v =
  match v with
  | Front -> echunk_push_front
  | Back -> echunk_push_back

let echunk_get = echunk_get
let echunk_set = echunk_set

let echunk_copy = echunk_copy
