open EChunkImpl
open View

let echunk_default = echunk_default
let echunk_dummy = echunk_dummy
let echunk_create = echunk_create
let echunk_is_empty = echunk_is_empty
let echunk_is_full = echunk_is_full

let echunk_peek = function
  | Front -> echunk_peek_front
  | Back -> echunk_peek_back

let echunk_pop = function
  | Front -> echunk_pop_front
  | Back -> echunk_pop_back

let echunk_push = function
  | Front -> echunk_push_front
  | Back -> echunk_push_back
