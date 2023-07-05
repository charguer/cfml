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

(** [echunk_carve v c0 c1 i]
  moves the first [i] element of [c0] at the side pointed by [v] to the other side of [c1] *)
let rec echunk_carve v c0 c1 i =
  if i > 0 then begin
    let x = echunk_pop v c0 in
    echunk_push (view_swap v) c1 x;
    echunk_carve v c0 c1 (i - 1)
  end

(** [echunk_split c i]
  moves the [i] first elements of [c] to another fresh chunk [c0].
  [c0 ++ c = old c]*)
let echunk_split c i =
  let d = echunk_default c in
  let c0 = echunk_create d in
  echunk_carve Front c c0 i;
  c0, c
