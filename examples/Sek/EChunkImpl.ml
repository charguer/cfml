open Capacity

(** Type pour des buffers circulaires de capacité fixe K   TODO TRANSLATE ALL*)

type 'a echunk = { (* TODO: remove prefixes *)
  data : 'a array;
  mutable front : int;
  mutable size : int;
  default : 'a }

let echunk_fields c =
  c.data, c.front, c.size, c.default

let echunk_default c =
  c.default

let echunk_dummy d = {
  data = [||];
  front = 0;
  size = 0;
  default = d
}

let echunk_create d = {
  data = Array.make capacity d;
  front = 0;
  size = 0;
  default = d
}

let echunk_is_empty c =
  c.size = 0

let echunk_is_full c =
  c.size = capacity

let echunk_peek_back c =
  let back = wrap_up (c.front + c.size - 1) in
  c.data.(back)

let echunk_pop_back c =
  let x = echunk_peek_back c in
  let new_size = c.size - 1 in
  c.size <- new_size;
  let i = wrap_up (c.front + new_size) in
  c.data.(i) <- c.default;
  x

let echunk_push_back c x =
  let old_size = c.size in
  c.size <- old_size + 1;
  let i = wrap_up (c.front + old_size) in
  c.data.(i) <- x

let echunk_peek_front c =
  c.data.(c.front)

let echunk_pop_front c =
  let x = echunk_peek_front c in
  let old_front = c.front in
  c.size <- c.size - 1;
  c.front <- wrap_up (old_front + 1);
  c.data.(old_front) <- c.default;
  x

let echunk_push_front c x =
  let new_front = wrap_down (c.front - 1) in
  c.size <- c.size + 1;
  c.front <- new_front;
  c.data.(new_front) <- x

(* let echunk_get c i =
  c.data.(i)

let echunk_set c i x =
  c.data.(i) <- x *)

(* let echunk_copy c =
  let data = Array.copy c.data in
  { data = data;
    top = c.top;
    default = c.default }

let echunk_sub c size =
  let d = c.default in
  let t = c.data in
  let item i =
    if i < size then t.(i) else d in
  let tsub = Array.init capacity item in
  { data = tsub;
    top = size;
    default = d; }
*)
