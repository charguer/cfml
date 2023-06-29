open Capacity

(** Type pour des buffers circulaires de capacité fixe K   TODO TRANSLATE ALL*)

type 'a echunk = { (* TODO: remove prefixes *)
  e_data : 'a array;
  mutable e_front : int;
  mutable e_size : int;
  e_default : 'a }

let echunk_default c =
  c.e_default

let echunk_dummy d = {
  e_data = [||];
  e_front = 0;
  e_size = 0;
  e_default = d
}

let echunk_create d = {
  e_data = Array.make capacity d;
  e_front = 0;
  e_size = 0;
  e_default = d
}

let echunk_is_empty c =
  c.e_size = 0

let echunk_is_full c =
  c.e_size = capacity

let echunk_peek_back c =
  let back = wrap_up (c.e_front + c.e_size - 1) in
  c.e_data.(back)

let echunk_pop_back c =
  let x = echunk_peek_back c in
  let new_size = c.e_size - 1 in
  c.e_size <- new_size;
  let i = wrap_up (c.e_front + new_size) in
  c.e_data.(i) <- c.e_default;
  x

let echunk_push_back c x =
  let old_size = c.e_size in
  c.e_size <- old_size + 1;
  let i = wrap_up (c.e_front + old_size) in
  c.e_data.(i) <- x

let echunk_peek_front c =
  c.e_data.(c.e_front)

let echunk_pop_front c =
  let x = echunk_peek_front c in
  let old_front = c.e_front in
  c.e_size <- c.e_size - 1;
  c.e_front <- wrap_up (old_front + 1);
  c.e_data.(old_front) <- c.e_default;
  x

let echunk_push_front c x =
  let new_front = wrap_down (c.e_front - 1) in
  c.e_size <- c.e_size + 1;
  c.e_front <- new_front;
  c.e_data.(new_front) <- x

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
