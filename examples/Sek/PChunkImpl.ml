open PArray

(**
  Type pour des buffers circulaires de capacité fixe K
*)
type 'a pchunk = {
  p_data : 'a parray;
  p_front : int;
  p_size : int;
  p_default : 'a
}
let capacity = 32

let pchunk_default c = c.p_default

let pchunk_dummy d = {
  p_data = parray_create 0 d;
  p_front = 0;
  p_size = 0;
  p_default = d
}

let pchunk_create d = {
  p_data = parray_create capacity d;
  p_front = 0;
  p_size = 0;
  p_default = d
}

let pchunk_is_empty c =
  c.p_size = 0
let pchunk_is_full c =
  c.p_size = capacity

let wrap_up n =
  if n >= capacity then n - capacity else n

let pchunk_peek_back c =
  let back = wrap_up (c.p_front + c.p_size - 1) in
  parray_get c.p_data back

let pchunk_pop_back c =
  let x = pchunk_peek_back c in
  let new_size = c.p_size - 1 in
  let i = wrap_up (c.p_front + new_size) in
  let c' = {
    p_data = parray_set c.p_data i c.p_default;
    p_front = c.p_front;
    p_size = new_size;
    p_default = c.p_default
  } in
  (x, c')

let pchunk_push_back c x =
  let i = wrap_up (c.p_front + c.p_size) in
  {
    p_data = parray_set c.p_data i x;
    p_front = c.p_front;
    p_size = c.p_size + 1;
    p_default = c.p_default
  }

let wrap_down n =
  if n < 0 then n + capacity else n

let pchunk_peek_front c =
  parray_get c.p_data c.p_front

let pchunk_pop_front c =
  let x = pchunk_peek_front c in
  let c' = {
    p_data = parray_set c.p_data c.p_front c.p_default;
    p_front = wrap_up (c.p_front + 1);
    p_size = c.p_size - 1;
    p_default = c.p_default
  } in
  (x, c')

let pchunk_push_front c x =
  let new_front = wrap_down (c.p_front - 1) in
  {
    p_data = parray_set c.p_data new_front x;
    p_front = new_front;
    p_size = c.p_size + 1;
    p_default = c.p_default
  }

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
  (* assert (size <= 0 && size <= c.top); *)
  let d = c.default in
  let t = c.data in
  let item i =
    if i < size then t.(i) else d in
  let tsub = Array.init capacity item in
  { data = tsub;
    top = size;
    default = d; } *)
