open PArray
open Capacity

(** Type pour des buffers circulaires de capacité fixe K *)

type 'a pchunk = {
  p_data : 'a parray;
  p_front : int;
  p_size : int;
  p_default : 'a }

let pchunk_default c =
  c.p_default

let pchunk_dummy d = {
  p_data = parray_create 0 d;
  p_front = 0;
  p_size = 0;
  p_default = d }

let pchunk_create d = {
  p_data = parray_create capacity d;
  p_front = 0;
  p_size = 0;
  p_default = d }

let pchunk_is_empty c =
  c.p_size = 0

let pchunk_is_full c =
  c.p_size = capacity

let pchunk_size c =
  c.p_size

let pchunk_peek_back c =
  let back = wrap_up (c.p_front + c.p_size - 1) in
  parray_get c.p_data back

let pchunk_pop_back c =
  let x = pchunk_peek_back c in
  let new_size = c.p_size - 1 in
  let i = wrap_up (c.p_front + new_size) in
  let pa = parray_set c.p_data i c.p_default in
  let c' = {
    p_data = pa;
    p_front = c.p_front;
    p_size = new_size;
    p_default = c.p_default } in
  (c', x)

let pchunk_push_back c x =
  let i = wrap_up (c.p_front + c.p_size) in {
    p_data = parray_set c.p_data i x;
    p_front = c.p_front;
    p_size = c.p_size + 1;
    p_default = c.p_default
  }

let pchunk_peek_front c =
  parray_get c.p_data c.p_front

let pchunk_pop_front c =
  let x = pchunk_peek_front c in
  let pa = parray_set c.p_data c.p_front c.p_default in
  let c' = {
    p_data = pa;
    p_front = wrap_up (c.p_front + 1);
    p_size = c.p_size - 1;
    p_default = c.p_default
  } in
  (c', x)

let pchunk_push_front c x =
  let new_front = wrap_down (c.p_front - 1) in {
    p_data = parray_set c.p_data new_front x;
    p_front = new_front;
    p_size = c.p_size + 1;
    p_default = c.p_default
  }

let pchunk_get c i =
  let j = wrap_up (c.p_front + i) in
  parray_get c.p_data j

let pchunk_set c i x =
  let j = wrap_up (front + i) in
  let pa = parray_set c.p_data j x in
  let front = c.p_front in {
    p_data = pa;
    p_front = front;
    p_size = c.p_size;
    p_default = c.p_default
  }

(* returns a pchunk that contains all elements of c0 and of c1;
   implemented by growing a pchunk starting from c0, thus the
   cost is proportional to the size of c1;
   requires the size of c0 plus the size of c1 to not exceed capacity *)
let rec pchunk_concat c0 c1 =
  if pchunk_is_empty c1 then
    c0
  (* else if pchunk_is_empty c0 then
    c1 *)
  else begin
    let c1', x = pchunk_pop_front c1 in
    let c0' = pchunk_push_back c0 x in
    pchunk_concat c0' c1'
  end

(* [pchunk_displace c0 c1 k] migrates [k] elements from back of [c0] to
   the front of c1; returns the pair of what the shrunk c0 and the extended c1 *)
let rec pchunk_displace c0 c1 k =
  if k = 0 then
    (c0, c1)
  else begin
    let c0', x = pchunk_pop_back c0 in
    let c1' = pchunk_push_front c1 x in
    pchunk_displace c0' c1' (k - 1)
  end

(* given a pchunk [c] and an integer [k], and returns a pair of pchunks
   [(c1,c2)] such that [c1] contains the first [k] elements from [c]
   and [c2] contains the remaining [size c - k] elements. *)
let pchunk_split c k =
  let c0 = pchunk_create c.p_default in
  pchunk_displace c c0 k


(* TODO pchunk_of_echunk using parray_of_array *)