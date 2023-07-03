open Owner
open Capacity
open PChunkImpl

type 'a schunk = {
  support : 'a pchunk;
  id : owner }

(* Two specs for [s: 'a schunk]:
  - either [s] is uniquely owned by some owner [o], in which case
    [s.support.data] is a [PArray_Base] and one may work directly
    on the underlying array
  - either [s] is shared and behaves as a regular ['a parray] *)
  
let schunk_default c =
pchunk_default c.support

let schunk_dummy d = {
  support = pchunk_dummy d;
  id = none }

(** [schunk_create d o]
  returns an empty schunk with default value [d] and id [o]. *)
let schunk_create d o = {
  support = pchunk_create d;
  id = o }

(** [schunk_create_shared d]
  returns an empty schunk with default value [d] and id [none]. *)
let schunk_create_shared d =
  schunk_create d none

(** [schunk_is_empty c]
  checks whether [s] is empty. *)
let schunk_is_empty c =
  pchunk_is_empty c.support

(** [schunk_is_full c]
  checks whether [c] is full. *)
let pchunk_is_full c =
  pchunk_is_full c.support

(** [schunk_size c]
  returns the number of elements in [c]. *)
let schunk_size c =
  pchunk_size c.support

(** [schunk_support_unique c]
  Given a schunk c that is uniquely owned, returns the underlying array *)
let schunk_get_uniquely_owned_support c =
  let sp = c.support in
  let pa = sp.data in
  match pa.PArray.desc with
  | PArray.PArray_Base a -> a
  | _ -> assert false (* Not supposed to happen in the expected use cases *)

(** [pchunk_peek_back c]
  returns the back element of [c]. *)
let pchunk_peek_back c =
  let back = wrap_up (c.front + c.size - 1) in
  parray_get c.data back

(** [pchunk_pop_back c]
  returns the pair of a pchunk with all elements of [c] except the back one,
  and of the back element. *)
let pchunk_pop_back c =
  let x = pchunk_peek_back c in
  let new_size = c.size - 1 in
  let i = wrap_up (c.front + new_size) in
  let pa = parray_set c.data i c.default in
  let c' = {
    data = pa;
    front = c.front;
    size = new_size;
    default = c.default } in
  (c', x)

(** [pchunk_push_back c x]
  returns a pchunk with all elements of [c] and [x] added at the back. *)
let pchunk_push_back c x =
  let i = wrap_up (c.front + c.size) in
  { data = parray_set c.data i x;
    front = c.front;
    size = c.size + 1;
    default = c.default }

(** [pchunk_peek_front c]
  returns the front element of [c]. *)
let pchunk_peek_front c =
  parray_get c.data c.front

(** [pchunk_pop_front c]
  returns the pair of a pchunk with all elements of [c] except the front one,
  and of the front element. *)
let pchunk_pop_front c =
  let x = pchunk_peek_front c in
  let pa = parray_set c.data c.front c.default in
  let c' = {
    data = pa;
    front = wrap_up (c.front + 1);
    size = c.size - 1;
    default = c.default } in
  (c', x)

(** [pchunk_push_front c x]
  returns a pchunk with all elements of [c] and [x] added at the front. *)
let pchunk_push_front c x =
  let new_front = wrap_down (c.front - 1) in
  let pa = parray_set c.data new_front x in
  { data = pa;
    front = new_front;
    size = c.size + 1;
    default = c.default }

(** [pchunk_get c i]
  returns the element stored in [i]-th position in [c]. *)
let pchunk_get c i =
  let j = wrap_up (c.front + i) in
  parray_get c.data j

(** [pchunk_set c i x]
  returns a pchunk with all elements of [c],
  except the one in the [i]-th position which is replaced by [x]. *)
let pchunk_set c i x =
  let front = c.front in
  let j = wrap_up (front + i) in
  let pa = parray_set c.data j x in
  { data = pa;
    front = front;
    size = c.size;
    default = c.default }

(** [pchunk_concat c0 c1]
  returns a pchunk that contains all elements of [c0] and of [c1].

  Implemented by growing a pchunk starting from [c0], thus the
  cost is proportional to the size of [c1].
  Requires the combined sizes of [c0] and [c1] to not exceed capacity. *)
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

(** [pchunk_displace c0 c1 k]
  migrates [k] elements from the back of [c0] to the front of [c1].
  Returns the pair of the shrunk [c0] and the extended [c1]. *)
let rec pchunk_displace c0 c1 k =
  if k = 0 then
    (c0, c1)
  else begin
    let c0', x = pchunk_pop_back c0 in
    let c1' = pchunk_push_front c1 x in
    pchunk_displace c0' c1' (k - 1)
  end

(** [pchunk_split c k]
  returns a pair of pchunks [(c1, c2)] such that [c1] contains
  the [k] front elements from [c] and [c2] contains
  the remaining [size c - k] elements. *)
let pchunk_split c k =
  let c0 = pchunk_create c.default in
  pchunk_displace c c0 (c.size - k)

(** [pchunk_of_echunk ec] consumes an [echunk] for producing a [pchunk]. *)
let pchunk_of_echunk ec =
  let dat, f, s, d = EChunkImpl.echunk_fields ec in
  { data = parray_of_array dat;
  front = f;
  size = s;
  default = d }
