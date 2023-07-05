open Capacity

(** Fixed capacity circular buffers. *)
type 'a echunk = {
  data : 'a array;
  mutable front : int;
  mutable size : int;
  default : 'a }

(** [echunk_fields c]
  returns the 4-tuple of the fields of [c].
  Hopefully we can get rid of this later... *)
let echunk_fields c =
  c.data, c.front, c.size, c.default

(** [echunk_of_fields a f s d]
  makes an [echunk] with the specified fields. *)
let echunk_of_fields a f s d = {
  data = a;
  front = f;
  size = s;
  default = d }

(** [echunk_default c]
  returns the default value of c. *)
let echunk_default c =
  c.default

(* Useful? *)
let echunk_dummy d = {
  data = [||];
  front = 0;
  size = 0;
  default = d }

(** [echunk_create d]
  returns an empty fresh [echunk] with default value [d]. *)
let echunk_create d = {
  data = Array.make capacity d;
  front = 0;
  size = 0;
  default = d }

(** [echunk_is_empty c]
  checks for emptiness of [c]. *)
let echunk_is_empty c =
  c.size = 0

(** [echunk_is_full c]
  checks for fullness of [c]. *)
let echunk_is_full c =
  c.size = capacity

(** [echunk_size c]
  returns the number of elements in [c]. *)
let echunk_size c =
  c.size

(** [echunk_peek_back c]
  returns the value at the back of [c]. *)
let echunk_peek_back c =
  let back = wrap_up (c.front + c.size - 1) in
  c.data.(back)

(** [echunk_pop_back c]
  removes and returns the value at the back of [c]. *)
let echunk_pop_back c =
  let new_size = c.size - 1 in
  c.size <- new_size;
  let i = wrap_up (c.front + new_size) in
  let x = c.data.(i) in
  c.data.(i) <- c.default;
  x

(** [echunk_push_back c x]
  appends the value [x] to the back of [c]. *)
let echunk_push_back c x =
  let old_size = c.size in
  c.size <- old_size + 1;
  let i = wrap_up (c.front + old_size) in
  c.data.(i) <- x

(** [echunk_peek_front c]
  returns the value at the front of [c]. *)
let echunk_peek_front c =
  c.data.(c.front)

(** [echunk_pop_front c]
  removes and returns the value at the front of [c]. *)
let echunk_pop_front c =
  let old_front = c.front in
  c.size <- c.size - 1;
  c.front <- wrap_up (old_front + 1);
  let x = c.data.(old_front) in
  c.data.(old_front) <- c.default;
  x

(** [echunk_push_front c x]
  appends the value [x] to the front of [c]. *)
let echunk_push_front c x =
  let new_front = wrap_down (c.front - 1) in
  c.size <- c.size + 1;
  c.front <- new_front;
  c.data.(new_front) <- x

(** [echunk_get c i]
  returns the value stored at the [i]-th position in [c]. *)
let echunk_get c i =
  let j = wrap_up (c.front + i) in
  c.data.(j)

(** [echunk_set c i x]
  sets the value stored at the [i]-th position in [c] to [x]. *)
let echunk_set c i x =
  let j = wrap_up (c.front + i) in
  c.data.(j) <- x

(** [echunk_copy c]
  returns a fresh copy of [c]. *)
let echunk_copy c =
  let a = Array.copy c.data in
  { data = a;
    front = c.front;
    size = c.size;
    default = c.default }


(*---------------------------------------------------------------------------*)
(* LATER? *)

(*
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
