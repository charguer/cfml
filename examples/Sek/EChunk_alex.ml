
type 'a default = 'a

type 'a echunk = {
  data : 'a array;
  mutable top : int;
  default : 'a default; }

(* Capacity is hard-coded for now, to avoid the boilerplate of a functor *)
let capacity = 16

let echunk_default c =
  c.default

let echunk_dummy d =
  { data = [||];
    top = 0;
    default = d; }

let echunk_create d =
  { data = Array.make capacity d;
    top = 0;
    default = d; }

let echunk_is_empty c =
  c.top = 0

let echunk_is_full c =
  c.top = capacity

let echunk_peek c =
  assert (not (echunk_is_empty c));
  c.data.(c.top-1)

let echunk_pop c =
  let x = echunk_peek c in
  let newtop = c.top - 1 in
  c.top <- newtop;
  c.data.(newtop) <- c.default;
  x

let echunk_push c x =
  c.data.(c.top) <- x;
  c.top <- c.top + 1

let echunk_get c i =
  c.data.(i)

let echunk_set c i x =
  c.data.(i) <- x

let echunk_copy c =
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
    default = d; }
