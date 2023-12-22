open EChunk

type 'a schunk = {
  support : 'a echunk;
  view : int;
  owner : Id.t option; }

let get_default x =
  x.support.default

let copy_array_sized size c d =
  let rd i = if i < size then c.(i) else d in
  Array.init capacity rd

let echunk_of_schunk p =
  let d = p.support.default in
  let t = copy_array_sized p.view p.support.data p.support.default in
  { data = t;
    top = p.view;
    default = d; }

let schunk_of_echunk c v =
  { support = c;
    view = c.top;
    owner = Some v; }

let schunk_empty d =
  { support = echunk_create d;
    view = 0;
    owner = None; }

let schunk_is_empty p =
  p.view = 0

let schunk_is_full p =
  p.view = capacity

let schunk_peek p =
  assert (not (schunk_is_empty p));
  p.support.data.(p.view-1)

let schunk_push p x =
  let n = p.view in
  if n = p.support.top then begin
      echunk_push p.support x;
      { p with view = n+1 }
    end else begin
      let c = echunk_of_schunk p in
      echunk_push c x;
      { support = c;
        view = n+1;
        owner = None; }
    end

let schunk_pop p =
  let x = schunk_peek p in
  let n = p.view - 1 in
  { p with view = n }, x
