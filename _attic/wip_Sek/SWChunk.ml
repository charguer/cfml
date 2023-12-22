open View
open Weighted
open SChunk

type 'a partial_swchunk = ('a weighted) schunk
type 'a swchunk = ('a partial_swchunk) weighted

let swchunk_default (c: 'a swchunk) =
  unweighted (schunk_default (unweighted c))

let swchunk_dummy d : 'a swchunk =
  let uw = schunk_dummy (dummy_weighted d) in
  dummy_weighted uw

let partial_swchunk_create d oo : 'a partial_swchunk =
  schunk_create (dummy_weighted d) oo

let swchunk_create d oo : 'a swchunk =
  let uw = partial_swchunk_create d oo in
  dummy_weighted uw

let swchunk_is_empty (c: 'a swchunk) =
  schunk_is_empty (unweighted c)

let swchunk_is_full (c: 'a swchunk) =
  schunk_is_full (unweighted c)

let swchunk_size (c: 'a swchunk) =
  schunk_size (unweighted c)

let swchunk_peek v (c: 'a swchunk) : 'a weighted =
  schunk_peek v (unweighted c)

let swchunk_push v o (c: 'a swchunk) x : 'a swchunk =
  let uw = schunk_push v o (unweighted c) x in
  mk_weighted uw (weight c + weight x)

let swchunk_pop v o (c: 'a swchunk) : 'a swchunk * 'a weighted =
  let uw, x = schunk_pop v o (unweighted c) in
  mk_weighted uw (weight c - weight x), x

let swchunk_concat o (c0: 'a swchunk) (c1: 'a swchunk) : 'a swchunk =
  let el = schunk_concat o (unweighted c0) (unweighted c1) in
  mk_weighted el (weight c0 + weight c1)
  (* Or reimplement it with the push and pop directly, no real advantage *)

(** [swchunk_carve v o c0 c1 w]
  moves the element of [c0] at the side pointed by v to the other side of [c1]
  as long as the combined weight of moved elements does not exceed [w].
  We want [w] to not exceed the total weight stored.
  Returns the pair the extended [c1] and of the shrunk [c0] *)
let rec swchunk_carve v o (c0: 'a swchunk) (c1: 'a swchunk) w =
  (* assert (not (swchunk_is_empty c0)) *)
  let c0', x = swchunk_pop v o c0 in
  if weight x > w then
    c1, c0
  else begin
    let c1' = swchunk_push (view_swap v) o c1 x in
    swchunk_carve v o c0' c1' (w - weight x)
  end

(** [swchunk_split o c w]
  returns the pair of the longest prefix of [c] of weight not exceeding [w],
  and of its complementary suffix. *)
let swchunk_split o (c: 'a swchunk) w =
  let c0 = swchunk_create (swchunk_default c) o in
  swchunk_carve Front o c c0 w

(* [swchunk_split c w] returns [(c1, c2)] such that [c1 ++ c2 = c] and [c1] is
  maximal such that [weight c1 <= w]
  works only if weights are all positive... not very elegant to *)
(* let swchunk_split c w =
  let uw = unweighted c in
  let b = weight c - w in
  let i = ref (schunk_size uw) in
  let a = ref 0 in
  while !i > 0 && !a < b do
    decr i;
    a := !a + weight (schunk_get uw !i);
  done;
  let uw1, uw2 = schunk_split uw !i in
  mk_weighted uw1 (weight c - !a), mk_weighted uw2 !a *)
