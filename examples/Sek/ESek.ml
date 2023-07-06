open Capacity
open Weighted
open View
open Owner
open EChunk
open SChunk
open SWChunk
open SWSek

(* ideally, we want to have 'a instead of 'a weighted as all weights are 1 *)

type 'a esek = {
  sides : (('a weighted) echunk) array; (* weights are all 1, of size 2 *)
  buffers : (('a weighted) echunk) array; (* one for each side, a buffer is either empty or full *)
  mutable mid : ('a partial_swchunk) swsek option;
  id : owner }

(*-----------------------------------------------------------------------------*)
(* Utility fonctions to add weights of 1. Get rid of it somehow? *)

let ewchunk_create d =
  echunk_create (dummy_weighted d)

let swchunk_of_ewchunk o ec =
  mk_weighted (schunk_of_echunk o ec) (echunk_size ec)

let ewchunk_of_swchunk o sc =
  echunk_of_schunk o (unweighted sc)


(*-----------------------------------------------------------------------------*)

let esek_default s =
  unweighted (echunk_default s.sides.(0))

let esek_create_with id d =
  let empty () = ewchunk_create d in
  { sides = [| empty (); empty () |];
    buffers = [| empty (); empty () |];
    mid = None;
    id = id }

let esek_create d =
  esek_create_with (fresh_id ()) d

let esek_is_empty s =
  echunk_is_empty s.sides.(0) &&
  echunk_is_empty s.sides.(1)


(*---------------------------------------------------------------------------*)
(* Invariant: if one of the side is empty, then both buffers and mid must be empty.
  Auxiliary functions *)

let esek_populate v s =
  let fi = view_index v in
  let sides = s.sides in
  let buffers = s.buffers in
  let front = sides.(fi) in
  let fb = buffers.(fi) in

  if echunk_is_empty front then begin
    if echunk_is_empty fb then begin
      match s.mid with
      | None ->
          let bi = view_index (view_swap v) in
          let bb = buffers.(bi) in
          if echunk_is_full bb then begin
            sides.(fi) <- bb;
            buffers.(bi) <- front
          end
      | Some m ->
        let id = s.id in
        let m1, front1 = swsek_pop v (Some id) m in
        let m2 = swsek_wrap_mid m1 in
        let front2 = ewchunk_of_swchunk id front1 in
        sides.(fi) <- front2;
        s.mid <- m2
    end else begin
      sides.(fi) <- fb;
      buffers.(fi) <- front
    end
  end

let esek_populate_both s =
  (* Note: could take a view v as argument to decide which side to populate first *)
  esek_populate Front s;
  esek_populate Back s

(*-----------------------------------------------------------------------------*)
(* Pop *)

let esek_pop v s =
  let fi = view_index v in
  let sides = s.sides in
  let front = sides.(fi) in
  let x =
    if echunk_is_empty front then begin
      let bi = view_index (view_swap v) in
      echunk_pop v sides.(bi)
    end else
      echunk_pop v front
  in
  esek_populate v s;
  unweighted x

(*-----------------------------------------------------------------------------*)
(* Push *)

let esek_push_into_mid v s c =
  let d = esek_default s in
  let id = s.id in
  let o = Some id in
  let m = swsek_extract_mid d o s.mid in
  let c' = swchunk_of_ewchunk id c in
  let m' = swsek_push v o m c' in
  s.mid <- Some m'

let rec esek_push v s x =
  let d = esek_default s in
  let fi = view_index v in
  let sides = s.sides in
  let buffers = s.buffers in
  let front = sides.(fi) in
  let fb = buffers.(fi) in

  if echunk_is_full front then begin
    if echunk_is_full fb then begin
      esek_push_into_mid v s fb
    end;
    buffers.(fi) <- front;
    sides.(fi) <- ewchunk_create d
  end;
  echunk_push v front (mk_weighted x 1);
  esek_populate_both s

(*-----------------------------------------------------------------------------*)
(* Concat *)

(** [mk_esek_pov v front mid back id]
  makes an esek with the specified fields and empty buffers (normal form). *)
let mk_esek_pov v front mid back id =
  let d = echunk_default front in
  let front', back' = view_exchange v (front, back) in
  { sides = [| front'; back' |];
    buffers = [| echunk_create d; echunk_create d |];
    mid = mid;
    id = id }


(** [mk_esek_populated v front mid back id]
  same as before but ensures invariants hold. *)
let mk_esek_populated v front mid back id =
  let s = mk_esek_pov v front mid back id in
  esek_populate_both s;
  s


(** [esek_absorb_buffer v s]
  utility function for adding a buffer to the middle. *)
let esek_absorb_buffer v s =
  let d = esek_default s in
  let fi = view_index v in
  let buffers = s.buffers in
  let fb = buffers.(fi) in
  if echunk_is_full fb then begin
    esek_push_into_mid Front s fb;
    buffers.(fi) <- ewchunk_create d
  end

(** [esek_normalize s]
  eliminates buffers. *)
let esek_normalize s =
  esek_absorb_buffer Front s;
  esek_absorb_buffer Back s

(* push the chunk [c2] to the side of the middle sequence [s1] pointed by [v].
   If [c1] is the last chunk in the sequence [s1], we attempt to
   fuse the elements of [c2] into the back of [c1], if space allows. *)
let rec esek_concat s1 s2 =
  esek_normalize s1;
  esek_normalize s2;
  let d = esek_default s1 in
  let front1, back1 = view_sides Front s1.sides in
  let front2, back2 = view_sides Front s2.sides in

  let id = s1.id in
  let o = Some id in
  let m = swsek_extract_mid d o s1.mid in
  let mb1 = swsek_absorb Back o m (swchunk_of_ewchunk id back1) in
  let mb1f2 = swsek_absorb Back o mb1 (swchunk_of_ewchunk id front2) in
  let mid1 = swsek_wrap_mid mb1f2 in
  let mid = swsek_merge_middle swsek_concat o mid1 s2.mid in
  mk_esek_populated Front front1 mid back2 id

(* [esek_split s i] returns [(s1, s2)] such that [s1 ++ s2 = s] and [s1] has i elements *)
let esek_split s i =
  esek_normalize s;
  let d = esek_default s in
  let empty () = ewchunk_create d in
  let front, back = view_sides Front s.sides in
  let mid = s.mid in
  
  let id = s.id in
  let o = Some id in
  let wf = echunk_size front in
  let wm = swsek_mid_weight s.mid in

  let front1, mid1, back1, front2, mid2, back2 =
    if i <= wf then
      let b, f = echunk_split front i in
      empty (), None, b, f, mid, back
    else begin
      let i' = i - wf in
      if i' < wm then begin
        match mid with
        | None -> assert false (* Impossible as wm > 1 *)
        | Some m ->
          let m1, m2 = swsek_split o m i' in
          let m2', f2 = swsek_pop Front o m2 in (* non empty as m1.p_weight <= w - wf < wm so m2.p_weight > 0 *)
          let f2' = ewchunk_of_swchunk id f2 in
          let b, f = echunk_split f2' (i' - m1.p_weight) in
          front, swsek_wrap_mid m1, b, f, swsek_wrap_mid m2', back
      end else begin
        let b, f = echunk_split back (i' - wm) in
        front, mid, b, f, None, empty ()
      end
    end
  in
  let s1 = mk_esek_populated Front front1 mid1 back1 id in
  let s2 = mk_esek_populated Front front2 mid2 back2 id in
  s1, s2


(*---------------------------------------------------------------------------*)

(* Conversions *)

