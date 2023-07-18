open Capacity
open Weighted
open View
open Owner
open SWChunk

(* note: other solution
  type 'a swsek =
    | Empty
    | Struct of ... 
*)

type 'a swsek = { (* a sequence of ['a weighted] elements *)
  s_sides : ('a swchunk) array; (* array of 2 items of type [(('a weighted) schunk) weighted] *)
  s_mid : ('a partial_swchunk) swsek option; (* a sequence of weighted chunks of weighted elements *)
  s_weight : int
}

(*-----------------------------------------------------------------------------*)

let swsek_default s =
  swchunk_default s.s_sides.(0)

let swsek_create d oo =
  (* note: if oo = None, we could have pa0 for both sides *)
  let empty () = swchunk_create d oo in
  { s_sides = [| empty (); empty () |];
    s_mid = None;
    s_weight = 0 }

let swsek_is_empty s =
  swchunk_is_empty s.s_sides.(0) &&
  swchunk_is_empty s.s_sides.(1)

(*---------------------------------------------------------------------------*)

(** [swsek_extract_mid d mo] returns the middle sequence in the option [mo], if any,
   otherwise returns an empty middle sequence, built using the default value [d] *)
let swsek_extract_mid d oo mo =
  match mo with
  | None -> swsek_create (partial_swchunk_create d oo) oo
  | Some m -> m
  
(** [swsek_wrap_mid] takes a possibly empty middle sequence [m], and returns it
  as an option for storage in the [s_mid] record field. *)
let swsek_wrap_mid m =
  if swsek_is_empty m then
    None
  else
    Some m

(** [swsek_mid_weight mo] returns the weight of the middle sek in option [mo], if any,
  otherwise returns 0. *)
let swsek_mid_weight mo =
  match mo with
  | None -> 0
  | Some m -> m.s_weight


(*---------------------------------------------------------------------------*)
(* Invariant: if one of the side is empty, then mid must be empty.
   Auxiliary functions*)

let mk_swsek_pov v front mid back w =
  let front', back' = view_exchange v (front, back) in
  { s_sides = [| front'; back' |];
    s_mid = mid;
    s_weight = w }


let mk_swsek_pov_weight v front mid back =
  let w = weight front + swsek_mid_weight mid + weight back in
  mk_swsek_pov v front mid back w

(*-----------------------------------------------------------------------------*)
(* Pop, which is needed to restore the invariant *)

let rec swsek_pop : 'a. view -> owner option -> 'a swsek -> 'a swsek * 'a weighted = fun v o s ->
  let front, back = view_sides v s.s_sides in
  let mid = s.s_mid in

  let x, front', mid', back' =
    if swchunk_is_empty front then begin (* note: assert (not (swchunk_is_empty back)) *)
      let back1, x = swchunk_pop v o back in
      x, front, mid, back1
    end else begin
      let front1, x = swchunk_pop v o front in
      if swchunk_is_empty front1 then begin
        match mid with
        | None -> x, front1, None, back
        | Some m ->
          let m1, front2 = swsek_pop v o m in
          let m2 = swsek_wrap_mid m1 in
          x, front2, m2, back
      end else
        x, front1, mid, back
    end
  in
  mk_swsek_pov_weight v front' mid' back', x
  (* optimized as:
  let w = s.s_weight - weight x in
  mk_swsek_pov v front' mid' back' w, x *)


(*-----------------------------------------------------------------------------*)
(* Auxiliary functions for invariant, continued *)

let swsek_populate v o s =
  let front, back = view_sides v s.s_sides in
  if swchunk_is_empty front then begin
    match s.s_mid with
    | None -> s
    | Some m ->
      let m1, front1 = swsek_pop v o m in
      let m2 = swsek_wrap_mid m1 in
      mk_swsek_pov v front1 m2 back s.s_weight
  end else
    s

let swsek_populate_both o s =
  (* Note: could take a view v as argument to decide which side to populate first *)
  let s' = swsek_populate Front o s in
  swsek_populate Back o s'

let mk_swsek_populated v o front mid back w =
  let s = mk_swsek_pov v front mid back w in
  swsek_populate_both o s

let mk_swsek_weight_populated v o front mid back =
  let s = mk_swsek_pov_weight v front mid back in
  swsek_populate_both o s

(*-----------------------------------------------------------------------------*)
(* Push *)

let rec swsek_push : 'a. view -> owner option -> 'a swsek -> 'a weighted -> 'a swsek = fun v o s x ->
  let front, back = view_sides v s.s_sides in (* first prove with v = Front *)
  let mid = s.s_mid in

  let front1, mid1 =
    if swchunk_is_full front then begin
      let d = swchunk_default front in
      let front' = swchunk_create d o in
      let m = swsek_extract_mid d o mid in
      let m' = swsek_push v o m front in
      front', Some m'

      (* TODO: would it be useful to define swsek_push_into_mid v s c ? not so sure
      let m = swsek_extract_mid d s.s_mid in
      Some (swsek_push v m side)

      code dessus devient
      (swchunk_create d), (swsek_push_into_mid v s front)
      *)
    end else
      front, mid
    in
  let front2 = swchunk_push v o front1 x in
  mk_swsek_weight_populated v o front2 mid1 back
  (* optimized as: mk_swsek_populated v o front2 mid1 back (s.s_weight + weight x) *)


(* LATER
let psek_peek pov s =
  let ind = view_index pov in
  let sides = s.s_sides in
  let side = sides.(ind) in

  (if schunk_is_empty side then
    schunk_peek pov (sides.(view_index (view_swap pov)))
  else
    schunk_peek pov side).elem
*)

(*-----------------------------------------------------------------------------*)
(* Concat *)

(* push the chunk [c2] to the side of the middle sequence [s1] pointed by [v].
   If [c1] is the last chunk in the sequence [s1], we attempt to
   fuse the elements of [c2] into the back of [c1], if space allows. *)
let swsek_absorb v o s1 c2 =
  if swchunk_is_empty c2 then
    s1
  else if swsek_is_empty s1 then
    swsek_push v o s1 c2
  else
    let s1', c1 = swsek_pop v o s1 in
    if swchunk_size c1 + swchunk_size c2 <= capacity then begin
      let c12 = swchunk_concat o c1 c2 in
      swsek_push v o s1' c12
    end else
      swsek_push v o s1 c2

(** given two middle sequences and a concatenation function with wanted spec,
  returns the middle *)
let swsek_merge_middle concat o mid1 mid2 =
  match mid1, mid2 with
  | None, _ -> mid2
  | _, None -> mid1
  | Some m1, Some m2 ->
    let m2', c2 = swsek_pop Front o m2 in
    let m1' = swsek_absorb Back o m1 c2 in
    Some (concat o m1' m2')

let rec swsek_concat : 'a. owner option -> 'a swsek -> 'a swsek -> 'a swsek = fun o s1 s2 ->
  let d = swsek_default s1 in
  let front1, back1 = view_sides Front s1.s_sides in
  let front2, back2 = view_sides Front s2.s_sides in

  let m = swsek_extract_mid d o s1.s_mid in
  let mb1 = swsek_absorb Back o m back1 in
  let mb1f2 = swsek_absorb Back o mb1 front2 in
  let mid1 = swsek_wrap_mid mb1f2 in
  let mid = swsek_merge_middle swsek_concat o mid1 s2.s_mid in
    
  mk_swsek_weight_populated Front o front1 mid back2
  (* optimized as:
  let w = s1.s_weight + s2.s_weight in
  mk_swsek_populated Front o front1 mid back2 w *)

(* [swsek_split s w] returns [(s1, s2)] such that [s1 ++ s2 = s] and [s1] is
  maximal such that [weight s1 <= w] *)
let rec swsek_split : 'a. owner option -> 'a swsek -> int -> 'a swsek * 'a swsek = fun o s w ->
  let d = swsek_default s in
  let front, back = view_sides Front s.s_sides in
  let mid = s.s_mid in
  let empty () = swchunk_create d o in
  let wf = weight front in
  let wm = swsek_mid_weight mid in

  let front1, mid1, back1, front2, mid2, back2 =
    if w <= wf then
      let b, f = swchunk_split o front w in
      empty (), None, b, f, mid, back
    else begin
      let w' = w - wf in
      if w' < wm then begin
        match mid with
        | None -> assert false (* Impossible as wm > 1 *)
        | Some m ->
          let m1, m2 = swsek_split o m w' in
          let m2', f2 = swsek_pop Front o m2 in (* non empty as m1.s_weight <= w - wf < wm so m2.s_weight > 0 *)
          let b, f = swchunk_split o f2 (w' - m1.s_weight) in
          front, swsek_wrap_mid m1, b, f, swsek_wrap_mid m2', back
      end else begin
        let b, f = swchunk_split o back (w' - wm) in
        front, mid, b, f, None, empty ()
      end
    end
  in
  let s1 = mk_swsek_weight_populated Front o front1 mid1 back1 in
  let s2 = mk_swsek_weight_populated Front o front2 mid2 back2 in
  s1, s2
