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

type 'a swsek = (* a sequence of ['a weighted] elements *)
  | SWSek_Empty of 'a (* default value *)
  | SWSek_Level of  ('a swchunk) array * (* array of 2 items of type [(('a weighted) schunk) weighted] *)
                    ('a partial_swchunk) swsek * (* a sequence of weighted chunks of weighted elements *)
                    int (* weight*)

(*-----------------------------------------------------------------------------*)

let swsek_create d =
  SWSek_Empty d

let swsek_default s =
  match s with
  | SWSek_Empty d -> d
  | SWSek_Level (sides, _, _) -> swchunk_default (sides.(0))

let swsek_create_mid d =
  let mid_d = partial_swchunk_create d None in
  swsek_create mid_d

let swsek_is_empty s =
  match s with
  | SWSek_Empty _ -> true
  | SWSek_Level (sides, _, _) ->
      let front, back = view_sides Front sides in
      swchunk_is_empty front && swchunk_is_empty back

(*---------------------------------------------------------------------------*)

(** [swsek_weight s] returns the weight of the sequence s, 0 if empty. *)
let swsek_weight s =
  match s with
  | SWSek_Empty _ -> 0
  | SWSek_Level (_, _, w) -> w


(*---------------------------------------------------------------------------*)
(* Invariant: if one of the side is empty, then mid must be empty.
   Auxiliary functions*)

let mk_swsek_pov v front mid back w =
  let front', back' = view_exchange v (front, back) in
  SWSek_Level ([| front'; back' |], mid, w)

let mk_swsek_pov_weight v front mid back =
  let w = weight front + swsek_weight mid + weight back in
  mk_swsek_pov v front mid back w


(* sets mid to Empty if it is if effectively empty *)
(* let swsek_collapse s =
  match s with
  | SWSek_Empty _ -> s
  | SWSek_Level (sides, mid, w) ->
      if swsek_is_empty mid then
        match mid with
        | SWSek_Empty _ -> s
        | SWSek_Level (_, _, _) ->
            let front, back = view_sides Front sides in
            let d = swchunk_default front in
            let md = swsek_create_mid d in
            mk_swsek_pov_weight Front front md back
      else
        s *)

let swsek_collapse s =
  match s with
  | SWSek_Empty _ -> s
  | SWSek_Level (sides, mid, w) ->
      match mid with
      | SWSek_Empty _ -> s
      | SWSek_Level (mid_sides, _, _) ->
          if w = 0 then begin
            let d = swchunk_default mid_sides.(0) in
            SWSek_Level (sides, SWSek_Empty d, w)
          end else
            s


let mk_swsek_weight_collapsed v front mid back =
  let s = mk_swsek_pov_weight v front mid back in
  swsek_collapse s

(*-----------------------------------------------------------------------------*)
(* Pop, which is needed to restore the invariant *)

let rec swsek_pop : 'a. view -> owner option -> 'a swsek -> 'a swsek * 'a weighted = fun v o s ->
  match s with
  | SWSek_Empty _ -> assert false
  | SWSek_Level (sides, mid, w) -> begin
      let front, back = view_sides v sides in
      let x, front', mid', back' =
        if swchunk_is_empty front then begin (* note: assert (not (swchunk_is_empty back)) *)
          let back1, x = swchunk_pop v o back in
          x, front, mid, back1
        end else begin
          let front1, x = swchunk_pop v o front in
          if swchunk_is_empty front1 && not (swsek_is_empty mid) then
            x, front1, mid, back
          else begin
            let m1, front2 = swsek_pop v o mid in
            x, front2, m1, back
          end
        end
      in
      mk_swsek_weight_collapsed v front' mid' back', x
      (* optimized as:
      let w = s.s_weight - weight x in
      mk_swsek_pov v front' mid' back' w, x *)
    end


(*-----------------------------------------------------------------------------*)
(* Auxiliary functions for invariant, continued *)

let swsek_populate v o s =
  match s with
  | SWSek_Empty d -> s
  | SWSek_Level (sides, mid, w) -> begin
      let front, back = view_sides v sides in
      if swchunk_is_empty front then begin
        match mid with
        | SWSek_Empty _ -> s
        | SWSek_Level (_, _, _) ->
            let m1, front1 = swsek_pop v o mid in
            mk_swsek_pov v front1 m1 back w
        end else
          s
    end

let swsek_populate_both o s =
  (* Note: could take a view v as argument to decide which side to populate first *)
  let s' = swsek_populate Front o s in
  swsek_populate Back o s'

let mk_swsek_weight_invariant v o front mid back =
  let s = mk_swsek_weight_collapsed v front mid back in
  swsek_populate_both o s

(*-----------------------------------------------------------------------------*)
(* Push *)

let rec swsek_push : 'a. view -> owner option -> 'a swsek -> 'a weighted -> 'a swsek = fun v o s x ->
  match s with
  | SWSek_Empty d ->
      let empty () = swchunk_create d o in
      let partial_empty = partial_swchunk_create d o in
      let front, back = empty (), empty () in
      let front' = swchunk_push v o front x in
      mk_swsek_weight_invariant v o front' (SWSek_Empty partial_empty) back
  | SWSek_Level (sides, mid, w) -> begin
      let front, back = view_sides v sides in (* first prove with v = Front *)
      let front1, mid1 =
        if swchunk_is_full front then begin
          let d = swchunk_default front in
          let front' = swchunk_create d o in
          let mid' = swsek_push v o mid front in
          front', mid'

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
      mk_swsek_weight_invariant v o front2 mid1 back
      (* optimized as: mk_swsek_populated v o front2 mid1 back (s.s_weight + weight x) *)
    end


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
      let s1_restore = swsek_push v o s1' c1 in
      swsek_push v o s1_restore c2

let rec swsek_concat : 'a. owner option -> 'a swsek -> 'a swsek -> 'a swsek = fun o s1 s2 ->
  match s1, s2 with
  | SWSek_Empty _, _ -> s2
  | _, SWSek_Empty _ -> s1
  | SWSek_Level (sides1, mid1, _), SWSek_Level (sides2, mid2, _) ->
    let front1, back1 = view_sides Front sides1 in
    let front2, back2 = view_sides Front sides2 in

    let mb1 = swsek_absorb Back o mid1 back1 in
    let mb1f2 = swsek_absorb Back o mb1 front2 in
    let mid = swsek_concat o mb1f2 mid2 in
      
    mk_swsek_weight_invariant Front o front1 mid back2
  (* optimized as:
  let w = s1.s_weight + s2.s_weight in
  mk_swsek_populated Front o front1 mid back2 w *)

(* [swsek_split s w] returns [(s1, s2)] such that [s1 ++ s2 = s] and [s1] is
  maximal such that [weight s1 <= w] *)
let rec swsek_split : 'a. owner option -> 'a swsek -> int -> 'a swsek * 'a swsek = fun o s w ->
  match s with
  | SWSek_Empty d -> SWSek_Empty d, SWSek_Empty d
  | SWSek_Level (sides, mid, ws) -> begin
      let front, back = view_sides Front sides in
      let d = swchunk_default front in
      let empty () = swchunk_create d o in
      let mid_empty () = swsek_create_mid d in
      let wf = weight front in
      let wm = swsek_weight mid in

      let front1, mid1, back1, front2, mid2, back2 =
        if w <= wf then
          let b, f = swchunk_split o front w in
          empty (), mid_empty (), b, f, mid, back
        else begin
          let w' = w - wf in
          if w' < wm then begin
            let m1, m2 = swsek_split o mid w' in
            let m2', f2 = swsek_pop Front o m2 in (* non empty as m1.s_weight <= w - wf < wm so m2.s_weight > 0 *)
            let b, f = swchunk_split o f2 (w' - swsek_weight m1) in
            front, m1, b, f, m2', back
          end else begin
            let b, f = swchunk_split o back (w' - wm) in
            front, mid, b, f, mid_empty (), empty ()
          end
        end
      in
      let s1 = mk_swsek_weight_invariant Front o front1 mid1 back1 in
      let s2 = mk_swsek_weight_invariant Front o front2 mid2 back2 in
      s1, s2
    end
