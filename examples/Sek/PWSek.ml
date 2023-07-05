open Capacity
open Weighted
open View
open Owner
open SWChunk

type 'a pwsek = { (* a sequence of ['a weighted] elements *)
  p_sides : ('a swchunk) array; (* array of 2 items of type [(('a weighted) schunk) weighted] *)
  p_mid : ('a partial_swchunk) pwsek option; (* a sequence of weighted chunks of weighted elements *)
  p_weight : int
}

(*-----------------------------------------------------------------------------*)

let pwsek_default s =
  swchunk_default s.p_sides.(0)

let pwsek_create d oo =
  (* note: if oo = None, we could have pa0 for both sides *)
  let empty () = swchunk_create d oo in
  { p_sides = [| empty (); empty () |];
    p_mid = None;
    p_weight = 0 }

let pwsek_is_empty s =
  swchunk_is_empty s.p_sides.(0) &&
  swchunk_is_empty s.p_sides.(1)

(*---------------------------------------------------------------------------*)

(** [pwsek_extract_mid d mo] returns the middle sequence in the option [mo], if any,
   otherwise returns an empty middle sequence, built using the default value [d] *)
let pwsek_extract_mid d oo mo =
  match mo with
  | None -> pwsek_create (partial_swchunk_create d oo) oo
  | Some m -> m
  
(** [pwsek_wrap_mid] takes a possibly empty middle sequence [m], and returns it
  as an option for storage in the [p_mid] record field. *)
let pwsek_wrap_mid m =
  if pwsek_is_empty m then
    None
  else
    Some m

(** [pwsek_mid_weight mo] returns the weight of the middle sek in option [mo], if any,
  otherwise returns 0. *)
let pwsek_mid_weight mo =
  match mo with
  | None -> 0
  | Some m -> m.p_weight


(*---------------------------------------------------------------------------*)
(* Invariant: if one of the side is empty, then mid must be empty.
   Auxiliary functions*)

let mk_pwsek_pov v front mid back w =
  let front', back' = view_exchange v (front, back) in
  { p_sides = [| front'; back' |];
    p_mid = mid;
    p_weight = w }


let mk_pwsek_pov_weight v front mid back =
  let w = weight front + pwsek_mid_weight mid + weight back in
  mk_pwsek_pov v front mid back w

(*-----------------------------------------------------------------------------*)
(* Pop, which is needed to restore the invariant *)

let rec pwsek_pop : 'a. view -> owner option -> 'a pwsek -> 'a pwsek * 'a weighted = fun v o s ->
  let front, back = view_sides v s.p_sides in
  let mid = s.p_mid in

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
          let m1, front2 = pwsek_pop v o m in
          let m2 = pwsek_wrap_mid m1 in
          x, front2, m2, back
      end else
        x, front1, mid, back
    end
  in
  mk_pwsek_pov_weight v front' mid' back', x
  (* optimized as:
  let w = s.p_weight - weight x in
  mk_pwsek_pov v front' mid' back' w, x *)


(*-----------------------------------------------------------------------------*)
(* Auxiliary functions for invariant, continued *)

let pwsek_populate v o s =
  let front, back = view_sides v s.p_sides in
  if swchunk_is_empty front then begin
    match s.p_mid with
    | None -> s
    | Some m ->
      let m1, front1 = pwsek_pop v o m in
      let m2 = pwsek_wrap_mid m1 in
      mk_pwsek_pov v front1 m2 back s.p_weight
  end else
    s

let pwsek_populate_both o s =
  (* Note: could take a view v as argument to decide which side to populate first *)
  let s' = pwsek_populate Front o s in
  pwsek_populate Back o s'

let mk_pwsek_populated v o front mid back w =
  let s = mk_pwsek_pov v front mid back w in
  pwsek_populate_both o s

let mk_pwsek_weight_populated v o front mid back =
  let s = mk_pwsek_pov_weight v front mid back in
  pwsek_populate_both o s

(*-----------------------------------------------------------------------------*)
(* Push *)

let rec pwsek_push : 'a. view -> owner option -> 'a pwsek -> 'a weighted -> 'a pwsek = fun v o s x ->
  let d = pwsek_default s in
  let front, back = view_sides v s.p_sides in
  let mid = s.p_mid in

  let front1, mid1 =
    if swchunk_is_full front then begin
      let front' = swchunk_create d o in
      let m = pwsek_extract_mid d o mid in
      front', Some (pwsek_push v o m front)

      (* TODO: would it be useful to define pwsek_push_into_mid v s c ? not so sure
      let m = pwsek_extract_mid d s.p_mid in
      Some (pwsek_push v m side)

      code dessus devient
      (swchunk_create d), (pwsek_push_into_mid v s front)
      *)
    end else
      front, mid
    in
  let front2 = swchunk_push v o front1 x in
  mk_pwsek_weight_populated v o front2 mid1 back
  (* optimized as: mk_pwsek_populated v o front2 mid1 back (s.p_weight + weight x) *)


(* LATER
let psek_peek pov s =
  let ind = view_index pov in
  let sides = s.p_sides in
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
let pwsek_absorb v o s1 c2 =
  if swchunk_is_empty c2 then
    s1
  else if pwsek_is_empty s1 then
    pwsek_push v o s1 c2
  else
    let s1', c1 = pwsek_pop v o s1 in
    if swchunk_size c1 + swchunk_size c2 <= capacity then begin
      let c12 = swchunk_concat o c1 c2 in
      pwsek_push v o s1' c12
    end else
      pwsek_push v o s1 c2

(** given two middle sequences and a concatenation function with wanted spec,
  returns the middle *)
let pwsek_merge_middle concat o mid1 mid2 =
  match mid1, mid2 with
  | None, _ -> mid2
  | _, None -> mid1
  | Some m1, Some m2 ->
    let m2', c2 = pwsek_pop Front o m2 in
    let m1' = pwsek_absorb Back o m1 c2 in
    Some (concat o m1' m2')

let rec pwsek_concat : 'a. owner option -> 'a pwsek -> 'a pwsek -> 'a pwsek = fun o s1 s2 ->
  let d = pwsek_default s1 in
  let front1, back1 = view_sides Front s1.p_sides in
  let front2, back2 = view_sides Front s2.p_sides in

  let m = pwsek_extract_mid d o s1.p_mid in
  let mb1 = pwsek_absorb Back o m back1 in
  let mb1f2 = pwsek_absorb Back o mb1 front2 in
  let mid1 = pwsek_wrap_mid mb1f2 in
  let mid = pwsek_merge_middle pwsek_concat o mid1 s2.p_mid in
    
  mk_pwsek_weight_populated Front o front1 mid back2
  (* optimized as:
  let w = s1.p_weight + s2.p_weight in
  mk_pwsek_populated Front o front1 mid back2 w *)

(* [pwsek_split s w] returns [(s1, s2)] such that [s1 ++ s2 = s] and [s1] is
  maximal such that [weight s1 <= w] *)
let rec pwsek_split : 'a. owner option -> 'a pwsek -> int -> 'a pwsek * 'a pwsek = fun o s w ->
  let d = pwsek_default s in
  let front, back = view_sides Front s.p_sides in
  let mid = s.p_mid in
  let empty () = swchunk_create d o in
  let wf = weight front in
  let wm = pwsek_mid_weight mid in

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
          let m1, m2 = pwsek_split o m w' in
          let m2', f2 = pwsek_pop Front o m2 in (* non empty as m1.p_weight <= w - wf < wm so m2.p_weight > 0 *)
          let b, f = swchunk_split o f2 (w' - m1.p_weight) in
          front, pwsek_wrap_mid m1, b, f, pwsek_wrap_mid m2', back
      end else begin
        let b, f = swchunk_split o back (w' - wm) in
        front, mid, b, f, None, empty ()
      end
    end
  in
  let s1 = mk_pwsek_weight_populated Front o front1 mid1 back1 in
  let s2 = mk_pwsek_weight_populated Front o front2 mid2 back2 in
  s1, s2
