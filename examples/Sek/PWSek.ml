open PChunk
open Capacity
open Weighted
open View

(*-----------------------------------------------------------------------------*)

type 'a pwchunk = 'a weighted pchunk

let pwchunk_default c =
  pchunk_default (elem c)

let pwchunk_create d =
  pchunk_create (dummy_weighted d)

let pwchunk_is_empty c =
  pchunk_is_empty (elem c)

let pwchunk_is_full c =
  pchunk_is_full (elem c)

let pwchunk_size c =
  pchunk_size (elem c)

(*-----------------------------------------------------------------------------*)

type 'a pwchunkw = 'a pwchunk weighted

let pwchunkw_default c =
  elem (pwchunk_default c) (* TODO elem -> unweight *)

let pwchunkw_create d =
  dummy_weighted (pwchunk_create d)

let pwchunkw_push v c x =
  let el = pchunk_push v (elem c) x in
  mk_weighted el (weight c + weight x)

let pwchunkw_pop v c =
  let el, x = pchunk_pop v (elem c) in
  mk_weighted el (weight c - weight x), x

let pwchunkw_concat c0 c1 =
  let el = pchunk_concat (elem c0) (elem c1) in
  mk_weighted el (weight c0 + weight c1)

(* [pwchunkw_split c w] returns [(c1, c2)] such that [c1 ++ c2 = c] and [c1] is
  maximal such that [weight c1 <= w] *)
let pwchunkw_split c w =
  let uw = elem c in
  let b = weight c - w in
  let i, a = ref (pchunk_size uw), ref 0 in
  while !i > 0 && !a < b do
    decr i;
    a := !a + weight (pchunk_get uw !i);
  done;
  let uw1, uw2 = pchunk_split uw !i in
  mk_weighted uw1 !a, mk_weighted uw2 (weight c - !a)

(*-----------------------------------------------------------------------------*)

type 'a pwsek = { (* a sequence of ['a weighted] elements *)
  p_sides : 'a pwchunkw array; (* array of 2 items of type [(('a weighted) pchunk) weighted] *)
  p_mid : 'a pwchunk pwsek option; (* a sequence of weighted chunks of weighted elements *)
  p_weight : int
}

(*-----------------------------------------------------------------------------*)


(*
let psek_populate s =

see
  let[@inline] populate pov s o =
  let populate_both_nonempty_level weight front middle back o =

*)

let pwsek_default s =
  pwchunkw_default s.p_sides.(0)

let pwsek_create d =
  let pa0 = pwchunkw_create d in
  { p_sides = [| pa0; pa0 |];
    p_mid = None;
    p_weight = 0 }

let pwsek_is_empty s =
     pwchunk_is_empty s.p_sides.(0)
  && pwchunk_is_empty s.p_sides.(1)

(* [pwsek_get_mid d mo] returns the middle sequence in the option [mo], if any,
   otherwise returns an empty middle sequence, built using the default value [d] *)
let pwsek_get_mid d mo =
  match mo with
  | None -> pwsek_create (pwchunk_create d)
  | Some m -> m

let pwsek_mid_weight mo =
  match mo with
  | None -> 0
  | Some m -> m.p_weight

(*-----------------------------------------------------------------------------*)
(* Invariant: if one of the side is empty, then mid must be empty.
   Auxiliary functions*)

(* [pwsek_mk_mid] takes a possibly empty middle sequence [m], and returns it
   as an option for storage in the [p_mid] record field. *)
let pwsek_mk_mid m =
  if pwsek_is_empty m then
    None
  else
    Some m

let mk_pwsek_pov v front mid back w =
  let front', back' = view_exchange v (front, back) in
  { p_sides = [| front'; back' |];
    p_mid = mid;
    p_weight = w }

(*-----------------------------------------------------------------------------*)
(* Pop, which is needed to restore the invariant *)

let rec pwsek_pop : 'a. view -> 'a pwsek -> 'a pwsek * 'a weighted = fun v s ->
  let front, back = view_sides v s.p_sides in
  let mid = s.p_mid in

  let x, front', mid', back' =
    if pwchunk_is_empty front then begin
      let back1, x = pwchunkw_pop v back in
      x, front, mid, back1
    end else begin
      let front1, x = pwchunkw_pop v front in
      if pwchunk_is_empty front1 then begin
        match mid with
        | None -> x, front1, None, back
        | Some m ->
          let m1, front2 = pwsek_pop v m in
          let m2 = pwsek_mk_mid m1 in
          x, front2, m2, back
      end else
        x, front1, mid, back
    end
  in
  let w = s.p_weight - weight x in
  mk_pwsek_pov v front' mid' back' w, x

(*-----------------------------------------------------------------------------*)
(* Auxiliary functions for invariant, continued *)

let pwsek_populate v s =
  let front, back = view_sides v s.p_sides in
  if pwchunk_is_empty front then begin
    match s.p_mid with
    | None -> s
    | Some m ->
      let m1, front1 = pwsek_pop v m in
      let m2 = pwsek_mk_mid m1 in
      mk_pwsek_pov v front m2 back s.p_weight
  end else
    s

let pwsek_populate_both s =
  (* Note: could take a view v as argument to decide which side to populate first *)
  let s' = pwsek_populate Front s in
  pwsek_populate Back s'

let mk_pwsek_populated v front mid back w =
  let s = mk_pwsek_pov v front mid back w in
  pwsek_populate_both s

(*-----------------------------------------------------------------------------*)
(* Push *)

let rec pwsek_push : 'a. view -> 'a pwsek -> 'a weighted -> 'a pwsek = fun v s x ->
  let d = pwsek_default s in
  let front, back = view_sides v s.p_sides in
  let mid = s.p_mid in

  let front1, mid1 =
    if pwchunk_is_full front then begin
      let front' = pwchunkw_create d in
      let m = pwsek_get_mid d mid in
      front', Some (pwsek_push v m front)

      (* TODO: would it be useful to define pwsek_push_into_mid v s c ? not so sure
      let m = pwsek_get_mid d s.p_mid in
      Some (pwsek_push v m side)

      code dessus devient
      (pwchunkw_create d), (pwsek_push_into_mid v s front)
      *)
    end else
      front, mid
    in
  let front2 = pwchunkw_push v front1 x in
  mk_pwsek_populated v front2 mid1 back (s.p_weight + weight x)


(* LATER
let psek_peek pov s =
  let ind = view_index pov in
  let sides = s.p_sides in
  let side = sides.(ind) in

  (if pchunk_is_empty side then
    pchunk_peek pov (sides.(view_index (view_swap pov)))
  else
    pchunk_peek pov side).elem
*)

(*-----------------------------------------------------------------------------*)
(* Concat *)

(* push the chunk [c2] to the back of the middle sequence [s1].
   If [c1] is the last chunk in the sequence [s1], we attempt to
   fuse the elements of [c2] into the back of [c1], if space allows. *)
let pwsek_absorb_back s1 c2 =
  if pwchunk_is_empty c2 then
    s1
  else if pwsek_is_empty s1 then
    pwsek_push Back s1 c2
  else
    let s1', c1 = pwsek_pop Back s1 in
    if pwchunk_size c1 + pwchunk_size c2 <= capacity then begin
      let c12 = pwchunkw_concat c1 c2 in
      pwsek_push Back s1' c12
    end else
      pwsek_push Back s1 c2

let rec pwsek_concat : 'a. 'a pwsek -> 'a pwsek -> 'a pwsek = fun s1 s2 ->
  let d = pwsek_default s1 in
  let front1, back1 = view_sides Front s1.p_sides in
  let front2, back2 = view_sides Front s2.p_sides in

  let m = pwsek_get_mid d s1.p_mid in
  let mb1 = pwsek_absorb_back m back1 in
  let mb1f2 = pwsek_absorb_back mb1 front2 in
  let mid1 = pwsek_mk_mid mb1f2 in
  let mid2 = s2.p_mid in

  let mid =
    match mid1, mid2 with
    | None, _ -> mid2
    | _, None -> mid1
    | Some m1, Some m2 ->
      let m2', c2 = pwsek_pop Front m2 in
      let m1' = pwsek_absorb_back m1 c2 in
      Some (pwsek_concat m1' m2')
    in
  let w = s1.p_weight + s2.p_weight in
  mk_pwsek_populated Front front1 mid back2 w

(* [pwsek_split s w] returns [(s1, s2)] such that [s1 ++ s2 = s] and [s1] is
  maximal such that [weight s1 <= w] *)
let rec pwsek_split : 'a. 'a pwsek -> int -> 'a pwsek * 'a pwsek = fun s w ->
  let d = pwsek_default s in
  let front, back = view_sides Front s.p_sides in
  let mid = s.p_mid in
  let empty = pwchunkw_create d in
  let wf = weight front in
  let wm = pwsek_mid_weight mid in

  let front1, mid1, back1, front2, mid2, back2 =
    if w <= wf then
      let b, f = pwchunkw_split front w in
      empty, None, b, f, mid, back
    else if w - wf < wm then
      match mid with
      | None -> assert false (* Impossible as wm > 1 *)
      | Some m ->
        let m1, m2 = pwsek_split m (w - wf) in
        let m2', f2 = pwsek_pop Front m in (* non empty as m1.p_weight <= w - wf < wm so m2.p_weight > 0 *)
        let b, f = pwchunkw_split f2 (w - m1.p_weight) in
        front, pwsek_mk_mid m1, b, f, pwsek_mk_mid m2', back
    else
      let b, f = pwchunkw_split back (w - wf - wm) in
      front, mid, b, f, None, empty
  in
  let w1 = weight front1 + (pwsek_mid_weight mid1) + weight back1 in
  let w2 = weight front2 + (pwsek_mid_weight mid2) + weight back2 in
  mk_pwsek_populated Front front1 mid1 back1 w1, mk_pwsek_populated Front front2 mid2 back2 w2
