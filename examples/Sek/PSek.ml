open PChunk
open Capacity
open Weighted
open View

(* rename to pwsek *)
(* later: psek/sek *)

type 'a pwchunk = 'a weighted pchunk
type 'a pwchunkw = 'a pwchunk weighted
(* 'a weighted pchunk weighted *)

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


let pwchunkw_default c =
  elem (pwchunk_default c)

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

(* let pwchunk_weight c = (* later: iter or fold *)
  let w = ref 0 in
  for i = 0 to (pchunk_size c) - 1 do
    w := !w + (pchunk_get c i).weight
  done;
  !w *)

type 'a pwsek = {
  p_sides : 'a pwchunkw array; (* array of size 2, with weights *)
  p_mid : 'a pwchunk pwsek option;
  p_weight : int
}
(* if one of the side is empty, then mid must be empty *)

(*
let psek_populate s =

see
  let[@inline] populate pov s o =
  let populate_both_nonempty_level weight front middle back o =

*)

let pwsek_default s =
  pwchunkw_default s.p_sides.(0)

let pwsek_create d =
  let pa0 = pwchunkw_create d in {
    p_sides = [| pa0; pa0 |];
    p_mid = None;
    p_weight = 0 }

let mk_pwsek_pov v front mid back w =
  let front', back' = view_exchange v (front, back) in {
    p_sides = [| front'; back' |];
    p_mid = mid;
    p_weight = w }

let pwsek_is_empty s =
  pwchunk_is_empty s.p_sides.(0) && pwchunk_is_empty s.p_sides.(1)

let pwsek_get_mid mo d =
  match mo with
  | None -> pwsek_create (pwchunk_create d)
  | Some m -> m

let pwsek_mk_mid m =
  if pwsek_is_empty m then
    None
  else
    Some m
  

let rec pwsek_pop : 'a. view -> 'a pwsek -> 'a pwsek * 'a weighted = fun v s ->
  let vi = view_index v in
  let vj = view_index (view_swap v) in
  let sides = s.p_sides in
  let sd = sides.(vi) in
  let othersd = sides.(vj) in

  if pwchunk_is_empty sd then begin
    let othersd1, x = pwchunkw_pop v othersd in
    let w = s.p_weight - weight x in
    mk_pwsek_pov v sd None othersd1 w, x
  end else begin
    let sd1, x = pwchunkw_pop v sd in
    let w = s.p_weight - weight x in

    let mid = s.p_mid in
    let s1 =
      if pwchunk_is_empty sd1 then begin
        match mid with
        | None -> mk_pwsek_pov v sd1 None othersd w
        | Some m ->
          let m1, sd2 = pwsek_pop v m in
          let m2 = pwsek_mk_mid m1 in
          mk_pwsek_pov v sd2 m2 othersd w
      end else
        mk_pwsek_pov v sd1 mid othersd w
    in s1, x
  end

let pwsek_populate v s =
  let vi = view_index v in
  let vj = view_index (view_swap v) in
  let sides = s.p_sides in
  let sd = sides.(vi) in
  let othersd = sides.(vj) in

  if pwchunk_is_empty sd then begin
    match s.p_mid with
    | None -> s
    | Some m ->
      let m1, sd1 = pwsek_pop v m in
      let m2 = pwsek_mk_mid m1 in
      mk_pwsek_pov v sd1 m2 othersd s.p_weight
  end else
    s

let pwsek_populate_both s =
  let s' = pwsek_populate Front s in
  pwsek_populate Back s'

let rec pwsek_push : 'a. view -> 'a pwsek -> 'a weighted -> 'a pwsek = fun v s x ->
  let vi = view_index v in
  let d = pwsek_default s in
  let sides = s.p_sides in
  let side = sides.(vi) in

  let sd, mid =
    if pwchunk_is_full side then begin
      pwchunkw_create d,
      let m = pwsek_get_mid s.p_mid d in
      Some (pwsek_push v m side)
    end else
      side, s.p_mid
  in
  let sd' = pwchunkw_push v sd x in
  
  let vj = view_index (view_swap v) in
  let othersd = sides.(vj) in
  let s' = mk_pwsek_pov v sd' mid othersd (s.p_weight + weight x) in
  pwsek_populate (view_swap v) s'

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

let pwsek_absorb s1 c2 =
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

  let vf = view_index Front in
  let vb = view_index Back in
  let sides1 = s1.p_sides in
  let front1 = sides1.(vf) in
  let back1 = sides1.(vb) in
  let sides2 = s2.p_sides in
  let front2 = sides2.(vf) in
  let back2 = sides2.(vb) in

  let m = pwsek_get_mid s1.p_mid d in
  let mb1 = pwsek_absorb m back1 in
  let mb1f2 = pwsek_absorb mb1 front2 in
  let mid1 = pwsek_mk_mid mb1f2 in
  let mid2 = s2.p_mid in

  let mid = (* use psek_get_mid *) (* todo: if mid2 not empty, pop its front, and absorb it as well *)
    match mid1, mid2 with
    | None, _ -> mid2
    | _, None -> mid1
    | Some m1, Some m2 ->
      let m2', c2 = pwsek_pop Front m2 in
      let m1' = pwsek_absorb m1 c2 in
      Some (pwsek_concat m1' m2')
  in
  let s12 = mk_pwsek_pov Front front1 mid back2 (s1.p_weight + s2.p_weight) in
  pwsek_populate_both s12

(* LATER *)
let rec psek_split : 'a. 'a pwsek -> int -> 'a pwsek * 'a pwsek = fun s ->
  assert false


(* psek *)

let psek_push pov s x =
  pwsek_push pov s (mk_weighted x 1)
