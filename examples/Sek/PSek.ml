open PChunk
open Capacity
open Weighted
open View

type 'a pwchunk = 'a weighted pchunk

let pwchunk_default c =
  (pchunk_default c).elem

let pwchunk_create d =
  pchunk_create (dummy_weighted d)

let pwchunk_weight c =
  let w = ref 0 in
  for i = 0 to (pchunk_size c) - 1 do
    w := !w + (pchunk_get c i).weight
  done;
  !w


type 'a psek = {
  p_sides : 'a pwchunk array;
  p_mid : 'a pwchunk psek option;
  p_weight : int
}
(* On veut un invariant "Si mid non vide alors front et back non vides" *)

let psek_default s =
  pwchunk_default s.p_sides.(0)

let psek_create d = {
  p_sides = [| pwchunk_create d; pwchunk_create d |];
  p_mid = None;
  p_weight = 0
}

let rec psek_is_empty : 'a. 'a psek -> bool = fun s ->
  pchunk_is_empty s.p_sides.(0) && pchunk_is_empty s.p_sides.(1)

let psek_peek pov s =
  let ind = view_index pov in
  let sides = s.p_sides in
  let side = sides.(ind) in

  (if pchunk_is_empty side then
    pchunk_peek pov (sides.(view_index (view_swap pov)))
  else
    pchunk_peek pov side).elem

let rec psek_pop : 'a. view -> 'a psek -> 'a psek * 'a = fun pov s ->
  let ind = view_index pov in
  let w = s.p_weight in
  let sides = [| s.p_sides.(0); s.p_sides.(1) |] in

  if pchunk_is_empty sides.(ind) then begin
    let jnd = view_index (view_swap pov) in
    let c, x = pchunk_pop pov sides.(jnd) in
    sides.(jnd) <- c;
    { p_sides = sides; p_mid = None; p_weight = w - x.weight }, x.elem
  end else begin
    let c, x = pchunk_pop pov sides.(ind) in
    let s' =
      if pchunk_is_empty c then begin
        match s.p_mid with
        | None ->
          sides.(ind) <- c;
          { p_sides = sides; p_mid = None; p_weight = w - x.weight }
        | Some m ->
          let m', c' = psek_pop pov m in
          sides.(ind) <- c';
          { p_sides = sides; p_mid = (if psek_is_empty m' then None else Some m'); p_weight = w - x.weight }
      end else begin
        sides.(ind) <- c;
        { p_sides = sides; p_mid = s.p_mid; p_weight = w - x.weight }
      end
    in
    s', x.elem
  end

let rec psek_weighted_push : 'a. view -> 'a psek -> 'a -> int -> 'a psek = fun pov s x w ->
  let ind = view_index pov in
  let default = psek_default s in
  let sides = [| s.p_sides.(0); s.p_sides.(1) |] in
  let side = sides.(ind) in

  let mid =
    if pchunk_is_full side then begin
      sides.(ind) <- pwchunk_create default;
      Some (psek_weighted_push pov (
        match s.p_mid with
        | None -> psek_create (pwchunk_create default)
        | Some m -> m
      ) side (pwchunk_weight side))
    end else s.p_mid
  in
  sides.(ind) <- pchunk_push pov sides.(ind) (mk_weighted x w);
  { p_sides = sides; p_mid = mid; p_weight = s.p_weight + w }

let psek_push pov s x = psek_weighted_push pov s x 1

let psek_absorb s c =
  if psek_is_empty s then
    psek_push Back s c
  else
    let s', c' = psek_pop Back s in
    if pchunk_size c' + pchunk_size c <= capacity then
      psek_push Back s' (pchunk_concat c' c)
    else
      psek_push Back s c

let rec psek_concat : 'a. 'a psek -> 'a psek -> 'a psek = fun s s' ->
  let indf = view_index Front in
  let indb = view_index Back in

  let default = psek_default s in
  let sfront = s.p_sides.(indf) in
  let sback = s.p_sides.(indb) in
  let s'front = s.p_sides.(indf) in
  let s'back = s.p_sides.(indb) in
  
  let absorbed =
    match s.p_mid with
    | None ->
        if pchunk_is_empty sback && pchunk_is_empty s'front then None
        else Some (psek_absorb (psek_absorb (psek_create (pwchunk_create default)) sback) s'front)
    | Some m -> Some (psek_absorb (psek_absorb m sback) s'front)
  in
  let mid =
    match absorbed, s'.p_mid with
    | None, _ -> s'.p_mid
    | _, None -> absorbed
    | Some m, Some m' -> Some (psek_concat m m')
  in
  { p_sides = [| sfront; s'back |]; p_mid = mid; p_weight = s.p_weight + s'.p_weight }

let rec psek_split : 'a. 'a psek -> int -> 'a psek * 'a psek = fun s ->
  assert false
