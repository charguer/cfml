open PChunk
open Capacity
open Weighted
open View

(* rename to pwsek *)
(* later: psek/sek *)

type 'a pwchunk = 'a weighted pchunk
(* 'a weighted pchunk weighted *)

let pwchunk_default c =
  (pchunk_default c).elem

let pwchunk_create d =
  pchunk_create (dummy_weighted d)

let pwchunk_weight c = (* later: iter or fold *)
  let w = ref 0 in
  for i = 0 to (pchunk_size c) - 1 do
    w := !w + (pchunk_get c i).weight
  done;
  !w

type 'a psek = {
  p_sides : 'a pwchunk array; (* array of size 2 *)
  p_mid : 'a pwchunk psek option;
  p_weight : int
}
(* if one of the side is empty, then mid must be empty *)

(*
let psek_populate s =

see
  let[@inline] populate pov s o =
  let populate_both_nonempty_level weight front middle back o =

*)

let psek_default s =
  pwchunk_default s.p_sides.(0)

let psek_create d = {
  let pa0 = pwchunk_create d in
  p_sides = [| pa0; pa0 |];
  p_mid = None;
  p_weight = 0 }

let psek_is_empty s =
  pchunk_is_empty s.p_sides.(0) && pchunk_is_empty s.p_sides.(1)

(* pwsek_push : 'a. view -> 'a psek -> 'a weighted -> 'a psek = fun v s x -> *)
let rec psek_weighted_push : 'a. view -> 'a psek -> 'a -> int -> 'a psek = fun pov s x w ->
  let ind = view_index pov in (* ind -> vi *)
  let default = psek_default s in (* default -> d *)
  let sides = [| s.p_sides.(0); s.p_sides.(1) |] in (* Array.copy s_psides *)
  let side = sides.(ind) in
  (* let side, mid =
        ...
     mkseq_onesided pov side mid (s.p_weight + weight x) *)
  let mid =
    if pchunk_is_full side then begin
      sides.(ind) <- pwchunk_create default;
      (* let mid = psek_get_mid d s.p_mid in
         Some (psek_weighted_push pov mid side) *)
      Some (psek_weighted_push pov (
        match s.p_mid with
        | None -> psek_create (pwchunk_create default)
        | Some m -> m
      ) side (pwchunk_weight side))
    end else s.p_mid
  in
  sides.(ind) <- pchunk_push pov sides.(ind) (mk_weighted x w);
  (* populate *) { p_sides = sides;
    p_mid = mid;
    p_weight = s.p_weight + w }
(* todo
  sides.(ind) <- pchunk_push pov sides.(ind) x;
  { p_sides = sides; p_mid = mid; p_weight = s.p_weight + weight x }
*)

let rec psek_pop : 'a. view -> 'a psek -> 'a psek * 'a = fun pov s ->
  let ind = view_index pov in
  let w = s.p_weight in
  let sides = [| s.p_sides.(0); s.p_sides.(1) |] in

  if pchunk_is_empty sides.(ind) then begin
    let jnd = view_index (view_swap pov) in
    let c, x = pchunk_pop pov sides.(jnd) in
    sides.(jnd) <- c;
    (* mkseq_onesided (swap pov) *)
    { p_sides = sides; p_mid = None; p_weight = w - x.weight }, x.elem
  end else begin
    let c, x = pchunk_pop pov sides.(ind) in (* c -> side *)
    (* call mksed_onesided c *)
      replace all with populate *)
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

let psek_absorb s c = (* c1, c2, c12 *)
  if psek_is_empty s then
    psek_push Back s c
  else
    let s', c' = psek_pop Back s in
    if pchunk_size c' + pchunk_size c <= capacity then begin
      let c'' = pchunk_concat c' c in
      psek_push Back s' c''
    end else
      psek_push Back s c

let rec psek_concat : 'a. 'a psek -> 'a psek -> 'a psek = fun s s' -> (* s1 s2 *)
  let indf = view_index Front in
  let indb = view_index Back in

  let default = psek_default s in
  let sfront = s.p_sides.(indf) in (* front1, back1   front2, back2 *)
  let sback = s.p_sides.(indb) in
  let s'front = s'.p_sides.(indf) in
  let s'back = s'.p_sides.(indb) in

  let absorbed =
    match s.p_mid with
    | None ->
        if pchunk_is_empty sback && pchunk_is_empty s'front then None
        else Some (psek_absorb (psek_absorb (psek_create (pwchunk_create default)) sback) s'front)
    | Some m -> Some (psek_absorb (psek_absorb m sback) s'front)
  in
  let mid = (* use psek_get_mid *) (* todo: if mid2 not empty, pop its front, and absorb it as well *)
    match absorbed, s'.p_mid with
    | None, _ -> s'.p_mid
    | _, None -> absorbed
    | Some m, Some m' -> Some (psek_concat m m')
  in
  { p_sides = [| sfront; s'back |]; p_mid = mid; p_weight = s.p_weight + s'.p_weight }

let rec psek_split : 'a. 'a psek -> int -> 'a psek * 'a psek = fun s ->
  assert false


(* psek *)

let psek_push pov s x =
  psek_weighted_push pov s x 1
