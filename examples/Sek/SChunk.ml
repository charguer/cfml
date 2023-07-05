open View
open Owner
open EChunk
open PChunk

type 'a schunk =
  | MaybeOwned of {
      support : 'a echunk;
      id : owner }
  | Shared of 'a pchunk

let schunk_match_id o c =
  match o, c with
  | None, Shared pc -> c
  | None, MaybeOwned { support = ec; _ } ->
      let pc = pchunk_of_echunk ec in
      Shared pc
  | Some o, Shared pc ->
      let ec = echunk_of_pchunk pc in
      MaybeOwned { support = ec; id = o }
  | Some o, MaybeOwned { support = ec; id = i } ->
      if o = i then
        c
      else begin
        let ec' = echunk_copy ec in
        MaybeOwned { support = ec'; id = o }
      end

let schunk_default c =
  match c with
  | MaybeOwned { support = ec; _ } -> echunk_default ec
  | Shared pc -> pchunk_default pc

let schunk_dummy d =
  Shared (pchunk_dummy d)

let schunk_create_maybe_owned d o =
  let ec = echunk_create d in
  MaybeOwned {
    support = ec;
    id = o }

let schunk_create_shared d =
  let pc = pchunk_create d in
  Shared pc

let schunk_create d oo =
  match oo with
  | Some o -> schunk_create_maybe_owned d o
  | None -> schunk_create_shared d

let schunk_is_empty c =
  match c with
  | MaybeOwned { support = ec; _ } -> echunk_is_empty ec
  | Shared pc -> pchunk_is_empty pc

let schunk_is_full c =
  match c with
  | MaybeOwned { support = ec; _ } -> echunk_is_full ec
  | Shared pc -> pchunk_is_full pc

let schunk_size c =
  match c with
  | MaybeOwned { support = ec; _ } -> echunk_size ec
  | Shared pc -> pchunk_size pc

let schunk_peek v c =
  match c with
  | MaybeOwned { support = ec; _ } -> echunk_peek v ec
  | Shared pc -> pchunk_peek v pc

let schunk_pop v o c =
  let oc = schunk_match_id o c in
  match oc with
  | MaybeOwned { support = ec; id = i } ->
      let x = echunk_pop v ec in
      oc, x
  | Shared pc ->
      let pc', x = pchunk_pop v pc in
      Shared pc', x

let schunk_push v o c x =
  let oc = schunk_match_id o c in
  match oc with
  | MaybeOwned { support = ec; id = i } ->
      echunk_push v ec x;
      oc
  | Shared pc ->
      let pc' = pchunk_push v pc x in
      Shared pc'

let rec schunk_concat oo c0 c1 =
  if schunk_is_empty c1 then
    c0
  (* else if schunk_is_empty oc0 then
    c1 *)
  else begin
    let c1', x = schunk_pop Front oo c1 in
    let c0' = schunk_push Back oo c0 x in
    schunk_concat oo c0' c1'
  end

let schunk_of_echunk o ec =
  MaybeOwned {
    support = ec;
    id = o }

let echunk_of_schunk o sc =
  match sc with
  | MaybeOwned { support = ec; id = i } ->
      if o = i then
        ec
      else
        echunk_copy ec
  | Shared pc -> echunk_of_pchunk pc
