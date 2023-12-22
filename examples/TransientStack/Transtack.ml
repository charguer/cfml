open EChunk
open SChunk

type 'a pstack =
  { pfront : 'a schunk;
    ptail : 'a schunk list; }

type 'a estack =
  { mutable front : 'a echunk;
    mutable tail : 'a schunk list;
    mutable spare : 'a echunk option; (* Spare echunk, if set, always empty. *)
    mutable id : Id.t; }

(* Conversions and copy functions *)

let pstack_to_estack s =
  let pf = s.pfront in
  { front = echunk_of_schunk pf;
    tail = s.ptail;
    spare = None;
    id = Id.create () }

let estack_to_pstack s =
  let newpfront = schunk_of_echunk s.front s.id in
  { pfront = newpfront;
    ptail = s.tail; }

let copy_with_sharing s =
  let front = echunk_copy s.front in
  let tail = s.tail in
  let spare = None in
  let sid = Id.create () in
  s.id <- sid;
  let id = Id.create () in
  { front; tail; spare; id }

let estack_to_pstack_preserving s =
  estack_to_pstack (copy_with_sharing s)

let copy_without_sharing s =
  let front = echunk_copy s.front in
  let id = Id.create () in
  let copy p = schunk_of_echunk (echunk_of_schunk p) id in
  let tail = List.map copy s.tail in
  let spare = None in
  { front; tail; spare; id }

(* Ephemeral operations *)

let ecreate d =
  { front = echunk_create d;
    tail = [];
    spare = None;
    id = Id.create (); }

let eis_empty x =
  echunk_is_empty x.front

let epeek s =
  assert (not (eis_empty s));
  echunk_peek s.front

let get_empty x d =
  match x with
  | None -> echunk_create d
  | Some e -> e

let epush s x =
  if echunk_is_full s.front then begin
    let p = schunk_of_echunk s.front s.id in
    s.tail <- p :: s.tail;
    s.front <- get_empty s.spare s.front.default;
    s.spare <- None
  end;
  echunk_push s.front x

let epop s =
  assert (not (eis_empty s));
  let x = echunk_pop s.front in
  if echunk_is_empty s.front then begin
    match s.tail with
    | [] -> ()
    | p::ps ->
       let newfront =
         if Id.eq_opt p.owner s.id
          then p.support
          else echunk_of_schunk p in
       s.tail <- ps;
       s.spare <- Some (s.front);
       s.front <- newfront
  end;
  x

(* Persistent operations *)

let pcreate d =
  { pfront = schunk_empty d;
    ptail = []; }

let pis_empty s =
  schunk_is_empty s.pfront

let ppeek s =
  assert (not (pis_empty s));
  schunk_peek s.pfront

let ppush s x =
  if schunk_is_full s.pfront then
    let p = schunk_empty (get_default s.pfront) in
    let p' = schunk_push p x in
    { pfront = p';
      ptail = s.pfront :: s.ptail }
  else
    let p' = schunk_push s.pfront x in
    { s with pfront = p' }

let ppop s =
  assert (not (pis_empty s));
  let p',x = schunk_pop s.pfront in
  let s' =
    if schunk_is_empty p' then
      match s.ptail with
      | [] -> { s with pfront = p' }
      | p::ps -> { pfront = p; ptail = ps }
    else
      { s with pfront = p' } in
  (s',x)
