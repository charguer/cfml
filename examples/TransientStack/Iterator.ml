open EChunk
open SChunk
open Transtack

(** An iterator for both ephemeral and persistent sequences.
    It contains the following fields:

    [focused] is the ephemeral chunk storing the item focused by the iterator.
    The element under focus is at index [fview-1]. The next element reached
    by the iterator is at index [fview-2]. When [fview] is at [0], the next
    element to be visited lies in another ephemeral chunk.

    [fview] is the index of the item focused by the iterator, within the ephemeral
    chunk [focused].

    [fid] is the identifier associated with the shareable chunk that was used
    to access to the ephemeral chunk [focused]. In the particular case where
    [focused] corresponds to the front chunk of an ephemeral stack, [fid]
    is set to the identifier of that stack.

    Note that the triple (focused,fview,fid) essentially corresponds to the
    inlining of the fields from the type [schunk]. This inlining saves the
    need to follow an indirection upon every iterator operation.

    [traveled] is the number of chunks that the iterator has already traversed
    in full.

    [uestack] is an option. If the iterator traverses an ephemeral stack, it
    contains the address of that stack. If the iterator traverses a persistent
    stack, it contains the value [None].

    [rest] describes the list of shareable chunks that remain to be traversed
    by the iterator, after the items from [focused] are all visited. *)

type 'a iterator =
  { mutable focused : 'a echunk;
    mutable fview : int;
    mutable fid : Id.t option;
    mutable traveled : int;
    rest : ('a schunk) ListIterator.t;
    uestack : 'a estack option;
  }

let of_pstack x =
  let focused = x.pfront.support in
  let fview = x.pfront.view in
  let fid = x.pfront.owner in
  let traveled = 0 in
  let rest = ListIterator.of_list x.ptail in
  let uestack = None in
  { focused; fview; fid; traveled; rest; uestack }

let of_estack x =
  let focused = x.front in
  let fview = x.front.top in
  let fid = Some x.id in
  let traveled = 0 in
  let rest = ListIterator.of_list x.tail in
  let uestack = Some x in
  { focused; fview; fid; traveled; rest; uestack }

let finished it =
  it.fview = 0

let get it =
  assert (not (finished it));
  it.focused.data.(it.fview - 1)

let move it =
  assert (not (finished it));
  let nview = it.fview - 1 in
  if nview = 0 && (not (ListIterator.finished it.rest)) then begin
    let s = ListIterator.get_and_move it.rest in
    it.focused <- s.support;
    it.fview <- s.view;
    it.fid <- s.owner;
    it.traveled <- it.traveled + 1;
  end else
    it.fview <- nview

(* [fupdate k f xs] update the k-nth element of the list xs
   using f, and returns this element *)
let rec fupdate k f xs =
  match xs,k with
  | [],_ ->
     assert false
  | x::xs,0 ->
     let z = f x in
     z,z::xs
  | x::xs,k ->
     let z,zs = fupdate (k-1) f xs in
     z,x::zs

(* Replace the k-nth schunk with a fresh one and returns it. *)
let update_estack k s =
  let owner = s.id in
  let upd x =
    let c = echunk_of_schunk x in
    schunk_of_echunk c owner in
  let nschunk,ntail = fupdate k upd s.tail in
  s.tail <- ntail;
  nschunk

(* [ensure_uniquely_own_focused it] ensures that uestack uniquely
   owns the focused echunk. If not, it copies it, and reflect this
   change in uestack. This operation assumes the iterator to
   operator on an ephemeral sequence. *)
let ensure_uniquely_own_focused it =
  match it.uestack with
  | None -> assert false
  | Some uestack ->
     if not (Id.eq_opt it.fid uestack.id)
     then begin
         let nschunk = update_estack (it.traveled-1) uestack in
         it.focused <- nschunk.support;
         it.fid <- Some uestack.id;
       end

let set it x =
  assert (not (finished it));
  ensure_uniquely_own_focused it;
  it.focused.data.(it.fview - 1) <- x
