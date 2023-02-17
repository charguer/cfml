
type node = {
  mutable value : int;
  mutable sub : node MList.mlist }

type contents = Empty | Nonempty of node

type heap = contents ref

let create () =
  ref Empty

let is_empty p =
  !p = Empty

let merge q1 q2 =
  if q1.value < q2.value
    then (MList.push q1.sub q2; q1)
    else (MList.push q2.sub q1; q2)

let insert p x =
  let q2 = { value = x; sub = MList.create() } in
  match !p with
  | Empty -> p := Nonempty q2
  | Nonempty q1 -> p := Nonempty (merge q1 q2)

let rec merge_pairs l =
  let q1 = MList.pop l in
  if MList.is_empty l then q1 else
  let q2 = MList.pop l in
  let q = merge q1 q2 in
  if MList.is_empty l
     then q
     else merge q (merge_pairs l)

let pop_min p =
  match !p with
  | Empty -> assert false
  | Nonempty q ->
    let x = q.value in
    if MList.is_empty q.sub
      then p := Empty
      else p := Nonempty (merge_pairs q.sub);
    x



(* ---------WITH NULL

(*open NullPointers*)
external mk_null : unit -> 'a = "null"
external is_null : 'a -> bool = "is_null"
let null : 'a = mk_null()


type heap = node (* or null *)
and node = { value : int; sub : node mlist }

let create () =
  ref null

let is_empty p =
  p == null

let merge q1 q2 =
  if q1.value < q2.value
    then (MList.push q1.sub q2; q1)
    else (MList.push q2.sub q1; q2)

let insert p x =
  let q1 = !p in
  let q2 = { value = x; sub = MList.create() } in
  if q1 == null
    then p := q2
    else p := merge q1 q2

let rec merge_pairs l =
  let q1 = MList.pop l in
  if MList.is_empty l then q else
  let q2 = MList.pop l in
  let q = merge q1 q2 in
  if MList.is_empty l
     then q
     else merge q (merge_pairs l)

let pop_min p =
  let q = !p in
  let x = q.value in
  if MList.is_empty q.sub
    then p := null
    else p := merge_pairs q.sub

*)
