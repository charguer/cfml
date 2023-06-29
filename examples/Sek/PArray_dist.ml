(**
  Type pour un tableau persistant  TODO: rename to SIMPLE_...
*)
type 'a parray = {
  mutable data : 'a parray_desc;
  mutable maxdist : int
  }

 and 'a parray_desc =
| PArray_Base of 'a array
| PArray_Diff of 'a parray * int * 'a

let dist_bound a =
  Array.length a

let parray_create size d =
  let a = Array.make size d in
  { data = PArray_Base a; maxdist = 0 }

(* let rec parray_length pa =
  match pa.data with
  | PArray_Base a -> Array.length a
  | PArray_Diff (origin, _, _) -> parray_length origin *)

(* On coupe la chaîne avec un nouveau tableau contenant toutes les modifications de la version. *)
let rec parray_base_copy pa =
  match pa.data with
  | PArray_Base a -> (Array.copy a)
  | PArray_Diff (origin, index, value) ->
    let a = parray_base_copy origin in
    a.(index) <- value;
    a

let parray_rebase_and_get_array pa =
  match pa.data with
  | PArray_Base a -> a
  | PArray_Diff (origin, _, _) ->
    let a = parray_base_copy pa in
    pa.data <- PArray_Base a;
    a

let parray_get pa i =
  let a = parray_rebase_and_get_array pa in
  a.(i)

let parray_set pa i x =
  let a = parray_rebase_and_get_array pa in
  let cond = (pa.maxdist = dist_bound a) in
  if cond then begin
    let b = Array.copy a in
    b.(i) <- x;
    { data = PArray_Base b; maxdist = 0 }
  end else begin
    let v = a.(i) in
    a.(i) <- x;
    let pb = { data = PArray_Base a; maxdist = pa.maxdist + 1 } in
    pa.data <- PArray_Diff (pb, i, v);
    pb
  end


let parray_copy pa =
  let a = parray_base_copy pa in
  { data = PArray_Base a; maxdist = 0 }
