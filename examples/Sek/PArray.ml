(**
  Type pour un tableau persistant
*)
type 'a parray = {
  mutable data : 'a parray_desc;
  size : int
} and 'a parray_desc =
| PArray_Base of 'a array
| PArray_Diff of 'a parray * int * 'a

let parray_create size a =
  { data = PArray_Base (Array.make size a); size = size }

let parray_length a =
  a.size

(* On coupe la chaîne avec un nouveau tableau contenant toutes les modifications de la version. *)
let rec parray_base_copy pa =
  match pa.data with
  | PArray_Base a -> (Array.copy a)
  | PArray_Diff (origin, index, value) ->
    let new_base = parray_base_copy origin in
    new_base.(index) <- value;
    new_base

let parray_get pa i =
  let base = match pa.data with
  | PArray_Base a -> a
  | PArray_Diff (_, _, _) -> parray_base_copy pa
  in
  pa.data <- PArray_Base base;
  base.(i)

let parray_set pa i x =
  let base = match pa.data with
  | PArray_Base a -> a
  | PArray_Diff (_, _, _) -> parray_base_copy pa
  in
  let new_version = { data = PArray_Base base; size = pa.size } in
  pa.data <- PArray_Diff (new_version, i, base.(i));
  base.(i) <- x;
  new_version

(* Pour la copie : on peut juste renvoyer le même parray, puisqu'il pointera toujours sur la même version ? *)
let parray_copy pa = pa
