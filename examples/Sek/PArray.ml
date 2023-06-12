(**
  Type pour un tableau persistant
*)
type 'a parray = {
  mutable data : 'a _parray;
  size : int
} and 'a _parray =
| PArray_Base of 'a array
| PArray_Diff of 'a parray_diff
and 'a parray_diff = {
  origin : 'a parray;
  index : int;
  value : 'a
}

let parray_create size a =
  { data = PArray_Base (Array.make size a); size = size }

let parray_length a =
  a.size

(* On coupe la chaîne avec un nouveau tableau contenant toutes les modifications de la version. *)
let rec parray_base_copy pa =
  match pa.data with
  | PArray_Base a -> (Array.copy a)
  | PArray_Diff d ->
    let new_base = parray_base_copy d.origin in
    new_base.(d.index) <- d.value;
    new_base

let parray_get pa i =
  let base = match pa.data with
  | PArray_Base a -> a
  | PArray_Diff _ -> parray_base_copy pa
  in
  pa.data <- PArray_Base base;
  base.(i)

let parray_set pa i x =
  let base = match pa.data with
  | PArray_Base a -> a
  | PArray_Diff _ -> parray_base_copy pa
  in
  pa.data <- PArray_Base base;
  base.(i) <- x

(* Pour la copie : on peut juste renvoyer le même parray, puisqu'il pointera toujours sur la même version ? *)
let parray_copy pa = pa
