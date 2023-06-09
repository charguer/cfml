(**
  Type pour un tableau persistant
*)
type 'a parray = {
  mutable data : 'a _parray;
  length : int
} and 'a _parray =
| PArray_Base of 'a array
| PArray_Diff of 'a parray_diff
and 'a parray_diff = {
  origin : 'a parray;
  index : int;
  value : 'a
}

let parray_create size a =
  { data = PArray_Base (Array.make size a); length = size }

let parray_length a =
  a.length

(* On ramène le tableau de base à la version actuelle. *)
let rec parray_pull pa =
  match pa.data with
  | PArray_Base _ -> ()
  | PArray_Diff d ->
    parray_pull d.origin;
    match d.origin.data with
    | PArray_Base a ->
      d.origin.data <- PArray_Diff { origin = pa; index = d.index; value = a.(d.index) };
      a.(d.index) <- d.value;
      pa.data <- PArray_Base a
    | PArray_Diff _ -> ()

let rec parray_get pa i =
  parray_pull pa;
  match pa.data with
  | PArray_Base a -> a.(i)
  | PArray_Diff d -> if d.index = i then d.value else parray_get d.origin i

let rec parray_set pa i x =
  parray_pull pa;
  match pa.data with
  | PArray_Base a ->
    let new_ver = { data = PArray_Base a; length = pa.length } in
    pa.data <- PArray_Diff { origin = new_ver; index = i; value = a.(i) };
    a.(i) <- x;
    new_ver
  | PArray_Diff _ -> { data = PArray_Diff { origin = pa; index = i; value = x }; length = pa.length }

let rec parray_base_copy pa =
  match pa.data with
  | PArray_Base a -> Array.copy a
  | PArray_Diff d ->
    let c = parray_base_copy d.origin in
    c.(d.index) <- d.value;
    c

let parray_copy pa =
  (* parray_pull pa; -- considère-t-on qu'une copie nous met en version la plus récente utilisée, je dirais que non *)
  { data = PArray_Base (parray_base_copy pa); length = pa.length }
