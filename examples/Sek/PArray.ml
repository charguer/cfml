(** Persistent arrays. *)
type 'a parray = {
  mutable desc : 'a parray_desc;
  dist : int }

and 'a parray_desc =
  | PArray_Base of 'a array
  | PArray_Diff of 'a parray * int * 'a

let dist_bound a =
  Array.length a

(** [parray_mk_base a]
  makes a fresh [parray] with base array [a].
  The created [parray] is a head version. *)
let parray_mk_base a = {
  desc = PArray_Base a;
  dist = 0 }

(** [parray_create sz d]
  creates a fresh [parray] of size [sz] filled with default value [d].
  The created [parray] is a head version. *)
let parray_create sz d =
  let a = Array.make sz d in
  parray_mk_base a

(** [parray_base_copy pa]
  returns a copy of [pa]'s underlying base [array]. *)
let rec parray_base_copy pa =
  match pa.desc with
  | PArray_Base a -> Array.copy a
  | PArray_Diff (origin, index, value) ->
    let a = parray_base_copy origin in
    a.(index) <- value;
    a

(** [parray_rebase_and_get_array pa]
  makes [pa] a base version, and returns the underlying base [array]. *)
let parray_rebase_and_get_array pa =
  match pa.desc with
  | PArray_Base a -> a
  | PArray_Diff (origin, _, _) ->
    let a = parray_base_copy pa in
    pa.desc <- PArray_Base a;
    a

(** [parray_touch pa]
  makes [pa] a base version. *)
let parray_touch pa =
  ignore (parray_rebase_and_get_array pa)

(** [parray_get pa i]
  returns the [i]-th element of [pa]. Makes [pa] a head version. *)
let parray_get pa i =
  let a = parray_rebase_and_get_array pa in
  a.(i)

(** [parray_set pa i x]
  returns a [parray] with all elements of [pa] except the [i]-th element,
  which is set to [x]. The returned [parray] is a head version. *)
let parray_set pa i x =
  let a = parray_rebase_and_get_array pa in
  let cond = (pa.dist = dist_bound a) in
  if cond then begin
    let b = Array.copy a in
    b.(i) <- x;
    { desc = PArray_Base b;
      dist = 0 }
  end else begin
    let v = a.(i) in
    a.(i) <- x;
    let pb = {
      desc = PArray_Base a;
      dist = pa.dist + 1 } in
    pa.desc <- PArray_Diff (pb, i, v);
    pb
  end

(** [parray_copy pa]
  returns a fresh copy of [pa], which is a head version *)
let parray_copy pa =
  let a = parray_base_copy pa in
  parray_mk_base a

(** [parray_of_array a]
  consumes [a] to produce a persistent version of it.
  The returned [parray] is a head version. *)
let parray_of_array = parray_mk_base

(** [parray_to_array pa]
  returns an ephemeral copy of [pa]. *)
let array_of_parray = parray_base_copy
