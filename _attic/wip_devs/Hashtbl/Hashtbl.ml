(* OCaml Hashtable module, simplified by:
   - using list of pairs for buckets instead of an ad-hoc data type,
   - undoing the depth-3 manual unfolding of the find_rec operation,
   - removing the statistics features,
   - uniformizing the names to the auxiliary recursive functions,
   - adding a few let-bindings to name intermediate results.
*)

(* OCaml's generic hashing function *)
external seeded_hash_param : int -> int -> int -> 'a -> int = "caml_hash" [@@noalloc]
let hash x = seeded_hash_param 10 100 0 x

(* Hashtable implementation. *)

type ('a, 'b) t =
  { mutable size: int;                  (* number of entries *)
    mutable data: ('a * 'b) list array; (* the buckets *)
  }

let rec power_2_above x n =
  if x >= n then x
  else if x * 2 > Sys.max_array_length then x
  else power_2_above (x * 2) n

let create initial_size =
  let s = power_2_above 16 initial_size in
  { size = 0;
    data = Array.make s [] }

let length h = h.size

let index h key =
   (hash key) mod (Array.length h.data)

let add h key info =
  let i = index h key in
  let old_bucket = h.data.(i) in
  let bucket = (key, info) :: old_bucket in
  h.data.(i) <- bucket;
  h.size <- h.size + 1

let remove h key =
  let rec aux = function
    | [] -> []
    | (k, i):: next ->
        if compare k key = 0 then begin
          h.size <- h.size - 1;
          next
        end else
          (k, i) :: aux next
    in
  let i = index h key in
  h.data.(i) <- aux h.data.(i)

let find h key =
  let rec aux = function
    | [] -> raise Not_found
    | (k, d) :: rest ->
        if compare key k = 0
          then d
          else aux rest
    in
  let i = index h key in
  aux h.data.(i)

let mem h key =
  let rec aux = function
  | [] -> false
  | (k, d) :: rest ->
      compare k key = 0 || aux rest in
  let i = index h key in
  aux h.data.(i)

let iter f h =
  let rec aux = function
    | [] -> ()
    | (k, d) :: rest ->
        f k d;
        aux rest
    in
  let d = h.data in
  for i = 0 to Array.length d - 1 do
    aux d.(i)
  done
