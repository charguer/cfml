(* This file is a copy of [array.ml], with different [external] declarations,
   because:
   - we must axiomatize the functions that cannot be implemented in OCaml;
   - and only those.
*)

(* A literal array [|v1; .. ; vN|] is encoded by CFML as
   [of_list [v1; .. ; vN]].
   This requires us to make [of_list] a primitive function. *)
external of_list : 'a list -> 'a array = "%array_of_list"

(* [unsafe_get] and [unsafe_set] intentionally omitted, at least for now. *)

external length : 'a array -> int = "%array_length"
external get : 'a array -> int -> 'a = "%array_get"
external set : 'a array -> int -> 'a -> unit = "%array_set"
external make : int -> 'a -> 'a array = "%array_make"

(* [make_float] omitted. *)

let init n f =
  assert (0 <= n);
  if n = 0 then of_list [] else begin
    let res = make n (f 0) in
    for i = 1 to pred n do
      set res i (f i)
    done;
    res
  end
  (* Remark: might be optimized by using a sub-array to avoid initialization *)

(* [make_matrix] omitted. *)

let copy a =
   let n = length a in
   if n = 0 then of_list [] else begin
     let r = make (length a) (get a 0) in
     for i = 0 to pred n do
        set r i (get a i);
     done;
      r
   end

(* Re-implementation of [append]. *)
let append a1 a2 =
  let n1 = length a1 in
  let n2 = length a2 in
  if n1 = 0 && n2 = 0 then of_list [] else begin
     let d = (if n1 <> 0 then get a1 0 else get a2 0) in
     let a = make (n1+n2) d in
     for i = 0 to pred n1 do
        set a i (get a1 i);
     done;
     for i = 0 to pred n2 do
        set a (n1+i) (get a2 i);
     done;
     a
   end

(* Re-implementation of [concat]. *)
(* TEMPORARY problematic reference to [List]?
let concat ts =
  List.fold_left append (of_list []) ts
*)

(* Re-implementation of [sub]. *)
let sub a ofs len =
  assert (not (ofs < 0 || len < 0 || ofs > length a - len));
  init len (fun i -> get a (ofs + i))

let fill a start nb v =
  assert (not (start < 0 || nb < 0 || start > length a - nb));
  for i = start to pred (start + nb) do
    set a i v;
  done

(* Re-implementation of [blit]. *)
(* TEMPORARY incorrect: should work also when [a1] and [a2] are the same array! *)
let blit a1 start1 a2 start2 nb =
  assert (not (nb < 0 || start1 < 0 || start1 > length a1 - nb
                      || start2 < 0 || start2 > length a2 - nb));
  for i = 0 to pred nb do
    set a2 (start2 + i) (get a1 (start1 + i));
  done

let iter f a =
  for i = 0 to pred (length a) do
    f (get a i)
  done

let map f a =
  let n = length a in
  if n = 0 then of_list [] else begin
    let r = make n (f (get a 0)) in
    for i = 1 to pred n do
      set r i (f (get a i));
    done;
    r
  end

let iteri f a =
  for i = 0 to pred (length a) do
    f i (get a i)
  done

let mapi f a =
  let n = length a in
  if n = 0 then of_list [] else begin
    let r = make n (f 0 (get a 0)) in
    for i = 1 to pred n do
      set r i (f i (get a i));
    done;
    r
  end

let to_list a =
  let rec tolist i res =
    if i < 0 then res else tolist (i - 1) (get a i :: res) in
  tolist (length a - 1) []

let fold_left f x a =
  let r = ref x in
  for i = 0 to pred (length a) do
    r := f !r (get a i)
  done;
  !r

let fold_right f a x =
  let r = ref x in
  for i = pred (length a) downto 0 do
    r := f (get a i) !r
  done;
  !r

(* [sort], [stable_sort], [fast_sort] omitted, for now. *)
