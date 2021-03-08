(* TEMPORARY

(* [big_endian] and [word_size] are defined as external *constants* here.
   In OCaml they are external *functions* and they are invoked once on
   startup. *)
external big_endian : (* unit -> *) bool = "%big_endian"
external word_size : (* unit -> *) int = "%word_size"

let max_array_length = (1 lsl (word_size - 10)) - 1
let max_string_length = word_size / 8 * max_array_length - 1

*)

let big_endian = false
let word_size = 64
let max_array_length = 18014398509481983
let max_string_length = 144115188075855863
