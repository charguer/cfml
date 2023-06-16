Set Implicit Arguments.
From CFML Require Import WPLib.
From CFML Require Import WPDisplay WPRecord.  

Require Import Sys_ml.

Parameter word_size_spec :
  word_size = 32 \/ word_size = 64.

(* [Sys.max_array_length] is nonnegative. We do not guarantee anything more.
   In reality, [Sys.max_array_length] is [2^22 - 1] on a 32-bit machine, and
   [2^54 - 1] on a 64-bit machine. (10 bits are reserved in an array header,
   the rest encodes the array length.) *)

(* Ideally, we should guarantee that [Sys.max_array_length] is less than or
   equal to [max_int]. This could be useful someday if we need to prove that
   certain integer calculations cannot overflow. *)

Parameter max_array_length_spec :
  0 <= max_array_length.

Parameter max_string_length_spec :
  0 <= max_string_length.
