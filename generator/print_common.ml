open Asttypes
open Mytools
let sprintf = Printf.sprintf

(*#########################################################################*)
(* ** Printing of base values *)

let parent_if_infix s =
   if Renaming.is_infix_name s then begin
      if s.[0] = '*' || s.[String.length s - 1] = '*'
         then sprintf "( %s )" s
         else sprintf "(%s)" s
   end else s

let string_of_ident s =
   parent_if_infix (Ident.name s)

let string_of_lident idt =
   let names = Longident.flatten idt in
   parent_if_infix (String.concat "." names)

let string_of_constant = function
  | Const_int n -> string_of_int n
  | Const_char c -> String.make 1 c
  | Const_string s -> s
  | Const_float f -> f
  | Const_int32 _ -> unsupported_noloc "int32 type"
  | Const_int64 _ -> unsupported_noloc "int64 type"
  | Const_nativeint _ -> unsupported_noloc "native int type"

let string_of_recflag = function
  | Nonrecursive -> ""
  | Recursive -> " rec"
  | Default -> " DEFAULT"
