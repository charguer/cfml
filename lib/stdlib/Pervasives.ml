

(************************************************************)
(** Exception *)

external raise : exn -> 'a = "%raise"

external failwith : string -> 'a = "%failwith"


(************************************************************)
(** Type conversion *)

external magic : 'a -> 'b = "%magic"


(************************************************************)
(** Boolean *)

let not x =
  if x then false else true


(************************************************************)
(** Physical equality *)

external ( == ) : 'a -> 'a -> bool = "%physical_eq"

let ( != ) x y =
  not (x == y)


(************************************************************)
(** Comparison *)

external ( = ) : 'a -> 'a -> bool = "%compare_eq"
external ( <> ) : 'a -> 'a -> bool = "%compare_neq"
external ( < ) : 'a -> 'a -> bool = "%compare_lt"
external ( > ) : 'a -> 'a -> bool = "%compare_gt"
external ( <= ) : 'a -> 'a -> bool = "%compare_le"
external ( >= ) : 'a -> 'a -> bool = "%compare_ge"

(* CFML does not support reasoning about polymorphic comparison
let min x y =
   if x <= y then x else y
let max x y =
  if x >= y then x else y
*)

let min (x:int) (y:int) =
   if x <= y then x else y
let max (x:int) (y:int) =
  if x >= y then x else y

(* Alternative to also support float
external min : 'a -> 'a -> bool = "%compare_min"
external max : 'a -> 'a -> bool = "%compare_max"
*)



(************************************************************)
(** Boolean *)

external ( && ) : bool -> bool -> bool = "%bool_and"
external ( || ) : bool -> bool -> bool = "%bool_or"


(************************************************************)
(** Integer *)

external ( ~- ) : int -> int = "%int_neg"
external ( + ) : int -> int -> int = "%int_add"
external ( - ) : int -> int -> int = "%int_sub"
external ( * ) : int -> int -> int = "%int_mul"
external ( / ) : int -> int -> int = "%int_div"
external ( mod ) : int -> int -> int = "%int_mod"

let succ n =
  n + 1

let pred n =
  n - 1

let abs (x:int)  =
  if x >= 0 then x else -x


(************************************************************)
(** Bit-level Integer *)

external ( land ) : int -> int -> int = "%int_land"
external ( lor )  : int -> int -> int = "%int_lor"
external ( lxor ) : int -> int -> int = "%int_lxor"
external lnot : int -> int = "%int_lnot"
external ( lsl ) : int -> int -> int = "%int_lsl"
external ( lsr ) : int -> int -> int = "%int_lsr"
external ( asr ) : int -> int -> int = "%int_asr"



(************************************************************)
(** References *)

type 'a ref = { mutable contents : 'a }

let ref x =
  { contents = x }

let (!) r =
  r.contents

let (:=) r x =
  r.contents <- x

let incr r =
  r := !r + 1

let decr r =
  r := !r - 1

(** [ref_unsafe_set r x] allows to modifies the contents of a reference *)
(* unsupported currently, needs explicit types
let ref_unsafe_set r x =
  r.contents <- (magic x)
*)

(************************************************************)
(** Pairs *)

let fst (x,y) =
  x

let snd (x,y) =
  y


(************************************************************)
(** Unit *)

let ignore x =
  ()


(************************************************************)
(** Lists *)

let rec ( @ ) l1 l2 =
  match l1 with
  | [] -> l2
  | hd :: tl -> hd :: (tl @ l2)


(************************************************************)
(** Float *)

(* TODO:
   float ops
   float_of_int and int_of_float
*)
