
(**************************************************************)
(** Parameters to control the normalization and generation *)

val use_credits : bool ref

val use_left_to_right_order : bool ref

val generate_deep_embedding : bool ref

val generate_encoders : bool ref


(**************************************************************)
(**************************************************************)

(** The rest of this file contains some helper functions. *)

(**************************************************************)
(** Option manipulation functions *)

val option_map : ('a -> 'b) -> 'a option -> 'b option
val option_iter : ('a -> unit) -> 'a option -> unit
val unsome : 'a option -> 'a
val list_of_option : 'a option -> 'a list
val option_app : 'a -> ('b -> 'a) -> 'b option -> 'a
val unsome_safe : 'a -> 'a option -> 'a
val bool_of_option : bool option -> bool


(**************************************************************)
(** List manipulation functions *)

val list_make : int -> 'a -> 'a list
val list_mapi : (int -> 'a -> 'b) -> 'a list -> 'b list
val list_init : int -> (int -> 'a) -> 'a list
val list_nat : int -> int list
val list_separ : 'a -> 'a list -> 'a list
val filter_somes : 'a option list -> 'a list
val list_unique : 'a list -> 'a list
val list_intersect : 'a list -> 'a list -> 'a list
val list_minus : 'a list -> 'a list -> 'a list
val list_concat_map : ('a -> 'b list) -> 'a list -> 'b list
val list_assoc_option : 'a -> ('a * 'b) list -> 'b option
val assoc_list_map : ('a -> 'b) -> ('c * 'a) list -> ('c * 'b) list
val list_remove : int -> 'a list -> 'a list
val list_replace : int -> 'a -> 'a list -> 'a list
val list_replace_nth : int -> 'a list -> 'a list -> 'a list
val list_ksort : ('a -> 'a -> int) -> ('a * 'b) list -> ('a * 'b) list
val list_index : 'a -> 'a list -> int
val list_is_included : 'a list -> 'a list -> bool


(**************************************************************)
(** String manipulation functions *)

val str_cmp : string -> string -> int
val str_starts_with : string -> string -> bool

(** Capitalize the first letter of a string (if any) *)

val str_capitalize_1 : string -> string

(** Capitalize the second letter of a string (if any) *)

val str_capitalize_2 : string -> string


(**************************************************************)
(** File manipulation functions *)

val file_put_contents : string -> string -> unit


(**************************************************************)
(** Try-with manipulation functions *)

(** Tests whether a function throws [Not_found],
    and returns the result in the form of a boolean value. *)

val gives_not_found : (unit -> 'a) -> bool


(**************************************************************)
(** Pretty-printing functions *)

val lin0 : string  (** The empty string *)

val lin1 : string  (** The line-return string *)

val lin2 : string  (** The double line-return string *)

(** Display a list of values with a separator *)

val show_list : ('a -> string) -> string -> 'a list -> string

(** Display a list of values with a separator, including it at the front *)

val show_listp : ('a -> string) -> string -> 'a list -> string

(** Display a list of values with a separator, including it at the back *)

val show_listq : ('a -> string) -> string -> 'a list -> string

(** Dispaly the content of an option, else the empty string *)

val show_option : ('a -> string) -> 'a option -> string

(** Display a string, enclosed using parentheses if the first argument is true *)

val show_par : bool -> string -> string

(** Display *)

val show_str : 'a -> 'a


(**************************************************************)
(** Error messages *)

(** Display a string on stdout *)

val output : string -> unit

(** Display a message explaining that a feature is not supported *)

val unsupported_noloc : string -> 'a

(** Display a message explaining that a feature is not supported,
    and report the location *)

val unsupported : Location.t -> string -> 'a

(** Display message associated with a warning,
    and report the location *)

val warning : Location.t -> string -> unit

exception Not_in_normal_form of Location.t * string

val not_in_normal_form : Location.t -> string -> 'a
