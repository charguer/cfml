
(** Configure the typechecker to 
    - not include stdlib 
    - use the value restriction 
    - ignore "mli" files that might exist next to "ml" files
  *)

val configure : unit -> unit
