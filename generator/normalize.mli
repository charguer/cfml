
(** A-Normalization of the source code. Essentially:
    - naming all side-effects
    - naming all functions. *)

val normalize_structure : Parsetree.structure -> Parsetree.structure


