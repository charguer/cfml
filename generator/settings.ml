
let configure () =
   Config.interface_suffix := "____mli_files_are_ignored____";
   Clflags.strict_value_restriction := true;  
   Clflags.no_std_include := true

(* strict_value_restriction is needed to avoid problematic over-generalization
   on e.g. the code "let x = r.nb in ()", where nb is a record field *)