
(* TODO DEPRECATED *)

open Format
open Parse_type
open Normalize
open Mytools


(** Use this program to compile a MLI file into a CMJ file. *)

(*#########################################################################*)

let ppf = Format.std_formatter

let no_mystd_include = ref false

(*#########################################################################*)

let (^/) = Filename.concat

let _ =
   Settings.configure();

   (*---------------------------------------------------*)
   let files = ref [] in
   Arg.parse
     [ ("-I", Arg.String (fun i -> Clflags.include_dirs := i::!Clflags.include_dirs),
                      "includes a directory where to look for interface files");
       ("-rectypes", Arg.Set Clflags.recursive_types, "activates recursive types");
       ("-nostdlib", Arg.Set no_mystd_include, "do not include standard library");
       ("-nopervasives", Arg.Set Clflags.nopervasives, "do not include standard pervasives file");
       ("-where", Arg.Unit (fun () -> print_endline Cfml_config.libdir; exit 0),
        " print CFML's library files location and exit");
     ]
     (fun f -> files := f::!files)
     ("usage: [-I dir] [..other options..] file.mli");

   Clflags.strict_sequence := true;
   if not !no_mystd_include then
     Clflags.include_dirs :=
       (Cfml_config.libdir ^/ "stdlib") :: !Clflags.include_dirs;

   if List.length !files <> 1
      then failwith "Expects one argument: the filename of the MLI file";
   let sourcefile = List.hd !files in
   if not (Filename.check_suffix sourcefile ".mli")
      then failwith "Extension should be .mli";
   let output_prefix =  Misc.chop_extension_if_any sourcefile in
   typecheck_interface_file ppf sourcefile output_prefix;
   Printf.printf "Wrote %s.cmj\n" output_prefix
