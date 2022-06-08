open Format
open Parse_type
open Normalize
open Mytools

(*#########################################################################*)

let is_tracing = ref false

let trace s =
  if !is_tracing
     then (print_string s; print_newline())

let ppf = Format.std_formatter

let only_cmj = ref false

let only_normalize = ref false

let no_mystd_include = ref false

let outputfile = ref None

(* err_formatter *)


(*#########################################################################*)

let (^/) = Filename.concat

let spec =
  Arg.align [
    ("-I", Arg.String (fun i -> Clflags.include_dirs := i::!Clflags.include_dirs),
                      " includes a directory where to look for interface files");
    ("-rectypes", Arg.Set Clflags.recursive_types, " activates recursive types");
    ("-left2right", Arg.Set Mytools.use_left_to_right_order, " use the left-to-right evaluation order for sub-expressions, instead of OCaml order");
    ("-credits", Arg.Set Mytools.use_credits, " generate 'pay' instructions");
    ("-nostdlib", Arg.Set no_mystd_include, " do not include standard library");
    ("-nopervasives", Arg.Set Clflags.nopervasives, " do not include standard pervasives file");
    ("-o", Arg.String (fun s -> outputfile := Some s), " set the output file name");
    ("-only_cmj", Arg.Set only_cmj, " only generate the .cmj file, not the .v file");
    ("-only_normalize", Arg.Set only_normalize, " only generate the .cmj file, and attempt normalization, not the .v file");
    ("-deep_embedding", Arg.Set Mytools.generate_deep_embedding, " generate the deep embedding of the source programs");
    ("-def_encoders", Arg.Set Mytools.generate_encoders, " generate the definition of the encoders for each type");

    ("-debug", Arg.Set is_tracing, " trace the various steps");
    ("-width", Arg.Set_int Print_coq.width, " set pretty-printing width for the .v file");
    ("-where", Arg.Unit Cfml_config.print_libdir,
     " print CFML's library files location and exit");
  ]

(*
    ("-strict_value_restriction", Arg.Set Clflags.strict_value_restriction, " enforce the strict value restriction (relaxed value restriction is the default)");
*)

let rename_cmj_and_exit sourcefile =
  let prefixname = Filename.chop_extension sourcefile in
  let cmd = Printf.sprintf "mv %s.cmj_temp %s.cmj" prefixname prefixname in
  begin try ignore (Sys.command cmd)
         with _ -> Printf.printf "Could not rename %s.cmj_temp file.\n" prefixname end;
  exit 0


let _ =
   Settings.configure();

   (*---------------------------------------------------*)
   trace "1) parsing of command line";
   let files = ref [] in
   Arg.parse
     spec
     (fun f -> files := f::!files)
     ("usage: [-I dir] [..other options..] file.ml");
   (*
   let args = Sys.argv in
   if Array.length args < 2 then
      failwith "Expects one argument: the filename of the ML source file";
   let sourcefile = args.(1) in
   *)
   Clflags.strict_sequence := true;

   if not !no_mystd_include then
     Cfml_config.libdir |> option_iter begin fun libdir ->
       Clflags.include_dirs := (libdir ^/ "stdlib") :: !Clflags.include_dirs
     end;

   trace "1) parsing of command line";
   if List.length !files <> 1 then
      failwith "Expects one argument: the filename of the ML source file";
   let sourcefile = List.hd !files in
   if !Clflags.nopervasives
     && Filename.basename sourcefile <> "Pervasives.ml" then
      failwith "Option -nopervasives may only be used to compile file Pervasives";
      (* this defensive check is needed for the correctness of normalization
         of special operators such as "mod" or "&&";
         see also function [add_pervasives_prefix_if_needed] *)

   if not (Filename.check_suffix sourcefile ".ml") then
     failwith "The file name must be of the form *.ml";
   let basename = Filename.chop_suffix (Filename.basename sourcefile) ".ml" in
   let dirname = Filename.dirname sourcefile in
   let outputfile : string =
     match !outputfile with
     | None ->
         Filename.concat dirname ((String.capitalize_ascii basename) ^ "_ml.v")
     | Some f ->
         f
   in
   let debugdir = Filename.concat dirname "_output" in
   let debugdirBase = Filename.concat debugdir (String.capitalize_ascii basename) in
   (*  FAILURE ON WINDOWS   *)
   let cmd = Printf.sprintf "mkdir -p %s" debugdir in
   begin try ignore (Sys.command cmd)
         with _ -> Printf.printf "Could not create debug directory\n" end;


   (*---------------------------------------------------*)
   trace "2) reading and typing source file";
   let (opt,inputfile) = process_implementation_file ppf sourcefile in
   (* Note: the above line calls Typemod.type_implementation, which calls
            Env.save_signature simple_sg modulename (outputprefix ^ ".cmj_temp");
      The %.cmj_temp file is renamed to %.cmj after the %_ml.v is produced. *)
   let parsetree1 : Parsetree.structure =
      match opt with
      | None -> failwith "Could not read and typecheck input file"
      | Some (parsetree1, (typedtree1,_)) -> parsetree1
      in
   (* TEMPORARY file_put_contents (debugdirBase ^ "_original.ml") (Print_past.string_of_structure parsetree1);*)

   if !only_cmj then begin
      trace "3) exiting since -only_cmj";
      rename_cmj_and_exit sourcefile;
   end;

   (*---------------------------------------------------*)
   trace "3) normalizing source code";
   let parsetree2 : Parsetree.structure = normalize_structure parsetree1 in
   (* TEMPORARY file_put_contents (debugdirBase ^ "_normalized.ml") (Print_past.string_of_structure parsetree2); *)

   (*---------------------------------------------------*)
   trace "4) typing normalized code";
   let (typedtree2, _ : Typedtree.structure * Typedtree.module_coercion) =
      let fail () =
         failwith (Printf.sprintf "Could not typecheck the normalized source code\nCheck out the file %s_normalized.ml." debugdirBase) in
      try
         match typecheck_implementation_file ppf sourcefile parsetree2 with
         | None -> fail() (* TODO: useful?*)
         | Some typedtree2 -> typedtree2
      with Typetexp.Error(loc, err) -> fail()
      in

   (*---------------------------------------------------*)
   trace "5) dumping normalized file";
   file_put_contents (debugdirBase ^ "_normalized_typed.ml") (Print_tast.string_of_structure typedtree2);
   (* ignore (typedtree2); *)

   if !only_normalize then begin
      trace "6) exiting since -only_normalize";
      rename_cmj_and_exit sourcefile;
   end;

   (*---------------------------------------------------*)
   trace "5) constructing caracteristic formula ast";
   let cftops =
      try Characteristic.cfg_file !no_mystd_include typedtree2
      with
      | Typetexp.Error(_, _) -> assert false
      | Not_in_normal_form (loc, s) ->
         Location.print_error Format.std_formatter loc;
         Printf.printf "  %s.\nThe normalized file does not appear to be in normal form.\nTo investigate, open %s_normalized.ml\nand %s_normalized_typed.ml.\n" s debugdirBase debugdirBase;
         exit 1
      in

   (*---------------------------------------------------*)
   trace "6) converting caracteristic formula ast to coq ast";
   let coqtops = Formula_to_coq.coqtops_of_cftops cftops in

   (*---------------------------------------------------*)
   trace "7) dumping debug formula file";
   let result = Print_coq.tops coqtops in
   file_put_contents (debugdirBase ^ "_formulae.v") result;

   (*---------------------------------------------------*)
   trace "8) dumping %_ml.v file";
   file_put_contents outputfile result;

   (*---------------------------------------------------*)
   trace "9) characteristic formulae successfully generated\n";
   rename_cmj_and_exit sourcefile


(*########################################################
todo:
- top level functions should not be named
- fun p1 p2   transformation only works for exhaustive patterns
  => check   | Texp_function of (pattern * expression) list * partial
     always partial !!
*)

(*
"Require Import FuncDefs.\n\n"coqtop_set_implicit_arguments
*)
(*
Clflags.no_std_include := true;
*)
