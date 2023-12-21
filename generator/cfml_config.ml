open Mytools

(* [basis] gives the path to the CFML root folder *)

let basis : string option =
  (*  Printf.eprintf "CURRENT %s\n" Sys.argv.(0);
        CURRENT /home/charguer/cfml2/_build/default/generator/cfmlc.exe *)
  let cur_exec = Sys.argv.(0) in
  let basis = Filename.chop_suffix cur_exec "_build/default/generator/cfmlc.exe" in
  Some basis

  (* DEPRECATED

  This code first defines [basis] in the following manner.

   Method 1. Use the full path to this executable file, ".../bin/cfml/cfmlc",
             and keep only the prefix "...".

   Method 2. Execute the command [opam config var prefix].

  (* Method 1. *)
  match Filename.chop_suffix_opt ~suffix:"/bin/cfml/cfmlc" Sys.argv.(0) with
  | Some basis ->
      Some basis
  | None ->
      try
        (* Method 2. *)
        let c = Unix.open_process_in "opam config var prefix" in
        let basis = input_line c in
        close_in_noerr c;
        Some basis
      with _ ->
        (* Failure of both methods. *)
        None
  *)

(* Then, [libdir] is obtained by appending "/lib/cfml" to [basis]. *)

let libdir =
  basis |> option_map (fun basis -> basis ^ "/lib/cfml")

let print_libdir () =
  match libdir with
  | Some libdir ->
      print_endline libdir;
      exit 0
  | None ->
      print_endline "undefined";
      exit 0

