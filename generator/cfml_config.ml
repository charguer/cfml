open Mytools

(* This code first defines [basis] in the following manner.

   Method 1. Use the full path to this executable file, ".../bin/cfml/cfmlc",
             and keep only the prefix "...".

   Method 2. Execute the command [opam config var prefix]. *)

let basis : string option =
  (* Method 1. *)
  match Filename.chop_suffix_opt ~suffix:"/bin/cfml/cmlfc" Sys.argv.(0) with
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
