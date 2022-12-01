

(*#########################################################################*)
(* ** Switch for controlling generation (could be moved to a file named Flags.ml) *)

let use_credits = ref false

let use_left_to_right_order = ref false

let generate_deep_embedding = ref false

let generate_encoders = ref false




(*#########################################################################*)

(**************************************************************)
(** Option manipulation functions *)

let option_map f = function
  | None -> None
  | Some x -> Some (f x)

let option_iter f = function
  | None -> ()
  | Some x -> f x

let unsome = function
  | None -> assert false
  | Some v -> v

let list_of_option = function
  | None -> []
  | Some v -> [v]

let option_app d f = function
  | None -> d
  | Some x -> f x

let unsome_safe d = function
  | None -> d
  | Some s -> s

let bool_of_option xo =
   match xo with
   | None -> false
   | Some x -> x


(**************************************************************)
(** List manipulation functions *)

(* TODO: see which functions are now in OCaml stdlib *)
(* let list_make n v =
  List.init n (fun _ -> v) *)

let rec list_make n v =
   if n = 0 then [] else v::(list_make (n-1) v)

let list_mapi f l =
  let rec aux i = function
    | [] -> []
    | h::t -> (f i h)::(aux (i+1) t)
    in
  aux 0 l

let list_nat n = (* for n >= 0 *)
  let rec aux i =
    if i = 0 then [] else (i-1)::(aux (i-1)) in
  List.rev (aux n)

let list_init n f = (* for n >= 0 *)
  let rec aux i =
    if i >= n then [] else (f i)::(aux (i+1)) in
  aux 0

let rec list_separ sep = function
  | [] -> []
  | a::[] -> a::[]
  | a::l -> a::sep::(list_separ sep l)

let rec filter_somes = function
  | [] -> []
  | None::l -> filter_somes l
  | (Some x) :: l -> x :: filter_somes l

let list_unique l =
   let rec aux acc = function
      | [] -> acc
      | a::q ->
         if List.mem a acc then aux acc q else aux (a::acc) q
      in
   aux [] l

let list_intersect l1 l2 =
   List.filter (fun x -> List.mem x l1) l2

let list_minus l1 l2 =
   List.filter (fun t -> not (List.mem t l2)) l1

let list_concat_map f l =
   List.concat (List.map f l)

let list_assoc_option x l =
   try Some (List.assoc x l)
   with Not_found -> None

let rec assoc_list_map f = function
  | [] -> []
  | (k,v)::l -> (k, f v)::(assoc_list_map f l)

let rec list_remove i l = (* i >= 0 *)
   match l with
   | [] -> failwith "list_remove invalid index" (* todo: illegal argument *)
   | x::t -> if i = 0 then t else x::(list_remove (i-1) t)

let rec list_replace i v l = (* i >= 0 *)
   match l with
   | [] -> failwith "list_replace invalid index" (* todo: illegal argument *)
   | x::t -> if i = 0 then v::t else x::(list_replace (i-1) v t)

let list_replace_nth i vs xs =
   list_replace i (List.nth vs i) xs

let list_ksort cmp l =
  List.sort (fun (k1,_) (k2,_) -> cmp k1 k2) l

let list_index k l =
   let rec aux n = function
      | [] -> raise Not_found
      | x::l -> if x = k then n else aux (n+1) l
      in
   aux 0 l

(** [list_is_included l1 l2] returns true if any item in [l1] also belongs to [l2] *)

let list_is_included l1 l2 =
   List.for_all (fun x -> List.mem x l2) l1


(**************************************************************)
(** String manipulation functions *)

let str_cmp (s1:string) (s2:string) =
  if s1 < s2 then -1 else if s1 = s2 then 0 else 1

let str_starts_with p s =
   let n = String.length p in
      String.length s >= n
   && String.sub s 0 n = p

let str_capitalize_1 s =
   if String.length s <= 0 then s else
   let s' = Bytes.of_string s in
   Bytes.set s' 0 (Char.uppercase_ascii s.[0]);
   Bytes.unsafe_to_string s'

let str_capitalize_2 s =
   if String.length s < 2 then s else
   let s' = Bytes.of_string s in
   Bytes.set s' 1 (Char.uppercase_ascii s.[1]);
   Bytes.unsafe_to_string s'


(**************************************************************)
(** File manipulation functions *)

let file_put_contents filename text =
   try
      let handle = open_out filename in
      output_string handle text;
      close_out handle
   with Sys_error s ->
     failwith ("Could not write in file: " ^ filename ^ "\n" ^ s)


(**************************************************************)
(** Try-with manipulation functions *)

let gives_not_found f =
   try ignore (f()); false
   with Not_found -> true


(**************************************************************)
(** Pretty-printing functions *)

let lin0 = ""
let lin1 = "\n"
let lin2 = "\n\n"

let show_list s sep l =
  String.concat sep (List.map s l)

let show_listp s sep l =
  if l = [] then "" else
  sep ^ (String.concat sep (List.map s l))

let show_listq s sep l =
  if l = [] then "" else
  (String.concat sep (List.map s l)) ^ sep

let show_option f ox =
   match ox with
   | None -> ""
   | Some x -> f x

let show_par required s =
  if required then "(" ^ s ^ ")" else s

let show_str s =
  s


(**************************************************************)
(** Error messages *)

let output s =
  Printf.printf "%s\n" s

let unsupported_noloc s =
  failwith ("Unsupported language construction : " ^ s)

let unsupported loc s =
  Location.print_error Format.err_formatter loc;
  unsupported_noloc s

let warning loc s =
  Location.print Format.err_formatter loc;
  Format.fprintf Format.err_formatter "Warning: @[<v 2>%s@]\n" s

exception Not_in_normal_form of Location.t * string

let not_in_normal_form loc s =
   raise (Not_in_normal_form (loc, s))






