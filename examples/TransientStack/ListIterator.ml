type 'a t = 'a list ref

let of_list l =
  ref l

let finished it =
  match !it with
  | [] -> true
  | _ -> false

let get it =
  match !it with
  | [] -> assert false
  | x::_ -> x

let get_and_move it =
  match !it with
  | [] -> assert false
  | x::xs ->
     it := xs;
     x

let move it =
  ignore (get_and_move it)
