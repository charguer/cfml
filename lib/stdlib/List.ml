
(* TODO INCLUDE?

let hd = function
  | [] -> assert false
  | a::l -> a

let tl = function
  | [] -> assert false
  | a::l -> l

*)

let length l =
   let rec aux len = function
     | [] -> len
     | a::l -> aux (len + 1) l
     in
  aux 0 l

let nth l n =
  assert (n >= 0);
  let rec aux l n =
    match l with
    | [] -> assert false
    | a::l -> if n = 0 then a else aux l (n - 1)
    in
  aux l n


let append l1 l2 =
  let rec aux = function
    | [] -> l2
    | a::l -> a::(aux l)
    in
  aux l1

let (@) = append

let rec rev_append l1 l2 =
  match l1 with
  | [] -> l2
  | a :: l -> rev_append l (a :: l2)

let rev l =
  rev_append l []

let rec concat = function
  | [] -> []
  | l::r -> l @ concat r


let rec iter f = function
  | [] -> ()
  | a::l -> f a; iter f l


let iteri f l =
   let rec aux i = function
     | [] -> ()
     | a::l -> f i a; aux (i + 1) l
   in
   aux 0 l

let rec map f = function
  | [] -> []
  | a::l ->
     let r = f a in
     r :: map f l

let mapi f l =
   let rec aux i = function
     | [] -> []
     | a::l ->
        let r = f i a in
        r :: aux (i + 1) l
   in
   aux 0 l

(* TODO INCLUDE?
let rev_map f l =
  let rec rmap_f acc = function
    | [] -> acc
    | a::l -> rmap_f (f a :: acc) l
  in
  rmap_f [] l
*)

let rec fold_left f acc l =
  match l with
  | [] -> acc
  | a::l -> fold_left f (f acc a) l

let rec fold_right f l acc =
  match l with
  | [] -> acc
  | a::l -> f a (fold_right f l acc)


let rec for_all p = function
  | [] -> true
  | a::l -> p a && for_all p l

let rec exists p = function
  | [] -> false
  | a::l -> p a || exists p l

exception Find_not_found

let rec find p = function
  | [] -> raise Find_not_found
  | a::l -> if p a then a else find p l

let filter p l =
  let rec aux acc = function
     | [] -> rev acc
     | a::l -> if p a then aux (a::acc) l else aux acc l
     in
  aux [] l

let partition p l =
  let rec aux yes no = function
     | [] -> (rev yes, rev no)
     | x :: l ->
         if p x
            then aux (x :: yes) no l
            else aux yes (x :: no) l
     in
  aux [] [] l

let rec split = function
  | [] -> ([], [])
  | (x,y)::l ->
      let (rx, ry) = split l in
      (x::rx, y::ry)

let rec combine l1 l2 =
  match (l1, l2) with
  | ([], []) -> []
  | (a1::l1, a2::l2) -> (a1, a2) :: (combine l1 l2)
  | (_, _) -> assert false


let take n l =
  assert (n >= 0);
  let rec aux n l =
     if n = 0 then [] else begin
        match l with
        | [] -> assert false
        | a::l -> a::(aux (n-1) l)
     end
     in
  aux n l

let drop n l =
  assert (n >= 0);
  let rec aux n l =
     if n = 0 then l else begin
        match l with
        | [] -> assert false
        | a::l -> aux (n-1) l
     end
     in
  aux n l

let split_at n l =
  assert (n >= 0);
  let rec aux n l =
     if n = 0 then ([], l) else begin
        match l with
        | [] -> assert false
        | a::l ->
           let (l1,l2) = aux (n-1) l in
           (a::l1,l2)
     end
     in
  aux n l


(************************************************************)
(* LATER  move into a separate List2 file


  let rec for_all2 p l1 l2 =
    match (l1, l2) with
      ([], []) -> true
    | (a1::l1, a2::l2) -> p a1 a2 && for_all2 p l1 l2
    | (_, _) -> invalid_arg "List.for_all2"

  let rec exists2 p l1 l2 =
    match (l1, l2) with
      ([], []) -> false
    | (a1::l1, a2::l2) -> p a1 a2 || exists2 p l1 l2
    | (_, _) -> invalid_arg "List.exists2"


  let rec map2 f l1 l2 =
    match (l1, l2) with
      ([], []) -> []
    | (a1::l1, a2::l2) -> let r = f a1 a2 in r :: map2 f l1 l2
    | (_, _) -> invalid_arg "List.map2"

  let rev_map2 f l1 l2 =
    let rec rmap2_f acc l1 l2 =
      match (l1, l2) with
      | ([], []) -> acc
      | (a1::l1, a2::l2) -> rmap2_f (f a1 a2 :: acc) l1 l2
      | (_, _) -> invalid_arg "List.rev_map2"
    in
    rmap2_f [] l1 l2
  ;;

  let rec iter2 f l1 l2 =
    match (l1, l2) with
      ([], []) -> ()
    | (a1::l1, a2::l2) -> f a1 a2; iter2 f l1 l2
    | (_, _) -> invalid_arg "List.iter2"

  let rec fold_left2 f acc l1 l2 =
    match (l1, l2) with
      ([], []) -> acc
    | (a1::l1, a2::l2) -> fold_left2 f (f acc a1 a2) l1 l2
    | (_, _) -> invalid_arg "List.fold_left2"

  let rec fold_right2 f l1 l2 acc =
    match (l1, l2) with
      ([], []) -> acc
    | (a1::l1, a2::l2) -> f a1 a2 (fold_right2 f l1 l2 acc)
    | (_, _) -> invalid_arg "List.fold_right2"
*)
