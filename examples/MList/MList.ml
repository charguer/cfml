
type 'a contents = Nil | Cons of 'a * 'a mlist
and 'a mlist = ('a contents) ref


(* open Format *)

(* let rec pp_contents fmt p = match !p with *)
(*   | Nil -> fprintf fmt "nil@." *)
(*   | Cons (x, r) -> fprintf fmt "@[%d; %a@]" x pp_contents r *)

let is_empty p =
  match !p with
  | Nil -> true
  | Cons (x,q) -> false

let create () =
  ref Nil

let push p x =
  let q = ref !p in
  p := Cons (x, q)

let pop p =
  match !p with
  | Nil -> assert false
  | Cons (x,q) -> p := !q; x

let rec rev_aux acc l =
  match !l with
  | Nil -> acc
  | Cons(x, r) ->
    let k = !r in
    r := !acc;
    rev_aux l (ref k)

let rev_main p =
  rev_aux (ref Nil) p

(* let rec rev_aux q p = *)
(*   match !p with *)
(*   | Nil -> eprintf "end: %a@." pp_contents q; q *)
(*   | Cons (x,p2) -> *)
(*       eprintf "q again: %a@." pp_contents q; *)
(*       eprintf "p2 again: %a@." pp_contents p2; *)
(*       eprintf "here@."; *)
(*       let p3 = ref !p2 in *)
(*       eprintf "p3 again: %a@." pp_contents p3; *)
(*       p2 := !q; *)
(*       (\* eprintf "p3 again: %a@." pp_contents p3; *\) *)
(*       eprintf "hey p2: %a@." pp_contents p2; *)
(*       (\* eprintf "p3: %a@." pp_contents p3; *\) *)
(*       rev_aux p2 p3 *)

(* let rev p = *)
(*   rev_aux (ref Nil) p *)

(* let () = *)
(*   let l3 = ref (Cons (3, ref Nil)) in *)
(*   let l2 = ref (Cons (2, l3)) in *)
(*   let l1 = ref (Cons (1, l2)) in *)
(*   eprintf "%a@." pp_contents l1; *)
(*   let l = rev l1 in *)
(*   eprintf "%a@." pp_contents l *)
(*   (\* let l1 = Cons (1, Cons (2, Cons (3,  *\) *)
