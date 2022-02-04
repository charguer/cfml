(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*         Francois Pottier, projet Cristal, INRIA Rocquencourt           *)
(*                  Jeremie Dimino, Jane Street Europe                    *)
(*                                                                        *)
(*   Copyright 2002 Institut National de Recherche en Informatique et     *)
(*     en Automatique.                                                    *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

exception Empty

type 'a cell_fields = { content: 'a; mutable next: 'a cell; }
and 'a cell =
  | Nil
  | Cons of 'a cell_fields

(* @ predicate is_cell (s: 'a seq) (from to: 'a cell) =
      if from = to then s = empty
      else
        let Cons { content = v; next = n } = from in (* user-provided *)

        (* let Cons { content = v; loc = l } = from in (\* tool-translated, type-directed *\)
         * own { next = n; } = l in
           l ~> { next = n; } *)

        v = s[0] && Seq.length s > 0 &&
        is_cell s[1 ..] n to
*)

type 'a t = {
  mutable length: int;
  mutable first: 'a cell;
  mutable last: 'a cell
  (* @ mutable model view: 'a seq *)
  (* @ mutable model valid: bool *)
} (* @ invariant
        valid ->
        let s = view in
        let n = Seq.length s in
        length = n &&
        if n = 0 then last = first = Nil
        else is_cell s[.. n - 1] first last &&
             let Cons { content = necessarily s[n - 1]; next = Nil } = last in
             true *)

let create () = {
  length = 0;
  first = Nil;
  last = Nil;
  (* @ view = empty;
      valid = true *)
}
(* @ q = create ()
      ensures q.view = empty && q.valid *)

let clear q =
  q.length <- 0;
  q.first <- Nil;
  q.last <- Nil
  (* @ q.view <- empty;
      q.valid <- true *)
(* @ clear q
      (* does not require q.valid *)
      ensures q.view = empty && q.valid *)

let add x q =
  let cell = Cons {
    content = x;
    next = Nil
  } in
  match q.last with
  | Nil ->
    q.length <- 1;
    q.first <- cell;
    q.last <- cell
  | Cons last ->
    q.length <- q.length + 1;
    last.next <- cell;
    q.last <- cell

let push =
  add

let peek q =
  match q.first with
  | Nil -> assert false
  | Cons { content } -> content

let peek_opt q =
  match q.first with
  | Nil -> None
  | Cons { content } -> Some content

let top =
  peek

let take q =
  match q.first with
  | Nil -> assert false
  | Cons { content; next = Nil } ->
    clear q;
    content
  | Cons { content; next } ->
    q.length <- q.length - 1;
    q.first <- next;
    content

(***

let take_opt q =
  match q.first with
  | Nil -> None
  | Cons { content; next = Nil } ->
    clear q;
    Some content
  | Cons { content; next } ->
    q.length <- q.length - 1;
    q.first <- next;
    Some content

let pop =
  take

let copy =
  let rec copy q_res prev cell =
    match cell with
    | Nil -> q_res.last <- prev; q_res
    | Cons { content; next } ->
      let res = Cons { content; next = Nil } in
      begin match prev with
      | Nil -> q_res.first <- res
      | Cons p -> p.next <- res
      end;
      copy q_res res next
  in
  fun q -> copy { length = q.length; first = Nil; last = Nil } Nil q.first

let is_empty q =
  q.length = 0

let length q =
  q.length

let iter =
  let rec iter f cell =
    match cell with
    | Nil -> ()
    | Cons { content; next } ->
      f content;
      iter f next
  in
  fun f q -> iter f q.first

let fold =
  let rec fold f accu cell =
    match cell with
    | Nil -> accu
    | Cons { content; next } ->
      let accu = f accu content in
      fold f accu next
  in
  fun f accu q -> fold f accu q.first

let transfer q1 q2 =
  if q1.length > 0 then
    match q2.last with
    | Nil ->
      q2.length <- q1.length;
      q2.first <- q1.first;
      q2.last <- q1.last;
      clear q1
    | Cons last ->
      q2.length <- q2.length + q1.length;
      last.next <- q1.first;
      q2.last <- q1.last;
      clear q1

(** {1 Iterators} *)

let to_seq q =
  let rec aux c () = match c with
    | Nil -> Seq.Nil
    | Cons { content=x; next; } -> Seq.Cons (x, aux next)
  in
  aux q.first

let add_seq q i = Seq.iter (fun x -> push x q) i

let of_seq g =
  let q = create() in
  add_seq q g;
  q

 ***)
