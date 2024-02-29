
type 'a contents = Nil | Cons of 'a * 'a mlist
and 'a mlist = ('a contents) ref

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

let rec copy p =
  match !p with
  | Nil -> ref Nil
  | Cons (x, q) ->
      let ll = copy q in
      ref (Cons (x, ll))

let rec rev_aux acc l =
  match !l with
  | Nil -> acc
  | Cons(x, r) ->
    let k = !r in
    r := !acc;
    rev_aux l (ref k)

let rev_main p =
  rev_aux (ref Nil) p

let rec cmp (eq: 'a -> 'a -> bool) l1 l2 =
  match !l1, !l2 with
  | Nil, Nil -> true
  | Cons (_, _), Nil | Nil, Cons (_, _) -> false
  | Cons (x1, xs1), Cons (x2, xs2) ->
      eq x1 x2 && cmp eq xs1 xs2

let is_null p =
  match !p with
  | Nil -> true
  | _ -> false

let rec fold_mleft f acc p =
  match !p with
  | Nil -> acc
  | Cons (x, q) -> fold_mleft f (f acc x) q

let rec iter f p =
  match !p with
  | Nil -> ()
  | Cons (x, q) -> f x; iter f q

let test_iter (l: int mlist) =
  let c = ref 0 in
  iter (fun _ -> c := !c + 1) l;
  !c
