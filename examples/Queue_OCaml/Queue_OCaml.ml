exception Empty

type 'a cell_contents = { content: 'a; mutable next: 'a cell; }
and 'a cell =
  | Nil
  | Cons of 'a cell_contents

type 'a t = {
  mutable length: int;
  mutable first: 'a cell;
  mutable last: 'a cell
}

let create () = {
  length = 0;
  first = Nil;
  last = Nil
}

let clear q =
  q.length <- 0;
  q.first <- Nil;
  q.last <- Nil

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

let push = add

let take q =
  match q.first with
  | Nil -> raise Empty
  | Cons c ->
    if c.next = Nil then
      (* queue contains a single element *)
      clear q
    else begin
      (* queue contains at least two elements *)
      q.length <- q.length - 1;
      q.first <- c.next end;
    c.content

let pop = take

let rec copy_aux q_res prev cell =
  match cell with
  | Nil -> q_res.last <- prev; q_res
  | Cons c ->
    let res = Cons { content = c.content; next = Nil } in
    begin match prev with
      | Nil -> q_res.first <- res
      | Cons p -> p.next <- res
    end;
    copy_aux q_res res c.next

let copy =
  fun q -> copy_aux { length = q.length; first = Nil; last = Nil } Nil q.first

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
