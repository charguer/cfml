type 'a queue = {
  mutable front: 'a MList.mlist;
  mutable rear : 'a MList.mlist;
  mutable size : int;
}

let create () = {
  front = ref MList.Nil;
  rear = ref MList.Nil;
  size = 0;
}

let is_empty q = q.size = 0

let push x q =
  if is_empty q then begin
    let l = MList.create () in
    MList.push l x;
    q.front <- l end
  else
    MList.push q.rear x;
  q.size <- q.size + 1

let pop q =
  let x = match !(q.front) with
    | MList.Nil -> assert false
    | MList.Cons (x, r) ->
      if MList.is_empty r then begin
        q.front <- MList.rev_main q.rear;
        q.rear <- MList.create ();
        x end
      else MList.pop q.front in
  q.size <- q.size - 1;
  x

let rec transfer q1 q2 =
  if not (is_empty q1) then begin
    let x = pop q1 in
    push x q2;
    transfer q1 q2
  end
