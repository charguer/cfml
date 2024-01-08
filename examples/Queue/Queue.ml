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
