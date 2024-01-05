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
