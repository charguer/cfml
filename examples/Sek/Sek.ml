
(** Simplified version of the Sek library (available on opam)
    by Arthur Charguéraud and François Pottier, with contributions
    by Emilie Guermeur. *)

type 'a chunk = {
  mutable data : 'a array;
  mutable size : int;
  default : 'a;
}

type 'a pchunk = {
  support : 'a chunk;
  mutable view_size : int;
  version : int;
}

type 'a pstack = {
  pfront : 'a pchunk;
  ptail : 'a pchunk list;
  pversion_max : int;
}

type 'a stack = {
  mutable front : 'a chunk;
  mutable tail : 'a pchunk list;
  version_owned : int;
}

let capacity = 16

(* Auxiliary functions *)

let empty_chunk d =
  { data = Array.make capacity d;
    size = 0;
    default = d; }

let empty_pchunk d =
  { support = empty_chunk d;
    view_size = 0;
    version = 0; }

let chunk_of_pchunk p =
  let d = p.support.default in
  let t = Array.init capacity (fun i ->
    if i < p.view_size then p.support.data.(i) else d) in
  { data = t;
    size = p.view_size;
    default = d; }

let chunk_push c x =
  c.data.(c.size) <- x;
  c.size <- c.size + 1

(* Conversion functions *)

let persistent_to_ephemeral s =
  { front = chunk_of_pchunk s.pfront;
    tail = s.ptail;
    version_owned = s.pversion_max + 1; }

let ephemeral_to_persistent s =
  { pfront = { support = s.front;
                view_size = s.front.size;
                version = s.version_owned; };
    ptail = s.tail;
    pversion_max = s.version_owned; }

(* Ephemeral operations *)

let empty d =
  { front = empty_chunk d;
    tail = [];
    version_owned = 0; }

let push s x =
  if s.front.size = capacity then begin
    let p = { support = s.front;
               view_size = capacity;
               version = s.version_owned; } in
    s.tail <- p :: s.tail;
    s.front <- empty_chunk s.front.default;
  end;
  chunk_push s.front x

let pop s =
  let n = s.front.size in
  if n = 0 then raise Not_found;
  let n' = n - 1 in
  s.front.size <- n';
  let x = s.front.data.(n') in
  s.front.data.(n') <- s.front.default;
  if n' = 0 then begin
    match s.tail with
    | [] -> ()
    | p::ps ->
        s.tail <- ps;
        s.front <- if p.version = s.version_owned
                      then p.support
                      else chunk_of_pchunk p
  end;
  x

(* Persistent operations *)

let pempty d =
  { pfront = empty_pchunk d;
     ptail = [];
     pversion_max = 0; }

let ppush s x =
  if s.pfront.view_size = capacity then begin
    let c = empty_chunk s.pfront.support.default in
    chunk_push c x;
    let p = { support = c;
               view_size = 1;
               version = 0; } in
    { s with pfront = p;
             ptail = s.pfront :: s.ptail }
  end else begin
    let p = s.pfront in
    let n = p.view_size in
    if n = p.support.size then begin
      chunk_push p.support x;
      let p' = { p with view_size = n+1 } in
      { s with pfront = p' }
    end else begin
      let c = chunk_of_pchunk p in
      chunk_push c x;
      let p' = { support = c;
                 view_size = n+1;
                 version = 0; } in
      { s with pfront = p' }
    end
end

let ppop s =
  let n = s.pfront.view_size in
  if n = 0 then raise Not_found;
  let n' = n - 1 in
  let x = s.pfront.support.data.(n') in
  let p' = { s.pfront with view_size = n' } in
  let s' =
    if n' > 0 then
      { s with pfront = p' }
    else
      match s.ptail with
      | [] -> { s with pfront = p' }
      | p::ps -> { s with pfront = p; ptail = ps }
    in
  (s',x)

(* Test *)

let nb = 1000

let _ =
  let s = empty 0 in
  for i = 0 to nb-1 do
    push s i;
  done;
  for i = nb-1 downto 0 do
    let x = pop s in
    assert (x = i);
  done

let _ =
  let s = ref (pempty 0) in
  for i = 0 to nb-1 do
    s := ppush !s i;
  done;
  for i = nb-1 downto 0 do
    let (s2,x) = ppop !s in
    s := s2;
    assert (x = i);
  done
