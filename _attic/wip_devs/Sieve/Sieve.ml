
(* Compute primes in the range [0,n), for n > 1 *)


(* Erathostenes *)

let sieve n =
  let t = Array.make n true in
  t.(0) <- false;
  t.(1) <- false;
  let i = ref 2 in
  while !i < n do
    if t.(!i) then begin
      let r = ref !i in
      while !r * !i < n do
        t.(!r * !i) <- false;
        incr r;
      done;
    end;
    incr i;
  done;
  t


let sieve_chains n =
  let t = Array.make n true in
  t.(0) <- false;
  t.(1) <- false;
  let prev = Array.init (n+1) (fun i -> i-1) in
  let next = Array.init (n+1) (fun i -> i+1) in
  let remove k =
    assert(t.(k));
    t.(k) <- false;
    let pnext = next.(k) in
    let pprev = prev.(k) in
    next.(pprev) <- pnext;
    prev.(pnext) <- pprev;
    in
  let i = ref 2 in
  while !i < n do
    if t.(!i) then begin
      let r = ref !i in
      while !r * !i < n do (* débordement avec n/i hors boucle *) (* t.(r * i) <- false; r := next !r done; *)
   
        let m = ref (!r * !i) in
        while !m < n && t.(!m) do
          remove !m;
          m := !m * !i;
        done;
        r := next.(!r);
      done;

(*deuxième boucle : 
  r:= i *i
  while !r < n
    if not t.(r) then
      remove (r);
    r = next r 
  done
*)


    end;
    incr i; (* utiliser next *)
  done;
  t

(* tableau avec que les entiers premiers *)
(* suppression via abstraction liste chaînée *)


let show t =
  Array.iteri (fun i v -> if v then Printf.printf "%d " i) t;
  print_newline()

let demo1 = 
  let n = 100 in
  let t = sieve n in
  show t; 
  print_newline()

let demo2 = 
  let n = 100000000 in
  let _t = sieve_chains n in
  print_string "done"; 
  print_newline()

let demo3 = 
  let n = 100000 in
  let x = Array.fold_left (fun acc v -> acc + (if v then 1 else 0)) 0 (sieve n) in
  let y = Array.fold_left (fun acc v -> acc + (if v then 1 else 0)) 0 (sieve_chains n) in
  Printf.printf "%d\n%d\n" x y


(*
https://github.com/aistun/EulerSieve
http://toccata.lri.fr/gallery/euler_sieve.en.html
*)



