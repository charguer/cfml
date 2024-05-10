
(** Same examples as in the first chapter of the course
    Separation Logic Foundations
    https://softwarefoundations.cis.upenn.edu/slf-current/Basic.html *)

let create (v: int) =
  ref v

let swap r1 r2 =
  let tmp = !r1 in
  r1 := !r2;
  r2 := tmp

let incr r =
  r := !r + 1

let example_let n =
  let a = n+1 in
  let b = n-1 in
  a + b

let quadruple n =
  let m = n + n in
  m + m

let inplace_double p =
  let n = !p in
  let m = n + n in
  p := m

let incr_two p q =
  incr p;
  incr q

let aliased_call p =
  incr_two p p

let incr_first p q =
  incr p

let transfer p q =
  let n = !p in
  let m = !q in
  let s = n + m in
  p := s;
  q := 0

let ref_greater p =
  let n = !p in
  let m = n + 1 in
  ref m

let succ_using_incr n =
  let p = ref n in
  incr p;
  ! p

let get_and_free p =
  let v = !p in
  v

let rec factorec n =
  if n <= 1
    then 1
    else n * factorec (n-1)

let rec repeat_incr p m =
  if m > 0 then begin
    incr p;
    repeat_incr p (m - 1)
  end

let rec step_transfer p q =
  if !q > 0 then begin
    incr p;
    decr q;
    step_transfer p q
  end
