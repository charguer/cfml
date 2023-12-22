open Transtack

let default = 0

let main () =
  (* EStack demo *)
  let e = ecreate default in
  epush e 1;
  epush e 2;
  let x = epop e in
  assert (x=2);

  (* PStack demo *)
  let p0 = pcreate default in
  let p1 = ppush p0 1 in
  let p2 = ppush p1 2 in
  let p3,x = ppop p2 in
  assert (x=2);
  let p4 = ppush p1 3 in
  let p5,x = ppop p4 in
  assert (x=3);

  (* Conversion estack_to_pstack demo *)
  let pe = estack_to_pstack e in (* e is lost *)
  let pe1,x = ppop pe in
  assert (x=1);
  let pe2,x = ppop pe in
  assert (x=1);

  (* Conversion pstack_to_estack demo *)
  let ep = pstack_to_estack p2 in (* p2 is unmodified *)
  epush ep 4;
  epush ep 5;
  let p3,x = ppop p2 in (* p2 was not affected *)
  assert (x=2);
  let pep = estack_to_pstack ep in
  let _,x = ppop pep in
  assert (x=5)
