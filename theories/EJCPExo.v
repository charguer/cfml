(**

EJCP: hands-on session.

Author: Arthur Charguéraud.
License: MIT.

*)

Set Implicit Arguments.
Generalizable Variables A.
From Sep Require Import Example.
From Sep Require ExampleStack ExampleList.

Implicit Types n m : int.
Implicit Types p q : loc.



(* ####################################################### *)
(** * Basic functions *)

Module ExoBasic.

(** Hints: 
    - [xwp] to begin the proof
    - [xapp] for applications, or [xappn] to repeat
    - [xif] for a case analysis
    - [xval] for a value
    - [xsimpl] to prove entailments
    - [auto], [math], [rew_list] to prove pure facts
      or just [*] after a tactic to invoke automation.
*)


(* ******************************************************* *)
(** ** Basic pure function (warm up) *)

(** 
[[
  let double n =
    n + n
]]
*)

Definition double :=
  VFun 'n :=
    'n '+ 'n.

Lemma Triple_double : forall n,
  TRIPLE (double n)
    PRE \[]
    POST (fun m => (* SOLUTION *) \[m = 2 * n] (* /SOLUTION *)).
Proof using.
  (* SOLUTION *) xwp. xapp. xsimpl. math. (* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Basic imperative function with one argument *)

(** 
[[
  let inplace_double p =
    p := !p + !p
]]
*)

Definition inplace_double :=
  VFun 'p :=
    'p ':= ('!'p '+ '!'p).

Lemma Triple_inplace_double : forall p n,
  TRIPLE (inplace_double p)
    PRE ((* SOLUTION *) p ~~> n (* /SOLUTION *))
    POST (fun (_:unit) => (* SOLUTION *) p ~~> (2 * n) (* /SOLUTION *)).
Proof using.
  (* SOLUTION *) xwp. xapp. xapp. xapp. xapp. xsimpl. math. (* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Basic imperative function with two arguments (white belt) *)

(** 
[[
  let decr_and_incr p q =
    decr p;
    incr q
]]
*)

Definition decr_and_incr :=
  VFun 'p 'q :=
    decr 'p ';
    incr 'q.

Lemma Triple_decr_and_incr : forall p q n m,
  TRIPLE (decr_and_incr p q)
    PRE ((* SOLUTION *) p ~~> n \* q ~~> m (* /SOLUTION *))
    POST ((* SOLUTION *) fun (_:unit) => p ~~> (n-1) \* q ~~> (m+1) (* /SOLUTION *)).
Proof using.





  (* SOLUTION *) xwp. xapp. xapp. xsimpl. (* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** *** A recursive function (yellow belt) *) 

(** Here, we will assume [!p > 0].

[[
  let rec transfer p q =
    if !p > 0 then (
      decr p;
      incr q;
      transfer p q
    )
]]
*)

Definition transfer :=
  VFix 'f 'p 'q :=
    If_ '! 'p '> 0 Then
      decr 'p ';
      incr 'q ';
      'f 'p 'q
    End.

Lemma Triple_transfer : forall p q n m,
  n >= 0 ->
  TRIPLE (transfer p q)
    PRE (p ~~> n \* q ~~> m)
    POST (fun (_:unit) => (* SOLUTION *) p ~~> 0 \* q ~~> (n + m) (* /SOLUTION *)).
Proof using.
  introv N. gen m N. induction_wf IH: (downto 0) n. intros.
  (* SOLUTION *)
  xwp. xapp. xapp. xif ;=> C.
  { xapp. xapp. xapp. { hnf. math. } { math. } 
    xsimpl. math. }
  { xval. xsimpl. math. math. }
  (* /SOLUTION *)
Qed.

End ExoBasic.


(* ####################################################### *)
(** * Stack *)

(** Hints: 
    - [xunfold Stackn] to unfold all
    - [xchange Stackn_eq] to unfold one
    - [xchange <- Stackn_eq] to fold one
    - [xchange (Stackn_eq p)] to unfold the one at pointer [p]
    - [xchange <- (Stackn_eq p)] to fold the one at pointer [p]
    - [xchanges] to invoke [xsimpl] subsequently
*)


Module ExoStack.
Import ExampleStack.Stackn.

(** Recall from [ExampleStack.v]
[[
  type 'a lstack = { data : 'a list; size : int }
]]
*)

(* ******************************************************* *)
(** ** The clear function *) 

(** 
[[
   let clear p =  
     p.data <- [];
     p.size <- 0
]]
*)

Definition clear :=
  VFun 'p :=
    Set 'p'.data ':= ``nil ';
    Set 'p'.size ':= ``0.

Lemma Triple_clear : forall `{Enc A} (p:loc) (L:list A),
  TRIPLE (clear p)
    PRE (p ~> Stackn L)
    POST (fun (u:unit) => p ~> Stackn nil).
Proof using.
  (* SOLUTION *) xwp. xunfold Stackn. xapp. xapp. xsimpl. (* /SOLUTION *)
Qed.

Hint Extern 1 (Register_Spec (clear)) => Provide @Triple_clear.


(* ******************************************************* *)
(** ** The concat function (orange belt)  *) 

(** 
[[
   let concat p1 p2 =
     p1.data <- p1.data @ p2.data;
     p1.size <- p1.size + p2.size;
     clear p2
]]
*)

Definition concat :=
  VFun 'p1 'p2 :=
    Set 'p1'.data ':= (('p1'.data) '++ ('p2'.data)) ';
    Set 'p1'.size ':= (('p1'.size) '+ ('p2'.size)) ';
    clear 'p2.

Lemma Triple_concat : forall `{Enc A} (p1 p2:loc) (L1 L2:list A),
  TRIPLE (concat p1 p2)
    PRE (p1 ~> Stackn L1 \* p2 ~> Stackn L2)
    POST (fun (u:unit) => (* SOLUTION *) p1 ~> Stackn (L1 ++ L2) \* p2 ~> Stackn nil (* /SOLUTION *)).
Proof using.
  (* SOLUTION *) 
  xwp. xunfold Stackn. xapp. xapp. xapp. xapp. xapp. xapp. xapp.
  xapp. xchange <- (Stackn_eq p1). { rew_listx. auto. }
  xchange <- (Stackn_eq p2). xapp. xsimpl. 
  (* /SOLUTION *)
Qed.

End ExoStack.


(* ####################################################### *)
(** * Mutable lists *)

(** Hints: 
    - [xchange MList_eq] and the variants like for [Stackn]
    - [xchange (MList_not_nil p)] to unfold [p ~> MList L] when [L <> nil]
    - [xchange MList_cons] to unfold [p ~> MList (x::L)] 
      into [\exists q, p ~~> Cons x q \* q ~> MList L]
    - [xchange <- MList_cons] to fold back to [p ~> MList (x::L)]
    - [xchange <- (MList_cons p)], like the above for a specific [p]
    - [xchanges] is convenient here too.
*)

Module ExoList.
Import ExampleList.MList.


(* ******************************************************* *)
(** ** Create one element *)

(**
[[
  let mk_one x =
    mk_cons x (create())
]]
*)

Definition mk_one : val :=
  VFun 'x :=
     mk_cons 'x (create '()).

Lemma Triple_mk_one : forall A `{EA:Enc A} (x:A),
  TRIPLE (mk_one ``x)
    PRE \[]
    POST (fun p => p ~> MList (x::nil)).
Proof using.
  (* SOLUTION *) intros. xwp. xapp ;=> q. xapp. xsimpl. (* /SOLUTION *)
Qed.

Hint Extern 1 (Register_Spec (mk_one)) => Provide @Triple_mk_one.


(* ******************************************************* *)
(** ** Push back using append *)

(** Note: [L&x] is a notation for [L++x::nil]. *)

(**
[[
  let push_back p x =
    inplace_append p (mk_one x)
]]
*)

(** Recall:
[[
  TRIPLE (inplace_append p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (_:unit) => p1 ~> MList (L1++L2)).
]]
*)

Definition push_back : val :=
  VFun 'p 'x :=
    inplace_append 'p (mk_one 'x).

Lemma Triple_push_back : forall `{EA:Enc A} (L:list A) (x:A) (p:loc),
  TRIPLE (push_back ``p ``x)
    PRE (p ~> MList L)
    POST (fun (_:unit) => p ~> MList (L++x::nil)).
Proof using.
  (* SOLUTION *) xwp. xapp ;=> q. xapp. xsimpl. (* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Push back not using append (blue belt) *)

(** Hint: the following function is a specialization of 
    [inplace_append] for the case where the second list
    consists of a single element. Its proof is similar. *)

(**
[[
  let rec push_back' p x =
    if is_empty p 
      then set_cons p x (create())
      else push_back' (tail p) x
]]
*)

Definition push_back' : val :=
  VFix 'f 'p 'x :=
    If_ is_empty 'p 
      Then set_cons 'p 'x (create '())
      Else 'f (tail 'p) 'x.

Lemma Triple_push_back' : forall `{EA:Enc A} (L:list A) (x:A) (p:loc),
  TRIPLE (push_back' ``p ``x)
    PRE (p ~> MList L)
    POST (fun (_:unit) => p ~> MList (L++x::nil)).
Proof using.
  intros. gen p. induction_wf IH: (@list_sub A) L. intros.
  (* SOLUTION *) 
  xwp. xif ;=> C. 
  { subst. xchanges (MList_eq p) ;=> v1.
    xapp ;=> q. xapp. xchanges <- (MList_cons p). }
  { xchanges~ (MList_not_nil p) ;=> y L' p' ->.
    xapp. xapp. { auto. } xchanges <- MList_cons. }
  (* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Pop back (brown belt) *)

(**
[[
  let rec pop_back p =
    if is_empty (tail p) then (
      let x = head p in
      set_nil p;
      x 
    ) else (
      pop_back (tail p)
    )
]]
*)

Definition pop_back : val :=
  VFix 'f 'p :=
    If_ is_empty (tail 'p) Then (
      Let 'x := head 'p in
      set_nil 'p ';
      'x
    ) Else (
      'f (tail 'p)
    ).

Lemma Triple_pop_back : forall `{EA:Enc A} (L:list A) (p:loc),
  L <> nil ->
  TRIPLE (pop_back ``p)
    PRE (p ~> MList L)
    POST (fun x => \exists L1, \[L = L1++x::nil] \* p ~> MList L1).
Proof using.
  introv. gen p. induction_wf IH: (@list_sub A) L. introv N.
  (* SOLUTION *) 
  xwp. destruct L as [|x L']; tryfalse. xchange MList_cons ;=> p'.
  xapp. xapp. xif ;=> C.
  { subst. xapp. xapp. xval. xsimpl (@nil A). { rew_list. auto. }
    xchanges <- MList_nil. }
  { xapp. xapp. { auto. } { auto. } intros y L1' ->.
    xsimpl (x::L1'). { rew_list. auto. } xchanges <- MList_cons. } 
  (* /SOLUTION *)
Qed.


(* ******************************************************* *)
(** ** Reversed copy using iter (black belt) *)

(** Hints: 
    - [xfun] to substitute a function definition in its occurences
    - [xapp (>> __ E)] to provide [E] as argument to the specification
      lemma that [xapp] would apply.
    - The proof has a similar pattern to [length_using_iter].
*)

(**
[[
  let rec reversed_copy p =
    let q = create() in
    iter (fun x => push q x) p;
    q
]]
*)

Definition reversed_copy : val :=
  VFun 'p :=
    Let 'q := create '() in
    iter (Fun 'x := push 'q 'x) 'p ';
    'q.

Lemma Triple_reversed_copy : forall A `{EA:Enc A} (L:list A) (p:loc),
  TRIPLE (reversed_copy ``p)
    PRE (p ~> MList L)
    POST (fun q => p ~> MList L \* q ~> MList (rev L)).
Proof using.
  (* SOLUTION *) 
  xwp. xapp ;=> q. xfun.
  xapp (>> __ (fun (K:list A) => q ~> MList (rev K))).
  { intros x K L' E. xwp. xapp. xsimpl*. }
  xval. xsimpl~.
  (* /SOLUTION *)
Qed.

End ExoList.


