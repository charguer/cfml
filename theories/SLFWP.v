
Lemma flocal_elim : forall F H Q,
  H ==> wp t Q' \* (Q' \--* (Q \*+ \GC)) ->
  H ==> wp t Q.
Proof using. introv L M. lets N: (L Q). applys* himpl_trans N. Qed.





  prove1: 
    F Q ==> mklocal F Q
    (take Q1 = Q)

  prove 2:
    (mkflocal (mkflocal F)) Q := mkflocal F
    right-to-left : instance of (1)
    left-to-right: ...

    (mkflocal (mkflocal F)) Q
  = \exists Q1, mkflocal F Q1 \* (Q1 \--* (Q \*+ \GC))
  = \exists Q1, (\exists Q2, F Q2 \* (Q2 \--* (Q1 \*+ \GC))) \* (Q1 \--* (Q \*+ \GC))
  = \exists Q1 Q2, F Q2 \* (Q2 \--* (Q1 \*+ \GC) \* (Q1 \--* (Q \*+ \GC))
  = \exists Q1 Q2, F Q2 \* (Q2 \--* (Q1 \*+ \GC) \* ((Q1 \*+ \GC) \--* ((Q \*+ \GC) \*+ \GC))
  ==> \exists Q1 Q2, F Q2 \* (Q2 \--* (Q1 \*+ \GC) \* ((Q1 \*+ \GC) \--* (Q \*+ \GC \*+ \GC))
  = \exists Q1 Q2, F Q2 \* (Q2 \--* (Q \*+ \GC \*+ \GC))
  = \exists Q2, F Q2 \* (Q2 \--* (Q \*+ \GC))
  = mkflocal F


  mkflocal F Q := \exists Q1, F Q1 \* (Q1 \--* (Q \*+ \GC)).

  \exists Q1, F Q1 \* (Q1 \--* (Q \*+ \GC)) ==> F Q


  F Q1 \* (Q1 \--* (Q \*+ \GC)) ==> F Q



  wp t Q1 \* (Q1 \--* (Q \*+ \GC)) ==> wp t Q


  H ==> wp t Q1 \* (Q1 \--* (Q \*+ \GC)) ->
  H ==> wp t Q.


let H1 := wp t Q1
let H2 := (Q1 \--* (Q \*+ \GC)) 


  H ==> H1 \* H2 ->
  H1 ==> wp t Q1 ->
  Q1 \* H2 ==> Q \*+ \GC ->
  H ==> wp t Q.


  H ==> H1 \* H2 ->
  triple t H1 Q1 ->
  Q1 \* H2 ==> Q \*+ \GC ->
  triple t H Q


reciprocally, with 
   forall Q1,   wp t Q1 \* (Q1 \--* (Q \*+ \GC)) ==> wp t Q
we can simulate frame


  H ==> H1 \* H2 ->
  H1 ==> wp t Q1 ->
  Q1 \* H2 ==> Q \*+ \GC ->
  H ==> wp t Q.

exploit fact

  H ==> H1 \* H2 ->
  H1 ==> wp t Q1 ->
  Q1 \* H2 ==> Q \*+ \GC ->
  H ==> wp t Q1 \* (Q1 \--* (Q \*+ \GC))

suffices (hchange 1 and 2)

  H1 \* H2 ==> wp t Q1 \* (Q1 \--* (Q \*+ \GC))
  wp t Q1 \* H2 ==> wp t Q1 \* (Q1 \--* (Q \*+ \GC))
  H2 ==> (Q1 \--* (Q \*+ \GC))

done.




-------


Definition wpgen_fail : formula := fun Q =>
  \[False].

Definition wpgen_val (v:val) : formula := fun Q =>
  Q v.

Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := fun Q =>
  F1 (fun X => F2of X Q).

Definition wpgen_seq (F1 F2:formula) : formula := fun Q =>
  F1 (fun X => F2 Q).

Definition wpgen_app (t1:trm) (t2:trm) : formula := fun Q =>  
  wp (trm_app t1 t2) Q.

Definition wpgen_if_val (v:val) (F1 F2:formula) : formula := fun Q =>
  \exists (b:bool), \[v = val_bool b] \* (if b then F1 Q else F2 Q).

Definition wpgen_if (F0 F1 F2:formula) : formula :=
  wpgen_let F0 (fun v => wpgen_if_val v F1 F2).

Fixpoint wpgen (t:trm) : formula :=
  match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpgen_fail
  | trm_fun x t1 => wpgen_val (val_fun x t1)
  | trm_fix f x t1 => wpgen_val (val_fix f x t1)
  | trm_if t0 t1 t2 => wpgen_if (wpgen t0) (wpgen t1) (wpgen t2)
  | trm_let x t1 t2 => wpgen_let (wpgen t1) (fun X => wpgen (subst x X t2))
  | trm_app t1 t2 => wgpen_app t1 t2
  end.


Lemma wpgen_himpl_wp : forall t Q,
  H ==> wpgen t Q ->
  triple t H Q.

  H ==> wp t Q ->
  triple t H Q.

  H ==> wpgen t Q ->
  H ==> wp t Q ->

  wpgen t Q ==> wp t Q.

(in details)

then derive

  Lemma triple_of_wpgen : forall t Q,
    H ==> wpgen t Q ->
    triple t H Q.




Lemma wpgen_himpl_wp : forall t Q,
  wpgen t Q ==> wp t Q.

Definition wpgen_sound_for t := forall Q,
  wpgen t Q ==> wp t Q.

wpgen_sound_for (trm_val v)
wpgen_sound_for (trm_fun x t).
wpgen_sound_for (trm_fix f x t).
..



--------






Definition wpgen_fail : formula := mkflocal (fun Q =>
  \[False]).

Definition wpgen_val (v:val) : formula := mkflocal (fun Q =>
  Q v).

Definition wpaux_var (E:ctx) (x:var) : formula :=
  match Ctx.lookup x E with
  | None => wpgen_fail
  | Some v => wpgen_val v
  end.

Definition wpgen_let (F1:formula) (F2of:val->formula) : formula := mkflocal (fun Q =>
  F1 (fun X => F2of X Q)).

Definition wpgen_seq (F1 F2:formula) : formula := mkflocal (fun Q =>
  F1 (fun X => F2 Q)).

Definition wpgen_app (t1:trm) (t2:trm) : formula := mkflocal (fun Q =>  
  wp (trm_app t1 t2) Q)

Definition wpgen_if_val (v:val) (F1 F2:formula) : formula := mkflocal (fun Q =>
  \exists (b:bool), \[v = val_bool b] \* (if b then F1 Q else F2 Q)).

Definition wpgen_if (F0 F1 F2:formula) : formula :=
  wpgen_let F0 (fun v => wpgen_if_val v F1 F2).

Fixpoint wpgen (E:ctx) (t:trm) : formula :=
  let aux := wpgen E in
  match t with
  | trm_val v => wpgen_val v
  | trm_var x => wpaux_var E x
  | trm_fun x t1 => trm_fun (isubst (Ctx.rem x E) t1)
  | trm_fix f x t1 => trm_fix (isubst (Ctx.rem x (Ctx.rem f E)) t1))
  | trm_if t0 t1 t2 => wpgen_if (aux t0) (aux t1) (aux t2)
  | trm_let x t1 t2 => wpgen_let (aux t1) (fun X => wpgen (Ctx.add x X E) t2)
  | trm_app t1 t2 => wgpen_app (isubst E t1) (isubst E t2)
  end.







forward proof 
- with let
- lets
- subst all pb

reasoning on calls
- with = 2*x (app vs apps)
- with y st P x y

recursion
- call that does not fit coq