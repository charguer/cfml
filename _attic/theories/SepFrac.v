

Definition hoare (t:trm) (H:hprop) (Q:val->hprop) :=
  forall h, H h -> exists h' v, eval (heap_state h) t (heap_state h') v
                             /\ Q v h'

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall H', hoare t (H \* H') (Q \*+ H' \*+ \GC).


--------------
heap = (state * Z)

Definition hoare (t:trm) (H:hprop) (Q:val->hprop) :=
  forall h, H h -> exists h' v, evaln n (heap_state h) t (heap_state h') v
                             /\ Q v h'
                             /\ heap_credits h = n + heap_credits h'.

Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall H', hoare t (H \* H') (Q \*+ H' \*+ \GC).

--------------
heap = fmap loc (val * pourcentage)  (O,1]
heap_state h = map (fun x (v,pour) => v) h
heap_ro h = filter (fun x (v,pour) => pour < 1) h

Definition hoare (t:trm) (H:hprop) (Q:val->hprop) :=
  forall h, H h -> exists h' v, eval (heap_state h) t (heap_state h') v
                             /\ Q v h'
                             /\ h'^ro = h^ro.

--------------

heap = (state * state * disjoint (fst,snd))
^rw : (f,r) -> (f,empty)
^ro : (f,r) -> (empty,r)

Definition hoare (t:trm) (H:hprop) (Q:val->hprop) :=
  forall h, H h -> exists h' v, eval (heap_state h) t (heap_state h') v
                             /\ Q v (h'^rw)
                             /\ h'^ro = h^ro.


Definition triple (t:trm) (H:hprop) (Q:val->hprop) : Prop :=
  forall HI HO, isframe HI HO ->
    hoare t (H \* HI) (Q \*+ HO \*+ \GC).


Lemma triple_frame : forall HI HO t H1 Q1,
  triple t H1 Q1 ->
  isframe HI HO ->
  triple t (H1 \* HI) (Q1 \*+ HO).

Definition onlyro (H:hprop) : Prop :=
  forall h, H h -> h^rw = heap_empty.

Definition onlyrw (H:hprop) : Prop :=
  forall h, H h -> h^ro = heap_empty.

Definition isframe (HI HO:hprop) : Prop :=
  exists HR, onlyrw HO /\ onlyro HR /\ HI = HO \* HR.
