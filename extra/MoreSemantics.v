    [pat_bool : bool -> pat
  | pat_int : int -> pat




(** Evaluation rules for pattern matching. 
    [patmatch v p] returns:
    - [None] if the value [v] is not an instance of the pattern [p],
    - [Some S] is the value [v] is equal to the instantiation of [p]
      with the bindings from [S]. *)

Definition patmatch (v:val) (p:pat) : option ctx :=
  (* If (exists G, patsubst G p = v) then Some (epsilon such G) else None *)
  match p, v with
  | pat_var x, _ => Some (Ctx.one_var x v)
  | pat_constr id1 xs, val_constr id2 vs => 
      If id1 = id2 /\ length xs = length vs /\ var_distinct xs
        then Some (Ctx.combine xs vs)
        else None
  | _, _ => None
  end.





Lemma map_lookup_combine : forall `{Inhab A} xs vs (E:ctx A),
  E = combine xs vs ->
  length xs = length vs ->
  var_distinct xs ->
  LibList.map (fun x => lookup_or_arbitrary x E) xs = vs.
Proof using.
  introv HE HL HD. gen E HD.
  unfold combine. rewrite~ List_combine_eq.
  list2_ind~ xs vs. clears xs vs. (* LATER: automate clear? *)
  intros x1 xs1 x2 xs2 EQ IH E HE HD.
  rew_listx in *. (* LATER bug does not perform [rewrite map_cons] *)
  rew_listx. fequals. 
  { subst E. rewrite~ lookup_or_arbitrary_cons_same. }
  { destruct HD as (HN&HD'). sets_eq E': (LibList.combine xs1 xs2). subst E.
    rewrites* <- (>> IH E'). applys map_congr.
    { intros x Hx. rewrite~ lookup_or_arbitrary_cons_neq.
      forwards*: var_fresh_mem_inv HN Hx. } }
Qed.



(* ********************************************************************** *)
(* * Correctness of pattern matching evaluation/instantiation *)

Lemma patmatch_inv_patsubst : forall v p Gopt,
  patmatch v p = Gopt ->
  match Gopt with
  | None => forall G, v <> patsubst G p
  | Some G => v = patsubst G p
  end.
Proof using.
  introv E. induction p; simpl.
  { subst Gopt. simpl. unfold Ctx.one_var, Ctx.lookup_or_arbitrary, Ctx.lookup.
    rewrite var_eq_spec. case_if*. (* LATER: lemma *) }
  { destruct Gopt as [G|].
    { destruct v; tryfalse.
      { simpls. case_if as C. destruct C as (C1&C2&C3). subst. 
        inverts E. rewrites~ (>> Ctx.map_lookup_combine C2). } }
    { intros G N. destruct v; tryfalse.
      { inverts N. simpls. case_if as C. false C. rew_listx~. } } }
Qed.

Lemma patmatch_eq_None_inv : forall v p,
  patmatch v p = None -> 
  forall G, v <> patsubst G p.
Proof using. introv H. applys (>> patmatch_inv_patsubst H). Qed.

Lemma patmatch_eq_Some_inv : forall v p G,
  patmatch v p = Some G -> 
  v = patsubst G p.
Proof using. introv H. applys (>> patmatch_inv_patsubst H). Qed.

