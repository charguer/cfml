Lemma range_split : forall n,
  n > 1 ->
  0 < Z.quot n 2 < n.
Admitted. (* TODO *)


(* ####################################################### *)
(** ** Local reasoning with arrays *)

(** Consider the function [array_incr], which increments all the cells of
    an array of integer by one unit.

    An efficient, parallel version of this function can be implemented using
    a divide-and-conquer approach: if the array has length more than [1],
    then split in two parts and make a recursive call on each of the two parts.
    The two recursive calls can be safely executed in parallel, because they
    act over disjoint pieces of the array. Our programming language does not
    enable us to express this form of parallelism, yet it would be possible
    to do so using a simple extension based on the "fork-join" parallel construct.

[[
    let rec array_incr_par n p =
      if n = 1 then incr p
      else if n > 1 then begin
        let m = n/2 in
        array_incr_par x m;
        array_incr_par x (n-m) (p+m)
      end
]]

    Our concern here is to show how the description of an array can be split
    in two parts in the course of a recursive function. *)

(** The description of an array, that is, a set of consecutive cells,
    can be split in two parts, at an arbitrary index. Concretely, if
    we have [harray (L1++L2) p], then we can separate the left part
    [harray L1 p] from the right part [harray L2 q], where the address
    [q] is equal to [p + length L1]. Reciprocally, the two parts can
    be merged back into the original form at any time. *)

Lemma hcells_concat_eq : forall p L1 L2,
  hcells (L1++L2) p = (hcells L1 p \* hcells L2 (length L1 + p)%nat).
Proof using.
  intros. gen p. induction L1; intros; rew_list; simpl.
  { xsimpl. }
  { rewrite IHL1. math_rewrite (length L1 + S p = S (length L1 + p))%nat.
    xsimpl. }
Qed.

Lemma harray_concat_eq : forall p L1 L2,
  harray (L1++L2) p = (harray L1 p \* harray L2 (length L1 + p)%nat).
Proof using.
  intros. unfold harray, null, loc. rewrite hcells_concat_eq.
  applys himpl_antisym; xsimpl*. math.
Qed.

(** To deal with the base cases, the following two lemmas are helpul. *)

Lemma hcells_nil_eq : forall p,
  hcells nil p = \[].
Proof using. auto. Qed.

Lemma hcells_one_eq : forall p x,
  hcells (x::nil) p = (p ~~> x).
Proof using. intros. simpl. xsimpl*. Qed.

Lemma harray_nil_eq : forall p,
  harray nil p = \[p <> null].
Proof using. intros. unfold harray. rewrite hcells_nil_eq. xsimpl*. Qed.

Lemma harray_one_eq : forall p x,
  harray (x::nil) p = (p ~~> x).
Proof using.
  intros. unfold harray. rewrite hcells_one_eq. applys himpl_antisym.
  { xsimpl. } { xchanges hsingle_not_null. }
Qed.

(** Let us put this lemma to practice on our example program. *)

Import DemoPrograms.

Definition array_incr_par : val :=
  VFix 'f 'p 'n :=
    Let 'b1 := ('n '= 1) in
    If_ 'b1 Then incr 'p Else
    Let 'b2 := ('n '> 1) in
    If_ 'b2 Then
      Let 'm := 'n '/ 2 in
      Let 'n2 := ('n '- 'm) in
      Let 'p2 := (val_ptr_add 'p 'm) in
      'f 'p 'm ';
      'f 'p2 'n2
    End.

Definition vals_of_ints (L:list int) : list val :=
  LibList.map val_int L.

Parameter triple_div : forall n1 n2 : int,
  triple (val_div n1 n2)
    \[n2 <> 0]
    (fun r => \[r = val_int (Z.quot n1 n2)]).

Hint Resolve triple_div : triple.

Definition harray_int (L:list int) (p:loc) : hprop :=
  harray (LibList.map val_int L) p.

Lemma harray_int_nil_eq : forall p,
  harray_int nil p = \[p <> null].
Proof using. intros. unfold harray_int. rew_listx. rewrite* harray_nil_eq. Qed.

Lemma harray_int_one_eq : forall p n,
  harray_int (n::nil) p = (p ~~> (val_int n)).
Proof using. intros. unfold harray_int. rew_listx. rewrite* harray_one_eq. Qed.

Lemma harray_int_concat_eq : forall p L1 L2,
  harray_int (L1++L2) p = (harray_int L1 p \* harray_int L2 (length L1 + p)%nat).
Proof using. intros. unfold harray_int. rew_listx. rewrite* harray_concat_eq. rew_listx*. Qed.

Import LibListZ.
Open Scope liblist_scope.

Lemma take_app_drop_spec_nonneg : forall A (n:int) (l:list A),
  0 <= n <= length l ->
  exists f r,
      l = f ++ r
   /\ length f = n
   /\ length r = length l - n.
Proof using.
  introv M. exists (take n l) (drop n l).
  forwards* (R&_): take_app_drop_spec n l.
Qed.

Lemma triple_array_incr : forall (n:int) L p,
  n = LibListZ.length L ->
  triple (array_incr_par p n)
    (harray_int L p)
    (fun _ => harray_int (LibList.map (fun x => x + 1) L) p).
Proof using.
  intros n. induction_wf IH: (wf_downto 0) n.
  introv E. xwp. xapp. xif; intros C1.
  { forwards (x&Hx): length_one_inv L. math. (* TODO math *) subst.
    rewrite harray_int_one_eq. xapp. rewrite <- harray_one_eq. xsimpl. }
  { asserts C1': (n <> 1). { intros N. applys C1. fequals. } clear C1. (* TODO cleanup *)
    xapp. xif; intros C2.
    { forwards R: range_split n. { math. }
      xapp. { math. } sets m: (Z.quot n 2).
      xapp. xapp triple_ptr_add. { math. }
      forwards (L1&L2&EL&LL1&LL2): take_app_drop_spec_nonneg m L. { math. }
      rewrite EL. rewrite harray_int_concat_eq.
      xapp (>> IH L1). { math. } { math. }
      rew_listx. asserts_rewrite (abs (p + m) = (LibList.length L1 + p)%nat).
      { apply eq_nat_of_eq_int. rewrite abs_nonneg; math. }
      xapp (>> IH L2). { math. } { math. }
      rewrite harray_int_concat_eq. rew_listx. xsimpl. }
    { asserts En: (n = 0). { math. }
      forwards HL: (length_zero_inv L). { math. }
      xval. subst. do 2 rewrite harray_int_nil_eq. xsimpl*. } }
Qed.



Notation "'Array'' p `[ i ]" := (trm_app (trm_app (trm_val val_array_get) p) i)
  (at level 69, p at level 0, no associativity,
   format "'Array''  p `[ i ]") : charac.

Notation "'Array'' p `[ i ] `<- x" := (trm_app (trm_app (trm_app (trm_val val_array_set) p) i) x)
  (at level 69, p at level 0, no associativity,
   format "'Array''  p `[ i ]  `<-  x") : charac.




(** Let us present the verification of an example program involving arrays.
    The function [array_incr p n] increments by one unit the contents of
    each of the [n] cells from the array at location [p].

    It is implemented as a recursive function (because our language does not
    feature for-loops). For simplicity of the code, it begins by incrementing
    the cells near the end of the array, and decrements the value of the
    argument [n] at each recursive call.

[[
    let rec array_incr p n =
      if n > 0 then begin
        p.(n-1) <- p.(n-1) + 1;
        array_incr p (n-1)
      end
]]
*)

Import SLFProgramSyntax. (* TODO *)

Definition array_incr : val :=
  VFix 'f 'p 'n :=
    Let 'b := ('n '> 0) in
    If_ 'b Then
      Let 'i := 'n '- 1 in
      Let 'x := val_array_get 'p 'i in
      Let 'y := 'x '+ 1 in
      val_array_set 'p 'i 'y ';
      'f 'p 'i
    End.

(** To specify the function [array_incr], we introduce an auxiliary definition
    specialized for describing arrays of integers. The predicate [harray_int L p]
    is similar to [harray L p] with the difference that [L] has type [list int]
    instead of [list val]. *)

Definition harray_int (L:list int) (p:loc) : hprop :=
  harray (LibList.map val_int L) p.

(** The specification of [array_incr] includes a precondition [harray_int L p],
    and a postcondition of the form [harray_int L' p], where [L'] is obtained
    by adding one unit to the every element from [L]. Formally, [L'] is equal to
    [LibList.map (fun x => x + 1) L]. *)


Implicit Types i : int. (* TODO *)

Parameter triple_array_get' : forall p i L,
  triple (val_array_get p i)
    (harray L p \* \[0 <= i < length L])
    (fun r => \[r = list_get L i] \* harray L p).

Parameter triple_array_set': forall p i v L,
  triple (val_array_set p i v)
    (harray L p \* \[0 <= i < length L])
    (fun _ => harray (list_update L i v) p).

Hint Resolve triple_array_get' triple_array_set' : triple.

Lemma triple_array_incr : forall (n:int) (L:list int) p,
  n = LibListZ.length L ->
  triple (array_incr p n)
    (harray_int L p)
    (fun _ => harray_int (LibList.map (fun x => x + 1) L) p).
Proof using.
  introv K. gen n. induction_wf IH: (@list_sub int) L. introv N. xwp.
  xapp. xif; intros C.
  { forwards (x&L'&->): length_pos_inv_last L. { math. } rew_listx in *.
    xapp. xapp. { rewrite length_map. rew_listx. (* TODO rew_listx. *) math. }
    rew_listx.
    xapp. xapp triple_array_get. xapp_debug. eapply H.
  { xval. rewrite (length_zero_inv L); [|math]. rew_listx. xsimpl. }
Qed.
