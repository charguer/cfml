Set Implicit Arguments.
From CFML Require Import WPLib.
From CFML Require Import WPDisplay WPRecord.
From TLC Require Import LibListZ LibListSub.
Require Sys_ml.
Require Array_ml.

(* -------------------------------------------------------------------------- *)

(* Conventions. *)

Implicit Types t : loc.         (* array *)
Implicit Types i ofs len : int. (* index *)


(* -------------------------------------------------------------------------- *)

(* The length of an array is at most [Sys.max_array_length]. This could be
   useful someday if we need to prove that certain integer calculations
   cannot overflow. *)

Parameter bounded_length : forall A `{EA:Enc A} t (xs : list A),
  t ~> Array xs ==>
  t ~> Array xs \* \[ length xs <= Sys_ml.max_array_length ].

(* -------------------------------------------------------------------------- *)

(* [Array.of_list]. *)

Parameter of_list_spec : forall A `{EA:Enc A} (xs:list A),
  SPEC (Array_ml.of_list xs)
    PRE \[]
    POST (fun t => t ~> Array xs).

Hint Extern 1 (RegisterSpec Array_ml.of_list) => Provide of_list_spec.

(* -------------------------------------------------------------------------- *)

(* [Array.length]. *)

Parameter length_spec : forall A `{EA:Enc A} (xs:list A) t,
  SPEC (Array_ml.length t)
    INV (t ~> Array xs)
    POST (fun n => \[n = length xs]).

Hint Extern 1 (RegisterSpec Array_ml.length) => Provide length_spec.

(* -------------------------------------------------------------------------- *)

(* [Array.get]. *)

Parameter get_spec : forall A `{EA:Enc A} `{Inhab A} (xs:list A) t i,
  index xs i ->
  SPEC (Array_ml.get t i)
    INV (t ~> Array xs)
    POST \[= xs[i] ].

Hint Extern 1 (RegisterSpec Array_ml.get) => Provide get_spec.

Notation "r [ i ]" :=
  (Wpgen_app _ Array_ml.get ((Dyn r)::(Dyn i)::nil))
  (in custom cf at level 69,
   no associativity,
   r constr at level 0,
   i constr at level 0,
   format "r [ i ]") : cf_scope.

Notation "r [ i ]" :=
  (Wptag (Wpgen_app _ Array_ml.get ((Dyn r)::(Dyn i)::nil)))
  (in custom cf at level 69,
   only printing,
   no associativity,
   r constr at level 0,
   i constr at level 0,
   format "r [ i ]") : cf_scope.

(* -------------------------------------------------------------------------- *)

(* [Array.set]. *)

Parameter set_spec : forall A `{EA:Enc A} (xs:list A) t i x,
  index xs i ->
  SPEC (Array_ml.set t i x)
    PRE (t ~> Array xs)
    POSTUNIT (t ~> Array (xs[i:=x])).

Hint Extern 1 (RegisterSpec Array_ml.set) => Provide set_spec.

Notation "r [ i ] <- v" :=
  (Wpgen_app _ Array_ml.set ((Dyn r)::(Dyn i)::(Dyn v)::nil))
  (in custom cf at level 69,
   no associativity,
   r constr at level 0,
   i constr at level 0,
   v constr at level 69,
   format "r [ i ]  <-  v") : cf_scope.

Notation "r [ i ] <- v" :=
  (Wptag (Wpgen_app _ Array_ml.set ((Dyn r)::(Dyn i)::(Dyn v)::nil)))
  (in custom cf at level 69,
   only printing,
   no associativity,
   r constr at level 0,
   i constr at level 0,
   v constr at level 69,
   format "r [ i ]  <-  v") : cf_scope.


(* -------------------------------------------------------------------------- *)

(* [Array.make]. *)

(* In practice, the parameter [n] of [Array.make] must not exceed the constant
   [Sys.max_array_length]. In the specification, we ignore this aspect, as it
   would pollute the client quite severely, without a clear benefit. If someday
   we decide to make this precondition explicit, then we should guarantee that
   [Sys.max_array_length] is at least [2^22 - 1], as this will help prove that
   it is safe to allocate arrays of known small size. *)

Parameter make_spec : forall A `{EA:Enc A} n (x:A),
  0 <= n ->
  SPEC (Array_ml.make n x)
    PRE \[]
    POST (fun t => \exists xs, t ~> Array xs \* \[xs = make n x]).

Hint Extern 1 (RegisterSpec Array_ml.make) => Provide make_spec.


Axiom init_spec : forall A `{EA:Enc A} (F : list A -> hprop) (n : int) (f : func),
  0 <= n ->
  (forall (i : int) (xs : list A),
      index n i ->
      i = length xs ->
      SPEC (f i)
        PRE (F xs)
        POST (fun x => F (xs & x))) ->
  SPEC (Array_ml.init n f)
    PRE (F nil)
    POST (fun t =>
           \exists xs, t ~> Array xs \* \[n = length xs] \* F xs).
(* TODO *)


(* -------------------------------------------------------------------------- *)

(* Immutable arrays *)

(* [Farray L p] asserts that [p] stores a array with values [L] that will
   never be modified. This assertion can only be obtained by giving away
   permanently a [p ~> Array L] assertion. Doing so guarantees that the 
   array values can never be mutated. *)

Parameter FArray : forall A `{EA:Enc A} (L : list A) (t : loc), Prop.

Parameter FArray_intro :  forall A `{EA:Enc A} (L : list A) (t : loc), 
  (t ~> Array L) ==> \[FArray L t].

Lemma of_list_spec_farray : forall A `{EA:Enc A} (L:list A),
  SPEC (Array_ml.of_list L)
    PRE \[]
    POST (fun t => \[FArray L t]).
Proof using. intros. xapp. xchanges* FArray_intro. Qed.

Axiom get_spec_farray : forall A `{EA:Enc A} `{Inhab A} (L:list A) t i,
  index L i ->
  FArray L t ->
  SPEC (Array_ml.get t i)
    PRE \[]
    POST \[= L[i] ].

Module FarraySpec.
#[export]
Hint Extern 1 (RegisterSpec Array_ml.of_list) => Provide of_list_spec_farray.
#[export]
Hint Extern 1 (RegisterSpec Array_ml.get) => Provide get_spec_farray.
End FarraySpec.


(* TODO: complete
(* -------------------------------------------------------------------------- *)

(* [Array.init]. *)

(* TEMPORARY clean up: *)

Local Hint Resolve index_of_index_length int_index_prove. (* for array indexing *)

Lemma aaa: forall n, n <= n.
Proof. math. Qed.
Lemma aab: forall n, 0 <= n -> n <> 0 -> 0 < n.
Proof. math. Qed.
Lemma aac: forall i, 1 <= i -> 0 <= i.
Proof. math. Qed.

Local Hint Resolve aaa aab aac.

Lemma singleton_prefix_make:
  forall n A `{EA:Enc A} (x : A),
  0 < n ->
  prefix (x :: nil) (make n x).
Proof.
  intros.
  exists (make (n - 1) x).
  rewrite app_cons_one_r.
  rewrite* <- make_eq_cons_make_pred.
Qed.

Lemma prefix_snoc_write:
  forall A `{EA:Enc A} i n x (xs zs : list A),
  prefix xs zs ->
  i = length xs ->
  n = length zs ->
  i < n ->
  prefix (xs & x) zs[i := x].
Proof.
  introv [ ys Hp ] Hxs Hzs ?.
  (* [ys] cannot be empty. *)
  destruct ys as [| y ys ].
  { false. rewrite app_nil_r in Hp. subst xs. math. }
  (* The witness is the tail of [ys], now also named [ys]. *)
  exists ys. subst zs. rewrite* update_middle.
Qed.

Lemma prefix_identity:
  forall A `{EA:Enc A} n (xs zs : list A),
  prefix xs zs ->
  n = length xs ->
  n = length zs ->
  xs = zs.
Proof.
  introv [ ys ? ] Hxs Hzs. subst zs. rewrite length_app in Hzs.
  assert (ys = nil). { eapply length_zero_inv. math. }
  subst ys. rewrite app_nil_r. reflexivity.
Qed.

Lemma init_spec : forall A `{EA:Enc A} (F : list A -> hprop) (n : int) (f : func),
  0 <= n ->
  (forall (i : int) (xs : list A),
      index n i ->
      i = length xs ->
      SPEC (f i)
        PRE (F xs)
        POST (fun x => F (xs & x))) ->
  SPEC (Array_ml.init n f)
    PRE (F nil)
    POST (fun t =>
           \exists xs, t ~> Array xs \* \[n = length xs] \* F xs).
Proof.
  introv ? hf.
  xcf.
  (* assert (0 <= n) *)
  xassert. { xret. xsimpl*. }
  (* if n = 0 *)
  xret. xintros. xif.
  (* Case: [n = 0]. *)
  { xstraight. }
  (* Case: [n <> 0]. *)
  { xapp* hf as x.
    xstraight.
    (* The loop invariant: at the [i]-th iteration, a prefix of length [i]
       has been initialized, and its contents forms a list [xs] which
       satisfies the user-supplied predicate [F]. *)
    xfor_inv (fun i =>
      \exists xs zs,
      F xs \*
      res ~> Array zs \*
      \[ prefix xs zs ] \*
      \[ i = length xs ] \*
      \[ n = length zs ]
    ).
    math.
    (* 1. The invariant initially holds. *)
    { xsimpl (nil & x).
      { rewrite* length_make. }
      { rewrite app_nil_l, length_one. eauto. }
      { rewrite app_nil_l. apply* singleton_prefix_make. }
    }
    (* 2. The loop body preserves the invariant. *)
    { clear x. intros i [ ? ? ]. xpull; intros xs zs. intros.
      xapp* hf as x.
      xapp*.
      xsimpl* (xs & x).
      { rewrite* length_update. }
      { rew_list. math. }
      { eauto using prefix_snoc_write. }
    }
    (* 3. The invariant implies the postcondition. *)
    { clear x. intros xs zs. intros. xret.
      forwards*: prefix_identity. math. subst xs.
      xsimpl*. }
  }
Qed.

Hint Extern 1 (RegisterSpec Array_ml.init) => Provide init_spec.

(* -------------------------------------------------------------------------- *)

(* [Array.copy]. *)

Parameter copy_spec : forall A `{EA:Enc A} (xs:list A) t,
  SPEC (Array_ml.copy t)
    INV (t ~> Array xs)
    POST (fun t' => t' ~> Array xs).

Hint Extern 1 (RegisterSpec Array_ml.copy) => Provide copy_spec.

(* -------------------------------------------------------------------------- *)

(* [Array.fill]. *)

Parameter fill_spec : forall A `{EA:Enc A} `{Inhab A} (xs:list A) t ofs len x,
  0 <= ofs ->
  ofs <= length xs ->
  0 <= len ->
  ofs + len <= length xs ->
  SPEC (Array_ml.fill t ofs len x)
    PRE (t ~> Array xs)
    POSTUNIT (\exists xs', t ~> Array xs' \*
      \[ length xs' = length xs ] \*
      \[ forall i, ofs <= i < ofs + len -> xs'[i] = x ] \*
      \[ forall i, (i < ofs \/ ofs + len <= i) -> xs'[i] = xs[i] ]
    ).

Hint Extern 1 (RegisterSpec Array_ml.fill) => Provide fill_spec.

(* TEMPORARY todo: define [LibListZ.fill] at the logical level *)

(* -------------------------------------------------------------------------- *)

(* [Array.iter]. *)

Parameter iter_spec : forall A (I : list A -> hprop) xs f t,
  (
    forall ys x,
    prefix (ys & x) xs ->
    SPEC (f x)
      PRE (I ys)
      POSTUNIT (I (ys & x))
  ) ->
  SPEC (Array_ml.iter f t)
    PRE (t ~> Array xs \* I nil)
    POSTUNIT (t ~> Array xs \* I xs ).

Hint Extern 1 (RegisterSpec Array_ml.iter) => Provide iter_spec.

(* TEMPORARY iter: give a stronger spec with "read" access to array *)
(* TEMPORARY give a generic spec to iter-like functions *)

(* -------------------------------------------------------------------------- *)

(* [Array.sub]. *)

Parameter sub_spec : forall A `{EA:Enc A} `{Inhab A} (xs:list A) t ofs len,
  0 <= ofs ->
  0 <= len ->
  ofs + len <= length xs ->
  SPEC (Array_ml.sub t ofs len)
    INV (t ~> Array xs)
    POST (fun t' => \exists xs',
             t' ~> Array xs'
          \* \[length xs' = len]
          \* \[forall i, ofs <= i < len -> xs'[i] = xs[i]]).

Hint Extern 1 (RegisterSpec Array_ml.sub) => Provide sub_spec.

(* TEMPORARY todo: define [LibListZ.sub] at the logical level *)

(* TODO: spec of arrays with credits *)


*)
