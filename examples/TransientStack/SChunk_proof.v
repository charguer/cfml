Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From CFML Require Import LibSepGroup Stdlib.Array_proof.
From TLC Require Import LibListZ LibMap.
From TLC Require Import LibListSub.

From CFML Require Import LibSepTLCbuffer.
Import IndexHints.

Require Import ListMisc.

Require Import EChunk_ml.
Require Import EChunk_proof.

Require Import Id_proof.

Require Import SChunk_ml.

(*************************************************)
(** Misc *)

Global Instance Inhab_schunk : forall A (EA:Enc A) (IA:Inhab A), Inhab (schunk_ A).
Proof.
  intros. constructor*.
  now exists (@schunk_make__ A null 0 None).
Qed.

Hint Resolve Inhab_schunk : core.

(*************************************************)
(** An init_spec for simple cases. *)
(* Read Only and deterministic f. *)
Lemma init_spec_ro_det : forall A `{IA:Inhab A} `{EA:Enc A} (L:list A) (f : func) (n:int) (J:int -> hprop) (H:hprop),
  n = length L ->
  (forall (i : int),
      index L i ->
      SPEC (f i)
        PRE (J i)
        INV H
        POST (fun x => J (i+1) \* \[x = L[i]])) ->
  SPEC (Array_ml.init n f)
    PRE (J 0)
    INV H
    POST (fun t => J n \* t ~> Array L).
Proof.
  introv Hn HL.
  xtriple.
  pose (F := (fun (xs:list A) => H \* J (length xs) \* \[prefix xs L])).
  asserts E : (H \* J 0 ==> F nil).
  { unfold F. xsimpl. apply prefix_nil. }
  xchange E.
  xapp* (>> init_spec F n f); unfold F.
  { intros i xs Hi e.
    xtriple.
    xpull; intros ([|x zs],P).
    { false. rew_list in *. subst. rew_index in *. math. }
    subst i.
    xapp* (HL (length xs)). intros y Hy. rew_listx.
    math_rewrite (length xs + 1 = 1 + length xs).
    xsimpl*. subst.
    list_cases*.
    eauto with prefix. }
  { intros x xs Hxs.
    xpull; intros HP.
    rewrites* (>>prefix_full_inv HP). subst n.
    xsimpl*. }
Qed.

(*************************************************)
(** Tactics for hor *)

(* TODO fails xchange *)
Ltac hor_left := rewrite hor_eq_exists_bool; xsimpl true.
Ltac hor_right := rewrite hor_eq_exists_bool; xsimpl false.

(*************************************************)
(** SChunks *)

Record SChunk_inv A {IA:Inhab A} {EA:Enc A}
 (align:bool) (S L:list A) (s:schunk_ A) : Prop :=
  make_SChunk_inv {
      schunk_list :
        forall i, 0 <= i < s.(view') ->
             L[i] = S[length S - s.(view') + i];
      schunk_length : length L = s.(view');
      schunk_size :
        if align
        then s.(view') = length S
        else 0 <= s.(view') <= length S
    }.

(* SChunk align LC L p is the SChunk representing L with support represented
   by LC. LC and L are equal if align is true. *)
Definition SChunk A {IA:Inhab A} {EA:Enc A}
           (align:bool) (S L:list A) (s:schunk_ A) : hprop :=
   s.(support') ~> EChunk S
\* \[SChunk_inv align S L s].

Lemma haffine_SChunk : forall A (IA:Inhab A) (EA:Enc A) a S L (s:schunk_ A),
  haffine (s ~> SChunk a S L).
Proof.
  intros. xunfold SChunk. xaffine.
Qed.

Hint Resolve haffine_SChunk : haffine.

Lemma SChunk_eq : forall A {IA:Inhab A} {EA:Enc A} (s:schunk_ A) S L b,
  s ~> SChunk b S L =
  s.(support') ~> EChunk S
\* \[SChunk_inv b S L s].
Proof. auto. Qed.

Hint Extern 1 (RegisterOpen SChunk) => Provide SChunk_eq.

Lemma SChunk_close : forall A (c:echunk_ A) {IA:Inhab A} {EA:Enc A} S L (s:schunk_ A) b,
  c = s.(support') ->
  c ~> EChunk S
    \* \[SChunk_inv b S L s]
  = s ~> SChunk b S L.
Proof. introv E. subst. auto. Qed.

Tactic Notation "xclose_schunk" constr(c) :=
  xchange (>> SChunk_close c).
Tactic Notation "xclose_schunk" "*" constr(c) :=
  xclose_schunk c; auto_star; simpl; auto.

Lemma SChunk_inv_share : forall A (IA:Inhab A) (EA:Enc A)
    (align:bool) (S L:list A) (s:schunk_ A),
  SChunk_inv align S L s ->
  SChunk_inv false S L s.
Proof.
  intros A IA EA b L Lrepr (c,vs,o) [].
  destruct b; try easy.
  constructor*.
Qed.

Lemma schunk_inv_length : forall A (IA:Inhab A) (EA:Enc A) (s:schunk_ A) (L:list A),
    s ~> SChunk true L L ==+> \[view' s = length L].
Proof.
  intros.
  xopen s. (* xopen p. *) intros X. lets []:X. xsimpl*.
  xclose* s. (*  xclose_repr* SChunk_eq p. *)
       (*  xchange* (SChunk_close (support' p)). *)
     (*  xclose_schunk* (support' p). *)
Qed.

(*************************************************)
(** Specifications *)

Lemma get_default_spec : forall A (IA:Inhab A) (EA:Enc A) b LC L (s:schunk_ A),
  SPEC (get_default s)
    PRE (\$1 \* s ~> SChunk b LC L)
    POST (fun (d:A) => s ~> SChunk b LC L).
Proof.
  xcf.
  xopen s; intros.
  xopen (support' s); intros.
  xpay. xapp.
  xclose* (support' s) LC.
  xunfolds* SChunk.
Qed.

Hint Extern 1 (RegisterSpec get_default) => Provide get_default_spec.

Lemma schunk_empty_spec : forall A (IA:Inhab A) (EA:Enc A) (d:A),
  SPEC (schunk_empty d)
    PRE (\$(2+K))
    POST (fun p => p ~> SChunk true (@nil A) (@nil A) \* \[p.(owner') = None]).
Proof.
  xcf_go*.
  xunfolds SChunk. constructor*; simpl; easy.
Qed.

Hint Extern 1 (RegisterSpec schunk_empty) => Provide schunk_empty_spec.

Lemma schunk_is_empty_spec : forall A (IA:Inhab A) (EA:Enc A) b (s:schunk_ A) (LC L:list A),
  SPEC (schunk_is_empty s)
    PRE (\$1 \* s ~> SChunk b LC L)
    POST (fun b' =>  s ~> SChunk b LC L \* \[b' = isTrue (L=nil)]).
Proof.
  xcf*.
  xopen s; intros Hp.
  xpay. xval.
  xunfolds* SChunk.
  destruct (SChunk_inv_share Hp), s; simpl in *.
  split; intros ->.
  { destruct* L. math. }
  { easy. }
Qed.

Hint Extern 1 (RegisterSpec schunk_is_empty) => Provide schunk_is_empty_spec.

Lemma schunk_is_full_spec :  forall A (IA:Inhab A) (EA:Enc A) b (s:schunk_ A) (LC L:list A),
  SPEC (schunk_is_full s)
    PRE (\$1)
    INV (s ~> SChunk b LC L)
    POST \[= isTrue (IsFull L)].
Proof.
  xcf*.
  xopen s; intros Hp.
  xpay. xval.
  xunfolds* SChunk.
  apply SChunk_inv_share in Hp.
  destruct s, Hp as [? He ?]; simpl in *.
  now rewrite <- He.
Qed.

Hint Extern 1 (RegisterSpec schunk_is_full) => Provide schunk_is_full_spec.

Lemma schunk_peek_spec : forall (A:Type) (IA:Inhab A) (EA:Enc A) (s:schunk_ A) b LC (L:list A),
  L <> nil ->
  SPEC (schunk_peek s)
    PRE (\$2)
    INV (s ~> SChunk b LC L)
    POST (fun x => \exists L', \[L = x::L']).
Proof.
  intros A IA EA p b Lc L HL.
  destruct L as [|x L]; tryfalse.
  xcf. xpay.
  xassert_cost 1.
  { xgo*. subst. now rewrite istrue_isTrue_eq. }
  xopen p. intros Hp.
  lets [E ? ?] : (>> SChunk_inv_share Hp); rew_list in *.
  xopen (support' p). (*
  xopen_echunk (support' p). *) intros c s d Lc' HLc'.
  lets [Hf Ht ? ? ?] : HLc'.
  xappn*.
  xclose* (support' p). (* xclose_echunk* (support' p) Lc. *)
  xclose* p. (* xclose_schunk* (support' p). *)
  xsimpl*. fequals*.
  rewrite* Hf. subst.
  math_rewrite (length Lc - 1 - (view' p - 1) = length Lc - view' p + 0).
  rewrite* <- E.
Qed.

Hint Extern 1 (RegisterSpec schunk_peek) => Provide schunk_peek_spec.

Lemma copy_array_sized_spec : forall A (IA:Inhab A) (EA:Enc A) (s:int) (c:echunk_ A) (d:A) (L T:list A),
  length L = K ->
  0 <= s <= length L ->
  SPEC (copy_array_sized s c d)
    PRE (\$(length L + 1))
    INV (c ~> Array L)
    POST (fun (r:loc) => \exists (T:list A), r ~> Array T
         \* \[ (forall i, 0 <= i < s -> T[i] = L[i])
               /\ (forall i, s <= i < length T -> T[i] = d)
               /\ length T = length L]).
Proof.
  introv T HL Hs.
  xcf. xpay.
  xlet. rewrite <- HL.
  xapp (>> init_spec_ro_det (take s L ++ make (length L - s) d) (fun i => \$(-i)) (c ~> Array L)).
  { rew_listx; rew_listp*. }
  { intros i Hi.
    xapp Spec_rd; clear Spec_rd. xpay.
    xif; intros Hi'.
    { rew_index* in Hi. xapp*. xsimpl.
      list_cases*. }
    { xval. xsimpl.
      list_cases*. } }
  { xsimpl*.
    split; try split; intros; list_cases*. }
Qed.

Hint Extern 1 (RegisterSpec copy_array_sized) => Provide copy_array_sized_spec.

Lemma echunk_of_schunk_spec : forall A (IA:Inhab A) (EA:Enc A) (align:bool) (LC L:list A) (s:schunk_ A),
  SPEC (echunk_of_schunk s)
    PRE (\$(K+2))
    INV (s ~> SChunk align LC L)
    POST (fun c => c ~> EChunk L).
Proof.
  intros. xcf. xpay.
  xopen s; intros Hp.
  lets [Sl Se SS] : Hp.
  destruct s as (pf,vs,o); simpl in *.
  lets [Hl He Hs]: SChunk_inv_share Hp; simpl in *.
  xopen pf; intros t s d Lpf HLpf.
  lets [Ef Et El Ec Es] : HLpf.
  xappn*; intros a T (Tl&Tr&Tle).
  xapp; intros r.
  xunfold EChunk; xsimpl.
  { constructor*; rew_list*; intros i Hi.
    { rewrite* Tl.
      rewrite* Ef.
      rewrite* Hl.
      fequals*. } }
  { xclose* pf.
    xunfolds* SChunk. }
Qed.

Hint Extern 1 (RegisterSpec echunk_of_schunk) => Provide echunk_of_schunk_spec.

Lemma schunk_of_echunk_spec : forall A (IA:Inhab A) (EA:Enc A) (c:echunk_ A) (o:Id.t_) L,
  SPEC (schunk_of_echunk c o)
    PRE (\$1 \* c ~> EChunk L)
    POST (fun p => p ~> SChunk true L L \* \[p.(owner') = Some o /\ p.(support') = c]).
Proof.
  xcf*. xpay.
  xopen c. intros t s d T HT.
  xapp. xval; simpl.
  xsimpl*.
  xclose* c.
  xunfolds SChunk.
  destruct* HT. do 2 constructor*.
Qed.

Hint Extern 1 (RegisterSpec schunk_of_echunk) => Provide schunk_of_echunk_spec.

(* NB: we need such a postcondition to be able to prove things
   in the shared case *)
Lemma schunk_pop_spec : forall A (IA:Inhab A) (EA:Enc A) (align:bool) (LC L:list A) (s:schunk_ A),
  L <> nil ->
  SPEC (schunk_pop s)
    PRE (\$3 \* s ~> SChunk align LC L)
    POST (fun '(p',x) => \exists (L':list A),
                p' ~> SChunk false LC L' \*
                \[L = x::L' /\
                  p'.(support') = s.(support') /\ p'.(owner') = s.(owner')]).
Proof.
  introv HL.
  destruct L as [|x L]; tryfalse; clear HL.
  xcf. xpay.
  xapp. { auto_false. }
  intros x' L' E. injection E as E1 E2.
  xopen s; intros Hp.
  lets [Hl Hs] : (SChunk_inv_share Hp); simpl in *.
  destruct s as (c,vs,vo); simpl in *.
  asserts vsneq0 : (vs <> 0).
  { intros ->. rew_int in Hl. rew_listx in Hl. false. }
  xopen c; intros t s d T HT. xlets.
  lets [Ef Et El Ec Es] : HT.
  xappn*. xlets. xval.
  xclose* c.
  xsimpl*; rew_list in *.
  xunfolds SChunk.
  constructor*; simpl; try math.
  intros i Hi. subst.
  math_rewrite (length LC -  (1 + length L' - 1) + i = length LC - (1 + length L') + (1+i)).
  rewrite* <- Hl.
  list_cases*.
Qed.

Hint Extern 1 (RegisterSpec schunk_pop) => Provide schunk_pop_spec.

Module Hint.
  Ltac auto_star := subst; rew_listx in *; rew_int; try math_only_if_arith; jauto.
End Hint.
Import Hint.

Lemma schunk_push_spec : forall A (IA:Inhab A) (EA:Enc A) (align:bool) (LC L: list A) (s:schunk_ A) (x:A),
  ~ IsFull L ->
  SPEC (schunk_push s x)
    PRE (\$(2 + if align then 0 else K+2)
           \* s ~> SChunk align LC L)
    POST (fun p' =>
            (if align
             then p' ~> SChunk align (x::LC) (x::L)
             else hor (p' ~> SChunk align (x::LC) (x::L) \* \[s.(support') = p'.(support')])
                      (s ~> SChunk align LC L \* p' ~> SChunk true (x::L) (x::L)))
              \* \[owner' p' = owner' s \/ owner' p' = None] ).
Proof.
  introv HL.
  xcf. xpay.
  xopen s; intros Hp.
  destruct s as (c,vs,o).
  lets [Hl ? ?] : Hp; simpl in *.
  xopen c; intros t s d T HT.
  lets [Ef Et El Ec Es] : HT.
  xapp. xlets. xif; intros Hvs.
  { destruct Hvs.
    asserts_rewrite (L=LC) in *.
    { apply* eq_of_extens.
      intros i Hi. rew_index in Hi.
      erewrite* Hl.
      fequal*. }
    xclose* c. (* xclose_echunk* c LC. *)
    xapp*.
(* OLD
xval.
    xchange (SChunk_close' c align (vs+1) o).
     { constructor; auto; intros; simpl; fequal*. case_if*. }
*)
    xval_as p'.
    xclose_schunk* p'.
     { subst p'. constructor; auto; intros; simpl; fequal*. case_if*. }
    case_if; simpl. { xsimpl*. } { hor_left; subst p'; auto. } (* TODO: hor_left* *)

(* OLD
    (* Note: tradeoff between repeating manually the description of [p]
       or duplicating the folding of [c]. *)
    xchange (SChunk_close' c align (vs+1) o).
     { constructor; auto; intros; simpl; fequal*. case_if*. }
    case_if; simpl. { xsimpl*. } { hor_left; auto. } (* TODO: hor_left* *)
    (* Alternative:
    case_if; simpl; try hor_left; unfold id_; auto_star.
    all: rewrite SChunk_eq; simpl; xsimpl;
        constructor; auto; intros; simpl; fequal*. }
    (* Sub-alternative --  all: xunfolds_schunk;
         constructor; auto; intros; simpl; fequal*. *)  *)}
*)
}
  { xclose* c. (* xclose_echunk* c LC. *)
    xclose_schunk* c.  subst.
    xapp*; intros r.
    xapp*. xval*.
    case_if*. xsimpl*. hor_right.
    xunfolds SChunk. (* rewrite SChunk_eq. xsimpl. *)
    constructor*; simpls*. { intros. fequals*. } }
Qed.

Hint Extern 1 (RegisterSpec schunk_push) => Provide schunk_push_spec.
