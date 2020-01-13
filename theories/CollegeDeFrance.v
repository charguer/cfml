Set Implicit Arguments.
From Sep Require SLFRules SLFWPgen SLFList. 


(* ########################################################### *)
(** ** Preuve à la main *)

Module ProveIncr.
Import SLFRules SLFProgramSyntax SLFExtra.

(** Fonction incrément, en OCaml

[[
   let incr p =
      p := !p + 1
]]

    Idem, en forme A-normale.

[[
   let incr p =
      let n = !p in
      let m = n+1 in
      p := m
]]

*)

(** Même fonction, exprimée dans le langage embarqué. *)

Definition incr : val :=
  val_fun "p" (
    trm_let "n" (val_get "p") (
    trm_let "m" (val_add "n" (val_int 1)) (
    val_set "p" "m"))).

(** Idem, dans des notations Coq pour le langage embarqué. *)

Definition incr' : val :=
  VFun 'p :=
    Let 'n := '! 'p in
    Let 'm := 'n '+ 1 in
   'p ':= 'm.

(** Spécification et vérification de la fonction [incr] *)

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun _ => p ~~~> (n+1)).
Proof using.
  (* initialize the proof *)
  intros. applys triple_app_fun_direct. simpl.
  (* reason about [let n = ..] *)
  applys triple_let.
  (* reason about [!p] *)
  { apply triple_get. }
  (* name [n'] the result of [!p] *)
  intros n'. simpl.
  (* substitute away the equality [n = n'] *)
  apply triple_hpure. intros ->.
  (* reason about [let m = ..] *)
  applys triple_let.
  (* apply the frame rule to put aside [p ~~~> n] *)
  { applys triple_conseq_frame.
    (* reason about [n+1] in the empty state *)
    { applys triple_add. }
    { xsimpl. }
    { xsimpl. } }
  (* name [m'] the result of [n+1] *)
  intros m'. simpl.
  (* substitute away the equality [m = m'] *)
  apply triple_hpure. intros ->.
  (* reason about [p := m] *)
  applys triple_conseq.
  { applys triple_set. }
  { xsimpl. }
  { xsimpl. }
Qed.


(* ########################################################### *)
(** ** Preuve avec l'infrastructure *)

Import SLFWPgen.
Open Scope wpgen_scope.


Lemma triple_incr' : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~~> n)
    (fun _ => p ~~~> (n+1)).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl.
Qed.

End ProveIncr.


(* ########################################################### *)
(** ** Preuve de la concaténation de listes *)

Module ProveAppend.
Import Example SLFList.

Module ListDef.

Fixpoint MList (L:list int) (p:loc) : hprop := (* defines [p ~> MList L] *)
  match L with
  | nil => \[p = null]
  | x::L' => \exists q, (p`.head ~~> x) \* (p`.tail ~~> q) \* (q ~> MList L')
  end.

Lemma MList_nil : forall p,
  (p ~> MList nil) = \[p = null].
Proof using. xunfold MList. auto. Qed.

Lemma MList_cons : forall p x L',
  p ~> MList (x::L') =
  \exists q, (p`.head ~~> x) \* (p`.tail ~~> q) \* q ~> MList L'.
Proof using. xunfold MList. auto. Qed.

Parameter MList_if : forall (p:loc) (L:list int),
    (p ~> MList L)
  = (If p = null
      then \[L = nil]
      else \exists x q L', \[L = x::L']
           \* (p`.head ~~> x) \* (p`.tail ~~> q) \* (q ~> MList L')).
(* Proof in [SLFList.v] *)

End ListDef.

Import SLFList.

(** Fonction de concaténation

[[
    let mappend p1 p2 =
      if p1.tail == null
        then p1.tail <- p2
        else mappend p1.tail p2
]]

*)

Definition mappend : val :=
  VFix 'f 'p1 'p2 :=
    If_ 'p1'.tail '= null
      Then Set 'p1'.tail ':= 'p2
      Else 'f ('p1'.tail) 'p2.

Lemma Triple_mappend : forall (p1 p2:loc) (L1 L2:list int),
  p1 <> null ->
  TRIPLE (mappend p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (_:unit) => p1 ~> MList (L1++L2)).
Proof using.
  intros. gen p1. induction_wf IH: list_sub L1.
  xwp. xchange (MList_if p1). case_if. xpull. intros x q L1' ->.
  xapp. xapp. xif; intros Cq.
  { xchange (MList_if q). case_if. xpull. intros ->.
    xapp. xchange <- MList_cons. }
  { xapp. xapp. { auto. } { auto. }
    rew_list. xchange <- MList_cons. }
Qed.


End ProveAppend.
