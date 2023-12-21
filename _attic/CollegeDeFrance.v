Set Implicit Arguments.
From Sep Require SLFRules SLFWPgen SLFList.


(* ########################################################### *)
(** ** Preuve à la main *)

Module ProveIncr.
Import SLFRules SLFProgramSyntax SLFExtra.

(** Fonction d'incrémentation d'une référence, en OCaml.

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
    trm_let "n" (trm_app val_get (trm_var "p")) (
    trm_let "m" (trm_app (trm_app val_add
                             (trm_var "n")) (val_int 1)) (
    trm_app (trm_app val_set (trm_var "p")) (trm_var "m")))).

(** Idem, dans des notations Coq pour le langage embarqué. *)

Definition incr' : val :=
  VFun 'p :=
    Let 'n := '! 'p in
    Let 'm := 'n '+ 1 in
    'p ':= 'm.

(** Spécification et vérification de la fonction [incr] *)

Lemma triple_incr : forall (p:loc) (n:int),
  triple (trm_app incr p)
    (p ~~> n)
    (fun _ => p ~~> (n+1)).

Proof using.
  intros.
  (* déroulons le corps de la fonction *)
  applys triple_app_fun_direct. simpl.
  (* raisonnons sur [let n = ..] *)
  applys triple_let.
  (* raisonnons sur [!p] *)
  { apply triple_get. }
  (* nommons [n'] le résultat de [!p] *)
  intros n'. simpl.
  (* extrayons et substituons [n' = n] *)
  apply triple_hpure. intros ->.
  (* raisonnons sur [let m = ..] *)
  applys triple_let.
  (* mettons de côté [p ~~> n] *)
  { applys triple_conseq_frame.
    (* raisonnons sur [n+1] dans l'état vide *)
    { applys triple_add. }
    (* simplifions l'implication *)
    { xsimpl. }
    (* on en déduit la postcondition  *)
    { xsimpl. } }
  (* nommons [m'] le résultat de [n+1] *)
  intros m'. simpl.
  (* extrayons et substituons [m' = m] *)
  apply triple_hpure. intros ->.
  (* raisonnons sur [p := m] *)
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
    (p ~~> n)
    (fun _ => p ~~> (n+1)).
Proof using.
  xwp. xapp. xapp. xapp. xsimpl.
Qed.

End ProveIncr.



























(* ########################################################### *)
(** ** Preuve de la concaténation de listes *)

Module ProveAppend.
Import Example SLFList.

Module ListDef.

(** Définition de [MList L p], noté [p ~> MList L] *)

Fixpoint MList (L:list int) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists q, (p`.head ~~> x) \* (p`.tail ~~> q)
                     \* (q ~> MList L')
  end.

(** Reformulation utile pour replier la définition *)

Lemma MList_cons : forall p x L',
  p ~> MList (x::L') =
  \exists q, (p`.head ~~> x) \* (p`.tail ~~> q) \* q ~> MList L'.
Proof using. xunfold MList. auto. Qed.

(** Lemme pour l'analyse par cas selon [p = null] *)

Parameter MList_if : forall (p:loc) (L:list int),
    (p ~> MList L)
  = (If p = null
      then \[L = nil]
      else \exists x q L', \[L = x::L']
           \* (p`.head ~~> x) \* (p`.tail ~~> q)
           \* (q ~> MList L')).
(* Proof in [SLFList.v] *)

End ListDef.

Import SLFList.

(** Fonction de concaténation

[[
    let rec append p1 p2 =
      if p1.tail == null
        then p1.tail <- p2
        else append p1.tail p2
]]

*)

Definition append : val :=
  VFix 'f 'p1 'p2 :=
    If_ 'p1'.tail '= null
      Then Set 'p1'.tail ':= 'p2
      Else 'f ('p1'.tail) 'p2.

(** Notation [TRIPLE t PRE H POST Q] pour [Triple t H Q].
    Notation [PRE H CODE F POST Q]   pour [H ==> F Q].    *)

Lemma Triple_append : forall (L1 L2:list int) (p1 p2:loc),
  p1 <> null ->
  TRIPLE (append p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (_:unit) => p1 ~> MList (L1++L2)).
Proof using.
  intros L1. induction_wf IH: list_sub L1. introv N. xwp.
  xchange (MList_if p1). case_if. xpull. intros x q L1' ->.
  xapp. xapp. xif; intros Cq.
  { xchange (MList_if q). case_if. xpull. intros ->.
    xapp. xchange <- MList_cons. }
  { xapp. xapp. { auto. } { auto. }
    xchange <- MList_cons. }
Qed.

End ProveAppend.












