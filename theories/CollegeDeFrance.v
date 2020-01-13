Set Implicit Arguments.
From Sep Require SLFRules SLFWPgen SLFList.


(* ########################################################### *)
(** ** Preuve à la main *)

Module ProveIncr.
Import SLFRules SLFProgramSyntax SLFExtra.

(** Fonction incrément, en OCaml.

[[
   let incr p =
      p := !p + 1
]]

    Idem, en nommant les calculs intermédiaires.

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
  (* mettons de côté [p ~~~> n] *)
  { applys triple_conseq_frame.
    (* raisonnons sur [n+1] dans l'état vide *)
    { applys triple_add. }
    { xsimpl. }
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

(** Définition de [p ~> MList L] *)

Fixpoint MList (L:list int) (p:loc) : hprop :=
  match L with
  | nil => \[p = null]
  | x::L' => \exists q, (p`.head ~~> x) \* (p`.tail ~~> q)
                     \* (q ~> MList L')
  end.

(** Lemmes pour déplier ou replier la définition *)

Lemma MList_nil : forall p,
  (p ~> MList nil) = \[p = null].
Proof using. xunfold MList. auto. Qed.

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

(** Notation [TRIPLE t PRE H POST Q] pour [Triple t H Q].
    Notation [PRE H CODE F POST Q]   pour [H ==> F Q].    *)

Lemma Triple_mappend : forall (p1 p2:loc) (L1 L2:list int),
  p1 <> null -> (* equivalent to [L1 <> nil] *)
  TRIPLE (mappend p1 p2)
    PRE (p1 ~> MList L1 \* p2 ~> MList L2)
    POST (fun (_:unit) => p1 ~> MList (L1++L2)).
Proof using.
  introv N. gen p1. induction_wf IH: list_sub L1. xwp.
  xchange (MList_if p1). case_if. xpull. intros x q L1' ->.
  xapp. xapp. xif; intros Cq.
  { xchange (MList_if q). case_if. xpull. intros ->.
    xapp. xchange <- MList_cons. }
  { xapp. xapp. { auto. } { auto. }
    rew_list. xchange <- MList_cons. }
Qed.


End ProveAppend.
