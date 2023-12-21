
(* ********************************************************************** *)
(* * Decoders *)

(* ---------------------------------------------------------------------- *)
(* ** [Decode] predicate and instances *)

Definition Decode (v:val) A {EA:Enc A} (V:A) : Prop :=
  v = ``V.

Lemma Decode_enc : forall A (EA:Enc A) (V:A),
  Decode (``V) V.
Proof using. intros. hnfs~. Qed.

Hint Extern 1 (Decode (``_) _) => eapply Decode_enc : Decode.

Lemma Decode_unit :
  Decode val_unit tt.
Proof using. intros. hnfs~. Qed.

Lemma Decode_int : forall (n:int),
  Decode (val_int n) n.
Proof using. intros. hnfs~. Qed.

Lemma Decode_bool : forall (b:bool),
  Decode (val_bool b) b.
Proof using. intros. hnfs~. Qed.

Lemma Decode_loc : forall (l:loc),
  Decode (val_loc l) l.
Proof using. intros. hnfs~. Qed.

Hint Resolve Decode_unit Decode_int Decode_bool Decode_loc : Decode.

Lemma Decode_nil : forall A (EA:Enc A),
  Decode (val_constr "nil" nil) (@nil A).
Proof using. intros. hnfs~. Qed.

Lemma Decode_cons : forall A (EA:Enc A) (X:A) (L:list A) (x l : val),
  Decode x X ->
  Decode l L ->
  Decode (val_constr "cons" (x::l::nil)) (X::L).
Proof using. introv Dx DL. unfolds. rew_enc. fequals. Qed.

Lemma Decode_None : forall A (EA:Enc A),
  Decode (val_constr "none" nil) (@None A).
Proof using. intros. hnfs~. Qed.

Lemma Decode_Some : forall A (EA:Enc A) (V:A) (v:val),
  Decode v V ->
  Decode (val_constr "some" (v::nil)) (Some V).
Proof using. intros. unfolds. rew_enc. fequals. Qed.

(* TODO: generalize to tuples, and strings and char base types *)

(* ---------------------------------------------------------------------- *)
(* ** Predicate [Decodes] *)

Definition Decodes (vs:vals) (Vs:dyns) : Prop :=
  vs = encs Vs.

Lemma Decodes_nil :
  Decodes nil nil.
Proof using. intros. hnfs~. Qed.

Lemma Decodes_cons : forall (v:val) (vs:vals) A (EA:Enc A) (V:A) (Vs:dyns),
  Decode v V ->
  Decodes vs Vs ->
  Decodes (v::vs) ((Dyn V)::Vs).
Proof using.
  introv Dv Dvs. unfolds Decodes. simpl. rewrite enc_dyn_make. fequals.
Qed.



Lemma Triple_ref_Decode : forall A (EA:Enc A) (V:A) (v:val),
  Decode v V ->
  Triple (val_ref v)
    \[]
    (fun l => l ~~> V).
Proof using. introv Hv. unfolds Decode. subst v. applys Triple_ref. Qed.




Lemma Triple_set_Decode : forall A1 `{EA1:Enc A1} (V1 V2:A1) (l:loc) (v2:val),
  Decode v2 V2 ->
  Triple (val_set l v2)
    (l ~~> V1)
    (fun (u:unit) => l ~~> V2).
Proof using.
  introv Hv2. unfolds Decode. subst v2. applys Triple_set.
Qed.
Lemma Triple_eq_Decode : forall A `(EA:Enc A) (v1 v2:val) (V1 V2:A),
  Decode v1 V1 ->
  Decode v2 V2 ->
  Enc_comparable V1 V2 ->
  Triple (val_eq v1 v2)
    \[]
    (fun (b:bool) => \[b = isTrue (V1 = V2)]).
Proof using.
  introv D1 D2 I. unfolds Decode. subst v1 v2. applys* Triple_eq.
Qed.


Lemma Triple_neq_Decode : forall A `(EA:Enc A) (v1 v2:val) (V1 V2:A),
  Decode v1 V1 ->
  Decode v2 V2 ->
  Enc_comparable V1 V2 ->
  Triple (val_neq v1 v2)
    \[]
    (fun (b:bool) => \[b = isTrue (V1 <> V2)]).
Proof using.
  introv D1 D2 I. unfolds Decode. subst v1 v2. applys* Triple_neq.
Qed.



Hint Extern 1 (Register_Spec (val_set_field _)) => Provide @Triple_set_field_Decode.

(* not used
Lemma xapp_record_new_noarg : forall (Vs:dyns) (Q:loc->hprop) (H:hprop) (ks:fields) (vs:vals),
  noduplicates_fields_exec ks = true ->
  LibListExec.is_nil ks = false ->
  Decodes vs Vs ->
  List.length ks = List.length Vs ->
  (fun p => p ~> Record (List.combine ks Vs)) \*+ H ===> (protect Q) ->
  H ==> ^(Wpgen_app_untyped (trm_apps (trm_val (val_record_init ks)) (trms_vals vs))) Q.
Proof using. introv HN HE HD EQ HI. unfolds Decodes. applys* xapp_record_new. Qed.
*)

(* DEPRECATED
Ltac xnew_core_noarg tt :=
  applys xapp_record_new_noarg;
  [ try reflexivity
  | try reflexivity
  | xdecodes
  | try reflexivity
  | xsimpl; simpl List.combine; unfold protect; xnew_post tt ].

Ltac xapp_record_new tt :=
  xnew_core_noarg tt.

Tactic Notation "xnew" :=
  xnew_core_noarg tt.
*)


Lemma Triple_set_field_Decode : forall (v2:val) A (EA:Enc A) (V1:A) (l:loc) f (V2:A),
  Decode v2 V2 ->
  Triple ((val_set_field f) l v2)
    (l`.f ~~> V1)
    (fun (r:unit) => l`.f ~~> V2).
Proof using. introv M. unfolds Decode. subst v2. applys Triple_set_field_strong. Qed.
