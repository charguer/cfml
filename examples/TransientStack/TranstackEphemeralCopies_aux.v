Set Implicit Arguments.
From CFML Require Import WPLib Stdlib.
From CFML Require Import LibSepGroup List_proof.

Require Import List_ml.
From TLC Require Import LibMap LibList LibListZ.

Require Import Mono.

Require Import ListMisc.
Require Import Option_aux.

Require Import EChunk_ml EChunk_proof.

Require Import Id_ml Id_proof.

Require Import SChunk_ml SChunkMaybeOwned_derived.

Require Import Transtack_ml TranstackCommon.
Require Import TranstackEphemeral_aux TranstackPersistent_aux.

(* For focus *)
Require Import Iterator_tools.

(**************************************)
(** Copies *)

Lemma map_spec_aux :forall A B (EA:Enc A) (IA:Inhab A) (f:func) (I:list B -> hprop) (R:A -> B -> Prop) (xs:list A) L,
  (forall k, length k < length xs -> SPEC (f (xs[length k])) PRE (I (L++k)) POST (fun x' => \[R xs[length k] x'] \* I (L++k&x'))) ->
  SPEC (List_ml.map f xs)
    PRE (I L)
    POST (fun ys => \[Forall2 R xs ys] \* I (L ++ ys)).
Proof.
  induction xs as [|x xs]; introv Hf; xcf*.
  { xmatch. apply xval_lemma.
    rew_listx. xsimpl*. }
  { xmatch.
    lets Hf' : (Hf nil). rew_list in Hf'.
    xapp* (>> Hf'). intros.
    rew_list.
    xapp* IHxs.
    { intros k ?. rew_list.
      specialize Hf with (x0::k). rew_list in Hf.
      rewrite read_cons_case in Hf.
      case_if*; try (exfalso; math).
      rew_int in Hf.
      xapp* Hf. xsimpl*. intros.
      rewrite app_cons_l. rew_list. xsimpl. }
    { intros.
      xval. rew_listx. xsimpl*. } }
Qed.

Lemma map_spec : forall A B (EA:Enc A) (IA:Inhab A) (f:func) (I:list B -> hprop) (R:A -> B -> Prop) (xs:list A),
   (forall k, length k < length xs -> SPEC (f (xs[length k])) PRE (I k) POST (fun x' => \[R xs[length k] x'] \* I (k&x'))) ->
  SPEC (List_ml.map f xs)
    PRE (I nil)
    POST (fun ys => \[Forall2 R xs ys] \* I ys).
Proof.
  intros. xapp* (>> map_spec_aux I).
  (*{ intros k. rew_list. xapp* (H k). xgo*. } TODO why was needed? *)
  intros. xsimpl*.
Qed.

Hint Extern 1 (RegisterSpec List_ml.map) => Provide map_spec.

Lemma ListOf_last : forall A B (R:A -> B -> hprop) xs x ys y,
    x ~> R y \* xs ~> ListOf R ys ==> (xs&x) ~> ListOf R (ys&y).
Proof.
  induction xs; intros.
  { xchange ListOf_nil_r. intros. subst.
    rew_list. xsimpl*. xunfold ListOf. xsimpl*. }
  { xchange ListOf_cons_r. intros ? ys' ?. subst.
    rew_list. xunfold ListOf. xsimpl*.
    rewrites <- (>> repr_eq xs).
    xchange IHxs. }
Qed.

Lemma copy_without_sharing_spec_low_bound : forall A (IA:Inhab A) (EA:Enc A) M st (e:estack_ A) L,
  SPEC (copy_without_sharing e)
    PRE (\$((K+4)*(length st.(schunks)) + K + 3))
    INV (Shared M \* e ~> EStackInState st M L)
    POST (fun e' => Shared (@empty A) \* e' ~> EStack \{} L).
Proof.
  unfold TripleMon. xcf*. xpay_pre.
  destruct st as [ft v]. simpl.
  xopen_estackInState e. intros LFS ? t ? LF LS id HLFS Hft (->,->) Hi.
  lets [? ?] : Hi.
  xappn. intros f'.
  destruct M as [E I]; unfold Shared; simpl in *.
  xappn*. intros nv Hnv.
  xlet. xapp. xchange <- (>> Shared_eq (mk_m E I)).
  xchange ListOf_inv_length. intros.
  pose (J := fun ys => (Shared (mk_m E I) \* t ~> ListOf (SChunkMaybeOwned (mk_m E I) (Some id)) LS) \* \$((K+4) * (length t - length ys)) \* ys ~> ListOf (SChunkMaybeOwned (@mk_m A \{} \{}) (Some nv)) (take (length ys) LS)).
  asserts Init : ((Shared (mk_m E I) \* t ~> ListOf (SChunkMaybeOwned (mk_m E I) (Some id)) LS) \* \$((K+4) * (length t)) ==> J nil).
  { unfold J. xsimpl. rew_listx.
    xchanges* <- ListOf_nil. }
  xchange Init.
  xapp (>> map_spec J (fun (x:schunk_ A) (y:schunk_ A) => owner' y = Some nv)); unfold J.
  { intros.
    xtriple. xapp* Spec_copy.
    xpay.
    xchange* (>> ListOf_focus t (length k)).
    xapp* SChunkMaybeOwned_derived.echunk_of_schunk_spec.
    intros. unfold protect.
    xapp*. intros ? (?&?). rew_listx. xsimpl*.
    xchange* <- (>> SChunkMaybeOwned_Owned (@mk_m A \{} \{}) (Some nv)). congruence.
    xchange (>> ListOf_last k).
    rewrites* (>> take_pos_last (1 + length k)).
    rew_int. xsimpl*. }
  { intros t' Ht'.
    lets Hlt' : (Forall2_inv_length Ht').
    xlet. xapp. intros.
    xchange (>> ListOf_inv_length t). intros Hlt. unfold Xsimpl.
    xunfold (EStackInState (A:=A)). xunfold (EStackInStateDeep (A:=A)).
    xsimpl* (mk_m (\{}:EChunkMap A) \{}).
    rewrite* Pspare.
    rewrite <- Hlt',Hlt. rewrite take_full_length.
    xunfold OptionOf.
    xchange RefGroup_empty.
    xchange EChunkGroup_empty.
    xchange (>> echunk_inv_length LF). intros. simpl.
    xunfolds_estack.
    { constructor*.
      { rewrite Forall_eq_forall_mem in *. intros s Hs.
        lets (i,(?&Hss)) : (>> mem_inv_read Hs). rewrite Hss.
        lets* Hos : (>> Forall2_inv_read i Ht').
        rew_index* in *. } }
    { unfold Xsimpl. xunfold Id. xsimpl. subst. rew_list. simpl. rew_int.
      unfold potential_pop. destruct t'; try case_if*; try math. } }
Qed.

(* TODO HERE *)
Lemma pos_sum : forall i j, i >= 0 -> j >= 0 -> i + j >= 0.
Proof. math. Qed.

Lemma pos_mul : forall i j, i >= 0 -> j >= 0 -> i * j >= 0.
Proof. math. Qed.

Lemma length_concat_same : forall A (L:list (list A)) i,
  Forall (fun x => length x = i) L ->
  length (concat L) = i * length L.
Proof.
  induction L; intros ?; rew_listx*; intros (?&HL).
  apply IHL in HL. math.
Qed.

Lemma copy_without_sharing_spec : forall A (IA:Inhab A) (EA:Enc A) M st (e:estack_ A) L,
  SPEC (copy_without_sharing e)
    PRE (\$(5*(length L) + 2*K + 7))
    INV (Shared M \* e ~> EStackInState st M L)
    POST (fun e' => Shared (@empty A) \* e' ~> EStack \{} L).
Proof.
  xtriple.
  destruct st as [ft v u].
  xopen_estackInState e. intros LFS f t ? LF LS id HLFS Hft (->,->) Hi.
  xchange ListOf_inv_length; intros.
  xchange* <- (>> EStackInStateDeep_eq e (mk_st ft (Some id) (Some e)) LFS).
  xchange* <- (>> EStackInState_eq e (mk_st ft (Some id) (Some e))).
  xapp copy_without_sharing_spec_low_bound. intros.
  xsimpl*. subst. simpl in *. rew_list. rew_int.
  math_rewrite (4 + 5 * length L + 2 * K - (K + 4) * (1 + length t) - K = 5 * length L + K + 4 - (K+4)*(1+length t)).
  math_rewrite (5 * length L + K+ 4 - (K + 4) * (1 + length t)= 5 * length L - (K + 4) * (length t)).
  lets [[]] : Hi. subst. rew_list.
  asserts_rewrite (length (concat LS) = K * length t).
  { unfold IsFull in *.
    rewrites* (>> length_concat_same K). }
  lets ? : capacity_spec.
  math_rewrite (5 * (length LF + K * length t) - (K + 4) * length t = 5*(length LF) + K*(4*length t) - (4*length t)
               ).
  math_rewrite (5* length LF + K * (4 * length t) - 4 * length t = 5*(length LF) + (K-1)*(4*length t)).
  applys* pos_sum.
  applys* pos_mul.
Qed.
