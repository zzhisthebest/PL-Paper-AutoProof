Require Import Fsub.EffectExclusion.Tactics.
Require Import Coq.Program.Equality.
Require Export Fsub.EffectExclusion.Fsub_LetSum_Lemmas.
Require Import Lia.
Require Import Arith.

(* ============ supplied definitions from Task.v ============ *)
Definition transitivity_on_sub Q := forall E S T,
  sub E S Q -> sub E Q T -> sub E S T.

Definition transitivity_on_subqtype Q := forall E S T,
  subqtype E S Q -> subqtype E Q T -> subqtype E S T.

Definition transitivity_on_subqual Q := forall E S T,
  subqual E S Q -> subqual E Q T -> subqual E S T.

(* ================= Dev.v ================= *)

(* ========================================================= *)
(* Environment extension relation                             *)
(* ========================================================= *)

Definition extends (E E' : env) : Prop :=
  forall x b, binds x b E -> binds x b E'.

Lemma extends_refl : forall E, extends E E.
Proof. intros E x b H; auto. Qed.

Lemma extends_trans : forall E1 E2 E3,
  extends E1 E2 -> extends E2 E3 -> extends E1 E3.
Proof. intros E1 E2 E3 H12 H23 x b H; auto. Qed.

Lemma extends_cons : forall E x b,
  extends E ((x,b) :: E).
Proof. intros E x b y c H. apply binds_cons. auto. Qed.

Lemma extends_cons_same : forall E E' x b,
  extends E E' -> extends ((x,b)::E) ((x,b)::E').
Proof.
  intros E E' x b H y c Hy.
  apply binds_cons_1 in Hy as [[? ?]|Hy]; subst.
  - left; auto.
  - right; apply H; auto.
Qed.

Lemma extends_app_l : forall E F, extends E (F ++ E).
Proof. intros E F x b H. apply binds_app_3. auto. Qed.

Lemma binds_mid_weaken : forall (A : Type) (y : atom) (c : A) E1 x b E2,
  binds y c (E1 ++ E2) -> binds y c (E1 ++ x ~ b ++ E2).
Proof.
  intros A y c E1 x b E2 H. unfold binds in *.
  apply in_app_iff.
  apply in_app_iff in H. destruct H as [H|H].
  - left; auto.
  - right. right; auto.
Qed.

Lemma notin_dom_remove_mid : forall (E1:env) x (b:binding) (E2:env) y,
  y `notin` dom (E1 ++ x ~ b ++ E2) -> y `notin` dom (E1 ++ E2).
Proof.
  intros E1 x b E2 y H Hy.
  apply binds_In_inv in Hy as [c Hc].
  apply H. apply (binds_In _ y c). eapply binds_mid_weaken; eauto.
Qed.

(* ========================================================= *)
(* wf_env basic facts                                         *)
(* ========================================================= *)

Lemma wf_env_cons_inv : forall x (b:binding) (E:env),
  wf_env ((x,b)::E) -> wf_env E.
Proof. intros x b E H; inversion H; subst; auto. Qed.

Lemma wf_env_sub_inv : forall (X:atom) (T:typ) (E:env),
  wf_env (X ~ bind_sub T ++ E) ->
  wf_env E /\ wf_typ E T /\ X `notin` dom E.
Proof. intros. inversion H; subst; auto. Qed.

Lemma wf_env_typ_inv : forall (x:atom) (T:qtyp) (E:env),
  wf_env (x ~ bind_typ T ++ E) ->
  wf_env E /\ wf_qtyp E T /\ x `notin` dom E.
Proof. intros. inversion H; subst; auto. Qed.

Lemma wf_env_qua_inv : forall (X:atom) (Q:qua) (E:env),
  wf_env (X ~ bind_qua Q ++ E) ->
  wf_env E /\ wf_qua E Q /\ X `notin` dom E.
Proof. intros. inversion H; subst; auto. Qed.

Lemma wf_env_uniq : forall E, wf_env E -> uniq E.
Proof.
  induction 1; simpl.
  - constructor.
  - apply uniq_cons; auto.
  - apply uniq_cons; auto.
  - apply uniq_cons; auto.
Qed.

(* ========================================================= *)
(* Removing a middle bind_typ from well-formedness            *)
(* ========================================================= *)

Lemma binds_qua_remove_typ_mid : forall (E1:env) x (T:qtyp) (E2:env) z R,
  binds z (bind_qua R) (E1 ++ x ~ bind_typ T ++ E2) ->
  binds z (bind_qua R) (E1 ++ E2).
Proof.
  intros E1 x T E2 z R H. unfold binds in *.
  apply in_app_iff.
  apply in_app_iff in H. destruct H as [H|H].
  - left; auto.
  - simpl in H. destruct H as [Heq|H].
    + inversion Heq; subst; discriminate.
    + right; auto.
Qed.

Lemma binds_sub_remove_typ_mid : forall (E1:env) x (T:qtyp) (E2:env) z U,
  binds z (bind_sub U) (E1 ++ x ~ bind_typ T ++ E2) ->
  binds z (bind_sub U) (E1 ++ E2).
Proof.
  intros E1 x T E2 z U H. unfold binds in *.
  apply in_app_iff.
  apply in_app_iff in H. destruct H as [H|H].
  - left; auto.
  - simpl in H. destruct H as [Heq|H].
    + inversion Heq; subst; discriminate.
    + right; auto.
Qed.

Fixpoint wf_qua_remove_typ_mid (Q:qua) {struct Q} :
  forall (E1:env) x (T:qtyp) (E2:env),
  wf_qua (E1 ++ x ~ bind_typ T ++ E2) Q -> wf_qua (E1 ++ E2) Q.
Proof.
  destruct Q as [b|n|X|Q1 Q2|Q1 Q2|Q1]; intros E1 x T E2 H.
  - apply wf_qua_base.
  - inversion H.
  - inversion H; subst. eapply wf_qua_fvar. eapply binds_qua_remove_typ_mid; eauto.
  - inversion H; subst. apply wf_qua_meet.
    + apply (wf_qua_remove_typ_mid Q1 E1 x T E2); eassumption.
    + apply (wf_qua_remove_typ_mid Q2 E1 x T E2); eassumption.
  - inversion H; subst. apply wf_qua_join.
    + apply (wf_qua_remove_typ_mid Q1 E1 x T E2); eassumption.
    + apply (wf_qua_remove_typ_mid Q2 E1 x T E2); eassumption.
  - inversion H; subst. apply wf_qua_negate.
    apply (wf_qua_remove_typ_mid Q1 E1 x T E2); eassumption.
Qed.

Scheme wf_t_mut := Induction for wf_typ Sort Prop
with wf_q_mut := Induction for wf_qtyp Sort Prop.
Combined Scheme wf_tq_mut from wf_t_mut, wf_q_mut.

Lemma wf_typ_qtyp_remove_typ_mid :
  (forall (E:env) (T:typ), wf_typ E T ->
     forall (E1:env) x (TT:qtyp) (E2:env),
       E = E1 ++ x ~ bind_typ TT ++ E2 -> wf_typ (E1 ++ E2) T) /\
  (forall (E:env) (T:qtyp), wf_qtyp E T ->
     forall (E1:env) x (TT:qtyp) (E2:env),
       E = E1 ++ x ~ bind_typ TT ++ E2 -> wf_qtyp (E1 ++ E2) T).
Proof.
  apply wf_tq_mut
    with (P := fun E T _ => forall (E1:env) x (TT:qtyp) (E2:env),
                E = E1 ++ x ~ bind_typ TT ++ E2 -> wf_typ (E1 ++ E2) T)
         (P0 := fun E T _ => forall (E1:env) x (TT:qtyp) (E2:env),
                E = E1 ++ x ~ bind_typ TT ++ E2 -> wf_qtyp (E1 ++ E2) T).
  - intros E E1 x TT E2 Heq. subst. constructor.
  - intros E E1 x TT E2 Heq. subst. constructor.
  - intros U E X b E1 x TT E2 Heq. subst.
    apply wf_typ_var with (U:=U).
    apply (binds_sub_remove_typ_mid E1 x TT E2 X U). exact b.
  - intros E T1 T2 w1 IH1 w2 IH2 E1 x TT E2 Heq. subst.
    apply wf_typ_arrow.
    + apply (IH1 E1 x TT E2). reflexivity.
    + apply (IH2 E1 x TT E2). reflexivity.
  - intros L E T1 T2 w1 IH1 w0 IH0 E1 x TT E2 Heq. subst.
    apply wf_typ_all with (L:=L).
    + apply (IH1 E1 x TT E2). reflexivity.
    + intros X HX.
      apply (IH0 X HX (X ~ bind_sub T1 ++ E1) x TT E2).
      rewrite app_assoc. reflexivity.
  - intros L E T1 T2 wq w0 IH0 E1 x TT E2 Heq. subst.
    apply wf_typ_qall with (L:=L).
    + apply (wf_qua_remove_typ_mid T1 E1 x TT E2). exact wq.
    + intros X HX.
      apply (IH0 X HX (X ~ bind_qua T1 ++ E1) x TT E2).
      rewrite app_assoc. reflexivity.
  - intros E T1 T2 w1 IH1 w2 IH2 E1 x TT E2 Heq. subst.
    apply wf_typ_sum.
    + apply (IH1 E1 x TT E2). reflexivity.
    + apply (IH2 E1 x TT E2). reflexivity.
  - intros E T1 T2 w1 IH1 w2 IH2 E1 x TT E2 Heq. subst.
    apply wf_typ_pair.
    + apply (IH1 E1 x TT E2). reflexivity.
    + apply (IH2 E1 x TT E2). reflexivity.
  - intros E Q T wq wT IHT E1 x TT E2 Heq. subst.
    apply wf_qtyp_qtyp.
    + apply (wf_qua_remove_typ_mid Q E1 x TT E2). exact wq.
    + apply (IHT E1 x TT E2). reflexivity.
Qed.

Lemma wf_typ_remove_typ_mid : forall (E1:env) x (T:qtyp) (E2:env) S,
  wf_typ (E1 ++ x ~ bind_typ T ++ E2) S -> wf_typ (E1 ++ E2) S.
Proof.
  intros. eapply (proj1 wf_typ_qtyp_remove_typ_mid); eauto.
Qed.

Lemma wf_qtyp_remove_typ_mid : forall (E1:env) x (T:qtyp) (E2:env) S,
  wf_qtyp (E1 ++ x ~ bind_typ T ++ E2) S -> wf_qtyp (E1 ++ E2) S.
Proof.
  intros. eapply (proj2 wf_typ_qtyp_remove_typ_mid); eauto.
Qed.

(* removal of a middle bind_typ from wf_env *)
Lemma wf_env_remove_typ_mid : forall (E1:env) (x:atom) (T:qtyp) (E2:env),
  wf_env (E1 ++ x ~ bind_typ T ++ E2) -> wf_env (E1 ++ E2).
Proof.
  intros E1. induction E1 as [| a E1 IH]; intros x T E2 H.
  - simpl in *. apply wf_env_cons_inv in H. auto.
  - destruct a as [y c]. simpl in *.
    inversion H; subst.
    + eapply wf_env_sub.
      * apply (IH x T E2). eassumption.
      * apply (wf_typ_remove_typ_mid E1 x T E2 T0). eassumption.
      * apply (notin_dom_remove_mid E1 x (bind_typ T) E2 y). eassumption.
    + eapply wf_env_typ.
      * apply (IH x T E2). eassumption.
      * apply (wf_qtyp_remove_typ_mid E1 x T E2 T0). eassumption.
      * apply (notin_dom_remove_mid E1 x (bind_typ T) E2 y). eassumption.
    + eapply wf_env_qua.
      * apply (IH x T E2). eassumption.
      * apply (wf_qua_remove_typ_mid Q E1 x T E2). eassumption.
      * apply (notin_dom_remove_mid E1 x (bind_typ T) E2 y). eassumption.
Qed.

(* ========================================================= *)
(* Environment similarity (same names and binding kinds)      *)
(* ========================================================= *)

Inductive same_kind : binding -> binding -> Prop :=
  | sk_sub : forall T1 T2, same_kind (bind_sub T1) (bind_sub T2)
  | sk_typ : forall T1 T2, same_kind (bind_typ T1) (bind_typ T2)
  | sk_qua : forall Q1 Q2, same_kind (bind_qua Q1) (bind_qua Q2).

Inductive env_sim : env -> env -> Prop :=
  | sim_nil : env_sim nil nil
  | sim_cons : forall x b1 b2 E1 E2,
      same_kind b1 b2 -> env_sim E1 E2 ->
      env_sim ((x,b1)::E1) ((x,b2)::E2).

Lemma same_kind_refl : forall b, same_kind b b.
Proof. intros [T|T|Q]; constructor. Qed.

Lemma env_sim_refl : forall E, env_sim E E.
Proof.
  induction E as [| [x b] E IH].
  - constructor.
  - apply sim_cons; [apply same_kind_refl | exact IH].
Qed.

Lemma env_sim_app_tail : forall E1 E2 x b1 b2,
  same_kind b1 b2 -> env_sim E1 E2 ->
  env_sim ((x,b1)::E1) ((x,b2)::E2).
Proof. intros; apply sim_cons; auto. Qed.

Lemma binds_sim_sub : forall E1 E2, env_sim E1 E2 ->
  forall x T, binds x (bind_sub T) E1 -> exists T', binds x (bind_sub T') E2.
Proof.
  intros E1 E2 H. induction H as [| x b1 b2 E1 E2 Hk Hsim IHsim]; intros xx T Hb.
  - destruct Hb.
  - destruct Hb as [Heq|Hb].
    + inversion Heq; subst. inversion Hk; subst. eexists; simpl; left; reflexivity.
    + destruct (IHsim xx T Hb) as [T' HT']. exists T'. apply binds_cons. exact HT'.
Qed.

Lemma binds_sim_typ : forall E1 E2, env_sim E1 E2 ->
  forall x T, binds x (bind_typ T) E1 -> exists T', binds x (bind_typ T') E2.
Proof.
  intros E1 E2 H. induction H as [| x b1 b2 E1 E2 Hk Hsim IHsim]; intros xx T Hb.
  - destruct Hb.
  - destruct Hb as [Heq|Hb].
    + inversion Heq; subst. inversion Hk; subst. eexists; simpl; left; reflexivity.
    + destruct (IHsim xx T Hb) as [T' HT']. exists T'. apply binds_cons. exact HT'.
Qed.

Lemma binds_sim_qua : forall E1 E2, env_sim E1 E2 ->
  forall x Q, binds x (bind_qua Q) E1 -> exists Q', binds x (bind_qua Q') E2.
Proof.
  intros E1 E2 H. induction H as [| x b1 b2 E1 E2 Hk Hsim IHsim]; intros xx Q Hb.
  - destruct Hb.
  - destruct Hb as [Heq|Hb].
    + inversion Heq; subst. inversion Hk; subst. eexists; simpl; left; reflexivity.
    + destruct (IHsim xx Q Hb) as [Q' HQ']. exists Q'. apply binds_cons. exact HQ'.
Qed.

(* ========================================================= *)
(* Well-formedness lemmas: extends and env_sim                *)
(* ========================================================= *)

Lemma wf_qua_extends : forall E E', extends E E' ->
  forall Q, wf_qua E Q -> wf_qua E' Q.
Proof.
  intros E E' Hext Q H. induction H.
  - constructor.
  - eapply wf_qua_fvar. apply Hext. exact H.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
Qed.

Lemma wf_typ_qtyp_extends :
  (forall (E:env) (T:typ), wf_typ E T ->
     forall E', extends E E' -> wf_typ E' T) /\
  (forall (E:env) (T:qtyp), wf_qtyp E T ->
     forall E', extends E E' -> wf_qtyp E' T).
Proof.
  apply wf_tq_mut
    with (P := fun E T _ => forall E', extends E E' -> wf_typ E' T)
         (P0 := fun E T _ => forall E', extends E E' -> wf_qtyp E' T).
  - intros E E' He. constructor.
  - intros E E' He. constructor.
  - intros U E X b E' He. eapply wf_typ_var. apply He. exact b.
  - intros E T1 T2 w1 IH1 w2 IH2 E' He. constructor; auto.
  - intros L E T1 T2 w1 IH1 w0 IH0 E' He.
    apply wf_typ_all with (L:=L).
    + apply IH1. exact He.
    + intros X HX. apply (IH0 X HX). apply extends_cons_same. exact He.
  - intros L E T1 T2 wq w0 IH0 E' He.
    apply wf_typ_qall with (L:=L).
    + apply wf_qua_extends with (E:=E); auto.
    + intros X HX. apply (IH0 X HX). apply extends_cons_same. exact He.
  - intros E T1 T2 w1 IH1 w2 IH2 E' He. constructor; auto.
  - intros E T1 T2 w1 IH1 w2 IH2 E' He. constructor; auto.
  - intros E Q T wq wT IHT E' He. apply wf_qtyp_qtyp.
    + apply wf_qua_extends with (E:=E); auto.
    + apply IHT. exact He.
Qed.

Lemma wf_typ_extends : forall E E', extends E E' ->
  forall T, wf_typ E T -> wf_typ E' T.
Proof. intros. eapply (proj1 wf_typ_qtyp_extends); eauto. Qed.

Lemma wf_qtyp_extends : forall E E', extends E E' ->
  forall T, wf_qtyp E T -> wf_qtyp E' T.
Proof. intros. eapply (proj2 wf_typ_qtyp_extends); eauto. Qed.

Fixpoint wf_qua_sim (Q:qua) {struct Q} :
  forall E E', env_sim E E' -> wf_qua E Q -> wf_qua E' Q.
Proof.
  destruct Q as [b|n|X|Q1 Q2|Q1 Q2|Q1]; intros E E' Hs H.
  - constructor.
  - inversion H.
  - inversion H; subst.
    match goal with
    | Hb : binds X (bind_qua ?R) E |- _ =>
        destruct (binds_sim_qua E E' Hs X R Hb) as [Q' HQ'];
        eapply wf_qua_fvar; exact HQ'
    end.
  - inversion H; subst. constructor.
    + eapply (wf_qua_sim Q1); eauto.
    + eapply (wf_qua_sim Q2); eauto.
  - inversion H; subst. constructor.
    + eapply (wf_qua_sim Q1); eauto.
    + eapply (wf_qua_sim Q2); eauto.
  - inversion H; subst. constructor.
    eapply (wf_qua_sim Q1); eauto.
Qed.

Lemma wf_typ_qtyp_sim :
  (forall (E:env) (T:typ), wf_typ E T ->
     forall E', env_sim E E' -> wf_typ E' T) /\
  (forall (E:env) (T:qtyp), wf_qtyp E T ->
     forall E', env_sim E E' -> wf_qtyp E' T).
Proof.
  apply wf_tq_mut
    with (P := fun E T _ => forall E', env_sim E E' -> wf_typ E' T)
         (P0 := fun E T _ => forall E', env_sim E E' -> wf_qtyp E' T).
  - intros E E' Hs. constructor.
  - intros E E' Hs. constructor.
  - intros U E X b E' Hs.
    destruct (binds_sim_sub E E' Hs X U b) as [U' HU'].
    eapply wf_typ_var. exact HU'.
  - intros E T1 T2 w1 IH1 w2 IH2 E' Hs. constructor; auto.
  - intros L E T1 T2 w1 IH1 w0 IH0 E' Hs.
    apply wf_typ_all with (L:=L).
    + apply IH1. exact Hs.
    + intros X HX. apply (IH0 X HX). apply sim_cons; [apply sk_sub|exact Hs].
  - intros L E T1 T2 wq w0 IH0 E' Hs.
    apply wf_typ_qall with (L:=L).
    + eapply wf_qua_sim; eauto.
    + intros X HX. apply (IH0 X HX). apply sim_cons; [apply sk_qua|exact Hs].
  - intros E T1 T2 w1 IH1 w2 IH2 E' Hs. constructor; auto.
  - intros E T1 T2 w1 IH1 w2 IH2 E' Hs. constructor; auto.
  - intros E Q T wq wT IHT E' Hs. apply wf_qtyp_qtyp.
    + eapply wf_qua_sim; eauto.
    + apply IHT. exact Hs.
Qed.

Lemma wf_typ_sim : forall E E', env_sim E E' ->
  forall T, wf_typ E T -> wf_typ E' T.
Proof. intros. eapply (proj1 wf_typ_qtyp_sim); eauto. Qed.

Lemma wf_qtyp_sim : forall E E', env_sim E E' ->
  forall T, wf_qtyp E T -> wf_qtyp E' T.
Proof. intros. eapply (proj2 wf_typ_qtyp_sim); eauto. Qed.

Lemma wf_qua_bind_sub_irrel : forall x E U1 U2 Q,
  wf_qua (x ~ bind_sub U1 ++ E) Q -> wf_qua (x ~ bind_sub U2 ++ E) Q.
Proof. intros. eapply wf_qua_sim; eauto. apply sim_cons; [apply sk_sub|apply env_sim_refl]. Qed.

Lemma wf_qua_bind_qua_irrel : forall x E Q1 Q2 Q,
  wf_qua (x ~ bind_qua Q1 ++ E) Q -> wf_qua (x ~ bind_qua Q2 ++ E) Q.
Proof. intros. eapply wf_qua_sim; eauto. apply sim_cons; [apply sk_qua|apply env_sim_refl]. Qed.

Lemma wf_qua_bind_typ_irrel : forall x E T1 T2 Q,
  wf_qua (x ~ bind_typ T1 ++ E) Q -> wf_qua (x ~ bind_typ T2 ++ E) Q.
Proof. intros. eapply wf_qua_sim; eauto. apply sim_cons; [apply sk_typ|apply env_sim_refl]. Qed.

Lemma wf_typ_bind_sub_irrel : forall x E U1 U2 T,
  wf_typ (x ~ bind_sub U1 ++ E) T -> wf_typ (x ~ bind_sub U2 ++ E) T.
Proof. intros. eapply wf_typ_sim; eauto. apply sim_cons; [apply sk_sub|apply env_sim_refl]. Qed.

Lemma wf_qtyp_bind_sub_irrel : forall x E U1 U2 T,
  wf_qtyp (x ~ bind_sub U1 ++ E) T -> wf_qtyp (x ~ bind_sub U2 ++ E) T.
Proof. intros. eapply wf_qtyp_sim; eauto. apply sim_cons; [apply sk_sub|apply env_sim_refl]. Qed.

Lemma wf_typ_bind_qua_irrel : forall x E Q1 Q2 T,
  wf_typ (x ~ bind_qua Q1 ++ E) T -> wf_typ (x ~ bind_qua Q2 ++ E) T.
Proof. intros. eapply wf_typ_sim; eauto. apply sim_cons; [apply sk_qua|apply env_sim_refl]. Qed.

Lemma wf_qtyp_bind_qua_irrel : forall x E Q1 Q2 T,
  wf_qtyp (x ~ bind_qua Q1 ++ E) T -> wf_qtyp (x ~ bind_qua Q2 ++ E) T.
Proof. intros. eapply wf_qtyp_sim; eauto. apply sim_cons; [apply sk_qua|apply env_sim_refl]. Qed.

Lemma wf_typ_bind_typ_irrel : forall x E T1 T2 T,
  wf_typ (x ~ bind_typ T1 ++ E) T -> wf_typ (x ~ bind_typ T2 ++ E) T.
Proof. intros. eapply wf_typ_sim; eauto. apply sim_cons; [apply sk_typ|apply env_sim_refl]. Qed.

Lemma wf_qtyp_bind_typ_irrel : forall x E T1 T2 T,
  wf_qtyp (x ~ bind_typ T1 ++ E) T -> wf_qtyp (x ~ bind_typ T2 ++ E) T.
Proof. intros. eapply wf_qtyp_sim; eauto. apply sim_cons; [apply sk_typ|apply env_sim_refl]. Qed.

Ltac wf_qua_auto :=
  lazymatch goal with
  | |- wf_env _ => eassumption
  | |- wf_qua _ (qua_base _) => constructor
  | |- wf_qua _ (qua_negate _) => eapply wf_qua_negate; wf_qua_auto
  | |- wf_qua _ (qua_join _ _) => eapply wf_qua_join; [wf_qua_auto|wf_qua_auto]
  | |- wf_qua _ (qua_meet _ _) => eapply wf_qua_meet; [wf_qua_auto|wf_qua_auto]
  | |- wf_qua _ _ => eassumption
  end.

(* ========================================================= *)
(* Subqualifier well-formedness                               *)
(* ========================================================= *)

Lemma subqual_wf : forall E Q R, subqual E Q R ->
  wf_env E /\ wf_qua E Q /\ wf_qua E R.
Proof.
  intros E Q R H.
  induction H as [E Q Hwf HQ | E Q Hwf HQ | E Q' Q R0 b h1 IH1 hc h2 IH2 | E Q' Q R0 b h1 IH1 hc h2 IH2 | E b1 b2 Hwf Ho | E X Hwf HQ | R0 E Q X hb h1 IH1 | E R1 R2 Q h1 IH1 HR2 | E R1 R2 Q HR1 h2 IH1 | E R1 R2 Q h1 IH1 h2 IH2 | E R1 R2 Q h1 IH1 HR2 | E R1 R2 Q HR1 h2 IH1 | E R1 R2 Q h1 IH1 h2 IH2 | E Q R S Hwf HQ HR HS | E Q R S h1 IH1 h2 IH2 | E Q Hwf HQ | E Q Hwf HQ | E Q Hwf HQ].
  - repeat split; auto. constructor.
  - repeat split; auto. constructor.
  - destruct IH1 as [He [HQ HQ']]. destruct IH2 as [_ [_ HR]].
    repeat split; auto.
  - destruct IH1 as [He [HQ' HR]]. destruct IH2 as [_ [HQ _]].
    repeat split; auto.
  - repeat split; auto; constructor.
  - repeat split; auto.
  - destruct IH1 as [He [HR HQ]].
    repeat split; auto. eapply wf_qua_fvar. exact hb.
  - destruct IH1 as [He [HQ HR1]].
    repeat split; auto. constructor; auto.
  - destruct IH1 as [He [HQ HR2]].
    repeat split; auto. constructor; auto.
  - destruct IH1 as [He [HR1 HQ]]. destruct IH2 as [_ [HR2 _]].
    repeat split; auto. constructor; auto.
  - destruct IH1 as [He [HR1 HQ]].
    repeat split; auto. constructor; auto.
  - destruct IH1 as [He [HR2 HQ]].
    repeat split; auto. constructor; auto.
  - destruct IH1 as [He [HQ HR1]]. destruct IH2 as [_ [_ HR2]].
    repeat split; auto. constructor; auto.
  - repeat split; auto.
    + constructor; auto. constructor; auto.
    + constructor; auto. constructor; auto. constructor; auto.
  - destruct IH1 as [He [HQ HR]]. destruct IH2 as [_ [_ HS]].
    repeat split; auto.
  - repeat split; auto; try wf_qua_auto.
  - repeat split; auto; try wf_qua_auto.
  - repeat split; auto; try wf_qua_auto.
Qed.

(* ========================================================= *)
(* Subtyping well-formedness                                  *)
(* ========================================================= *)

Scheme sub_mut := Induction for sub Sort Prop
with subqtype_mut := Induction for subqtype Sort Prop.
Combined Scheme sub_tq_mut from sub_mut, subqtype_mut.

Lemma sub_subqtype_wf :
  (forall (E:env) (S T:typ), sub E S T ->
     wf_env E /\ wf_typ E S /\ wf_typ E T) /\
  (forall (E:env) (S T:qtyp), subqtype E S T ->
     wf_env E /\ wf_qtyp E S /\ wf_qtyp E T).
Proof.
  apply sub_tq_mut
    with (P := fun E S T _ => wf_env E /\ wf_typ E S /\ wf_typ E T)
         (P0 := fun E S T _ => wf_env E /\ wf_qtyp E S /\ wf_qtyp E T).
  - intros E S w w0. split; [auto|split; [auto|constructor]].
  - intros E w. split; [auto|split; constructor].
  - intros E X w w0. split; [auto|split; auto].
  - intros U E T X b s IH. destruct IH as [He [HU HT]].
    split; [auto|split].
    + eapply wf_typ_var. exact b.
    + auto.
  - intros E S1 S2 T1 T2 s IH1 s0 IH2.
    destruct IH1 as [He [HT1 HS1]]. destruct IH2 as [_ [HS2 HT2]].
    split; [auto|split].
    + apply wf_typ_arrow; auto.
    + apply wf_typ_arrow; auto.
  - intros L E S1 S2 T1 T2 s IH1 s0 IH0.
    destruct IH1 as [He [HT1 HS1]].
    split; [auto|split].
    + apply wf_typ_all with (L:=L).
      * auto.
      * intros X HX. destruct (IH0 X HX) as [_ [Hq _]].
        eapply wf_qtyp_bind_sub_irrel; eauto.
    + apply wf_typ_all with (L:=L).
      * auto.
      * intros X HX. destruct (IH0 X HX) as [_ [_ HT]].
        exact HT.
  - intros L E S1 S2 T1 T2 s s0 IH0.
    destruct (subqual_wf _ _ _ s) as [He [HT1 HS1]].
    split; [auto|split].
    + apply wf_typ_qall with (L:=L).
      * auto.
      * intros X HX. destruct (IH0 X HX) as [_ [Hq _]].
        eapply wf_qtyp_bind_qua_irrel; eauto.
    + apply wf_typ_qall with (L:=L).
      * auto.
      * intros X HX. destruct (IH0 X HX) as [_ [_ HT]].
        exact HT.
  - intros E S1 S2 T1 T2 s IH1 s0 IH2.
    destruct IH1 as [He [HS1 HT1]]. destruct IH2 as [_ [HS2 HT2]].
    split; [auto|split].
    + apply wf_typ_sum; auto.
    + apply wf_typ_sum; auto.
  - intros E S1 S2 T1 T2 s IH1 s0 IH2.
    destruct IH1 as [He [HS1 HT1]]. destruct IH2 as [_ [HS2 HT2]].
    split; [auto|split].
    + apply wf_typ_pair; auto.
    + apply wf_typ_pair; auto.
  - intros E Q1 T1 Q2 T2 s s0 IH.
    destruct (subqual_wf _ _ _ s) as [He [HQ1 HQ2]].
    destruct IH as [_ [HT1 HT2]].
    split; [auto|split].
    + apply wf_qtyp_qtyp; auto.
    + apply wf_qtyp_qtyp; auto.
Qed.

Lemma sub_wf : forall E S T, sub E S T ->
  wf_env E /\ wf_typ E S /\ wf_typ E T.
Proof. intros. eapply (proj1 sub_subqtype_wf); eauto. Qed.

Lemma subqtype_wf : forall E S T, subqtype E S T ->
  wf_env E /\ wf_qtyp E S /\ wf_qtyp E T.
Proof. intros. eapply (proj2 sub_subqtype_wf); eauto. Qed.

(* ========================================================= *)
(* wf_env implies its bindings are well-formed                *)
(* ========================================================= *)

Lemma wf_env_binds_typ : forall E x T,
  wf_env E -> binds x (bind_typ T) E -> wf_qtyp E T.
Proof.
  intros E xx TT H. induction H as [| E X U Hwf IH HT hf
    | E x0 T0 Hwf IH HT hf | E X Q Hwf IH HQ hf]; intros Hb.
  - unfold binds in Hb; destruct Hb.
  - unfold binds in Hb; destruct Hb as [Heq|Hb].
    + inversion Heq; subst; try (eapply wf_qtyp_extends; [|exact HT]; apply extends_app_l).
    + eapply wf_qtyp_extends; [|apply IH; exact Hb].
      apply extends_app_l.
  - unfold binds in Hb; destruct Hb as [Heq|Hb].
    + inversion Heq; subst; try (eapply wf_qtyp_extends; [|exact HT]; apply extends_app_l).
    + eapply wf_qtyp_extends; [|apply IH; exact Hb].
      apply extends_app_l.
  - unfold binds in Hb; destruct Hb as [Heq|Hb].
    + inversion Heq; subst; try (eapply wf_qtyp_extends; [|exact HT]; apply extends_app_l).
    + eapply wf_qtyp_extends; [|apply IH; exact Hb].
      apply extends_app_l.
Qed.

Lemma wf_env_binds_sub : forall E x U,
  wf_env E -> binds x (bind_sub U) E -> wf_typ E U.
Proof.
  intros E xx UU H. induction H as [| E X U Hwf IH HT hf
    | E x0 T0 Hwf IH HT hf | E X Q Hwf IH HQ hf]; intros Hb.
  - unfold binds in Hb; destruct Hb.
  - unfold binds in Hb; destruct Hb as [Heq|Hb].
    + inversion Heq; subst; try (eapply wf_typ_extends; [|exact HT]; apply extends_app_l).
    + eapply wf_typ_extends; [|apply IH; exact Hb].
      apply extends_app_l.
  - unfold binds in Hb; destruct Hb as [Heq|Hb].
    + inversion Heq; subst; try (eapply wf_typ_extends; [|exact HT]; apply extends_app_l).
    + eapply wf_typ_extends; [|apply IH; exact Hb].
      apply extends_app_l.
  - unfold binds in Hb; destruct Hb as [Heq|Hb].
    + inversion Heq; subst; try (eapply wf_typ_extends; [|exact HT]; apply extends_app_l).
    + eapply wf_typ_extends; [|apply IH; exact Hb].
      apply extends_app_l.
Qed.

Lemma wf_env_binds_qua : forall E x Q,
  wf_env E -> binds x (bind_qua Q) E -> wf_qua E Q.
Proof.
  intros E xx QQ H. induction H as [| E X U Hwf IH HT hf
    | E x0 T0 Hwf IH HT hf | E X Q0 Hwf IH HQ hf]; intros Hb.
  - unfold binds in Hb; destruct Hb.
  - unfold binds in Hb; destruct Hb as [Heq|Hb].
    + inversion Heq; subst; try (eapply wf_qua_extends; [|exact HQ]; apply extends_app_l).
    + eapply wf_qua_extends; [|apply IH; exact Hb].
      apply extends_app_l.
  - unfold binds in Hb; destruct Hb as [Heq|Hb].
    + inversion Heq; subst; try (eapply wf_qua_extends; [|exact HQ]; apply extends_app_l).
    + eapply wf_qua_extends; [|apply IH; exact Hb].
      apply extends_app_l.
  - unfold binds in Hb; destruct Hb as [Heq|Hb].
    + inversion Heq; subst; try (eapply wf_qua_extends; [|exact HQ]; apply extends_app_l).
    + eapply wf_qua_extends; [|apply IH; exact Hb].
      apply extends_app_l.
Qed.

Lemma typing_wf_env : forall E Q e T, typing E Q e T -> wf_env E.
Proof.
  intros E Q e T H. induction H; auto.
  - pick fresh z. apply wf_env_cons_inv with (x:=z) (b:=bind_typ V) (E:=E).
    match goal with IHw : forall x, x `notin` L -> wf_env (x ~ bind_typ ?VV ++ ?EE) |- _ => apply (IHw z Fr) end.
  - pick fresh z. apply wf_env_cons_inv with (x:=z) (b:=bind_sub V) (E:=E).
    match goal with IHw : forall x, x `notin` L -> wf_env (x ~ bind_sub ?VV ++ ?EE) |- _ => apply (IHw z Fr) end.
  - pick fresh z. apply wf_env_cons_inv with (x:=z) (b:=bind_qua Q) (E:=E).
    match goal with IHw : forall x, x `notin` L -> wf_env (x ~ bind_qua ?QQ ++ ?EE) |- _ => apply (IHw z Fr) end.
Qed.

Lemma typing_wf_qua : forall E Q e T, typing E Q e T -> wf_qua E Q.
Proof.
  intros E Q e T H. induction H; auto; try constructor.
  all: match goal with
       | s : subqual ?E ?Q ?R |- wf_qua ?E ?R =>
           destruct (subqual_wf _ _ _ s) as [_ [_ HR]]; exact HR
       end.
Qed.

Lemma typing_premise_bind_typ_wf : forall (L:atoms) (E:env) (T1:qtyp) (Q:qua) (e:exp) (T2:qtyp),
  (forall x : atom, x `notin` L -> typing (x ~ bind_typ T1 ++ E) Q (open_ee e x) T2) ->
  wf_qtyp E T1.
Proof.
  intros L E T1 Q e T2 H. pick fresh x for L.
  pose proof (typing_wf_env _ _ _ _ (H x Fr)) as Hwf.
  destruct (wf_env_typ_inv _ _ _ Hwf) as [_ [HV _]]; exact HV.
Qed.

Lemma typing_premise_bind_sub_wf : forall (L:atoms) (E:env) (V:typ) (Q:qua) (e:exp) (T2:atom -> qtyp),
  (forall X : atom, X `notin` L -> typing (X ~ bind_sub V ++ E) Q (open_te e X) (T2 X)) ->
  wf_typ E V.
Proof.
  intros L E V Q e T2 H. pick fresh X for L.
  pose proof (typing_wf_env _ _ _ _ (H X Fr)) as Hwf.
  destruct (wf_env_sub_inv _ _ _ Hwf) as [_ [HV _]]; exact HV.
Qed.

Lemma typing_premise_bind_qua_wf : forall (L:atoms) (E:env) (Qb:qua) (P:qua) (e:exp) (T2:atom -> qtyp),
  (forall X : atom, X `notin` L -> typing (X ~ bind_qua Qb ++ E) P (open_qe e X) (T2 X)) ->
  wf_qua E Qb.
Proof.
  intros L E Qb P e T2 H. pick fresh X for L.
  pose proof (typing_wf_env _ _ _ _ (H X Fr)) as Hwf.
  destruct (wf_env_qua_inv _ _ _ Hwf) as [_ [HQ _]]; exact HQ.
Qed.



(* ========================================================= *)
(* Monotonicity under environment extension                   *)
(* ========================================================= *)

Lemma subqual_extends : forall E Q R, subqual E Q R ->
  forall E', extends E E' -> wf_env E' -> subqual E' Q R.
Proof.
  intros E Q R H. induction H; intros E' Hext Hwf.
  - eapply subqual_top; eauto; try (eapply wf_qua_extends; eauto).
  - eapply subqual_bot; eauto; try (eapply wf_qua_extends; eauto).
  - eapply subqual_eval_elim; eauto; try (eapply wf_qua_extends; eauto).
  - eapply subqual_eval_intro; eauto; try (eapply wf_qua_extends; eauto).
  - eapply subqual_lift_elem; eauto; try (eapply wf_qua_extends; eauto).
  - eapply subqual_refl_qvar; eauto; try (eapply wf_qua_extends; eauto).
  - eapply subqual_trans_qvar; eauto; try (apply Hext; assumption).
  - eapply subqual_join_inl; eauto; try (eapply wf_qua_extends; eauto).
  - eapply subqual_join_inr; eauto; try (eapply wf_qua_extends; eauto).
  - eapply subqual_join_elim; eauto; try (eapply wf_qua_extends; eauto).
  - eapply subqual_meet_eliml; eauto; try (eapply wf_qua_extends; eauto).
  - eapply subqual_meet_elimr; eauto; try (eapply wf_qua_extends; eauto).
  - eapply subqual_meet_intro; eauto; try (eapply wf_qua_extends; eauto).
  - eapply subqual_dist; eauto; try (eapply wf_qua_extends; eauto).
  - eapply subqual_trans; eauto; try (eapply wf_qua_extends; eauto).
  - eapply subqual_negate_intro; eauto; try (eapply wf_qua_extends; eauto).
  - eapply subqual_negate_elim; eauto; try (eapply wf_qua_extends; eauto).
  - eapply subqual_refl_negate; eauto; try (eapply wf_qua_extends; eauto).
Qed.

Lemma sub_subqtype_extends :
  (forall (E:env) (S T:typ), sub E S T ->
     forall E', extends E E' -> wf_env E' -> sub E' S T) /\
  (forall (E:env) (S T:qtyp), subqtype E S T ->
     forall E', extends E E' -> wf_env E' -> subqtype E' S T).
Proof.
  apply sub_tq_mut
    with (P := fun E S T _ => forall E', extends E E' -> wf_env E' -> sub E' S T)
         (P0 := fun E S T _ => forall E', extends E E' -> wf_env E' -> subqtype E' S T).
  - intros E S w w0 E' Hext Hwf. eapply sub_top; eauto; try (eapply wf_typ_extends; eauto).
  - intros E w E' Hext Hwf. apply sub_refl_int; auto.
  - intros E X w w0 E' Hext Hwf. eapply sub_refl_tvar; eauto; try (eapply wf_typ_extends; eauto).
  - intros U E T X b s IH E' Hext Hwf. eapply sub_trans_tvar; eauto; try (apply Hext; exact b).
  - intros E S1 S2 T1 T2 s IH1 s0 IH2 E' Hext Hwf.
    eapply sub_arrow; eauto.
  - intros L E S1 S2 T1 T2 s IH1 s0 IH0 E' Hext Hwf.
    eapply sub_all with (L := L \u dom E').
    + apply (IH1 E' Hext Hwf).
    + intros X HX.
      assert (HXL : X `notin` L) by (exact (notin_union_1 X L (dom E') HX)).
      assert (HXd : X `notin` dom E') by (exact (notin_union_2 X L (dom E') HX)).
      apply (IH0 X HXL (X ~ bind_sub T1 ++ E')).
      * apply extends_cons_same; exact Hext.
      * apply wf_env_sub; auto.
        destruct (sub_wf _ _ _ (IH1 E' Hext Hwf)) as [_ [HT1 _]]; exact HT1.
  - intros L E S1 S2 T1 T2 s s0 IH0 E' Hext Hwf.
    eapply sub_qall with (L := L \u dom E').
    + eapply subqual_extends; eauto.
    + intros X HX.
      assert (HXL : X `notin` L) by (exact (notin_union_1 X L (dom E') HX)).
      assert (HXd : X `notin` dom E') by (exact (notin_union_2 X L (dom E') HX)).
      apply (IH0 X HXL (X ~ bind_qua T1 ++ E')).
      * apply extends_cons_same; exact Hext.
      * apply wf_env_qua; auto.
        destruct (subqual_wf _ _ _ (subqual_extends _ _ _ s E' Hext Hwf)) as [_ [HQ _]]; exact HQ.
  - intros E S1 S2 T1 T2 s IH1 s0 IH2 E' Hext Hwf.
    eapply sub_sum; eauto.
  - intros E S1 S2 T1 T2 s IH1 s0 IH2 E' Hext Hwf.
    eapply sub_pair; eauto.
  - intros E Q1 T1 Q2 T2 s s0 IH E' Hext Hwf.
    eapply sub_qtyp_qtyp.
    + eapply subqual_extends; eauto.
    + apply (IH E' Hext Hwf).
Qed.

Lemma sub_extends : forall E S T, sub E S T ->
  forall E', extends E E' -> wf_env E' -> sub E' S T.
Proof. intros. eapply (proj1 sub_subqtype_extends); eauto. Qed.

Lemma subqtype_extends : forall E S T, subqtype E S T ->
  forall E', extends E E' -> wf_env E' -> subqtype E' S T.
Proof. intros. eapply (proj2 sub_subqtype_extends); eauto. Qed.

Lemma typing_extends : forall E Q e T, typing E Q e T ->
  forall E', extends E E' -> wf_env E' -> typing E' Q e T.
Proof.
  intros E Q e T H.
  induction H as [E P0 i Hwfi HP
    | E x T Hwfv Hb
    | L0 E P0 V e1 T1 Hp IH
    | Qa T1 E e1 e2 T2 H1 IH1 H2 IH2
    | L0 E P0 V e1 T1 Hp IH
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P0 Qb e1 T1 HP Hp IH
    | Qa E e1 Qb T H1 IH1 Hs
    | S E Qa e Ta H1 IH1 Hs
    | E Qa R e Ta H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P0 T e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P0 e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P0 e E H1 IH1
    | Qa T1 T2 P0 e E H1 IH1
    | E R Qa T P0 e H1 IH1 Hs
    | E R Qa T P0 e H1 IH1 Hs
    | E R Qa T P0 e H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T H1 IH1 H2 IH2 H3 IH3].
  all: intros E' Hext HwfE.
  - eapply typing_int; eauto; try (eapply wf_qua_extends; eauto).
  - eapply typing_var; eauto; try (apply Hext; exact Hb).
  - eapply typing_abs with (L := L0 \u dom E').
    intros x HX.
    assert (HXL : x `notin` L0) by (exact (notin_union_1 x L0 (dom E') HX)).
    assert (HXd : x `notin` dom E') by (exact (notin_union_2 x L0 (dom E') HX)).
    apply (IH x HXL (x ~ bind_typ V ++ E')).
    + apply extends_cons_same. exact Hext.
    + apply wf_env_typ; auto.
      eapply wf_qtyp_extends; eauto.
      apply (typing_premise_bind_typ_wf L0 E V P0 e1 T1 Hp).
  - eapply typing_app; [apply (IH1 E' Hext HwfE) | apply (IH2 E' Hext HwfE)].
  - eapply typing_tabs with (L := L0 \u dom E').
    intros X HX.
    assert (HXL : X `notin` L0) by (exact (notin_union_1 X L0 (dom E') HX)).
    assert (HXd : X `notin` dom E') by (exact (notin_union_2 X L0 (dom E') HX)).
    apply (IH X HXL (X ~ bind_sub V ++ E')).
    + apply extends_cons_same. exact Hext.
    + apply wf_env_sub; auto.
      eapply wf_typ_extends; eauto.
      apply (typing_premise_bind_sub_wf L0 E V P0 e1 (fun X => open_tqt T1 X) Hp).
  - eapply typing_tapp; [apply (IH1 E' Hext HwfE) | eapply sub_extends; eauto].
  - eapply typing_qabs with (L := L0 \u dom E').
    + eapply wf_qua_extends; eauto.
    + intros X HX.
      assert (HXL : X `notin` L0) by (exact (notin_union_1 X L0 (dom E') HX)).
      assert (HXd : X `notin` dom E') by (exact (notin_union_2 X L0 (dom E') HX)).
      apply (IH X HXL (X ~ bind_qua Qb ++ E')).
      * apply extends_cons_same. exact Hext.
      * apply wf_env_qua; auto.
        eapply wf_qua_extends; eauto.
        apply (typing_premise_bind_qua_wf L0 E Qb P0 e1 (fun X => open_qqt T1 X) Hp).
  - eapply typing_qapp; [apply (IH1 E' Hext HwfE) | eapply subqual_extends; eauto].
  - eapply typing_sub; [apply (IH1 E' Hext HwfE) | eapply subqtype_extends; eauto].
  - eapply typing_subqual; [apply (IH1 E' Hext HwfE) | eapply subqual_extends; eauto].
  - eapply typing_let with (L := L \u dom E').
    + apply (IH1 E' Hext HwfE).
    + intros x HX.
      assert (HXL : x `notin` L) by (exact (notin_union_1 x L (dom E') HX)).
      assert (HXd : x `notin` dom E') by (exact (notin_union_2 x L (dom E') HX)).
      apply (IH2 x HXL (x ~ bind_typ T1 ++ E')).
      * apply extends_cons_same. exact Hext.
      * apply wf_env_typ; auto.
        eapply wf_qtyp_extends; eauto.
        apply (typing_premise_bind_typ_wf L E T1 Qa e2 T2 H2).
  - eapply typing_inl.
    + eapply wf_qua_extends; eauto.
    + apply (IH1 E' Hext HwfE).
    + eapply wf_qtyp_extends; eauto.
  - eapply typing_inr.
    + eapply wf_qua_extends; eauto.
    + apply (IH1 E' Hext HwfE).
    + eapply wf_qtyp_extends; eauto.
  - eapply typing_case with (L := L \u dom E').
    + apply (IH1 E' Hext HwfE).
    + intros x HX.
      assert (HXL : x `notin` L) by (exact (notin_union_1 x L (dom E') HX)).
      assert (HXd : x `notin` dom E') by (exact (notin_union_2 x L (dom E') HX)).
      apply (IH2 x HXL (x ~ bind_typ T1 ++ E')).
      * apply extends_cons_same. exact Hext.
      * apply wf_env_typ; auto.
        eapply wf_qtyp_extends; eauto.
        apply (typing_premise_bind_typ_wf L E T1 Qa e2 T H2).
    + intros x HX.
      assert (HXL : x `notin` L) by (exact (notin_union_1 x L (dom E') HX)).
      assert (HXd : x `notin` dom E') by (exact (notin_union_2 x L (dom E') HX)).
      apply (IH3 x HXL (x ~ bind_typ T2 ++ E')).
      * apply extends_cons_same. exact Hext.
      * apply wf_env_typ; auto.
        eapply wf_qtyp_extends; eauto.
        apply (typing_premise_bind_typ_wf L E T2 Qa e3 T H3).
  - eapply typing_pair.
    + eapply wf_qua_extends; eauto.
    + apply (IH1 E' Hext HwfE).
    + apply (IH2 E' Hext HwfE).
  - eapply typing_first. apply (IH1 E' Hext HwfE).
  - eapply typing_second. apply (IH1 E' Hext HwfE).
  - eapply typing_upqual; [apply (IH1 E' Hext HwfE) | eapply subqual_extends; eauto].
  - eapply typing_check; [apply (IH1 E' Hext HwfE) | eapply subqual_extends; eauto].
  - eapply typing_without; [apply (IH1 E' Hext HwfE) | eapply subqual_extends; eauto].
  - apply typing_do. exact HwfE.
  - eapply typing_if0; [apply (IH1 E' Hext HwfE) | apply (IH2 E' Hext HwfE) | apply (IH3 E' Hext HwfE)].
Qed.

Lemma typing_ctx_extends : forall E Q c T U, typing_ctx E Q c T U ->
  forall E', extends E E' -> wf_env E' -> typing_ctx E' Q c T U.
Proof.
  intros E Q c T U H.
  induction H as [E Q0 T0 w wq wT
    | E Q0 c0 e1 T1 T2 U0 t0 IH t1
    | E Q0 c0 e1 T1 T2 U0 t0 IH v t1
    | L E Q0 c0 T1 T1' T2 U0 t0 IH s w
    | L E Q0 c0 R R' T2 U0 t0 IH s w
    | L E Q0 c0 e1 T1 T2 U0 t0 IH t1
    | E P0 Q0 c0 T1 T2 U0 t0 IH
    | E P0 Q0 c0 T1 T2 U0 t0 IH
    | L E P0 Q0 c0 T0 T1 T2 e2 e3 U0 w t0 IH t1 t2
    | E P0 Q0 c0 e T1 T2 U0 w t0 IH t1
    | E P0 Q0 c0 v T1 T2 U0 w t0 IH v0 t1
    | E P0 Q0 c0 T1 T2 U0 w t0 IH w0
    | E P0 Q0 c0 T1 T2 U0 w t0 IH w0
    | E Q0 c0 s t T0 U0 t0 IH cv ord
    | E Q0 c0 P0 T0 U0 t0 IH
    | E Q0 c0 R P0 T0 U0 w t0 IH
    | E Q0 c0 S T0 U0 t0 IH s
    | E Q0 R c0 T0 U0 t0 IH s
    | E Q0 c0 t T0 U0 t0 IH
    | E R c0 e2 e3 T0 Q0 U0 w t0 IH t1 t2].
  all: intros E' Hext HwfE.
  - eapply typing_ctx_done; eauto; try (eapply wf_qua_extends; eauto); try (eapply wf_qtyp_extends; eauto).
  - eapply typing_ctx_abs.
    + apply (IH E' Hext HwfE).
    + eapply typing_extends; eauto.
  - eapply typing_ctx_app.
    + apply (IH E' Hext HwfE).
    + exact v.
    + eapply typing_extends; eauto.
  - eapply typing_ctx_tabs with (L := L \u dom E').
    + apply (IH E' Hext HwfE).
    + eapply sub_extends; eauto.
    + intros X HX.
      assert (HXL : X `notin` L) by (exact (notin_union_1 X L (dom E') HX)).
      eapply wf_qtyp_extends; [apply extends_cons_same; exact Hext | apply (w X HXL)].
  - eapply typing_ctx_qabs with (L := L \u dom E').
    + apply (IH E' Hext HwfE).
    + eapply subqual_extends; eauto.
    + intros X HX.
      assert (HXL : X `notin` L) by (exact (notin_union_1 X L (dom E') HX)).
      eapply wf_qtyp_extends; [apply extends_cons_same; exact Hext | apply (w X HXL)].
  - eapply typing_ctx_let with (L := L \u dom E').
    + apply (IH E' Hext HwfE).
    + intros x HX.
      assert (HXL : x `notin` L) by (exact (notin_union_1 x L (dom E') HX)).
      assert (HXd : x `notin` dom E') by (exact (notin_union_2 x L (dom E') HX)).
      eapply typing_extends.
      * apply (t1 x HXL).
      * apply extends_cons_same. exact Hext.
      * apply wf_env_typ; auto.
        eapply wf_qtyp_extends; eauto.
        apply (typing_premise_bind_typ_wf L E T1 Q0 e1 T2 t1).
  - eapply typing_ctx_inl. apply (IH E' Hext HwfE).
  - eapply typing_ctx_inr. apply (IH E' Hext HwfE).
  - eapply typing_ctx_case with (L := L \u dom E').
    + eapply wf_qua_extends; eauto.
    + apply (IH E' Hext HwfE).
    + intros x HX.
      assert (HXL : x `notin` L) by (exact (notin_union_1 x L (dom E') HX)).
      assert (HXd : x `notin` dom E') by (exact (notin_union_2 x L (dom E') HX)).
      eapply typing_extends.
      * apply (t1 x HXL).
      * apply extends_cons_same. exact Hext.
      * apply wf_env_typ; auto.
        eapply wf_qtyp_extends; eauto.
        apply (typing_premise_bind_typ_wf L E T1 Q0 e2 T0 t1).
    + intros x HX.
      assert (HXL : x `notin` L) by (exact (notin_union_1 x L (dom E') HX)).
      assert (HXd : x `notin` dom E') by (exact (notin_union_2 x L (dom E') HX)).
      eapply typing_extends.
      * apply (t2 x HXL).
      * apply extends_cons_same. exact Hext.
      * apply wf_env_typ; auto.
        eapply wf_qtyp_extends; eauto.
        apply (typing_premise_bind_typ_wf L E T2 Q0 e3 T0 t2).
  - eapply typing_ctx_pair_1.
    + eapply wf_qua_extends; eauto.
    + apply (IH E' Hext HwfE).
    + eapply typing_extends; eauto.
  - eapply typing_ctx_pair_2.
    + eapply wf_qua_extends; eauto.
    + apply (IH E' Hext HwfE).
    + exact v0.
    + eapply typing_extends; eauto.
  - eapply typing_ctx_first.
    + eapply wf_qua_extends; eauto.
    + apply (IH E' Hext HwfE).
    + eapply wf_qtyp_extends; eauto.
  - eapply typing_ctx_second.
    + eapply wf_qua_extends; eauto.
    + apply (IH E' Hext HwfE).
    + eapply wf_qtyp_extends; eauto.
  - eapply typing_ctx_barrier.
    + apply (IH E' Hext HwfE).
    + exact cv.
    + exact ord.
  - eapply typing_ctx_upqual. apply (IH E' Hext HwfE).
  - eapply typing_ctx_check.
    + eapply wf_qua_extends; eauto.
    + apply (IH E' Hext HwfE).
  - eapply typing_ctx_sub.
    + apply (IH E' Hext HwfE).
    + eapply subqtype_extends; eauto.
  - eapply typing_ctx_subqual.
    + apply (IH E' Hext HwfE).
    + eapply subqual_extends; eauto.
  - eapply typing_ctx_without. apply (IH E' Hext HwfE).
  - eapply typing_ctx_if0.
    + eapply wf_qua_extends; eauto.
    + apply (IH E' Hext HwfE).
    + eapply typing_extends; eauto.
    + eapply typing_extends; eauto.
Qed.

(* ========================================================= *)
(* Free variable and substitution helper lemmas               *)
(* ========================================================= *)

Definition fv_tt_qtyp (T:qtyp) : atoms :=
  match T with qtyp_qtyp _ T' => fv_tt T' end.

Lemma notin_singleton_eq_false : forall X, X `notin` singleton X -> False.
Proof. intros X H. exact (notin_singleton_1 X X H eq_refl). Qed.

Fixpoint subst_tt_id (T:typ) {struct T} :
  forall X V, X `notin` fv_tt T -> subst_tt X V T = T
with subst_tqt_id (T:qtyp) {struct T} :
  forall X V, X `notin` fv_tqt T -> subst_tqt X V T = T.
Proof.
  - destruct T; intros X V H; simpl in *.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + destruct (eq_dec a X) as [Heq|Hneq].
      * subst. match goal with H' : ?Z `notin` singleton ?Z |- _ => exfalso; exact (notin_singleton_eq_false Z H') end.
      * reflexivity.
    + apply f_equal2.
      * apply subst_tqt_id. exact (notin_union_1 _ _ _ H).
      * apply subst_tqt_id. exact (notin_union_2 _ _ _ H).
    + apply f_equal2.
      * apply subst_tt_id. exact (notin_union_1 _ _ _ H).
      * apply subst_tqt_id. exact (notin_union_2 _ _ _ H).
    + apply f_equal. apply subst_tqt_id. exact H.
    + apply f_equal2.
      * apply subst_tqt_id. exact (notin_union_1 _ _ _ H).
      * apply subst_tqt_id. exact (notin_union_2 _ _ _ H).
    + apply f_equal2.
      * apply subst_tqt_id. exact (notin_union_1 _ _ _ H).
      * apply subst_tqt_id. exact (notin_union_2 _ _ _ H).
    + apply f_equal. apply subst_tqt_id. exact H.
  - destruct T as [Q T]. intros X V H. simpl in *.
    apply f_equal. apply subst_tt_id. exact H.
Qed.

Fixpoint subst_qq_id (Q:qua) {struct Q} :
  forall X R, X `notin` fv_qq Q -> subst_qq X R Q = Q.
Proof.
  destruct Q; intros X R H; simpl in *.
  - reflexivity.
  - reflexivity.
  - destruct (eq_dec a X) as [Heq|Hneq].
    + subst. match goal with H' : ?Z `notin` singleton ?Z |- _ => exfalso; exact (notin_singleton_eq_false Z H') end.
    + reflexivity.
  - f_equal; [apply subst_qq_id; exact (notin_union_1 _ _ _ H)
            |apply subst_qq_id; exact (notin_union_2 _ _ _ H)].
  - f_equal; [apply subst_qq_id; exact (notin_union_1 _ _ _ H)
            |apply subst_qq_id; exact (notin_union_2 _ _ _ H)].
  - f_equal. apply subst_qq_id. exact H.
Qed.

Fixpoint subst_qt_id (T:typ) {struct T} :
  forall X R, X `notin` fv_qt T -> subst_qt X R T = T
with subst_qqt_id (T:qtyp) {struct T} :
  forall X R, X `notin` fv_qqt T -> subst_qqt X R T = T.
Proof.
  - destruct T; intros X R H; simpl in *.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + f_equal; [apply subst_qqt_id; exact (notin_union_1 _ _ _ H)
              |apply subst_qqt_id; exact (notin_union_2 _ _ _ H)].
    + f_equal; [apply subst_qt_id; exact (notin_union_1 _ _ _ H)
              |apply subst_qqt_id; exact (notin_union_2 _ _ _ H)].
    + f_equal; [apply subst_qq_id; exact (notin_union_1 _ _ _ H)
              |apply subst_qqt_id; exact (notin_union_2 _ _ _ H)].
    + f_equal; [apply subst_qqt_id; exact (notin_union_1 _ _ _ H)
              |apply subst_qqt_id; exact (notin_union_2 _ _ _ H)].
    + f_equal; [apply subst_qqt_id; exact (notin_union_1 _ _ _ H)
              |apply subst_qqt_id; exact (notin_union_2 _ _ _ H)].
    + f_equal. apply subst_qqt_id. exact H.
  - destruct T as [Q T]. intros X R H. simpl in *.
    f_equal; [apply subst_qq_id; exact (notin_union_1 _ _ _ H)
            |apply subst_qt_id; exact (notin_union_2 _ _ _ H)].
Qed.

Ltac notin_split_all :=
  repeat match goal with
  | H : ?X `notin` (?A `union` ?B) |- _ =>
      let H1 := fresh "HN" in let H2 := fresh "HN" in
      assert (H1 : X `notin` A) by exact (notin_union_1 _ _ _ H);
      assert (H2 : X `notin` B) by exact (notin_union_2 _ _ _ H);
      clear H
  end.

Ltac solve_notin_H := notin_split_all; eassumption.

Ltac solve_subst_id :=
  first [ reflexivity
        | apply subst_tqt_id; solve_notin_H
        | apply subst_tt_id; solve_notin_H
        | apply subst_qq_id; solve_notin_H
        | apply subst_qt_id; solve_notin_H
        | apply subst_qqt_id; solve_notin_H
        | match goal with
          | |- (if ?a == ?X then ?v else ?E) = ?E =>
              destruct (eq_dec a X) as [Heq|Hneq];
              [ subst; simpl in *;
                match goal with H' : ?Z `notin` singleton ?Z |- _ =>
                  exfalso; exact (notin_singleton_eq_false Z H') end
              | reflexivity ]
          end ].

Fixpoint subst_te_id (e:exp) {struct e} :
  forall X V, X `notin` fv_te e -> subst_te X V e = e.
Proof.
  destruct e; intros X V H; simpl in *; try reflexivity;
    try (f_equal; try solve_subst_id).
  all: try (apply subst_te_id; solve_notin_H).
Qed.

Fixpoint subst_qe_id (e:exp) {struct e} :
  forall X R, X `notin` fv_qe e -> subst_qe X R e = e.
Proof.
  destruct e; intros X R H; simpl in *; try reflexivity;
    try (f_equal; try solve_subst_id).
  all: try (apply subst_qe_id; solve_notin_H).
Qed.

Ltac solve_ee_fvar :=
  match goal with
  | |- subst_ee ?X ?v (exp_fvar ?a) = exp_fvar ?a =>
      destruct (eq_dec a X) as [Heq|Hneq];
      [ subst; simpl in *;
        match goal with H' : ?Z `notin` singleton ?Z |- _ =>
          exfalso; exact (notin_singleton_eq_false Z H') end
      | simpl; reflexivity ]
  end.

Fixpoint subst_ee_id (e:exp) {struct e} :
  forall X v, X `notin` fv_ee e -> subst_ee X v e = e.
Proof.
  destruct e; intros X v H; try solve_ee_fvar; simpl in *; try reflexivity;
    try f_equal.
  all: try solve_subst_id.
  all: try (apply subst_ee_id; solve_notin_H).
Qed.

(* closedness of types/qualifiers *)
Fixpoint no_bvar_tt (T:typ) : Prop :=
  match T with
  | typ_top => True
  | typ_int => True
  | typ_bvar _ => False
  | typ_fvar _ => True
  | typ_arrow T1 T2 => no_bvar_tqt T1 /\ no_bvar_tqt T2
  | typ_all T1 T2 => no_bvar_tt T1 /\ no_bvar_tqt T2
  | typ_qall Q T => no_bvar_tqt T
  | typ_sum T1 T2 => no_bvar_tqt T1 /\ no_bvar_tqt T2
  | typ_pair T1 T2 => no_bvar_tqt T1 /\ no_bvar_tqt T2
  | typ_ref T1 => no_bvar_tqt T1
  end
with no_bvar_tqt (T:qtyp) : Prop :=
  match T with qtyp_qtyp Q T' => no_bvar_tt T' end.

Fixpoint no_bvar_qq (Q:qua) : Prop :=
  match Q with
  | qua_base _ => True
  | qua_bvar _ => False
  | qua_fvar _ => True
  | qua_meet Q1 Q2 => no_bvar_qq Q1 /\ no_bvar_qq Q2
  | qua_join Q1 Q2 => no_bvar_qq Q1 /\ no_bvar_qq Q2
  | qua_negate Q1 => no_bvar_qq Q1
  end.

Fixpoint open_tt_rec_closed (T:typ) {struct T} :
  forall K U, no_bvar_tt T -> open_tt_rec K U T = T
with open_tqt_rec_closed (T:qtyp) {struct T} :
  forall K U, no_bvar_tqt T -> open_tqt_rec K U T = T.
Proof.
  - destruct T; intros K U H; simpl in *; try reflexivity.
    + destruct H.
    + destruct H as [H1 H2]. f_equal; [apply open_tqt_rec_closed; exact H1 | apply open_tqt_rec_closed; exact H2].
    + destruct H as [H1 H2]. f_equal; [apply open_tt_rec_closed; exact H1 | apply open_tqt_rec_closed; exact H2].
    + f_equal. apply open_tqt_rec_closed. exact H.
    + destruct H as [H1 H2]. f_equal; [apply open_tqt_rec_closed; exact H1 | apply open_tqt_rec_closed; exact H2].
    + destruct H as [H1 H2]. f_equal; [apply open_tqt_rec_closed; exact H1 | apply open_tqt_rec_closed; exact H2].
    + f_equal. apply open_tqt_rec_closed. exact H.
  - destruct T as [Q T]. intros K U H. simpl in *. f_equal. apply open_tt_rec_closed. exact H.
Qed.

Fixpoint open_qq_rec_closed (Q:qua) {struct Q} :
  forall K R, no_bvar_qq Q -> open_qq_rec K R Q = Q.
Proof.
  destruct Q; intros K R H; simpl in *; try reflexivity.
  - destruct H.
  - destruct H as [H1 H2]. f_equal; [apply open_qq_rec_closed; exact H1 | apply open_qq_rec_closed; exact H2].
  - destruct H as [H1 H2]. f_equal; [apply open_qq_rec_closed; exact H1 | apply open_qq_rec_closed; exact H2].
  - f_equal. apply open_qq_rec_closed. exact H.
Qed.

Definition closed_tt (V:typ) : Prop := forall K U, open_tt_rec K U V = V.
Definition closed_qq (R:qua) : Prop := forall K R0, open_qq_rec K R0 R = R.

Fixpoint subst_tt_open_tt_rec (T:typ) {struct T} :
  forall K U X V, closed_tt V ->
    subst_tt X V (open_tt_rec K U T) = open_tt_rec K (subst_tt X V U) (subst_tt X V T)
with subst_tqt_open_tqt_rec (T:qtyp) {struct T} :
  forall K U X V, closed_tt V ->
    subst_tqt X V (open_tqt_rec K U T) = open_tqt_rec K (subst_tt X V U) (subst_tqt X V T).
Proof.
  - destruct T; intros K U X V Hc; simpl.
    + reflexivity.
    + reflexivity.
    + destruct (eq_dec K n) as [Heq|Hneq]; simpl; reflexivity.
    + destruct (eq_dec a X) as [Heq|Hneq]; simpl.
      * rewrite Hc; reflexivity.
      * reflexivity.
    + f_equal;
      [rewrite (subst_tqt_open_tqt_rec _ K U X V Hc) | rewrite (subst_tqt_open_tqt_rec _ (S K) U X V Hc)]; reflexivity.
    + f_equal;
      [rewrite (subst_tt_open_tt_rec _ K U X V Hc) | rewrite (subst_tqt_open_tqt_rec _ (S K) U X V Hc)]; reflexivity.
    + f_equal. rewrite (subst_tqt_open_tqt_rec _ (S K) U X V Hc). reflexivity.
    + f_equal;
      [rewrite (subst_tqt_open_tqt_rec _ K U X V Hc) | rewrite (subst_tqt_open_tqt_rec _ K U X V Hc)]; reflexivity.
    + f_equal;
      [rewrite (subst_tqt_open_tqt_rec _ K U X V Hc) | rewrite (subst_tqt_open_tqt_rec _ K U X V Hc)]; reflexivity.
    + f_equal. rewrite (subst_tqt_open_tqt_rec _ K U X V Hc). reflexivity.
  - destruct T as [Q T]. intros K U X V Hc. simpl.
    f_equal. rewrite (subst_tt_open_tt_rec _ K U X V Hc). reflexivity.
Qed.

Fixpoint subst_te_open_te_rec (e:exp) {struct e} :
  forall K U X V, closed_tt V ->
    subst_te X V (open_te_rec K U e) = open_te_rec K (subst_tt X V U) (subst_te X V e).
Proof.
  destruct e; intros K U X V Hc; simpl; try reflexivity.
  all: try f_equal.
  all: try (rewrite (subst_tqt_open_tqt_rec _ _ U X V Hc); reflexivity).
  all: try (rewrite (subst_tt_open_tt_rec _ _ U X V Hc); reflexivity).
  all: try (rewrite (subst_te_open_te_rec _ _ U X V Hc); reflexivity).
  all: try reflexivity.
Qed.

Lemma subst_tt_atom_eq : forall X Y V, Y <> X -> subst_tt X V (typ_fvar Y) = typ_fvar Y.
Proof.
  intros. simpl. destruct (eq_dec Y X) as [Heq|Hneq].
  - exfalso. exact (H Heq).
  - reflexivity.
Qed.

Lemma subst_tt_atom_self : forall X V, subst_tt X V (typ_fvar X) = V.
Proof. intros. simpl. destruct (eq_dec X X); [reflexivity | exfalso; apply n; reflexivity]. Qed.

Lemma subst_te_open_te_atom : forall (e:exp) X V Y,
  closed_tt V -> Y <> X ->
  subst_te X V (open_te e Y) = open_te (subst_te X V e) Y.
Proof.
  intros. unfold open_te.
  rewrite subst_te_open_te_rec with (U:=typ_fvar Y) by exact H.
  rewrite subst_tt_atom_eq by exact H0. reflexivity.
Qed.

Lemma subst_te_open_te_self : forall (e:exp) X V,
  closed_tt V ->
  subst_te X V (open_te e X) = open_te (subst_te X V e) V.
Proof.
  intros. unfold open_te.
  rewrite subst_te_open_te_rec with (U:=typ_fvar X) by exact H.
  rewrite subst_tt_atom_self. reflexivity.
Qed.

Lemma subst_tt_open_tt_atom : forall (T:typ) X V Y,
  closed_tt V -> Y <> X ->
  subst_tt X V (open_tt T Y) = open_tt (subst_tt X V T) Y.
Proof.
  intros. unfold open_tt.
  rewrite subst_tt_open_tt_rec with (U:=typ_fvar Y) by exact H.
  rewrite subst_tt_atom_eq by exact H0. reflexivity.
Qed.

Lemma subst_tqt_open_tqt_atom : forall (T:qtyp) X V Y,
  closed_tt V -> Y <> X ->
  subst_tqt X V (open_tqt T Y) = open_tqt (subst_tqt X V T) Y.
Proof.
  intros. unfold open_tqt.
  rewrite subst_tqt_open_tqt_rec with (U:=typ_fvar Y) by exact H.
  rewrite subst_tt_atom_eq by exact H0. reflexivity.
Qed.

Lemma subst_tqt_open_tqt_self : forall (T:qtyp) X V,
  closed_tt V ->
  subst_tqt X V (open_tqt T X) = open_tqt (subst_tqt X V T) V.
Proof.
  intros. unfold open_tqt.
  rewrite subst_tqt_open_tqt_rec with (U:=typ_fvar X) by exact H.
  rewrite subst_tt_atom_self. reflexivity.
Qed.

Fixpoint subst_qq_open_qq_rec (Q:qua) {struct Q} :
  forall K R0 X R, closed_qq R ->
    subst_qq X R (open_qq_rec K R0 Q) = open_qq_rec K (subst_qq X R R0) (subst_qq X R Q).
Proof.
  destruct Q; intros K R0 X R Hc; simpl.
  - reflexivity.
  - destruct (eq_dec K n) as [Heq|Hneq]; simpl; reflexivity.
  - destruct (eq_dec a X) as [Heq|Hneq]; simpl.
    + rewrite Hc; reflexivity.
    + reflexivity.
  - f_equal; [rewrite (subst_qq_open_qq_rec _ K R0 X R Hc)
            | rewrite (subst_qq_open_qq_rec _ K R0 X R Hc)]; reflexivity.
  - f_equal; [rewrite (subst_qq_open_qq_rec _ K R0 X R Hc)
            | rewrite (subst_qq_open_qq_rec _ K R0 X R Hc)]; reflexivity.
  - f_equal. rewrite (subst_qq_open_qq_rec _ K R0 X R Hc). reflexivity.
Qed.

Fixpoint subst_qt_open_qt_rec (T:typ) {struct T} :
  forall K R0 X R, closed_qq R ->
    subst_qt X R (open_qt_rec K R0 T) = open_qt_rec K (subst_qq X R R0) (subst_qt X R T)
with subst_qqt_open_qqt_rec (T:qtyp) {struct T} :
  forall K R0 X R, closed_qq R ->
    subst_qqt X R (open_qqt_rec K R0 T) = open_qqt_rec K (subst_qq X R R0) (subst_qqt X R T).
Proof.
  - destruct T; intros K R0 X R Hc; simpl; try reflexivity.
    + f_equal;
      [rewrite (subst_qqt_open_qqt_rec _ K R0 X R Hc)
      |rewrite (subst_qqt_open_qqt_rec _ (S K) R0 X R Hc)]; reflexivity.
    + f_equal;
      [rewrite (subst_qt_open_qt_rec _ K R0 X R Hc)
      |rewrite (subst_qqt_open_qqt_rec _ (S K) R0 X R Hc)]; reflexivity.
    + f_equal;
      [rewrite (subst_qq_open_qq_rec _ K R0 X R Hc)
      |rewrite (subst_qqt_open_qqt_rec _ (S K) R0 X R Hc)]; reflexivity.
    + f_equal;
      [rewrite (subst_qqt_open_qqt_rec _ K R0 X R Hc)
      |rewrite (subst_qqt_open_qqt_rec _ K R0 X R Hc)]; reflexivity.
    + f_equal;
      [rewrite (subst_qqt_open_qqt_rec _ K R0 X R Hc)
      |rewrite (subst_qqt_open_qqt_rec _ K R0 X R Hc)]; reflexivity.
    + f_equal. rewrite (subst_qqt_open_qqt_rec _ K R0 X R Hc). reflexivity.
  - destruct T as [Q T]. intros K R0 X R Hc. simpl. f_equal.
    + rewrite (subst_qq_open_qq_rec _ K R0 X R Hc). reflexivity.
    + rewrite (subst_qt_open_qt_rec _ K R0 X R Hc). reflexivity.
Qed.

Fixpoint subst_qe_open_qe_rec (e:exp) {struct e} :
  forall K R0 X R, closed_qq R ->
    subst_qe X R (open_qe_rec K R0 e) = open_qe_rec K (subst_qq X R R0) (subst_qe X R e).
Proof.
  destruct e; intros K R0 X R Hc; simpl; try reflexivity.
  all: try f_equal.
  all: try (rewrite (subst_qq_open_qq_rec _ _ R0 X R Hc); reflexivity).
  all: try (rewrite (subst_qt_open_qt_rec _ _ R0 X R Hc); reflexivity).
  all: try (rewrite (subst_qqt_open_qqt_rec _ _ R0 X R Hc); reflexivity).
  all: try (rewrite (subst_qe_open_qe_rec _ _ R0 X R Hc); reflexivity).
  all: try reflexivity.
Qed.

Lemma subst_qq_atom_eq : forall X Y R, Y <> X -> subst_qq X R (qua_fvar Y) = qua_fvar Y.
Proof.
  intros. simpl. destruct (eq_dec Y X) as [Heq|Hneq].
  - exfalso. exact (H Heq).
  - reflexivity.
Qed.

Lemma subst_qq_atom_self : forall X R, subst_qq X R (qua_fvar X) = R.
Proof. intros. simpl. destruct (eq_dec X X); [reflexivity | exfalso; apply n; reflexivity]. Qed.

Lemma subst_qe_open_qe_atom : forall (e:exp) X R Y,
  closed_qq R -> Y <> X ->
  subst_qe X R (open_qe e Y) = open_qe (subst_qe X R e) Y.
Proof.
  intros. unfold open_qe.
  rewrite subst_qe_open_qe_rec with (R0:=qua_fvar Y) by exact H.
  rewrite subst_qq_atom_eq by exact H0. reflexivity.
Qed.

Lemma subst_qe_open_qe_self : forall (e:exp) X R,
  closed_qq R ->
  subst_qe X R (open_qe e X) = open_qe (subst_qe X R e) R.
Proof.
  intros. unfold open_qe.
  rewrite subst_qe_open_qe_rec with (R0:=qua_fvar X) by exact H.
  rewrite subst_qq_atom_self. reflexivity.
Qed.

Lemma subst_qt_open_qt_atom : forall (T:typ) X R Y,
  closed_qq R -> Y <> X ->
  subst_qt X R (open_qt T Y) = open_qt (subst_qt X R T) Y.
Proof.
  intros. unfold open_qt.
  rewrite subst_qt_open_qt_rec with (R0:=qua_fvar Y) by exact H.
  rewrite subst_qq_atom_eq by exact H0. reflexivity.
Qed.

Lemma subst_qqt_open_qqt_atom : forall (T:qtyp) X R Y,
  closed_qq R -> Y <> X ->
  subst_qqt X R (open_qqt T Y) = open_qqt (subst_qqt X R T) Y.
Proof.
  intros. unfold open_qqt.
  rewrite subst_qqt_open_qqt_rec with (R0:=qua_fvar Y) by exact H.
  rewrite subst_qq_atom_eq by exact H0. reflexivity.
Qed.

Lemma subst_qqt_open_qqt_self : forall (T:qtyp) X R,
  closed_qq R ->
  subst_qqt X R (open_qqt T X) = open_qqt (subst_qqt X R T) R.
Proof.
  intros. unfold open_qqt.
  rewrite subst_qqt_open_qqt_rec with (R0:=qua_fvar X) by exact H.
  rewrite subst_qq_atom_self. reflexivity.
Qed.

(* locally-closed (with depth) for type bvars and qualifier bvars *)
Fixpoint lc_tt (T:typ) (d:nat) : Prop :=
  match T with
  | typ_top => True
  | typ_int => True
  | typ_bvar n => n < d
  | typ_fvar _ => True
  | typ_arrow T1 T2 => lc_tqt T1 d /\ lc_tqt T2 (S d)
  | typ_all T1 T2 => lc_tt T1 d /\ lc_tqt T2 (S d)
  | typ_qall Q T => lc_tqt T (S d)
  | typ_sum T1 T2 => lc_tqt T1 d /\ lc_tqt T2 d
  | typ_pair T1 T2 => lc_tqt T1 d /\ lc_tqt T2 d
  | typ_ref T1 => lc_tqt T1 d
  end
with lc_tqt (T:qtyp) (d:nat) : Prop :=
  match T with qtyp_qtyp Q T' => lc_tt T' d end.

Fixpoint lc_qq (Q:qua) (d:nat) : Prop :=
  match Q with
  | qua_base _ => True
  | qua_bvar n => n < d
  | qua_fvar _ => True
  | qua_meet Q1 Q2 => lc_qq Q1 d /\ lc_qq Q2 d
  | qua_join Q1 Q2 => lc_qq Q1 d /\ lc_qq Q2 d
  | qua_negate Q1 => lc_qq Q1 d
  end.

Fixpoint lc_qqt (T:qtyp) (d:nat) : Prop :=
  match T with qtyp_qtyp Q T' => lc_qq Q d /\ lc_tt_q T' d end
with lc_tt_q (T:typ) (d:nat) : Prop :=
  match T with
  | typ_top => True | typ_int => True | typ_bvar _ => True | typ_fvar _ => True
  | typ_arrow T1 T2 => lc_qqt T1 d /\ lc_qqt T2 (S d)
  | typ_all T1 T2 => lc_tt_q T1 d /\ lc_qqt T2 (S d)
  | typ_qall Q T => lc_qq Q d /\ lc_qqt T (S d)
  | typ_sum T1 T2 => lc_qqt T1 d /\ lc_qqt T2 d
  | typ_pair T1 T2 => lc_qqt T1 d /\ lc_qqt T2 d
  | typ_ref T1 => lc_qqt T1 d
  end.

Fixpoint open_tt_lc (T:typ) {struct T} :
  forall d, lc_tt T d -> forall K U, d <= K -> open_tt_rec K U T = T
with open_tqt_lc (T:qtyp) {struct T} :
  forall d, lc_tqt T d -> forall K U, d <= K -> open_tqt_rec K U T = T.
Proof.
  - destruct T; intros d Hlc K U HK; simpl in *; try reflexivity.
    + simpl. destruct (eq_dec K n) as [Heq|Hneq]; [|reflexivity].
      exfalso; lia.
    + f_equal;
      [apply (open_tqt_lc _ d); [exact (proj1 Hlc) | exact HK]
      |apply (open_tqt_lc _ (S d)); [exact (proj2 Hlc) | apply le_n_S; exact HK]].
    + f_equal;
      [apply (open_tt_lc _ d); [exact (proj1 Hlc) | exact HK]
      |apply (open_tqt_lc _ (S d)); [exact (proj2 Hlc) | apply le_n_S; exact HK]].
    + simpl. f_equal. apply (open_tqt_lc _ (S d)); [exact Hlc | apply le_n_S; exact HK].
    + f_equal;
      [apply (open_tqt_lc _ d); [exact (proj1 Hlc) | exact HK]
      |apply (open_tqt_lc _ d); [exact (proj2 Hlc) | exact HK]].
    + f_equal;
      [apply (open_tqt_lc _ d); [exact (proj1 Hlc) | exact HK]
      |apply (open_tqt_lc _ d); [exact (proj2 Hlc) | exact HK]].
    + simpl. f_equal. apply (open_tqt_lc _ d); [exact Hlc | exact HK].
  - destruct T as [Q T]. intros d Hlc K U HK. simpl in *. f_equal.
    apply (open_tt_lc _ d); [exact Hlc | exact HK].
Qed.

Fixpoint open_qq_lc (Q:qua) {struct Q} :
  forall d, lc_qq Q d -> forall K R, d <= K -> open_qq_rec K R Q = Q.
Proof.
  destruct Q; intros d Hlc K R HK; simpl in *; try reflexivity.
  - simpl. destruct (eq_dec K n) as [Heq|Hneq]; [|reflexivity]. exfalso; lia.
  - destruct Hlc as [H1 H2]. f_equal; [apply (open_qq_lc _ d); [exact H1|exact HK]
            |apply (open_qq_lc _ d); [exact H2|exact HK]].
  - destruct Hlc as [H1 H2]. f_equal; [apply (open_qq_lc _ d); [exact H1|exact HK]
            |apply (open_qq_lc _ d); [exact H2|exact HK]].
  - simpl. f_equal. apply (open_qq_lc _ d); [exact Hlc|exact HK].
Qed.

Fixpoint open_qt_lc (T:typ) {struct T} :
  forall d, lc_tt_q T d -> forall K R, d <= K -> open_qt_rec K R T = T
with open_qqt_lc (T:qtyp) {struct T} :
  forall d, lc_qqt T d -> forall K R, d <= K -> open_qqt_rec K R T = T.
Proof.
  - destruct T; intros d Hlc K R HK; simpl in *; try reflexivity.
    + f_equal;
      [apply (open_qqt_lc _ d); [exact (proj1 Hlc)|exact HK]
      |apply (open_qqt_lc _ (S d)); [exact (proj2 Hlc)|apply le_n_S; exact HK]].
    + f_equal;
      [apply (open_qt_lc _ d); [exact (proj1 Hlc)|exact HK]
      |apply (open_qqt_lc _ (S d)); [exact (proj2 Hlc)|apply le_n_S; exact HK]].
    + f_equal;
      [apply (open_qq_lc _ d); [exact (proj1 Hlc)|exact HK]
      |apply (open_qqt_lc _ (S d)); [exact (proj2 Hlc)|apply le_n_S; exact HK]].
    + f_equal;
      [apply (open_qqt_lc _ d); [exact (proj1 Hlc)|exact HK]
      |apply (open_qqt_lc _ d); [exact (proj2 Hlc)|exact HK]].
    + f_equal;
      [apply (open_qqt_lc _ d); [exact (proj1 Hlc)|exact HK]
      |apply (open_qqt_lc _ d); [exact (proj2 Hlc)|exact HK]].
    + simpl. f_equal. apply (open_qqt_lc _ d); [exact Hlc|exact HK].
  - destruct T as [Q T]. intros d Hlc K R HK. simpl in *. f_equal.
    + apply (open_qq_lc _ d); [exact (proj1 Hlc)|exact HK].
    + apply (open_qt_lc _ d); [exact (proj2 Hlc)|exact HK].
Qed.

(* conversion lemmas: opening at level K, then locally closed at depth d,
   implies locally closed before opening at depth max d (S K) *)
Fixpoint lc_tt_open_tt (T:typ) {struct T} :
  forall K X d, lc_tt (open_tt_rec K (typ_fvar X) T) d -> lc_tt T (Nat.max d (S K))
with lc_tqt_open_tqt (T:qtyp) {struct T} :
  forall K X d, lc_tqt (open_tqt_rec K (typ_fvar X) T) d -> lc_tqt T (Nat.max d (S K)).
Proof.
  - destruct T; intros K X d H; simpl in *.
    + exact I.
    + exact I.
    + destruct (eq_dec K n) as [Heq|Hneq]; simpl in *.
      * assert (Hn : n < S K) by (rewrite Heq; apply Nat.lt_succ_diag_r).
        assert (Hm : S K <= Nat.max d (S K)) by apply Nat.le_max_r. lia.
      * apply Nat.lt_le_trans with d; [exact H | apply Nat.le_max_l].
    + exact I.
    + split.
      * apply (lc_tqt_open_tqt _ K X d). exact (proj1 H).
      * rewrite Nat.succ_max_distr. apply (lc_tqt_open_tqt _ (S K) X (S d)). exact (proj2 H).
    + split.
      * apply (lc_tt_open_tt _ K X d). exact (proj1 H).
      * rewrite Nat.succ_max_distr. apply (lc_tqt_open_tqt _ (S K) X (S d)). exact (proj2 H).
    + rewrite Nat.succ_max_distr. apply (lc_tqt_open_tqt _ (S K) X (S d)). exact H.
    + split.
      * apply (lc_tqt_open_tqt _ K X d). exact (proj1 H).
      * apply (lc_tqt_open_tqt _ K X d). exact (proj2 H).
    + split.
      * apply (lc_tqt_open_tqt _ K X d). exact (proj1 H).
      * apply (lc_tqt_open_tqt _ K X d). exact (proj2 H).
    + apply (lc_tqt_open_tqt _ K X d). exact H.
  - destruct T as [Q T]. intros K X d H. simpl in *.
    apply (lc_tt_open_tt _ K X d). exact H.
Qed.

Fixpoint lc_qq_open_qq (Q:qua) {struct Q} :
  forall K X d, lc_qq (open_qq_rec K (qua_fvar X) Q) d -> lc_qq Q (Nat.max d (S K)).
Proof.
  destruct Q; intros K X d H; simpl in *.
  - exact I.
  - destruct (eq_dec K n) as [Heq|Hneq]; simpl in *.
    + assert (Hn : n < S K) by (rewrite Heq; apply Nat.lt_succ_diag_r).
      assert (Hm : S K <= Nat.max d (S K)) by apply Nat.le_max_r. lia.
    + apply Nat.lt_le_trans with d; [exact H | apply Nat.le_max_l].
  - exact I.
  - split; [apply (lc_qq_open_qq _ K X d)|apply (lc_qq_open_qq _ K X d)]; [exact (proj1 H)|exact (proj2 H)].
  - split; [apply (lc_qq_open_qq _ K X d)|apply (lc_qq_open_qq _ K X d)]; [exact (proj1 H)|exact (proj2 H)].
  - apply (lc_qq_open_qq _ K X d). exact H.
Qed.

Fixpoint lc_qt_open_qt (T:typ) {struct T} :
  forall K X d, lc_tt_q (open_qt_rec K (qua_fvar X) T) d -> lc_tt_q T (Nat.max d (S K))
with lc_qqt_open_qqt (T:qtyp) {struct T} :
  forall K X d, lc_qqt (open_qqt_rec K (qua_fvar X) T) d -> lc_qqt T (Nat.max d (S K)).
Proof.
  - destruct T; intros K X d H; simpl in *.
    + exact I. + exact I. + exact I. + exact I.
    + split.
      * apply (lc_qqt_open_qqt _ K X d). exact (proj1 H).
      * rewrite Nat.succ_max_distr. apply (lc_qqt_open_qqt _ (S K) X (S d)). exact (proj2 H).
    + split.
      * apply (lc_qt_open_qt _ K X d). exact (proj1 H).
      * rewrite Nat.succ_max_distr. apply (lc_qqt_open_qqt _ (S K) X (S d)). exact (proj2 H).
    + split.
      * apply (lc_qq_open_qq _ K X d). exact (proj1 H).
      * rewrite Nat.succ_max_distr. apply (lc_qqt_open_qqt _ (S K) X (S d)). exact (proj2 H).
    + split.
      * apply (lc_qqt_open_qqt _ K X d). exact (proj1 H).
      * apply (lc_qqt_open_qqt _ K X d). exact (proj2 H).
    + split.
      * apply (lc_qqt_open_qqt _ K X d). exact (proj1 H).
      * apply (lc_qqt_open_qqt _ K X d). exact (proj2 H).
    + apply (lc_qqt_open_qqt _ K X d). exact H.
  - destruct T as [Q T]. intros K X d H. simpl in *. split.
    + apply (lc_qq_open_qq _ K X d). exact (proj1 H).
    + apply (lc_qt_open_qt _ K X d). exact (proj2 H).
Qed.

(* monotonicity of locally-closed bounds *)
Fixpoint lc_tt_mono (T:typ) {struct T} :
  forall d, lc_tt T d -> lc_tt T (S d)
with lc_tqt_mono (T:qtyp) {struct T} :
  forall d, lc_tqt T d -> lc_tqt T (S d).
Proof.
  - destruct T; intros d H; simpl in *; try exact I.
    + lia.
    + split; [apply (lc_tqt_mono _ d)|apply (lc_tqt_mono _ (S d))]; [exact (proj1 H)|exact (proj2 H)].
    + split; [apply (lc_tt_mono _ d)|apply (lc_tqt_mono _ (S d))]; [exact (proj1 H)|exact (proj2 H)].
    + apply (lc_tqt_mono _ (S d)). exact H.
    + split; [apply (lc_tqt_mono _ d)|apply (lc_tqt_mono _ d)]; [exact (proj1 H)|exact (proj2 H)].
    + split; [apply (lc_tqt_mono _ d)|apply (lc_tqt_mono _ d)]; [exact (proj1 H)|exact (proj2 H)].
    + apply (lc_tqt_mono _ d). exact H.
  - destruct T as [Q T]. intros d H. simpl in *. apply (lc_tt_mono _ d). exact H.
Qed.

Fixpoint lc_qq_mono (Q:qua) {struct Q} :
  forall d, lc_qq Q d -> lc_qq Q (S d).
Proof.
  destruct Q; intros d H; simpl in *; try exact I.
  - lia.
  - split; [apply (lc_qq_mono _ d)|apply (lc_qq_mono _ d)]; [exact (proj1 H)|exact (proj2 H)].
  - split; [apply (lc_qq_mono _ d)|apply (lc_qq_mono _ d)]; [exact (proj1 H)|exact (proj2 H)].
  - apply (lc_qq_mono _ d). exact H.
Qed.

Fixpoint lc_qt_mono (T:typ) {struct T} :
  forall d, lc_tt_q T d -> lc_tt_q T (S d)
with lc_qqt_mono (T:qtyp) {struct T} :
  forall d, lc_qqt T d -> lc_qqt T (S d).
Proof.
  - destruct T; intros d H; simpl in *; try exact I.
    + split; [apply (lc_qqt_mono _ d)|apply (lc_qqt_mono _ (S d))]; [exact (proj1 H)|exact (proj2 H)].
    + split; [apply (lc_qt_mono _ d)|apply (lc_qqt_mono _ (S d))]; [exact (proj1 H)|exact (proj2 H)].
    + split; [apply (lc_qq_mono _ d)|apply (lc_qqt_mono _ (S d))]; [exact (proj1 H)|exact (proj2 H)].
    + split; [apply (lc_qqt_mono _ d)|apply (lc_qqt_mono _ d)]; [exact (proj1 H)|exact (proj2 H)].
    + split; [apply (lc_qqt_mono _ d)|apply (lc_qqt_mono _ d)]; [exact (proj1 H)|exact (proj2 H)].
    + apply (lc_qqt_mono _ d). exact H.
  - destruct T as [Q T]. intros d H. simpl in *. split.
    + apply (lc_qq_mono _ d). exact (proj1 H).
    + apply (lc_qt_mono _ d). exact (proj2 H).
Qed.

(* qualifier-opening does not increase type-variable local closure (forward) *)
Fixpoint lc_tt_open_qual_fwd (T:typ) {struct T} :
  forall K R d, lc_tt (open_qt_rec K R T) d -> lc_tt T d
with lc_tqt_open_qual_fwd (T:qtyp) {struct T} :
  forall K R d, lc_tqt (open_qqt_rec K R T) d -> lc_tqt T d.
Proof.
  - destruct T; intros K R d H; simpl in *; try exact H.
    + destruct H as [H1 H2]. split.
      * apply (lc_tqt_open_qual_fwd _ K R d). exact H1.
      * apply (lc_tqt_open_qual_fwd _ (S K) R (S d)). exact H2.
    + destruct H as [H1 H2]. split.
      * apply (lc_tt_open_qual_fwd _ K R d). exact H1.
      * apply (lc_tqt_open_qual_fwd _ (S K) R (S d)). exact H2.
    + apply (lc_tqt_open_qual_fwd _ (S K) R (S d)). exact H.
    + destruct H as [H1 H2]. split.
      * apply (lc_tqt_open_qual_fwd _ K R d). exact H1.
      * apply (lc_tqt_open_qual_fwd _ K R d). exact H2.
    + destruct H as [H1 H2]. split.
      * apply (lc_tqt_open_qual_fwd _ K R d). exact H1.
      * apply (lc_tqt_open_qual_fwd _ K R d). exact H2.
    + apply (lc_tqt_open_qual_fwd _ K R d). exact H.
  - destruct T as [Q T]. intros K R d H. simpl in *.
    apply (lc_tt_open_qual_fwd _ K R d). exact H.
Qed.

Lemma qual_lc : forall Q, qual Q -> lc_qq Q 0.
Proof.
  intros Q H. induction H; simpl.
  - exact I.
  - exact I.
  - split; assumption.
  - split; assumption.
  - assumption.
Qed.

Scheme type_mut := Induction for type Sort Prop
with qtype_mut := Induction for qtype Sort Prop.
Combined Scheme type_q_mut from type_mut, qtype_mut.

Lemma type_qtype_lc :
  (forall (T:typ), type T -> lc_tt T 0) /\
  (forall (T:qtyp), qtype T -> lc_tqt T 0).
Proof.
  apply type_q_mut
    with (P := fun T _ => lc_tt T 0)
         (P0 := fun T _ => lc_tqt T 0).
  - exact I.
  - exact I.
  - intros X. exact I.
  - intros T1 T2 H1 IH1 H2 IH2.
    change (lc_tqt T1 0 /\ lc_tqt T2 1). split.
    + exact IH1.
    + apply lc_tqt_mono. exact IH2.
  - intros L T1 T2 HT1 IHT1 Hbody IHbody.
    change (lc_tt T1 0 /\ lc_tqt T2 1). split.
    + exact IHT1.
    + pick fresh X for L.
      pose proof (IHbody X Fr) as Hx.
      pose proof (lc_tqt_open_tqt T2 0 X 0 Hx) as Hc.
      change (lc_tqt T2 1) in Hc. exact Hc.
  - intros L Q T Hq Hbody IHbody.
    change (lc_tqt T 1).
    pick fresh X for L.
    pose proof (IHbody X Fr) as Hx.
    pose proof (lc_tqt_open_qual_fwd T 0 (qua_fvar X) 0 Hx) as Hc.
    apply lc_tqt_mono. exact Hc.
  - intros T1 T2 H1 IH1 H2 IH2.
    change (lc_tqt T1 0 /\ lc_tqt T2 0). split; assumption.
  - intros T1 T2 H1 IH1 H2 IH2.
    change (lc_tqt T1 0 /\ lc_tqt T2 0). split; assumption.
  - intros Q T Hq HT IHT. change (lc_tt T 0). exact IHT.
Qed.

Lemma type_closed_tt : forall (V:typ), type V -> closed_tt V.
Proof.
  intros V H K U.
  apply (open_tt_lc V 0 (proj1 type_qtype_lc V H) K U (Nat.le_0_l K)).
Qed.

Lemma qual_closed_qq : forall (R:qua), qual R -> closed_qq R.
Proof.
  intros R H K R0.
  apply (open_qq_lc R 0 (qual_lc R H) K R0 (Nat.le_0_l K)).
Qed.

(* ========================================================= *)
(* Membership removal                                          *)
(* ========================================================= *)

Lemma binds_remove_typ_mid : forall (E1:env) x (T:qtyp) (E2:env) z b,
  b <> bind_typ T ->
  binds z b (E1 ++ x ~ bind_typ T ++ E2) -> binds z b (E1 ++ E2).
Proof.
  intros E1 x T E2 z b Hneq Hb.
  destruct b as [U|U|R].
  - unfold binds in *. apply in_app_iff.
    apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [left;auto|].
    simpl in Hb. destruct Hb as [Heq|Hb].
    + inversion Heq; subst; discriminate.
    + right; auto.
  - unfold binds in *. apply in_app_iff.
    apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [left;auto|].
    simpl in Hb. destruct Hb as [Heq|Hb].
    + inversion Heq; subst. exfalso. apply Hneq. reflexivity.
    + right; auto.
  - unfold binds in *. apply in_app_iff.
    apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [left;auto|].
    simpl in Hb. destruct Hb as [Heq|Hb].
    + inversion Heq; subst; discriminate.
    + right; auto.
Qed.

Lemma binds_qua_remove_typ_mid' : forall (E1:env) x (T:qtyp) (E2:env) z R,
  binds z (bind_qua R) (E1 ++ x ~ bind_typ T ++ E2) -> binds z (bind_qua R) (E1 ++ E2).
Proof. intros. eapply binds_remove_typ_mid; eauto. intro Hc; inversion Hc. Qed.

Lemma binds_sub_remove_typ_mid' : forall (E1:env) x (T:qtyp) (E2:env) z U,
  binds z (bind_sub U) (E1 ++ x ~ bind_typ T ++ E2) -> binds z (bind_sub U) (E1 ++ E2).
Proof. intros. eapply binds_remove_typ_mid; eauto. intro Hc; inversion Hc. Qed.

Lemma binds_qua_remove_sub_mid : forall (E1:env) X (U:typ) (E2:env) z R,
  binds z (bind_qua R) (E1 ++ X ~ bind_sub U ++ E2) -> binds z (bind_qua R) (E1 ++ E2).
Proof.
  intros E1 X U E2 z R H. unfold binds in *.
  apply in_app_iff.
  apply in_app_iff in H. destruct H as [H|H]; [left;auto|].
  simpl in H. destruct H as [Heq|H].
  - inversion Heq; subst; discriminate.
  - right; auto.
Qed.

Lemma binds_remove_sub_same : forall (E1:env) X (U U0:typ) (E2:env) z,
  binds z (bind_sub U) (E1 ++ X ~ bind_sub U0 ++ E2) ->
  (z = X /\ U = U0) \/ binds z (bind_sub U) (E1 ++ E2).
Proof.
  intros E1 X U U0 E2 z H. unfold binds in *.
  apply in_app_iff in H. destruct H as [H|H].
  - right. unfold binds. apply in_app_iff. left; auto.
  - simpl in H. destruct H as [Heq|H].
    + left. inversion Heq; subst. split; reflexivity.
    + right. unfold binds. apply in_app_iff. right; auto.
Qed.

Lemma binds_remove_qua_same : forall (E1:env) X (Q Q0:qua) (E2:env) z,
  binds z (bind_qua Q) (E1 ++ X ~ bind_qua Q0 ++ E2) ->
  (z = X /\ Q = Q0) \/ binds z (bind_qua Q) (E1 ++ E2).
Proof.
  intros E1 X Q Q0 E2 z H. unfold binds in *.
  apply in_app_iff in H. destruct H as [H|H].
  - right. unfold binds. apply in_app_iff. left; auto.
  - simpl in H. destruct H as [Heq|H].
    + left. inversion Heq; subst. split; reflexivity.
    + right. unfold binds. apply in_app_iff. right; auto.
Qed.

(* ========================================================= *)
(* wf_qua removal                                              *)
(* ========================================================= *)

Fixpoint wf_qua_remove_sub_mid (Q:qua) {struct Q} :
  forall (E1:env) X (U:typ) (E2:env),
  wf_qua (E1 ++ X ~ bind_sub U ++ E2) Q -> wf_qua (E1 ++ E2) Q.
Proof.
  destruct Q as [b|n|X0|Q1 Q2|Q1 Q2|Q1]; intros E1 X U E2 H.
  - apply wf_qua_base.
  - inversion H.
  - inversion H; subst. eapply wf_qua_fvar. eapply binds_qua_remove_sub_mid; eauto.
  - inversion H; subst. apply wf_qua_meet.
    + apply (wf_qua_remove_sub_mid Q1 E1 X U E2); eassumption.
    + apply (wf_qua_remove_sub_mid Q2 E1 X U E2); eassumption.
  - inversion H; subst. apply wf_qua_join.
    + apply (wf_qua_remove_sub_mid Q1 E1 X U E2); eassumption.
    + apply (wf_qua_remove_sub_mid Q2 E1 X U E2); eassumption.
  - inversion H; subst. apply wf_qua_negate.
    apply (wf_qua_remove_sub_mid Q1 E1 X U E2); eassumption.
Qed.

Lemma wf_qua_remove_qua_mid_aux : forall (E1:env) X (Q0:qua) (E2:env) z R,
  binds z (bind_qua R) (E1 ++ X ~ bind_qua Q0 ++ E2) ->
  X `notin` fv_qq (qua_fvar z) -> binds z (bind_qua R) (E1 ++ E2).
Proof.
  intros E1 X Q0 E2 z R Hb Hf.
  destruct (binds_remove_qua_same E1 X R Q0 E2 z Hb) as [[Hz HR]|Hout].
  - subst. exfalso. simpl in Hf. exact (notin_singleton_1 X X Hf eq_refl).
  - exact Hout.
Qed.

Fixpoint wf_qua_remove_qua_mid (Q:qua) {struct Q} :
  forall (E1:env) X (Q0:qua) (E2:env),
  X `notin` fv_qq Q -> wf_qua (E1 ++ X ~ bind_qua Q0 ++ E2) Q -> wf_qua (E1 ++ E2) Q.
Proof.
  destruct Q as [b|n|z|Q1 Q2|Q1 Q2|Q1]; intros E1 X Q0 E2 Hf H.
  - apply wf_qua_base.
  - inversion H.
  - inversion H; subst. eapply wf_qua_fvar.
    eapply wf_qua_remove_qua_mid_aux; eauto.
  - simpl in Hf.
    assert (Hf1 : X `notin` fv_qq Q1) by (exact (notin_union_1 X (fv_qq Q1) (fv_qq Q2) Hf)).
    assert (Hf2 : X `notin` fv_qq Q2) by (exact (notin_union_2 X (fv_qq Q1) (fv_qq Q2) Hf)).
    inversion H; subst. apply wf_qua_meet.
    + apply (wf_qua_remove_qua_mid Q1 E1 X Q0 E2); eassumption.
    + apply (wf_qua_remove_qua_mid Q2 E1 X Q0 E2); eassumption.
  - simpl in Hf.
    assert (Hf1 : X `notin` fv_qq Q1) by (exact (notin_union_1 X (fv_qq Q1) (fv_qq Q2) Hf)).
    assert (Hf2 : X `notin` fv_qq Q2) by (exact (notin_union_2 X (fv_qq Q1) (fv_qq Q2) Hf)).
    inversion H; subst. apply wf_qua_join.
    + apply (wf_qua_remove_qua_mid Q1 E1 X Q0 E2); eassumption.
    + apply (wf_qua_remove_qua_mid Q2 E1 X Q0 E2); eassumption.
  - simpl in Hf. inversion H; subst. apply wf_qua_negate.
    apply (wf_qua_remove_qua_mid Q1 E1 X Q0 E2); eassumption.
Qed.

(* ========================================================= *)
(* Removing a middle bind_typ from subqual/sub/subqtype        *)
(* ========================================================= *)

Ltac solve_subqual_remove :=
  first [ eapply subqual_top; eauto using wf_env_remove_typ_mid, wf_qua_remove_typ_mid
        | eapply subqual_bot; eauto using wf_env_remove_typ_mid, wf_qua_remove_typ_mid
        | eapply subqual_eval_elim; eauto
        | eapply subqual_eval_intro; eauto
        | eapply subqual_lift_elem; eauto using wf_env_remove_typ_mid
        | eapply subqual_refl_qvar; eauto using wf_env_remove_typ_mid, wf_qua_remove_typ_mid
        | eapply subqual_trans_qvar; eauto using binds_qua_remove_typ_mid'
        | eapply subqual_join_inl; eauto using wf_qua_remove_typ_mid
        | eapply subqual_join_inr; eauto using wf_qua_remove_typ_mid
        | eapply subqual_join_elim; eauto
        | eapply subqual_meet_eliml; eauto using wf_qua_remove_typ_mid
        | eapply subqual_meet_elimr; eauto using wf_qua_remove_typ_mid
        | eapply subqual_meet_intro; eauto
        | eapply subqual_dist; eauto using wf_env_remove_typ_mid, wf_qua_remove_typ_mid
        | eapply subqual_trans; eauto
        | eapply subqual_negate_intro; eauto using wf_env_remove_typ_mid, wf_qua_remove_typ_mid
        | eapply subqual_negate_elim; eauto using wf_env_remove_typ_mid, wf_qua_remove_typ_mid
        | eapply subqual_refl_negate; eauto using wf_env_remove_typ_mid, wf_qua_remove_typ_mid ].

Lemma subqual_remove_typ_mid_gen : forall (E:env) Q R,
  subqual E Q R ->
  forall (E1:env) x (T:qtyp) (E2:env),
  E = E1 ++ x ~ bind_typ T ++ E2 -> subqual (E1 ++ E2) Q R.
Proof.
  intros E Q R H.
  induction H as [Ew Qw Hwf HQ | Ew Qw Hwf HQ
    | Ew Qa Qb Qc bb h1 IH1 hc h2 IH2 | Ew Qa Qb Qc bb h1 IH1 hc h2 IH2
    | Ew b1 b2 Hwf Ho | Ew Xw Hwf HQ
    | R0 Ew Qw Xw hb h1 IH1
    | Ew R1 R2 Qw h1 IH1 HR2 | Ew R1 R2 Qw HR1 h2 IH1
    | Ew R1 R2 Qw h1 IH1 h2 IH2
    | Ew R1 R2 Qw h1 IH1 HR2 | Ew R1 R2 Qw HR1 h2 IH1
    | Ew R1 R2 Qw h1 IH1 h2 IH2
    | Ew Qw Rw Sw Hwf HQ HR HS
    | Ew Qw Rw Sw h1 IH1 h2 IH2
    | Ew Qw Hwf HQ | Ew Qw Hwf HQ | Ew Qw Hwf HQ].
  - intros E1 x T E2 Heq. subst Ew. eapply subqual_top.
    + exact (wf_env_remove_typ_mid E1 x T E2 Hwf).
    + exact (wf_qua_remove_typ_mid Qw E1 x T E2 HQ).
  - intros E1 x T E2 Heq. subst Ew. eapply subqual_bot.
    + exact (wf_env_remove_typ_mid E1 x T E2 Hwf).
    + exact (wf_qua_remove_typ_mid Qw E1 x T E2 HQ).
  - intros E1 x T E2 Heq. subst Ew. eapply subqual_eval_elim.
    + apply (IH1 E1 x T E2). reflexivity.
    + exact hc.
    + apply (IH2 E1 x T E2). reflexivity.
  - intros E1 x T E2 Heq. subst Ew. eapply subqual_eval_intro.
    + apply (IH1 E1 x T E2). reflexivity.
    + exact hc.
    + apply (IH2 E1 x T E2). reflexivity.
  - intros E1 x T E2 Heq. subst Ew. eapply subqual_lift_elem.
    + exact (wf_env_remove_typ_mid E1 x T E2 Hwf).
    + exact Ho.
  - intros E1 x T E2 Heq. subst Ew. eapply subqual_refl_qvar.
    + exact (wf_env_remove_typ_mid E1 x T E2 Hwf).
    + exact (wf_qua_remove_typ_mid (qua_fvar Xw) E1 x T E2 HQ).
  - intros E1 x T E2 Heq. subst Ew. eapply subqual_trans_qvar.
    + exact (binds_qua_remove_typ_mid' E1 x T E2 Xw R0 hb).
    + apply (IH1 E1 x T E2). reflexivity.
  - intros E1 x T E2 Heq. subst Ew. eapply subqual_join_inl.
    + apply (IH1 E1 x T E2). reflexivity.
    + exact (wf_qua_remove_typ_mid R2 E1 x T E2 HR2).
  - intros E1 x T E2 Heq. subst Ew. eapply subqual_join_inr.
    + exact (wf_qua_remove_typ_mid R1 E1 x T E2 HR1).
    + apply (IH1 E1 x T E2). reflexivity.
  - intros E1 x T E2 Heq. subst Ew. eapply subqual_join_elim.
    + apply (IH1 E1 x T E2). reflexivity.
    + apply (IH2 E1 x T E2). reflexivity.
  - intros E1 x T E2 Heq. subst Ew. eapply subqual_meet_eliml.
    + apply (IH1 E1 x T E2). reflexivity.
    + exact (wf_qua_remove_typ_mid R2 E1 x T E2 HR2).
  - intros E1 x T E2 Heq. subst Ew. eapply subqual_meet_elimr.
    + exact (wf_qua_remove_typ_mid R1 E1 x T E2 HR1).
    + apply (IH1 E1 x T E2). reflexivity.
  - intros E1 x T E2 Heq. subst Ew. eapply subqual_meet_intro.
    + apply (IH1 E1 x T E2). reflexivity.
    + apply (IH2 E1 x T E2). reflexivity.
  - intros E1 x T E2 Heq. subst Ew. eapply subqual_dist.
    + exact (wf_env_remove_typ_mid E1 x T E2 Hwf).
    + exact (wf_qua_remove_typ_mid Qw E1 x T E2 HQ).
    + exact (wf_qua_remove_typ_mid Rw E1 x T E2 HR).
    + exact (wf_qua_remove_typ_mid Sw E1 x T E2 HS).
  - intros E1 x T E2 Heq. subst Ew. eapply subqual_trans.
    + apply (IH1 E1 x T E2). reflexivity.
    + apply (IH2 E1 x T E2). reflexivity.
  - intros E1 x T E2 Heq. subst Ew. eapply subqual_negate_intro.
    + exact (wf_env_remove_typ_mid E1 x T E2 Hwf).
    + exact (wf_qua_remove_typ_mid Qw E1 x T E2 HQ).
  - intros E1 x T E2 Heq. subst Ew. eapply subqual_negate_elim.
    + exact (wf_env_remove_typ_mid E1 x T E2 Hwf).
    + exact (wf_qua_remove_typ_mid Qw E1 x T E2 HQ).
  - intros E1 x T E2 Heq. subst Ew. eapply subqual_refl_negate.
    + exact (wf_env_remove_typ_mid E1 x T E2 Hwf).
    + exact (wf_qua_remove_typ_mid Qw E1 x T E2 HQ).
Qed.

Lemma subqual_remove_typ_mid : forall (E1:env) x (T:qtyp) (E2:env) Q R,
  subqual (E1 ++ x ~ bind_typ T ++ E2) Q R -> subqual (E1 ++ E2) Q R.
Proof.
  intros E1 x T E2 Q R H.
  exact (subqual_remove_typ_mid_gen (E1 ++ x ~ bind_typ T ++ E2) Q R H E1 x T E2 eq_refl).
Qed.

(* ========================================================= *)
(* Removing a middle bind_typ from sub/subqtype                *)
(* ========================================================= *)

Lemma sub_subqtype_remove_typ_mid :
  (forall (E:env) (S T:typ), sub E S T ->
     forall (E1:env) x (TT:qtyp) (E2:env),
       E = E1 ++ x ~ bind_typ TT ++ E2 -> sub (E1 ++ E2) S T) /\
  (forall (E:env) (S T:qtyp), subqtype E S T ->
     forall (E1:env) x (TT:qtyp) (E2:env),
       E = E1 ++ x ~ bind_typ TT ++ E2 -> subqtype (E1 ++ E2) S T).
Proof.
  apply sub_tq_mut
    with (P := fun E S T _ => forall (E1:env) x (TT:qtyp) (E2:env),
                E = E1 ++ x ~ bind_typ TT ++ E2 -> sub (E1 ++ E2) S T)
         (P0 := fun E S T _ => forall (E1:env) x (TT:qtyp) (E2:env),
                E = E1 ++ x ~ bind_typ TT ++ E2 -> subqtype (E1 ++ E2) S T).
  - intros E S w w0 E1 x TT E2 Heq. subst E.
    eapply sub_top.
    + exact (wf_env_remove_typ_mid E1 x TT E2 w).
    + exact (wf_typ_remove_typ_mid E1 x TT E2 S w0).
  - intros E w E1 x TT E2 Heq. subst E. apply sub_refl_int.
    exact (wf_env_remove_typ_mid E1 x TT E2 w).
  - intros E X w w0 E1 x TT E2 Heq. subst E. eapply sub_refl_tvar.
    + exact (wf_env_remove_typ_mid E1 x TT E2 w).
    + exact (wf_typ_remove_typ_mid E1 x TT E2 (typ_fvar X) w0).
  - intros U E T X b s IH E1 x TT E2 Heq. subst E. eapply sub_trans_tvar.
    + exact (binds_sub_remove_typ_mid' E1 x TT E2 X U b).
    + apply (IH E1 x TT E2). reflexivity.
  - intros E S1 S2 T1 T2 s IH1 s0 IH2 E1 x TT E2 Heq. subst E.
    eapply sub_arrow.
    + apply (IH1 E1 x TT E2). reflexivity.
    + apply (IH2 E1 x TT E2). reflexivity.
  - intros L E S1 S2 T1 T2 s IH1 s0 IH0 E1 x TT E2 Heq. subst E.
    eapply sub_all with (L:=L).
    + apply (IH1 E1 x TT E2). reflexivity.
    + intros X HX. apply (IH0 X HX (X ~ bind_sub T1 ++ E1) x TT E2).
      rewrite app_assoc. reflexivity.
  - intros L E S1 S2 T1 T2 s s0 IH0 E1 x TT E2 Heq. subst E.
    eapply sub_qall with (L:=L).
    + exact (subqual_remove_typ_mid E1 x TT E2 T1 S1 s).
    + intros X HX. apply (IH0 X HX (X ~ bind_qua T1 ++ E1) x TT E2).
      rewrite app_assoc. reflexivity.
  - intros E S1 S2 T1 T2 s IH1 s0 IH2 E1 x TT E2 Heq. subst E.
    eapply sub_sum.
    + apply (IH1 E1 x TT E2). reflexivity.
    + apply (IH2 E1 x TT E2). reflexivity.
  - intros E S1 S2 T1 T2 s IH1 s0 IH2 E1 x TT E2 Heq. subst E.
    eapply sub_pair.
    + apply (IH1 E1 x TT E2). reflexivity.
    + apply (IH2 E1 x TT E2). reflexivity.
  - intros E Q1 T1 Q2 T2 s s0 IH E1 x TT E2 Heq. subst E.
    eapply sub_qtyp_qtyp.
    + exact (subqual_remove_typ_mid E1 x TT E2 Q1 Q2 s).
    + apply (IH E1 x TT E2). reflexivity.
Qed.

Lemma sub_remove_typ_mid : forall (E1:env) x (TT:qtyp) (E2:env) S T,
  sub (E1 ++ x ~ bind_typ TT ++ E2) S T -> sub (E1 ++ E2) S T.
Proof.
  intros. eapply (proj1 sub_subqtype_remove_typ_mid); [exact H | reflexivity].
Qed.

Lemma subqtype_remove_typ_mid : forall (E1:env) x (TT:qtyp) (E2:env) S T,
  subqtype (E1 ++ x ~ bind_typ TT ++ E2) S T -> subqtype (E1 ++ E2) S T.
Proof.
  intros. eapply (proj2 sub_subqtype_remove_typ_mid); [exact H | reflexivity].
Qed.

(* ========================================================= *)
(* fv lemmas for opening (needed for wf removal under binders) *)
(* ========================================================= *)

Fixpoint fv_tt_open_tt (T:typ) {struct T} :
  forall K Y X, X `notin` fv_tt T -> X <> Y ->
    X `notin` fv_tt (open_tt_rec K (typ_fvar Y) T)
with fv_tqt_open_tqt (T:qtyp) {struct T} :
  forall K Y X, X `notin` fv_tqt T -> X <> Y ->
    X `notin` fv_tqt (open_tqt_rec K (typ_fvar Y) T).
Proof.
  - destruct T; intros K Y X Hf Hne; simpl in *.
    + exact (notin_empty_1 X).
    + exact (notin_empty_1 X).
    + destruct (eq_dec K n) as [Heq|Hneq]; simpl.
      * apply notin_singleton_2. intro HYX. apply Hne. symmetry. exact HYX.
      * exact (notin_empty_1 X).
    + exact Hf.
    + apply notin_union_3.
      * apply (fv_tqt_open_tqt _ K Y X). exact (notin_union_1 _ _ _ Hf). exact Hne.
      * apply (fv_tqt_open_tqt _ (S K) Y X). exact (notin_union_2 _ _ _ Hf). exact Hne.
    + apply notin_union_3.
      * apply (fv_tt_open_tt _ K Y X). exact (notin_union_1 _ _ _ Hf). exact Hne.
      * apply (fv_tqt_open_tqt _ (S K) Y X). exact (notin_union_2 _ _ _ Hf). exact Hne.
    + apply (fv_tqt_open_tqt _ (S K) Y X). exact Hf. exact Hne.
    + apply notin_union_3.
      * apply (fv_tqt_open_tqt _ K Y X). exact (notin_union_1 _ _ _ Hf). exact Hne.
      * apply (fv_tqt_open_tqt _ K Y X). exact (notin_union_2 _ _ _ Hf). exact Hne.
    + apply notin_union_3.
      * apply (fv_tqt_open_tqt _ K Y X). exact (notin_union_1 _ _ _ Hf). exact Hne.
      * apply (fv_tqt_open_tqt _ K Y X). exact (notin_union_2 _ _ _ Hf). exact Hne.
    + apply (fv_tqt_open_tqt _ K Y X). exact Hf. exact Hne.
  - destruct T as [Q T]. intros K Y X Hf Hne. simpl in *.
    apply (fv_tt_open_tt _ K Y X). exact Hf. exact Hne.
Qed.

(* qualifier opening does not change type-variable fvs *)
Fixpoint fv_tt_open_qt (T:typ) {struct T} :
  forall K R X, X `notin` fv_tt T -> X `notin` fv_tt (open_qt_rec K R T)
with fv_tt_open_qqt (T:qtyp) {struct T} :
  forall K R X, X `notin` fv_tqt T -> X `notin` fv_tqt (open_qqt_rec K R T).
Proof.
  - destruct T; intros K R X Hf; simpl in *; try exact Hf.
    + apply notin_union_3.
      * apply (fv_tt_open_qqt _ K R X). exact (notin_union_1 _ _ _ Hf).
      * apply (fv_tt_open_qqt _ (S K) R X). exact (notin_union_2 _ _ _ Hf).
    + apply notin_union_3.
      * apply (fv_tt_open_qt _ K R X). exact (notin_union_1 _ _ _ Hf).
      * apply (fv_tt_open_qqt _ (S K) R X). exact (notin_union_2 _ _ _ Hf).
    + apply (fv_tt_open_qqt _ (S K) R X). exact Hf.
    + apply notin_union_3.
      * apply (fv_tt_open_qqt _ K R X). exact (notin_union_1 _ _ _ Hf).
      * apply (fv_tt_open_qqt _ K R X). exact (notin_union_2 _ _ _ Hf).
    + apply notin_union_3.
      * apply (fv_tt_open_qqt _ K R X). exact (notin_union_1 _ _ _ Hf).
      * apply (fv_tt_open_qqt _ K R X). exact (notin_union_2 _ _ _ Hf).
    + apply (fv_tt_open_qqt _ K R X). exact Hf.
  - destruct T as [Q T]. intros K R X Hf. simpl in *.
    apply (fv_tt_open_qt _ K R X). exact Hf.
Qed.

(* ========================================================= *)
(* wf removal of a bind_sub, with type-variable freshness      *)
(* ========================================================= *)

Lemma wf_typ_qtyp_remove_sub_mid :
  (forall (E:env) (T:typ), wf_typ E T ->
     forall (E1:env) X (U:typ) (E2:env),
       E = E1 ++ X ~ bind_sub U ++ E2 -> X `notin` fv_tt T ->
       wf_typ (E1 ++ E2) T) /\
  (forall (E:env) (T:qtyp), wf_qtyp E T ->
     forall (E1:env) X (U:typ) (E2:env),
       E = E1 ++ X ~ bind_sub U ++ E2 -> X `notin` fv_tqt T ->
       wf_qtyp (E1 ++ E2) T).
Proof.
  apply wf_tq_mut
    with (P := fun E T _ => forall (E1:env) X (U:typ) (E2:env),
                E = E1 ++ X ~ bind_sub U ++ E2 -> X `notin` fv_tt T ->
                wf_typ (E1 ++ E2) T)
         (P0 := fun E T _ => forall (E1:env) X (U:typ) (E2:env),
                E = E1 ++ X ~ bind_sub U ++ E2 -> X `notin` fv_tqt T ->
                wf_qtyp (E1 ++ E2) T).
  - intros E E1 X U E2 Heq Hf. subst E. constructor.
  - intros E E1 X U E2 Heq Hf. subst E. constructor.
  - intros U0 E X' b E1 X U E2 Heq Hf. subst E.
    destruct (binds_remove_sub_same E1 X U0 U E2 X' b) as [[HX HU]|Hb].
    + subst X'. simpl in Hf. exfalso. exact (notin_singleton_1 X X Hf eq_refl).
    + eapply wf_typ_var. exact Hb.
  - intros E T1 T2 w1 IH1 w2 IH2 E1 X U E2 Heq Hf. subst E.
    simpl in Hf.
    apply wf_typ_arrow.
    + apply (IH1 E1 X U E2). reflexivity. exact (notin_union_1 X (fv_tqt T1) (fv_tqt T2) Hf).
    + apply (IH2 E1 X U E2). reflexivity. exact (notin_union_2 X (fv_tqt T1) (fv_tqt T2) Hf).
  - intros L E T1 T2 w1 IH1 w0 IH0 E1 X U E2 Heq Hf. subst E.
    simpl in Hf.
    assert (Hf1 : X `notin` fv_tt T1) by (exact (notin_union_1 X (fv_tt T1) (fv_tqt T2) Hf)).
    assert (Hf2 : X `notin` fv_tqt T2) by (exact (notin_union_2 X (fv_tt T1) (fv_tqt T2) Hf)).
    eapply wf_typ_all with (L := L \u singleton X).
    + apply (IH1 E1 X U E2). reflexivity. exact Hf1.
    + intros Y HY.
      assert (HYL : Y `notin` L) by (exact (notin_union_1 Y L (singleton X) HY)).
      assert (HYs : Y `notin` singleton X) by (exact (notin_union_2 Y L (singleton X) HY)).
      assert (HXY : X <> Y) by (exact (notin_singleton_1 X Y HYs)).
      apply (IH0 Y HYL (Y ~ bind_sub T1 ++ E1) X U E2).
      * rewrite app_assoc. reflexivity.
      * apply (fv_tqt_open_tqt T2 0 Y X Hf2 HXY).
  - intros L E T1 T2 wq w0 IH0 E1 X U E2 Heq Hf. subst E.
    simpl in Hf.
    eapply wf_typ_qall with (L := L \u singleton X).
    + exact (wf_qua_remove_sub_mid T1 E1 X U E2 wq).
    + intros Y HY.
      assert (HYL : Y `notin` L) by (exact (notin_union_1 Y L (singleton X) HY)).
      apply (IH0 Y HYL (Y ~ bind_qua T1 ++ E1) X U E2).
      * rewrite app_assoc. reflexivity.
      * exact (fv_tt_open_qqt T2 0 (qua_fvar Y) X Hf).
  - intros E T1 T2 w1 IH1 w2 IH2 E1 X U E2 Heq Hf. subst E.
    simpl in Hf.
    apply wf_typ_sum.
    + apply (IH1 E1 X U E2). reflexivity. exact (notin_union_1 X (fv_tqt T1) (fv_tqt T2) Hf).
    + apply (IH2 E1 X U E2). reflexivity. exact (notin_union_2 X (fv_tqt T1) (fv_tqt T2) Hf).
  - intros E T1 T2 w1 IH1 w2 IH2 E1 X U E2 Heq Hf. subst E.
    simpl in Hf.
    apply wf_typ_pair.
    + apply (IH1 E1 X U E2). reflexivity. exact (notin_union_1 X (fv_tqt T1) (fv_tqt T2) Hf).
    + apply (IH2 E1 X U E2). reflexivity. exact (notin_union_2 X (fv_tqt T1) (fv_tqt T2) Hf).
  - intros E Q T wq wT IHT E1 X U E2 Heq Hf. subst E.
    simpl in Hf.
    apply wf_qtyp_qtyp.
    + exact (wf_qua_remove_sub_mid Q E1 X U E2 wq).
    + apply (IHT E1 X U E2). reflexivity. exact Hf.
Qed.

(* qualifier fvs are unchanged by type-variable opening *)
Fixpoint fv_qt_open_tt (T:typ) {struct T} :
  forall K Y X, X `notin` fv_qt T -> X `notin` fv_qt (open_tt_rec K (typ_fvar Y) T)
with fv_qqt_open_tqt (T:qtyp) {struct T} :
  forall K Y X, X `notin` fv_qqt T -> X `notin` fv_qqt (open_tqt_rec K (typ_fvar Y) T).
Proof.
  - destruct T; intros K Y X Hf; simpl in *; try exact Hf.
    + match goal with |- X `notin` fv_qt (if ?c then _ else _) => destruct c as [Heq|Hneq] end; simpl; exact (notin_empty_1 X).
    + apply notin_union_3.
      * apply (fv_qqt_open_tqt _ K Y X). exact (notin_union_1 _ _ _ Hf).
      * apply (fv_qqt_open_tqt _ (S K) Y X). exact (notin_union_2 _ _ _ Hf).
    + apply notin_union_3.
      * apply (fv_qt_open_tt _ K Y X). exact (notin_union_1 _ _ _ Hf).
      * apply (fv_qqt_open_tqt _ (S K) Y X). exact (notin_union_2 _ _ _ Hf).
    + apply notin_union_3.
      * exact (notin_union_1 _ _ _ Hf).
      * apply (fv_qqt_open_tqt _ (S K) Y X). exact (notin_union_2 _ _ _ Hf).
    + apply notin_union_3.
      * apply (fv_qqt_open_tqt _ K Y X). exact (notin_union_1 _ _ _ Hf).
      * apply (fv_qqt_open_tqt _ K Y X). exact (notin_union_2 _ _ _ Hf).
    + apply notin_union_3.
      * apply (fv_qqt_open_tqt _ K Y X). exact (notin_union_1 _ _ _ Hf).
      * apply (fv_qqt_open_tqt _ K Y X). exact (notin_union_2 _ _ _ Hf).
    + apply (fv_qqt_open_tqt _ K Y X). exact Hf.
  - destruct T as [Q T]. intros K Y X Hf. simpl in *.
    apply notin_union_3.
    + exact (notin_union_1 _ _ _ Hf).
    + apply (fv_qt_open_tt _ K Y X). exact (notin_union_2 _ _ _ Hf).
Qed.

(* qualifier fvs under qualifier opening *)
Fixpoint fv_qq_open_qq (Q:qua) {struct Q} :
  forall K Y X, X `notin` fv_qq Q -> X <> Y ->
    X `notin` fv_qq (open_qq_rec K (qua_fvar Y) Q).
Proof.
  destruct Q; intros K Y X Hf Hne; simpl in *; try exact Hf.
  - destruct (eq_dec K n) as [Heq|Hneq]; simpl.
    + apply notin_singleton_2. intro HYX. apply Hne. symmetry. exact HYX.
    + exact (notin_empty_1 X).
  - apply notin_union_3.
    + apply (fv_qq_open_qq _ K Y X). exact (notin_union_1 _ _ _ Hf). exact Hne.
    + apply (fv_qq_open_qq _ K Y X). exact (notin_union_2 _ _ _ Hf). exact Hne.
  - apply notin_union_3.
    + apply (fv_qq_open_qq _ K Y X). exact (notin_union_1 _ _ _ Hf). exact Hne.
    + apply (fv_qq_open_qq _ K Y X). exact (notin_union_2 _ _ _ Hf). exact Hne.
  - apply (fv_qq_open_qq _ K Y X). exact Hf. exact Hne.
Qed.

Fixpoint fv_qt_open_qt (T:typ) {struct T} :
  forall K Y X, X `notin` fv_qt T -> X <> Y ->
    X `notin` fv_qt (open_qt_rec K (qua_fvar Y) T)
with fv_qqt_open_qqt (T:qtyp) {struct T} :
  forall K Y X, X `notin` fv_qqt T -> X <> Y ->
    X `notin` fv_qqt (open_qqt_rec K (qua_fvar Y) T).
Proof.
  - destruct T; intros K Y X Hf Hne; simpl in *; try exact Hf.
    + apply notin_union_3.
      * apply (fv_qqt_open_qqt _ K Y X). exact (notin_union_1 _ _ _ Hf). exact Hne.
      * apply (fv_qqt_open_qqt _ (S K) Y X). exact (notin_union_2 _ _ _ Hf). exact Hne.
    + apply notin_union_3.
      * apply (fv_qt_open_qt _ K Y X). exact (notin_union_1 _ _ _ Hf). exact Hne.
      * apply (fv_qqt_open_qqt _ (S K) Y X). exact (notin_union_2 _ _ _ Hf). exact Hne.
    + simpl. apply notin_union_3.
      * apply (fv_qq_open_qq _ K Y X). exact (notin_union_1 _ _ _ Hf). exact Hne.
      * apply (fv_qqt_open_qqt _ (S K) Y X). exact (notin_union_2 _ _ _ Hf). exact Hne.
    + apply notin_union_3.
      * apply (fv_qqt_open_qqt _ K Y X). exact (notin_union_1 _ _ _ Hf). exact Hne.
      * apply (fv_qqt_open_qqt _ K Y X). exact (notin_union_2 _ _ _ Hf). exact Hne.
    + apply notin_union_3.
      * apply (fv_qqt_open_qqt _ K Y X). exact (notin_union_1 _ _ _ Hf). exact Hne.
      * apply (fv_qqt_open_qqt _ K Y X). exact (notin_union_2 _ _ _ Hf). exact Hne.
    + apply (fv_qqt_open_qqt _ K Y X). exact Hf. exact Hne.
  - destruct T as [Qw Tw]. intros K Y X Hf Hne. simpl in *.
    apply notin_union_3.
    + apply (fv_qq_open_qq Qw K Y X). exact (notin_union_1 X (fv_qq Qw) (fv_qt Tw) Hf). exact Hne.
    + apply (fv_qt_open_qt Tw K Y X). exact (notin_union_2 X (fv_qq Qw) (fv_qt Tw) Hf). exact Hne.
Qed.

Lemma binds_sub_remove_qua_mid : forall (E1:env) X (Q0:qua) (E2:env) z U,
  binds z (bind_sub U) (E1 ++ X ~ bind_qua Q0 ++ E2) -> binds z (bind_sub U) (E1 ++ E2).
Proof.
  intros E1 X Q0 E2 z U H. unfold binds in *.
  apply in_app_iff.
  apply in_app_iff in H. destruct H as [H|H]; [left;auto|].
  simpl in H. destruct H as [Heq|H].
  - inversion Heq; subst; discriminate.
  - right; auto.
Qed.

(* ========================================================= *)
(* wf removal of a bind_qua, with qualifier freshness          *)
(* ========================================================= *)

Lemma wf_typ_qtyp_remove_qua_mid :
  (forall (E:env) (T:typ), wf_typ E T ->
     forall (E1:env) X (Q0:qua) (E2:env),
       E = E1 ++ X ~ bind_qua Q0 ++ E2 -> X `notin` fv_qt T ->
       wf_typ (E1 ++ E2) T) /\
  (forall (E:env) (T:qtyp), wf_qtyp E T ->
     forall (E1:env) X (Q0:qua) (E2:env),
       E = E1 ++ X ~ bind_qua Q0 ++ E2 -> X `notin` fv_qqt T ->
       wf_qtyp (E1 ++ E2) T).
Proof.
  apply wf_tq_mut
    with (P := fun E T _ => forall (E1:env) X (Q0:qua) (E2:env),
                E = E1 ++ X ~ bind_qua Q0 ++ E2 -> X `notin` fv_qt T ->
                wf_typ (E1 ++ E2) T)
         (P0 := fun E T _ => forall (E1:env) X (Q0:qua) (E2:env),
                E = E1 ++ X ~ bind_qua Q0 ++ E2 -> X `notin` fv_qqt T ->
                wf_qtyp (E1 ++ E2) T).
  - intros E E1 X Q0 E2 Heq Hf. subst E. constructor.
  - intros E E1 X Q0 E2 Heq Hf. subst E. constructor.
  - intros U E X' b E1 X Q0 E2 Heq Hf. subst E.
    eapply wf_typ_var. exact (binds_sub_remove_qua_mid E1 X Q0 E2 X' U b).
  - intros E T1 T2 w1 IH1 w2 IH2 E1 X Q0 E2 Heq Hf. subst E.
    simpl in Hf.
    apply wf_typ_arrow.
    + apply (IH1 E1 X Q0 E2). reflexivity. exact (notin_union_1 X (fv_qqt T1) (fv_qqt T2) Hf).
    + apply (IH2 E1 X Q0 E2). reflexivity. exact (notin_union_2 X (fv_qqt T1) (fv_qqt T2) Hf).
  - intros L E T1 T2 w1 IH1 w0 IH0 E1 X Q0 E2 Heq Hf. subst E.
    simpl in Hf.
    assert (Hf1 : X `notin` fv_qt T1) by (exact (notin_union_1 X (fv_qt T1) (fv_qqt T2) Hf)).
    assert (Hf2 : X `notin` fv_qqt T2) by (exact (notin_union_2 X (fv_qt T1) (fv_qqt T2) Hf)).
    eapply wf_typ_all with (L := L).
    + apply (IH1 E1 X Q0 E2). reflexivity. exact Hf1.
    + intros Y HY.
      apply (IH0 Y HY (Y ~ bind_sub T1 ++ E1) X Q0 E2).
      * rewrite app_assoc. reflexivity.
      * exact (fv_qqt_open_tqt T2 0 Y X Hf2).
  - intros L E T1 T2 wq w0 IH0 E1 X Q0 E2 Heq Hf. subst E.
    simpl in Hf.
    assert (Hf1 : X `notin` fv_qq T1) by (exact (notin_union_1 X (fv_qq T1) (fv_qqt T2) Hf)).
    assert (Hf2 : X `notin` fv_qqt T2) by (exact (notin_union_2 X (fv_qq T1) (fv_qqt T2) Hf)).
    eapply wf_typ_qall with (L := L \u singleton X).
    + exact (wf_qua_remove_qua_mid T1 E1 X Q0 E2 Hf1 wq).
    + intros Y HY.
      assert (HYL : Y `notin` L) by (exact (notin_union_1 Y L (singleton X) HY)).
      assert (HYs : Y `notin` singleton X) by (exact (notin_union_2 Y L (singleton X) HY)).
      assert (HXY : X <> Y) by (exact (notin_singleton_1 X Y HYs)).
      apply (IH0 Y HYL (Y ~ bind_qua T1 ++ E1) X Q0 E2).
      * rewrite app_assoc. reflexivity.
      * exact (fv_qqt_open_qqt T2 0 Y X Hf2 HXY).
  - intros E T1 T2 w1 IH1 w2 IH2 E1 X Q0 E2 Heq Hf. subst E.
    simpl in Hf.
    apply wf_typ_sum.
    + apply (IH1 E1 X Q0 E2). reflexivity. exact (notin_union_1 X (fv_qqt T1) (fv_qqt T2) Hf).
    + apply (IH2 E1 X Q0 E2). reflexivity. exact (notin_union_2 X (fv_qqt T1) (fv_qqt T2) Hf).
  - intros E T1 T2 w1 IH1 w2 IH2 E1 X Q0 E2 Heq Hf. subst E.
    simpl in Hf.
    apply wf_typ_pair.
    + apply (IH1 E1 X Q0 E2). reflexivity. exact (notin_union_1 X (fv_qqt T1) (fv_qqt T2) Hf).
    + apply (IH2 E1 X Q0 E2). reflexivity. exact (notin_union_2 X (fv_qqt T1) (fv_qqt T2) Hf).
  - intros E Q T wq wT IHT E1 X Q0 E2 Heq Hf. subst E.
    simpl in Hf.
    assert (Hf1 : X `notin` fv_qq Q) by (exact (notin_union_1 X (fv_qq Q) (fv_qt T) Hf)).
    assert (Hf2 : X `notin` fv_qt T) by (exact (notin_union_2 X (fv_qq Q) (fv_qt T) Hf)).
    apply wf_qtyp_qtyp.
    + exact (wf_qua_remove_qua_mid Q E1 X Q0 E2 Hf1 wq).
    + apply (IHT E1 X Q0 E2). reflexivity. exact Hf2.
Qed.

(* ================= ChunkExp.v ================= *)

Fixpoint lc_exp (e:exp) (d:nat) : Prop :=
  match e with
  | exp_int _ _ => True
  | exp_bvar n => n < d
  | exp_fvar _ => True
  | exp_abs _ _ e1 => lc_exp e1 (S d)
  | exp_app e1 e2 => lc_exp e1 d /\ lc_exp e2 d
  | exp_tabs _ _ e1 => lc_exp e1 (S d)
  | exp_tapp e1 _ => lc_exp e1 d
  | exp_qabs _ _ e1 => lc_exp e1 (S d)
  | exp_qapp e1 _ => lc_exp e1 d
  | exp_let e1 e2 => lc_exp e1 d /\ lc_exp e2 (S d)
  | exp_inl _ e1 => lc_exp e1 d
  | exp_inr _ e1 => lc_exp e1 d
  | exp_case e1 e2 e3 => lc_exp e1 d /\ lc_exp e2 (S d) /\ lc_exp e3 (S d)
  | exp_pair _ e1 e2 => lc_exp e1 d /\ lc_exp e2 d
  | exp_first e1 => lc_exp e1 d
  | exp_second e1 => lc_exp e1 d
  | exp_ref _ e1 => lc_exp e1 d
  | exp_ref_label _ _ => True
  | exp_deref e1 => lc_exp e1 d
  | exp_set_ref e1 e2 => lc_exp e1 d /\ lc_exp e2 d
  | exp_upqual _ e1 => lc_exp e1 d
  | exp_check _ e1 => lc_exp e1 d
  | exp_without _ e1 => lc_exp e1 d
  | exp_do _ => True
  | exp_if0 e1 e2 e3 => lc_exp e1 d /\ lc_exp e2 d /\ lc_exp e3 d
  end.

Fixpoint open_ee_rec_lc (e:exp) {struct e} :
  forall d, lc_exp e d -> forall K f, d <= K -> open_ee_rec K f e = e.
Proof.
  destruct e; intros d H K f HK; simpl in *; try reflexivity.
  - (* bvar *) destruct (eq_dec K n) as [Heq|Hneq]; [|reflexivity]. exfalso; lia.
  - (* abs *) f_equal. apply (open_ee_rec_lc _ (S d)); [exact H | apply le_n_S; exact HK].
  - (* app *) destruct H as [H1 H2]. f_equal.
    + apply (open_ee_rec_lc _ d); [exact H1 | exact HK].
    + apply (open_ee_rec_lc _ d); [exact H2 | exact HK].
  - (* tabs *) f_equal. apply (open_ee_rec_lc _ (S d)); [exact H | apply le_n_S; exact HK].
  - (* tapp *) f_equal. apply (open_ee_rec_lc _ d); [exact H | exact HK].
  - (* qabs *) f_equal. apply (open_ee_rec_lc _ (S d)); [exact H | apply le_n_S; exact HK].
  - (* qapp *) f_equal. apply (open_ee_rec_lc _ d); [exact H | exact HK].
  - (* let *) destruct H as [H1 H2]. f_equal.
    + apply (open_ee_rec_lc _ d); [exact H1 | exact HK].
    + apply (open_ee_rec_lc _ (S d)); [exact H2 | apply le_n_S; exact HK].
  - (* inl *) f_equal. apply (open_ee_rec_lc _ d); [exact H | exact HK].
  - (* inr *) f_equal. apply (open_ee_rec_lc _ d); [exact H | exact HK].
  - (* case *) destruct H as [H1 [H2 H3]]. f_equal.
    + apply (open_ee_rec_lc _ d); [exact H1 | exact HK].
    + apply (open_ee_rec_lc _ (S d)); [exact H2 | apply le_n_S; exact HK].
    + apply (open_ee_rec_lc _ (S d)); [exact H3 | apply le_n_S; exact HK].
  - (* pair *) destruct H as [H1 H2]. f_equal.
    + apply (open_ee_rec_lc _ d); [exact H1 | exact HK].
    + apply (open_ee_rec_lc _ d); [exact H2 | exact HK].
  - (* first *) f_equal. apply (open_ee_rec_lc _ d); [exact H | exact HK].
  - (* second *) f_equal. apply (open_ee_rec_lc _ d); [exact H | exact HK].
  - (* ref *) f_equal. apply (open_ee_rec_lc _ d); [exact H | exact HK].
  - (* deref *) f_equal. apply (open_ee_rec_lc _ d); [exact H | exact HK].
  - (* set_ref *) destruct H as [H1 H2]. f_equal.
    + apply (open_ee_rec_lc _ d); [exact H1 | exact HK].
    + apply (open_ee_rec_lc _ d); [exact H2 | exact HK].
  - (* upqual *) f_equal. apply (open_ee_rec_lc _ d); [exact H | exact HK].
  - (* check *) f_equal. apply (open_ee_rec_lc _ d); [exact H | exact HK].
  - (* without *) f_equal. apply (open_ee_rec_lc _ d); [exact H | exact HK].
  - (* if0 *) destruct H as [H1 [H2 H3]]. f_equal.
    + apply (open_ee_rec_lc _ d); [exact H1 | exact HK].
    + apply (open_ee_rec_lc _ d); [exact H2 | exact HK].
    + apply (open_ee_rec_lc _ d); [exact H3 | exact HK].
Qed.

Fixpoint lc_exp_mono (e:exp) {struct e} : forall d, lc_exp e d -> lc_exp e (S d).
Proof.
  destruct e; intros d H; simpl in *; try exact I; try lia.
  - (* abs *) apply (lc_exp_mono _ (S d)); exact H.
  - (* app *) destruct H as [H1 H2]. split.
    + apply (lc_exp_mono _ d); exact H1.
    + apply (lc_exp_mono _ d); exact H2.
  - (* tabs *) apply (lc_exp_mono _ (S d)); exact H.
  - (* tapp *) apply (lc_exp_mono _ d); exact H.
  - (* qabs *) apply (lc_exp_mono _ (S d)); exact H.
  - (* qapp *) apply (lc_exp_mono _ d); exact H.
  - (* let *) destruct H as [H1 H2]. split.
    + apply (lc_exp_mono _ d); exact H1.
    + apply (lc_exp_mono _ (S d)); exact H2.
  - (* inl *) apply (lc_exp_mono _ d); exact H.
  - (* inr *) apply (lc_exp_mono _ d); exact H.
  - (* case *) destruct H as [H1 [H2 H3]]. split; [apply (lc_exp_mono _ d); exact H1|split].
    + apply (lc_exp_mono _ (S d)); exact H2.
    + apply (lc_exp_mono _ (S d)); exact H3.
  - (* pair *) destruct H as [H1 H2]. split.
    + apply (lc_exp_mono _ d); exact H1.
    + apply (lc_exp_mono _ d); exact H2.
  - (* first *) apply (lc_exp_mono _ d); exact H.
  - (* second *) apply (lc_exp_mono _ d); exact H.
  - (* ref *) apply (lc_exp_mono _ d); exact H.
  - (* deref *) apply (lc_exp_mono _ d); exact H.
  - (* set_ref *) destruct H as [H1 H2]. split.
    + apply (lc_exp_mono _ d); exact H1.
    + apply (lc_exp_mono _ d); exact H2.
  - (* upqual *) apply (lc_exp_mono _ d); exact H.
  - (* check *) apply (lc_exp_mono _ d); exact H.
  - (* without *) apply (lc_exp_mono _ d); exact H.
  - (* if0 *) destruct H as [H1 [H2 H3]]. split; [apply (lc_exp_mono _ d); exact H1|split].
    + apply (lc_exp_mono _ d); exact H2.
    + apply (lc_exp_mono _ d); exact H3.
Qed.

Fixpoint lc_exp_open_ee (e:exp) {struct e} :
  forall K Y d, lc_exp (open_ee_rec K (exp_fvar Y) e) d -> lc_exp e (Nat.max d (S K)).
Proof.
  destruct e; intros K Y d H; simpl in *; try exact I.
  - (* bvar *) destruct (eq_dec K n) as [Heq|Hneq]; simpl in *.
    + assert (Hn : n < S K) by (rewrite Heq; apply Nat.lt_succ_diag_r).
      assert (Hm : S K <= Nat.max d (S K)) by apply Nat.le_max_r. lia.
    + apply Nat.lt_le_trans with d; [exact H | apply Nat.le_max_l].
  - (* abs *) rewrite Nat.succ_max_distr. apply (lc_exp_open_ee _ (S K) Y (S d)). exact H.
  - (* app *) destruct H as [H1 H2]. split.
    + apply (lc_exp_open_ee _ K Y d). exact H1.
    + apply (lc_exp_open_ee _ K Y d). exact H2.
  - (* tabs *) rewrite Nat.succ_max_distr. apply (lc_exp_open_ee _ (S K) Y (S d)). exact H.
  - (* tapp *) apply (lc_exp_open_ee _ K Y d). exact H.
  - (* qabs *) rewrite Nat.succ_max_distr. apply (lc_exp_open_ee _ (S K) Y (S d)). exact H.
  - (* qapp *) apply (lc_exp_open_ee _ K Y d). exact H.
  - (* let *) destruct H as [H1 H2]. split.
    + apply (lc_exp_open_ee _ K Y d). exact H1.
    + rewrite Nat.succ_max_distr. apply (lc_exp_open_ee _ (S K) Y (S d)). exact H2.
  - (* inl *) apply (lc_exp_open_ee _ K Y d). exact H.
  - (* inr *) apply (lc_exp_open_ee _ K Y d). exact H.
  - (* case *) destruct H as [H1 [H2 H3]]. split; [apply (lc_exp_open_ee _ K Y d); exact H1 | split].
    + rewrite Nat.succ_max_distr. apply (lc_exp_open_ee _ (S K) Y (S d)). exact H2.
    + rewrite Nat.succ_max_distr. apply (lc_exp_open_ee _ (S K) Y (S d)). exact H3.
  - (* pair *) destruct H as [H1 H2]. split.
    + apply (lc_exp_open_ee _ K Y d). exact H1.
    + apply (lc_exp_open_ee _ K Y d). exact H2.
  - (* first *) apply (lc_exp_open_ee _ K Y d). exact H.
  - (* second *) apply (lc_exp_open_ee _ K Y d). exact H.
  - (* ref *) apply (lc_exp_open_ee _ K Y d). exact H.
  - (* deref *) apply (lc_exp_open_ee _ K Y d). exact H.
  - (* set_ref *) destruct H as [H1 H2]. split.
    + apply (lc_exp_open_ee _ K Y d). exact H1.
    + apply (lc_exp_open_ee _ K Y d). exact H2.
  - (* upqual *) apply (lc_exp_open_ee _ K Y d). exact H.
  - (* check *) apply (lc_exp_open_ee _ K Y d). exact H.
  - (* without *) apply (lc_exp_open_ee _ K Y d). exact H.
  - (* if0 *) destruct H as [H1 [H2 H3]]. split; [apply (lc_exp_open_ee _ K Y d); exact H1 | split].
    + apply (lc_exp_open_ee _ K Y d). exact H2.
    + apply (lc_exp_open_ee _ K Y d). exact H3.
Qed.

(* open_te / open_qe do not change expression local closure *)
Fixpoint lc_exp_open_te_fwd (e:exp) {struct e} :
  forall K U d, lc_exp (open_te_rec K U e) d -> lc_exp e d.
Proof.
  destruct e; intros K U d H; simpl in *; try exact H.
  - (* abs *) apply (lc_exp_open_te_fwd _ (S K) U (S d)); exact H.
  - (* app *) destruct H as [H1 H2]. split.
    + apply (lc_exp_open_te_fwd _ K U d); exact H1.
    + apply (lc_exp_open_te_fwd _ K U d); exact H2.
  - (* tabs *) apply (lc_exp_open_te_fwd _ (S K) U (S d)); exact H.
  - (* tapp *) apply (lc_exp_open_te_fwd _ K U d); exact H.
  - (* qabs *) apply (lc_exp_open_te_fwd _ (S K) U (S d)); exact H.
  - (* qapp *) apply (lc_exp_open_te_fwd _ K U d); exact H.
  - (* let *) destruct H as [H1 H2]. split.
    + apply (lc_exp_open_te_fwd _ K U d); exact H1.
    + apply (lc_exp_open_te_fwd _ (S K) U (S d)); exact H2.
  - (* inl *) apply (lc_exp_open_te_fwd _ K U d); exact H.
  - (* inr *) apply (lc_exp_open_te_fwd _ K U d); exact H.
  - (* case *) destruct H as [H1 [H2 H3]]. split; [apply (lc_exp_open_te_fwd _ K U d); exact H1|split].
    + apply (lc_exp_open_te_fwd _ (S K) U (S d)); exact H2.
    + apply (lc_exp_open_te_fwd _ (S K) U (S d)); exact H3.
  - (* pair *) destruct H as [H1 H2]. split.
    + apply (lc_exp_open_te_fwd _ K U d); exact H1.
    + apply (lc_exp_open_te_fwd _ K U d); exact H2.
  - (* first *) apply (lc_exp_open_te_fwd _ K U d); exact H.
  - (* second *) apply (lc_exp_open_te_fwd _ K U d); exact H.
  - (* ref *) apply (lc_exp_open_te_fwd _ K U d); exact H.
  - (* deref *) apply (lc_exp_open_te_fwd _ K U d); exact H.
  - (* set_ref *) destruct H as [H1 H2]. split.
    + apply (lc_exp_open_te_fwd _ K U d); exact H1.
    + apply (lc_exp_open_te_fwd _ K U d); exact H2.
  - (* upqual *) apply (lc_exp_open_te_fwd _ K U d); exact H.
  - (* check *) apply (lc_exp_open_te_fwd _ K U d); exact H.
  - (* without *) apply (lc_exp_open_te_fwd _ K U d); exact H.
  - (* if0 *) destruct H as [H1 [H2 H3]]. split; [apply (lc_exp_open_te_fwd _ K U d); exact H1|split].
    + apply (lc_exp_open_te_fwd _ K U d); exact H2.
    + apply (lc_exp_open_te_fwd _ K U d); exact H3.
Qed.

Fixpoint lc_exp_open_qe_fwd (e:exp) {struct e} :
  forall K R d, lc_exp (open_qe_rec K R e) d -> lc_exp e d.
Proof.
  destruct e; intros K R d H; simpl in *; try exact H.
  - (* abs *) apply (lc_exp_open_qe_fwd _ (S K) R (S d)); exact H.
  - (* app *) destruct H as [H1 H2]. split.
    + apply (lc_exp_open_qe_fwd _ K R d); exact H1.
    + apply (lc_exp_open_qe_fwd _ K R d); exact H2.
  - (* tabs *) apply (lc_exp_open_qe_fwd _ (S K) R (S d)); exact H.
  - (* tapp *) apply (lc_exp_open_qe_fwd _ K R d); exact H.
  - (* qabs *) apply (lc_exp_open_qe_fwd _ (S K) R (S d)); exact H.
  - (* qapp *) apply (lc_exp_open_qe_fwd _ K R d); exact H.
  - (* let *) destruct H as [H1 H2]. split.
    + apply (lc_exp_open_qe_fwd _ K R d); exact H1.
    + apply (lc_exp_open_qe_fwd _ (S K) R (S d)); exact H2.
  - (* inl *) apply (lc_exp_open_qe_fwd _ K R d); exact H.
  - (* inr *) apply (lc_exp_open_qe_fwd _ K R d); exact H.
  - (* case *) destruct H as [H1 [H2 H3]]. split; [apply (lc_exp_open_qe_fwd _ K R d); exact H1|split].
    + apply (lc_exp_open_qe_fwd _ (S K) R (S d)); exact H2.
    + apply (lc_exp_open_qe_fwd _ (S K) R (S d)); exact H3.
  - (* pair *) destruct H as [H1 H2]. split.
    + apply (lc_exp_open_qe_fwd _ K R d); exact H1.
    + apply (lc_exp_open_qe_fwd _ K R d); exact H2.
  - (* first *) apply (lc_exp_open_qe_fwd _ K R d); exact H.
  - (* second *) apply (lc_exp_open_qe_fwd _ K R d); exact H.
  - (* ref *) apply (lc_exp_open_qe_fwd _ K R d); exact H.
  - (* deref *) apply (lc_exp_open_qe_fwd _ K R d); exact H.
  - (* set_ref *) destruct H as [H1 H2]. split.
    + apply (lc_exp_open_qe_fwd _ K R d); exact H1.
    + apply (lc_exp_open_qe_fwd _ K R d); exact H2.
  - (* upqual *) apply (lc_exp_open_qe_fwd _ K R d); exact H.
  - (* check *) apply (lc_exp_open_qe_fwd _ K R d); exact H.
  - (* without *) apply (lc_exp_open_qe_fwd _ K R d); exact H.
  - (* if0 *) destruct H as [H1 [H2 H3]]. split; [apply (lc_exp_open_qe_fwd _ K R d); exact H1|split].
    + apply (lc_exp_open_qe_fwd _ K R d); exact H2.
    + apply (lc_exp_open_qe_fwd _ K R d); exact H3.
Qed.

Lemma expr_lc : forall e, expr e -> lc_exp e 0.
Proof.
  intros e H. induction H.
  - simpl. exact I.
  - simpl. exact I.
  - (* abs *)
    simpl. pick fresh z.
    pose proof (H3 z Fr) as Hx.
    pose proof (lc_exp_open_ee e1 0 z 0 Hx) as Hc.
    change (lc_exp e1 1) in Hc. exact Hc.
  - (* app *) simpl. split; assumption.
  - (* tabs *)
    simpl. pick fresh z.
    pose proof (H2 z Fr) as Hx.
    pose proof (lc_exp_open_te_fwd e1 0 (typ_fvar z) 0 Hx) as Hc.
    apply lc_exp_mono in Hc. change (lc_exp e1 1) in Hc. exact Hc.
  - (* tapp *) simpl. assumption.
  - (* qabs *)
    simpl. pick fresh z.
    pose proof (H2 z Fr) as Hx.
    pose proof (lc_exp_open_qe_fwd e1 0 (qua_fvar z) 0 Hx) as Hc.
    apply lc_exp_mono in Hc. change (lc_exp e1 1) in Hc. exact Hc.
  - (* qapp *) simpl. assumption.
  - (* let *)
    simpl. split.
    + exact IHexpr.
    + pick fresh z.
      pose proof (H1 z Fr) as Hx.
      pose proof (lc_exp_open_ee e2 0 z 0 Hx) as Hc.
      change (lc_exp e2 1) in Hc. exact Hc.
  - (* inl *) simpl. assumption.
  - (* inr *) simpl. assumption.
  - (* case *)
    simpl. split.
    + exact IHexpr.
    + split.
      * pick fresh z.
        pose proof (H1 z Fr) as Hx.
        pose proof (lc_exp_open_ee e2 0 z 0 Hx) as Hc.
        change (lc_exp e2 1) in Hc. exact Hc.
      * pick fresh z.
        pose proof (H3 z Fr) as Hx.
        pose proof (lc_exp_open_ee e3 0 z 0 Hx) as Hc.
        change (lc_exp e3 1) in Hc. exact Hc.
  - (* pair *) simpl. split; assumption.
  - (* first *) simpl. assumption.
  - (* second *) simpl. assumption.
  - (* upqual *) simpl. assumption.
  - (* check *) simpl. assumption.
  - (* without *) simpl. assumption.
  - (* do *) simpl. exact I.
  - (* if0 *) simpl. split; [assumption|split; assumption].
Qed.

Lemma value_expr : forall v, value v -> expr v.
Proof.
  intros v H. induction H.
  - apply expr_int. exact H.
  - exact H.
  - exact H.
  - exact H.
  - apply expr_inl; assumption.
  - apply expr_inr; assumption.
  - apply expr_pair; assumption.
Qed.

Definition closed_ee (v:exp) : Prop := forall K f, open_ee_rec K f v = v.

Lemma value_closed_ee : forall v, value v -> closed_ee v.
Proof.
  intros v Hv K f. apply open_ee_rec_lc with (d:=0).
  - apply expr_lc. apply value_expr. exact Hv.
  - apply Nat.le_0_l.
Qed.

(* ================= ChunkExp2.v ================= *)

(* ---------- qualifier-level annotation facts ---------- *)
Lemma qual_lc_any : forall Q, qual Q -> forall d, lc_qq Q d.
Proof.
  intros Q H. induction H; intros d; simpl.
  - exact I.
  - exact I.
  - split; auto.
  - split; auto.
  - auto.
Qed.

(* type-opening does not affect qualifier-level closure *)
Fixpoint lc_tt_q_open_tt_fwd (T:typ) {struct T} :
  forall K X d, lc_tt_q (open_tt_rec K (typ_fvar X) T) d -> lc_tt_q T d
with lc_qqt_open_tqt_fwd (T:qtyp) {struct T} :
  forall K X d, lc_qqt (open_tqt_rec K (typ_fvar X) T) d -> lc_qqt T d.
Proof.
  - destruct T; intros K X d H; simpl in *.
    + exact I. + exact I. + exact I. + exact I.
    + destruct H as [H1 H2]; split.
      * apply (lc_qqt_open_tqt_fwd _ K X d). exact H1.
      * apply (lc_qqt_open_tqt_fwd _ (S K) X (S d)). exact H2.
    + destruct H as [H1 H2]; split.
      * apply (lc_tt_q_open_tt_fwd _ K X d). exact H1.
      * apply (lc_qqt_open_tqt_fwd _ (S K) X (S d)). exact H2.
    + destruct H as [H1 H2]; split.
      * exact H1.
      * apply (lc_qqt_open_tqt_fwd _ (S K) X (S d)). exact H2.
    + destruct H as [H1 H2]; split.
      * apply (lc_qqt_open_tqt_fwd _ K X d). exact H1.
      * apply (lc_qqt_open_tqt_fwd _ K X d). exact H2.
    + destruct H as [H1 H2]; split.
      * apply (lc_qqt_open_tqt_fwd _ K X d). exact H1.
      * apply (lc_qqt_open_tqt_fwd _ K X d). exact H2.
    + apply (lc_qqt_open_tqt_fwd _ K X d). exact H.
  - destruct T as [Q T]. intros K X d H. simpl in *.
    destruct H as [H1 H2]; split.
    + exact H1.
    + apply (lc_tt_q_open_tt_fwd _ K X d). exact H2.
Qed.

Lemma type_qtype_lc_qq_any :
  (forall (T:typ), type T -> forall d, lc_tt_q T d) /\
  (forall (T:qtyp), qtype T -> forall d, lc_qqt T d).
Proof.
  apply type_q_mut
    with (P := fun T _ => forall d, lc_tt_q T d)
         (P0 := fun T _ => forall d, lc_qqt T d).
  - intros d. exact I.
  - intros d. exact I.
  - intros X d. exact I.
  - intros T1 T2 H1 IH1 H2 IH2 d. simpl. split; auto.
  - intros L T1 T2 HT1 IHT1 Hbody IHbody d. simpl. split.
    + apply IHT1.
    + pick fresh X for L.
      pose proof (IHbody X Fr (S d)) as Hx.
      apply (lc_qqt_open_tqt_fwd T2 0 X (S d)). exact Hx.
  - intros L Q T Hq Hbody IHbody d. simpl. split.
    + apply qual_lc_any; exact Hq.
    + pick fresh X for L.
      pose proof (IHbody X Fr (S d)) as Hx.
      pose proof (lc_qqt_open_qqt T 0 X (S d) Hx) as Hc.
      replace (Nat.max (S d) (S 0)) with (S d) in Hc by (destruct d; simpl; reflexivity).
      exact Hc.
  - intros T1 T2 H1 IH1 H2 IH2 d. simpl. split; auto.
  - intros T1 T2 H1 IH1 H2 IH2 d. simpl. split; auto.
  - intros Q T Hq HT IHT d. simpl. split.
    + apply qual_lc_any; exact Hq.
    + apply IHT.
Qed.

(* ---------- type-variable closure of expressions ---------- *)
Fixpoint lc_te_exp (e:exp) (d:nat) : Prop :=
  match e with
  | exp_int _ _ => True
  | exp_bvar _ => True
  | exp_fvar _ => True
  | exp_abs _ V e1 => lc_tqt V d /\ lc_te_exp e1 (S d)
  | exp_app e1 e2 => lc_te_exp e1 d /\ lc_te_exp e2 d
  | exp_tabs _ V e1 => lc_tt V d /\ lc_te_exp e1 (S d)
  | exp_tapp e1 V => lc_te_exp e1 d /\ lc_tt V d
  | exp_qabs _ _ e1 => lc_te_exp e1 (S d)
  | exp_qapp e1 _ => lc_te_exp e1 d
  | exp_let e1 e2 => lc_te_exp e1 d /\ lc_te_exp e2 (S d)
  | exp_inl _ e1 => lc_te_exp e1 d
  | exp_inr _ e1 => lc_te_exp e1 d
  | exp_case e1 e2 e3 => lc_te_exp e1 d /\ lc_te_exp e2 (S d) /\ lc_te_exp e3 (S d)
  | exp_pair _ e1 e2 => lc_te_exp e1 d /\ lc_te_exp e2 d
  | exp_first e1 => lc_te_exp e1 d
  | exp_second e1 => lc_te_exp e1 d
  | exp_ref _ e1 => lc_te_exp e1 d
  | exp_ref_label _ _ => True
  | exp_deref e1 => lc_te_exp e1 d
  | exp_set_ref e1 e2 => lc_te_exp e1 d /\ lc_te_exp e2 d
  | exp_upqual _ e1 => lc_te_exp e1 d
  | exp_check _ e1 => lc_te_exp e1 d
  | exp_without _ e1 => lc_te_exp e1 d
  | exp_do _ => True
  | exp_if0 e1 e2 e3 => lc_te_exp e1 d /\ lc_te_exp e2 d /\ lc_te_exp e3 d
  end.

Fixpoint open_te_rec_lc (e:exp) {struct e} :
  forall d, lc_te_exp e d -> forall K U, d <= K -> open_te_rec K U e = e.
Proof.
  destruct e as [P i|i|a|P V e1|e1 e2|P V e1|e1 V|P Q e1|e1 Q|e1 e2|P e1|P e1|e1 e2 e3|P e1 e2|e1|e1|P e1|P l|e1|e1 e2|P e1|P e1|P e1|b|e1 e2 e3];
    intros d H K U HK; simpl in *; try reflexivity.
  - (* abs *) destruct H as [H1 H2]. simpl. f_equal.
    + apply (open_tqt_lc V d H1 K U HK).
    + apply (open_te_rec_lc e1 (S d) H2 (S K) U (le_n_S _ _ HK)).
  - (* app *) destruct H as [H1 H2]. simpl. f_equal.
    + apply (open_te_rec_lc e1 d H1 K U HK).
    + apply (open_te_rec_lc e2 d H2 K U HK).
  - (* tabs *) destruct H as [H1 H2]. simpl. f_equal.
    + apply (open_tt_lc V d H1 K U HK).
    + apply (open_te_rec_lc e1 (S d) H2 (S K) U (le_n_S _ _ HK)).
  - (* tapp *) destruct H as [H1 H2]. simpl. f_equal.
    + apply (open_te_rec_lc e1 d H1 K U HK).
    + apply (open_tt_lc V d H2 K U HK).
  - (* qabs *) simpl. f_equal.
    apply (open_te_rec_lc e1 (S d) H (S K) U (le_n_S _ _ HK)).
  - (* qapp *) simpl. f_equal.
    apply (open_te_rec_lc e1 d H K U HK).
  - (* let *) destruct H as [H1 H2]. simpl. f_equal.
    + apply (open_te_rec_lc e1 d H1 K U HK).
    + apply (open_te_rec_lc e2 (S d) H2 (S K) U (le_n_S _ _ HK)).
  - (* inl *) simpl. f_equal. apply (open_te_rec_lc e1 d H K U HK).
  - (* inr *) simpl. f_equal. apply (open_te_rec_lc e1 d H K U HK).
  - (* case *) destruct H as [H1 [H2 H3]]. simpl. f_equal.
    + apply (open_te_rec_lc e1 d H1 K U HK).
    + apply (open_te_rec_lc e2 (S d) H2 (S K) U (le_n_S _ _ HK)).
    + apply (open_te_rec_lc e3 (S d) H3 (S K) U (le_n_S _ _ HK)).
  - (* pair *) destruct H as [H1 H2]. simpl. f_equal.
    + apply (open_te_rec_lc e1 d H1 K U HK).
    + apply (open_te_rec_lc e2 d H2 K U HK).
  - (* first *) simpl. f_equal. apply (open_te_rec_lc e1 d H K U HK).
  - (* second *) simpl. f_equal. apply (open_te_rec_lc e1 d H K U HK).
  - (* ref *) simpl. f_equal. apply (open_te_rec_lc e1 d H K U HK).
  - (* deref *) simpl. f_equal. apply (open_te_rec_lc e1 d H K U HK).
  - (* set_ref *) destruct H as [H1 H2]. simpl. f_equal.
    + apply (open_te_rec_lc e1 d H1 K U HK).
    + apply (open_te_rec_lc e2 d H2 K U HK).
  - (* upqual *) simpl. f_equal. apply (open_te_rec_lc e1 d H K U HK).
  - (* check *) simpl. f_equal. apply (open_te_rec_lc e1 d H K U HK).
  - (* without *) simpl. f_equal. apply (open_te_rec_lc e1 d H K U HK).
  - (* if0 *) destruct H as [H1 [H2 H3]]. simpl. f_equal.
    + apply (open_te_rec_lc e1 d H1 K U HK).
    + apply (open_te_rec_lc e2 d H2 K U HK).
    + apply (open_te_rec_lc e3 d H3 K U HK).
Qed.

Fixpoint lc_te_exp_open_te (e:exp) {struct e} :
  forall K Y d, lc_te_exp (open_te_rec K (typ_fvar Y) e) d ->
    lc_te_exp e (Nat.max d (S K)).
Proof.
  destruct e as [P i|i|a|P V e1|e1 e2|P V e1|e1 V|P Q e1|e1 Q|e1 e2|P e1|P e1|e1 e2 e3|P e1 e2|e1|e1|P e1|P l|e1|e1 e2|P e1|P e1|P e1|b|e1 e2 e3];
    intros K Y d H; simpl in *; try exact H.
  - (* abs *) destruct H as [H1 H2]. split.
    + apply (lc_tqt_open_tqt V K Y d H1).
    + rewrite Nat.succ_max_distr. apply (lc_te_exp_open_te e1 (S K) Y (S d) H2).
  - (* app *) destruct H as [H1 H2]. split.
    + apply (lc_te_exp_open_te e1 K Y d H1).
    + apply (lc_te_exp_open_te e2 K Y d H2).
  - (* tabs *) destruct H as [H1 H2]. split.
    + apply (lc_tt_open_tt V K Y d H1).
    + rewrite Nat.succ_max_distr. apply (lc_te_exp_open_te e1 (S K) Y (S d) H2).
  - (* tapp *) destruct H as [H1 H2]. split.
    + apply (lc_te_exp_open_te e1 K Y d H1).
    + apply (lc_tt_open_tt V K Y d H2).
  - (* qabs *) rewrite Nat.succ_max_distr. apply (lc_te_exp_open_te e1 (S K) Y (S d) H).
  - (* qapp *) apply (lc_te_exp_open_te e1 K Y d H).
  - (* let *) destruct H as [H1 H2]. split.
    + apply (lc_te_exp_open_te e1 K Y d H1).
    + rewrite Nat.succ_max_distr. apply (lc_te_exp_open_te e2 (S K) Y (S d) H2).
  - (* inl *) apply (lc_te_exp_open_te e1 K Y d H).
  - (* inr *) apply (lc_te_exp_open_te e1 K Y d H).
  - (* case *) destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_te_exp_open_te e1 K Y d H1).
    + rewrite Nat.succ_max_distr. apply (lc_te_exp_open_te e2 (S K) Y (S d) H2).
    + rewrite Nat.succ_max_distr. apply (lc_te_exp_open_te e3 (S K) Y (S d) H3).
  - (* pair *) destruct H as [H1 H2]. split.
    + apply (lc_te_exp_open_te e1 K Y d H1).
    + apply (lc_te_exp_open_te e2 K Y d H2).
  - (* first *) apply (lc_te_exp_open_te e1 K Y d H).
  - (* second *) apply (lc_te_exp_open_te e1 K Y d H).
  - (* ref *) apply (lc_te_exp_open_te e1 K Y d H).
  - (* deref *) apply (lc_te_exp_open_te e1 K Y d H).
  - (* set_ref *) destruct H as [H1 H2]. split.
    + apply (lc_te_exp_open_te e1 K Y d H1).
    + apply (lc_te_exp_open_te e2 K Y d H2).
  - (* upqual *) apply (lc_te_exp_open_te e1 K Y d H).
  - (* check *) apply (lc_te_exp_open_te e1 K Y d H).
  - (* without *) apply (lc_te_exp_open_te e1 K Y d H).
  - (* if0 *) destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_te_exp_open_te e1 K Y d H1).
    + apply (lc_te_exp_open_te e2 K Y d H2).
    + apply (lc_te_exp_open_te e3 K Y d H3).
Qed.

Fixpoint lc_te_exp_open_ee_fwd (e:exp) {struct e} :
  forall K f d, lc_te_exp (open_ee_rec K f e) d -> lc_te_exp e d.
Proof.
  destruct e as [P i|i|a|P V e1|e1 e2|P V e1|e1 V|P Q e1|e1 Q|e1 e2|P e1|P e1|e1 e2 e3|P e1 e2|e1|e1|P e1|P l|e1|e1 e2|P e1|P e1|P e1|b|e1 e2 e3];
    intros K f d H; simpl in *; try exact H.
  - (* bvar *) exact I.
  - (* abs *) destruct H as [H1 H2]. split.
    + exact H1.
    + apply (lc_te_exp_open_ee_fwd e1 (S K) f (S d) H2).
  - (* app *) destruct H as [H1 H2]. split; [apply (lc_te_exp_open_ee_fwd e1 K f d H1)|apply (lc_te_exp_open_ee_fwd e2 K f d H2)].
  - (* tabs *) destruct H as [H1 H2]. split.
    + exact H1.
    + apply (lc_te_exp_open_ee_fwd e1 (S K) f (S d) H2).
  - (* tapp *) destruct H as [H1 H2]. split; [apply (lc_te_exp_open_ee_fwd e1 K f d H1)|exact H2].
  - (* qabs *) apply (lc_te_exp_open_ee_fwd e1 (S K) f (S d) H).
  - (* qapp *) apply (lc_te_exp_open_ee_fwd e1 K f d H).
  - (* let *) destruct H as [H1 H2]. split; [apply (lc_te_exp_open_ee_fwd e1 K f d H1)|apply (lc_te_exp_open_ee_fwd e2 (S K) f (S d) H2)].
  - (* inl *) apply (lc_te_exp_open_ee_fwd e1 K f d H).
  - (* inr *) apply (lc_te_exp_open_ee_fwd e1 K f d H).
  - (* case *) destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_te_exp_open_ee_fwd e1 K f d H1).
    + apply (lc_te_exp_open_ee_fwd e2 (S K) f (S d) H2).
    + apply (lc_te_exp_open_ee_fwd e3 (S K) f (S d) H3).
  - (* pair *) destruct H as [H1 H2]. split; [apply (lc_te_exp_open_ee_fwd e1 K f d H1)|apply (lc_te_exp_open_ee_fwd e2 K f d H2)].
  - (* first *) apply (lc_te_exp_open_ee_fwd e1 K f d H).
  - (* second *) apply (lc_te_exp_open_ee_fwd e1 K f d H).
  - (* ref *) apply (lc_te_exp_open_ee_fwd e1 K f d H).
  - (* deref *) apply (lc_te_exp_open_ee_fwd e1 K f d H).
  - (* set_ref *) destruct H as [H1 H2]. split; [apply (lc_te_exp_open_ee_fwd e1 K f d H1)|apply (lc_te_exp_open_ee_fwd e2 K f d H2)].
  - (* upqual *) apply (lc_te_exp_open_ee_fwd e1 K f d H).
  - (* check *) apply (lc_te_exp_open_ee_fwd e1 K f d H).
  - (* without *) apply (lc_te_exp_open_ee_fwd e1 K f d H).
  - (* if0 *) destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_te_exp_open_ee_fwd e1 K f d H1).
    + apply (lc_te_exp_open_ee_fwd e2 K f d H2).
    + apply (lc_te_exp_open_ee_fwd e3 K f d H3).
Qed.

Fixpoint lc_te_exp_open_qe_fwd (e:exp) {struct e} :
  forall K R d, lc_te_exp (open_qe_rec K R e) d -> lc_te_exp e d.
Proof.
  destruct e as [P i|i|a|P V e1|e1 e2|P V e1|e1 V|P Q e1|e1 Q|e1 e2|P e1|P e1|e1 e2 e3|P e1 e2|e1|e1|P e1|P l|e1|e1 e2|P e1|P e1|P e1|b|e1 e2 e3];
    intros K R d H; simpl in *; try exact H.
  - (* abs *) destruct H as [H1 H2]. split.
    + apply (lc_tqt_open_qual_fwd V K R d H1).
    + apply (lc_te_exp_open_qe_fwd e1 (S K) R (S d) H2).
  - (* app *) destruct H as [H1 H2]. split; [apply (lc_te_exp_open_qe_fwd e1 K R d H1)|apply (lc_te_exp_open_qe_fwd e2 K R d H2)].
  - (* tabs *) destruct H as [H1 H2]. split.
    + apply (lc_tt_open_qual_fwd V K R d H1).
    + apply (lc_te_exp_open_qe_fwd e1 (S K) R (S d) H2).
  - (* tapp *) destruct H as [H1 H2]. split; [apply (lc_te_exp_open_qe_fwd e1 K R d H1)|apply (lc_tt_open_qual_fwd V K R d H2)].
  - (* qabs *) apply (lc_te_exp_open_qe_fwd e1 (S K) R (S d) H).
  - (* qapp *) apply (lc_te_exp_open_qe_fwd e1 K R d H).
  - (* let *) destruct H as [H1 H2]. split; [apply (lc_te_exp_open_qe_fwd e1 K R d H1)|apply (lc_te_exp_open_qe_fwd e2 (S K) R (S d) H2)].
  - (* inl *) apply (lc_te_exp_open_qe_fwd e1 K R d H).
  - (* inr *) apply (lc_te_exp_open_qe_fwd e1 K R d H).
  - (* case *) destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_te_exp_open_qe_fwd e1 K R d H1).
    + apply (lc_te_exp_open_qe_fwd e2 (S K) R (S d) H2).
    + apply (lc_te_exp_open_qe_fwd e3 (S K) R (S d) H3).
  - (* pair *) destruct H as [H1 H2]. split; [apply (lc_te_exp_open_qe_fwd e1 K R d H1)|apply (lc_te_exp_open_qe_fwd e2 K R d H2)].
  - (* first *) apply (lc_te_exp_open_qe_fwd e1 K R d H).
  - (* second *) apply (lc_te_exp_open_qe_fwd e1 K R d H).
  - (* ref *) apply (lc_te_exp_open_qe_fwd e1 K R d H).
  - (* deref *) apply (lc_te_exp_open_qe_fwd e1 K R d H).
  - (* set_ref *) destruct H as [H1 H2]. split; [apply (lc_te_exp_open_qe_fwd e1 K R d H1)|apply (lc_te_exp_open_qe_fwd e2 K R d H2)].
  - (* upqual *) apply (lc_te_exp_open_qe_fwd e1 K R d H).
  - (* check *) apply (lc_te_exp_open_qe_fwd e1 K R d H).
  - (* without *) apply (lc_te_exp_open_qe_fwd e1 K R d H).
  - (* if0 *) destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_te_exp_open_qe_fwd e1 K R d H1).
    + apply (lc_te_exp_open_qe_fwd e2 K R d H2).
    + apply (lc_te_exp_open_qe_fwd e3 K R d H3).
Qed.

Fixpoint lc_te_exp_mono (e:exp) {struct e} :
  forall d, lc_te_exp e d -> lc_te_exp e (S d).
Proof.
  destruct e as [P i|i|a|P V e1|e1 e2|P V e1|e1 V|P Q e1|e1 Q|e1 e2|P e1|P e1|e1 e2 e3|P e1 e2|e1|e1|P e1|P l|e1|e1 e2|P e1|P e1|P e1|b|e1 e2 e3];
    intros d H; simpl in *; try exact H.
  - destruct H as [H1 H2]. split.
    + apply (lc_tqt_mono V d H1).
    + apply (lc_te_exp_mono e1 (S d) H2).
  - destruct H as [H1 H2]. split; [apply (lc_te_exp_mono e1 d H1)|apply (lc_te_exp_mono e2 d H2)].
  - destruct H as [H1 H2]. split.
    + apply (lc_tt_mono V d H1).
    + apply (lc_te_exp_mono e1 (S d) H2).
  - destruct H as [H1 H2]. split; [apply (lc_te_exp_mono e1 d H1)|apply (lc_tt_mono V d H2)].
  - apply (lc_te_exp_mono e1 (S d) H).
  - apply (lc_te_exp_mono e1 d H).
  - destruct H as [H1 H2]. split; [apply (lc_te_exp_mono e1 d H1)|apply (lc_te_exp_mono e2 (S d) H2)].
  - apply (lc_te_exp_mono e1 d H).
  - apply (lc_te_exp_mono e1 d H).
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_te_exp_mono e1 d H1).
    + apply (lc_te_exp_mono e2 (S d) H2).
    + apply (lc_te_exp_mono e3 (S d) H3).
  - destruct H as [H1 H2]. split; [apply (lc_te_exp_mono e1 d H1)|apply (lc_te_exp_mono e2 d H2)].
  - apply (lc_te_exp_mono e1 d H).
  - apply (lc_te_exp_mono e1 d H).
  - apply (lc_te_exp_mono e1 d H).
  - apply (lc_te_exp_mono e1 d H).
  - destruct H as [H1 H2]. split; [apply (lc_te_exp_mono e1 d H1)|apply (lc_te_exp_mono e2 d H2)].
  - apply (lc_te_exp_mono e1 d H).
  - apply (lc_te_exp_mono e1 d H).
  - apply (lc_te_exp_mono e1 d H).
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_te_exp_mono e1 d H1).
    + apply (lc_te_exp_mono e2 d H2).
    + apply (lc_te_exp_mono e3 d H3).
Qed.

Lemma expr_lc_te : forall e, expr e -> lc_te_exp e 0.
Proof.
  intros e H.
  induction H as [P0 i Hq
    | x
    | L P0 T e1 Hq HT Hq' Hbody IHbody
    | e1 e2 He1 IH1 He2 IH2
    | L P0 T e1 Hq HT Hbody IHbody
    | e1 V He1 IH1 HT
    | L P0 Q e1 Hq HQ Hbody IHbody
    | e1 Q He1 IH1 HQ
    | L e1 e2 He1 IH1 Hbody IHbody
    | P0 e1 Hq He1 IH1
    | P0 e1 Hq He1 IH1
    | L e1 e2 e3 He1 IH1 Hbody2 IH2 Hbody3 IH3
    | P0 e1 e2 Hq He1 IH1 He2 IH2
    | e1 He1 IH1
    | e1 He1 IH1
    | P0 e1 Hq He1 IH1
    | P0 e1 Hq He1 IH1
    | P0 e1 Hq He1 IH1
    | b
    | e1 e2 e3 He1 IH1 He2 IH2 He3 IH3].
  - exact I.
  - exact I.
  - (* abs *) split.
    + exact (proj2 type_qtype_lc T HT).
    + pick fresh x for L. pose proof (IHbody x Fr) as Hx.
      apply lc_te_exp_mono. apply (lc_te_exp_open_ee_fwd e1 0 (exp_fvar x) 0 Hx).
  - (* app *) split; [exact IH1 | exact IH2].
  - (* tabs *) split.
    + exact (proj1 type_qtype_lc T HT).
    + pick fresh X for L. pose proof (IHbody X Fr) as Hx.
      pose proof (lc_te_exp_open_te e1 0 X 0 Hx) as Hc.
      change (lc_te_exp e1 1) in Hc. exact Hc.
  - (* tapp *) split.
    + exact IH1.
    + exact (proj1 type_qtype_lc V HT).
  - (* qabs *) pick fresh X for L. pose proof (IHbody X Fr) as Hx.
    apply lc_te_exp_mono. apply (lc_te_exp_open_qe_fwd e1 0 (qua_fvar X) 0 Hx).
  - (* qapp *) exact IH1.
  - (* let *) split.
    + exact IH1.
    + pick fresh x for L. pose proof (IHbody x Fr) as Hx.
      apply lc_te_exp_mono. apply (lc_te_exp_open_ee_fwd e2 0 (exp_fvar x) 0 Hx).
  - (* inl *) exact IH1.
  - (* inr *) exact IH1.
  - (* case *) split; [exact IH1 | split].
    + pick fresh x for L. pose proof (IH2 x Fr) as Hx.
      apply lc_te_exp_mono. apply (lc_te_exp_open_ee_fwd e2 0 (exp_fvar x) 0 Hx).
    + pick fresh x for L. pose proof (IH3 x Fr) as Hx.
      apply lc_te_exp_mono. apply (lc_te_exp_open_ee_fwd e3 0 (exp_fvar x) 0 Hx).
  - (* pair *) split; [exact IH1 | exact IH2].
  - exact IH1.
  - exact IH1.
  - (* upqual *) exact IH1.
  - (* check *) exact IH1.
  - (* without *) exact IH1.
  - exact I.
  - (* if0 *) split; [exact IH1 | split; [exact IH2 | exact IH3]].
Qed.

Definition closed_te (v:exp) : Prop := forall K U, open_te_rec K U v = v.

Lemma value_closed_te : forall v, value v -> closed_te v.
Proof.
  intros v Hv K U.
  apply (open_te_rec_lc v 0 (expr_lc_te v (value_expr v Hv)) K U (Nat.le_0_l K)).
Qed.

(* ---------- qualifier-variable closure of expressions ---------- *)
Fixpoint lc_qe_exp (e:exp) (d:nat) : Prop :=
  match e with
  | exp_int P _ => lc_qq P d
  | exp_bvar _ => True
  | exp_fvar _ => True
  | exp_abs P V e1 => lc_qq P d /\ lc_qqt V d /\ lc_qe_exp e1 (S d)
  | exp_app e1 e2 => lc_qe_exp e1 d /\ lc_qe_exp e2 d
  | exp_tabs P V e1 => lc_qq P d /\ lc_tt_q V d /\ lc_qe_exp e1 (S d)
  | exp_tapp e1 V => lc_qe_exp e1 d /\ lc_tt_q V d
  | exp_qabs P Q e1 => lc_qq P d /\ lc_qq Q d /\ lc_qe_exp e1 (S d)
  | exp_qapp e1 Q => lc_qe_exp e1 d /\ lc_qq Q d
  | exp_let e1 e2 => lc_qe_exp e1 d /\ lc_qe_exp e2 (S d)
  | exp_inl P e1 => lc_qq P d /\ lc_qe_exp e1 d
  | exp_inr P e1 => lc_qq P d /\ lc_qe_exp e1 d
  | exp_case e1 e2 e3 => lc_qe_exp e1 d /\ lc_qe_exp e2 (S d) /\ lc_qe_exp e3 (S d)
  | exp_pair P e1 e2 => lc_qq P d /\ lc_qe_exp e1 d /\ lc_qe_exp e2 d
  | exp_first e1 => lc_qe_exp e1 d
  | exp_second e1 => lc_qe_exp e1 d
  | exp_ref P e1 => lc_qq P d /\ lc_qe_exp e1 d
  | exp_ref_label P _ => lc_qq P d
  | exp_deref e1 => lc_qe_exp e1 d
  | exp_set_ref e1 e2 => lc_qe_exp e1 d /\ lc_qe_exp e2 d
  | exp_upqual P e1 => lc_qq P d /\ lc_qe_exp e1 d
  | exp_check P e1 => lc_qq P d /\ lc_qe_exp e1 d
  | exp_without P e1 => lc_qq P d /\ lc_qe_exp e1 d
  | exp_do _ => True
  | exp_if0 e1 e2 e3 => lc_qe_exp e1 d /\ lc_qe_exp e2 d /\ lc_qe_exp e3 d
  end.

Fixpoint open_qe_rec_lc (e:exp) {struct e} :
  forall d, lc_qe_exp e d -> forall K R, d <= K -> open_qe_rec K R e = e.
Proof.
  destruct e as [P i|i|a|P V e1|e1 e2|P V e1|e1 V|P Q e1|e1 Q|e1 e2|P e1|P e1|e1 e2 e3|P e1 e2|e1|e1|P e1|P l|e1|e1 e2|P e1|P e1|P e1|b|e1 e2 e3];
    intros d H K R HK; simpl in *; try reflexivity.
  - (* int *) f_equal. apply (open_qq_lc P d H K R HK).
  - (* abs *) destruct H as [H1 [H2 H3]]. simpl. f_equal.
    + apply (open_qq_lc P d H1 K R HK).
    + apply (open_qqt_lc V d H2 K R HK).
    + apply (open_qe_rec_lc e1 (S d) H3 (S K) R (le_n_S _ _ HK)).
  - (* app *) destruct H as [H1 H2]. simpl. f_equal.
    + apply (open_qe_rec_lc e1 d H1 K R HK).
    + apply (open_qe_rec_lc e2 d H2 K R HK).
  - (* tabs *) destruct H as [H1 [H2 H3]]. simpl. f_equal.
    + apply (open_qq_lc P d H1 K R HK).
    + apply (open_qt_lc V d H2 K R HK).
    + apply (open_qe_rec_lc e1 (S d) H3 (S K) R (le_n_S _ _ HK)).
  - (* tapp *) destruct H as [H1 H2]. simpl. f_equal.
    + apply (open_qe_rec_lc e1 d H1 K R HK).
    + apply (open_qt_lc V d H2 K R HK).
  - (* qabs *) destruct H as [H1 [H2 H3]]. simpl. f_equal.
    + apply (open_qq_lc P d H1 K R HK).
    + apply (open_qq_lc Q d H2 K R HK).
    + apply (open_qe_rec_lc e1 (S d) H3 (S K) R (le_n_S _ _ HK)).
  - (* qapp *) destruct H as [H1 H2]. simpl. f_equal.
    + apply (open_qe_rec_lc e1 d H1 K R HK).
    + apply (open_qq_lc Q d H2 K R HK).
  - (* let *) destruct H as [H1 H2]. simpl. f_equal.
    + apply (open_qe_rec_lc e1 d H1 K R HK).
    + apply (open_qe_rec_lc e2 (S d) H2 (S K) R (le_n_S _ _ HK)).
  - (* inl *) destruct H as [H1 H2]. simpl. f_equal.
    + apply (open_qq_lc P d H1 K R HK).
    + apply (open_qe_rec_lc e1 d H2 K R HK).
  - (* inr *) destruct H as [H1 H2]. simpl. f_equal.
    + apply (open_qq_lc P d H1 K R HK).
    + apply (open_qe_rec_lc e1 d H2 K R HK).
  - (* case *) destruct H as [H1 [H2 H3]]. simpl. f_equal.
    + apply (open_qe_rec_lc e1 d H1 K R HK).
    + apply (open_qe_rec_lc e2 (S d) H2 (S K) R (le_n_S _ _ HK)).
    + apply (open_qe_rec_lc e3 (S d) H3 (S K) R (le_n_S _ _ HK)).
  - (* pair *) destruct H as [H1 [H2 H3]]. simpl. f_equal.
    + apply (open_qq_lc P d H1 K R HK).
    + apply (open_qe_rec_lc e1 d H2 K R HK).
    + apply (open_qe_rec_lc e2 d H3 K R HK).
  - (* first *) simpl. f_equal. apply (open_qe_rec_lc e1 d H K R HK).
  - (* second *) simpl. f_equal. apply (open_qe_rec_lc e1 d H K R HK).
  - (* ref *) destruct H as [H1 H2]. simpl. f_equal.
    + apply (open_qq_lc P d H1 K R HK).
    + apply (open_qe_rec_lc e1 d H2 K R HK).
  - (* ref_label *) simpl. f_equal. apply (open_qq_lc P d H K R HK).
  - (* deref *) simpl. f_equal. apply (open_qe_rec_lc e1 d H K R HK).
  - (* set_ref *) destruct H as [H1 H2]. simpl. f_equal.
    + apply (open_qe_rec_lc e1 d H1 K R HK).
    + apply (open_qe_rec_lc e2 d H2 K R HK).
  - (* upqual *) destruct H as [H1 H2]. simpl. f_equal.
    + apply (open_qq_lc P d H1 K R HK).
    + apply (open_qe_rec_lc e1 d H2 K R HK).
  - (* check *) destruct H as [H1 H2]. simpl. f_equal.
    + apply (open_qq_lc P d H1 K R HK).
    + apply (open_qe_rec_lc e1 d H2 K R HK).
  - (* without *) destruct H as [H1 H2]. simpl. f_equal.
    + apply (open_qq_lc P d H1 K R HK).
    + apply (open_qe_rec_lc e1 d H2 K R HK).
  - (* if0 *) destruct H as [H1 [H2 H3]]. simpl. f_equal.
    + apply (open_qe_rec_lc e1 d H1 K R HK).
    + apply (open_qe_rec_lc e2 d H2 K R HK).
    + apply (open_qe_rec_lc e3 d H3 K R HK).
Qed.

Fixpoint lc_qe_exp_open_qe (e:exp) {struct e} :
  forall K Y d, lc_qe_exp (open_qe_rec K (qua_fvar Y) e) d ->
    lc_qe_exp e (Nat.max d (S K)).
Proof.
  destruct e as [P i|i|a|P V e1|e1 e2|P V e1|e1 V|P Q e1|e1 Q|e1 e2|P e1|P e1|e1 e2 e3|P e1 e2|e1|e1|P e1|P l|e1|e1 e2|P e1|P e1|P e1|b|e1 e2 e3];
    intros K Y d H; simpl in *; try exact H.
  - (* int *) apply (lc_qq_open_qq P K Y d H).
  - (* abs *) destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_qq_open_qq P K Y d H1).
    + apply (lc_qqt_open_qqt V K Y d H2).
    + rewrite Nat.succ_max_distr. apply (lc_qe_exp_open_qe e1 (S K) Y (S d) H3).
  - (* app *) destruct H as [H1 H2]. split.
    + apply (lc_qe_exp_open_qe e1 K Y d H1).
    + apply (lc_qe_exp_open_qe e2 K Y d H2).
  - (* tabs *) destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_qq_open_qq P K Y d H1).
    + apply (lc_qt_open_qt V K Y d H2).
    + rewrite Nat.succ_max_distr. apply (lc_qe_exp_open_qe e1 (S K) Y (S d) H3).
  - (* tapp *) destruct H as [H1 H2]. split.
    + apply (lc_qe_exp_open_qe e1 K Y d H1).
    + apply (lc_qt_open_qt V K Y d H2).
  - (* qabs *) destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_qq_open_qq P K Y d H1).
    + apply (lc_qq_open_qq Q K Y d H2).
    + rewrite Nat.succ_max_distr. apply (lc_qe_exp_open_qe e1 (S K) Y (S d) H3).
  - (* qapp *) destruct H as [H1 H2]. split.
    + apply (lc_qe_exp_open_qe e1 K Y d H1).
    + apply (lc_qq_open_qq Q K Y d H2).
  - (* let *) destruct H as [H1 H2]. split.
    + apply (lc_qe_exp_open_qe e1 K Y d H1).
    + rewrite Nat.succ_max_distr. apply (lc_qe_exp_open_qe e2 (S K) Y (S d) H2).
  - (* inl *) destruct H as [H1 H2]. split.
    + apply (lc_qq_open_qq P K Y d H1).
    + apply (lc_qe_exp_open_qe e1 K Y d H2).
  - (* inr *) destruct H as [H1 H2]. split.
    + apply (lc_qq_open_qq P K Y d H1).
    + apply (lc_qe_exp_open_qe e1 K Y d H2).
  - (* case *) destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_qe_exp_open_qe e1 K Y d H1).
    + rewrite Nat.succ_max_distr. apply (lc_qe_exp_open_qe e2 (S K) Y (S d) H2).
    + rewrite Nat.succ_max_distr. apply (lc_qe_exp_open_qe e3 (S K) Y (S d) H3).
  - (* pair *) destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_qq_open_qq P K Y d H1).
    + apply (lc_qe_exp_open_qe e1 K Y d H2).
    + apply (lc_qe_exp_open_qe e2 K Y d H3).
  - (* first *) apply (lc_qe_exp_open_qe e1 K Y d H).
  - (* second *) apply (lc_qe_exp_open_qe e1 K Y d H).
  - (* ref *) destruct H as [H1 H2]. split.
    + apply (lc_qq_open_qq P K Y d H1).
    + apply (lc_qe_exp_open_qe e1 K Y d H2).
  - (* ref_label *) apply (lc_qq_open_qq P K Y d H).
  - (* deref *) apply (lc_qe_exp_open_qe e1 K Y d H).
  - (* set_ref *) destruct H as [H1 H2]. split.
    + apply (lc_qe_exp_open_qe e1 K Y d H1).
    + apply (lc_qe_exp_open_qe e2 K Y d H2).
  - (* upqual *) destruct H as [H1 H2]. split.
    + apply (lc_qq_open_qq P K Y d H1).
    + apply (lc_qe_exp_open_qe e1 K Y d H2).
  - (* check *) destruct H as [H1 H2]. split.
    + apply (lc_qq_open_qq P K Y d H1).
    + apply (lc_qe_exp_open_qe e1 K Y d H2).
  - (* without *) destruct H as [H1 H2]. split.
    + apply (lc_qq_open_qq P K Y d H1).
    + apply (lc_qe_exp_open_qe e1 K Y d H2).
  - (* if0 *) destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_qe_exp_open_qe e1 K Y d H1).
    + apply (lc_qe_exp_open_qe e2 K Y d H2).
    + apply (lc_qe_exp_open_qe e3 K Y d H3).
Qed.

Fixpoint lc_qe_exp_open_ee_fwd (e:exp) {struct e} :
  forall K f d, lc_qe_exp (open_ee_rec K f e) d -> lc_qe_exp e d.
Proof.
  destruct e as [P i|i|a|P V e1|e1 e2|P V e1|e1 V|P Q e1|e1 Q|e1 e2|P e1|P e1|e1 e2 e3|P e1 e2|e1|e1|P e1|P l|e1|e1 e2|P e1|P e1|P e1|b|e1 e2 e3];
    intros K f d H; simpl in *.
  - (* int *) exact H.
  - exact I. - exact I.
  - (* abs *) destruct H as [H1 [H2 H3]]. split; [|split]; [exact H1|exact H2|].
    apply (lc_qe_exp_open_ee_fwd e1 (S K) f (S d) H3).
  - (* app *) destruct H as [H1 H2]. split; [apply (lc_qe_exp_open_ee_fwd e1 K f d H1)|apply (lc_qe_exp_open_ee_fwd e2 K f d H2)].
  - (* tabs *) destruct H as [H1 [H2 H3]]. split; [|split]; [exact H1|exact H2|].
    apply (lc_qe_exp_open_ee_fwd e1 (S K) f (S d) H3).
  - (* tapp *) destruct H as [H1 H2]. split; [apply (lc_qe_exp_open_ee_fwd e1 K f d H1)|exact H2].
  - (* qabs *) destruct H as [H1 [H2 H3]]. split; [|split]; [exact H1|exact H2|].
    apply (lc_qe_exp_open_ee_fwd e1 (S K) f (S d) H3).
  - (* qapp *) destruct H as [H1 H2]. split; [apply (lc_qe_exp_open_ee_fwd e1 K f d H1)|exact H2].
  - (* let *) destruct H as [H1 H2]. split; [apply (lc_qe_exp_open_ee_fwd e1 K f d H1)|apply (lc_qe_exp_open_ee_fwd e2 (S K) f (S d) H2)].
  - (* inl *) destruct H as [H1 H2]. split; [exact H1|apply (lc_qe_exp_open_ee_fwd e1 K f d H2)].
  - (* inr *) destruct H as [H1 H2]. split; [exact H1|apply (lc_qe_exp_open_ee_fwd e1 K f d H2)].
  - (* case *) destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_qe_exp_open_ee_fwd e1 K f d H1).
    + apply (lc_qe_exp_open_ee_fwd e2 (S K) f (S d) H2).
    + apply (lc_qe_exp_open_ee_fwd e3 (S K) f (S d) H3).
  - (* pair *) destruct H as [H1 [H2 H3]]. split; [|split].
    + exact H1.
    + apply (lc_qe_exp_open_ee_fwd e1 K f d H2).
    + apply (lc_qe_exp_open_ee_fwd e2 K f d H3).
  - (* first *) apply (lc_qe_exp_open_ee_fwd e1 K f d H).
  - (* second *) apply (lc_qe_exp_open_ee_fwd e1 K f d H).
  - (* ref *) destruct H as [H1 H2]. split; [exact H1|apply (lc_qe_exp_open_ee_fwd e1 K f d H2)].
  - (* ref_label *) exact H.
  - (* deref *) apply (lc_qe_exp_open_ee_fwd e1 K f d H).
  - (* set_ref *) destruct H as [H1 H2]. split; [apply (lc_qe_exp_open_ee_fwd e1 K f d H1)|apply (lc_qe_exp_open_ee_fwd e2 K f d H2)].
  - (* upqual *) destruct H as [H1 H2]. split; [exact H1|apply (lc_qe_exp_open_ee_fwd e1 K f d H2)].
  - (* check *) destruct H as [H1 H2]. split; [exact H1|apply (lc_qe_exp_open_ee_fwd e1 K f d H2)].
  - (* without *) destruct H as [H1 H2]. split; [exact H1|apply (lc_qe_exp_open_ee_fwd e1 K f d H2)].
  - exact I.
  - (* if0 *) destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_qe_exp_open_ee_fwd e1 K f d H1).
    + apply (lc_qe_exp_open_ee_fwd e2 K f d H2).
    + apply (lc_qe_exp_open_ee_fwd e3 K f d H3).
Qed.

Fixpoint lc_qe_exp_open_te_fwd (e:exp) {struct e} :
  forall K X d, lc_qe_exp (open_te_rec K (typ_fvar X) e) d -> lc_qe_exp e d.
Proof.
  destruct e as [P i|i|a|P V e1|e1 e2|P V e1|e1 V|P Q e1|e1 Q|e1 e2|P e1|P e1|e1 e2 e3|P e1 e2|e1|e1|P e1|P l|e1|e1 e2|P e1|P e1|P e1|b|e1 e2 e3];
    intros K X d H; simpl in *.
  - exact H.
  - exact I. - exact I.
  - (* abs *) destruct H as [H1 [H2 H3]]. split; [|split]; [exact H1| |].
    + apply (lc_qqt_open_tqt_fwd V K X d). exact H2.
    + apply (lc_qe_exp_open_te_fwd e1 (S K) X (S d) H3).
  - (* app *) destruct H as [H1 H2]. split; [apply (lc_qe_exp_open_te_fwd e1 K X d H1)|apply (lc_qe_exp_open_te_fwd e2 K X d H2)].
  - (* tabs *) destruct H as [H1 [H2 H3]]. split; [|split]; [exact H1| |].
    + apply (lc_tt_q_open_tt_fwd V K X d). exact H2.
    + apply (lc_qe_exp_open_te_fwd e1 (S K) X (S d) H3).
  - (* tapp *) destruct H as [H1 H2]. split; [apply (lc_qe_exp_open_te_fwd e1 K X d H1)|].
    apply (lc_tt_q_open_tt_fwd V K X d). exact H2.
  - (* qabs *) destruct H as [H1 [H2 H3]]. split; [|split]; [exact H1|exact H2|].
    apply (lc_qe_exp_open_te_fwd e1 (S K) X (S d) H3).
  - (* qapp *) destruct H as [H1 H2]. split; [apply (lc_qe_exp_open_te_fwd e1 K X d H1)|exact H2].
  - (* let *) destruct H as [H1 H2]. split; [apply (lc_qe_exp_open_te_fwd e1 K X d H1)|apply (lc_qe_exp_open_te_fwd e2 (S K) X (S d) H2)].
  - (* inl *) destruct H as [H1 H2]. split; [exact H1|apply (lc_qe_exp_open_te_fwd e1 K X d H2)].
  - (* inr *) destruct H as [H1 H2]. split; [exact H1|apply (lc_qe_exp_open_te_fwd e1 K X d H2)].
  - (* case *) destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_qe_exp_open_te_fwd e1 K X d H1).
    + apply (lc_qe_exp_open_te_fwd e2 (S K) X (S d) H2).
    + apply (lc_qe_exp_open_te_fwd e3 (S K) X (S d) H3).
  - (* pair *) destruct H as [H1 [H2 H3]]. split; [|split].
    + exact H1.
    + apply (lc_qe_exp_open_te_fwd e1 K X d H2).
    + apply (lc_qe_exp_open_te_fwd e2 K X d H3).
  - (* first *) apply (lc_qe_exp_open_te_fwd e1 K X d H).
  - (* second *) apply (lc_qe_exp_open_te_fwd e1 K X d H).
  - (* ref *) destruct H as [H1 H2]. split; [exact H1|apply (lc_qe_exp_open_te_fwd e1 K X d H2)].
  - (* ref_label *) exact H.
  - (* deref *) apply (lc_qe_exp_open_te_fwd e1 K X d H).
  - (* set_ref *) destruct H as [H1 H2]. split; [apply (lc_qe_exp_open_te_fwd e1 K X d H1)|apply (lc_qe_exp_open_te_fwd e2 K X d H2)].
  - (* upqual *) destruct H as [H1 H2]. split; [exact H1|apply (lc_qe_exp_open_te_fwd e1 K X d H2)].
  - (* check *) destruct H as [H1 H2]. split; [exact H1|apply (lc_qe_exp_open_te_fwd e1 K X d H2)].
  - (* without *) destruct H as [H1 H2]. split; [exact H1|apply (lc_qe_exp_open_te_fwd e1 K X d H2)].
  - exact I.
  - (* if0 *) destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_qe_exp_open_te_fwd e1 K X d H1).
    + apply (lc_qe_exp_open_te_fwd e2 K X d H2).
    + apply (lc_qe_exp_open_te_fwd e3 K X d H3).
Qed.

Fixpoint lc_qe_exp_mono (e:exp) {struct e} :
  forall d, lc_qe_exp e d -> lc_qe_exp e (S d).
Proof.
  destruct e as [P i|i|a|P V e1|e1 e2|P V e1|e1 V|P Q e1|e1 Q|e1 e2|P e1|P e1|e1 e2 e3|P e1 e2|e1|e1|P e1|P l|e1|e1 e2|P e1|P e1|P e1|b|e1 e2 e3];
    intros d H; simpl in *.
  - apply (lc_qq_mono P d H).
  - exact I. - exact I.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_qq_mono P d H1).
    + apply (lc_qqt_mono V d H2).
    + apply (lc_qe_exp_mono e1 (S d) H3).
  - destruct H as [H1 H2]. split; [apply (lc_qe_exp_mono e1 d H1)|apply (lc_qe_exp_mono e2 d H2)].
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_qq_mono P d H1).
    + apply (lc_qt_mono V d H2).
    + apply (lc_qe_exp_mono e1 (S d) H3).
  - destruct H as [H1 H2]. split; [apply (lc_qe_exp_mono e1 d H1)|apply (lc_qt_mono V d H2)].
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_qq_mono P d H1).
    + apply (lc_qq_mono Q d H2).
    + apply (lc_qe_exp_mono e1 (S d) H3).
  - destruct H as [H1 H2]. split; [apply (lc_qe_exp_mono e1 d H1)|apply (lc_qq_mono Q d H2)].
  - destruct H as [H1 H2]. split; [apply (lc_qe_exp_mono e1 d H1)|apply (lc_qe_exp_mono e2 (S d) H2)].
  - destruct H as [H1 H2]. split; [apply (lc_qq_mono P d H1)|apply (lc_qe_exp_mono e1 d H2)].
  - destruct H as [H1 H2]. split; [apply (lc_qq_mono P d H1)|apply (lc_qe_exp_mono e1 d H2)].
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_qe_exp_mono e1 d H1).
    + apply (lc_qe_exp_mono e2 (S d) H2).
    + apply (lc_qe_exp_mono e3 (S d) H3).
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_qq_mono P d H1).
    + apply (lc_qe_exp_mono e1 d H2).
    + apply (lc_qe_exp_mono e2 d H3).
  - apply (lc_qe_exp_mono e1 d H).
  - apply (lc_qe_exp_mono e1 d H).
  - destruct H as [H1 H2]. split; [apply (lc_qq_mono P d H1)|apply (lc_qe_exp_mono e1 d H2)].
  - apply (lc_qq_mono P d H).
  - apply (lc_qe_exp_mono e1 d H).
  - destruct H as [H1 H2]. split; [apply (lc_qe_exp_mono e1 d H1)|apply (lc_qe_exp_mono e2 d H2)].
  - destruct H as [H1 H2]. split; [apply (lc_qq_mono P d H1)|apply (lc_qe_exp_mono e1 d H2)].
  - destruct H as [H1 H2]. split; [apply (lc_qq_mono P d H1)|apply (lc_qe_exp_mono e1 d H2)].
  - destruct H as [H1 H2]. split; [apply (lc_qq_mono P d H1)|apply (lc_qe_exp_mono e1 d H2)].
  - exact I.
  - destruct H as [H1 [H2 H3]]. split; [|split].
    + apply (lc_qe_exp_mono e1 d H1).
    + apply (lc_qe_exp_mono e2 d H2).
    + apply (lc_qe_exp_mono e3 d H3).
Qed.

Lemma expr_lc_qe : forall e, expr e -> lc_qe_exp e 0.
Proof.
  intros e H.
  induction H as [P0 i Hq
    | x
    | L P0 T e1 Hq HT Hq' Hbody IHbody
    | e1 e2 He1 IH1 He2 IH2
    | L P0 T e1 Hq HT Hbody IHbody
    | e1 V He1 IH1 HT
    | L P0 Q e1 Hq HQ Hbody IHbody
    | e1 Q He1 IH1 HQ
    | L e1 e2 He1 IH1 Hbody IHbody
    | P0 e1 Hq He1 IH1
    | P0 e1 Hq He1 IH1
    | L e1 e2 e3 He1 IH1 Hbody2 IH2 Hbody3 IH3
    | P0 e1 e2 Hq He1 IH1 He2 IH2
    | e1 He1 IH1
    | e1 He1 IH1
    | P0 e1 Hq He1 IH1
    | P0 e1 Hq He1 IH1
    | P0 e1 Hq He1 IH1
    | b
    | e1 e2 e3 He1 IH1 He2 IH2 He3 IH3].
  - exact (qual_lc P0 Hq).
  - exact I.
  - (* abs *) split; [|split].
    + exact (qual_lc P0 Hq).
    + exact (proj2 type_qtype_lc_qq_any T HT 0).
    + pick fresh x for L. pose proof (IHbody x Fr) as Hx.
      apply lc_qe_exp_mono. apply (lc_qe_exp_open_ee_fwd e1 0 (exp_fvar x) 0 Hx).
  - (* app *) split; [exact IH1 | exact IH2].
  - (* tabs *) split; [|split].
    + exact (qual_lc P0 Hq).
    + exact (proj1 type_qtype_lc_qq_any T HT 0).
    + pick fresh X for L. pose proof (IHbody X Fr) as Hx.
      apply lc_qe_exp_mono. apply (lc_qe_exp_open_te_fwd e1 0 X 0 Hx).
  - (* tapp *) split.
    + exact IH1.
    + exact (proj1 type_qtype_lc_qq_any V HT 0).
  - (* qabs *) split; [|split].
    + exact (qual_lc P0 Hq).
    + exact (qual_lc Q HQ).
    + pick fresh X for L. pose proof (IHbody X Fr) as Hx.
      pose proof (lc_qe_exp_open_qe e1 0 X 0 Hx) as Hc.
      change (lc_qe_exp e1 1) in Hc. exact Hc.
  - (* qapp *) split; [exact IH1 | exact (qual_lc Q HQ)].
  - (* let *) split.
    + exact IH1.
    + pick fresh x for L. pose proof (IHbody x Fr) as Hx.
      apply lc_qe_exp_mono. apply (lc_qe_exp_open_ee_fwd e2 0 (exp_fvar x) 0 Hx).
  - (* inl *) split; [exact (qual_lc P0 Hq) | exact IH1].
  - (* inr *) split; [exact (qual_lc P0 Hq) | exact IH1].
  - (* case *) split; [exact IH1 | split].
    + pick fresh x for L. pose proof (IH2 x Fr) as Hx.
      apply lc_qe_exp_mono. apply (lc_qe_exp_open_ee_fwd e2 0 (exp_fvar x) 0 Hx).
    + pick fresh x for L. pose proof (IH3 x Fr) as Hx.
      apply lc_qe_exp_mono. apply (lc_qe_exp_open_ee_fwd e3 0 (exp_fvar x) 0 Hx).
  - (* pair *) split; [|split].
    + exact (qual_lc P0 Hq).
    + exact IH1.
    + exact IH2.
  - exact IH1.
  - exact IH1.
  - (* upqual *) split; [exact (qual_lc P0 Hq) | exact IH1].
  - (* check *) split; [exact (qual_lc P0 Hq) | exact IH1].
  - (* without *) split; [exact (qual_lc P0 Hq) | exact IH1].
  - exact I.
  - (* if0 *) split; [exact IH1 | split; [exact IH2 | exact IH3]].
Qed.

Definition closed_qe (v:exp) : Prop := forall K R, open_qe_rec K R v = v.

Lemma value_closed_qe : forall v, value v -> closed_qe v.
Proof.
  intros v Hv K R.
  apply (open_qe_rec_lc v 0 (expr_lc_qe v (value_expr v Hv)) K R (Nat.le_0_l K)).
Qed.

(* ================= ChunkInv.v ================= *)

(* ---------- reflexivity of subqual / sub / subqtype ---------- *)

Fixpoint subqual_refl_Q (Q:qua) {struct Q} :
  forall E, wf_env E -> wf_qua E Q -> subqual E Q Q.
Proof.
  destruct Q as [b|n|X|Q1 Q2|Q1 Q2|Q1]; intros E Hwf HQ.
  - apply subqual_lift_elem; [exact Hwf | apply (reflexive)].
  - inversion HQ.
  - inversion HQ; subst.
    match goal with Hb : binds X (bind_qua ?R) E |- _ =>
      eapply subqual_refl_qvar; [exact Hwf | eapply wf_qua_fvar; exact Hb] end.
  - inversion HQ; subst.
    match goal with H1 : wf_qua E Q1, H2 : wf_qua E Q2 |- subqual E (qua_meet Q1 Q2) (qua_meet Q1 Q2) =>
      apply subqual_meet_intro;
      [ eapply subqual_meet_eliml; [apply (subqual_refl_Q Q1 E Hwf H1)|exact H2]
      | eapply subqual_meet_elimr; [exact H1|apply (subqual_refl_Q Q2 E Hwf H2)] ]
    end.
  - inversion HQ; subst.
    match goal with H1 : wf_qua E Q1, H2 : wf_qua E Q2 |- subqual E (qua_join Q1 Q2) (qua_join Q1 Q2) =>
      apply subqual_join_elim;
      [ eapply subqual_join_inl; [apply (subqual_refl_Q Q1 E Hwf H1)|exact H2]
      | eapply subqual_join_inr; [exact H1|apply (subqual_refl_Q Q2 E Hwf H2)] ]
    end.
  - inversion HQ; subst. apply subqual_refl_negate; eassumption.
Qed.

Lemma subqual_refl : forall E Q, wf_env E -> wf_qua E Q -> subqual E Q Q.
Proof. intros. apply (subqual_refl_Q Q E); auto. Qed.

Lemma sub_refl_qtype :
  (forall (E:env) (T:typ), wf_typ E T -> wf_env E -> sub E T T) /\
  (forall (E:env) (T:qtyp), wf_qtyp E T -> wf_env E -> subqtype E T T).
Proof.
  apply wf_tq_mut
    with (P := fun E T _ => wf_env E -> sub E T T)
         (P0 := fun E T _ => wf_env E -> subqtype E T T).
  - intros E Hwf. apply sub_top; [exact Hwf|apply wf_typ_top].
  - intros E Hwf. apply sub_refl_int; exact Hwf.
  - intros U E X b Hwf. eapply sub_refl_tvar; [exact Hwf | eapply wf_typ_var; exact b].
  - intros E T1 T2 w1 IH1 w2 IH2 Hwf. eapply sub_arrow; [apply IH1|apply IH2]; exact Hwf.
  - intros L E T1 T2 w1 IH1 w0 IH0 Hwf.
    eapply sub_all with (L := L \u dom E).
    + apply IH1. exact Hwf.
    + intros X HX.
      assert (HXL : X `notin` L) by (exact (notin_union_1 _ _ _ HX)).
      assert (HXd : X `notin` dom E) by (exact (notin_union_2 _ _ _ HX)).
      apply (IH0 X HXL). apply wf_env_sub; auto.
  - intros L E T1 T2 wq w0 IH0 Hwf.
    eapply sub_qall with (L := L \u dom E).
    + apply subqual_refl; auto.
    + intros X HX.
      assert (HXL : X `notin` L) by (exact (notin_union_1 _ _ _ HX)).
      assert (HXd : X `notin` dom E) by (exact (notin_union_2 _ _ _ HX)).
      apply (IH0 X HXL). apply wf_env_qua; auto.
  - intros E T1 T2 w1 IH1 w2 IH2 Hwf. eapply sub_sum; [apply IH1|apply IH2]; exact Hwf.
  - intros E T1 T2 w1 IH1 w2 IH2 Hwf. eapply sub_pair; [apply IH1|apply IH2]; exact Hwf.
  - intros E Q T wq wT IHT Hwf. eapply sub_qtyp_qtyp.
    + apply subqual_refl; auto.
    + apply IHT. exact Hwf.
Qed.

Lemma sub_refl : forall E T, wf_env E -> wf_typ E T -> sub E T T.
Proof. intros. eapply (proj1 sub_refl_qtype); eauto. Qed.

Lemma subqtype_refl : forall E T, wf_env E -> wf_qtyp E T -> subqtype E T T.
Proof. intros. eapply (proj2 sub_refl_qtype); eauto. Qed.

(* ---------- inversion of sub on source shapes ---------- *)

Lemma sub_int_inv : forall E T, sub E typ_int T -> T = typ_int \/ T = typ_top.
Proof.
  intros E T H. inversion H; subst.
  all: try (right; reflexivity).
  left; reflexivity.
Qed.

Lemma sub_arrow_inv : forall E S1 S2 T, sub E (typ_arrow S1 S2) T ->
  T = typ_top \/ exists T1 T2, T = typ_arrow T1 T2 /\ subqtype E T1 S1 /\ subqtype E S2 T2.
Proof.
  intros E S1 S2 T H. dependent destruction H.
  - left; reflexivity.
  - right. exists T1, T2. split; [reflexivity|split; assumption].
Qed.

Lemma sub_sum_inv : forall E S1 S2 T, sub E (typ_sum S1 S2) T ->
  T = typ_top \/ exists T1 T2, T = typ_sum T1 T2 /\ subqtype E S1 T1 /\ subqtype E S2 T2.
Proof.
  intros E S1 S2 T H. dependent destruction H.
  - left; reflexivity.
  - right. exists T1, T2. split; [reflexivity|split; assumption].
Qed.

Lemma sub_pair_inv : forall E S1 S2 T, sub E (typ_pair S1 S2) T ->
  T = typ_top \/ exists T1 T2, T = typ_pair T1 T2 /\ subqtype E S1 T1 /\ subqtype E S2 T2.
Proof.
  intros E S1 S2 T H. dependent destruction H.
  - left; reflexivity.
  - right. exists T1, T2. split; [reflexivity|split; assumption].
Qed.

Lemma sub_all_inv : forall E S1 S2 T, sub E (typ_all S1 S2) T ->
  T = typ_top \/ exists L T1 T2, T = typ_all T1 T2 /\ sub E T1 S1 /\
    (forall X, X `notin` L -> subqtype (X ~ bind_sub T1 ++ E) (open_tqt S2 X) (open_tqt T2 X)).
Proof.
  intros E S1 S2 T H. dependent destruction H.
  - left; reflexivity.
  - right. exists L, T1, T2. split; [reflexivity|split; assumption].
Qed.

Lemma sub_qall_inv : forall E S1 S2 T, sub E (typ_qall S1 S2) T ->
  T = typ_top \/ exists L T1 T2, T = typ_qall T1 T2 /\ subqual E T1 S1 /\
    (forall X, X `notin` L -> subqtype (X ~ bind_qua T1 ++ E) (open_qqt S2 X) (open_qqt T2 X)).
Proof.
  intros E S1 S2 T H. dependent destruction H.
  - left; reflexivity.
  - right. exists L, T1, T2. split; [reflexivity|split; assumption].
Qed.

Lemma sub_tvar_inv : forall E X T, sub E (typ_fvar X) T ->
  T = typ_top \/ (T = typ_fvar X /\ wf_typ E (typ_fvar X)) \/
  (exists U, binds X (bind_sub U) E /\ sub E U T).
Proof.
  intros E X T H. dependent destruction H.
  - left; reflexivity.
  - right; left. split; [reflexivity|assumption].
  - right; right. exists U. split; assumption.
Qed.

Lemma subqtype_inv : forall E Q T R, subqtype E (qtyp_qtyp Q T) R ->
  exists Q' T', R = qtyp_qtyp Q' T' /\ subqual E Q Q' /\ sub E T T'.
Proof.
  intros E Q T R H. dependent destruction H.
  exists Q2, T2. split; [reflexivity|split; assumption].
Qed.

(* ================= ChunkAlg.v ================= *)

(* order facts *)
Lemma ord_refl_B : forall a : B, a ≤ a.
Proof. intros. apply (proj2 (@meet_consistent B O L LSet a a)). symmetry. apply meet_idempotent. Qed.
Lemma ord_trans_B : forall x y z : B, x ≤ y -> y ≤ z -> x ≤ z.
Proof. intros. exact (@transitive B O x y z H H0). Qed.

Lemma ord_meet_l : forall a b : B, a ⊓ b ≤ a.
Proof. intros. destruct (proj2 (@meet_is_glb B O L LSet a b (a ⊓ b)) (ord_refl_B _)) as [H1 H2]. exact H1. Qed.

Lemma ord_meet_r : forall a b : B, a ⊓ b ≤ b.
Proof. intros. destruct (proj2 (@meet_is_glb B O L LSet a b (a ⊓ b)) (ord_refl_B _)) as [H1 H2]. exact H2. Qed.

Lemma ord_join_l : forall a b : B, a ≤ a ⊔ b.
Proof. intros. destruct (proj2 (@join_is_lub B O L LSet a b (a ⊔ b)) (ord_refl_B _)) as [H1 H2]. exact H1. Qed.

Lemma ord_join_r : forall a b : B, b ≤ a ⊔ b.
Proof. intros. destruct (proj2 (@join_is_lub B O L LSet a b (a ⊔ b)) (ord_refl_B _)) as [H1 H2]. exact H2. Qed.

Lemma ord_top : forall a : B, a ≤ top.
Proof. intros. apply (proj2 (@join_consistent B O L LSet a top)). symmetry. apply join_top. Qed.

Lemma ord_bot : forall a : B, bot ≤ a.
Proof. intros. apply (proj2 (@meet_consistent B O L LSet bot a)). transitivity (a ⊓ bot).
- symmetry. apply meet_bot.
- apply meet_commutative. Qed.

(* base lifts *)
Lemma subqual_base_meet_l : forall E a b, wf_env E ->
  subqual E (qua_base (a ⊓ b)) (qua_base a).
Proof. intros. apply subqual_lift_elem; auto. apply ord_meet_l. Qed.

Lemma subqual_base_meet_r : forall E a b, wf_env E ->
  subqual E (qua_base (a ⊓ b)) (qua_base b).
Proof. intros. apply subqual_lift_elem; auto. apply ord_meet_r. Qed.

Lemma subqual_base_join_l : forall E a b, wf_env E ->
  subqual E (qua_base a) (qua_base (a ⊔ b)).
Proof. intros. apply subqual_lift_elem; auto. apply ord_join_l. Qed.

Lemma subqual_base_join_r : forall E a b, wf_env E ->
  subqual E (qua_base b) (qua_base (a ⊔ b)).
Proof. intros. apply subqual_lift_elem; auto. apply ord_join_r. Qed.

Lemma subqual_base_refl : forall E b, wf_env E -> subqual E (qua_base b) (qua_base b).
Proof. intros. apply subqual_lift_elem; auto; apply ord_refl_B. Qed.

(* reflexivity of subqual *)
Lemma subqual_meet_mono : forall E Q1 Q2 R1 R2,
  wf_env E -> wf_qua E Q1 -> wf_qua E Q2 ->
  subqual E Q1 R1 -> subqual E Q2 R2 ->
  subqual E (qua_meet Q1 Q2) (qua_meet R1 R2).
Proof.
  intros E Q1 Q2 R1 R2 Hwf HQ1 HQ2 Hs1 Hs2.
  apply subqual_meet_intro.
  - eapply subqual_meet_eliml; eauto.
  - eapply subqual_meet_elimr; eauto.
Qed.

Lemma subqual_join_mono : forall E Q1 Q2 R1 R2,
  wf_env E -> wf_qua E Q1 -> wf_qua E Q2 ->
  subqual E Q1 R1 -> subqual E Q2 R2 ->
  subqual E (qua_join Q1 Q2) (qua_join R1 R2).
Proof.
  intros E Q1 Q2 R1 R2 Hwf HQ1 HQ2 Hs1 Hs2.
  destruct (subqual_wf _ _ _ Hs1) as [_ [_ HR1]].
  destruct (subqual_wf _ _ _ Hs2) as [_ [_ HR2]].
  eapply subqual_join_elim.
  - eapply subqual_join_inl; eauto.
  - eapply subqual_join_inr; eauto.
Qed.

Lemma subqual_meet_comm : forall E Q R,
  wf_env E -> wf_qua E Q -> wf_qua E R ->
  subqual E (qua_meet Q R) (qua_meet R Q).
Proof.
  intros. apply subqual_meet_intro.
  - eapply subqual_meet_elimr; eauto. apply subqual_refl; auto.
  - eapply subqual_meet_eliml; eauto. apply subqual_refl; auto.
Qed.

Lemma subqual_negate_contra : forall E Q1 Q2,
  wf_env E -> wf_qua E Q1 -> wf_qua E Q2 ->
  subqual E Q1 Q2 -> subqual E (qua_negate Q2) (qua_negate Q1).
Proof.
  intros E Q1 Q2 Hwf HQ1 HQ2 Hs.
  pose proof (wf_qua_negate _ _ HQ1) as HnQ1.
  pose proof (wf_qua_negate _ _ HQ2) as HnQ2.
  (* A: Q1 ⊓ ¬Q2 <: ¬Q1 *)
  pose proof (subqual_meet_mono E Q1 (qua_negate Q2) Q2 (qua_negate Q2) Hwf HQ1 HnQ2 Hs (subqual_refl E (qua_negate Q2) Hwf HnQ2)) as HA1.
  pose proof (subqual_negate_elim E Q2 Hwf HQ2) as HA2.
  pose proof (subqual_trans _ _ _ _ HA1 HA2) as HA3.
  pose proof (subqual_bot E (qua_negate Q1) Hwf HnQ1) as HA4.
  pose proof (subqual_trans _ _ _ _ HA3 HA4) as HA.
  (* B: ¬Q2⊓¬Q1 <: ¬Q1 *)
  pose proof (subqual_meet_elimr E (qua_negate Q2) (qua_negate Q1) (qua_negate Q1) HnQ2 (subqual_refl E (qua_negate Q1) Hwf HnQ1)) as HB.
  pose proof (subqual_join_elim _ _ _ _ HA HB) as HAB.
  (* C: ¬Q2 <: Q1 ⊔ ¬Q1 *)
  pose proof (subqual_top E (qua_negate Q2) Hwf HnQ2) as HC1.
  pose proof (subqual_negate_intro E Q1 Hwf HQ1) as HC2.
  pose proof (subqual_trans _ _ _ _ HC1 HC2) as HC.
  (* D: ¬Q2 <: ¬Q2 ⊓ (Q1⊔¬Q1) *)
  pose proof (subqual_meet_intro _ _ _ _ (subqual_refl E (qua_negate Q2) Hwf HnQ2) HC) as HD.
  (* E: dist *)
  pose proof (subqual_dist E (qua_negate Q2) Q1 (qua_negate Q1) Hwf HnQ2 HQ1 HnQ1) as HE.
  (* F: (¬Q2⊓Q1) <: (Q1⊓¬Q2) *)
  pose proof (subqual_meet_comm E (qua_negate Q2) Q1 Hwf HnQ2 HQ1) as HF.
  (* G: join mono *)
  pose proof (subqual_join_mono E (qua_negate Q2) (qua_negate Q1) (qua_negate Q2) (qua_negate Q1) Hwf HnQ2 HnQ1 (subqual_refl E (qua_negate Q2) Hwf HnQ2) (subqual_refl E (qua_negate Q1) Hwf HnQ1)) as HG.
  (* H: join of (¬Q2⊓Q1) and (¬Q2⊓¬Q1) <: join of (Q1⊓¬Q2) and (¬Q2⊓¬Q1) *)
  destruct (subqual_wf _ _ _ HF) as [_ [_ HFw]].
  pose proof (wf_qua_meet _ _ _ HnQ2 HQ1) as Hwf1.
  pose proof (wf_qua_meet _ _ _ HnQ2 HnQ1) as Hwf2.
  pose proof (subqual_join_mono E (qua_meet (qua_negate Q2) Q1) (qua_meet (qua_negate Q2) (qua_negate Q1)) (qua_meet Q1 (qua_negate Q2)) (qua_meet (qua_negate Q2) (qua_negate Q1)) Hwf Hwf1 Hwf2 HF (subqual_refl E (qua_meet (qua_negate Q2) (qua_negate Q1)) Hwf Hwf2)) as HH.
  pose proof (subqual_trans _ _ _ _ HD HE) as HDE.
  pose proof (subqual_trans _ _ _ _ HDE HH) as HDEH.
  eapply subqual_trans; [exact HDEH | exact HAB].
Qed.

(* base meet/join/negate equivalences *)
Lemma subqual_meet_base_fwd : forall E a b, wf_env E ->
  subqual E (qua_meet (qua_base a) (qua_base b)) (qua_base (a ⊓ b)).
Proof.
  intros E a b Hwf.
  eapply subqual_eval_elim with (Q':=qua_meet (qua_base a) (qua_base b))
    (b:=a ⊓ b) (R:=qua_base (a ⊓ b)).
  - apply subqual_refl; [exact Hwf | repeat constructor].
  - simpl. reflexivity.
  - apply subqual_base_refl. exact Hwf.
Qed.

Lemma subqual_base_meet_fwd : forall E a b, wf_env E ->
  subqual E (qua_base (a ⊓ b)) (qua_meet (qua_base a) (qua_base b)).
Proof.
  intros E a b Hwf. apply subqual_meet_intro.
  - eapply subqual_trans.
    + apply subqual_base_meet_l. exact Hwf.
    + apply subqual_base_refl. exact Hwf.
  - eapply subqual_trans.
    + apply subqual_base_meet_r. exact Hwf.
    + apply subqual_base_refl. exact Hwf.
Qed.

Lemma subqual_join_base_fwd : forall E a b, wf_env E ->
  subqual E (qua_join (qua_base a) (qua_base b)) (qua_base (a ⊔ b)).
Proof.
  intros E a b Hwf.
  eapply subqual_eval_elim with (Q':=qua_join (qua_base a) (qua_base b))
    (b:=a ⊔ b) (R:=qua_base (a ⊔ b)).
  - apply subqual_refl; [exact Hwf | repeat constructor].
  - simpl. reflexivity.
  - apply subqual_base_refl. exact Hwf.
Qed.

Lemma subqual_base_join_fwd : forall E a b, wf_env E ->
  subqual E (qua_base (a ⊔ b)) (qua_join (qua_base a) (qua_base b)).
Proof.
  intros E a b Hwf.
  eapply subqual_eval_intro with (Q':=qua_join (qua_base a) (qua_base b))
    (Q:=qua_base (a ⊔ b)) (R:=qua_join (qua_base a) (qua_base b)) (b:=a ⊔ b).
  - apply subqual_refl; [exact Hwf | repeat constructor].
  - simpl. reflexivity.
  - apply subqual_base_refl. exact Hwf.
Qed.

Lemma subqual_neg_base_fwd : forall E b, wf_env E ->
  subqual E (qua_negate (qua_base b)) (qua_base (negate b)).
Proof.
  intros E b Hwf.
  eapply subqual_eval_elim with (Q':=qua_negate (qua_base b))
    (b:=negate b) (R:=qua_base (negate b)).
  - apply subqual_refl; [exact Hwf | repeat constructor].
  - simpl. reflexivity.
  - apply subqual_base_refl. exact Hwf.
Qed.

Lemma subqual_base_neg_fwd : forall E b, wf_env E ->
  subqual E (qua_base (negate b)) (qua_negate (qua_base b)).
Proof.
  intros E b Hwf.
  eapply subqual_eval_intro with (Q':=qua_negate (qua_base b))
    (Q:=qua_base (negate b)) (R:=qua_negate (qua_base b)) (b:=negate b).
  - apply subqual_refl; [exact Hwf | repeat constructor].
  - simpl. reflexivity.
  - apply subqual_base_refl. exact Hwf.
Qed.

(* concretize inversion lemmas *)
Lemma concretize_base_inv : forall b0 b, concretize (qua_base b0) = Some b -> b = b0.
Proof. intros. simpl in H. inversion H. reflexivity. Qed.

Lemma concretize_meet_inv : forall Q1 Q2 b,
  concretize (qua_meet Q1 Q2) = Some b ->
  exists b1 b2, concretize Q1 = Some b1 /\ concretize Q2 = Some b2 /\ b = b1 ⊓ b2.
Proof.
  intros Q1 Q2 b H. cbn [concretize] in H.
  destruct (concretize Q1) as [b1|] eqn:E1; [|discriminate H].
  destruct (concretize Q2) as [b2|] eqn:E2; [|discriminate H].
  inversion H. subst. eauto.
Qed.

Lemma concretize_join_inv : forall Q1 Q2 b,
  concretize (qua_join Q1 Q2) = Some b ->
  exists b1 b2, concretize Q1 = Some b1 /\ concretize Q2 = Some b2 /\ b = b1 ⊔ b2.
Proof.
  intros Q1 Q2 b H. cbn [concretize] in H.
  destruct (concretize Q1) as [b1|] eqn:E1; [|discriminate H].
  destruct (concretize Q2) as [b2|] eqn:E2; [|discriminate H].
  inversion H. subst. eauto.
Qed.

Lemma concretize_negate_inv : forall Q1 b,
  concretize (qua_negate Q1) = Some b ->
  exists b1, concretize Q1 = Some b1 /\ b = negate b1.
Proof.
  intros Q1 b H. cbn [concretize] in H.
  destruct (concretize Q1) as [b1|] eqn:E1; [|discriminate H].
  inversion H. subst. eauto.
Qed.

(* mutual forward/backward concretization *)
Fixpoint concretize_subqual_mut (Q:qua) {struct Q} :
  forall E, wf_env E -> wf_qua E Q -> forall b, concretize Q = Some b ->
     subqual E Q (qua_base b) /\ subqual E (qua_base b) Q.
Proof.
  destruct Q as [b0|n|X|Q1 Q2|Q1 Q2|Q1]; intros E Hwf HQ b Hc.
  - apply concretize_base_inv in Hc. subst b.
    split; apply subqual_base_refl; exact Hwf.
  - cbn [concretize] in Hc. discriminate Hc.
  - cbn [concretize] in Hc. discriminate Hc.
  - inversion HQ as [| R0 E0 X0 Hb | E0 Q1' Q2' HQ1 HQ2 | E0 Q1' Q2' HQ1 HQ2 | E0 Q1' HQ1]; subst.
    destruct (concretize_meet_inv Q1 Q2 b Hc) as [b1 [b2 [E1 [E2 Hb]]]]. subst b.
    destruct (concretize_subqual_mut Q1 E Hwf HQ1 b1 E1) as [Hf1 Hb1].
    destruct (concretize_subqual_mut Q2 E Hwf HQ2 b2 E2) as [Hf2 Hb2].
    split.
    + eapply subqual_eval_elim with (Q':=qua_meet (qua_base b1) (qua_base b2))
        (b:=b1 ⊓ b2) (R:=qua_base (b1 ⊓ b2)).
      * eapply subqual_meet_mono.
        -- exact Hwf.
        -- exact HQ1.
        -- exact HQ2.
        -- exact Hf1.
        -- exact Hf2.
      * cbn [concretize]; reflexivity.
      * apply subqual_base_refl. exact Hwf.
    + apply subqual_meet_intro.
      * eapply subqual_trans.
        -- apply subqual_base_meet_l. exact Hwf.
        -- exact Hb1.
      * eapply subqual_trans.
        -- apply subqual_base_meet_r. exact Hwf.
        -- exact Hb2.
  - inversion HQ as [| R0 E0 X0 Hb | E0 Q1' Q2' HQ1 HQ2 | E0 Q1' Q2' HQ1 HQ2 | E0 Q1' HQ1]; subst.
    destruct (concretize_join_inv Q1 Q2 b Hc) as [b1 [b2 [E1 [E2 Hb]]]]. subst b.
    destruct (concretize_subqual_mut Q1 E Hwf HQ1 b1 E1) as [Hf1 Hb1].
    destruct (concretize_subqual_mut Q2 E Hwf HQ2 b2 E2) as [Hf2 Hb2].
    split.
    + eapply subqual_eval_elim with (Q':=qua_join (qua_base b1) (qua_base b2))
        (b:=b1 ⊔ b2) (R:=qua_base (b1 ⊔ b2)).
      * eapply subqual_join_mono.
        -- exact Hwf.
        -- exact HQ1.
        -- exact HQ2.
        -- exact Hf1.
        -- exact Hf2.
      * cbn [concretize]; reflexivity.
      * apply subqual_base_refl. exact Hwf.
    + eapply subqual_eval_intro with (Q':=qua_join (qua_base b1) (qua_base b2))
        (Q:=qua_base (b1 ⊔ b2)) (R:=qua_join Q1 Q2) (b:=b1 ⊔ b2).
      * eapply subqual_join_mono.
        -- exact Hwf.
        -- constructor.
        -- constructor.
        -- exact Hb1.
        -- exact Hb2.
      * cbn [concretize]; reflexivity.
      * apply subqual_base_refl. exact Hwf.
  - inversion HQ as [| R0 E0 X0 Hb | E0 Q1' Q2' HQ1 HQ2 | E0 Q1' Q2' HQ1 HQ2 | E0 Q1' HQ1]; subst.
    destruct (concretize_negate_inv Q1 b Hc) as [b1 [E1 Hb]]. subst b.
    destruct (concretize_subqual_mut Q1 E Hwf HQ1 b1 E1) as [Hf1 Hb1].
    split.
    + eapply subqual_trans.
      * eapply subqual_negate_contra.
        -- exact Hwf.
        -- constructor.
        -- exact HQ1.
        -- exact Hb1.
      * apply subqual_neg_base_fwd. exact Hwf.
    + eapply subqual_trans.
      * apply subqual_base_neg_fwd. exact Hwf.
      * eapply subqual_negate_contra.
        -- exact Hwf.
        -- exact HQ1.
        -- constructor.
        -- exact Hf1.
Qed.

Lemma concretize_subqual : forall E Q b, wf_env E -> wf_qua E Q ->
  concretize Q = Some b -> subqual E Q (qua_base b).
Proof. intros. apply (proj1 (concretize_subqual_mut Q E H H0 b H1)). Qed.

Lemma concretize_subqual_bwd : forall E Q b, wf_env E -> wf_qua E Q ->
  concretize Q = Some b -> subqual E (qua_base b) Q.
Proof. intros. apply (proj2 (concretize_subqual_mut Q E H H0 b H1)). Qed.


Lemma wf_qua_nobind_concrete : forall E Q, wf_qua E Q ->
  (forall X R, binds X (bind_qua R) E -> False) -> exists b, concretize Q = Some b.
Proof.
  intros E Q HQ. induction HQ; intros Hnb.
  - exists b. reflexivity.
  - exfalso. eapply Hnb; eauto.
  - destruct (IHHQ1 Hnb) as [b1 H1].
    destruct (IHHQ2 Hnb) as [b2 H2].
    exists (b1 ⊓ b2). simpl. rewrite H1. rewrite H2. reflexivity.
  - destruct (IHHQ1 Hnb) as [b1 H1].
    destruct (IHHQ2 Hnb) as [b2 H2].
    exists (b1 ⊔ b2). simpl. rewrite H1. rewrite H2. reflexivity.
  - destruct (IHHQ Hnb) as [b1 H1].
    exists (negate b1). simpl. rewrite H1. reflexivity.
Qed.

Lemma wf_qua_empty_concrete : forall Q, wf_qua empty Q -> exists b, concretize Q = Some b.
Proof.
  intros. eapply wf_qua_nobind_concrete; [exact H |].
  intros X R Hb. exact (proj1 (binds_nil_iff _ X (bind_qua R)) Hb).
Qed.

(* removing a bind_sub binding from qualifier-variable lookups *)
Lemma wf_qua_fv_dom : forall E Q, wf_qua E Q -> forall Z, Z `in` fv_qq Q -> Z `in` dom E.
Proof.
  intros E Q H. induction H; intros Z HZ; simpl in *.
  - exfalso. exact (AtomSetImpl.empty_1 HZ).
  - apply AtomSetImpl.singleton_1 in HZ. subst Z.
    apply (binds_In _ X (bind_qua R)). exact H.
  - apply AtomSetImpl.union_1 in HZ. destruct HZ as [HZ|HZ]; auto.
  - apply AtomSetImpl.union_1 in HZ. destruct HZ as [HZ|HZ]; auto.
  - auto.
Qed.

Fixpoint den (V:atom -> B) (Q:qua) {struct Q} : B :=
  match Q with
  | qua_base b => b
  | qua_bvar _ => bot
  | qua_fvar X => V X
  | qua_meet Q1 Q2 => den V Q1 ⊓ den V Q2
  | qua_join Q1 Q2 => den V Q1 ⊔ den V Q2
  | qua_negate Q1 => negate (den V Q1)
  end.

Lemma den_ext : forall V1 V2 Q, (forall X, X `in` fv_qq Q -> V1 X = V2 X) ->
  den V1 Q = den V2 Q.
Proof.
  intros V1 V2 Q H. induction Q; simpl in *; try reflexivity.
  - apply H. apply AtomSetImpl.singleton_2. reflexivity.
  - f_equal.
    + apply IHQ1. intros Y HY. apply H. apply AtomSetImpl.union_2. exact HY.
    + apply IHQ2. intros Y HY. apply H. apply AtomSetImpl.union_3. exact HY.
  - f_equal.
    + apply IHQ1. intros Y HY. apply H. apply AtomSetImpl.union_2. exact HY.
    + apply IHQ2. intros Y HY. apply H. apply AtomSetImpl.union_3. exact HY.
  - f_equal. apply IHQ. intros Y HY. apply H. exact HY.
Qed.

Lemma concretize_den : forall Q b, concretize Q = Some b -> forall V, den V Q = b.
Proof.
  induction Q; intros bb H V; simpl in *.
  - inversion H. reflexivity.
  - discriminate H.
  - discriminate H.
  - cbn [concretize] in H.
    destruct (concretize Q1) as [b1|] eqn:E1; [|discriminate H].
    destruct (concretize Q2) as [b2|] eqn:E2; [|discriminate H].
    inversion H. subst. simpl.
    rewrite (IHQ1 b1 eq_refl V). rewrite (IHQ2 b2 eq_refl V). reflexivity.
  - cbn [concretize] in H.
    destruct (concretize Q1) as [b1|] eqn:E1; [|discriminate H].
    destruct (concretize Q2) as [b2|] eqn:E2; [|discriminate H].
    inversion H. subst. simpl.
    rewrite (IHQ1 b1 eq_refl V). rewrite (IHQ2 b2 eq_refl V). reflexivity.
  - cbn [concretize] in H.
    destruct (concretize Q) as [b1|] eqn:E1; [|discriminate H].
    inversion H. subst. simpl. rewrite (IHQ b1 eq_refl V). reflexivity.
Qed.

Definition respects (V:atom -> B) (E:env) : Prop :=
  forall X Q, binds X (bind_qua Q) E -> V X = den V Q.

Lemma den_subqual : forall E Q R, wf_env E -> subqual E Q R ->
  forall V, respects V E -> den V Q ≤ den V R.
Proof.
  intros E Q R Hwf_sub H. induction H; intros V HV; simpl in *.
  - apply ord_top.
  - apply ord_bot.
  - eapply ord_trans_B with (y:=den V Q').
    + eapply IHsubqual1; [exact Hwf_sub | exact HV].
    + rewrite (concretize_den Q' b H0 V). eapply IHsubqual2; [exact Hwf_sub | exact HV].
  - eapply ord_trans_B with (y:=den V Q').
    + rewrite (concretize_den Q' b H0 V). eapply IHsubqual2; [exact Hwf_sub | exact HV].
    + eapply IHsubqual1; [exact Hwf_sub | exact HV].
  - assumption.
  - apply ord_refl_B.
  - rewrite (HV X R H). apply IHsubqual; [exact Hwf_sub | exact HV].
  - eapply ord_trans_B with (y:=den V R1).
    + eapply IHsubqual; [exact Hwf_sub | exact HV].
    + apply ord_join_l.
  - eapply ord_trans_B with (y:=den V R2).
    + eapply IHsubqual; [exact Hwf_sub | exact HV].
    + apply ord_join_r.
  - apply (proj1 (@join_is_lub B O L LSet (den V R1) (den V R2) (den V Q))). split.
    + eapply IHsubqual1; [exact Hwf_sub | exact HV].
    + eapply IHsubqual2; [exact Hwf_sub | exact HV].
  - eapply ord_trans_B with (y:=den V R1).
    + apply ord_meet_l.
    + eapply IHsubqual; [exact Hwf_sub | exact HV].
  - eapply ord_trans_B with (y:=den V R2).
    + apply ord_meet_r.
    + eapply IHsubqual; [exact Hwf_sub | exact HV].
  - apply (proj1 (@meet_is_glb B O L LSet (den V R1) (den V R2) (den V Q))). split.
    + eapply IHsubqual1; [exact Hwf_sub | exact HV].
    + eapply IHsubqual2; [exact Hwf_sub | exact HV].
  - rewrite distrib. apply ord_refl_B.
  - eapply ord_trans_B with (y:=den V R).
    + eapply IHsubqual1; [exact Hwf_sub | exact HV].
    + eapply IHsubqual2; [exact Hwf_sub | exact HV].
  - rewrite negate_bot. apply ord_refl_B.
  - rewrite negate_top. apply ord_bot.
  - apply ord_refl_B.
Qed.

Lemma wf_env_valuation : forall E, wf_env E -> exists V, respects V E.
Proof.
  intros E Hwf. induction Hwf as [| E X T Hwf IH HT hf
    | E x T Hwf IH HT hf | E X Q Hwf IH HQ hf].
  - exists (fun _ => bot). intros Y Qb Hb.
    exfalso. exact (proj1 (binds_nil_iff _ Y Qb) Hb).
  - destruct IH as [V Hres]. exists V. intros Y Qb Hb.
    apply Hres. apply (binds_qua_remove_sub_mid nil X T E Y Qb). exact Hb.
  - destruct IH as [V Hres]. exists V. intros Y Qb Hb.
    apply Hres. apply (binds_qua_remove_typ_mid nil x T E Y Qb). exact Hb.
  - destruct IH as [V Hres].
    exists (fun Y => if eq_dec Y X then den V Q else V Y). intros Y Qb Hb.
    apply binds_cons_1 in Hb. destruct Hb as [[Heq HQeq]|HbE].
    + inversion Heq; subst Y. inversion HQeq; subst Qb.
      simpl. destruct (eq_dec X X) as [_|Hneq].
      * symmetry. apply den_ext. intros Z HZ.
        simpl. destruct (eq_dec Z X) as [HeqZ|HneqZ].
        -- exfalso. subst Z. apply hf. apply (wf_qua_fv_dom E Q HQ X HZ).
        -- reflexivity.
      * exfalso. exact (Hneq eq_refl).
    + assert (HY : Y <> X).
      { intro. subst Y. apply hf. apply (binds_In _ X (bind_qua Qb)). exact HbE. }
      pose proof (wf_env_binds_qua _ _ _ Hwf HbE) as HQb.
      simpl. destruct (eq_dec Y X) as [HeqY|HneqY].
      * exfalso. exact (HY HeqY).
      * rewrite (Hres Y Qb HbE).
        symmetry. apply den_ext. intros Z HZ.
        simpl. destruct (eq_dec Z X) as [HeqZ|HneqZ].
        -- exfalso. subst Z. apply hf. apply (wf_qua_fv_dom E Qb HQb X HZ).
        -- reflexivity.
Qed.

Lemma subqual_concretize_ord : forall E Q R,
  subqual E Q R -> forall a, concretize Q = Some a ->
    forall b, concretize R = Some b -> a ≤ b.
Proof.
  intros E Q R H a Ha b Hb.
  destruct (subqual_wf _ _ _ H) as [Hwf _].
  destruct (wf_env_valuation E Hwf) as [V HV].
  pose proof (den_subqual _ _ _ Hwf H V HV) as Hord.
  rewrite (concretize_den Q a Ha V) in Hord.
  rewrite (concretize_den R b Hb V) in Hord.
  exact Hord.
Qed.

Lemma subqual_base_ord : forall E a b, subqual E (qua_base a) (qua_base b) -> a ≤ b.
Proof.
  intros. eapply subqual_concretize_ord;
    [exact H | simpl; reflexivity | simpl; reflexivity].
Qed.

(* ================= ChunkMisc.v ================= *)

Fixpoint concretize_wf_qua (Q:qua) {struct Q} :
  forall (E:env) b, concretize Q = Some b -> wf_qua E Q.
Proof.
  destruct Q as [b0|n|X|Q1 Q2|Q1 Q2|Q1]; intros E b H; simpl in *.
  - apply wf_qua_base.
  - inversion H.
  - inversion H.
  - destruct (concretize Q1) as [b1|] eqn:E1; [|discriminate].
    destruct (concretize Q2) as [b2|] eqn:E2; [|discriminate].
    inversion H; subst. apply wf_qua_meet.
    + apply (concretize_wf_qua Q1 E b1 E1).
    + apply (concretize_wf_qua Q2 E b2 E2).
  - destruct (concretize Q1) as [b1|] eqn:E1; [|discriminate].
    destruct (concretize Q2) as [b2|] eqn:E2; [|discriminate].
    inversion H; subst. apply wf_qua_join.
    + apply (concretize_wf_qua Q1 E b1 E1).
    + apply (concretize_wf_qua Q2 E b2 E2).
  - destruct (concretize Q1) as [b1|] eqn:E1; [|discriminate].
    inversion H; subst. apply wf_qua_negate.
    apply (concretize_wf_qua Q1 E b1 E1).
Qed.

Lemma abstractize_concretize : forall t, concretize (abstractize t) = Some t.
Proof. intros. reflexivity. Qed.

(* ================= ChunkShape.v ================= *)

Lemma wf_qua_qual : forall E Q, wf_qua E Q -> qual Q.
Proof. intros E Q H. induction H; try constructor; auto. Qed.

Lemma wf_tq_type :
  (forall (E:env) (T:typ), wf_typ E T -> type T) /\
  (forall (E:env) (T:qtyp), wf_qtyp E T -> qtype T).
Proof.
  apply wf_tq_mut
    with (P := fun E T _ => type T)
         (P0 := fun E T _ => qtype T).
  - constructor.
  - constructor.
  - constructor.
  - intros E T1 T2 w1 IH1 w2 IH2. apply type_arrow; auto.
  - intros L E T1 T2 w1 IH1 w0 IH0. apply type_all with (L:=L).
    + apply IH1.
    + intros X Hx. apply (IH0 X Hx).
  - intros L E Q T wq w0 IH0. apply type_qall with (L:=L).
    + eapply wf_qua_qual; eauto.
    + intros X Hx. apply (IH0 X Hx).
  - intros E T1 T2 w1 IH1 w2 IH2. apply type_sum; auto.
  - intros E T1 T2 w1 IH1 w2 IH2. apply type_pair; auto.
  - intros E Q T wq wT IHT. apply qtype_qtyp.
    + eapply wf_qua_qual; eauto.
    + apply IHT.
Qed.

Lemma wf_typ_type : forall E T, wf_typ E T -> type T.
Proof. intros. eapply (proj1 wf_tq_type); eauto. Qed.
Lemma wf_qtyp_qtype : forall E T, wf_qtyp E T -> qtype T.
Proof. intros. eapply (proj2 wf_tq_type); eauto. Qed.

Lemma typing_expr : forall E Q e T, typing E Q e T -> expr e.
Proof.
  intros E Q e T H.
  induction H as [E P0 i Hwfi HP
    | E x T0 Hwfv Hb
    | L0 E P0 V e1 T1 Hp IHp
    | Qa T1 E e1 e2 T2 H1 IH1 H2 IH2
    | L0 E P0 V e1 T1 Hp IHp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P0 Qb e1 T1 HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e Ta H1 IH1 Hs
    | E Qa R e Ta H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P0 T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P0 e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P0 e H1 IH1
    | Qa T1 T2 P0 e H1 IH1
    | E R Qa T0 P0 e H1 IH1 Hs
    | E R Qa T0 P0 e H1 IH1 Hs
    | E R Qa T0 P0 e H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3].
  - (* int *) eapply expr_int. eapply wf_qua_qual. exact HP.
  - (* var *) apply expr_var.
  - (* abs *)
    assert (HqP : qual P0).
    { assert (Hw : wf_qua E P0).
      { pick fresh y for L0.
        apply (wf_qua_remove_typ_mid P0 (@nil (atom*binding)) y V E).
        eapply typing_wf_qua. apply (Hp y Fr). }
      apply wf_qua_qual in Hw. exact Hw. }
    assert (HtV : qtype V).
    { pick fresh y for L0.
      pose proof (typing_wf_env _ _ _ _ (Hp y Fr)) as Hw.
      destruct (wf_env_typ_inv _ _ _ Hw) as [_ [HV _]].
      exact (wf_qtyp_qtype E V HV). }
    eapply expr_abs with (L:=L0); [exact HqP | exact HtV | exact HqP | intros y Hy; apply (IHp y Hy)].
  - (* app *) eapply expr_app; eauto.
  - (* tabs *)
    assert (HqP : qual P0).
    { assert (Hw : wf_qua E P0).
      { pick fresh y for L0.
        apply (wf_qua_remove_sub_mid P0 (@nil (atom*binding)) y V E).
        eapply typing_wf_qua. apply (Hp y Fr). }
      apply wf_qua_qual in Hw. exact Hw. }
    assert (HtV : type V).
    { pick fresh y for L0.
      pose proof (typing_wf_env _ _ _ _ (Hp y Fr)) as Hw.
      destruct (wf_env_sub_inv _ _ _ Hw) as [_ [HV _]].
      exact (wf_typ_type E V HV). }
    eapply expr_tabs with (L:=L0); [exact HqP | exact HtV | intros y Hy; apply (IHp y Hy)].
  - (* tapp *) eapply expr_tapp; [exact IH1 |].
    destruct (sub_wf _ _ _ Hs) as [_ [HV _]]. exact (wf_typ_type E Ta HV).
  - (* qabs *)
    assert (HqQ : qual Qb).
    { pick fresh y for L0.
      pose proof (typing_wf_env _ _ _ _ (Hp y Fr)) as Hw.
      destruct (wf_env_qua_inv _ _ _ Hw) as [_ [HQ _]].
      apply wf_qua_qual in HQ. exact HQ. }
    eapply expr_qabs with (L:=L0); [eapply wf_qua_qual; exact HP | exact HqQ | intros y Hy; apply (IHp y Hy)].
  - (* qapp *) eapply expr_qapp; [exact IH1 |].
    destruct (subqual_wf _ _ _ Hs) as [_ [HQ _]]. exact (wf_qua_qual E Qa HQ).
  - (* sub *) exact IH1.
  - (* subqual *) exact IH1.
  - (* let *) eapply expr_let; [exact IH1 | intros y Hy; apply (IH2 y Hy)].
  - (* inl *) eapply expr_inl; [eapply wf_qua_qual; exact HP | exact IH1].
  - (* inr *) eapply expr_inr; [eapply wf_qua_qual; exact HP | exact IH1].
  - (* case *) eapply expr_case; [exact IH1 | intros y Hy; apply (IH2 y Hy) | intros y Hy; apply (IH3 y Hy)].
  - (* pair *) eapply expr_pair; [eapply wf_qua_qual; exact HP | exact IH1 | exact IH2].
  - (* first *) eapply expr_first; exact IHIH1.
  - (* second *) eapply expr_second; exact IHIH1.
  - (* upqual *) eapply expr_upqual; [|exact IH1].
    destruct (subqual_wf _ _ _ Hs) as [_ [_ HP]]. exact (wf_qua_qual E P0 HP).
  - (* check *) eapply expr_check; [|exact IH1].
    destruct (subqual_wf _ _ _ Hs) as [_ [_ HP]]. exact (wf_qua_qual E P0 HP).
  - (* without *) eapply expr_without; [|exact IH1].
    destruct (subqual_wf _ _ _ Hs) as [_ [_ HP]].
    pose proof (wf_qua_qual E (qua_negate P0) HP) as Hq. inversion Hq. assumption.
  - (* do *) apply expr_do.
  - (* if0 *) eapply expr_if0; eauto.
Qed.

Lemma typing_value_effect : forall E Q e T, typing E Q e T -> value e ->
  forall R, wf_env E -> wf_qua E R -> typing E R e T.
Proof.
  intros E Q e T H. induction H as [E P0 i Hwfi HP
    | E x T0 Hwfv Hb
    | L0 E P0 V e1 T1 Hp IHp
    | Qa T1 E e1 e2 T2 H1 IH1 H2 IH2
    | L0 E P0 V e1 T1 Hp IHp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P0 Qb e1 T1 HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e Ta H1 IH1 Hs
    | E Qa R0 e Ta H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P0 T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P0 e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P0 e H1 IH1
    | Qa T1 T2 P0 e H1 IH1
    | E R0 Qa T0 P0 e H1 IH1 Hs
    | E R0 Qa T0 P0 e H1 IH1 Hs
    | E R0 Qa T0 P0 e H1 IH1 Hs
    | E b Hwfb
    | E R0 Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3];
    intros Vv R HwE HwR.
  - (* int *) apply typing_subqual with (Q:=qua_base bot).
    + apply typing_int; auto.
    + apply subqual_bot; auto.
  - (* var *) exfalso; inversion Vv.
  - (* abs *) apply typing_subqual with (Q:=qua_base bot).
    + eapply typing_abs with (L:=L0). intros y Hy. apply (Hp y Hy).
    + apply subqual_bot; auto.
  - (* app *) exfalso; inversion Vv.
  - (* tabs *) apply typing_subqual with (Q:=qua_base bot).
    + eapply typing_tabs with (L:=L0). intros y Hy. apply (Hp y Hy).
    + apply subqual_bot; auto.
  - (* tapp *) exfalso; inversion Vv.
  - (* qabs *) apply typing_subqual with (Q:=qua_base bot).
    + eapply typing_qabs with (L:=L0); [exact HP | intros y Hy; apply (Hp y Hy)].
    + apply subqual_bot; auto.
  - (* qapp *) exfalso; inversion Vv.
  - (* sub *) apply typing_sub with (S:=S). apply (IH1 Vv R HwE HwR). exact Hs.
  - (* subqual *) exact (IH1 Vv R HwE HwR).
  - (* let *) exfalso; inversion Vv.
  - (* inl *) inversion Vv; subst.
    match goal with Hv : value e1 |- _ =>
      eapply typing_inl; [exact HP | apply (IH1 Hv R HwE HwR) | exact HT2] end.
  - (* inr *) inversion Vv; subst.
    match goal with Hv : value e1 |- _ =>
      eapply typing_inr; [exact HP | apply (IH1 Hv R HwE HwR) | exact HT1] end.
  - (* case *) exfalso; inversion Vv.
  - (* pair *) inversion Vv; subst.
    match goal with Hv1 : value e1, Hv2 : value e2 |- _ =>
      eapply typing_pair; [exact HP | apply (IH1 Hv1 R HwE HwR) | apply (IH2 Hv2 R HwE HwR)] end.
  - (* first *) exfalso; inversion Vv.
  - (* second *) exfalso; inversion Vv.
  - (* upqual *) exfalso; inversion Vv.
  - (* check *) exfalso; inversion Vv.
  - (* without *) exfalso; inversion Vv.
  - (* do *) exfalso; inversion Vv.
  - (* if0 *) exfalso; inversion Vv.
Qed.

Lemma wf_qua_lc : forall E Q, wf_qua E Q -> lc_qq Q 0.
Proof.
  intros E Q H. induction H; simpl; try exact I.
  - split; assumption.
  - split; assumption.
  - assumption.
Qed.

Lemma wf_qua_closed_qq : forall E Q, wf_qua E Q -> closed_qq Q.
Proof.
  intros E Q H K R. apply (open_qq_lc Q 0 (wf_qua_lc E Q H) K R (Nat.le_0_l K)).
Qed.

Lemma wf_typ_closed_tt : forall E T, wf_typ E T -> closed_tt T.
Proof.
  intros E T H. apply type_closed_tt. exact (wf_typ_type E T H).
Qed.

Lemma wf_qtyp_closed_tqt : forall E T, wf_qtyp E T -> closed_tt (match T with qtyp_qtyp _ T' => T' end).
Proof.
  intros E T H. destruct T as [Q T']. inversion H; subst.
  match goal with Hw : wf_typ E T' |- _ => exact (wf_typ_closed_tt E T' Hw) end.
Qed.

(* ================= ChunkCtx.v ================= *)

Lemma typing_ctx_wf_env : forall E Q c T U, typing_ctx E Q c T U -> wf_env E.
Proof.
  intros E Q c T U H. induction H; auto.
Qed.

Lemma typing_ctx_wf_qua : forall E Q c T U, typing_ctx E Q c T U -> wf_env E /\ wf_qua E Q.
Proof.
  intros E Q c T U H. induction H; try (split; auto; fail).
  all: try (match goal with
            | IH : wf_env ?E /\ wf_qua ?E ?Q |- wf_env ?E /\ wf_qua ?E ?Q =>
                destruct IH as [He HQ]; split; auto
            end).
  all: try (match goal with
            | IH : wf_env ?E /\ wf_qua ?E ?Q |- wf_env ?E /\ wf_qua ?E (abstractize ?t) =>
                destruct IH as [He HQ]; split; auto; constructor
            end).
  all: try (match goal with
            | IH : wf_env ?E /\ wf_qua ?E ?Q, Hs : subqual ?E ?R ?Q |- wf_env ?E /\ wf_qua ?E ?R =>
                destruct IH as [He HQ]; split; auto;
                destruct (subqual_wf _ _ _ Hs) as [_ [_ HR]]; exact HR
            end).
  all: try (match goal with
            | IH : wf_env ?E /\ wf_qua ?E ?Q |- wf_env ?E /\ wf_qua ?E (qua_meet (abstractize (negate ?t)) ?Q) =>
                destruct IH as [He HQ]; split; auto; constructor; [constructor|assumption]
            end).
  all: try (match goal with
            | Hs : subqual ?E ?R ?Q |- wf_env ?E /\ wf_qua ?E ?R =>
                destruct (subqual_wf _ _ _ Hs) as [He [HR _]]; split; auto
            end).
  all: try (match goal with |- ?G => idtac "FAILED:" G end).
Qed.

(* ================= ChunkSubEe.v ================= *)

Fixpoint subst_ee_open_ee_rec (e:exp) {struct e} :
  forall K f X v, closed_ee v ->
    subst_ee X v (open_ee_rec K f e) =
    open_ee_rec K (subst_ee X v f) (subst_ee X v e).
Proof.
  destruct e as [P i|i|a|P V e1|e1 e2|P V e1|e1 V|P Q e1|e1 Q|e1 e2|P e1|P e1|e1 e2 e3|P e1 e2|e1|e1|P e1|P l|e1|e1 e2|P e1|P e1|P e1|b|e1 e2 e3];
    intros K f X v Hc; simpl.
  - reflexivity.
  - destruct (eq_dec K i) as [Heq|Hneq]; simpl; reflexivity.
  - destruct (eq_dec a X) as [Heq|Hneq]; simpl.
    + rewrite Hc. reflexivity.
    + reflexivity.
  - f_equal. apply (subst_ee_open_ee_rec _ (S K) f X v Hc).
  - f_equal; [apply (subst_ee_open_ee_rec _ K f X v Hc)
            |apply (subst_ee_open_ee_rec _ K f X v Hc)].
  - f_equal. apply (subst_ee_open_ee_rec _ (S K) f X v Hc).
  - f_equal. apply (subst_ee_open_ee_rec _ K f X v Hc).
  - f_equal. apply (subst_ee_open_ee_rec _ (S K) f X v Hc).
  - f_equal. apply (subst_ee_open_ee_rec _ K f X v Hc).
  - f_equal; [apply (subst_ee_open_ee_rec _ K f X v Hc)
            |apply (subst_ee_open_ee_rec _ (S K) f X v Hc)].
  - f_equal. apply (subst_ee_open_ee_rec _ K f X v Hc).
  - f_equal. apply (subst_ee_open_ee_rec _ K f X v Hc).
  - f_equal; [apply (subst_ee_open_ee_rec _ K f X v Hc)
            |apply (subst_ee_open_ee_rec _ (S K) f X v Hc)
            |apply (subst_ee_open_ee_rec _ (S K) f X v Hc)].
  - f_equal; [apply (subst_ee_open_ee_rec _ K f X v Hc)
            |apply (subst_ee_open_ee_rec _ K f X v Hc)].
  - f_equal. apply (subst_ee_open_ee_rec _ K f X v Hc).
  - f_equal. apply (subst_ee_open_ee_rec _ K f X v Hc).
  - f_equal. apply (subst_ee_open_ee_rec _ K f X v Hc).
  - reflexivity.
  - f_equal. apply (subst_ee_open_ee_rec _ K f X v Hc).
  - f_equal; [apply (subst_ee_open_ee_rec _ K f X v Hc)
            |apply (subst_ee_open_ee_rec _ K f X v Hc)].
  - f_equal. apply (subst_ee_open_ee_rec _ K f X v Hc).
  - f_equal. apply (subst_ee_open_ee_rec _ K f X v Hc).
  - f_equal. apply (subst_ee_open_ee_rec _ K f X v Hc).
  - reflexivity.
  - f_equal; [apply (subst_ee_open_ee_rec _ K f X v Hc)
            |apply (subst_ee_open_ee_rec _ K f X v Hc)
            |apply (subst_ee_open_ee_rec _ K f X v Hc)].
Qed.

Lemma subst_ee_open_ee_atom : forall (e:exp) X v Y,
  closed_ee v -> Y <> X ->
  subst_ee X v (open_ee e Y) = open_ee (subst_ee X v e) Y.
Proof.
  intros. unfold open_ee.
  rewrite subst_ee_open_ee_rec with (f:=exp_fvar Y) by exact H.
  simpl. destruct (eq_dec Y X) as [Heq|Hneq].
  - exfalso; exact (H0 Heq).
  - reflexivity.
Qed.

Lemma subst_ee_open_ee_self : forall (e:exp) X v,
  closed_ee v ->
  subst_ee X v (open_ee e X) = open_ee (subst_ee X v e) v.
Proof.
  intros. unfold open_ee.
  rewrite subst_ee_open_ee_rec with (f:=exp_fvar X) by exact H.
  simpl. destruct (eq_dec X X) as [Heq|Hneq]; [reflexivity|exfalso; apply Hneq; reflexivity].
Qed.



Fixpoint subst_ee_open_te_rec (e:exp) {struct e} :
  forall K U X v, closed_te v ->
    subst_ee X v (open_te_rec K U e) = open_te_rec K U (subst_ee X v e).
Proof.
  destruct e as [P i|i|a|P V e1|e1 e2|P V e1|e1 V|P Q e1|e1 Q|e1 e2|P e1|P e1|e1 e2 e3|P e1 e2|e1|e1|P e1|P l|e1|e1 e2|P e1|P e1|P e1|b|e1 e2 e3];
    intros K U X v Hct; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (eq_dec a X) as [Heq|Hneq]; simpl.
    + rewrite Hct. reflexivity.
    + reflexivity.
  - f_equal. apply (subst_ee_open_te_rec _ (S K) U X v Hct).
  - f_equal; [apply (subst_ee_open_te_rec _ K U X v Hct)
            |apply (subst_ee_open_te_rec _ K U X v Hct)].
  - f_equal. apply (subst_ee_open_te_rec _ (S K) U X v Hct).
  - f_equal. apply (subst_ee_open_te_rec _ K U X v Hct).
  - f_equal. apply (subst_ee_open_te_rec _ (S K) U X v Hct).
  - f_equal. apply (subst_ee_open_te_rec _ K U X v Hct).
  - f_equal; [apply (subst_ee_open_te_rec _ K U X v Hct)
            |apply (subst_ee_open_te_rec _ (S K) U X v Hct)].
  - f_equal. apply (subst_ee_open_te_rec _ K U X v Hct).
  - f_equal. apply (subst_ee_open_te_rec _ K U X v Hct).
  - f_equal; [apply (subst_ee_open_te_rec _ K U X v Hct)
            |apply (subst_ee_open_te_rec _ (S K) U X v Hct)
            |apply (subst_ee_open_te_rec _ (S K) U X v Hct)].
  - f_equal; [apply (subst_ee_open_te_rec _ K U X v Hct)
            |apply (subst_ee_open_te_rec _ K U X v Hct)].
  - f_equal. apply (subst_ee_open_te_rec _ K U X v Hct).
  - f_equal. apply (subst_ee_open_te_rec _ K U X v Hct).
  - f_equal. apply (subst_ee_open_te_rec _ K U X v Hct).
  - reflexivity.
  - f_equal. apply (subst_ee_open_te_rec _ K U X v Hct).
  - f_equal; [apply (subst_ee_open_te_rec _ K U X v Hct)
            |apply (subst_ee_open_te_rec _ K U X v Hct)].
  - f_equal. apply (subst_ee_open_te_rec _ K U X v Hct).
  - f_equal. apply (subst_ee_open_te_rec _ K U X v Hct).
  - f_equal. apply (subst_ee_open_te_rec _ K U X v Hct).
  - reflexivity.
  - f_equal; [apply (subst_ee_open_te_rec _ K U X v Hct)
            |apply (subst_ee_open_te_rec _ K U X v Hct)
            |apply (subst_ee_open_te_rec _ K U X v Hct)].
Qed.

Fixpoint subst_ee_open_qe_rec (e:exp) {struct e} :
  forall K R X v, closed_qe v ->
    subst_ee X v (open_qe_rec K R e) = open_qe_rec K R (subst_ee X v e).
Proof.
  destruct e as [P i|i|a|P V e1|e1 e2|P V e1|e1 V|P Q e1|e1 Q|e1 e2|P e1|P e1|e1 e2 e3|P e1 e2|e1|e1|P e1|P l|e1|e1 e2|P e1|P e1|P e1|b|e1 e2 e3];
    intros K R X v Hcq; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (eq_dec a X) as [Heq|Hneq]; simpl.
    + rewrite Hcq. reflexivity.
    + reflexivity.
  - f_equal. apply (subst_ee_open_qe_rec _ (S K) R X v Hcq).
  - f_equal; [apply (subst_ee_open_qe_rec _ K R X v Hcq)
            |apply (subst_ee_open_qe_rec _ K R X v Hcq)].
  - f_equal. apply (subst_ee_open_qe_rec _ (S K) R X v Hcq).
  - f_equal. apply (subst_ee_open_qe_rec _ K R X v Hcq).
  - f_equal. apply (subst_ee_open_qe_rec _ (S K) R X v Hcq).
  - f_equal. apply (subst_ee_open_qe_rec _ K R X v Hcq).
  - f_equal; [apply (subst_ee_open_qe_rec _ K R X v Hcq)
            |apply (subst_ee_open_qe_rec _ (S K) R X v Hcq)].
  - f_equal. apply (subst_ee_open_qe_rec _ K R X v Hcq).
  - f_equal. apply (subst_ee_open_qe_rec _ K R X v Hcq).
  - f_equal; [apply (subst_ee_open_qe_rec _ K R X v Hcq)
            |apply (subst_ee_open_qe_rec _ (S K) R X v Hcq)
            |apply (subst_ee_open_qe_rec _ (S K) R X v Hcq)].
  - f_equal; [apply (subst_ee_open_qe_rec _ K R X v Hcq)
            |apply (subst_ee_open_qe_rec _ K R X v Hcq)].
  - f_equal. apply (subst_ee_open_qe_rec _ K R X v Hcq).
  - f_equal. apply (subst_ee_open_qe_rec _ K R X v Hcq).
  - f_equal. apply (subst_ee_open_qe_rec _ K R X v Hcq).
  - reflexivity.
  - f_equal. apply (subst_ee_open_qe_rec _ K R X v Hcq).
  - f_equal; [apply (subst_ee_open_qe_rec _ K R X v Hcq)
            |apply (subst_ee_open_qe_rec _ K R X v Hcq)].
  - f_equal. apply (subst_ee_open_qe_rec _ K R X v Hcq).
  - f_equal. apply (subst_ee_open_qe_rec _ K R X v Hcq).
  - f_equal. apply (subst_ee_open_qe_rec _ K R X v Hcq).
  - reflexivity.
  - f_equal; [apply (subst_ee_open_qe_rec _ K R X v Hcq)
            |apply (subst_ee_open_qe_rec _ K R X v Hcq)
            |apply (subst_ee_open_qe_rec _ K R X v Hcq)].
Qed.

Lemma subst_ee_open_te_atom : forall (e:exp) X v (Y:atom),
  closed_te v ->
  subst_ee X v (open_te e (typ_fvar Y)) = open_te (subst_ee X v e) (typ_fvar Y).
Proof.
  intros. unfold open_te.
  apply (subst_ee_open_te_rec e 0 (typ_fvar Y) X v H). 
Qed.

Lemma subst_ee_open_qe_atom : forall (e:exp) X v (Y:atom),
  closed_qe v ->
  subst_ee X v (open_qe e (qua_fvar Y)) = open_qe (subst_ee X v e) (qua_fvar Y).
Proof.
  intros. unfold open_qe.
  apply (subst_ee_open_qe_rec e 0 (qua_fvar Y) X v H).
Qed.

(* ================= ChunkTypingEe.v ================= *)

Lemma binds_remove_typ_mid_neq : forall (E1:env) x (T:qtyp) (E2:env) z b,
  z <> x -> binds z b (E1 ++ x ~ bind_typ T ++ E2) -> binds z b (E1 ++ E2).
Proof.
  intros E1 x T E2 z b Hne H. unfold binds in *.
  apply in_app_iff. apply in_app_iff in H. destruct H as [H|H].
  - left; auto.
  - simpl in H. destruct H as [Heq|H].
    + inversion Heq; subst. exfalso; apply Hne; reflexivity.
    + right; auto.
Qed.

Lemma binds_typ_head : forall (E1:env) x (T:qtyp) (E2:env),
  binds x (bind_typ T) (E1 ++ x ~ bind_typ T ++ E2).
Proof.
  intros. unfold binds. apply in_app_iff. right. simpl. left. reflexivity.
Qed.

Lemma notin_union3_l : forall (x:atom) A B C,
  x `notin` (A \u (B \u C)) -> x `notin` A.
Proof. intros. exact (notin_union_1 _ _ _ H). Qed.
Lemma notin_union3_m : forall (x:atom) A B C,
  x `notin` (A \u (B \u C)) -> x `notin` B.
Proof. intros. exact (notin_union_1 _ _ _ (notin_union_2 _ _ _ H)). Qed.
Lemma notin_union3_r : forall (x:atom) A B C,
  x `notin` (A \u (B \u C)) -> x `notin` C.
Proof. intros. exact (notin_union_2 _ _ _ (notin_union_2 _ _ _ H)). Qed.
Lemma notin_union3_r_neq : forall (x y:atom) A B,
  x `notin` (A \u (B \u singleton y)) -> x <> y.
Proof.
  intros x y A B H. intro Heq. subst.
  exact (notin_singleton_1 y y (notin_union3_r y A B (singleton y) H) eq_refl).
Qed.

Lemma typing_subst_ee_gen : forall (E:env) Q e T,
  typing E Q e T ->
  forall (E1:env) x (T1:qtyp) (E2:env) v,
    E = E1 ++ x ~ bind_typ T1 ++ E2 ->
    closed_ee v -> closed_te v -> closed_qe v ->
    wf_env (E1 ++ E2) ->
    typing (E1 ++ E2) (qua_base bot) v T1 ->
    typing (E1 ++ E2) Q (subst_ee x v e) T.
Proof.
  intros E Q e T H.
  induction H as [E P0 i Hwfi HP
    | E x0 Tb Hwfv Hb
    | L0 E P0 V e1 T1' Hp IHp
    | Qa T1x E e1 e2 T2 H1 IH1 H2 IH2
    | L0 E P0 V e1 T1' Hp IHp
    | Qa T1x E e1 Ta T2 H1 IH1 Hs
    | L0 E P0 Qb e1 T1' HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1x T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1x T2 P0 e1 E Qa HP H1 IH1 HT2
    | T1x T2 P0 e1 E Qa HP H1 IH1 HT1
    | L T1x T2 P0 T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1x T2 P0 e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1x T2 P0 e0 E H1 IH1
    | Qa T1x T2 P0 e0 E H1 IH1
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3];
    intros E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv; subst.
  - (* int *) apply typing_int; auto.
    exact (wf_qua_remove_typ_mid P0 E1 x T1 E2 HP).
  - (* var *) simpl. destruct (eq_dec x0 x) as [Heq|Hneq].
    + subst x0.
      assert (Hwsrc : wf_env (E1 ++ x ~ bind_typ T1 ++ E2)) by exact Hwfv.
      pose proof (binds_unique _ x (bind_typ Tb) (bind_typ T1) _ Hb
                    (binds_typ_head E1 x T1 E2) (wf_env_uniq _ Hwsrc)) as Heqb.
      injection Heqb as HTb. subst Tb.
      destruct (eq_dec x x) as [Heqx|Hneqx]; [|exfalso; apply Hneqx; reflexivity].
      exact Hv.
    + simpl. destruct (eq_dec x0 x) as [Heqx|Hneqx].
      * exfalso; apply Hneq; exact Heqx.
      * apply typing_var; auto.
        exact (binds_remove_typ_mid_neq E1 x T1 E2 x0 (bind_typ Tb) Hneq Hb).
  - (* abs *) eapply typing_abs with (L := L0 \u (dom (E1++E2) \u singleton x)).
    intros y Hy.
    pose proof (notin_union3_l y L0 (dom (E1++E2)) (singleton x) Hy) as HyL.
    pose proof (notin_union3_m y L0 (dom (E1++E2)) (singleton x) Hy) as HyD.
    pose proof (notin_union3_r_neq y x L0 (dom (E1++E2)) Hy) as Hyx.
    pose proof (Hp y HyL) as Hty.
    assert (HV : wf_qtyp (E1++E2) V).
    { pose proof (typing_wf_env _ _ _ _ Hty) as Hw.
      destruct (wf_env_typ_inv _ _ _ Hw) as [_ [HV0 _]].
      exact (wf_qtyp_remove_typ_mid E1 x T1 E2 V HV0). }
    assert (HwEy : wf_env (y ~ bind_typ V ++ (E1++E2))).
    { apply wf_env_typ; auto. }
    assert (Hvy : typing (y ~ bind_typ V ++ (E1++E2)) (qua_base bot) v T1).
    { eapply typing_extends; [exact Hv | apply extends_app_l | exact HwEy]. }
    pose proof (IHp y HyL (y ~ bind_typ V ++ E1) x T1 E2 v
                  ltac:(rewrite app_assoc; reflexivity) Hce Hct Hcq HwEy Hvy) as HI.
    rewrite app_assoc in HI.
    rewrite (subst_ee_open_ee_atom e1 x v y Hce Hyx) in HI.
    exact HI.
  - (* app *) eapply typing_app; [apply (IH1 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv)
                                 |apply (IH2 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv)].
  - (* tabs *) eapply typing_tabs with (L := L0 \u (dom (E1++E2) \u singleton x)).
    intros X HX.
    pose proof (notin_union3_l X L0 (dom (E1++E2)) (singleton x) HX) as HXL.
    pose proof (notin_union3_m X L0 (dom (E1++E2)) (singleton x) HX) as HXD.
    pose proof (Hp X HXL) as Hty.
    assert (HV : wf_typ (E1++E2) V).
    { pose proof (typing_wf_env _ _ _ _ Hty) as Hw.
      destruct (wf_env_sub_inv _ _ _ Hw) as [_ [HV0 _]].
      exact (wf_typ_remove_typ_mid E1 x T1 E2 V HV0). }
    assert (HwEX : wf_env (X ~ bind_sub V ++ (E1++E2))).
    { apply wf_env_sub; auto. }
    assert (HvX : typing (X ~ bind_sub V ++ (E1++E2)) (qua_base bot) v T1).
    { eapply typing_extends; [exact Hv | apply extends_app_l | exact HwEX]. }
    pose proof (IHp X HXL (X ~ bind_sub V ++ E1) x T1 E2 v
                  ltac:(rewrite app_assoc; reflexivity) Hce Hct Hcq HwEX HvX) as HI.
    rewrite app_assoc in HI.
    rewrite (subst_ee_open_te_atom e1 x v X Hct) in HI.
    exact HI.
  - (* tapp *) eapply typing_tapp.
    + apply (IH1 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv).
    + exact (sub_remove_typ_mid E1 x T1 E2 Ta T1x Hs).
  - (* qabs *) eapply typing_qabs with (L := L0 \u (dom (E1++E2) \u singleton x)).
    + exact (wf_qua_remove_typ_mid P0 E1 x T1 E2 HP).
    + intros X HX.
      pose proof (notin_union3_l X L0 (dom (E1++E2)) (singleton x) HX) as HXL.
      pose proof (notin_union3_m X L0 (dom (E1++E2)) (singleton x) HX) as HXD.
      pose proof (Hp X HXL) as Hty.
      assert (HQb : wf_qua (E1++E2) Qb).
      { pose proof (typing_wf_env _ _ _ _ Hty) as Hw.
        destruct (wf_env_qua_inv _ _ _ Hw) as [_ [HQ0 _]].
        exact (wf_qua_remove_typ_mid Qb E1 x T1 E2 HQ0). }
      assert (HwEX : wf_env (X ~ bind_qua Qb ++ (E1++E2))).
      { apply wf_env_qua; auto. }
      assert (HvX : typing (X ~ bind_qua Qb ++ (E1++E2)) (qua_base bot) v T1).
      { eapply typing_extends; [exact Hv | apply extends_app_l | exact HwEX]. }
      pose proof (IHp X HXL (X ~ bind_qua Qb ++ E1) x T1 E2 v
                    ltac:(rewrite app_assoc; reflexivity) Hce Hct Hcq HwEX HvX) as HI.
      rewrite app_assoc in HI.
      rewrite (subst_ee_open_qe_atom e1 x v X Hcq) in HI.
      exact HI.
  - (* qapp *) eapply typing_qapp.
    + apply (IH1 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv).
    + exact (subqual_remove_typ_mid E1 x T1 E2 Qa Qb Hs).
  - (* sub *) eapply typing_sub.
    + apply (IH1 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv).
    + exact (subqtype_remove_typ_mid E1 x T1 E2 S T0 Hs).
  - (* subqual *) eapply typing_subqual.
    + apply (IH1 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv).
    + exact (subqual_remove_typ_mid E1 x T1 E2 Qa R Hs).
  - (* let *) eapply typing_let with (L := L \u (dom (E1++E2) \u singleton x)).
    + apply (IH1 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv).
    + intros y Hy.
      pose proof (notin_union3_l y L (dom (E1++E2)) (singleton x) Hy) as HyL.
      pose proof (notin_union3_m y L (dom (E1++E2)) (singleton x) Hy) as HyD.
      pose proof (notin_union3_r_neq y x L (dom (E1++E2)) Hy) as Hyx.
      pose proof (H2 y HyL) as Hty.
      assert (HT1x : wf_qtyp (E1++E2) T1x).
      { pose proof (typing_wf_env _ _ _ _ Hty) as Hw.
        destruct (wf_env_typ_inv _ _ _ Hw) as [_ [HT _]].
        exact (wf_qtyp_remove_typ_mid E1 x T1 E2 T1x HT). }
      assert (HwEy : wf_env (y ~ bind_typ T1x ++ (E1++E2))).
      { apply wf_env_typ; auto. }
      assert (Hvy : typing (y ~ bind_typ T1x ++ (E1++E2)) (qua_base bot) v T1).
      { eapply typing_extends; [exact Hv | apply extends_app_l | exact HwEy]. }
      pose proof (IH2 y HyL (y ~ bind_typ T1x ++ E1) x T1 E2 v
                    ltac:(rewrite app_assoc; reflexivity) Hce Hct Hcq HwEy Hvy) as HI.
      rewrite app_assoc in HI.
      rewrite (subst_ee_open_ee_atom e2 x v y Hce Hyx) in HI.
      exact HI.
  - (* inl *) eapply typing_inl.
    + exact (wf_qua_remove_typ_mid P0 E1 x T1 E2 HP).
    + apply (IH1 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv).
    + exact (wf_qtyp_remove_typ_mid E1 x T1 E2 T2 HT2).
  - (* inr *) eapply typing_inr.
    + exact (wf_qua_remove_typ_mid P0 E1 x T1 E2 HP).
    + apply (IH1 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv).
    + exact (wf_qtyp_remove_typ_mid E1 x T1 E2 T1x HT1).
  - (* case *) eapply typing_case with (L := L \u (dom (E1++E2) \u singleton x)).
    + apply (IH1 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv).
    + intros y Hy.
      pose proof (notin_union3_l y L (dom (E1++E2)) (singleton x) Hy) as HyL.
      pose proof (notin_union3_m y L (dom (E1++E2)) (singleton x) Hy) as HyD.
      pose proof (notin_union3_r_neq y x L (dom (E1++E2)) Hy) as Hyx.
      pose proof (H2 y HyL) as Hty.
      assert (HT1x : wf_qtyp (E1++E2) T1x).
      { pose proof (typing_wf_env _ _ _ _ Hty) as Hw.
        destruct (wf_env_typ_inv _ _ _ Hw) as [_ [HT _]].
        exact (wf_qtyp_remove_typ_mid E1 x T1 E2 T1x HT). }
      assert (HwEy : wf_env (y ~ bind_typ T1x ++ (E1++E2))).
      { apply wf_env_typ; auto. }
      assert (Hvy : typing (y ~ bind_typ T1x ++ (E1++E2)) (qua_base bot) v T1).
      { eapply typing_extends; [exact Hv | apply extends_app_l | exact HwEy]. }
      pose proof (IH2 y HyL (y ~ bind_typ T1x ++ E1) x T1 E2 v
                    ltac:(rewrite app_assoc; reflexivity) Hce Hct Hcq HwEy Hvy) as HI.
      rewrite app_assoc in HI.
      rewrite (subst_ee_open_ee_atom e2 x v y Hce Hyx) in HI.
      exact HI.
    + intros y Hy.
      pose proof (notin_union3_l y L (dom (E1++E2)) (singleton x) Hy) as HyL.
      pose proof (notin_union3_m y L (dom (E1++E2)) (singleton x) Hy) as HyD.
      pose proof (notin_union3_r_neq y x L (dom (E1++E2)) Hy) as Hyx.
      pose proof (H3 y HyL) as Hty.
      assert (HT2 : wf_qtyp (E1++E2) T2).
      { pose proof (typing_wf_env _ _ _ _ Hty) as Hw.
        destruct (wf_env_typ_inv _ _ _ Hw) as [_ [HT _]].
        exact (wf_qtyp_remove_typ_mid E1 x T1 E2 T2 HT). }
      assert (HwEy : wf_env (y ~ bind_typ T2 ++ (E1++E2))).
      { apply wf_env_typ; auto. }
      assert (Hvy : typing (y ~ bind_typ T2 ++ (E1++E2)) (qua_base bot) v T1).
      { eapply typing_extends; [exact Hv | apply extends_app_l | exact HwEy]. }
      pose proof (IH3 y HyL (y ~ bind_typ T2 ++ E1) x T1 E2 v
                    ltac:(rewrite app_assoc; reflexivity) Hce Hct Hcq HwEy Hvy) as HI.
      rewrite app_assoc in HI.
      rewrite (subst_ee_open_ee_atom e3 x v y Hce Hyx) in HI.
      exact HI.
  - (* pair *) eapply typing_pair.
    + exact (wf_qua_remove_typ_mid P0 E1 x T1 E2 HP).
    + apply (IH1 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv).
    + apply (IH2 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv).
  - (* first *) eapply typing_first.
    apply (IH1 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv).
  - (* second *) eapply typing_second.
    apply (IH1 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv).
  - (* upqual *) eapply typing_upqual.
    + apply (IH1 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv).
    + exact (subqual_remove_typ_mid E1 x T1 E2 Qa P0 Hs).
  - (* check *) eapply typing_check.
    + apply (IH1 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv).
    + exact (subqual_remove_typ_mid E1 x T1 E2 Qa P0 Hs).
  - (* without *) eapply typing_without.
    + apply (IH1 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv).
    + exact (subqual_remove_typ_mid E1 x T1 E2 R (qua_negate P0) Hs).
  - (* do *) apply typing_do; auto.
  - (* if0 *) eapply typing_if0.
    + apply (IH1 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv).
    + apply (IH2 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv).
    + apply (IH3 E1 x T1 E2 v eq_refl Hce Hct Hcq HwE Hv).
Qed.

(* ================= ChunkTrans.v ================= *)

Lemma sub_wf_left : forall (E:env) (S T:typ), sub E S T -> wf_typ E S.
Proof. intros E S T H. destruct (sub_wf E S T H) as [_ [HS _]]. exact HS. Qed.

(* env_sim helpers for narrowing at the head binder *)
Lemma env_sim_narrow_sub_head : forall X (U U':typ) E,
  env_sim (X ~ bind_sub U ++ E) (X ~ bind_sub U' ++ E).
Proof. intros. apply sim_cons; [apply sk_sub|apply env_sim_refl]. Qed.

Lemma env_sim_narrow_qua_head : forall X (Q0 Q0':qua) E,
  env_sim (X ~ bind_qua Q0 ++ E) (X ~ bind_qua Q0' ++ E).
Proof. intros. apply sim_cons; [apply sk_qua|apply env_sim_refl]. Qed.

Lemma wf_env_narrow_sub_head : forall X (U U':typ) E,
  wf_env (X ~ bind_sub U ++ E) -> wf_typ E U' -> wf_env (X ~ bind_sub U' ++ E).
Proof.
  intros X U U' E Hw HU'.
  destruct (wf_env_sub_inv _ _ _ Hw) as [HE [HU Hfresh]].
  eapply wf_env_sub; eauto.
Qed.

Lemma wf_env_narrow_qua_head : forall X (Q0 Q0':qua) E,
  wf_env (X ~ bind_qua Q0 ++ E) -> wf_qua E Q0' -> wf_env (X ~ bind_qua Q0' ++ E).
Proof.
  intros X Q0 Q0' E Hw HQ'.
  destruct (wf_env_qua_inv _ _ _ Hw) as [HE [HQ Hfresh]].
  eapply wf_env_qua; eauto.
Qed.

Lemma binds_qua_narrow_sub_head : forall X (U U':typ) E Y R,
  binds Y (bind_qua R) (X ~ bind_sub U ++ E) ->
  binds Y (bind_qua R) (X ~ bind_sub U' ++ E).
Proof.
  intros. unfold binds in *. simpl in *.
  destruct H as [Heq|Ht]; [inversion Heq; discriminate|].
  right; exact Ht.
Qed.

Lemma binds_qua_narrow_qua_head_inv : forall X (Q0 Q0':qua) E Y R,
  binds Y (bind_qua R) (X ~ bind_qua Q0 ++ E) ->
  (Y = X /\ R = Q0) \/ binds Y (bind_qua R) (X ~ bind_qua Q0' ++ E).
Proof.
  intros. unfold binds in *. simpl in *.
  destruct H as [Heq|Ht].
  - inversion Heq; subst. left; auto.
  - right. right; exact Ht.
Qed.

Lemma subqual_narrow_sub_gen : forall (E:env) Q R, subqual E Q R ->
  forall X (U U':typ) (E0:env),
    E = X ~ bind_sub U ++ E0 -> sub E0 U' U ->
    subqual (X ~ bind_sub U' ++ E0) Q R.
Proof.
  intros E Q R H.
  induction H as [Ew Qw Hwf HQ | Ew Qw Hwf HQ
    | Ew Qa Qb Qc bb h1 IH1 hc h2 IH2 | Ew Qa Qb Qc bb h1 IH1 hc h2 IH2
    | Ew b1 b2 Hwf Ho | Ew Xw Hwf HQ
    | R0 Ew Qw Xw hb h1 IH1
    | Ew R1 R2 Qw h1 IH1 HR2 | Ew R1 R2 Qw HR1 h2 IH1
    | Ew R1 R2 Qw h1 IH1 h2 IH2
    | Ew R1 R2 Qw h1 IH1 HR2 | Ew R1 R2 Qw HR1 h2 IH1
    | Ew R1 R2 Qw h1 IH1 h2 IH2
    | Ew Qa R2 S2 Hwf HQa HR2 HS2
    | Ew Qa R2 S2 h1 IH1 h2 IH2
    | Ew Qw Hwf HQ | Ew Qw Hwf HQ | Ew Qw Hwf HQ];
    intros X U U' E0 HE Hnarrow; subst Ew.
  - (* top *)
    eapply subqual_top.
    + eapply wf_env_narrow_sub_head; [exact Hwf|].
      exact (sub_wf_left E0 U' U Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_narrow_sub_head|exact HQ].
  - (* bot *)
    eapply subqual_bot.
    + eapply wf_env_narrow_sub_head; [exact Hwf|].
      exact (sub_wf_left E0 U' U Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_narrow_sub_head|exact HQ].
  - (* eval_elim *)
    eapply subqual_eval_elim; [apply (IH1 X U U' E0 eq_refl Hnarrow)|exact hc|apply (IH2 X U U' E0 eq_refl Hnarrow)].
  - (* eval_intro *)
    eapply subqual_eval_intro; [apply (IH1 X U U' E0 eq_refl Hnarrow)|exact hc|apply (IH2 X U U' E0 eq_refl Hnarrow)].
  - (* lift *)
    eapply subqual_lift_elem.
    + eapply wf_env_narrow_sub_head; [exact Hwf|].
      exact (sub_wf_left E0 U' U Hnarrow).
    + exact Ho.
  - (* refl_qvar *)
    eapply subqual_refl_qvar.
    + eapply wf_env_narrow_sub_head; [exact Hwf|].
      exact (sub_wf_left E0 U' U Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_narrow_sub_head|exact HQ].
  - (* trans_qvar *)
    eapply subqual_trans_qvar.
    + exact (binds_qua_narrow_sub_head X U U' E0 Xw R0 hb).
    + apply (IH1 X U U' E0 eq_refl Hnarrow).
  - (* join_inl *)
    eapply subqual_join_inl.
    + apply (IH1 X U U' E0 eq_refl Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_narrow_sub_head|exact HR2].
  - (* join_inr *)
    eapply subqual_join_inr.
    + eapply wf_qua_sim; [apply env_sim_narrow_sub_head|exact HR1].
    + apply (IH1 X U U' E0 eq_refl Hnarrow).
  - (* join_elim *)
    eapply subqual_join_elim.
    + apply (IH1 X U U' E0 eq_refl Hnarrow).
    + apply (IH2 X U U' E0 eq_refl Hnarrow).
  - (* meet_eliml *)
    eapply subqual_meet_eliml.
    + apply (IH1 X U U' E0 eq_refl Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_narrow_sub_head|exact HR2].
  - (* meet_elimr *)
    eapply subqual_meet_elimr.
    + eapply wf_qua_sim; [apply env_sim_narrow_sub_head|exact HR1].
    + apply (IH1 X U U' E0 eq_refl Hnarrow).
  - (* meet_intro *)
    eapply subqual_meet_intro.
    + apply (IH1 X U U' E0 eq_refl Hnarrow).
    + apply (IH2 X U U' E0 eq_refl Hnarrow).
  - (* dist *)
    eapply subqual_dist.
    + eapply wf_env_narrow_sub_head; [exact Hwf|].
      exact (sub_wf_left E0 U' U Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_narrow_sub_head|exact HQa].
    + eapply wf_qua_sim; [apply env_sim_narrow_sub_head|exact HR2].
    + eapply wf_qua_sim; [apply env_sim_narrow_sub_head|exact HS2].
  - (* trans *)
    eapply subqual_trans.
    + apply (IH1 X U U' E0 eq_refl Hnarrow).
    + apply (IH2 X U U' E0 eq_refl Hnarrow).
  - (* negate_intro *)
    eapply subqual_negate_intro.
    + eapply wf_env_narrow_sub_head; [exact Hwf|].
      exact (sub_wf_left E0 U' U Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_narrow_sub_head|exact HQ].
  - (* negate_elim *)
    eapply subqual_negate_elim.
    + eapply wf_env_narrow_sub_head; [exact Hwf|].
      exact (sub_wf_left E0 U' U Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_narrow_sub_head|exact HQ].
  - (* refl_negate *)
    eapply subqual_refl_negate.
    + eapply wf_env_narrow_sub_head; [exact Hwf|].
      exact (sub_wf_left E0 U' U Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_narrow_sub_head|exact HQ].
Qed.





Lemma env_sim_change_sub_mid : forall (E1:env) X (U U':typ) (E2:env),
  env_sim (E1 ++ (X, bind_sub U) :: E2) (E1 ++ (X, bind_sub U') :: E2).
Proof.
  induction E1 as [| [y c] E1 IH]; intros X U U' E2; simpl.
  - apply sim_cons; [apply sk_sub|apply env_sim_refl].
  - apply sim_cons; [apply same_kind_refl|apply IH].
Qed.

Lemma env_sim_change_qua_mid : forall (E1:env) X (Q0 Q0':qua) (E2:env),
  env_sim (E1 ++ (X, bind_qua Q0) :: E2) (E1 ++ (X, bind_qua Q0') :: E2).
Proof.
  induction E1 as [| [y c] E1 IH]; intros X Q0 Q0' E2; simpl.
  - apply sim_cons; [apply sk_qua|apply env_sim_refl].
  - apply sim_cons; [apply same_kind_refl|apply IH].
Qed.

Lemma binds_qua_change_sub_mid : forall (E1:env) X (U U':typ) (E2:env) Y R,
  binds Y (bind_qua R) (E1 ++ X ~ bind_sub U ++ E2) ->
  binds Y (bind_qua R) (E1 ++ X ~ bind_sub U' ++ E2).
Proof.
  induction E1 as [| [y c] E1 IH]; intros X U U' E2 Y R Hb; simpl in *.
  - unfold binds in *. simpl in Hb. destruct Hb as [Heq|Ht]; [inversion Heq; discriminate|].
    right; exact Ht.
  - unfold binds in *. simpl in Hb. destruct Hb as [Heq|Ht].
    + left; exact Heq.
    + right; apply (IH X U U' E2 Y R). exact Ht.
Qed.

Lemma binds_qua_change_qua_mid : forall (E1:env) X (Q0 Q0':qua) (E2:env) Y R,
  binds Y (bind_qua R) (E1 ++ X ~ bind_qua Q0 ++ E2) ->
  (Y = X /\ R = Q0) \/ binds Y (bind_qua R) (E1 ++ X ~ bind_qua Q0' ++ E2).
Proof.
  induction E1 as [| [y c] E1 IH]; intros X Q0 Q0' E2 Y R Hb; simpl in *.
  - unfold binds in *. simpl in Hb. destruct Hb as [Heq|Ht].
    + inversion Heq; subst. left; auto.
    + right. right; exact Ht.
  - unfold binds in *. simpl in Hb. destruct Hb as [Heq|Ht].
    + right. left; exact Heq.
    + destruct (IH X Q0 Q0' E2 Y R Ht) as [Hl|Hin].
      * left; exact Hl.
      * right; right; exact Hin.
Qed.

Lemma extends_insert_mid : forall (E1 E2:env) X (b:binding),
  extends E2 (E1 ++ (X,b) :: E2).
Proof.
  intros E1 E2 X b y c Hy.
  apply binds_mid_weaken.
  apply binds_app_3. exact Hy.
Qed.

Lemma dom_change_mid : forall (E1:env) X (b b':binding) (E2:env),
  dom (E1 ++ (X,b) :: E2) = dom (E1 ++ (X,b') :: E2).
Proof.
  induction E1 as [| [y c] E1 IH]; intros X b b' E2; simpl.
  - reflexivity.
  - rewrite (IH X b b' E2). reflexivity.
Qed.

Lemma wf_env_change_sub_mid : forall (E1:env) X (U U':typ) (E2:env),
  wf_env (E1 ++ (X, bind_sub U) :: E2) -> wf_typ E2 U' ->
  wf_env (E1 ++ (X, bind_sub U') :: E2).
Proof.
  induction E1 as [| [y c] E1 IH]; intros X U U' E2 Hw HU'; simpl in *.
  - destruct (wf_env_sub_inv _ _ _ Hw) as [HE [HU Hf]].
    eapply wf_env_sub; eauto.
  - destruct c as [U0|T0|Q0]; inversion Hw; subst.
    + eapply wf_env_sub.
      * apply (IH X U U' E2); eassumption.
      * eapply wf_typ_sim; [apply env_sim_change_sub_mid|eassumption].
      * rewrite <- (dom_change_mid E1 X (bind_sub U) (bind_sub U') E2); eassumption.
    + eapply wf_env_typ.
      * apply (IH X U U' E2); eassumption.
      * eapply wf_qtyp_sim; [apply env_sim_change_sub_mid|eassumption].
      * rewrite <- (dom_change_mid E1 X (bind_sub U) (bind_sub U') E2); eassumption.
    + eapply wf_env_qua.
      * apply (IH X U U' E2); eassumption.
      * eapply wf_qua_sim; [apply env_sim_change_sub_mid|eassumption].
      * rewrite <- (dom_change_mid E1 X (bind_sub U) (bind_sub U') E2); eassumption.
Qed.

Lemma wf_env_change_qua_mid : forall (E1:env) X (Q0 Q0':qua) (E2:env),
  wf_env (E1 ++ (X, bind_qua Q0) :: E2) -> wf_qua E2 Q0' ->
  wf_env (E1 ++ (X, bind_qua Q0') :: E2).
Proof.
  induction E1 as [| [y c] E1 IH]; intros X Q0 Q0' E2 Hw HQ'; simpl in *.
  - destruct (wf_env_qua_inv _ _ _ Hw) as [HE [HQ Hf]].
    eapply wf_env_qua; eauto.
  - destruct c as [U0|T0|Q0b]; inversion Hw; subst.
    + eapply wf_env_sub.
      * apply (IH X Q0 Q0' E2); eassumption.
      * eapply wf_typ_sim; [apply env_sim_change_qua_mid|eassumption].
      * rewrite <- (dom_change_mid E1 X (bind_qua Q0) (bind_qua Q0') E2); eassumption.
    + eapply wf_env_typ.
      * apply (IH X Q0 Q0' E2); eassumption.
      * eapply wf_qtyp_sim; [apply env_sim_change_qua_mid|eassumption].
      * rewrite <- (dom_change_mid E1 X (bind_qua Q0) (bind_qua Q0') E2); eassumption.
    + eapply wf_env_qua.
      * apply (IH X Q0 Q0' E2); eassumption.
      * eapply wf_qua_sim; [apply env_sim_change_qua_mid|eassumption].
      * rewrite <- (dom_change_mid E1 X (bind_qua Q0) (bind_qua Q0') E2); eassumption.
Qed.




Lemma subqual_narrow_sub_gen2 : forall (E:env) Q R, subqual E Q R ->
  forall (E1:env) X (U U':typ) (E2:env),
    E = E1 ++ (X, bind_sub U) :: E2 -> sub E2 U' U ->
    subqual (E1 ++ (X, bind_sub U') :: E2) Q R.
Proof.
  intros E Q R H.
  induction H as [Ew Qw Hwf HQ | Ew Qw Hwf HQ
    | Ew Qa Qb Qc bb h1 IH1 hc h2 IH2 | Ew Qa Qb Qc bb h1 IH1 hc h2 IH2
    | Ew b1 b2 Hwf Ho | Ew Xw Hwf HQ
    | R0 Ew Qw Xw hb h1 IH1
    | Ew R1 R2 Qw h1 IH1 HR2 | Ew R1 R2 Qw HR1 h2 IH1
    | Ew R1 R2 Qw h1 IH1 h2 IH2
    | Ew R1 R2 Qw h1 IH1 HR2 | Ew R1 R2 Qw HR1 h2 IH1
    | Ew R1 R2 Qw h1 IH1 h2 IH2
    | Ew Qa R2 S2 Hwf HQa HR2 HS2
    | Ew Qa R2 S2 h1 IH1 h2 IH2
    | Ew Qw Hwf HQ | Ew Qw Hwf HQ | Ew Qw Hwf HQ];
    intros E1 X U U' E2 HE Hnarrow; subst Ew.
  - (* top *)
    eapply subqual_top.
    + eapply wf_env_change_sub_mid; [exact Hwf|].
      exact (sub_wf_left E2 U' U Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_change_sub_mid|exact HQ].
  - (* bot *)
    eapply subqual_bot.
    + eapply wf_env_change_sub_mid; [exact Hwf|].
      exact (sub_wf_left E2 U' U Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_change_sub_mid|exact HQ].
  - (* eval_elim *)
    eapply subqual_eval_elim; [apply (IH1 E1 X U U' E2 eq_refl Hnarrow)|exact hc|apply (IH2 E1 X U U' E2 eq_refl Hnarrow)].
  - (* eval_intro *)
    eapply subqual_eval_intro; [apply (IH1 E1 X U U' E2 eq_refl Hnarrow)|exact hc|apply (IH2 E1 X U U' E2 eq_refl Hnarrow)].
  - (* lift *)
    eapply subqual_lift_elem.
    + eapply wf_env_change_sub_mid; [exact Hwf|].
      exact (sub_wf_left E2 U' U Hnarrow).
    + exact Ho.
  - (* refl_qvar *)
    eapply subqual_refl_qvar.
    + eapply wf_env_change_sub_mid; [exact Hwf|].
      exact (sub_wf_left E2 U' U Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_change_sub_mid|exact HQ].
  - (* trans_qvar *)
    eapply subqual_trans_qvar.
    + exact (binds_qua_change_sub_mid E1 X U U' E2 Xw R0 hb).
    + apply (IH1 E1 X U U' E2 eq_refl Hnarrow).
  - (* join_inl *)
    eapply subqual_join_inl.
    + apply (IH1 E1 X U U' E2 eq_refl Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_change_sub_mid|exact HR2].
  - (* join_inr *)
    eapply subqual_join_inr.
    + eapply wf_qua_sim; [apply env_sim_change_sub_mid|exact HR1].
    + apply (IH1 E1 X U U' E2 eq_refl Hnarrow).
  - (* join_elim *)
    eapply subqual_join_elim.
    + apply (IH1 E1 X U U' E2 eq_refl Hnarrow).
    + apply (IH2 E1 X U U' E2 eq_refl Hnarrow).
  - (* meet_eliml *)
    eapply subqual_meet_eliml.
    + apply (IH1 E1 X U U' E2 eq_refl Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_change_sub_mid|exact HR2].
  - (* meet_elimr *)
    eapply subqual_meet_elimr.
    + eapply wf_qua_sim; [apply env_sim_change_sub_mid|exact HR1].
    + apply (IH1 E1 X U U' E2 eq_refl Hnarrow).
  - (* meet_intro *)
    eapply subqual_meet_intro.
    + apply (IH1 E1 X U U' E2 eq_refl Hnarrow).
    + apply (IH2 E1 X U U' E2 eq_refl Hnarrow).
  - (* dist *)
    eapply subqual_dist.
    + eapply wf_env_change_sub_mid; [exact Hwf|].
      exact (sub_wf_left E2 U' U Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_change_sub_mid|exact HQa].
    + eapply wf_qua_sim; [apply env_sim_change_sub_mid|exact HR2].
    + eapply wf_qua_sim; [apply env_sim_change_sub_mid|exact HS2].
  - (* trans *)
    eapply subqual_trans.
    + apply (IH1 E1 X U U' E2 eq_refl Hnarrow).
    + apply (IH2 E1 X U U' E2 eq_refl Hnarrow).
  - (* negate_intro *)
    eapply subqual_negate_intro.
    + eapply wf_env_change_sub_mid; [exact Hwf|].
      exact (sub_wf_left E2 U' U Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_change_sub_mid|exact HQ].
  - (* negate_elim *)
    eapply subqual_negate_elim.
    + eapply wf_env_change_sub_mid; [exact Hwf|].
      exact (sub_wf_left E2 U' U Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_change_sub_mid|exact HQ].
  - (* refl_negate *)
    eapply subqual_refl_negate.
    + eapply wf_env_change_sub_mid; [exact Hwf|].
      exact (sub_wf_left E2 U' U Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_change_sub_mid|exact HQ].
Qed.

Lemma subqual_narrow_sub_head : forall X (U U':typ) (E:env) Q R,
  sub E U' U ->
  subqual (X ~ bind_sub U ++ E) Q R ->
  subqual (X ~ bind_sub U' ++ E) Q R.
Proof.
  intros X U U' E Q R Hn Hq.
  exact (subqual_narrow_sub_gen2 (X ~ bind_sub U ++ E) Q R Hq (@nil (atom*binding)) X U U' E eq_refl Hn).
Qed.

Lemma subqual_wf_left : forall (E:env) Q R, subqual E Q R -> wf_qua E Q.
Proof. intros E Q R H. destruct (subqual_wf E Q R H) as [_ [HQ _]]. exact HQ. Qed.

Lemma subqual_narrow_qua_gen : forall (E:env) Q R, subqual E Q R ->
  forall X (Q0 Q0':qua) (E0:env),
    E = X ~ bind_qua Q0 ++ E0 -> subqual E0 Q0' Q0 ->
    subqual (X ~ bind_qua Q0' ++ E0) Q R.
Proof.
  intros E Q R H.
  induction H as [Ew Qw Hwf HQ | Ew Qw Hwf HQ
    | Ew Qa Qb Qc bb h1 IH1 hc h2 IH2 | Ew Qa Qb Qc bb h1 IH1 hc h2 IH2
    | Ew b1 b2 Hwf Ho | Ew Xw Hwf HQ
    | R0 Ew Qw Xw hb h1 IH1
    | Ew R1 R2 Qw h1 IH1 HR2 | Ew R1 R2 Qw HR1 h2 IH1
    | Ew R1 R2 Qw h1 IH1 h2 IH2
    | Ew R1 R2 Qw h1 IH1 HR2 | Ew R1 R2 Qw HR1 h2 IH1
    | Ew R1 R2 Qw h1 IH1 h2 IH2
    | Ew Qa R2 S2 Hwf HQa HR2 HS2
    | Ew Qa R2 S2 h1 IH1 h2 IH2
    | Ew Qw Hwf HQ | Ew Qw Hwf HQ | Ew Qw Hwf HQ];
    intros X Q0 Q0' E0 HE Hnarrow; subst Ew.
  - eapply subqual_top.
    + eapply wf_env_narrow_qua_head; [exact Hwf| exact (subqual_wf_left E0 Q0' Q0 Hnarrow)].
    + eapply wf_qua_sim; [apply (env_sim_narrow_qua_head X Q0 Q0' E0)|exact HQ].
  - eapply subqual_bot.
    + eapply wf_env_narrow_qua_head; [exact Hwf| exact (subqual_wf_left E0 Q0' Q0 Hnarrow)].
    + eapply wf_qua_sim; [apply (env_sim_narrow_qua_head X Q0 Q0' E0)|exact HQ].
  - eapply subqual_eval_elim; [apply (IH1 X Q0 Q0' E0 eq_refl Hnarrow)|exact hc|apply (IH2 X Q0 Q0' E0 eq_refl Hnarrow)].
  - eapply subqual_eval_intro; [apply (IH1 X Q0 Q0' E0 eq_refl Hnarrow)|exact hc|apply (IH2 X Q0 Q0' E0 eq_refl Hnarrow)].
  - eapply subqual_lift_elem.
    + eapply wf_env_narrow_qua_head; [exact Hwf| exact (subqual_wf_left E0 Q0' Q0 Hnarrow)].
    + exact Ho.
  - eapply subqual_refl_qvar.
    + eapply wf_env_narrow_qua_head; [exact Hwf| exact (subqual_wf_left E0 Q0' Q0 Hnarrow)].
    + eapply wf_qua_sim; [apply (env_sim_narrow_qua_head X Q0 Q0' E0)|exact HQ].
  - destruct (binds_qua_narrow_qua_head_inv X Q0 Q0' E0 Xw R0 hb) as [[HY HR]|Hbt].
    + subst Xw. subst R0.
      pose proof (IH1 X Q0 Q0' E0 eq_refl Hnarrow) as HT.
      assert (HwfT : wf_env (X ~ bind_qua Q0' ++ E0)).
      { destruct (subqual_wf _ _ _ HT) as [Hwe _]. exact Hwe. }
      assert (Hlow : subqual (X ~ bind_qua Q0' ++ E0) Q0' Q0).
      { eapply subqual_extends; [exact Hnarrow | apply (extends_insert_mid (@nil (atom*binding)) E0 X (bind_qua Q0')) | exact HwfT]. }
      eapply subqual_trans_qvar; [| eapply subqual_trans; [exact Hlow|exact HT]].
      unfold binds. simpl. left; reflexivity.
    + eapply subqual_trans_qvar; [exact Hbt|apply (IH1 X Q0 Q0' E0 eq_refl Hnarrow)].
  - eapply subqual_join_inl.
    + apply (IH1 X Q0 Q0' E0 eq_refl Hnarrow).
    + eapply wf_qua_sim; [apply (env_sim_narrow_qua_head X Q0 Q0' E0)|exact HR2].
  - eapply subqual_join_inr.
    + eapply wf_qua_sim; [apply (env_sim_narrow_qua_head X Q0 Q0' E0)|exact HR1].
    + apply (IH1 X Q0 Q0' E0 eq_refl Hnarrow).
  - eapply subqual_join_elim.
    + apply (IH1 X Q0 Q0' E0 eq_refl Hnarrow).
    + apply (IH2 X Q0 Q0' E0 eq_refl Hnarrow).
  - eapply subqual_meet_eliml.
    + apply (IH1 X Q0 Q0' E0 eq_refl Hnarrow).
    + eapply wf_qua_sim; [apply (env_sim_narrow_qua_head X Q0 Q0' E0)|exact HR2].
  - eapply subqual_meet_elimr.
    + eapply wf_qua_sim; [apply (env_sim_narrow_qua_head X Q0 Q0' E0)|exact HR1].
    + apply (IH1 X Q0 Q0' E0 eq_refl Hnarrow).
  - eapply subqual_meet_intro.
    + apply (IH1 X Q0 Q0' E0 eq_refl Hnarrow).
    + apply (IH2 X Q0 Q0' E0 eq_refl Hnarrow).
  - eapply subqual_dist.
    + eapply wf_env_narrow_qua_head; [exact Hwf| exact (subqual_wf_left E0 Q0' Q0 Hnarrow)].
    + eapply wf_qua_sim; [apply (env_sim_narrow_qua_head X Q0 Q0' E0)|exact HQa].
    + eapply wf_qua_sim; [apply (env_sim_narrow_qua_head X Q0 Q0' E0)|exact HR2].
    + eapply wf_qua_sim; [apply (env_sim_narrow_qua_head X Q0 Q0' E0)|exact HS2].
  - eapply subqual_trans.
    + apply (IH1 X Q0 Q0' E0 eq_refl Hnarrow).
    + apply (IH2 X Q0 Q0' E0 eq_refl Hnarrow).
  - eapply subqual_negate_intro.
    + eapply wf_env_narrow_qua_head; [exact Hwf| exact (subqual_wf_left E0 Q0' Q0 Hnarrow)].
    + eapply wf_qua_sim; [apply (env_sim_narrow_qua_head X Q0 Q0' E0)|exact HQ].
  - eapply subqual_negate_elim.
    + eapply wf_env_narrow_qua_head; [exact Hwf| exact (subqual_wf_left E0 Q0' Q0 Hnarrow)].
    + eapply wf_qua_sim; [apply (env_sim_narrow_qua_head X Q0 Q0' E0)|exact HQ].
  - eapply subqual_refl_negate.
    + eapply wf_env_narrow_qua_head; [exact Hwf| exact (subqual_wf_left E0 Q0' Q0 Hnarrow)].
    + eapply wf_qua_sim; [apply (env_sim_narrow_qua_head X Q0 Q0' E0)|exact HQ].
Qed.

Lemma subqual_narrow_qua_gen2 : forall (E:env) Q R, subqual E Q R ->
  forall (E1:env) X (Q0 Q0':qua) (E2:env),
    E = E1 ++ (X, bind_qua Q0) :: E2 -> subqual E2 Q0' Q0 ->
    subqual (E1 ++ (X, bind_qua Q0') :: E2) Q R.
Proof.
  intros E Q R H.
  induction H as [Ew Qw Hwf HQ | Ew Qw Hwf HQ
    | Ew Qa Qb Qc bb h1 IH1 hc h2 IH2 | Ew Qa Qb Qc bb h1 IH1 hc h2 IH2
    | Ew b1 b2 Hwf Ho | Ew Xw Hwf HQ
    | R0 Ew Qw Xw hb h1 IH1
    | Ew R1 R2 Qw h1 IH1 HR2 | Ew R1 R2 Qw HR1 h2 IH1
    | Ew R1 R2 Qw h1 IH1 h2 IH2
    | Ew R1 R2 Qw h1 IH1 HR2 | Ew R1 R2 Qw HR1 h2 IH1
    | Ew R1 R2 Qw h1 IH1 h2 IH2
    | Ew Qa R2 S2 Hwf HQa HR2 HS2
    | Ew Qa R2 S2 h1 IH1 h2 IH2
    | Ew Qw Hwf HQ | Ew Qw Hwf HQ | Ew Qw Hwf HQ];
    intros E1 X Q0 Q0' E2 HE Hnarrow; subst Ew.
  - eapply subqual_top.
    + eapply wf_env_change_qua_mid; [exact Hwf| exact (subqual_wf_left E2 Q0' Q0 Hnarrow)].
    + eapply wf_qua_sim; [apply env_sim_change_qua_mid|exact HQ].
  - eapply subqual_bot.
    + eapply wf_env_change_qua_mid; [exact Hwf| exact (subqual_wf_left E2 Q0' Q0 Hnarrow)].
    + eapply wf_qua_sim; [apply env_sim_change_qua_mid|exact HQ].
  - eapply subqual_eval_elim; [apply (IH1 E1 X Q0 Q0' E2 eq_refl Hnarrow)|exact hc|apply (IH2 E1 X Q0 Q0' E2 eq_refl Hnarrow)].
  - eapply subqual_eval_intro; [apply (IH1 E1 X Q0 Q0' E2 eq_refl Hnarrow)|exact hc|apply (IH2 E1 X Q0 Q0' E2 eq_refl Hnarrow)].
  - eapply subqual_lift_elem.
    + eapply wf_env_change_qua_mid; [exact Hwf| exact (subqual_wf_left E2 Q0' Q0 Hnarrow)].
    + exact Ho.
  - eapply subqual_refl_qvar.
    + eapply wf_env_change_qua_mid; [exact Hwf| exact (subqual_wf_left E2 Q0' Q0 Hnarrow)].
    + eapply wf_qua_sim; [apply env_sim_change_qua_mid|exact HQ].
  - destruct (binds_qua_change_qua_mid E1 X Q0 Q0' E2 Xw R0 hb) as [[HY HR]|Hbt].
    + subst Xw. subst R0.
      pose proof (IH1 E1 X Q0 Q0' E2 eq_refl Hnarrow) as HT.
      assert (HwfT : wf_env (E1 ++ (X, bind_qua Q0') :: E2)).
      { destruct (subqual_wf _ _ _ HT) as [Hwe _]. exact Hwe. }
      assert (Hlow : subqual (E1 ++ (X, bind_qua Q0') :: E2) Q0' Q0).
      { eapply subqual_extends; [exact Hnarrow | apply (extends_insert_mid E1 E2 X (bind_qua Q0')) | exact HwfT]. }
      eapply subqual_trans_qvar; [| eapply subqual_trans; [exact Hlow|exact HT]].
      unfold binds. apply in_app_iff. right. left. reflexivity.
    + eapply subqual_trans_qvar; [exact Hbt|apply (IH1 E1 X Q0 Q0' E2 eq_refl Hnarrow)].
  - eapply subqual_join_inl.
    + apply (IH1 E1 X Q0 Q0' E2 eq_refl Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_change_qua_mid|exact HR2].
  - eapply subqual_join_inr.
    + eapply wf_qua_sim; [apply env_sim_change_qua_mid|exact HR1].
    + apply (IH1 E1 X Q0 Q0' E2 eq_refl Hnarrow).
  - eapply subqual_join_elim.
    + apply (IH1 E1 X Q0 Q0' E2 eq_refl Hnarrow).
    + apply (IH2 E1 X Q0 Q0' E2 eq_refl Hnarrow).
  - eapply subqual_meet_eliml.
    + apply (IH1 E1 X Q0 Q0' E2 eq_refl Hnarrow).
    + eapply wf_qua_sim; [apply env_sim_change_qua_mid|exact HR2].
  - eapply subqual_meet_elimr.
    + eapply wf_qua_sim; [apply env_sim_change_qua_mid|exact HR1].
    + apply (IH1 E1 X Q0 Q0' E2 eq_refl Hnarrow).
  - eapply subqual_meet_intro.
    + apply (IH1 E1 X Q0 Q0' E2 eq_refl Hnarrow).
    + apply (IH2 E1 X Q0 Q0' E2 eq_refl Hnarrow).
  - eapply subqual_dist.
    + eapply wf_env_change_qua_mid; [exact Hwf| exact (subqual_wf_left E2 Q0' Q0 Hnarrow)].
    + eapply wf_qua_sim; [apply env_sim_change_qua_mid|exact HQa].
    + eapply wf_qua_sim; [apply env_sim_change_qua_mid|exact HR2].
    + eapply wf_qua_sim; [apply env_sim_change_qua_mid|exact HS2].
  - eapply subqual_trans.
    + apply (IH1 E1 X Q0 Q0' E2 eq_refl Hnarrow).
    + apply (IH2 E1 X Q0 Q0' E2 eq_refl Hnarrow).
  - eapply subqual_negate_intro.
    + eapply wf_env_change_qua_mid; [exact Hwf| exact (subqual_wf_left E2 Q0' Q0 Hnarrow)].
    + eapply wf_qua_sim; [apply env_sim_change_qua_mid|exact HQ].
  - eapply subqual_negate_elim.
    + eapply wf_env_change_qua_mid; [exact Hwf| exact (subqual_wf_left E2 Q0' Q0 Hnarrow)].
    + eapply wf_qua_sim; [apply env_sim_change_qua_mid|exact HQ].
  - eapply subqual_refl_negate.
    + eapply wf_env_change_qua_mid; [exact Hwf| exact (subqual_wf_left E2 Q0' Q0 Hnarrow)].
    + eapply wf_qua_sim; [apply env_sim_change_qua_mid|exact HQ].
Qed.


Lemma subqual_narrow_qua_head : forall X (Q0 Q0':qua) (E:env) Q R,
  subqual E Q0' Q0 ->
  subqual (X ~ bind_qua Q0 ++ E) Q R ->
  subqual (X ~ bind_qua Q0' ++ E) Q R.
Proof.
  intros X Q0 Q0' E Q R Hn Hq.
  exact (subqual_narrow_qua_gen2 (X ~ bind_qua Q0 ++ E) Q R Hq (@nil (atom*binding)) X Q0 Q0' E eq_refl Hn).
Qed.

Lemma binds_sub_narrow_qua_head : forall X (Q0 Q0':qua) E Z W,
  binds Z (bind_sub W) (X ~ bind_qua Q0 ++ E) ->
  binds Z (bind_sub W) (X ~ bind_qua Q0' ++ E).
Proof.
  intros. unfold binds in *. simpl in *.
  destruct H as [Heq|Ht]; [inversion Heq; discriminate|].
  right; exact Ht.
Qed.

Lemma binds_sub_change_qua_mid : forall (E1:env) X (Q0 Q0':qua) (E2:env) Z W,
  binds Z (bind_sub W) (E1 ++ (X, bind_qua Q0) :: E2) ->
  binds Z (bind_sub W) (E1 ++ (X, bind_qua Q0') :: E2).
Proof.
  intros E1 X Q0 Q0' E2 Z W H. unfold binds in *.
  apply in_app_iff in H. destruct H as [H|H].
  - apply in_app_iff. left; exact H.
  - simpl in H. destruct H as [Heq|Ht].
    + inversion Heq; discriminate.
    + apply in_app_iff. right; right; exact Ht.
Qed.

Lemma sub_subqtype_narrow_qua_gen2 :
  (forall (E:env) (S T:typ), sub E S T ->
     forall (E1:env) X (Q0 Q0':qua) (E2:env),
       E = E1 ++ (X, bind_qua Q0) :: E2 -> subqual E2 Q0' Q0 ->
       sub (E1 ++ (X, bind_qua Q0') :: E2) S T) /\
  (forall (E:env) (S T:qtyp), subqtype E S T ->
     forall (E1:env) X (Q0 Q0':qua) (E2:env),
       E = E1 ++ (X, bind_qua Q0) :: E2 -> subqual E2 Q0' Q0 ->
       subqtype (E1 ++ (X, bind_qua Q0') :: E2) S T).
Proof.
  apply sub_tq_mut
    with (P := fun E S T _ => forall (E1:env) X (Q0 Q0':qua) (E2:env),
                E = E1 ++ (X, bind_qua Q0) :: E2 -> subqual E2 Q0' Q0 ->
                sub (E1 ++ (X, bind_qua Q0') :: E2) S T)
         (P0 := fun E S T _ => forall (E1:env) X (Q0 Q0':qua) (E2:env),
                E = E1 ++ (X, bind_qua Q0) :: E2 -> subqual E2 Q0' Q0 ->
                subqtype (E1 ++ (X, bind_qua Q0') :: E2) S T).
  - intros E S w w0 E1 X Q0 Q0' E2 HE Hn. subst E. eapply sub_top.
    + eapply wf_env_change_qua_mid; [eassumption | exact (subqual_wf_left E2 Q0' Q0 Hn)].
    + eapply wf_typ_sim; [apply (env_sim_change_qua_mid E1 X Q0 Q0' E2)|exact w0].
  - intros E w E1 X Q0 Q0' E2 HE Hn. subst E. apply sub_refl_int.
    eapply wf_env_change_qua_mid; [eassumption | exact (subqual_wf_left E2 Q0' Q0 Hn)].
  - intros E Z w w0 E1 X Q0 Q0' E2 HE Hn. subst E. eapply sub_refl_tvar.
    + eapply wf_env_change_qua_mid; [eassumption | exact (subqual_wf_left E2 Q0' Q0 Hn)].
    + eapply wf_typ_sim; [apply (env_sim_change_qua_mid E1 X Q0 Q0' E2)|exact w0].
  - intros U E T Z b s IH E1 X Q0 Q0' E2 HE Hn. subst E. eapply sub_trans_tvar.
    + exact (binds_sub_change_qua_mid E1 X Q0 Q0' E2 Z U b).
    + apply (IH E1 X Q0 Q0' E2 eq_refl Hn).
  - intros E S1 S2 T1 T2 s IH1 s0 IH2 E1 X Q0 Q0' E2 HE Hn. subst E.
    eapply sub_arrow.
    + apply (IH1 E1 X Q0 Q0' E2 eq_refl Hn).
    + apply (IH2 E1 X Q0 Q0' E2 eq_refl Hn).
  - intros L E S1 S2 T1 T2 s IH1 s0 IH0 E1 X Q0 Q0' E2 HE Hn. subst E.
    eapply sub_all with (L:=L).
    + apply (IH1 E1 X Q0 Q0' E2 eq_refl Hn).
    + intros Z HZ. apply (IH0 Z HZ (Z ~ bind_sub T1 ++ E1) X Q0 Q0' E2).
      rewrite <- app_assoc. reflexivity. exact Hn.
  - intros L E S1 S2 T1 T2 s s0 IH0 E1 X Q0 Q0' E2 HE Hn. subst E.
    eapply sub_qall with (L:=L).
    + eapply subqual_narrow_qua_gen2; [exact s|reflexivity|exact Hn].
    + intros Z HZ. apply (IH0 Z HZ (Z ~ bind_qua T1 ++ E1) X Q0 Q0' E2).
      rewrite <- app_assoc. reflexivity. exact Hn.
  - intros E S1 S2 T1 T2 s IH1 s0 IH2 E1 X Q0 Q0' E2 HE Hn. subst E.
    eapply sub_sum.
    + apply (IH1 E1 X Q0 Q0' E2 eq_refl Hn).
    + apply (IH2 E1 X Q0 Q0' E2 eq_refl Hn).
  - intros E S1 S2 T1 T2 s IH1 s0 IH2 E1 X Q0 Q0' E2 HE Hn. subst E.
    eapply sub_pair.
    + apply (IH1 E1 X Q0 Q0' E2 eq_refl Hn).
    + apply (IH2 E1 X Q0 Q0' E2 eq_refl Hn).
  - intros E Q1 T1 Q2 T2 s s0 IH E1 X Q0 Q0' E2 HE Hn. subst E.
    eapply sub_qtyp_qtyp.
    + eapply subqual_narrow_qua_gen2; [exact s|reflexivity|exact Hn].
    + apply (IH E1 X Q0 Q0' E2 eq_refl Hn).
Qed.


Lemma sub_narrow_qua_head : forall X (Q0 Q0':qua) (E:env) S T,
  subqual E Q0' Q0 -> sub (X ~ bind_qua Q0 ++ E) S T -> sub (X ~ bind_qua Q0' ++ E) S T.
Proof. intros. exact (proj1 sub_subqtype_narrow_qua_gen2 (X ~ bind_qua Q0 ++ E) S T H0 (@nil (atom*binding)) X Q0 Q0' E eq_refl H). Qed.

Lemma subqtype_narrow_qua_head : forall X (Q0 Q0':qua) (E:env) S T,
  subqual E Q0' Q0 -> subqtype (X ~ bind_qua Q0 ++ E) S T -> subqtype (X ~ bind_qua Q0' ++ E) S T.
Proof. intros. exact (proj2 sub_subqtype_narrow_qua_gen2 (X ~ bind_qua Q0 ++ E) S T H0 (@nil (atom*binding)) X Q0 Q0' E eq_refl H). Qed.

(* ================= ChunkTrans2.v ================= *)

Definition trans_on_typ (T:typ) : Prop :=
  forall E S U, sub E S T -> sub E T U -> sub E S U.
Definition trans_on_qtyp (T:qtyp) : Prop :=
  forall E S U, subqtype E S T -> subqtype E T U -> subqtype E S U.

Fixpoint size_qua (Q:qua) : nat :=
  match Q with
  | qua_base _ => 0
  | qua_bvar _ => 0
  | qua_fvar _ => 0
  | qua_meet Q1 Q2 => S (size_qua Q1 + size_qua Q2)
  | qua_join Q1 Q2 => S (size_qua Q1 + size_qua Q2)
  | qua_negate Q1 => S (size_qua Q1)
  end.

Fixpoint size_typ (T:typ) : nat :=
  match T with
  | typ_top => 0
  | typ_int => 0
  | typ_bvar _ => 0
  | typ_fvar _ => 0
  | typ_arrow T1 T2 => S (size_qtyp T1 + size_qtyp T2)
  | typ_all T1 T2 => S (size_typ T1 + size_qtyp T2)
  | typ_qall Q T => S (size_qua Q + size_qtyp T)
  | typ_sum T1 T2 => S (size_qtyp T1 + size_qtyp T2)
  | typ_pair T1 T2 => S (size_qtyp T1 + size_qtyp T2)
  | typ_ref T1 => S (size_qtyp T1)
  end
with size_qtyp (T:qtyp) : nat :=
  match T with qtyp_qtyp Q T' => S (size_qua Q + size_typ T') end.

(* opening with an fvar preserves sizes *)
Fixpoint size_open_tt (T:typ) {struct T} :
  forall K X, size_typ (open_tt_rec K (typ_fvar X) T) = size_typ T
with size_open_tqt (T:qtyp) {struct T} :
  forall K X, size_qtyp (open_tqt_rec K (typ_fvar X) T) = size_qtyp T.
Proof.
  - destruct T as [| |n|a|T1 T2|T1 T2|Q T1|T1 T2|T1 T2|T1]; intros K X; simpl.
    + reflexivity.
    + reflexivity.
    + destruct (eq_dec K n); simpl; reflexivity.
    + reflexivity.
    + rewrite (size_open_tqt T1 K X). rewrite (size_open_tqt T2 (S K) X). reflexivity.
    + rewrite (size_open_tt T1 K X). rewrite (size_open_tqt T2 (S K) X). reflexivity.
    + rewrite (size_open_tqt T1 (S K) X). reflexivity.
    + rewrite (size_open_tqt T1 K X). rewrite (size_open_tqt T2 K X). reflexivity.
    + rewrite (size_open_tqt T1 K X). rewrite (size_open_tqt T2 K X). reflexivity.
    + rewrite (size_open_tqt T1 K X). reflexivity.
  - destruct T as [Q T]. intros K X. simpl.
    rewrite (size_open_tt T K X). reflexivity.
Qed.

Fixpoint size_open_qq (Q:qua) {struct Q} :
  forall K X, size_qua (open_qq_rec K (qua_fvar X) Q) = size_qua Q.
Proof.
  destruct Q as [b|n|a|Q1 Q2|Q1 Q2|Q1]; intros K X; simpl.
  - reflexivity.
  - destruct (eq_dec K n); simpl; reflexivity.
  - reflexivity.
  - rewrite (size_open_qq Q1 K X). rewrite (size_open_qq Q2 K X). reflexivity.
  - rewrite (size_open_qq Q1 K X). rewrite (size_open_qq Q2 K X). reflexivity.
  - rewrite (size_open_qq Q1 K X). reflexivity.
Qed.

Fixpoint size_open_qt (T:typ) {struct T} :
  forall K X, size_typ (open_qt_rec K (qua_fvar X) T) = size_typ T
with size_open_qqt (T:qtyp) {struct T} :
  forall K X, size_qtyp (open_qqt_rec K (qua_fvar X) T) = size_qtyp T.
Proof.
  - destruct T as [| |n|a|T1 T2|T1 T2|Q T1|T1 T2|T1 T2|T1]; intros K X; simpl.
    + reflexivity. + reflexivity. + reflexivity. + reflexivity.
    + rewrite (size_open_qqt T1 K X). rewrite (size_open_qqt T2 (S K) X). reflexivity.
    + rewrite (size_open_qt T1 K X). rewrite (size_open_qqt T2 (S K) X). reflexivity.
    + rewrite (size_open_qq Q K X). rewrite (size_open_qqt T1 (S K) X). reflexivity.
    + rewrite (size_open_qqt T1 K X). rewrite (size_open_qqt T2 K X). reflexivity.
    + rewrite (size_open_qqt T1 K X). rewrite (size_open_qqt T2 K X). reflexivity.
    + rewrite (size_open_qqt T1 K X). reflexivity.
  - destruct T as [Q T]. intros K X. simpl.
    rewrite (size_open_qq Q K X). rewrite (size_open_qt T K X). reflexivity.
Qed.



(* Membership survives payload change of the bind_sub at X when the queried name differs. *)
Lemma binds_sub_narrow_neq : forall (E1:env) X (U U':typ) (E2:env) Z W,
  Z <> X -> binds Z (bind_sub W) (E1 ++ X ~ bind_sub U ++ E2) ->
  binds Z (bind_sub W) (E1 ++ X ~ bind_sub U' ++ E2).
Proof.
  intros E1 X U U' E2 Z W Hne H. unfold binds in *.
  apply in_app_iff in H. destruct H as [H|H].
  - apply in_app_iff. left; auto.
  - simpl in H. destruct H as [Heq|H].
    + inversion Heq; subst. exfalso; apply Hne; reflexivity.
    + apply in_app_iff. right. simpl. right; auto.
Qed.

Lemma binds_sub_head_bind : forall (E1:env) X (U:typ) (E2:env),
  binds X (bind_sub U) (E1 ++ X ~ bind_sub U ++ E2).
Proof. intros. unfold binds. apply in_app_iff. right. simpl. left. reflexivity. Qed.

(* Restricted bind_sub narrowing, parameterized by transitivity at the old payload. *)
Lemma narrow_sub_bind_tq :
  (forall (E:env) (S T:typ), sub E S T ->
     forall (U:typ), trans_on_typ U ->
     forall (E1:env) X (U':typ) (E2:env),
       E = E1 ++ X ~ bind_sub U ++ E2 ->
       sub E2 U' U ->
       sub (E1 ++ X ~ bind_sub U' ++ E2) S T) /\
  (forall (E:env) (S T:qtyp), subqtype E S T ->
     forall (U:typ), trans_on_typ U ->
     forall (E1:env) X (U':typ) (E2:env),
       E = E1 ++ X ~ bind_sub U ++ E2 ->
       sub E2 U' U ->
       subqtype (E1 ++ X ~ bind_sub U' ++ E2) S T).
Proof.
  apply sub_tq_mut
    with (P := fun E S T _ => forall (U:typ), trans_on_typ U ->
             forall (E1:env) X (U':typ) (E2:env),
               E = E1 ++ X ~ bind_sub U ++ E2 ->
               sub E2 U' U ->
               sub (E1 ++ X ~ bind_sub U' ++ E2) S T)
         (P0 := fun E S T _ => forall (U:typ), trans_on_typ U ->
             forall (E1:env) X (U':typ) (E2:env),
               E = E1 ++ X ~ bind_sub U ++ E2 ->
               sub E2 U' U ->
               subqtype (E1 ++ X ~ bind_sub U' ++ E2) S T).
  - (* sub_top *) intros E S Hwf HS U HT E1 X U' E2 HE Hsub; subst E.
    eapply sub_top.
    + eapply wf_env_change_sub_mid; [exact Hwf |].
      destruct (sub_wf _ _ _ Hsub) as [_ [HU'w _]]; exact HU'w.
    + eapply wf_typ_sim.
      * apply env_sim_change_sub_mid.
      * exact HS.
  - (* sub_refl_int *) intros E Hwf U HT E1 X U' E2 HE Hsub; subst E.
    apply sub_refl_int.
    eapply wf_env_change_sub_mid; [exact Hwf |].
    destruct (sub_wf _ _ _ Hsub) as [_ [HU'w _]]; exact HU'w.
  - (* sub_refl_tvar *) intros E X Hwf HX U HT E1 X0 U' E2 HE Hsub; subst E.
    apply sub_refl_tvar.
    + eapply wf_env_change_sub_mid; [exact Hwf |].
      destruct (sub_wf _ _ _ Hsub) as [_ [HU'w _]]; exact HU'w.
    + eapply wf_typ_sim; [apply env_sim_change_sub_mid | exact HX].
  - (* sub_trans_tvar *) intros U0 E T X0 b s0 IH U HT E1 X U' E2 HE Hsub; subst E.
    destruct (eq_dec X0 X) as [Heq|Hne].
    + subst X0.
      assert (WU : U0 = U).
      { destruct (sub_wf _ _ _ s0) as [HwE _].
        assert (Hb1 : binds X (bind_sub U) (E1 ++ X ~ bind_sub U ++ E2))
          by apply binds_sub_head_bind.
        assert (Hb2 : binds X (bind_sub U0) (E1 ++ X ~ bind_sub U ++ E2)) by exact b.
        pose proof (binds_unique _ _ _ _ _ Hb2 Hb1 (wf_env_uniq _ HwE)) as HEq.
        inversion HEq; reflexivity. }
      subst U0.
      assert (Hsub' : sub E2 U' U) by exact Hsub.
      assert (Hroot : sub (E1 ++ X ~ bind_sub U' ++ E2) U' U).
      { eapply sub_extends.
        - exact Hsub.
        - apply extends_insert_mid.
        - eapply wf_env_change_sub_mid; [destruct (sub_wf _ _ _ s0) as [HwE _]; exact HwE |].
          destruct (sub_wf _ _ _ Hsub) as [_ [HU'w _]]; exact HU'w. }
      assert (Hprem : sub (E1 ++ X ~ bind_sub U' ++ E2) U T).
      { apply (IH U HT E1 X U' E2); [reflexivity | exact Hsub']. }
      (* Rebuild with binds at X of U'. *)
      eapply sub_trans_tvar.
      * apply binds_sub_head_bind.
      * apply (HT (E1 ++ X ~ bind_sub U' ++ E2) U' T Hroot Hprem).
    + eapply sub_trans_tvar with (U:=U0).
      * eapply binds_sub_narrow_neq; eauto.
      * apply (IH U HT E1 X U' E2); [reflexivity | exact Hsub].
  - (* sub_arrow *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2 U HT E1 X U' E2 HE Hsub; subst E.
    eapply sub_arrow.
    + apply (IH1 U HT E1 X U' E2). reflexivity. exact Hsub.
    + apply (IH2 U HT E1 X U' E2). reflexivity. exact Hsub.
  - (* sub_all *) intros L E S1 S2 T1 T2 s1 IH1 s2 IH2 U HT E1 X U' E2 HE Hsub; subst E.
    eapply sub_all.
    + apply (IH1 U HT E1 X U' E2). reflexivity. exact Hsub.
    + intros Y HY.
      eapply (IH2 Y HY U HT (Y ~ bind_sub T1 ++ E1) X U' E2).
      * rewrite app_assoc. reflexivity.
      * exact Hsub.
  - (* sub_qall *) intros L E S1 S2 T1 T2 s1 s2 IH2 U HT E1 X U' E2 HE Hsub; subst E.
    eapply sub_qall.
    + eapply subqual_narrow_sub_gen2; [exact s1 | reflexivity | exact Hsub].
    + intros Y HY.
      eapply (IH2 Y HY U HT (Y ~ bind_qua T1 ++ E1) X U' E2).
      * rewrite app_assoc. reflexivity.
      * exact Hsub.
  - (* sub_sum *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2 U HT E1 X U' E2 HE Hsub; subst E.
    eapply sub_sum.
    + apply (IH1 U HT E1 X U' E2). reflexivity. exact Hsub.
    + apply (IH2 U HT E1 X U' E2). reflexivity. exact Hsub.
  - (* sub_pair *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2 U HT E1 X U' E2 HE Hsub; subst E.
    eapply sub_pair.
    + apply (IH1 U HT E1 X U' E2). reflexivity. exact Hsub.
    + apply (IH2 U HT E1 X U' E2). reflexivity. exact Hsub.
  - (* subqtype_qtyp *) intros E Q1 T1 Q2 T2 s1 s2 IH U HT E1 X U' E2 HE Hsub; subst E.
    eapply sub_qtyp_qtyp.
    + eapply subqual_narrow_sub_gen2; [exact s1 | reflexivity | exact Hsub].
    + apply (IH U HT E1 X U' E2). reflexivity. exact Hsub.
Qed.

Lemma wf_typ_all_build : forall L E S1 S2 T1 T2,
  sub E T1 S1 ->
  (forall X, X `notin` L -> subqtype (X ~ bind_sub T1 ++ E) (open_tqt S2 X) (open_tqt T2 X)) ->
  wf_typ E (typ_all S1 S2).
Proof.
  intros L E S1 S2 T1 T2 Hs Hq.
  destruct (sub_wf _ _ _ Hs) as [Hwf [_ HS1]].
  apply wf_typ_all with (L:=L).
  - exact HS1.
  - intros X HX.
    destruct (subqtype_wf _ _ _ (Hq X HX)) as [_ [HqS _]].
    eapply wf_qtyp_bind_sub_irrel; eauto.
Qed.

Lemma wf_typ_qall_build : forall L E S1 S2 T1 T2,
  subqual E T1 S1 ->
  (forall X, X `notin` L -> subqtype (X ~ bind_qua T1 ++ E) (open_qqt S2 X) (open_qqt T2 X)) ->
  wf_typ E (typ_qall S1 S2).
Proof.
  intros L E S1 S2 T1 T2 Hs Hq.
  destruct (subqual_wf _ _ _ Hs) as [Hwf [HT1 HS1]].
  apply wf_typ_qall with (L:=L).
  - exact HS1.
  - intros X HX.
    destruct (subqtype_wf _ _ _ (Hq X HX)) as [_ [HqS _]].
    eapply wf_qtyp_bind_qua_irrel; eauto.
Qed.

Lemma trans_size : forall n,
  (forall (E:env) (S T:typ), sub E S T -> size_typ T <= n ->
     forall U, sub E T U -> sub E S U) /\
  (forall (E:env) (S T:qtyp), subqtype E S T -> size_qtyp T <= n ->
     forall U, subqtype E T U -> subqtype E S U).
Proof.
  induction n as [n IH] using lt_wf_ind.
  assert (Hall :
    (forall (E:env) (S T:typ), sub E S T -> size_typ T <= n ->
       forall U, sub E T U -> sub E S U) /\
    (forall (E:env) (S T:qtyp), subqtype E S T -> size_qtyp T <= n ->
       forall U, subqtype E T U -> subqtype E S U)).
  { apply (sub_tq_mut
      (fun E S T _ => size_typ T <= n -> forall U, sub E T U -> sub E S U)
      (fun E S T _ => size_qtyp T <= n -> forall U, subqtype E T U -> subqtype E S U)).
    + (* sub_top *) intros E0 S0 Hwf HS0 HT U h2.
      inversion h2; subst. apply sub_top; assumption.
    + (* sub_refl_int *) intros E0 Hwf HT U h2.
      destruct (sub_int_inv _ _ h2) as [-> | ->].
      * apply sub_refl_int; assumption.
      * apply sub_top; [assumption|apply wf_typ_int].
    + (* sub_refl_tvar *) intros E0 X Hwf HX HT U h2.
      destruct (sub_tvar_inv _ _ _ h2) as [-> | [[-> _] | [U0 [Hb Hs]]]].
      * apply sub_top; [assumption|exact HX].
      * apply sub_refl_tvar; assumption.
      * eapply sub_trans_tvar; eauto.
    + (* sub_trans_tvar *) intros U0 E0 T0 X0 b s0 IH0 HT U h2.
      eapply sub_trans_tvar; [exact b | apply (IH0 HT U h2)].
    + (* sub_arrow *) intros E0 S1 S2 T1 T2 s1 IH1 s2 IH2 HT U h2.
      destruct (sub_arrow_inv _ _ _ _ h2) as [-> | [U1 [U2 [-> [hC hD]]]]].
      * apply sub_top.
        -- destruct (subqtype_wf _ _ _ s1) as [Hwf _]. exact Hwf.
        -- apply wf_typ_arrow.
           ++ destruct (subqtype_wf _ _ _ s1) as [_ [_ HS1]]. exact HS1.
           ++ destruct (subqtype_wf _ _ _ s2) as [_ [HS2 _]]. exact HS2.
      * eapply sub_arrow.
        -- (* U1 <: S1, middle T1 *)
           assert (Hlt : size_qtyp T1 < n) by (simpl in HT; lia).
           exact (proj2 (IH (size_qtyp T1) Hlt) E0 U1 T1 hC (Nat.le_refl _) S1 s1).
        -- (* S2 <: U2, middle T2 *)
           assert (Hlt : size_qtyp T2 < n) by (simpl in HT; lia).
           exact (proj2 (IH (size_qtyp T2) Hlt) E0 S2 T2 s2 (Nat.le_refl _) U2 hD).
    + (* sub_all *) intros L E0 S1 S2 T1 T2 s1 IH1 s2 IH2 HT U h2.
      destruct (sub_all_inv _ _ _ _ h2) as [-> | [L' [U1 [U2 [-> [hC hD]]]]]].
      * apply sub_top.
        -- destruct (sub_wf _ _ _ s1) as [Hwf _]. exact Hwf.
        -- eapply wf_typ_all_build; eauto.
      * eapply sub_all with (L := L \u L').
        -- (* U1 <: S1, middle T1 *)
           assert (Hlt : size_typ T1 < n) by (simpl in HT; lia).
           exact (proj1 (IH (size_typ T1) Hlt) E0 U1 T1 hC (Nat.le_refl _) S1 s1).
        -- intros X HX.
           apply notin_union_1 in HX as HXL.
           apply notin_union_2 in HX as HXL'.
           (* narrow h1 binder premise from T1 to U1 *)
           assert (HT1 : trans_on_typ T1).
           { assert (Hlt : size_typ T1 < n) by (simpl in HT; lia).
             intros E' S' U' h1' h2'.
             exact (proj1 (IH (size_typ T1) Hlt) E' S' T1 h1' (Nat.le_refl _) U' h2'). }
           assert (Hnarrow : subqtype (X ~ bind_sub U1 ++ E0) (open_tqt S2 X) (open_tqt T2 X)).
           { eapply (proj2 narrow_sub_bind_tq
                       (X ~ bind_sub T1 ++ E0) (open_tqt S2 X) (open_tqt T2 X)
                       (s2 X HXL) T1 HT1 (@nil (atom*binding)) X U1 E0).
             - reflexivity.
             - exact hC. }
           (* trans at middle open T2 X *)
           assert (Hlt : size_qtyp (open_tqt T2 X) < n).
           { unfold open_tqt. rewrite (size_open_tqt T2 0 X). simpl in HT. lia. }
           exact (proj2 (IH (size_qtyp (open_tqt T2 X)) Hlt)
                    (X ~ bind_sub U1 ++ E0) (open_tqt S2 X) (open_tqt T2 X)
                    Hnarrow (Nat.le_refl _) (open_tqt U2 X) (hD X HXL')).
    + (* sub_qall *) intros L E0 S1 S2 T1 T2 s1 s2 IH2 HT U h2.
      destruct (sub_qall_inv _ _ _ _ h2) as [-> | [L' [U1 [U2 [-> [hC hD]]]]]].
      * apply sub_top.
        -- destruct (subqual_wf _ _ _ s1) as [Hwf _]. exact Hwf.
        -- eapply wf_typ_qall_build; eauto.
      * eapply sub_qall with (L := L \u L').
        -- apply (subqual_trans E0 U1 T1 S1 hC s1).
        -- intros X HX.
           apply notin_union_1 in HX as HXL.
           apply notin_union_2 in HX as HXL'.
           assert (Hnarrow : subqtype (X ~ bind_qua U1 ++ E0) (open_qqt S2 X) (open_qqt T2 X)).
           { eapply (proj2 sub_subqtype_narrow_qua_gen2
                       (X ~ bind_qua T1 ++ E0) (open_qqt S2 X) (open_qqt T2 X)
                       (s2 X HXL) (@nil (atom*binding)) X T1 U1 E0).
             - reflexivity.
             - exact hC. }
           assert (Hlt : size_qtyp (open_qqt T2 X) < n).
           { unfold open_qqt. rewrite (size_open_qqt T2 0 X). simpl in HT. lia. }
           exact (proj2 (IH (size_qtyp (open_qqt T2 X)) Hlt)
                    (X ~ bind_qua U1 ++ E0) (open_qqt S2 X) (open_qqt T2 X)
                    Hnarrow (Nat.le_refl _) (open_qqt U2 X) (hD X HXL')).
    + (* sub_sum *) intros E0 S1 S2 T1 T2 s1 IH1 s2 IH2 HT U h2.
      destruct (sub_sum_inv _ _ _ _ h2) as [-> | [U1 [U2 [-> [hC hD]]]]].
      * apply sub_top.
        -- destruct (subqtype_wf _ _ _ s1) as [Hwf _]. exact Hwf.
        -- apply wf_typ_sum.
           ++ destruct (subqtype_wf _ _ _ s1) as [_ [HS1 _]]. exact HS1.
           ++ destruct (subqtype_wf _ _ _ s2) as [_ [HS2 _]]. exact HS2.
      * eapply sub_sum.
        -- assert (Hlt : size_qtyp T1 < n) by (simpl in HT; lia).
           exact (proj2 (IH (size_qtyp T1) Hlt) E0 S1 T1 s1 (Nat.le_refl _) U1 hC).
        -- assert (Hlt : size_qtyp T2 < n) by (simpl in HT; lia).
           exact (proj2 (IH (size_qtyp T2) Hlt) E0 S2 T2 s2 (Nat.le_refl _) U2 hD).
    + (* sub_pair *) intros E0 S1 S2 T1 T2 s1 IH1 s2 IH2 HT U h2.
      destruct (sub_pair_inv _ _ _ _ h2) as [-> | [U1 [U2 [-> [hC hD]]]]].
      * apply sub_top.
        -- destruct (subqtype_wf _ _ _ s1) as [Hwf _]. exact Hwf.
        -- apply wf_typ_pair.
           ++ destruct (subqtype_wf _ _ _ s1) as [_ [HS1 _]]. exact HS1.
           ++ destruct (subqtype_wf _ _ _ s2) as [_ [HS2 _]]. exact HS2.
      * eapply sub_pair.
        -- assert (Hlt : size_qtyp T1 < n) by (simpl in HT; lia).
           exact (proj2 (IH (size_qtyp T1) Hlt) E0 S1 T1 s1 (Nat.le_refl _) U1 hC).
        -- assert (Hlt : size_qtyp T2 < n) by (simpl in HT; lia).
           exact (proj2 (IH (size_qtyp T2) Hlt) E0 S2 T2 s2 (Nat.le_refl _) U2 hD).
    + (* subqtype_qtyp *) intros E0 Q1 T1 Q2 T2 s1 s2 IH2 HT U h2.
      destruct (subqtype_inv _ _ _ _ h2) as [Q2' [T2' [-> [hC hD]]]].
      eapply sub_qtyp_qtyp.
      * apply (subqual_trans E0 Q1 Q2 Q2' s1 hC).
      * assert (Hlt : size_typ T2 < n) by (simpl in HT; lia).
        exact (proj1 (IH (size_typ T2) Hlt) E0 T1 T2 s2 (Nat.le_refl _) T2' hD).
    }
  destruct Hall as [H1 H2]. split; [exact H1 | exact H2].
Qed.

(* ========================================================= *)
(* Public transitivity of sub and subqtype                    *)
(* ========================================================= *)

Lemma sub_trans : forall E S T U, sub E S T -> sub E T U -> sub E S U.
Proof.
  intros E S T U HST HTU.
  exact (proj1 (trans_size (size_typ T)) E S T HST (Nat.le_refl _) U HTU).
Qed.

Lemma subqtype_trans : forall E S T U, subqtype E S T -> subqtype E T U -> subqtype E S U.
Proof.
  intros E S T U HST HTU.
  exact (proj2 (trans_size (size_qtyp T)) E S T HST (Nat.le_refl _) U HTU).
Qed.


(* ================= ChunkSubQe.v ================= *)

Definition env_free_qe (X:atom) (E:env) : Prop :=
  (forall Y T, binds Y (bind_typ T) E -> X `notin` fv_qqt T) /\
  (forall Y W, binds Y (bind_sub W) E -> X `notin` fv_qt W) /\
  (forall Y Q, binds Y (bind_qua Q) E -> X `notin` fv_qq Q).

(* ---------- commutation: qualifier opening vs qe-substitution ---------- *)

(* qe-substitution commutes with type-opening (open_tt/open_te) and expression-opening open_ee *)

Fixpoint subst_qt_open_tt_rec (T:typ) {struct T} :
  forall K U X R,
    subst_qt X R (open_tt_rec K U T) =
    open_tt_rec K (subst_qt X R U) (subst_qt X R T)
with subst_qqt_open_tqt_rec (T:qtyp) {struct T} :
  forall K U X R,
    subst_qqt X R (open_tqt_rec K U T) =
    open_tqt_rec K (subst_qt X R U) (subst_qqt X R T).
Proof.
  - destruct T; intros K U X R; simpl; try reflexivity.
    all: try (destruct (eq_dec K n) as [Heq|Hneq]; simpl; reflexivity).
    all: try (f_equal; try (apply (subst_qqt_open_tqt_rec _ _ U X R));
              try (apply (subst_qt_open_tt_rec _ _ U X R)); try reflexivity).
    all: try reflexivity.
  - destruct T as [Q T]. intros K U X R. simpl. f_equal.
    apply (subst_qt_open_tt_rec T K U X R).
Qed.

Fixpoint subst_qe_open_te_rec (e:exp) {struct e} :
  forall K U X R,
    subst_qe X R (open_te_rec K U e) =
    open_te_rec K (subst_qt X R U) (subst_qe X R e).
Proof.
  destruct e as [P i|i|a|P V e1|e1 e2|P V e1|e1 V|P Q e1|e1 Q|e1 e2|P e1|P e1|e1 e2 e3|P e1 e2|e1|e1|P e1|P l|e1|e1 e2|P e1|P e1|P e1|b|e1 e2 e3];
    intros K U X R; simpl; try reflexivity.
  all: try (f_equal; try (apply (subst_qqt_open_tqt_rec _ _ U X R));
            try (apply (subst_qt_open_tt_rec _ _ U X R));
            try (apply (subst_qe_open_te_rec _ _ U X R)); try reflexivity).
  all: try reflexivity.
Qed.

Fixpoint subst_qe_open_ee_rec (e:exp) {struct e} :
  forall K f X R,
    subst_qe X R (open_ee_rec K f e) =
    open_ee_rec K (subst_qe X R f) (subst_qe X R e).
Proof.
  destruct e as [P i|i|a|P V e1|e1 e2|P V e1|e1 V|P Q e1|e1 Q|e1 e2|P e1|P e1|e1 e2 e3|P e1 e2|e1|e1|P e1|P l|e1|e1 e2|P e1|P e1|P e1|b|e1 e2 e3];
    intros K f0 X R; simpl.
  - reflexivity.
  - destruct (eq_dec K i) as [Heq|Hneq]; simpl; reflexivity.
  - reflexivity.
  - f_equal. apply (subst_qe_open_ee_rec _ (S K) f0 X R).
  - f_equal; [apply (subst_qe_open_ee_rec _ K f0 X R)
            |apply (subst_qe_open_ee_rec _ K f0 X R)].
  - f_equal. apply (subst_qe_open_ee_rec _ (S K) f0 X R).
  - f_equal. apply (subst_qe_open_ee_rec _ K f0 X R).
  - f_equal. apply (subst_qe_open_ee_rec _ (S K) f0 X R).
  - f_equal. apply (subst_qe_open_ee_rec _ K f0 X R).
  - f_equal; [apply (subst_qe_open_ee_rec _ K f0 X R)
            |apply (subst_qe_open_ee_rec _ (S K) f0 X R)].
  - f_equal. apply (subst_qe_open_ee_rec _ K f0 X R).
  - f_equal. apply (subst_qe_open_ee_rec _ K f0 X R).
  - f_equal; [apply (subst_qe_open_ee_rec _ K f0 X R)
            |apply (subst_qe_open_ee_rec _ (S K) f0 X R)
            |apply (subst_qe_open_ee_rec _ (S K) f0 X R)].
  - f_equal; [apply (subst_qe_open_ee_rec _ K f0 X R)
            |apply (subst_qe_open_ee_rec _ K f0 X R)].
  - f_equal. apply (subst_qe_open_ee_rec _ K f0 X R).
  - f_equal. apply (subst_qe_open_ee_rec _ K f0 X R).
  - f_equal. apply (subst_qe_open_ee_rec _ K f0 X R).
  - reflexivity.
  - f_equal. apply (subst_qe_open_ee_rec _ K f0 X R).
  - f_equal; [apply (subst_qe_open_ee_rec _ K f0 X R)
            |apply (subst_qe_open_ee_rec _ K f0 X R)].
  - f_equal. apply (subst_qe_open_ee_rec _ K f0 X R).
  - f_equal. apply (subst_qe_open_ee_rec _ K f0 X R).
  - f_equal. apply (subst_qe_open_ee_rec _ K f0 X R).
  - reflexivity.
  - f_equal; [apply (subst_qe_open_ee_rec _ K f0 X R)
            |apply (subst_qe_open_ee_rec _ K f0 X R)
            |apply (subst_qe_open_ee_rec _ K f0 X R)].
Qed.

Lemma subst_qqt_open_tqt_atom : forall (T:qtyp) X R (Y:atom),
  subst_qqt X R (open_tqt T (typ_fvar Y)) = open_tqt (subst_qqt X R T) (typ_fvar Y).
Proof.
  intros. unfold open_tqt.
  rewrite (subst_qqt_open_tqt_rec T 0 (typ_fvar Y) X R). simpl. reflexivity.
Qed.

Lemma binds_remove_qua_mid : forall (E1:env) X (Q0:qua) (E2:env) z b,
  b <> bind_qua Q0 -> binds z b (E1 ++ X ~ bind_qua Q0 ++ E2) -> binds z b (E1 ++ E2).
Proof.
  intros E1 X Q0 E2 z b Hne H. unfold binds in *.
  apply in_app_iff. apply in_app_iff in H. destruct H as [H|H].
  - left; auto.
  - simpl in H. destruct H as [Heq|H].
    + inversion Heq; subst. exfalso; apply Hne; reflexivity.
    + right; auto.
Qed.

Lemma binds_remove_qua_neq_name : forall (E1:env) X (Q0:qua) (E2:env) z b,
  z <> X -> binds z b (E1 ++ X ~ bind_qua Q0 ++ E2) -> binds z b (E1 ++ E2).
Proof.
  intros E1 X Q0 E2 z b Hne H. unfold binds in *.
  apply in_app_iff. apply in_app_iff in H. destruct H as [H|H].
  - left; auto.
  - simpl in H. destruct H as [Heq|H].
    + inversion Heq; subst. exfalso; apply Hne; reflexivity.
    + right; auto.
Qed.

Fixpoint wf_qua_subst_qe (Q:qua) {struct Q} :
  forall (E1:env) X (Q0:qua) (E2:env) R,
    wf_qua (E1 ++ X ~ bind_qua Q0 ++ E2) Q ->
    wf_qua (E1 ++ E2) R ->
    wf_qua (E1 ++ E2) (subst_qq X R Q).
Proof.
  destruct Q as [b|n|a|Q1 Q2|Q1 Q2|Q1]; intros E1 X Q0 E2 R H HR; simpl.
  - apply wf_qua_base.
  - inversion H.
  - inversion H; subst. destruct (eq_dec a X) as [Heq|Hneq].
    + subst. exact HR.
    + eapply wf_qua_fvar.
      match goal with
      | Hb : binds a (bind_qua ?Qb) (E1 ++ X ~ bind_qua Q0 ++ E2) |- _ =>
          eapply binds_remove_qua_neq_name; [exact Hneq | exact Hb]
      end.
  - inversion H; subst. apply wf_qua_meet.
    + apply (wf_qua_subst_qe Q1 E1 X Q0 E2 R); assumption.
    + apply (wf_qua_subst_qe Q2 E1 X Q0 E2 R); assumption.
  - inversion H; subst. apply wf_qua_join.
    + apply (wf_qua_subst_qe Q1 E1 X Q0 E2 R); assumption.
    + apply (wf_qua_subst_qe Q2 E1 X Q0 E2 R); assumption.
  - inversion H; subst. apply wf_qua_negate.
    apply (wf_qua_subst_qe Q1 E1 X Q0 E2 R); assumption.
Qed.

Lemma wf_tq_subst_qe :
  (forall (E:env) (T:typ), wf_typ E T ->
     forall (E1:env) X (Q0:qua) (E2:env) R,
       E = E1 ++ X ~ bind_qua Q0 ++ E2 ->
       wf_qua (E1 ++ E2) R ->
       wf_typ (E1 ++ E2) (subst_qt X R T)) /\
  (forall (E:env) (T:qtyp), wf_qtyp E T ->
     forall (E1:env) X (Q0:qua) (E2:env) R,
       E = E1 ++ X ~ bind_qua Q0 ++ E2 ->
       wf_qua (E1 ++ E2) R ->
       wf_qtyp (E1 ++ E2) (subst_qqt X R T)).
Proof.
  apply wf_tq_mut
    with (P := fun E T _ => forall (E1:env) X (Q0:qua) (E2:env) R,
              E = E1 ++ X ~ bind_qua Q0 ++ E2 ->
              wf_qua (E1 ++ E2) R ->
              wf_typ (E1 ++ E2) (subst_qt X R T))
         (P0 := fun E T _ => forall (E1:env) X (Q0:qua) (E2:env) R,
              E = E1 ++ X ~ bind_qua Q0 ++ E2 ->
              wf_qua (E1 ++ E2) R ->
              wf_qtyp (E1 ++ E2) (subst_qqt X R T)).
  - intros E E1 X Q0 E2 R HE HR. subst. constructor.
  - intros E E1 X Q0 E2 R HE HR. subst. constructor.
  - intros U E X0 b E1 X Q0 E2 R HE HR. subst.
    simpl. eapply wf_typ_var.
    eapply binds_remove_qua_mid; [|exact b].
    intros Heq; inversion Heq.
  - intros E T1 T2 w1 IH1 w2 IH2 E1 X Q0 E2 R HE HR. subst.
    simpl. apply wf_typ_arrow.
    + apply (IH1 E1 X Q0 E2 R); [reflexivity|exact HR].
    + apply (IH2 E1 X Q0 E2 R); [reflexivity|exact HR].
  - intros L E T1 T2 w1 IH1 w0 IH0 E1 XX Q0 E2 R HE HR. subst.
    simpl. apply wf_typ_all with (L := L \u singleton XX \u dom (E1++E2)).
    + apply (IH1 E1 XX Q0 E2 R); [reflexivity|exact HR].
    + intros Z HZ.
      assert (HZL : Z `notin` L) by (apply notin_union_1 in HZ; exact HZ).
      pose proof (IH0 Z HZL (Z ~ bind_sub T1 ++ E1) XX Q0 E2 R) as Hq.
      rewrite app_assoc in Hq.
      assert (HR' : wf_qua ((Z ~ bind_sub T1 ++ E1) ++ E2) R).
      { rewrite app_assoc. eapply wf_qua_extends; [|exact HR]. apply extends_app_l. }
      specialize (Hq eq_refl HR').
      rewrite (subst_qqt_open_tqt_atom T2 XX R Z) in Hq.
      simpl in Hq.
      eapply wf_qtyp_sim.
      * apply sim_cons; [apply sk_sub|apply env_sim_refl].
      * exact Hq.
  - intros L E Q T wq w0 IH0 E1 XX Q0 E2 R HE HR. subst.
    simpl. apply wf_typ_qall with (L := L \u singleton XX \u dom (E1++E2)).
    + apply (wf_qua_subst_qe Q E1 XX Q0 E2 R); [exact wq|exact HR].
    + intros Z HZ.
      assert (HZL : Z `notin` L) by (apply notin_union_1 in HZ; exact HZ).
      pose proof (IH0 Z HZL (Z ~ bind_qua Q ++ E1) XX Q0 E2 R) as Hq.
      rewrite app_assoc in Hq.
      assert (HR' : wf_qua ((Z ~ bind_qua Q ++ E1) ++ E2) R).
      { rewrite app_assoc. eapply wf_qua_extends; [|exact HR]. apply extends_app_l. }
      specialize (Hq eq_refl HR').
      pose proof (wf_qua_closed_qq (E1++E2) R HR) as HcR.
      assert (HZsing : Z `notin` singleton XX).
      { apply notin_union_2 in HZ. apply notin_union_1 in HZ. exact HZ. }
      assert (HZne : Z <> XX) by (symmetry; exact (notin_singleton_1 XX Z HZsing)).
      rewrite (subst_qqt_open_qqt_atom T XX R Z HcR HZne) in Hq.
      simpl in Hq.
      eapply wf_qtyp_sim.
      * apply sim_cons; [apply sk_qua|apply env_sim_refl].
      * exact Hq.
  - intros E T1 T2 w1 IH1 w2 IH2 E1 X Q0 E2 R HE HR. subst.
    simpl. apply wf_typ_sum.
    + apply (IH1 E1 X Q0 E2 R); [reflexivity|exact HR].
    + apply (IH2 E1 X Q0 E2 R); [reflexivity|exact HR].
  - intros E T1 T2 w1 IH1 w2 IH2 E1 X Q0 E2 R HE HR. subst.
    simpl. apply wf_typ_pair.
    + apply (IH1 E1 X Q0 E2 R); [reflexivity|exact HR].
    + apply (IH2 E1 X Q0 E2 R); [reflexivity|exact HR].
  - intros E Q T wq wT IHT E1 X Q0 E2 R HE HR. subst.
    simpl. apply wf_qtyp_qtyp.
    + apply (wf_qua_subst_qe Q E1 X Q0 E2 R); [exact wq|exact HR].
    + apply (IHT E1 X Q0 E2 R); [reflexivity|exact HR].
Qed.

(* ================= ChunkTeSubst.v ================= *)

(* ========================================================= *)
(* Type-variable substitution on environments                *)
(* ========================================================= *)

Fixpoint subst_te_env (Z:atom) (U:typ) (E:env) : env :=
  match E with
  | nil => nil
  | (y, bind_typ T) :: E' =>
      (y, bind_typ (subst_tqt Z U T)) :: subst_te_env Z U E'
  | (y, bind_sub T) :: E' =>
      (y, bind_sub (subst_tt Z U T)) :: subst_te_env Z U E'
  | (y, bind_qua Q) :: E' =>
      (y, bind_qua Q) :: subst_te_env Z U E'
  end.

Lemma subst_te_env_app : forall (E1 E2:env) X V,
  subst_te_env X V (E1 ++ E2) =
  subst_te_env X V E1 ++ subst_te_env X V E2.
Proof.
  induction E1 as [|[y b] E1 IH]; intros E2 X V; simpl.
  - reflexivity.
  - destruct b; simpl; rewrite IH; reflexivity.
Qed.

Lemma subst_te_env_cons : forall (y:atom) b (E:env) X V,
  subst_te_env X V ((y,b) :: E) =
  (y, subst_tb X V b) :: subst_te_env X V E.
Proof. intros. destruct b; reflexivity. Qed.

Lemma in_dom_app_iff : forall (E1 E2:env) x,
  x `in` dom (E1 ++ E2) <-> x `in` dom E1 \/ x `in` dom E2.
Proof.
  intros E1 E2 x. split.
  - intro H. apply binds_In_inv in H as [b Hb].
    apply binds_app_1 in Hb as [Hb|Hb]; [left|right];
      exact (binds_In _ x b _ Hb).
  - intros [H|H]; apply binds_In_inv in H as [b Hb].
    + exact (binds_In _ x b _ (binds_app_2 _ _ _ _ _ Hb)).
    + exact (binds_In _ x b _ (binds_app_3 _ _ _ _ _ Hb)).
Qed.

Lemma notin_dom_app_l : forall (E1 E2:env) x,
  x `notin` dom (E1 ++ E2) -> x `notin` dom E1.
Proof. intros E1 E2 x H Hc. apply H. apply in_dom_app_iff. left. exact Hc. Qed.

Lemma notin_dom_app_r : forall (E1 E2:env) x,
  x `notin` dom (E1 ++ E2) -> x `notin` dom E2.
Proof. intros E1 E2 x H Hc. apply H. apply in_dom_app_iff. right. exact Hc. Qed.

Lemma in_dom_subst_te_env_iff : forall (E:env) X V x,
  x `in` dom (subst_te_env X V E) <-> x `in` dom E.
Proof.
  induction E as [|[y b] E IH]; intros X V x; simpl.
  - split; intro H; exact H.
  - destruct b; simpl; rewrite add_iff; rewrite IH; rewrite add_iff; tauto.
Qed.

Lemma notin_dom_subst_te_env : forall (E:env) X V x,
  x `notin` dom (subst_te_env X V E) <-> x `notin` dom E.
Proof.
  intros E X V x. split; intro H; intro Hc; apply H.
  - exact (proj2 (in_dom_subst_te_env_iff E X V x) Hc).
  - exact (proj1 (in_dom_subst_te_env_iff E X V x) Hc).
Qed.

(* ========================================================= *)
(* Membership of bindings in substituted environments         *)
(* ========================================================= *)

Lemma binds_subst_te_env : forall (E:env) z b X V,
  binds z b E -> binds z (subst_tb X V b) (subst_te_env X V E).
Proof.
  induction E as [|[y c] E IH]; intros z b X V H.
  - unfold binds in H; destruct H.
  - destruct c; simpl in *.
    + unfold binds in H. simpl in H. destruct H as [Heq|H].
      * left; inversion Heq; subst; reflexivity.
      * right; apply IH; exact H.
    + unfold binds in H. simpl in H. destruct H as [Heq|H].
      * left; inversion Heq; subst; reflexivity.
      * right; apply IH; exact H.
    + unfold binds in H. simpl in H. destruct H as [Heq|H].
      * left; inversion Heq; subst; reflexivity.
      * right; apply IH; exact H.
Qed.

Lemma binds_sub_subst_te : forall (E:env) z U X V,
  binds z (bind_sub U) E ->
  binds z (bind_sub (subst_tt X V U)) (subst_te_env X V E).
Proof. intros. change (binds z (subst_tb X V (bind_sub U)) (subst_te_env X V E)). apply binds_subst_te_env. exact H. Qed.

Lemma binds_typ_subst_te : forall (E:env) z T X V,
  binds z (bind_typ T) E ->
  binds z (bind_typ (subst_tqt X V T)) (subst_te_env X V E).
Proof. intros. change (binds z (subst_tb X V (bind_typ T)) (subst_te_env X V E)). apply binds_subst_te_env. exact H. Qed.

Lemma binds_qua_subst_te : forall (E:env) z Q X V,
  binds z (bind_qua Q) E ->
  binds z (bind_qua Q) (subst_te_env X V E).
Proof. intros. change (binds z (subst_tb X V (bind_qua Q)) (subst_te_env X V E)). apply binds_subst_te_env. exact H. Qed.

Lemma binds_typ_remove_sub_mid : forall (E1:env) X (U:typ) (E2:env) z T,
  binds z (bind_typ T) (E1 ++ X ~ bind_sub U ++ E2) ->
  binds z (bind_typ T) (E1 ++ E2).
Proof.
  intros E1 X U E2 z T H. unfold binds in *.
  apply in_app_iff.
  apply in_app_iff in H. destruct H as [H|H].
  - left; auto.
  - simpl in H. destruct H as [Heq|H].
    + inversion Heq; subst; discriminate.
    + right; auto.
Qed.

(* ========================================================= *)
(* fv facts for well-formed types                             *)
(* ========================================================= *)

(* Opening only adds free variables. *)
Fixpoint fv_tt_open_tt_subset (T:typ) {struct T} :
  forall K Y X, X `in` fv_tt T -> X `in` fv_tt (open_tt_rec K (typ_fvar Y) T)
with fv_tqt_open_tqt_subset (T:qtyp) {struct T} :
  forall K Y X, X `in` fv_tqt T -> X `in` fv_tqt (open_tqt_rec K (typ_fvar Y) T).
Proof.
  - destruct T as [| |n|a|T1 T2|T1 T2|Q T1|T1 T2|T1 T2|T1]; intros K Y X Hin; simpl in *.
    + exfalso; exact (notin_empty_1 X Hin).
    + exfalso; exact (notin_empty_1 X Hin).
    + destruct (eq_dec K n); simpl.
      * exfalso; exact (notin_empty_1 X Hin).
      * exact Hin.
    + simpl. exact Hin.
    + apply (proj2 (union_iff _ _ _)). destruct (proj1 (union_iff _ _ _) Hin) as [H|H];
        [left; apply (fv_tqt_open_tqt_subset T1 K Y X H)
        |right; apply (fv_tqt_open_tqt_subset T2 (S K) Y X H)].
    + apply (proj2 (union_iff _ _ _)). destruct (proj1 (union_iff _ _ _) Hin) as [H|H];
        [left; apply (fv_tt_open_tt_subset T1 K Y X H)
        |right; apply (fv_tqt_open_tqt_subset T2 (S K) Y X H)].
    + apply (fv_tqt_open_tqt_subset T1 (S K) Y X Hin).
    + apply (proj2 (union_iff _ _ _)). destruct (proj1 (union_iff _ _ _) Hin) as [H|H];
        [left; apply (fv_tqt_open_tqt_subset T1 K Y X H)
        |right; apply (fv_tqt_open_tqt_subset T2 K Y X H)].
    + apply (proj2 (union_iff _ _ _)). destruct (proj1 (union_iff _ _ _) Hin) as [H|H];
        [left; apply (fv_tqt_open_tqt_subset T1 K Y X H)
        |right; apply (fv_tqt_open_tqt_subset T2 K Y X H)].
    + apply (fv_tqt_open_tqt_subset T1 K Y X Hin).
  - destruct T as [Q T]. intros K Y X Hin. simpl in *.
    apply (fv_tt_open_tt_subset T K Y X Hin).
Qed.

(* Qualifier opening only adds qualifier free variables. *)
Fixpoint fv_qq_open_qq_subset (Q:qua) {struct Q} :
  forall K Y X, X `in` fv_qq Q -> X `in` fv_qq (open_qq_rec K (qua_fvar Y) Q).
Proof.
  destruct Q as [b|n|a|Q1 Q2|Q1 Q2|Q1]; intros K Y X Hin; simpl in *.
  - exfalso; exact (notin_empty_1 X Hin).
  - exfalso; exact (notin_empty_1 X Hin).
  - exact Hin.
  - apply (proj2 (union_iff _ _ _)). destruct (proj1 (union_iff _ _ _) Hin) as [H|H];
      [left; apply (fv_qq_open_qq_subset Q1 K Y X H)
      |right; apply (fv_qq_open_qq_subset Q2 K Y X H)].
  - apply (proj2 (union_iff _ _ _)). destruct (proj1 (union_iff _ _ _) Hin) as [H|H];
      [left; apply (fv_qq_open_qq_subset Q1 K Y X H)
      |right; apply (fv_qq_open_qq_subset Q2 K Y X H)].
  - apply (fv_qq_open_qq_subset Q1 K Y X Hin).
Qed.

(* Qualifier opening does not remove type free variables. *)
Fixpoint fv_qt_open_qt_subset (T:typ) {struct T} :
  forall K Y X, X `in` fv_qt T -> X `in` fv_qt (open_qt_rec K (qua_fvar Y) T)
with fv_qqt_open_qqt_subset (T:qtyp) {struct T} :
  forall K Y X, X `in` fv_qqt T -> X `in` fv_qqt (open_qqt_rec K (qua_fvar Y) T).
Proof.
  - destruct T as [| |n|a|T1 T2|T1 T2|Q T1|T1 T2|T1 T2|T1]; intros K Y X Hin; simpl in *.
    + exfalso; exact (notin_empty_1 X Hin).
    + exfalso; exact (notin_empty_1 X Hin).
    + exact Hin.
    + exact Hin.
    + apply (proj2 (union_iff _ _ _)). destruct (proj1 (union_iff _ _ _) Hin) as [H|H];
        [left; apply (fv_qqt_open_qqt_subset T1 K Y X H)
        |right; apply (fv_qqt_open_qqt_subset T2 (S K) Y X H)].
    + apply (proj2 (union_iff _ _ _)). destruct (proj1 (union_iff _ _ _) Hin) as [H|H];
        [left; apply (fv_qt_open_qt_subset T1 K Y X H)
        |right; apply (fv_qqt_open_qqt_subset T2 (S K) Y X H)].
    + apply (proj2 (union_iff _ _ _)). destruct (proj1 (union_iff _ _ _) Hin) as [H|H].
      * left. apply (fv_qq_open_qq_subset Q K Y X H).
      * right. apply (fv_qqt_open_qqt_subset T1 (S K) Y X H).
    + apply (proj2 (union_iff _ _ _)). destruct (proj1 (union_iff _ _ _) Hin) as [H|H];
        [left; apply (fv_qqt_open_qqt_subset T1 K Y X H)
        |right; apply (fv_qqt_open_qqt_subset T2 K Y X H)].
    + apply (proj2 (union_iff _ _ _)). destruct (proj1 (union_iff _ _ _) Hin) as [H|H];
        [left; apply (fv_qqt_open_qqt_subset T1 K Y X H)
        |right; apply (fv_qqt_open_qqt_subset T2 K Y X H)].
    + apply (fv_qqt_open_qqt_subset T1 K Y X Hin).
  - destruct T as [Q T]. intros K Y X Hin. simpl in *.
    destruct (proj1 (union_iff _ _ _) Hin) as [H|H].
    + apply (proj2 (union_iff _ _ _)). left. apply (fv_qq_open_qq_subset Q K Y X H).
    + apply (proj2 (union_iff _ _ _)). right. apply (fv_qt_open_qt_subset T K Y X H).
Qed.

(* Opening with a qualifier variable does not change type free variables. *)
Fixpoint fv_tt_open_qt_eq (T:typ) {struct T} :
  forall K Y, fv_tt (open_qt_rec K (qua_fvar Y) T) = fv_tt T
with fv_tqt_open_qqt_eq (T:qtyp) {struct T} :
  forall K Y, fv_tqt (open_qqt_rec K (qua_fvar Y) T) = fv_tqt T.
Proof.
  - destruct T as [| |n|a|T1 T2|T1 T2|Q T1|T1 T2|T1 T2|T1]; intros K Y; simpl.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + rewrite (fv_tqt_open_qqt_eq T1 K Y).
      rewrite (fv_tqt_open_qqt_eq T2 (S K) Y). reflexivity.
    + rewrite (fv_tt_open_qt_eq T1 K Y).
      rewrite (fv_tqt_open_qqt_eq T2 (S K) Y). reflexivity.
    + rewrite (fv_tqt_open_qqt_eq T1 (S K) Y). reflexivity.
    + rewrite (fv_tqt_open_qqt_eq T1 K Y).
      rewrite (fv_tqt_open_qqt_eq T2 K Y). reflexivity.
    + rewrite (fv_tqt_open_qqt_eq T1 K Y).
      rewrite (fv_tqt_open_qqt_eq T2 K Y). reflexivity.
    + rewrite (fv_tqt_open_qqt_eq T1 K Y). reflexivity.
  - destruct T as [Q T]. intros K Y. simpl.
    rewrite (fv_tt_open_qt_eq T K Y). reflexivity.
Qed.

Lemma wf_typ_qtyp_fv_dom :
  (forall (E:env) (T:typ), wf_typ E T ->
     forall X, X `notin` dom E -> X `notin` fv_tt T) /\
  (forall (E:env) (T:qtyp), wf_qtyp E T ->
     forall X, X `notin` dom E -> X `notin` fv_tqt T).
Proof.
  apply wf_tq_mut
    with (P := fun E T _ => forall X, X `notin` dom E -> X `notin` fv_tt T)
         (P0 := fun E T _ => forall X, X `notin` dom E -> X `notin` fv_tqt T).
  - intros E X HX. simpl. apply notin_empty_1.
  - intros E X HX. simpl. apply notin_empty_1.
  - intros U E Z b X HX. simpl.
    apply notin_singleton. intro Heq.
    apply HX. rewrite Heq in b. exact (binds_In _ _ _ _ b).
  - intros E T1 T2 w1 IH1 w2 IH2 X HX. simpl.
    apply notin_union.
    + apply IH1. exact HX.
    + apply IH2. exact HX.
  - intros L E T1 T2 w1 IH1 w0 IH0 X HX. simpl.
    apply notin_union.
    + apply IH1. exact HX.
    + pick fresh Y for (L \u dom E \u singleton X).
      assert (HYL : Y `notin` L) by
        (exact (notin_union_1 Y L (dom E `union` singleton X) Fr)).
      assert (HYD : Y `notin` dom E) by
        (exact (notin_union_1 Y (dom E) (singleton X)
                  (notin_union_2 Y L (dom E `union` singleton X) Fr))).
      assert (HYX : Y `notin` singleton X) by
        (exact (notin_union_2 Y (dom E) (singleton X)
                  (notin_union_2 Y L (dom E `union` singleton X) Fr))).
      assert (HXY : X <> Y) by (apply (notin_singleton_1 X Y HYX)).
      assert (Hnotin : X `notin` fv_tqt (open_tqt T2 Y)).
      { apply (IH0 Y HYL). simpl. apply notin_add.
        - symmetry. exact HXY.
        - exact HX. }
      intro Hin. apply Hnotin.
      apply (fv_tqt_open_tqt_subset T2 0 Y X Hin).
  - intros L E Q T wq w0 IH0 X HX. simpl.
    pick fresh Y for (L \u dom E \u singleton X).
    assert (HYL : Y `notin` L) by
      (exact (notin_union_1 Y L (dom E `union` singleton X) Fr)).
    assert (HYD : Y `notin` dom E) by
      (exact (notin_union_1 Y (dom E) (singleton X)
                (notin_union_2 Y L (dom E `union` singleton X) Fr))).
    assert (HYX : Y `notin` singleton X) by
      (exact (notin_union_2 Y (dom E) (singleton X)
                (notin_union_2 Y L (dom E `union` singleton X) Fr))).
    assert (HXY : X <> Y) by (apply (notin_singleton_1 X Y HYX)).
    assert (Hnotin : X `notin` fv_tqt (open_qqt T Y)).
    { apply (IH0 Y HYL). simpl. apply notin_add.
      - symmetry. exact HXY.
      - exact HX. }
    intro Hin. apply Hnotin.
    unfold open_qqt. rewrite (fv_tqt_open_qqt_eq T 0 Y). exact Hin.
  - intros E T1 T2 w1 IH1 w2 IH2 X HX. simpl.
    apply notin_union; [apply IH1|apply IH2]; exact HX.
  - intros E T1 T2 w1 IH1 w2 IH2 X HX. simpl.
    apply notin_union; [apply IH1|apply IH2]; exact HX.
  - intros E Q T wq wT IHT X HX. simpl. apply IHT. exact HX.
Qed.

Lemma wf_typ_fv_dom : forall E T, wf_typ E T ->
  forall X, X `notin` dom E -> X `notin` fv_tt T.
Proof. intros. eapply (proj1 wf_typ_qtyp_fv_dom); eauto. Qed.

Lemma wf_qtyp_fv_dom : forall E T, wf_qtyp E T ->
  forall X, X `notin` dom E -> X `notin` fv_tqt T.
Proof. intros. eapply (proj2 wf_typ_qtyp_fv_dom); eauto. Qed.

(* ========================================================= *)
(* Substitution is the identity on environments out of scope *)
(* ========================================================= *)

Lemma subst_te_env_id : forall (E:env) X V,
  wf_env E -> X `notin` dom E -> subst_te_env X V E = E.
Proof.
  induction E as [|[y b] E IH]; intros X V Hwf HX.
  - reflexivity.
  - destruct b as [Tsub|Ttyp|Q]; simpl.
    + f_equal.
      * f_equal. f_equal. apply subst_tt_id.
        apply (wf_typ_fv_dom ((y, bind_sub Tsub) :: E) Tsub).
        -- eapply wf_env_binds_sub; [exact Hwf | unfold binds; left; reflexivity].
        -- exact HX.
      * apply IH; [apply wf_env_cons_inv in Hwf; exact Hwf | apply (notin_add_2 y X (dom E) HX)].
    + f_equal.
      * f_equal. f_equal. apply subst_tqt_id.
        apply (wf_qtyp_fv_dom ((y, bind_typ Ttyp) :: E) Ttyp).
        -- eapply wf_env_binds_typ; [exact Hwf | unfold binds; left; reflexivity].
        -- exact HX.
      * apply IH; [apply wf_env_cons_inv in Hwf; exact Hwf | apply (notin_add_2 y X (dom E) HX)].
    + assert (Htail := IH X V (wf_env_cons_inv _ _ _ Hwf)
                     (notin_add_2 y X (dom E) HX)).
      simpl. rewrite Htail. reflexivity.
Qed.

(* Closedness of a type under qualifier-variable opening. *)
Definition closed_qt (V:typ) : Prop :=
  forall K R, open_qt_rec K R V = V.

Lemma wf_typ_closed_qt : forall E V, wf_typ E V -> closed_qt V.
Proof.
  intros E V H K R.
  apply (open_qt_lc V 0).
  - exact (proj1 type_qtype_lc_qq_any V (wf_typ_type E V H) 0).
  - apply Nat.le_0_l.
Qed.

(* Type-variable substitution commutes with qualifier-variable opening. *)
Fixpoint subst_tt_open_qt_rec (T:typ) {struct T} :
  forall K (R:qua) X V, closed_qt V ->
    subst_tt X V (open_qt_rec K R T) = open_qt_rec K R (subst_tt X V T)
with subst_tqt_open_qqt_rec (T:qtyp) {struct T} :
  forall K (R:qua) X V, closed_qt V ->
    subst_tqt X V (open_qqt_rec K R T) = open_qqt_rec K R (subst_tqt X V T).
Proof.
  - destruct T as [| |n|a|T1 T2|T1 T2|Q T1|T1 T2|T1 T2|T1]; intros K R X V Hc; simpl.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + destruct (eq_dec a X) as [Heq|Hneq].
      * subst a. rewrite (Hc K R). reflexivity.
      * reflexivity.
    + rewrite (subst_tqt_open_qqt_rec T1 K R X V Hc).
      rewrite (subst_tqt_open_qqt_rec T2 (S K) R X V Hc). reflexivity.
    + rewrite (subst_tt_open_qt_rec T1 K R X V Hc).
      rewrite (subst_tqt_open_qqt_rec T2 (S K) R X V Hc). reflexivity.
    + rewrite (subst_tqt_open_qqt_rec T1 (S K) R X V Hc). reflexivity.
    + rewrite (subst_tqt_open_qqt_rec T1 K R X V Hc).
      rewrite (subst_tqt_open_qqt_rec T2 K R X V Hc). reflexivity.
    + rewrite (subst_tqt_open_qqt_rec T1 K R X V Hc).
      rewrite (subst_tqt_open_qqt_rec T2 K R X V Hc). reflexivity.
    + rewrite (subst_tqt_open_qqt_rec T1 K R X V Hc). reflexivity.
  - destruct T as [Q T]. intros K R X V Hc. simpl.
    rewrite (subst_tt_open_qt_rec T K R X V Hc). reflexivity.
Qed.

Lemma subst_tt_open_qt_atom : forall (T:typ) X V (Y:atom),
  closed_qt V ->
  subst_tt X V (open_qt T Y) = open_qt (subst_tt X V T) Y.
Proof. intros. unfold open_qt. apply (subst_tt_open_qt_rec T 0 (qua_fvar Y) X V H). Qed.

Lemma subst_tqt_open_qqt_atom : forall (T:qtyp) X V (Y:atom),
  closed_qt V ->
  subst_tqt X V (open_qqt T Y) = open_qqt (subst_tqt X V T) Y.
Proof. intros. unfold open_qqt. apply (subst_tqt_open_qqt_rec T 0 (qua_fvar Y) X V H). Qed.

Lemma subst_tqt_open_qqt : forall (T:qtyp) X V Q,
  closed_qt V ->
  subst_tqt X V (open_qqt T Q) = open_qqt (subst_tqt X V T) Q.
Proof. intros. unfold open_qqt. apply (subst_tqt_open_qqt_rec T 0 Q X V H). Qed.

(* ========================================================= *)
(* wf_qua is unchanged by type substitution                    *)
(* ========================================================= *)

Lemma wf_qua_subst_te : forall (E:env) Q, wf_qua E Q ->
  forall E1 X U E2 V,
    E = E1 ++ X ~ bind_sub U ++ E2 ->
    wf_qua (subst_te_env X V (E1++E2)) Q.
Proof.
  intros E Q H. induction H as [E b
    | R E Z Hb
    | E Q1 Q2 H1 IH1 H2 IH2
    | E Q1 Q2 H1 IH1 H2 IH2
    | E Q1 H1 IH1]; intros E1 X U E2 V Heq; subst E.
  - apply wf_qua_base.
  - eapply wf_qua_fvar.
    apply binds_qua_subst_te.
    apply (binds_qua_remove_sub_mid E1 X U E2 Z R Hb).
  - apply wf_qua_meet.
    + apply (IH1 E1 X U E2 V eq_refl).
    + apply (IH2 E1 X U E2 V eq_refl).
  - apply wf_qua_join.
    + apply (IH1 E1 X U E2 V eq_refl).
    + apply (IH2 E1 X U E2 V eq_refl).
  - apply wf_qua_negate. apply (IH1 E1 X U E2 V eq_refl).
Qed.

(* ========================================================= *)
(* wf_typ / wf_qtyp preservation under type substitution      *)
(* ========================================================= *)

Lemma wf_typ_qtyp_subst_te :
  (forall (E:env) (T:typ), wf_typ E T ->
     forall E1 X U E2 V,
       E = E1 ++ X ~ bind_sub U ++ E2 ->
       wf_env (subst_te_env X V (E1++E2)) ->
       wf_typ (subst_te_env X V (E1++E2)) V ->
       wf_typ (subst_te_env X V (E1++E2)) (subst_tt X V T)) /\
  (forall (E:env) (T:qtyp), wf_qtyp E T ->
     forall E1 X U E2 V,
       E = E1 ++ X ~ bind_sub U ++ E2 ->
       wf_env (subst_te_env X V (E1++E2)) ->
       wf_typ (subst_te_env X V (E1++E2)) V ->
       wf_qtyp (subst_te_env X V (E1++E2)) (subst_tqt X V T)).
Proof.
  apply wf_tq_mut
    with (P := fun E T _ => forall E1 X U E2 V,
            E = E1 ++ X ~ bind_sub U ++ E2 ->
            wf_env (subst_te_env X V (E1++E2)) ->
            wf_typ (subst_te_env X V (E1++E2)) V ->
            wf_typ (subst_te_env X V (E1++E2)) (subst_tt X V T))
         (P0 := fun E T _ => forall E1 X U E2 V,
            E = E1 ++ X ~ bind_sub U ++ E2 ->
            wf_env (subst_te_env X V (E1++E2)) ->
            wf_typ (subst_te_env X V (E1++E2)) V ->
            wf_qtyp (subst_te_env X V (E1++E2)) (subst_tqt X V T)).
  - intros E E1 X U E2 V Heq Hw HV. subst E. constructor.
  - intros E E1 X U E2 V Heq Hw HV. subst E. constructor.
  - intros U0 E Z b E1 X U E2 V Heq Hw HV; subst E.
    destruct (eq_dec Z X) as [Heq|Hneq].
    + subst Z. rewrite subst_tt_atom_self. exact HV.
    + rewrite (subst_tt_atom_eq _ _ _ Hneq).
      eapply wf_typ_var.
      apply binds_sub_subst_te.
      destruct (binds_remove_sub_same E1 X U0 U E2 Z b) as [[HeqZ HU]|Hout].
      * exfalso. exact (Hneq HeqZ).
      * exact Hout.
  - intros E T1 T2 w1 IH1 w2 IH2 E1 X U E2 V Heq Hw HV; subst E.
    simpl. apply wf_typ_arrow.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV).
    + apply (IH2 E1 X U E2 V eq_refl Hw HV).
  - intros L E T1 T2 w1 IH1 w0 IH0 E1 X U E2 V Heq Hw HV; subst E.
    simpl.
    eapply wf_typ_all with (L := L \u dom (E1++E2) \u singleton X).
    + apply (IH1 E1 X U E2 V eq_refl Hw HV).
    + intros Y HY.
      assert (HYL : Y `notin` L) by
        (exact (notin_union_1 Y L (dom (E1++E2) `union` singleton X) HY)).
      assert (HYD : Y `notin` dom (E1++E2)) by
        (exact (notin_union_1 Y (dom (E1++E2)) (singleton X)
                  (notin_union_2 Y L (dom (E1++E2) `union` singleton X) HY))).
      assert (HYX : Y `notin` singleton X) by
        (exact (notin_union_2 Y (dom (E1++E2)) (singleton X)
                  (notin_union_2 Y L (dom (E1++E2) `union` singleton X) HY))).
      assert (HXY : Y <> X) by (symmetry; exact (notin_singleton_1 X Y HYX)).
      assert (HwE'' : wf_env (subst_te_env X V ((Y ~ bind_sub T1 ++ E1) ++ E2))).
      { rewrite app_assoc. simpl. eapply wf_env_sub.
        - exact Hw.
        - apply (IH1 E1 X U E2 V eq_refl Hw HV).
        - apply (proj2 (notin_dom_subst_te_env (E1++E2) X V Y)).
          exact HYD. }
      assert (HVE'' : wf_typ (subst_te_env X V ((Y ~ bind_sub T1 ++ E1) ++ E2)) V).
      { change (wf_typ ((Y, bind_sub (subst_tt X V T1)) :: subst_te_env X V (E1++E2)) V).
        eapply wf_typ_extends; [| exact HV]. apply extends_cons. }
      pose proof (IH0 Y HYL (Y ~ bind_sub T1 ++ E1) X U E2 V eq_refl HwE'' HVE'') as HI.
      rewrite (subst_tqt_open_tqt_atom T2 X V Y) in HI.
      * exact HI.
      * apply wf_typ_closed_tt in HV. exact HV.
      * exact HXY.
  - intros L E Q T wq w0 IH0 E1 X U E2 V Heq Hw HV; subst E.
    simpl.
    eapply wf_typ_qall with (L := L \u dom (E1++E2) \u singleton X).
    + apply (wf_qua_subst_te _ Q wq E1 X U E2 V eq_refl).
    + intros Y HY.
      assert (HYL : Y `notin` L) by
        (exact (notin_union_1 Y L (dom (E1++E2) `union` singleton X) HY)).
      assert (HYD : Y `notin` dom (E1++E2)) by
        (exact (notin_union_1 Y (dom (E1++E2)) (singleton X)
                  (notin_union_2 Y L (dom (E1++E2) `union` singleton X) HY))).
      assert (HYX : Y `notin` singleton X) by
        (exact (notin_union_2 Y (dom (E1++E2)) (singleton X)
                  (notin_union_2 Y L (dom (E1++E2) `union` singleton X) HY))).
      assert (HXY : Y <> X) by (symmetry; exact (notin_singleton_1 X Y HYX)).
      assert (HwE'' : wf_env (subst_te_env X V ((Y ~ bind_qua Q ++ E1) ++ E2))).
      { rewrite app_assoc. simpl. eapply wf_env_qua.
        - exact Hw.
        - apply (wf_qua_subst_te _ Q wq E1 X U E2 V eq_refl).
        - apply (proj2 (notin_dom_subst_te_env (E1++E2) X V Y)). exact HYD. }
      assert (HVE'' : wf_typ (subst_te_env X V ((Y ~ bind_qua Q ++ E1) ++ E2)) V).
      { change (wf_typ ((Y, bind_qua Q) :: subst_te_env X V (E1++E2)) V).
        eapply wf_typ_extends; [| exact HV]. apply extends_cons. }
      pose proof (IH0 Y HYL (Y ~ bind_qua Q ++ E1) X U E2 V eq_refl HwE'' HVE'') as HI.
      rewrite (subst_tqt_open_qqt_atom T X V Y (wf_typ_closed_qt _ _ HV)) in HI.
      exact HI.
  - intros E T1 T2 w1 IH1 w2 IH2 E1 X U E2 V Heq Hw HV; subst E.
    simpl. apply wf_typ_sum.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV).
    + apply (IH2 E1 X U E2 V eq_refl Hw HV).
  - intros E T1 T2 w1 IH1 w2 IH2 E1 X U E2 V Heq Hw HV; subst E.
    simpl. apply wf_typ_pair.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV).
    + apply (IH2 E1 X U E2 V eq_refl Hw HV).
  - intros E Q T wq wT IHT E1 X U E2 V Heq Hw HV; subst E.
    simpl. apply wf_qtyp_qtyp.
    + apply (wf_qua_subst_te _ Q wq E1 X U E2 V eq_refl).
    + apply (IHT E1 X U E2 V eq_refl Hw HV).
Qed.

Lemma wf_typ_subst_te : forall E T, wf_typ E T ->
  forall E1 X U E2 V,
    E = E1 ++ X ~ bind_sub U ++ E2 ->
    wf_env (subst_te_env X V (E1++E2)) ->
    wf_typ (subst_te_env X V (E1++E2)) V ->
    wf_typ (subst_te_env X V (E1++E2)) (subst_tt X V T).
Proof. intros. eapply (proj1 wf_typ_qtyp_subst_te); eauto. Qed.

Lemma wf_qtyp_subst_te : forall E T, wf_qtyp E T ->
  forall E1 X U E2 V,
    E = E1 ++ X ~ bind_sub U ++ E2 ->
    wf_env (subst_te_env X V (E1++E2)) ->
    wf_typ (subst_te_env X V (E1++E2)) V ->
    wf_qtyp (subst_te_env X V (E1++E2)) (subst_tqt X V T).
Proof. intros. eapply (proj2 wf_typ_qtyp_subst_te); eauto. Qed.

(* ========================================================= *)
(* wf_env preservation under type substitution                *)
(* ========================================================= *)

Lemma wf_env_subst_te : forall (E1:env) X (U:typ) (E2:env) V,
  wf_env (E1 ++ X ~ bind_sub U ++ E2) ->
  wf_typ (subst_te_env X V E2) V ->
  wf_env (subst_te_env X V (E1++E2)).
Proof.
  induction E1 as [|[y b] E1 IH]; intros X U E2 V Hwf HV.
  - simpl in Hwf. destruct (wf_env_sub_inv _ _ _ Hwf) as [HwE2 [HU HX]].
    simpl. rewrite (subst_te_env_id E2 X V HwE2 HX). exact HwE2.
  - destruct b as [Tsub|Ttyp|Q].
    + simpl in Hwf. inversion Hwf as [| E0 X0 U0 Htail HT Hnot | E0 x0 T0 Htail HT Hnot | E0 X0 Q0 Htail HQ Hnot]; subst.
      assert (HwIH : wf_env (subst_te_env X V (E1++E2)))
        by (apply (IH X U E2 V); [exact Htail | exact HV]).
      assert (HVE : wf_typ (subst_te_env X V (E1++E2)) V).
      { rewrite subst_te_env_app. eapply wf_typ_extends;
          [apply extends_app_l | exact HV]. }
      simpl. eapply wf_env_sub.
      * exact HwIH.
      * apply (wf_typ_subst_te (E1 ++ X ~ bind_sub U ++ E2) Tsub HT
                 E1 X U E2 V eq_refl HwIH HVE).
      * apply (proj2 (notin_dom_subst_te_env (E1++E2) X V y)).
        apply (notin_dom_remove_mid E1 X (bind_sub U) E2 y Hnot).
    + simpl in Hwf. inversion Hwf as [| E0 X0 U0 Htail HT Hnot | E0 x0 T0 Htail HT Hnot | E0 X0 Q0 Htail HQ Hnot]; subst.
      assert (HwIH : wf_env (subst_te_env X V (E1++E2)))
        by (apply (IH X U E2 V); [exact Htail | exact HV]).
      assert (HVE : wf_typ (subst_te_env X V (E1++E2)) V).
      { rewrite subst_te_env_app. eapply wf_typ_extends;
          [apply extends_app_l | exact HV]. }
      simpl. eapply wf_env_typ.
      * exact HwIH.
      * apply (wf_qtyp_subst_te (E1 ++ X ~ bind_sub U ++ E2) Ttyp HT
                 E1 X U E2 V eq_refl HwIH HVE).
      * apply (proj2 (notin_dom_subst_te_env (E1++E2) X V y)).
        apply (notin_dom_remove_mid E1 X (bind_sub U) E2 y Hnot).
    + simpl in Hwf. inversion Hwf as [| E0 X0 U0 Htail HT Hnot | E0 x0 T0 Htail HT Hnot | E0 X0 Q0 Htail HQ Hnot]; subst.
      assert (HwIH : wf_env (subst_te_env X V (E1++E2)))
        by (apply (IH X U E2 V); [exact Htail | exact HV]).
      simpl. eapply wf_env_qua.
      * exact HwIH.
      * apply (wf_qua_subst_te (E1 ++ X ~ bind_sub U ++ E2) Q HQ
                 E1 X U E2 V eq_refl).
      * apply (proj2 (notin_dom_subst_te_env (E1++E2) X V y)).
        apply (notin_dom_remove_mid E1 X (bind_sub U) E2 y Hnot).
Qed.

(* ========================================================= *)
(* Opening a well-formed body with a well-formed type          *)
(* ========================================================= *)

Lemma wf_qtyp_open_tqt_gen : forall (E:env) X (U:typ) (Tbody:qtyp) V,
  wf_env E ->
  wf_typ E V ->
  X `notin` dom E ->
  X `notin` fv_tqt Tbody ->
  wf_qtyp (X ~ bind_sub U ++ E) (open_tqt Tbody X) ->
  wf_qtyp E (open_tqt Tbody V).
Proof.
  intros E X U Tbody V Hw HV HX Hfv Hbody.
  assert (Heq : subst_te_env X V E = E).
  { apply (subst_te_env_id E X V Hw HX). }
  assert (Hres := wf_qtyp_subst_te (X ~ bind_sub U ++ E) (open_tqt Tbody X) Hbody
                    (@nil (atom*binding)) X U E V).
  assert (Heq' : subst_te_env X V ((@nil (atom*binding)) ++ E) = E).
  { rewrite app_nil_l. exact Heq. }
  rewrite Heq' in Hres.
  specialize (Hres eq_refl).
  assert (Hw' : wf_env E) by exact Hw.
  assert (HV' : wf_typ E V) by exact HV.
  specialize (Hres Hw' HV').
  rewrite (subst_tqt_open_tqt_self Tbody X V (wf_typ_closed_tt E V HV)) in Hres.
  rewrite (subst_tqt_id Tbody X V Hfv) in Hres.
  exact Hres.
Qed.

(* ========================================================= *)
(* subqual preservation under type substitution               *)
(* ========================================================= *)

Lemma subqual_subst_te : forall (E:env) Q R, subqual E Q R ->
  forall E1 X U E2 V,
    E = E1 ++ X ~ bind_sub U ++ E2 ->
    wf_env (subst_te_env X V (E1++E2)) ->
    wf_typ (subst_te_env X V (E1++E2)) V ->
    subqual (subst_te_env X V (E1++E2)) Q R.
Proof.
  intros E Q R H.
  induction H as [E0 Q0 Hwf HQ
    | E0 Q0 Hwf HQ
    | E0 Qa Qb Qc bb h1 IH1 hc h2 IH2
    | E0 Qa Qb Qc bb h1 IH1 hc h2 IH2
    | E0 b1 b2 Hwf Ho
    | E0 Xw Hwf HQ
    | R0 E0 Qw Xw hb h1 IH1
    | E0 R1 R2 Qw h1 IH1 HR2
    | E0 R1 R2 Qw HR1 h2 IH1
    | E0 R1 R2 Qw h1 IH1 h2 IH2
    | E0 R1 R2 Qw h1 IH1 HR2
    | E0 R1 R2 Qw HR1 h2 IH1
    | E0 R1 R2 Qw h1 IH1 h2 IH2
    | E0 Qw Rw Sw Hwf HQ HR HS
    | E0 Qw Rw Sw h1 IH1 h2 IH2
    | E0 Qw Hwf HQ
    | E0 Qw Hwf HQ
    | E0 Qw Hwf HQ];
    intros E1 X U E2 V Heq Hw HV; subst E0.
  - eapply subqual_top; [exact Hw | apply (wf_qua_subst_te _ Q0 HQ E1 X U E2 V eq_refl)].
  - eapply subqual_bot; [exact Hw | apply (wf_qua_subst_te _ Q0 HQ E1 X U E2 V eq_refl)].
  - eapply subqual_eval_elim;
      [apply (IH1 E1 X U E2 V eq_refl Hw HV) | exact hc
      |apply (IH2 E1 X U E2 V eq_refl Hw HV)].
  - eapply subqual_eval_intro;
      [apply (IH1 E1 X U E2 V eq_refl Hw HV) | exact hc
      |apply (IH2 E1 X U E2 V eq_refl Hw HV)].
  - eapply subqual_lift_elem; [exact Hw | exact Ho].
  - eapply subqual_refl_qvar;
      [exact Hw | apply (wf_qua_subst_te _ (qua_fvar Xw) HQ E1 X U E2 V eq_refl)].
  - eapply subqual_trans_qvar.
    + apply binds_qua_subst_te.
      exact (binds_qua_remove_sub_mid E1 X U E2 Xw R0 hb).
    + apply (IH1 E1 X U E2 V eq_refl Hw HV).
  - eapply subqual_join_inl.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV).
    + apply (wf_qua_subst_te _ R2 HR2 E1 X U E2 V eq_refl).
  - eapply subqual_join_inr.
    + apply (wf_qua_subst_te _ R1 HR1 E1 X U E2 V eq_refl).
    + apply (IH1 E1 X U E2 V eq_refl Hw HV).
  - eapply subqual_join_elim.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV).
    + apply (IH2 E1 X U E2 V eq_refl Hw HV).
  - eapply subqual_meet_eliml.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV).
    + apply (wf_qua_subst_te _ R2 HR2 E1 X U E2 V eq_refl).
  - eapply subqual_meet_elimr.
    + apply (wf_qua_subst_te _ R1 HR1 E1 X U E2 V eq_refl).
    + apply (IH1 E1 X U E2 V eq_refl Hw HV).
  - eapply subqual_meet_intro.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV).
    + apply (IH2 E1 X U E2 V eq_refl Hw HV).
  - eapply subqual_dist.
    + exact Hw.
    + apply (wf_qua_subst_te _ Qw HQ E1 X U E2 V eq_refl).
    + apply (wf_qua_subst_te _ Rw HR E1 X U E2 V eq_refl).
    + apply (wf_qua_subst_te _ Sw HS E1 X U E2 V eq_refl).
  - eapply subqual_trans.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV).
    + apply (IH2 E1 X U E2 V eq_refl Hw HV).
  - eapply subqual_negate_intro.
    + exact Hw.
    + apply (wf_qua_subst_te _ Qw HQ E1 X U E2 V eq_refl).
  - eapply subqual_negate_elim.
    + exact Hw.
    + apply (wf_qua_subst_te _ Qw HQ E1 X U E2 V eq_refl).
  - eapply subqual_refl_negate.
    + exact Hw.
    + apply (wf_qua_subst_te _ Qw HQ E1 X U E2 V eq_refl).
Qed.

Lemma binds_sub_subst_te_mid : forall (E1:env) X (U0:typ) (E2:env) V Y (W:typ),
  Y <> X ->
  binds Y (bind_sub W) (E1 ++ X ~ bind_sub U0 ++ E2) ->
  binds Y (bind_sub (subst_tt X V W)) (subst_te_env X V (E1++E2)).
Proof.
  intros E1 X U0 E2 V Y W Hne Hb.
  apply binds_sub_subst_te.
  destruct (binds_remove_sub_same E1 X W U0 E2 Y Hb) as [[Heq _]|Hout].
  - exfalso. exact (Hne Heq).
  - exact Hout.
Qed.

Lemma binds_typ_subst_te_mid : forall (E1:env) X (U0:typ) (E2:env) V Y T,
  binds Y (bind_typ T) (E1 ++ X ~ bind_sub U0 ++ E2) ->
  binds Y (bind_typ (subst_tqt X V T)) (subst_te_env X V (E1++E2)).
Proof.
  intros. apply binds_typ_subst_te.
  apply (binds_typ_remove_sub_mid E1 X U0 E2 Y T). exact H.
Qed.

Lemma binds_qua_subst_te_mid : forall (E1:env) X (U0:typ) (E2:env) V Y Q,
  binds Y (bind_qua Q) (E1 ++ X ~ bind_sub U0 ++ E2) ->
  binds Y (bind_qua Q) (subst_te_env X V (E1++E2)).
Proof.
  intros. apply binds_qua_subst_te.
  apply (binds_qua_remove_sub_mid E1 X U0 E2 Y Q). exact H.
Qed.

(* ========================================================= *)
(* sub / subqtype preservation under type substitution        *)
(* ========================================================= *)

Lemma sub_subqtype_subst_te :
  (forall (E:env) (S T:typ), sub E S T ->
     forall E1 X U E2 V,
       E = E1 ++ X ~ bind_sub U ++ E2 ->
       wf_env (subst_te_env X V (E1++E2)) ->
       wf_typ (subst_te_env X V (E1++E2)) V ->
       sub (subst_te_env X V (E1++E2)) V (subst_tt X V U) ->
       sub (subst_te_env X V (E1++E2)) (subst_tt X V S) (subst_tt X V T)) /\
  (forall (E:env) (S T:qtyp), subqtype E S T ->
     forall E1 X U E2 V,
       E = E1 ++ X ~ bind_sub U ++ E2 ->
       wf_env (subst_te_env X V (E1++E2)) ->
       wf_typ (subst_te_env X V (E1++E2)) V ->
       sub (subst_te_env X V (E1++E2)) V (subst_tt X V U) ->
       subqtype (subst_te_env X V (E1++E2)) (subst_tqt X V S) (subst_tqt X V T)).
Proof.
  apply sub_tq_mut
    with (P := fun E S T _ => forall E1 X U E2 V,
            E = E1 ++ X ~ bind_sub U ++ E2 ->
            wf_env (subst_te_env X V (E1++E2)) ->
            wf_typ (subst_te_env X V (E1++E2)) V ->
            sub (subst_te_env X V (E1++E2)) V (subst_tt X V U) ->
            sub (subst_te_env X V (E1++E2)) (subst_tt X V S) (subst_tt X V T))
         (P0 := fun E S T _ => forall E1 X U E2 V,
            E = E1 ++ X ~ bind_sub U ++ E2 ->
            wf_env (subst_te_env X V (E1++E2)) ->
            wf_typ (subst_te_env X V (E1++E2)) V ->
            sub (subst_te_env X V (E1++E2)) V (subst_tt X V U) ->
            subqtype (subst_te_env X V (E1++E2)) (subst_tqt X V S) (subst_tqt X V T)).
  - (* sub_top *) intros E S Hwf HS E1 X U E2 V Heq Hw HV Hsub; subst E. simpl.
    eapply sub_top.
    + exact Hw.
    + apply (wf_typ_subst_te (E1 ++ X ~ bind_sub U ++ E2) S HS
               E1 X U E2 V eq_refl Hw HV).
  - (* sub_refl_int *) intros E Hwf E1 X U E2 V Heq Hw HV Hsub; subst E. simpl.
    apply sub_refl_int. exact Hw.
  - (* sub_refl_tvar *) intros E Z Hwf HZ E1 X U E2 V Heq Hw HV Hsub; subst E.
    destruct (eq_dec Z X) as [HeqZ|HneZ].
    + subst Z. rewrite subst_tt_atom_self.
      apply (sub_refl (subst_te_env X V (E1++E2)) V Hw HV).
    + rewrite (subst_tt_atom_eq _ _ _ HneZ).
      apply sub_refl_tvar.
      * exact Hw.
      * inversion HZ; subst.
        eapply wf_typ_var.
        eapply binds_sub_subst_te_mid; eauto.
  - (* sub_trans_tvar *) intros U0 E T Z b s IH E1 X U E2 V Heq Hw HV Hsub; subst E.
    destruct (eq_dec Z X) as [HeqZ|HneZ].
    + subst Z.
      destruct (binds_remove_sub_same E1 X U0 U E2 X b) as [[_ HU]|Hout].
      * subst U0. rewrite subst_tt_atom_self.
        pose proof (IH E1 X U E2 V eq_refl Hw HV Hsub) as Hres.
        eapply sub_trans; [exact Hsub | exact Hres].
      * assert (Hwfull : wf_env (E1 ++ X ~ bind_sub U ++ E2)).
        { exact (proj1 (sub_wf _ _ _ (sub_trans_tvar U0 _ T X b s))). }
        assert (HU : U0 = U).
        { assert (Hb1 : binds X (bind_sub U0) (E1 ++ X ~ bind_sub U ++ E2)).
          { apply (binds_mid_weaken _ X (bind_sub U0) E1 X (bind_sub U) E2 Hout). }
          pose proof (binds_unique _ X (bind_sub U0) (bind_sub U) _
                        Hb1 (binds_sub_head_bind E1 X U E2)
                        (wf_env_uniq _ Hwfull)) as Heqb.
          inversion Heqb; reflexivity. }
        subst U0.
        rewrite subst_tt_atom_self.
        pose proof (IH E1 X U E2 V eq_refl Hw HV Hsub) as Hres.
        eapply sub_trans; [exact Hsub | exact Hres].
    + rewrite (subst_tt_atom_eq _ _ _ HneZ).
      eapply sub_trans_tvar.
      * eapply binds_sub_subst_te_mid; eauto.
      * apply (IH E1 X U E2 V eq_refl Hw HV Hsub).
  - (* sub_arrow *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2 E1 X U E2 V Heq Hw HV Hsub; subst E.
    simpl. eapply sub_arrow.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
    + apply (IH2 E1 X U E2 V eq_refl Hw HV Hsub).
  - (* sub_all *) intros L E S1 S2 T1 T2 s1 IH1 s2 IH2 E1 X U E2 V Heq Hw HV Hsub; subst E.
    simpl. eapply sub_all with (L := L \u dom (E1++E2) \u singleton X).
    + apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
    + intros Y HY.
      assert (HYL : Y `notin` L) by
        (exact (notin_union_1 Y L (dom (E1++E2) `union` singleton X) HY)).
      assert (HYD : Y `notin` dom (E1++E2)) by
        (exact (notin_union_1 Y (dom (E1++E2)) (singleton X)
                  (notin_union_2 Y L (dom (E1++E2) `union` singleton X) HY))).
      assert (HYX : Y `notin` singleton X) by
        (exact (notin_union_2 Y (dom (E1++E2)) (singleton X)
                  (notin_union_2 Y L (dom (E1++E2) `union` singleton X) HY))).
      assert (HXY : Y <> X) by (symmetry; exact (notin_singleton_1 X Y HYX)).
      assert (HwE'' : wf_env (subst_te_env X V ((Y ~ bind_sub T1 ++ E1) ++ E2))).
      { rewrite app_assoc. simpl. eapply wf_env_sub.
        - exact Hw.
        - apply (wf_typ_subst_te (E1 ++ X ~ bind_sub U ++ E2) T1
                   (proj1 (proj2 (sub_wf _ _ _ s1)))
                   E1 X U E2 V eq_refl Hw HV).
        - apply (proj2 (notin_dom_subst_te_env (E1++E2) X V Y)). exact HYD. }
      assert (HVE'' : wf_typ (subst_te_env X V ((Y ~ bind_sub T1 ++ E1) ++ E2)) V).
      { change (wf_typ ((Y, bind_sub (subst_tt X V T1)) :: subst_te_env X V (E1++E2)) V).
        eapply wf_typ_extends; [| exact HV]. apply extends_cons. }
      assert (Hsub'' : sub (subst_te_env X V ((Y ~ bind_sub T1 ++ E1) ++ E2)) V (subst_tt X V U)).
      { eapply sub_extends; [exact Hsub | | exact HwE''].
        change (extends (subst_te_env X V (E1++E2))
                  ((Y, bind_sub (subst_tt X V T1)) :: subst_te_env X V (E1++E2))).
        apply extends_cons. }
      pose proof (IH2 Y HYL (Y ~ bind_sub T1 ++ E1) X U E2 V eq_refl HwE'' HVE'' Hsub'') as HI.
      rewrite (subst_tqt_open_tqt_atom S2 X V Y (wf_typ_closed_tt _ _ HV) HXY) in HI.
      rewrite (subst_tqt_open_tqt_atom T2 X V Y (wf_typ_closed_tt _ _ HV) HXY) in HI.
      rewrite app_assoc in HI. simpl in HI.
      exact HI.
  - (* sub_qall *) intros L E S1 S2 T1 T2 s1 s2 IH2 E1 X U E2 V Heq Hw HV Hsub; subst E.
    simpl. eapply sub_qall with (L := L \u dom (E1++E2) \u singleton X).
    + apply (subqual_subst_te (E1 ++ X ~ bind_sub U ++ E2) T1 S1 s1
               E1 X U E2 V eq_refl Hw HV).
    + intros Y HY.
      assert (HYL : Y `notin` L) by
        (exact (notin_union_1 Y L (dom (E1++E2) `union` singleton X) HY)).
      assert (HYD : Y `notin` dom (E1++E2)) by
        (exact (notin_union_1 Y (dom (E1++E2)) (singleton X)
                  (notin_union_2 Y L (dom (E1++E2) `union` singleton X) HY))).
      assert (HYX : Y `notin` singleton X) by
        (exact (notin_union_2 Y (dom (E1++E2)) (singleton X)
                  (notin_union_2 Y L (dom (E1++E2) `union` singleton X) HY))).
      assert (HXY : Y <> X) by (symmetry; exact (notin_singleton_1 X Y HYX)).
      assert (Hq' : subqual (subst_te_env X V (E1++E2)) T1 S1).
      { apply (subqual_subst_te (E1 ++ X ~ bind_sub U ++ E2) T1 S1 s1
                 E1 X U E2 V eq_refl Hw HV). }
      assert (Hwq' : wf_qua (subst_te_env X V (E1++E2)) T1)
        by (apply (proj1 (proj2 (subqual_wf _ _ _ Hq')))).
      assert (HwE'' : wf_env (subst_te_env X V ((Y ~ bind_qua T1 ++ E1) ++ E2))).
      { rewrite app_assoc. simpl. eapply wf_env_qua.
        - exact Hw.
        - exact Hwq'.
        - apply (proj2 (notin_dom_subst_te_env (E1++E2) X V Y)). exact HYD. }
      assert (HVE'' : wf_typ (subst_te_env X V ((Y ~ bind_qua T1 ++ E1) ++ E2)) V).
      { change (wf_typ ((Y, bind_qua T1) :: subst_te_env X V (E1++E2)) V).
        eapply wf_typ_extends; [| exact HV]. apply extends_cons. }
      assert (Hsub'' : sub (subst_te_env X V ((Y ~ bind_qua T1 ++ E1) ++ E2)) V (subst_tt X V U)).
      { eapply sub_extends; [exact Hsub | | exact HwE''].
        change (extends (subst_te_env X V (E1++E2))
                  ((Y, bind_qua T1) :: subst_te_env X V (E1++E2))).
        apply extends_cons. }
      pose proof (IH2 Y HYL (Y ~ bind_qua T1 ++ E1) X U E2 V eq_refl HwE'' HVE'' Hsub'') as HI.
      rewrite (subst_tqt_open_qqt_atom S2 X V Y (wf_typ_closed_qt _ _ HV)) in HI.
      rewrite (subst_tqt_open_qqt_atom T2 X V Y (wf_typ_closed_qt _ _ HV)) in HI.
      rewrite app_assoc in HI. simpl in HI.
      exact HI.
  - (* sub_sum *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2 E1 X U E2 V Heq Hw HV Hsub; subst E.
    simpl. eapply sub_sum.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
    + apply (IH2 E1 X U E2 V eq_refl Hw HV Hsub).
  - (* sub_pair *) intros E S1 S2 T1 T2 s1 IH1 s2 IH2 E1 X U E2 V Heq Hw HV Hsub; subst E.
    simpl. eapply sub_pair.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
    + apply (IH2 E1 X U E2 V eq_refl Hw HV Hsub).
  - (* subqtype_qtyp *) intros E Q1 T1 Q2 T2 s1 s2 IH2 E1 X U E2 V Heq Hw HV Hsub; subst E.
    simpl. eapply sub_qtyp_qtyp.
    + apply (subqual_subst_te (E1 ++ X ~ bind_sub U ++ E2) Q1 Q2 s1
               E1 X U E2 V eq_refl Hw HV).
    + apply (IH2 E1 X U E2 V eq_refl Hw HV Hsub).
Qed.

Lemma sub_subst_te : forall (E:env) (S T:typ), sub E S T ->
  forall E1 X U E2 V,
    E = E1 ++ X ~ bind_sub U ++ E2 ->
    wf_env (subst_te_env X V (E1++E2)) ->
    wf_typ (subst_te_env X V (E1++E2)) V ->
    sub (subst_te_env X V (E1++E2)) V (subst_tt X V U) ->
    sub (subst_te_env X V (E1++E2)) (subst_tt X V S) (subst_tt X V T).
Proof. intros. eapply (proj1 sub_subqtype_subst_te); eauto. Qed.

Lemma subqtype_subst_te : forall (E:env) (S T:qtyp), subqtype E S T ->
  forall E1 X U E2 V,
    E = E1 ++ X ~ bind_sub U ++ E2 ->
    wf_env (subst_te_env X V (E1++E2)) ->
    wf_typ (subst_te_env X V (E1++E2)) V ->
    sub (subst_te_env X V (E1++E2)) V (subst_tt X V U) ->
    subqtype (subst_te_env X V (E1++E2)) (subst_tqt X V S) (subst_tqt X V T).
Proof. intros. eapply (proj2 sub_subqtype_subst_te); eauto. Qed.



(* Type-variable substitution commutes with qualifier-variable opening of
   expressions. *)
Fixpoint subst_te_open_qe_rec (e:exp) {struct e} :
  forall K R X V, closed_qt V ->
    subst_te X V (open_qe_rec K R e) = open_qe_rec K R (subst_te X V e).
Proof.
  destruct e as [P i|i|a|P V0 e1|e1 e2|P V0 e1|e1 V0|P Q e1|e1 Q|e1 e2
    |P e1|P e1|e1 e2 e3|P e1 e2|e1|e1|P e1|P l|e1|e1 e2|P e1|P e1|P e1
    |b|e1 e2 e3];
    intros K R X V Hc; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - f_equal; try reflexivity.
    + apply (subst_tqt_open_qqt_rec V0 K R X V Hc).
    + apply (subst_te_open_qe_rec e1 (S K) R X V Hc).
  - f_equal; try reflexivity.
    + apply (subst_te_open_qe_rec e1 K R X V Hc).
    + apply (subst_te_open_qe_rec e2 K R X V Hc).
  - f_equal; try reflexivity.
    + apply (subst_tt_open_qt_rec V0 K R X V Hc).
    + apply (subst_te_open_qe_rec e1 (S K) R X V Hc).
  - f_equal; try reflexivity.
    + apply (subst_te_open_qe_rec e1 K R X V Hc).
    + apply (subst_tt_open_qt_rec V0 K R X V Hc).
  - f_equal; try reflexivity.
    apply (subst_te_open_qe_rec e1 (S K) R X V Hc).
  - f_equal; try reflexivity.
    apply (subst_te_open_qe_rec e1 K R X V Hc).
  - f_equal; try reflexivity.
    + apply (subst_te_open_qe_rec e1 K R X V Hc).
    + apply (subst_te_open_qe_rec e2 (S K) R X V Hc).
  - f_equal; try reflexivity.
    apply (subst_te_open_qe_rec e1 K R X V Hc).
  - f_equal; try reflexivity.
    apply (subst_te_open_qe_rec e1 K R X V Hc).
  - f_equal; try reflexivity.
    + apply (subst_te_open_qe_rec e1 K R X V Hc).
    + apply (subst_te_open_qe_rec e2 (S K) R X V Hc).
    + apply (subst_te_open_qe_rec e3 (S K) R X V Hc).
  - f_equal; try reflexivity.
    + apply (subst_te_open_qe_rec e1 K R X V Hc).
    + apply (subst_te_open_qe_rec e2 K R X V Hc).
  - f_equal; try reflexivity.
    apply (subst_te_open_qe_rec e1 K R X V Hc).
  - f_equal; try reflexivity.
    apply (subst_te_open_qe_rec e1 K R X V Hc).
  - f_equal; try reflexivity.
    apply (subst_te_open_qe_rec e1 K R X V Hc).
  - reflexivity.
  - f_equal; try reflexivity.
    apply (subst_te_open_qe_rec e1 K R X V Hc).
  - f_equal; try reflexivity.
    + apply (subst_te_open_qe_rec e1 K R X V Hc).
    + apply (subst_te_open_qe_rec e2 K R X V Hc).
  - f_equal; try reflexivity.
    apply (subst_te_open_qe_rec e1 K R X V Hc).
  - f_equal; try reflexivity.
    apply (subst_te_open_qe_rec e1 K R X V Hc).
  - f_equal; try reflexivity.
    apply (subst_te_open_qe_rec e1 K R X V Hc).
  - reflexivity.
  - f_equal; try reflexivity.
    + apply (subst_te_open_qe_rec e1 K R X V Hc).
    + apply (subst_te_open_qe_rec e2 K R X V Hc).
    + apply (subst_te_open_qe_rec e3 K R X V Hc).
Qed.

Lemma subst_te_open_qe_atom : forall (e:exp) X V (Y:atom),
  closed_qt V ->
  subst_te X V (open_qe e Y) = open_qe (subst_te X V e) Y.
Proof.
  intros. unfold open_qe.
  apply (subst_te_open_qe_rec e 0 (qua_fvar Y) X V H).
Qed.

(* Type-variable substitution commutes with term-variable opening. *)
Fixpoint subst_te_open_ee_rec (e:exp) {struct e} :
  forall K f X V,
    subst_te X V (open_ee_rec K f e) =
    open_ee_rec K (subst_te X V f) (subst_te X V e).
Proof.
  destruct e as [P i|i|a|P V0 e1|e1 e2|P V0 e1|e1 V0|P Q e1|e1 Q|e1 e2
    |P e1|P e1|e1 e2 e3|P e1 e2|e1|e1|P e1|P l|e1|e1 e2|P e1|P e1|P e1
    |b|e1 e2 e3];
    intros K f X V; simpl.
  - reflexivity.
  - destruct (eq_dec K i) as [Heq|Hneq]; simpl; reflexivity.
  - reflexivity.
  - f_equal. apply (subst_te_open_ee_rec e1 (S K) f X V).
  - f_equal; [apply (subst_te_open_ee_rec e1 K f X V)
            |apply (subst_te_open_ee_rec e2 K f X V)].
  - f_equal. apply (subst_te_open_ee_rec e1 (S K) f X V).
  - f_equal. apply (subst_te_open_ee_rec e1 K f X V).
  - f_equal. apply (subst_te_open_ee_rec e1 (S K) f X V).
  - f_equal. apply (subst_te_open_ee_rec e1 K f X V).
  - f_equal; [apply (subst_te_open_ee_rec e1 K f X V)
            |apply (subst_te_open_ee_rec e2 (S K) f X V)].
  - f_equal. apply (subst_te_open_ee_rec e1 K f X V).
  - f_equal. apply (subst_te_open_ee_rec e1 K f X V).
  - f_equal; [apply (subst_te_open_ee_rec e1 K f X V)
            |apply (subst_te_open_ee_rec e2 (S K) f X V)
            |apply (subst_te_open_ee_rec e3 (S K) f X V)].
  - f_equal; [apply (subst_te_open_ee_rec e1 K f X V)
            |apply (subst_te_open_ee_rec e2 K f X V)].
  - f_equal. apply (subst_te_open_ee_rec e1 K f X V).
  - f_equal. apply (subst_te_open_ee_rec e1 K f X V).
  - f_equal. apply (subst_te_open_ee_rec e1 K f X V).
  - reflexivity.
  - f_equal. apply (subst_te_open_ee_rec e1 K f X V).
  - f_equal; [apply (subst_te_open_ee_rec e1 K f X V)
            |apply (subst_te_open_ee_rec e2 K f X V)].
  - f_equal. apply (subst_te_open_ee_rec e1 K f X V).
  - f_equal. apply (subst_te_open_ee_rec e1 K f X V).
  - f_equal. apply (subst_te_open_ee_rec e1 K f X V).
  - reflexivity.
  - f_equal; [apply (subst_te_open_ee_rec e1 K f X V)
            |apply (subst_te_open_ee_rec e2 K f X V)
            |apply (subst_te_open_ee_rec e3 K f X V)].
Qed.

Lemma subst_te_open_ee_atom : forall (e:exp) X V (Y:atom),
  subst_te X V (open_ee e Y) = open_ee (subst_te X V e) Y.
Proof.
  intros. unfold open_ee.
  apply (subst_te_open_ee_rec e 0 (exp_fvar Y) X V).
Qed.

(* ========================================================= *)
(* typing preservation under type substitution                *)
(* ========================================================= *)

Lemma typing_subst_te_gen : forall (E:env) Q e T,
  typing E Q e T ->
  forall E1 X U E2 V,
    E = E1 ++ X ~ bind_sub U ++ E2 ->
    wf_env (subst_te_env X V (E1++E2)) ->
    wf_typ (subst_te_env X V (E1++E2)) V ->
    sub (subst_te_env X V (E1++E2)) V (subst_tt X V U) ->
    typing (subst_te_env X V (E1++E2)) Q (subst_te X V e) (subst_tqt X V T).
Proof.
  intros E Q e T H.
  induction H as [E P0 i Hwfi HP
    | E x0 Tb Hwfv Hb
    | L0 E P0 V0 e1 T1' Hp IHp
    | Qa T1x E e1 e2 T2 H1 IH1 H2 IH2
    | L0 E P0 V0 e1 T1' Hp IHp
    | Qa T1x E e1 Ta T2 H1 IH1 Hs
    | L0 E P0 Qb e1 T1' HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1x T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1x T2 P0 e1 E Qa HP H1 IH1 HT2
    | T1x T2 P0 e1 E Qa HP H1 IH1 HT1
    | L T1x T2 P0 T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1x T2 P0 e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1x T2 P0 e0 E H1 IH1
    | Qa T1x T2 P0 e0 E H1 IH1
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3];
    intros E1 X U E2 V Heq Hw HV Hsub; subst E.
  - (* int *) simpl. eapply typing_int.
    + exact Hw.
    + apply (wf_qua_subst_te (E1 ++ X ~ bind_sub U ++ E2) P0 HP
               E1 X U E2 V eq_refl).
  - (* var *) simpl. eapply typing_var.
    + exact Hw.
    + eapply binds_typ_subst_te_mid; exact Hb.
  - (* abs *) simpl. eapply typing_abs with (L := L0 \u dom (E1++E2) \u singleton X).
    intros y Hy.
    assert (HyL : y `notin` L0) by
      (exact (notin_union_1 y L0 (dom (E1++E2) `union` singleton X) Hy)).
    assert (HyD : y `notin` dom (E1++E2)) by
      (exact (notin_union_1 y (dom (E1++E2)) (singleton X)
                (notin_union_2 y L0 (dom (E1++E2) `union` singleton X) Hy))).
    assert (HyX : y `notin` singleton X) by
      (exact (notin_union_2 y (dom (E1++E2)) (singleton X)
                (notin_union_2 y L0 (dom (E1++E2) `union` singleton X) Hy))).
    assert (Hyx : y <> X) by (symmetry; exact (notin_singleton_1 X y HyX)).
    pose proof (Hp y HyL) as Hty.
    destruct (wf_env_typ_inv _ _ _ (typing_wf_env _ _ _ _ Hty)) as [Hwtail [HV0 _]].
    assert (HV0' : wf_qtyp (subst_te_env X V (E1++E2)) (subst_tqt X V V0)).
    { apply (wf_qtyp_subst_te (E1 ++ X ~ bind_sub U ++ E2) V0 HV0
               E1 X U E2 V eq_refl Hw HV). }
    assert (HwE'' : wf_env (subst_te_env X V ((y ~ bind_typ V0 ++ E1) ++ E2))).
    { rewrite app_assoc. simpl. eapply wf_env_typ.
      - exact Hw.
      - exact HV0'.
      - apply (proj2 (notin_dom_subst_te_env (E1++E2) X V y)). exact HyD. }
    assert (HVE'' : wf_typ (subst_te_env X V ((y ~ bind_typ V0 ++ E1) ++ E2)) V).
    { change (wf_typ ((y, bind_typ (subst_tqt X V V0)) :: subst_te_env X V (E1++E2)) V).
      eapply wf_typ_extends; [| exact HV]. apply extends_cons. }
    assert (Hsub'' : sub (subst_te_env X V ((y ~ bind_typ V0 ++ E1) ++ E2))
                          V (subst_tt X V U)).
    { eapply sub_extends; [exact Hsub | | exact HwE''].
      change (extends (subst_te_env X V (E1++E2))
                ((y, bind_typ (subst_tqt X V V0)) :: subst_te_env X V (E1++E2))).
      apply extends_cons. }
    pose proof (IHp y HyL (y ~ bind_typ V0 ++ E1) X U E2 V
                  ltac:(rewrite app_assoc; reflexivity) HwE'' HVE'' Hsub'') as HI.
    rewrite subst_te_open_ee_atom in HI.
    rewrite app_assoc in HI. simpl in HI.
    exact HI.
  - (* app *) simpl. eapply typing_app.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
    + apply (IH2 E1 X U E2 V eq_refl Hw HV Hsub).
  - (* tabs *) simpl. eapply typing_tabs with (L := L0 \u dom (E1++E2) \u singleton X).
    intros Y HY.
    assert (HYL : Y `notin` L0) by
      (exact (notin_union_1 Y L0 (dom (E1++E2) `union` singleton X) HY)).
    assert (HYD : Y `notin` dom (E1++E2)) by
      (exact (notin_union_1 Y (dom (E1++E2)) (singleton X)
                (notin_union_2 Y L0 (dom (E1++E2) `union` singleton X) HY))).
    assert (HYX : Y `notin` singleton X) by
      (exact (notin_union_2 Y (dom (E1++E2)) (singleton X)
                (notin_union_2 Y L0 (dom (E1++E2) `union` singleton X) HY))).
    assert (HXY : Y <> X) by (symmetry; exact (notin_singleton_1 X Y HYX)).
    pose proof (Hp Y HYL) as Hty.
    destruct (wf_env_sub_inv _ _ _ (typing_wf_env _ _ _ _ Hty)) as [Hwtail [HV0 _]].
    assert (Hct : closed_tt V) by (apply wf_typ_closed_tt in HV; exact HV).
    assert (HV0' : wf_typ (subst_te_env X V (E1++E2)) (subst_tt X V V0)).
    { apply (wf_typ_subst_te (E1 ++ X ~ bind_sub U ++ E2) V0 HV0
               E1 X U E2 V eq_refl Hw HV). }
    assert (HwE'' : wf_env (subst_te_env X V ((Y ~ bind_sub V0 ++ E1) ++ E2))).
    { rewrite app_assoc. simpl. eapply wf_env_sub.
      - exact Hw.
      - exact HV0'.
      - apply (proj2 (notin_dom_subst_te_env (E1++E2) X V Y)). exact HYD. }
    assert (HVE'' : wf_typ (subst_te_env X V ((Y ~ bind_sub V0 ++ E1) ++ E2)) V).
    { change (wf_typ ((Y, bind_sub (subst_tt X V V0)) :: subst_te_env X V (E1++E2)) V).
      eapply wf_typ_extends; [| exact HV]. apply extends_cons. }
    assert (Hsub'' : sub (subst_te_env X V ((Y ~ bind_sub V0 ++ E1) ++ E2))
                          V (subst_tt X V U)).
    { eapply sub_extends; [exact Hsub | | exact HwE''].
      change (extends (subst_te_env X V (E1++E2))
                ((Y, bind_sub (subst_tt X V V0)) :: subst_te_env X V (E1++E2))).
      apply extends_cons. }
    pose proof (IHp Y HYL (Y ~ bind_sub V0 ++ E1) X U E2 V
                  ltac:(rewrite app_assoc; reflexivity) HwE'' HVE'' Hsub'') as HI.
    rewrite (subst_te_open_te_atom e1 X V Y Hct HXY) in HI.
    rewrite (subst_tqt_open_tqt_atom T1' X V Y Hct HXY) in HI.
    rewrite app_assoc in HI. simpl in HI.
    exact HI.
  - (* tapp *) simpl.
    assert (Hct : closed_tt V) by (apply wf_typ_closed_tt in HV; exact HV).
    unfold open_tqt. rewrite (subst_tqt_open_tqt_rec T2 0 Ta X V Hct).
    eapply typing_tapp.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
    + apply (sub_subst_te (E1 ++ X ~ bind_sub U ++ E2) Ta T1x Hs
               E1 X U E2 V eq_refl Hw HV Hsub).
  - (* qabs *) simpl. eapply typing_qabs with (L := L0 \u dom (E1++E2) \u singleton X).
    + apply (wf_qua_subst_te (E1 ++ X ~ bind_sub U ++ E2) P0 HP
               E1 X U E2 V eq_refl).
    + intros Y HY.
      assert (HYL : Y `notin` L0) by
        (exact (notin_union_1 Y L0 (dom (E1++E2) `union` singleton X) HY)).
      assert (HYD : Y `notin` dom (E1++E2)) by
        (exact (notin_union_1 Y (dom (E1++E2)) (singleton X)
                  (notin_union_2 Y L0 (dom (E1++E2) `union` singleton X) HY))).
      pose proof (Hp Y HYL) as Hty.
      destruct (wf_env_qua_inv _ _ _ (typing_wf_env _ _ _ _ Hty)) as [Hwtail [HQb _]].
      assert (Hcq : closed_qt V) by (apply wf_typ_closed_qt in HV; exact HV).
      assert (HQb' : wf_qua (subst_te_env X V (E1++E2)) Qb).
      { apply (wf_qua_subst_te (E1 ++ X ~ bind_sub U ++ E2) Qb HQb
                 E1 X U E2 V eq_refl). }
      assert (HwE'' : wf_env (subst_te_env X V ((Y ~ bind_qua Qb ++ E1) ++ E2))).
      { rewrite app_assoc. simpl. eapply wf_env_qua.
        - exact Hw.
        - exact HQb'.
        - apply (proj2 (notin_dom_subst_te_env (E1++E2) X V Y)). exact HYD. }
      assert (HVE'' : wf_typ (subst_te_env X V ((Y ~ bind_qua Qb ++ E1) ++ E2)) V).
      { change (wf_typ ((Y, bind_qua Qb) :: subst_te_env X V (E1++E2)) V).
        eapply wf_typ_extends; [| exact HV]. apply extends_cons. }
      assert (Hsub'' : sub (subst_te_env X V ((Y ~ bind_qua Qb ++ E1) ++ E2))
                            V (subst_tt X V U)).
      { eapply sub_extends; [exact Hsub | | exact HwE''].
        change (extends (subst_te_env X V (E1++E2))
                  ((Y, bind_qua Qb) :: subst_te_env X V (E1++E2))).
        apply extends_cons. }
      pose proof (IHp Y HYL (Y ~ bind_qua Qb ++ E1) X U E2 V
                    ltac:(rewrite app_assoc; reflexivity) HwE'' HVE'' Hsub'') as HI.
      rewrite (subst_te_open_qe_atom e1 X V Y Hcq) in HI.
      rewrite (subst_tqt_open_qqt_atom T1' X V Y Hcq) in HI.
      rewrite app_assoc in HI. simpl in HI.
      exact HI.
  - (* qapp *) simpl.
    assert (Hcq : closed_qt V) by (apply wf_typ_closed_qt in HV; exact HV).
    unfold open_qqt. rewrite (subst_tqt_open_qqt_rec T0 0 Qa X V Hcq).
    eapply typing_qapp.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
    + apply (subqual_subst_te (E1 ++ X ~ bind_sub U ++ E2) Qa Qb Hs
               E1 X U E2 V eq_refl Hw HV).
  - (* sub *) simpl. eapply typing_sub.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
    + apply (subqtype_subst_te (E1 ++ X ~ bind_sub U ++ E2) S T0 Hs
               E1 X U E2 V eq_refl Hw HV Hsub).
  - (* subqual *) simpl. eapply typing_subqual.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
    + apply (subqual_subst_te (E1 ++ X ~ bind_sub U ++ E2) Qa R Hs
               E1 X U E2 V eq_refl Hw HV).
  - (* let *) simpl. eapply typing_let with (L := L \u dom (E1++E2) \u singleton X).
    + apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
    + intros y Hy.
      assert (HyL : y `notin` L) by
        (exact (notin_union_1 y L (dom (E1++E2) `union` singleton X) Hy)).
      assert (HyD : y `notin` dom (E1++E2)) by
        (exact (notin_union_1 y (dom (E1++E2)) (singleton X)
                  (notin_union_2 y L (dom (E1++E2) `union` singleton X) Hy))).
      pose proof (H2 y HyL) as Hty.
      destruct (wf_env_typ_inv _ _ _ (typing_wf_env _ _ _ _ Hty)) as [Hwtail [HT1 _]].
      assert (HT1' : wf_qtyp (subst_te_env X V (E1++E2)) (subst_tqt X V T1x)).
      { apply (wf_qtyp_subst_te (E1 ++ X ~ bind_sub U ++ E2) T1x HT1
                 E1 X U E2 V eq_refl Hw HV). }
      assert (HwE'' : wf_env (subst_te_env X V ((y ~ bind_typ T1x ++ E1) ++ E2))).
      { rewrite app_assoc. simpl. eapply wf_env_typ.
        - exact Hw.
        - exact HT1'.
        - apply (proj2 (notin_dom_subst_te_env (E1++E2) X V y)). exact HyD. }
      assert (HVE'' : wf_typ (subst_te_env X V ((y ~ bind_typ T1x ++ E1) ++ E2)) V).
      { change (wf_typ ((y, bind_typ (subst_tqt X V T1x)) :: subst_te_env X V (E1++E2)) V).
        eapply wf_typ_extends; [| exact HV]. apply extends_cons. }
      assert (Hsub'' : sub (subst_te_env X V ((y ~ bind_typ T1x ++ E1) ++ E2))
                            V (subst_tt X V U)).
      { eapply sub_extends; [exact Hsub | | exact HwE''].
        change (extends (subst_te_env X V (E1++E2))
                  ((y, bind_typ (subst_tqt X V T1x)) :: subst_te_env X V (E1++E2))).
        apply extends_cons. }
      pose proof (IH2 y HyL (y ~ bind_typ T1x ++ E1) X U E2 V
                    ltac:(rewrite app_assoc; reflexivity) HwE'' HVE'' Hsub'') as HI.
      rewrite subst_te_open_ee_atom in HI.
      rewrite app_assoc in HI. simpl in HI.
      exact HI.
  - (* inl *) simpl. eapply typing_inl.
    + apply (wf_qua_subst_te (E1 ++ X ~ bind_sub U ++ E2) P0 HP
               E1 X U E2 V eq_refl).
    + apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
    + apply (wf_qtyp_subst_te (E1 ++ X ~ bind_sub U ++ E2) T2 HT2
               E1 X U E2 V eq_refl Hw HV).
  - (* inr *) simpl. eapply typing_inr.
    + apply (wf_qua_subst_te (E1 ++ X ~ bind_sub U ++ E2) P0 HP
               E1 X U E2 V eq_refl).
    + apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
    + apply (wf_qtyp_subst_te (E1 ++ X ~ bind_sub U ++ E2) T1x HT1
               E1 X U E2 V eq_refl Hw HV).
  - (* case *) simpl. eapply typing_case with (L := L \u dom (E1++E2) \u singleton X).
    + apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
    + intros y Hy.
      assert (HyL : y `notin` L) by
        (exact (notin_union_1 y L (dom (E1++E2) `union` singleton X) Hy)).
      assert (HyD : y `notin` dom (E1++E2)) by
        (exact (notin_union_1 y (dom (E1++E2)) (singleton X)
                  (notin_union_2 y L (dom (E1++E2) `union` singleton X) Hy))).
      pose proof (H2 y HyL) as Hty.
      destruct (wf_env_typ_inv _ _ _ (typing_wf_env _ _ _ _ Hty)) as [Hwtail [HT1 _]].
      assert (HT1' : wf_qtyp (subst_te_env X V (E1++E2)) (subst_tqt X V T1x)).
      { apply (wf_qtyp_subst_te (E1 ++ X ~ bind_sub U ++ E2) T1x HT1
                 E1 X U E2 V eq_refl Hw HV). }
      assert (HwE'' : wf_env (subst_te_env X V ((y ~ bind_typ T1x ++ E1) ++ E2))).
      { rewrite app_assoc. simpl. eapply wf_env_typ.
        - exact Hw.
        - exact HT1'.
        - apply (proj2 (notin_dom_subst_te_env (E1++E2) X V y)). exact HyD. }
      assert (HVE'' : wf_typ (subst_te_env X V ((y ~ bind_typ T1x ++ E1) ++ E2)) V).
      { change (wf_typ ((y, bind_typ (subst_tqt X V T1x)) :: subst_te_env X V (E1++E2)) V).
        eapply wf_typ_extends; [| exact HV]. apply extends_cons. }
      assert (Hsub'' : sub (subst_te_env X V ((y ~ bind_typ T1x ++ E1) ++ E2))
                            V (subst_tt X V U)).
      { eapply sub_extends; [exact Hsub | | exact HwE''].
        change (extends (subst_te_env X V (E1++E2))
                  ((y, bind_typ (subst_tqt X V T1x)) :: subst_te_env X V (E1++E2))).
        apply extends_cons. }
      pose proof (IH2 y HyL (y ~ bind_typ T1x ++ E1) X U E2 V
                    ltac:(rewrite app_assoc; reflexivity) HwE'' HVE'' Hsub'') as HI.
      rewrite subst_te_open_ee_atom in HI.
      rewrite app_assoc in HI. simpl in HI.
      exact HI.
    + intros y Hy.
      assert (HyL : y `notin` L) by
        (exact (notin_union_1 y L (dom (E1++E2) `union` singleton X) Hy)).
      assert (HyD : y `notin` dom (E1++E2)) by
        (exact (notin_union_1 y (dom (E1++E2)) (singleton X)
                  (notin_union_2 y L (dom (E1++E2) `union` singleton X) Hy))).
      pose proof (H3 y HyL) as Hty.
      destruct (wf_env_typ_inv _ _ _ (typing_wf_env _ _ _ _ Hty)) as [Hwtail [HT2 _]].
      assert (HT2' : wf_qtyp (subst_te_env X V (E1++E2)) (subst_tqt X V T2)).
      { apply (wf_qtyp_subst_te (E1 ++ X ~ bind_sub U ++ E2) T2 HT2
                 E1 X U E2 V eq_refl Hw HV). }
      assert (HwE'' : wf_env (subst_te_env X V ((y ~ bind_typ T2 ++ E1) ++ E2))).
      { rewrite app_assoc. simpl. eapply wf_env_typ.
        - exact Hw.
        - exact HT2'.
        - apply (proj2 (notin_dom_subst_te_env (E1++E2) X V y)). exact HyD. }
      assert (HVE'' : wf_typ (subst_te_env X V ((y ~ bind_typ T2 ++ E1) ++ E2)) V).
      { change (wf_typ ((y, bind_typ (subst_tqt X V T2)) :: subst_te_env X V (E1++E2)) V).
        eapply wf_typ_extends; [| exact HV]. apply extends_cons. }
      assert (Hsub'' : sub (subst_te_env X V ((y ~ bind_typ T2 ++ E1) ++ E2))
                            V (subst_tt X V U)).
      { eapply sub_extends; [exact Hsub | | exact HwE''].
        change (extends (subst_te_env X V (E1++E2))
                  ((y, bind_typ (subst_tqt X V T2)) :: subst_te_env X V (E1++E2))).
        apply extends_cons. }
      pose proof (IH3 y HyL (y ~ bind_typ T2 ++ E1) X U E2 V
                    ltac:(rewrite app_assoc; reflexivity) HwE'' HVE'' Hsub'') as HI.
      rewrite subst_te_open_ee_atom in HI.
      rewrite app_assoc in HI. simpl in HI.
      exact HI.
  - (* pair *) simpl. eapply typing_pair.
    + apply (wf_qua_subst_te (E1 ++ X ~ bind_sub U ++ E2) P0 HP
               E1 X U E2 V eq_refl).
    + apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
    + apply (IH2 E1 X U E2 V eq_refl Hw HV Hsub).
  - (* first *) simpl. eapply typing_first.
    apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
  - (* second *) simpl. eapply typing_second.
    apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
  - (* upqual *) simpl. eapply typing_upqual.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
    + apply (subqual_subst_te (E1 ++ X ~ bind_sub U ++ E2) Qa P0 Hs
               E1 X U E2 V eq_refl Hw HV).
  - (* check *) simpl. eapply typing_check.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
    + apply (subqual_subst_te (E1 ++ X ~ bind_sub U ++ E2) Qa P0 Hs
               E1 X U E2 V eq_refl Hw HV).
  - (* without *) simpl. eapply typing_without.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
    + apply (subqual_subst_te (E1 ++ X ~ bind_sub U ++ E2) R (qua_negate P0) Hs
               E1 X U E2 V eq_refl Hw HV).
  - (* do *) simpl. apply typing_do. exact Hw.
  - (* if0 *) simpl. eapply typing_if0.
    + apply (IH1 E1 X U E2 V eq_refl Hw HV Hsub).
    + apply (IH2 E1 X U E2 V eq_refl Hw HV Hsub).
    + apply (IH3 E1 X U E2 V eq_refl Hw HV Hsub).
Qed.

(* ================= ChunkTypingQe.v ================= *)

(* ========================================================= *)
(* Qualifier-variable substitution on environments (qe)       *)
(* ========================================================= *)

Definition subst_env_qb (X:atom) (R:qua) (E:env) : env :=
  map (fun b => subst_qb X R b) E.

Lemma subst_env_qb_app : forall (E1 E2:env) X R,
  subst_env_qb X R (E1 ++ E2) =
  subst_env_qb X R E1 ++ subst_env_qb X R E2.
Proof.
  intros. unfold subst_env_qb. apply map_app.
Qed.

Lemma subst_env_qb_cons : forall (y:atom) b (E:env) X R,
  subst_env_qb X R ((y,b) :: E) =
  (y, subst_qb X R b) :: subst_env_qb X R E.
Proof. intros. destruct b; reflexivity. Qed.

Lemma dom_subst_env_qb : forall (E:env) X R,
  dom (subst_env_qb X R E) = dom E.
Proof.
  induction E as [|[y b] E IH]; intros X R; simpl.
  - reflexivity.
  - destruct b; simpl; rewrite IH; reflexivity.
Qed.

Lemma binds_subst_env_qb : forall (E:env) z b X R,
  binds z b E -> binds z (subst_qb X R b) (subst_env_qb X R E).
Proof.
  induction E as [|[y c] E IH]; intros z b X R H.
  - unfold binds in H; destruct H.
  - destruct c; simpl in *.
    + unfold binds in H. simpl in H. destruct H as [Heq|H].
      * left; inversion Heq; subst; reflexivity.
      * right; apply IH; exact H.
    + unfold binds in H. simpl in H. destruct H as [Heq|H].
      * left; inversion Heq; subst; reflexivity.
      * right; apply IH; exact H.
    + unfold binds in H. simpl in H. destruct H as [Heq|H].
      * left; inversion Heq; subst; reflexivity.
      * right; apply IH; exact H.
Qed.

Lemma binds_sub_subst_env_qb : forall (E:env) z U X R,
  binds z (bind_sub U) E ->
  binds z (bind_sub (subst_qt X R U)) (subst_env_qb X R E).
Proof. intros. eapply binds_subst_env_qb with (b := bind_sub U). exact H. Qed.

Lemma binds_typ_subst_env_qb : forall (E:env) z T X R,
  binds z (bind_typ T) E ->
  binds z (bind_typ (subst_qqt X R T)) (subst_env_qb X R E).
Proof. intros. eapply binds_subst_env_qb with (b := bind_typ T). exact H. Qed.

Lemma binds_qua_subst_env_qb : forall (E:env) z Q X R,
  binds z (bind_qua Q) E ->
  binds z (bind_qua (subst_qq X R Q)) (subst_env_qb X R E).
Proof. intros. eapply binds_subst_env_qb with (b := bind_qua Q). exact H. Qed.

Lemma binds_qua_mid : forall (E1:env) X (Q0:qua) (E2:env),
  binds X (bind_qua Q0) (E1 ++ X ~ bind_qua Q0 ++ E2).
Proof.
  intros. unfold binds. apply in_app_iff. right.
  apply in_app_iff. left. simpl. left. reflexivity.
Qed.

Lemma binds_typ_remove_qua_mid : forall (E1:env) X (Q0:qua) (E2:env) z T,
  binds z (bind_typ T) (E1 ++ X ~ bind_qua Q0 ++ E2) ->
  binds z (bind_typ T) (E1 ++ E2).
Proof.
  intros E1 X Q0 E2 z T H. unfold binds in *.
  apply in_app_iff. apply in_app_iff in H. destruct H as [H|H].
  - left; auto.
  - simpl in H. destruct H as [Heq|H].
    + inversion Heq; subst; discriminate.
    + right; auto.
Qed.

(* ========================================================= *)
(* Concretized qualifiers are unaffected by qe-substitution  *)
(* ========================================================= *)

Lemma concretize_subst_qq : forall (Q:qua) b,
  concretize Q = Some b -> forall X R, subst_qq X R Q = Q.
Proof.
  induction Q as [b0|n|a|Q1 IH1 Q2 IH2|Q1 IH1 Q2 IH2|Q1 IH1];
    intros b Hc X R; simpl in *.
  - reflexivity.
  - discriminate.
  - discriminate.
  - destruct (concretize Q1) as [b1|] eqn:E1;
      destruct (concretize Q2) as [b2|] eqn:E2; try discriminate;
      simpl in Hc; injection Hc as Hb; subst b.
    simpl. rewrite (IH1 b1 eq_refl X R). rewrite (IH2 b2 eq_refl X R). reflexivity.
  - destruct (concretize Q1) as [b1|] eqn:E1;
      destruct (concretize Q2) as [b2|] eqn:E2; try discriminate;
      simpl in Hc; injection Hc as Hb; subst b.
    simpl. rewrite (IH1 b1 eq_refl X R). rewrite (IH2 b2 eq_refl X R). reflexivity.
  - destruct (concretize Q1) as [b1|] eqn:E1; try discriminate;
      simpl in Hc; injection Hc as Hb; subst b.
    simpl. rewrite (IH1 b1 eq_refl X R). reflexivity.
Qed.

(* ========================================================= *)
(* Well-formedness of qualifiers after qe-substitution into M *)
(* ========================================================= *)

Fixpoint wf_qua_subst_qe_M (Q:qua) {struct Q} :
  forall (E1:env) X (Q0:qua) (E2:env) R,
    wf_qua (E1 ++ X ~ bind_qua Q0 ++ E2) Q ->
    wf_qua (subst_env_qb X R (E1 ++ E2)) R ->
    wf_qua (subst_env_qb X R (E1 ++ E2)) (subst_qq X R Q).
Proof.
  destruct Q as [b|n|a|Q1 Q2|Q1 Q2|Q1]; intros E1 X Q0 E2 R H HR; simpl.
  - apply wf_qua_base.
  - inversion H.
  - inversion H; subst. destruct (eq_dec a X) as [Heq|Hneq].
    + subst. exact HR.
    + eapply wf_qua_fvar.
      apply binds_qua_subst_env_qb.
      match goal with
      | Hb : binds a (bind_qua ?R0) (E1 ++ X ~ bind_qua Q0 ++ E2) |- _ =>
          eapply binds_remove_qua_neq_name; [exact Hneq | exact Hb] end.
  - inversion H; subst. apply wf_qua_meet.
    + apply (wf_qua_subst_qe_M Q1 E1 X Q0 E2 R); assumption.
    + apply (wf_qua_subst_qe_M Q2 E1 X Q0 E2 R); assumption.
  - inversion H; subst. apply wf_qua_join.
    + apply (wf_qua_subst_qe_M Q1 E1 X Q0 E2 R); assumption.
    + apply (wf_qua_subst_qe_M Q2 E1 X Q0 E2 R); assumption.
  - inversion H; subst. apply wf_qua_negate.
    apply (wf_qua_subst_qe_M Q1 E1 X Q0 E2 R); assumption.
Qed.

Lemma wf_tq_subst_qe_M :
  (forall (E:env) (T:typ), wf_typ E T ->
     forall (E1:env) X (Q0:qua) (E2:env) R,
       E = E1 ++ X ~ bind_qua Q0 ++ E2 ->
       wf_qua (subst_env_qb X R (E1 ++ E2)) R ->
       wf_typ (subst_env_qb X R (E1 ++ E2)) (subst_qt X R T)) /\
  (forall (E:env) (T:qtyp), wf_qtyp E T ->
     forall (E1:env) X (Q0:qua) (E2:env) R,
       E = E1 ++ X ~ bind_qua Q0 ++ E2 ->
       wf_qua (subst_env_qb X R (E1 ++ E2)) R ->
       wf_qtyp (subst_env_qb X R (E1 ++ E2)) (subst_qqt X R T)).
Proof.
  apply wf_tq_mut
    with (P := fun E T _ => forall (E1:env) X (Q0:qua) (E2:env) R,
              E = E1 ++ X ~ bind_qua Q0 ++ E2 ->
              wf_qua (subst_env_qb X R (E1 ++ E2)) R ->
              wf_typ (subst_env_qb X R (E1 ++ E2)) (subst_qt X R T))
         (P0 := fun E T _ => forall (E1:env) X (Q0:qua) (E2:env) R,
              E = E1 ++ X ~ bind_qua Q0 ++ E2 ->
              wf_qua (subst_env_qb X R (E1 ++ E2)) R ->
              wf_qtyp (subst_env_qb X R (E1 ++ E2)) (subst_qqt X R T)).
  - intros E E1 X Q0 E2 R HE HR. subst. constructor.
  - intros E E1 X Q0 E2 R HE HR. subst. constructor.
  - intros U E Y b E1 X Q0 E2 R HE HR. subst.
    simpl. eapply wf_typ_var.
    apply binds_sub_subst_env_qb.
    apply (binds_sub_remove_qua_mid E1 X Q0 E2 Y U b).
  - intros E T1 T2 w1 IH1 w2 IH2 E1 X Q0 E2 R HE HR. subst.
    simpl. apply wf_typ_arrow.
    + apply (IH1 E1 X Q0 E2 R); [reflexivity|exact HR].
    + apply (IH2 E1 X Q0 E2 R); [reflexivity|exact HR].
  - intros L E T1 T2 w1 IH1 w0 IH0 E1 XX Q0 E2 R HE HR. subst.
    simpl. apply wf_typ_all with (L := L \u singleton XX \u dom (subst_env_qb XX R (E1 ++ E2))).
    + apply (IH1 E1 XX Q0 E2 R); [reflexivity|exact HR].
    + intros Z HZ.
      assert (HZL : Z `notin` L) by (apply notin_union_1 in HZ; exact HZ).
      assert (HZs : Z `notin` singleton XX) by (apply notin_union_2 in HZ; apply notin_union_1 in HZ; exact HZ).
      assert (HZX : Z <> XX) by (symmetry; exact (notin_singleton_1 XX Z HZs)).
      pose proof (IH0 Z HZL (Z ~ bind_sub T1 ++ E1) XX Q0 E2 R) as Hq.
      rewrite app_assoc in Hq.
      assert (HR' : wf_qua (subst_env_qb XX R ((Z ~ bind_sub T1 ++ E1) ++ E2)) R).
      { eapply wf_qua_extends; [apply extends_cons | exact HR]. }
      specialize (Hq eq_refl HR').
      rewrite (subst_qqt_open_tqt_atom T2 XX R Z) in Hq.
      exact Hq.
  - intros L E Q T wq w0 IH0 E1 XX Q0 E2 R HE HR. subst.
    simpl. apply wf_typ_qall with (L := L \u singleton XX \u dom (subst_env_qb XX R (E1 ++ E2))).
    + apply (wf_qua_subst_qe_M Q E1 XX Q0 E2 R); [exact wq|exact HR].
    + intros Z HZ.
      assert (HZL : Z `notin` L) by (apply notin_union_1 in HZ; exact HZ).
      assert (HZs : Z `notin` singleton XX) by (apply notin_union_2 in HZ; apply notin_union_1 in HZ; exact HZ).
      assert (HZX : Z <> XX) by (symmetry; exact (notin_singleton_1 XX Z HZs)).
      pose proof (IH0 Z HZL (Z ~ bind_qua Q ++ E1) XX Q0 E2 R) as Hq.
      rewrite app_assoc in Hq.
      assert (HR' : wf_qua (subst_env_qb XX R ((Z ~ bind_qua Q ++ E1) ++ E2)) R).
      { eapply wf_qua_extends; [apply extends_cons | exact HR]. }
      specialize (Hq eq_refl HR').
      assert (HcR : closed_qq R) by (apply (wf_qua_closed_qq _ _ HR)).
      rewrite (subst_qqt_open_qqt_atom T XX R Z HcR HZX) in Hq.
      exact Hq.
  - intros E T1 T2 w1 IH1 w2 IH2 E1 X Q0 E2 R HE HR. subst.
    simpl. apply wf_typ_sum.
    + apply (IH1 E1 X Q0 E2 R); [reflexivity|exact HR].
    + apply (IH2 E1 X Q0 E2 R); [reflexivity|exact HR].
  - intros E T1 T2 w1 IH1 w2 IH2 E1 X Q0 E2 R HE HR. subst.
    simpl. apply wf_typ_pair.
    + apply (IH1 E1 X Q0 E2 R); [reflexivity|exact HR].
    + apply (IH2 E1 X Q0 E2 R); [reflexivity|exact HR].
  - intros E Q T wq wT IHT E1 X Q0 E2 R HE HR. subst.
    simpl. apply wf_qtyp_qtyp.
    + apply (wf_qua_subst_qe_M Q E1 X Q0 E2 R); [exact wq|exact HR].
    + apply (IHT E1 X Q0 E2 R); [reflexivity|exact HR].
Qed.

Lemma wf_typ_subst_qe_M : forall (E:env) (T:typ),
  wf_typ E T ->
  forall (E1:env) X (Q0:qua) (E2:env) R,
    E = E1 ++ X ~ bind_qua Q0 ++ E2 ->
    wf_qua (subst_env_qb X R (E1 ++ E2)) R ->
    wf_typ (subst_env_qb X R (E1 ++ E2)) (subst_qt X R T).
Proof. intros. eapply (proj1 wf_tq_subst_qe_M); eauto. Qed.

Lemma wf_qtyp_subst_qe_M : forall (E:env) (T:qtyp),
  wf_qtyp E T ->
  forall (E1:env) X (Q0:qua) (E2:env) R,
    E = E1 ++ X ~ bind_qua Q0 ++ E2 ->
    wf_qua (subst_env_qb X R (E1 ++ E2)) R ->
    wf_qtyp (subst_env_qb X R (E1 ++ E2)) (subst_qqt X R T).
Proof. intros. eapply (proj2 wf_tq_subst_qe_M); eauto. Qed.

(* ========================================================= *)
(* Opening only adds free variables (fv_qt / fv_qqt)          *)
(* ========================================================= *)

Fixpoint fv_qt_open_tt_subset (T:typ) {struct T} :
  forall K Y X, X `in` fv_qt T -> X `in` fv_qt (open_tt_rec K (typ_fvar Y) T)
with fv_qqt_open_tqt_subset (T:qtyp) {struct T} :
  forall K Y X, X `in` fv_qqt T -> X `in` fv_qqt (open_tqt_rec K (typ_fvar Y) T).
Proof.
  - destruct T as [| |n|a|T1 T2|T1 T2|Q T2|T1 T2|T1 T2|T1]; intros K Y X Hin; simpl in *.
    + exact Hin.
    + exact Hin.
    + destruct (eq_dec K n); simpl; exact Hin.
    + exact Hin.
    + apply (proj2 (union_iff _ _ _)). destruct (proj1 (union_iff _ _ _) Hin) as [H|H];
        [left; apply (fv_qqt_open_tqt_subset T1 K Y X H)
        |right; apply (fv_qqt_open_tqt_subset T2 (S K) Y X H)].
    + apply (proj2 (union_iff _ _ _)). destruct (proj1 (union_iff _ _ _) Hin) as [H|H];
        [left; apply (fv_qt_open_tt_subset T1 K Y X H)
        |right; apply (fv_qqt_open_tqt_subset T2 (S K) Y X H)].
    + apply (proj2 (union_iff _ _ _)). destruct (proj1 (union_iff _ _ _) Hin) as [H|H].
      * left; exact H.
      * right; apply (fv_qqt_open_tqt_subset T2 (S K) Y X H).
    + apply (proj2 (union_iff _ _ _)). destruct (proj1 (union_iff _ _ _) Hin) as [H|H];
        [left; apply (fv_qqt_open_tqt_subset T1 K Y X H)
        |right; apply (fv_qqt_open_tqt_subset T2 K Y X H)].
    + apply (proj2 (union_iff _ _ _)). destruct (proj1 (union_iff _ _ _) Hin) as [H|H];
        [left; apply (fv_qqt_open_tqt_subset T1 K Y X H)
        |right; apply (fv_qqt_open_tqt_subset T2 K Y X H)].
    + apply (fv_qqt_open_tqt_subset T1 K Y X Hin).
  - destruct T as [Q T]. intros K Y X Hin. simpl in *.
    apply (proj2 (union_iff _ _ _)). destruct (proj1 (union_iff _ _ _) Hin) as [H|H].
    + left; exact H.
    + right; apply (fv_qt_open_tt_subset T K Y X H).
Qed.

(* ========================================================= *)
(* Free variables of well-formed items lie in the environment *)
(* ========================================================= *)

Lemma wf_qua_fv_dom_notin : forall (E:env) (Q:qua),
  wf_qua E Q -> forall X, X `notin` dom E -> X `notin` fv_qq Q.
Proof.
  intros E Q H. induction H as [E0 b|R0 E0 Y Hb|E0 Q1 Q2 H1 IH1 H2 IH2
    |E0 Q1 Q2 H1 IH1 H2 IH2|E0 Q1 H1 IH1]; intros X HX; simpl.
  - apply notin_empty_1.
  - apply notin_singleton. intro HXY. subst Y.
    match goal with Hb0 : binds ?Z (bind_qua ?R) E0 |- _ => apply HX; exact (binds_In binding Z (bind_qua R) E0 Hb0) end.
  - apply notin_union; [apply IH1|apply IH2]; exact HX.
  - apply notin_union; [apply IH1|apply IH2]; exact HX.
  - apply IH1. exact HX.
Qed.

Lemma wf_typ_qtyp_fv_qt_dom :
  (forall (E:env) (T:typ), wf_typ E T ->
     forall X, X `notin` dom E -> X `notin` fv_qt T) /\
  (forall (E:env) (T:qtyp), wf_qtyp E T ->
     forall X, X `notin` dom E -> X `notin` fv_qqt T).
Proof.
  apply wf_tq_mut
    with (P := fun E T _ => forall X, X `notin` dom E -> X `notin` fv_qt T)
         (P0 := fun E T _ => forall X, X `notin` dom E -> X `notin` fv_qqt T).
  - intros E X HX. simpl. apply notin_empty_1.
  - intros E X HX. simpl. apply notin_empty_1.
  - intros U E Y b X HX. simpl. apply notin_empty_1.
  - intros E T1 T2 w1 IH1 w2 IH2 X HX. simpl.
    apply notin_union; [apply IH1|apply IH2]; exact HX.
  - intros L E T1 T2 w1 IH1 w0 IH0 X HX. simpl.
    apply notin_union.
    + apply IH1. exact HX.
    + pick fresh Y for (L \u dom E \u singleton X).
      assert (HYL : Y `notin` L) by
        (apply notin_union_1 in Fr as H1; exact H1).
      assert (HYD : Y `notin` dom E) by
        (apply notin_union_2 in Fr as H1; apply notin_union_1 in H1 as H2; exact H2).
      assert (HYX : Y `notin` singleton X) by
        (apply notin_union_2 in Fr as H2; apply notin_union_2 in H2; exact H2).
      assert (HXY : X <> Y) by (apply (notin_singleton_1 X Y HYX)).
      assert (Hnotin : X `notin` fv_qqt (open_tqt T2 Y)).
      { apply (IH0 Y HYL). simpl. apply notin_add.
        - symmetry. exact HXY.
        - exact HX. }
      intro Hin. apply Hnotin.
      apply (fv_qqt_open_tqt_subset T2 0 Y X Hin).
  - intros L E Q T wq w0 IH0 X HX. simpl.
    apply notin_union.
    + apply (wf_qua_fv_dom_notin E Q wq X HX).
    + pick fresh Y for (L \u dom E \u singleton X).
      assert (HYL : Y `notin` L) by
        (apply notin_union_1 in Fr as H1; exact H1).
      assert (HYD : Y `notin` dom E) by
        (apply notin_union_2 in Fr as H1; apply notin_union_1 in H1 as H2; exact H2).
      assert (HYX : Y `notin` singleton X) by
        (apply notin_union_2 in Fr as H2; apply notin_union_2 in H2; exact H2).
      assert (HXY : X <> Y) by (apply (notin_singleton_1 X Y HYX)).
      assert (Hnotin : X `notin` fv_qqt (open_qqt T Y)).
      { apply (IH0 Y HYL). simpl. apply notin_add.
        - symmetry. exact HXY.
        - exact HX. }
      intro Hin. apply Hnotin.
      apply (fv_qqt_open_qqt_subset T 0 Y X Hin).
  - intros E T1 T2 w1 IH1 w2 IH2 X HX. simpl.
    apply notin_union; [apply IH1|apply IH2]; exact HX.
  - intros E T1 T2 w1 IH1 w2 IH2 X HX. simpl.
    apply notin_union; [apply IH1|apply IH2]; exact HX.
  - intros E Q T wq wT IHT X HX. simpl.
    apply notin_union.
    + apply (wf_qua_fv_dom_notin E Q wq X HX).
    + apply IHT. exact HX.
Qed.

Lemma wf_typ_fv_qt_dom : forall (E:env) (T:typ), wf_typ E T ->
  forall X, X `notin` dom E -> X `notin` fv_qt T.
Proof. intros. eapply (proj1 wf_typ_qtyp_fv_qt_dom); eauto. Qed.

Lemma wf_qtyp_fv_qqt_dom : forall (E:env) (T:qtyp), wf_qtyp E T ->
  forall X, X `notin` dom E -> X `notin` fv_qqt T.
Proof. intros. eapply (proj2 wf_typ_qtyp_fv_qt_dom); eauto. Qed.

(* ========================================================= *)
(* The mapped environment is the identity when X is not bound *)
(* ========================================================= *)

Lemma subst_env_qb_id : forall (E:env) X R,
  wf_env E -> X `notin` dom E -> subst_env_qb X R E = E.
Proof.
  induction E as [|[y b] E IH]; intros X R Hwf HX.
  - reflexivity.
  - simpl in HX. pose proof (notin_add_2 y X (dom E) HX) as HXE.
    destruct b as [U|T|Q].
    + change (wf_env (y ~ bind_sub U ++ E)) in Hwf.
      destruct (wf_env_sub_inv _ _ _ Hwf) as [HwfE [HU _]].
      simpl. rewrite (IH X R HwfE HXE).
      assert (HUeq : subst_qt X R U = U).
      { apply subst_qt_id. apply (wf_typ_fv_qt_dom E U HU X HXE). }
      rewrite HUeq. reflexivity.
    + change (wf_env (y ~ bind_typ T ++ E)) in Hwf.
      destruct (wf_env_typ_inv _ _ _ Hwf) as [HwfE [HT _]].
      simpl. rewrite (IH X R HwfE HXE).
      assert (HTeq : subst_qqt X R T = T).
      { apply subst_qqt_id. apply (wf_qtyp_fv_qqt_dom E T HT X HXE). }
      rewrite HTeq. reflexivity.
    + change (wf_env (y ~ bind_qua Q ++ E)) in Hwf.
      destruct (wf_env_qua_inv _ _ _ Hwf) as [HwfE [HQ _]].
      simpl. rewrite (IH X R HwfE HXE).
      assert (HQeq : subst_qq X R Q = Q).
      { apply subst_qq_id. apply (wf_qua_fv_dom_notin E Q HQ X HXE). }
      rewrite HQeq. reflexivity.
Qed.

(* ========================================================= *)
(* Subqualifier substitution for qualifier variables          *)
(* ========================================================= *)

Lemma subqual_subst_qe : forall (E:env) S T,
  subqual E S T ->
  forall (E1:env) X (Q0:qua) (E2:env) R,
    E = E1 ++ X ~ bind_qua Q0 ++ E2 ->
    X `notin` fv_qq Q0 -> closed_qq R ->
    wf_qua (subst_env_qb X R (E1 ++ E2)) R ->
    subqual (subst_env_qb X R (E1 ++ E2)) R Q0 ->
    subqual (subst_env_qb X R (E1 ++ E2))
            (subst_qq X R S) (subst_qq X R T).
Proof.
  intros E S T H.
  induction H as [Ew Qw Hwf HQ | Ew Qw Hwf HQ
    | Ew Qa Qb Qc bb h1 IH1 hc h2 IH2 | Ew Qa Qb Qc bb h1 IH1 hc h2 IH2
    | Ew b1 b2 Hwf Ho | Ew Xw Hwf HQ
    | R0 Ew Qw Xw hb h1 IH1
    | Ew R1 R2 Qw h1 IH1 HR2 | Ew R1 R2 Qw HR1 h2 IH1
    | Ew R1 R2 Qw h1 IH1 h2 IH2
    | Ew R1 R2 Qw h1 IH1 HR2 | Ew R1 R2 Qw HR1 h2 IH1
    | Ew R1 R2 Qw h1 IH1 h2 IH2
    | Ew Qw Rw Sw Hwf HQ HDIST HS
    | Ew Qw Rw Sw h1 IH1 h2 IH2
    | Ew Qw Hwf HQ | Ew Qw Hwf HQ | Ew Qw Hwf HQ];
    intros E1 X Q0 E2 R Heq HX Hc HRarg HsubR; subst Ew.
  - pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. eapply subqual_top.
    + exact HwM.
    + apply (wf_qua_subst_qe_M Qw E1 X Q0 E2 R HQ HRarg).
  - pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. eapply subqual_bot.
    + exact HwM.
    + apply (wf_qua_subst_qe_M Qw E1 X Q0 E2 R HQ HRarg).
  - pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    eapply subqual_eval_elim with (Q' := subst_qq X R Qa) (b := bb).
    + apply (IH1 E1 X Q0 E2 R eq_refl HX Hc HRarg HsubR).
    + rewrite (concretize_subst_qq Qa bb hc X R). exact hc.
    + apply (IH2 E1 X Q0 E2 R eq_refl HX Hc HRarg HsubR).
  - pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    eapply subqual_eval_intro with (Q' := subst_qq X R Qa) (b := bb).
    + apply (IH1 E1 X Q0 E2 R eq_refl HX Hc HRarg HsubR).
    + rewrite (concretize_subst_qq Qa bb hc X R). exact hc.
    + apply (IH2 E1 X Q0 E2 R eq_refl HX Hc HRarg HsubR).
  - pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    eapply subqual_lift_elem; [exact HwM | exact Ho].
  - pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. destruct (eq_dec Xw X) as [HeqX|Hneq].
    + subst Xw. apply subqual_refl; [exact HwM | exact HRarg].
    + eapply subqual_refl_qvar; [exact HwM |].
      inversion HQ; subst.
      eapply wf_qua_fvar. apply binds_qua_subst_env_qb.
      match goal with Hb : binds Xw (bind_qua ?RB) (E1 ++ X ~ bind_qua Q0 ++ E2) |- _ =>
        eapply binds_remove_qua_neq_name; [exact Hneq | exact Hb] end.
  - pose proof (subqual_wf _ _ _ h1) as [HwE _].
    simpl. destruct (eq_dec Xw X) as [HeqX|Hneq].
    + subst Xw.
      assert (HR0b : bind_qua R0 = bind_qua Q0).
      { eapply (binds_unique _ X (bind_qua R0) (bind_qua Q0)); [exact hb | apply binds_qua_mid | apply wf_env_uniq; exact HwE]. }
      injection HR0b as HR0. subst R0.
      pose proof (IH1 E1 X Q0 E2 R eq_refl HX Hc HRarg HsubR) as HIH.
      rewrite (subst_qq_id Q0 X R HX) in HIH.
      eapply subqual_trans; [exact HsubR | exact HIH].
    + eapply subqual_trans_qvar.
      * apply binds_qua_subst_env_qb.
        eapply binds_remove_qua_neq_name; [exact Hneq | exact hb].
      * apply (IH1 E1 X Q0 E2 R eq_refl HX Hc HRarg HsubR).
  - pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. eapply subqual_join_inl.
    + apply (IH1 E1 X Q0 E2 R eq_refl HX Hc HRarg HsubR).
    + apply (wf_qua_subst_qe_M R2 E1 X Q0 E2 R HR2 HRarg).
  - pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. eapply subqual_join_inr.
    + apply (wf_qua_subst_qe_M R1 E1 X Q0 E2 R HR1 HRarg).
    + apply (IH1 E1 X Q0 E2 R eq_refl HX Hc HRarg HsubR).
  - pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. eapply subqual_join_elim.
    + apply (IH1 E1 X Q0 E2 R eq_refl HX Hc HRarg HsubR).
    + apply (IH2 E1 X Q0 E2 R eq_refl HX Hc HRarg HsubR).
  - pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. eapply subqual_meet_eliml.
    + apply (IH1 E1 X Q0 E2 R eq_refl HX Hc HRarg HsubR).
    + apply (wf_qua_subst_qe_M R2 E1 X Q0 E2 R HR2 HRarg).
  - pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. eapply subqual_meet_elimr.
    + apply (wf_qua_subst_qe_M R1 E1 X Q0 E2 R HR1 HRarg).
    + apply (IH1 E1 X Q0 E2 R eq_refl HX Hc HRarg HsubR).
  - pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. eapply subqual_meet_intro.
    + apply (IH1 E1 X Q0 E2 R eq_refl HX Hc HRarg HsubR).
    + apply (IH2 E1 X Q0 E2 R eq_refl HX Hc HRarg HsubR).
  - pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. eapply subqual_dist.
    + exact HwM.
    + apply (wf_qua_subst_qe_M Qw E1 X Q0 E2 R HQ HRarg).
    + apply (wf_qua_subst_qe_M Rw E1 X Q0 E2 R HDIST HRarg).
    + apply (wf_qua_subst_qe_M Sw E1 X Q0 E2 R HS HRarg).
  - pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. eapply subqual_trans.
    + apply (IH1 E1 X Q0 E2 R eq_refl HX Hc HRarg HsubR).
    + apply (IH2 E1 X Q0 E2 R eq_refl HX Hc HRarg HsubR).
  - pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. eapply subqual_negate_intro.
    + exact HwM.
    + apply (wf_qua_subst_qe_M Qw E1 X Q0 E2 R HQ HRarg).
  - pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. eapply subqual_negate_elim.
    + exact HwM.
    + apply (wf_qua_subst_qe_M Qw E1 X Q0 E2 R HQ HRarg).
  - pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. eapply subqual_refl_negate.
    + exact HwM.
    + apply (wf_qua_subst_qe_M Qw E1 X Q0 E2 R HQ HRarg).
Qed.


(* ========================================================= *)
(* Opening a well-formed body with a well-formed qualifier     *)
(* ========================================================= *)

Lemma wf_qtyp_open_qqt_gen : forall (E:env) X (Q0:qua) (Tbody:qtyp) Q,
  wf_env E ->
  wf_qua E Q ->
  X `notin` dom E ->
  X `notin` fv_qqt Tbody ->
  wf_qtyp (X ~ bind_qua Q0 ++ E) (open_qqt Tbody X) ->
  wf_qtyp E (open_qqt Tbody Q).
Proof.
  intros E X Q0 Tbody Q HwE HQ HX Hfv Hbody.
  assert (Heq : subst_env_qb X Q E = E).
  { apply (subst_env_qb_id E X Q HwE HX). }
  assert (Hclosed : closed_qq Q) by (apply (wf_qua_closed_qq _ _ HQ)).
  assert (Hconv : subst_qqt X Q (open_qqt Tbody X) = open_qqt Tbody Q).
  { unfold open_qqt.
    rewrite (subst_qqt_open_qqt_rec Tbody 0 (qua_fvar X) X Q Hclosed).
    rewrite (subst_qq_atom_self X Q).
    rewrite (subst_qqt_id Tbody X Q Hfv). reflexivity. }
  assert (Hres := wf_qtyp_subst_qe_M (X ~ bind_qua Q0 ++ E)
                   (open_qqt Tbody X) Hbody
                   (@nil (atom*binding)) X Q0 E Q eq_refl).
  simpl in Hres. rewrite Heq in Hres. specialize (Hres HQ).
  rewrite Hconv in Hres. exact Hres.
Qed.


Lemma notin_union3_l_qe : forall (x:atom) A B C,
  x `notin` (A \u (B \u C)) -> x `notin` A.
Proof. intros. exact (notin_union_1 _ _ _ H). Qed.
Lemma notin_union3_m_qe : forall (x:atom) A B C,
  x `notin` (A \u (B \u C)) -> x `notin` B.
Proof. intros. exact (notin_union_1 _ _ _ (notin_union_2 _ _ _ H)). Qed.
Lemma notin_union3_r_qe : forall (x:atom) A B C,
  x `notin` (A \u (B \u C)) -> x `notin` C.
Proof. intros. exact (notin_union_2 _ _ _ (notin_union_2 _ _ _ H)). Qed.
Lemma notin_union3_r_neq_qe : forall (x y:atom) A B,
  x `notin` (A \u (B \u singleton y)) -> x <> y.
Proof.
  intros x y A B H. intro Heq. subst.
  exact (notin_singleton_1 y y (notin_union3_r_qe y A B (singleton y) H) eq_refl).
Qed.

Lemma subst_qe_open_te_atom : forall (e:exp) X R (Y:atom),
  subst_qe X R (open_te e (typ_fvar Y)) = open_te (subst_qe X R e) (typ_fvar Y).
Proof.
  intros. unfold open_te. rewrite subst_qe_open_te_rec. simpl. reflexivity.
Qed.

Lemma subst_qe_open_ee_atom : forall (e:exp) X R (Y:atom),
  subst_qe X R (open_ee e (exp_fvar Y)) = open_ee (subst_qe X R e) (exp_fvar Y).
Proof.
  intros. unfold open_ee. rewrite subst_qe_open_ee_rec. simpl. reflexivity.
Qed.

Lemma extends_tail_qe : forall (E:env) (x:atom) (b:binding),
  extends E (x ~ b ++ E).
Proof. intros E x b z c H. unfold binds. simpl. right. exact H. Qed.

Lemma sub_subqtype_subst_qe :
  (forall (E:env) (S T:typ), sub E S T ->
     forall (E1:env) (X:atom) (Q0:qua) (E2:env) (R:qua),
       E = E1 ++ X ~ bind_qua Q0 ++ E2 ->
       X `notin` fv_qq Q0 ->
       closed_qq R ->
       wf_qua (subst_env_qb X R (E1++E2)) R ->
       subqual (subst_env_qb X R (E1++E2)) R Q0 ->
       sub (subst_env_qb X R (E1++E2)) (subst_qt X R S) (subst_qt X R T)) /\
  (forall (E:env) (S T:qtyp), subqtype E S T ->
     forall (E1:env) (X:atom) (Q0:qua) (E2:env) (R:qua),
       E = E1 ++ X ~ bind_qua Q0 ++ E2 ->
       X `notin` fv_qq Q0 ->
       closed_qq R ->
       wf_qua (subst_env_qb X R (E1++E2)) R ->
       subqual (subst_env_qb X R (E1++E2)) R Q0 ->
       subqtype (subst_env_qb X R (E1++E2)) (subst_qqt X R S) (subst_qqt X R T)).
Proof.
  apply sub_tq_mut with
    (P := fun (E:env) (S T:typ) (_:sub E S T) =>
       forall (E1:env) (X:atom) (Q0:qua) (E2:env) (R:qua),
         E = E1 ++ X ~ bind_qua Q0 ++ E2 ->
         X `notin` fv_qq Q0 ->
         closed_qq R ->
         wf_qua (subst_env_qb X R (E1++E2)) R ->
         subqual (subst_env_qb X R (E1++E2)) R Q0 ->
         sub (subst_env_qb X R (E1++E2)) (subst_qt X R S) (subst_qt X R T))
    (P0 := fun (E:env) (S T:qtyp) (_:subqtype E S T) =>
       forall (E1:env) (X:atom) (Q0:qua) (E2:env) (R:qua),
         E = E1 ++ X ~ bind_qua Q0 ++ E2 ->
         X `notin` fv_qq Q0 ->
         closed_qq R ->
         wf_qua (subst_env_qb X R (E1++E2)) R ->
         subqual (subst_env_qb X R (E1++E2)) R Q0 ->
         subqtype (subst_env_qb X R (E1++E2)) (subst_qqt X R S) (subst_qqt X R T)).
  - (* sub_top *) intros E S w w0 E1 Xs Q0 E2 Rr Heq HX Hc HR HsubR; subst E.
    pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. apply sub_top.
    + exact HwM.
    + exact (wf_typ_subst_qe_M (E1 ++ Xs ~ bind_qua Q0 ++ E2) S w0 E1 Xs Q0 E2 Rr eq_refl HR).
  - (* sub_refl_int *) intros E w E1 Xs Q0 E2 Rr Heq HX Hc HR HsubR; subst E.
    pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. apply sub_refl_int. exact HwM.
  - (* sub_refl_tvar *) intros E X w w0 E1 Xs Q0 E2 Rr Heq HX Hc HR HsubR; subst E.
    pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. apply sub_refl_tvar.
    + exact HwM.
    + exact (wf_typ_subst_qe_M (E1 ++ Xs ~ bind_qua Q0 ++ E2) X w0 E1 Xs Q0 E2 Rr eq_refl HR).
  - (* sub_trans_tvar *) intros U E T X b s IH E1 Xs Q0 E2 Rr Heq HX Hc HR HsubR; subst E.
    pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl.
    eapply (sub_trans_tvar (subst_qt Xs Rr U)
              (subst_env_qb Xs Rr (E1++E2)) (subst_qt Xs Rr T) X).
    + exact (binds_sub_subst_env_qb (E1++E2) X U Xs Rr
               (binds_sub_remove_qua_mid E1 Xs Q0 E2 X U b)).
    + apply (IH E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
  - (* sub_arrow *) intros E S1 S2 T1 T2 s IH1 s0 IH2 E1 Xs Q0 E2 Rr Heq HX Hc HR HsubR; subst E.
    pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. eapply sub_arrow.
    + apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + apply (IH2 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
  - (* sub_all *) intros L E S1 S2 T1 T2 s IH1 s0 IH0 E1 Xs Q0 E2 Rr Heq HX Hc HR HsubR; subst E.
    pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. eapply sub_all with (L := L \u (dom (subst_env_qb Xs Rr (E1++E2)) \u singleton Xs)).
    + apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + intros Z HZ.
      pose proof (notin_union3_l_qe Z L (dom (subst_env_qb Xs Rr (E1++E2))) (singleton Xs) HZ) as HZL.
      pose proof (notin_union3_m_qe Z L (dom (subst_env_qb Xs Rr (E1++E2))) (singleton Xs) HZ) as HZD.
      pose proof (notin_union3_r_neq_qe Z Xs L (dom (subst_env_qb Xs Rr (E1++E2))) HZ) as HZX.
      pose proof (s0 Z HZL) as Hbody.
      assert (HwM' : wf_env (subst_env_qb Xs Rr ((Z ~ bind_sub T1 ++ E1) ++ E2))).
      { change (wf_env (Z ~ bind_sub (subst_qt Xs Rr T1) ++ subst_env_qb Xs Rr (E1++E2))).
        apply wf_env_sub.
        - exact HwM.
        - pose proof (sub_wf _ _ _ (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR)) as [_ [Hwt _]].
          exact Hwt.
        - exact HZD. }
      assert (HR' : wf_qua (subst_env_qb Xs Rr ((Z ~ bind_sub T1 ++ E1) ++ E2)) Rr).
      { change (wf_qua (Z ~ bind_sub (subst_qt Xs Rr T1) ++ subst_env_qb Xs Rr (E1++E2)) Rr).
        eapply wf_qua_extends.
        - apply extends_cons.
        - exact HR. }
      assert (HsubR' : subqual (subst_env_qb Xs Rr ((Z ~ bind_sub T1 ++ E1) ++ E2)) Rr Q0).
      { eapply subqual_extends.
        - exact HsubR.
        - apply extends_cons.
        - exact HwM'. }
      pose proof (IH0 Z HZL (Z ~ bind_sub T1 ++ E1) Xs Q0 E2 Rr eq_refl HX Hc HR' HsubR') as HI.
      rewrite app_assoc in HI.
      rewrite (subst_qqt_open_tqt_atom S2 Xs Rr Z) in HI.
      rewrite (subst_qqt_open_tqt_atom T2 Xs Rr Z) in HI.
      exact HI.
  - (* sub_qall *) intros L E S1 S2 T1 T2 s s0 IH0 E1 Xs Q0 E2 Rr Heq HX Hc HR HsubR; subst E.
    pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. eapply sub_qall with (L := L \u (dom (subst_env_qb Xs Rr (E1++E2)) \u singleton Xs)).
    + pose proof (subqual_subst_qe (E1 ++ Xs ~ bind_qua Q0 ++ E2) T1 S1 s
                    E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR) as HsubFirst.
      exact HsubFirst.
    + intros Z HZ.
      pose proof (notin_union3_l_qe Z L (dom (subst_env_qb Xs Rr (E1++E2))) (singleton Xs) HZ) as HZL.
      pose proof (notin_union3_m_qe Z L (dom (subst_env_qb Xs Rr (E1++E2))) (singleton Xs) HZ) as HZD.
      pose proof (notin_union3_r_neq_qe Z Xs L (dom (subst_env_qb Xs Rr (E1++E2))) HZ) as HZX.
      pose proof (s0 Z HZL) as Hbody.
      pose proof (subqual_subst_qe (E1 ++ Xs ~ bind_qua Q0 ++ E2) T1 S1 s
                    E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR) as HsubFirst.
      pose proof (subqual_wf _ _ _ HsubFirst) as [_ [HT1 _]].
      assert (HwM' : wf_env (subst_env_qb Xs Rr ((Z ~ bind_qua T1 ++ E1) ++ E2))).
      { change (wf_env (Z ~ bind_qua (subst_qq Xs Rr T1) ++ subst_env_qb Xs Rr (E1++E2))).
        apply wf_env_qua.
        - exact HwM.
        - exact HT1.
        - exact HZD. }
      assert (HR' : wf_qua (subst_env_qb Xs Rr ((Z ~ bind_qua T1 ++ E1) ++ E2)) Rr).
      { change (wf_qua (Z ~ bind_qua (subst_qq Xs Rr T1) ++ subst_env_qb Xs Rr (E1++E2)) Rr).
        eapply wf_qua_extends.
        - apply extends_cons.
        - exact HR. }
      assert (HsubR' : subqual (subst_env_qb Xs Rr ((Z ~ bind_qua T1 ++ E1) ++ E2)) Rr Q0).
      { eapply subqual_extends.
        - exact HsubR.
        - apply extends_cons.
        - exact HwM'. }
      pose proof (IH0 Z HZL (Z ~ bind_qua T1 ++ E1) Xs Q0 E2 Rr eq_refl HX Hc HR' HsubR') as HI.
      rewrite app_assoc in HI.
      rewrite (subst_qqt_open_qqt_atom S2 Xs Rr Z Hc HZX) in HI.
      rewrite (subst_qqt_open_qqt_atom T2 Xs Rr Z Hc HZX) in HI.
      exact HI.
  - (* sub_sum *) intros E S1 S2 T1 T2 s IH1 s0 IH2 E1 Xs Q0 E2 Rr Heq HX Hc HR HsubR; subst E.
    pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. eapply sub_sum.
    + apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + apply (IH2 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
  - (* sub_pair *) intros E S1 S2 T1 T2 s IH1 s0 IH2 E1 Xs Q0 E2 Rr Heq HX Hc HR HsubR; subst E.
    pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. eapply sub_pair.
    + apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + apply (IH2 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
  - (* sub_qtyp_qtyp *) intros E Q1 T1 Q2 T2 s s0 IH E1 Xs Q0 E2 Rr Heq HX Hc HR HsubR; subst E.
    pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
    simpl. eapply sub_qtyp_qtyp.
    + exact (subqual_subst_qe (E1 ++ Xs ~ bind_qua Q0 ++ E2) Q1 Q2 s
               E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + apply (IH E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
Qed.

Lemma sub_subst_qe : forall (E:env) (S T:typ), sub E S T ->
  forall (E1:env) (X:atom) (Q0:qua) (E2:env) (R:qua),
    E = E1 ++ X ~ bind_qua Q0 ++ E2 ->
    X `notin` fv_qq Q0 -> closed_qq R ->
    wf_qua (subst_env_qb X R (E1++E2)) R ->
    subqual (subst_env_qb X R (E1++E2)) R Q0 ->
    sub (subst_env_qb X R (E1++E2)) (subst_qt X R S) (subst_qt X R T).
Proof. intros. exact (proj1 sub_subqtype_subst_qe E S T H E1 X Q0 E2 R H0 H1 H2 H3 H4). Qed.

Lemma subqtype_subst_qe : forall (E:env) (S T:qtyp), subqtype E S T ->
  forall (E1:env) (X:atom) (Q0:qua) (E2:env) (R:qua),
    E = E1 ++ X ~ bind_qua Q0 ++ E2 ->
    X `notin` fv_qq Q0 -> closed_qq R ->
    wf_qua (subst_env_qb X R (E1++E2)) R ->
    subqual (subst_env_qb X R (E1++E2)) R Q0 ->
    subqtype (subst_env_qb X R (E1++E2)) (subst_qqt X R S) (subst_qqt X R T).
Proof. intros. exact (proj2 sub_subqtype_subst_qe E S T H E1 X Q0 E2 R H0 H1 H2 H3 H4). Qed.

Lemma typing_subst_qe_gen : forall (E:env) (P:qua) (e:exp) (T:qtyp),
  typing E P e T ->
  forall (E1:env) (X:atom) (Q0:qua) (E2:env) (R:qua),
    E = E1 ++ X ~ bind_qua Q0 ++ E2 ->
    X `notin` fv_qq Q0 ->
    closed_qq R ->
    wf_qua (subst_env_qb X R (E1++E2)) R ->
    subqual (subst_env_qb X R (E1++E2)) R Q0 ->
    typing (subst_env_qb X R (E1++E2)) (subst_qq X R P) (subst_qe X R e) (subst_qqt X R T).
Proof.
  intros E P e T H.
  induction H as [E P0 i Hwfi HP
    | E x0 Tb Hwfv Hb
    | L0 E P0 V e1 T1' Hp IHp
    | Qa T1x E e1 e2 T2 H1 IH1 H2 IH2
    | L0 E P0 V e1 T1' Hp IHp
    | Qa T1x E e1 Ta T2 H1 IH1 Hs
    | L0 E P0 Qb e1 T1' HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1x T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1x T2 P0 e1 E Qa HP H1 IH1 HT2
    | T1x T2 P0 e1 E Qa HP H1 IH1 HT1
    | L T1x T2 P0 T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1x T2 P0 e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1x T2 P0 e0 E H1 IH1
    | Qa T1x T2 P0 e0 E H1 IH1
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3];
    intros E1 Xs Q0 E2 Rr Heq HX Hc HR HsubR; subst E;
    pose proof (subqual_wf _ _ _ HsubR) as [HwM _].
  - (* int *) simpl. apply typing_int.
    + exact HwM.
    + apply (wf_qua_subst_qe_M P0 E1 Xs Q0 E2 Rr HP HR).
  - (* var *) simpl. apply typing_var.
    + exact HwM.
    + exact (binds_typ_subst_env_qb (E1++E2) x0 Tb Xs Rr
               (binds_typ_remove_qua_mid E1 Xs Q0 E2 x0 Tb Hb)).
  - (* abs *) simpl. eapply typing_abs with (L := L0 \u (dom (subst_env_qb Xs Rr (E1++E2)) \u singleton Xs)).
    intros y Hy.
    pose proof (notin_union3_l_qe y L0 (dom (subst_env_qb Xs Rr (E1++E2))) (singleton Xs) Hy) as HyL.
    pose proof (notin_union3_m_qe y L0 (dom (subst_env_qb Xs Rr (E1++E2))) (singleton Xs) Hy) as HyD.
    pose proof (notin_union3_r_neq_qe y Xs L0 (dom (subst_env_qb Xs Rr (E1++E2))) Hy) as Hyx.
    pose proof (Hp y HyL) as Hty.
    assert (HV : wf_qtyp (subst_env_qb Xs Rr (E1++E2)) (subst_qqt Xs Rr V)).
    { pose proof (typing_wf_env _ _ _ _ Hty) as Hw.
      destruct (wf_env_typ_inv _ _ _ Hw) as [_ [HV0 _]].
      exact (wf_qtyp_subst_qe_M (E1 ++ Xs ~ bind_qua Q0 ++ E2) V HV0
               E1 Xs Q0 E2 Rr eq_refl HR). }
    assert (HwM' : wf_env (subst_env_qb Xs Rr ((y ~ bind_typ V ++ E1) ++ E2))).
    { change (wf_env (y ~ bind_typ (subst_qqt Xs Rr V) ++ subst_env_qb Xs Rr (E1++E2))).
      apply wf_env_typ; [exact HwM | exact HV | exact HyD]. }
    assert (HR' : wf_qua (subst_env_qb Xs Rr ((y ~ bind_typ V ++ E1) ++ E2)) Rr).
    { change (wf_qua (y ~ bind_typ (subst_qqt Xs Rr V) ++ subst_env_qb Xs Rr (E1++E2)) Rr).
      eapply wf_qua_extends.
      - apply extends_cons.
      - exact HR. }
    assert (HsubR' : subqual (subst_env_qb Xs Rr ((y ~ bind_typ V ++ E1) ++ E2)) Rr Q0).
    { eapply subqual_extends.
      - exact HsubR.
      - apply extends_cons.
      - exact HwM'. }
    pose proof (IHp y HyL (y ~ bind_typ V ++ E1) Xs Q0 E2 Rr eq_refl HX Hc HR' HsubR') as HI.
    rewrite app_assoc in HI.
    rewrite (subst_qe_open_ee_atom e1 Xs Rr y) in HI.
    exact HI.
  - (* app *) simpl. eapply typing_app.
    + apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + apply (IH2 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
  - (* tabs *) simpl. eapply typing_tabs with (L := L0 \u (dom (subst_env_qb Xs Rr (E1++E2)) \u singleton Xs)).
    intros Z HZ.
    pose proof (notin_union3_l_qe Z L0 (dom (subst_env_qb Xs Rr (E1++E2))) (singleton Xs) HZ) as HZL.
    pose proof (notin_union3_m_qe Z L0 (dom (subst_env_qb Xs Rr (E1++E2))) (singleton Xs) HZ) as HZD.
    pose proof (Hp Z HZL) as Hty.
    assert (HV : wf_typ (subst_env_qb Xs Rr (E1++E2)) (subst_qt Xs Rr V)).
    { pose proof (typing_wf_env _ _ _ _ Hty) as Hw.
      destruct (wf_env_sub_inv _ _ _ Hw) as [_ [HV0 _]].
      exact (wf_typ_subst_qe_M (E1 ++ Xs ~ bind_qua Q0 ++ E2) V HV0
               E1 Xs Q0 E2 Rr eq_refl HR). }
    assert (HwM' : wf_env (subst_env_qb Xs Rr ((Z ~ bind_sub V ++ E1) ++ E2))).
    { change (wf_env (Z ~ bind_sub (subst_qt Xs Rr V) ++ subst_env_qb Xs Rr (E1++E2))).
      apply wf_env_sub; [exact HwM | exact HV | exact HZD]. }
    assert (HR' : wf_qua (subst_env_qb Xs Rr ((Z ~ bind_sub V ++ E1) ++ E2)) Rr).
    { change (wf_qua (Z ~ bind_sub (subst_qt Xs Rr V) ++ subst_env_qb Xs Rr (E1++E2)) Rr).
      eapply wf_qua_extends.
      - apply extends_cons.
      - exact HR. }
    assert (HsubR' : subqual (subst_env_qb Xs Rr ((Z ~ bind_sub V ++ E1) ++ E2)) Rr Q0).
    { eapply subqual_extends.
      - exact HsubR.
      - apply extends_cons.
      - exact HwM'. }
    pose proof (IHp Z HZL (Z ~ bind_sub V ++ E1) Xs Q0 E2 Rr eq_refl HX Hc HR' HsubR') as HI.
    rewrite app_assoc in HI.
    rewrite (subst_qe_open_te_atom e1 Xs Rr Z) in HI.
    rewrite (subst_qqt_open_tqt_atom T1' Xs Rr Z) in HI.
    exact HI.
  - (* tapp *) simpl. unfold open_tqt. rewrite (subst_qqt_open_tqt_rec T2 0 Ta Xs Rr).
    eapply typing_tapp.
    + apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + exact (sub_subst_qe (E1 ++ Xs ~ bind_qua Q0 ++ E2) Ta T1x Hs
               E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
  - (* qabs *) simpl. eapply typing_qabs with (L := L0 \u (dom (subst_env_qb Xs Rr (E1++E2)) \u singleton Xs)).
    + apply (wf_qua_subst_qe_M P0 E1 Xs Q0 E2 Rr HP HR).
    + intros Z HZ.
      pose proof (notin_union3_l_qe Z L0 (dom (subst_env_qb Xs Rr (E1++E2))) (singleton Xs) HZ) as HZL.
      pose proof (notin_union3_m_qe Z L0 (dom (subst_env_qb Xs Rr (E1++E2))) (singleton Xs) HZ) as HZD.
      pose proof (notin_union3_r_neq_qe Z Xs L0 (dom (subst_env_qb Xs Rr (E1++E2))) HZ) as HZX.
      pose proof (Hp Z HZL) as Hty.
      assert (HQb : wf_qua (subst_env_qb Xs Rr (E1++E2)) (subst_qq Xs Rr Qb)).
      { pose proof (typing_wf_env _ _ _ _ Hty) as Hw.
        destruct (wf_env_qua_inv _ _ _ Hw) as [_ [HQ0 _]].
        exact (wf_qua_subst_qe_M Qb E1 Xs Q0 E2 Rr HQ0 HR). }
      assert (HwM' : wf_env (subst_env_qb Xs Rr ((Z ~ bind_qua Qb ++ E1) ++ E2))).
      { change (wf_env (Z ~ bind_qua (subst_qq Xs Rr Qb) ++ subst_env_qb Xs Rr (E1++E2))).
        apply wf_env_qua; [exact HwM | exact HQb | exact HZD]. }
      assert (HR' : wf_qua (subst_env_qb Xs Rr ((Z ~ bind_qua Qb ++ E1) ++ E2)) Rr).
      { change (wf_qua (Z ~ bind_qua (subst_qq Xs Rr Qb) ++ subst_env_qb Xs Rr (E1++E2)) Rr).
        eapply wf_qua_extends.
        - apply extends_cons.
        - exact HR. }
      assert (HsubR' : subqual (subst_env_qb Xs Rr ((Z ~ bind_qua Qb ++ E1) ++ E2)) Rr Q0).
      { eapply subqual_extends.
        - exact HsubR.
        - apply extends_cons.
        - exact HwM'. }
      pose proof (IHp Z HZL (Z ~ bind_qua Qb ++ E1) Xs Q0 E2 Rr eq_refl HX Hc HR' HsubR') as HI.
      rewrite app_assoc in HI.
      rewrite (subst_qe_open_qe_atom e1 Xs Rr Z Hc HZX) in HI.
      rewrite (subst_qqt_open_qqt_atom T1' Xs Rr Z Hc HZX) in HI.
      exact HI.
  - (* qapp *) simpl. unfold open_qqt. rewrite (subst_qqt_open_qqt_rec T0 0 Qa Xs Rr Hc).
    eapply typing_qapp.
    + apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + exact (subqual_subst_qe (E1 ++ Xs ~ bind_qua Q0 ++ E2) Qa Qb Hs
               E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
  - (* sub *) simpl. eapply typing_sub.
    + apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + exact (subqtype_subst_qe (E1 ++ Xs ~ bind_qua Q0 ++ E2) S T0 Hs
               E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
  - (* subqual *) simpl. eapply typing_subqual.
    + apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + exact (subqual_subst_qe (E1 ++ Xs ~ bind_qua Q0 ++ E2) Qa R Hs
               E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
  - (* let *) simpl. eapply typing_let with (L := L \u (dom (subst_env_qb Xs Rr (E1++E2)) \u singleton Xs)).
    + apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + intros y Hy.
      pose proof (notin_union3_l_qe y L (dom (subst_env_qb Xs Rr (E1++E2))) (singleton Xs) Hy) as HyL.
      pose proof (notin_union3_m_qe y L (dom (subst_env_qb Xs Rr (E1++E2))) (singleton Xs) Hy) as HyD.
      pose proof (notin_union3_r_neq_qe y Xs L (dom (subst_env_qb Xs Rr (E1++E2))) Hy) as Hyx.
      pose proof (H2 y HyL) as Hty.
      assert (HT1x : wf_qtyp (subst_env_qb Xs Rr (E1++E2)) (subst_qqt Xs Rr T1x)).
      { pose proof (typing_wf_env _ _ _ _ Hty) as Hw.
        destruct (wf_env_typ_inv _ _ _ Hw) as [_ [HT _]].
        exact (wf_qtyp_subst_qe_M (E1 ++ Xs ~ bind_qua Q0 ++ E2) T1x HT
                 E1 Xs Q0 E2 Rr eq_refl HR). }
      assert (HwM' : wf_env (subst_env_qb Xs Rr ((y ~ bind_typ T1x ++ E1) ++ E2))).
      { change (wf_env (y ~ bind_typ (subst_qqt Xs Rr T1x) ++ subst_env_qb Xs Rr (E1++E2))).
        apply wf_env_typ; [exact HwM | exact HT1x | exact HyD]. }
      assert (HR' : wf_qua (subst_env_qb Xs Rr ((y ~ bind_typ T1x ++ E1) ++ E2)) Rr).
      { change (wf_qua (y ~ bind_typ (subst_qqt Xs Rr T1x) ++ subst_env_qb Xs Rr (E1++E2)) Rr).
        eapply wf_qua_extends.
        - apply extends_cons.
        - exact HR. }
      assert (HsubR' : subqual (subst_env_qb Xs Rr ((y ~ bind_typ T1x ++ E1) ++ E2)) Rr Q0).
      { eapply subqual_extends.
        - exact HsubR.
        - apply extends_cons.
        - exact HwM'. }
      pose proof (IH2 y HyL (y ~ bind_typ T1x ++ E1) Xs Q0 E2 Rr eq_refl HX Hc HR' HsubR') as HI.
      rewrite app_assoc in HI.
      rewrite (subst_qe_open_ee_atom e2 Xs Rr y) in HI.
      exact HI.
  - (* inl *) simpl. eapply typing_inl.
    + apply (wf_qua_subst_qe_M P0 E1 Xs Q0 E2 Rr HP HR).
    + apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + exact (wf_qtyp_subst_qe_M (E1 ++ Xs ~ bind_qua Q0 ++ E2) T2 HT2
               E1 Xs Q0 E2 Rr eq_refl HR).
  - (* inr *) simpl. eapply typing_inr.
    + apply (wf_qua_subst_qe_M P0 E1 Xs Q0 E2 Rr HP HR).
    + apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + exact (wf_qtyp_subst_qe_M (E1 ++ Xs ~ bind_qua Q0 ++ E2) T1x HT1
               E1 Xs Q0 E2 Rr eq_refl HR).
  - (* case *) simpl. eapply typing_case with (L := L \u (dom (subst_env_qb Xs Rr (E1++E2)) \u singleton Xs)).
    + apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + intros y Hy.
      pose proof (notin_union3_l_qe y L (dom (subst_env_qb Xs Rr (E1++E2))) (singleton Xs) Hy) as HyL.
      pose proof (notin_union3_m_qe y L (dom (subst_env_qb Xs Rr (E1++E2))) (singleton Xs) Hy) as HyD.
      pose proof (notin_union3_r_neq_qe y Xs L (dom (subst_env_qb Xs Rr (E1++E2))) Hy) as Hyx.
      pose proof (H2 y HyL) as Hty.
      assert (HT1x : wf_qtyp (subst_env_qb Xs Rr (E1++E2)) (subst_qqt Xs Rr T1x)).
      { pose proof (typing_wf_env _ _ _ _ Hty) as Hw.
        destruct (wf_env_typ_inv _ _ _ Hw) as [_ [HT _]].
        exact (wf_qtyp_subst_qe_M (E1 ++ Xs ~ bind_qua Q0 ++ E2) T1x HT
                 E1 Xs Q0 E2 Rr eq_refl HR). }
      assert (HwM' : wf_env (subst_env_qb Xs Rr ((y ~ bind_typ T1x ++ E1) ++ E2))).
      { change (wf_env (y ~ bind_typ (subst_qqt Xs Rr T1x) ++ subst_env_qb Xs Rr (E1++E2))).
        apply wf_env_typ; [exact HwM | exact HT1x | exact HyD]. }
      assert (HR' : wf_qua (subst_env_qb Xs Rr ((y ~ bind_typ T1x ++ E1) ++ E2)) Rr).
      { change (wf_qua (y ~ bind_typ (subst_qqt Xs Rr T1x) ++ subst_env_qb Xs Rr (E1++E2)) Rr).
        eapply wf_qua_extends.
        - apply extends_cons.
        - exact HR. }
      assert (HsubR' : subqual (subst_env_qb Xs Rr ((y ~ bind_typ T1x ++ E1) ++ E2)) Rr Q0).
      { eapply subqual_extends.
        - exact HsubR.
        - apply extends_cons.
        - exact HwM'. }
      pose proof (IH2 y HyL (y ~ bind_typ T1x ++ E1) Xs Q0 E2 Rr eq_refl HX Hc HR' HsubR') as HI.
      rewrite app_assoc in HI.
      rewrite (subst_qe_open_ee_atom e2 Xs Rr y) in HI.
      exact HI.
    + intros y Hy.
      pose proof (notin_union3_l_qe y L (dom (subst_env_qb Xs Rr (E1++E2))) (singleton Xs) Hy) as HyL.
      pose proof (notin_union3_m_qe y L (dom (subst_env_qb Xs Rr (E1++E2))) (singleton Xs) Hy) as HyD.
      pose proof (notin_union3_r_neq_qe y Xs L (dom (subst_env_qb Xs Rr (E1++E2))) Hy) as Hyx.
      pose proof (H3 y HyL) as Hty.
      assert (HT2 : wf_qtyp (subst_env_qb Xs Rr (E1++E2)) (subst_qqt Xs Rr T2)).
      { pose proof (typing_wf_env _ _ _ _ Hty) as Hw.
        destruct (wf_env_typ_inv _ _ _ Hw) as [_ [HT _]].
        exact (wf_qtyp_subst_qe_M (E1 ++ Xs ~ bind_qua Q0 ++ E2) T2 HT
                 E1 Xs Q0 E2 Rr eq_refl HR). }
      assert (HwM' : wf_env (subst_env_qb Xs Rr ((y ~ bind_typ T2 ++ E1) ++ E2))).
      { change (wf_env (y ~ bind_typ (subst_qqt Xs Rr T2) ++ subst_env_qb Xs Rr (E1++E2))).
        apply wf_env_typ; [exact HwM | exact HT2 | exact HyD]. }
      assert (HR' : wf_qua (subst_env_qb Xs Rr ((y ~ bind_typ T2 ++ E1) ++ E2)) Rr).
      { change (wf_qua (y ~ bind_typ (subst_qqt Xs Rr T2) ++ subst_env_qb Xs Rr (E1++E2)) Rr).
        eapply wf_qua_extends.
        - apply extends_cons.
        - exact HR. }
      assert (HsubR' : subqual (subst_env_qb Xs Rr ((y ~ bind_typ T2 ++ E1) ++ E2)) Rr Q0).
      { eapply subqual_extends.
        - exact HsubR.
        - apply extends_cons.
        - exact HwM'. }
      pose proof (IH3 y HyL (y ~ bind_typ T2 ++ E1) Xs Q0 E2 Rr eq_refl HX Hc HR' HsubR') as HI.
      rewrite app_assoc in HI.
      rewrite (subst_qe_open_ee_atom e3 Xs Rr y) in HI.
      exact HI.
  - (* pair *) simpl. eapply typing_pair.
    + apply (wf_qua_subst_qe_M P0 E1 Xs Q0 E2 Rr HP HR).
    + apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + apply (IH2 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
  - (* first *) simpl. eapply typing_first.
    apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
  - (* second *) simpl. eapply typing_second.
    apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
  - (* upqual *) simpl. eapply typing_upqual.
    + apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + exact (subqual_subst_qe (E1 ++ Xs ~ bind_qua Q0 ++ E2) Qa P0 Hs
               E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
  - (* check *) simpl. eapply typing_check.
    + apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + exact (subqual_subst_qe (E1 ++ Xs ~ bind_qua Q0 ++ E2) Qa P0 Hs
               E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
  - (* without *) simpl. eapply typing_without.
    + apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + exact (subqual_subst_qe (E1 ++ Xs ~ bind_qua Q0 ++ E2) R (qua_negate P0) Hs
               E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
  - (* do *) simpl. apply typing_do. exact HwM.
  - (* if0 *) simpl. eapply typing_if0.
    + apply (IH1 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + apply (IH2 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
    + apply (IH3 E1 Xs Q0 E2 Rr eq_refl HX Hc HR HsubR).
Qed.

Corollary typing_subst_qe : forall (E:env) (X:atom) (Q0:qua) (R:qua) (P:qua) (e:exp) (T:qtyp),
  typing (X ~ bind_qua Q0 ++ E) P e T ->
  X `notin` dom E ->
  X `notin` fv_qq Q0 ->
  closed_qq R ->
  wf_qua E R ->
  subqual E R Q0 ->
  typing E (subst_qq X R P) (subst_qe X R e) (subst_qqt X R T).
Proof.
  intros E X Q0 R P e T Hty HXE HX Hc HR HsubR.
  pose proof (typing_subst_qe_gen (X ~ bind_qua Q0 ++ E) P e T Hty
                (@nil (atom*binding)) X Q0 E R eq_refl HX Hc) as Hres.
  simpl in Hres.
  assert (HwE : wf_env E).
  { pose proof (typing_wf_env _ _ _ _ Hty) as Hw.
    exact (proj1 (wf_env_qua_inv X Q0 E Hw)). }
  assert (Hid : subst_env_qb X R E = E).
  { apply (subst_env_qb_id E X R HwE HXE). }
  rewrite Hid in Hres.
  exact (Hres HR HsubR).
Qed.

(* ================= ChunkTypingWf.v ================= *)

Lemma wf_qtyp_qtyp_inv : forall E Q T,
  wf_qtyp E (qtyp_qtyp Q T) -> wf_qua E Q /\ wf_typ E T.
Proof. intros E Q T H. inversion H; subst. split; assumption. Qed.

Lemma wf_typ_arrow_inv : forall E T1 T2,
  wf_typ E (typ_arrow T1 T2) -> wf_qtyp E T1 /\ wf_qtyp E T2.
Proof. intros E T1 T2 H. inversion H; subst. split; assumption. Qed.

Lemma wf_typ_sum_inv : forall E T1 T2,
  wf_typ E (typ_sum T1 T2) -> wf_qtyp E T1 /\ wf_qtyp E T2.
Proof. intros E T1 T2 H. inversion H; subst. split; assumption. Qed.

Lemma wf_typ_pair_inv : forall E T1 T2,
  wf_typ E (typ_pair T1 T2) -> wf_qtyp E T1 /\ wf_qtyp E T2.
Proof. intros E T1 T2 H. inversion H; subst. split; assumption. Qed.

Lemma wf_typ_all_inv : forall E T1 T2,
  wf_typ E (typ_all T1 T2) ->
  wf_typ E T1 /\ exists L, forall X, X `notin` L ->
    wf_qtyp (X ~ bind_sub T1 ++ E) (open_tqt T2 X).
Proof.
  intros E T1 T2 H. dependent destruction H.
  split; [assumption|].
  match goal with Hf : forall X, X `notin` ?LL -> _ |- _ => exists LL; exact Hf end.
Qed.

Lemma wf_typ_qall_inv : forall E Q T,
  wf_typ E (typ_qall Q T) ->
  wf_qua E Q /\ exists L, forall X, X `notin` L ->
    wf_qtyp (X ~ bind_qua Q ++ E) (open_qqt T X).
Proof.
  intros E Q T H. dependent destruction H.
  split; [assumption|].
  match goal with Hf : forall X, X `notin` ?LL -> _ |- _ => exists LL; exact Hf end.
Qed.

Lemma typing_wf_qtyp_from_opens :
  (forall (E:env) X (U:typ) (Tbody:qtyp) V,
      wf_env E -> wf_typ E V -> X `notin` dom E -> X `notin` fv_tqt Tbody ->
      wf_qtyp (X ~ bind_sub U ++ E) (open_tqt Tbody X) ->
      wf_qtyp E (open_tqt Tbody V)) ->
  (forall (E:env) X (Q0:qua) (Tbody:qtyp) Q,
      wf_env E -> wf_qua E Q -> X `notin` dom E -> X `notin` fv_qqt Tbody ->
      wf_qtyp (X ~ bind_qua Q0 ++ E) (open_qqt Tbody X) ->
      wf_qtyp E (open_qqt Tbody Q)) ->
  forall E Q e T, typing E Q e T -> wf_qtyp E T.
Proof.
  intros HopenT HopenQ E Q e T H.
  induction H as [E P0 i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P0 V0 b0 T1 Hp HIp
    | Qa T1 E e1 e2 T2 H1 IH1 H2 IH2
    | L0 E P0 V0 b0 T1 Hp HIp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P0 Qb b0 T1 HP Hp HIp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P0 T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P0 e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P0 e0 H1 IH1
    | Qa T1 T2 P0 e0 H1 IH1
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E bb Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3].
  - apply wf_qtyp_qtyp; [exact HP|apply wf_typ_int].
  - eapply wf_env_binds_typ; eassumption.
  - (* abs *)
    pick fresh y for L0.
    assert (HwfE : wf_env E).
    { eapply wf_env_cons_inv. apply (typing_wf_env _ _ _ _ (Hp y Fr)). }
    assert (HV : wf_qtyp E V0).
    { destruct (wf_env_typ_inv _ _ _ (typing_wf_env _ _ _ _ (Hp y Fr))) as [_ [Hv _]]. exact Hv. }
    assert (HT1 : wf_qtyp E T1).
    { pose proof (HIp y Fr) as Hw.
      exact (wf_qtyp_remove_typ_mid (@nil (atom*binding)) y V0 E T1 Hw). }
    assert (HP0 : wf_qua E P0).
    { pose proof (typing_wf_qua _ _ _ _ (Hp y Fr)) as Hw.
      exact (wf_qua_remove_typ_mid P0 (@nil (atom*binding)) y V0 E Hw). }
    apply wf_qtyp_qtyp; [exact HP0|].
    apply wf_typ_arrow; assumption.
  - (* app *)
    destruct (wf_qtyp_qtyp_inv _ _ _ IH1) as [_ Hall].
    destruct (wf_typ_arrow_inv _ _ _ Hall) as [_ HT2]. exact HT2.
  - (* tabs *)
    pick fresh y for L0.
    assert (HwfE : wf_env E).
    { eapply wf_env_cons_inv. apply (typing_wf_env _ _ _ _ (Hp y Fr)). }
    assert (HV : wf_typ E V0).
    { destruct (wf_env_sub_inv _ _ _ (typing_wf_env _ _ _ _ (Hp y Fr))) as [_ [Hv _]]. exact Hv. }
    assert (HP0 : wf_qua E P0).
    { pose proof (typing_wf_qua _ _ _ _ (Hp y Fr)) as Hw.
      exact (wf_qua_remove_sub_mid P0 (@nil (atom*binding)) y V0 E Hw). }
    apply wf_qtyp_qtyp; [exact HP0|].
    apply wf_typ_all with (L := L0). exact HV.
    intros X HX. exact (HIp X HX).
  - (* tapp *)
    destruct (wf_qtyp_qtyp_inv _ _ _ IH1) as [_ Hall].
    destruct (wf_typ_all_inv E T1 T2 Hall) as [HVall [Lall Hbody]].
    pick fresh X for (Lall \u (dom E \u fv_tqt T2)).
    apply (HopenT E X T1 T2 Ta).
    + apply (typing_wf_env _ _ _ _ H1).
    + destruct (sub_wf _ _ _ Hs) as [_ [HVa _]]. exact HVa.
    + pose proof Fr as Hx. apply notin_union_2 in Hx. apply notin_union_1 in Hx. exact Hx.
    + pose proof Fr as Hx. apply notin_union_2 in Hx. apply notin_union_2 in Hx. exact Hx.
    + apply Hbody. apply notin_union_1 in Fr; exact Fr.
  - (* qabs *)
    pick fresh y for L0.
    assert (HwfE : wf_env E).
    { eapply wf_env_cons_inv. apply (typing_wf_env _ _ _ _ (Hp y Fr)). }
    assert (HQb : wf_qua E Qb).
    { destruct (wf_env_qua_inv _ _ _ (typing_wf_env _ _ _ _ (Hp y Fr))) as [_ [Hq _]]. exact Hq. }
    apply wf_qtyp_qtyp; [exact HP|].
    apply wf_typ_qall with (L := L0). exact HQb.
    intros X HX. exact (HIp X HX).
  - (* qapp *)
    destruct (wf_qtyp_qtyp_inv _ _ _ IH1) as [_ Hall].
    destruct (wf_typ_qall_inv E Qb T0 Hall) as [HQb [Lall Hbody]].
    pick fresh X for (Lall \u (dom E \u fv_qqt T0)).
    apply (HopenQ E X Qb T0 Qa).
    + apply (typing_wf_env _ _ _ _ H1).
    + destruct (subqual_wf _ _ _ Hs) as [_ [HQa _]]. exact HQa.
    + pose proof Fr as Hx. apply notin_union_2 in Hx. apply notin_union_1 in Hx. exact Hx.
    + pose proof Fr as Hx. apply notin_union_2 in Hx. apply notin_union_2 in Hx. exact Hx.
    + apply Hbody. apply notin_union_1 in Fr; exact Fr.
  - (* sub *) destruct (subqtype_wf _ _ _ Hs) as [_ [_ HT]]. exact HT.
  - (* subqual *) exact IH1.
  - (* let *)
    pick fresh y for L.
    exact (wf_qtyp_remove_typ_mid (@nil (atom*binding)) y T1 E T2 (IH2 y Fr)).
  - (* inl *)
    apply wf_qtyp_qtyp; [exact HP|].
    apply wf_typ_sum; [exact IH1|exact HT2].
  - (* inr *)
    apply wf_qtyp_qtyp; [exact HP|].
    apply wf_typ_sum; [exact HT1|exact IH1].
  - (* case *)
    pick fresh y for L.
    exact (wf_qtyp_remove_typ_mid (@nil (atom*binding)) y T1 E T0 (IH2 y Fr)).
  - (* pair *)
    apply wf_qtyp_qtyp; [exact HP|].
    apply wf_typ_pair; assumption.
  - (* first *)
    destruct (wf_qtyp_qtyp_inv _ _ _ IHIH1) as [_ Hall].
    destruct (wf_typ_pair_inv _ _ _ Hall) as [HT1 _]. exact HT1.
  - (* second *)
    destruct (wf_qtyp_qtyp_inv _ _ _ IHIH1) as [_ Hall].
    destruct (wf_typ_pair_inv _ _ _ Hall) as [_ HT2]. exact HT2.
  - (* upqual *)
    destruct (wf_qtyp_qtyp_inv _ _ _ IH1) as [_ HT].
    apply wf_qtyp_qtyp.
    + destruct (subqual_wf _ _ _ Hs) as [_ [_ HP]]. exact HP.
    + exact HT.
  - (* check *) exact IH1.
  - (* without *) exact IH1.
  - (* do *)
    apply wf_qtyp_qtyp.
    + apply wf_qua_base.
    + apply wf_typ_int.
  - (* if0 *) exact IH2.
Qed.

(* ================= ChunkTypingWfFinal.v ================= *)

Lemma typing_wf_qtyp : forall E Q e T, typing E Q e T -> wf_qtyp E T.
Proof.
  eapply typing_wf_qtyp_from_opens.
  - exact wf_qtyp_open_tqt_gen.
  - exact wf_qtyp_open_qqt_gen.
Qed.

(* ================= ChunkValueCore.v ================= *)

Section ValueCore.
Variable Hwf_typing : forall E Q e T, typing E Q e T -> wf_qtyp E T.

Lemma sub_top_inv_typ : forall E T, sub E typ_top T -> T = typ_top.
Proof. intros E T H. inversion H; subst; reflexivity. Qed.

Lemma subqtype_narrow_sub_head : forall X (U U':typ) E S T,
  sub E U' U -> subqtype (X ~ bind_sub U ++ E) S T ->
  subqtype (X ~ bind_sub U' ++ E) S T.
Proof.
  intros X U U' E S T Hn H.
  exact (proj2 narrow_sub_bind_tq (X ~ bind_sub U ++ E) S T H U
           (fun E0 S0 T0 Hs Ht => sub_trans E0 S0 U T0 Hs Ht)
           (@nil (atom*binding)) X U' E eq_refl Hn).
Qed.

Lemma typing_tabs_core : forall E Q e T,
  typing E Q e T ->
  forall Pa V b, e = exp_tabs Pa V b ->
  exists Tbody L Pq A B L2,
    (forall X, X `notin` L -> typing (X ~ bind_sub V ++ E) Pa (open_te b X) (open_tqt Tbody X)) /\
    wf_typ E (typ_all V Tbody) /\
    subqual E Pa Pq /\
    ((T = qtyp_qtyp Pq (typ_all A B) /\ sub E A V /\
      (forall X, X `notin` L2 ->
         subqtype (X ~ bind_sub A ++ E) (open_tqt Tbody X) (open_tqt B X)))
     \/ T = qtyp_qtyp Pq typ_top).
Proof.
  intros E Q e T H.
  induction H as [E P0 i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P0 V0 b0 T1 Hp HIp
    | Qa T1 E e1 e2 T2 H1 IH1 H2 IH2
    | L0 E P0 V0 b0 T1 Hp HIp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P0 Qb b0 T1 HP Hp HIp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P0 T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P0 e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P0 e0 H1 IH1
    | Qa T1 T2 P0 e0 H1 IH1
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E bb Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3];
    intros Pa V b Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - (* core tabs *) inversion Heq; subst.
    assert (HwfE : wf_env E).
    { pick fresh y for L0. eapply wf_env_cons_inv.
      apply (typing_wf_env _ _ _ _ (Hp y Fr)). }
    assert (HV : wf_typ E V).
    { pick fresh y for L0. destruct (wf_env_sub_inv _ _ _ (typing_wf_env _ _ _ _ (Hp y Fr))) as [_ [Hv _]]. exact Hv. }
    assert (Hwfa : wf_qua E Pa).
    { pick fresh y for L0. pose proof (typing_wf_qua _ _ _ _ (Hp y Fr)) as Hw.
      exact (wf_qua_remove_sub_mid Pa (@nil (atom*binding)) y V E Hw). }
    assert (Hwfall : wf_typ E (typ_all V T1)).
    { apply wf_typ_all with (L := L0).
      - exact HV.
      - intros X HX. pose proof (Hwf_typing _ _ _ _ (Hp X HX)) as Hw. exact Hw. }
    exists T1, L0, Pa, V, T1, L0. repeat split.
    + intros X HX. apply Hp. exact HX.
    + exact Hwfall.
    + eapply subqual_refl; eassumption.
    + left. split; [reflexivity|split].
      * eapply sub_refl; [exact HwfE | exact HV].
      * intros X HX. eapply subqtype_refl.
        -- apply (typing_wf_env _ _ _ _ (Hp X HX)).
        -- apply (Hwf_typing _ _ _ _ (Hp X HX)).
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - (* sub *)
    destruct (IH1 Pa V b Heq) as [Tbody [L [Pq0 [A0 [B0 [L2 [Hbody [Hwf [Hsq Hdis]]]]]]]]].
    destruct Hdis as [[HeqT [HsA HsB]] | Htop].
    + subst S. inversion Hs; subst.
      destruct (sub_all_inv E A0 B0 T2 H5) as [-> | [L1 [A1 [B1 [-> [HnA HnB]]]]]].
      * exists Tbody, L, Q2, A0, B0, L2. repeat split; auto.
        eapply subqual_trans; eassumption.
      * exists Tbody, L, Q2, A1, B1, (L2 \u L1). repeat split; auto.
        -- eapply subqual_trans; eassumption.
        -- left. split; [reflexivity|split].
           ++ eapply sub_trans; eassumption.
           ++ intros X HX.
              pose proof (notin_union_1 _ _ _ HX) as HXL2.
              pose proof (notin_union_2 _ _ _ HX) as HXL1.
              eapply subqtype_trans.
              ** eapply subqtype_narrow_sub_head; [exact HnA | apply HsB; exact HXL2].
              ** apply HnB; exact HXL1.
    + subst S. inversion Hs; subst.
      pose proof (sub_top_inv_typ _ _ H5) as ->.
      exists Tbody, L, Q2, A0, B0, L2. repeat split; auto.
      eapply subqual_trans; eassumption.
  - (* subqual *) exact (IH1 Pa V b Heq).
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
Qed.

(* ---------------- abstraction ---------------- *)

Lemma typing_abs_core : forall E Q e T,
  typing E Q e T ->
  forall Pa V b, e = exp_abs Pa V b ->
  exists Tbody L Pq A B,
    (forall x, x `notin` L -> typing (x ~ bind_typ V ++ E) Pa (open_ee b x) Tbody) /\
    wf_typ E (typ_arrow V Tbody) /\
    subqual E Pa Pq /\
    ((T = qtyp_qtyp Pq (typ_arrow A B) /\ subqtype E A V /\ subqtype E Tbody B)
     \/ T = qtyp_qtyp Pq typ_top).
Proof.
  intros E Q e T H.
  induction H as [E P0 i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P0 V0 b0 T1 Hp HIp
    | Qa T1 E e1 e2 T2 H1 IH1 H2 IH2
    | L0 E P0 V0 b0 T1 Hp HIp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P0 Qb b0 T1 HP Hp HIp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P0 T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P0 e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P0 e0 H1 IH1
    | Qa T1 T2 P0 e0 H1 IH1
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E bb Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3];
    intros Pa V b Heq.
  - discriminate Heq.
  - discriminate Heq.
  - (* core abs *) inversion Heq; subst.
    assert (HwfE : wf_env E).
    { pick fresh y for L0. eapply wf_env_cons_inv.
      apply (typing_wf_env _ _ _ _ (Hp y Fr)). }
    assert (HV : wf_qtyp E V).
    { pick fresh y for L0. destruct (wf_env_typ_inv _ _ _ (typing_wf_env _ _ _ _ (Hp y Fr))) as [_ [Hv _]]. exact Hv. }
    pick fresh y for L0.
    assert (HTb : wf_qtyp E T1).
    { pose proof (Hwf_typing _ _ _ _ (Hp y Fr)) as Hw.
      exact (wf_qtyp_remove_typ_mid (@nil (atom*binding)) y V E T1 Hw). }
    assert (Hwfa : wf_qua E Pa).
    { pose proof (typing_wf_qua _ _ _ _ (Hp y Fr)) as Hw.
      exact (wf_qua_remove_typ_mid Pa (@nil (atom*binding)) y V E Hw). }
    exists T1, L0, Pa, V, T1. repeat split.
    + intros x Hx. apply Hp. exact Hx.
    + apply wf_typ_arrow; assumption.
    + eapply subqual_refl; eassumption.
    + left. split; [reflexivity|split].
      * eapply subqtype_refl; [exact HwfE | exact HV].
      * eapply subqtype_refl; [exact HwfE | exact HTb].
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - (* sub *)
    destruct (IH1 Pa V b Heq) as [Tbody [L [Pq0 [A0 [B0 [Hbody [Hwf [Hsq Hdis]]]]]]]].
    destruct Hdis as [[HeqT [HsA HsB]] | Htop].
    + subst S. inversion Hs; subst.
      destruct (sub_arrow_inv E A0 B0 T2 H5) as [-> | [A1 [B1 [-> [HnA HnB]]]]].
      * exists Tbody, L, Q2, A0, B0. repeat split; auto.
        eapply subqual_trans; eassumption.
      * exists Tbody, L, Q2, A1, B1. repeat split; auto.
        -- eapply subqual_trans; eassumption.
        -- left. split; [reflexivity|split].
           ++ eapply subqtype_trans; eassumption.
           ++ eapply subqtype_trans; eassumption.
    + subst S. inversion Hs; subst.
      pose proof (sub_top_inv_typ _ _ H5) as ->.
      exists Tbody, L, Q2, A0, B0. repeat split; auto.
      eapply subqual_trans; eassumption.
  - (* subqual *) exact (IH1 Pa V b Heq).
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
Qed.

Lemma typing_qabs_core : forall E Q e T,
  typing E Q e T ->
  forall Pa Qb b, e = exp_qabs Pa Qb b ->
  exists Tbody L Pq A B L2,
    (forall X, X `notin` L -> typing (X ~ bind_qua Qb ++ E) Pa (open_qe b X) (open_qqt Tbody X)) /\
    wf_typ E (typ_qall Qb Tbody) /\
    subqual E Pa Pq /\
    ((T = qtyp_qtyp Pq (typ_qall A B) /\ subqual E A Qb /\
      (forall X, X `notin` L2 ->
         subqtype (X ~ bind_qua A ++ E) (open_qqt Tbody X) (open_qqt B X)))
     \/ T = qtyp_qtyp Pq typ_top).
Proof.
  intros E Q e T H.
  induction H as [E P0 i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P0 V0 b0 T1 Hp HIp
    | Qa T1 E e1 e2 T2 H1 IH1 H2 IH2
    | L0 E P0 V0 b0 T1 Hp HIp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P0 Qb0 b0 T1 HP Hp HIp
    | Qa E e1 Qb0 T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P0 T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P0 e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P0 e0 H1 IH1
    | Qa T1 T2 P0 e0 H1 IH1
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E bb Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3];
    intros Pa Qb b Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - (* core qabs *) inversion Heq; subst.
    assert (HwfE : wf_env E).
    { pick fresh y for L0. eapply wf_env_cons_inv.
      apply (typing_wf_env _ _ _ _ (Hp y Fr)). }
    assert (HQb : wf_qua E Qb).
    { pick fresh y for L0. destruct (wf_env_qua_inv _ _ _ (typing_wf_env _ _ _ _ (Hp y Fr))) as [_ [Hq _]]. exact Hq. }
    assert (Hwfall : wf_typ E (typ_qall Qb T1)).
    { apply wf_typ_qall with (L := L0).
      - exact HQb.
      - intros X HX. pose proof (Hwf_typing _ _ _ _ (Hp X HX)) as Hw. exact Hw. }
    exists T1, L0, Pa, Qb, T1, L0. repeat split.
    + intros X HX. apply Hp. exact HX.
    + exact Hwfall.
    + eapply subqual_refl; eassumption.
    + left. split; [reflexivity|split].
      * eapply subqual_refl; assumption.
      * intros X HX. eapply subqtype_refl.
        -- apply (typing_wf_env _ _ _ _ (Hp X HX)).
        -- apply (Hwf_typing _ _ _ _ (Hp X HX)).
  - discriminate Heq.
  - (* sub *)
    destruct (IH1 Pa Qb b Heq) as [Tbody [L [Pq0 [A0 [B0 [L2 [Hbody [Hwf [Hsq Hdis]]]]]]]]].
    destruct Hdis as [[HeqT [HsA HsB]] | Htop].
    + subst S. inversion Hs; subst.
      destruct (sub_qall_inv E A0 B0 T2 H5) as [-> | [L1 [A1 [B1 [-> [HnA HnB]]]]]].
      * exists Tbody, L, Q2, A0, B0, L2. repeat split; auto.
        eapply subqual_trans; eassumption.
      * exists Tbody, L, Q2, A1, B1, (L2 \u L1). repeat split; auto.
        -- eapply subqual_trans; eassumption.
        -- left. split; [reflexivity|split].
           ++ eapply subqual_trans; eassumption.
           ++ intros X HX.
              pose proof (notin_union_1 _ _ _ HX) as HXL2.
              pose proof (notin_union_2 _ _ _ HX) as HXL1.
              eapply subqtype_trans.
              ** eapply subqtype_narrow_qua_head; [exact HnA | apply HsB; exact HXL2].
              ** apply HnB; exact HXL1.
    + subst S. inversion Hs; subst.
      pose proof (sub_top_inv_typ _ _ H5) as ->.
      exists Tbody, L, Q2, A0, B0, L2. repeat split; auto.
      eapply subqual_trans; eassumption.
  - (* subqual *) exact (IH1 Pa Qb b Heq).
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
Qed.

Lemma typing_int_core : forall E Q e T,
  typing E Q e T ->
  forall Pi i, e = exp_int Pi i ->
  exists Pq, wf_qua E Pi /\ subqual E Pi Pq /\
    ((T = qtyp_qtyp Pq typ_int) \/ T = qtyp_qtyp Pq typ_top).
Proof.
  intros E Q e T H.
  induction H as [E P0 i0 Hwf HP
    | E x T0 Hwf Hb
    | L0 E P0 V0 b0 T1 Hp HIp
    | Qa T1 E e1 e2 T2 H1 IH1 H2 IH2
    | L0 E P0 V0 b0 T1 Hp HIp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P0 Qb b0 T1 HP Hp HIp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P0 T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P0 e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P0 e0 H1 IH1
    | Qa T1 T2 P0 e0 H1 IH1
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E bb Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3];
    intros Pi i Heq.
  - (* core int *) inversion Heq; subst.
    exists Pi. repeat split; auto.
    eapply subqual_refl; eassumption.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - (* sub *)
    destruct (IH1 Pi i Heq) as [Pq0 [HPi [Hsq Hdis]]].
    destruct Hdis as [HeqT | Htop].
    + subst S. inversion Hs; subst.
      destruct (sub_int_inv _ _ H5) as [-> | ->].
      * exists Q2. repeat split; auto.
        eapply subqual_trans; eassumption.
      * exists Q2. repeat split; auto.
        eapply subqual_trans; eassumption.
    + subst S. inversion Hs; subst.
      pose proof (sub_top_inv_typ _ _ H5) as ->.
      exists Q2. repeat split; auto.
      eapply subqual_trans; eassumption.
  - (* subqual *) exact (IH1 Pi i Heq).
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
Qed.

Lemma typing_inl_core : forall E Q e T,
  typing E Q e T ->
  forall Pa b, e = exp_inl Pa b ->
  exists T1 T2 Pq A B,
    typing E Q b T1 /\ wf_qtyp E T2 /\ subqual E Pa Pq /\
    ((T = qtyp_qtyp Pq (typ_sum A B) /\ subqtype E T1 A /\ subqtype E T2 B)
     \/ T = qtyp_qtyp Pq typ_top).
Proof.
  intros E Q e T H.
  induction H as [E P0 i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P0 V0 b0 T1 Hp HIp
    | Qa T1 E e1 e2 T2 H1 IH1 H2 IH2
    | L0 E P0 V0 b0 T1 Hp HIp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P0 Qb0 b0 T1 HP Hp HIp
    | Qa E e1 Qb0 T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P0 T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P0 e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P0 e0 H1 IH1
    | Qa T1 T2 P0 e0 H1 IH1
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E bb Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3];
    intros Pa b Heq.

  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - (* sub *)
    destruct (IH1 Pa b Heq) as [T1 [T2 [Pq0 [A0 [B0 [Hbody [HT2 [Hsq Hdis]]]]]]]].
    destruct Hdis as [[HeqT [HsA HsB]] | Htop].
    + subst S. inversion Hs; subst.
      destruct (sub_sum_inv E A0 B0 T4 H5) as [-> | [A1 [B1 [-> [HnA HnB]]]]].
      * exists T1, T2, Q2, A0, B0. repeat split; auto.
        eapply subqual_trans; eassumption.
      * exists T1, T2, Q2, A1, B1. repeat split; auto.
        -- eapply subqual_trans; eassumption.
        -- left. split; [reflexivity|split].
           ++ eapply subqtype_trans; eassumption.
           ++ eapply subqtype_trans; eassumption.
    + subst S. inversion Hs; subst.
      pose proof (sub_top_inv_typ _ _ H5) as ->.
      exists T1, T2, Q2, A0, B0. repeat split; auto.
      eapply subqual_trans; eassumption.
  - (* subqual *)
    destruct (IH1 Pa b Heq) as [T1 [T2 [Pq0 [A0 [B0 [Hbody [HT2 [Hsq Hdis]]]]]]]].
    exists T1, T2, Pq0, A0, B0. repeat split; auto.
    eapply typing_subqual; [exact Hbody | exact Hs].
  - discriminate Heq.
  - (* core inl *) inversion Heq; subst.
    assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ _ H1)).
    assert (HT1 : wf_qtyp E T1) by (apply (Hwf_typing _ _ _ _ H1)).
    exists T1, T2, Pa, T1, T2. repeat split.
    + exact H1.
    + exact HT2.
    + eapply subqual_refl; eassumption.
    + left. split; [reflexivity|split].
      * eapply subqtype_refl; assumption.
      * eapply subqtype_refl; assumption.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.

Qed.

Lemma typing_inr_core : forall E Q e T,
  typing E Q e T ->
  forall Pa b, e = exp_inr Pa b ->
  exists T1 T2 Pq A B,
    typing E Q b T2 /\ wf_qtyp E T1 /\ subqual E Pa Pq /\
    ((T = qtyp_qtyp Pq (typ_sum A B) /\ subqtype E T1 A /\ subqtype E T2 B)
     \/ T = qtyp_qtyp Pq typ_top).
Proof.
  intros E Q e T H.
  induction H as [E P0 i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P0 V0 b0 T1 Hp HIp
    | Qa T1 E e1 e2 T2 H1 IH1 H2 IH2
    | L0 E P0 V0 b0 T1 Hp HIp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P0 Qb0 b0 T1 HP Hp HIp
    | Qa E e1 Qb0 T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P0 T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P0 e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P0 e0 H1 IH1
    | Qa T1 T2 P0 e0 H1 IH1
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E bb Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3];
    intros Pa b Heq.

  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - (* sub *)
    destruct (IH1 Pa b Heq) as [T1 [T2 [Pq0 [A0 [B0 [Hbody [HT1 [Hsq Hdis]]]]]]]].
    destruct Hdis as [[HeqT [HsA HsB]] | Htop].
    + subst S. inversion Hs; subst.
      destruct (sub_sum_inv E A0 B0 T4 H5) as [-> | [A1 [B1 [-> [HnA HnB]]]]].
      * exists T1, T2, Q2, A0, B0. repeat split; auto.
        eapply subqual_trans; eassumption.
      * exists T1, T2, Q2, A1, B1. repeat split; auto.
        -- eapply subqual_trans; eassumption.
        -- left. split; [reflexivity|split].
           ++ eapply subqtype_trans; eassumption.
           ++ eapply subqtype_trans; eassumption.
    + subst S. inversion Hs; subst.
      pose proof (sub_top_inv_typ _ _ H5) as ->.
      exists T1, T2, Q2, A0, B0. repeat split; auto.
      eapply subqual_trans; eassumption.
  - (* subqual *)
    destruct (IH1 Pa b Heq) as [T1 [T2 [Pq0 [A0 [B0 [Hbody [HT1 [Hsq Hdis]]]]]]]].
    exists T1, T2, Pq0, A0, B0. repeat split; auto.
    eapply typing_subqual; [exact Hbody | exact Hs].
  - discriminate Heq.
  - discriminate Heq.
  - (* core inr *) inversion Heq; subst.
    assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ _ H1)).
    assert (HT2 : wf_qtyp E T2) by (apply (Hwf_typing _ _ _ _ H1)).
    exists T1, T2, Pa, T1, T2. repeat split.
    + exact H1.
    + exact HT1.
    + eapply subqual_refl; eassumption.
    + left. split; [reflexivity|split].
      * eapply subqtype_refl; assumption.
      * eapply subqtype_refl; assumption.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.

Qed.

Lemma typing_pair_core : forall E Q e T,
  typing E Q e T ->
  forall Pa b1 b2, e = exp_pair Pa b1 b2 ->
  exists T1 T2 Pq A B,
    typing E Q b1 T1 /\ typing E Q b2 T2 /\ subqual E Pa Pq /\
    ((T = qtyp_qtyp Pq (typ_pair A B) /\ subqtype E T1 A /\ subqtype E T2 B)
     \/ T = qtyp_qtyp Pq typ_top).
Proof.
  intros E Q e T H.
  induction H as [E P0 i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P0 V0 b0 T1 Hp HIp
    | Qa T1 E e1 e2 T2 H1 IH1 H2 IH2
    | L0 E P0 V0 b0 T1 Hp HIp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P0 Qb0 b0 T1 HP Hp HIp
    | Qa E e1 Qb0 T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT2
    | T1 T2 P0 e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P0 T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P0 e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P0 e0 H1 IH1
    | Qa T1 T2 P0 e0 H1 IH1
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E R Qa T0 P0 e0 H1 IH1 Hs
    | E bb Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3];
    intros Pa b1 b2 Heq.

  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - (* sub *)
    destruct (IH1 Pa b1 b2 Heq) as [T1 [T2 [Pq0 [A0 [B0 [Hbody1 [Hbody2 [Hsq Hdis]]]]]]]].
    destruct Hdis as [[HeqT [HsA HsB]] | Htop].
    + subst S. inversion Hs; subst.
      destruct (sub_pair_inv E A0 B0 T4 H5) as [-> | [A1 [B1 [-> [HnA HnB]]]]].
      * exists T1, T2, Q2, A0, B0. repeat split; auto.
        eapply subqual_trans; eassumption.
      * exists T1, T2, Q2, A1, B1. repeat split; auto.
        -- eapply subqual_trans; eassumption.
        -- left. split; [reflexivity|split].
           ++ eapply subqtype_trans; eassumption.
           ++ eapply subqtype_trans; eassumption.
    + subst S. inversion Hs; subst.
      pose proof (sub_top_inv_typ _ _ H5) as ->.
      exists T1, T2, Q2, A0, B0. repeat split; auto.
      eapply subqual_trans; eassumption.
  - (* subqual *)
    destruct (IH1 Pa b1 b2 Heq) as [T1 [T2 [Pq0 [A0 [B0 [Hbody1 [Hbody2 [Hsq Hdis]]]]]]]].
    exists T1, T2, Pq0, A0, B0. repeat split; auto.
    + eapply typing_subqual; [exact Hbody1 | exact Hs].
    + eapply typing_subqual; [exact Hbody2 | exact Hs].
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - (* core pair *) inversion Heq; subst.
    assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ _ H1)).
    assert (HT1 : wf_qtyp E T1) by (apply (Hwf_typing _ _ _ _ H1)).
    assert (HT2 : wf_qtyp E T2) by (apply (Hwf_typing _ _ _ _ H2)).
    exists T1, T2, Pa, T1, T2. repeat split.
    + exact H1.
    + exact H2.
    + eapply subqual_refl; eassumption.
    + left. split; [reflexivity|split].
      * eapply subqtype_refl; assumption.
      * eapply subqtype_refl; assumption.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.

Qed.

End ValueCore.

(* ================= ChunkValueInst.v ================= *)

Definition typing_abs_core_wf := typing_abs_core typing_wf_qtyp.
Definition typing_tabs_core_wf := typing_tabs_core typing_wf_qtyp.
Definition typing_qabs_core_wf := typing_qabs_core typing_wf_qtyp.
Definition typing_int_core_wf := typing_int_core.
Definition typing_inl_core_wf := typing_inl_core typing_wf_qtyp.
Definition typing_inr_core_wf := typing_inr_core typing_wf_qtyp.
Definition typing_pair_core_wf := typing_pair_core typing_wf_qtyp.

(* ================= ChunkCtxWfSource.v ================= *)

Lemma typing_ctx_wf_source : forall E Q c T U,
  typing_ctx E Q c T U -> wf_qtyp E T.
Proof.
  intros E Q c T U H. induction H as [E0 Q0 T0 Hwf HQ HT
    | E0 Q0 c0 e1 T1 T2 U0 Hc IH Hty
    | E0 Q0 c0 e1 T1 T2 U0 Hc IH Hval Hty
    | L E0 Q0 c0 T1 T1' T2 U0 Hc IH Hsub Hbody
    | L E0 Q0 c0 R R' T2 U0 Hc IH Hsub Hbody
    | L E0 Q0 c0 e1 T1 T2 U0 Hc IH Hbody
    | E0 P Q0 c0 T1 T2 U0 Hc IH
    | E0 P Q0 c0 T1 T2 U0 Hc IH
    | L E0 P Q0 c0 T0 T1 T2 e2 e3 U0 HP Hc IH Hb2 Hb3
    | E0 P Q0 c0 e T1 T2 U0 HP Hc IH Hty
    | E0 P Q0 c0 v T1 T2 U0 HP Hc IH Hv Hty
    | E0 P Q0 c0 T1 T2 U0 HP Hc IH HT2
    | E0 P Q0 c0 T1 T2 U0 HP Hc IH HT1
    | E0 Q0 c0 s t T0 U0 Hc IH Hconc Hord
    | E0 Q0 c0 P T0 U0 Hc IH
    | E0 Q0 c0 R P T0 U0 HR Hc IH
    | E0 Q0 c0 S T0 U0 Hc IH Hsub
    | E0 Q0 R c0 T0 U0 Hc IH Hsub
    | E0 Q0 c0 t T0 U0 Hc IH
    | E0 R c0 e2 e3 T0 Q0 U0 HQ Hc IH H2 H3].
  - exact HT.
  - (* abs *) apply wf_qtyp_qtyp.
    + destruct (typing_ctx_wf_qua _ _ _ _ _ Hc) as [_ HQ]. exact HQ.
    + apply wf_typ_arrow.
      * apply (typing_wf_qtyp _ _ _ _ Hty).
      * exact IH.
  - (* app *) destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ Hty)) as [_ Hall].
    destruct (wf_typ_arrow_inv _ _ _ Hall) as [HT1 _]. exact HT1.
  - (* tabs *) apply wf_qtyp_qtyp.
    + destruct (typing_ctx_wf_qua _ _ _ _ _ Hc) as [_ HQ]. exact HQ.
    + apply wf_typ_all with (L := L).
      * destruct (sub_wf _ _ _ Hsub) as [_ [_ HT1]]. exact HT1.
      * intros X HX. exact (Hbody X HX).
  - (* qabs *) apply wf_qtyp_qtyp.
    + destruct (typing_ctx_wf_qua _ _ _ _ _ Hc) as [_ HQ]. exact HQ.
    + apply wf_typ_qall with (L := L).
      * destruct (subqual_wf _ _ _ Hsub) as [_ [_ HR]]. exact HR.
      * intros X HX. exact (Hbody X HX).
  - (* let *) pick fresh x for L.
    destruct (wf_env_typ_inv _ _ _ (typing_wf_env _ _ _ _ (Hbody x Fr))) as [_ [HT1 _]]. exact HT1.
  - (* inl *) destruct (wf_qtyp_qtyp_inv _ _ _ IH) as [_ Hall].
    destruct (wf_typ_sum_inv _ _ _ Hall) as [HT1 _]. exact HT1.
  - (* inr *) destruct (wf_qtyp_qtyp_inv _ _ _ IH) as [_ Hall].
    destruct (wf_typ_sum_inv _ _ _ Hall) as [_ HT2]. exact HT2.
  - (* case *) apply wf_qtyp_qtyp.
    + exact HP.
    + apply wf_typ_sum.
      * pick fresh x for L.
        destruct (wf_env_typ_inv _ _ _ (typing_wf_env _ _ _ _ (Hb2 x Fr))) as [_ [HT1 _]]. exact HT1.
      * pick fresh y for L.
        destruct (wf_env_typ_inv _ _ _ (typing_wf_env _ _ _ _ (Hb3 y Fr))) as [_ [HT2 _]]. exact HT2.
  - (* pair_1 *) destruct (wf_qtyp_qtyp_inv _ _ _ IH) as [_ Hall].
    destruct (wf_typ_pair_inv _ _ _ Hall) as [HT1 _]. exact HT1.
  - (* pair_2 *) destruct (wf_qtyp_qtyp_inv _ _ _ IH) as [_ Hall].
    destruct (wf_typ_pair_inv _ _ _ Hall) as [_ HT2]. exact HT2.
  - (* first *) apply wf_qtyp_qtyp; [exact HP|].
    apply wf_typ_pair; assumption.
  - (* second *) apply wf_qtyp_qtyp; [exact HP|].
    apply wf_typ_pair; assumption.
  - (* barrier *) exact IH.
  - (* upqual *) exact IH.
  - (* check *) destruct (wf_qtyp_qtyp_inv _ _ _ IH) as [HP HT].
    apply wf_qtyp_qtyp; [|exact HT].
    apply wf_qua_meet; [exact HP|exact HR].
  - (* sub *) destruct (subqtype_wf _ _ _ Hsub) as [_ [HS _]]. exact HS.
  - (* subqual *) exact IH.
  - (* without *) exact IH.
  - (* if0 *) apply wf_qtyp_qtyp; [exact HQ|apply wf_typ_int].
Qed.

(* ================= ChunkCore.v ================= *)

Lemma C_app_gen : forall E Q e T,
  typing E Q e T ->
  forall u1 u2, e = exp_app u1 u2 ->
  forall k U, typing_ctx E Q k T U ->
  exists R T1 T2, typing E R u1 (qtyp_qtyp R (typ_arrow T1 T2)) /\ typing E R u2 T1 /\ typing_ctx E R k T2 U.
Proof.
  intros E Q e T Hty.
  induction Hty as [E P i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E a1 a2 T2 H1 IH1 H2 IH2
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P Qb e1 T1 HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P e1 E Qa HP H1 IH1 HT2
    | T1 T2 P e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P e0 E H1 IH1
    | Qa T1 T2 P e0 E H1 IH1
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3].
  - intros u1 u2 Heq k U Hctx. discriminate Heq.
  - intros u1 u2 Heq k U Hctx. discriminate Heq.
  - intros u1 u2 Heq k U Hctx. discriminate Heq.
  - intros u1 u2 Heq k U Hctx. inversion Heq; subst. eexists; eexists; eexists; split;[exact H1|split;[exact H2|exact Hctx]].
  - intros u1 u2 Heq k U Hctx. discriminate Heq.
  - intros u1 u2 Heq k U Hctx. discriminate Heq.
  - intros u1 u2 Heq k U Hctx. discriminate Heq.
  - intros u1 u2 Heq k U Hctx. discriminate Heq.
  - intros u1 u2 Heq k U Hctx. apply (IH1 u1 u2 Heq k U (typing_ctx_sub E Qa k S T0 U Hctx Hs)).
  - intros u1 u2 Heq k U Hctx. apply (IH1 u1 u2 Heq k U (typing_ctx_subqual E R Qa k T0 U Hctx Hs)).
  - intros u1 u2 Heq k U Hctx. discriminate Heq.
  - intros u1 u2 Heq k U Hctx. discriminate Heq.
  - intros u1 u2 Heq k U Hctx. discriminate Heq.
  - intros u1 u2 Heq k U Hctx. discriminate Heq.
  - intros u1 u2 Heq k U Hctx. discriminate Heq.
  - intros u1 u2 Heq k U Hctx. discriminate Heq.
  - intros u1 u2 Heq k U Hctx. discriminate Heq.
  - intros u1 u2 Heq k U Hctx. discriminate Heq.
  - intros u1 u2 Heq k U Hctx. discriminate Heq.
  - intros u1 u2 Heq k U Hctx. discriminate Heq.
  - intros u1 u2 Heq k U Hctx. discriminate Heq.
  - intros u1 u2 Heq k U Hctx. discriminate Heq.
Qed.

Lemma C_app : forall E Q (e1:exp) (e2:exp) T k U,
  typing E Q (exp_app e1 e2) T -> typing_ctx E Q k T U ->
  exists R T1 T2, typing E R e1 (qtyp_qtyp R (typ_arrow T1 T2)) /\ typing E R e2 T1 /\ typing_ctx E R k T2 U.
Proof.
  intros E Q e1 e2 T k U Hty Hctx.
  exact (C_app_gen E Q (exp_app e1 e2) T Hty e1 e2 eq_refl k U Hctx).
Qed.

Lemma C_tapp_gen : forall E Q e T,
  typing E Q e T ->
  forall u1 Vv, e = exp_tapp u1 Vv ->
  forall k U, typing_ctx E Q k T U ->
  exists R T1 T2, typing E R u1 (qtyp_qtyp R (typ_all T1 T2)) /\ sub E Vv T1 /\ typing_ctx E R k (open_tqt T2 Vv) U.
Proof.
  intros E Q e T Hty.
  induction Hty as [E P i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E a1 a2 T2 H1 IH1 H2 IH2
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P Qb e1 T1 HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P e1 E Qa HP H1 IH1 HT2
    | T1 T2 P e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P e0 E H1 IH1
    | Qa T1 T2 P e0 E H1 IH1
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3].
  - intros u1 Vv Heq k U Hctx. discriminate Heq.
  - intros u1 Vv Heq k U Hctx. discriminate Heq.
  - intros u1 Vv Heq k U Hctx. discriminate Heq.
  - intros u1 Vv Heq k U Hctx. discriminate Heq.
  - intros u1 Vv Heq k U Hctx. discriminate Heq.
  - intros u1 Vv Heq k U Hctx. inversion Heq; subst. eexists; eexists; eexists; split;[exact H1|split;[exact Hs|exact Hctx]].
  - intros u1 Vv Heq k U Hctx. discriminate Heq.
  - intros u1 Vv Heq k U Hctx. discriminate Heq.
  - intros u1 Vv Heq k U Hctx. apply (IH1 u1 Vv Heq k U (typing_ctx_sub E Qa k S T0 U Hctx Hs)).
  - intros u1 Vv Heq k U Hctx. apply (IH1 u1 Vv Heq k U (typing_ctx_subqual E R Qa k T0 U Hctx Hs)).
  - intros u1 Vv Heq k U Hctx. discriminate Heq.
  - intros u1 Vv Heq k U Hctx. discriminate Heq.
  - intros u1 Vv Heq k U Hctx. discriminate Heq.
  - intros u1 Vv Heq k U Hctx. discriminate Heq.
  - intros u1 Vv Heq k U Hctx. discriminate Heq.
  - intros u1 Vv Heq k U Hctx. discriminate Heq.
  - intros u1 Vv Heq k U Hctx. discriminate Heq.
  - intros u1 Vv Heq k U Hctx. discriminate Heq.
  - intros u1 Vv Heq k U Hctx. discriminate Heq.
  - intros u1 Vv Heq k U Hctx. discriminate Heq.
  - intros u1 Vv Heq k U Hctx. discriminate Heq.
  - intros u1 Vv Heq k U Hctx. discriminate Heq.
Qed.

Lemma C_tapp : forall E Q (e1:exp) (V:typ) T k U,
  typing E Q (exp_tapp e1 V) T -> typing_ctx E Q k T U ->
  exists R T1 T2, typing E R e1 (qtyp_qtyp R (typ_all T1 T2)) /\ sub E V T1 /\ typing_ctx E R k (open_tqt T2 V) U.
Proof.
  intros E Q e1 V T k U Hty Hctx.
  exact (C_tapp_gen E Q (exp_tapp e1 V) T Hty e1 V eq_refl k U Hctx).
Qed.

Lemma C_qapp_gen : forall E Q e T,
  typing E Q e T ->
  forall u1 zQb, e = exp_qapp u1 zQb ->
  forall k U, typing_ctx E Q k T U ->
  exists R Q1 T1, typing E R u1 (qtyp_qtyp R (typ_qall Q1 T1)) /\ subqual E zQb Q1 /\ typing_ctx E R k (open_qqt T1 zQb) U.
Proof.
  intros E Q e T Hty.
  induction Hty as [E P i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E a1 a2 T2 H1 IH1 H2 IH2
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P Qb e1 T1 HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P e1 E Qa HP H1 IH1 HT2
    | T1 T2 P e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P e0 E H1 IH1
    | Qa T1 T2 P e0 E H1 IH1
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3].
  - intros u1 zQb Heq k U Hctx. discriminate Heq.
  - intros u1 zQb Heq k U Hctx. discriminate Heq.
  - intros u1 zQb Heq k U Hctx. discriminate Heq.
  - intros u1 zQb Heq k U Hctx. discriminate Heq.
  - intros u1 zQb Heq k U Hctx. discriminate Heq.
  - intros u1 zQb Heq k U Hctx. discriminate Heq.
  - intros u1 zQb Heq k U Hctx. discriminate Heq.
  - intros u1 zQb Heq k U Hctx. inversion Heq; subst. eexists; eexists; eexists; split;[exact H1|split;[exact Hs|exact Hctx]].
  - intros u1 zQb Heq k U Hctx. apply (IH1 u1 zQb Heq k U (typing_ctx_sub E Qa k S T0 U Hctx Hs)).
  - intros u1 zQb Heq k U Hctx. apply (IH1 u1 zQb Heq k U (typing_ctx_subqual E R Qa k T0 U Hctx Hs)).
  - intros u1 zQb Heq k U Hctx. discriminate Heq.
  - intros u1 zQb Heq k U Hctx. discriminate Heq.
  - intros u1 zQb Heq k U Hctx. discriminate Heq.
  - intros u1 zQb Heq k U Hctx. discriminate Heq.
  - intros u1 zQb Heq k U Hctx. discriminate Heq.
  - intros u1 zQb Heq k U Hctx. discriminate Heq.
  - intros u1 zQb Heq k U Hctx. discriminate Heq.
  - intros u1 zQb Heq k U Hctx. discriminate Heq.
  - intros u1 zQb Heq k U Hctx. discriminate Heq.
  - intros u1 zQb Heq k U Hctx. discriminate Heq.
  - intros u1 zQb Heq k U Hctx. discriminate Heq.
  - intros u1 zQb Heq k U Hctx. discriminate Heq.
Qed.

Lemma C_qapp : forall E Q (e1:exp) (Qb:qua) T k U,
  typing E Q (exp_qapp e1 Qb) T -> typing_ctx E Q k T U ->
  exists R Q1 T1, typing E R e1 (qtyp_qtyp R (typ_qall Q1 T1)) /\ subqual E Qb Q1 /\ typing_ctx E R k (open_qqt T1 Qb) U.
Proof.
  intros E Q e1 Qb T k U Hty Hctx.
  exact (C_qapp_gen E Q (exp_qapp e1 Qb) T Hty e1 Qb eq_refl k U Hctx).
Qed.

Lemma C_let_gen : forall E Q e T,
  typing E Q e T ->
  forall c1 c2, e = exp_let c1 c2 ->
  forall k U, typing_ctx E Q k T U ->
  exists R L T1 T2, typing E R c1 T1 /\ (forall x, x `notin` L -> typing (x ~ bind_typ T1 ++ E) R (open_ee c2 x) T2) /\ typing_ctx E R k T2 U.
Proof.
  intros E Q e T Hty.
  induction Hty as [E P i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E a1 a2 T2 H1 IH1 H2 IH2
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P Qb e1 T1 HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P e1 E Qa HP H1 IH1 HT2
    | T1 T2 P e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P e0 E H1 IH1
    | Qa T1 T2 P e0 E H1 IH1
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3].
  - intros c1 c2 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 Heq k U Hctx. apply (IH1 c1 c2 Heq k U (typing_ctx_sub E Qa k S T0 U Hctx Hs)).
  - intros c1 c2 Heq k U Hctx. apply (IH1 c1 c2 Heq k U (typing_ctx_subqual E R Qa k T0 U Hctx Hs)).
  - intros c1 c2 Heq k U Hctx. inversion Heq; subst. eexists; eexists; eexists; eexists; split;[exact H1|split;[exact H2|exact Hctx]].
  - intros c1 c2 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 Heq k U Hctx. discriminate Heq.
Qed.

Lemma C_let : forall E Q (e1:exp) (e2:exp) T k U,
  typing E Q (exp_let e1 e2) T -> typing_ctx E Q k T U ->
  exists R L T1 T2, typing E R e1 T1 /\ (forall x, x `notin` L -> typing (x ~ bind_typ T1 ++ E) R (open_ee e2 x) T2) /\ typing_ctx E R k T2 U.
Proof.
  intros E Q e1 e2 T k U Hty Hctx.
  exact (C_let_gen E Q (exp_let e1 e2) T Hty e1 e2 eq_refl k U Hctx).
Qed.

Lemma C_inl_gen : forall E Q e T,
  typing E Q e T ->
  forall c1 zP, e = exp_inl zP c1 ->
  forall k U, typing_ctx E Q k T U ->
  exists R T1 T2, wf_qua E zP /\ typing E R c1 T1 /\ wf_qtyp E T2 /\ typing_ctx E R k (qtyp_qtyp zP (typ_sum T1 T2)) U.
Proof.
  intros E Q e T Hty.
  induction Hty as [E P i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E a1 a2 T2 H1 IH1 H2 IH2
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P Qb e1 T1 HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P e1 E Qa HP H1 IH1 HT2
    | T1 T2 P e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P e0 E H1 IH1
    | Qa T1 T2 P e0 E H1 IH1
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3].
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. apply (IH1 c1 zP Heq k U (typing_ctx_sub E Qa k S T0 U Hctx Hs)).
  - intros c1 zP Heq k U Hctx. apply (IH1 c1 zP Heq k U (typing_ctx_subqual E R Qa k T0 U Hctx Hs)).
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. inversion Heq; subst. eexists; eexists; eexists; split;[exact HP|split;[exact H1|split;[exact HT2|exact Hctx]]].
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
Qed.

Lemma C_inl : forall E Q (e1:exp) (P:qua) T k U,
  typing E Q (exp_inl P e1) T -> typing_ctx E Q k T U ->
  exists R T1 T2, wf_qua E P /\ typing E R e1 T1 /\ wf_qtyp E T2 /\ typing_ctx E R k (qtyp_qtyp P (typ_sum T1 T2)) U.
Proof.
  intros E Q e1 P T k U Hty Hctx.
  exact (C_inl_gen E Q (exp_inl P e1) T Hty e1 P eq_refl k U Hctx).
Qed.

Lemma C_inr_gen : forall E Q e T,
  typing E Q e T ->
  forall c1 zP, e = exp_inr zP c1 ->
  forall k U, typing_ctx E Q k T U ->
  exists R T1 T2, wf_qua E zP /\ typing E R c1 T2 /\ wf_qtyp E T1 /\ typing_ctx E R k (qtyp_qtyp zP (typ_sum T1 T2)) U.
Proof.
  intros E Q e T Hty.
  induction Hty as [E P i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E a1 a2 T2 H1 IH1 H2 IH2
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P Qb e1 T1 HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P e1 E Qa HP H1 IH1 HT2
    | T1 T2 P e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P e0 E H1 IH1
    | Qa T1 T2 P e0 E H1 IH1
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3].
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. apply (IH1 c1 zP Heq k U (typing_ctx_sub E Qa k S T0 U Hctx Hs)).
  - intros c1 zP Heq k U Hctx. apply (IH1 c1 zP Heq k U (typing_ctx_subqual E R Qa k T0 U Hctx Hs)).
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. inversion Heq; subst. eexists; eexists; eexists; split;[exact HP|split;[exact H1|split;[exact HT1|exact Hctx]]].
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
Qed.

Lemma C_inr : forall E Q (e1:exp) (P:qua) T k U,
  typing E Q (exp_inr P e1) T -> typing_ctx E Q k T U ->
  exists R T1 T2, wf_qua E P /\ typing E R e1 T2 /\ wf_qtyp E T1 /\ typing_ctx E R k (qtyp_qtyp P (typ_sum T1 T2)) U.
Proof.
  intros E Q e1 P T k U Hty Hctx.
  exact (C_inr_gen E Q (exp_inr P e1) T Hty e1 P eq_refl k U Hctx).
Qed.

Lemma C_case_gen : forall E Q e T,
  typing E Q e T ->
  forall c1 c2 c3, e = exp_case c1 c2 c3 ->
  forall k U, typing_ctx E Q k T U ->
  exists R L P T1 T2 T0, typing E R c1 (qtyp_qtyp P (typ_sum T1 T2)) /\ (forall x, x `notin` L -> typing (x ~ bind_typ T1 ++ E) R (open_ee c2 x) T0) /\ (forall x, x `notin` L -> typing (x ~ bind_typ T2 ++ E) R (open_ee c3 x) T0) /\ typing_ctx E R k T0 U.
Proof.
  intros E Q e T Hty.
  induction Hty as [E P i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E a1 a2 T2 H1 IH1 H2 IH2
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P Qb e1 T1 HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P e1 E Qa HP H1 IH1 HT2
    | T1 T2 P e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P e0 E H1 IH1
    | Qa T1 T2 P e0 E H1 IH1
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3].
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. apply (IH1 c1 c2 c3 Heq k U (typing_ctx_sub E Qa k S T0 U Hctx Hs)).
  - intros c1 c2 c3 Heq k U Hctx. apply (IH1 c1 c2 c3 Heq k U (typing_ctx_subqual E R Qa k T0 U Hctx Hs)).
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. inversion Heq; subst. eexists; eexists; eexists; eexists; eexists; eexists; split;[exact H1|split;[exact H2|split;[exact H3|exact Hctx]]].
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
Qed.

Lemma C_case : forall E Q (e1:exp) (e2:exp) (e3:exp) T k U,
  typing E Q (exp_case e1 e2 e3) T -> typing_ctx E Q k T U ->
  exists R L P T1 T2 T0, typing E R e1 (qtyp_qtyp P (typ_sum T1 T2)) /\ (forall x, x `notin` L -> typing (x ~ bind_typ T1 ++ E) R (open_ee e2 x) T0) /\ (forall x, x `notin` L -> typing (x ~ bind_typ T2 ++ E) R (open_ee e3 x) T0) /\ typing_ctx E R k T0 U.
Proof.
  intros E Q e1 e2 e3 T k U Hty Hctx.
  exact (C_case_gen E Q (exp_case e1 e2 e3) T Hty e1 e2 e3 eq_refl k U Hctx).
Qed.

Lemma C_pair_gen : forall E Q e T,
  typing E Q e T ->
  forall c1 c2 zP, e = exp_pair zP c1 c2 ->
  forall k U, typing_ctx E Q k T U ->
  exists R T1 T2, wf_qua E zP /\ typing E R c1 T1 /\ typing E R c2 T2 /\ typing_ctx E R k (qtyp_qtyp zP (typ_pair T1 T2)) U.
Proof.
  intros E Q e T Hty.
  induction Hty as [E P i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E a1 a2 T2 H1 IH1 H2 IH2
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P Qb e1 T1 HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P e1 E Qa HP H1 IH1 HT2
    | T1 T2 P e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P e0 E H1 IH1
    | Qa T1 T2 P e0 E H1 IH1
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3].
  - intros c1 c2 zP Heq k U Hctx. discriminate Heq.
  - intros c1 c2 zP Heq k U Hctx. discriminate Heq.
  - intros c1 c2 zP Heq k U Hctx. discriminate Heq.
  - intros c1 c2 zP Heq k U Hctx. discriminate Heq.
  - intros c1 c2 zP Heq k U Hctx. discriminate Heq.
  - intros c1 c2 zP Heq k U Hctx. discriminate Heq.
  - intros c1 c2 zP Heq k U Hctx. discriminate Heq.
  - intros c1 c2 zP Heq k U Hctx. discriminate Heq.
  - intros c1 c2 zP Heq k U Hctx. apply (IH1 c1 c2 zP Heq k U (typing_ctx_sub E Qa k S T0 U Hctx Hs)).
  - intros c1 c2 zP Heq k U Hctx. apply (IH1 c1 c2 zP Heq k U (typing_ctx_subqual E R Qa k T0 U Hctx Hs)).
  - intros c1 c2 zP Heq k U Hctx. discriminate Heq.
  - intros c1 c2 zP Heq k U Hctx. discriminate Heq.
  - intros c1 c2 zP Heq k U Hctx. discriminate Heq.
  - intros c1 c2 zP Heq k U Hctx. discriminate Heq.
  - intros c1 c2 zP Heq k U Hctx. inversion Heq; subst. eexists; eexists; eexists; split;[exact HP|split;[exact H1|split;[exact H2|exact Hctx]]].
  - intros c1 c2 zP Heq k U Hctx. discriminate Heq.
  - intros c1 c2 zP Heq k U Hctx. discriminate Heq.
  - intros c1 c2 zP Heq k U Hctx. discriminate Heq.
  - intros c1 c2 zP Heq k U Hctx. discriminate Heq.
  - intros c1 c2 zP Heq k U Hctx. discriminate Heq.
  - intros c1 c2 zP Heq k U Hctx. discriminate Heq.
  - intros c1 c2 zP Heq k U Hctx. discriminate Heq.
Qed.

Lemma C_pair : forall E Q (e1:exp) (e2:exp) (P:qua) T k U,
  typing E Q (exp_pair P e1 e2) T -> typing_ctx E Q k T U ->
  exists R T1 T2, wf_qua E P /\ typing E R e1 T1 /\ typing E R e2 T2 /\ typing_ctx E R k (qtyp_qtyp P (typ_pair T1 T2)) U.
Proof.
  intros E Q e1 e2 P T k U Hty Hctx.
  exact (C_pair_gen E Q (exp_pair P e1 e2) T Hty e1 e2 P eq_refl k U Hctx).
Qed.

Lemma C_first_gen : forall E Q e T,
  typing E Q e T ->
  forall c1, e = exp_first c1 ->
  forall k U, typing_ctx E Q k T U ->
  exists R P T1 T2, typing E R c1 (qtyp_qtyp P (typ_pair T1 T2)) /\ typing_ctx E R k T1 U.
Proof.
  intros E Q e T Hty.
  induction Hty as [E P i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E a1 a2 T2 H1 IH1 H2 IH2
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P Qb e1 T1 HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P e1 E Qa HP H1 IH1 HT2
    | T1 T2 P e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P e0 E H1 IH1
    | Qa T1 T2 P e0 E H1 IH1
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3].
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. apply (IH1 c1 Heq k U (typing_ctx_sub E Qa k S T0 U Hctx Hs)).
  - intros c1 Heq k U Hctx. apply (IH1 c1 Heq k U (typing_ctx_subqual E R Qa k T0 U Hctx Hs)).
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. inversion Heq; subst. match goal with Ht : typing ?E ?Q ?c1 (qtyp_qtyp ?P (typ_pair ?T1 ?T2)), Hk : typing_ctx ?E ?Q ?k ?T1 ?U |- _ => exists Q, P, T1, T2; split;[exact Ht|exact Hk] end.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
Qed.

Lemma C_first : forall E Q (e1:exp) T k U,
  typing E Q (exp_first e1) T -> typing_ctx E Q k T U ->
  exists R P T1 T2, typing E R e1 (qtyp_qtyp P (typ_pair T1 T2)) /\ typing_ctx E R k T1 U.
Proof.
  intros E Q e1 T k U Hty Hctx.
  exact (C_first_gen E Q (exp_first e1) T Hty e1 eq_refl k U Hctx).
Qed.

Lemma C_second_gen : forall E Q e T,
  typing E Q e T ->
  forall c1, e = exp_second c1 ->
  forall k U, typing_ctx E Q k T U ->
  exists R P T1 T2, typing E R c1 (qtyp_qtyp P (typ_pair T1 T2)) /\ typing_ctx E R k T2 U.
Proof.
  intros E Q e T Hty.
  induction Hty as [E P i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E a1 a2 T2 H1 IH1 H2 IH2
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P Qb e1 T1 HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P e1 E Qa HP H1 IH1 HT2
    | T1 T2 P e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P e0 E H1 IH1
    | Qa T1 T2 P e0 E H1 IH1
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3].
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. apply (IH1 c1 Heq k U (typing_ctx_sub E Qa k S T0 U Hctx Hs)).
  - intros c1 Heq k U Hctx. apply (IH1 c1 Heq k U (typing_ctx_subqual E R Qa k T0 U Hctx Hs)).
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. inversion Heq; subst. match goal with Ht : typing ?E ?Q ?c1 (qtyp_qtyp ?P (typ_pair ?T1 ?T2)), Hk : typing_ctx ?E ?Q ?k ?T2 ?U |- _ => exists Q, P, T1, T2; split;[exact Ht|exact Hk] end.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
  - intros c1 Heq k U Hctx. discriminate Heq.
Qed.

Lemma C_second : forall E Q (e1:exp) T k U,
  typing E Q (exp_second e1) T -> typing_ctx E Q k T U ->
  exists R P T1 T2, typing E R e1 (qtyp_qtyp P (typ_pair T1 T2)) /\ typing_ctx E R k T2 U.
Proof.
  intros E Q e1 T k U Hty Hctx.
  exact (C_second_gen E Q (exp_second e1) T Hty e1 eq_refl k U Hctx).
Qed.

Lemma C_upqual_gen : forall E Q e T,
  typing E Q e T ->
  forall c1 zP, e = exp_upqual zP c1 ->
  forall k U, typing_ctx E Q k T U ->
  exists R Q' T', typing E R c1 (qtyp_qtyp Q' T') /\ subqual E Q' zP /\ typing_ctx E R k (qtyp_qtyp zP T') U.
Proof.
  intros E Q e T Hty.
  induction Hty as [E P i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E a1 a2 T2 H1 IH1 H2 IH2
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P Qb e1 T1 HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P e1 E Qa HP H1 IH1 HT2
    | T1 T2 P e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P e0 E H1 IH1
    | Qa T1 T2 P e0 E H1 IH1
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3].
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. apply (IH1 c1 zP Heq k U (typing_ctx_sub E Qa k S T0 U Hctx Hs)).
  - intros c1 zP Heq k U Hctx. apply (IH1 c1 zP Heq k U (typing_ctx_subqual E R Qa k T0 U Hctx Hs)).
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. inversion Heq; subst. eexists; eexists; eexists; split;[exact H1|split;[exact Hs|exact Hctx]].
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
Qed.

Lemma C_upqual : forall E Q (e1:exp) (P:qua) T k U,
  typing E Q (exp_upqual P e1) T -> typing_ctx E Q k T U ->
  exists R Q' T', typing E R e1 (qtyp_qtyp Q' T') /\ subqual E Q' P /\ typing_ctx E R k (qtyp_qtyp P T') U.
Proof.
  intros E Q e1 P T k U Hty Hctx.
  exact (C_upqual_gen E Q (exp_upqual P e1) T Hty e1 P eq_refl k U Hctx).
Qed.

Lemma C_check_gen : forall E Q e T,
  typing E Q e T ->
  forall c1 zP, e = exp_check zP c1 ->
  forall k U, typing_ctx E Q k T U ->
  exists R Q' T', typing E R c1 (qtyp_qtyp Q' T') /\ subqual E Q' zP /\ typing_ctx E R k (qtyp_qtyp Q' T') U.
Proof.
  intros E Q e T Hty.
  induction Hty as [E P i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E a1 a2 T2 H1 IH1 H2 IH2
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P Qb e1 T1 HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P e1 E Qa HP H1 IH1 HT2
    | T1 T2 P e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P e0 E H1 IH1
    | Qa T1 T2 P e0 E H1 IH1
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3].
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. apply (IH1 c1 zP Heq k U (typing_ctx_sub E Qa k S T0 U Hctx Hs)).
  - intros c1 zP Heq k U Hctx. apply (IH1 c1 zP Heq k U (typing_ctx_subqual E R Qa k T0 U Hctx Hs)).
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. inversion Heq; subst. eexists; eexists; eexists; split;[exact H1|split;[exact Hs|exact Hctx]].
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
Qed.

Lemma C_check : forall E Q (e1:exp) (P:qua) T k U,
  typing E Q (exp_check P e1) T -> typing_ctx E Q k T U ->
  exists R Q' T', typing E R e1 (qtyp_qtyp Q' T') /\ subqual E Q' P /\ typing_ctx E R k (qtyp_qtyp Q' T') U.
Proof.
  intros E Q e1 P T k U Hty Hctx.
  exact (C_check_gen E Q (exp_check P e1) T Hty e1 P eq_refl k U Hctx).
Qed.

Lemma C_without_gen : forall E Q e T,
  typing E Q e T ->
  forall c1 zP, e = exp_without zP c1 ->
  forall k U, typing_ctx E Q k T U ->
  exists R Q' T', typing E R c1 (qtyp_qtyp Q' T') /\ subqual E R (qua_negate zP) /\ typing_ctx E R k (qtyp_qtyp Q' T') U.
Proof.
  intros E Q e T Hty.
  induction Hty as [E P i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E a1 a2 T2 H1 IH1 H2 IH2
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P Qb e1 T1 HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P e1 E Qa HP H1 IH1 HT2
    | T1 T2 P e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P e0 E H1 IH1
    | Qa T1 T2 P e0 E H1 IH1
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3].
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. apply (IH1 c1 zP Heq k U (typing_ctx_sub E Qa k S T0 U Hctx Hs)).
  - intros c1 zP Heq k U Hctx. apply (IH1 c1 zP Heq k U (typing_ctx_subqual E R Qa k T0 U Hctx Hs)).
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. inversion Heq; subst. eexists; eexists; eexists; split;[exact H1|split;[exact Hs|exact Hctx]].
  - intros c1 zP Heq k U Hctx. discriminate Heq.
  - intros c1 zP Heq k U Hctx. discriminate Heq.
Qed.

Lemma C_without : forall E Q (e1:exp) (P:qua) T k U,
  typing E Q (exp_without P e1) T -> typing_ctx E Q k T U ->
  exists R Q' T', typing E R e1 (qtyp_qtyp Q' T') /\ subqual E R (qua_negate P) /\ typing_ctx E R k (qtyp_qtyp Q' T') U.
Proof.
  intros E Q e1 P T k U Hty Hctx.
  exact (C_without_gen E Q (exp_without P e1) T Hty e1 P eq_refl k U Hctx).
Qed.

Lemma C_if0_gen : forall E Q e T,
  typing E Q e T ->
  forall c1 c2 c3, e = exp_if0 c1 c2 c3 ->
  forall k U, typing_ctx E Q k T U ->
  exists R Q' T0, typing E R c1 (qtyp_qtyp Q' typ_int) /\ typing E R c2 T0 /\ typing E R c3 T0 /\ typing_ctx E R k T0 U.
Proof.
  intros E Q e T Hty.
  induction Hty as [E P i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E a1 a2 T2 H1 IH1 H2 IH2
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P Qb e1 T1 HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P e1 E Qa HP H1 IH1 HT2
    | T1 T2 P e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P e0 E H1 IH1
    | Qa T1 T2 P e0 E H1 IH1
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3].
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. apply (IH1 c1 c2 c3 Heq k U (typing_ctx_sub E Qa k S T0 U Hctx Hs)).
  - intros c1 c2 c3 Heq k U Hctx. apply (IH1 c1 c2 c3 Heq k U (typing_ctx_subqual E R Qa k T0 U Hctx Hs)).
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. discriminate Heq.
  - intros c1 c2 c3 Heq k U Hctx. inversion Heq; subst. eexists; eexists; eexists; split;[exact H1|split;[exact H2|split;[exact H3|exact Hctx]]].
Qed.

Lemma C_if0 : forall E Q (e1:exp) (e2:exp) (e3:exp) T k U,
  typing E Q (exp_if0 e1 e2 e3) T -> typing_ctx E Q k T U ->
  exists R Q' T0, typing E R e1 (qtyp_qtyp Q' typ_int) /\ typing E R e2 T0 /\ typing E R e3 T0 /\ typing_ctx E R k T0 U.
Proof.
  intros E Q e1 e2 e3 T k U Hty Hctx.
  exact (C_if0_gen E Q (exp_if0 e1 e2 e3) T Hty e1 e2 e3 eq_refl k U Hctx).
Qed.

Lemma C_do_gen : forall E Q e T,
  typing E Q e T ->
  forall zb, e = exp_do zb ->
  forall k U, typing_ctx E Q k T U ->
  exists R, typing_ctx E R k (qtyp_qtyp (qua_base bot) typ_int) U.
Proof.
  intros E Q e T Hty.
  induction Hty as [E P i Hwf HP
    | E x T0 Hwf Hb
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E a1 a2 T2 H1 IH1 H2 IH2
    | L0 E P V e1 T1 Hp IHp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E P Qb e1 T1 HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 P e1 E Qa HP H1 IH1 HT2
    | T1 T2 P e1 E Qa HP H1 IH1 HT1
    | L T1 T2 P T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 P e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 P e0 E H1 IH1
    | Qa T1 T2 P e0 E H1 IH1
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E R Qa T0 P e0 H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3].
  - intros zb Heq k U Hctx. discriminate Heq.
  - intros zb Heq k U Hctx. discriminate Heq.
  - intros zb Heq k U Hctx. discriminate Heq.
  - intros zb Heq k U Hctx. discriminate Heq.
  - intros zb Heq k U Hctx. discriminate Heq.
  - intros zb Heq k U Hctx. discriminate Heq.
  - intros zb Heq k U Hctx. discriminate Heq.
  - intros zb Heq k U Hctx. discriminate Heq.
  - intros zb Heq k U Hctx. apply (IH1 zb Heq k U (typing_ctx_sub E Qa k S T0 U Hctx Hs)).
  - intros zb Heq k U Hctx. apply (IH1 zb Heq k U (typing_ctx_subqual E R Qa k T0 U Hctx Hs)).
  - intros zb Heq k U Hctx. discriminate Heq.
  - intros zb Heq k U Hctx. discriminate Heq.
  - intros zb Heq k U Hctx. discriminate Heq.
  - intros zb Heq k U Hctx. discriminate Heq.
  - intros zb Heq k U Hctx. discriminate Heq.
  - intros zb Heq k U Hctx. discriminate Heq.
  - intros zb Heq k U Hctx. discriminate Heq.
  - intros zb Heq k U Hctx. discriminate Heq.
  - intros zb Heq k U Hctx. discriminate Heq.
  - intros zb Heq k U Hctx. discriminate Heq.
  - intros zb Heq k U Hctx. inversion Heq; subst. eexists; exact Hctx.
  - intros zb Heq k U Hctx. discriminate Heq.
Qed.

Lemma C_do : forall E Q (b:B) T k U,
  typing E Q (exp_do b) T -> typing_ctx E Q k T U ->
  exists R, typing_ctx E R k (qtyp_qtyp (qua_base bot) typ_int) U.
Proof.
  intros E Q b T k U Hty Hctx.
  exact (C_do_gen E Q (exp_do b) T Hty b eq_refl k U Hctx).
Qed.

(* ================= ChunkStateInv.v ================= *)

Lemma state_abs : forall E Q e T e2 k U,
  typing E Q e T ->
  typing_ctx E Q (frame_abs e2 :: k) T U ->
  exists Q' T1 T2, typing E Q' e (qtyp_qtyp Q' (typ_arrow T1 T2)) /\
    typing E Q' e2 T1 /\ typing_ctx E Q' k T2 U.
Proof.
  intros E Q e T e2 k U He Hc.
  remember (frame_abs e2 :: k) as c eqn:Hce.
  revert e2 k Hce He.
  induction Hc; intros ee2 kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - (* abs *)
    match goal with
    | He' : typing ?E ?Q ?e (qtyp_qtyp ?Q (typ_arrow ?T1 ?T2)) |- _ =>
        exists Q, T1, T2; split; [exact He' | split; [eassumption | eassumption]]
    end.
  - (* sub *)
    apply (IHHc ee2 kk Hcek). eapply typing_sub; [exact Hek | exact H].
  - (* subqual *)
    apply (IHHc ee2 kk Hcek). eapply typing_subqual; [exact Hek | exact H].
Qed.

Ltac state_direct := repeat eexists; repeat split; eauto.

Lemma state_app : forall E Q e T f k U,
  typing E Q e T ->
  typing_ctx E Q (frame_app f :: k) T U ->
  exists Q' T1 T2, typing E Q' e T1 /\ value f /\
    typing E Q' f (qtyp_qtyp Q' (typ_arrow T1 T2)) /\ typing_ctx E Q' k T2 U.
Proof.
  intros E Q e T f k U He Hc.
  remember (frame_app f :: k) as c eqn:Hce.
  revert f k Hce He.
  induction Hc; intros ff kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - state_direct.
  - apply (IHHc ff kk Hcek). eapply typing_sub; [exact Hek | exact H].
  - apply (IHHc ff kk Hcek). eapply typing_subqual; [exact Hek | exact H].
Qed.

Lemma state_tabs : forall E Q e T T1' k U,
  typing E Q e T ->
  typing_ctx E Q (frame_tabs T1' :: k) T U ->
  exists Q' L T1 T2, typing E Q' e (qtyp_qtyp Q' (typ_all T1 T2)) /\
    sub E T1' T1 /\
    (forall X, X `notin` L -> wf_qtyp (X ~ bind_sub T1 ++ E) (open_tqt T2 X)) /\
    typing_ctx E Q' k (open_tqt T2 T1') U.
Proof.
  intros E Q e T T1' k U He Hc.
  remember (frame_tabs T1' :: k) as c eqn:Hce.
  revert T1' k Hce He.
  induction Hc; intros T1'' kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - state_direct.
  - apply (IHHc T1'' kk Hcek). eapply typing_sub; [exact Hek | exact H].
  - apply (IHHc T1'' kk Hcek). eapply typing_subqual; [exact Hek | exact H].
Qed.

Lemma state_qabs : forall E Q e T R' k U,
  typing E Q e T ->
  typing_ctx E Q (frame_qabs R' :: k) T U ->
  exists Q' L R T2, typing E Q' e (qtyp_qtyp Q' (typ_qall R T2)) /\
    subqual E R' R /\
    (forall X, X `notin` L -> wf_qtyp (X ~ bind_qua R ++ E) (open_qqt T2 X)) /\
    typing_ctx E Q' k (open_qqt T2 R') U.
Proof.
  intros E Q e T R' k U He Hc.
  remember (frame_qabs R' :: k) as c eqn:Hce.
  revert R' k Hce He.
  induction Hc; intros R'' kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - state_direct.
  - apply (IHHc R'' kk Hcek). eapply typing_sub; [exact Hek | exact H].
  - apply (IHHc R'' kk Hcek). eapply typing_subqual; [exact Hek | exact H].
Qed.

Lemma state_let : forall E Q e T e2 k U,
  typing E Q e T ->
  typing_ctx E Q (frame_let e2 :: k) T U ->
  exists Q' L T1 T2, typing E Q' e T1 /\
    (forall x, x `notin` L -> typing (x ~ bind_typ T1 ++ E) Q' (open_ee e2 x) T2) /\
    typing_ctx E Q' k T2 U.
Proof.
  intros E Q e T e2 k U He Hc.
  remember (frame_let e2 :: k) as c eqn:Hce.
  revert e2 k Hce He.
  induction Hc; intros ee2 kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - state_direct.
  - apply (IHHc ee2 kk Hcek). eapply typing_sub; [exact Hek | exact H].
  - apply (IHHc ee2 kk Hcek). eapply typing_subqual; [exact Hek | exact H].
Qed.

Lemma state_inl : forall E Q e T P k U,
  typing E Q e T ->
  typing_ctx E Q (frame_inl P :: k) T U ->
  exists Q' T1 T2, typing E Q' e T1 /\ typing_ctx E Q' k (qtyp_qtyp P (typ_sum T1 T2)) U.
Proof.
  intros E Q e T P k U He Hc.
  remember (frame_inl P :: k) as c eqn:Hce.
  revert P k Hce He.
  induction Hc; intros PP kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - state_direct.
  - apply (IHHc PP kk Hcek). eapply typing_sub; [exact Hek | exact H].
  - apply (IHHc PP kk Hcek). eapply typing_subqual; [exact Hek | exact H].
Qed.

Lemma state_inr : forall E Q e T P k U,
  typing E Q e T ->
  typing_ctx E Q (frame_inr P :: k) T U ->
  exists Q' T1 T2, typing E Q' e T2 /\ typing_ctx E Q' k (qtyp_qtyp P (typ_sum T1 T2)) U.
Proof.
  intros E Q e T P k U He Hc.
  remember (frame_inr P :: k) as c eqn:Hce.
  revert P k Hce He.
  induction Hc; intros PP kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - state_direct.
  - apply (IHHc PP kk Hcek). eapply typing_sub; [exact Hek | exact H].
  - apply (IHHc PP kk Hcek). eapply typing_subqual; [exact Hek | exact H].
Qed.

Lemma state_case : forall E Q e T e2 e3 k U,
  typing E Q e T ->
  typing_ctx E Q (frame_case e2 e3 :: k) T U ->
  exists Q' L P T1 T2 T0, wf_qua E P /\
    typing E Q' e (qtyp_qtyp P (typ_sum T1 T2)) /\
    (forall x, x `notin` L -> typing (x ~ bind_typ T1 ++ E) Q' (open_ee e2 x) T0) /\
    (forall x, x `notin` L -> typing (x ~ bind_typ T2 ++ E) Q' (open_ee e3 x) T0) /\
    typing_ctx E Q' k T0 U.
Proof.
  intros E Q e T e2 e3 k U He Hc.
  remember (frame_case e2 e3 :: k) as c eqn:Hce.
  revert e2 e3 k Hce He.
  induction Hc; intros ee2 ee3 kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - exists Q, L, P, T1, T2, T; repeat split; eauto.
  - apply (IHHc ee2 ee3 kk Hcek). eapply typing_sub; [exact Hek | exact H].
  - apply (IHHc ee2 ee3 kk Hcek). eapply typing_subqual; [exact Hek | exact H].
Qed.

Lemma state_pair_1 : forall E Q e T P e2 k U,
  typing E Q e T ->
  typing_ctx E Q (frame_pair_1 P e2 :: k) T U ->
  exists Q' T1 T2, wf_qua E P /\ typing E Q' e T1 /\ typing E Q' e2 T2 /\
    typing_ctx E Q' k (qtyp_qtyp P (typ_pair T1 T2)) U.
Proof.
  intros E Q e T P e2 k U He Hc.
  remember (frame_pair_1 P e2 :: k) as c eqn:Hce.
  revert P e2 k Hce He.
  induction Hc; intros PP ee2 kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - state_direct.
  - apply (IHHc PP ee2 kk Hcek). eapply typing_sub; [exact Hek | exact H].
  - apply (IHHc PP ee2 kk Hcek). eapply typing_subqual; [exact Hek | exact H].
Qed.

Lemma state_pair_2 : forall E Q e T P v k U,
  typing E Q e T ->
  typing_ctx E Q (frame_pair_2 P v :: k) T U ->
  exists Q' T1 T2, wf_qua E P /\ value v /\ typing E Q' v T1 /\ typing E Q' e T2 /\
    typing_ctx E Q' k (qtyp_qtyp P (typ_pair T1 T2)) U.
Proof.
  intros E Q e T P v k U He Hc.
  remember (frame_pair_2 P v :: k) as c eqn:Hce.
  revert P v k Hce He.
  induction Hc; intros PP vv kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - state_direct.
  - apply (IHHc PP vv kk Hcek). eapply typing_sub; [exact Hek | exact H].
  - apply (IHHc PP vv kk Hcek). eapply typing_subqual; [exact Hek | exact H].
Qed.

Lemma state_first : forall E Q e T k U,
  typing E Q e T ->
  typing_ctx E Q (frame_first :: k) T U ->
  exists Q' P T1 T2, wf_qua E P /\ wf_qtyp E T2 /\
    typing E Q' e (qtyp_qtyp P (typ_pair T1 T2)) /\ typing_ctx E Q' k T1 U.
Proof.
  intros E Q e T k U He Hc.
  remember (frame_first :: k) as c eqn:Hce.
  revert k Hce He.
  induction Hc; intros kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - exists Q, P, T1, T2; repeat split; eauto.
  - apply (IHHc kk Hcek). eapply typing_sub; [exact Hek | exact H].
  - apply (IHHc kk Hcek). eapply typing_subqual; [exact Hek | exact H].
Qed.

Lemma state_second : forall E Q e T k U,
  typing E Q e T ->
  typing_ctx E Q (frame_second :: k) T U ->
  exists Q' P T1 T2, wf_qua E P /\ wf_qtyp E T1 /\
    typing E Q' e (qtyp_qtyp P (typ_pair T1 T2)) /\ typing_ctx E Q' k T2 U.
Proof.
  intros E Q e T k U He Hc.
  remember (frame_second :: k) as c eqn:Hce.
  revert k Hce He.
  induction Hc; intros kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - exists Q, P, T1, T2; repeat split; eauto.
  - apply (IHHc kk Hcek). eapply typing_sub; [exact Hek | exact H].
  - apply (IHHc kk Hcek). eapply typing_subqual; [exact Hek | exact H].
Qed.

Lemma state_upqual : forall E Q e T P k U,
  typing E Q e T ->
  typing_ctx E Q (frame_upqual P :: k) T U ->
  exists Q' T0, typing E Q' e (qtyp_qtyp P T0) /\ typing_ctx E Q' k (qtyp_qtyp P T0) U.
Proof.
  intros E Q e T P k U He Hc.
  remember (frame_upqual P :: k) as c eqn:Hce.
  revert P k Hce He.
  induction Hc; intros PP kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - state_direct.
  - apply (IHHc PP kk Hcek). eapply typing_sub; [exact Hek | exact H].
  - apply (IHHc PP kk Hcek). eapply typing_subqual; [exact Hek | exact H].
Qed.

Lemma state_if0 : forall E Q e T e2 e3 k U,
  typing E Q e T ->
  typing_ctx E Q (frame_if0 e2 e3 :: k) T U ->
  exists Q' Qe T0, wf_qua E Qe /\ typing E Q' e (qtyp_qtyp Qe typ_int) /\
    typing E Q' e2 T0 /\ typing E Q' e3 T0 /\ typing_ctx E Q' k T0 U.
Proof.
  intros E Q e T e2 e3 k U He Hc.
  remember (frame_if0 e2 e3 :: k) as c eqn:Hce.
  revert e2 e3 k Hce He.
  induction Hc; intros ee2 ee3 kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - apply (IHHc ee2 ee3 kk Hcek). eapply typing_sub; [exact Hek | exact H].
  - apply (IHHc ee2 ee3 kk Hcek). eapply typing_subqual; [exact Hek | exact H].
  - state_direct.
Qed.

Lemma state_barrier : forall E Q e T s k U,
  typing E Q e T ->
  typing_ctx E Q (frame_barrier s :: k) T U ->
  exists Q' Q0 T', typing E Q' e T' /\ typing_ctx E Q0 k T' U.
Proof.
  intros E Q e T s k U He Hc.
  remember (frame_barrier s :: k) as c eqn:Hce.
  revert s k Hce He.
  induction Hc; intros ss kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - state_direct.
  - apply (IHHc ss kk Hcek). eapply typing_sub; [exact Hek | exact H].
  - apply (IHHc ss kk Hcek). eapply typing_subqual; [exact Hek | exact H].
Qed.

Lemma state_check : forall E Q e T R k U,
  typing E Q e T ->
  typing_ctx E Q (frame_check R :: k) T U ->
  exists Q' P T0, wf_qua E R /\ typing E Q' e (qtyp_qtyp (qua_meet P R) T0) /\
    typing_ctx E Q' k (qtyp_qtyp P T0) U.
Proof.
  intros E Q e T R k U He Hc.
  remember (frame_check R :: k) as c eqn:Hce.
  revert R k Hce He.
  induction Hc; intros RR kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - state_direct.
  - apply (IHHc RR kk Hcek). eapply typing_sub; [exact Hek | exact H].
  - apply (IHHc RR kk Hcek). eapply typing_subqual; [exact Hek | exact H].
Qed.

Lemma state_without : forall E Q e T t k U,
  typing E Q e T ->
  typing_ctx E Q (frame_without t :: k) T U ->
  exists Q' Q0 T', typing E Q' e T' /\ typing_ctx E Q0 k T' U.
Proof.
  intros E Q e T t k U He Hc.
  remember (frame_without t :: k) as c eqn:Hce.
  revert t k Hce He.
  induction Hc; intros tt kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - apply (IHHc tt kk Hcek). eapply typing_sub; [exact Hek | exact H].
  - apply (IHHc tt kk Hcek). eapply typing_subqual; [exact Hek | exact H].
  - state_direct.
Qed.

(* ================= ChunkBarrier.v ================= *)

Lemma typing_ctx_barrier_compatible :
  forall E Q c T U, typing_ctx E Q c T U ->
  forall Qa t, wf_env E -> wf_qua E Qa -> concretize Qa = Some t ->
    subqual E Qa Q -> barrier_compatible c t.
Proof.
  intros E Q c T U Hc.
  induction Hc as [E Q0 T0 w wq wT
    | E Q0 c0 e1 T1 T2 U0 t0 IH t1
    | E Q0 c0 e1 T1 T2 U0 t0 IH v t1
    | L E Q0 c0 T1 T1' T2 U0 t0 IH s w
    | L E Q0 c0 R R' T2 U0 t0 IH s w
    | L E Q0 c0 e1 T1 T2 U0 t0 IH t1
    | E P Q0 c0 T1 T2 U0 t0 IH
    | E P Q0 c0 T1 T2 U0 t0 IH
    | L E P Q0 c0 T0 T1 T2 e2 e3 U0 w t0 IH t1 t2
    | E P Q0 c0 e T1 T2 U0 w t0 IH t1
    | E P Q0 c0 v T1 T2 U0 w t0 IH v0 t1
    | E P Q0 c0 T1 T2 U0 w t0 IH w0
    | E P Q0 c0 T1 T2 U0 w t0 IH w0
    | E Q0 c0 s t T0 U0 t0 IH cv ord
    | E Q0 c0 P T0 U0 t0 IH
    | E Q0 c0 R P T0 U0 w t0 IH
    | E Q0 c0 S T0 U0 t0 IH s
    | E Q0 R c0 T0 U0 t0 IH s
    | E Q0 c0 t T0 U0 t0 IH
    | E R c0 e2 e3 T0 Q0 U0 w t0 IH t1 t2];
    intros Qa tt HwE HwQ Hconc Hsq.
  - (* done *) apply barrier_compatible_done.
  - (* abs *) eapply barrier_compatible_other; [apply (IH Qa tt HwE HwQ Hconc Hsq) | intros x Hx; discriminate | intros x Hx; discriminate].
  - (* app *) eapply barrier_compatible_other; [apply (IH Qa tt HwE HwQ Hconc Hsq) | intros x Hx; discriminate | intros x Hx; discriminate].
  - (* tabs *) eapply barrier_compatible_other; [apply (IH Qa tt HwE HwQ Hconc Hsq) | intros x Hx; discriminate | intros x Hx; discriminate].
  - (* qabs *) eapply barrier_compatible_other; [apply (IH Qa tt HwE HwQ Hconc Hsq) | intros x Hx; discriminate | intros x Hx; discriminate].
  - (* let *) eapply barrier_compatible_other; [apply (IH Qa tt HwE HwQ Hconc Hsq) | intros x Hx; discriminate | intros x Hx; discriminate].
  - (* inl *) eapply barrier_compatible_other; [apply (IH Qa tt HwE HwQ Hconc Hsq) | intros x Hx; discriminate | intros x Hx; discriminate].
  - (* inr *) eapply barrier_compatible_other; [apply (IH Qa tt HwE HwQ Hconc Hsq) | intros x Hx; discriminate | intros x Hx; discriminate].
  - (* case *) eapply barrier_compatible_other; [apply (IH Qa tt HwE HwQ Hconc Hsq) | intros x Hx; discriminate | intros x Hx; discriminate].
  - (* pair1 *) eapply barrier_compatible_other; [apply (IH Qa tt HwE HwQ Hconc Hsq) | intros x Hx; discriminate | intros x Hx; discriminate].
  - (* pair2 *) eapply barrier_compatible_other; [apply (IH Qa tt HwE HwQ Hconc Hsq) | intros x Hx; discriminate | intros x Hx; discriminate].
  - (* first *) eapply barrier_compatible_other; [apply (IH Qa tt HwE HwQ Hconc Hsq) | intros x Hx; discriminate | intros x Hx; discriminate].
  - (* second *) eapply barrier_compatible_other; [apply (IH Qa tt HwE HwQ Hconc Hsq) | intros x Hx; discriminate | intros x Hx; discriminate].
  - (* barrier *)
    assert (Htle : tt ≤ t).
    { eapply subqual_concretize_ord; [exact Hsq | exact Hconc | reflexivity]. }
    assert (Hbase : subqual E (abstractize t) Q0).
    { eapply subqual_trans.
      - apply subqual_lift_elem; [exact HwE | exact ord].
      - destruct (typing_ctx_wf_qua _ _ _ _ _ t0) as [He0 HQ0].
        eapply concretize_subqual_bwd; [exact He0 | exact HQ0 | exact cv]. }
    assert (HqQ0 : subqual E Qa Q0).
    { eapply subqual_trans; [exact Hsq | exact Hbase]. }
    assert (Hbc : barrier_compatible c0 tt).
    { apply (IH Qa tt HwE HwQ Hconc HqQ0). }
    eapply barrier_compatible_frame; [exact Hbc | exact Htle].
  - (* upqual *) eapply barrier_compatible_other; [apply (IH Qa tt HwE HwQ Hconc Hsq) | intros x Hx; discriminate | intros x Hx; discriminate].
  - (* check *) eapply barrier_compatible_other; [apply (IH Qa tt HwE HwQ Hconc Hsq) | intros x Hx; discriminate | intros x Hx; discriminate].
  - (* sub *) apply (IH Qa tt HwE HwQ Hconc Hsq).
  - (* subqual *)
    assert (HqQ0 : subqual E Qa Q0).
    { eapply subqual_trans; [exact Hsq | exact s]. }
    apply (IH Qa tt HwE HwQ Hconc HqQ0).
  - (* without *)
    destruct (typing_ctx_wf_qua _ _ _ _ _ t0) as [He0 HQ0].
    assert (Hle : tt ≤ (negate t)).
    { eapply subqual_concretize_ord.
      - eapply subqual_trans.
        + exact Hsq.
        + eapply subqual_meet_eliml.
          * apply subqual_base_refl. exact HwE.
          * exact HQ0.
      - exact Hconc.
      - reflexivity. }
    assert (HqQ0 : subqual E Qa Q0).
    { eapply subqual_trans.
      - exact Hsq.
      - eapply subqual_meet_elimr.
        + constructor.
        + apply subqual_refl; assumption. }
    assert (Hbc : barrier_compatible c0 tt).
    { apply (IH Qa tt HwE HwQ Hconc HqQ0). }
    eapply barrier_compatible_without; [exact Hbc | exact Hle].
  - (* if0 *) eapply barrier_compatible_other; [apply (IH Qa tt HwE HwQ Hconc Hsq) | intros x Hx; discriminate | intros x Hx; discriminate].
Qed.

Lemma state_barrier_common :
  forall E Q e T s k U,
    typing E Q e T ->
    typing_ctx E Q (frame_barrier s :: k) T U ->
    exists Qc T', typing E Qc e T' /\ typing_ctx E Qc k T' U.
Proof.
  intros E Q e T s k U He Hc.
  remember (frame_barrier s :: k) as c eqn:Hce.
  revert s k Hce He.
  induction Hc; intros ss kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - (* barrier *)
    eexists; eexists; split; [| exact Hc].
    eapply typing_subqual.
    + exact Hek.
    + eapply subqual_trans.
      * apply subqual_lift_elem.
        -- apply typing_ctx_wf_env in Hc. exact Hc.
        -- exact H0.
      * destruct (typing_ctx_wf_qua _ _ _ _ _ Hc) as [He0 HQ0].
        eapply concretize_subqual_bwd; [exact He0 | exact HQ0 | exact H].
  - apply (IHHc ss kk Hcek). eapply typing_sub; [exact Hek | exact H].
  - apply (IHHc ss kk Hcek). eapply typing_subqual; [exact Hek | exact H].
Qed.

Lemma state_without_common :
  forall E Q e T t k U,
    typing E Q e T ->
    typing_ctx E Q (frame_without t :: k) T U ->
    exists Qc T', typing E Qc e T' /\ typing_ctx E Qc k T' U.
Proof.
  intros E Q e T t k U He Hc.
  remember (frame_without t :: k) as c eqn:Hce.
  revert t k Hce He.
  induction Hc; intros tt kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - apply (IHHc tt kk Hcek). eapply typing_sub; [exact Hek | exact H].
  - apply (IHHc tt kk Hcek). eapply typing_subqual; [exact Hek | exact H].
  - (* without *)
    eexists; eexists; split; [| exact Hc].
    eapply typing_subqual.
    + exact Hek.
    + destruct (typing_ctx_wf_qua _ _ _ _ _ Hc) as [He0 HQ0].
      eapply subqual_meet_elimr.
      * constructor.
      * apply subqual_refl; assumption.
Qed.

Lemma state_barrier_concrete :
  forall E Q e T s k U,
    typing E Q e T ->
    typing_ctx E Q (frame_barrier s :: k) T U ->
    exists Qc s' T', concretize Qc = Some s' /\ s ≤ s' /\
      typing E Qc e T' /\ typing_ctx E Qc k T' U.
Proof.
  intros E Q e T s k U He Hc.
  remember (frame_barrier s :: k) as c eqn:Hce.
  revert s k Hce He.
  induction Hc; intros ss kk Hcek Hek; try (inversion Hcek; subst; clear Hcek).
  - (* barrier *)
    eexists; eexists; eexists; repeat split; [exact H | exact H0 | | exact Hc].
    eapply typing_subqual.
    + exact Hek.
    + eapply subqual_trans.
      * apply subqual_lift_elem.
        -- apply typing_ctx_wf_env in Hc. exact Hc.
        -- exact H0.
      * destruct (typing_ctx_wf_qua _ _ _ _ _ Hc) as [He0 HQ0].
        eapply concretize_subqual_bwd; [exact He0 | exact HQ0 | exact H].
  - assert (HeT : typing E Q e T) by (eapply typing_sub; [exact Hek | exact H]).
    destruct (IHHc ss kk Hcek HeT) as [Q0 [s0 [T0 [Hc0 [Hle [Hty Hctx]]]]]].
    eexists Q0; eexists s0; eexists T0; repeat split; eauto.
  - assert (HeT : typing E Q e T) by (eapply typing_subqual; [exact Hek | exact H]).
    destruct (IHHc ss kk Hcek HeT) as [Q0 [s0 [T0 [Hc0 [Hle [Hty Hctx]]]]]].
    eexists Q0; eexists s0; eexists T0; repeat split; eauto.
Qed.

(* ================= ChunkValueHead.v ================= *)

Lemma typing_value_head : forall E Q e Tt, typing E Q e Tt -> value e ->
  forall Pq Tq, Tt = qtyp_qtyp Pq Tq ->
  (exists Pi i, e = exp_int Pi i /\ subqual E Pi Pq) \/
  (exists Pa V b, e = exp_abs Pa V b /\ subqual E Pa Pq) \/
  (exists Pa V b, e = exp_tabs Pa V b /\ subqual E Pa Pq) \/
  (exists Pa Qb b, e = exp_qabs Pa Qb b /\ subqual E Pa Pq) \/
  (exists Pa b, e = exp_inl Pa b /\ subqual E Pa Pq) \/
  (exists Pa b, e = exp_inr Pa b /\ subqual E Pa Pq) \/
  (exists Pa b1 b2, e = exp_pair Pa b1 b2 /\ subqual E Pa Pq).
Proof.
  intros E Q e Tt H.
  induction H as [E Pi i Hwf HP
    | E x T0 Hwf Hb
    | L0 E Pa V b T1 Hp IHp
    | Qa T1 E a1 a2 T2 H1 IH1 H2 IH2
    | L0 E Pa V b T1 Hp IHp
    | Qa T1 E e1 Ta T2 H1 IH1 Hs
    | L0 E Pa Qb b T1 HP Hp IHp
    | Qa E e1 Qb T0 H1 IH1 Hs
    | S E Qa e0 T0 H1 IH1 Hs
    | E Qa R e0 T0 H1 IH1 Hs
    | L T1 T2 e1 e2 E Qa H1 IH1 H2 IH2
    | T1 T2 Pa e1 E Qa HP H1 IH1 HT2
    | T1 T2 Pa e1 E Qa HP H1 IH1 HT1
    | L T1 T2 Pa T0 e1 e2 e3 E Qa H1 IH1 H2 IH2 H3 IH3
    | T1 T2 Pa e1 e2 E Qa HP H1 IH1 H2 IH2
    | Qa T1 T2 Pa e0 H1 IH1
    | Qa T1 T2 Pa e0 H1 IH1
    | E R Qa T0 Pa e0 H1 IH1 Hs
    | E R Qa T0 Pa e0 H1 IH1 Hs
    | E R Qa T0 Pa e0 H1 IH1 Hs
    | E b Hwfb
    | E R Qa e1 e2 e3 T0 H1 IH1 H2 IH2 H3 IH3];
    intros Vv Pq Tq HT.
  - (* int *) left. exists Pi, i. split; [reflexivity|].
    inversion HT; try subst Pq. eapply subqual_refl; eassumption.
  - exfalso; inversion Vv.
  - (* abs *) right. left. exists Pa, V, b. split; [reflexivity|].
    inversion HT; try subst Pq.
    assert (Hwf : wf_env E).
    { pick fresh y for L0. eapply wf_env_cons_inv. eapply typing_wf_env. apply (Hp y Fr). }
    assert (Hq : wf_qua E Pa).
    { pick fresh y for L0.
      apply (wf_qua_remove_typ_mid Pa (@nil (atom*binding)) y V E).
      eapply typing_wf_qua. apply (Hp y Fr). }
    eapply subqual_refl; eassumption.
  - exfalso; inversion Vv.
  - (* tabs *) right. right. left. exists Pa, V, b. split; [reflexivity|].
    inversion HT; try subst Pq.
    assert (Hwf : wf_env E).
    { pick fresh y for L0. eapply wf_env_cons_inv. eapply typing_wf_env. apply (Hp y Fr). }
    assert (Hq : wf_qua E Pa).
    { pick fresh y for L0.
      apply (wf_qua_remove_sub_mid Pa (@nil (atom*binding)) y V E).
      eapply typing_wf_qua. apply (Hp y Fr). }
    eapply subqual_refl; eassumption.
  - exfalso; inversion Vv.
  - (* qabs *) right. right. right. left. exists Pa, Qb, b. split; [reflexivity|].
    inversion HT; try subst Pq.
    assert (Hwf : wf_env E).
    { pick fresh y for L0. eapply wf_env_cons_inv. eapply typing_wf_env. apply (Hp y Fr). }
    eapply subqual_refl; eassumption.
  - exfalso; inversion Vv.
  - (* sub *) subst T0.
    inversion Hs.
    subst S; subst Pq; subst Tq.
    assert (HIH := IH1 Vv Q1 T1 eq_refl).
    destruct HIH as [D|[D|[D|[D|[D|[D|D]]]]]];
      [| | | | | | ].
    + destruct D as [Pi [i [He Hsq]]]. left. exists Pi,i. split; [exact He|].
      eapply subqual_trans; eassumption.
    + destruct D as [Pa [V [b [He Hsq]]]]. right; left. exists Pa,V,b. split; [exact He|].
      eapply subqual_trans; eassumption.
    + destruct D as [Pa [V [b [He Hsq]]]]. right; right; left. exists Pa,V,b. split; [exact He|].
      eapply subqual_trans; eassumption.
    + destruct D as [Pa [Qb [b [He Hsq]]]]. right; right; right; left. exists Pa,Qb,b. split; [exact He|].
      eapply subqual_trans; eassumption.
    + destruct D as [Pa [b [He Hsq]]]. right; right; right; right; left. exists Pa,b. split; [exact He|].
      eapply subqual_trans; eassumption.
    + destruct D as [Pa [b [He Hsq]]]. right; right; right; right; right; left. exists Pa,b. split; [exact He|].
      eapply subqual_trans; eassumption.
    + destruct D as [Pa [b1 [b2 [He Hsq]]]]. right; right; right; right; right; right. exists Pa,b1,b2. split; [exact He|].
      eapply subqual_trans; eassumption.
  - (* subqual *) apply (IH1 Vv Pq Tq HT).
  - exfalso; inversion Vv.
  - (* inl *) right. right. right. right. left. exists Pa, e1. split; [reflexivity|].
    inversion HT; try subst Pq.
    assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
    eapply subqual_refl; [exact Hwf | exact HP].
  - (* inr *) right. right. right. right. right. left. exists Pa, e1. split; [reflexivity|].
    inversion HT; try subst Pq.
    assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
    eapply subqual_refl; [exact Hwf | exact HP].
  - exfalso; inversion Vv.
  - (* pair *) right. right. right. right. right. right. exists Pa, e1, e2. split; [reflexivity|].
    inversion HT; try subst Pq.
    assert (Hwf : wf_env E) by (eapply typing_wf_env; eassumption).
    eapply subqual_refl; [exact Hwf | exact HP].
  - exfalso; inversion Vv.
  - exfalso; inversion Vv.
  - exfalso; inversion Vv.
  - exfalso; inversion Vv.
  - exfalso; inversion Vv.
  - exfalso; inversion Vv.
  - exfalso; inversion Vv.
Qed.

(* ================= ChunkSubqualConcrete.v ================= *)

(* If a subqual derivation has a target that concretizes to some b, then the
   same derivation can be retargeted at the concrete base qualifier for b. *)
Lemma subqual_concrete_target : forall (E:env) (R Q:qua),
  subqual E R Q ->
  forall b, concretize Q = Some b -> subqual E R (qua_base b).
Proof.
  intros E R Q H.
  induction H as
  [ E Q wfE HQ
  | E Q wfE HQ
  | E Q' Q R b' h1 IH1 h2 h3 IH3
  | E Q' Q R b' h1 IH1 h2 h3 IH3
  | E b1 b2 wfE Ho
  | E X wfE HQ
  | R0 E Q X hb h1 IH1
  | E R1 R2 Q h1 IH1 wfR2
  | E R1 R2 Q wfR1 h2 IH2
  | E R1 R2 Q h1 IH1 h2 IH2
  | E R1 R2 Q h1 IH1 wfR2
  | E R1 R2 Q wfR1 h2 IH2
  | E R1 R2 Q h1 IH1 h2 IH2
  | E Q R S wfE HQ HR HS
  | E Q R S h1 IH1 h2 IH2
  | E Q wfE HQ
  | E Q wfE HQ
  | E Q wfE HQ ];
  intros b Hc.
  - (* subqual_top *)
    apply concretize_base_inv in Hc. subst b.
    apply subqual_top; assumption.
  - (* subqual_bot *)
    apply subqual_bot; [exact wfE | apply wf_qua_base].
  - (* subqual_eval_elim *)
    eapply subqual_trans with (R := qua_base b').
    + apply IH1. exact h2.
    + apply IH3. exact Hc.
  - (* subqual_eval_intro *)
    destruct (subqual_wf _ _ _ h1) as [Hwf [HQ' _]].
    eapply subqual_trans with (R := qua_base b').
    + exact h3.
    + eapply subqual_trans with (R := Q').
      * exact (concretize_subqual_bwd E Q' b' Hwf HQ' h2).
      * apply IH1. exact Hc.
  - (* subqual_lift_elem *)
    apply concretize_base_inv in Hc. subst b.
    apply subqual_lift_elem; assumption.
  - (* subqual_refl_qvar *)
    cbn [concretize] in Hc. discriminate Hc.
  - (* subqual_trans_qvar *)
    eapply subqual_trans_qvar; [exact hb | apply IH1; exact Hc].
  - (* subqual_join_inl *)
    destruct (subqual_wf _ _ _ h1) as [Hwf _].
    destruct (concretize_join_inv _ _ _ Hc) as [b1' [b2' [E1 [E2 Hb]]]].
    subst b.
    eapply subqual_trans.
    + apply IH1. exact E1.
    + eapply subqual_lift_elem; [exact Hwf | apply ord_join_l].
  - (* subqual_join_inr *)
    destruct (subqual_wf _ _ _ h2) as [Hwf _].
    destruct (concretize_join_inv _ _ _ Hc) as [b1' [b2' [E1 [E2 Hb]]]].
    subst b.
    eapply subqual_trans.
    + apply IH2. exact E2.
    + eapply subqual_lift_elem; [exact Hwf | apply ord_join_r].
  - (* subqual_join_elim *)
    apply subqual_join_elim; [apply IH1; exact Hc | apply IH2; exact Hc].
  - (* subqual_meet_eliml *)
    eapply subqual_meet_eliml; [apply IH1; exact Hc | exact wfR2].
  - (* subqual_meet_elimr *)
    eapply subqual_meet_elimr; [exact wfR1 | apply IH2; exact Hc].
  - (* subqual_meet_intro *)
    destruct (subqual_wf _ _ _ h1) as [Hwf _].
    destruct (concretize_meet_inv _ _ _ Hc) as [b1' [b2' [E1 [E2 Hb]]]].
    subst b.
    eapply subqual_trans with (R := qua_meet (qua_base b1') (qua_base b2')).
    + apply subqual_meet_intro.
      * apply IH1. exact E1.
      * apply IH2. exact E2.
    + apply subqual_meet_base_fwd. exact Hwf.
  - (* subqual_dist *)
    eapply subqual_eval_elim
      with (Q' := qua_join (qua_meet Q R) (qua_meet Q S)) (b := b).
    + apply subqual_dist; assumption.
    + exact Hc.
    + apply subqual_base_refl. exact wfE.
  - (* subqual_trans *)
    eapply subqual_trans.
    + exact h1.
    + apply IH2. exact Hc.
  - (* subqual_negate_intro *)
    destruct (concretize_join_inv _ _ _ Hc) as [b1' [b2' [E1 [E2 Hb]]]].
    destruct (concretize_negate_inv _ _ E2) as [q [F1 Fb2]].
    assert (Hb1q : b1' = q).
    { rewrite F1 in E1. injection E1 as Heq. symmetry. exact Heq. }
    subst b1'. subst b2'.
    rewrite (negate_bot q) in Hb. subst b.
    apply subqual_base_refl. exact wfE.
  - (* subqual_negate_elim *)
    apply concretize_base_inv in Hc. subst b.
    apply subqual_negate_elim; assumption.
  - (* subqual_refl_negate *)
    destruct (concretize_negate_inv _ _ Hc) as [q [Hq Hb]].
    subst b.
    destruct (concretize_subqual_mut Q E wfE HQ q Hq) as [Hf Hbwd].
    eapply subqual_trans with (R := qua_negate (qua_base q)).
    + exact (subqual_negate_contra E (qua_base q) Q wfE
               (wf_qua_base E q) HQ Hbwd).
    + apply subqual_neg_base_fwd. exact wfE.
Qed.

Corollary subqual_negate_concrete : forall (E:env) (R Q:qua) t,
  subqual E R (qua_negate Q) -> concretize Q = Some t ->
  subqual E R (qua_base (negate t)).
Proof.
  intros E R Q t H Hc.
  eapply subqual_concrete_target.
  - exact H.
  - cbn [concretize]. rewrite Hc. reflexivity.
Qed.

(* ================= ChunkPresPush.v ================= *)

Lemma wf_qua_of_typing_qtyp : forall E Q e P T,
  typing E Q e (qtyp_qtyp P T) -> wf_qua E P.
Proof.
  intros. destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ H)) as [HP _]. exact HP.
Qed.

Lemma wf_qtyp_of_typing_typ : forall E Q e (P:qua) T,
  typing E Q e (qtyp_qtyp P T) -> wf_typ E T.
Proof.
  intros. destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ H)) as [_ HT]. exact HT.
Qed.

Lemma typing_state_inv : forall E e k U,
  typing_state E (state_step e k) U ->
  exists Q T, typing E Q e T /\ typing_ctx E Q k T U.
Proof.
  intros E e k U H. inversion H; subst. eauto.
Qed.

Lemma pres_app_1 : forall E e1 e2 k U,
  typing_state E 〈 exp_app e1 e2 | k 〉 U ->
  typing_state E 〈 e1 | frame_abs e2 :: k 〉 U.
Proof.
  intros E e1 e2 k U HT.
  destruct (typing_state_inv E (exp_app e1 e2) k U HT) as [Q [T [Hty Hctx]]].
  destruct (C_app E Q e1 e2 T k U Hty Hctx)
    as [R [T1 [T2 [Hty1 [Hty2 Hctx']]]]].
  eapply typing_step.
  - exact Hty1.
  - eapply typing_ctx_abs; eassumption.
Qed.


Lemma pres_tapp : forall E e1 V k U,
  typing_state E 〈 exp_tapp e1 V | k 〉 U ->
  typing_state E 〈 e1 | frame_tabs V :: k 〉 U.
Proof.
  intros E e1 V k U HT.
  destruct (typing_state_inv E (exp_tapp e1 V) k U HT) as [Q [T [Hty Hctx]]].
  destruct (C_tapp E Q e1 V T k U Hty Hctx) as [R [T1 [T2 [Hty1 [Hsub Hctx']]]]].
  destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ Hty1)) as [_ Hall].
  destruct (wf_typ_all_inv E T1 T2 Hall) as [_ [L Hbody]].
  eapply typing_step.
  - exact Hty1.
  - eapply typing_ctx_tabs with (L := L); eassumption.
Qed.

Lemma pres_qapp : forall E e1 Qb k U,
  typing_state E 〈 exp_qapp e1 Qb | k 〉 U ->
  typing_state E 〈 e1 | frame_qabs Qb :: k 〉 U.
Proof.
  intros E e1 Qb k U HT.
  destruct (typing_state_inv E (exp_qapp e1 Qb) k U HT) as [Q [T [Hty Hctx]]].
  destruct (C_qapp E Q e1 Qb T k U Hty Hctx) as [R [Q1 [T1 [Hty1 [Hsub Hctx']]]]].
  destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ Hty1)) as [_ Hall].
  destruct (wf_typ_qall_inv E Q1 T1 Hall) as [_ [L Hbody]].
  eapply typing_step.
  - exact Hty1.
  - eapply typing_ctx_qabs with (L := L); eassumption.
Qed.

Lemma pres_let : forall E e1 e2 k U,
  typing_state E 〈 exp_let e1 e2 | k 〉 U ->
  typing_state E 〈 e1 | frame_let e2 :: k 〉 U.
Proof.
  intros E e1 e2 k U HT.
  destruct (typing_state_inv E (exp_let e1 e2) k U HT) as [Q [T [Hty Hctx]]].
  destruct (C_let E Q e1 e2 T k U Hty Hctx) as [R [L [T1 [T2 [Hty1 [Hbody Hctx']]]]]].
  eapply typing_step.
  - exact Hty1.
  - eapply typing_ctx_let with (L := L); eassumption.
Qed.

Lemma pres_inl : forall E e1 P k U,
  typing_state E 〈 exp_inl P e1 | k 〉 U ->
  typing_state E 〈 e1 | frame_inl P :: k 〉 U.
Proof.
  intros E e1 P k U HT.
  destruct (typing_state_inv E (exp_inl P e1) k U HT) as [Q [T [Hty Hctx]]].
  destruct (C_inl E Q e1 P T k U Hty Hctx) as [R [T1 [T2 [HP [Hty1 [HT2 Hctx']]]]]].
  eapply typing_step.
  - exact Hty1.
  - eapply typing_ctx_inl; eassumption.
Qed.

Lemma pres_inr : forall E e1 P k U,
  typing_state E 〈 exp_inr P e1 | k 〉 U ->
  typing_state E 〈 e1 | frame_inr P :: k 〉 U.
Proof.
  intros E e1 P k U HT.
  destruct (typing_state_inv E (exp_inr P e1) k U HT) as [Q [T [Hty Hctx]]].
  destruct (C_inr E Q e1 P T k U Hty Hctx) as [R [T1 [T2 [HP [Hty1 [HT1 Hctx']]]]]].
  eapply typing_step.
  - exact Hty1.
  - eapply typing_ctx_inr; eassumption.
Qed.

Lemma pres_case : forall E e1 e2 e3 k U,
  typing_state E 〈 exp_case e1 e2 e3 | k 〉 U ->
  typing_state E 〈 e1 | frame_case e2 e3 :: k 〉 U.
Proof.
  intros E e1 e2 e3 k U HT.
  destruct (typing_state_inv E (exp_case e1 e2 e3) k U HT) as [Q [T [Hty Hctx]]].
  destruct (C_case E Q e1 e2 e3 T k U Hty Hctx)
    as [R [L [P [T1 [T2 [T0 [Hty1 [Hbody2 [Hbody3 Hctx']]]]]]]]].
  assert (HP : wf_qua E P).
  { eapply wf_qua_of_typing_qtyp; exact Hty1. }
  eapply typing_step.
  - exact Hty1.
  - eapply typing_ctx_case with (L := L); eassumption.
Qed.

Lemma pres_pair_1 : forall E P e1 e2 k U,
  typing_state E 〈 exp_pair P e1 e2 | k 〉 U ->
  typing_state E 〈 e1 | frame_pair_1 P e2 :: k 〉 U.
Proof.
  intros E P e1 e2 k U HT.
  destruct (typing_state_inv E (exp_pair P e1 e2) k U HT) as [Q [T [Hty Hctx]]].
  destruct (C_pair E Q e1 e2 P T k U Hty Hctx) as [R [T1 [T2 [HP [Hty1 [Hty2 Hctx']]]]]].
  eapply typing_step.
  - exact Hty1.
  - eapply typing_ctx_pair_1; eassumption.
Qed.

Lemma pres_pair_2 : forall E P v e2 k U,
  value v ->
  typing_state E 〈 v | frame_pair_1 P e2 :: k 〉 U ->
  typing_state E 〈 e2 | frame_pair_2 P v :: k 〉 U.
Proof.
  intros E P v e2 k U Hv HT.
  destruct (typing_state_inv E v (frame_pair_1 P e2 :: k) U HT) as [Q [T [Hty Hctx]]].
  destruct (state_pair_1 E Q v T P e2 k U Hty Hctx)
    as [R [T1 [T2 [HP [Htyv [Htye2 Hctx']]]]]].
  eapply typing_step.
  - exact Htye2.
  - eapply typing_ctx_pair_2; eassumption.
Qed.

Lemma pres_first : forall E e1 k U,
  typing_state E 〈 exp_first e1 | k 〉 U ->
  typing_state E 〈 e1 | frame_first :: k 〉 U.
Proof.
  intros E e1 k U HT.
  destruct (typing_state_inv E (exp_first e1) k U HT) as [Q [T [Hty Hctx]]].
  destruct (C_first E Q e1 T k U Hty Hctx) as [R [P [T1 [T2 [Hty1 Hctx']]]]].
  destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ Hty1)) as [HP HTp].
  destruct (wf_typ_pair_inv _ _ _ HTp) as [_ HT2].
  eapply typing_step.
  - exact Hty1.
  - eapply typing_ctx_first; eassumption.
Qed.

Lemma pres_second : forall E e1 k U,
  typing_state E 〈 exp_second e1 | k 〉 U ->
  typing_state E 〈 e1 | frame_second :: k 〉 U.
Proof.
  intros E e1 k U HT.
  destruct (typing_state_inv E (exp_second e1) k U HT) as [Q [T [Hty Hctx]]].
  destruct (C_second E Q e1 T k U Hty Hctx) as [R [P [T1 [T2 [Hty1 Hctx']]]]].
  destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ Hty1)) as [HP HTp].
  destruct (wf_typ_pair_inv _ _ _ HTp) as [HT1 _].
  eapply typing_step.
  - exact Hty1.
  - eapply typing_ctx_second; eassumption.
Qed.

Lemma pres_upqual_1 : forall E P e1 k U,
  typing_state E 〈 exp_upqual P e1 | k 〉 U ->
  typing_state E 〈 e1 | frame_upqual P :: k 〉 U.
Proof.
  intros E P e1 k U HT.
  destruct (typing_state_inv E (exp_upqual P e1) k U HT) as [Q [T [Hty Hctx]]].
  destruct (C_upqual E Q e1 P T k U Hty Hctx) as [R [Q' [T' [Hty1 [Hsub Hctx']]]]].
  destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ Hty1)) as [_ HT'].
  assert (Hsubq : subqtype E (qtyp_qtyp Q' T') (qtyp_qtyp P T')).
  { eapply sub_qtyp_qtyp; [exact Hsub|].
    eapply sub_refl; [apply (typing_wf_env _ _ _ _ Hty1)|exact HT']. }
  assert (HtyP : typing E R e1 (qtyp_qtyp P T'))
    by (eapply typing_sub; eassumption).
  eapply typing_step.
  - exact HtyP.
  - eapply typing_ctx_upqual; eassumption.
Qed.

Lemma pres_check_1 : forall E P e1 k U,
  typing_state E 〈 exp_check P e1 | k 〉 U ->
  typing_state E 〈 e1 | frame_check P :: k 〉 U.
Proof.
  intros E P e1 k U HT.
  destruct (typing_state_inv E (exp_check P e1) k U HT) as [Q [T [Hty Hctx]]].
  destruct (C_check E Q e1 P T k U Hty Hctx) as [R [Q' [T' [Hty1 [Hsub Hctx']]]]].
  assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ _ Hty1)).
  assert (HQ' : wf_qua E Q') by (eapply wf_qua_of_typing_qtyp; exact Hty1).
  destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ Hty1)) as [_ HT'].
  assert (HsubM : subqual E Q' (qua_meet Q' P)).
  { eapply subqual_meet_intro.
    - eapply subqual_refl; eassumption.
    - exact Hsub. }
  assert (Hsubq : subqtype E (qtyp_qtyp Q' T') (qtyp_qtyp (qua_meet Q' P) T')).
  { eapply sub_qtyp_qtyp; [exact HsubM|].
    eapply sub_refl; eassumption. }
  assert (HtyM : typing E R e1 (qtyp_qtyp (qua_meet Q' P) T'))
    by (eapply typing_sub; eassumption).
  destruct (subqual_wf _ _ _ Hsub) as [_ [_ HP]].
  eapply typing_step.
  - exact HtyM.
  - eapply typing_ctx_check; eassumption.
Qed.

Lemma pres_if0_1 : forall E e1 e2 e3 k U,
  typing_state E 〈 exp_if0 e1 e2 e3 | k 〉 U ->
  typing_state E 〈 e1 | frame_if0 e2 e3 :: k 〉 U.
Proof.
  intros E e1 e2 e3 k U HT.
  destruct (typing_state_inv E (exp_if0 e1 e2 e3) k U HT) as [Q [T [Hty Hctx]]].
  destruct (C_if0 E Q e1 e2 e3 T k U Hty Hctx) as [R [Q' [T0 [Hty1 [Hty2 [Hty3 Hctx']]]]]].
  assert (HQ' : wf_qua E Q') by (eapply wf_qua_of_typing_qtyp; exact Hty1).
  eapply typing_step.
  - exact Hty1.
  - eapply typing_ctx_if0; eassumption.
Qed.

Lemma pres_do : forall E b k U,
  typing_state E 〈 exp_do b | k 〉 U ->
  typing_state E 〈 exp_int (qua_base bot) 42 | k 〉 U.
Proof.
  intros E b k U HT.
  destruct (typing_state_inv E (exp_do b) k U HT) as [Q [T [Hty Hctx]]].
  destruct (C_do E Q b T k U Hty Hctx) as [R Hctx'].
  destruct (typing_ctx_wf_qua _ _ _ _ _ Hctx') as [HwfE HR].
  eapply typing_step.
  - eapply typing_subqual.
    + eapply typing_int; [exact HwfE|apply wf_qua_base].
    + eapply subqual_bot; [exact HwfE|exact HR].
  - exact Hctx'.
Qed.

Lemma pres_barrier : forall E e s k U,
  value e ->
  typing_state E 〈 e | frame_barrier s :: k 〉 U ->
  typing_state E 〈 e | k 〉 U.
Proof.
  intros E e s k U Hv HT.
  destruct (typing_state_inv E e (frame_barrier s :: k) U HT) as [Q [T [Hty Hctx]]].
  destruct (state_barrier_common E Q e T s k U Hty Hctx) as [R [T' [Hty' Hctx']]].
  eapply typing_step; eassumption.
Qed.

Lemma pres_elim_without : forall E e s k U,
  value e ->
  typing_state E 〈 e | frame_without s :: k 〉 U ->
  typing_state E 〈 e | k 〉 U.
Proof.
  intros E e s k U Hv HT.
  destruct (typing_state_inv E e (frame_without s :: k) U HT) as [Q [T [Hty Hctx]]].
  destruct (state_without_common E Q e T s k U Hty Hctx) as [R [T' [Hty' Hctx']]].
  eapply typing_step; eassumption.
Qed.

Lemma pres_if0_zero : forall E Q e2 e3 k U,
  typing_state E 〈 exp_int Q 0%Z | frame_if0 e2 e3 :: k 〉 U ->
  typing_state E 〈 e2 | k 〉 U.
Proof.
  intros E Q e2 e3 k U HT.
  destruct (typing_state_inv E (exp_int Q 0%Z) (frame_if0 e2 e3 :: k) U HT) as [R [T [Hty Hctx]]].
  destruct (state_if0 E R (exp_int Q 0%Z) T e2 e3 k U Hty Hctx)
    as [R' [Qe [T0 [HQe [Hty1 [Hty2 [Hty3 Hctx']]]]]]].
  eapply typing_step; eassumption.
Qed.

Lemma pres_if0_nonzero : forall E Q (n:Z) e2 e3 k U,
  not (Z.eq n 0) ->
  typing_state E 〈 exp_int Q n | frame_if0 e2 e3 :: k 〉 U ->
  typing_state E 〈 e3 | k 〉 U.
Proof.
  intros E Q n e2 e3 k U Hn HT.
  destruct (typing_state_inv E (exp_int Q n) (frame_if0 e2 e3 :: k) U HT) as [R [T [Hty Hctx]]].
  destruct (state_if0 E R (exp_int Q n) T e2 e3 k U Hty Hctx)
    as [R' [Qe [T0 [HQe [Hty1 [Hty2 [Hty3 Hctx']]]]]]].
  eapply typing_step; eassumption.
Qed.


Lemma pres_app_abs : forall E Qa V e1 e2 t k U,
  value e2 ->
  concretize Qa = Some t ->
  barrier_compatible k t ->
  typing_state E 〈 e2 | frame_app (exp_abs Qa V e1) :: k 〉 U ->
  typing_state E 〈 open_ee e1 e2 | frame_barrier t :: k 〉 U.
Proof.
  intros E Qa V e1 e2 t k U Hv Hconc Hbc HT.
  destruct (typing_state_inv E e2 (frame_app (exp_abs Qa V e1) :: k) U HT)
    as [Q [T [Hty Hctx]]].
  destruct (state_app E Q e2 T (exp_abs Qa V e1) k U Hty Hctx)
    as [Q' [T1 [T2 [He2 [Hvf [Hf Hctx']]]]]].
  destruct (typing_abs_core_wf E Q' (exp_abs Qa V e1) (qtyp_qtyp Q' (typ_arrow T1 T2))
              Hf Qa V e1 eq_refl)
    as [Tbody [L [Pq [A [B [Hbody [Hwf [Hsq Hdis]]]]]]]].
  destruct Hdis as [[HeqT [HsA HsB]] | Htop].
  - inversion HeqT; subst.
    assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ _ He2)).
    assert (HQ : wf_qua E Qa) by (destruct (subqual_wf _ _ _ Hsq) as [_ [HQ _]]; exact HQ).
    assert (He2V : typing E Pq e2 V) by (eapply typing_sub; eassumption).
    assert (He2bot : typing E (qua_base bot) e2 V).
    { eapply typing_value_effect; [exact He2V | exact Hv | exact HwfE | apply wf_qua_base]. }
    pick fresh x for (L \u dom E \u fv_ee e1).
    assert (HxL : x `notin` L) by (apply notin_union_1 in Fr; exact Fr).
    pose proof (Hbody x HxL) as Hbodyx.
    assert (HbodySub : typing E Qa (subst_ee x e2 (open_ee e1 x)) Tbody).
    { eapply (typing_subst_ee_gen (x ~ bind_typ V ++ E) Qa (open_ee e1 x) Tbody Hbodyx
                (@nil (atom*binding)) x V E e2 eq_refl
                (value_closed_ee e2 Hv) (value_closed_te e2 Hv)
                (value_closed_qe e2 Hv) HwfE He2bot). }
    rewrite (subst_ee_open_ee_self e1 x e2 (value_closed_ee e2 Hv)) in HbodySub.
    rewrite (subst_ee_id e1 x e2) in HbodySub.
    + assert (Hbase : subqual E Qa (qua_base t)).
      { eapply concretize_subqual; eassumption. }
      assert (HbodyB : typing E Qa (open_ee e1 e2) B)
        by (eapply typing_sub; [exact HbodySub|exact HsB]).
      assert (HbodyFinal : typing E (qua_base t) (open_ee e1 e2) B).
      { eapply typing_subqual; [exact HbodyB|exact Hbase]. }
      assert (HctxQ : typing_ctx E Qa k B U).
      { eapply typing_ctx_subqual; [exact Hctx'|exact Hsq]. }
      assert (HctxBar : typing_ctx E (qua_base t) (frame_barrier t :: k) B U).
      { eapply typing_ctx_barrier; [exact HctxQ|exact Hconc|apply ord_refl_B]. }
      eapply typing_step; eassumption.
    + pose proof Fr as Hx; apply notin_union_2 in Hx; apply notin_union_2 in Hx; exact Hx.
  - inversion Htop.
Qed.


Lemma pres_app_tabs : forall E Qa U e1 V t k Uout,
  type V ->
  concretize Qa = Some t ->
  barrier_compatible k t ->
  typing_state E 〈 exp_tabs Qa U e1 | frame_tabs V :: k 〉 Uout ->
  typing_state E 〈 open_te e1 V | frame_barrier t :: k 〉 Uout.
Proof.
  intros E Qa U e1 V t k Uout HtypeV Hconc Hbc HT.
  destruct (typing_state_inv E (exp_tabs Qa U e1) (frame_tabs V :: k) Uout HT)
    as [Q [T [Hty Hctx]]].
  destruct (state_tabs E Q (exp_tabs Qa U e1) T V k Uout Hty Hctx)
    as [Q' [Lst [T1 [T2 [Hf [HsubV [Hwfb Hctx']]]]]]].
  destruct (typing_tabs_core_wf E Q' (exp_tabs Qa U e1)
              (qtyp_qtyp Q' (typ_all T1 T2)) Hf Qa U e1 eq_refl)
    as [Tbody [L0 [Pq [A [B [L2 [Hbody [Hwf [Hsq Hdis]]]]]]]]].
  destruct Hdis as [[HeqT [HsA HsB]] | Htop].
  - inversion HeqT; subst.
    assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ _ Hf)).
    assert (HQa : wf_qua E Qa) by (destruct (subqual_wf _ _ _ Hsq) as [_ [HQ _]]; exact HQ).
    assert (HVwf : wf_typ E V) by (destruct (sub_wf _ _ _ HsubV) as [_ [HV _]]; exact HV).
    assert (HclosedV : closed_tt V) by (apply (wf_typ_closed_tt E V HVwf)).
    assert (HsubVT : sub E V U).
    { eapply sub_trans; [exact HsubV | exact HsA]. }
    pick fresh X for (L0 \u (L2 \u (dom E \u (fv_te e1 \u (fv_tt U \u (fv_tqt Tbody \u (fv_tqt B \u fv_tt A))))))).
    pose proof (notin_union_1 _ _ _ Fr) as HXL0.
    pose proof (notin_union_2 _ _ _ Fr) as F1.
    pose proof (notin_union_1 _ _ _ F1) as HXL2.
    pose proof (notin_union_2 _ _ _ F1) as F2.
    pose proof (notin_union_1 _ _ _ F2) as HXdom.
    pose proof (notin_union_2 _ _ _ F2) as F3.
    pose proof (notin_union_1 _ _ _ F3) as HXte.
    pose proof (notin_union_2 _ _ _ F3) as F4.
    pose proof (notin_union_1 _ _ _ F4) as HXU.
    pose proof (notin_union_2 _ _ _ F4) as F5.
    pose proof (notin_union_1 _ _ _ F5) as HXTb.
    pose proof (notin_union_2 _ _ _ F5) as F6.
    pose proof (notin_union_1 _ _ _ F6) as HXB.
    pose proof (notin_union_2 _ _ _ F6) as HXA.
    assert (Henv : subst_te_env X V ((@nil (atom*binding)) ++ E) = E).
    { simpl. apply (subst_te_env_id E X V HwfE HXdom). }
    assert (HbodyX := Hbody X HXL0).
    assert (HbodyVraw : typing (subst_te_env X V ((@nil (atom*binding)) ++ E)) Qa
                 (subst_te X V (open_te e1 X)) (subst_tqt X V (open_tqt Tbody X))).
    { eapply (typing_subst_te_gen (X ~ bind_sub U ++ E) Qa (open_te e1 X) (open_tqt Tbody X) HbodyX
                (@nil (atom*binding)) X U E V eq_refl).
      - rewrite Henv. exact HwfE.
      - rewrite Henv. exact HVwf.
      - rewrite Henv. rewrite (subst_tt_id U X V HXU). exact HsubVT. }
    rewrite Henv in HbodyVraw.
    assert (HbodyV := HbodyVraw).
    rewrite (subst_te_open_te_self e1 X V HclosedV) in HbodyV.
    rewrite (subst_te_id e1 X V HXte) in HbodyV.
    rewrite (subst_tqt_open_tqt_self Tbody X V HclosedV) in HbodyV.
    rewrite (subst_tqt_id Tbody X V HXTb) in HbodyV.
    assert (HsubqVraw : subqtype (subst_te_env X V ((@nil (atom*binding)) ++ E))
                 (subst_tqt X V (open_tqt Tbody X)) (subst_tqt X V (open_tqt B X))).
    { eapply (subqtype_subst_te (X ~ bind_sub A ++ E)
                (open_tqt Tbody X) (open_tqt B X) (HsB X HXL2)
                (@nil (atom*binding)) X A E V eq_refl).
      - rewrite Henv. exact HwfE.
      - rewrite Henv. exact HVwf.
      - rewrite Henv. rewrite (subst_tt_id A X V HXA). exact HsubV. }
    rewrite Henv in HsubqVraw.
    assert (HsubqV := HsubqVraw).
    rewrite (subst_tqt_open_tqt_self Tbody X V HclosedV) in HsubqV.
    rewrite (subst_tqt_id Tbody X V HXTb) in HsubqV.
    rewrite (subst_tqt_open_tqt_self B X V HclosedV) in HsubqV.
    rewrite (subst_tqt_id B X V HXB) in HsubqV.
        assert (HbodyTgt : typing E Qa (open_te e1 V) (open_tqt B V))
          by (eapply typing_sub; [exact HbodyV|exact HsubqV]).
        assert (Hbase : subqual E Qa (qua_base t)).
        { eapply concretize_subqual; eassumption. }
        assert (HbodyFinal : typing E (qua_base t) (open_te e1 V) (open_tqt B V)).
        { eapply typing_subqual; [exact HbodyTgt|exact Hbase]. }
        assert (HctxQ : typing_ctx E Qa k (open_tqt B V) Uout).
        { eapply typing_ctx_subqual; [exact Hctx'|exact Hsq]. }
        assert (HctxBar : typing_ctx E (qua_base t) (frame_barrier t :: k) (open_tqt B V) Uout).
        { eapply typing_ctx_barrier; [exact HctxQ|exact Hconc|apply ord_refl_B]. }
        eapply typing_step; eassumption.
  - inversion Htop.
Qed.


Lemma pres_let_value : forall E v1 e2 k U,
  value v1 ->
  typing_state E 〈 v1 | frame_let e2 :: k 〉 U ->
  typing_state E 〈 open_ee e2 v1 | k 〉 U.
Proof.
  intros E v1 e2 k U Hv HT.
  destruct (typing_state_inv E v1 (frame_let e2 :: k) U HT) as [Q [T [Hty Hctx]]].
  destruct (state_let E Q v1 T e2 k U Hty Hctx) as [Q' [L [T1 [T2 [Htyv [Hbody Hctx']]]]]].
  assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ _ Htyv)).
  assert (Hvbot : typing E (qua_base bot) v1 T1).
  { eapply typing_value_effect; [exact Htyv|exact Hv|exact HwfE|apply wf_qua_base]. }
  pick fresh x for (L \u (dom E \u fv_ee e2)).
  assert (HxL : x `notin` L) by (apply notin_union_1 in Fr; exact Fr).
  assert (HxE : x `notin` fv_ee e2).
  { pose proof Fr as H1; apply notin_union_2 in H1; apply notin_union_2 in H1; exact H1. }
  assert (Hbodyx := Hbody x HxL).
  assert (Hsubst : typing E Q' (subst_ee x v1 (open_ee e2 x)) T2).
  { eapply (typing_subst_ee_gen (x ~ bind_typ T1 ++ E) Q' (open_ee e2 x) T2 Hbodyx
              (@nil (atom*binding)) x T1 E v1 eq_refl
              (value_closed_ee v1 Hv) (value_closed_te v1 Hv)
              (value_closed_qe v1 Hv) HwfE Hvbot). }
  rewrite (subst_ee_open_ee_self e2 x v1 (value_closed_ee v1 Hv)) in Hsubst.
  rewrite (subst_ee_id e2 x v1 HxE) in Hsubst.
  eapply typing_step; eassumption.
Qed.

Lemma pres_case_inl : forall E P v e2 e3 k U,
  value v ->
  typing_state E 〈 exp_inl P v | frame_case e2 e3 :: k 〉 U ->
  typing_state E 〈 open_ee e2 v | k 〉 U.
Proof.
  intros E P v e2 e3 k U Hv HT.
  destruct (typing_state_inv E (exp_inl P v) (frame_case e2 e3 :: k) U HT)
    as [Q [T [Hty Hctx]]].
  destruct (state_case E Q (exp_inl P v) T e2 e3 k U Hty Hctx)
    as [Q' [L [Pc [T1 [T2 [T0 [HP [Htyinl [Hb2 [Hb3 Hctx']]]]]]]]]].
  destruct (typing_inl_core_wf E Q' (exp_inl P v) (qtyp_qtyp Pc (typ_sum T1 T2)) Htyinl P v eq_refl)
    as [T1c [T2c [Pq [A [B [Htyv [HT2c [Hsq Hdis]]]]]]]].
  destruct Hdis as [[HeqT [HsA HsB]] | Htop].
  - inversion HeqT; subst.
    assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ _ Htyv)).
    assert (HvT1 : typing E Q' v A) by (eapply typing_sub; [exact Htyv|exact HsA]).
    assert (Hvbot : typing E (qua_base bot) v A).
    { eapply typing_value_effect; [exact HvT1|exact Hv|exact HwfE|apply wf_qua_base]. }
    pick fresh x for (L \u (dom E \u fv_ee e2)).
    assert (HxL : x `notin` L) by (apply notin_union_1 in Fr; exact Fr).
    assert (HxE : x `notin` fv_ee e2).
    { pose proof Fr as H1; apply notin_union_2 in H1; apply notin_union_2 in H1; exact H1. }
    assert (Hbodyx := Hb2 x HxL).
    assert (Hsubst : typing E Q' (subst_ee x v (open_ee e2 x)) T0).
    { eapply (typing_subst_ee_gen (x ~ bind_typ A ++ E) Q' (open_ee e2 x) T0 Hbodyx
                (@nil (atom*binding)) x A E v eq_refl
                (value_closed_ee v Hv) (value_closed_te v Hv)
                (value_closed_qe v Hv) HwfE Hvbot). }
    rewrite (subst_ee_open_ee_self e2 x v (value_closed_ee v Hv)) in Hsubst.
    rewrite (subst_ee_id e2 x v HxE) in Hsubst.
    eapply typing_step; eassumption.
  - inversion Htop.
Qed.

Lemma pres_case_inr : forall E P v e2 e3 k U,
  value v ->
  typing_state E 〈 exp_inr P v | frame_case e2 e3 :: k 〉 U ->
  typing_state E 〈 open_ee e3 v | k 〉 U.
Proof.
  intros E P v e2 e3 k U Hv HT.
  destruct (typing_state_inv E (exp_inr P v) (frame_case e2 e3 :: k) U HT)
    as [Q [T [Hty Hctx]]].
  destruct (state_case E Q (exp_inr P v) T e2 e3 k U Hty Hctx)
    as [Q' [L [Pc [T1 [T2 [T0 [HP [Htyinr [Hb2 [Hb3 Hctx']]]]]]]]]].
  destruct (typing_inr_core_wf E Q' (exp_inr P v) (qtyp_qtyp Pc (typ_sum T1 T2)) Htyinr P v eq_refl)
    as [T1c [T2c [Pq [A [B [Htyv [HT1c [Hsq Hdis]]]]]]]].
  destruct Hdis as [[HeqT [HsA HsB]] | Htop].
  - inversion HeqT; subst.
    assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ _ Htyv)).
    assert (HvT2 : typing E Q' v B) by (eapply typing_sub; [exact Htyv|exact HsB]).
    assert (Hvbot : typing E (qua_base bot) v B).
    { eapply typing_value_effect; [exact HvT2|exact Hv|exact HwfE|apply wf_qua_base]. }
    pick fresh x for (L \u (dom E \u fv_ee e3)).
    assert (HxL : x `notin` L) by (apply notin_union_1 in Fr; exact Fr).
    assert (HxE : x `notin` fv_ee e3).
    { pose proof Fr as H1; apply notin_union_2 in H1; apply notin_union_2 in H1; exact H1. }
    assert (Hbodyx := Hb3 x HxL).
    assert (Hsubst : typing E Q' (subst_ee x v (open_ee e3 x)) T0).
    { eapply (typing_subst_ee_gen (x ~ bind_typ B ++ E) Q' (open_ee e3 x) T0 Hbodyx
                (@nil (atom*binding)) x B E v eq_refl
                (value_closed_ee v Hv) (value_closed_te v Hv)
                (value_closed_qe v Hv) HwfE Hvbot). }
    rewrite (subst_ee_open_ee_self e3 x v (value_closed_ee v Hv)) in Hsubst.
    rewrite (subst_ee_id e3 x v HxE) in Hsubst.
    eapply typing_step; eassumption.
  - inversion Htop.
Qed.

Lemma pres_first_pair : forall E P v1 v2 k U,
  value v1 -> value v2 ->
  typing_state E 〈 exp_pair P v1 v2 | frame_first :: k 〉 U ->
  typing_state E 〈 v1 | k 〉 U.
Proof.
  intros E P v1 v2 k U Hv1 Hv2 HT.
  destruct (typing_state_inv E (exp_pair P v1 v2) (frame_first :: k) U HT) as [Q [T [Hty Hctx]]].
  destruct (state_first E Q (exp_pair P v1 v2) T k U Hty Hctx)
    as [Q' [Pc [T1 [T2 [HP [HT2 [Htypair Hctx']]]]]]].
  destruct (typing_pair_core_wf E Q' (exp_pair P v1 v2) (qtyp_qtyp Pc (typ_pair T1 T2)) Htypair P v1 v2 eq_refl)
    as [T1c [T2c [Pq [A [B [Htyv1 [Htyv2 [Hsq Hdis]]]]]]]].
  destruct Hdis as [[HeqT [HsA HsB]] | Htop].
  - inversion HeqT; subst.
    assert (Hty1 : typing E Q' v1 A) by (eapply typing_sub; [exact Htyv1|exact HsA]).
    eapply typing_step; eassumption.
  - inversion Htop.
Qed.

Lemma pres_second_pair : forall E P v1 v2 k U,
  value v1 -> value v2 ->
  typing_state E 〈 exp_pair P v1 v2 | frame_second :: k 〉 U ->
  typing_state E 〈 v2 | k 〉 U.
Proof.
  intros E P v1 v2 k U Hv1 Hv2 HT.
  destruct (typing_state_inv E (exp_pair P v1 v2) (frame_second :: k) U HT) as [Q [T [Hty Hctx]]].
  destruct (state_second E Q (exp_pair P v1 v2) T k U Hty Hctx)
    as [Q' [Pc [T1 [T2 [HP [HT1 [Htypair Hctx']]]]]]].
  destruct (typing_pair_core_wf E Q' (exp_pair P v1 v2) (qtyp_qtyp Pc (typ_pair T1 T2)) Htypair P v1 v2 eq_refl)
    as [T1c [T2c [Pq [A [B [Htyv1 [Htyv2 [Hsq Hdis]]]]]]]].
  destruct Hdis as [[HeqT [HsA HsB]] | Htop].
  - inversion HeqT; subst.
    assert (Hty2 : typing E Q' v2 B) by (eapply typing_sub; [exact Htyv2|exact HsB]).
    eapply typing_step; eassumption.
  - inversion Htop.
Qed.

Lemma pres_make_inl : forall E P v k U,
  value v ->
  typing_state E 〈 v | frame_inl P :: k 〉 U ->
  typing_state E 〈 exp_inl P v | k 〉 U.
Proof.
  intros E P v k U Hv HT.
  destruct (typing_state_inv E v (frame_inl P :: k) U HT) as [Q [T [Hty Hctx]]].
  destruct (state_inl E Q v T P k U Hty Hctx) as [Q' [T1 [T2 [Htyv Hctx']]]].
  destruct (wf_qtyp_qtyp_inv _ _ _ (typing_ctx_wf_source _ _ _ _ _ Hctx')) as [HP HTsum].
  destruct (wf_typ_sum_inv _ _ _ HTsum) as [_ HT2].
  eapply typing_step.
  - eapply typing_inl; eassumption.
  - exact Hctx'.
Qed.

Lemma pres_make_inr : forall E P v k U,
  value v ->
  typing_state E 〈 v | frame_inr P :: k 〉 U ->
  typing_state E 〈 exp_inr P v | k 〉 U.
Proof.
  intros E P v k U Hv HT.
  destruct (typing_state_inv E v (frame_inr P :: k) U HT) as [Q [T [Hty Hctx]]].
  destruct (state_inr E Q v T P k U Hty Hctx) as [Q' [T1 [T2 [Htyv Hctx']]]].
  destruct (wf_qtyp_qtyp_inv _ _ _ (typing_ctx_wf_source _ _ _ _ _ Hctx')) as [HP HTsum].
  destruct (wf_typ_sum_inv _ _ _ HTsum) as [HT1 _].
  eapply typing_step.
  - eapply typing_inr; eassumption.
  - exact Hctx'.
Qed.

Lemma pres_make_pair : forall E P v1 v2 k U,
  value v1 -> value v2 ->
  typing_state E 〈 v2 | frame_pair_2 P v1 :: k 〉 U ->
  typing_state E 〈 exp_pair P v1 v2 | k 〉 U.
Proof.
  intros E P v1 v2 k U Hv1 Hv2 HT.
  destruct (typing_state_inv E v2 (frame_pair_2 P v1 :: k) U HT) as [Q [T [Hty Hctx]]].
  destruct (state_pair_2 E Q v2 T P v1 k U Hty Hctx)
    as [Q' [T1 [T2 [HP [Hv1' [Htyv1 [Htyv2 Hctx']]]]]]].
  eapply typing_step.
  - eapply typing_pair; eassumption.
  - exact Hctx'.
Qed.


Lemma pres_check : forall E e P k U,
  typing_state E 〈 e | frame_check P :: k 〉 U ->
  typing_state E 〈 e | k 〉 U.
Proof.
  intros E e P k U HT.
  destruct (typing_state_inv E e (frame_check P :: k) U HT) as [Q [T [Hty Hctx]]].
  destruct (state_check E Q e T P k U Hty Hctx) as [Q' [Pc [T0 [HR [HtyM Hctx']]]]].
  assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ _ HtyM)).
  assert (HP : wf_qua E Pc) by (destruct (wf_qtyp_qtyp_inv _ _ _ (typing_ctx_wf_source _ _ _ _ _ Hctx')) as [HP _]; exact HP).
  assert (Hsub : subqual E (qua_meet Pc P) Pc).
  { eapply subqual_meet_eliml; [eapply subqual_refl; eassumption|exact HR]. }
  assert (Hsubq : subqtype E (qtyp_qtyp (qua_meet Pc P) T0) (qtyp_qtyp Pc T0)).
  { eapply sub_qtyp_qtyp; [exact Hsub|].
    destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ HtyM)) as [_ HT0].
    eapply sub_refl; [exact HwfE|exact HT0]. }
  assert (HtyP : typing E Q' e (qtyp_qtyp Pc T0)) by (eapply typing_sub; eassumption).
  eapply typing_step; eassumption.
Qed.


Lemma pres_upqual_int : forall E Q z P k U,
  typing_state E 〈 exp_int Q z | frame_upqual P :: k 〉 U ->
  typing_state E 〈 exp_int P z | k 〉 U.
Proof.
  intros E Q z P k U HT.
  destruct (typing_state_inv E (exp_int Q z) (frame_upqual P :: k) U HT)
    as [Qs [T [Hty Hctx]]].
  destruct (state_upqual E Qs (exp_int Q z) T P k U Hty Hctx)
    as [Q' [T0 [HtyP Hctx']]].
  destruct (typing_int_core_wf E Q' (exp_int Q z) (qtyp_qtyp P T0) HtyP Q z eq_refl)
    as [Pq [HQ [Hsq Hdis]]].
  assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ _ HtyP)).
  assert (HQ' : wf_qua E Q') by (apply (typing_wf_qua _ _ _ _ HtyP)).
  assert (HP : wf_qua E P) by (destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ HtyP)) as [HP _]; exact HP).
  assert (Hcore : typing E (qua_base bot) (exp_int P z) (qtyp_qtyp P typ_int)).
  { eapply typing_int; eassumption. }
  assert (Hfinal0 : typing E Q' (exp_int P z) (qtyp_qtyp P T0)).
  { destruct Hdis as [Heq | Heq].
    - inversion Heq; subst.
      eapply typing_subqual; [exact Hcore|].
      eapply subqual_bot; assumption.
    - inversion Heq; subst.
      assert (Htop : subqtype E (qtyp_qtyp Pq typ_int) (qtyp_qtyp Pq typ_top)).
      { eapply sub_qtyp_qtyp.
        - eapply subqual_refl; eassumption.
        - eapply sub_top; [exact HwfE|apply wf_typ_int]. }
      eapply typing_subqual.
      + eapply typing_sub; [exact Hcore|exact Htop].
      + eapply subqual_bot; assumption. }
  eapply typing_step; eassumption.
Qed.


Lemma pres_upqual_abs : forall E Qa V b P k U,
  typing_state E 〈 exp_abs Qa V b | frame_upqual P :: k 〉 U ->
  typing_state E 〈 exp_abs P V b | k 〉 U.
Proof.
  intros E Qa V b P k U HT.
  destruct (typing_state_inv E (exp_abs Qa V b) (frame_upqual P :: k) U HT)
    as [Qs [T [Hty Hctx]]].
  destruct (state_upqual E Qs (exp_abs Qa V b) T P k U Hty Hctx)
    as [Q' [T0 [HtyP Hctx']]].
  destruct (typing_abs_core_wf E Q' (exp_abs Qa V b) (qtyp_qtyp P T0) HtyP Qa V b eq_refl)
    as [Tbody [L [Pq [A [B [Hbody [Hwf [Hsq Hdis]]]]]]]].
  assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ _ HtyP)).
  assert (HQ' : wf_qua E Q') by (apply (typing_wf_qua _ _ _ _ HtyP)).
  assert (HP : wf_qua E P) by (destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ HtyP)) as [HP _]; exact HP).
  assert (HsqP : subqual E Qa P).
  { destruct Hdis as [[Heq _] | Heq]; inversion Heq; subst; exact Hsq. }
  assert (HbodyP : forall x, x `notin` L -> typing (x ~ bind_typ V ++ E) P (open_ee b x) Tbody).
  { intros x Hx.
    assert (Hsqx : subqual (x ~ bind_typ V ++ E) Qa P).
    { eapply subqual_extends; [exact HsqP|apply extends_cons|].
      apply (typing_wf_env _ _ _ _ (Hbody x Hx)). }
    eapply typing_subqual; [exact (Hbody x Hx)|exact Hsqx]. }
  assert (Hcore : typing E (qua_base bot) (exp_abs P V b) (qtyp_qtyp P (typ_arrow V Tbody))).
  { eapply typing_abs with (L := L). exact HbodyP. }
  assert (Hfinal : typing E Q' (exp_abs P V b) (qtyp_qtyp P T0)).
  { destruct Hdis as [[Heq [HsA HsB]] | Heq].
    - inversion Heq; subst.
      assert (Hsubq : subqtype E (qtyp_qtyp Pq (typ_arrow V Tbody)) (qtyp_qtyp Pq (typ_arrow A B))).
      { eapply sub_qtyp_qtyp.
        - eapply subqual_refl; eassumption.
        - eapply sub_arrow; eassumption. }
      eapply typing_subqual.
      + eapply typing_sub; [exact Hcore|exact Hsubq].
      + eapply subqual_bot; assumption.
    - inversion Heq; subst.
      assert (Htop : subqtype E (qtyp_qtyp Pq (typ_arrow V Tbody)) (qtyp_qtyp Pq typ_top)).
      { eapply sub_qtyp_qtyp.
        - eapply subqual_refl; eassumption.
        - eapply sub_top; [exact HwfE|exact Hwf]. }
      eapply typing_subqual.
      + eapply typing_sub; [exact Hcore|exact Htop].
      + eapply subqual_bot; assumption. }
  eapply typing_step; eassumption.
Qed.


Lemma pres_upqual_tabs : forall E Qa V b P k U,
  typing_state E 〈 exp_tabs Qa V b | frame_upqual P :: k 〉 U ->
  typing_state E 〈 exp_tabs P V b | k 〉 U.
Proof.
  intros E Qa V b P k U HT.
  destruct (typing_state_inv E (exp_tabs Qa V b) (frame_upqual P :: k) U HT)
    as [Qs [T [Hty Hctx]]].
  destruct (state_upqual E Qs (exp_tabs Qa V b) T P k U Hty Hctx)
    as [Q' [T0 [HtyP Hctx']]].
  destruct (typing_tabs_core_wf E Q' (exp_tabs Qa V b) (qtyp_qtyp P T0) HtyP Qa V b eq_refl)
    as [Tbody [L [Pq [A [B [L2 [Hbody [Hwf [Hsq Hdis]]]]]]]]].
  assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ _ HtyP)).
  assert (HQ' : wf_qua E Q') by (apply (typing_wf_qua _ _ _ _ HtyP)).
  assert (HP : wf_qua E P) by (destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ HtyP)) as [HP _]; exact HP).
  assert (HsqP : subqual E Qa P).
  { destruct Hdis as [[Heq _] | Heq]; inversion Heq; subst; exact Hsq. }
  assert (HbodyP : forall X, X `notin` L ->
            typing (X ~ bind_sub V ++ E) P (open_te b X) (open_tqt Tbody X)).
  { intros X HX.
    assert (Hsqx : subqual (X ~ bind_sub V ++ E) Qa P).
    { eapply subqual_extends; [exact HsqP|apply extends_cons|].
      apply (typing_wf_env _ _ _ _ (Hbody X HX)). }
    eapply typing_subqual; [exact (Hbody X HX)|exact Hsqx]. }
  assert (Hcore : typing E (qua_base bot) (exp_tabs P V b) (qtyp_qtyp P (typ_all V Tbody))).
  { eapply typing_tabs with (L := L). exact HbodyP. }
  assert (Hfinal : typing E Q' (exp_tabs P V b) (qtyp_qtyp P T0)).
  { destruct Hdis as [[Heq [HsA HsB]] | Heq].
    - inversion Heq; subst.
      assert (Hsubq : subqtype E (qtyp_qtyp Pq (typ_all V Tbody)) (qtyp_qtyp Pq (typ_all A B))).
      { eapply sub_qtyp_qtyp.
        - eapply subqual_refl; eassumption.
        - eapply sub_all with (L := L2); eassumption. }
      eapply typing_subqual.
      + eapply typing_sub; [exact Hcore|exact Hsubq].
      + eapply subqual_bot; assumption.
    - inversion Heq; subst.
      assert (Htop : subqtype E (qtyp_qtyp Pq (typ_all V Tbody)) (qtyp_qtyp Pq typ_top)).
      { eapply sub_qtyp_qtyp.
        - eapply subqual_refl; eassumption.
        - eapply sub_top; [exact HwfE|exact Hwf]. }
      eapply typing_subqual.
      + eapply typing_sub; [exact Hcore|exact Htop].
      + eapply subqual_bot; assumption. }
  eapply typing_step; eassumption.
Qed.

Lemma pres_upqual_qabs : forall E Qa Qb b P k U,
  typing_state E 〈 exp_qabs Qa Qb b | frame_upqual P :: k 〉 U ->
  typing_state E 〈 exp_qabs P Qb b | k 〉 U.
Proof.
  intros E Qa Qb b P k U HT.
  destruct (typing_state_inv E (exp_qabs Qa Qb b) (frame_upqual P :: k) U HT)
    as [Qs [T [Hty Hctx]]].
  destruct (state_upqual E Qs (exp_qabs Qa Qb b) T P k U Hty Hctx)
    as [Q' [T0 [HtyP Hctx']]].
  destruct (typing_qabs_core_wf E Q' (exp_qabs Qa Qb b) (qtyp_qtyp P T0) HtyP Qa Qb b eq_refl)
    as [Tbody [L [Pq [A [B [L2 [Hbody [Hwf [Hsq Hdis]]]]]]]]].
  assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ _ HtyP)).
  assert (HQ' : wf_qua E Q') by (apply (typing_wf_qua _ _ _ _ HtyP)).
  assert (HP : wf_qua E P) by (destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ HtyP)) as [HP _]; exact HP).
  assert (HsqP : subqual E Qa P).
  { destruct Hdis as [[Heq _] | Heq]; inversion Heq; subst; exact Hsq. }
  assert (HbodyP : forall X, X `notin` L ->
            typing (X ~ bind_qua Qb ++ E) P (open_qe b X) (open_qqt Tbody X)).
  { intros X HX.
    assert (Hsqx : subqual (X ~ bind_qua Qb ++ E) Qa P).
    { eapply subqual_extends; [exact HsqP|apply extends_cons|].
      apply (typing_wf_env _ _ _ _ (Hbody X HX)). }
    eapply typing_subqual; [exact (Hbody X HX)|exact Hsqx]. }
  assert (Hcore : typing E (qua_base bot) (exp_qabs P Qb b) (qtyp_qtyp P (typ_qall Qb Tbody))).
  { eapply typing_qabs with (L := L); [exact HP|exact HbodyP]. }
  assert (Hfinal : typing E Q' (exp_qabs P Qb b) (qtyp_qtyp P T0)).
  { destruct Hdis as [[Heq [HsA HsB]] | Heq].
    - inversion Heq; subst.
      assert (Hsubq : subqtype E (qtyp_qtyp Pq (typ_qall Qb Tbody)) (qtyp_qtyp Pq (typ_qall A B))).
      { eapply sub_qtyp_qtyp.
        - eapply subqual_refl; eassumption.
        - eapply sub_qall with (L := L2); eassumption. }
      eapply typing_subqual.
      + eapply typing_sub; [exact Hcore|exact Hsubq].
      + eapply subqual_bot; assumption.
    - inversion Heq; subst.
      assert (Htop : subqtype E (qtyp_qtyp Pq (typ_qall Qb Tbody)) (qtyp_qtyp Pq typ_top)).
      { eapply sub_qtyp_qtyp.
        - eapply subqual_refl; eassumption.
        - eapply sub_top; [exact HwfE|exact Hwf]. }
      eapply typing_subqual.
      + eapply typing_sub; [exact Hcore|exact Htop].
      + eapply subqual_bot; assumption. }
  eapply typing_step; eassumption.
Qed.

Lemma pres_upqual_inl : forall E Qa b P k U,
  typing_state E 〈 exp_inl Qa b | frame_upqual P :: k 〉 U ->
  typing_state E 〈 exp_inl P b | k 〉 U.
Proof.
  intros E Qa b P k U HT.
  destruct (typing_state_inv E (exp_inl Qa b) (frame_upqual P :: k) U HT)
    as [Qs [T [Hty Hctx]]].
  destruct (state_upqual E Qs (exp_inl Qa b) T P k U Hty Hctx)
    as [Q' [T0 [HtyP Hctx']]].
  destruct (typing_inl_core_wf E Q' (exp_inl Qa b) (qtyp_qtyp P T0) HtyP Qa b eq_refl)
    as [T1 [T2 [Pq [A [B [Hbody [HT2 [Hsq Hdis]]]]]]]].
  assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ _ HtyP)).
  assert (HsqP : subqual E Qa P).
  { destruct Hdis as [[Heq _] | Heq]; inversion Heq; subst; exact Hsq. }
  assert (HP : wf_qua E P) by (destruct (subqual_wf _ _ _ HsqP) as [_ [_ HP]]; exact HP).
  assert (Hcore : typing E Q' (exp_inl P b) (qtyp_qtyp P (typ_sum T1 T2))).
  { eapply typing_inl; eassumption. }
  assert (Hfinal : typing E Q' (exp_inl P b) (qtyp_qtyp P T0)).
  { destruct Hdis as [[Heq [HsA HsB]] | Heq].
    - inversion Heq; subst.
      assert (Hsubq : subqtype E (qtyp_qtyp Pq (typ_sum T1 T2)) (qtyp_qtyp Pq (typ_sum A B))).
      { eapply sub_qtyp_qtyp.
        - eapply subqual_refl; eassumption.
        - eapply sub_sum; eassumption. }
      eapply typing_sub; [exact Hcore|exact Hsubq].
    - inversion Heq; subst.
      assert (Hsubq : subqtype E (qtyp_qtyp Pq (typ_sum T1 T2)) (qtyp_qtyp Pq typ_top)).
      { eapply sub_qtyp_qtyp.
        - eapply subqual_refl; eassumption.
        - eapply sub_top.
          + exact HwfE.
          + destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ Hcore)) as [_ HTp].
            exact HTp. }
      eapply typing_sub; [exact Hcore|exact Hsubq]. }
  eapply typing_step; eassumption.
Qed.

Lemma pres_upqual_inr : forall E Qa b P k U,
  typing_state E 〈 exp_inr Qa b | frame_upqual P :: k 〉 U ->
  typing_state E 〈 exp_inr P b | k 〉 U.
Proof.
  intros E Qa b P k U HT.
  destruct (typing_state_inv E (exp_inr Qa b) (frame_upqual P :: k) U HT)
    as [Qs [T [Hty Hctx]]].
  destruct (state_upqual E Qs (exp_inr Qa b) T P k U Hty Hctx)
    as [Q' [T0 [HtyP Hctx']]].
  destruct (typing_inr_core_wf E Q' (exp_inr Qa b) (qtyp_qtyp P T0) HtyP Qa b eq_refl)
    as [T1 [T2 [Pq [A [B [Hbody [HT1 [Hsq Hdis]]]]]]]].
  assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ _ HtyP)).
  assert (HsqP : subqual E Qa P).
  { destruct Hdis as [[Heq _] | Heq]; inversion Heq; subst; exact Hsq. }
  assert (HP : wf_qua E P) by (destruct (subqual_wf _ _ _ HsqP) as [_ [_ HP]]; exact HP).
  assert (Hcore : typing E Q' (exp_inr P b) (qtyp_qtyp P (typ_sum T1 T2))).
  { eapply typing_inr; eassumption. }
  assert (Hfinal : typing E Q' (exp_inr P b) (qtyp_qtyp P T0)).
  { destruct Hdis as [[Heq [HsA HsB]] | Heq].
    - inversion Heq; subst.
      assert (Hsubq : subqtype E (qtyp_qtyp Pq (typ_sum T1 T2)) (qtyp_qtyp Pq (typ_sum A B))).
      { eapply sub_qtyp_qtyp.
        - eapply subqual_refl; eassumption.
        - eapply sub_sum; eassumption. }
      eapply typing_sub; [exact Hcore|exact Hsubq].
    - inversion Heq; subst.
      assert (Hsubq : subqtype E (qtyp_qtyp Pq (typ_sum T1 T2)) (qtyp_qtyp Pq typ_top)).
      { eapply sub_qtyp_qtyp.
        - eapply subqual_refl; eassumption.
        - eapply sub_top.
          + exact HwfE.
          + destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ Hcore)) as [_ HTp].
            exact HTp. }
      eapply typing_sub; [exact Hcore|exact Hsubq]. }
  eapply typing_step; eassumption.
Qed.

Lemma pres_upqual_pair : forall E Qa b1 b2 P k U,
  typing_state E 〈 exp_pair Qa b1 b2 | frame_upqual P :: k 〉 U ->
  typing_state E 〈 exp_pair P b1 b2 | k 〉 U.
Proof.
  intros E Qa b1 b2 P k U HT.
  destruct (typing_state_inv E (exp_pair Qa b1 b2) (frame_upqual P :: k) U HT)
    as [Qs [T [Hty Hctx]]].
  destruct (state_upqual E Qs (exp_pair Qa b1 b2) T P k U Hty Hctx)
    as [Q' [T0 [HtyP Hctx']]].
  destruct (typing_pair_core_wf E Q' (exp_pair Qa b1 b2) (qtyp_qtyp P T0) HtyP Qa b1 b2 eq_refl)
    as [T1 [T2 [Pq [A [B [Hbody1 [Hbody2 [Hsq Hdis]]]]]]]].
  assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ _ HtyP)).
  assert (HsqP : subqual E Qa P).
  { destruct Hdis as [[Heq _] | Heq]; inversion Heq; subst; exact Hsq. }
  assert (HP : wf_qua E P) by (destruct (subqual_wf _ _ _ HsqP) as [_ [_ HP]]; exact HP).
  assert (Hcore : typing E Q' (exp_pair P b1 b2) (qtyp_qtyp P (typ_pair T1 T2))).
  { eapply typing_pair; eassumption. }
  assert (Hfinal : typing E Q' (exp_pair P b1 b2) (qtyp_qtyp P T0)).
  { destruct Hdis as [[Heq [HsA HsB]] | Heq].
    - inversion Heq; subst.
      assert (Hsubq : subqtype E (qtyp_qtyp Pq (typ_pair T1 T2)) (qtyp_qtyp Pq (typ_pair A B))).
      { eapply sub_qtyp_qtyp.
        - eapply subqual_refl; eassumption.
        - eapply sub_pair; eassumption. }
      eapply typing_sub; [exact Hcore|exact Hsubq].
    - inversion Heq; subst.
      assert (Hsubq : subqtype E (qtyp_qtyp Pq (typ_pair T1 T2)) (qtyp_qtyp Pq typ_top)).
      { eapply sub_qtyp_qtyp.
        - eapply subqual_refl; eassumption.
        - eapply sub_top.
          + exact HwfE.
          + destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ Hcore)) as [_ HTp].
            exact HTp. }
      eapply typing_sub; [exact Hcore|exact Hsubq]. }
  eapply typing_step; eassumption.
Qed.


Lemma pres_app_2 : forall E v e2 k U,
  value v ->
  typing_state E 〈 v | frame_abs e2 :: k 〉 U ->
  typing_state E 〈 e2 | frame_app v :: k 〉 U.
Proof.
  intros E v e2 k U Hv HT.
  destruct (typing_state_inv E v (frame_abs e2 :: k) U HT) as [Q [T [Hty Hctx]]].
  destruct (state_abs E Q v T e2 k U Hty Hctx) as [Q' [T1 [T2 [Htyv [Htye2 Hctx']]]]].
  eapply typing_step.
  - exact Htye2.
  - eapply typing_ctx_app; eassumption.
Qed.


Lemma pres_without : forall E Q e1 t k U,
  concretize Q = Some t ->
  typing_state E 〈 exp_without Q e1 | k 〉 U ->
  typing_state E 〈 e1 | frame_without t :: k 〉 U.
Proof.
  intros E Q e1 t k U Hconc HT.
  destruct (typing_state_inv E (exp_without Q e1) k U HT) as [Qs [T [Hty Hctx]]].
  destruct (C_without E Qs e1 Q T k U Hty Hctx)
    as [R [Q' [T' [Hty1 [HsubR Hctx']]]]].
  assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ _ Hty1)).
  assert (HR : wf_qua E R) by (destruct (subqual_wf _ _ _ HsubR) as [_ [HR _]]; exact HR).
  assert (Hneg : subqual E R (qua_base (negate t)))
    by (eapply subqual_negate_concrete; eassumption).
  assert (Hmeet : subqual E R (qua_meet (qua_base (negate t)) R)).
  { eapply subqual_meet_intro.
    - exact Hneg.
    - eapply subqual_refl; assumption. }
  assert (HtyM : typing E (qua_meet (qua_base (negate t)) R) e1 (qtyp_qtyp Q' T'))
    by (eapply typing_subqual; [exact Hty1|exact Hmeet]).
  assert (HctxM : typing_ctx E (qua_meet (qua_base (negate t)) R)
                    (frame_without t :: k) (qtyp_qtyp Q' T') U).
  { eapply typing_ctx_without. exact Hctx'. }
  eapply typing_step; eassumption.
Qed.

(* ================= ChunkPresQe.v ================= *)

Lemma pres_app_qabs : forall E P Qa e1 R t k U,
  qual R ->
  concretize P = Some t ->
  barrier_compatible k t ->
  typing_state E 〈 exp_qabs P Qa e1 | frame_qabs R :: k 〉 U ->
  typing_state E 〈 open_qe e1 R | frame_barrier t :: k 〉 U.
Proof.
  intros E P Qa e1 R t k U HqualR Hconc Hbc HT.
  destruct (typing_state_inv E (exp_qabs P Qa e1) (frame_qabs R :: k) U HT)
    as [Q [T [Hty Hctx]]].
  destruct (state_qabs E Q (exp_qabs P Qa e1) T R k U Hty Hctx)
    as [Q' [Lst [Rann [T2 [HtyQ [HsubRann [Hwfb Hctx']]]]]]].
  destruct (typing_qabs_core_wf E Q' (exp_qabs P Qa e1)
              (qtyp_qtyp Q' (typ_qall Rann T2)) HtyQ P Qa e1 eq_refl)
    as [Tbody [L0 [Pq [A [B [L2 [Hbody [Hwf [Hsq Hdis]]]]]]]]].
  destruct Hdis as [[HeqT [HsA HsB]] | Htop].
  - inversion HeqT; subst.
    assert (HwfE : wf_env E) by (apply (typing_wf_env _ _ _ _ HtyQ)).
    assert (HQa : wf_qua E Qa).
    { destruct (wf_typ_qall_inv _ _ _ Hwf) as [HQ _]. exact HQ. }
    assert (HRwf : wf_qua E R).
    { destruct (subqual_wf _ _ _ HsubRann) as [_ [HR _]]. exact HR. }
    assert (HRc : closed_qq R) by (apply (wf_qua_closed_qq _ _ HRwf)).
    assert (HsubRQ : subqual E R Qa).
    { eapply subqual_trans; [exact HsubRann | exact HsA]. }
    pick fresh X for
      (L0 \u (L2 \u (dom E \u (fv_qq Qa \u (fv_qq P \u
        (fv_qe e1 \u (fv_qqt Tbody \u (fv_qqt B \u fv_qq A)))))))).
    pose proof (notin_union_1 _ _ _ Fr) as HXL0.
    pose proof (notin_union_2 _ _ _ Fr) as F1.
    pose proof (notin_union_1 _ _ _ F1) as HXL2.
    pose proof (notin_union_2 _ _ _ F1) as F2.
    pose proof (notin_union_1 _ _ _ F2) as HXdom.
    pose proof (notin_union_2 _ _ _ F2) as F3.
    pose proof (notin_union_1 _ _ _ F3) as HXQ.
    pose proof (notin_union_2 _ _ _ F3) as F4.
    pose proof (notin_union_1 _ _ _ F4) as HXP.
    pose proof (notin_union_2 _ _ _ F4) as F5.
    pose proof (notin_union_1 _ _ _ F5) as HXe.
    pose proof (notin_union_2 _ _ _ F5) as F6.
    pose proof (notin_union_1 _ _ _ F6) as HXTb.
    pose proof (notin_union_2 _ _ _ F6) as F7.
    pose proof (notin_union_1 _ _ _ F7) as HXB.
    pose proof (notin_union_2 _ _ _ F7) as HXA.
    assert (HbodyX := Hbody X HXL0).
    assert (HbodyRaw : typing E (subst_qq X R P)
                 (subst_qe X R (open_qe e1 X))
                 (subst_qqt X R (open_qqt Tbody X))).
    { eapply (typing_subst_qe E X Qa R P (open_qe e1 X) (open_qqt Tbody X));
        eassumption. }
    assert (HbodyV := HbodyRaw).
    rewrite (subst_qe_open_qe_self e1 X R HRc) in HbodyV.
    rewrite (subst_qe_id e1 X R HXe) in HbodyV.
    rewrite (subst_qqt_open_qqt_self Tbody X R HRc) in HbodyV.
    rewrite (subst_qqt_id Tbody X R HXTb) in HbodyV.
    rewrite (subst_qq_id P X R HXP) in HbodyV.
    assert (Henv : subst_env_qb X R ((@nil (atom*binding)) ++ E) = E).
    { simpl. apply (subst_env_qb_id E X R HwfE HXdom). }
    assert (HsubqRaw : subqtype (subst_env_qb X R ((@nil (atom*binding)) ++ E))
                 (subst_qqt X R (open_qqt Tbody X))
                 (subst_qqt X R (open_qqt B X))).
    { eapply (subqtype_subst_qe (X ~ bind_qua A ++ E)
                (open_qqt Tbody X) (open_qqt B X) (HsB X HXL2)
                (@nil (atom*binding)) X A E R eq_refl).
      - exact HXA.
      - exact HRc.
      - rewrite Henv. exact HRwf.
      - rewrite Henv. exact HsubRann. }
    rewrite Henv in HsubqRaw.
    assert (Hsubq := HsubqRaw).
    rewrite (subst_qqt_open_qqt_self Tbody X R HRc) in Hsubq.
    rewrite (subst_qqt_id Tbody X R HXTb) in Hsubq.
    rewrite (subst_qqt_open_qqt_self B X R HRc) in Hsubq.
    rewrite (subst_qqt_id B X R HXB) in Hsubq.
    assert (HbodySub : typing E P (open_qe e1 R) (open_qqt B R))
      by (eapply typing_sub; [exact HbodyV | exact Hsubq]).
    assert (HPwf : wf_qua E P) by (apply (typing_wf_qua _ _ _ _ HbodyV)).
    assert (HsubPt : subqual E P (qua_base t)).
    { eapply concretize_subqual; eassumption. }
    assert (HbodyFinal : typing E (qua_base t) (open_qe e1 R) (open_qqt B R)).
    { eapply typing_subqual; [exact HbodySub | exact HsubPt]. }
    assert (HctxP : typing_ctx E P k (open_qqt B R) U).
    { eapply typing_ctx_subqual; [exact Hctx' | exact Hsq]. }
    assert (HctxBar : typing_ctx E (qua_base t) (frame_barrier t :: k) (open_qqt B R) U).
    { eapply typing_ctx_barrier; [exact HctxP | exact Hconc | apply ord_refl_B]. }
    eapply typing_step; eassumption.
  - inversion Htop.
Qed.

(* ================= ChunkPreservation.v ================= *)

Lemma preservation_aux : forall E s s' U,
  typing_state E s U -> s --> s' -> typing_state E s' U.
Proof.
  intros E s s' U HT HS.
  dependent destruction HS.
  all: try solve [ eapply pres_barrier; eauto ].
  all: try solve [ eapply pres_app_1; eauto ].
  all: try solve [ eapply pres_app_2; eauto ].
  all: try solve [ eapply pres_tapp; eauto ].
  all: try solve [ eapply pres_qapp; eauto ].
  all: try solve [ eapply pres_let; eauto ].
  all: try solve [ eapply pres_inl; eauto ].
  all: try solve [ eapply pres_inr; eauto ].
  all: try solve [ eapply pres_case; eauto ].
  all: try solve [ eapply pres_pair_1; eauto ].
  all: try solve [ eapply pres_pair_2; eauto ].
  all: try solve [ eapply pres_first; eauto ].
  all: try solve [ eapply pres_second; eauto ].
  all: try solve [ eapply pres_app_abs; eauto ].
  all: try solve [ eapply pres_app_tabs; eauto ].
  all: try solve [ eapply pres_app_qabs; eauto ].
  all: try solve [ eapply pres_let_value; eauto ].
  all: try solve [ eapply pres_case_inl; eauto ].
  all: try solve [ eapply pres_case_inr; eauto ].
  all: try solve [ eapply pres_first_pair; eauto ].
  all: try solve [ eapply pres_second_pair; eauto ].
  all: try solve [ eapply pres_make_inl; eauto ].
  all: try solve [ eapply pres_make_inr; eauto ].
  all: try solve [ eapply pres_make_pair; eauto ].
  all: try solve [ eapply pres_upqual_1; eauto ].
  all: try solve [ eapply pres_upqual_int; eauto ].
  all: try solve [ eapply pres_upqual_abs; eauto ].
  all: try solve [ eapply pres_upqual_tabs; eauto ].
  all: try solve [ eapply pres_upqual_qabs; eauto ].
  all: try solve [ eapply pres_upqual_inl; eauto ].
  all: try solve [ eapply pres_upqual_inr; eauto ].
  all: try solve [ eapply pres_upqual_pair; eauto ].
  all: try solve [ eapply pres_check_1; eauto ].
  all: try solve [ eapply pres_check; eauto ].
  all: try solve [ eapply pres_without; eauto ].
  all: try solve [ eapply pres_elim_without; eauto ].
  all: try solve [ eapply pres_do; eauto ].
  all: try solve [ eapply pres_if0_1; eauto ].
  all: try solve [ eapply pres_if0_zero; eauto ].
  all: try solve [ eapply pres_if0_nonzero; eauto ].
  all: try (eapply pres_second_pair with (E:=E) (P:=P) (v1:=v1) (v2:=v2) (k:=k) (U:=U); eauto).
Qed.

(* ================= ChunkProgress.v ================= *)

(* ---------- basic facts on the empty environment ---------- *)

Lemma typing_fvar_binds : forall E Q x T,
  typing E Q (exp_fvar x) T ->
  exists U, binds x (bind_typ U) E.
Proof.
  intros E Q x T H.
  remember (exp_fvar x) as e eqn:He.
  revert x He.
  induction H; intros x0 He; try (inversion He; discriminate).
  - inversion He; subst. eexists. exact H0.
  - apply (IHtyping x0 He).
  - apply (IHtyping x0 He).
Qed.

Lemma typing_fvar_empty_false : forall Q x T,
  typing empty Q (exp_fvar x) T -> False.
Proof.
  intros Q x T H.
  destruct (typing_fvar_binds empty Q x T H) as [U Hb].
  unfold binds in Hb. simpl in Hb. destruct Hb.
Qed.

Lemma typing_without_wf : forall E Q e P T,
  typing E Q (exp_without P e) T -> wf_qua E P.
Proof.
  intros E Q e P T H.
  remember (exp_without P e) as ee eqn:He.
  revert P e He.
  induction H; intros P0 e0 He; try (inversion He; discriminate).
  - (* typing_sub *) apply (IHtyping P0 e0 He).
  - (* typing_subqual *) apply (IHtyping P0 e0 He).
  - (* typing_without *) inversion He; subst.
    destruct (subqual_wf _ _ _ H0) as [_ [_ HPneg]].
    inversion HPneg; subst. assumption.
Qed.

Lemma typing_do_subqual : forall E Q b T,
  typing E Q (exp_do b) T -> subqual E (qua_base b) Q.
Proof.
  intros E Q b T H.
  remember (exp_do b) as e eqn:He.
  revert b He.
  induction H; intros b0 He; try (inversion He; discriminate).
  - apply (IHtyping b0 He).
  - eapply subqual_trans; [apply (IHtyping b0 He) | exact H0].
  - inversion He; subst. eapply subqual_lift_elem; [exact H | apply (reflexive)].
Qed.

(* ---------- canonical forms for values typed in the empty environment -- *)

Lemma value_arrow_abs : forall f Q T1 T2,
  value f ->
  typing empty Q f (qtyp_qtyp Q (typ_arrow T1 T2)) ->
  exists Pa V b, f = exp_abs Pa V b /\ wf_qua empty Pa /\ subqual empty Pa Q.
Proof.
  intros f Q T1 T2 Hv Hty.
  destruct f as [Pi i|u0|y|Pa V b|u1 u2|Pa V b|u1 Vv|Pa Qb b|u1 Qb|u1 u2|Pa b|Pa b|u1 u2 u3|Pa b1 b2|u1|u1|Pa u1|Pa l|u1|u1 u2|Pa u1|Pa u1|Pa u1|bb|u1 u2 u3].
  - (* int *) exfalso.
    destruct (typing_int_core_wf empty Q (exp_int Pi i) (qtyp_qtyp Q (typ_arrow T1 T2)) Hty Pi i eq_refl)
      as [Pq [HP [Hsq [Heq|Heq]]]];
      inversion Heq; discriminate.
  - (* bvar *) exfalso. inversion Hv.
  - (* fvar *) exfalso. apply (typing_fvar_empty_false Q y (qtyp_qtyp Q (typ_arrow T1 T2)) Hty).
  - (* abs *) exists Pa, V, b. split; [reflexivity|split].
    + destruct (typing_abs_core_wf empty Q (exp_abs Pa V b) (qtyp_qtyp Q (typ_arrow T1 T2)) Hty Pa V b eq_refl)
        as [Tbody [L [Pq [A [B [Hbody [Hwf [Hsq [Heq|Heq]]]]]]]]].
      * destruct Heq as [HeqT _]. inversion HeqT; subst.
        destruct (subqual_wf _ _ _ Hsq) as [_ [HPa _]]. exact HPa.
      * inversion Heq.
    + destruct (typing_abs_core_wf empty Q (exp_abs Pa V b) (qtyp_qtyp Q (typ_arrow T1 T2)) Hty Pa V b eq_refl)
        as [Tbody [L [Pq [A [B [Hbody [Hwf [Hsq [Heq|Heq]]]]]]]]].
      * destruct Heq as [HeqT _]. inversion HeqT; subst. exact Hsq.
      * inversion Heq.
  - (* app *) exfalso. inversion Hv.
  - (* tabs *) exfalso.
    destruct (typing_tabs_core_wf empty Q (exp_tabs Pa V b) (qtyp_qtyp Q (typ_arrow T1 T2)) Hty Pa V b eq_refl)
      as [Tbody [L [Pq [A [B [L2 [Hbody [Hwf [Hsq [Heq|Heq]]]]]]]]]].
      * destruct Heq as [HeqT _]; inversion HeqT; discriminate.
      * inversion Heq.
  - (* tapp *) exfalso. inversion Hv.
  - (* qabs *) exfalso.
    destruct (typing_qabs_core_wf empty Q (exp_qabs Pa Qb b) (qtyp_qtyp Q (typ_arrow T1 T2)) Hty Pa Qb b eq_refl)
      as [Tbody [L [Pq [A [B [L2 [Hbody [Hwf [Hsq [Heq|Heq]]]]]]]]]].
      * destruct Heq as [HeqT _]; inversion HeqT; discriminate.
      * inversion Heq.
  - (* qapp *) exfalso. inversion Hv.
  - (* let *) exfalso. inversion Hv.
  - (* inl *) exfalso.
    destruct (typing_inl_core_wf empty Q (exp_inl Pa b) (qtyp_qtyp Q (typ_arrow T1 T2)) Hty Pa b eq_refl)
      as [T1' [T2' [Pq [A [B [Hbody [HT2 [Hsq [Heq|Heq]]]]]]]]].
      * destruct Heq as [HeqT _]; inversion HeqT; discriminate.
      * inversion Heq.
  - (* inr *) exfalso.
    destruct (typing_inr_core_wf empty Q (exp_inr Pa b) (qtyp_qtyp Q (typ_arrow T1 T2)) Hty Pa b eq_refl)
      as [T1' [T2' [Pq [A [B [Hbody [HT1 [Hsq [Heq|Heq]]]]]]]]].
      * destruct Heq as [HeqT _]; inversion HeqT; discriminate.
      * inversion Heq.
  - (* case *) exfalso. inversion Hv.
  - (* pair *) exfalso.
    destruct (typing_pair_core_wf empty Q (exp_pair Pa b1 b2) (qtyp_qtyp Q (typ_arrow T1 T2)) Hty Pa b1 b2 eq_refl)
      as [T1' [T2' [Pq [A [B [Hb1 [Hb2 [Hsq [Heq|Heq]]]]]]]]].
      * destruct Heq as [HeqT _]; inversion HeqT; discriminate.
      * inversion Heq.
  - (* first *) exfalso. inversion Hv.
  - (* second *) exfalso. inversion Hv.
  - (* ref *) exfalso. inversion Hv.
  - (* ref_label *) exfalso. inversion Hv.
  - (* deref *) exfalso. inversion Hv.
  - (* set_ref *) exfalso. inversion Hv.
  - (* upqual *) exfalso. inversion Hv.
  - (* check *) exfalso. inversion Hv.
  - (* without *) exfalso. inversion Hv.
  - (* do *) exfalso. inversion Hv.
  - (* if0 *) exfalso. inversion Hv.
Qed.

(* ---------- value annotation and shape facts ---------- *)

Lemma int_typing_shape : forall Q P T Pi i,
  typing empty Q (exp_int Pi i) (qtyp_qtyp P T) -> T = typ_int \/ T = typ_top.
Proof.
  intros Q P T Pi i H.
  destruct (typing_int_core_wf empty Q (exp_int Pi i) (qtyp_qtyp P T) H Pi i eq_refl)
    as [Pq [Hwf [Hsq [Heq|Heq]]]].
  - inversion Heq; subst. left. reflexivity.
  - inversion Heq; subst. right. reflexivity.
Qed.

Lemma abs_typing_shape : forall Q P T Pa V b,
  typing empty Q (exp_abs Pa V b) (qtyp_qtyp P T) ->
  (exists A B, T = typ_arrow A B) \/ T = typ_top.
Proof.
  intros Q P T Pa V b H.
  destruct (typing_abs_core_wf empty Q (exp_abs Pa V b) (qtyp_qtyp P T) H Pa V b eq_refl)
    as [Tbody [L [Pq [A [B [Hbody [Hwf [Hsq Hdis]]]]]]]].
  destruct Hdis as [[Heq _]|Heq].
  - inversion Heq; subst. left. eauto.
  - inversion Heq; subst. right. reflexivity.
Qed.

Lemma tabs_typing_shape : forall Q P T Pa V b,
  typing empty Q (exp_tabs Pa V b) (qtyp_qtyp P T) ->
  (exists A B, T = typ_all A B) \/ T = typ_top.
Proof.
  intros Q P T Pa V b H.
  destruct (typing_tabs_core_wf empty Q (exp_tabs Pa V b) (qtyp_qtyp P T) H Pa V b eq_refl)
    as [Tbody [L [Pq [A [B [L2 [Hbody [Hwf [Hsq Hdis]]]]]]]]].
  destruct Hdis as [[Heq _]|Heq].
  - inversion Heq; subst. left. eauto.
  - inversion Heq; subst. right. reflexivity.
Qed.

Lemma qabs_typing_shape : forall Q P T Pa Qb b,
  typing empty Q (exp_qabs Pa Qb b) (qtyp_qtyp P T) ->
  (exists A B, T = typ_qall A B) \/ T = typ_top.
Proof.
  intros Q P T Pa Qb b H.
  destruct (typing_qabs_core_wf empty Q (exp_qabs Pa Qb b) (qtyp_qtyp P T) H Pa Qb b eq_refl)
    as [Tbody [L [Pq [A [B [L2 [Hbody [Hwf [Hsq Hdis]]]]]]]]].
  destruct Hdis as [[Heq _]|Heq].
  - inversion Heq; subst. left. eauto.
  - inversion Heq; subst. right. reflexivity.
Qed.

Lemma int_ann : forall Q P T Pi i,
  typing empty Q (exp_int Pi i) (qtyp_qtyp P T) ->
  wf_qua empty Pi /\ subqual empty Pi P.
Proof.
  intros Q P T Pi i H.
  destruct (typing_int_core_wf empty Q (exp_int Pi i) (qtyp_qtyp P T) H Pi i eq_refl)
    as [Pq [Hwf [Hsq [Heq|Heq]]]].
  all: inversion Heq; subst; split; assumption.
Qed.

Lemma abs_ann : forall Q P T Pa V b,
  typing empty Q (exp_abs Pa V b) (qtyp_qtyp P T) ->
  wf_qua empty Pa /\ subqual empty Pa P.
Proof.
  intros Q P T Pa V b H.
  destruct (typing_abs_core_wf empty Q (exp_abs Pa V b) (qtyp_qtyp P T) H Pa V b eq_refl)
    as [Tbody [L [Pq [A [B [Hbody [Hwf [Hsq Hdis]]]]]]]].
  destruct Hdis as [[Heq _]|Heq]; inversion Heq; subst; split; [|exact Hsq| |exact Hsq];
    destruct (subqual_wf _ _ _ Hsq) as [_ [HPa _]]; exact HPa.
Qed.

Lemma tabs_ann : forall Q P T Pa V b,
  typing empty Q (exp_tabs Pa V b) (qtyp_qtyp P T) ->
  wf_qua empty Pa /\ subqual empty Pa P.
Proof.
  intros Q P T Pa V b H.
  destruct (typing_tabs_core_wf empty Q (exp_tabs Pa V b) (qtyp_qtyp P T) H Pa V b eq_refl)
    as [Tbody [L [Pq [A [B [L2 [Hbody [Hwf [Hsq Hdis]]]]]]]]].
  destruct Hdis as [[Heq _]|Heq]; inversion Heq; subst; split; [|exact Hsq| |exact Hsq];
    destruct (subqual_wf _ _ _ Hsq) as [_ [HPa _]]; exact HPa.
Qed.

Lemma qabs_ann : forall Q P T Pa Qb b,
  typing empty Q (exp_qabs Pa Qb b) (qtyp_qtyp P T) ->
  wf_qua empty Pa /\ subqual empty Pa P.
Proof.
  intros Q P T Pa Qb b H.
  destruct (typing_qabs_core_wf empty Q (exp_qabs Pa Qb b) (qtyp_qtyp P T) H Pa Qb b eq_refl)
    as [Tbody [L [Pq [A [B [L2 [Hbody [Hwf [Hsq Hdis]]]]]]]]].
  destruct Hdis as [[Heq _]|Heq]; inversion Heq; subst; split; [|exact Hsq| |exact Hsq];
    destruct (subqual_wf _ _ _ Hsq) as [_ [HPa _]]; exact HPa.
Qed.

(* ---------------- shared frame helpers ---------------- *)

Lemma progress_frame_app : forall (v:exp) Q T f k U,
  value v ->
  typing empty Q v T ->
  typing_ctx empty Q (frame_app f :: k) T U ->
  exists s', state_step v (frame_app f :: k) --> s'.
Proof.
  intros v Q T f k U Hv Hty Hctx.
  destruct (state_app empty Q v T f k U Hty Hctx) as
    [Q' [T1 [T2 [Htyv [Hvf [Htyf Hctx']]]]]].
  destruct (value_arrow_abs f Q' T1 T2 Hvf Htyf) as
    [Pa [V [b [Heq [HwfPa HsubPa]]]]]. subst f.
  destruct (wf_qua_empty_concrete Pa HwfPa) as [t Hconc].
  pose proof (concretize_subqual_bwd empty Pa t wf_env_empty HwfPa Hconc) as Hbase.
  pose proof (subqual_trans empty (qua_base t) Pa Q' Hbase HsubPa) as Hsub.
  pose proof (typing_ctx_barrier_compatible empty Q' k T2 U Hctx'
                (qua_base t) t wf_env_empty (wf_qua_base empty t) eq_refl Hsub) as Hbar.
  exists (state_step (open_ee b v) (frame_barrier t :: k)).
  eapply step_app_abs; [exact Hv | exact Hconc | exact Hbar].
Qed.

Lemma progress_frame_pair_2 : forall (v:exp) Q T P v1 k U,
  value v ->
  typing empty Q v T ->
  typing_ctx empty Q (frame_pair_2 P v1 :: k) T U ->
  exists s', state_step v (frame_pair_2 P v1 :: k) --> s'.
Proof.
  intros v Q T P v1 k U Hv Hty Hctx.
  destruct (state_pair_2 empty Q v T P v1 k U Hty Hctx) as
    [Q' [T1 [T2 [HP [Hv1 [Hty1 [Htyv Hctx']]]]]]].
  exists (state_step (exp_pair P v1 v) k).
  eapply step_make_pair; [exact Hv | exact Hv1].
Qed.

(* ---------------- upqual ---------------- *)

Lemma progress_upqual_int : forall Q T P k U Pi i,
  typing empty Q (exp_int Pi i) T ->
  typing_ctx empty Q (frame_upqual P :: k) T U ->
  exists s', state_step (exp_int Pi i) (frame_upqual P :: k) --> s'.
Proof.
  intros Q T P k U Pi i Hty Hctx.
  destruct (state_upqual empty Q (exp_int Pi i) T P k U Hty Hctx) as [Q' [T0 [Htyv Hctx']]].
  destruct (int_ann Q' P T0 Pi i Htyv) as [HwfPi Hsub].
  destruct (wf_qua_empty_concrete Pi HwfPi) as [cQ HcQ].
  assert (HwfP : wf_qua empty P) by (destruct (subqual_wf _ _ _ Hsub) as [_ [_ HP]]; exact HP).
  destruct (wf_qua_empty_concrete P HwfP) as [cP HcP].
  assert (Hord : cQ ≤ cP) by (eapply subqual_concretize_ord; eassumption).
  exists (state_step (exp_int P i) k).
  eapply step_upqual_int; eassumption.
Qed.

Lemma progress_upqual_abs : forall Q T P k U Pa V b,
  typing empty Q (exp_abs Pa V b) T ->
  typing_ctx empty Q (frame_upqual P :: k) T U ->
  exists s', state_step (exp_abs Pa V b) (frame_upqual P :: k) --> s'.
Proof.
  intros Q T P k U Pa V b Hty Hctx.
  destruct (state_upqual empty Q (exp_abs Pa V b) T P k U Hty Hctx) as [Q' [T0 [Htyv Hctx']]].
  destruct (abs_ann Q' P T0 Pa V b Htyv) as [HwfPa Hsub].
  destruct (wf_qua_empty_concrete Pa HwfPa) as [cQ HcQ].
  assert (HwfP : wf_qua empty P) by (destruct (subqual_wf _ _ _ Hsub) as [_ [_ HP]]; exact HP).
  destruct (wf_qua_empty_concrete P HwfP) as [cP HcP].
  assert (Hord : cQ ≤ cP) by (eapply subqual_concretize_ord; eassumption).
  exists (state_step (exp_abs P V b) k).
  eapply step_upqual_abs; eassumption.
Qed.

Lemma progress_upqual_tabs : forall Q T P k U Pa V b,
  typing empty Q (exp_tabs Pa V b) T ->
  typing_ctx empty Q (frame_upqual P :: k) T U ->
  exists s', state_step (exp_tabs Pa V b) (frame_upqual P :: k) --> s'.
Proof.
  intros Q T P k U Pa V b Hty Hctx.
  destruct (state_upqual empty Q (exp_tabs Pa V b) T P k U Hty Hctx) as [Q' [T0 [Htyv Hctx']]].
  destruct (tabs_ann Q' P T0 Pa V b Htyv) as [HwfPa Hsub].
  destruct (wf_qua_empty_concrete Pa HwfPa) as [cQ HcQ].
  assert (HwfP : wf_qua empty P) by (destruct (subqual_wf _ _ _ Hsub) as [_ [_ HP]]; exact HP).
  destruct (wf_qua_empty_concrete P HwfP) as [cP HcP].
  assert (Hord : cQ ≤ cP) by (eapply subqual_concretize_ord; eassumption).
  exists (state_step (exp_tabs P V b) k).
  eapply step_upqual_tabs; eassumption.
Qed.

Lemma progress_upqual_qabs : forall Q T P k U Pa Qb b,
  typing empty Q (exp_qabs Pa Qb b) T ->
  typing_ctx empty Q (frame_upqual P :: k) T U ->
  exists s', state_step (exp_qabs Pa Qb b) (frame_upqual P :: k) --> s'.
Proof.
  intros Q T P k U Pa Qb b Hty Hctx.
  destruct (state_upqual empty Q (exp_qabs Pa Qb b) T P k U Hty Hctx) as [Q' [T0 [Htyv Hctx']]].
  destruct (qabs_ann Q' P T0 Pa Qb b Htyv) as [HwfPa Hsub].
  destruct (wf_qua_empty_concrete Pa HwfPa) as [cQ HcQ].
  assert (HwfP : wf_qua empty P) by (destruct (subqual_wf _ _ _ Hsub) as [_ [_ HP]]; exact HP).
  destruct (wf_qua_empty_concrete P HwfP) as [cP HcP].
  assert (Hord : cQ ≤ cP) by (eapply subqual_concretize_ord; eassumption).
  exists (state_step (exp_qabs P Qb b) k).
  eapply step_upqual_qabs; eassumption.
Qed.

(* ---------------- check ---------------- *)

Lemma progress_check_int : forall Q T R k U Pi i,
  typing empty Q (exp_int Pi i) T ->
  typing_ctx empty Q (frame_check R :: k) T U ->
  exists s', state_step (exp_int Pi i) (frame_check R :: k) --> s'.
Proof.
  intros Q T R k U Pi i Hty Hctx.
  destruct (state_check empty Q (exp_int Pi i) T R k U Hty Hctx) as
    [Q' [Pc [T0 [HR [Htyv Hctx']]]]].
  destruct (int_ann Q' (qua_meet Pc R) T0 Pi i Htyv) as [HwfPi HsubMeet].
  assert (HwfMeet : wf_qua empty (qua_meet Pc R))
    by (destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ Htyv)) as [Hm _]; exact Hm).
  assert (HwfPc : wf_qua empty Pc) by (inversion HwfMeet; subst; assumption).
  assert (HsubR : subqual empty Pi R).
  { eapply subqual_trans; [exact HsubMeet|].
    eapply subqual_meet_elimr; [exact HwfPc | apply subqual_refl; [exact wf_env_empty | exact HR]]. }
  destruct (wf_qua_empty_concrete Pi HwfPi) as [cQ HcQ].
  destruct (wf_qua_empty_concrete R HR) as [cP HcP].
  assert (Hord : cQ ≤ cP) by (eapply subqual_concretize_ord; eassumption).
  exists (state_step (exp_int Pi i) k).
  eapply step_check_int; eassumption.
Qed.

Lemma progress_check_abs : forall Q T R k U Pa V b,
  typing empty Q (exp_abs Pa V b) T ->
  typing_ctx empty Q (frame_check R :: k) T U ->
  exists s', state_step (exp_abs Pa V b) (frame_check R :: k) --> s'.
Proof.
  intros Q T R k U Pa V b Hty Hctx.
  destruct (state_check empty Q (exp_abs Pa V b) T R k U Hty Hctx) as
    [Q' [Pc [T0 [HR [Htyv Hctx']]]]].
  destruct (abs_ann Q' (qua_meet Pc R) T0 Pa V b Htyv) as [HwfPa HsubMeet].
  assert (HwfMeet : wf_qua empty (qua_meet Pc R))
    by (destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ Htyv)) as [Hm _]; exact Hm).
  assert (HwfPc : wf_qua empty Pc) by (inversion HwfMeet; subst; assumption).
  assert (HsubR : subqual empty Pa R).
  { eapply subqual_trans; [exact HsubMeet|].
    eapply subqual_meet_elimr; [exact HwfPc | apply subqual_refl; [exact wf_env_empty | exact HR]]. }
  destruct (wf_qua_empty_concrete Pa HwfPa) as [cQ HcQ].
  destruct (wf_qua_empty_concrete R HR) as [cP HcP].
  assert (Hord : cQ ≤ cP) by (eapply subqual_concretize_ord; eassumption).
  exists (state_step (exp_abs Pa V b) k).
  eapply step_check_abs; eassumption.
Qed.

Lemma progress_check_tabs : forall Q T R k U Pa V b,
  typing empty Q (exp_tabs Pa V b) T ->
  typing_ctx empty Q (frame_check R :: k) T U ->
  exists s', state_step (exp_tabs Pa V b) (frame_check R :: k) --> s'.
Proof.
  intros Q T R k U Pa V b Hty Hctx.
  destruct (state_check empty Q (exp_tabs Pa V b) T R k U Hty Hctx) as
    [Q' [Pc [T0 [HR [Htyv Hctx']]]]].
  destruct (tabs_ann Q' (qua_meet Pc R) T0 Pa V b Htyv) as [HwfPa HsubMeet].
  assert (HwfMeet : wf_qua empty (qua_meet Pc R))
    by (destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ Htyv)) as [Hm _]; exact Hm).
  assert (HwfPc : wf_qua empty Pc) by (inversion HwfMeet; subst; assumption).
  assert (HsubR : subqual empty Pa R).
  { eapply subqual_trans; [exact HsubMeet|].
    eapply subqual_meet_elimr; [exact HwfPc | apply subqual_refl; [exact wf_env_empty | exact HR]]. }
  destruct (wf_qua_empty_concrete Pa HwfPa) as [cQ HcQ].
  destruct (wf_qua_empty_concrete R HR) as [cP HcP].
  assert (Hord : cQ ≤ cP) by (eapply subqual_concretize_ord; eassumption).
  exists (state_step (exp_tabs Pa V b) k).
  eapply step_check_tabs; eassumption.
Qed.

Lemma progress_check_qabs : forall Q T R k U Pa Qb b,
  typing empty Q (exp_qabs Pa Qb b) T ->
  typing_ctx empty Q (frame_check R :: k) T U ->
  exists s', state_step (exp_qabs Pa Qb b) (frame_check R :: k) --> s'.
Proof.
  intros Q T R k U Pa Qb b Hty Hctx.
  destruct (state_check empty Q (exp_qabs Pa Qb b) T R k U Hty Hctx) as
    [Q' [Pc [T0 [HR [Htyv Hctx']]]]].
  destruct (qabs_ann Q' (qua_meet Pc R) T0 Pa Qb b Htyv) as [HwfPa HsubMeet].
  assert (HwfMeet : wf_qua empty (qua_meet Pc R))
    by (destruct (wf_qtyp_qtyp_inv _ _ _ (typing_wf_qtyp _ _ _ _ Htyv)) as [Hm _]; exact Hm).
  assert (HwfPc : wf_qua empty Pc) by (inversion HwfMeet; subst; assumption).
  assert (HsubR : subqual empty Pa R).
  { eapply subqual_trans; [exact HsubMeet|].
    eapply subqual_meet_elimr; [exact HwfPc | apply subqual_refl; [exact wf_env_empty | exact HR]]. }
  destruct (wf_qua_empty_concrete Pa HwfPa) as [cQ HcQ].
  destruct (wf_qua_empty_concrete R HR) as [cP HcP].
  assert (Hord : cQ ≤ cP) by (eapply subqual_concretize_ord; eassumption).
  exists (state_step (exp_qabs Pa Qb b) k).
  eapply step_check_qabs; eassumption.
Qed.

(* ---------------- tabs positive ---------------- *)

Lemma progress_frame_tabs_tabs : forall Q T Varg k U Pa V b,
  typing empty Q (exp_tabs Pa V b) T ->
  typing_ctx empty Q (frame_tabs Varg :: k) T U ->
  exists s', state_step (exp_tabs Pa V b) (frame_tabs Varg :: k) --> s'.
Proof.
  intros Q T Varg k U Pa V b Hty Hctx.
  destruct (state_tabs empty Q (exp_tabs Pa V b) T Varg k U Hty Hctx) as
    [Q' [L [T1 [T2 [Htyv [HsubV [HwfBody Hctx']]]]]]].
  destruct (tabs_ann Q' Q' (typ_all T1 T2) Pa V b Htyv) as [HwfPa HsubPa].
  destruct (sub_wf _ _ _ HsubV) as [_ [HtypeV _]].
  assert (HtypeVarg : type Varg) by (exact (wf_typ_type empty Varg HtypeV)).
  destruct (wf_qua_empty_concrete Pa HwfPa) as [t Hconc].
  pose proof (concretize_subqual_bwd empty Pa t wf_env_empty HwfPa Hconc) as Hbase.
  pose proof (subqual_trans empty (qua_base t) Pa Q' Hbase HsubPa) as Hsub.
  pose proof (typing_ctx_barrier_compatible empty Q' k (open_tqt T2 Varg) U Hctx'
                (qua_base t) t wf_env_empty (wf_qua_base empty t) eq_refl Hsub) as Hbar.
  exists (state_step (open_te b Varg) (frame_barrier t :: k)).
  eapply step_app_tabs; [exact HtypeVarg | exact Hconc | exact Hbar].
Qed.

(* ---------------- qabs positive ---------------- *)

Lemma progress_frame_qabs_qabs : forall Q T R k U Pa Qb b,
  typing empty Q (exp_qabs Pa Qb b) T ->
  typing_ctx empty Q (frame_qabs R :: k) T U ->
  exists s', state_step (exp_qabs Pa Qb b) (frame_qabs R :: k) --> s'.
Proof.
  intros Q T R k U Pa Qb b Hty Hctx.
  destruct (state_qabs empty Q (exp_qabs Pa Qb b) T R k U Hty Hctx) as
    [Q' [L [R0 [T2 [Htyv [HsubR [HwfBody Hctx']]]]]]].
  destruct (qabs_ann Q' Q' (typ_qall R0 T2) Pa Qb b Htyv) as [HwfPa HsubPa].
  destruct (subqual_wf _ _ _ HsubR) as [_ [HwfR _]].
  assert (HqualR : qual R) by (exact (wf_qua_qual empty R HwfR)).
  destruct (wf_qua_empty_concrete Pa HwfPa) as [t Hconc].
  pose proof (concretize_subqual_bwd empty Pa t wf_env_empty HwfPa Hconc) as Hbase.
  pose proof (subqual_trans empty (qua_base t) Pa Q' Hbase HsubPa) as Hsub.
  pose proof (typing_ctx_barrier_compatible empty Q' k (open_qqt T2 R) U Hctx'
                (qua_base t) t wf_env_empty (wf_qua_base empty t) eq_refl Hsub) as Hbar.
  exists (state_step (open_qe b R) (frame_barrier t :: k)).
  eapply step_app_qabs; [exact HqualR | exact Hconc | exact Hbar].
Qed.

(* ---------------- if0 positive ---------------- *)

Lemma progress_if0_int : forall Q T e2 e3 k U Pi i,
  typing empty Q (exp_int Pi i) T ->
  typing_ctx empty Q (frame_if0 e2 e3 :: k) T U ->
  exists s', state_step (exp_int Pi i) (frame_if0 e2 e3 :: k) --> s'.
Proof.
  intros Q T e2 e3 k U Pi i Hty Hctx.
  destruct (state_if0 empty Q (exp_int Pi i) T e2 e3 k U Hty Hctx) as
    [Q' [Qe [T0 [HQe [Htyv [Hty2 [Hty3 Hctx']]]]]]].
  destruct (Z.eq_dec i 0) as [Heq|Hneq].
  - subst i. exists (state_step e2 k). apply step_if0_zero.
  - exists (state_step e3 k). eapply step_if0_nonzero. exact Hneq.
Qed.

(* ---------------- contradiction tactic ---------------- *)

Ltac solve_shape_contradiction :=
  match goal with
  | H : typing empty ?Q (exp_int ?Pi ?i) (qtyp_qtyp ?P ?T) |- _ =>
      destruct (int_typing_shape Q P T Pi i H) as [Heq|Heq]; discriminate Heq
  | H : typing empty ?Q (exp_abs ?Pa ?V ?b) (qtyp_qtyp ?P ?T) |- _ =>
      destruct (abs_typing_shape Q P T Pa V b H) as [[A [B Heq]]|Heq]; discriminate Heq
  | H : typing empty ?Q (exp_tabs ?Pa ?V ?b) (qtyp_qtyp ?P ?T) |- _ =>
      destruct (tabs_typing_shape Q P T Pa V b H) as [[A [B Heq]]|Heq]; discriminate Heq
  | H : typing empty ?Q (exp_qabs ?Pa ?Qb ?b) (qtyp_qtyp ?P ?T) |- _ =>
      destruct (qabs_typing_shape Q P T Pa Qb b H) as [[A [B Heq]]|Heq]; discriminate Heq
  end.

(* ---------------- progress for integer values ---------------- *)

Lemma progress_int : forall Pi i Q T k U,
  typing empty Q (exp_int Pi i) T ->
  typing_ctx empty Q k T U ->
  done_state (state_step (exp_int Pi i) k) \/
  exists s', state_step (exp_int Pi i) k --> s'.
Proof.
  intros Pi i Q T k U Hty Hctx.
  assert (Hv : value (exp_int Pi i)).
  { apply value_int.
    destruct (typing_int_core_wf empty Q (exp_int Pi i) T Hty Pi i eq_refl) as (Pq & Hwf & _).
    exact (wf_qua_qual empty Pi Hwf). }
  destruct k as [|f k].
  - left. apply done_value. exact Hv.
  - destruct f as
      [ e2 | f0 | V | R | e2 | P | P | e2 e3 | P e2 | P v1 | | | P | R | t | s | e2 e3 ].
    + (* frame_abs *) right. exists (state_step e2 (frame_app (exp_int Pi i) :: k)).
      apply step_app_2. exact Hv.
    + (* frame_app *) right. eapply progress_frame_app; eassumption.
    + (* frame_tabs *) exfalso.
      destruct (state_tabs empty Q (exp_int Pi i) T V k U Hty Hctx) as
        [Q' [L [T1 [T2 [Htyv [_ [_ _]]]]]]].
      solve_shape_contradiction.
    + (* frame_qabs *) exfalso.
      destruct (state_qabs empty Q (exp_int Pi i) T R k U Hty Hctx) as
        [Q' [L [R0 [T2 [Htyv [_ [_ _]]]]]]].
      solve_shape_contradiction.
    + (* frame_let *) right. exists (state_step (open_ee e2 (exp_int Pi i)) k).
      apply step_let_value. exact Hv.
    + (* frame_inl *) right. exists (state_step (exp_inl P (exp_int Pi i)) k).
      apply step_make_inl. exact Hv.
    + (* frame_inr *) right. exists (state_step (exp_inr P (exp_int Pi i)) k).
      apply step_make_inr. exact Hv.
    + (* frame_case *) exfalso.
      destruct (state_case empty Q (exp_int Pi i) T e2 e3 k U Hty Hctx) as
        [Q' [L [P [T1 [T2 [T0 [HP [Htyv _]]]]]]]].
      solve_shape_contradiction.
    + (* frame_pair_1 *) right. exists (state_step e2 (frame_pair_2 P (exp_int Pi i) :: k)).
      apply step_pair_2. exact Hv.
    + (* frame_pair_2 *) right. eapply progress_frame_pair_2; eassumption.
    + (* frame_first *) exfalso.
      destruct (state_first empty Q (exp_int Pi i) T k U Hty Hctx) as
        [Q' [P [T1 [T2 [HP [HT2 [Htyv Hctx']]]]]]].
      solve_shape_contradiction.
    + (* frame_second *) exfalso.
      destruct (state_second empty Q (exp_int Pi i) T k U Hty Hctx) as
        [Q' [P [T1 [T2 [HP [HT1 [Htyv Hctx']]]]]]].
      solve_shape_contradiction.
    + (* frame_upqual *) right. eapply progress_upqual_int; eassumption.
    + (* frame_check *) right. eapply progress_check_int; eassumption.
    + (* frame_without *) right. exists (state_step (exp_int Pi i) k).
      apply step_elim_without. exact Hv.
    + (* frame_barrier *) right. exists (state_step (exp_int Pi i) k).
      apply step_barrier. exact Hv.
    + (* frame_if0 *) right. eapply progress_if0_int; eassumption.
Qed.

(* ---------------- progress for abstraction values ---------------- *)

Lemma progress_abs : forall Pa V b Q T k U,
  typing empty Q (exp_abs Pa V b) T ->
  typing_ctx empty Q k T U ->
  done_state (state_step (exp_abs Pa V b) k) \/
  exists s', state_step (exp_abs Pa V b) k --> s'.
Proof.
  intros Pa V b Q T k U Hty Hctx.
  assert (Hv : value (exp_abs Pa V b)) by (apply value_abs; exact (typing_expr empty Q (exp_abs Pa V b) T Hty)).
  destruct k as [|f k].
  - left. apply done_value. exact Hv.
  - destruct f as
      [ e2 | f0 | V0 | R | e2 | P | P | e2 e3 | P e2 | P v1 | | | P | R | t | s | e2 e3 ].
    + (* frame_abs *) right. exists (state_step e2 (frame_app (exp_abs Pa V b) :: k)).
      apply step_app_2. exact Hv.
    + (* frame_app *) right. eapply progress_frame_app; eassumption.
    + (* frame_tabs *) exfalso.
      destruct (state_tabs empty Q (exp_abs Pa V b) T V0 k U Hty Hctx) as
        [Q' [L [T1 [T2 [Htyv [_ [_ _]]]]]]].
      solve_shape_contradiction.
    + (* frame_qabs *) exfalso.
      destruct (state_qabs empty Q (exp_abs Pa V b) T R k U Hty Hctx) as
        [Q' [L [R0 [T2 [Htyv [_ [_ _]]]]]]].
      solve_shape_contradiction.
    + (* frame_let *) right. exists (state_step (open_ee e2 (exp_abs Pa V b)) k).
      apply step_let_value. exact Hv.
    + (* frame_inl *) right. exists (state_step (exp_inl P (exp_abs Pa V b)) k).
      apply step_make_inl. exact Hv.
    + (* frame_inr *) right. exists (state_step (exp_inr P (exp_abs Pa V b)) k).
      apply step_make_inr. exact Hv.
    + (* frame_case *) exfalso.
      destruct (state_case empty Q (exp_abs Pa V b) T e2 e3 k U Hty Hctx) as
        [Q' [L [P0 [T1 [T2 [T0 [HP [Htyv _]]]]]]]].
      solve_shape_contradiction.
    + (* frame_pair_1 *) right. exists (state_step e2 (frame_pair_2 P (exp_abs Pa V b) :: k)).
      apply step_pair_2. exact Hv.
    + (* frame_pair_2 *) right. eapply progress_frame_pair_2; eassumption.
    + (* frame_first *) exfalso.
      destruct (state_first empty Q (exp_abs Pa V b) T k U Hty Hctx) as
        [Q' [P0 [T1 [T2 [HP [HT2 [Htyv Hctx']]]]]]].
      solve_shape_contradiction.
    + (* frame_second *) exfalso.
      destruct (state_second empty Q (exp_abs Pa V b) T k U Hty Hctx) as
        [Q' [P0 [T1 [T2 [HP [HT1 [Htyv Hctx']]]]]]].
      solve_shape_contradiction.
    + (* frame_upqual *) right. eapply progress_upqual_abs; eassumption.
    + (* frame_check *) right. eapply progress_check_abs; eassumption.
    + (* frame_without *) right. exists (state_step (exp_abs Pa V b) k).
      apply step_elim_without. exact Hv.
    + (* frame_barrier *) right. exists (state_step (exp_abs Pa V b) k).
      apply step_barrier. exact Hv.
    + (* frame_if0 *) exfalso.
      destruct (state_if0 empty Q (exp_abs Pa V b) T e2 e3 k U Hty Hctx) as
        [Q' [Qe [T0 [HQe [Htyv _]]]]].
      solve_shape_contradiction.
Qed.

(* ---------------- progress for type abstraction values ---------------- *)

Lemma progress_tabs : forall Pa V b Q T k U,
  typing empty Q (exp_tabs Pa V b) T ->
  typing_ctx empty Q k T U ->
  done_state (state_step (exp_tabs Pa V b) k) \/
  exists s', state_step (exp_tabs Pa V b) k --> s'.
Proof.
  intros Pa V b Q T k U Hty Hctx.
  assert (Hv : value (exp_tabs Pa V b)) by (apply value_tabs; exact (typing_expr empty Q (exp_tabs Pa V b) T Hty)).
  destruct k as [|f k].
  - left. apply done_value. exact Hv.
  - destruct f as
      [ e2 | f0 | V0 | R | e2 | P | P | e2 e3 | P e2 | P v1 | | | P | R | t | s | e2 e3 ].
    + (* frame_abs *) right. exists (state_step e2 (frame_app (exp_tabs Pa V b) :: k)).
      apply step_app_2. exact Hv.
    + (* frame_app *) right. eapply progress_frame_app; eassumption.
    + (* frame_tabs *) right. eapply progress_frame_tabs_tabs; eassumption.
    + (* frame_qabs *) exfalso.
      destruct (state_qabs empty Q (exp_tabs Pa V b) T R k U Hty Hctx) as
        [Q' [L [R0 [T2 [Htyv [_ [_ _]]]]]]].
      solve_shape_contradiction.
    + (* frame_let *) right. exists (state_step (open_ee e2 (exp_tabs Pa V b)) k).
      apply step_let_value. exact Hv.
    + (* frame_inl *) right. exists (state_step (exp_inl P (exp_tabs Pa V b)) k).
      apply step_make_inl. exact Hv.
    + (* frame_inr *) right. exists (state_step (exp_inr P (exp_tabs Pa V b)) k).
      apply step_make_inr. exact Hv.
    + (* frame_case *) exfalso.
      destruct (state_case empty Q (exp_tabs Pa V b) T e2 e3 k U Hty Hctx) as
        [Q' [L [P0 [T1 [T2 [T0 [HP [Htyv _]]]]]]]].
      solve_shape_contradiction.
    + (* frame_pair_1 *) right. exists (state_step e2 (frame_pair_2 P (exp_tabs Pa V b) :: k)).
      apply step_pair_2. exact Hv.
    + (* frame_pair_2 *) right. eapply progress_frame_pair_2; eassumption.
    + (* frame_first *) exfalso.
      destruct (state_first empty Q (exp_tabs Pa V b) T k U Hty Hctx) as
        [Q' [P0 [T1 [T2 [HP [HT2 [Htyv Hctx']]]]]]].
      solve_shape_contradiction.
    + (* frame_second *) exfalso.
      destruct (state_second empty Q (exp_tabs Pa V b) T k U Hty Hctx) as
        [Q' [P0 [T1 [T2 [HP [HT1 [Htyv Hctx']]]]]]].
      solve_shape_contradiction.
    + (* frame_upqual *) right. eapply progress_upqual_tabs; eassumption.
    + (* frame_check *) right. eapply progress_check_tabs; eassumption.
    + (* frame_without *) right. exists (state_step (exp_tabs Pa V b) k).
      apply step_elim_without. exact Hv.
    + (* frame_barrier *) right. exists (state_step (exp_tabs Pa V b) k).
      apply step_barrier. exact Hv.
    + (* frame_if0 *) exfalso.
      destruct (state_if0 empty Q (exp_tabs Pa V b) T e2 e3 k U Hty Hctx) as
        [Q' [Qe [T0 [HQe [Htyv _]]]]].
      solve_shape_contradiction.
Qed.

(* ---------------- progress for qualifier abstraction values ---------------- *)

Lemma progress_qabs : forall Pa Qb b Q T k U,
  typing empty Q (exp_qabs Pa Qb b) T ->
  typing_ctx empty Q k T U ->
  done_state (state_step (exp_qabs Pa Qb b) k) \/
  exists s', state_step (exp_qabs Pa Qb b) k --> s'.
Proof.
  intros Pa Qb b Q T k U Hty Hctx.
  assert (Hv : value (exp_qabs Pa Qb b)) by (apply value_qabs; exact (typing_expr empty Q (exp_qabs Pa Qb b) T Hty)).
  destruct k as [|f k].
  - left. apply done_value. exact Hv.
  - destruct f as
      [ e2 | f0 | V0 | R | e2 | P | P | e2 e3 | P e2 | P v1 | | | P | R | t | s | e2 e3 ].
    + (* frame_abs *) right. exists (state_step e2 (frame_app (exp_qabs Pa Qb b) :: k)).
      apply step_app_2. exact Hv.
    + (* frame_app *) right. eapply progress_frame_app; eassumption.
    + (* frame_tabs *) exfalso.
      destruct (state_tabs empty Q (exp_qabs Pa Qb b) T V0 k U Hty Hctx) as
        [Q' [L [T1 [T2 [Htyv [_ [_ _]]]]]]].
      solve_shape_contradiction.
    + (* frame_qabs *) right. eapply progress_frame_qabs_qabs; eassumption.
    + (* frame_let *) right. exists (state_step (open_ee e2 (exp_qabs Pa Qb b)) k).
      apply step_let_value. exact Hv.
    + (* frame_inl *) right. exists (state_step (exp_inl P (exp_qabs Pa Qb b)) k).
      apply step_make_inl. exact Hv.
    + (* frame_inr *) right. exists (state_step (exp_inr P (exp_qabs Pa Qb b)) k).
      apply step_make_inr. exact Hv.
    + (* frame_case *) exfalso.
      destruct (state_case empty Q (exp_qabs Pa Qb b) T e2 e3 k U Hty Hctx) as
        [Q' [L [P0 [T1 [T2 [T0 [HP [Htyv _]]]]]]]].
      solve_shape_contradiction.
    + (* frame_pair_1 *) right. exists (state_step e2 (frame_pair_2 P (exp_qabs Pa Qb b) :: k)).
      apply step_pair_2. exact Hv.
    + (* frame_pair_2 *) right. eapply progress_frame_pair_2; eassumption.
    + (* frame_first *) exfalso.
      destruct (state_first empty Q (exp_qabs Pa Qb b) T k U Hty Hctx) as
        [Q' [P0 [T1 [T2 [HP [HT2 [Htyv Hctx']]]]]]].
      solve_shape_contradiction.
    + (* frame_second *) exfalso.
      destruct (state_second empty Q (exp_qabs Pa Qb b) T k U Hty Hctx) as
        [Q' [P0 [T1 [T2 [HP [HT1 [Htyv Hctx']]]]]]].
      solve_shape_contradiction.
    + (* frame_upqual *) right. eapply progress_upqual_qabs; eassumption.
    + (* frame_check *) right. eapply progress_check_qabs; eassumption.
    + (* frame_without *) right. exists (state_step (exp_qabs Pa Qb b) k).
      apply step_elim_without. exact Hv.
    + (* frame_barrier *) right. exists (state_step (exp_qabs Pa Qb b) k).
      apply step_barrier. exact Hv.
    + (* frame_if0 *) exfalso.
      destruct (state_if0 empty Q (exp_qabs Pa Qb b) T e2 e3 k U Hty Hctx) as
        [Q' [Qe [T0 [HQe [Htyv _]]]]].
      solve_shape_contradiction.
Qed.

(* ---------------- progress ---------------- *)

Lemma progress_aux : forall s U, typing_state empty s U ->
  done_state s \/ exists s', s --> s'.
Proof.
  intros s U HT.
  destruct s as [e k].
  destruct (typing_state_inv empty e k U HT) as [Q [T [Hty Hctx]]].
  destruct e as
    [ Pi i | n | x | Pa V b | e1 e2 | Pa V b | e1 V | Pa Qb b | e1 Qb
    | e1 e2 | P e1 | P e1 | e1 e2 e3 | P e1 e2 | e1 | e1
    | P e1 | P l | e1 | e1 e2 | P e1 | P e1 | P e1 | bb | e1 e2 e3 ].
  - exact (progress_int Pi i Q T k U Hty Hctx).
  - exfalso. apply typing_expr in Hty. inversion Hty.
  - exfalso. exact (typing_fvar_empty_false Q x T Hty).
  - exact (progress_abs Pa V b Q T k U Hty Hctx).
  - right. exists (state_step e1 (frame_abs e2 :: k)). apply step_app_1.
  - exact (progress_tabs Pa V b Q T k U Hty Hctx).
  - right. exists (state_step e1 (frame_tabs V :: k)). apply step_tapp.
  - exact (progress_qabs Pa Qb b Q T k U Hty Hctx).
  - right. exists (state_step e1 (frame_qabs Qb :: k)). apply step_qapp.
  - right. exists (state_step e1 (frame_let e2 :: k)). apply step_let.
  - right. exists (state_step e1 (frame_inl P :: k)). apply step_inl.
  - right. exists (state_step e1 (frame_inr P :: k)). apply step_inr.
  - right. exists (state_step e1 (frame_case e2 e3 :: k)). apply step_case.
  - right. exists (state_step e1 (frame_pair_1 P e2 :: k)). apply step_pair_1.
  - right. exists (state_step e1 (frame_first :: k)). apply step_first.
  - right. exists (state_step e1 (frame_second :: k)). apply step_second.
  - exfalso. apply typing_expr in Hty. inversion Hty.
  - exfalso. apply typing_expr in Hty. inversion Hty.
  - exfalso. apply typing_expr in Hty. inversion Hty.
  - exfalso. apply typing_expr in Hty. inversion Hty.
  - right. exists (state_step e1 (frame_upqual P :: k)). apply step_upqual_1.
  - right. exists (state_step e1 (frame_check P :: k)). apply step_check_1.
  - right.
    destruct (wf_qua_empty_concrete P (typing_without_wf empty Q e1 P T Hty)) as [t Hconc].
    exists (state_step e1 (frame_without t :: k)). apply step_without. exact Hconc.
  - right.
    pose proof (typing_do_subqual empty Q bb T Hty) as Hsub.
    pose proof (typing_ctx_barrier_compatible empty Q k T U Hctx
                  (qua_base bb) bb wf_env_empty (wf_qua_base empty bb) eq_refl Hsub) as Hbar.
    exists (state_step (exp_int (qua_base bot) 42) k). apply step_do. exact Hbar.
  - right. exists (state_step e1 (frame_if0 e2 e3 :: k)). apply step_if0.
Qed.

(* ================= target theorems ================= *)
Theorem preservation : forall E s s' U,
  typing_state E s U ->
  s --> s' ->
  typing_state E s' U.
Proof. exact preservation_aux. Qed.

Theorem progress : forall s U,
  typing_state empty s U ->
  done_state s \/ exists s', s --> s'.
Proof. exact progress_aux. Qed.
