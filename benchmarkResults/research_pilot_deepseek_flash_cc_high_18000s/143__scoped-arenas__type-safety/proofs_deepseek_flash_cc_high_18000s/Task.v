Require Export Arith.EqNat.

Require Export PeanoNat.

Require Import Coq.Arith.Arith.

Require Import Coq.Bool.Bool.

Require Import Coq.Program.Equality.

Require Import Coq.Lists.List.

Require Import FunctionalExtensionality.

Require Import Coq.Logic.PropExtensionality.

Require Import Psatz.

Require Import ZArith.

Require Import Coq.Arith.Compare_dec.

Import ListNotations.

Require Import vars.

Require Import env.

Require Import nats.

Require Import qualifiers.

Require Import boolean.

Require Import lang.

Require Import qenv.

Require Import ops.

Require Import killsep.

Require Import rules.

Require Import vtp_subst.

Import QualNotations.

Local Open Scope qualifiers.

Import OpeningNotations.

Local Open Scope opening.

Import SplicingNotations.

Local Open Scope splicing.

Import SubstitutionNotations.

Local Open Scope substitutions.

Inductive disjointq (Σ Σ' : senv) : qual -> qual -> Prop :=
| disj_bot : forall q,
    disjointq Σ Σ' q ∅
| disj_loc : forall T q q',
    closed_ty 0 0 (‖Σ‖) T ->
    closed_Qual 0 0 (‖Σ‖) q↑ ->
    ♦∉ q ->
    Σ' = [(T,q)] :: Σ ->
    disjointq Σ Σ' q' (&!‖Σ‖)
.

Arguments disj_loc { Σ Σ' }.

Notation " S → T ∋ q ⊕ q'" := (disjointq S T q q') (at level 10).

Definition CtxOK (Γ : tenv) (φ : qual) (Σ : senv) (ϰ : qual) (σ : store) : Prop :=
  qdom' σ ⊑↑ qdom Σ /\ ‖ σ ‖ = ‖ Σ ‖ /\
     φ ⊑↑ (qdom Σ) /\
  closed_Qual 0 0 (‖Σ‖) ϰ↑ /\
  kill_sep ϰ φ /\
  forall l o cty T q,
  (l ∈ₗ ϰ -> indexr l σ = Some None) /\ (~(l∈ₗ ϰ) ->
    l ∈ₗ φ ->
    indexr l Σ = Some cty ->
    (exists ctm, (indexr l σ = Some (Some ctm) /\ (‖ cty ‖) = (‖ ctm ‖)) /\
    (indexr o cty = Some (T,q) ->  (exists v, indexr o ctm = Some v /\
      value v /\ (q ⊑↑ φ -> vtp Σ ϰ φ v T q))))

  )
.

Fixpoint wf_step (t:tm) : Prop :=
  match t with
  | ttabs t1 => local_locs t1 = ∅
  | ttapp t1 => wf_step t1
  | tabs t1 => local_locs t1 = ∅
  | tapp t1 t2 => wf_step t1 /\ wf_step t2 /\ ((value t1) \/ local_locs t2 = ∅)
  | tref t1 => wf_step t1
  | trefat t1 t2 => wf_step t1 /\ wf_step t2 /\ (local_locs t1 = ∅ \/ (value t2))
  | tderef t1 => wf_step t1
  | tassign t1 t2 => wf_step t1 /\ wf_step t2 /\ ((value t1) \/ local_locs t2 = ∅)
  | twithr t1 t2 => wf_step t1 /\ wf_step t2 /\ (local_locs t2 = ∅)
  | twithc l t1 => wf_step t1
  | _ => True
  end.

Definition wf_store (σ : store) : Prop :=
    forall l o v, sindexr' l o σ = Some (v) -> wf_step v /\ value v.

Inductive envUpdate (Σ : senv) (φ : qual) (ϰ : qual) (LC : qual): senv -> qual -> qual -> Prop :=
| env_phi : forall Σ',

    Σ' ⊇₂ Σ ->
    ‖Σ'‖ = ‖Σ‖ ->
    envUpdate Σ φ ϰ LC Σ' φ ϰ
| env_fresh : forall T q,
    kill_sep ϰ q ->
    envUpdate Σ φ ϰ LC ([(T,q)] :: Σ) (φ ⊔ &!(‖Σ‖)) ϰ
| env_kill : forall l,
    l < (‖Σ‖) ->
    l ∈ₗ LC ->
    envUpdate Σ φ ϰ LC Σ (q_remove Σ l φ) (ϰ ⊔ &!l)
.

Inductive preserve (Γ : tenv) (Σ : senv) (ϰ : qual) (φ : qual) (LC : qual) (t' : tm) (T : ty) (d : qual) (σ' : store) : Prop :=
| Preserve : forall Σ' d' φ' ϰ',
    Σ' ⊇₂ Σ ->

    envUpdate Σ φ ϰ LC Σ' φ' ϰ' ->
    d' ⊑↑ φ' ->
    wf_senv Σ' ->
    CtxOK Γ φ' Σ' ϰ' σ' ->
    Σ → Σ' ∋ d ⊕ d'  ->
    has_type Γ φ' Σ' t' T (d ⋓ d') ->

    wf_store σ' ->
    wf_step t' ->
    preserve Γ Σ ϰ φ LC t' T d σ'.

Arguments Preserve {Γ Σ ϰ φ LC t' T d σ'}.

(* ===== Partial proof infrastructure (helper definitions and lemmas) ===== *)

Lemma qual_eta : forall q : qual, (((qfresh q, qfvs q), qbvs q), qlocs q) = q.
Proof. intro q. destruct q as [p n]. destruct p as [b c]. destruct b as [bf bg]. reflexivity. Qed.

Lemma qual_ext : forall (q1 q2 : qual),
  qfresh q1 = qfresh q2 -> qfvs q1 = qfvs q2 -> qbvs q1 = qbvs q2 -> qlocs q1 = qlocs q2 -> q1 = q2.
Proof.
  intros q1 q2 H1 H2 H3 H4.
  rewrite <- (qual_eta q1), <- (qual_eta q2).
  rewrite H1, H2, H3, H4. reflexivity.
Qed.

Lemma n_or_empty_r : forall f, n_or f n_empty = f.
Proof. intros. apply functional_extensionality. intro x. unfold n_or, n_empty. rewrite orb_false_r. reflexivity. Qed.
Lemma n_or_empty_l : forall f, n_or n_empty f = f.
Proof. intros. apply functional_extensionality. intro x. unfold n_or, n_empty. rewrite orb_false_l. reflexivity. Qed.
Lemma n_or_comm : forall f g, n_or f g = n_or g f.
Proof. intros. apply functional_extensionality. intro x. unfold n_or. destruct (f x),(g x); reflexivity. Qed.
Lemma n_or_assoc : forall f g h, n_or (n_or f g) h = n_or f (n_or g h).
Proof. intros. apply functional_extensionality. intro x. unfold n_or. destruct (f x),(g x),(h x); reflexivity. Qed.
Lemma n_and_comm : forall f g, n_and f g = n_and g f.
Proof. intros. apply functional_extensionality. intro x. unfold n_and. destruct (f x),(g x); reflexivity. Qed.

Lemma qor_comm : forall a b, qor a b = qor b a.
Proof.
  intros. apply qual_ext.
  - unfold qor, qfresh. simpl. apply orb_comm.
  - unfold qor, qfvs. simpl. apply n_or_comm.
  - unfold qor, qbvs. simpl. apply n_or_comm.
  - unfold qor, qlocs. simpl. apply n_or_comm.
Qed.
Lemma qor_assoc : forall a b c, qor (qor a b) c = qor a (qor b c).
Proof.
  intros. apply qual_ext.
  - unfold qor, qfresh. simpl. rewrite orb_assoc. reflexivity.
  - unfold qor, qfvs. simpl. apply n_or_assoc.
  - unfold qor, qbvs. simpl. apply n_or_assoc.
  - unfold qor, qlocs. simpl. apply n_or_assoc.
Qed.
Lemma qor_empty_r : forall d, qor d q_empty = d.
Proof.
  intros. apply qual_ext.
  - unfold qor, q_empty, qfresh. simpl. rewrite orb_false_r. reflexivity.
  - unfold qor, q_empty, qfvs. simpl. apply n_or_empty_r.
  - unfold qor, q_empty, qbvs. simpl. apply n_or_empty_r.
  - unfold qor, q_empty, qlocs. simpl. apply n_or_empty_r.
Qed.
Lemma qor_empty_l : forall d, qor q_empty d = d.
Proof.
  intros. apply qual_ext.
  - unfold qor, q_empty, qfresh. simpl. reflexivity.
  - unfold qor, q_empty, qfvs. simpl. apply n_or_empty_l.
  - unfold qor, q_empty, qbvs. simpl. apply n_or_empty_l.
  - unfold qor, q_empty, qlocs. simpl. apply n_or_empty_l.
Qed.

Lemma Subq_refl : forall q, Subq q q.
Proof. intros q. unfold Subq, N_sub, N_lift. repeat split; intros; auto. Qed.
Lemma Subq_trans : forall a b c, Subq a b -> Subq b c -> Subq a c.
Proof.
  intros a b c [H1 [H2 [H3 H4]]] [G1 [G2 [G3 G4]]].
  unfold Subq; simpl. split.
  - intros H; apply G1; apply H1; auto.
  - split.
    + intros x Hx; apply G2; apply H2; auto.
    + split.
      * intros x Hx; apply G3; apply H3; auto.
      * intros x Hx; apply G4; apply H4; auto.
Qed.
Lemma subq_refl : forall q, q ⊑ q.
Proof.
  intros. unfold subq. repeat split; auto.
  - unfold Is_true, implb. destruct (qfresh q); reflexivity.
  - unfold n_sub; auto. - unfold n_sub; auto. - unfold n_sub; auto.
Qed.
Lemma Is_true_implb_iff : forall a b : bool, Is_true (implb a b) <-> (a = true -> b = true).
Proof. intros a b. unfold Is_true. destruct a; destruct b; simpl; intuition congruence. Qed.
Lemma subq_trans : forall a b c, a ⊑ b -> b ⊑ c -> a ⊑ c.
Proof.
  intros a b c [H1 [H2 [H3 H4]]] [G1 [G2 [G3 G4]]].
  unfold subq; simpl. split.
  - apply Is_true_implb_iff. intros H.
    apply Is_true_implb_iff in H1. apply Is_true_implb_iff in G1.
    apply G1. apply H1. exact H.
  - split.
    + unfold n_sub in *; intros x Hx; apply G2; apply H2; auto.
    + split.
      * unfold n_sub in *; intros x Hx; apply G3; apply H3; auto.
      * unfold n_sub in *; intros x Hx; apply G4; apply H4; auto.
Qed.

Lemma Q_lift_fresh : forall q, qfresh (Q_lift q) = Is_true (qfresh q).
Proof. intro. reflexivity. Qed.
Lemma Q_lift_fvs : forall q, qfvs (Q_lift q) = N_lift (qfvs q).
Proof. intro. reflexivity. Qed.
Lemma Q_lift_bvs : forall q, qbvs (Q_lift q) = N_lift (qbvs q).
Proof. intro. reflexivity. Qed.
Lemma Q_lift_locs : forall q, qlocs (Q_lift q) = N_lift (qlocs q).
Proof. intro. reflexivity. Qed.

Definition dfr (q : qual) : qual := (false, qfvs q, qbvs q, qlocs q).
Definition qsub (q q0 q1 : qual) : qual :=
  ( orb (orb (qfresh q) (andb (qfvs q 0) (qfresh q0))) (andb (qfvs q 1) (qfresh q1)),
    (fun x => qfvs q (S (S x))),
    qbvs q,
    (fun x => orb (orb (qlocs q x) (andb (qfvs q 0) (qlocs q0 x)))
                  (andb (qfvs q 1) (qlocs q1 x))) ).

Fixpoint tsub (T : ty) (U0 U1 : ty) (q0 q1 : qual) : ty :=
  match T with
  | TTop => TTop
  | TVar (varF i) => match i with 0 => U0 | 1 => U1 | S (S j) => TVar (varF j) end
  | TVar (varB i) => TVar (varB i)
  | TAll d1 d2 T1 T2 => TAll (qsub d1 q0 q1) (qsub d2 q0 q1) (tsub T1 U0 U1 q0 q1) (tsub T2 U0 U1 q0 q1)
  | TUnit => TUnit
  | TFun d1 d2 T1 T2 => TFun (qsub d1 q0 q1) (qsub d2 q0 q1) (tsub T1 U0 U1 q0 q1) (tsub T2 U0 U1 q0 q1)
  | TRef d T => TRef (qsub d q0 q1) (tsub T U0 U1 q0 q1)
  end.

Fixpoint tmsub (t : tm) (u0 u1 : tm) : tm :=
  match t with
  | ttabs t1 => ttabs (tmsub t1 u0 u1)
  | ttapp t1 => ttapp (tmsub t1 u0 u1)
  | tunit => tunit
  | tvar (varF i) => match i with 0 => u0 | 1 => u1 | S (S j) => tvar (varF j) end
  | tvar (varB i) => tvar (varB i)
  | tabs t1 => tabs (tmsub t1 u0 u1)
  | tapp t1 t2 => tapp (tmsub t1 u0 u1) (tmsub t2 u0 u1)
  | tloc l o => tloc l o
  | tref t1 => tref (tmsub t1 u0 u1)
  | trefat t1 t2 => trefat (tmsub t1 u0 u1) (tmsub t2 u0 u1)
  | tderef t1 => tderef (tmsub t1 u0 u1)
  | tassign t1 t2 => tassign (tmsub t1 u0 u1) (tmsub t2 u0 u1)
  | twithr t1 t2 => twithr (tmsub t1 u0 u1) (tmsub t2 u0 u1)
  | twithc l t1 => twithc l (tmsub t1 u0 u1)
  end.

Lemma qsub_fresh : forall q q0 q1,
  qfresh (qsub q q0 q1) = orb (orb (qfresh q) (andb (qfvs q 0) (qfresh q0))) (andb (qfvs q 1) (qfresh q1)).
Proof. intros. reflexivity. Qed.
Lemma qsub_fvs : forall q q0 q1, qfvs (qsub q q0 q1) = (fun x => qfvs q (S (S x))).
Proof. intros. reflexivity. Qed.
Lemma qsub_bvs : forall q q0 q1, qbvs (qsub q q0 q1) = qbvs q.
Proof. intros. reflexivity. Qed.
Lemma qsub_locs : forall q q0 q1,
  qlocs (qsub q q0 q1) = (fun x => orb (orb (qlocs q x) (andb (qfvs q 0) (qlocs q0 x))) (andb (qfvs q 1) (qlocs q1 x))).
Proof. intros. reflexivity. Qed.

Lemma qsub_closed : forall q q0 q1, qfvs q = n_empty -> qsub q q0 q1 = q.
Proof.
  intros q q0 q1 H. apply qual_ext.
  - rewrite qsub_fresh. rewrite H. unfold n_empty. simpl. repeat rewrite ?orb_false_r. reflexivity.
  - rewrite qsub_fvs. rewrite H. apply functional_extensionality. intro x. reflexivity.
  - rewrite qsub_bvs. reflexivity.
  - rewrite qsub_locs. rewrite H. unfold n_empty. simpl.
    apply functional_extensionality. intro x. repeat rewrite ?orb_false_r. reflexivity.
Qed.

Lemma qsub_marker0 : forall q0 q1, qfvs q0 = n_empty -> qbvs q0 = n_empty -> qfvs q1 = n_empty ->
  qsub ($!0) q0 q1 = q0.
Proof.
  intros q0 q1 H0 H0b H1. apply qual_ext.
  - rewrite qsub_fresh. unfold qfresh, qfvs, qbvs, qlocs, n_one. simpl.
    repeat rewrite ?orb_false_r. reflexivity.
  - rewrite qsub_fvs. rewrite H0. apply functional_extensionality. intro x.
    unfold qfvs, n_one, n_empty. simpl. reflexivity.
  - rewrite qsub_bvs. rewrite H0b. unfold qbvs, n_empty. reflexivity.
  - rewrite qsub_locs. apply functional_extensionality. intro x.
    unfold qfvs, n_one, qlocs, n_empty. simpl. repeat rewrite ?orb_false_r. reflexivity.
Qed.
Lemma qsub_marker1 : forall q0 q1, qfvs q0 = n_empty -> qfvs q1 = n_empty -> qbvs q1 = n_empty ->
  qsub ($!1) q0 q1 = q1.
Proof.
  intros q0 q1 H0 H1 H1b. apply qual_ext.
  - rewrite qsub_fresh. unfold qfresh, qfvs, qbvs, qlocs, n_one. simpl.
    repeat rewrite ?orb_false_r. reflexivity.
  - rewrite qsub_fvs. rewrite H1. apply functional_extensionality. intro x.
    unfold qfvs, n_one, n_empty. simpl. reflexivity.
  - rewrite qsub_bvs. rewrite H1b. unfold qbvs, n_empty. reflexivity.
  - rewrite qsub_locs. apply functional_extensionality. intro x.
    unfold qfvs, n_one, qlocs, n_empty. simpl. repeat rewrite ?orb_false_r. reflexivity.
Qed.

Lemma closed_Qual_weaken : forall b f l q b' f',
  closed_Qual b f l q -> b <= b' -> f <= f' -> closed_Qual b' f' l q.
Proof.
  intros b f l q b' f' [H1 [H2 H3]] Hb Hf. unfold closed_Qual. repeat split;
  unfold closed_Nats in *.
  - intros x Hx. apply H1 in Hx. lia.
  - intros x Hx. apply H2 in Hx. lia.
  - intros x Hx. apply H3 in Hx. lia.
Qed.
Lemma closed_ty_weaken : forall b f l T b' f',
  closed_ty b f l T -> b <= b' -> f <= f' -> closed_ty b' f' l T.
Proof.
  intros b f l T. revert b f l. induction T; intros b f l b' f' Hc Hb Hf; inversion Hc; subst.
  - apply cl_TTop.
  - apply cl_ttvarf. lia.
  - apply cl_ttvarb. lia.
  - eapply cl_TAll.
    + eapply closed_Qual_weaken with (b:=b) (f:=f); eauto.
    + eapply closed_Qual_weaken with (b:=S (S b)) (f:=f); eauto; lia.
    + eapply (IHT1 b f l b' f'); eauto.
    + eapply (IHT2 (S (S b)) f l (S (S b')) f'); eauto; lia.
  - apply cl_TUnit.
  - eapply cl_TFun.
    + eapply closed_Qual_weaken with (b:=b) (f:=f); eauto.
    + eapply closed_Qual_weaken with (b:=S (S b)) (f:=f); eauto; lia.
    + eapply (IHT1 b f l b' f'); eauto.
    + eapply (IHT2 (S (S b)) f l (S (S b')) f'); eauto; lia.
  - eapply cl_TRef.
    + eapply (IHT b f l b' f'); eauto.
    + eapply closed_Qual_weaken with (b:=b) (f:=f); eauto.
Qed.
Lemma closed_tm_weaken : forall b f l t b' f',
  closed_tm b f l t -> b <= b' -> f <= f' -> closed_tm b' f' l t.
Proof.
  intros b f l t b' f' H. revert b' f'.
  induction H; intros b' f' Hb Hf.
  - apply cl_ttabs. apply IHclosed_tm; lia.
  - apply cl_ttapp. apply IHclosed_tm; lia.
  - apply cl_tsct.
  - apply cl_tvarb. lia.
  - apply cl_tvarf. lia.
  - apply cl_tabs. apply IHclosed_tm; lia.
  - apply cl_tapp. apply IHclosed_tm1; lia. apply IHclosed_tm2; lia.
  - apply cl_tloc. lia.
  - apply cl_tref. apply IHclosed_tm; lia.
  - apply cl_trefat. apply IHclosed_tm1; lia. apply IHclosed_tm2; lia.
  - apply cl_tderef. apply IHclosed_tm; lia.
  - apply cl_tassign. apply IHclosed_tm1; lia. apply IHclosed_tm2; lia.
  - apply cl_twithr. apply IHclosed_tm1; lia. apply IHclosed_tm2; lia.
  - apply cl_twithc. lia. apply IHclosed_tm; lia.
Qed.

Lemma closed_qual_qfvs_empty : forall l (q : qual), closed_Qual 0 0 l (Q_lift q) -> qfvs q = n_empty.
Proof.
  intros l q [Hfvs [Hbvs Hlocs]]. unfold closed_Nats in *.
  apply functional_extensionality. intro x. destruct (qfvs q x) eqn:E; auto.
  exfalso. assert (x < 0) by exact (Hfvs x E). lia.
Qed.
Lemma closed_qual_qbvs_empty : forall l (q : qual), closed_Qual 0 0 l (Q_lift q) -> qbvs q = n_empty.
Proof.
  intros l q [Hfvs [Hbvs Hlocs]]. unfold closed_Nats in *.
  apply functional_extensionality. intro x. destruct (qbvs q x) eqn:E; auto.
  exfalso. assert (x < 0) by exact (Hbvs x E). lia.
Qed.
Lemma closed_qual_qlocs_bound : forall b f l (q : qual), closed_Qual b f l (Q_lift q) -> forall x, qlocs q x = true -> x < l.
Proof. intros b f l q [Hfvs [Hbvs Hlocs]] x Hx. exact (Hlocs x Hx). Qed.

Lemma qsub_closed_qual : forall b f l (q q0 q1 : qual),
  closed_Qual b (f+2) l (Q_lift q) -> closed_Qual 0 0 l (Q_lift q0) -> closed_Qual 0 0 l (Q_lift q1) ->
  closed_Qual b f l (Q_lift (qsub q q0 q1)).
Proof.
  intros b f l q q0 q1 Hq H0 H1. destruct Hq as [Hf [Hb Hl]].
  unfold closed_Qual. repeat split; unfold closed_Nats in *.
  - intros x Hx. rewrite Q_lift_fvs in Hx. rewrite qsub_fvs in Hx. apply Hf in Hx. lia.
  - intros x Hx. rewrite Q_lift_bvs in Hx. rewrite qsub_bvs in Hx. apply Hb in Hx. exact Hx.
  - intros x Hx. rewrite Q_lift_locs in Hx. change (qlocs (qsub q q0 q1) x = true) in Hx.
    rewrite qsub_locs in Hx. apply orb_true_iff in Hx. destruct Hx as [Hx|Hx].
    + apply orb_true_iff in Hx. destruct Hx as [Hx|Hx].
      * apply Hl in Hx. exact Hx.
      * apply andb_true_iff in Hx. destruct Hx as [_ Hx]. pose proof (closed_qual_qlocs_bound 0 0 l q0 H0 x Hx). lia.
    + apply andb_true_iff in Hx. destruct Hx as [_ Hx]. pose proof (closed_qual_qlocs_bound 0 0 l q1 H1 x Hx). lia.
Qed.

Lemma qsub_fresh_mono : forall fa fb fa0 fb0 fa1 fb1 f0 f1,
  (fa = true -> fb = true) -> (fa0 = true -> fb0 = true) -> (fa1 = true -> fb1 = true) ->
  orb (orb fa (andb fa0 f0)) (andb fa1 f1) = true -> orb (orb fb (andb fb0 f0)) (andb fb1 f1) = true.
Proof. intros. destruct fa, fb, fa0, fb0, fa1, fb1, f0, f1; simpl in *; auto; try discriminate; try (exfalso; auto). Qed.
Lemma qsub_locs_mono : forall la lb l0 l1 fa0 fb0 fa1 fb1,
  (la = true -> lb = true) -> (fa0 = true -> fb0 = true) -> (fa1 = true -> fb1 = true) ->
  orb (orb la (andb fa0 l0)) (andb fa1 l1) = true -> orb (orb lb (andb fb0 l0)) (andb fb1 l1) = true.
Proof. intros. destruct la, lb, l0, l1, fa0, fb0, fa1, fb1; simpl in *; auto; try discriminate; try (exfalso; auto). Qed.

Lemma qsub_subq : forall a b q0 q1, Subq (Q_lift a) (Q_lift b) ->
  Subq (Q_lift (qsub a q0 q1)) (Q_lift (qsub b q0 q1)).
Proof.
  intros a b q0 q1 [Hf [Hfa [Hba Hla]]]. unfold Subq. repeat split.
  - intros Hx. rewrite Q_lift_fresh in Hx. apply Is_true_eq_true in Hx.
    rewrite qsub_fresh in Hx. rewrite Q_lift_fresh. apply Is_true_eq_left. rewrite qsub_fresh.
    eapply qsub_fresh_mono.
    + intros H. apply Is_true_eq_true. apply Hf. rewrite Q_lift_fresh. apply Is_true_eq_left. exact H.
    + intros H. apply Hfa. exact H.
    + intros H. apply Hfa. exact H.
    + exact Hx.
  - intros x Hx. rewrite Q_lift_fvs in Hx. change (qfvs a (S (S x)) = true) in Hx.
    rewrite Q_lift_fvs. change (qfvs b (S (S x)) = true). apply Hfa. exact Hx.
  - intros x Hx. rewrite Q_lift_bvs in Hx. change (qbvs a x = true) in Hx.
    rewrite Q_lift_bvs. change (qbvs b x = true). apply Hba. exact Hx.
  - intros x Hx. rewrite Q_lift_locs in Hx. change (qlocs (qsub a q0 q1) x = true) in Hx.
    rewrite qsub_locs in Hx. rewrite Q_lift_locs. change (qlocs (qsub b q0 q1) x = true).
    rewrite qsub_locs. eapply qsub_locs_mono.
    + intros H; apply Hla; exact H.
    + intros H; apply Hfa; exact H.
    + intros H; apply Hfa; exact H.
    + exact Hx.
Qed.

Lemma qsub_qor : forall a b q0 q1,
  qsub (qor a b) q0 q1 = qor (qsub a q0 q1) (qsub b q0 q1).
Proof.
  intros a b q0 q1. apply qual_ext.
  - unfold qsub, qor, qfresh, qfvs, qbvs, qlocs, n_or. cbn.
    remember (fst (fst (fst a))) as A eqn:EA.
    remember (fst (fst (fst b))) as B eqn:EB.
    remember (snd (fst (fst a)) 0) as a0 eqn:Ea0.
    remember (snd (fst (fst b)) 0) as b0 eqn:Eb0.
    remember (snd (fst (fst a)) 1) as a1 eqn:Ea1.
    remember (snd (fst (fst b)) 1) as b1 eqn:Eb1.
    remember (fst (fst (fst q0))) as F0 eqn:EF0.
    remember (fst (fst (fst q1))) as F1 eqn:EF1.
    destruct A, B, a0, b0, a1, b1, F0, F1; reflexivity.
  - unfold qsub, qor, qfvs, n_or. cbn. apply functional_extensionality. intro x. reflexivity.
  - unfold qsub, qor, qbvs, n_or. cbn. apply functional_extensionality. intro x. reflexivity.
  - unfold qsub, qor, qfresh, qfvs, qbvs, qlocs, n_or. cbn.
    apply functional_extensionality. intro x.
    remember (fst (fst (fst a))) as A eqn:EA.
    remember (fst (fst (fst b))) as B eqn:EB.
    remember (snd (fst (fst a)) 0) as a0 eqn:Ea0.
    remember (snd (fst (fst b)) 0) as b0 eqn:Eb0.
    remember (snd (fst (fst a)) 1) as a1 eqn:Ea1.
    remember (snd (fst (fst b)) 1) as b1 eqn:Eb1.
    remember (snd a x) as La eqn:ELa.
    remember (snd b x) as Lb eqn:ELb.
    remember (snd q0 x) as L0 eqn:EL0.
    remember (snd q1 x) as L1 eqn:EL1.
    destruct A, B, a0, b0, a1, b1, La, Lb, L0, L1; reflexivity.
Qed.

Lemma qsub_open_qual : forall k d' d q0 q1,
  qsub (open_qual k d' d) q0 q1 = open_qual k (qsub d' q0 q1) (qsub d q0 q1).
Proof.
  intros k d' d q0 q1. unfold open_qual.
  destruct (qbvs d k) eqn:E.
  - rewrite qsub_qor.
    assert (Hbase : qsub (qfresh d, qfvs d, n_diff (qbvs d) (n_one k), qlocs d) q0 q1 =
      (qfresh (qsub d q0 q1), qfvs (qsub d q0 q1),
       n_diff (qbvs (qsub d q0 q1)) (n_one k), qlocs (qsub d q0 q1))).
    { apply qual_ext.
      - rewrite qsub_fresh. reflexivity.
      - rewrite qsub_fvs. rewrite qsub_fvs. reflexivity.
      - rewrite qsub_bvs. rewrite qsub_bvs. reflexivity.
      - rewrite qsub_locs. rewrite qsub_locs. reflexivity. }
    rewrite qsub_bvs. rewrite E. simpl. rewrite Hbase. reflexivity.
  - rewrite qsub_bvs. rewrite E. simpl. reflexivity.
Qed.

Lemma open_rec_tm_varB_lt : forall k u x,
  x < k -> open_rec_tm k u (tvar (varB x)) = tvar (varB x).
Proof.
  intros. cbn [open_rec_tm]. destruct (Nat.eqb k x) eqn:E; auto.
  apply Nat.eqb_eq in E. lia.
Qed.

Lemma closed_tm_open_id : forall t b f L,
  closed_tm b f L t -> forall k, b <= k -> forall u, open_rec_tm k u t = t.
Proof.
  intros t. induction t; intros b f L Hc k Hk u; inversion Hc; subst.
  - cbn [open_rec_tm]. f_equal. eapply IHt; eauto; lia.
  - cbn [open_rec_tm]. f_equal. eapply IHt; eauto.
  - cbn [open_rec_tm]. reflexivity.
  - cbn [open_rec_tm]. eapply open_rec_tm_varB_lt. lia.
  - cbn [open_rec_tm]. reflexivity.
  - cbn [open_rec_tm]. f_equal. eapply IHt; eauto; lia.
  - cbn [open_rec_tm]. f_equal. eapply IHt1; eauto. eapply IHt2; eauto.
  - cbn [open_rec_tm]. reflexivity.
  - cbn [open_rec_tm]. f_equal. eapply IHt; eauto.
  - cbn [open_rec_tm]. f_equal. eapply IHt; eauto.
  - cbn [open_rec_tm]. f_equal. eapply IHt1; eauto. eapply IHt2; eauto.
  - cbn [open_rec_tm]. f_equal. eapply IHt1; eauto. eapply IHt2; eauto.
  - cbn [open_rec_tm]. f_equal. eapply IHt1; eauto. eapply IHt2; eauto; lia.
  - cbn [open_rec_tm]. f_equal. eapply IHt; eauto.
Qed.

Lemma tmsub_if : forall (b:bool) u v u0 u1,
  tmsub (if b then u else v) u0 u1 = if b then tmsub u u0 u1 else tmsub v u0 u1.
Proof. intros. destruct b; reflexivity. Qed.

Lemma open_rec_tm_varB : forall k u x,
  open_rec_tm k u (tvar (varB x)) = if Nat.eqb k x then u else tvar (varB x).
Proof. intros. reflexivity. Qed.

Lemma tmsub_open_rec_tm : forall t k u u0 u1,
  closed_tm 0 0 0 u0 -> closed_tm 0 0 0 u1 ->
  tmsub (open_rec_tm k u t) u0 u1 =
  open_rec_tm k (tmsub u u0 u1) (tmsub t u0 u1).
Proof.
  intros t. induction t; intros k u u0 u1 H0 H1.
  - simpl. f_equal. apply IHt; auto.
  - simpl. f_equal. apply IHt; auto.
  - reflexivity.
  - destruct v as [i|i].
    + destruct i as [|[|j]]; simpl.
      * rewrite closed_tm_open_id with (t:=u0) (b:=0) (f:=0) (L:=0); auto; lia.
      * rewrite closed_tm_open_id with (t:=u1) (b:=0) (f:=0) (L:=0); auto; lia.
      * reflexivity.
    + rewrite open_rec_tm_varB. rewrite tmsub_if. reflexivity.
  - simpl. f_equal. apply IHt; auto.
  - simpl. f_equal. apply IHt1; auto. apply IHt2; auto.
  - reflexivity.
  - simpl. f_equal. apply IHt; auto.
  - simpl. f_equal. apply IHt; auto.
  - simpl. f_equal. apply IHt1; auto. apply IHt2; auto.
  - simpl. f_equal. apply IHt1; auto. apply IHt2; auto.
  - simpl. f_equal. apply IHt1; auto. apply IHt2; auto.
  - simpl. f_equal. apply IHt; auto.
Qed.

Lemma open_qual_closed : forall b f L (q:qual),
  closed_Qual b f L (Q_lift q) -> forall k, b <= k -> forall d', open_qual k d' q = q.
Proof.
  intros b f L q Hc k Hk d'. destruct Hc as [Hf [Hb Hl]].
  unfold open_qual. unfold closed_Nats in Hb.
  destruct (qbvs q k) eqn:E.
  - exfalso. assert (k < b) by exact (Hb k E). lia.
  - reflexivity.
Qed.

Lemma open_rec_ty_varB_lt : forall k U d x,
  x < k -> open_rec_ty k U d (TVar (varB x)) = TVar (varB x).
Proof.
  intros. cbn [open_rec_ty]. destruct (Nat.eqb k x) eqn:E; auto.
  apply Nat.eqb_eq in E. lia.
Qed.

Lemma closed_ty_open_id : forall T b f L,
  closed_ty b f L T -> forall k, b <= k -> forall U d, open_rec_ty k U d T = T.
Proof.
  intros T. induction T; intros b f L Hc k Hk U d; inversion Hc; subst.
  - cbn [open_rec_ty]. reflexivity.
  - cbn [open_rec_ty]. reflexivity.
  - cbn [open_rec_ty]. eapply open_rec_ty_varB_lt. lia.
  - cbn [open_rec_ty]. f_equal.
    + erewrite open_qual_closed; eauto.
    + erewrite open_qual_closed; eauto. lia.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto. lia.
  - cbn [open_rec_ty]. reflexivity.
  - cbn [open_rec_ty]. f_equal.
    + erewrite open_qual_closed; eauto.
    + erewrite open_qual_closed; eauto. lia.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto. lia.
  - cbn [open_rec_ty]. f_equal.
    + erewrite open_qual_closed; eauto.
    + eapply IHT; eauto.
  Unshelve.
  all: try reflexivity; try assumption; try lia.
Qed.

Lemma tsub_if : forall (b:bool) U V U0 U1 q0 q1,
  tsub (if b then U else V) U0 U1 q0 q1 = if b then tsub U U0 U1 q0 q1 else tsub V U0 U1 q0 q1.
Proof. intros. destruct b; reflexivity. Qed.

Lemma open_rec_ty_varB_eq : forall k U d x,
  open_rec_ty k U d (TVar (varB x)) = if Nat.eqb k x then U else TVar (varB x).
Proof. intros. reflexivity. Qed.

Lemma splice_ty_if : forall n (b:bool) U V,
  splice_ty n (if b then U else V) = if b then splice_ty n U else splice_ty n V.
Proof. intros. destruct b; reflexivity. Qed.
Lemma open_rec_ty_varF : forall k U d x, open_rec_ty k U d (TVar (varF x)) = TVar (varF x).
Proof. intros. reflexivity. Qed.
Lemma open_rec_ty_varB : forall k U d x,
  open_rec_ty k U d (TVar (varB x)) = if Nat.eqb k x then U else TVar (varB x).
Proof. intros. reflexivity. Qed.

Lemma open_rec_ty_splice_varF : forall k U d n i,
  open_rec_ty k U d (splice_ty n (TVar (varF i))) = splice_ty n (TVar (varF i)).
Proof.
  intros. destruct (le_lt_dec n i) as [Hle|Hlt].
  - assert (Hs: splice_ty n (TVar (varF i)) = TVar (varF (S i))).
    { cbn [splice_ty]. destruct (le_lt_dec n i) as [H1|H2]; [reflexivity|lia]. }
    rewrite Hs. apply open_rec_ty_varF.
  - assert (Hs: splice_ty n (TVar (varF i)) = TVar (varF i)).
    { cbn [splice_ty]. destruct (le_lt_dec n i) as [H1|H2]; [lia|reflexivity]. }
    rewrite Hs. apply open_rec_ty_varF.
Qed.


Lemma tsub_open_rec_ty : forall T k U d U0 U1 s0 s1,
  closed_ty 0 0 0 U0 -> closed_ty 0 0 0 U1 ->
  tsub (open_rec_ty k U d T) U0 U1 s0 s1 =
  open_rec_ty k (tsub U U0 U1 s0 s1) (qsub d s0 s1) (tsub T U0 U1 s0 s1).
Proof.
  intros T. induction T; intros k U d U0 U1 s0 s1 H0 H1.
  - cbn [open_rec_ty tsub]. reflexivity.
  - destruct v as [i|i].
    + destruct i as [|[|j]]; cbn [open_rec_ty tsub].
      * rewrite closed_ty_open_id with (T:=U0) (b:=0) (f:=0) (L:=0); auto; lia.
      * rewrite closed_ty_open_id with (T:=U1) (b:=0) (f:=0) (L:=0); auto; lia.
      * reflexivity.
    + cbn [open_rec_ty tsub]. rewrite tsub_if. cbn [tsub]. reflexivity.
  - cbn [open_rec_ty tsub]. f_equal.
    + rewrite qsub_open_qual. reflexivity.
    + rewrite qsub_open_qual. reflexivity.
    + apply IHT1; auto.
    + apply IHT2; auto.
  - cbn [open_rec_ty tsub]. reflexivity.
  - cbn [open_rec_ty tsub]. f_equal.
    + rewrite qsub_open_qual. reflexivity.
    + rewrite qsub_open_qual. reflexivity.
    + apply IHT1; auto.
    + apply IHT2; auto.
  - cbn [open_rec_ty tsub]. f_equal.
    + rewrite qsub_open_qual. reflexivity.
    + apply IHT; auto.
Qed.

Lemma closed_qual_fvs_empty_any_b : forall b L (q:qual),
  closed_Qual b 0 L (Q_lift q) -> qfvs q = n_empty.
Proof.
  intros b L q [Hf [Hb Hl]]. unfold closed_Nats in *.
  apply functional_extensionality. intro x. destruct (qfvs q x) eqn:E; auto.
  exfalso. assert (x < 0) by exact (Hf x E). lia.
Qed.

Lemma tsub_closed_ty : forall T b L, closed_ty b 0 L T ->
  forall U0 U1 s0 s1, tsub T U0 U1 s0 s1 = T.
Proof.
  intros T. induction T; intros b L Hc U0 U1 s0 s1; inversion Hc; subst.
  - reflexivity.
  - exfalso. lia.
  - reflexivity.
  - cbn [tsub]. f_equal.
    + apply qsub_closed. apply closed_qual_fvs_empty_any_b with (b:=b) (L:=L). assumption.
    + apply qsub_closed. apply closed_qual_fvs_empty_any_b with (b:=S (S b)) (L:=L). assumption.
    + apply (IHT1 b L); auto.
    + apply (IHT2 (S (S b)) L); auto.
  - reflexivity.
  - cbn [tsub]. f_equal.
    + apply qsub_closed. apply closed_qual_fvs_empty_any_b with (b:=b) (L:=L). assumption.
    + apply qsub_closed. apply closed_qual_fvs_empty_any_b with (b:=S (S b)) (L:=L). assumption.
    + apply (IHT1 b L); auto.
    + apply (IHT2 (S (S b)) L); auto.
  - cbn [tsub]. f_equal.
    + apply qsub_closed. apply closed_qual_fvs_empty_any_b with (b:=b) (L:=L). assumption.
    + apply (IHT b L); auto.
Qed.

Lemma tsub_closed_ty_gen : forall T b f L, closed_ty b (f+2) L T ->
  forall U0 U1 s0 s1,
    closed_ty 0 0 L U0 -> closed_ty 0 0 L U1 ->
    closed_Qual 0 0 L (Q_lift s0) -> closed_Qual 0 0 L (Q_lift s1) ->
    closed_ty b f L (tsub T U0 U1 s0 s1).
Proof.
  intros T. induction T; intros b f L Hc U0 U1 s0 s1 H0 H1 G0 G1; inversion Hc; subst.
  - apply cl_TTop.
  - match goal with |- context[TVar (varF ?x)] => destruct x as [|[|j]]; cbn [tsub] end.
    + eapply closed_ty_weaken; eauto; lia.
    + eapply closed_ty_weaken; eauto; lia.
    + apply cl_ttvarf. lia.
  - cbn [tsub]. apply cl_ttvarb. lia.
  - cbn [tsub]. eapply cl_TAll.
    + eapply qsub_closed_qual; eauto.
    + eapply qsub_closed_qual; eauto.
    + eapply (IHT1 b f L); eauto.
    + eapply (IHT2 (S (S b)) f L); eauto.
  - apply cl_TUnit.
  - cbn [tsub]. eapply cl_TFun.
    + eapply qsub_closed_qual; eauto.
    + eapply qsub_closed_qual; eauto.
    + eapply (IHT1 b f L); eauto.
    + eapply (IHT2 (S (S b)) f L); eauto.
  - cbn [tsub]. eapply cl_TRef.
    + eapply (IHT b f L); eauto.
    + exact (qsub_closed_qual b f L q s0 s1 H7 G0 G1).
Qed.

Definition csub (U0 U1 : ty) (s0 s1 : qual) (e : binding*bool*ty*qual) : binding*bool*ty*qual :=
  (fst (fst (fst e)), snd (fst (fst e)), tsub (snd (fst e)) U0 U1 s0 s1, qsub (snd e) s0 s1).

Definition ctxsub (D : tenv) (U0 U1 : ty) (s0 s1 : qual) : tenv := map (csub U0 U1 s0 s1) D.

Lemma ctxsub_length : forall D U0 U1 s0 s1,
  length (ctxsub D U0 U1 s0 s1) = length D.
Proof. intros. unfold ctxsub. apply map_length. Qed.

Lemma ctxsub_indexr : forall D U0 U1 s0 s1 x e,
  indexr x D = Some e ->
  indexr x (ctxsub D U0 U1 s0 s1) = Some (csub U0 U1 s0 s1 e).
Proof.
  intros D. induction D as [|a D' IH]; intros U0 U1 s0 s1 x e H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb x (length D')) eqn:E; [injection H as -> |].
    + unfold ctxsub. simpl. rewrite map_length. rewrite E. reflexivity.
    + unfold ctxsub in *. simpl. rewrite map_length. rewrite E. apply IH. exact H.
Qed.

Lemma qsub_closed_qual_same : forall b f L (q s0 s1 : qual),
  closed_Qual b f L (Q_lift q) ->
  closed_Qual 0 0 L (Q_lift s0) -> closed_Qual 0 0 L (Q_lift s1) ->
  closed_Qual b f L (Q_lift (qsub q s0 s1)).
Proof.
  intros b f L q s0 s1 Hq H0 H1. destruct Hq as [Hf [Hb Hl]].
  unfold closed_Qual. repeat split; unfold closed_Nats in *.
  - intros x Hx. rewrite Q_lift_fvs in Hx. rewrite qsub_fvs in Hx.
    apply Hf in Hx. lia.
  - intros x Hx. rewrite Q_lift_bvs in Hx. rewrite qsub_bvs in Hx. apply Hb in Hx. exact Hx.
  - intros x Hx. rewrite Q_lift_locs in Hx. change (qlocs (qsub q s0 s1) x = true) in Hx.
    rewrite qsub_locs in Hx. apply orb_true_iff in Hx. destruct Hx as [Hx|Hx].
    + apply orb_true_iff in Hx. destruct Hx as [Hx|Hx].
      * apply Hl in Hx. exact Hx.
      * apply andb_true_iff in Hx. destruct Hx as [_ Hx]. pose proof (closed_qual_qlocs_bound 0 0 L s0 H0 x Hx). lia.
    + apply andb_true_iff in Hx. destruct Hx as [_ Hx]. pose proof (closed_qual_qlocs_bound 0 0 L s1 H1 x Hx). lia.
Qed.

Definition no_lookup (G:tenv) : Prop := forall x v, indexr x G = Some v -> False.

Lemma no_lookup_nil : no_lookup [].
Proof. intros x v H. cbn in H. discriminate H. Qed.

Lemma stp_target_TFun_nl : forall G Sig T1 d1 T2 d2,
  stp G Sig T1 d1 T2 d2 -> no_lookup G ->
  forall a b c e, T2 = TFun a b c e -> exists a' b' c' e', T1 = TFun a' b' c' e'.
Proof.
  intros G Sig T1 d1 T2 d2 H. induction H; intros Hnl a b c e Heq.
  - discriminate Heq.
  - exfalso. eapply Hnl; eauto.
  - exfalso. eapply Hnl; eauto.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - exists d1, d2, T1, T2. reflexivity.
  - destruct (IHstp2 Hnl a b c e Heq) as [a' [b' [c' [e' H2]]]].
    eapply IHstp1. exact Hnl. exact H2.
Qed.

Lemma stp_target_TAll_nl : forall G Sig T1 d1 T2 d2,
  stp G Sig T1 d1 T2 d2 -> no_lookup G ->
  forall a b c e, T2 = TAll a b c e -> exists a' b' c' e', T1 = TAll a' b' c' e'.
Proof.
  intros G Sig T1 d1 T2 d2 H. induction H; intros Hnl a b c e Heq.
  - discriminate Heq.
  - exfalso. eapply Hnl; eauto.
  - exfalso. eapply Hnl; eauto.
  - exists d1, d2, T1, T2. reflexivity.
  - discriminate Heq.
  - discriminate Heq.
  - discriminate Heq.
  - destruct (IHstp2 Hnl a b c e Heq) as [a' [b' [c' [e' H2]]]].
    eapply IHstp1. exact Hnl. exact H2.
Qed.

Lemma stp_target_TRef_nl : forall G Sig T1 d1 T2 d2,
  stp G Sig T1 d1 T2 d2 -> no_lookup G ->
  forall q U, T2 = TRef q U -> exists q' U', T1 = TRef q' U'.
Proof.
  intros G Sig T1 d1 T2 d2 H. induction H; intros Hnl q U Heq.
  - discriminate Heq.
  - exfalso. eapply Hnl; eauto.
  - exfalso. eapply Hnl; eauto.
  - discriminate Heq.
  - discriminate Heq.
  - exists q1, T1. reflexivity.
  - discriminate Heq.
  - destruct (IHstp2 Hnl q U Heq) as [q' [U' H2]].
    eapply IHstp1. exact Hnl. exact H2.
Qed.

Lemma canonical_TFun : forall G Sig v phi T d, has_type G phi Sig v T d ->
  no_lookup G -> value v ->
  forall b0 b1 T1 T2, T = TFun b0 b1 T1 T2 -> exists t, v = tabs t.
Proof.
  intros G Sig v phi T d H.
  dependent induction H; intros Hnl Hv a0 a1 P Q Heq.
  - discriminate Heq.
  - inversion Hv.
  - inversion Hv.
  - discriminate Heq.
  - inversion Hv.
  - exists t. reflexivity.
  - inversion Hv.
  - inversion Hv.
  - discriminate Heq.
  - inversion Hv.
  - inversion Hv.
  - inversion Hv.
  - inversion Hv.
  - destruct (stp_target_TFun_nl _ _ _ _ _ _ H0 Hnl a0 a1 P Q Heq)
      as [a' [b' [c' [e' Hs]]]].
    eapply IHhas_type. exact Hnl. exact Hv. exact Hs.
  - inversion Hv.
  - inversion Hv.
Qed.

Lemma canonical_TAll : forall G Sig v phi T d, has_type G phi Sig v T d ->
  no_lookup G -> value v ->
  forall a0 a1 P Q, T = TAll a0 a1 P Q -> exists t, v = ttabs t.
Proof.
  intros G Sig v phi T d H.
  dependent induction H; intros Hnl Hv a0 a1 P Q Heq.
  - exists t. reflexivity.
  - inversion Hv.
  - inversion Hv.
  - discriminate Heq.
  - inversion Hv.
  - discriminate Heq.
  - inversion Hv.
  - inversion Hv.
  - discriminate Heq.
  - inversion Hv.
  - inversion Hv.
  - inversion Hv.
  - inversion Hv.
  - destruct (stp_target_TAll_nl _ _ _ _ _ _ H0 Hnl a0 a1 P Q Heq)
      as [a' [b' [c' [e' Hs]]]].
    eapply IHhas_type. exact Hnl. exact Hv. exact Hs.
  - inversion Hv.
  - inversion Hv.
Qed.

Lemma canonical_TRef : forall G Sig v phi T d, has_type G phi Sig v T d ->
  no_lookup G -> value v ->
  forall u0 u1, T = TRef u0 u1 -> exists l o, v = tloc l o.
Proof.
  intros G Sig v phi T d H.
  dependent induction H; intros Hnl Hv u0 u1 Heq.
  - discriminate Heq.
  - inversion Hv.
  - inversion Hv.
  - discriminate Heq.
  - inversion Hv.
  - discriminate Heq.
  - inversion Hv.
  - inversion Hv.
  - exists l, o. reflexivity.
  - inversion Hv.
  - inversion Hv.
  - inversion Hv.
  - inversion Hv.
  - destruct (stp_target_TRef_nl _ _ _ _ _ _ H0 Hnl u0 u1 Heq)
      as [q' [U' Hs]].
    eapply IHhas_type. exact Hnl. exact Hv. exact Hs.
  - inversion Hv.
  - inversion Hv.
Qed.

Lemma value_local_locs : forall v, value v -> wf_step v -> local_locs v = ∅.
Proof.
  intros v Hv Hw. destruct Hv; simpl in *; auto.
Qed.

Lemma wf_step_value_local_locs : forall v, value v -> wf_step v -> local_locs v = ∅.
Proof. intros. eapply value_local_locs; eauto. Qed.

Lemma indexr_Some_lt : forall {X} (n:nat) (l:list X) a, indexr n l = Some a -> n < length l.
Proof.
  intros X n l. induction l as [|x xs IH]; intros a H; simpl in *; [discriminate|].
  destruct (Nat.eqb n (length xs)) eqn:E.
  - apply Nat.eqb_eq in E. lia.
  - apply IH in H. simpl. lia.
Qed.
Lemma indexr_ge_None : forall {X} (n:nat) (l:list X), n >= length l -> indexr n l = None.
Proof.
  intros X n l. induction l as [|x xs IH]; intros H; simpl in *; [reflexivity|].
  destruct (Nat.eqb n (length xs)) eqn:E.
  - apply Nat.eqb_eq in E. lia.
  - apply IH. lia.
Qed.
Lemma indexr_cons : forall {X} (x:X) (l:list X) n,
  indexr n (x::l) = if Nat.eqb n (length l) then Some x else indexr n l.
Proof. intros. reflexivity. Qed.
Lemma indexr_app_suffix_0 : forall {X} (D:list X) a b, indexr 0 (D ++ [a;b]) = Some b.
Proof.
  intros X D. induction D as [|d D' IH]; intros a b.
  - reflexivity.
  - change (indexr 0 (d :: (D' ++ [a;b])) = Some b). rewrite indexr_cons.
    rewrite (proj2 (Nat.eqb_neq 0 (length (D' ++ [a;b])))); [simpl; apply IH | rewrite app_length; simpl; lia].
Qed.
Lemma indexr_app_suffix_1 : forall {X} (D:list X) a b, indexr 1 (D ++ [a;b]) = Some a.
Proof.
  intros X D. induction D as [|d D' IH]; intros a b.
  - reflexivity.
  - change (indexr 1 (d :: (D' ++ [a;b])) = Some a). rewrite indexr_cons.
    rewrite (proj2 (Nat.eqb_neq 1 (length (D' ++ [a;b])))); [simpl; apply IH | rewrite app_length; simpl; lia].
Qed.
Lemma indexr_app_suffix_S : forall {X} (D:list X) a b i,
  indexr (S (S i)) (D ++ [a;b]) = indexr i D.
Proof.
  intros X D. induction D as [|d D' IH]; intros a b i.
  - rewrite indexr_ge_None; [|simpl; lia]. symmetry. apply indexr_ge_None. simpl. lia.
  - change (indexr (S (S i)) (d :: (D' ++ [a;b])) = indexr i (d :: D')).
    rewrite indexr_cons. rewrite indexr_cons.
    destruct (Nat.eqb i (length D')) eqn:E.
    + assert (Heq: Nat.eqb (S (S i)) (length (D' ++ [a;b])) = true).
      { apply Nat.eqb_eq. rewrite app_length. simpl. pose proof (proj1 (Nat.eqb_eq i (length D')) E). lia. }
      rewrite Heq. simpl. reflexivity.
    + assert (Heq: Nat.eqb (S (S i)) (length (D' ++ [a;b])) = false).
      { apply Nat.eqb_neq. rewrite app_length. simpl. pose proof (proj1 (Nat.eqb_neq i (length D')) E). lia. }
      rewrite Heq. simpl. apply IH.
Qed.
Lemma sindexr_cons : forall {X} (a:list X) (s:list (list X)) l o,
  sindexr l o (a :: s) = if Nat.eqb l (length s) then indexr o a else sindexr l o s.
Proof. intros. reflexivity. Qed.
Lemma sindexr_lt_head : forall {X} (a:list X) (s:list (list X)) l o,
  l < length s -> sindexr l o (a :: s) = sindexr l o s.
Proof.
  intros. rewrite sindexr_cons. replace (Nat.eqb l (length s)) with false. reflexivity.
  symmetry. apply Nat.eqb_neq. lia.
Qed.
Lemma sindexr_head : forall {X} (a:list X) (s:list (list X)) o,
  sindexr (length s) o (a :: s) = indexr o a.
Proof. intros. rewrite sindexr_cons. rewrite Nat.eqb_refl. reflexivity. Qed.
Lemma sindexr_lookup : forall {X} (s:list (list X)) l o,
  sindexr l o s = match indexr l s with Some c => indexr o c | None => None end.
Proof.
  intros X s. induction s as [|a s' IH]; intros l o; simpl.
  - reflexivity.
  - destruct (Nat.eqb l (length s')) eqn:E; simpl; [reflexivity | apply IH].
Qed.
Lemma sindexr_Some_lt : forall {X} (s:list (list X)) l o x,
  sindexr l o s = Some x -> l < length s.
Proof.
  intros. rewrite sindexr_lookup in H. destruct (indexr l s) as [c|] eqn:E; [|discriminate].
  eapply indexr_Some_lt; eauto.
Qed.
Lemma sindexr'_cons : forall {X} (a:option (list X)) (s:list (option (list X))) l o,
  sindexr' l o (a :: s) = if Nat.eqb l (length s) then indexr' o a else sindexr' l o s.
Proof. intros. reflexivity. Qed.
Lemma sindexr'_lookup : forall {X} (s:list (option (list X))) l o,
  sindexr' l o s = match indexr l s with Some c => indexr' o c | None => None end.
Proof.
  intros X s. induction s as [|a s' IH]; intros l o; simpl.
  - reflexivity.
  - destruct (Nat.eqb l (length s')) eqn:E; simpl; [reflexivity | apply IH].
Qed.
Lemma sindexr'_Some_lt : forall {X} (s:list (option (list X))) l o x,
  sindexr' l o s = Some x -> l < length s.
Proof.
  intros. rewrite sindexr'_lookup in H. destruct (indexr l s) as [c|] eqn:E; [|discriminate].
  eapply indexr_Some_lt; eauto.
Qed.
Lemma length_update : forall {A} (s:list A) l (v:A), length (update s l v) = length s.
Proof. intros A s. induction s as [|x xs IH]; intros l v; simpl; auto. destruct (Nat.eqb l (length xs)); simpl; auto. Qed.
Lemma length_supdate : forall {A} (s:list (option (list A))) l o (v:A),
  length (supdate s l o v) = length s.
Proof. intros A s. induction s as [|x xs IH]; intros l o v; simpl; auto. destruct (Nat.eqb l (length xs)); simpl; auto. Qed.

Lemma update_cons : forall {A} (x:A) (xs:list A) l (v:A),
  update (x::xs) l v = if Nat.eqb l (length xs) then (v::xs) else (x :: update xs l v).
Proof. intros. reflexivity. Qed.

Lemma indexr_update_same : forall {A} (s:list A) l (v:A) old,
  indexr l s = Some old -> indexr l (update s l v) = Some v.
Proof.
  intros A s. induction s as [|x xs IH]; intros l v old H.
  - simpl in H. discriminate.
  - rewrite indexr_cons in H. rewrite update_cons.
    destruct (Nat.eqb l (length xs)) eqn:E.
    + rewrite indexr_cons. rewrite E. simpl. reflexivity.
    + rewrite indexr_cons. rewrite length_update. rewrite E. simpl.
      eapply IH. simpl in H. exact H.
Qed.

Lemma update_preserves_other : forall {A} (s:list A) l (v:A) k old,
  indexr k s = Some old -> k <> l -> indexr k (update s l v) = Some old.
Proof.
  intros A s. induction s as [|x xs IH]; intros l v k old H Hne.
  - simpl in H. discriminate.
  - rewrite indexr_cons in H. rewrite update_cons.
    destruct (Nat.eqb k (length xs)) eqn:Ek; destruct (Nat.eqb l (length xs)) eqn:El.
    + exfalso. apply Hne. apply Nat.eqb_eq in Ek. apply Nat.eqb_eq in El. lia.
    + rewrite indexr_cons. rewrite length_update. rewrite Ek. simpl.
      simpl in H. injection H as Hx. subst old. reflexivity.
    + rewrite indexr_cons. rewrite Ek. simpl. simpl in H. exact H.
    + rewrite indexr_cons. rewrite length_update. rewrite Ek. simpl.
      eapply IH. simpl in H. exact H. exact Hne.
Qed.

Lemma update_preserves_none : forall {A} (s:list A) l (v:A) k,
  indexr k s = None -> k <> l -> indexr k (update s l v) = None.
Proof.
  intros A s. induction s as [|x xs IH]; intros l v k H Hne.
  - reflexivity.
  - rewrite indexr_cons in H. rewrite update_cons.
    destruct (Nat.eqb k (length xs)) eqn:Ek; destruct (Nat.eqb l (length xs)) eqn:El.
    + unfold Is_true in H. inversion H.
    + unfold Is_true in H. inversion H.
    + rewrite indexr_cons. rewrite Ek. simpl. simpl in H. exact H.
    + rewrite indexr_cons. rewrite length_update. rewrite Ek. simpl.
      eapply IH. simpl in H. exact H. exact Hne.
Qed.

Lemma indexr'_None : forall {X} o, @indexr' X o None = None.
Proof. intros. reflexivity. Qed.
Lemma indexr'_Some : forall {X} o (c:list X), indexr' o (Some c) = indexr o c.
Proof. intros. reflexivity. Qed.
Lemma update'_None : forall {A} o (v:A), update' None o v = None.
Proof. intros. reflexivity. Qed.
Lemma update'_Some : forall {A} o (c:list A) (v:A), update' (Some c) o v = Some (update c o v).
Proof. intros. reflexivity. Qed.
Lemma slength_update' : forall {A} (s:option (list A)) o (v:A), slength (update' s o v) = slength s.
Proof. intros A s. destruct s; simpl; auto. apply length_update. Qed.

Lemma supdate_cons : forall {A} (x:option (list A)) (xs:list (option (list A))) l o (v:A),
  supdate (x::xs) l o v = if Nat.eqb l (length xs) then (update' x o v :: xs) else (x :: supdate xs l o v).
Proof. intros. reflexivity. Qed.



Lemma n_splice_sub : forall n f g, n_sub f g -> n_sub (n_splice n f) (n_splice n g).
Proof.
  intros n f g H x Hx. unfold n_sub in *. unfold n_splice in *.
  destruct (x =? n) eqn:E; [discriminate Hx|].
  destruct (x <? n) eqn:E2.
  - apply H. exact Hx.
  - apply H. exact Hx.
Qed.

Lemma splice_qual_subq : forall n a b, Subq (Q_lift a) (Q_lift b) ->
  Subq (Q_lift (splice_qual n a)) (Q_lift (splice_qual n b)).
Proof.
  intros n a b [Hf [Hfa [Hba Hla]]]. unfold Subq. repeat split.
  - intros Hx. change (qfresh (Q_lift (splice_qual n a))) in Hx.
    change (qfresh (Q_lift (splice_qual n b))). apply Hf. exact Hx.
  - intros x Hx. rewrite Q_lift_fvs in Hx. change (n_splice n (qfvs a) x = true) in Hx.
    rewrite Q_lift_fvs. change (n_splice n (qfvs b) x = true).
    exact (n_splice_sub n (qfvs a) (qfvs b) Hfa x Hx).
  - intros x Hx. rewrite Q_lift_bvs in Hx. change (qbvs a x = true) in Hx.
    rewrite Q_lift_bvs. change (qbvs b x = true). apply Hba. exact Hx.
  - intros x Hx. rewrite Q_lift_locs in Hx. change (qlocs a x = true) in Hx.
    rewrite Q_lift_locs. change (qlocs b x = true). apply Hla. exact Hx.
Qed.

Lemma splice_qual_closed : forall b f L (q:qual),
  closed_Qual b f L (Q_lift q) -> forall n, closed_Qual b (f+1) L (Q_lift (splice_qual n q)).
Proof.
  intros b f L q [Hf [Hb Hl]] n. unfold closed_Qual. repeat split; unfold closed_Nats in *.
  - intros y Hy. rewrite Q_lift_fvs in Hy. change (n_splice n (qfvs q) y = true) in Hy.
    unfold n_splice in Hy. destruct (y =? n) eqn:E; [discriminate Hy|].
    destruct (y <? n) eqn:E2.
    + apply Hf in Hy. lia.
    + apply Hf in Hy. lia.
  - intros y Hy. rewrite Q_lift_bvs in Hy. change (qbvs q y = true) in Hy. apply Hb in Hy. lia.
  - intros y Hy. rewrite Q_lift_locs in Hy. change (qlocs q y = true) in Hy. apply Hl in Hy. lia.
Qed.

Lemma splice_ty_closed : forall T b f L, closed_ty b f L T ->
  forall n, closed_ty b (f+1) L (splice_ty n T).
Proof.
  intros T. induction T; intros b f L Hc n; inversion Hc; subst.
  - apply cl_TTop.
  - cbn [splice_ty]. match goal with |- context[le_lt_dec n ?x] => destruct (le_lt_dec n x) as [Hle|Hlt] end.
    + apply cl_ttvarf. lia.
    + apply cl_ttvarf. lia.
  - cbn [splice_ty]. apply cl_ttvarb. lia.
  - cbn [splice_ty]. eapply cl_TAll.
    + apply splice_qual_closed; eauto.
    + apply splice_qual_closed; eauto.
    + eapply (IHT1 b f L); eauto.
    + eapply (IHT2 (S (S b)) f L); eauto.
  - apply cl_TUnit.
  - cbn [splice_ty]. eapply cl_TFun.
    + apply splice_qual_closed; eauto.
    + apply splice_qual_closed; eauto.
    + eapply (IHT1 b f L); eauto.
    + eapply (IHT2 (S (S b)) f L); eauto.
  - cbn [splice_ty]. eapply cl_TRef.
    + eapply (IHT b f L); eauto.
    + apply splice_qual_closed; eauto.
Qed.

Lemma splice_closed_tm : forall t b f L, closed_tm b f L t ->
  forall n, closed_tm b (f+1) L (splice n t).
Proof.
  intros t b f L Hc. revert b f L Hc. induction t; intros b f L Hc n; inversion Hc; subst.
  - cbn [splice]. apply cl_ttabs. eapply IHt; eauto.
  - cbn [splice]. apply cl_ttapp. eapply IHt; eauto.
  - apply cl_tsct.
  - cbn [splice]. apply cl_tvarb. lia.
  - cbn [splice]. match goal with |- context[le_lt_dec n ?x] => destruct (le_lt_dec n x) as [Hle|Hlt] end.
    + apply cl_tvarf. lia.
    + apply cl_tvarf. lia.
  - cbn [splice]. apply cl_tabs. eapply IHt; eauto.
  - cbn [splice]. apply cl_tapp. eapply IHt1; eauto. eapply IHt2; eauto.
  - apply cl_tloc. lia.
  - cbn [splice]. apply cl_tref. eapply IHt; eauto.
  - cbn [splice]. apply cl_tderef. eapply IHt; eauto.
  - cbn [splice]. apply cl_tassign. eapply IHt1; eauto. eapply IHt2; eauto.
  - cbn [splice]. apply cl_trefat. eapply IHt1; eauto. eapply IHt2; eauto.
  - cbn [splice]. apply cl_twithr. eapply IHt1; eauto. eapply IHt2; eauto.
  - cbn [splice]. apply cl_twithc; [lia | eapply IHt; eauto].
Qed.

Lemma n_splice_nor : forall n f g, n_splice n (n_or f g) = n_or (n_splice n f) (n_splice n g).
Proof.
  intros. apply functional_extensionality. intro y. unfold n_splice, n_or.
  destruct (y =? n) eqn:E; destruct (y <? n) eqn:E2; simpl;
  try (destruct (f y)); try (destruct (g y));
  try (destruct (f (pred y))); try (destruct (g (pred y))); reflexivity.
Qed.

Lemma splice_qual_qor : forall n a b,
  splice_qual n (qor a b) = qor (splice_qual n a) (splice_qual n b).
Proof.
  intros. apply qual_ext; unfold splice_qual, qor, qfresh; simpl; try reflexivity.
  apply n_splice_nor.
Qed.

Lemma splice_qual_open_qual : forall n k d' d,
  splice_qual n (open_qual k d' d) = open_qual k (splice_qual n d') (splice_qual n d).
Proof.
  intros n k d' d. unfold open_qual.
  destruct (qbvs d k) eqn:E.
  - rewrite splice_qual_qor.
    assert (Hbvs : qbvs (splice_qual n d) = qbvs d) by reflexivity.
    rewrite Hbvs. rewrite E. simpl.
    assert (Hbase : splice_qual n (qfresh d, qfvs d, n_diff (qbvs d) (n_one k), qlocs d) =
      (qfresh (splice_qual n d), qfvs (splice_qual n d),
       n_diff (qbvs (splice_qual n d)) (n_one k), qlocs (splice_qual n d))).
    { apply qual_ext; unfold splice_qual; simpl; reflexivity. }
    rewrite Hbase. reflexivity.
  - assert (Hbvs : qbvs (splice_qual n d) = qbvs d) by reflexivity.
    rewrite Hbvs. rewrite E. simpl. reflexivity.
Qed.

Lemma open_rec_tm_varF : forall k u x, open_rec_tm k u (tvar (varF x)) = tvar (varF x).
Proof. intros. reflexivity. Qed.
Lemma splice_varF_ge : forall n i, n <= i -> splice n (tvar (varF i)) = tvar (varF (S i)).
Proof.
  intros. cbn [splice]. destruct (le_lt_dec n i) as [H1|H2]; [reflexivity|lia].
Qed.
Lemma splice_varF_lt : forall n i, i < n -> splice n (tvar (varF i)) = tvar (varF i).
Proof.
  intros. cbn [splice]. destruct (le_lt_dec n i) as [H1|H2]; [lia|reflexivity].
Qed.
Lemma splice_varB : forall n i, splice n (tvar (varB i)) = tvar (varB i).
Proof. intros. reflexivity. Qed.

Lemma open_rec_tm_splice_varF : forall k u n i,
  open_rec_tm k u (splice n (tvar (varF i))) = splice n (tvar (varF i)).
Proof.
  intros k u n i. destruct (le_lt_dec n i) as [Hle|Hlt].
  - assert (Hs: splice n (tvar (varF i)) = tvar (varF (S i))).
    { cbn [splice]. destruct (le_lt_dec n i) as [H1|H2]; [reflexivity|lia]. }
    rewrite Hs. apply open_rec_tm_varF.
  - assert (Hs: splice n (tvar (varF i)) = tvar (varF i)).
    { cbn [splice]. destruct (le_lt_dec n i) as [H1|H2]; [lia|reflexivity]. }
    rewrite Hs. apply open_rec_tm_varF.
Qed.

Lemma splice_if : forall n (b:bool) u v,
  splice n (if b then u else v) = if b then splice n u else splice n v.
Proof. intros. destruct b; reflexivity. Qed.

Lemma splice_open_rec_tm : forall t k u n,
  splice n (open_rec_tm k u t) = open_rec_tm k (splice n u) (splice n t).
Proof.
  intros t. induction t; intros k u n; simpl.
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - reflexivity.
  - destruct v as [i|i].
    + symmetry. apply open_rec_tm_splice_varF.
    + rewrite splice_if. reflexivity.
  - f_equal. apply IHt.
  - f_equal. apply IHt1. apply IHt2.
  - reflexivity.
  - f_equal. apply IHt.
  - f_equal. apply IHt.
  - f_equal. apply IHt1. apply IHt2.
  - f_equal. apply IHt1. apply IHt2.
  - f_equal. apply IHt1. apply IHt2.
  - f_equal. apply IHt.
Qed.


Lemma splice_ty_open_rec_ty : forall T k U d n,
  splice_ty n (open_rec_ty k U d T) =
  open_rec_ty k (splice_ty n U) (splice_qual n d) (splice_ty n T).
Proof.
  intros T. induction T; intros k U d n.
  - cbn [splice_ty open_rec_ty]. reflexivity.
  - destruct v as [i|i].
    + rewrite open_rec_ty_varF. symmetry. apply open_rec_ty_splice_varF.
    + cbn [splice_ty open_rec_ty]. rewrite splice_ty_if. cbn [splice_ty open_rec_ty]. reflexivity.
  - cbn [splice_ty open_rec_ty]. f_equal.
    + rewrite splice_qual_open_qual. reflexivity.
    + rewrite splice_qual_open_qual. reflexivity.
    + apply IHT1.
    + apply IHT2.
  - cbn [splice_ty open_rec_ty]. reflexivity.
  - cbn [splice_ty open_rec_ty]. f_equal.
    + rewrite splice_qual_open_qual. reflexivity.
    + rewrite splice_qual_open_qual. reflexivity.
    + apply IHT1.
    + apply IHT2.
  - cbn [splice_ty open_rec_ty]. f_equal.
    + rewrite splice_qual_open_qual. reflexivity.
    + apply IHT.
Qed.

Lemma splice_qual_id_below : forall b f L (q:qual),
  closed_Qual b f L (Q_lift q) -> forall n, f <= n -> splice_qual n q = q.
Proof.
  intros b f L q [Hf [Hb Hl]] n Hfn. apply qual_ext; unfold splice_qual; simpl.
  - reflexivity.
  - apply functional_extensionality. intro y.
    change (n_splice n (qfvs q) y = qfvs q y). unfold n_splice.
    destruct (qfvs q y) eqn:Ey.
    + assert (y < f) by exact (Hf y Ey). assert (Hy: y < n) by lia.
      destruct (y =? n) eqn:E; [apply Nat.eqb_eq in E; lia|].
      destruct (y <? n) eqn:E2; [reflexivity | apply Nat.ltb_ge in E2; lia].
    + destruct (y =? n) eqn:E.
      * reflexivity.
      * destruct (y <? n) eqn:E2.
        -- reflexivity.
        -- destruct (qfvs q (pred y)) eqn:E3.
           ++ exfalso. assert (pred y < f) by exact (Hf (pred y) E3).
              apply Nat.ltb_ge in E2. apply Nat.eqb_neq in E.
              assert (Hpy: pred y = y - 1) by (destruct y; simpl; lia). lia.
           ++ reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma splice_ty_id_below : forall T b f L, closed_ty b f L T ->
  forall n, f <= n -> splice_ty n T = T.
Proof.
  intros T. induction T; intros b f L Hc n Hfn; inversion Hc; subst.
  - reflexivity.
  - cbn [splice_ty]. match goal with |- context[le_lt_dec n ?x] => destruct (le_lt_dec n x) as [H|H]; [lia|reflexivity] end.
  - reflexivity.
  - cbn [splice_ty]. f_equal.
    + apply splice_qual_id_below with (b:=b) (f:=f) (L:=L); auto.
    + apply splice_qual_id_below with (b:=S (S b)) (f:=f) (L:=L); auto.
    + apply (IHT1 b f L); auto.
    + apply (IHT2 (S (S b)) f L); auto.
  - reflexivity.
  - cbn [splice_ty]. f_equal.
    + apply splice_qual_id_below with (b:=b) (f:=f) (L:=L); auto.
    + apply splice_qual_id_below with (b:=S (S b)) (f:=f) (L:=L); auto.
    + apply (IHT1 b f L); auto.
    + apply (IHT2 (S (S b)) f L); auto.
  - cbn [splice_ty]. f_equal.
    + apply splice_qual_id_below with (b:=b) (f:=f) (L:=L); auto.
    + apply (IHT b f L); auto.
Qed.

Lemma splice_tm_id_below : forall t b f L, closed_tm b f L t ->
  forall n, f <= n -> splice n t = t.
Proof.
  intros t. induction t; intros b f L Hc n Hfn; inversion Hc; subst.
  - cbn [splice]. f_equal. apply (IHt (S (S b)) f L); auto.
  - cbn [splice]. f_equal. apply (IHt b f L); auto.
  - reflexivity.
  - reflexivity.
  - cbn [splice]. match goal with |- context[le_lt_dec n ?x] => destruct (le_lt_dec n x) as [H|H]; [lia|reflexivity] end.
  - cbn [splice]. f_equal. apply (IHt (S (S b)) f L); auto.
  - cbn [splice]. f_equal. apply (IHt1 b f L); auto. apply (IHt2 b f L); auto.
  - reflexivity.
  - cbn [splice]. f_equal. apply (IHt b f L); auto.
  - cbn [splice]. f_equal. apply (IHt b f L); auto.
  - cbn [splice]. f_equal. apply (IHt1 b f L); auto. apply (IHt2 b f L); auto.
  - cbn [splice]. f_equal. apply (IHt1 b f L); auto. apply (IHt2 b f L); auto.
  - cbn [splice]. f_equal. apply (IHt1 b f L); auto. apply (IHt2 (S (S b)) f L); auto.
  - cbn [splice]. f_equal. apply (IHt b f L); auto.
Qed.

Lemma qfresh_splice_qual : forall n q, qfresh (splice_qual n q) = qfresh q.
Proof. intros. reflexivity. Qed.
Lemma qbvs_splice_qual : forall n q, qbvs (splice_qual n q) = qbvs q.
Proof. intros. reflexivity. Qed.
Lemma qlocs_splice_qual : forall n q, qlocs (splice_qual n q) = qlocs q.
Proof. intros. reflexivity. Qed.

Lemma n_splice_nand : forall n f g, n_splice n (n_and f g) = n_and (n_splice n f) (n_splice n g).
Proof.
  intros. apply functional_extensionality. intro y. unfold n_splice, n_and.
  destruct (y =? n) eqn:E; destruct (y <? n) eqn:E2; simpl;
  try (destruct (f y)); try (destruct (g y));
  try (destruct (f (pred y))); try (destruct (g (pred y))); reflexivity.
Qed.



Lemma splice_qual_empty : forall n, splice_qual n q_empty = q_empty.
Proof.
  intros n. apply splice_qual_id_below with (b:=0) (f:=0) (L:=0).
  - unfold closed_Qual. split.
    + unfold closed_Nats. intros x Hx. discriminate Hx.
    + split.
      * unfold closed_Nats. intros x Hx. discriminate Hx.
      * unfold closed_Nats. intros x Hx. discriminate Hx.
  - lia.
Qed.
Lemma splice_ty_TUnit : forall n, splice_ty n TUnit = TUnit.
Proof. intros. reflexivity. Qed.
Lemma n_splice_diff : forall n p q,
  n_splice n (n_diff p q) = n_diff (n_splice n p) (n_splice n q).
Proof.
  intros n p q. apply functional_extensionality. intro x.
  unfold n_splice, n_diff.
  destruct (x =? n) eqn:E; destruct (x <? n) eqn:E2; reflexivity.
Qed.
Lemma splice_qual_qdiff : forall n a b,
  splice_qual n (qdiff a b) = qdiff (splice_qual n a) (splice_qual n b).
Proof.
  intros n a b. apply qual_ext.
  - reflexivity.
  - apply functional_extensionality. intro x.
    change (n_splice n (n_diff (qfvs a) (qfvs b)) x =
            n_diff (n_splice n (qfvs a)) (n_splice n (qfvs b)) x).
    rewrite n_splice_diff. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
Lemma not_free_splice : forall n T, not_free 0 T -> not_free 0 (splice_ty n T).
Proof.
  intros n T H. unfold not_free in *.
  rewrite <- H at 2.
  rewrite splice_ty_open_rec_ty, splice_ty_TUnit, splice_qual_empty.
  reflexivity.
Qed.

Lemma n_diff_empty_r : forall f, n_diff f n_empty = f.
Proof. intros. apply functional_extensionality. intro x. unfold n_diff, n_empty. simpl. rewrite andb_true_r. reflexivity. Qed.

Lemma Is_true_orb : forall a b, Is_true (a || b) <-> Is_true a \/ Is_true b.
Proof. intros. unfold Is_true. destruct a,b; simpl; intuition. Qed.
Lemma Is_true_andb : forall a b, Is_true (a && b) <-> Is_true a /\ Is_true b.
Proof. intros. unfold Is_true. destruct a,b; simpl; intuition. Qed.

Lemma qor_subq_l : forall a b, a ⊑↑ (qor a b).
Proof.
  intros a b. unfold Subq. split.
  - change (Is_true (qfresh a) -> Is_true (qfresh a || qfresh b)).
    intros H. apply Is_true_orb. left. exact H.
  - split.
    + change (forall x, qfvs a x = true -> (qfvs a x || qfvs b x) = true).
      intros x H. rewrite H. reflexivity.
    + split.
      * change (forall x, qbvs a x = true -> (qbvs a x || qbvs b x) = true).
        intros x H. rewrite H. reflexivity.
      * change (forall x, qlocs a x = true -> (qlocs a x || qlocs b x) = true).
        intros x H. rewrite H. reflexivity.
Qed.
Lemma qor_subq_r : forall a b, b ⊑↑ (qor a b).
Proof.
  intros a b. unfold Subq. split.
  - change (Is_true (qfresh b) -> Is_true (qfresh a || qfresh b)).
    intros H. apply Is_true_orb. right. exact H.
  - split.
    + change (forall x, qfvs b x = true -> (qfvs a x || qfvs b x) = true).
      intros x H. rewrite H. rewrite orb_true_r. reflexivity.
    + split.
      * change (forall x, qbvs b x = true -> (qbvs a x || qbvs b x) = true).
        intros x H. rewrite H. rewrite orb_true_r. reflexivity.
      * change (forall x, qlocs b x = true -> (qlocs a x || qlocs b x) = true).
        intros x H. rewrite H. rewrite orb_true_r. reflexivity.
Qed.
Lemma qor_subq_mono : forall a b c d, a ⊑↑ b -> c ⊑↑ d -> qor a c ⊑↑ qor b d.
Proof.
  intros a b c d [Hf1 [H1 [H2 H3]]] [Gf1 [G1 [G2 G3]]].
  unfold N_sub in H1, H2, H3, G1, G2, G3. unfold Subq. split.
  - change (Is_true (qfresh a || qfresh c) -> Is_true (qfresh b || qfresh d)).
    intros H. apply Is_true_orb in H. apply Is_true_orb. destruct H as [H|H].
    + left. apply Hf1. exact H.
    + right. apply Gf1. exact H.
  - split.
    + change (forall x, (qfvs a x || qfvs c x) = true -> (qfvs b x || qfvs d x) = true).
      intros x H. apply orb_true_iff in H. destruct H as [H|H].
      * apply H1 in H. rewrite orb_true_iff. left. exact H.
      * apply G1 in H. rewrite orb_true_iff. right. exact H.
    + split.
      * change (forall x, (qbvs a x || qbvs c x) = true -> (qbvs b x || qbvs d x) = true).
        intros x H. apply orb_true_iff in H. destruct H as [H|H].
        -- apply H2 in H. rewrite orb_true_iff. left. exact H.
        -- apply G2 in H. rewrite orb_true_iff. right. exact H.
      * change (forall x, (qlocs a x || qlocs c x) = true -> (qlocs b x || qlocs d x) = true).
        intros x H. apply orb_true_iff in H. destruct H as [H|H].
        -- apply H3 in H. rewrite orb_true_iff. left. exact H.
        -- apply G3 in H. rewrite orb_true_iff. right. exact H.
Qed.
Lemma qand_subq_l : forall a b, qand a b ⊑↑ a.
Proof.
  intros a b. unfold Subq. split.
  - change (Is_true (qfresh a && qfresh b) -> Is_true (qfresh a)).
    intros H. apply Is_true_andb in H. tauto.
  - split.
    + change (forall x, (qfvs a x && qfvs b x) = true -> qfvs a x = true).
      intros x H. apply andb_true_iff in H. tauto.
    + split.
      * change (forall x, (qbvs a x && qbvs b x) = true -> qbvs a x = true).
        intros x H. apply andb_true_iff in H. tauto.
      * change (forall x, (qlocs a x && qlocs b x) = true -> qlocs a x = true).
        intros x H. apply andb_true_iff in H. tauto.
Qed.
Lemma qand_subq_r : forall a b, qand a b ⊑↑ b.
Proof.
  intros a b. unfold Subq. split.
  - change (Is_true (qfresh a && qfresh b) -> Is_true (qfresh b)).
    intros H. apply Is_true_andb in H. tauto.
  - split.
    + change (forall x, (qfvs a x && qfvs b x) = true -> qfvs b x = true).
      intros x H. apply andb_true_iff in H. tauto.
    + split.
      * change (forall x, (qbvs a x && qbvs b x) = true -> qbvs b x = true).
        intros x H. apply andb_true_iff in H. tauto.
      * change (forall x, (qlocs a x && qlocs b x) = true -> qlocs b x = true).
        intros x H. apply andb_true_iff in H. tauto.
Qed.
Lemma qdiff_subq_l : forall a b, qdiff a b ⊑↑ a.
Proof.
  intros a b. unfold Subq. split.
  - change (Is_true (qfresh a && negb (qfresh b)) -> Is_true (qfresh a)).
    intros H. apply Is_true_andb in H. tauto.
  - split.
    + change (forall x, (qfvs a x && negb (qfvs b x)) = true -> qfvs a x = true).
      intros x H. apply andb_true_iff in H. tauto.
    + split.
      * change (forall x, (qbvs a x && negb (qbvs b x)) = true -> qbvs a x = true).
        intros x H. apply andb_true_iff in H. tauto.
      * change (forall x, (qlocs a x && negb (qlocs b x)) = true -> qlocs a x = true).
        intros x H. apply andb_true_iff in H. tauto.
Qed.
Lemma qdiff_subq_mono : forall a b c, a ⊑↑ b -> qdiff a c ⊑↑ qdiff b c.
Proof.
  intros a b c [Hf1 [H1 [H2 H3]]]. unfold N_sub in H1, H2, H3. unfold Subq. split.
  - change (Is_true (qfresh a && negb (qfresh c)) -> Is_true (qfresh b && negb (qfresh c))).
    intros H. apply Is_true_andb in H. destruct H as [Ha Hc].
    apply Is_true_andb. split; [apply Hf1; exact Ha | exact Hc].
  - split.
    + change (forall x, (qfvs a x && negb (qfvs c x)) = true -> (qfvs b x && negb (qfvs c x)) = true).
      intros x H. apply andb_true_iff in H. destruct H as [Hx Hc].
      apply H1 in Hx. apply andb_true_iff. auto.
    + split.
      * change (forall x, (qbvs a x && negb (qbvs c x)) = true -> (qbvs b x && negb (qbvs c x)) = true).
        intros x H. apply andb_true_iff in H. destruct H as [Hx Hc].
        apply H2 in Hx. apply andb_true_iff. auto.
      * change (forall x, (qlocs a x && negb (qlocs c x)) = true -> (qlocs b x && negb (qlocs c x)) = true).
        intros x H. apply andb_true_iff in H. destruct H as [Hx Hc].
        apply H3 in Hx. apply andb_true_iff. auto.
Qed.
Lemma qdiff_empty_r : forall a, qdiff a q_empty = a.
Proof.
  intros a. apply qual_ext.
  - unfold qdiff, q_empty, qfresh. simpl. rewrite andb_true_r. reflexivity.
  - unfold qdiff, q_empty, qfvs. simpl. apply n_diff_empty_r.
  - unfold qdiff, q_empty, qbvs. simpl. apply n_diff_empty_r.
  - unfold qdiff, q_empty, qlocs. simpl. apply n_diff_empty_r.
Qed.

Lemma closed_qual_qdiff : forall b f L a c,
  closed_Qual b f L (Q_lift a) -> closed_Qual b f L (Q_lift (qdiff a c)).
Proof.
  intros b f L a c [Hf [Hb Hl]]. unfold closed_Qual. split; [|split].
  - unfold closed_Nats in *. intros x Hx. apply Hf.
    unfold N_lift, qdiff in Hx. simpl in Hx. apply andb_true_iff in Hx. tauto.
  - unfold closed_Nats in *. intros x Hx. apply Hb.
    unfold N_lift, qdiff in Hx. simpl in Hx. apply andb_true_iff in Hx. tauto.
  - unfold closed_Nats in *. intros x Hx. apply Hl.
    unfold N_lift, qdiff in Hx. simpl in Hx. apply andb_true_iff in Hx. tauto.
Qed.

Lemma has_type_closed_phi : forall Γ φ Σ t T d,
  has_type Γ φ Σ t T d -> closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift φ).
Proof.
  intros Γ φ Σ t T d H. induction H; eauto.
Qed.

Hint Resolve qdiff_subq_mono closed_qual_qdiff Subq_refl : core.

Ltac solve_qdiff_ih IH :=
  match goal with
  | Hq : qdiff ?phi ?L = ?fd |- has_type ?G ?fd2 ?S ?t ?T ?d =>
      eapply IH; [ rewrite <- Hq; apply qdiff_subq_mono; assumption
                 | eapply closed_qual_qdiff; assumption ]
  end.

Lemma has_type_weaken_phi : forall Γ φ Σ t T d,
  has_type Γ φ Σ t T d ->
  forall φ', φ ⊑↑ φ' -> closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift φ') ->
  has_type Γ φ' Σ t T d.
Proof.
  intros Γ φ Σ t T d H. induction H; intros φ' Hle Hcl.
  - apply t_tabs; eauto 8. eapply Subq_trans with (b := Q_lift φ); [eassumption|exact Hle].
  - apply t_tapp; eauto 10.
    eapply Subq_trans with (b := Q_lift (φ ⊔ {♦})); [eassumption | apply qor_subq_mono; [exact Hle | apply Subq_refl]].
    eapply Subq_trans with (b := Q_lift φ); [eassumption|exact Hle].
  - apply t_tapp_fresh; eauto 10.
    eapply Subq_trans with (b := Q_lift (φ ⊔ {♦})); [eassumption | apply qor_subq_mono; [exact Hle | apply Subq_refl]].
    eapply Subq_trans with (b := Q_lift (φ ⊔ {♦})); [eassumption | apply qor_subq_mono; [exact Hle | apply Subq_refl]].
    eapply Subq_trans with (b := Q_lift (φ ⊔ {♦})); [eassumption | apply qor_subq_mono; [exact Hle | apply Subq_refl]].
  - apply t_base; eauto 8.
  - eapply t_var; eauto 10. eapply Subq_trans with (b := Q_lift φ); [eassumption|exact Hle].
  - eapply t_abs; eauto 8. eapply Subq_trans with (b := Q_lift φ); [eassumption|exact Hle].
  - eapply t_app with (φd := qdiff φ' (local_locs t1)); eauto 12.
    all: try solve_qdiff_ih IHhas_type2.
    all: try (eapply Subq_trans with (b := Q_lift (φ ⊔ {♦})); [eassumption | apply qor_subq_mono; [exact Hle | apply Subq_refl]]).
  - eapply t_app_fresh with (φd := qdiff φ' (local_locs t1)); eauto 12.
    all: try solve_qdiff_ih IHhas_type2.
    all: try (eapply Subq_trans with (b := Q_lift (φ ⊔ {♦})); [eassumption | apply qor_subq_mono; [exact Hle | apply Subq_refl]]).
  - apply t_loc; eauto 10. eapply Subq_trans with (b := Q_lift φ); [eassumption|exact Hle].
  - apply t_ref; eauto 8.
  - eapply t_refat with (φd := qdiff φ' (local_locs t2)); eauto 12.
    all: try solve_qdiff_ih IHhas_type1.
  - eapply t_deref; eauto 10. eapply Subq_trans with (b := Q_lift φ); [eassumption|exact Hle].
  - eapply t_assign with (φd := qdiff φ' (local_locs t1)); eauto 12.
    all: try solve_qdiff_ih IHhas_type2.
  - eapply t_sub; eauto 10. eapply Subq_trans with (b := Q_lift (φ ⊔ {♦})); [eassumption | apply qor_subq_mono; [exact Hle | apply Subq_refl]].
  - eapply t_withr; eauto 10. eapply Subq_trans with (b := Q_lift φ); [eassumption|exact Hle].
  - apply t_withc; eauto 10.
Qed.

Lemma closed_qual_of_subq_qdom : forall b f (Σ : senv) (φ : qual),
  φ ⊑↑ qdom Σ -> closed_Qual b f (‖Σ‖) (Q_lift φ).
Proof.
  intros b f Σ φ [Hfr [Hfv [Hbv Hlc]]].
  unfold closed_Qual. split; [|split].
  - unfold closed_Nats. intros x Hx.
    exfalso. pose proof (Hfv x Hx) as Hc. unfold N_lift, qdom, n_empty in Hc. simpl in Hc. discriminate Hc.
  - unfold closed_Nats. intros x Hx.
    exfalso. pose proof (Hbv x Hx) as Hc. unfold N_lift, qdom, n_empty in Hc. simpl in Hc. discriminate Hc.
  - unfold closed_Nats. intros x Hx.
    pose proof (Hlc x Hx) as Hc. unfold N_lift, qdom, n_dom in Hc.
    apply Nat.ltb_lt in Hc. exact Hc.
Qed.

Lemma closed_Qual_loc_weaken : forall b f l (q:Qual), closed_Qual b f l q -> forall L, l <= L -> closed_Qual b f L q.
Proof.
  intros b f l q [H1 [H2 H3]] L Hl. unfold closed_Qual. split; [|split];
  unfold closed_Nats in *; intros x Hx; [apply H1 in Hx|apply H2 in Hx|apply H3 in Hx]; lia.
Qed.

Lemma closed_ty_loc_weaken : forall b f l T, closed_ty b f l T -> forall l', l <= l' -> closed_ty b f l' T.
Proof.
  intros b f l T. revert b f l. induction T; intros b f l Hc l' Hl; inversion Hc; subst.
  - apply cl_TTop.
  - apply cl_ttvarf. assumption.
  - apply cl_ttvarb. assumption.
  - eapply cl_TAll.
    + eapply closed_Qual_loc_weaken; eauto.
    + eapply closed_Qual_loc_weaken; eauto.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - apply cl_TUnit.
  - eapply cl_TFun.
    + eapply closed_Qual_loc_weaken; eauto.
    + eapply closed_Qual_loc_weaken; eauto.
    + eapply IHT1; eauto.
    + eapply IHT2; eauto.
  - eapply cl_TRef.
    + eapply IHT; eauto.
    + eapply closed_Qual_loc_weaken; eauto.
Qed.

Lemma closed_tm_loc_weaken : forall b f l t, closed_tm b f l t -> forall L, l <= L -> closed_tm b f L t.
Proof.
  intros b f l t H. induction H; intros L Hl.
  - apply cl_ttabs. apply IHclosed_tm. lia.
  - apply cl_ttapp. apply IHclosed_tm. lia.
  - apply cl_tsct.
  - apply cl_tvarb. lia.
  - apply cl_tvarf. lia.
  - apply cl_tabs. apply IHclosed_tm. lia.
  - apply cl_tapp. apply IHclosed_tm1; lia. apply IHclosed_tm2; lia.
  - apply cl_tloc. lia.
  - apply cl_tref. apply IHclosed_tm. lia.
  - apply cl_trefat. apply IHclosed_tm1; lia. apply IHclosed_tm2; lia.
  - apply cl_tderef. apply IHclosed_tm. lia.
  - apply cl_tassign. apply IHclosed_tm1; lia. apply IHclosed_tm2; lia.
  - apply cl_twithr. apply IHclosed_tm1; lia. apply IHclosed_tm2; lia.
  - apply cl_twithc. lia. apply IHclosed_tm. lia.
Qed.

Lemma indexr_update_other : forall {A} (s:list A) l (v:A) k,
  k <> l -> indexr k (update s l v) = indexr k s.
Proof.
  intros A s. induction s as [|x xs IH]; intros l v k Hne.
  - reflexivity.
  - rewrite update_cons. destruct (Nat.eqb l (length xs)) eqn:El.
    + rewrite !indexr_cons. destruct (Nat.eqb k (length xs)) eqn:Ek.
      * exfalso. apply Hne. apply Nat.eqb_eq in Ek. apply Nat.eqb_eq in El. lia.
      * reflexivity.
    + rewrite !indexr_cons. rewrite length_update. destruct (Nat.eqb k (length xs)) eqn:Ek.
      * reflexivity.
      * apply IH. exact Hne.
Qed.

Lemma sindexr'_supdate_same : forall {A} (σ:list (option (list A))) l o v old,
  sindexr' l o σ = Some old -> sindexr' l o (supdate σ l o v) = Some v.
Proof.
  intros A σ. induction σ as [|a σ' IH]; intros l o v old H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb l (length σ')) eqn:E.
    + cbn [supdate sindexr']. rewrite E.
      destruct a as [c|]; [|simpl in H; discriminate].
      simpl in H. change (indexr o c = Some old) in H.
      change (indexr o (update c o v) = Some v).
      eapply indexr_update_same with (old:=old). exact H.
    + cbn [supdate sindexr']. rewrite length_supdate. rewrite E.
      eapply IH. exact H.
Qed.

Lemma sindexr'_supdate_other : forall {A} (σ:list (option (list A))) l o v l' o',
  l' <> l \/ o' <> o -> sindexr' l' o' (supdate σ l o v) = sindexr' l' o' σ.
Proof.
  intros A σ. induction σ as [|a σ' IH]; intros l o v l' o' Hd; simpl.
  - reflexivity.
  - destruct (Nat.eqb l (length σ')) eqn:El.
    + destruct (Nat.eqb l' (length σ')) eqn:El'.
      * assert (Heq : l' = l). { apply Nat.eqb_eq in El. apply Nat.eqb_eq in El'. lia. }
        destruct Hd as [Hl|Ho].
        -- exfalso. apply Hl. exact Heq.
        -- subst l'. cbn [supdate sindexr']. try rewrite El. try rewrite El'.
           destruct a as [c|]; [|reflexivity].
           change (indexr o' (update c o v) = indexr o' c).
           rewrite indexr_update_other; [reflexivity|exact Ho].
      * assert (Hlne : l' <> l). { intro Hll. apply Nat.eqb_neq in El'. apply El'. subst l'. apply Nat.eqb_eq in El. exact El. }
        cbn [supdate sindexr']. try rewrite El. try rewrite El'.
        reflexivity.
    + destruct (Nat.eqb l' (length σ')) eqn:El'.
      * cbn [supdate sindexr']. try rewrite El. rewrite length_supdate. try rewrite El'. reflexivity.
      * cbn [supdate sindexr']. try rewrite El. rewrite length_supdate. try rewrite El'.
        apply IH. exact Hd.
Qed.

Lemma length_cinsert : forall {A} (σ:list (option (list A))) l (v:A),
  length (cinsert σ l v) = length σ.
Proof.
  intros A σ. induction σ as [|a σ' IH]; intros l v; simpl.
  - reflexivity.
  - cbn [cinsert]. destruct (Nat.eqb l (length σ')); simpl; [reflexivity|]. f_equal. apply IH.
Qed.

Lemma cinsert_cell : forall {A} (σ:list (option (list A))) l v c,
  indexr l σ = Some c -> indexr l (cinsert σ l v) = Some (insert' c v).
Proof.
  intros A σ. induction σ as [|a σ' IH]; intros l v c H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb l (length σ')) eqn:E.
    + cbn [cinsert indexr]. rewrite E. simpl. injection H as Hca. subst c. reflexivity.
    + cbn [cinsert indexr]. rewrite length_cinsert. rewrite E. simpl. apply IH. exact H.
Qed.

Lemma cinsert_other : forall {A} (σ:list (option (list A))) l v k,
  k <> l -> indexr k (cinsert σ l v) = indexr k σ.
Proof.
  intros A σ. induction σ as [|a σ' IH]; intros l v k Hne.
  - reflexivity.
  - destruct (Nat.eqb l (length σ')) eqn:El.
    + assert (Hk : Nat.eqb k (length σ') = false).
      { apply Nat.eqb_neq. intro Hkl. apply Hne. rewrite Hkl. symmetry. apply Nat.eqb_eq. exact El. }
      cbn [cinsert indexr]. try rewrite El. cbn [indexr]. try rewrite Hk. reflexivity.
    + cbn [cinsert indexr]. try rewrite El. cbn [indexr]. try rewrite length_cinsert.
      destruct (Nat.eqb k (length σ')) eqn:Ek.
      * reflexivity.
      * apply IH. exact Hne.
Qed.

Lemma sindexr'_cinsert_other : forall {A} (σ:list (option (list A))) l v l' o',
  l' <> l -> sindexr' l' o' (cinsert σ l v) = sindexr' l' o' σ.
Proof.
  intros A σ. induction σ as [|a σ' IH]; intros l v l' o' Hne; simpl.
  - reflexivity.
  - destruct (Nat.eqb l (length σ')) eqn:El.
    + assert (Hk : Nat.eqb l' (length σ') = false).
      { apply Nat.eqb_neq. intro Hl. apply Hne. rewrite Hl. symmetry. apply Nat.eqb_eq. exact El. }
      cbn [cinsert sindexr']. try rewrite El. cbn [sindexr']. try rewrite Hk. reflexivity.
    + cbn [cinsert sindexr']. try rewrite El. cbn [sindexr']. try rewrite length_cinsert.
      destruct (Nat.eqb l' (length σ')) eqn:Ek.
      * reflexivity.
      * apply IH. exact Hne.
Qed.

Lemma sindexr'_cinsert_same : forall {A} (σ:list (option (list A))) l v o s,
  indexr l σ = Some (Some s) ->
  sindexr' l o (cinsert σ l v) = if Nat.eqb o (length s) then Some v else sindexr' l o σ.
Proof.
  intros A σ. induction σ as [|a σ' IH]; intros l v o s H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb l (length σ')) eqn:E.
    + cbn [cinsert sindexr']. try rewrite E. cbn [sindexr']. try rewrite E.
      injection H as Ha. subst a. simpl. reflexivity.
    + cbn [cinsert sindexr']. try rewrite E. cbn [sindexr']. try rewrite length_cinsert.
      try rewrite E. simpl. apply IH. exact H.
Qed.

Lemma sindexr'_cons_same : forall {A} (a:option (list A)) (σ:list (option (list A))) o,
  sindexr' (length σ) o (a :: σ) = indexr' o a.
Proof.
  intros. cbn [sindexr']. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma sindexr'_cons_old : forall {A} (a:option (list A)) (σ:list (option (list A))) l o,
  l < length σ -> sindexr' l o (a :: σ) = sindexr' l o σ.
Proof.
  intros. cbn [sindexr'].
  replace (Nat.eqb l (length σ)) with false by (symmetry; apply Nat.eqb_neq; lia).
  reflexivity.
Qed.

Lemma wf_store_cons : forall v σ, wf_step v -> value v -> wf_store σ ->
  wf_store (Some (v :: nil) :: σ).
Proof.
  intros v σ Hwf Hval Hσ l o u Hlu.
  cbn [sindexr'] in Hlu.
  destruct (Nat.eqb l (length σ)) eqn:E; simpl in Hlu.
  - apply Nat.eqb_eq in E. subst l.
    simpl in Hlu.
    destruct o; simpl in Hlu; [|discriminate].
    injection Hlu as <-. split; assumption.
  - exact (Hσ l o u Hlu).
Qed.

Lemma qmem_loc_mono : forall l a b, a ⊑↑ b -> l ∈ₗ a -> l ∈ₗ b.
Proof.
  intros l a b [Hf [H1 [H2 H3]]] H.
  unfold N_sub in H3. unfold N_lift in *.
  apply H3. exact H.
Qed.

Lemma vtp_weaken_phi : forall Σ ϰ φ v T d,
  vtp Σ ϰ φ v T d -> forall φ', φ ⊑↑ φ' -> vtp Σ ϰ φ' v T d.
Proof.
  intros Σ ϰ φ v T d H. induction H; intros φ' Hle.
  all: eauto 12 using vtp_tabs, vtp_base, vtp_loc, vtp_abs, vtp_top, qmem_loc_mono.
Qed.

Lemma indexr_update_same_none : forall {A} (c:list A) l (v:A),
  indexr l c = None -> indexr l (update c l v) = None.
Proof.
  intros A c. induction c as [|x xs IH]; intros l v H.
  - reflexivity.
  - rewrite indexr_cons in H. rewrite update_cons.
    destruct (Nat.eqb l (length xs)) eqn:E.
    + discriminate H.
    + rewrite indexr_cons. rewrite length_update. try rewrite E. simpl.
      apply IH. simpl in H. exact H.
Qed.

Lemma sindexr'_supdate_none : forall {A} (σ:list (option (list A))) l o v k o',
  sindexr' k o' σ = None -> sindexr' k o' (supdate σ l o v) = None.
Proof.
  intros A σ. induction σ as [|a σ' IH]; intros l o v k o' H; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb l (length σ')) eqn:El.
    + cbn [supdate sindexr']. try rewrite El.
      destruct (Nat.eqb k (length σ')) eqn:Ek.
      * apply Nat.eqb_eq in Ek. subst k.
        destruct a as [c|]; [|reflexivity].
        simpl in H. simpl.
        destruct (Nat.eqb o' o) eqn:Eo.
        -- apply Nat.eqb_eq in Eo. subst o'. apply indexr_update_same_none. exact H.
        -- apply Nat.eqb_neq in Eo. eapply update_preserves_none; eauto.
      * cbn [sindexr']. try rewrite length_supdate. try rewrite Ek. simpl.
        exact H.
    + cbn [supdate sindexr']. try rewrite El.
      destruct (Nat.eqb k (length σ')) eqn:Ek.
      * cbn [sindexr']. try rewrite length_supdate. try rewrite Ek. simpl.
        match goal with
        | |- sindexr' _ _ (supdate _ _ _ _) = None => apply IH; exact H
        | _ => exact H
        end.
      * cbn [sindexr']. try rewrite length_supdate. try rewrite Ek. simpl.
        apply IH. exact H.
Qed.

Lemma wf_store_supdate : forall σ l o v,
  wf_store σ -> wf_step v -> value v -> wf_store (supdate σ l o v).
Proof.
  intros σ l o v Hσ Hwf Hval k o' u Hlook.
  destruct (sindexr' k o' σ) as [old|] eqn:E.
  - destruct (Nat.eqb k l) eqn:Ek.
    + destruct (Nat.eqb o' o) eqn:Eo.
      * apply Nat.eqb_eq in Ek. apply Nat.eqb_eq in Eo. subst k. subst o'.
        assert (Hs : sindexr' l o (supdate σ l o v) = Some v)
          by (eapply sindexr'_supdate_same with (old:=old); exact E).
        rewrite Hs in Hlook. injection Hlook as <-. split; assumption.
      * apply Nat.eqb_neq in Eo.
        assert (Heq : sindexr' k o' (supdate σ l o v) = sindexr' k o' σ)
          by (apply sindexr'_supdate_other; right; exact Eo).
        rewrite Heq in Hlook. rewrite E in Hlook. injection Hlook as <-.
        exact (Hσ k o' old E).
    + assert (Heq : sindexr' k o' (supdate σ l o v) = sindexr' k o' σ)
        by (apply sindexr'_supdate_other; left; apply Nat.eqb_neq in Ek; exact Ek).
      rewrite Heq in Hlook. rewrite E in Hlook. injection Hlook as <-.
      exact (Hσ k o' old E).
  - exfalso. pose proof (sindexr'_supdate_none σ l o v k o' E) as Hnone.
    rewrite Hnone in Hlook. discriminate Hlook.
Qed.

Lemma sindexr'_cinsert_cell_none : forall {A} (σ:list (option (list A))) l v o,
  indexr l σ = None -> sindexr' l o (cinsert σ l v) = None.
Proof.
  intros A σ. induction σ as [|a σ' IH]; intros l v o H; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb l (length σ')) eqn:El.
    + cbn [cinsert sindexr']. try rewrite El. discriminate H.
    + cbn [cinsert sindexr']. try rewrite El. simpl in H.
      try rewrite length_cinsert. try rewrite El. simpl.
      apply IH. exact H.
Qed.

Lemma sindexr'_cinsert_cell_Some_None : forall {A} (σ:list (option (list A))) l v o,
  indexr l σ = Some None -> sindexr' l o (cinsert σ l v) = None.
Proof.
  intros A σ. induction σ as [|a σ' IH]; intros l v o H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb l (length σ')) eqn:El.
    + cbn [cinsert sindexr']. try rewrite El. simpl.
      injection H as Ha. subst a. reflexivity.
    + cbn [cinsert sindexr']. try rewrite El. simpl in H.
      try rewrite length_cinsert. try rewrite El. simpl.
      apply IH. exact H.
Qed.

Lemma wf_store_cinsert : forall σ l v,
  wf_store σ -> wf_step v -> value v -> wf_store (cinsert σ l v).
Proof.
  intros σ l v Hσ Hwf Hval k o u Hlook.
  destruct (Nat.eqb k l) eqn:Ek.
  - apply Nat.eqb_eq in Ek. subst k.
    destruct (indexr l σ) as [c|] eqn:Hs.
    + destruct c as [s|] eqn:Hs2.
      * pose proof (sindexr'_cinsert_same σ l v o s Hs) as E.
        rewrite E in Hlook. destruct (Nat.eqb o (length s)) eqn:Eo.
        -- injection Hlook as Hvu. rewrite <- Hvu. split; assumption.
        -- exact (Hσ l o u Hlook).
      * exfalso. pose proof (sindexr'_cinsert_cell_Some_None σ l v o Hs) as E.
        rewrite E in Hlook. discriminate Hlook.
    + exfalso. pose proof (sindexr'_cinsert_cell_none σ l v o Hs) as E.
      rewrite E in Hlook. discriminate Hlook.
  - assert (Heq : sindexr' k o (cinsert σ l v) = sindexr' k o σ)
      by (apply sindexr'_cinsert_other; apply Nat.eqb_neq; exact Ek).
    rewrite Heq in Hlook. exact (Hσ k o u Hlook).
Qed.

Lemma sindexr'_update_none_same : forall (σ:store) l o,
  sindexr' l o (update σ l None) = None.
Proof.
  intros σ. induction σ as [|a σ' IH]; intros l o; simpl.
  - reflexivity.
  - destruct (Nat.eqb l (length σ')) eqn:E.
    + cbn [sindexr']. try rewrite E. simpl. reflexivity.
    + cbn [sindexr']. try rewrite E. rewrite length_update. try rewrite E. simpl.
      apply IH.
Qed.

Lemma sindexr'_update_other : forall (σ:store) l k o,
  k <> l -> sindexr' k o (update σ l None) = sindexr' k o σ.
Proof.
  intros σ. induction σ as [|a σ' IH]; intros l k o Hne; simpl.
  - reflexivity.
  - destruct (Nat.eqb l (length σ')) eqn:El.
    + assert (Hk : Nat.eqb k (length σ') = false).
      { apply Nat.eqb_neq. intro Hkl. apply Hne. rewrite Hkl. symmetry. apply Nat.eqb_eq. exact El. }
      cbn [sindexr']. try rewrite El. try rewrite Hk. simpl. reflexivity.
    + cbn [sindexr']. try rewrite El. rewrite length_update.
      destruct (Nat.eqb k (length σ')) eqn:Ek.
      * reflexivity.
      * apply IH. exact Hne.
Qed.

Lemma wf_store_update_None : forall (σ:store) l, wf_store σ -> wf_store (update σ l None).
Proof.
  intros σ l Hσ k o u Hlook.
  destruct (Nat.eqb k l) eqn:Ek.
  - apply Nat.eqb_eq in Ek. subst k.
    pose proof (sindexr'_update_none_same σ l o) as E. rewrite E in Hlook. discriminate Hlook.
  - assert (Heq : sindexr' k o (update σ l None) = sindexr' k o σ)
      by (apply sindexr'_update_other; apply Nat.eqb_neq; exact Ek).
    rewrite Heq in Hlook. exact (Hσ k o u Hlook).
Qed.

Lemma qstp_len_weaken : forall Γ Σ d1 d2,
  qstp Γ Σ d1 d2 -> forall Σ', ‖Σ‖ <= ‖Σ'‖ -> qstp Γ Σ' d1 d2.
Proof.
  intros Γ Σ d1 d2 H. induction H; intros Σ' Hlen.
  - apply qs_sq; [assumption | eapply closed_Qual_loc_weaken; [eassumption|exact Hlen]].
  - eapply qs_self; eauto using closed_Qual_loc_weaken.
  - eapply qs_self_all; eauto using closed_Qual_loc_weaken.
  - eapply qs_qvar; eauto using closed_ty_loc_weaken, closed_Qual_loc_weaken.
  - eapply qs_qvar_ty; eauto using closed_ty_loc_weaken, closed_Qual_loc_weaken.
  - apply qs_cong; [apply IHqstp; exact Hlen | eauto using closed_Qual_loc_weaken].
  - eapply qs_trans; eauto.
Qed.

Lemma stp_len_weaken : forall Γ Σ T1 d1 T2 d2,
  stp Γ Σ T1 d1 T2 d2 -> forall Σ', ‖Σ‖ <= ‖Σ'‖ -> stp Γ Σ' T1 d1 T2 d2.
Proof.
  intros Γ Σ T1 d1 T2 d2 H. induction H; intros Σ' Hlen; econstructor; eauto using closed_ty_loc_weaken, qstp_len_weaken.
Qed.

Lemma has_type_len_weaken : forall Γ φ Σ t T d,
  has_type Γ φ Σ t T d ->
  forall Σ', ‖Σ‖ <= ‖Σ'‖ ->
  (forall l o c, sindexr l o Σ = Some c -> sindexr l o Σ' = Some c) ->
  has_type Γ φ Σ' t T d.
Proof.
  intros Γ φ Σ t T d H. induction H; intros Σ' Hlen Hlook.
  - eapply t_tabs; eauto using closed_ty_loc_weaken, closed_Qual_loc_weaken, closed_tm_loc_weaken.
  - eapply t_tapp; eauto using closed_ty_loc_weaken, closed_Qual_loc_weaken.
  - eapply t_tapp_fresh; eauto using closed_ty_loc_weaken, closed_Qual_loc_weaken.
  - eapply t_base; eauto using closed_Qual_loc_weaken.
  - eapply t_var; eauto using closed_ty_loc_weaken, closed_Qual_loc_weaken.
  - eapply t_abs; eauto using closed_ty_loc_weaken, closed_Qual_loc_weaken, closed_tm_loc_weaken.
  - eapply t_app; eauto.
  - eapply t_app_fresh; eauto.
  - eapply t_loc; eauto using closed_ty_loc_weaken, closed_Qual_loc_weaken.
  - eapply t_ref; eauto using closed_ty_loc_weaken.
  - eapply t_refat; eauto.
  - eapply t_deref; eauto.
  - eapply t_assign; eauto.
  - eapply t_sub; eauto using stp_len_weaken.
  - eapply t_withr; eauto using closed_ty_loc_weaken, closed_Qual_loc_weaken, closed_tm_loc_weaken.
  - eapply t_withc; eauto using closed_ty_loc_weaken, closed_Qual_loc_weaken.
    eapply Nat.lt_le_trans; [exact H|exact Hlen].
Qed.

Lemma vtp_len_weaken : forall Σ ϰ φ v T d,
  vtp Σ ϰ φ v T d ->
  forall Σ', ‖Σ‖ <= ‖Σ'‖ ->
  (forall l o c, sindexr l o Σ = Some c -> sindexr l o Σ' = Some c) ->
  vtp Σ' ϰ φ v T d.
Proof.
  intros Σ ϰ φ v T d H. induction H; intros Σ' Hlen Hlook.
  - eapply vtp_tabs; eauto using closed_tm_loc_weaken, closed_ty_loc_weaken, closed_Qual_loc_weaken, has_type_len_weaken, stp_len_weaken, qstp_len_weaken.
  - eapply vtp_base; eauto using closed_Qual_loc_weaken.
  - eapply vtp_loc with (T:=T) (q1:=q1).
    + eapply closed_Qual_loc_weaken; [exact H|exact Hlen].
    + eapply closed_ty_loc_weaken; [exact H0|exact Hlen].
    + eapply closed_Qual_loc_weaken; [exact H1|exact Hlen].
    + eapply closed_Qual_loc_weaken; [exact H2|exact Hlen].
    + exact H3.
    + exact (Hlook l o (T,q1) H4).
    + eapply stp_len_weaken; [exact H5|exact Hlen].
    + eapply stp_len_weaken; [exact H6|exact Hlen].
    + eapply qstp_len_weaken; [exact H7|exact Hlen].
    + exact H8.
    + eapply qstp_len_weaken; [exact H9|exact Hlen].
    + eapply qstp_len_weaken; [exact H10|exact Hlen].
    + exact H11.
  - eapply vtp_abs; eauto using closed_tm_loc_weaken, closed_ty_loc_weaken, closed_Qual_loc_weaken, has_type_len_weaken, stp_len_weaken, qstp_len_weaken.
  - eapply vtp_top; eauto.
Qed.

Lemma wf_senvs_len_weaken : forall L (c:senvs),
  wf_senvs L c -> forall L', L <= L' -> wf_senvs L' c.
Proof.
  intros L c H L' Hle x T q Hx. destruct (H x T q Hx) as [Hq [Ht Hq']].
  split; [exact Hq|]. split.
  - eapply closed_ty_loc_weaken; [exact Ht|exact Hle].
  - eapply closed_Qual_loc_weaken; [exact Hq'|exact Hle].
Qed.

Lemma wf_senvc_len_weaken : forall L (c:senvs),
  wf_senvc L c -> forall L', L <= L' -> wf_senvc L' c.
Proof.
  intros L c [Hp Hw] L' Hle. split; [exact Hp|].
  eapply wf_senvs_len_weaken; eauto.
Qed.

Lemma wf_senvs_singleton : forall L T q,
  ♦∉ q -> closed_ty 0 0 L T -> closed_Qual 0 0 L q↑ ->
  forall L', L <= L' -> wf_senvs L' ((T,q) :: nil).
Proof.
  intros L T q Hf Ht Hq L' Hle x T' q' Hx.
  cbn [indexr] in Hx. destruct x.
  - cbn in Hx. injection Hx as -> ->. split; [exact Hf|]. split.
    + eapply closed_ty_loc_weaken; [exact Ht|exact Hle].
    + eapply closed_Qual_loc_weaken; [exact Hq|exact Hle].
  - simpl in Hx. discriminate Hx.
Qed.

Lemma wf_senv_cons : forall (Σ:senv) T q,
  wf_senv Σ -> ♦∉ q -> closed_ty 0 0 (‖Σ‖) T -> closed_Qual 0 0 (‖Σ‖) q↑ ->
  wf_senv (((T,q) :: nil) :: Σ).
Proof.
  intros Σ T q HΣ Hf Ht Hq l c Hc.
  rewrite indexr_cons in Hc.
  destruct (Nat.eqb l (length Σ)) eqn:E.
  - injection Hc as Hce. subst c.
    split.
    + cbn. exact (Nat.lt_0_succ 0).
    + eapply wf_senvs_singleton with (L:=‖Σ‖) (L':=S (‖Σ‖)); [exact Hf|exact Ht|exact Hq|apply Nat.le_succ_diag_r].
  - apply wf_senvc_len_weaken with (L:=‖Σ‖) (L':=S (‖Σ‖)); [exact (HΣ l c Hc)|apply Nat.le_succ_diag_r].
Qed.

Lemma sindexr_front_lookup : forall (c0:senvs) (Σ:senv) l o x,
  sindexr l o Σ = Some x -> sindexr l o (c0 :: Σ) = Some x.
Proof.
  intros c0 Σ. induction Σ as [|c Σ' IH]; intros l o x H.
  - cbn [sindexr] in H. discriminate H.
  - assert (Hlt : l < length (c :: Σ')) by (eapply sindexr_Some_lt; eauto).
    simpl in Hlt. cbn [sindexr] in H. cbn [sindexr].
    change ((if Nat.eqb l (S (‖Σ'‖)) then indexr o c0
             else if Nat.eqb l (‖Σ'‖) then indexr o c else sindexr l o Σ') = Some x).
    replace (Nat.eqb l (S (‖Σ'‖))) with false
      by (symmetry; apply Nat.eqb_neq; lia).
    simpl. exact H.
Qed.

Lemma n_dom'_cons_Some_new : forall {X} (c:list X) (σ:list (option (list X))),
  n_dom' (Some c :: σ) (length σ) = true.
Proof.
  intros. unfold n_dom'.
  replace (length σ <? length (Some c :: σ)) with true
    by (symmetry; apply Nat.ltb_lt; simpl; lia).
  rewrite indexr_cons. rewrite Nat.eqb_refl. simpl. reflexivity.
Qed.

Lemma qdom'_cons_subq : forall {X A} (σ:list (option (list X))) (c:list X)
  (c0:A) (Σ:list A),
  qdom' σ ⊑↑ qdom Σ -> length σ = length Σ ->
  qdom' (Some c :: σ) ⊑↑ qdom (c0 :: Σ).
Proof.
  intros X A σ c c0 Σ [Hf [H1 [H2 H3]]] Hlen.
  unfold N_sub in H3. unfold Subq. split.
  - change (Is_true true -> Is_true true). intros; exact I.
  - split.
    + change (forall x, N_lift n_empty x -> N_lift n_empty x). auto.
    + split.
      * change (forall x, N_lift n_empty x -> N_lift n_empty x). auto.
      * change (forall x, n_dom' (Some c :: σ) x = true -> n_dom (c0 :: Σ) x = true).
        intros x Hx.
        unfold n_dom. apply Nat.ltb_lt.
        unfold n_dom' in Hx. apply andb_true_iff in Hx. destruct Hx as [Hltx Hcell].
        apply Nat.ltb_lt in Hltx.
        destruct (lt_dec x (length σ)) as [Hxlt|Hxge].
        -- assert (Hcell' : (match indexr x σ with Some (Some _) => true | _ => false end) = true).
           { rewrite indexr_cons in Hcell.
             replace (Nat.eqb x (length σ)) with false in Hcell
               by (symmetry; apply Nat.eqb_neq; lia). simpl in Hcell. exact Hcell. }
           specialize (H3 x). unfold N_lift in H3.
           assert (Hx' : n_dom' σ x = true).
           { unfold n_dom'. apply andb_true_iff. split; [apply Nat.ltb_lt; exact Hxlt|exact Hcell']. }
           specialize (H3 Hx'). unfold n_dom in H3. apply Nat.ltb_lt in H3. simpl.
           apply Nat.lt_lt_succ_r; exact H3.
        -- assert (Hxeq : x = length σ).
           { apply Nat.le_antisymm.
             - exact (proj1 (Nat.lt_succ_r x (length σ)) Hltx).
             - lia. }
           subst x. rewrite Hlen. simpl.
           apply Nat.lt_succ_diag_r.
Qed.

Lemma qloc_new_subq_qdom : forall (Σ:senv) (c:senvs),
  &!(‖Σ‖) ⊑↑ qdom (c :: Σ).
Proof.
  intros Σ c. unfold Subq. split.
  - change (False -> True). intros; exact I.
  - split.
    + change (forall x, N_lift n_empty x -> N_lift n_empty x). auto.
    + split.
      * change (forall x, N_lift n_empty x -> N_lift n_empty x). auto.
      * change (forall x, N_lift (n_one (‖Σ‖)) x -> N_lift (n_dom (c :: Σ)) x).
        intros x Hx. unfold N_lift in *. unfold n_one in Hx.
        apply Nat.eqb_eq in Hx. subst x. unfold n_dom.
        apply Nat.ltb_lt. apply Nat.lt_succ_diag_r.
Qed.

Lemma qdom_cons_subq : forall (Σ:senv) (c:senvs),
  qdom Σ ⊑↑ qdom (c :: Σ).
Proof.
  intros Σ c. unfold Subq. split.
  - change (True -> True). intros; exact I.
  - split.
    + change (forall x, N_lift n_empty x -> N_lift n_empty x). auto.
    + split.
      * change (forall x, N_lift n_empty x -> N_lift n_empty x). auto.
      * change (forall x, N_lift (n_dom Σ) x -> N_lift (n_dom (c :: Σ)) x).
        intros x Hx. unfold N_lift in *. unfold n_dom in *.
        apply Nat.ltb_lt in Hx. apply Nat.ltb_lt. simpl. lia.
Qed.

Lemma qor_idem : forall a, qor a a = a.
Proof.
  intros. apply qual_ext.
  - unfold qor, qfresh. simpl. apply orb_diag.
  - unfold qor, qfvs. simpl. apply functional_extensionality. intro x. unfold n_or. apply orb_diag.
  - unfold qor, qbvs. simpl. apply functional_extensionality. intro x. unfold n_or. apply orb_diag.
  - unfold qor, qlocs. simpl. apply functional_extensionality. intro x. unfold n_or. apply orb_diag.
Qed.

Lemma qor_subq_same : forall a b c, a ⊑↑ c -> b ⊑↑ c -> qor a b ⊑↑ c.
Proof.
  intros. eapply Subq_trans.
  - apply qor_subq_mono; [exact H|exact H0].
  - rewrite qor_idem. apply Subq_refl.
Qed.

Lemma phi_cons_subq_qdom : forall (Σ:senv) (c:senvs) φ,
  φ ⊑↑ qdom Σ -> qor φ (&!(‖Σ‖)) ⊑↑ qdom (c :: Σ).
Proof.
  intros. eapply qor_subq_same.
  - eapply Subq_trans; [exact H|apply qdom_cons_subq].
  - apply qloc_new_subq_qdom.
Qed.

Lemma qand_qor_distrib_l : forall a b c,
  qand (qor a b) c = qor (qand a c) (qand b c).
Proof.
  intros. apply qual_ext.
  - unfold qand, qor, qfresh. simpl.
    destruct (fst (fst (fst a))),(fst (fst (fst b))),(fst (fst (fst c))); reflexivity.
  - unfold qand, qor, qfvs. simpl. apply functional_extensionality. intro x.
    unfold n_and, n_or. destruct (snd (fst (fst a)) x),(snd (fst (fst b)) x),(snd (fst (fst c)) x); reflexivity.
  - unfold qand, qor, qbvs. simpl. apply functional_extensionality. intro x.
    unfold n_and, n_or. destruct (snd (fst a) x),(snd (fst b) x),(snd (fst c) x); reflexivity.
  - unfold qand, qor, qlocs. simpl. apply functional_extensionality. intro x.
    unfold n_and, n_or. destruct (snd a x),(snd b x),(snd c x); reflexivity.
Qed.

Lemma qand_loc_closed_empty : forall l (ϰ:qual),
  closed_Qual 0 0 l (Q_lift ϰ) -> qand (&!l) ϰ = q_empty.
Proof.
  intros l ϰ Hc. apply qual_ext.
  - unfold qand, q_empty, qfresh. simpl. destruct (qfresh ϰ); reflexivity.
  - unfold qand, q_empty, qfvs. simpl. apply functional_extensionality. intro x.
    unfold n_and, n_empty. reflexivity.
  - unfold qand, q_empty, qbvs. simpl. apply functional_extensionality. intro x.
    unfold n_and, n_empty. reflexivity.
  - unfold qand, q_empty, qlocs. simpl. apply functional_extensionality. intro x.
    unfold n_and, n_one, n_empty. destruct (Nat.eqb x l) eqn:E.
    + apply Nat.eqb_eq in E. subst x. destruct (snd ϰ l) eqn:Hq; [|simpl; reflexivity].
      exfalso. pose proof (closed_qual_qlocs_bound 0 0 l ϰ Hc l Hq). lia.
    + reflexivity.
Qed.

Lemma kill_sep_cons : forall (Σ:senv) (c:senvs) ϰ φ,
  kill_sep ϰ φ -> closed_Qual 0 0 (‖Σ‖) (Q_lift ϰ) ->
  kill_sep ϰ (qor φ (&!(‖Σ‖))).
Proof.
  intros Σ c ϰ φ Hk Hc. unfold kill_sep in *.
  rewrite qand_qor_distrib_l.
  rewrite qand_loc_closed_empty; [|exact Hc].
  rewrite qor_empty_r. exact Hk.
Qed.

Lemma subq_qor_loc_elim : forall a b l,
  closed_Qual 0 0 l (Q_lift a) -> a ⊑↑ qor b (&!l) -> a ⊑↑ b.
Proof.
  intros a b l Hc [Hf [H1 [H2 H3]]].
  unfold N_sub in H1, H2, H3. unfold Subq. split.
  - change (Is_true (qfresh a) -> Is_true (qfresh b)). intros Ha.
    apply Hf in Ha. unfold qor in Ha. simpl in Ha.
    destruct (qfresh b) eqn:Eb.
    + reflexivity.
    + exfalso. unfold Is_true in Ha. simpl in Ha. exact Ha.
  - split.
    + change (forall x, N_lift (qfvs a) x -> N_lift (qfvs b) x). intros x Hx.
      specialize (H1 x Hx). unfold N_lift in *. simpl in H1.
      apply orb_true_iff in H1. destruct H1 as [H|H]; [exact H|discriminate H].
    + split.
      * change (forall x, N_lift (qbvs a) x -> N_lift (qbvs b) x). intros x Hx.
        specialize (H2 x Hx). unfold N_lift in *. simpl in H2.
        apply orb_true_iff in H2. destruct H2 as [H|H]; [exact H|discriminate H].
      * change (forall x, N_lift (qlocs a) x -> N_lift (qlocs b) x). intros x Hx.
        specialize (H3 x Hx). unfold N_lift in *.
        apply orb_true_iff in H3. destruct H3 as [H|H]; [exact H|].
        unfold n_one in H. apply Nat.eqb_eq in H. subst x.
        exfalso. pose proof (closed_qual_qlocs_bound 0 0 l a Hc l Hx). lia.
Qed.

Lemma indexr_front_lookup : forall {X} (c0:X) (l:list X) k x,
  indexr k l = Some x -> indexr k (c0 :: l) = Some x.
Proof.
  intros X c0 l k x H.
  assert (Hlt : k < length l) by (eapply indexr_Some_lt; eauto).
  rewrite indexr_cons.
  replace (Nat.eqb k (length l)) with false
    by (symmetry; apply Nat.eqb_neq; lia).
  simpl. exact H.
Qed.

Lemma indexr_new_head : forall {X} (x:X) (l:list X),
  indexr (length l) (x :: l) = Some x.
Proof. intros. rewrite indexr_cons. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma indexr_cons_old : forall {X} (c0:X) (l:list X) k,
  k < length l -> indexr k (c0 :: l) = indexr k l.
Proof.
  intros. rewrite indexr_cons.
  replace (Nat.eqb k (length l)) with false
    by (symmetry; apply Nat.eqb_neq; lia).
  reflexivity.
Qed.

Lemma mem_qor_loc_elim : forall l φ k,
  l ∈ₗ (qor φ (&!k)) -> l <> k -> l ∈ₗ φ.
Proof.
  intros l φ k H Hne. unfold qmem in *. simpl in H. unfold N_lift in *.
  apply orb_true_iff in H. destruct H as [H|H]; [exact H|].
  exfalso. apply Hne. unfold n_one in H. apply Nat.eqb_eq in H. exact H.
Qed.

Lemma mem_qor_new_loc : forall l φ,
  l ∈ₗ (qor φ (&!l)).
Proof.
  intros. unfold qmem. simpl. unfold N_lift, n_or. rewrite orb_true_iff. right.
  unfold n_one. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma wf_senv_cell_qual_closed : forall (Σ:senv) l (cty:senvs) o T q,
  wf_senv Σ -> indexr l Σ = Some cty -> indexr o cty = Some (T,q) ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift q).
Proof.
  intros Σ l cty o T q HΣ Hl Ho.
  destruct (HΣ l cty Hl) as [Hp Hws].
  exact (proj2 (proj2 (Hws o T q Ho))).
Qed.

Lemma CtxOK_cons : forall Γ φ (Σ:senv) ϰ σ T q v,
  CtxOK Γ φ Σ ϰ σ ->
  wf_senv Σ ->
  value v ->
  closed_ty 0 0 (‖Σ‖) T ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift q) ->
  vtp (((T,q) :: nil) :: Σ) ϰ (qor φ (&!(‖Σ‖))) v T q ->
  CtxOK Γ (qor φ (&!(‖Σ‖))) (((T,q) :: nil) :: Σ) ϰ (Some (v :: nil) :: σ).
Proof.
  intros Γ φ Σ ϰ σ T q v Hctx Hwf Hval HcT Hcq Hvtp.
  destruct Hctx as [Hqdom [Hlen [Hphi [Hcl [Hkill Hcell]]]]].
  split.
  - apply qdom'_cons_subq with (σ:=σ) (c:=(v::nil)) (c0:=((T,q)::nil)) (Σ:=Σ); [exact Hqdom|exact Hlen].
  - split.
    + simpl. rewrite Hlen. reflexivity.
    + split.
      * exact (phi_cons_subq_qdom Σ ((T,q) :: nil) φ Hphi).
      * split.
        -- eapply closed_Qual_loc_weaken; [exact Hcl|apply Nat.le_succ_diag_r].
        -- split.
           ++ apply (kill_sep_cons Σ (((T,q)::nil)) ϰ φ); [exact Hkill|exact Hcl].
           ++ intros l o cty T' q'. split.
              ** intros Hmem. unfold N_lift in Hmem.
                 pose proof (closed_qual_qlocs_bound 0 0 (‖Σ‖) ϰ Hcl l Hmem) as Hlt.
                 assert (Hlts : l < length σ) by lia.
                 rewrite (indexr_cons_old (Some (v :: nil)) σ l Hlts).
                 exact (proj1 (Hcell l o cty T' q') Hmem).
              ** intros Hnotmem Hphi' Hlook.
                 destruct (Nat.eqb l (length Σ)) eqn:E.
                 --- apply Nat.eqb_eq in E. subst l.
                     assert (Hnew : indexr (length Σ) (((T,q)::nil)::Σ) = Some ((T,q)::nil))
                       by apply indexr_new_head.
                     change (indexr (length Σ) (((T,q)::nil)::Σ) = Some cty) in Hlook.
                     assert (Hcty : cty = (T,q) :: nil).
                     { rewrite Hnew in Hlook. injection Hlook as ->. reflexivity. }
                     subst cty.
                     exists (v :: nil). split.
                     { split.
                       { assert (Hnew2 : indexr (length σ) (Some (v::nil) :: σ) = Some (Some (v::nil)))
                           by apply indexr_new_head.
                         rewrite <- Hlen. exact Hnew2. }
                       { simpl. reflexivity. } }
                     { intros Ho. destruct o as [|o'].
                       { simpl in Ho. injection Ho as HT Hqe. subst T' q'.
                         exists v. split.
                         { simpl. reflexivity. }
                         { split; [exact Hval|]. intros _. exact Hvtp. } }
                       { simpl in Ho. discriminate Ho. } }
                 --- assert (HltΣ' : l < length (((T,q)::nil)::Σ))
                       by (eapply indexr_Some_lt; exact Hlook).
                     simpl in HltΣ'.
                     assert (Hne : l <> length Σ) by (apply Nat.eqb_neq; exact E).
                     assert (Hle : l <= length Σ) by (apply Nat.lt_succ_r; exact HltΣ').
                     assert (Hlt : l < length Σ) by lia.
                     assert (Hlts : l < length σ) by (rewrite Hlen; exact Hlt).
                     assert (Hphi_old : l ∈ₗ φ).
                     { eapply mem_qor_loc_elim; [exact Hphi'|exact Hne]. }
                     assert (HlΣ : indexr l Σ = Some cty).
                     { exact (eq_trans (eq_sym (indexr_cons_old ((T,q)::nil) Σ l Hlt)) Hlook). }
                     destruct (Hcell l o cty T' q') as [_ Hinner].
                     destruct (Hinner Hnotmem Hphi_old HlΣ) as [ctm Hspec2].
                     destruct Hspec2 as [HAB Hspec].
                     destruct HAB as [Hctm Hlencty].
                     exists ctm. split.
                     { split.
                       { rewrite (indexr_cons_old (Some (v :: nil)) σ l Hlts). exact Hctm. }
                       { exact Hlencty. } }
                     { intros Ho.
                       destruct (Hspec Ho) as [v0 Hv0rest].
                       destruct Hv0rest as [Hv0 Hrest].
                       destruct Hrest as [Hval0 Hvtp0].
                       exists v0. split; [exact Hv0|]. split; [exact Hval0|].
                       intros Hq'.
                       assert (Hqold : q' ⊑↑ φ).
                       { eapply subq_qor_loc_elim.
                         - exact (wf_senv_cell_qual_closed Σ l cty o T' q' Hwf HlΣ Ho).
                         - exact Hq'. }
                       assert (HvΣ : vtp (((T,q)::nil)::Σ) ϰ φ v0 T' q').
                       { eapply vtp_len_weaken; [exact (Hvtp0 Hqold)|apply Nat.le_succ_diag_r| intros lx ox cx Hx; exact (sindexr_front_lookup ((T,q)::nil) Σ lx ox cx Hx)]. }
                       eapply vtp_weaken_phi; [exact HvΣ|apply qor_subq_l]. }
Qed.

Lemma supdate_cell : forall {A} (σ:list (option (list A))) l o v c,
  indexr l σ = Some c -> indexr l (supdate σ l o v) = Some (update' c o v).
Proof.
  intros A σ. induction σ as [|a σ' IH]; intros l o v c H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb l (length σ')) eqn:E.
    + injection H as Hca. cbn [supdate indexr]. rewrite E. rewrite Hca. reflexivity.
    + cbn [supdate indexr]. rewrite length_supdate. rewrite E. simpl. apply IH. exact H.
Qed.

Lemma supdate_other : forall {A} (σ:list (option (list A))) l o v k,
  k <> l -> indexr k (supdate σ l o v) = indexr k σ.
Proof.
  intros A σ. induction σ as [|a σ' IH]; intros l o v k Hne; simpl.
  - reflexivity.
  - destruct (Nat.eqb l (length σ')) eqn:El.
    + assert (Hk : Nat.eqb k (length σ') = false).
      { apply Nat.eqb_neq. intro Hkl. apply Hne. rewrite Hkl. symmetry. apply Nat.eqb_eq. exact El. }
      cbn [supdate indexr]. try rewrite El. cbn [indexr]. try rewrite Hk. reflexivity.
    + cbn [supdate indexr]. try rewrite El. cbn [indexr]. rewrite length_supdate.
      destruct (Nat.eqb k (length σ')) eqn:Ek.
      * reflexivity.
      * apply IH. exact Hne.
Qed.

Lemma supdate_none : forall (σ:store) l o v,
  indexr l σ = None -> indexr l (supdate σ l o v) = None.
Proof.
  intros σ. induction σ as [|a σ' IH]; intros l o v H; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb l (length σ')) eqn:E.
    + discriminate H.
    + cbn [supdate]. try rewrite E. cbn [indexr].
      rewrite length_supdate. try rewrite E. simpl.
      apply IH. exact H.
Qed.

Lemma cell_present_supdate : forall (σ:store) l o v x,
  (match indexr x (supdate σ l o v) with Some (Some _) => true | _ => false end) =
  (match indexr x σ with Some (Some _) => true | _ => false end).
Proof.
  intros σ l o v x. destruct (Nat.eqb x l) eqn:E.
  - apply Nat.eqb_eq in E. subst x.
    destruct (indexr l σ) as [c0|] eqn:H.
    + destruct c0 as [c|] eqn:Hc.
      * assert (Hup : indexr l (supdate σ l o v) = Some (update' (Some c) o v))
          by (eapply supdate_cell; exact H).
        rewrite Hup. simpl. reflexivity.
      * assert (Hup : indexr l (supdate σ l o v) = Some (update' None o v))
          by (eapply supdate_cell; exact H).
        rewrite Hup. simpl. reflexivity.
    + assert (Hup : indexr l (supdate σ l o v) = None) by (eapply supdate_none; exact H).
      rewrite Hup. reflexivity.
  - assert (Hup : indexr x (supdate σ l o v) = indexr x σ)
      by (apply supdate_other; apply Nat.eqb_neq; exact E).
    rewrite Hup. reflexivity.
Qed.

Lemma qdom'_supdate : forall (σ:store) l o v,
  qdom' (supdate σ l o v) = qdom' σ.
Proof.
  intros. unfold qdom'. f_equal.
  apply functional_extensionality. intro x. unfold n_dom'.
  rewrite length_supdate. rewrite cell_present_supdate. reflexivity.
Qed.

Lemma indexr_update_lt : forall {A} (s:list A) l (v:A),
  l < length s -> indexr l (update s l v) = Some v.
Proof.
  intros A s. induction s as [|x xs IH]; intros l v Hlt; simpl in Hlt.
  - lia.
  - rewrite update_cons. destruct (Nat.eqb l (length xs)) eqn:E.
    + apply Nat.eqb_eq in E. subst l. rewrite indexr_cons. rewrite Nat.eqb_refl. reflexivity.
    + assert (Hlt' : l < length xs) by (apply Nat.eqb_neq in E; lia).
      rewrite indexr_cons. rewrite length_update. rewrite E. simpl. apply IH. exact Hlt'.
Qed.

Lemma qdom'_update_None_subq : forall (σ:store) l,
  qdom' (update σ l None) ⊑↑ qdom' σ.
Proof.
  intros σ l. unfold Subq. split.
  - change (True -> True). intros; exact I.
  - split.
    + change (forall x, N_lift n_empty x -> N_lift n_empty x). auto.
    + split.
      * change (forall x, N_lift n_empty x -> N_lift n_empty x). auto.
      * change (forall x, n_dom' (update σ l None) x = true -> n_dom' σ x = true).
        intros x Hx. unfold n_dom' in *. apply andb_true_iff in Hx.
        destruct Hx as [Hlt Hcell]. apply andb_true_iff. split.
        -- apply Nat.ltb_lt in Hlt. rewrite length_update in Hlt. apply Nat.ltb_lt. exact Hlt.
        -- destruct (Nat.eqb x l) eqn:E.
           ++ apply Nat.eqb_eq in E. subst x.
              assert (Hidx : indexr l (update σ l None) = Some None).
              { apply indexr_update_lt. apply Nat.ltb_lt in Hlt. rewrite length_update in Hlt. exact Hlt. }
              rewrite Hidx in Hcell. simpl in Hcell. discriminate Hcell.
           ++ apply Nat.eqb_neq in E.
              rewrite (indexr_update_other σ l None x E) in Hcell. exact Hcell.
Qed.

Lemma CtxOK_supdate : forall Γ φ (Σ:senv) ϰ σ l o v T q cty,
  CtxOK Γ φ Σ ϰ σ ->
  value v ->
  indexr l Σ = Some cty ->
  indexr o cty = Some (T,q) ->
  vtp Σ ϰ φ v T q ->
  CtxOK Γ φ Σ ϰ (supdate σ l o v).
Proof.
  intros Γ φ Σ ϰ σ l o v T q cty Hctx Hval HlΣ Htq Hvtp.
  destruct Hctx as [Hqdom [Hlen [Hphi [Hcl [Hkill Hcell]]]]].
  split.
  - rewrite qdom'_supdate. exact Hqdom.
  - split.
    + rewrite length_supdate. exact Hlen.
    + split; [exact Hphi|]. split; [exact Hcl|]. split; [exact Hkill|].
      intros l' o' cty' T' q'. split.
      { intros Hmem. destruct (Nat.eqb l' l) eqn:E.
        { apply Nat.eqb_eq in E. subst l'.
          assert (Hold : indexr l σ = Some None) by (exact (proj1 (Hcell l o cty T q) Hmem)).
          assert (Hup : indexr l (supdate σ l o v) = Some (update' None o v))
            by (eapply supdate_cell; exact Hold).
          rewrite Hup. simpl. reflexivity. }
        { apply Nat.eqb_neq in E.
          assert (Hup : indexr l' (supdate σ l o v) = indexr l' σ)
            by (apply supdate_other; exact E).
          rewrite Hup. exact (proj1 (Hcell l' o' cty' T' q') Hmem). } }
      { intros Hnotmem Hphi' Hlook. destruct (Nat.eqb l' l) eqn:E.
        { apply Nat.eqb_eq in E. subst l'.
          assert (Hcty' : cty' = cty).
          { rewrite HlΣ in Hlook. injection Hlook as ->. reflexivity. }
          subst cty'.
          destruct (Hcell l o' cty T' q') as [_ Hinner].
          destruct (Hinner Hnotmem Hphi' HlΣ) as [ctm Hspec2].
          destruct Hspec2 as [HAB Hspec].
          destruct HAB as [Hctm Hlencty].
          exists (update ctm o v). split.
          { split.
            { assert (Hup : indexr l (supdate σ l o v) = Some (update' (Some ctm) o v))
                by (eapply supdate_cell; exact Hctm).
              rewrite Hup. simpl. reflexivity. }
            { rewrite length_update. exact Hlencty. } }
          { intros Ho. destruct (Nat.eqb o' o) eqn:Eo.
            { apply Nat.eqb_eq in Eo. subst o'.
              rewrite Htq in Ho. injection Ho as HTe Hqe. subst T' q'.
              destruct (Hspec Htq) as [old [Hold [Hvalold _]]].
              exists v. split.
              { apply (indexr_update_same ctm o v old Hold). }
              { split; [exact Hval|]. intros _. exact Hvtp. } }
            { apply Nat.eqb_neq in Eo.
              destruct (Hspec Ho) as [v0 [Hv0 [Hval0 Hvtp0]]].
              exists v0. split.
              { rewrite indexr_update_other; [exact Hv0|exact Eo]. }
              { split; [exact Hval0|exact Hvtp0]. } } } }
        { apply Nat.eqb_neq in E.
          assert (Hup : indexr l' (supdate σ l o v) = indexr l' σ)
            by (apply supdate_other; exact E).
          destruct (Hcell l' o' cty' T' q') as [_ Hinner].
          destruct (Hinner Hnotmem Hphi' Hlook) as [ctm Hspec2].
          destruct Hspec2 as [HAB Hspec].
          destruct HAB as [Hctm Hlencty].
          exists ctm. split.
          { split; [rewrite Hup; exact Hctm|exact Hlencty]. }
          { exact Hspec. } } }
Qed.

Lemma length_sinsert : forall {A} (s:list (list A)) l (x:A),
  length (sinsert s l x) = length s.
Proof.
  intros A s. induction s as [|c s' IH]; intros l x; simpl.
  - reflexivity.
  - cbn [sinsert]. destruct (Nat.eqb l (length s')); simpl; [reflexivity|]. f_equal. apply IH.
Qed.

Lemma sinsert_cell : forall {A} (s:list (list A)) l (x:A) c,
  indexr l s = Some c -> indexr l (sinsert s l x) = Some (x :: c).
Proof.
  intros A s. induction s as [|c0 s' IH]; intros l x c H; simpl in *.
  - discriminate.
  - destruct (Nat.eqb l (length s')) eqn:E.
    + cbn [sinsert indexr]. rewrite E. simpl. injection H as Hc. subst c. reflexivity.
    + cbn [sinsert indexr]. rewrite length_sinsert. rewrite E. simpl. apply IH. exact H.
Qed.

Lemma sinsert_other : forall {A} (s:list (list A)) l (x:A) k,
  k <> l -> indexr k (sinsert s l x) = indexr k s.
Proof.
  intros A s. induction s as [|c s' IH]; intros l x k Hne.
  - reflexivity.
  - destruct (Nat.eqb l (length s')) eqn:El.
    + assert (Hk : Nat.eqb k (length s') = false).
      { apply Nat.eqb_neq. intro Hkl. apply Hne. rewrite Hkl. symmetry. apply Nat.eqb_eq. exact El. }
      cbn [sinsert indexr]. rewrite El. cbn [indexr]. rewrite Hk. reflexivity.
    + cbn [sinsert indexr]. rewrite El. cbn [indexr]. rewrite length_sinsert.
      destruct (Nat.eqb k (length s')) eqn:Ek.
      * reflexivity.
      * apply IH. exact Hne.
Qed.


Lemma sindexr_sinsert_lookup : forall {X} (Σ:list (list X)) l x l' o c,
  sindexr l' o Σ = Some c -> sindexr l' o (sinsert Σ l x) = Some c.
Proof.
  intros X Σ l x l' o c H.
  rewrite sindexr_lookup in H. rewrite sindexr_lookup.
  destruct (indexr l' Σ) as [cell|] eqn:Ecell; [|discriminate H].
  destruct (Nat.eqb l' l) eqn:El.
  - apply Nat.eqb_eq in El. subst l'.
    rewrite (sinsert_cell Σ l x cell Ecell).
    simpl.
    assert (Hlt : o < length cell) by (eapply indexr_Some_lt; exact H).
    exact (eq_trans (indexr_cons_old x cell o Hlt) H).
  - apply Nat.eqb_neq in El.
    rewrite (sinsert_other Σ l x l' El).
    rewrite Ecell. simpl. exact H.
Qed.

Lemma cinsert_none : forall {A} (σ:list (option (list A))) l v,
  indexr l σ = None -> indexr l (cinsert σ l v) = None.
Proof.
  intros A σ. induction σ as [|a σ' IH]; intros l v H; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb l (length σ')) eqn:E.
    + discriminate H.
    + cbn [cinsert]. try rewrite E. cbn [indexr]. rewrite length_cinsert. try rewrite E. simpl.
      apply IH. exact H.
Qed.

Lemma cell_present_cinsert : forall {A} (σ:list (option (list A))) l v x,
  (match indexr x (cinsert σ l v) with Some (Some _) => true | _ => false end) =
  (match indexr x σ with Some (Some _) => true | _ => false end).
Proof.
  intros A σ l v x. destruct (Nat.eqb x l) eqn:E.
  - apply Nat.eqb_eq in E. subst x.
    destruct (indexr l σ) as [c0|] eqn:H.
    + destruct c0 as [c|] eqn:Hc.
      * assert (Hup : indexr l (cinsert σ l v) = Some (insert' (Some c) v))
          by (eapply cinsert_cell; exact H).
        rewrite Hup. simpl. reflexivity.
      * assert (Hup : indexr l (cinsert σ l v) = Some (insert' None v))
          by (eapply cinsert_cell; exact H).
        rewrite Hup. simpl. reflexivity.
    + assert (Hup : indexr l (cinsert σ l v) = None) by (eapply cinsert_none; exact H).
      rewrite Hup. reflexivity.
  - assert (Hup : indexr x (cinsert σ l v) = indexr x σ)
      by (apply cinsert_other; apply Nat.eqb_neq; exact E).
    rewrite Hup. reflexivity.
Qed.

Lemma qdom'_cinsert : forall {A} (σ:list (option (list A))) l v,
  qdom' (cinsert σ l v) = qdom' σ.
Proof.
  intros. unfold qdom'. f_equal.
  apply functional_extensionality. intro x. unfold n_dom'.
  rewrite length_cinsert. rewrite cell_present_cinsert. reflexivity.
Qed.

Lemma qdom_sinsert : forall {A} (Σ:list (list A)) l x,
  qdom (sinsert Σ l x) = qdom Σ.
Proof.
  intros. unfold qdom. f_equal.
  apply functional_extensionality. intro y. unfold n_dom.
  rewrite length_sinsert. reflexivity.
Qed.

Lemma qdom_sinsert_senv : forall (Σ:senv) l (x:ty*qual),
  qdom (sinsert Σ l x) = qdom Σ.
Proof.
  intros. unfold qdom. f_equal.
  apply functional_extensionality. intro y. unfold n_dom.
  rewrite length_sinsert. reflexivity.
Qed.

Lemma vtp_sinsert : forall (Σ:senv) l x ϰ φ v0 T0 q0,
  vtp Σ ϰ φ v0 T0 q0 -> vtp (sinsert Σ l x) ϰ φ v0 T0 q0.
Proof.
  intros. eapply vtp_len_weaken.
  - exact H.
  - rewrite length_sinsert. apply Nat.le_refl.
  - intros l' o c Hc. exact (sindexr_sinsert_lookup Σ l x l' o c Hc).
Qed.


Lemma length_cinsert_store : forall (σ:store) l (v:tm),
  length (cinsert σ l v) = length σ.
Proof. intros. exact (length_cinsert σ l v). Qed.

Lemma length_sinsert_senv : forall (Σ:senv) l (x:ty*qual),
  length (sinsert Σ l x) = length Σ.
Proof. intros. exact (length_sinsert Σ l x). Qed.


Lemma sinsert_cell_senv : forall (Σ:senv) l (x:ty*qual) c,
  indexr l Σ = Some c -> indexr l (sinsert Σ l x) = Some (x :: c).
Proof. intros. exact (sinsert_cell Σ l x c H). Qed.

Lemma sinsert_other_senv : forall (Σ:senv) l (x:ty*qual) k,
  k <> l -> indexr k (sinsert Σ l x) = indexr k Σ.
Proof. intros. exact (sinsert_other Σ l x k H). Qed.

Lemma cinsert_cell_store : forall (σ:store) l (v:tm) c,
  indexr l σ = Some c -> indexr l (cinsert σ l v) = Some (insert' c v).
Proof. intros. exact (cinsert_cell σ l v c H). Qed.

Lemma cinsert_other_store : forall (σ:store) l (v:tm) k,
  k <> l -> indexr k (cinsert σ l v) = indexr k σ.
Proof. intros. exact (cinsert_other σ l v k H). Qed.

Lemma CtxOK_sinsert : forall Γ φ (Σ:senv) ϰ σ l v T q cty ctm,
  CtxOK Γ φ Σ ϰ σ ->
  value v ->
  indexr l Σ = Some cty ->
  indexr l σ = Some (Some ctm) ->
  vtp (sinsert Σ l (T,q)) ϰ φ v T q ->
  CtxOK Γ φ (sinsert Σ l (T,q)) ϰ (cinsert σ l v).
Proof.
  intros Γ φ Σ ϰ σ l v T q cty ctm Hctx Hval HlΣ Hlσ Hvtp.
  destruct Hctx as [Hqdom [Hlen [Hphi [Hcl [Hkill Hcell]]]]].
  assert (Hq1 : qdom' (cinsert σ l v) = qdom' σ) by apply qdom'_cinsert.
  split.
  - rewrite Hq1. rewrite qdom_sinsert_senv. exact Hqdom.
  - split.
    + rewrite length_cinsert_store. rewrite length_sinsert_senv. exact Hlen.
    + split.
      * rewrite qdom_sinsert_senv. exact Hphi.
      * split.
        -- rewrite length_sinsert_senv. exact Hcl.
        -- split.
           ++ exact Hkill.
           ++ intros l' o' cty' T' q'. split.
              ** intros Hmem. destruct (Nat.eqb l' l) eqn:E.
                 { apply Nat.eqb_eq in E. subst l'.
                   exfalso. pose proof (proj1 (Hcell l 0 cty T q) Hmem) as Hnone.
                   rewrite Hlσ in Hnone. discriminate Hnone. }
                 { apply Nat.eqb_neq in E.
                   assert (Hup : indexr l' (cinsert σ l v) = indexr l' σ)
                     by (apply cinsert_other_store; exact E).
                   rewrite Hup. exact (proj1 (Hcell l' o' cty' T' q') Hmem). }
              ** intros Hnotmem Hphi' Hlook.
                 destruct (Nat.eqb l' l) eqn:E.
                 { apply Nat.eqb_eq in E. subst l'.
                   assert (Hcty : cty' = (T,q) :: cty).
                   { assert (Hsi : indexr l (sinsert Σ l (T,q)) = Some ((T,q) :: cty))
                       by (apply sinsert_cell_senv; exact HlΣ).
                     assert (Heq : Some cty' = Some ((T,q) :: cty))
                       by (exact (eq_trans (eq_sym Hlook) Hsi)).
                     injection Heq as Hc. exact Hc. }
                   subst cty'.
                   destruct (Hcell l o' cty T' q') as [_ Hinner].
                   destruct (Hinner Hnotmem Hphi' HlΣ) as [cell Hspec2].
                   destruct Hspec2 as [HAB Hspec].
                   destruct HAB as [Hcellσ Hlencty].
                   exists (v :: cell). split.
                   { split.
                     { assert (Hsi2 : indexr l (cinsert σ l v) = Some (insert' (Some cell) v))
                         by (apply cinsert_cell_store; exact Hcellσ).
                       rewrite Hsi2. simpl. reflexivity. }
                     { simpl. f_equal. exact Hlencty. } }
                   { intros Ho. destruct (Nat.eqb o' (length cty)) eqn:Eo.
                     { apply Nat.eqb_eq in Eo. subst o'.
                       assert (Hnewty : indexr (length cty) ((T,q) :: cty) = Some (T,q))
                         by apply indexr_new_head.
                       rewrite Hnewty in Ho. injection Ho as HTe Hqe. subst T' q'.
                       assert (Hidx : indexr (length cty) (v :: cell) = Some v).
                       { rewrite Hlencty. apply indexr_new_head. }
                       exists v. split.
                       { exact Hidx. }
                       { split; [exact Hval|]. intros _. exact Hvtp. } }
                     { apply Nat.eqb_neq in Eo.
                       assert (HltΣ : o' < length ((T,q) :: cty)) by (eapply indexr_Some_lt; exact Ho).
                       simpl in HltΣ.
                       assert (Hlt : o' < length cty) by lia.
                       assert (Ho' : indexr o' cty = Some (T',q')).
                       { exact (eq_trans (eq_sym (indexr_cons_old (T,q) cty o' Hlt)) Ho). }
                       destruct (Hspec Ho') as [v0 [Hv0 [Hval0 Hvtp0]]].
                       assert (Hltc : o' < length cell) by (rewrite <- Hlencty; exact Hlt).
                       assert (Hidx : indexr o' (v :: cell) = Some v0).
                       { exact (eq_trans (indexr_cons_old v cell o' Hltc) Hv0). }
                       exists v0. split.
                       { exact Hidx. }
                       { split; [exact Hval0|]. intros Hq'. apply vtp_sinsert. exact (Hvtp0 Hq'). } } } }
                 { apply Nat.eqb_neq in E.
                   assert (Hup : indexr l' (cinsert σ l v) = indexr l' σ)
                     by (apply cinsert_other_store; exact E).
                   assert (HlΣ' : indexr l' Σ = Some cty').
                   { exact (eq_trans (eq_sym (sinsert_other Σ l (T,q) l' E)) Hlook). }
                   destruct (Hcell l' o' cty' T' q') as [_ Hinner].
                   destruct (Hinner Hnotmem Hphi' HlΣ') as [cell Hspec2].
                   destruct Hspec2 as [HAB Hspec].
                   destruct HAB as [Hcellσ Hlencty].
                   exists cell. split.
                   { split; [rewrite Hup; exact Hcellσ|exact Hlencty]. }
                   { intros Ho. destruct (Hspec Ho) as [v0 [Hv0 [Hval0 Hvtp0]]].
                     exists v0. split; [exact Hv0|]. split; [exact Hval0|].
                     intros Hq'. apply vtp_sinsert. exact (Hvtp0 Hq'). } }
Qed.

Lemma qand_subq_mono_l : forall a b c, a ⊑↑ b -> qand a c ⊑↑ qand b c.
Proof.
  intros a b c [Hf [H1 [H2 H3]]]. unfold N_sub in H1,H2,H3. unfold Subq. split.
  - change (Is_true (qfresh a && qfresh c) -> Is_true (qfresh b && qfresh c)).
    intros H. apply Is_true_andb in H. destruct H as [Ha Hc].
    apply Is_true_andb. split; [apply Hf; exact Ha|exact Hc].
  - split.
    + change (forall x, (qfvs a x && qfvs c x) = true -> (qfvs b x && qfvs c x) = true).
      intros x Hx. apply andb_true_iff in Hx. destruct Hx as [Hx Hc].
      apply andb_true_iff. split; [apply H1; exact Hx|exact Hc].
    + split.
      * change (forall x, (qbvs a x && qbvs c x) = true -> (qbvs b x && qbvs c x) = true).
        intros x Hx. apply andb_true_iff in Hx. destruct Hx as [Hx Hc].
        apply andb_true_iff. split; [apply H2; exact Hx|exact Hc].
      * change (forall x, (qlocs a x && qlocs c x) = true -> (qlocs b x && qlocs c x) = true).
        intros x Hx. apply andb_true_iff in Hx. destruct Hx as [Hx Hc].
        apply andb_true_iff. split; [apply H3; exact Hx|exact Hc].
Qed.

Lemma kill_sep_subq_l : forall ϰ φ φ', kill_sep ϰ φ -> φ' ⊑↑ φ -> kill_sep ϰ φ'.
Proof.
  intros ϰ φ φ' Hk Hsub. unfold kill_sep in *.
  eapply Subq_trans; [|exact Hk].
  apply qand_subq_mono_l. exact Hsub.
Qed.

Lemma closed_Qual_qor : forall b f l (a c:qual),
  closed_Qual b f l (Q_lift a) -> closed_Qual b f l (Q_lift c) ->
  closed_Qual b f l (Q_lift (qor a c)).
Proof.
  intros b f l a c Ha Hc. destruct Ha as [Haf [Hab Hal]]. destruct Hc as [Hcf [Hcb Hcl]].
  unfold closed_Qual. split; [|split].
  - unfold closed_Nats in *. intros x Hx. unfold N_lift in *. simpl in Hx.
    apply orb_true_iff in Hx. destruct Hx as [H|H]; [apply Haf in H|apply Hcf in H]; lia.
  - unfold closed_Nats in *. intros x Hx. unfold N_lift in *. simpl in Hx.
    apply orb_true_iff in Hx. destruct Hx as [H|H]; [apply Hab in H|apply Hcb in H]; lia.
  - unfold closed_Nats in *. intros x Hx. unfold N_lift in *. simpl in Hx.
    apply orb_true_iff in Hx. destruct Hx as [H|H]; [apply Hal in H|apply Hcl in H]; lia.
Qed.

Lemma q_remove'_fresh : forall (Σ:senv) k q n, qfresh (q_remove' Σ k q n) = false.
Proof.
  intros Σ k q n. induction n as [|n IH].
  - reflexivity.
  - cbn [q_remove'].
    change (qfresh (if qlocs q n && negb (n_one n k) then q_remove' Σ k q n ⊔ &! n else q_remove' Σ k q n) = false).
    destruct (qlocs q n && negb (n_one n k)) eqn:E.
    + change (orb (qfresh (q_remove' Σ k q n)) (qfresh (&!n)) = false). rewrite IH. reflexivity.
    + exact IH.
Qed.

Lemma q_remove'_fvs_empty : forall (Σ:senv) k q n, qfvs (q_remove' Σ k q n) = n_empty.
Proof.
  intros Σ k q n. induction n as [|n IH].
  - reflexivity.
  - cbn [q_remove'].
    change (qfvs (if qlocs q n && negb (n_one n k) then q_remove' Σ k q n ⊔ &! n else q_remove' Σ k q n) = n_empty).
    destruct (qlocs q n && negb (n_one n k)) eqn:E.
    + apply functional_extensionality. intro y.
      unfold n_or, n_empty.
      change ((qfvs (q_remove' Σ k q n) y || qfvs (&!n) y) = false).
      rewrite (f_equal (fun f => f y) IH). reflexivity.
    + exact IH.
Qed.

Lemma q_remove'_bvs_empty : forall (Σ:senv) k q n, qbvs (q_remove' Σ k q n) = n_empty.
Proof.
  intros Σ k q n. induction n as [|n IH].
  - reflexivity.
  - cbn [q_remove'].
    change (qbvs (if qlocs q n && negb (n_one n k) then q_remove' Σ k q n ⊔ &! n else q_remove' Σ k q n) = n_empty).
    destruct (qlocs q n && negb (n_one n k)) eqn:E.
    + apply functional_extensionality. intro y.
      unfold n_or, n_empty.
      change ((qbvs (q_remove' Σ k q n) y || qbvs (&!n) y) = false).
      rewrite (f_equal (fun f => f y) IH). reflexivity.
    + exact IH.
Qed.

Lemma q_remove'_locs_sub : forall (Σ:senv) k q n x,
  qlocs (q_remove' Σ k q n) x = true -> qlocs q x = true.
Proof.
  intros Σ k q n. induction n as [|n IH]; intros x H.
  - cbn [q_remove'] in H. discriminate H.
  - cbn [q_remove'] in H.
    change (qlocs (if qlocs q n && negb (n_one n k) then q_remove' Σ k q n ⊔ &! n else q_remove' Σ k q n) x = true) in H.
    destruct (qlocs q n && negb (n_one n k)) eqn:E.
    + change (n_or (qlocs (q_remove' Σ k q n)) (n_one n) x = true) in H.
      apply orb_true_iff in H. destruct H as [H|H].
      * apply IH. exact H.
      * unfold n_one in H. apply Nat.eqb_eq in H. subst x.
        apply andb_true_iff in E. tauto.
    + apply IH. exact H.
Qed.

Lemma qfresh_q_remove : forall (Σ:senv) l q, qfresh (q_remove Σ l q) = qfresh q.
Proof.
  intros. unfold q_remove, qor, qfresh. simpl.
  change (orb (qfresh (q_remove' Σ l q (‖Σ‖))) (qfresh q) = qfresh q).
  rewrite q_remove'_fresh. reflexivity.
Qed.

Lemma qfvs_q_remove : forall (Σ:senv) l q, qfvs (q_remove Σ l q) = qfvs q.
Proof.
  intros. unfold q_remove, qor, qfvs. simpl.
  change (n_or (qfvs (q_remove' Σ l q (‖Σ‖))) (qfvs q) = qfvs q).
  rewrite q_remove'_fvs_empty. apply n_or_empty_l.
Qed.

Lemma qbvs_q_remove : forall (Σ:senv) l q, qbvs (q_remove Σ l q) = qbvs q.
Proof.
  intros. unfold q_remove, qor, qbvs. simpl.
  change (n_or (qbvs (q_remove' Σ l q (‖Σ‖))) (qbvs q) = qbvs q).
  rewrite q_remove'_bvs_empty. apply n_or_empty_l.
Qed.

Lemma q_remove_locs_sub : forall (Σ:senv) l q x,
  qlocs (q_remove Σ l q) x = true -> qlocs q x = true.
Proof.
  intros. unfold q_remove in H. unfold qor in H. simpl in H.
  apply orb_true_iff in H. destruct H as [H|H]; [|discriminate H].
  eapply q_remove'_locs_sub; eauto.
Qed.

Lemma q_remove_subq_l : forall (Σ:senv) l (q:qual), q_remove Σ l q ⊑↑ q.
Proof.
  intros Σ l q. unfold Subq. split.
  - change (Is_true (qfresh (q_remove Σ l q)) -> Is_true (qfresh q)).
    rewrite qfresh_q_remove. intros H; exact H.
  - split.
    + change (forall x, N_lift (qfvs (q_remove Σ l q)) x -> N_lift (qfvs q) x).
      rewrite qfvs_q_remove. auto.
    + split.
      * change (forall x, N_lift (qbvs (q_remove Σ l q)) x -> N_lift (qbvs q) x).
        rewrite qbvs_q_remove. auto.
      * change (forall x, N_lift (qlocs (q_remove Σ l q)) x -> N_lift (qlocs q) x).
        intros x Hx. unfold N_lift in *. eapply q_remove_locs_sub; eauto.
Qed.

Lemma n_empty_sub : forall f, n_sub n_empty f.
Proof. intros f x H. unfold n_empty in H. discriminate H. Qed.

Lemma q_empty_subq : forall q, q_empty ⊑↑ q.
Proof.
  intros q. unfold Subq. split.
  - change (False -> Is_true (qfresh q)). intros H; destruct H.
  - split.
    + change (forall x, N_lift n_empty x -> N_lift (qfvs q) x).
      intros x Hx. unfold N_lift, n_empty in Hx.
      exfalso. discriminate Hx.
    + split.
      * change (forall x, N_lift n_empty x -> N_lift (qbvs q) x).
        intros x Hx. unfold N_lift, n_empty in Hx.
        exfalso. discriminate Hx.
      * change (forall x, N_lift n_empty x -> N_lift (qlocs q) x).
        intros x Hx. unfold N_lift, n_empty in Hx.
        exfalso. discriminate Hx.
Qed.

Lemma subq_qdom_fvs_empty : forall (Σ:senv) φ,
  φ ⊑↑ qdom Σ -> qfvs φ = n_empty.
Proof.
  intros. eapply closed_qual_qfvs_empty.
  eapply closed_qual_of_subq_qdom with (b:=0) (f:=0). exact H.
Qed.

Lemma subq_qdom_bvs_empty : forall (Σ:senv) φ,
  φ ⊑↑ qdom Σ -> qbvs φ = n_empty.
Proof.
  intros. eapply closed_qual_qbvs_empty.
  eapply closed_qual_of_subq_qdom with (b:=0) (f:=0). exact H.
Qed.

Lemma q_remove_fvs_empty : forall (Σ:senv) l φ,
  qfvs φ = n_empty -> qfvs (q_remove Σ l φ) = n_empty.
Proof. intros. rewrite qfvs_q_remove. exact H. Qed.

Lemma q_remove_bvs_empty : forall (Σ:senv) l φ,
  qbvs φ = n_empty -> qbvs (q_remove Σ l φ) = n_empty.
Proof. intros. rewrite qbvs_q_remove. exact H. Qed.

Lemma n_or_empty_both : forall f g, n_or f g = n_empty -> f = n_empty /\ g = n_empty.
Proof.
  intros f g H. split.
  - apply functional_extensionality. intro x.
    assert (Hpt := f_equal (fun h => h x) H). unfold n_or, n_empty in Hpt.
    apply orb_false_iff in Hpt. tauto.
  - apply functional_extensionality. intro x.
    assert (Hpt := f_equal (fun h => h x) H). unfold n_or, n_empty in Hpt.
    apply orb_false_iff in Hpt. tauto.
Qed.


Lemma qstp_nil_fvs_mono : forall Γ (Σ:senv) q d,
  Γ = nil -> qstp Γ Σ q d -> n_sub (qfvs q) (qfvs d).
Proof.
  intros Γ Σ q d Hnil H. induction H; unfold n_sub in *.
  - intros x Hx. destruct H as [Hf [Hfv [Hbv Hl]]]. unfold N_sub in Hfv.
    apply Hfv. exact Hx.
  - rewrite Hnil in H. simpl in H. inversion H.
  - rewrite Hnil in H. simpl in H. inversion H.
  - rewrite Hnil in H. simpl in H. inversion H.
  - rewrite Hnil in H. simpl in H. inversion H.
  - intros x Hx. unfold qor, n_or in *. simpl in *. apply orb_true_iff in Hx.
    destruct Hx as [Hx|Hx].
    + apply orb_true_iff. left. exact Hx.
    + apply orb_true_iff. right. apply IHqstp; [exact Hnil|exact Hx].
  - intros x Hx. apply IHqstp2; [exact Hnil|]. apply IHqstp1; [exact Hnil|exact Hx].
Qed.

Lemma qstp_nil_bvs_mono : forall Γ (Σ:senv) q d,
  Γ = nil -> qstp Γ Σ q d -> n_sub (qbvs q) (qbvs d).
Proof.
  intros Γ Σ q d Hnil H. induction H; unfold n_sub in *.
  - intros x Hx. destruct H as [Hf [Hfv [Hbv Hl]]]. unfold N_sub in Hbv.
    apply Hbv. exact Hx.
  - rewrite Hnil in H. simpl in H. inversion H.
  - rewrite Hnil in H. simpl in H. inversion H.
  - rewrite Hnil in H. simpl in H. inversion H.
  - rewrite Hnil in H. simpl in H. inversion H.
  - intros x Hx. unfold qor, n_or in *. simpl in *. apply orb_true_iff in Hx.
    destruct Hx as [Hx|Hx].
    + apply orb_true_iff. left. exact Hx.
    + apply orb_true_iff. right. apply IHqstp; [exact Hnil|exact Hx].
  - intros x Hx. apply IHqstp2; [exact Hnil|]. apply IHqstp1; [exact Hnil|exact Hx].
Qed.

Lemma qstp_nil_locs_mono : forall Γ (Σ:senv) q d,
  Γ = nil -> qstp Γ Σ q d -> n_sub (qlocs q) (qlocs d).
Proof.
  intros Γ Σ q d Hnil H. induction H; unfold n_sub in *.
  - intros x Hx. destruct H as [Hf [Hfv [Hbv Hl]]]. unfold N_sub in Hl.
    apply Hl. exact Hx.
  - rewrite Hnil in H. simpl in H. inversion H.
  - rewrite Hnil in H. simpl in H. inversion H.
  - rewrite Hnil in H. simpl in H. inversion H.
  - rewrite Hnil in H. simpl in H. inversion H.
  - intros x Hx. unfold qor, n_or in *. simpl in *. apply orb_true_iff in Hx.
    destruct Hx as [Hx|Hx].
    + apply orb_true_iff. left. exact Hx.
    + apply orb_true_iff. right. apply IHqstp; [exact Hnil|exact Hx].
  - intros x Hx. apply IHqstp2; [exact Hnil|]. apply IHqstp1; [exact Hnil|exact Hx].
Qed.

Lemma qstp_nil_locs_preserve : forall Γ (Σ:senv) q d l,
  Γ = nil -> qstp Γ Σ q d ->
  (forall x, qlocs q x = true -> x = l) ->
  qfvs d = n_empty -> qbvs d = n_empty ->
  (forall x, qlocs q x = true -> qlocs d x = true).
Proof.
  intros Γ Σ q d l Hnil H. induction H; intros Hsingle Hfd Hbd.
  - destruct H as [Hf [Hfv [Hbv Hl]]]. unfold N_sub in Hl.
    intros x Hx. apply Hl. exact Hx.
  - rewrite Hnil in H. simpl in H. inversion H.
  - rewrite Hnil in H. simpl in H. inversion H.
  - rewrite Hnil in H. simpl in H. inversion H.
  - rewrite Hnil in H. simpl in H. inversion H.
  - intros x Hx. unfold qor in Hx. simpl in Hx. apply orb_true_iff in Hx.
    destruct Hx as [Hx|Hx].
    + unfold qor. simpl. apply orb_true_iff. left. exact Hx.
    + unfold qor in Hfd, Hbd. simpl in Hfd, Hbd.
      destruct (n_or_empty_both _ _ Hfd) as [_ Hf2].
      destruct (n_or_empty_both _ _ Hbd) as [_ Hb2].
      assert (Hsingle1 : forall y, qlocs d1 y = true -> y = l).
      { intros y Hy. apply Hsingle. unfold qor. simpl. apply orb_true_iff. right. exact Hy. }
      unfold qor. simpl. apply orb_true_iff. right.
      exact (IHqstp Hnil Hsingle1 Hf2 Hb2 x Hx).
  - intros x Hx.
    pose proof (qstp_nil_locs_mono Γ Σ d1 d2 Hnil H) as H12.
    pose proof (qstp_nil_locs_mono Γ Σ d2 d3 Hnil H0) as H23.
    unfold n_sub in H12, H23.
    exact (H23 x (H12 x Hx)).

Qed.

Lemma qstp_nil_locs_preserve_fvs : forall Γ (Σ:senv) q d l,
  Γ = nil -> qstp Γ Σ q d ->
  (forall x, qlocs q x = true -> x = l) ->
  qfvs d = n_empty ->
  (forall x, qlocs q x = true -> qlocs d x = true).
Proof.
  intros Γ Σ q d l Hnil H. induction H; intros Hsingle Hfd.
  - destruct H as [Hf [Hfv [Hbv Hl]]]. unfold N_sub in Hl.
    intros x Hx. apply Hl. exact Hx.
  - rewrite Hnil in H. simpl in H. inversion H.
  - rewrite Hnil in H. simpl in H. inversion H.
  - rewrite Hnil in H. simpl in H. inversion H.
  - rewrite Hnil in H. simpl in H. inversion H.
  - intros x Hx. unfold qor in Hx. simpl in Hx. apply orb_true_iff in Hx.
    destruct Hx as [Hx|Hx].
    + unfold qor. simpl. apply orb_true_iff. left. exact Hx.
    + unfold qor in Hfd. simpl in Hfd.
      destruct (n_or_empty_both _ _ Hfd) as [_ Hf2].
      assert (Hsingle1 : forall y, qlocs d1 y = true -> y = l).
      { intros y Hy. apply Hsingle. unfold qor. simpl. apply orb_true_iff. right. exact Hy. }
      unfold qor. simpl. apply orb_true_iff. right.
      exact (IHqstp Hnil Hsingle1 Hf2 x Hx).
  - intros x Hx.
    pose proof (qstp_nil_locs_mono Γ Σ d1 d2 Hnil H) as H12.
    pose proof (qstp_nil_locs_mono Γ Σ d2 d3 Hnil H0) as H23.
    unfold n_sub in H12, H23.
    exact (H23 x (H12 x Hx)).
Qed.

Lemma qstp_loc_source_nil : forall Γ (Σ:senv) l d,
  Γ = nil -> qstp Γ Σ (&!l) d -> qfvs d = n_empty -> qlocs d l = true.
Proof.
  intros Γ Σ l d Hnil H Hf.
  pose proof (qstp_nil_locs_preserve_fvs Γ Σ (&!l) d l Hnil H) as Hall.
  apply Hall; [|exact Hf|].
  - intros x Hx. unfold n_one in Hx. apply Nat.eqb_eq in Hx. exact Hx.
  - unfold qlocs, n_one. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma vtp_weaken_phi_down_empty : forall Σ ϰ φ φ' v T d,
  vtp Σ ϰ φ v T d -> qfvs d = n_empty -> d ⊑↑ φ' -> vtp Σ ϰ φ' v T d.
Proof.
  intros Σ ϰ φ φ' v T d H. induction H; intros Hf Hsub.
  - eapply vtp_tabs; eauto.
  - eapply vtp_base; eauto.
  - eapply vtp_loc with (T:=T) (U:=U) (q1:=q1) (q2:=q2) (d:=d).
    + exact H.
    + exact H0.
    + exact H1.
    + exact H2.
    + destruct Hsub as [Hs1 [Hs2 [Hs3 Hs4]]]. unfold N_sub in Hs4.
      apply Hs4. eapply qstp_loc_source_nil; [reflexivity|exact H7|exact Hf].
    + exact H4.
    + exact H5.
    + exact H6.
    + exact H7.
    + exact H8.
    + exact H9.
    + exact H10.
    + exact H11.
  - eapply vtp_abs; eauto.
  - eapply vtp_top; eauto.
Qed.

Lemma qand_comm : forall a b, qand a b = qand b a.
Proof.
  intros. apply qual_ext.
  - unfold qand, qfresh. simpl. apply andb_comm.
  - unfold qand, qfvs. simpl. apply n_and_comm.
  - unfold qand, qbvs. simpl. apply n_and_comm.
  - unfold qand, qlocs. simpl. apply n_and_comm.
Qed.

Lemma qand_amp_empty : forall (q:qual) l,
  qlocs q l = false -> qand q (&!l) = q_empty.
Proof.
  intros q l Hl. apply qual_ext.
  - unfold qand, q_empty, qfresh. simpl. destruct (fst (fst (fst q))); reflexivity.
  - unfold qand, q_empty, qfvs. simpl. apply functional_extensionality. intro x.
    unfold n_and, n_empty. apply andb_false_r.
  - unfold qand, q_empty, qbvs. simpl. apply functional_extensionality. intro x.
    unfold n_and, n_empty. apply andb_false_r.
  - unfold qand, q_empty, qlocs. simpl. apply functional_extensionality. intro x.
    unfold n_and, n_one, n_empty. unfold qlocs in Hl. destruct (Nat.eqb x l) eqn:E.
    + apply Nat.eqb_eq in E. subst x. rewrite Hl. reflexivity.
    + apply andb_false_r.
Qed.

Lemma subq_fvs_empty : forall a b, a ⊑↑ b -> qfvs b = n_empty -> qfvs a = n_empty.
Proof.
  intros a b [Hf [H1 [H2 H3]]] Hb. unfold N_sub in H1.
  apply functional_extensionality. intro x.
  destruct (qfvs a x) eqn:E; [|reflexivity].
  exfalso. pose proof (H1 x E) as Hx.
  pose proof (f_equal (fun g => g x) Hb) as Hxb.
  unfold Q_lift in Hx; unfold N_lift in Hx; simpl in Hx;
  change (qfvs b x = true) in Hx;
  unfold n_empty in Hxb.
  rewrite Hxb in Hx. discriminate Hx.
Qed.

Lemma subq_locs_false : forall a b l, a ⊑↑ b -> qlocs b l = false -> qlocs a l = false.
Proof.
  intros a b l [Hf [H1 [H2 H3]]] Hb. unfold N_sub in H3.
  destruct (qlocs a l) eqn:E; [|reflexivity].
  exfalso. pose proof (H3 l E) as Hx.
  unfold Q_lift in Hx; unfold N_lift in Hx; simpl in Hx;
  change (qlocs b l = true) in Hx.
  rewrite Hb in Hx. discriminate Hx.
Qed.

Lemma closed_Qual_amp : forall b f L l,
  l < L -> closed_Qual b f L (Q_lift (&!l)).
Proof.
  intros. unfold closed_Qual. split; [|split].
  - unfold closed_Nats. intros x Hx. unfold N_lift, qfvs, n_empty in Hx. discriminate Hx.
  - unfold closed_Nats. intros x Hx. unfold N_lift, qbvs, n_empty in Hx. discriminate Hx.
  - unfold closed_Nats. intros x Hx. unfold N_lift, qlocs, n_one in Hx.
    apply Nat.eqb_eq in Hx. subst x. exact H.
Qed.

Lemma q_remove'_locs_lt : forall (Σ:senv) k φ n x,
  qlocs (q_remove' Σ k φ n) x = true -> x < n.
Proof.
  intros Σ k φ n. induction n as [|n IH]; intros x H.
  - cbn [q_remove'] in H. discriminate H.
  - cbn [q_remove'] in H.
    change (qlocs (if qlocs φ n && negb (n_one n k) then q_remove' Σ k φ n ⊔ &!n else q_remove' Σ k φ n) x = true) in H.
    destruct (qlocs φ n && negb (n_one n k)) eqn:E.
    + change (n_or (qlocs (q_remove' Σ k φ n)) (n_one n) x = true) in H.
      apply orb_true_iff in H. destruct H as [H|H].
      * apply IH in H. lia.
      * unfold n_one in H. apply Nat.eqb_eq in H. subst x. lia.
    + apply IH in H. lia.
Qed.

Lemma q_remove'_locs_l_false : forall (Σ:senv) l φ n,
  l < n -> qlocs (q_remove' Σ l φ n) l = false.
Proof.
  intros Σ l φ n. induction n as [|n IH]; intros Hlt.
  - lia.
  - cbn [q_remove'].
    change (qlocs (if qlocs φ n && negb (n_one n l) then q_remove' Σ l φ n ⊔ &!n else q_remove' Σ l φ n) l = false).
    destruct (Nat.eqb l n) eqn:En.
    + apply Nat.eqb_eq in En. subst l.
      destruct (qlocs φ n && negb (n_one n n)) eqn:E.
      * apply andb_true_iff in E. destruct E as [_ Hneg].
        unfold negb, n_one in Hneg. rewrite Nat.eqb_refl in Hneg. discriminate Hneg.
      * destruct (qlocs (q_remove' Σ n φ n) n) eqn:Hq; [|reflexivity].
        pose proof (q_remove'_locs_lt Σ n φ n n Hq). lia.
    + assert (Hltn : l < n) by (apply Nat.eqb_neq in En; lia).
      destruct (qlocs φ n && negb (n_one n l)) eqn:E; [|exact (IH Hltn)].
      change (n_or (qlocs (q_remove' Σ l φ n)) (n_one n) l = false).
      apply orb_false_iff. split.
      * apply IH. exact Hltn.
      * apply andb_true_iff in E. destruct E as [_ Hneg].
        unfold negb in Hneg. destruct (n_one n l); [discriminate Hneg|reflexivity].
Qed.

Lemma q_remove_qlocs_l_false : forall (Σ:senv) l φ,
  l < ‖Σ‖ -> qlocs (q_remove Σ l φ) l = false.
Proof.
  intros. unfold q_remove, qor. simpl.
  change (orb (qlocs (q_remove' Σ l φ (‖Σ‖)) l) false = false).
  rewrite q_remove'_locs_l_false; [reflexivity|exact H].
Qed.

Lemma kill_sep_amp_add : forall ϰ (d:qual) l,
  kill_sep ϰ d -> qlocs d l = false -> kill_sep (qor ϰ (&!l)) d.
Proof.
  intros ϰ d l Hk Hl. unfold kill_sep in *.
  rewrite qand_comm. rewrite qand_qor_distrib_l.
  assert (E1 : qand ϰ d = qand d ϰ) by apply qand_comm. rewrite E1.
  assert (E2 : qand (&!l) d = qand d (&!l)) by apply qand_comm. rewrite E2.
  rewrite qand_amp_empty; [|exact Hl].
  rewrite qor_empty_r. exact Hk.
Qed.

Lemma vtp_weaken_kappa_amp : forall Σ ϰ φ v T d l,
  vtp Σ ϰ φ v T d -> qlocs d l = false -> vtp Σ (qor ϰ (&!l)) φ v T d.
Proof.
  intros Σ ϰ φ v T d l H. induction H; intros Hl.
  - eapply vtp_tabs; eauto using kill_sep_amp_add.
  - eapply vtp_base; eauto using kill_sep_amp_add.
  - eapply vtp_loc with (T:=T) (U:=U) (q1:=q1) (q2:=q2) (d:=d).
    + exact H. + exact H0. + exact H1. + exact H2. + exact H3. + exact H4.
    + exact H5. + exact H6. + exact H7. + exact H8. + exact H9. + exact H10.
    + apply kill_sep_amp_add; [exact H11|exact Hl].
  - eapply vtp_abs; eauto using kill_sep_amp_add.
  - eapply vtp_top; eauto.
Qed.

Lemma mem_qor_amp_inv : forall l' φ l,
  l' ∈ₗ (qor φ (&!l)) -> l' = l \/ l' ∈ₗ φ.
Proof.
  intros l' φ l H. unfold qmem in H. unfold qor in H. simpl in H. unfold N_lift in H.
  unfold n_or in H. apply orb_true_iff in H. destruct H as [H|H].
  - right. unfold qmem. unfold N_lift. exact H.
  - left. unfold n_one in H. apply Nat.eqb_eq in H. exact H.
Qed.

Lemma mem_amp_self : forall l, l ∈ₗ (&!l).
Proof.
  intros. unfold qmem. unfold N_lift. unfold n_one. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma CtxOK_twithc : forall Γ φ (Σ:senv) ϰ σ l,
  CtxOK Γ φ Σ ϰ σ -> l < ‖Σ‖ ->
  CtxOK Γ (q_remove Σ l φ) Σ (qor ϰ (&!l)) (update σ l None).
Proof.
  intros Γ φ Σ ϰ σ l Hctx Hlt.
  destruct Hctx as [Hqdom [Hlen [Hphi [Hcl [Hkill Hcell]]]]].
  assert (Hfvsφ : qfvs φ = n_empty) by (eapply subq_qdom_fvs_empty; exact Hphi).
  assert (Hql : qlocs (q_remove Σ l φ) l = false) by (apply q_remove_qlocs_l_false; exact Hlt).
  assert (Hqsub : q_remove Σ l φ ⊑↑ φ) by apply q_remove_subq_l.
  split.
  - eapply Subq_trans; [apply qdom'_update_None_subq|exact Hqdom].
  - split.
    + rewrite length_update. exact Hlen.
    + split.
      * eapply Subq_trans; [exact Hqsub|exact Hphi].
      * split.
        -- apply closed_Qual_qor; [exact Hcl|apply closed_Qual_amp; exact Hlt].
        -- split.
           ++ unfold kill_sep.
              rewrite qand_comm. rewrite qand_qor_distrib_l.
              assert (E1 : qand ϰ (q_remove Σ l φ) = qand (q_remove Σ l φ) ϰ) by apply qand_comm.
              rewrite E1.
              assert (E2 : qand (&!l) (q_remove Σ l φ) = qand (q_remove Σ l φ) (&!l)) by apply qand_comm.
              rewrite E2.
              rewrite qand_amp_empty; [|exact Hql].
              rewrite qor_empty_r.
              eapply Subq_trans; [|exact Hkill].
              apply qand_subq_mono_l. exact Hqsub.
           ++ intros l' o' cty T q. split.
              ** intros Hmem.
                 destruct (Nat.eqb l' l) eqn:E.
                 { apply Nat.eqb_eq in E. subst l'.
                   assert (Hlσ : l < length σ) by lia.
                   exact (indexr_update_lt σ l None Hlσ). }
                 { apply Nat.eqb_neq in E.
                   assert (Hup : indexr l' (update σ l None) = indexr l' σ)
                     by (exact (indexr_update_other σ l None l' E)).
                   rewrite Hup.
                   destruct (mem_qor_amp_inv l' ϰ l Hmem) as [Heq|Hold].
                   - exfalso. exact (E Heq).
                   - exact (proj1 (Hcell l' o' cty T q) Hold). }
              ** intros Hnotmem Hphi' Hlook.
                 destruct (Nat.eqb l' l) eqn:E.
                 { apply Nat.eqb_eq in E. subst l'.
                   exfalso. apply Hnotmem. apply mem_qor_new_loc. }
                 { apply Nat.eqb_neq in E.
                   assert (Hnotmem_old : ~ l' ∈ₗ ϰ).
                   { intro Hin. apply Hnotmem. unfold qmem in *. unfold N_lift in *.
                     unfold qor. simpl. unfold n_or. apply orb_true_iff. left. exact Hin. }
                   assert (Hphi_old : l' ∈ₗ φ).
                   { unfold qmem in *. unfold N_lift in *. eapply q_remove_locs_sub; eauto. }
                   destruct (Hcell l' o' cty T q) as [_ Hinner].
                   destruct (Hinner Hnotmem_old Hphi_old Hlook) as [cell Hspec2].
                   destruct Hspec2 as [HAB Hspec].
                   destruct HAB as [Hctm Hlencty].
                   exists cell. split.
                   { split.
                     { assert (Hup : indexr l' (update σ l None) = indexr l' σ)
                         by (exact (indexr_update_other σ l None l' E)).
                       rewrite Hup. exact Hctm. }
                     { exact Hlencty. } }
                   { intros Ho.
                     destruct (Hspec Ho) as [v0 [Hv0 [Hval0 Hvtp0]]].
                     exists v0. split; [exact Hv0|]. split; [exact Hval0|].
                     intros Hq.
                     assert (Hqold : q ⊑↑ φ) by (eapply Subq_trans; [exact Hq|exact Hqsub]).
                     pose proof (Hvtp0 Hqold) as Hvtp_old.
                     assert (Hfq : qfvs q = n_empty)
                       by (eapply subq_fvs_empty; [exact Hq|exact (q_remove_fvs_empty Σ l φ Hfvsφ)]).
                     assert (Hlq : qlocs q l = false)
                       by (eapply subq_locs_false; [exact Hq|exact Hql]).
                     assert (Hvφ' : vtp Σ ϰ (q_remove Σ l φ) v0 T q)
                       by (eapply vtp_weaken_phi_down_empty; [exact Hvtp_old|exact Hfq|exact Hq]).
                     eapply vtp_weaken_kappa_amp; [exact Hvφ'|exact Hlq]. } }
Qed.

Lemma closed_Qual_add_amp : forall b f L (ϰ:qual) l,
  closed_Qual b f L (Q_lift ϰ) -> l < L ->
  closed_Qual b f L (Q_lift (qor ϰ (&!l))).
Proof.
  intros. apply closed_Qual_qor; [exact H|apply closed_Qual_amp; exact H0].
Qed.

Lemma subq_qor_amp_elim : forall (a φ:qual) l,
  a ⊑↑ (qor φ (&!l)) -> qlocs a l = false -> a ⊑↑ φ.
Proof.
  intros a φ l [Hf [H1 [H2 H3]]] Hl. unfold N_sub in H1, H2, H3. unfold Subq. split.
  - change (Is_true (qfresh a) -> Is_true (qfresh φ)). intros Ha.
    apply Hf in Ha. unfold qor in Ha. simpl in Ha.
    destruct (qfresh φ) eqn:E; [reflexivity|].
    exfalso. unfold Is_true in Ha. rewrite orb_false_r in Ha. exact Ha.
  - split.
    + change (forall x, N_lift (qfvs a) x -> N_lift (qfvs φ) x). intros x Hx.
      specialize (H1 x Hx). unfold Q_lift in H1; unfold N_lift in H1; simpl in H1.
      change (qfvs (qor φ (&!l)) x = true) in H1.
      unfold qfvs, qor, n_or in H1; simpl in H1.
      change (n_or (qfvs φ) n_empty x = true) in H1. rewrite n_or_empty_r in H1.
      unfold N_lift. exact H1.
    + split.
      * change (forall x, N_lift (qbvs a) x -> N_lift (qbvs φ) x). intros x Hx.
        specialize (H2 x Hx). unfold Q_lift in H2; unfold N_lift in H2; simpl in H2.
        change (qbvs (qor φ (&!l)) x = true) in H2.
        unfold qbvs, qor, n_or in H2; simpl in H2.
        change (n_or (qbvs φ) n_empty x = true) in H2. rewrite n_or_empty_r in H2.
        unfold N_lift. exact H2.
      * change (forall x, N_lift (qlocs a) x -> N_lift (qlocs φ) x). intros x Hx.
        specialize (H3 x Hx). unfold Q_lift in H3; unfold N_lift in H3; simpl in H3.
        change (qlocs (qor φ (&!l)) x = true) in H3.
        unfold qlocs, qor in H3; simpl in H3.
        change (n_or (qlocs φ) (n_one l) x = true) in H3.
        unfold n_or in H3. apply orb_true_iff in H3. destruct H3 as [H3|H3].
        -- unfold N_lift. exact H3.
        -- exfalso. unfold n_one in H3. apply Nat.eqb_eq in H3. subst x.
           unfold N_lift in Hx. unfold qlocs in Hx. unfold qlocs in Hl. rewrite Hl in Hx. discriminate Hx.
Qed.

Lemma stp_from_TTop : forall Γ Σ d1 T d2,
  stp Γ Σ TTop d1 T d2 -> T = TTop.
Proof.
  intros Γ Σ d1 T d2 H. remember TTop as S eqn:ES in H.
  induction H; try discriminate; subst.
  - reflexivity.
  - apply IHstp2. apply IHstp1. reflexivity.
Qed.

Lemma stp_from_TUnit : forall Γ Σ d1 T d2,
  stp Γ Σ TUnit d1 T d2 -> T = TUnit \/ T = TTop.
Proof.
  intros Γ Σ d1 T d2 H. remember TUnit as S eqn:ES in H.
  induction H; try discriminate; subst.
  - right. reflexivity.
  - left. reflexivity.
  - destruct (IHstp1 eq_refl) as [E|E]; subst T2.
    + apply IHstp2; reflexivity.
    + right. exact (stp_from_TTop Γ Σ d2 T3 d3 H0).
Qed.

Definition head_tag (T:ty) : nat :=
  match T with TTop => 0 | TVar _ => 1 | TAll _ _ _ _ => 2 | TUnit => 3 | TFun _ _ _ _ => 4 | TRef _ _ => 5 end.

Lemma head_tag_nonvar : forall T, (forall v, T <> TVar v) -> head_tag T <> 1.
Proof.
  intros T H. destruct T; simpl; try lia.
  exfalso. apply (H v). reflexivity.
Qed.

Lemma stp_shape_nonvar : forall Γ Σ T1 d1 T2 d2,
  stp Γ Σ T1 d1 T2 d2 -> (forall v, T1 <> TVar v) ->
  T2 = TTop \/ head_tag T2 = head_tag T1.
Proof.
  intros Γ Σ T1 d1 T2 d2 H. induction H; intros Hnv.
  - left. reflexivity.
  - exfalso. apply (Hnv (varF x)). reflexivity.
  - exfalso. apply (Hnv (varF x)). reflexivity.
  - right. reflexivity.
  - right. reflexivity.
  - right. reflexivity.
  - right. reflexivity.
  - destruct (IHstp1 Hnv) as [E|E].
    + subst T2. left. exact (stp_from_TTop Γ Σ d2 T3 d3 H0).
    + assert (Hnv2 : forall v, T2 <> TVar v).
      { intros v E2. subst T2. unfold head_tag in E. simpl in E.
        pose proof (head_tag_nonvar T1 Hnv) as Hne. exact (Hne (eq_sym E)). }
      destruct (IHstp2 Hnv2) as [E3|E3].
      * left. exact E3.
      * right. rewrite E3. exact E.
Qed.

Lemma stp_from_TRef_shape : forall Γ Σ q T d1 T2 d2,
  stp Γ Σ (TRef q T) d1 T2 d2 -> T2 = TTop \/ exists q' U, T2 = TRef q' U.
Proof.
  intros. destruct (stp_shape_nonvar Γ Σ (TRef q T) d1 T2 d2 H
    (fun v Hv => match Hv with end)) as [E|E].
  - left. exact E.
  - right. destruct T2; simpl in E; try discriminate.
    eexists; eexists; reflexivity.
Qed.

Lemma stp_from_TFun_shape : forall Γ Σ a b c e d1 T2 d2,
  stp Γ Σ (TFun a b c e) d1 T2 d2 ->
  T2 = TTop \/ exists a' b' c' e', T2 = TFun a' b' c' e'.
Proof.
  intros. destruct (stp_shape_nonvar Γ Σ (TFun a b c e) d1 T2 d2 H
    (fun v Hv => match Hv with end)) as [E|E].
  - left. exact E.
  - right. destruct T2; simpl in E; try discriminate.
    eexists; eexists; eexists; eexists; reflexivity.
Qed.

Lemma stp_from_TAll_shape : forall Γ Σ a b c e d1 T2 d2,
  stp Γ Σ (TAll a b c e) d1 T2 d2 ->
  T2 = TTop \/ exists a' b' c' e', T2 = TAll a' b' c' e'.
Proof.
  intros. destruct (stp_shape_nonvar Γ Σ (TAll a b c e) d1 T2 d2 H
    (fun v Hv => match Hv with end)) as [E|E].
  - left. exact E.
  - right. destruct T2; simpl in E; try discriminate.
    eexists; eexists; eexists; eexists; reflexivity.
Qed.

Lemma stp_from_TUnit_shape : forall Γ Σ d1 T2 d2,
  stp Γ Σ TUnit d1 T2 d2 -> T2 = TTop \/ T2 = TUnit.
Proof.
  intros. destruct (stp_shape_nonvar Γ Σ TUnit d1 T2 d2 H
    (fun v Hv => match Hv with end)) as [E|E].
  - left. exact E.
  - right. destruct T2; simpl in E; try discriminate; reflexivity.
Qed.

Lemma qstp_refl : forall Γ Σ (d:qual),
  closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift d) -> qstp Γ Σ d d.
Proof.
  intros. apply qs_sq; [apply Subq_refl|exact H].
Qed.

Lemma stp_refl_TTop : forall Γ Σ (d:qual),
  closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift d) -> stp Γ Σ TTop d TTop d.
Proof.
  intros. apply s_top; [apply cl_TTop|apply qstp_refl; exact H].
Qed.

Lemma stp_refl_TUnit : forall Γ Σ (d:qual),
  closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift d) -> stp Γ Σ TUnit d TUnit d.
Proof.
  intros. apply s_base. apply qstp_refl; exact H.
Qed.

Lemma stp_refl_TVar : forall Γ Σ x v (d:qual),
  indexr x Γ = Some v -> closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift d) ->
  stp Γ Σ (TVar (varF x)) d (TVar (varF x)) d.
Proof.
  intros. eapply s_tvar_refl; [exact H|apply qstp_refl; exact H0].
Qed.

Lemma indexr_Some_of_lt : forall {X} (l:list X) k, k < length l -> exists a, indexr k l = Some a.
Proof.
  intros X l. induction l as [|x xs IH]; intros k Hlt; simpl in Hlt.
  - lia.
  - destruct (Nat.eqb k (length xs)) eqn:E.
    + exists x. rewrite indexr_cons. rewrite E. reflexivity.
    + assert (Hlt' : k < length xs) by (apply Nat.eqb_neq in E; lia).
      destruct (IH k Hlt') as [a Ha]. exists a. rewrite indexr_cons. rewrite E. simpl. exact Ha.
Qed.

Lemma ty_size_open_rec_ty : forall T k U d,
  ty_size U = 0 -> ty_size (open_rec_ty k U d T) = ty_size T.
Proof.
  intros T. induction T; intros k U d HU; simpl.
  - reflexivity.
  - destruct v as [ii|ii].
    + reflexivity.
    + simpl. destruct (Nat.eqb k ii) eqn:E; [exact HU|reflexivity].
  - rewrite (IHT1 k U d HU), (IHT2 (S (S k)) U d HU). reflexivity.
  - reflexivity.
  - rewrite (IHT1 k U d HU), (IHT2 (S (S k)) U d HU). reflexivity.
  - rewrite (IHT k U d HU). reflexivity.
Qed.

Lemma ty_size_open_ty'_eq : forall {A} (env:list A) T,
  ty_size (open_ty' env T) = ty_size T.
Proof.
  intros. unfold open_ty'. unfold open_ty.
  rewrite ty_size_open_rec_ty; [|reflexivity].
  rewrite ty_size_open_rec_ty; [reflexivity|reflexivity].
Qed.

Lemma stp_refl_TRef : forall Γ Σ q T (d:qual),
  closed_ty 0 (‖Γ‖) (‖Σ‖) (TRef q T) ->
  closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift d) ->
  stp Γ Σ T ∅ T ∅ ->
  stp Γ Σ (TRef q T) d (TRef q T) d.
Proof.
  intros Γ Σ q T d Hct Hcq Hstp.
  inversion Hct; subst.
  apply s_ref.
  - apply qstp_refl; exact Hcq.
  - exact Hstp.
  - exact Hstp.
  - apply qstp_refl. assumption.
  - apply qstp_refl. assumption.
Qed.

Lemma open_ty'_TUnit : forall {A} (env:list A), open_ty' env TUnit = TUnit.
Proof. intros. reflexivity. Qed.
Lemma open_ty'_TTop : forall {A} (env:list A), open_ty' env TTop = TTop.
Proof. intros. reflexivity. Qed.
Lemma open_ty'_varF : forall {A} (env:list A) x, open_ty' env (TVar (varF x)) = TVar (varF x).
Proof. intros. reflexivity. Qed.
Lemma open_ty'_TAll : forall {A} (env:list A) d1 d2 T1 T2,
  open_ty' env (TAll d1 d2 T1 T2) =
  TAll (openq' env d1) (open_qual 3 ($!(S (‖env‖))) (open_qual 2 ($!‖env‖) d2))
       (open_ty' env T1)
       (open_rec_ty 3 (TVar (varF (S (‖env‖)))) ($!(S (‖env‖)))
          (open_rec_ty 2 (TVar (varF (‖env‖))) ($!‖env‖) T2)).
Proof. intros. reflexivity. Qed.
Lemma open_ty'_TFun : forall {A} (env:list A) d1 d2 T1 T2,
  open_ty' env (TFun d1 d2 T1 T2) =
  TFun (openq' env d1) (open_qual 3 ($!(S (‖env‖))) (open_qual 2 ($!‖env‖) d2))
       (open_ty' env T1)
       (open_rec_ty 3 (TVar (varF (S (‖env‖)))) ($!(S (‖env‖)))
          (open_rec_ty 2 (TVar (varF (‖env‖))) ($!‖env‖) T2)).
Proof. intros. reflexivity. Qed.
Lemma open_ty'_TRef : forall {A} (env:list A) d T,
  open_ty' env (TRef d T) = TRef (openq' env d) (open_ty' env T).
Proof. intros. reflexivity. Qed.

Definition openq_pair (k f : nat) (q:qual) : qual :=
  open_qual (S k) ($!(S f)) (open_qual k ($!f) q).

Definition open_pair_ty (k f : nat) (T:ty) : ty :=
  open_rec_ty (S k) (TVar (varF (S f))) ($!(S f))
    (open_rec_ty k (TVar (varF f)) ($!f) T).

Lemma open_pair_ty_TUnit : forall k f, open_pair_ty k f TUnit = TUnit.
Proof. intros. reflexivity. Qed.
Lemma open_pair_ty_TTop : forall k f, open_pair_ty k f TTop = TTop.
Proof. intros. reflexivity. Qed.
Lemma open_pair_ty_varF : forall k f x, open_pair_ty k f (TVar (varF x)) = TVar (varF x).
Proof. intros. reflexivity. Qed.
Lemma open_pair_ty_TRef : forall k f d T,
  open_pair_ty k f (TRef d T) = TRef (openq_pair k f d) (open_pair_ty k f T).
Proof. intros. reflexivity. Qed.

Lemma qfvs_open_qual_sub : forall k d' (q:qual) x,
  qfvs q x = true -> qfvs (open_qual k d' q) x = true.
Proof.
  intros. unfold open_qual.
  destruct (qbvs q k) eqn:E.
  - unfold qor, n_or; simpl. apply orb_true_iff. left. exact H.
  - exact H.
Qed.

Lemma qlocs_open_qual_sub : forall k d' (q:qual) x,
  qlocs q x = true -> qlocs (open_qual k d' q) x = true.
Proof.
  intros. unfold open_qual.
  destruct (qbvs q k) eqn:E.
  - unfold qor, n_or; simpl. apply orb_true_iff. left. exact H.
  - exact H.
Qed.

Lemma qfresh_open_qual_sub : forall k d' (q:qual),
  qfresh q = true -> qfresh (open_qual k d' q) = true.
Proof.
  intros. unfold open_qual.
  destruct (qbvs q k) eqn:E.
  - unfold qor; simpl. apply orb_true_iff. left. exact H.
  - exact H.
Qed.

Lemma qbvs_open_qual_sub : forall k d' (q:qual) x,
  qbvs q x = true -> x <> k -> qbvs (open_qual k d' q) x = true.
Proof.
  intros. unfold open_qual.
  destruct (qbvs q k) eqn:E.
  - unfold qor, n_or; simpl. apply orb_true_iff. left.
    unfold n_diff. apply andb_true_iff. split; [exact H|].
    unfold negb, n_one. destruct (Nat.eqb x k) eqn:Ex; [|reflexivity].
    apply Nat.eqb_eq in Ex. exfalso. apply H0. exact Ex.
  - exact H.
Qed.

Lemma qfvs_open_qual_elim_f : forall k f (q:qual) x,
  qfvs (open_qual k ($!f) q) x = true -> qfvs q x = true \/ x = f.
Proof.
  intros. unfold open_qual in H. destruct (qbvs q k) eqn:E; simpl in H.
  - unfold qor, n_or in H. simpl in H. apply orb_true_iff in H. destruct H as [H|H].
    + left. exact H.
    + right. unfold n_one in H. apply Nat.eqb_eq in H. exact H.
  - left. exact H.
Qed.

Lemma qbvs_open_qual_elim_f : forall k f (q:qual) x,
  qbvs (open_qual k ($!f) q) x = true -> qbvs q x = true /\ x <> k.
Proof.
  intros. unfold open_qual in H. destruct (qbvs q k) eqn:E; simpl in H.
  - unfold qor, n_or in H. simpl in H. apply orb_true_iff in H. destruct H as [H|H].
    + unfold n_diff in H. apply andb_true_iff in H. destruct H as [H Hk].
      split; [exact H|]. unfold negb, n_one in Hk. destruct (Nat.eqb x k) eqn:Ex.
      * discriminate Hk.
      * apply Nat.eqb_neq in Ex. exact Ex.
    + unfold qbvs, n_empty in H. discriminate H.
  - split; [exact H|].
    intro Hx. subst x. rewrite E in H. discriminate H.
Qed.

Lemma qlocs_open_qual_elim_f : forall k f (q:qual) x,
  qlocs (open_qual k ($!f) q) x = true -> qlocs q x = true.
Proof.
  intros. unfold open_qual in H. destruct (qbvs q k) eqn:E; simpl in H.
  - unfold qor, n_or in H. simpl in H. apply orb_true_iff in H. destruct H as [H|H].
    + exact H.
    + unfold qlocs, n_empty in H. discriminate H.
  - exact H.
Qed.

Lemma qfvs_openq_pair_elim : forall k f (q:qual) x,
  qfvs (openq_pair k f q) x = true -> qfvs q x = true \/ x = f \/ x = S f.
Proof.
  intros. unfold openq_pair in H.
  destruct (qfvs_open_qual_elim_f (S k) (S f) (open_qual k ($!f) q) x H) as [H1|H1].
  - destruct (qfvs_open_qual_elim_f k f q x H1) as [H2|H2]; [left; exact H2|right; left; exact H2].
  - right; right; exact H1.
Qed.

Lemma qbvs_openq_pair_elim : forall k f (q:qual) x,
  qbvs (openq_pair k f q) x = true -> qbvs q x = true /\ x <> k /\ x <> S k.
Proof.
  intros. unfold openq_pair in H.
  destruct (qbvs_open_qual_elim_f (S k) (S f) (open_qual k ($!f) q) x H) as [H1 HS].
  destruct (qbvs_open_qual_elim_f k f q x H1) as [H2 Hk].
  split; [exact H2|]. split; [exact Hk|exact HS].
Qed.

Lemma qlocs_openq_pair_elim : forall k f (q:qual) x,
  qlocs (openq_pair k f q) x = true -> qlocs q x = true.
Proof.
  intros. unfold openq_pair in H.
  apply (qlocs_open_qual_elim_f k f q x).
  apply (qlocs_open_qual_elim_f (S k) (S f) (open_qual k ($!f) q) x H).
Qed.

Lemma closed_Qual_openq_pair : forall b f L (q:qual) k,
  closed_Qual b f L (Q_lift q) -> b = k + 2 ->
  closed_Qual k (f + 2) L (Q_lift (openq_pair k f q)).
Proof.
  intros b f L q k [Hfv [Hbv Hl]] Hb.
  unfold closed_Qual. split; [|split].
  - unfold closed_Nats in *. intros x Hx.
    apply qfvs_openq_pair_elim in Hx.
    destruct Hx as [Hx|[Hx|Hx]]; [apply Hfv in Hx|subst x|subst x]; lia.
  - unfold closed_Nats in *. intros x Hx.
    apply qbvs_openq_pair_elim in Hx.
    destruct Hx as [Hx [Hk Hsk]]. apply Hbv in Hx. rewrite Hb in Hx. lia.
  - unfold closed_Nats in *. intros x Hx.
    apply qlocs_openq_pair_elim in Hx. apply Hl in Hx. exact Hx.
Qed.

Lemma open_pair_ty_TAll : forall k f d1 d2 T1 T2,
  open_pair_ty k f (TAll d1 d2 T1 T2) =
  TAll (openq_pair k f d1) (openq_pair (S (S k)) f d2)
       (open_pair_ty k f T1) (open_pair_ty (S (S k)) f T2).
Proof. intros. unfold open_pair_ty. reflexivity. Qed.

Lemma open_pair_ty_TFun : forall k f d1 d2 T1 T2,
  open_pair_ty k f (TFun d1 d2 T1 T2) =
  TFun (openq_pair k f d1) (openq_pair (S (S k)) f d2)
       (open_pair_ty k f T1) (open_pair_ty (S (S k)) f T2).
Proof. intros. unfold open_pair_ty. reflexivity. Qed.

Lemma closed_ty_open_pair : forall T b f L k,
  closed_ty b f L T -> b = k + 2 ->
  closed_ty k (f + 2) L (open_pair_ty k f T).
Proof.
  intros T. induction T; intros b f L k Hc Hb; inversion Hc; subst.
  - apply cl_TTop.
  - rewrite open_pair_ty_varF. apply cl_ttvarf. lia.
  - cbn [open_pair_ty open_rec_ty]. destruct (Nat.eqb k x) eqn:Ek.
    + apply Nat.eqb_eq in Ek. subst x. cbn [open_rec_ty]. apply cl_ttvarf. lia.
    + cbn [open_rec_ty]. destruct (Nat.eqb (S k) x) eqn:Es.
      * apply Nat.eqb_eq in Es. subst x. apply cl_ttvarf. lia.
      * apply cl_ttvarb. apply Nat.eqb_neq in Ek. apply Nat.eqb_neq in Es. lia.
  - rewrite open_pair_ty_TAll. eapply cl_TAll.
    + eapply closed_Qual_openq_pair; [exact H6|lia].
    + eapply closed_Qual_openq_pair; [exact H7|lia].
    + eapply IHT1; [exact H8|lia].
    + eapply IHT2; [exact H9|lia].
  - apply cl_TUnit.
  - rewrite open_pair_ty_TFun. eapply cl_TFun.
    + eapply closed_Qual_openq_pair; [exact H6|lia].
    + eapply closed_Qual_openq_pair; [exact H7|lia].
    + eapply IHT1; [exact H8|lia].
    + eapply IHT2; [exact H9|lia].
  - rewrite open_pair_ty_TRef. eapply cl_TRef.
    + eapply IHT; [exact H4|lia].
    + eapply closed_Qual_openq_pair; [exact H5|lia].
Qed.

Lemma closed_Qual_empty : forall b f L, closed_Qual b f L (Q_lift q_empty).
Proof.
  intros b f L. unfold closed_Qual. split; [|split].
  - unfold closed_Nats. intros x Hx. unfold N_lift, qfvs, q_empty, n_empty in Hx. discriminate Hx.
  - unfold closed_Nats. intros x Hx. unfold N_lift, qbvs, q_empty, n_empty in Hx. discriminate Hx.
  - unfold closed_Nats. intros x Hx. unfold N_lift, qlocs, q_empty, n_empty in Hx. discriminate Hx.
Qed.

Lemma open_pair_ty_zero_env : forall {A} (env:list A) T,
  open_pair_ty 0 (‖env‖) T = open_ty' env T.
Proof. intros. reflexivity. Qed.

Lemma openq_pair_zero_env : forall {A} (env:list A) (q:qual),
  openq_pair 0 (‖env‖) q = openq' env q.
Proof. intros. reflexivity. Qed.


Lemma closed_ty_open_pair_SS : forall T b f L k,
  closed_ty b f L T -> b = k + 2 ->
  closed_ty k (S (S f)) L (open_pair_ty k f T).
Proof.
  intros. pose proof (closed_ty_open_pair T b f L k H H0) as H'.
  rewrite Nat.add_comm in H'. simpl in H'. exact H'.
Qed.

Lemma closed_Qual_openq_pair_SS : forall b f L (q:qual) k,
  closed_Qual b f L (Q_lift q) -> b = k + 2 ->
  closed_Qual k (S (S f)) L (Q_lift (openq_pair k f q)).
Proof.
  intros. pose proof (closed_Qual_openq_pair b f L q k H H0) as H'.
  rewrite Nat.add_comm in H'. simpl in H'. exact H'.
Qed.

Lemma stp_refl_closed : forall n Γ Σ (T:ty) d,
  ty_size T <= n -> closed_ty 0 (‖Γ‖) (‖Σ‖) T ->
  closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift d) -> stp Γ Σ T d T d.
Proof.
  induction n as [|n IH]; intros Γ Σ T d Hsize Hct Hcq.
  - destruct T.
    + apply stp_refl_TTop. exact Hcq.
    + destruct v as [x|x].
      * simpl in Hsize. inversion Hct; subst.
        match goal with Hx : x < ‖Γ‖ |- _ => destruct (indexr_Some_of_lt Γ x Hx) as [v Hv]; eapply stp_refl_TVar; eauto end.
      * inversion Hct; subst. exfalso; lia.
    + simpl in Hsize. exfalso; lia.
    + apply stp_refl_TUnit. exact Hcq.
    + simpl in Hsize. exfalso; lia.
    + simpl in Hsize. exfalso; lia.
  - destruct T.
    + apply stp_refl_TTop. exact Hcq.
    + destruct v as [x|x].
      * simpl in Hsize. inversion Hct; subst.
        match goal with Hx : x < ‖Γ‖ |- _ => destruct (indexr_Some_of_lt Γ x Hx) as [v Hv]; eapply stp_refl_TVar; eauto end.
      * inversion Hct; subst. exfalso; lia.
    + inversion Hct; subst.
      assert (Hs1 : ty_size T1 <= n) by (simpl in Hsize; lia).
      assert (Hs2 : ty_size T2 <= n) by (simpl in Hsize; lia).
      assert (Hsz2 : ty_size (open_ty' Γ T2) <= n) by (rewrite ty_size_open_ty'_eq; exact Hs2).
      assert (Hct1 : closed_ty 0 (‖Γ‖) (‖Σ‖) T1) by eassumption.
      assert (Hcq1 : closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift q)) by eassumption.
      assert (Hct2 : closed_ty (S (S 0)) (‖Γ‖) (‖Σ‖) T2) by eassumption.
      assert (Hcq2 : closed_Qual (S (S 0)) (‖Γ‖) (‖Σ‖) (Q_lift q0)) by eassumption.
      assert (Hct2' : closed_ty 0 (‖(bind_ty, false, T1, q) :: (bind_tm, true, TAll q q0 T1 T2, {♦}) :: Γ‖) (‖Σ‖) (open_ty' Γ T2)).
      { rewrite <- open_pair_ty_zero_env.
        eapply closed_ty_open_pair_SS; [exact Hct2|reflexivity]. }
      assert (Hcq2' : closed_Qual 0 (‖(bind_ty, false, T1, q) :: (bind_tm, true, TAll q q0 T1 T2, {♦}) :: Γ‖) (‖Σ‖) (Q_lift (openq' Γ q0))).
      { rewrite <- openq_pair_zero_env.
        eapply closed_Qual_openq_pair_SS; [exact Hcq2|reflexivity]. }
      assert (Hstp1 : stp Γ Σ T1 q T1 q) by (eapply IH; [exact Hs1|exact Hct1|exact Hcq1]).
      assert (Hstp2 : stp ((bind_ty, false, T1, q) :: (bind_tm, true, TAll q q0 T1 T2, {♦}) :: Γ) Σ (open_ty' Γ T2) (openq' Γ q0) (open_ty' Γ T2) (openq' Γ q0))
        by (eapply IH; [exact Hsz2|exact Hct2'|exact Hcq2']).
      eapply s_all with (d1:=q) (d2:=q0) (d3:=q) (d4:=q0) (d5:=d) (d6:=d) (T3:=T1) (T4:=T2).
      * exact Hct.
      * exact Hct.
      * apply qstp_refl. exact Hcq.
      * exact Hstp1.
      * exact Hstp2.
    + apply stp_refl_TUnit. exact Hcq.
    + inversion Hct; subst.
      assert (Hs1 : ty_size T1 <= n) by (simpl in Hsize; lia).
      assert (Hs2 : ty_size T2 <= n) by (simpl in Hsize; lia).
      assert (Hsz2 : ty_size (open_ty' Γ T2) <= n) by (rewrite ty_size_open_ty'_eq; exact Hs2).
      assert (Hct1 : closed_ty 0 (‖Γ‖) (‖Σ‖) T1) by eassumption.
      assert (Hcq1 : closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift q)) by eassumption.
      assert (Hct2 : closed_ty (S (S 0)) (‖Γ‖) (‖Σ‖) T2) by eassumption.
      assert (Hcq2 : closed_Qual (S (S 0)) (‖Γ‖) (‖Σ‖) (Q_lift q0)) by eassumption.
      assert (Hct2' : closed_ty 0 (‖(bind_tm, false, T1, q) :: (bind_tm, true, TFun q q0 T1 T2, {♦}) :: Γ‖) (‖Σ‖) (open_ty' Γ T2)).
      { rewrite <- open_pair_ty_zero_env.
        eapply closed_ty_open_pair_SS; [exact Hct2|reflexivity]. }
      assert (Hcq2' : closed_Qual 0 (‖(bind_tm, false, T1, q) :: (bind_tm, true, TFun q q0 T1 T2, {♦}) :: Γ‖) (‖Σ‖) (Q_lift (openq' Γ q0))).
      { rewrite <- openq_pair_zero_env.
        eapply closed_Qual_openq_pair_SS; [exact Hcq2|reflexivity]. }
      assert (Hstp1 : stp Γ Σ T1 q T1 q) by (eapply IH; [exact Hs1|exact Hct1|exact Hcq1]).
      assert (Hstp2 : stp ((bind_tm, false, T1, q) :: (bind_tm, true, TFun q q0 T1 T2, {♦}) :: Γ) Σ (open_ty' Γ T2) (openq' Γ q0) (open_ty' Γ T2) (openq' Γ q0))
        by (eapply IH; [exact Hsz2|exact Hct2'|exact Hcq2']).
      eapply s_fun with (d1:=q) (d2:=q0) (d3:=q) (d4:=q0) (d5:=d) (d6:=d) (T3:=T1) (T4:=T2).
      * exact Hct.
      * exact Hct.
      * apply qstp_refl. exact Hcq.
      * exact Hstp1.
      * exact Hstp2.
    + inversion Hct; subst.
      assert (Hs : ty_size T <= n) by (simpl in Hsize; lia).
      assert (HctT : closed_ty 0 (‖Γ‖) (‖Σ‖) T) by eassumption.
      assert (Hstp : stp Γ Σ T ∅ T ∅) by (eapply IH; [exact Hs|exact HctT|apply closed_Qual_empty]).
      eapply stp_refl_TRef; [exact Hct|exact Hcq|exact Hstp].
Qed.

Lemma closed_Qual_diamond : forall b f L, closed_Qual b f L (Q_lift {♦}).
Proof.
  intros b f L. unfold closed_Qual. split; [|split].
  - unfold closed_Nats. intros x Hx. unfold N_lift, qfvs in Hx. simpl in Hx. discriminate Hx.
  - unfold closed_Nats. intros x Hx. unfold N_lift, qbvs in Hx. simpl in Hx. discriminate Hx.
  - unfold closed_Nats. intros x Hx. unfold N_lift, qlocs in Hx. simpl in Hx. discriminate Hx.
Qed.

Lemma closed_Qual_of_subq_or_diamond : forall b L (d φ:qual),
  closed_Qual b 0 L (Q_lift φ) -> d ⊑↑ (qor φ {♦}) ->
  closed_Qual b 0 L (Q_lift d).
Proof.
  intros b L d φ [Hpf [Hpb Hpl]] [Hf [H1 [H2 H3]]].
  unfold closed_Qual. split; [|split].
  - unfold closed_Nats in *. intros x Hx.
    specialize (H1 x Hx). unfold N_lift in H1. unfold qor in H1. simpl in H1.
    unfold n_or in H1. apply orb_true_iff in H1. destruct H1 as [H1|H1].
    + apply Hpf in H1. exact H1.
    + unfold n_empty in H1. discriminate H1.
  - unfold closed_Nats in *. intros x Hx.
    specialize (H2 x Hx). unfold N_lift in H2. unfold qor in H2. simpl in H2.
    unfold n_or in H2. apply orb_true_iff in H2. destruct H2 as [H2|H2].
    + apply Hpb in H2. exact H2.
    + unfold n_empty in H2. discriminate H2.
  - unfold closed_Nats in *. intros x Hx.
    specialize (H3 x Hx). unfold N_lift in H3. unfold qor in H3. simpl in H3.
    unfold n_or in H3. apply orb_true_iff in H3. destruct H3 as [H3|H3].
    + apply Hpl in H3. exact H3.
    + unfold n_empty in H3. discriminate H3.
Qed.

Lemma qstp_nil_subq : forall Γ (Σ:senv) q d,
  Γ = nil -> qstp Γ Σ q d -> q ⊑↑ d.
Proof.
  intros Γ Σ q d Hnil H. induction H.
  - exact H.
  - rewrite Hnil in H. simpl in H. inversion H.
  - rewrite Hnil in H. simpl in H. inversion H.
  - rewrite Hnil in H. simpl in H. inversion H.
  - rewrite Hnil in H. simpl in H. inversion H.
  - apply qor_subq_mono; [apply Subq_refl|apply IHqstp; exact Hnil].
  - eapply Subq_trans; [apply IHqstp1; exact Hnil|apply IHqstp2; exact Hnil].
Qed.

Lemma kill_sep_diamond : forall (ϰ:qual), kill_sep ϰ {♦}.
Proof.
  intros ϰ. unfold kill_sep. unfold Subq. split.
  - change (Is_true (qfresh {♦} && qfresh ϰ) -> Is_true (qfresh {♦})). simpl. intros; exact I.
  - split.
    + change (forall x, N_lift (n_and (qfvs {♦}) (qfvs ϰ)) x -> N_lift (qfvs {♦}) x).
      intros x Hx. unfold N_lift, n_and, qfvs in Hx. simpl in Hx. discriminate Hx.
    + split.
      * change (forall x, N_lift (n_and (qbvs {♦}) (qbvs ϰ)) x -> N_lift (qbvs {♦}) x).
        intros x Hx. unfold N_lift, n_and, qbvs in Hx. simpl in Hx. discriminate Hx.
      * change (forall x, N_lift (n_and (qlocs {♦}) (qlocs ϰ)) x -> N_lift (qlocs {♦}) x).
        intros x Hx. unfold N_lift, n_and, qlocs in Hx. simpl in Hx. discriminate Hx.
Qed.

Lemma kill_sep_subq_or_diamond : forall (ϰ φ d:qual),
  kill_sep ϰ φ -> d ⊑↑ (qor φ {♦}) -> kill_sep ϰ d.
Proof.
  intros ϰ φ d Hk Hsub. unfold kill_sep in *.
  eapply Subq_trans.
  - eapply Subq_trans.
    + apply qand_subq_mono_l. exact Hsub.
    + rewrite qand_qor_distrib_l. apply Subq_refl.
  - apply qor_subq_same; [exact Hk|apply kill_sep_diamond].
Qed.

Lemma vtp_base_retype : forall (Σ:senv) ϰ φ d1 d2,
  vtp Σ ϰ φ tunit TUnit d1 -> d2 ⊑↑ (qor φ {♦}) ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift d2) -> kill_sep ϰ φ ->
  vtp Σ ϰ φ tunit TUnit d2.
Proof.
  intros. eapply vtp_base.
  - exact H1.
  - apply (kill_sep_subq_or_diamond ϰ φ d2); [exact H2|exact H0].
Qed.

Lemma vtp_top_retype : forall (Σ:senv) ϰ φ v T (d:qual),
  vtp Σ ϰ φ v T d -> vtp Σ ϰ φ v TTop d.
Proof. intros. eapply vtp_top; exact H. Qed.

Lemma qstp_nil_closed_both : forall (Σ:senv) q d,
  qstp nil Σ q d -> qstp nil Σ d q ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift q) ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift d).
Proof.
  intros Σ q d Hqs Hrev Hc. pose proof (qstp_nil_subq nil Σ d q eq_refl Hrev) as Hsub.
  destruct Hc as [Hf [Hb Hl]]. destruct Hsub as [Hs1 [Hs2 [Hs3 Hs4]]].
  unfold N_sub in Hs2, Hs3, Hs4. unfold closed_Qual. split; [|split].
  - unfold closed_Nats in *. intros x Hx.
    specialize (Hs2 x Hx). unfold N_lift in Hs2. apply Hf in Hs2. exact Hs2.
  - unfold closed_Nats in *. intros x Hx.
    specialize (Hs3 x Hx). unfold N_lift in Hs3. apply Hb in Hs3. exact Hs3.
  - unfold closed_Nats in *. intros x Hx.
    specialize (Hs4 x Hx). unfold N_lift in Hs4. apply Hl in Hs4. exact Hs4.
Qed.

Lemma qstp_subq_nl : forall Γ (Σ:senv) q d,
  no_lookup Γ -> qstp Γ Σ q d -> q ⊑↑ d.
Proof.
  intros Γ Σ q d Hnl H. induction H.
  - exact H.
  - exfalso. eapply Hnl; eauto.
  - exfalso. eapply Hnl; eauto.
  - exfalso. eapply Hnl; eauto.
  - exfalso. eapply Hnl; eauto.
  - apply qor_subq_mono; [apply Subq_refl|apply IHqstp; exact Hnl].
  - eapply Subq_trans; [apply IHqstp1; exact Hnl|apply IHqstp2; exact Hnl].
Qed.

Lemma qstp_closed_both_nl : forall Γ (Σ:senv) q d,
  no_lookup Γ -> qstp Γ Σ q d -> qstp Γ Σ d q ->
  closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift q) ->
  closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift d).
Proof.
  intros Γ Σ q d Hnl Hqs Hrev Hc.
  pose proof (qstp_subq_nl Γ Σ d q Hnl Hrev) as Hsub.
  destruct Hc as [Hf [Hb Hl]]. destruct Hsub as [Hs1 [Hs2 [Hs3 Hs4]]].
  unfold N_sub in Hs2, Hs3, Hs4. unfold closed_Qual. split; [|split].
  - unfold closed_Nats in *. intros x Hx.
    specialize (Hs2 x Hx). unfold N_lift in Hs2. apply Hf in Hs2. exact Hs2.
  - unfold closed_Nats in *. intros x Hx.
    specialize (Hs3 x Hx). unfold N_lift in Hs3. apply Hb in Hs3. exact Hs3.
  - unfold closed_Nats in *. intros x Hx.
    specialize (Hs4 x Hx). unfold N_lift in Hs4. apply Hl in Hs4. exact Hs4.
Qed.

Lemma stp_closed_target_nl : forall Γ (Σ:senv) T1 d1 T2 d2,
  no_lookup Γ -> closed_ty 0 (‖Γ‖) (‖Σ‖) T1 -> stp Γ Σ T1 d1 T2 d2 ->
  closed_ty 0 (‖Γ‖) (‖Σ‖) T2.
Proof.
  intros Γ Σ T1 d1 T2 d2 Hnl Hc H. revert Hc. induction H; intros Hc.
  - apply cl_TTop.
  - exfalso. eapply Hnl; eauto.
  - exfalso. eapply Hnl; eauto.
  - eassumption.
  - apply cl_TUnit.
  - inversion Hc; subst. eapply cl_TRef.
    + eapply IHstp1; [exact Hnl|exact H9].
    + eapply qstp_closed_both_nl; [exact Hnl|exact H2|exact H3|exact H10].
  - eassumption.
  - eapply IHstp2; [exact Hnl|]. eapply IHstp1; [exact Hnl|exact Hc].
Qed.

Lemma stp_closed_target_nil : forall (Σ:senv) T1 d1 T2 d2,
  closed_ty 0 0 (‖Σ‖) T1 -> stp nil Σ T1 d1 T2 d2 ->
  closed_ty 0 0 (‖Σ‖) T2.
Proof.
  intros. eapply stp_closed_target_nl with (Γ:=nil) (Σ:=Σ) (T1:=T1) (d1:=d1) (T2:=T2) (d2:=d2); [apply no_lookup_nil|exact H|exact H0].
Qed.

Lemma closed_Qual_of_subq_or_diamond_f : forall b f L (d φ:qual),
  closed_Qual b f L (Q_lift φ) -> d ⊑↑ (qor φ {♦}) ->
  closed_Qual b f L (Q_lift d).
Proof.
  intros b f L d φ [Hpf [Hpb Hpl]] [Hf [H1 [H2 H3]]].
  unfold closed_Qual. split; [|split].
  - unfold closed_Nats in *. intros x Hx.
    specialize (H1 x Hx). unfold N_lift in H1. unfold qor in H1. simpl in H1.
    unfold n_or in H1. apply orb_true_iff in H1. destruct H1 as [H1|H1].
    + apply Hpf in H1. exact H1.
    + unfold n_empty in H1. discriminate H1.
  - unfold closed_Nats in *. intros x Hx.
    specialize (H2 x Hx). unfold N_lift in H2. unfold qor in H2. simpl in H2.
    unfold n_or in H2. apply orb_true_iff in H2. destruct H2 as [H2|H2].
    + apply Hpb in H2. exact H2.
    + unfold n_empty in H2. discriminate H2.
  - unfold closed_Nats in *. intros x Hx.
    specialize (H3 x Hx). unfold N_lift in H3. unfold qor in H3. simpl in H3.
    unfold n_or in H3. apply orb_true_iff in H3. destruct H3 as [H3|H3].
    + apply Hpl in H3. exact H3.
    + unfold n_empty in H3. discriminate H3.
Qed.

Lemma has_type_value_closed_nl : forall Γ (Σ:senv) φ v T d,
  no_lookup Γ -> has_type Γ φ Σ v T d -> value v ->
  closed_ty 0 (‖Γ‖) (‖Σ‖) T /\ closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift d).
Proof.
  intros Γ Σ φ v T d Hnl H. induction H; intros Hv.
  - (* t_tabs *) split.
    + exact H0.
    + eapply closed_Qual_of_subq_or_diamond_f; [exact H1|].
      eapply Subq_trans; [exact H3|apply qor_subq_l].


  - inversion Hv.
  - inversion Hv.
  - split.
    + apply cl_TUnit.
    + apply closed_Qual_empty.
  - inversion Hv.
  - (* t_abs *) split.
    + eassumption.
    + eapply closed_Qual_of_subq_or_diamond_f; [exact H1|].
      eapply Subq_trans; [exact H3|apply qor_subq_l].
  - inversion Hv.
  - inversion Hv.
  - (* t_loc *) split.
    + eapply cl_TRef.
      * eapply closed_ty_weaken; [exact H1|lia|lia].
      * eapply closed_Qual_weaken; [exact H2|lia|lia].
    + assert (Hlt : l < ‖Σ‖) by (eapply sindexr_Some_lt; eassumption).
      eapply closed_Qual_amp; exact Hlt.
  - inversion Hv.
  - inversion Hv.
  - inversion Hv.
  - inversion Hv.
  - (* t_sub *) split.
    + destruct (IHhas_type Hnl Hv) as [Hct1 Hcq1].
      eapply stp_closed_target_nl; [exact Hnl|exact Hct1|exact H0].
    + assert (Hcφ : closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift φ)) by (eapply has_type_closed_phi; eassumption).
      eapply closed_Qual_of_subq_or_diamond_f; [exact Hcφ|exact H1].
  - inversion Hv.
  - inversion Hv.
Qed.

Lemma has_type_value_closed : forall (Σ:senv) φ v T d,
  has_type nil φ Σ v T d -> value v ->
  closed_ty 0 0 (‖Σ‖) T /\ closed_Qual 0 0 (‖Σ‖) (Q_lift d).
Proof.
  intros. eapply has_type_value_closed_nl with (Γ:=nil) (Σ:=Σ) (φ:=φ) (v:=v) (T:=T) (d:=d); [apply no_lookup_nil|exact H|exact H0].
Qed.

Lemma vtp_tunit_any : forall (Σ:senv) ϰ φ (d:qual),
  closed_Qual 0 0 (‖Σ‖) (Q_lift d) -> kill_sep ϰ d ->
  vtp Σ ϰ φ tunit TUnit d.
Proof. intros. eapply vtp_base; eassumption. Qed.

Lemma vtp_tunit_top_any : forall (Σ:senv) ϰ φ (d:qual),
  closed_Qual 0 0 (‖Σ‖) (Q_lift d) -> kill_sep ϰ d ->
  vtp Σ ϰ φ tunit TTop d.
Proof. intros. eapply vtp_top. eapply vtp_tunit_any; eassumption. Qed.

Lemma kill_sep_empty : forall (ϰ:qual), kill_sep ϰ q_empty.
Proof.
  intros. eapply Subq_trans. eapply qand_subq_l. apply q_empty_subq.
Qed.

Lemma vtp_tunit_shape : forall (Σ:senv) ϰ φ T d,
  vtp Σ ϰ φ tunit T d -> T = TUnit \/ T = TTop.
Proof.
  intros Σ ϰ φ T d Hv. inversion Hv; subst.
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma vtp_tunit_sub : forall (Σ:senv) ϰ φ T d T2 d2,
  vtp Σ ϰ φ tunit T d -> stp [] Σ T d T2 d2 ->
  d2 ⊑↑ (qor φ {♦}) -> closed_Qual 0 0 (‖Σ‖) (Q_lift d2) ->
  kill_sep ϰ φ -> vtp Σ ϰ φ tunit T2 d2.
Proof.
  intros Σ ϰ φ T d T2 d2 Hv Hs Hsub Hcl Hk.
  destruct (vtp_tunit_shape Σ ϰ φ T d Hv) as [E|E]; subst T.
  - destruct (stp_from_TUnit_shape [] Σ d T2 d2 Hs) as [E|E]; subst T2.
    + eapply vtp_top. eapply vtp_base; [exact Hcl|].
      eapply kill_sep_subq_or_diamond; eassumption.
    + eapply vtp_base; [exact Hcl|].
      eapply kill_sep_subq_or_diamond; eassumption.
  - assert (T2 = TTop) as E by (eapply stp_from_TTop; eassumption). subst T2.
    eapply vtp_top. eapply vtp_base; [exact Hcl|].
    eapply kill_sep_subq_or_diamond; eassumption.
Qed.

Lemma has_type_value_qual_subq : forall Γ φ Σ v T d,
  has_type Γ φ Σ v T d -> value v -> d ⊑↑ (qor φ {♦}).
Proof.
  intros Γ φ Σ v T d H. induction H; intros Hv; try (inversion Hv; fail).
  - (* t_tabs *) eapply Subq_trans; [exact H3|apply qor_subq_l].
  - (* t_base *) apply q_empty_subq.
  - (* t_abs *) eapply Subq_trans; [exact H3|apply qor_subq_l].
  - (* t_loc *) eapply Subq_trans; [exact H3|apply qor_subq_l].
  - (* t_sub *) exact H1.
Qed.

Lemma has_type_tunit_vtp : forall (Σ:senv) ϰ φ T d,
  has_type nil φ Σ tunit T d -> d ⊑↑ (qor φ {♦}) ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift d) -> kill_sep ϰ φ ->
  vtp Σ ϰ φ tunit T d.
Proof.
  intros Σ ϰ φ T d H Hsub Hcl Hk. remember nil as Γ eqn:EG in H. remember tunit as u eqn:Eu in H.
  induction H; try discriminate; subst.
  - (* t_base *) eapply vtp_base.
    + apply closed_Qual_empty.
    + apply kill_sep_empty.
  - (* t_sub *) 
    assert (closed_ty 0 0 (‖Σ‖) T1 /\ closed_Qual 0 0 (‖Σ‖) (Q_lift d1)) as [Hct Hcq].
    { eapply has_type_value_closed; [exact H|apply value_cst]. }
    assert (d1 ⊑↑ (qor φ {♦})) as Hsub1.
    { eapply has_type_value_qual_subq; [exact H|apply value_cst]. }
    eapply vtp_tunit_sub with (T:=T1) (d:=d1).
    + apply IHhas_type; [reflexivity|reflexivity|exact Hsub1|exact Hcq|exact Hk].
    + exact H0.
    + exact Hsub.
    + exact Hcl.
    + exact Hk.
Qed.

Lemma vtp_loc_data : forall (Σ:senv) ϰ φ l o T d,
  vtp Σ ϰ φ &(l,o) T d ->
  exists q2 U T0 q1,
    (T = TRef q2 U \/ T = TTop) /\
    sindexr l o Σ = Some (T0,q1) /\
    l ∈ₗ φ /\
    closed_ty 0 0 (‖Σ‖) T0 /\
    stp [] Σ T0 ∅ U ∅ /\
    stp [] Σ U ∅ T0 ∅ /\
    closed_Qual 0 0 (‖Σ‖) (Q_lift q1) /\
    closed_Qual 0 0 (‖Σ‖) (Q_lift q2) /\
    closed_Qual 0 0 (‖Σ‖) (Q_lift d) /\
    qstp [] Σ (&!l) d /\
    qstp [] Σ q1 q2 /\
    qstp [] Σ q2 q1 /\
    ♦∉ q1.
Proof.
  intros Σ ϰ φ l o T d H. remember &(l,o) as v eqn:Ev in H. induction H; try discriminate.
  - (* vtp_loc *) injection Ev as Hl Ho. subst l0 o0.
    eexists q2, U, T, q1. split; [left; reflexivity|].
    split; [exact H4|]. split; [exact H3|]. split; [exact H0|].
    split; [exact H5|]. split; [exact H6|]. split; [exact H1|].
    split; [exact H2|]. split; [exact H|]. split; [exact H7|].
    split; [exact H9|]. split; [exact H10|]. exact H8.
  - (* vtp_top *) destruct (IHvtp Ev) as (q2 & U & T0 & q1 & Hshape & Hrest).
    exists q2, U, T0, q1. split; [right; reflexivity|exact Hrest].
Qed.

Lemma stp_qstp : forall Γ (Σ:senv) T1 d1 T2 d2,
  stp Γ Σ T1 d1 T2 d2 -> qstp Γ Σ d1 d2.
Proof.
  intros Γ Σ T1 d1 T2 d2 H. induction H; eauto using qs_trans.
Qed.

Lemma stp_ref_ref_quals : forall Γ (Σ:senv) S d T2 d2,
  stp Γ Σ S d T2 d2 ->
  forall q U, S = TRef q U ->
  T2 = TTop \/
  (exists q' U', T2 = TRef q' U' /\ qstp Γ Σ q q' /\ qstp Γ Σ q' q /\
     stp Γ Σ U ∅ U' ∅ /\ stp Γ Σ U' ∅ U ∅).
Proof.
  intros Γ Σ S d T2 d2 H. induction H; intros q0 U0 ES; try discriminate; subst.
  - left. reflexivity.
  - (* s_ref *) injection ES as Hq HT. subst q1 T1.
    right. exists q2, T2. split; [reflexivity|split; [exact H2|split; [exact H3|split; [exact H0|exact H1]]]].
  - (* s_trans *) destruct (IHstp1 q0 U0 eq_refl) as [E|(qm & Um & E & H1 & H2 & Hs1 & Hs2)].
    + subst T2. left. eapply stp_from_TTop; eassumption.
    + subst T2.
      destruct (IHstp2 qm Um eq_refl) as [E|(q' & U' & E & H3 & H4 & Hs3 & Hs4)].
      * left. exact E.
      * right. exists q', U'. split; [exact E|split].
        -- eapply qs_trans; [exact H1|exact H3].
        -- split.
           ++ eapply qs_trans; [exact H4|exact H2].
           ++ split.
              ** eapply s_trans; [exact Hs1|exact Hs3].
              ** eapply s_trans; [exact Hs4|exact Hs2].
Qed.

Lemma vtp_loc_retarget : forall (Σ:senv) ϰ φ l o T d T2 d2,
  vtp Σ ϰ φ &(l,o) T d ->
  stp [] Σ T d T2 d2 ->
  d2 ⊑↑ (qor φ {♦}) ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift d2) ->
  kill_sep ϰ φ ->
  vtp Σ ϰ φ &(l,o) T2 d2.
Proof.
  intros Σ ϰ φ l o T d T2 d2 Hv Hs Hsub Hcl2 Hk.
  destruct (vtp_loc_data Σ ϰ φ l o T d Hv) as
    (q2 & U & T0 & q1 & Hshape & Hstore & Hmem & HclT0 & Hstp1 & Hstp2 &
     Hclq1 & Hclq2 & Hcld & Hqsld & Hqs12 & Hqs21 & Hnq1).
  assert (Hkd2 : kill_sep ϰ d2) by (eapply kill_sep_subq_or_diamond; eassumption).
  destruct Hshape as [ET|ET].
  - subst T.
    destruct (stp_ref_ref_quals [] Σ (TRef q2 U) d T2 d2 Hs q2 U eq_refl)
      as [E2|(q' & U' & E2 & Hqq' & Hq'q & HU1 & HU2)].
    + subst T2. eapply vtp_top. eapply vtp_loc.
      * exact Hcl2.
      * exact HclT0.
      * exact Hclq1.
      * exact Hclq2.
      * exact Hmem.
      * exact Hstore.
      * exact Hstp1.
      * exact Hstp2.
      * eapply qs_trans; [exact Hqsld|eapply stp_qstp; exact Hs].
      * exact Hnq1.
      * exact Hqs12.
      * exact Hqs21.
      * exact Hkd2.
    + subst T2.
      assert (Hclq' : closed_Qual 0 0 (‖Σ‖) (Q_lift q'))
        by (eapply qstp_closed_both_nl with (Γ:=nil) (Σ:=Σ) (q:=q2) (d:=q'); [apply no_lookup_nil|exact Hqq'|exact Hq'q|exact Hclq2]).
      eapply vtp_loc.
      * exact Hcl2.
      * exact HclT0.
      * exact Hclq1.
      * exact Hclq'.
      * exact Hmem.
      * exact Hstore.
      * eapply s_trans; [exact Hstp1|exact HU1].
      * eapply s_trans; [exact HU2|exact Hstp2].
      * eapply qs_trans; [exact Hqsld|eapply stp_qstp; exact Hs].
      * exact Hnq1.
      * eapply qs_trans; [exact Hqs12|exact Hqq'].
      * eapply qs_trans; [exact Hq'q|exact Hqs21].
      * exact Hkd2.
  - subst T.
    assert (E2 : T2 = TTop) by (eapply stp_from_TTop; exact Hs). subst T2.
    eapply vtp_top. eapply vtp_loc.
    * exact Hcl2.
    * exact HclT0.
    * exact Hclq1.
    * exact Hclq2.
    * exact Hmem.
    * exact Hstore.
    * exact Hstp1.
    * exact Hstp2.
    * eapply qs_trans; [exact Hqsld|eapply stp_qstp; exact Hs].
    * exact Hnq1.
    * exact Hqs12.
    * exact Hqs21.
    * exact Hkd2.
Qed.

Lemma has_type_loc_vtp : forall (Σ:senv) ϰ φ l o T d,
  has_type nil φ Σ &(l,o) T d -> d ⊑↑ (qor φ {♦}) ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift d) -> kill_sep ϰ φ ->
  vtp Σ ϰ φ &(l,o) T d.
Proof.
  intros Σ ϰ φ l o T d H Hsub Hcl Hk.
  remember nil as Γ eqn:EG in H. remember &(l,o) as v eqn:Ev in H.
  induction H; try discriminate; subst.
  - (* t_loc *) injection Ev as Hl Ho. subst l0 o0.
    eapply vtp_loc.
    + exact Hcl.
    + exact H1.
    + exact H2.
    + exact H2.
    + eapply qmem_loc_mono; [exact H3|apply mem_amp_self].
    + exact H0.
    + eapply stp_refl_closed; [apply Nat.le_refl|exact H1|apply closed_Qual_empty].
    + eapply stp_refl_closed; [apply Nat.le_refl|exact H1|apply closed_Qual_empty].
    + eapply qstp_refl; exact Hcl.
    + exact H4.
    + eapply qstp_refl; exact H2.
    + eapply qstp_refl; exact H2.
    + eapply kill_sep_subq_or_diamond; [exact Hk|eapply Subq_trans; [exact H3|apply qor_subq_l]].
  - (* t_sub *)
    assert (Hct : closed_ty 0 0 (‖Σ‖) T1 /\ closed_Qual 0 0 (‖Σ‖) (Q_lift d1))
      by (eapply has_type_value_closed; [exact H|apply value_loc]).
    destruct Hct as [Hct1 Hcd1].
    assert (Hsub1 : d1 ⊑↑ (qor φ {♦}))
      by (eapply has_type_value_qual_subq; [exact H|apply value_loc]).
    eapply vtp_loc_retarget.
    + apply IHhas_type; [reflexivity|reflexivity|exact Hsub1|exact Hcd1|exact Hk].
    + exact H0.
    + exact Hsub.
    + exact Hcl.
    + exact Hk.
Qed.

Lemma kill_sep_empty_l : forall (d:qual), kill_sep q_empty d.
Proof.
  intros d. unfold kill_sep.
  eapply Subq_trans; [apply qand_subq_r|apply q_empty_subq].
Qed.

Lemma closed_Qual_of_subq_nil : forall L (a b:qual),
  a ⊑↑ b -> closed_Qual 0 0 L (Q_lift b) ->
  closed_Qual 0 0 L (Q_lift a).
Proof.
  intros L a b Hsub Hb.
  eapply closed_Qual_of_subq_or_diamond_f with (b:=0) (f:=0) (φ:=b);
    [exact Hb|eapply Subq_trans; [exact Hsub|apply qor_subq_l]].
Qed.

Lemma vtp_qstp_retype : forall (Σ:senv) ϰ φ v T d,
  vtp Σ ϰ φ v T d ->
  forall d', qstp [] Σ d d' ->
    d' ⊑↑ (qor φ {♦}) -> closed_Qual 0 0 (‖Σ‖) (Q_lift d') ->
    kill_sep ϰ φ -> local_locs v = ∅ -> vtp Σ ϰ φ v T d'.
Proof.
  intros Σ ϰ φ v T d Hv. induction Hv; intros d' Hq Hsub Hcl Hk HL.
  - (* vtp_tabs *) simpl in HL. eapply vtp_tabs.
    + exact H.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
    + eapply qs_trans; [exact H4|exact Hq].
    + exact H5.
    + exact H6.
    + exact H7.
    + eapply kill_sep_subq_or_diamond; eassumption.
    + rewrite HL. apply kill_sep_empty_l.
  - (* vtp_base *) eapply vtp_base.
    + exact Hcl.
    + eapply kill_sep_subq_or_diamond; eassumption.
  - (* vtp_loc *) eapply vtp_loc.
    + exact Hcl.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
    + exact H4.
    + exact H5.
    + exact H6.
    + eapply qs_trans; [exact H7|exact Hq].
    + exact H8.
    + exact H9.
    + exact H10.
    + eapply kill_sep_subq_or_diamond; eassumption.
  - (* vtp_abs *) simpl in HL. eapply vtp_abs.
    + exact H.
    + exact Hcl.
    + exact H1.
    + exact H2.
    + exact H3.
    + exact H4.
    + eapply qs_trans; [exact H5|exact Hq].
    + exact H6.
    + exact H7.
    + exact H8.
    + eapply kill_sep_subq_or_diamond; eassumption.
    + rewrite HL. apply kill_sep_empty_l.
  - (* vtp_top *) eapply vtp_top. eapply IHHv.
    + exact Hq.
    + exact Hsub.
    + exact Hcl.
    + exact Hk.
    + exact HL.
Qed.

Lemma t_tabs_vtp : forall (Σ:senv) ϰ φ t T1 d1 T2 d2 df,
  closed_tm 2 0 (‖Σ‖) t ->
  closed_ty 0 0 (‖Σ‖) (TAll d1 d2 T1 T2) ->
  d1 ⊑↑ df ⊔ {♦} -> ♦∉ df -> kill_sep (local_locs t) df ->
  has_type [(bind_ty, false, T1, d1); (bind_tm, true, (TAll d1 d2 T1 T2), df)]
    (df ⊔ $!0 ⊔ $!1) Σ (t <~²ᵗ ([] : tenv)) (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv)) ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift df) ->
  df ⊑↑ (qor φ {♦}) -> kill_sep ϰ φ ->
  local_locs t = ∅ ->
  vtp Σ ϰ φ (ttabs t) (TAll d1 d2 T1 T2) df.
Proof.
  intros Σ ϰ φ t T1 d1 T2 d2 df Hctm Hct Hd1 Hnd Hkl Hbody Hcdf Hdf Hk HL.
  inversion Hct; subst.
  assert (Hct1 : closed_ty 0 0 (‖Σ‖) T1) by assumption.
  assert (Hcd1 : closed_Qual 0 0 (‖Σ‖) (Q_lift d1)) by assumption.
  assert (Hct2 : closed_ty 0 2 (‖Σ‖) (T2 <~²ᵀ ([] : tenv))).
  { change (closed_ty 0 2 (‖Σ‖) (open_pair_ty 0 0 T2)).
    eapply closed_ty_open_pair with (b:=2) (f:=0) (k:=0); [exact H9|reflexivity]. }
  assert (Hcd2 : closed_Qual 0 2 (‖Σ‖) (Q_lift (d2 <~²ᵈ ([] : tenv)))).
  { change (closed_Qual 0 2 (‖Σ‖) (Q_lift (openq_pair 0 0 d2))).
    eapply closed_Qual_openq_pair with (b:=2) (f:=0) (k:=0); [exact H7|reflexivity]. }
  eapply vtp_tabs.
  - exact Hctm.
  - eapply cl_TAll; eassumption.
  - eapply cl_TAll; eassumption.
  - exact Hbody.
  - eapply stp_refl_closed; [apply Nat.le_refl|exact Hct1|exact Hcd1].
  - eapply qstp_refl; exact Hcdf.
  - eapply stp_refl_closed; [apply Nat.le_refl|exact Hct2|exact Hcd2].
  - exact Hd1.
  - exact Hnd.
  - eapply kill_sep_subq_or_diamond; eassumption.
  - rewrite HL. apply kill_sep_empty_l.
Qed.

Lemma t_abs_vtp : forall (Σ:senv) ϰ φ t T1 d1 T2 d2 df,
  closed_tm 2 0 (‖Σ‖) t ->
  closed_ty 0 0 (‖Σ‖) (TFun d1 d2 T1 T2) ->
  d1 ⊑↑ df ⊔ {♦} -> ♦∉ df -> kill_sep (local_locs t) df ->
  has_type [(bind_tm, false, T1, d1); (bind_tm, true, (TFun d1 d2 T1 T2), df)]
    (df ⊔ $!0 ⊔ $!1) Σ (t <~²ᵗ ([] : tenv)) (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv)) ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift df) ->
  df ⊑↑ (qor φ {♦}) -> kill_sep ϰ φ ->
  local_locs t = ∅ ->
  vtp Σ ϰ φ (tabs t) (TFun d1 d2 T1 T2) df.
Proof.
  intros Σ ϰ φ t T1 d1 T2 d2 df Hctm Hct Hd1 Hnd Hkl Hbody Hcdf Hdf Hk HL.
  inversion Hct; subst.
  assert (Hct1 : closed_ty 0 0 (‖Σ‖) T1) by assumption.
  assert (Hcd1 : closed_Qual 0 0 (‖Σ‖) (Q_lift d1)) by assumption.
  assert (Hct2 : closed_ty 0 2 (‖Σ‖) (T2 <~²ᵀ ([] : tenv))).
  { change (closed_ty 0 2 (‖Σ‖) (open_pair_ty 0 0 T2)).
    eapply closed_ty_open_pair with (b:=2) (f:=0) (k:=0); [exact H9|reflexivity]. }
  assert (Hcd2 : closed_Qual 0 2 (‖Σ‖) (Q_lift (d2 <~²ᵈ ([] : tenv)))).
  { change (closed_Qual 0 2 (‖Σ‖) (Q_lift (openq_pair 0 0 d2))).
    eapply closed_Qual_openq_pair with (b:=2) (f:=0) (k:=0); [exact H7|reflexivity]. }
  eapply vtp_abs.
  - exact Hctm.
  - exact Hcdf.
  - eapply cl_TFun; eassumption.
  - eapply cl_TFun; eassumption.
  - exact Hbody.
  - eapply stp_refl_closed; [apply Nat.le_refl|exact Hct1|exact Hcd1].
  - eapply qstp_refl; exact Hcdf.
  - eapply stp_refl_closed; [apply Nat.le_refl|exact Hct2|exact Hcd2].
  - exact Hd1.
  - exact Hnd.
  - eapply kill_sep_subq_or_diamond; eassumption.
  - rewrite HL. apply kill_sep_empty_l.
Qed.

Lemma stp_trans : forall Γ (Σ:senv) T1 d1 T2 d2 T3 d3,
  stp Γ Σ T1 d1 T2 d2 -> stp Γ Σ T2 d2 T3 d3 -> stp Γ Σ T1 d1 T3 d3.
Proof. intros. eapply s_trans; eassumption. Qed.

Lemma qstp_trans : forall Γ (Σ:senv) d1 d2 d3,
  qstp Γ Σ d1 d2 -> qstp Γ Σ d2 d3 -> qstp Γ Σ d1 d3.
Proof. intros. eapply qs_trans; eassumption. Qed.

Lemma stp_top_refl : forall Γ (Σ:senv) (T:ty) d,
  closed_ty 0 (‖Γ‖) (‖Σ‖) T ->
  closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift d) ->
  stp Γ Σ T d TTop d.
Proof.
  intros. eapply s_top; [exact H|eapply qstp_refl; exact H0].
Qed.

Lemma qstp_refl_nil : forall (Σ:senv) (d:qual),
  closed_Qual 0 0 (‖Σ‖) (Q_lift d) -> qstp [] Σ d d.
Proof. intros. apply qstp_refl. exact H. Qed.

Lemma has_type_tunit_shape : forall Γ φ (Σ:senv) T d,
  has_type Γ φ Σ tunit T d -> T = TTop \/ T = TUnit.
Proof.
  intros Γ φ Σ T d H. remember tunit as u eqn:Eu in H.
  induction H; try discriminate; subst.
  - right. reflexivity.
  - destruct (IHhas_type eq_refl) as [E|E]; subst T1.
    + assert (T2 = TTop) as E2 by (eapply stp_from_TTop; exact H0). subst T2. left. reflexivity.
    + destruct (stp_from_TUnit_shape Γ Σ d1 T2 d2 H0) as [E2|E2]; subst T2;
        [left|right]; reflexivity.
Qed.

Lemma has_type_loc_shape : forall Γ φ (Σ:senv) l o T d,
  has_type Γ φ Σ &(l,o) T d ->
  T = TTop \/ exists q U, T = TRef q U.
Proof.
  intros Γ φ Σ l o T d H. remember &(l,o) as v eqn:Ev in H.
  induction H; try discriminate; subst.
  - injection Ev as Hl Ho. subst l0 o0. right. exists q, T. reflexivity.
  - destruct (IHhas_type eq_refl) as [E|(q0 & U0 & E)]; subst T1.
    + assert (T2 = TTop) as E2 by (eapply stp_from_TTop; exact H0). subst T2. left. reflexivity.
    + destruct (stp_from_TRef_shape Γ Σ q0 U0 d1 T2 d2 H0) as [E2|(q' & U & E2)]; subst T2.
      * left. reflexivity.
      * right. exists q', U. reflexivity.
Qed.

Lemma has_type_abs_shape : forall Γ φ (Σ:senv) t T d,
  has_type Γ φ Σ (tabs t) T d ->
  T = TTop \/ exists d1 d2 T1 T2, T = TFun d1 d2 T1 T2.
Proof.
  intros Γ φ Σ t T d H. remember (tabs t) as v eqn:Ev in H.
  induction H; try discriminate; subst.
  - right. exists d1, d2, T1, T2. reflexivity.
  - destruct (IHhas_type eq_refl) as [E|(a & b & c & e & E)]; subst T1.
    + assert (T2 = TTop) as E2 by (eapply stp_from_TTop; exact H0). subst T2. left. reflexivity.
    + destruct (stp_from_TFun_shape Γ Σ a b c e d1 T2 d2 H0) as [E2|(a' & b' & c' & e' & E2)]; subst T2.
      * left. reflexivity.
      * right. exists a', b', c', e'. reflexivity.
Qed.

Lemma has_type_ttabs_shape : forall Γ φ (Σ:senv) t T d,
  has_type Γ φ Σ (ttabs t) T d ->
  T = TTop \/ exists d1 d2 T1 T2, T = TAll d1 d2 T1 T2.
Proof.
  intros Γ φ Σ t T d H. remember (ttabs t) as v eqn:Ev in H.
  induction H; try discriminate; subst.
  - right. exists d1, d2, T1, T2. reflexivity.
  - destruct (IHhas_type eq_refl) as [E|(a & b & c & e & E)]; subst T1.
    + assert (T2 = TTop) as E2 by (eapply stp_from_TTop; exact H0). subst T2. left. reflexivity.
    + destruct (stp_from_TAll_shape Γ Σ a b c e d1 T2 d2 H0) as [E2|(a' & b' & c' & e' & E2)]; subst T2.
      * left. reflexivity.
      * right. exists a', b', c', e'. reflexivity.
Qed.

Lemma has_type_fun_canonical : forall Γ φ (Σ:senv) v d1 d2 T1 T2 d,
  has_type Γ φ Σ v (TFun d1 d2 T1 T2) d -> value v ->
  exists t, v = tabs t.
Proof.
  intros Γ φ Σ v d1 d2 T1 T2 d H Hv. destruct Hv.
  - exfalso. destruct (has_type_ttabs_shape Γ φ Σ t (TFun d1 d2 T1 T2) d H) as [E|(a&b&c&e&E)]; discriminate E.
  - exists t. reflexivity.
  - exfalso. destruct (has_type_tunit_shape Γ φ Σ (TFun d1 d2 T1 T2) d H) as [E|E]; discriminate E.
  - exfalso. destruct (has_type_loc_shape Γ φ Σ l o (TFun d1 d2 T1 T2) d H) as [E|(q&U&E)]; discriminate E.
Qed.

Lemma has_type_all_canonical : forall Γ φ (Σ:senv) v d1 d2 T1 T2 d,
  has_type Γ φ Σ v (TAll d1 d2 T1 T2) d -> value v ->
  exists t, v = ttabs t.
Proof.
  intros Γ φ Σ v d1 d2 T1 T2 d H Hv. destruct Hv.
  - exists t. reflexivity.
  - exfalso. destruct (has_type_abs_shape Γ φ Σ t (TAll d1 d2 T1 T2) d H) as [E|(a&b&c&e&E)]; discriminate E.
  - exfalso. destruct (has_type_tunit_shape Γ φ Σ (TAll d1 d2 T1 T2) d H) as [E|E]; discriminate E.
  - exfalso. destruct (has_type_loc_shape Γ φ Σ l o (TAll d1 d2 T1 T2) d H) as [E|(q&U&E)]; discriminate E.
Qed.

Lemma has_type_ref_canonical : forall Γ φ (Σ:senv) v q U d,
  has_type Γ φ Σ v (TRef q U) d -> value v ->
  exists l o, v = &(l,o).
Proof.
  intros Γ φ Σ v q U d H Hv. destruct Hv.
  - exfalso. destruct (has_type_ttabs_shape Γ φ Σ t (TRef q U) d H) as [E|(a&b&c&e&E)]; discriminate E.
  - exfalso. destruct (has_type_abs_shape Γ φ Σ t (TRef q U) d H) as [E|(a&b&c&e&E)]; discriminate E.
  - exfalso. destruct (has_type_tunit_shape Γ φ Σ (TRef q U) d H) as [E|E]; discriminate E.
  - exists l, o. reflexivity.
Qed.

Lemma has_type_unit_canonical : forall Γ φ (Σ:senv) v d,
  has_type Γ φ Σ v TUnit d -> value v -> v = tunit.
Proof.
  intros Γ φ Σ v d H Hv. destruct Hv.
  - exfalso. destruct (has_type_ttabs_shape Γ φ Σ t TUnit d H) as [E|(a&b&c&e&E)]; discriminate E.
  - exfalso. destruct (has_type_abs_shape Γ φ Σ t TUnit d H) as [E|(a&b&c&e&E)]; discriminate E.
  - reflexivity.
  - exfalso. destruct (has_type_loc_shape Γ φ Σ l o TUnit d H) as [E|(q&U&E)]; discriminate E.
Qed.

Lemma extends_refl : forall {A} (l:list A), l ⊇ l.
Proof. intros. exists []. reflexivity. Qed.

Lemma extends_2D_refl : forall (Σ:senv), Σ ⊇₂ Σ.
Proof.
  intros Σ l c H. exists c. split; [exact H|apply extends_refl].
Qed.

Lemma envUpdate_refl : forall (Σ:senv) φ ϰ LC,
  envUpdate Σ φ ϰ LC Σ φ ϰ.
Proof.
  intros. eapply env_phi; [apply extends_2D_refl|reflexivity].
Qed.

Lemma extends_trans : forall {A} (a b c:list A),
  a ⊇ b -> b ⊇ c -> a ⊇ c.
Proof.
  intros A a b c [l1 E1] [l2 E2]. exists (l1 ++ l2).
  rewrite E1, E2. rewrite app_assoc. reflexivity.
Qed.

Lemma extends_2D_trans : forall (A B C:senv),
  A ⊇₂ B -> B ⊇₂ C -> A ⊇₂ C.
Proof.
  intros A B C H1 H2 l c Hc.
  destruct (H2 l c Hc) as [c2 [H2l Hc2]].
  destruct (H1 l c2 H2l) as [c1 [H1l Hc1]].
  exists c1. split; [exact H1l|eapply extends_trans; eassumption].
Qed.

Lemma has_type_value_shape : forall Γ φ (Σ:senv) v T d,
  has_type Γ φ Σ v T d -> value v ->
  T = TTop \/ T = TUnit \/
  (exists q U, T = TRef q U) \/
  (exists d1 d2 T1 T2, T = TFun d1 d2 T1 T2) \/
  (exists d1 d2 T1 T2, T = TAll d1 d2 T1 T2).
Proof.
  intros Γ φ Σ v T d H Hv. destruct Hv.
  - destruct (has_type_ttabs_shape Γ φ Σ t T d H) as [E|(a&b&c&e&E)]; subst; eauto 10.
  - destruct (has_type_abs_shape Γ φ Σ t T d H) as [E|(a&b&c&e&E)]; subst; eauto 10.
  - destruct (has_type_tunit_shape Γ φ Σ T d H) as [E|E]; subst; eauto 10.
  - destruct (has_type_loc_shape Γ φ Σ l o T d H) as [E|(q&U&E)]; subst; eauto 10.
Qed.

Lemma closed_Qual_mono_b : forall b b' f L (q:Qual),
  closed_Qual b f L q -> b <= b' -> closed_Qual b' f L q.
Proof.
  intros b b' f L q [Hf [Hb Hl]] Hle. split; [exact Hf|split].
  - unfold closed_Nats in *. intros x Hx. apply Hb in Hx. lia.
  - exact Hl.
Qed.

Lemma closed_Qual_mono_f : forall b f f' L (q:Qual),
  closed_Qual b f L q -> f <= f' -> closed_Qual b f' L q.
Proof.
  intros b f f' L q [Hf [Hb Hl]] Hle. split; [|split].
  - unfold closed_Nats in *. intros x Hx. apply Hf in Hx. lia.
  - exact Hb.
  - exact Hl.
Qed.

Lemma closed_Qual_marker : forall x F L,
  x < F -> closed_Qual 0 F L (Q_lift $!x).
Proof.
  intros x F L Hx. unfold closed_Qual. split; [|split].
  - unfold closed_Nats. intros y Hy. unfold Q_lift, N_lift, qfvs, n_one in Hy. simpl in Hy.
    apply Nat.eqb_eq in Hy. subst. exact Hx.
  - unfold closed_Nats. intros y Hy. unfold Q_lift, N_lift, qbvs, n_empty in Hy. simpl in Hy. discriminate Hy.
  - unfold closed_Nats. intros y Hy. unfold Q_lift, N_lift, qlocs, n_empty in Hy. simpl in Hy. discriminate Hy.
Qed.

Lemma qstp_closed : forall Γ (Σ:senv) q d,
  qstp Γ Σ q d ->
  closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift q) /\
  closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift d).
Proof.
  intros Γ Σ q d H. induction H.
  - split.
    + eapply closed_Qual_of_subq_or_diamond_f with (b:=0) (f:=‖Γ‖) (φ:=d2);
        [exact H0|eapply Subq_trans; [exact H|apply qor_subq_l]].
    + exact H0.
  - assert (Hlt : f < ‖Γ‖) by (eapply indexr_Some_lt; exact H).
    split.
    + eapply closed_Qual_qor with (b:=0) (f:=‖Γ‖) (l:=‖Σ‖).
      * eapply closed_Qual_mono_f; [exact H0|apply Nat.lt_le_incl; exact Hlt].
      * eapply closed_Qual_marker; exact Hlt.
    + eapply closed_Qual_marker; exact Hlt.
  - assert (Hlt : f < ‖Γ‖) by (eapply indexr_Some_lt; exact H).
    split.
    + eapply closed_Qual_qor with (b:=0) (f:=‖Γ‖) (l:=‖Σ‖).
      * eapply closed_Qual_mono_f; [exact H0|apply Nat.lt_le_incl; exact Hlt].
      * eapply closed_Qual_marker; exact Hlt.
    + eapply closed_Qual_marker; exact Hlt.
  - assert (Hlt : x < ‖Γ‖) by (eapply indexr_Some_lt; exact H).
    split.
    + eapply closed_Qual_marker; exact Hlt.
    + eapply closed_Qual_mono_f; [exact H1|apply Nat.lt_le_incl; exact Hlt].
  - assert (Hlt : x < ‖Γ‖) by (eapply indexr_Some_lt; exact H).
    split.
    + eapply closed_Qual_marker; exact Hlt.
    + eapply closed_Qual_mono_f; [exact H1|apply Nat.lt_le_incl; exact Hlt].
  - split.
    + eapply closed_Qual_qor with (b:=0) (f:=‖Γ‖) (l:=‖Σ‖); [exact H0|exact (proj1 IHqstp)].
    + eapply closed_Qual_qor with (b:=0) (f:=‖Γ‖) (l:=‖Σ‖); [exact H0|exact (proj2 IHqstp)].
  - split.
    + exact (proj1 IHqstp1).
    + exact (proj2 IHqstp2).
Qed.

Lemma stp_closed_quals : forall Γ (Σ:senv) T1 d1 T2 d2,
  stp Γ Σ T1 d1 T2 d2 ->
  closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift d1) /\
  closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift d2).
Proof.
  intros Γ Σ T1 d1 T2 d2 H. induction H.
  - apply qstp_closed; exact H0.
  - apply qstp_closed; exact H0.
  - apply IHstp.
  - apply qstp_closed; exact H1.
  - apply qstp_closed; exact H.
  - apply qstp_closed; exact H.
  - apply qstp_closed; exact H1.
  - split; [apply (proj1 IHstp1)|apply (proj2 IHstp2)].
Qed.

Lemma stp_qstp_weaken : forall Γ (Σ:senv) T1 d1 T2 d2,
  stp Γ Σ T1 d1 T2 d2 ->
  forall d1' d2', qstp Γ Σ d1' d1 -> qstp Γ Σ d2 d2' ->
    stp Γ Σ T1 d1' T2 d2'.
Proof.
  intros Γ Σ T1 d1 T2 d2 H. induction H; intros d1' d2' Hq1 Hq2.
  - eapply s_top; [exact H|].
    eapply qstp_trans; [exact Hq1|eapply qstp_trans; [exact H0|exact Hq2]].
  - eapply s_tvar_refl; [exact H|].
    eapply qstp_trans; [exact Hq1|eapply qstp_trans; [exact H0|exact Hq2]].
  - eapply s_tvar_trans; [exact H|exact H0|]. eapply IHstp; eassumption.
  - eapply s_all; [exact H|exact H0| |exact H2|exact H3].
    eapply qstp_trans; [exact Hq1|eapply qstp_trans; [exact H1|exact Hq2]].
  - eapply s_base.
    eapply qstp_trans; [exact Hq1|eapply qstp_trans; [exact H|exact Hq2]].
  - eapply s_ref; [|exact H0|exact H1|exact H2|exact H3].
    eapply qstp_trans; [exact Hq1|eapply qstp_trans; [exact H|exact Hq2]].
  - eapply s_fun; [exact H|exact H0| |exact H2|exact H3].
    eapply qstp_trans; [exact Hq1|eapply qstp_trans; [exact H1|exact Hq2]].
  - pose proof (stp_closed_quals Γ Σ T1 d1 T2 d2 H) as [_ Hc2].
    eapply s_trans.
    + eapply IHstp1; [exact Hq1|apply qstp_refl; exact Hc2].
    + eapply IHstp2; [apply qstp_refl; exact Hc2|exact Hq2].
Qed.

Lemma stp_uniform : forall Γ (Σ:senv) T1 T2 d1 d2,
  stp Γ Σ T1 d1 T2 d2 ->
  forall d, closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift d) ->
    stp Γ Σ T1 d T2 d.
Proof.
  intros Γ Σ T1 T2 d1 d2 H. induction H; intros d Hd.
  - eapply s_top; [exact H|eapply qstp_refl; exact Hd].
  - eapply s_tvar_refl; [exact H|eapply qstp_refl; exact Hd].
  - eapply s_tvar_trans; [exact H|exact H0|]. eapply IHstp; exact Hd.
  - eapply s_all; [exact H|exact H0|eapply qstp_refl; exact Hd|exact H2|exact H3].
  - eapply s_base; eapply qstp_refl; exact Hd.
  - eapply s_ref; [eapply qstp_refl; exact Hd|exact H0|exact H1|exact H2|exact H3].
  - eapply s_fun; [exact H|exact H0|eapply qstp_refl; exact Hd|exact H2|exact H3].
  - eapply s_trans; [eapply IHstp1; exact Hd|eapply IHstp2; exact Hd].
Qed.

Lemma stp_uniform_nil : forall (Σ:senv) T1 T2 d1 d2 d,
  stp [] Σ T1 d1 T2 d2 ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift d) ->
  stp [] Σ T1 d T2 d.
Proof. intros. eapply stp_uniform; eassumption. Qed.

Lemma vtp_top_stp : forall (Σ:senv) ϰ φ v T d d',
  vtp Σ ϰ φ v T d ->
  stp [] Σ T d TTop d' ->
  d' ⊑↑ (qor φ {♦}) ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift d') ->
  kill_sep ϰ φ -> local_locs v = ∅ ->
  vtp Σ ϰ φ v TTop d'.
Proof.
  intros Σ ϰ φ v T d d' Hv Hstp Hsub Hcl Hk HL.
  eapply vtp_top.
  eapply vtp_qstp_retype with (d:=d) (d':=d').
  - exact Hv.
  - eapply stp_qstp; exact Hstp.
  - exact Hsub.
  - exact Hcl.
  - exact Hk.
  - exact HL.
Qed.

Lemma qstp_closed_nil : forall (Σ:senv) q d,
  qstp [] Σ q d ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift q) /\
  closed_Qual 0 0 (‖Σ‖) (Q_lift d).
Proof. intros. pose proof (qstp_closed [] Σ q d H) as Hc. simpl in Hc. exact Hc. Qed.

Lemma stp_closed_quals_nil : forall (Σ:senv) T1 d1 T2 d2,
  stp [] Σ T1 d1 T2 d2 ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift d1) /\
  closed_Qual 0 0 (‖Σ‖) (Q_lift d2).
Proof. intros. pose proof (stp_closed_quals [] Σ T1 d1 T2 d2 H) as Hc. simpl in Hc. exact Hc. Qed.

Lemma stp_qstp_nil : forall (Σ:senv) T1 d1 T2 d2,
  stp [] Σ T1 d1 T2 d2 -> qstp [] Σ d1 d2.
Proof. intros. eapply stp_qstp; exact H. Qed.

Lemma stp_closed_both_nil : forall (Σ:senv) T1 d1 T2 d2,
  stp [] Σ T1 d1 T2 d2 ->
  closed_ty 0 0 (‖Σ‖) T1 -> closed_ty 0 0 (‖Σ‖) T2.
Proof.
  intros. eapply stp_closed_target_nil; [exact H0|exact H].
Qed.

Lemma CtxOK_qdom : forall Γ φ (Σ:senv) ϰ σ,
  CtxOK Γ φ Σ ϰ σ -> qdom' σ ⊑↑ qdom Σ.
Proof. intros Γ φ Σ ϰ σ H. destruct H as [H _]. exact H. Qed.

Lemma CtxOK_length : forall Γ φ (Σ:senv) ϰ σ,
  CtxOK Γ φ Σ ϰ σ -> ‖σ‖ = ‖Σ‖.
Proof. intros Γ φ Σ ϰ σ H. destruct H as [_ [H _]]. exact H. Qed.

Lemma CtxOK_phi : forall Γ φ (Σ:senv) ϰ σ,
  CtxOK Γ φ Σ ϰ σ -> φ ⊑↑ qdom Σ.
Proof. intros Γ φ Σ ϰ σ H. destruct H as [_ [_ [H _]]]. exact H. Qed.

Lemma CtxOK_kappa_closed : forall Γ φ (Σ:senv) ϰ σ,
  CtxOK Γ φ Σ ϰ σ -> closed_Qual 0 0 (‖Σ‖) (Q_lift ϰ).
Proof. intros Γ φ Σ ϰ σ H. destruct H as [_ [_ [_ [H _]]]]. exact H. Qed.

Lemma CtxOK_kill : forall Γ φ (Σ:senv) ϰ σ,
  CtxOK Γ φ Σ ϰ σ -> kill_sep ϰ φ.
Proof. intros Γ φ Σ ϰ σ H. destruct H as [_ [_ [_ [_ [H _]]]]]. exact H. Qed.

Lemma CtxOK_cell : forall Γ φ (Σ:senv) ϰ σ l o cty T q,
  CtxOK Γ φ Σ ϰ σ ->
  (l ∈ₗ ϰ -> indexr l σ = Some None) /\
  (~(l ∈ₗ ϰ) -> l ∈ₗ φ -> indexr l Σ = Some cty ->
    (exists ctm, (indexr l σ = Some (Some ctm) /\ ‖cty‖ = ‖ctm‖) /\
      (indexr o cty = Some (T,q) ->
        exists v, indexr o ctm = Some v /\ value v /\
          (q ⊑↑ φ -> vtp Σ ϰ φ v T q)))).
Proof. intros. destruct H as [_ [_ [_ [_ [_ H]]]]]. apply H. Qed.

Lemma preserve_ext : forall Γ (Σ:senv) ϰ φ LC t' T d σ',
  preserve Γ Σ ϰ φ LC t' T d σ' -> exists Σ', Σ' ⊇₂ Σ.
Proof. intros. destruct H as [Σ' d' φ' ϰ' H _]. eexists. exact H. Qed.

Lemma preserve_envUpdate : forall Γ (Σ:senv) ϰ φ LC t' T d σ',
  preserve Γ Σ ϰ φ LC t' T d σ' ->
  exists Σ' φ' ϰ', envUpdate Σ φ ϰ LC Σ' φ' ϰ'.
Proof. intros. destruct H as [Σ' d' φ' ϰ' _ H]. eauto. Qed.

Lemma preserve_qual : forall Γ (Σ:senv) ϰ φ LC t' T d σ',
  preserve Γ Σ ϰ φ LC t' T d σ' ->
  exists φ' d', d' ⊑↑ φ'.
Proof. intros. destruct H as [Σ' d' φ' ϰ' _ _ H]. eauto. Qed.

Lemma preserve_wf_senv : forall Γ (Σ:senv) ϰ φ LC t' T d σ',
  preserve Γ Σ ϰ φ LC t' T d σ' -> exists Σ', wf_senv Σ'.
Proof. intros. destruct H as [Σ' d' φ' ϰ' _ _ _ H]. eauto. Qed.

Lemma preserve_CtxOK : forall Γ (Σ:senv) ϰ φ LC t' T d σ',
  preserve Γ Σ ϰ φ LC t' T d σ' ->
  exists Σ' φ' ϰ', CtxOK Γ φ' Σ' ϰ' σ'.
Proof. intros. destruct H as [Σ' d' φ' ϰ' _ _ _ _ H]. eauto. Qed.

Lemma preserve_disjoint : forall Γ (Σ:senv) ϰ φ LC t' T d σ',
  preserve Γ Σ ϰ φ LC t' T d σ' ->
  exists Σ' d', Σ → Σ' ∋ d ⊕ d'.
Proof. intros. destruct H as [Σ' d' φ' ϰ' _ _ _ _ _ H]. eauto. Qed.

Lemma preserve_has_type : forall Γ (Σ:senv) ϰ φ LC t' T d σ',
  preserve Γ Σ ϰ φ LC t' T d σ' ->
  exists Σ' φ' d', has_type Γ φ' Σ' t' T (d ⋓ d').
Proof. intros. destruct H as [Σ' d' φ' ϰ' _ _ _ _ _ _ H]. eauto. Qed.

Lemma preserve_wf_store : forall Γ (Σ:senv) ϰ φ LC t' T d σ',
  preserve Γ Σ ϰ φ LC t' T d σ' -> wf_store σ'.
Proof. intros. destruct H as [Σ' d' φ' ϰ' _ _ _ _ _ _ _ H]. exact H. Qed.

Lemma preserve_wf_step : forall Γ (Σ:senv) ϰ φ LC t' T d σ',
  preserve Γ Σ ϰ φ LC t' T d σ' -> wf_step t'.
Proof. intros. destruct H as [Σ' d' φ' ϰ' _ _ _ _ _ _ _ _ H]. exact H. Qed.

Lemma wf_step_ttabs : forall t, wf_step (ttabs t) -> local_locs t = q_empty.
Proof. intros. simpl in H. exact H. Qed.
Lemma wf_step_ttapp : forall t, wf_step (ttapp t) -> wf_step t.
Proof. intros. simpl in H. exact H. Qed.
Lemma wf_step_tabs : forall t, wf_step (tabs t) -> local_locs t = q_empty.
Proof. intros. simpl in H. exact H. Qed.
Lemma wf_step_tapp : forall t1 t2, wf_step (tapp t1 t2) ->
  wf_step t1 /\ wf_step t2 /\ (value t1 \/ local_locs t2 = q_empty).
Proof. intros. simpl in H. exact H. Qed.
Lemma wf_step_tref : forall t, wf_step (tref t) -> wf_step t.
Proof. intros. simpl in H. exact H. Qed.
Lemma wf_step_trefat : forall t1 t2, wf_step (trefat t1 t2) ->
  wf_step t1 /\ wf_step t2 /\ (local_locs t1 = q_empty \/ value t2).
Proof. intros. simpl in H. exact H. Qed.
Lemma wf_step_tderef : forall t, wf_step (tderef t) -> wf_step t.
Proof. intros. simpl in H. exact H. Qed.
Lemma wf_step_tassign : forall t1 t2, wf_step (tassign t1 t2) ->
  wf_step t1 /\ wf_step t2 /\ (value t1 \/ local_locs t2 = q_empty).
Proof. intros. simpl in H. exact H. Qed.
Lemma wf_step_twithr : forall t1 t2, wf_step (twithr t1 t2) ->
  wf_step t1 /\ wf_step t2 /\ local_locs t2 = q_empty.
Proof. intros. simpl in H. exact H. Qed.
Lemma wf_step_twithc : forall l t, wf_step (twithc l t) -> wf_step t.
Proof. intros. simpl in H. exact H. Qed.

Lemma closed_Qual_qand : forall b f l (a c:qual),
  closed_Qual b f l (Q_lift a) -> closed_Qual b f l (Q_lift c) ->
  closed_Qual b f l (Q_lift (qand a c)).
Proof.
  intros b f l a c Ha Hc. destruct Ha as [Haf [Hab Hal]]. destruct Hc as [Hcf [Hcb Hcl]].
  unfold closed_Qual. split; [|split].
  - unfold closed_Nats in *. intros x Hx. unfold N_lift in *. simpl in Hx.
    apply andb_true_iff in Hx. destruct Hx as [H H']. apply Haf in H. apply Hcf in H'. lia.
  - unfold closed_Nats in *. intros x Hx. unfold N_lift in *. simpl in Hx.
    apply andb_true_iff in Hx. destruct Hx as [H H']. apply Hab in H. apply Hcb in H'. lia.
  - unfold closed_Nats in *. intros x Hx. unfold N_lift in *. simpl in Hx.
    apply andb_true_iff in Hx. destruct Hx as [H H']. apply Hal in H. apply Hcl in H'. lia.
Qed.

Lemma CtxOK_lookup_value : forall Γ φ (Σ:senv) ϰ σ l o cty T q,
  CtxOK Γ φ Σ ϰ σ ->
  ~(l ∈ₗ ϰ) -> l ∈ₗ φ -> indexr l Σ = Some cty ->
  indexr o cty = Some (T,q) -> q ⊑↑ φ ->
  exists ctm v, indexr l σ = Some (Some ctm) /\ indexr o ctm = Some v /\
    value v /\ vtp Σ ϰ φ v T q.
Proof.
  intros Γ φ Σ ϰ σ l o cty T q Hctx Hk Hl HlΣ Ho Hsub.
  destruct (CtxOK_cell Γ φ Σ ϰ σ l o cty T q Hctx) as [_ Hcell].
  destruct (Hcell Hk Hl HlΣ) as [ctm [Hlspec Hspec]].
  destruct Hlspec as [Hlσ _].
  destruct (Hspec Ho) as [v [Hvo [Hval Hvtp]]].
  exists ctm, v. split; [exact Hlσ|split; [exact Hvo|split; [exact Hval|apply Hvtp; exact Hsub]]].
Qed.

Lemma CtxOK_lookup_exists_value : forall Γ φ (Σ:senv) ϰ σ l o cty T q,
  CtxOK Γ φ Σ ϰ σ ->
  ~(l ∈ₗ ϰ) -> l ∈ₗ φ -> indexr l Σ = Some cty ->
  indexr o cty = Some (T,q) ->
  exists ctm v, indexr l σ = Some (Some ctm) /\ indexr o ctm = Some v /\ value v.
Proof.
  intros Γ φ Σ ϰ σ l o cty T q Hctx Hk Hl HlΣ Ho.
  destruct (CtxOK_cell Γ φ Σ ϰ σ l o cty T q Hctx) as [_ Hcell].
  destruct (Hcell Hk Hl HlΣ) as [ctm [Hlspec Hspec]].
  destruct Hlspec as [Hlσ _].
  destruct (Hspec Ho) as [v [Hvo [Hval _]]].
  exists ctm, v. split; [exact Hlσ|split; [exact Hvo|exact Hval]].
Qed.

Lemma kill_sep_not_both : forall (ϰ φ:qual) l,
  kill_sep ϰ φ -> l ∈ₗ φ -> ~(l ∈ₗ ϰ).
Proof.
  intros ϰ φ l Hk Hphi Hkapp.
  assert (Hmem : l ∈ₗ qand φ ϰ).
  { unfold qmem, N_lift. change (qlocs (qand φ ϰ) l = true).
    unfold qand, qlocs, n_and. apply andb_true_iff.
    split; [unfold qmem, N_lift in Hphi; exact Hphi|unfold qmem, N_lift in Hkapp; exact Hkapp]. }
  pose proof (qmem_loc_mono l (qand φ ϰ) {♦} Hk Hmem) as Hd.
  unfold qmem, N_lift, qlocs, n_empty in Hd. simpl in Hd. discriminate Hd.
Qed.

Lemma CtxOK_lookup_phi : forall Γ φ (Σ:senv) ϰ σ l o cty T q,
  CtxOK Γ φ Σ ϰ σ ->
  l ∈ₗ φ -> indexr l Σ = Some cty -> indexr o cty = Some (T,q) ->
  exists ctm v, indexr l σ = Some (Some ctm) /\ indexr o ctm = Some v /\
    value v /\ (q ⊑↑ φ -> vtp Σ ϰ φ v T q).
Proof.
  intros Γ φ Σ ϰ σ l o cty T q Hctx Hl HlΣ Ho.
  assert (Hnk : ~(l ∈ₗ ϰ)) by (eapply kill_sep_not_both; [eapply CtxOK_kill; exact Hctx|exact Hl]).
  destruct (CtxOK_cell Γ φ Σ ϰ σ l o cty T q Hctx) as [_ Hcell].
  destruct (Hcell Hnk Hl HlΣ) as [ctm [Hlspec Hspec]].
  destruct Hlspec as [Hlσ _].
  destruct (Hspec Ho) as [v [Hvo [Hval Hvtp]]].
  exists ctm, v. split; [exact Hlσ|split; [exact Hvo|split; [exact Hval|exact Hvtp]]].
Qed.

Lemma CtxOK_lookup_none : forall Γ φ (Σ:senv) ϰ σ l (o:offset) (cty:senvs) (T:ty) (q:qual),
  CtxOK Γ φ Σ ϰ σ -> l ∈ₗ ϰ -> indexr l σ = Some None.
Proof.
  intros Γ φ Σ ϰ σ l o cty T q Hctx Hl.
  destruct (CtxOK_cell Γ φ Σ ϰ σ l o cty T q Hctx) as [H _]. apply H. exact Hl.
Qed.

Lemma value_no_step : forall v σ t' σ',
  value v -> step v σ t' σ' -> False.
Proof.
  intros v σ t' σ' Hv Hs. destruct Hv; inversion Hs.
Qed.

Definition CtxLive (φ:qual) (Σ:senv) (σ:store) : Prop :=
  forall l o cty T q,
    l ∈ₗ φ -> indexr l Σ = Some cty -> indexr o cty = Some (T,q) ->
    exists ctm v, indexr l σ = Some (Some ctm) /\ indexr o ctm = Some v /\ value v.

Lemma CtxOK_live : forall Γ φ (Σ:senv) ϰ σ,
  CtxOK Γ φ Σ ϰ σ -> CtxLive φ Σ σ.
Proof.
  intros Γ φ Σ ϰ σ Hctx l o cty T q Hl HlΣ Ho.
  assert (Hnk : ~(l ∈ₗ ϰ)) by (eapply kill_sep_not_both; [eapply CtxOK_kill; exact Hctx|exact Hl]).
  eapply CtxOK_lookup_exists_value; [exact Hctx|exact Hnk|exact Hl|exact HlΣ|exact Ho].
Qed.

Lemma CtxLive_weaken : forall (φ φ':qual) (Σ:senv) (σ:store),
  CtxLive φ Σ σ -> φ' ⊑↑ φ -> CtxLive φ' Σ σ.
Proof.
  intros φ φ' Σ σ Hlive Hsub l o cty T q Hl HlΣ Ho.
  eapply Hlive; [|exact HlΣ|exact Ho].
  eapply qmem_loc_mono; [exact Hsub|exact Hl].
Qed.

Lemma has_type_loc_mem : forall Γ φ (Σ:senv) l o T d,
  has_type Γ φ Σ &(l,o) T d -> l ∈ₗ φ.
Proof.
  intros Γ φ Σ l o T d H. remember &(l,o) as v eqn:Ev in H.
  induction H; try discriminate; subst.
  - injection Ev as Hl Ho. subst l0 o0. eapply qmem_loc_mono; [exact H3|apply mem_amp_self].
  - apply IHhas_type. reflexivity.
Qed.

Lemma sindexr_Some_decomp : forall {A} (Σ:list (list A)) l o x,
  sindexr l o Σ = Some x ->
  exists cty, indexr l Σ = Some cty /\ indexr o cty = Some x.
Proof.
  intros A Σ l o x H. rewrite sindexr_lookup in H.
  destruct (indexr l Σ) as [c|] eqn:E; [|discriminate].
  exists c. split; [reflexivity|exact H].
Qed.

Lemma has_type_loc_store : forall Γ φ (Σ:senv) l o T d,
  has_type Γ φ Σ &(l,o) T d ->
  exists cty T0 q0, indexr l Σ = Some cty /\ indexr o cty = Some (T0,q0).
Proof.
  intros Γ φ Σ l o T d H. remember &(l,o) as v eqn:Ev in H.
  induction H; try discriminate; subst.
  - injection Ev as Hl Ho. subst l0 o0.
    destruct (sindexr_Some_decomp Σ l o (T,q) H0) as [cty [HlΣ HoΣ]].
    exists cty, T, q. split; assumption.
  - apply IHhas_type. reflexivity.
Qed.

Lemma step_deref_live : forall (φ:qual) (Σ:senv) (σ:store) l o cty T0 q0,
  CtxLive φ Σ σ -> l ∈ₗ φ -> indexr l Σ = Some cty ->
  indexr o cty = Some (T0,q0) ->
  exists v, step (! &(l,o)) σ v σ.
Proof.
  intros φ Σ σ l o cty T0 q0 Hlive Hl HlΣ Ho.
  destruct (Hlive l o cty T0 q0 Hl HlΣ Ho) as [ctm [v [Hlσ [Hvo Hval]]]].
  exists v. eapply step_deref; eassumption.
Qed.

Lemma step_assign_live : forall (φ:qual) (Σ:senv) (σ:store) l o cty T0 q0 v,
  CtxLive φ Σ σ -> ‖σ‖ = ‖Σ‖ -> l ∈ₗ φ -> indexr l Σ = Some cty ->
  indexr o cty = Some (T0,q0) -> value v ->
  step (tassign &(l,o) v) σ tunit (supdate σ l o v).
Proof.
  intros φ Σ σ l o cty T0 q0 v Hlive Hlen Hl HlΣ Ho Hval.
  destruct (Hlive l o cty T0 q0 Hl HlΣ Ho) as [ctm [v0 [Hlσ [Hvo Hv0]]]].
  assert (Hlσlt : l < ‖σ‖) by (rewrite Hlen; eapply indexr_Some_lt; exact HlΣ).
  assert (Holt : o < ‖ctm‖) by (eapply indexr_Some_lt; exact Hvo).
  eapply step_assign; [exact Hlσlt|exact Hlσ|exact Holt|exact Hval].
Qed.

Lemma step_refat_live : forall (φ:qual) (Σ:senv) (σ:store) l o cty T0 q0 v,
  CtxLive φ Σ σ -> l ∈ₗ φ -> indexr l Σ = Some cty ->
  indexr o cty = Some (T0,q0) -> value v ->
  exists s, indexr l σ = Some (Some s) /\ step (trefat v &(l,o)) σ &(l, ‖s‖) (cinsert σ l v).
Proof.
  intros φ Σ σ l o cty T0 q0 v Hlive Hl HlΣ Ho Hval.
  destruct (Hlive l o cty T0 q0 Hl HlΣ Ho) as [ctm [v0 [Hlσ [Hvo _]]]].
  exists ctm. split; [exact Hlσ|eapply step_refat; [exact Hval|exact Hlσ]].
Qed.

Definition CtxLiveLen (φ:qual) (Σ:senv) (σ:store) : Prop :=
  CtxLive φ Σ σ /\ ‖σ‖ = ‖Σ‖.

Lemma CtxOK_live_len : forall Γ φ (Σ:senv) ϰ σ,
  CtxOK Γ φ Σ ϰ σ -> CtxLiveLen φ Σ σ.
Proof.
  intros. split; [eapply CtxOK_live; eassumption|eapply CtxOK_length; eassumption].
Qed.

Lemma CtxLiveLen_weaken : forall (φ φ':qual) (Σ:senv) (σ:store),
  CtxLiveLen φ Σ σ -> φ' ⊑↑ φ -> CtxLiveLen φ' Σ σ.
Proof.
  intros φ φ' Σ σ [Hlive Hlen] Hsub. split;
    [eapply CtxLive_weaken; eassumption|exact Hlen].
Qed.

Lemma step_refat_context : forall t1 t2 t2' σ σ',
  step t2 σ t2' σ' -> step (trefat t1 t2) σ (trefat t1 t2') σ'.
Proof. intros. eapply step_c_refat_r; exact H. Qed.

Lemma progress_live : forall (Σ:senv) t T d φ,
  has_type [] φ Σ t T d -> wf_senv Σ -> wf_step t ->
  forall σ, CtxLiveLen φ Σ σ ->
  value t \/ exists t' σ', step t σ t' σ'.
Proof.
  intros Σ t T d φ H. remember (@nil (binding * bool * ty * qual)) as Γ eqn:EG in H.
  induction H; intros Hwf Hws σ Hlive; try subst.
  - left. apply value_ttabs.
  - destruct (IHhas_type eq_refl Hwf (wf_step_ttapp t Hws) σ Hlive) as [Hv|(t' & σ' & Hstep)].
    + destruct (has_type_all_canonical [] φ Σ t d1 d2 T1 T2 df H Hv) as [tb Et].
      subst t. right. eexists. eexists. apply step_ttapp.
    + right. eexists. eexists. eapply step_c_tapp; exact Hstep.
  - destruct (IHhas_type eq_refl Hwf (wf_step_ttapp t Hws) σ Hlive) as [Hv|(t' & σ' & Hstep)].
    + destruct (has_type_all_canonical [] φ Σ t _ _ _ _ _ H Hv) as [tb Et].
      subst t. right. eexists. eexists. apply step_ttapp.
    + right. eexists. eexists. eapply step_c_tapp; exact Hstep.
  - left. apply value_cst.
  - inversion H.
  - left. apply value_abs.
  - destruct (wf_step_tapp t1 t2 Hws) as [Hws1 [Hws2 _]].
    destruct (IHhas_type1 eq_refl Hwf Hws1 σ Hlive) as [Hv1|Hstep1].
    + destruct (IHhas_type2 eq_refl Hwf Hws2 σ
                 (CtxLiveLen_weaken φ (qdiff φ (local_locs t1)) Σ σ Hlive (qdiff_subq_l φ (local_locs t1)))) as [Hv2|Hstep2].
      * destruct (has_type_fun_canonical [] φ Σ t1 d1 d2 T1 T2 df H Hv1) as [tb Et].
        subst t1. right. eexists. eexists. eapply step_beta; exact Hv2.
      * destruct Hstep2 as (t2' & σ' & Hs2).
        right. eexists. eexists. eapply step_c_app_r; [exact Hv1|exact Hs2].
    + destruct Hstep1 as (t1' & σ' & Hs1).
      right. eexists. eexists. eapply step_c_app_l; exact Hs1.
  - destruct (wf_step_tapp t1 t2 Hws) as [Hws1 [Hws2 _]].
    destruct (IHhas_type1 eq_refl Hwf Hws1 σ Hlive) as [Hv1|Hstep1].
    + destruct (IHhas_type2 eq_refl Hwf Hws2 σ
                 (CtxLiveLen_weaken φ (qdiff φ (local_locs t1)) Σ σ Hlive (qdiff_subq_l φ (local_locs t1)))) as [Hv2|Hstep2].
      * destruct (has_type_fun_canonical [] φ Σ t1 _ _ _ _ _ H Hv1) as [tb Et].
        subst t1. right. eexists. eexists. eapply step_beta; exact Hv2.
      * destruct Hstep2 as (t2' & σ' & Hs2).
        right. eexists. eexists. eapply step_c_app_r; [exact Hv1|exact Hs2].
    + destruct Hstep1 as (t1' & σ' & Hs1).
      right. eexists. eexists. eapply step_c_app_l; exact Hs1.
  - left. apply value_loc.
  - destruct (IHhas_type eq_refl Hwf (wf_step_tref t Hws) σ Hlive) as [Hv|Hstep].
    + right. eexists. eexists. eapply step_ref; exact Hv.
    + destruct Hstep as (t' & σ' & Hs). right. eexists. eexists. eapply step_c_ref; exact Hs.
  - destruct (wf_step_trefat t1 t2 Hws) as [Hws1 [Hws2 _]].
    destruct (IHhas_type2 eq_refl Hwf Hws2 σ Hlive) as [Hv2|Hstep2].
    + destruct (has_type_ref_canonical [] φ Σ t2 d1 T1 d2 H1 Hv2) as (l & o & Et2).
      subst t2.
      destruct (IHhas_type1 eq_refl Hwf Hws1 σ
        (CtxLiveLen_weaken φ (qdiff φ (local_locs &(l,o))) Σ σ Hlive
          (qdiff_subq_l φ (local_locs &(l,o))))) as [Hv1|Hstep1].
      * destruct (has_type_loc_store [] φ Σ l o (TRef d1 T1) d2 H1) as (cty & T0 & q0 & HlΣ & Ho).
        assert (Hl : l ∈ₗ φ) by (eapply has_type_loc_mem; exact H1).
        destruct (step_refat_live φ Σ σ l o cty T0 q0 t1 (proj1 Hlive) Hl HlΣ Ho Hv1) as (s & Hls & Hstep).
        right. eexists. eexists. exact Hstep.
      * destruct Hstep1 as (t1' & σ' & Hs1).
        right. eexists. eexists. eapply step_c_refat_l; [exact Hv2|exact Hs1].
    + destruct Hstep2 as (t2' & σ' & Hs2).
      right. eexists. eexists. eapply step_c_refat_r; exact Hs2.
  - destruct (IHhas_type eq_refl Hwf (wf_step_tderef t Hws) σ Hlive) as [Hv|Hstep].
    + destruct (has_type_ref_canonical [] φ Σ t d1 T d H Hv) as (l & o & Et). subst t.
      destruct (has_type_loc_store [] φ Σ l o (TRef d1 T) d H) as (cty & T0 & q0 & HlΣ & Ho).
      assert (Hl : l ∈ₗ φ) by (eapply has_type_loc_mem; exact H).
      destruct (step_deref_live φ Σ σ l o cty T0 q0 (proj1 Hlive) Hl HlΣ Ho) as (v & Hstep).
      right. eexists. eexists. exact Hstep.
    + destruct Hstep as (t' & σ' & Hs). right. eexists. eexists. eapply step_c_deref; exact Hs.
  - destruct (wf_step_tassign t1 t2 Hws) as [Hws1 [Hws2 _]].
    destruct (IHhas_type1 eq_refl Hwf Hws1 σ Hlive) as [Hv1|Hstep1].
    + destruct (IHhas_type2 eq_refl Hwf Hws2 σ
        (CtxLiveLen_weaken φ (qdiff φ (local_locs t1)) Σ σ Hlive
          (qdiff_subq_l φ (local_locs t1)))) as [Hv2|Hstep2].
      * destruct (has_type_ref_canonical [] φ Σ t1 d1 T d H Hv1) as (l & o & Et1).
        subst t1.
        destruct (has_type_loc_store [] φ Σ l o (TRef d1 T) d H) as (cty & T0 & q0 & HlΣ & Ho).
        assert (Hl : l ∈ₗ φ) by (eapply has_type_loc_mem; exact H).
        right. eexists. eexists.
        eapply step_assign_live; [exact (proj1 Hlive)|exact (proj2 Hlive)|exact Hl|exact HlΣ|exact Ho|exact Hv2].
      * destruct Hstep2 as (t2' & σ' & Hs2).
        right. eexists. eexists. eapply step_c_assign_r; [exact Hv1|exact Hs2].
    + destruct Hstep1 as (t1' & σ' & Hs1).
      right. eexists. eexists. eapply step_c_assign_l; exact Hs1.
  - apply (IHhas_type eq_refl Hwf Hws σ Hlive).
  - destruct (wf_step_twithr t1 t2 Hws) as [Hws1 [Hws2 _]].
    destruct (IHhas_type1 eq_refl Hwf Hws1 σ Hlive) as [Hv1|Hstep1].
    + right. eexists. eexists. eapply step_twithr; exact Hv1.
    + destruct Hstep1 as (t1' & σ' & Hs1).
      right. eexists. eexists. eapply step_c_twithr_l; exact Hs1.
  - destruct (IHhas_type eq_refl Hwf (wf_step_twithc l t Hws) σ Hlive) as [Hv|Hstep].
    + right. eexists. eexists. eapply step_twithc; exact Hv.
    + destruct Hstep as (t' & σ' & Hs).
      right. eexists. eexists. eapply step_c_twithc; exact Hs.
Qed.

Lemma progress_ctx : forall (Σ:senv) ϰ t T d φ,
  has_type [] φ Σ t T d -> wf_senv Σ -> wf_step t ->
  forall σ, CtxOK [] φ Σ ϰ σ -> wf_store σ ->
  value t \/ exists t' σ', step t σ t' σ'.
Proof.
  intros Σ ϰ t T d φ H Hwf Hws σ Hctx Hstore.
  eapply progress_live; [exact H|exact Hwf|exact Hws|].
  eapply CtxOK_live_len; exact Hctx.
Qed.

Lemma preserve_intro : forall Γ (Σ:senv) ϰ φ LC t' T d σ'
  Σ' d' φ' ϰ',
  Σ' ⊇₂ Σ ->
  envUpdate Σ φ ϰ LC Σ' φ' ϰ' ->
  d' ⊑↑ φ' ->
  wf_senv Σ' ->
  CtxOK Γ φ' Σ' ϰ' σ' ->
  Σ → Σ' ∋ d ⊕ d' ->
  has_type Γ φ' Σ' t' T (d ⋓ d') ->
  wf_store σ' ->
  wf_step t' ->
  preserve Γ Σ ϰ φ LC t' T d σ'.
Proof. intros. eapply Preserve; eassumption. Qed.

Lemma value_dec : forall t:tm, sumbool (value t) (~ value t).
Proof.
  intros t. destruct t.
  - left. apply value_ttabs.
  - right. intros H. inversion H.
  - left. apply value_cst.
  - right. intros H. inversion H.
  - left. apply value_abs.
  - right. intros H. inversion H.
  - left. apply value_loc.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
  - right. intros H. inversion H.
Qed.

Lemma type_safety_from_preservation :
  (forall (Σ:senv) ϰ t T d φ σ t' σ',
    has_type [] φ Σ t T d -> wf_senv Σ -> wf_step t ->
    CtxOK [] φ Σ ϰ σ -> wf_store σ ->
    step t σ t' σ' ->
    preserve [] Σ ϰ φ (local_locs t) t' T d σ') ->
  forall {Σ ϰ t T d φ},
    has_type [] φ Σ t T d -> wf_senv Σ -> wf_step t ->
    value t \/
    (forall σ, CtxOK [] φ Σ ϰ σ -> wf_store σ ->
      exists t' σ',
        step t σ t' σ' /\ preserve [] Σ ϰ φ (local_locs t) t' T d σ').
Proof.
  intros Hpres Σ ϰ t T d φ H Hwf Hws.
  destruct (value_dec t) as [Hv|Hnv].
  - left. exact Hv.
  - right. intros σ Hctx Hstore.
    destruct (progress_ctx Σ ϰ t T d φ H Hwf Hws σ Hctx Hstore) as [Hv|Hstep].
    + exfalso. apply Hnv. exact Hv.
    + destruct Hstep as (t' & σ' & Hs).
      exists t', σ'. split; [exact Hs|eapply Hpres; eassumption].
Qed.

Lemma has_type_value_no_step : forall Γ φ (Σ:senv) t T d σ t' σ',
  has_type Γ φ Σ t T d -> value t -> step t σ t' σ' -> False.
Proof. intros. eapply value_no_step; eassumption. Qed.

Lemma qstp_marker_trans : forall Γ (Σ:senv) b T x dnew dold,
  indexr x Γ = Some (bind_tm, b, T, dnew) ->
  closed_ty 0 x (‖Σ‖) T ->
  closed_Qual 0 x (‖Σ‖) (Q_lift dnew) ->
  ♦∉ dnew ->
  qstp Γ Σ dnew dold ->
  qstp Γ Σ ($!x) dold.
Proof.
  intros. eapply qs_trans; [eapply qs_qvar; eassumption|exact H3].
Qed.

Lemma qstp_marker_trans_ty : forall Γ (Σ:senv) b T x dnew dold,
  indexr x Γ = Some (bind_ty, b, T, dnew) ->
  closed_ty 0 x (‖Σ‖) T ->
  closed_Qual 0 x (‖Σ‖) (Q_lift dnew) ->
  ♦∉ dnew ->
  qstp Γ Σ dnew dold ->
  qstp Γ Σ ($!x) dold.
Proof.
  intros. eapply qs_trans; [eapply qs_qvar_ty; eassumption|exact H3].
Qed.

Lemma envUpdate_cases : forall (Σ Σ':senv) φ ϰ LC φ' ϰ',
  envUpdate Σ φ ϰ LC Σ' φ' ϰ' ->
  (Σ' ⊇₂ Σ /\ ‖Σ'‖ = ‖Σ‖ /\ φ' = φ /\ ϰ' = ϰ) \/
  (exists T q, kill_sep ϰ q /\ Σ' = [(T,q)] :: Σ /\
     φ' = (φ ⊔ &!(‖Σ‖)) /\ ϰ' = ϰ) \/
  (exists l, l < ‖Σ‖ /\ l ∈ₗ LC /\ Σ' = Σ /\
     φ' = q_remove Σ l φ /\ ϰ' = (ϰ ⊔ &!l)).
Proof.
  intros Σ Σ' φ ϰ LC φ' ϰ' H. destruct H.
  - left. repeat split; eauto.
  - right. left. eexists T. eexists q. split; [exact H|split; [reflexivity|split; [reflexivity|reflexivity]]].
  - right. right. eexists. repeat split; try reflexivity; assumption.
Qed.

Lemma disjointq_cases : forall (Σ Σ':senv) q q',
  Σ → Σ' ∋ q ⊕ q' ->
  q' = q_empty \/
  exists T q0, closed_ty 0 0 (‖Σ‖) T /\ closed_Qual 0 0 (‖Σ‖) (Q_lift q0) /\
    ♦∉ q0 /\ Σ' = [(T,q0)] :: Σ /\ q' = &!(‖Σ‖).
Proof.
  intros Σ Σ' q q' H. destruct H.
  - left. reflexivity.
  - right. eexists T. eexists q. split; [exact H|split; [exact H0|split; [exact H1|split; [exact H2|reflexivity]]]].
Qed.

Lemma CtxOK_empty : CtxOK [] q_empty [] {♦} [].
Proof.
  unfold CtxOK. split.
  - apply Subq_refl.
  - split.
    + reflexivity.
    + split.
      * apply q_empty_subq.
      * split.
        -- apply closed_Qual_diamond.
        -- split.
           ++ apply qand_subq_r.
           ++ intros l o cty T q. split.
              ** intros Hmem. unfold qmem, N_lift in Hmem.
                 change (qlocs {♦} l = true) in Hmem. simpl in Hmem. discriminate Hmem.
              ** intros _ _ Hl. inversion Hl.
Qed.

Lemma wf_senv_empty : wf_senv [].
Proof. intros l c H. inversion H. Qed.

Lemma wf_store_empty : wf_store [].
Proof. intros l o v H. inversion H. Qed.

Lemma progress_or_value : forall {Σ ϰ t T d φ},
  has_type [] φ Σ t T d -> wf_senv Σ -> wf_step t ->
  value t \/
  (forall σ, CtxOK [] φ Σ ϰ σ -> wf_store σ ->
    exists t' σ', step t σ t' σ').
Proof.
  intros Σ ϰ t T d φ H Hwf Hws.
  destruct (value_dec t) as [Hv|Hnv].
  - left. exact Hv.
  - right. intros σ Hctx Hstore.
    destruct (progress_ctx Σ ϰ t T d φ H Hwf Hws σ Hctx Hstore) as [Hv|Hstep].
    + exfalso. apply Hnv. exact Hv.
    + exact Hstep.
Qed.

Lemma qqplus_empty_r : forall d, qqplus d q_empty = d.
Proof.
  intros d. unfold qqplus. destruct (qfresh d); [rewrite qor_empty_r|]; reflexivity.
Qed.

Lemma qqplus_empty_l : forall d, qqplus q_empty d = q_empty.
Proof. intros d. unfold qqplus. simpl. reflexivity. Qed.

Lemma disjointq_bot : forall (Σ Σ':senv) q, Σ → Σ' ∋ q ⊕ q_empty.
Proof. intros. apply disj_bot. Qed.

Lemma preserve_refl : forall Γ (Σ:senv) ϰ φ LC t T d σ,
  has_type Γ φ Σ t T d -> wf_senv Σ -> CtxOK Γ φ Σ ϰ σ ->
  wf_store σ -> wf_step t ->
  preserve Γ Σ ϰ φ LC t T d σ.
Proof.
  intros Γ Σ ϰ φ LC t T d σ Hty Hwf Hctx Hstore Hws.
  eapply preserve_intro with (Σ':=Σ) (d':=q_empty) (φ':=φ) (ϰ':=ϰ).
  - apply extends_2D_refl.
  - apply envUpdate_refl.
  - apply q_empty_subq.
  - exact Hwf.
  - exact Hctx.
  - apply disjointq_bot.
  - rewrite qqplus_empty_r. exact Hty.
  - exact Hstore.
  - exact Hws.
Qed.

Lemma CtxLiveLen_live : forall (φ:qual) (Σ:senv) (σ:store),
  CtxLiveLen φ Σ σ -> CtxLive φ Σ σ.
Proof. intros. apply (proj1 H). Qed.

Lemma CtxLiveLen_length : forall (φ:qual) (Σ:senv) (σ:store),
  CtxLiveLen φ Σ σ -> ‖σ‖ = ‖Σ‖.
Proof. intros. apply (proj2 H). Qed.

Lemma CtxOK_length_sym : forall Γ φ (Σ:senv) ϰ σ,
  CtxOK Γ φ Σ ϰ σ -> ‖Σ‖ = ‖σ‖.
Proof. intros. symmetry. eapply CtxOK_length; exact H. Qed.

Lemma vtp_tunit_has_type : forall (Σ:senv) ϰ φ d,
  vtp Σ ϰ φ tunit TUnit d ->
  d ⊑↑ (qor φ {♦}) ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift φ) ->
  has_type [] φ Σ tunit TUnit d.
Proof.
  intros Σ ϰ φ d Hv Hsub Hclphi. inversion Hv; subst.
  eapply t_sub with (T1:=TUnit) (d1:=q_empty).
  - eapply t_base. exact Hclphi.
  - eapply s_base. eapply qs_sq; [apply q_empty_subq|exact H].
  - exact Hsub.
  - simpl. apply kill_sep_empty_l.
Qed.

Lemma subq_amp_mem : forall (φ:qual) l,
  l ∈ₗ φ -> &!l ⊑↑ φ.
Proof.
  intros φ l Hmem. unfold Subq. split.
  - intros Hf. unfold qfresh, Q_lift in Hf. simpl in Hf. exfalso. exact Hf.
  - split.
    + unfold N_sub. intros x Hx. unfold N_lift, qfvs, n_empty, Q_lift in Hx. simpl in Hx. discriminate Hx.
    + split.
      * unfold N_sub. intros x Hx. unfold N_lift, qbvs, n_empty, Q_lift in Hx. simpl in Hx. discriminate Hx.
      * unfold N_sub. intros x Hx. unfold N_lift, qlocs, n_one, Q_lift in Hx. simpl in Hx.
        apply Nat.eqb_eq in Hx. subst x. unfold qmem, N_lift in Hmem. exact Hmem.
Qed.

Lemma vtp_loc_has_type : forall (Σ:senv) ϰ φ l o q U d,
  vtp Σ ϰ φ &(l,o) (TRef q U) d ->
  d ⊑↑ (qor φ {♦}) ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift φ) ->
  has_type [] φ Σ &(l,o) (TRef q U) d.
Proof.
  intros Σ ϰ φ l o q U d Hv Hsub Hclphi. inversion Hv; subst.
  eapply t_sub with (T1:=TRef q1 T) (d1:=&!l).
  - eapply t_loc.
    + exact Hclphi.
    + exact H8.
    + exact H4.
    + exact H5.
    + eapply subq_amp_mem; exact H7.
    + exact H15.
  - eapply s_ref.
    + exact H11.
    + exact H9.
    + exact H10.
    + exact H16.
    + exact H18.
  - exact Hsub.
  - simpl. apply kill_sep_empty_l.
Qed.

Lemma vtp_abs_has_type : forall (Σ:senv) ϰ φ t d1 d2 T1 T2 df2,
  vtp Σ ϰ φ (tabs t) (TFun d1 d2 T1 T2) df2 ->
  df2 ⊑↑ φ ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift φ) ->
  has_type [] φ Σ (tabs t) (TFun d1 d2 T1 T2) df2.
Proof.
  intros Σ ϰ φ t d1 d2 T1 T2 df2 Hv Hsub Hclphi. inversion Hv; subst.
  assert (Hdf12 : df1 ⊑↑ df2) by (eapply qstp_nil_subq; [reflexivity|exact H10]).
  assert (Hdf1 : df1 ⊑↑ φ) by (eapply Subq_trans; eassumption).
  assert (Hkill1 : kill_sep (local_locs t) df1)
    by (eapply kill_sep_subq_l; [exact H19|exact Hdf12]).
  eapply t_sub with (T1:=TFun d0 d3 T0 T3) (d1:=df1).
  - eapply t_abs.
    + exact H4.
    + exact H7.
    + exact Hclphi.
    + exact H15.
    + exact Hdf1.
    + exact H17.
    + exact Hkill1.
    + exact H8.
  - eapply s_fun.
    + exact H7.
    + exact H6.
    + exact H10.
    + exact H9.
    + exact H14.
  - eapply Subq_trans; [exact Hsub|apply qor_subq_l].
  - simpl. exact H19.
Qed.

Lemma vtp_tabs_has_type : forall (Σ:senv) ϰ φ t d1 d2 T1 T2 df2,
  vtp Σ ϰ φ (ttabs t) (TAll d1 d2 T1 T2) df2 ->
  df2 ⊑↑ φ ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift φ) ->
  has_type [] φ Σ (ttabs t) (TAll d1 d2 T1 T2) df2.
Proof.
  intros Σ ϰ φ t d1 d2 T1 T2 df2 Hv Hsub Hclphi. inversion Hv; subst.
  assert (Hdf12 : df1 ⊑↑ df2) by (eapply qstp_nil_subq; [reflexivity|exact H9]).
  assert (Hdf1 : df1 ⊑↑ φ) by (eapply Subq_trans; eassumption).
  assert (Hkill1 : kill_sep (local_locs t) df1)
    by (eapply kill_sep_subq_l; [exact H18|exact Hdf12]).
  eapply t_sub with (T1:=TAll d0 d3 T0 T3) (d1:=df1).
  - eapply t_tabs.
    + exact H4.
    + exact H6.
    + exact Hclphi.
    + exact H14.
    + exact Hdf1.
    + exact H16.
    + exact Hkill1.
    + exact H7.
  - eapply s_all.
    + exact H6.
    + exact H5.
    + exact H9.
    + exact H8.
    + exact H13.
  - eapply Subq_trans; [exact Hsub|apply qor_subq_l].
  - simpl. exact H18.
Qed.

Lemma vtp_value : forall (Σ:senv) ϰ φ v T d,
  vtp Σ ϰ φ v T d -> value v.
Proof.
  intros. induction H.
  - apply value_ttabs.
  - apply value_cst.
  - apply value_loc.
  - apply value_abs.
  - assumption.
Qed.

Lemma vtp_kill_local : forall (Σ:senv) ϰ φ v T d,
  vtp Σ ϰ φ v T d -> kill_sep (local_locs v) d.
Proof.
  intros. induction H.
  - simpl. exact H9.
  - simpl. apply kill_sep_empty_l.
  - simpl. apply kill_sep_empty_l.
  - simpl. exact H10.
  - assumption.
Qed.

Lemma vtp_has_type : forall (Σ:senv) ϰ φ v T d,
  vtp Σ ϰ φ v T d ->
  d ⊑↑ φ ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift φ) ->
  has_type [] φ Σ v T d.
Proof.
  intros Σ ϰ φ v T d Hv. pose proof Hv as Hv0. induction Hv; intros Hsub Hclphi.
  - eapply vtp_tabs_has_type; [exact Hv0|exact Hsub|exact Hclphi].
  - eapply vtp_tunit_has_type; [exact Hv0| |exact Hclphi].
    eapply Subq_trans; [exact Hsub|apply qor_subq_l].
  - eapply vtp_loc_has_type; [exact Hv0| |exact Hclphi].
    eapply Subq_trans; [exact Hsub|apply qor_subq_l].
  - eapply vtp_abs_has_type; [exact Hv0|exact Hsub|exact Hclphi].
  - eapply t_sub with (T1:=T) (d1:=d).
    + apply IHHv; [exact Hv|exact Hsub|exact Hclphi].
    + eapply stp_top_refl.
      * destruct (has_type_value_closed Σ φ t T d (IHHv Hv Hsub Hclphi) (vtp_value Σ ϰ φ t T d Hv)) as [Hct _].
        exact Hct.
      * destruct (has_type_value_closed Σ φ t T d (IHHv Hv Hsub Hclphi) (vtp_value Σ ϰ φ t T d Hv)) as [_ Hcq].
        exact Hcq.
    + eapply Subq_trans; [exact Hsub|apply qor_subq_l].
    + eapply vtp_kill_local. exact Hv.
Qed.

Lemma has_type_loc_data_full : forall Γ φ (Σ:senv) l o U d,
  has_type Γ φ Σ &(l,o) U d ->
  U = TTop \/
  (exists d1 T cty T0 q0,
    U = TRef d1 T /\
    indexr l Σ = Some cty /\ indexr o cty = Some (T0,q0) /\
    qstp Γ Σ q0 d1 /\ qstp Γ Σ d1 q0 /\
    stp Γ Σ T0 ∅ T ∅ /\ stp Γ Σ T ∅ T0 ∅).
Proof.
  intros Γ φ Σ l o U d H. remember &(l,o) as v eqn:Ev in H.
  induction H; try discriminate; subst.
  - injection Ev as Hl Ho. subst l0 o0.
    destruct (sindexr_Some_decomp Σ l o (T,q) H0) as (cty & HlΣ & HoΣ).
    right. exists q, T, cty, T, q. split; [reflexivity|split; [exact HlΣ|split; [exact HoΣ|split]]].
    + eapply qstp_refl. eapply closed_Qual_mono_f; [exact H2|lia].
    + split.
      * eapply qstp_refl. eapply closed_Qual_mono_f; [exact H2|lia].
      * split.
        -- eapply stp_refl_closed; [apply Nat.le_refl|eapply closed_ty_weaken; [exact H1|lia|lia]|apply closed_Qual_empty].
        -- eapply stp_refl_closed; [apply Nat.le_refl|eapply closed_ty_weaken; [exact H1|lia|lia]|apply closed_Qual_empty].
  - destruct (IHhas_type eq_refl) as [E|(dsrc & Tsrc & cty & T0 & q0 & E & HlΣ & HoΣ & Hq01 & Hq10 & Hst01 & Hst10)].
    + subst T1. left. eapply stp_from_TTop; exact H0.
    + subst T1.
      destruct (stp_ref_ref_quals Γ Σ (TRef dsrc Tsrc) d1 T2 d2 H0 dsrc Tsrc eq_refl)
        as [E2|(q' & U' & E2 & Hqq' & Hq'q & Hs1 & Hs2)].
      * left. exact E2.
      * right. subst T2. exists q', U', cty, T0, q0. split; [reflexivity|split; [exact HlΣ|split; [exact HoΣ|split]]].
        -- eapply qstp_trans; [exact Hq01|exact Hqq'].
        -- split.
           ++ eapply qstp_trans; [exact Hq'q|exact Hq10].
           ++ split.
              ** eapply stp_trans; [exact Hst01|exact Hs1].
              ** eapply stp_trans; [exact Hs2|exact Hst10].
Qed.

Lemma has_type_loc_ref_data : forall Γ φ (Σ:senv) l o d1 T d,
  has_type Γ φ Σ &(l,o) (TRef d1 T) d ->
  exists cty T0 q0,
    indexr l Σ = Some cty /\ indexr o cty = Some (T0,q0) /\
    qstp Γ Σ q0 d1 /\ qstp Γ Σ d1 q0 /\
    stp Γ Σ T0 ∅ T ∅ /\ stp Γ Σ T ∅ T0 ∅.
Proof.
  intros Γ φ Σ l o d1 T d H.
  destruct (has_type_loc_data_full Γ φ Σ l o (TRef d1 T) d H) as [E|(d1' & T' & cty & T0 & q0 & E & HlΣ & HoΣ & Hq01 & Hq10 & Hst01 & Hst10)].
  - discriminate E.
  - injection E as Hd HT. subst d1' T'. exists cty, T0, q0. auto 10.
Qed.

Lemma sindexr'_from_indexr : forall {X} (σ:list (option (list X))) l o c v,
  indexr l σ = Some (Some c) -> indexr o c = Some v ->
  sindexr' l o σ = Some v.
Proof.
  intros X σ l o c v Hl Ho. rewrite sindexr'_lookup. rewrite Hl. simpl. exact Ho.
Qed.

Lemma subq_lift : forall (a b:qual), a ⊑ b -> a ⊑↑ b.
Proof.
  intros a b [Hf [H1 [H2 H3]]]. unfold Subq. split.
  - intros Ha. change (Is_true (qfresh a)) in Ha. apply Is_true_eq_true in Ha.
    assert (Hf' : qfresh a = true -> qfresh b = true).
    { apply (proj1 (Is_true_implb_iff (qfresh a) (qfresh b))). exact Hf. }
    pose proof (Hf' Ha) as Hfb. apply Is_true_eq_left. exact Hfb.
  - split.
    + unfold N_sub, n_sub in *. intros x Hx. apply H1. exact Hx.
    + split.
      * unfold N_sub, n_sub in *. intros x Hx. apply H2. exact Hx.
      * unfold N_sub, n_sub in *. intros x Hx. apply H3. exact Hx.
Qed.

Lemma subq_unlift : forall (a b:qual), a ⊑↑ b -> a ⊑ b.
Proof.
  intros a b [Hf [H1 [H2 H3]]]. unfold subq. split.
  - apply (proj2 (Is_true_implb_iff (qfresh a) (qfresh b))). intros Ha.
    pose proof (Hf (Is_true_eq_left (qfresh a) Ha)) as Hb.
    exact (Is_true_eq_true (qfresh b) Hb).
  - split.
    + unfold n_sub, N_sub in *. intros x Hx. apply H1. exact Hx.
    + split.
      * unfold n_sub, N_sub in *. intros x Hx. apply H2. exact Hx.
      * unfold n_sub, N_sub in *. intros x Hx. apply H3. exact Hx.
Qed.

Lemma preserve_deref_direct : forall (Σ:senv) ϰ φ l o d1 T d σ,
  has_type [] φ Σ &(l,o) (TRef d1 T) d ->
  d1 ⊑↑ φ ->
  wf_senv Σ ->
  CtxOK [] φ Σ ϰ σ ->
  wf_store σ ->
  exists v, step (! &(l,o)) σ v σ /\
    preserve [] Σ ϰ φ (local_locs &(l,o)) v T d1 σ.
Proof.
  intros Σ ϰ φ l o d1 T d σ Hloc Hd1phi Hwf Hctx Hstore.
  assert (Hphi : φ ⊑↑ qdom Σ) by (eapply CtxOK_phi; exact Hctx).
  assert (Hclphi : closed_Qual 0 0 (‖Σ‖) (Q_lift φ))
    by (eapply closed_qual_of_subq_qdom with (b:=0) (f:=0); exact Hphi).
  assert (Hcld1 : closed_Qual 0 0 (‖Σ‖) (Q_lift d1)).
  { eapply closed_Qual_of_subq_or_diamond_f with (b:=0) (f:=0) (φ:=φ);
      [exact Hclphi|eapply Subq_trans; [exact Hd1phi|apply qor_subq_l]]. }
  destruct (has_type_loc_ref_data [] φ Σ l o d1 T d Hloc)
    as (cty & T0 & q0 & HlΣ & Ho & Hq01 & Hq10 & Hst01 & Hst10).
  assert (Hq0phi : q0 ⊑↑ φ).
  { apply subq_lift. eapply subq_trans with (b:=d1).
    - apply subq_unlift. eapply qstp_nil_subq; [reflexivity|exact Hq01].
    - apply subq_unlift. exact Hd1phi. }
  assert (Hlmem : l ∈ₗ φ) by (eapply has_type_loc_mem; exact Hloc).
  destruct (CtxOK_lookup_phi [] φ Σ ϰ σ l o cty T0 q0 Hctx Hlmem HlΣ Ho)
    as (ctm & v & Hlσ & Hvo & Hval & Hvtpcond).
  assert (Hvtp : vtp Σ ϰ φ v T0 q0) by (apply Hvtpcond; exact Hq0phi).
  assert (Hsi : sindexr' l o σ = Some v)
    by (eapply sindexr'_from_indexr; eassumption).
  destruct (Hstore l o v Hsi) as [Hwfv _].
  assert (Hlocals : local_locs v = q_empty) by (eapply value_local_locs; eassumption).
  assert (Hvtp1 : vtp Σ ϰ φ v T0 d1).
  { eapply vtp_qstp_retype with (d:=q0) (d':=d1).
    - exact Hvtp.
    - exact Hq01.
    - eapply Subq_trans; [exact Hd1phi|apply qor_subq_l].
    - exact Hcld1.
    - eapply CtxOK_kill; exact Hctx.
    - exact Hlocals. }
  assert (Hty0 : has_type [] φ Σ v T0 d1) by (eapply vtp_has_type; eassumption).
  assert (Hstpuni : stp [] Σ T0 d1 T d1).
  { eapply stp_uniform; [exact Hst01|exact Hcld1]. }
  assert (Htyv : has_type [] φ Σ v T d1).
  { eapply t_sub with (T1:=T0) (d1:=d1).
    - exact Hty0.
    - exact Hstpuni.
    - eapply Subq_trans; [exact Hd1phi|apply qor_subq_l].
    - rewrite Hlocals. apply kill_sep_empty_l. }
  exists v. split.
  - eapply step_deref; eassumption.
  - eapply preserve_intro with (Σ':=Σ) (d':=q_empty) (φ':=φ) (ϰ':=ϰ).
    + apply extends_2D_refl.
    + apply envUpdate_refl.
    + apply q_empty_subq.
    + exact Hwf.
    + exact Hctx.
    + apply disjointq_bot.
    + rewrite qqplus_empty_r. exact Htyv.
    + exact Hstore.
    + exact Hwfv.
Qed.

Lemma kill_sep_amp_locs_false : forall (d:qual) l,
  kill_sep (&!l) d -> qlocs d l = false.
Proof.
  intros d l H. pose proof (subq_locs_false (qand d (&!l)) {♦} l H) as Hf.
  unfold qand, qlocs, n_and, n_one in Hf. simpl in Hf.
  specialize (Hf eq_refl) as Hf2. rewrite Nat.eqb_refl in Hf2. simpl in Hf2.
  rewrite andb_true_r in Hf2. unfold qlocs. exact Hf2.
Qed.

Lemma qlocs_amp_neq : forall n x, x <> n -> qlocs (&!n) x = false.
Proof. intros. unfold qlocs, n_one. apply Nat.eqb_neq. auto. Qed.

Lemma q_remove'_locs_true : forall (Σ:senv) k q n x,
  qlocs q x = true -> x < n -> x <> k -> qlocs (q_remove' Σ k q n) x = true.
Proof.
  intros Σ k q n. induction n as [|n IH]; intros x Hx Hlt Hne.
  - lia.
  - cbn [q_remove'].
    change (qlocs (if qlocs q n && negb (n_one n k) then q_remove' Σ k q n ⊔ &! n else q_remove' Σ k q n) x = true).
    destruct (Nat.eq_dec x n) as [Exn|Hxn].
    + subst x. destruct (qlocs q n && negb (n_one n k)) eqn:E.
      * change (n_or (qlocs (q_remove' Σ k q n)) (n_one n) n = true).
        apply orb_true_iff. right. unfold n_one. rewrite Nat.eqb_refl. reflexivity.
      * apply andb_false_iff in E. destruct E as [Eq|En].
        -- rewrite Hx in Eq. discriminate Eq.
        -- unfold negb in En. apply negb_false_iff in En. unfold n_one in En.
           apply Nat.eqb_eq in En. exfalso. apply Hne. symmetry. exact En.
    + assert (Hxlt : x < n) by lia.
      destruct (qlocs q n && negb (n_one n k)) eqn:E.
      * change (n_or (qlocs (q_remove' Σ k q n)) (n_one n) x = true).
        apply orb_true_iff. left. apply IH; [exact Hx|exact Hxlt|exact Hne].
      * apply IH; [exact Hx|exact Hxlt|exact Hne].
Qed.

Lemma q_remove_locs_true : forall (Σ:senv) k q x,
  qlocs q x = true -> x < ‖Σ‖ -> x <> k -> qlocs (q_remove Σ k q) x = true.
Proof.
  intros Σ k q x Hx Hlt Hne. unfold q_remove.
  change (n_or (qlocs (q_remove' Σ k q (‖Σ‖))) (qlocs ((qfresh q, qfvs q, qbvs q, n_empty):qual)) x = true).
  apply orb_true_iff. left. eapply q_remove'_locs_true; eassumption.
Qed.

Lemma qlocs_qdom_lt : forall (Σ:senv) x,
  qlocs (qdom Σ) x = true -> x < ‖Σ‖.
Proof. intros. unfold qlocs, qdom, n_dom in H. apply Nat.ltb_lt. exact H. Qed.

Lemma subq_q_remove_or_diamond : forall (Σ:senv) l (d φ:qual),
  l < ‖Σ‖ ->
  φ ⊑↑ qdom Σ ->
  kill_sep (&!l) d ->
  d ⊑↑ (qor φ {♦}) ->
  d ⊑↑ (qor (q_remove Σ l φ) {♦}).
Proof.
  intros Σ l d φ Hlt Hphi Hkill Hsub.
  destruct Hsub as [Hf [H1 [H2 H3]]].
  destruct Hphi as [_ [_ [_ Hphilocs]]].
  assert (Hdl : qlocs d l = false) by (eapply kill_sep_amp_locs_false; exact Hkill).
  unfold Subq. split.
  - intros Hd. cbn. rewrite orb_true_r. exact I.
  - split.
    + unfold N_sub in *. intros x Hx. unfold Q_lift, N_lift, qor, n_or.
      specialize (H1 x Hx). unfold Q_lift, N_lift, qor, n_or in H1.
      rewrite qfvs_q_remove.
      simpl in *. apply orb_true_iff in H1. destruct H1 as [H1|H1]; [|discriminate H1].
      apply orb_true_iff. left. exact H1.
    + split.
      * unfold N_sub in *. intros x Hx. unfold Q_lift, N_lift, qor, n_or.
        specialize (H2 x Hx). unfold Q_lift, N_lift, qor, n_or in H2.
        rewrite qbvs_q_remove.
        simpl in *. apply orb_true_iff in H2. destruct H2 as [H2|H2]; [|discriminate H2].
        apply orb_true_iff. left. exact H2.
      * unfold N_sub in *. intros x Hx. unfold Q_lift, N_lift, qor, n_or. unfold Q_lift, N_lift in Hx.
        specialize (H3 x Hx). unfold Q_lift, N_lift, qor, n_or in H3.
        simpl in *. apply orb_true_iff in H3. destruct H3 as [Hxφ|Hxd]; [|unfold n_empty in Hxd; discriminate Hxd].
        assert (Hxlt : x < ‖Σ‖) by (eapply qlocs_qdom_lt; eapply Hphilocs; exact Hxφ).
        assert (Hne : x <> l).
        { intro E. subst x. rewrite Hdl in Hx. discriminate Hx. }
        apply orb_true_iff. left. eapply q_remove_locs_true; eassumption.
Qed.

Lemma subq_q_remove_of_kill : forall (Σ:senv) l (d φ:qual),
  l < ‖Σ‖ ->
  φ ⊑↑ qdom Σ ->
  kill_sep (&!l) d ->
  d ⊑↑ φ ->
  d ⊑↑ q_remove Σ l φ.
Proof.
  intros Σ l d φ Hlt Hphi Hkill Hsub.
  destruct Hsub as [Hf [H1 [H2 H3]]].
  destruct Hphi as [_ [_ [_ Hphilocs]]].
  assert (Hdl : qlocs d l = false) by (eapply kill_sep_amp_locs_false; exact Hkill).
  unfold Subq. split.
  - intros Hd. unfold Q_lift. rewrite qfresh_q_remove.
    pose proof (Hf Hd) as Hp. apply Is_true_eq_true in Hp. apply Is_true_eq_left. exact Hp.
  - split.
    + unfold N_sub in *. intros x Hx.
      change (qfvs (q_remove Σ l φ) x = true). rewrite qfvs_q_remove.
      specialize (H1 x Hx). unfold Q_lift, N_lift in H1. exact H1.
    + split.
      * unfold N_sub in *. intros x Hx.
        change (qbvs (q_remove Σ l φ) x = true). rewrite qbvs_q_remove.
        specialize (H2 x Hx). unfold Q_lift, N_lift in H2. exact H2.
      * unfold N_sub in *. intros x Hx. unfold Q_lift, N_lift in Hx.
        change (qlocs (q_remove Σ l φ) x = true).
        assert (Hxphi : qlocs φ x = true).
        { specialize (H3 x Hx). unfold Q_lift, N_lift in H3. exact H3. }
        eapply q_remove_locs_true.
        -- exact Hxphi.
        -- eapply qlocs_qdom_lt; eapply Hphilocs; exact Hxphi.
        -- intro E. change (qlocs d x = true) in Hx. subst x. rewrite Hdl in Hx. discriminate Hx.
Qed.

Lemma kill_sep_amp_of_locs_false : forall (d:qual) l,
  qlocs d l = false -> kill_sep (&!l) d.
Proof.
  intros d l Hl. unfold kill_sep. rewrite qand_amp_empty; [apply q_empty_subq|exact Hl].
Qed.

Lemma closed_Qual_q_remove : forall b f L (Σ:senv) l (q:qual),
  closed_Qual b f L (Q_lift q) -> closed_Qual b f L (Q_lift (q_remove Σ l q)).
Proof.
  intros b f L Σ l q [Hf [Hb Hl]]. unfold closed_Qual. split; [|split].
  - unfold closed_Nats in *. intros x Hx. change (qfvs (q_remove Σ l q) x = true) in Hx.
    rewrite qfvs_q_remove in Hx. apply Hf. change (qfvs (Q_lift q) x).
    unfold Q_lift, N_lift. exact Hx.
  - unfold closed_Nats in *. intros x Hx. change (qbvs (q_remove Σ l q) x = true) in Hx.
    rewrite qbvs_q_remove in Hx. apply Hb. change (qbvs (Q_lift q) x).
    unfold Q_lift, N_lift. exact Hx.
  - unfold closed_Nats in *. intros x Hx. change (qlocs (q_remove Σ l q) x = true) in Hx.
    apply Hl. change (qlocs (Q_lift q) x). unfold Q_lift, N_lift.
    pose proof (q_remove_locs_sub Σ l q x) as Hsub. apply Hsub. exact Hx.
Qed.

Lemma kill_sep_amp_of_qstp_target_nil : forall (Σ:senv) d1 d2 l,
  qstp [] Σ d1 d2 -> kill_sep (&!l) d2 -> kill_sep (&!l) d1.
Proof.
  intros Σ d1 d2 l Hqs Hkill.
  apply kill_sep_amp_of_locs_false.
  pose proof (kill_sep_amp_locs_false d2 l Hkill) as Hld2.
  pose proof (qstp_nil_locs_mono [] Σ d1 d2 eq_refl Hqs) as Hsub.
  unfold n_sub in Hsub. simpl in Hsub.
  destruct (qlocs d1 l) eqn:E; [|reflexivity]. exfalso.
  specialize (Hsub l E). rewrite Hld2 in Hsub. discriminate Hsub.
Qed.

Lemma has_type_tunit_remove_phi : forall (Σ:senv) φ T d l,
  has_type [] φ Σ tunit T d ->
  l < ‖Σ‖ -> kill_sep (&!l) d -> φ ⊑↑ qdom Σ ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift φ) ->
  has_type [] (q_remove Σ l φ) Σ tunit T d.
Proof.
  intros Σ φ T d l H. remember (@nil (binding*bool*ty*qual)) as Γ eqn:EG in H.
  remember tunit as u eqn:Eu in H.
  induction H; try discriminate; subst; intros Hlt Hkill Hphi Hcl.
  - eapply t_base. eapply closed_Qual_q_remove. exact Hcl.
  - eapply t_sub with (T1:=T1) (d1:=d1).
    + eapply IHhas_type.
      * reflexivity.
      * reflexivity.
      * exact Hlt.
      * eapply kill_sep_amp_of_qstp_target_nil.
        -- eapply stp_qstp; exact H0.
        -- exact Hkill.
      * exact Hphi.
      * exact Hcl.
    + exact H0.
    + eapply subq_q_remove_or_diamond; eassumption.
    + exact H2.
Qed.

Lemma has_type_loc_remove_phi : forall (Σ:senv) φ l0 o T d l,
  has_type [] φ Σ &(l0,o) T d ->
  l < ‖Σ‖ -> kill_sep (&!l) d -> φ ⊑↑ qdom Σ ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift φ) ->
  has_type [] (q_remove Σ l φ) Σ &(l0,o) T d.
Proof.
  intros Σ φ l0 o T d l H. remember (@nil (binding*bool*ty*qual)) as Γ eqn:EG in H.
  remember &(l0,o) as v eqn:Ev in H.
  induction H; try discriminate; subst; intros Hlt Hkill Hphi Hcl.
  - injection Ev as El Eo. subst l1. subst o0.
    assert (Hcl' : closed_Qual 0 0 (‖Σ‖) (Q_lift (q_remove Σ l φ)))
      by (eapply closed_Qual_q_remove; exact Hcl).
    assert (Hmemφ : l0 ∈ₗ φ).
    { eapply qmem_loc_mono; [exact H3|apply mem_amp_self]. }
    assert (Hl0lt : l0 < ‖Σ‖) by (eapply sindexr_Some_lt; exact H0).
    assert (Hne : l0 <> l).
    { intro E. subst l0.
      assert (Hfl : qlocs (&!l) l = false) by (eapply kill_sep_amp_locs_false; exact Hkill).
      assert (Htrue : qlocs (&!l) l = true).
      { unfold qlocs, n_one. apply Nat.eqb_refl. }
      rewrite Htrue in Hfl. discriminate Hfl. }
    assert (Hmem' : l0 ∈ₗ (q_remove Σ l φ)).
    { unfold qmem, N_lift. apply q_remove_locs_true; [unfold qmem, N_lift in Hmemφ; exact Hmemφ|exact Hl0lt|exact Hne]. }
    eapply t_loc.
    + exact Hcl'.
    + exact H0.
    + exact H1.
    + exact H2.
    + eapply subq_amp_mem; exact Hmem'.
    + exact H4.
  - eapply t_sub with (T1:=T1) (d1:=d1).
    + eapply IHhas_type.
      * reflexivity. * reflexivity.
      * exact Hlt.
      * eapply kill_sep_amp_of_qstp_target_nil; [eapply stp_qstp; exact H0|exact Hkill].
      * exact Hphi. * exact Hcl.
    + exact H0.
    + eapply subq_q_remove_or_diamond; eassumption.
    + exact H2.
Qed.

Lemma has_type_abs_remove_phi : forall (Σ:senv) φ t T d l,
  has_type [] φ Σ (tabs t) T d ->
  l < ‖Σ‖ -> kill_sep (&!l) d -> φ ⊑↑ qdom Σ ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift φ) ->
  has_type [] (q_remove Σ l φ) Σ (tabs t) T d.
Proof.
  intros Σ φ t T d l H. remember (@nil (binding*bool*ty*qual)) as Γ eqn:EG in H.
  remember (tabs t) as v eqn:Ev in H.
  induction H; try discriminate; subst; intros Hlt Hkill Hphi Hcl.
  - injection Ev as Et. subst t0.
    assert (Hcl' : closed_Qual 0 0 (‖Σ‖) (Q_lift (q_remove Σ l φ)))
      by (eapply closed_Qual_q_remove; exact Hcl).
    assert (Hdf' : df ⊑↑ (q_remove Σ l φ))
      by (eapply subq_q_remove_of_kill; eassumption).
    eapply t_abs.
    + exact H.
    + exact H0.
    + exact Hcl'.
    + exact H2.
    + exact Hdf'.
    + exact H4.
    + exact H5.
    + exact H6.
  - eapply t_sub with (T1:=T1) (d1:=d1).
    + eapply IHhas_type.
      * reflexivity. * reflexivity. * exact Hlt.
      * eapply kill_sep_amp_of_qstp_target_nil; [eapply stp_qstp; exact H0|exact Hkill].
      * exact Hphi. * exact Hcl.
    + exact H0.
    + eapply subq_q_remove_or_diamond; eassumption.
    + exact H2.
Qed.

Lemma has_type_tabs_remove_phi : forall (Σ:senv) φ t T d l,
  has_type [] φ Σ (ttabs t) T d ->
  l < ‖Σ‖ -> kill_sep (&!l) d -> φ ⊑↑ qdom Σ ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift φ) ->
  has_type [] (q_remove Σ l φ) Σ (ttabs t) T d.
Proof.
  intros Σ φ t T d l H. remember (@nil (binding*bool*ty*qual)) as Γ eqn:EG in H.
  remember (ttabs t) as v eqn:Ev in H.
  induction H; try discriminate; subst; intros Hlt Hkill Hphi Hcl.
  - injection Ev as Et. subst t0.
    assert (Hcl' : closed_Qual 0 0 (‖Σ‖) (Q_lift (q_remove Σ l φ)))
      by (eapply closed_Qual_q_remove; exact Hcl).
    assert (Hdf' : df ⊑↑ (q_remove Σ l φ))
      by (eapply subq_q_remove_of_kill; eassumption).
    eapply t_tabs.
    + exact H.
    + exact H0.
    + exact Hcl'.
    + exact H2.
    + exact Hdf'.
    + exact H4.
    + exact H5.
    + exact H6.
  - eapply t_sub with (T1:=T1) (d1:=d1).
    + eapply IHhas_type.
      * reflexivity. * reflexivity. * exact Hlt.
      * eapply kill_sep_amp_of_qstp_target_nil; [eapply stp_qstp; exact H0|exact Hkill].
      * exact Hphi. * exact Hcl.
    + exact H0.
    + eapply subq_q_remove_or_diamond; eassumption.
    + exact H2.
Qed.

Lemma has_type_value_remove_phi : forall (Σ:senv) φ v T d l,
  has_type [] φ Σ v T d -> value v ->
  l < ‖Σ‖ -> kill_sep (&!l) d -> φ ⊑↑ qdom Σ ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift φ) ->
  has_type [] (q_remove Σ l φ) Σ v T d.
Proof.
  intros Σ φ v T d l H Hv Hlt Hkill Hphi Hcl. destruct Hv.
  - eapply has_type_tabs_remove_phi; eassumption.
  - eapply has_type_abs_remove_phi; eassumption.
  - eapply has_type_tunit_remove_phi; eassumption.
  - eapply has_type_loc_remove_phi; eassumption.
Qed.

Lemma preserve_twithc_direct : forall (Σ:senv) ϰ φ l t T d σ,
  l < ‖Σ‖ -> has_type [] φ Σ t T d ->
  closed_ty 0 0 (‖Σ‖) T -> closed_Qual 0 0 (‖Σ‖) (Q_lift d) ->
  kill_sep (&!l) d ->
  value t -> wf_step t ->
  wf_senv Σ -> CtxOK [] φ Σ ϰ σ -> wf_store σ ->
  step (twithc l t) σ t (update σ l None) /\
  preserve [] Σ ϰ φ (local_locs (twithc l t)) t T d (update σ l None).
Proof.
  intros Σ ϰ φ l t T d σ Hlen Hpre Hct Hcd Hkill Hval Hws Hwf Hctx Hstore.
  assert (Hphi : φ ⊑↑ qdom Σ) by (eapply CtxOK_phi; exact Hctx).
  assert (Hclphi : closed_Qual 0 0 (‖Σ‖) (Q_lift φ))
    by (eapply closed_qual_of_subq_qdom with (b:=0) (f:=0); exact Hphi).
  assert (HlLC : l ∈ₗ (local_locs (twithc l t))).
  { change (qlocs (&!l ⊔ local_locs t) l = true).
    unfold qor, qlocs, n_or. apply orb_true_iff. left. unfold qlocs, n_one.
    apply Nat.eqb_refl. }
  assert (Hty' : has_type [] (q_remove Σ l φ) Σ t T d).
  { eapply has_type_value_remove_phi; [exact Hpre|exact Hval|exact Hlen|exact Hkill|exact Hphi|exact Hclphi]. }
  split.
  - eapply step_twithc; exact Hval.
  - eapply preserve_intro with (d':=q_empty) (φ':=q_remove Σ l φ) (ϰ':=qor ϰ (&!l)).
    + apply extends_2D_refl.
    + eapply env_kill; [exact Hlen|exact HlLC].
    + apply q_empty_subq.
    + exact Hwf.
    + eapply CtxOK_twithc; eassumption.
    + apply disjointq_bot.
    + rewrite qqplus_empty_r. exact Hty'.
    + eapply wf_store_update_None; exact Hstore.
    + exact Hws.
Qed.

Lemma wf_store_lookup : forall (σ:store) l o v,
  wf_store σ -> sindexr' l o σ = Some v -> wf_step v /\ value v.
Proof. intros. eapply H. exact H0. Qed.

Lemma wf_store_lookup_value : forall (σ:store) l o v,
  wf_store σ -> sindexr' l o σ = Some v -> value v.
Proof. intros. eapply (proj2 (wf_store_lookup σ l o v H H0)). Qed.

Lemma wf_store_lookup_wf_step : forall (σ:store) l o v,
  wf_store σ -> sindexr' l o σ = Some v -> wf_step v.
Proof. intros. eapply (proj1 (wf_store_lookup σ l o v H H0)). Qed.

Lemma qand_subq_mono_r : forall a b c, a ⊑↑ b -> qand c a ⊑↑ qand c b.
Proof.
  intros a b c H. pose proof (qand_subq_mono_l a b c H) as H0.
  rewrite qand_comm. rewrite (qand_comm c b). exact H0.
Qed.

Lemma kill_sep_amp_of_mem : forall (ϰ d:qual) l,
  l ∈ₗ ϰ -> kill_sep ϰ d -> kill_sep (&!l) d.
Proof.
  intros ϰ d l Hmem Hkill. unfold kill_sep in *.
  eapply Subq_trans with (Q_lift (qand d ϰ)).
  - eapply qand_subq_mono_r. eapply subq_amp_mem; exact Hmem.
  - exact Hkill.
Qed.

Lemma closed_Qual_qqplus : forall b f L (d d':qual),
  closed_Qual b f L (Q_lift d) -> closed_Qual b f L (Q_lift d') ->
  closed_Qual b f L (Q_lift (qqplus d d')).
Proof.
  intros b f L d d' Hd Hd'. unfold qqplus. destruct (qfresh d); [apply closed_Qual_qor|]; assumption.
Qed.

Lemma envUpdate_len_le : forall (Σ Σ':senv) φ ϰ LC φ' ϰ',
  envUpdate Σ φ ϰ LC Σ' φ' ϰ' -> ‖Σ‖ <= ‖Σ'‖.
Proof.
  intros Σ Σ' φ ϰ LC φ' ϰ' H.
  destruct H as [Σ'' Hext Hlen|T q Hk|l Hlt Hmem].
  - rewrite Hlen. lia.
  - simpl. lia.
  - lia.
Qed.

Lemma kill_sep_qor : forall (ϰ a b:qual),
  kill_sep ϰ a -> kill_sep ϰ b -> kill_sep ϰ (qor a b).
Proof.
  intros ϰ a b Ha Hb. unfold kill_sep in *.
  rewrite qand_qor_distrib_l. eapply qor_subq_same; eassumption.
Qed.

Lemma kill_sep_qqplus : forall (ϰ d d':qual),
  kill_sep ϰ d -> kill_sep ϰ d' -> kill_sep ϰ (qqplus d d').
Proof.
  intros. unfold qqplus. destruct (qfresh d); [apply kill_sep_qor|]; assumption.
Qed.

Lemma kill_sep_amp_disjoint : forall (Σ Σ':senv) d d' l,
  Σ → Σ' ∋ d ⊕ d' -> l < ‖Σ‖ -> kill_sep (&!l) d'.
Proof.
  intros Σ Σ' d d' l Hdis Hlt.
  destruct (disjointq_cases Σ Σ' d d' Hdis) as [E0|(T & q0 & _ & _ & _ & E1 & Ed)].
  - subst d'. unfold kill_sep. rewrite qand_comm.
    eapply Subq_trans; [apply qand_subq_r|apply q_empty_subq].
  - subst d'. apply kill_sep_amp_of_locs_false. apply qlocs_amp_neq.
    intro E. rewrite E in Hlt. lia.
Qed.

Lemma kill_sep_amp_qqplus_disjoint : forall (Σ Σ':senv) d d' l,
  Σ → Σ' ∋ d ⊕ d' -> l < ‖Σ‖ -> kill_sep (&!l) d ->
  kill_sep (&!l) (qqplus d d').
Proof.
  intros. apply kill_sep_qqplus; [exact H1|eapply kill_sep_amp_disjoint; eassumption].
Qed.

Lemma envUpdate_mono_LC : forall (Σ Σ':senv) φ ϰ LC LC' φ' ϰ',
  envUpdate Σ φ ϰ LC Σ' φ' ϰ' -> LC ⊑↑ LC' ->
  envUpdate Σ φ ϰ LC' Σ' φ' ϰ'.
Proof.
  intros Σ Σ' φ ϰ LC LC' φ' ϰ' H Hsub.
  destruct H as [Σ'' Hext Hlen|T q Hk|l Hlt Hmem].
  - eapply env_phi; eassumption.
  - eapply env_fresh; exact Hk.
  - eapply env_kill; [exact Hlt|eapply qmem_loc_mono; eassumption].
Qed.

Lemma preserve_twithc_context : forall (Σ:senv) ϰ φ l t t' T d σ',
  preserve [] Σ ϰ φ (local_locs t) t' T d σ' ->
  l < ‖Σ‖ ->
  closed_ty 0 0 (‖Σ‖) T ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift d) ->
  kill_sep (&!l) d ->
  preserve [] Σ ϰ φ (local_locs (twithc l t)) (twithc l t') T d σ'.
Proof.
  intros Σ ϰ φ l t t' T d σ' Hp Hlt Hct Hcd Hkill.
  destruct Hp as [Σ' d' φ' ϰ' Hext Henv Hd' Hwf' Hctx' Hdisj Hty' Hstore' Hws'].
  assert (Hlenle : ‖Σ‖ <= ‖Σ'‖) by (eapply envUpdate_len_le; exact Henv).
  assert (Hlen' : l < ‖Σ'‖) by lia.
  assert (Hphi' : φ' ⊑↑ qdom Σ') by (eapply CtxOK_phi; exact Hctx').
  assert (Hclphi' : closed_Qual 0 0 (‖Σ'‖) (Q_lift φ'))
    by (eapply closed_qual_of_subq_qdom with (b:=0) (f:=0); exact Hphi').
  assert (Hcd' : closed_Qual 0 0 (‖Σ'‖) (Q_lift d'))
    by (eapply closed_Qual_of_subq_nil; eassumption).
  assert (HcdΣ' : closed_Qual 0 0 (‖Σ'‖) (Q_lift d))
    by (eapply closed_Qual_loc_weaken; [exact Hcd|exact Hlenle]).
  assert (HctΣ' : closed_ty 0 0 (‖Σ'‖) T)
    by (eapply closed_ty_loc_weaken; [exact Hct|exact Hlenle]).
  assert (Hcdcomb : closed_Qual 0 0 (‖Σ'‖) (Q_lift (qqplus d d')))
    by (eapply closed_Qual_qqplus; eassumption).
  assert (Hkill' : kill_sep (&!l) d')
    by (eapply kill_sep_amp_disjoint; eassumption).
  assert (Hkillcomb : kill_sep (&!l) (qqplus d d'))
    by (eapply kill_sep_qqplus; eassumption).
  eapply preserve_intro with (Σ':=Σ') (d':=d') (φ':=φ') (ϰ':=ϰ').
  - exact Hext.
  - eapply envUpdate_mono_LC; [exact Henv|].
    change (local_locs t ⊑↑ (qor (&!l) (local_locs t))). apply qor_subq_r.
  - exact Hd'.
  - exact Hwf'.
  - exact Hctx'.
  - exact Hdisj.
  - eapply t_withc; [exact Hlen'|exact Hty'|exact HctΣ'|exact Hcdcomb|exact Hkillcomb].
  - exact Hstore'.
  - simpl. exact Hws'.
Qed.

Lemma subq_qqplus_l : forall (d d':qual), d ⊑↑ qqplus d d'.
Proof.
  intros d d'. unfold qqplus. destruct (qfresh d); [apply qor_subq_l|apply Subq_refl].
Qed.

Lemma qqplus_fresh_true : forall (d d':qual),
  qfresh d = true -> qqplus d d' = qor d d'.
Proof. intros. unfold qqplus. rewrite H. reflexivity. Qed.

Lemma qqplus_fresh_false : forall (d d':qual),
  qfresh d = false -> qqplus d d' = d.
Proof. intros. unfold qqplus. rewrite H. reflexivity. Qed.

Lemma envUpdate_subq_of_kill : forall (Σ Σ':senv) φ φ' ϰ ϰ' LC d,
  envUpdate Σ φ ϰ LC Σ' φ' ϰ' ->
  φ ⊑↑ qdom Σ -> d ⊑↑ φ -> kill_sep LC d -> d ⊑↑ φ'.
Proof.
  intros Σ Σ' φ φ' ϰ ϰ' LC d Henv Hphi Hsub Hkill.
  destruct Henv as [Σ'' Hext Hlen|T q Hk|l Hlt Hmem].
  - exact Hsub.
  - eapply Subq_trans; [exact Hsub|apply qor_subq_l].
  - eapply subq_q_remove_of_kill; [exact Hlt|exact Hphi| |exact Hsub].
    eapply kill_sep_amp_of_mem; eassumption.
Qed.

Lemma disjointq_fresh_false : forall (Σ Σ':senv) q q',
  Σ → Σ' ∋ q ⊕ q' -> qfresh q' = false.
Proof.
  intros Σ Σ' q q' H. destruct (disjointq_cases Σ Σ' q q' H) as [E|(T & q0 & _ & _ & _ & _ & E)].
  - subst q'. reflexivity.
  - subst q'. reflexivity.
Qed.

Lemma not_fresh_false : forall (d:qual), ♦∉ d -> qfresh d = false.
Proof.
  intros d H. destruct (qfresh d) eqn:E; [exfalso; apply H; exact I|reflexivity].
Qed.

Lemma qqplus_of_not_fresh : forall (d d':qual),
  ♦∉ d -> qqplus d d' = d.
Proof. intros. apply qqplus_fresh_false. eapply not_fresh_false; exact H. Qed.

Lemma preserve_ref_context : forall (Σ:senv) ϰ φ t t' T d1 σ',
  preserve [] Σ ϰ φ (local_locs t) t' T d1 σ' ->
  closed_ty 0 0 (‖Σ‖) T -> ♦∉ d1 ->
  preserve [] Σ ϰ φ (local_locs (tref t)) (tref t') (TRef d1 T) {♦} σ'.
Proof.
  intros Σ ϰ φ t t' T d1 σ' Hp Hct Hnd.
  destruct Hp as [Σ' d' φ' ϰ' Hext Henv Hd' Hwf' Hctx' Hdisj Hty' Hstore' Hws'].
  assert (Hlenle : ‖Σ‖ <= ‖Σ'‖) by (eapply envUpdate_len_le; exact Henv).
  assert (Hct' : closed_ty 0 0 (‖Σ'‖) T)
    by (eapply closed_ty_loc_weaken; [exact Hct|exact Hlenle]).
  assert (Hty1 : has_type [] φ' Σ' t' T d1).
  { rewrite (qqplus_of_not_fresh d1 d' Hnd) in Hty'. exact Hty'. }
  eapply preserve_intro with (Σ':=Σ') (d':=q_empty) (φ':=φ') (ϰ':=ϰ').
  - exact Hext.
  - exact Henv.
  - apply q_empty_subq.
  - exact Hwf'.
  - exact Hctx'.
  - apply disjointq_bot.
  - rewrite qqplus_empty_r. eapply t_ref; [exact Hty1|exact Hct'|exact Hnd].
  - exact Hstore'.
  - simpl. exact Hws'.
Qed.

Lemma kill_sep_subq_first : forall (ϰ ϰ' d:qual),
  kill_sep ϰ d -> ϰ' ⊑↑ ϰ -> kill_sep ϰ' d.
Proof.
  intros. unfold kill_sep in *. eapply Subq_trans with (Q_lift (qand d ϰ)).
  - eapply qand_subq_mono_r. exact H0.
  - exact H.
Qed.

Lemma kill_sep_local_locs_tapp_l : forall t1 t2 d,
  kill_sep (local_locs (tapp t1 t2)) d -> kill_sep (local_locs t1) d.
Proof. intros. eapply kill_sep_subq_first; [exact H|apply qor_subq_l]. Qed.

Lemma kill_sep_local_locs_tapp_r : forall t1 t2 d,
  kill_sep (local_locs (tapp t1 t2)) d -> kill_sep (local_locs t2) d.
Proof. intros. eapply kill_sep_subq_first; [exact H|apply qor_subq_r]. Qed.

Lemma kill_sep_local_locs_trefat_l : forall t1 t2 d,
  kill_sep (local_locs (trefat t1 t2)) d -> kill_sep (local_locs t1) d.
Proof. intros. eapply kill_sep_subq_first; [exact H|apply qor_subq_l]. Qed.

Lemma kill_sep_local_locs_trefat_r : forall t1 t2 d,
  kill_sep (local_locs (trefat t1 t2)) d -> kill_sep (local_locs t2) d.
Proof. intros. eapply kill_sep_subq_first; [exact H|apply qor_subq_r]. Qed.

Lemma kill_sep_local_locs_tassign_l : forall t1 t2 d,
  kill_sep (local_locs (tassign t1 t2)) d -> kill_sep (local_locs t1) d.
Proof. intros. eapply kill_sep_subq_first; [exact H|apply qor_subq_l]. Qed.

Lemma kill_sep_local_locs_tassign_r : forall t1 t2 d,
  kill_sep (local_locs (tassign t1 t2)) d -> kill_sep (local_locs t2) d.
Proof. intros. eapply kill_sep_subq_first; [exact H|apply qor_subq_r]. Qed.

Lemma kill_sep_local_locs_twithr_l : forall t1 t2 d,
  kill_sep (local_locs (twithr t1 t2)) d -> kill_sep (local_locs t1) d.
Proof. intros. eapply kill_sep_subq_first; [exact H|apply qor_subq_l]. Qed.

Lemma kill_sep_local_locs_twithr_r : forall t1 t2 d,
  kill_sep (local_locs (twithr t1 t2)) d -> kill_sep (local_locs t2) d.
Proof. intros. eapply kill_sep_subq_first; [exact H|apply qor_subq_r]. Qed.

Lemma kill_sep_local_locs_twithc : forall l t d,
  kill_sep (local_locs (twithc l t)) d -> kill_sep (local_locs t) d.
Proof. intros. eapply kill_sep_subq_first; [exact H|apply qor_subq_r]. Qed.

Lemma kill_sep_of_subq_diamond : forall (ϰ d:qual),
  d ⊑↑ {♦} -> kill_sep ϰ d.
Proof.
  intros. unfold kill_sep. eapply Subq_trans; [apply qand_subq_l|exact H].
Qed.

Lemma kill_sep_amp_of_closed_ge : forall (d:qual) L l,
  closed_Qual 0 0 L (Q_lift d) -> L <= l -> kill_sep (&!l) d.
Proof.
  intros d L l Hcl Hle. apply kill_sep_amp_of_locs_false.
  destruct Hcl as [_ [_ Hlocs]]. unfold closed_Nats in Hlocs.
  destruct (qlocs d l) eqn:E; [|reflexivity]. exfalso. apply Hlocs in E. lia.
Qed.

Lemma local_locs_open_rec_sub : forall t k u,
  local_locs (open_rec_tm k u t) ⊑↑ (qor (local_locs t) (local_locs u)).
Proof.
  induction t; intros k u; cbn [open_rec_tm local_locs].
  - apply IHt.
  - apply IHt.
  - apply q_empty_subq.
  - (* tvar *) destruct v as [x|x]; cbn [local_locs].
    + apply q_empty_subq.
    + destruct (Nat.eqb k x) eqn:E; cbn [local_locs].
      * eapply Subq_trans; [|apply qor_subq_r]. apply Subq_refl.
      * apply q_empty_subq.
  - apply IHt.
  - eapply qor_subq_same.
    + eapply Subq_trans; [apply IHt1|apply qor_subq_mono; [apply qor_subq_l|apply Subq_refl]].
    + eapply Subq_trans; [apply IHt2|apply qor_subq_mono; [apply qor_subq_r|apply Subq_refl]].
  - apply q_empty_subq.
  - apply IHt.
  - apply IHt.
  - eapply qor_subq_same.
    + eapply Subq_trans; [apply IHt1|apply qor_subq_mono; [apply qor_subq_l|apply Subq_refl]].
    + eapply Subq_trans; [apply IHt2|apply qor_subq_mono; [apply qor_subq_r|apply Subq_refl]].
  - eapply qor_subq_same.
    + eapply Subq_trans; [apply IHt1|apply qor_subq_mono; [apply qor_subq_l|apply Subq_refl]].
    + eapply Subq_trans; [apply IHt2|apply qor_subq_mono; [apply qor_subq_r|apply Subq_refl]].
  - eapply qor_subq_same.
    + eapply Subq_trans; [apply IHt1|apply qor_subq_mono; [apply qor_subq_l|apply Subq_refl]].
    + eapply Subq_trans; [apply IHt2|apply qor_subq_mono; [apply qor_subq_r|apply Subq_refl]].
  - (* twithc *) eapply qor_subq_same.
    + eapply Subq_trans; [apply qor_subq_l|apply qor_subq_l].
    + eapply Subq_trans; [exact (IHt k u)|apply qor_subq_mono; [apply qor_subq_r|apply Subq_refl]].
Qed.

Lemma local_locs_open_tm_sub : forall t u v,
  local_locs (t <~ᵗ u; v) ⊑↑
  (qor (qor (local_locs t) (local_locs u)) (local_locs v)).
Proof.
  intros t u v. unfold open_tm.
  eapply Subq_trans with (Q_lift (qor (local_locs (open_rec_tm 0 u t)) (local_locs v))).
  - apply local_locs_open_rec_sub.
  - apply qor_subq_mono.
    + apply local_locs_open_rec_sub.
    + apply Subq_refl.
Qed.

Lemma kill_sep_local_locs_open : forall t u v d,
  kill_sep (qor (qor (local_locs t) (local_locs u)) (local_locs v)) d ->
  kill_sep (local_locs (t <~ᵗ u; v)) d.
Proof.
  intros. eapply kill_sep_subq_first; [exact H|apply local_locs_open_tm_sub].
Qed.

Lemma local_locs_beta_sub : forall t v,
  local_locs (t <~ᵗ (tabs t); v) ⊑↑ (qor (local_locs t) (local_locs v)).
Proof.
  intros t v.
  eapply Subq_trans with (Q_lift (qor (qor (local_locs t) (local_locs (tabs t))) (local_locs v))).
  - apply local_locs_open_tm_sub.
  - apply qor_subq_same.
    + apply qor_subq_same; [apply qor_subq_l|apply qor_subq_l].
    + apply qor_subq_r.
Qed.

Lemma ctxsub_nil : forall U0 U1 s0 s1,
  ctxsub [] U0 U1 s0 s1 = [].
Proof. intros. unfold ctxsub. reflexivity. Qed.

Lemma ctxsub_cons : forall e D U0 U1 s0 s1,
  ctxsub (e :: D) U0 U1 s0 s1 = csub U0 U1 s0 s1 e :: ctxsub D U0 U1 s0 s1.
Proof. intros. unfold ctxsub. reflexivity. Qed.

Lemma tsub_TUnit : forall U0 U1 s0 s1,
  tsub TUnit U0 U1 s0 s1 = TUnit.
Proof. intros. reflexivity. Qed.

Lemma tsub_TTop : forall U0 U1 s0 s1,
  tsub TTop U0 U1 s0 s1 = TTop.
Proof. intros. reflexivity. Qed.

Lemma tsub_varF_SS : forall j U0 U1 s0 s1,
  tsub (TVar (varF (S (S j)))) U0 U1 s0 s1 = TVar (varF j).
Proof. intros. reflexivity. Qed.

Lemma csub_binding : forall U0 U1 s0 s1 e,
  fst (fst (fst (csub U0 U1 s0 s1 e))) = fst (fst (fst e)).
Proof. intros. unfold csub. reflexivity. Qed.

Lemma csub_flag : forall U0 U1 s0 s1 e,
  snd (fst (fst (csub U0 U1 s0 s1 e))) = snd (fst (fst e)).
Proof. intros. unfold csub. reflexivity. Qed.

Lemma csub_ty : forall U0 U1 s0 s1 e,
  snd (fst (csub U0 U1 s0 s1 e)) = tsub (snd (fst e)) U0 U1 s0 s1.
Proof. intros. unfold csub. reflexivity. Qed.

Lemma csub_qual : forall U0 U1 s0 s1 e,
  snd (csub U0 U1 s0 s1 e) = qsub (snd e) s0 s1.
Proof. intros. unfold csub. reflexivity. Qed.

Lemma ctxsub_indexr_None : forall D U0 U1 s0 s1 x,
  indexr x D = None -> indexr x (ctxsub D U0 U1 s0 s1) = None.
Proof.
  intros D. induction D as [|e D IH]; intros U0 U1 s0 s1 x H; simpl in *.
  - reflexivity.
  - unfold ctxsub. simpl. rewrite map_length.
    destruct (Nat.eqb x (length D)) eqn:E.
    + discriminate H.
    + exact (IH U0 U1 s0 s1 x H).
Qed.

Lemma ctxsub_indexr_None_inv : forall D U0 U1 s0 s1 x,
  indexr x (ctxsub D U0 U1 s0 s1) = None -> indexr x D = None.
Proof.
  intros D. induction D as [|a D IH]; intros U0 U1 s0 s1 x H; simpl in *.
  - reflexivity.
  - unfold ctxsub in H. simpl in H. rewrite map_length in H.
    destruct (Nat.eqb x (length D)) eqn:E.
    + discriminate H.
    + exact (IH U0 U1 s0 s1 x H).
Qed.

Lemma ctxsub_indexr_None_iff : forall D U0 U1 s0 s1 x,
  indexr x (ctxsub D U0 U1 s0 s1) = None <-> indexr x D = None.
Proof.
  intros. split.
  - apply ctxsub_indexr_None_inv.
  - apply ctxsub_indexr_None.
Qed.

Lemma tsub_TRef : forall T d U0 U1 s0 s1,
  tsub (TRef d T) U0 U1 s0 s1 = TRef (qsub d s0 s1) (tsub T U0 U1 s0 s1).
Proof. intros. reflexivity. Qed.

Lemma tsub_TFun : forall d1 d2 T1 T2 U0 U1 s0 s1,
  tsub (TFun d1 d2 T1 T2) U0 U1 s0 s1 =
  TFun (qsub d1 s0 s1) (qsub d2 s0 s1) (tsub T1 U0 U1 s0 s1) (tsub T2 U0 U1 s0 s1).
Proof. intros. reflexivity. Qed.

Lemma tsub_TAll : forall d1 d2 T1 T2 U0 U1 s0 s1,
  tsub (TAll d1 d2 T1 T2) U0 U1 s0 s1 =
  TAll (qsub d1 s0 s1) (qsub d2 s0 s1) (tsub T1 U0 U1 s0 s1) (tsub T2 U0 U1 s0 s1).
Proof. intros. reflexivity. Qed.

Lemma qsub_q_empty : forall q0 q1, qsub q_empty q0 q1 = q_empty.
Proof.
  intros. apply qual_ext.
  - unfold qsub, q_empty, qfresh. simpl. reflexivity.
  - unfold qsub, q_empty, qfvs. simpl. apply functional_extensionality. intro x. reflexivity.
  - unfold qsub, q_empty, qbvs. simpl. reflexivity.
  - unfold qsub, q_empty, qlocs. simpl. apply functional_extensionality. intro x. reflexivity.
Qed.

Lemma qsub_diamond : forall q0 q1, qsub {♦} q0 q1 = {♦}.
Proof.
  intros. apply qual_ext.
  - unfold qsub, qfresh. simpl. reflexivity.
  - unfold qsub, qfvs. simpl. apply functional_extensionality. intro x. reflexivity.
  - unfold qsub, qbvs. simpl. reflexivity.
  - unfold qsub, qlocs. simpl. apply functional_extensionality. intro x. reflexivity.
Qed.

Lemma qsub_amp : forall l q0 q1, qsub (&!l) q0 q1 = &!l.
Proof.
  intros. apply qual_ext.
  - unfold qsub, qfresh. simpl. reflexivity.
  - unfold qsub, qfvs. simpl. apply functional_extensionality. intro x. reflexivity.
  - unfold qsub, qbvs. simpl. reflexivity.
  - unfold qsub, qlocs. simpl. apply functional_extensionality. intro x. simpl.
    rewrite orb_false_r, orb_false_r. reflexivity.
Qed.

Lemma tsub_varB : forall x U0 U1 s0 s1,
  tsub (TVar (varB x)) U0 U1 s0 s1 = TVar (varB x).
Proof. intros. reflexivity. Qed.

Lemma tsub_varF_zero : forall U0 U1 s0 s1,
  tsub (TVar (varF 0)) U0 U1 s0 s1 = U0.
Proof. intros. reflexivity. Qed.

Lemma tsub_varF_one : forall U0 U1 s0 s1,
  tsub (TVar (varF 1)) U0 U1 s0 s1 = U1.
Proof. intros. reflexivity. Qed.

Lemma qsub_marker_SS : forall x q0 q1,
  qsub ($!(S (S x))) q0 q1 = $!x.
Proof.
  intros. apply qual_ext.
  - unfold qsub, qfresh. simpl. reflexivity.
  - unfold qsub, qfvs. simpl. apply functional_extensionality. intro y.
    unfold n_one. destruct (Nat.eqb y x) eqn:E.
    + apply Nat.eqb_eq in E. subst y. reflexivity.
    + reflexivity.
  - unfold qsub, qbvs. simpl. reflexivity.
  - unfold qsub, qlocs. simpl. apply functional_extensionality. intro y. reflexivity.
Qed.

Lemma tsub_varF : forall i U0 U1 s0 s1,
  tsub (TVar (varF i)) U0 U1 s0 s1 =
  match i with 0 => U0 | 1 => U1 | S (S j) => TVar (varF j) end.
Proof. intros. reflexivity. Qed.

Lemma open_tm_tunit : forall u v, (tunit <~ᵗ u; v) = tunit.
Proof. intros. reflexivity. Qed.

Lemma open_tm_loc : forall u v l o, ((&(l,o)) <~ᵗ u; v) = &(l,o).
Proof. intros. reflexivity. Qed.

Lemma open_tm_tvar : forall u v x, ((tvar (varF x)) <~ᵗ u; v) = tvar (varF x).
Proof. intros. reflexivity. Qed.

Lemma ctxsub_indexr_Some_inv : forall D U0 U1 s0 s1 x e',
  indexr x (ctxsub D U0 U1 s0 s1) = Some e' ->
  exists e, indexr x D = Some e /\ e' = csub U0 U1 s0 s1 e.
Proof.
  intros D U0 U1 s0 s1 x e' H.
  destruct (indexr x D) as [e|] eqn:E.
  - exists e. split; [reflexivity|].
    pose proof (ctxsub_indexr D U0 U1 s0 s1 x e E) as Hc.
    rewrite Hc in H. injection H as He. symmetry. exact He.
  - exfalso. pose proof (ctxsub_indexr_None D U0 U1 s0 s1 x E) as Hn.
    rewrite Hn in H. discriminate H.
Qed.

Lemma ctxsub_indexr_head : forall e D U0 U1 s0 s1,
  indexr (‖D‖) (ctxsub (e :: D) U0 U1 s0 s1) = Some (csub U0 U1 s0 s1 e).
Proof.
  intros. unfold ctxsub. simpl. rewrite map_length. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma open_qual_empty : forall k (d:qual), open_qual k d q_empty = q_empty.
Proof. intros. unfold open_qual, qbvs, q_empty. simpl. reflexivity. Qed.

Lemma openq_empty : openq q_empty q_empty q_empty = q_empty.
Proof. unfold openq. rewrite (open_qual_empty 0 q_empty). rewrite (open_qual_empty 1 q_empty). reflexivity. Qed.

Lemma open_ty_TUnit : forall U du V dv,
  open_ty U du V dv TUnit = TUnit.
Proof. intros. reflexivity. Qed.

Lemma open_ty_TTop : forall U du V dv,
  open_ty U du V dv TTop = TTop.
Proof. intros. reflexivity. Qed.

Lemma open_qual_diamond : forall k (d:qual), open_qual k d {♦} = {♦}.
Proof. intros. unfold open_qual, qbvs. simpl. reflexivity. Qed.

Lemma local_locs_ttapp_sub : forall t,
  local_locs (t <~ᵗ (ttabs t); tunit) ⊑↑ local_locs t.
Proof.
  intros. eapply Subq_trans with (Q_lift (qor (qor (local_locs t) (local_locs t)) q_empty)).
  - exact (local_locs_open_tm_sub t (ttabs t) tunit).
  - apply qor_subq_same.
    + apply qor_subq_same; [apply Subq_refl|apply Subq_refl].
    + apply q_empty_subq.
Qed.

Lemma kill_sep_qor_l : forall (a b d:qual),
  kill_sep a d -> kill_sep b d -> kill_sep (qor a b) d.
Proof.
  intros a b d Ha Hb. unfold kill_sep in *.
  rewrite qand_comm. rewrite qand_qor_distrib_l.
  eapply qor_subq_same.
  - rewrite qand_comm. exact Ha.
  - rewrite qand_comm. exact Hb.
Qed.

Lemma local_locs_open_tunit_amp : forall t l,
  local_locs (t <~ᵗ tunit; (& l)) ⊑↑ local_locs t.
Proof.
  intros. eapply Subq_trans with (Q_lift (qor (qor (local_locs t) (local_locs tunit)) (local_locs ((& l))))).
  - apply local_locs_open_tm_sub.
  - apply qor_subq_same.
    + apply qor_subq_same; [apply Subq_refl|apply q_empty_subq].
    + apply q_empty_subq.
Qed.

Lemma kill_sep_local_locs_twithr_reduct : forall l t (d:qual) L,
  closed_Qual 0 0 L (Q_lift d) -> L <= l ->
  kill_sep (local_locs t) d ->
  kill_sep (local_locs (twithc l (t <~ᵗ tunit; (& l)))) d.
Proof.
  intros l t d L Hcl Hle Hkill.
  change (kill_sep (qor (&!l) (local_locs (t <~ᵗ tunit; (& l)))) d).
  eapply kill_sep_qor_l.
  - eapply kill_sep_amp_of_closed_ge; eassumption.
  - eapply kill_sep_subq_first; [exact Hkill|apply local_locs_open_tunit_amp].
Qed.

Lemma qand_qor_distrib_r : forall a b c,
  qand a (qor b c) = qor (qand a b) (qand a c).
Proof.
  intros. rewrite (qand_comm a (qor b c)). rewrite qand_qor_distrib_l.
  rewrite (qand_comm b a). rewrite (qand_comm c a). reflexivity.
Qed.

Lemma qand_idem : forall (q:qual), qand q q = q.
Proof.
  intros. apply qual_ext.
  - unfold qand, qfresh. apply andb_diag.
  - unfold qand, qfvs, n_and. apply functional_extensionality. intro x. apply andb_diag.
  - unfold qand, qbvs, n_and. apply functional_extensionality. intro x. apply andb_diag.
  - unfold qand, qlocs, n_and. apply functional_extensionality. intro x. apply andb_diag.
Qed.

Lemma qor_idem2 : forall (q:qual), qor q q = q.
Proof.
  intros. apply qual_ext.
  - unfold qor, qfresh. apply orb_diag.
  - unfold qor, qfvs, n_or. apply functional_extensionality. intro x. apply orb_diag.
  - unfold qor, qbvs, n_or. apply functional_extensionality. intro x. apply orb_diag.
  - unfold qor, qlocs, n_or. apply functional_extensionality. intro x. apply orb_diag.
Qed.

Lemma qand_assoc : forall a b c,
  qand (qand a b) c = qand a (qand b c).
Proof.
  intros. apply qual_ext.
  - unfold qand, qfresh. simpl. symmetry. apply andb_assoc.
  - unfold qand, qfvs, n_and. simpl. apply functional_extensionality. intro x. symmetry. apply andb_assoc.
  - unfold qand, qbvs, n_and. simpl. apply functional_extensionality. intro x. symmetry. apply andb_assoc.
  - unfold qand, qlocs, n_and. simpl. apply functional_extensionality. intro x. symmetry. apply andb_assoc.
Qed.

Lemma qor_qand_distrib : forall a b c,
  qor a (qand b c) = qand (qor a b) (qor a c).
Proof.
  intros. apply qual_ext.
  - unfold qor, qand, qfresh. simpl. apply orb_andb_distrib_r.
  - unfold qor, qand, qfvs, n_or, n_and. simpl. apply functional_extensionality. intro x.
    apply orb_andb_distrib_r.
  - unfold qor, qand, qbvs, n_or, n_and. simpl. apply functional_extensionality. intro x.
    apply orb_andb_distrib_r.
  - unfold qor, qand, qlocs, n_or, n_and. simpl. apply functional_extensionality. intro x.
    apply orb_andb_distrib_r.
Qed.

Lemma qor_qand_distrib_l : forall a b c,
  qor (qand a b) c = qand (qor a c) (qor b c).
Proof.
  intros. apply qual_ext.
  - unfold qor, qand, qfresh. simpl. apply orb_andb_distrib_l.
  - unfold qor, qand, qfvs, n_or, n_and. simpl. apply functional_extensionality. intro x.
    apply orb_andb_distrib_l.
  - unfold qor, qand, qbvs, n_or, n_and. simpl. apply functional_extensionality. intro x.
    apply orb_andb_distrib_l.
  - unfold qor, qand, qlocs, n_or, n_and. simpl. apply functional_extensionality. intro x.
    apply orb_andb_distrib_l.
Qed.

Lemma qor_qand_absorb : forall a b, qor a (qand a b) = a.
Proof.
  intros. apply qual_ext.
  - unfold qor, qand, qfresh. simpl. apply absorption_orb.
  - unfold qor, qand, n_or, n_and. apply functional_extensionality. intro x.
    simpl. apply absorption_orb.
  - unfold qor, qand, n_or, n_and. apply functional_extensionality. intro x.
    simpl. apply absorption_orb.
  - unfold qor, qand, n_or, n_and. apply functional_extensionality. intro x.
    simpl. apply absorption_orb.
Qed.

Lemma qand_qor_absorb : forall a b, qand a (qor a b) = a.
Proof.
  intros. apply qual_ext.
  - unfold qand, qor, qfresh. simpl. apply absorption_andb.
  - unfold qand, qor, n_and, n_or. apply functional_extensionality. intro x.
    simpl. apply absorption_andb.
  - unfold qand, qor, n_and, n_or. apply functional_extensionality. intro x.
    simpl. apply absorption_andb.
  - unfold qand, qor, n_and, n_or. apply functional_extensionality. intro x.
    simpl. apply absorption_andb.
Qed.

Lemma qand_empty_l : forall q, qand q_empty q = q_empty.
Proof.
  intros. apply qual_ext.
  - unfold qand, q_empty, qfresh. simpl. reflexivity.
  - unfold qand, q_empty, qfvs, n_and, n_empty. simpl. apply functional_extensionality. intro x. reflexivity.
  - unfold qand, q_empty, qbvs, n_and, n_empty. simpl. reflexivity.
  - unfold qand, q_empty, qlocs, n_and, n_empty. simpl. apply functional_extensionality. intro x. reflexivity.
Qed.

Lemma qand_empty_r : forall q, qand q q_empty = q_empty.
Proof. intros. rewrite qand_comm. apply qand_empty_l. Qed.

Lemma subq_qand : forall a b c,
  a ⊑↑ b -> a ⊑↑ c -> a ⊑↑ (qand b c).
Proof.
  intros a b c [Hf1 [H1 [H2 H3]]] [Hf2 [G1 [G2 G3]]].
  unfold Subq. split.
  - intros Hfa. pose proof (Hf1 Hfa) as Hfb. pose proof (Hf2 Hfa) as Hfc.
    apply Is_true_eq_left. unfold qand, qfresh. simpl.
    apply andb_true_intro. split; apply Is_true_eq_true in Hfb; apply Is_true_eq_true in Hfc;
      [exact Hfb|exact Hfc].
  - split.
    + unfold N_sub in *. intros x Hx. unfold qand, qfvs, n_and. simpl.
      apply andb_true_intro. split; [apply H1|apply G1]; exact Hx.
    + split.
      * unfold N_sub in *. intros x Hx. unfold qand, qbvs, n_and. simpl.
        apply andb_true_intro. split; [apply H2|apply G2]; exact Hx.
      * unfold N_sub in *. intros x Hx. unfold qand, qlocs, n_and. simpl.
        apply andb_true_intro. split; [apply H3|apply G3]; exact Hx.
Qed.

Lemma step_local_locs_kill : forall t σ t' σ' d,
  step t σ t' σ' ->
  kill_sep (local_locs t) d ->
  closed_Qual 0 0 (‖σ‖) (Q_lift d) ->
  wf_store σ ->
  kill_sep (local_locs t') d.
Proof.
  intros t σ t' σ' d Hstep. induction Hstep; intros Hk Hcl Hwf.
  - (* ttapp *) simpl in Hk. eapply kill_sep_subq_first; [exact Hk|apply local_locs_ttapp_sub].
  - (* beta *) eapply kill_sep_subq_first; [exact Hk|apply local_locs_beta_sub].
  - (* ref *) eapply kill_sep_subq_first; [exact Hk|simpl; apply q_empty_subq].
  - (* refat *) eapply kill_sep_subq_first; [exact Hk|simpl; apply q_empty_subq].
  - (* deref *) simpl in Hk.
    assert (Hsi : sindexr' l o σ = Some v).
    { eapply sindexr'_from_indexr; eassumption. }
    destruct (Hwf l o v Hsi) as [Hwfv Hvalv].
    assert (Hlocals : local_locs v = q_empty) by (eapply value_local_locs; eassumption).
    rewrite Hlocals. exact Hk.
  - (* assign *) simpl. apply kill_sep_empty_l.
  - (* twithr *) change (kill_sep (qor (&!(‖σ‖)) (local_locs (t <~ᵗ tunit; (tloc (‖σ‖) 0)))) d).
    eapply kill_sep_qor_l.
    + eapply kill_sep_amp_of_closed_ge; [exact Hcl|apply Nat.le_refl].
    + eapply kill_sep_subq_first.
      * eapply kill_sep_subq_first; [exact Hk|apply qor_subq_r].
      * apply local_locs_open_tunit_amp.
  - (* twithc *) eapply kill_sep_subq_first; [exact Hk|simpl; apply qor_subq_r].
  - (* c_tapp *) apply IHHstep; assumption.
  - (* c_ref *) apply IHHstep; assumption.
  - (* c_refat_l *) eapply kill_sep_qor_l.
    + eapply IHHstep.
      * eapply kill_sep_local_locs_trefat_l; exact Hk.
      * exact Hcl. * exact Hwf.
    + eapply kill_sep_local_locs_trefat_r; exact Hk.
  - (* c_refat_r *) eapply kill_sep_qor_l.
    + eapply kill_sep_local_locs_trefat_l; exact Hk.
    + eapply IHHstep.
      * eapply kill_sep_local_locs_trefat_r; exact Hk.
      * exact Hcl. * exact Hwf.
  - (* c_deref *) apply IHHstep; assumption.
  - (* c_app_l *) eapply kill_sep_qor_l.
    + eapply IHHstep.
      * eapply kill_sep_local_locs_tapp_l; exact Hk.
      * exact Hcl. * exact Hwf.
    + eapply kill_sep_local_locs_tapp_r; exact Hk.
  - (* c_app_r *) eapply kill_sep_qor_l.
    + eapply kill_sep_local_locs_tapp_l; exact Hk.
    + eapply IHHstep.
      * eapply kill_sep_local_locs_tapp_r; exact Hk.
      * exact Hcl. * exact Hwf.
  - (* c_assign_l *) eapply kill_sep_qor_l.
    + eapply IHHstep.
      * eapply kill_sep_local_locs_tassign_l; exact Hk.
      * exact Hcl. * exact Hwf.
    + eapply kill_sep_local_locs_tassign_r; exact Hk.
  - (* c_assign_r *) eapply kill_sep_qor_l.
    + eapply kill_sep_local_locs_tassign_l; exact Hk.
    + eapply IHHstep.
      * eapply kill_sep_local_locs_tassign_r; exact Hk.
      * exact Hcl. * exact Hwf.
  - (* c_twithr_l *) eapply kill_sep_qor_l.
    + eapply IHHstep.
      * eapply kill_sep_local_locs_twithr_l; exact Hk.
      * exact Hcl. * exact Hwf.
    + eapply kill_sep_local_locs_twithr_r; exact Hk.
  - (* c_twithc *) change (kill_sep (qor (&!l) (local_locs t')) d).
    eapply kill_sep_qor_l.
    + eapply kill_sep_subq_first; [exact Hk|apply qor_subq_l].
    + eapply IHHstep.
      * eapply kill_sep_local_locs_twithc; exact Hk.
      * exact Hcl. * exact Hwf.
Qed.

Lemma preserve_deref_context : forall (Σ:senv) ϰ φ t t' d1 T d σ σ',
  preserve [] Σ ϰ φ (local_locs t) t' (TRef d1 T) d σ' ->
  step t σ t' σ' ->
  CtxOK [] φ Σ ϰ σ -> wf_store σ ->
  ♦∉ d1 -> d1 ⊑↑ φ -> kill_sep (local_locs t) d1 ->
  preserve [] Σ ϰ φ (local_locs (!t)) (!t') T d1 σ'.
Proof.
  intros Σ ϰ φ t t' d1 T d σ σ' Hp Hstep Hctx Hstore Hnd Hd1phi Hkill.
  destruct Hp as [Σ' d' φ' ϰ' Hext Henv Hd' Hwf' Hctx' Hdisj Hty' Hstore' Hws'].
  assert (Hlen : ‖σ‖ = ‖Σ‖) by (eapply CtxOK_length; exact Hctx).
  assert (Hphi : φ ⊑↑ qdom Σ) by (eapply CtxOK_phi; exact Hctx).
  assert (HclphiΣ : closed_Qual 0 0 (‖Σ‖) (Q_lift φ))
    by (eapply closed_qual_of_subq_qdom with (b:=0) (f:=0); exact Hphi).
  assert (Hclphiσ : closed_Qual 0 0 (‖σ‖) (Q_lift φ))
    by (rewrite Hlen; exact HclphiΣ).
  assert (Hcld1Σ : closed_Qual 0 0 (‖Σ‖) (Q_lift d1)).
  { eapply closed_Qual_of_subq_or_diamond_f with (b:=0) (f:=0) (φ:=φ);
      [exact HclphiΣ|eapply Subq_trans; [exact Hd1phi|apply qor_subq_l]]. }
  assert (Hcld1σ : closed_Qual 0 0 (‖σ‖) (Q_lift d1))
    by (rewrite Hlen; exact Hcld1Σ).
  assert (Hd1phi' : d1 ⊑↑ φ').
  { eapply envUpdate_subq_of_kill; [exact Henv|exact Hphi|exact Hd1phi|exact Hkill]. }
  assert (Hkillt' : kill_sep (local_locs t') d1)
    by (eapply step_local_locs_kill; eassumption).
  eapply preserve_intro with (Σ':=Σ') (d':=q_empty) (φ':=φ') (ϰ':=ϰ').
  - exact Hext.
  - exact Henv.
  - apply q_empty_subq.
  - exact Hwf'.
  - exact Hctx'.
  - apply disjointq_bot.
  - rewrite qqplus_empty_r. eapply t_deref; [exact Hty'|exact Hnd|exact Hd1phi'|exact Hkillt'].
  - exact Hstore'.
  - simpl. exact Hws'.
Qed.

Lemma local_locs_tapp : forall t1 t2,
  local_locs (tapp t1 t2) = qor (local_locs t1) (local_locs t2).
Proof. intros. reflexivity. Qed.

Lemma local_locs_trefat : forall t1 t2,
  local_locs (trefat t1 t2) = qor (local_locs t1) (local_locs t2).
Proof. intros. reflexivity. Qed.

Lemma local_locs_tassign : forall t1 t2,
  local_locs (tassign t1 t2) = qor (local_locs t1) (local_locs t2).
Proof. intros. reflexivity. Qed.

Lemma local_locs_twithr : forall t1 t2,
  local_locs (twithr t1 t2) = qor (local_locs t1) (local_locs t2).
Proof. intros. reflexivity. Qed.

Lemma local_locs_twithc : forall l t,
  local_locs (twithc l t) = qor (&!l) (local_locs t).
Proof. intros. reflexivity. Qed.

Lemma indexr_extends : forall {A} (l' c:list A) o x,
  indexr o c = Some x -> indexr o (l' ++ c) = Some x.
Proof.
  intros A l'. induction l' as [|a l' IH]; intros c o x H.
  - simpl. exact H.
  - simpl. destruct (Nat.eqb o (length (l' ++ c))) eqn:E.
    + apply Nat.eqb_eq in E. pose proof (indexr_Some_lt o c x H). rewrite app_length in E. lia.
    + apply IH. exact H.
Qed.

Lemma sindexr_nil : forall l o, sindexr l o ([]:senv) = None.
Proof. intros. reflexivity. Qed.

Lemma sindexr'_nil : forall l o, sindexr' l o ([]:store) = None.
Proof. intros. reflexivity. Qed.

Lemma indexr_nil : forall {A} x, indexr x ([]:list A) = None.
Proof. intros. reflexivity. Qed.

Lemma indexr_extends_nil : forall {A} (c:list A) o x,
  indexr o c = Some x -> indexr o ([] ++ c) = Some x.
Proof. intros. simpl. exact H. Qed.

Lemma qdiff_empty_l : forall q, qdiff q_empty q = q_empty.
Proof.
  intros. apply qual_ext.
  - unfold qdiff, q_empty, qfresh. simpl. reflexivity.
  - unfold qdiff, q_empty, qfvs, n_diff, n_empty. simpl. apply functional_extensionality. intro x. reflexivity.
  - unfold qdiff, q_empty, qbvs, n_diff, n_empty. simpl. reflexivity.
  - unfold qdiff, q_empty, qlocs, n_diff, n_empty. simpl. apply functional_extensionality. intro x. reflexivity.
Qed.

Lemma qdiff_qor : forall a b c,
  qdiff (qor a b) c = qor (qdiff a c) (qdiff b c).
Proof.
  intros. apply qual_ext.
  - unfold qdiff, qor, qfresh. simpl. apply andb_orb_distrib_l.

  - unfold qdiff, qor, n_diff, n_or. apply functional_extensionality. intro x.
    simpl. apply andb_orb_distrib_l.
  - unfold qdiff, qor, n_diff, n_or. apply functional_extensionality. intro x.
    simpl. apply andb_orb_distrib_l.
  - unfold qdiff, qor, n_diff, n_or. apply functional_extensionality. intro x.
    simpl. apply andb_orb_distrib_l.
Qed.

Lemma qdiff_self_empty : forall (q:qual), qdiff q q = q_empty.
Proof.
  intros. apply qual_ext.
  - unfold qdiff, qfresh, q_empty. simpl. destruct (fst (fst (fst q))); reflexivity.
  - unfold qdiff, qfvs, n_diff, q_empty, n_empty. simpl. apply functional_extensionality. intro x.
    destruct (snd (fst (fst q)) x); simpl; reflexivity.
  - unfold qdiff, qbvs, n_diff, q_empty, n_empty. simpl. apply functional_extensionality. intro x.
    destruct (snd (fst q) x); simpl; reflexivity.
  - unfold qdiff, qlocs, n_diff, q_empty, n_empty. simpl. apply functional_extensionality. intro x.
    destruct (snd q x); simpl; reflexivity.
Qed.

Lemma qfresh_q_empty : qfresh q_empty = false. Proof. reflexivity. Qed.
Lemma qfvs_q_empty : qfvs q_empty = n_empty. Proof. reflexivity. Qed.
Lemma qbvs_q_empty : qbvs q_empty = n_empty. Proof. reflexivity. Qed.
Lemma qlocs_q_empty : qlocs q_empty = n_empty. Proof. reflexivity. Qed.

Lemma wf_store_none_cons : forall (σ:store),
  wf_store σ -> wf_store (None :: σ).
Proof.
  intros σ H l o v Hl. rewrite sindexr'_cons in Hl.
  destruct (Nat.eqb l (length σ)) eqn:E.
  - simpl in Hl. discriminate Hl.
  - eapply H. exact Hl.
Qed.

Lemma wf_store_None_singleton : wf_store [None].
Proof. apply wf_store_none_cons. apply wf_store_empty. Qed.

Lemma CtxOK_empty_store : forall (ϰ:qual),
  closed_Qual 0 0 0 (Q_lift ϰ) -> qlocs ϰ = n_empty -> CtxOK [] q_empty [] ϰ [].
Proof.
  intros ϰ Hcl Hlocs. unfold CtxOK. split.
  - apply Subq_refl.
  - split.
    + reflexivity.
    + split.
      * apply q_empty_subq.
      * split.
        -- exact Hcl.
        -- split.
           ++ apply kill_sep_empty.
           ++ intros l o cty T q. split.
              ** intros Hmem. unfold qmem, N_lift in Hmem. rewrite Hlocs in Hmem. simpl in Hmem. discriminate Hmem.
              ** intros _ _ Hl. inversion Hl.
Qed.

Lemma CtxOK_length_nil : forall Γ φ (Σ:senv) ϰ,
  CtxOK Γ φ Σ ϰ [] -> ‖Σ‖ = 0.
Proof. intros. pose proof (CtxOK_length Γ φ Σ ϰ [] H) as Hlen. simpl in Hlen. symmetry. exact Hlen. Qed.

Lemma CtxOK_store_nil : forall Γ φ ϰ (σ:store),
  CtxOK Γ φ [] ϰ σ -> σ = [].
Proof.
  intros. pose proof (CtxOK_length Γ φ [] ϰ σ H) as Hlen. simpl in Hlen.
  apply length_zero_iff_nil. exact Hlen.
Qed.

Lemma CtxOK_store_nil_sym : forall Γ φ ϰ (σ:store),
  CtxOK Γ φ [] ϰ σ -> [] = σ.
Proof. intros. symmetry. eapply CtxOK_store_nil; exact H. Qed.

Lemma qdiff_fresh : forall a b, qfresh (qdiff a b) = andb (qfresh a) (negb (qfresh b)).
Proof. intros. reflexivity. Qed.

Lemma qdiff_fvs : forall a b, qfvs (qdiff a b) = n_diff (qfvs a) (qfvs b).
Proof. intros. reflexivity. Qed.

Lemma qdiff_bvs : forall a b, qbvs (qdiff a b) = n_diff (qbvs a) (qbvs b).
Proof. intros. reflexivity. Qed.

Lemma qdiff_locs : forall a b, qlocs (qdiff a b) = n_diff (qlocs a) (qlocs b).
Proof. intros. reflexivity. Qed.

Lemma qdiff_qdiff : forall a b,
  qdiff (qdiff a b) b = qdiff a b.
Proof.
  intros. apply qual_ext.
  - rewrite !qdiff_fresh. destruct (qfresh a); destruct (qfresh b); reflexivity.
  - apply functional_extensionality. intro x. rewrite !qdiff_fvs. unfold n_diff. simpl.
    destruct (qfvs a x); destruct (qfvs b x); reflexivity.
  - apply functional_extensionality. intro x. rewrite !qdiff_bvs. unfold n_diff. simpl.
    destruct (qbvs a x); destruct (qbvs b x); reflexivity.
  - apply functional_extensionality. intro x. rewrite !qdiff_locs. unfold n_diff. simpl.
    destruct (qlocs a x); destruct (qlocs b x); reflexivity.
Qed.

Lemma qand_fresh : forall a b, qfresh (qand a b) = andb (qfresh a) (qfresh b).
Proof. intros. reflexivity. Qed.
Lemma qand_fvs : forall a b, qfvs (qand a b) = n_and (qfvs a) (qfvs b).
Proof. intros. reflexivity. Qed.
Lemma qand_bvs : forall a b, qbvs (qand a b) = n_and (qbvs a) (qbvs b).
Proof. intros. reflexivity. Qed.
Lemma qand_locs : forall a b, qlocs (qand a b) = n_and (qlocs a) (qlocs b).
Proof. intros. reflexivity. Qed.

Lemma qdiff_qand : forall a b c,
  qdiff (qand a b) c = qand (qdiff a c) (qdiff b c).
Proof.
  intros. apply qual_ext.
  - rewrite qdiff_fresh, qand_fresh, qand_fresh, qdiff_fresh, qdiff_fresh.
    destruct (qfresh a); destruct (qfresh b); destruct (qfresh c); reflexivity.
  - apply functional_extensionality. intro x.
    rewrite qdiff_fvs, qand_fvs, qand_fvs, qdiff_fvs, qdiff_fvs.
    unfold n_diff, n_and. simpl.
    destruct (qfvs a x); destruct (qfvs b x); destruct (qfvs c x); reflexivity.
  - apply functional_extensionality. intro x.
    rewrite qdiff_bvs, qand_bvs, qand_bvs, qdiff_bvs, qdiff_bvs.
    unfold n_diff, n_and. simpl.
    destruct (qbvs a x); destruct (qbvs b x); destruct (qbvs c x); reflexivity.
  - apply functional_extensionality. intro x.
    rewrite qdiff_locs, qand_locs, qand_locs, qdiff_locs, qdiff_locs.
    unfold n_diff, n_and. simpl.
    destruct (qlocs a x); destruct (qlocs b x); destruct (qlocs c x); reflexivity.
Qed.

Lemma indexr_prefix_other : forall {X} (P D:list X) a a' i,
  i <> length D -> indexr i (P ++ a :: D) = indexr i (P ++ a' :: D).
Proof.
  intros X P. induction P as [|p P' IH]; intros D a a' i Hne.
  - simpl. destruct (Nat.eqb i (length D)) eqn:E.
    + apply Nat.eqb_eq in E. exfalso. apply Hne. exact E.
    + reflexivity.
  - simpl. destruct (Nat.eqb i (length (P' ++ a :: D))) eqn:E.
    + assert (E' : Nat.eqb i (length (P' ++ a' :: D)) = true).
      { apply Nat.eqb_eq. apply Nat.eqb_eq in E. rewrite app_length in E. rewrite app_length. simpl in *. lia. }
      rewrite E'. reflexivity.
    + assert (E' : Nat.eqb i (length (P' ++ a' :: D)) = false).
      { apply Nat.eqb_neq. apply Nat.eqb_neq in E. rewrite app_length in E. rewrite app_length. simpl in *. lia. }
      rewrite E'. apply IH. exact Hne.
Qed.

Lemma indexr_prefix_head : forall {X} (P D:list X) a,
  indexr (length D) (P ++ a :: D) = Some a.
Proof.
  intros X P. induction P as [|p P' IH]; intros D a.
  - simpl. rewrite Nat.eqb_refl. reflexivity.
  - simpl.
    assert (E : Nat.eqb (length D) (length (P' ++ a :: D)) = false).
    { apply Nat.eqb_neq. rewrite app_length. simpl. lia. }
    rewrite E. apply IH.
Qed.

Lemma ctx_len_false_repl : forall (P D:tenv) U d U' d',
  length (P ++ (bind_tm,false,U,d) :: D) = length (P ++ (bind_tm,false,U',d') :: D).
Proof. intros. rewrite !app_length. simpl. lia. Qed.

Lemma ctx_len_fun_repl : forall (P D:tenv) U U' d,
  length (P ++ (bind_tm,true,U,d) :: D) = length (P ++ (bind_tm,true,U',d) :: D).
Proof. intros. rewrite !app_length. simpl. lia. Qed.

Lemma qstp_ctx_false_repl : forall (Σ:senv) (Γ:tenv) q1 q2,
  qstp Γ Σ q1 q2 ->
  forall P D UB d UB' d',
  closed_ty 0 0 (‖Σ‖) UB' ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift d') ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift d) ->
  d' ⊑↑ d ->
  Γ = P ++ (bind_tm,false,UB,d) :: D ->
  qstp (P ++ (bind_tm,false,UB',d') :: D) Σ q1 q2.
Proof.
  intros Σ Γ q1 q2 H. induction H; intros P D UB d UB' d' HcUB' Hcd' Hcd Hsub E;
    rewrite E in *; pose proof (ctx_len_false_repl P D UB d UB' d') as Hlen; try rewrite Hlen in *.
  - (* qs_sq *) eapply qs_sq; eassumption.
  - (* qs_self *) destruct (Nat.eqb f (length D)) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst f.
      rewrite indexr_prefix_head in H. inversion H.
    + apply Nat.eqb_neq in Ex.
      eapply qs_self.
      * rewrite <- (indexr_prefix_other P D (bind_tm,false,UB,d) (bind_tm,false,UB',d') f); [exact H|exact Ex].
      * exact H0.
      * exact H1.
  - (* qs_self_all *) destruct (Nat.eqb f (length D)) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst f.
      rewrite indexr_prefix_head in H. inversion H.
    + apply Nat.eqb_neq in Ex.
      eapply qs_self_all.
      * rewrite <- (indexr_prefix_other P D (bind_tm,false,UB,d) (bind_tm,false,UB',d') f); [exact H|exact Ex].
      * exact H0.
      * exact H1.
  - (* qs_qvar *) destruct (Nat.eqb x (length D)) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst x.
      rewrite indexr_prefix_head in H. inversion H; subst.
      assert (Hnd' : ♦∉ d').
      { intros Hf. apply H2. destruct Hsub as [Hs _]. apply Hs. exact Hf. }
      eapply qs_trans.
      * eapply qs_qvar.
        -- rewrite indexr_prefix_head. reflexivity.
        -- eapply closed_ty_weaken; [exact HcUB'|lia|lia].
        -- eapply closed_Qual_weaken; [exact Hcd'|lia|lia].
        -- exact Hnd'.
      * eapply qs_sq.
        -- exact Hsub.
        -- eapply closed_Qual_weaken; [exact Hcd|lia|lia].
    + apply Nat.eqb_neq in Ex.
      eapply qs_qvar.
      * rewrite <- (indexr_prefix_other P D (bind_tm,false,UB,d) (bind_tm,false,UB',d') x); [exact H|exact Ex].
      * exact H0.
      * exact H1.
      * exact H2.
  - (* qs_qvar_ty *) destruct (Nat.eqb x (length D)) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst x.
      rewrite indexr_prefix_head in H. inversion H.
    + apply Nat.eqb_neq in Ex.
      eapply qs_qvar_ty.
      * rewrite <- (indexr_prefix_other P D (bind_tm,false,UB,d) (bind_tm,false,UB',d') x); [exact H|exact Ex].
      * exact H0.
      * exact H1.
      * exact H2.
  - (* qs_cong *) eapply qs_cong.
    + apply (IHqstp P D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl).
    + exact H0.
  - (* qs_trans *) eapply qs_trans.
    + apply (IHqstp1 P D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl).
    + apply (IHqstp2 P D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl).
Qed.

Lemma qstp_ctx_fun_repl : forall (Σ:senv) (Γ:tenv) q1 q2,
  qstp Γ Σ q1 q2 ->
  forall P D UB UB' d,
  (exists d1 d2 T1 T2, UB = TFun d1 d2 T1 T2) ->
  (exists d1 d2 T1 T2, UB' = TFun d1 d2 T1 T2) ->
  closed_ty 0 0 (‖Σ‖) UB' ->
  Γ = P ++ (bind_tm,true,UB,d) :: D ->
  qstp (P ++ (bind_tm,true,UB',d) :: D) Σ q1 q2.
Proof.
  intros Σ Γ q1 q2 H. induction H; intros P D UB UB' d HUB HUB' HcUB' E;
    rewrite E in *; pose proof (ctx_len_fun_repl P D UB UB' d) as Hlen; try rewrite Hlen in *.
  - (* qs_sq *) eapply qs_sq; eassumption.
  - (* qs_self *) destruct (Nat.eqb f (length D)) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst f.
      rewrite indexr_prefix_head in H. inversion H; subst.
      destruct HUB' as (a' & b' & c' & e' & EU'). subst UB'.
      eapply qs_self.
      * rewrite indexr_prefix_head. reflexivity.
      * exact H0.
      * exact H1.
    + apply Nat.eqb_neq in Ex.
      eapply qs_self.
      * rewrite <- (indexr_prefix_other P D (bind_tm,true,UB,d) (bind_tm,true,UB',d) f); [exact H|exact Ex].
      * exact H0.
      * exact H1.
  - (* qs_self_all *) destruct (Nat.eqb f (length D)) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst f.
      rewrite indexr_prefix_head in H. inversion H; subst.
      destruct HUB as (a & b & c & e & EU). discriminate EU.
    + apply Nat.eqb_neq in Ex.
      eapply qs_self_all.
      * rewrite <- (indexr_prefix_other P D (bind_tm,true,UB,d) (bind_tm,true,UB',d) f); [exact H|exact Ex].
      * exact H0.
      * exact H1.
  - (* qs_qvar *) destruct (Nat.eqb x (length D)) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst x.
      rewrite indexr_prefix_head in H. inversion H; subst.
      eapply qs_qvar.
      * rewrite indexr_prefix_head. reflexivity.
      * eapply closed_ty_weaken; [exact HcUB'|lia|lia].
      * exact H1.
      * exact H2.
    + apply Nat.eqb_neq in Ex.
      eapply qs_qvar.
      * rewrite <- (indexr_prefix_other P D (bind_tm,true,UB,d) (bind_tm,true,UB',d) x); [exact H|exact Ex].
      * exact H0.
      * exact H1.
      * exact H2.
  - (* qs_qvar_ty *) destruct (Nat.eqb x (length D)) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst x.
      rewrite indexr_prefix_head in H. inversion H.
    + apply Nat.eqb_neq in Ex.
      eapply qs_qvar_ty.
      * rewrite <- (indexr_prefix_other P D (bind_tm,true,UB,d) (bind_tm,true,UB',d) x); [exact H|exact Ex].
      * exact H0.
      * exact H1.
      * exact H2.
  - (* qs_cong *) eapply qs_cong.
    + apply (IHqstp P D UB UB' d HUB HUB' HcUB' eq_refl).
    + exact H0.
  - (* qs_trans *) eapply qs_trans.
    + apply (IHqstp1 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + apply (IHqstp2 P D UB UB' d HUB HUB' HcUB' eq_refl).
Qed.


Lemma open_ty'_ctx_len : forall (Γ Δ:tenv) T,
  ‖Γ‖ = ‖Δ‖ -> T <~²ᵀ Γ = T <~²ᵀ Δ.
Proof. intros. unfold open_ty', open_ty. rewrite H. reflexivity. Qed.

Lemma open_tm'_ctx_len : forall (Γ Δ:tenv) t,
  ‖Γ‖ = ‖Δ‖ -> t <~²ᵗ Γ = t <~²ᵗ Δ.
Proof. intros. unfold open_tm'. rewrite H. reflexivity. Qed.

Lemma openq'_ctx_len : forall (Γ Δ:tenv) q,
  ‖Γ‖ = ‖Δ‖ -> q <~²ᵈ Γ = q <~²ᵈ Δ.
Proof. intros. unfold openq'. rewrite H. reflexivity. Qed.

Lemma stp_ctx_false_repl : forall (Σ:senv) (Γ:tenv) T1 e1 T2 e2,
  stp Γ Σ T1 e1 T2 e2 ->
  forall P D UB d UB' d',
  closed_ty 0 0 (‖Σ‖) UB' ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift d') ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift d) ->
  d' ⊑↑ d ->
  Γ = P ++ (bind_tm,false,UB,d) :: D ->
  stp (P ++ (bind_tm,false,UB',d') :: D) Σ T1 e1 T2 e2.
Proof.
  intros Σ Γ T1 e1 T2 e2 H. induction H; intros P D UB d UB' d'
    HcUB' Hcd' Hcd Hsub E;
    rewrite E in *; pose proof (ctx_len_false_repl P D UB d UB' d') as Hlen;
    try rewrite Hlen in *.
  - (* s_top *) eapply s_top.
    + exact H.
    + apply (qstp_ctx_false_repl Σ (P++(bind_tm,false,UB,d)::D) d1 d2 H0 P D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl).
  - (* s_tvar_refl *) destruct (Nat.eqb x (length D)) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst x.
      eapply s_tvar_refl.
      * rewrite indexr_prefix_head. reflexivity.
      * apply (qstp_ctx_false_repl Σ (P++(bind_tm,false,UB,d)::D) d1 d2 H0 P D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl).
    + apply Nat.eqb_neq in Ex.
      eapply s_tvar_refl.
      * rewrite <- (indexr_prefix_other P D (bind_tm,false,UB,d) (bind_tm,false,UB',d') x); [exact H|exact Ex].
      * apply (qstp_ctx_false_repl Σ (P++(bind_tm,false,UB,d)::D) d1 d2 H0 P D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl).
  - (* s_tvar_trans *) destruct (Nat.eqb x (length D)) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst x.
      rewrite indexr_prefix_head in H. inversion H.
    + apply Nat.eqb_neq in Ex.
      eapply s_tvar_trans.
      * rewrite <- (indexr_prefix_other P D (bind_tm,false,UB,d) (bind_tm,false,UB',d') x); [exact H|exact Ex].
      * exact H0.
      * apply (IHstp P D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl).
  - (* s_all *) eapply s_all.
    + exact H.
    + exact H0.
    + apply (qstp_ctx_false_repl Σ (P++(bind_tm,false,UB,d)::D) d5 d6 H1 P D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl).
    + apply (IHstp1 P D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl).
    + pose proof (IHstp2 ((bind_ty,false,T3,d3)::(bind_tm,true,(TAll d1 d2 T1 T2),{♦})::P) D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl) as Hbody.
      replace (T2 <~²ᵀ (P++(bind_tm,false,UB,d)::D)) with (T2 <~²ᵀ (P++(bind_tm,false,UB',d')::D)) in Hbody by (apply open_ty'_ctx_len; rewrite !app_length; reflexivity).
      replace (T4 <~²ᵀ (P++(bind_tm,false,UB,d)::D)) with (T4 <~²ᵀ (P++(bind_tm,false,UB',d')::D)) in Hbody by (apply open_ty'_ctx_len; rewrite !app_length; reflexivity).
      replace (d2 <~²ᵈ (P++(bind_tm,false,UB,d)::D)) with (d2 <~²ᵈ (P++(bind_tm,false,UB',d')::D)) in Hbody by (apply openq'_ctx_len; rewrite !app_length; reflexivity).
      replace (d4 <~²ᵈ (P++(bind_tm,false,UB,d)::D)) with (d4 <~²ᵈ (P++(bind_tm,false,UB',d')::D)) in Hbody by (apply openq'_ctx_len; rewrite !app_length; reflexivity).
      exact Hbody.
  - (* s_base *) eapply s_base.
    apply (qstp_ctx_false_repl Σ (P++(bind_tm,false,UB,d)::D) d1 d2 H P D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl).
  - (* s_ref *) eapply s_ref.
    + apply (qstp_ctx_false_repl Σ (P++(bind_tm,false,UB,d)::D) d1 d2 H P D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl).
    + apply (IHstp1 P D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl).
    + apply (IHstp2 P D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl).
    + apply (qstp_ctx_false_repl Σ (P++(bind_tm,false,UB,d)::D) q1 q2 H2 P D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl).
    + apply (qstp_ctx_false_repl Σ (P++(bind_tm,false,UB,d)::D) q2 q1 H3 P D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl).
  - (* s_fun *) eapply s_fun.
    + exact H.
    + exact H0.
    + apply (qstp_ctx_false_repl Σ (P++(bind_tm,false,UB,d)::D) d5 d6 H1 P D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl).
    + apply (IHstp1 P D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl).
    + pose proof (IHstp2 ((bind_tm,false,T3,d3)::(bind_tm,true,(TFun d1 d2 T1 T2),{♦})::P) D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl) as Hbody.
      replace (T2 <~²ᵀ (P++(bind_tm,false,UB,d)::D)) with (T2 <~²ᵀ (P++(bind_tm,false,UB',d')::D)) in Hbody by (apply open_ty'_ctx_len; rewrite !app_length; reflexivity).
      replace (T4 <~²ᵀ (P++(bind_tm,false,UB,d)::D)) with (T4 <~²ᵀ (P++(bind_tm,false,UB',d')::D)) in Hbody by (apply open_ty'_ctx_len; rewrite !app_length; reflexivity).
      replace (d2 <~²ᵈ (P++(bind_tm,false,UB,d)::D)) with (d2 <~²ᵈ (P++(bind_tm,false,UB',d')::D)) in Hbody by (apply openq'_ctx_len; rewrite !app_length; reflexivity).
      replace (d4 <~²ᵈ (P++(bind_tm,false,UB,d)::D)) with (d4 <~²ᵈ (P++(bind_tm,false,UB',d')::D)) in Hbody by (apply openq'_ctx_len; rewrite !app_length; reflexivity).
      exact Hbody.
  - (* s_trans *) eapply s_trans.
    + apply (IHstp1 P D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl).
    + apply (IHstp2 P D UB d UB' d' HcUB' Hcd' Hcd Hsub eq_refl).
Qed.

Lemma stp_ctx_fun_repl : forall (Σ:senv) (Γ:tenv) T1 e1 T2 e2,
  stp Γ Σ T1 e1 T2 e2 ->
  forall P D UB UB' d,
  (exists d1 d2 T1 T2, UB = TFun d1 d2 T1 T2) ->
  (exists d1 d2 T1 T2, UB' = TFun d1 d2 T1 T2) ->
  closed_ty 0 0 (‖Σ‖) UB' ->
  Γ = P ++ (bind_tm,true,UB,d) :: D ->
  stp (P ++ (bind_tm,true,UB',d) :: D) Σ T1 e1 T2 e2.
Proof.
  intros Σ Γ T1 e1 T2 e2 H. induction H; intros P D UB UB' d HUB HUB' HcUB' E;
    rewrite E in *; pose proof (ctx_len_fun_repl P D UB UB' d) as Hlen;
    try rewrite Hlen in *.
  - (* s_top *) eapply s_top.
    + exact H.
    + apply (qstp_ctx_fun_repl Σ (P++(bind_tm,true,UB,d)::D) d1 d2 H0 P D UB UB' d HUB HUB' HcUB' eq_refl).
  - (* s_tvar_refl *) destruct (Nat.eqb x (length D)) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst x.
      eapply s_tvar_refl.
      * rewrite indexr_prefix_head. reflexivity.
      * apply (qstp_ctx_fun_repl Σ (P++(bind_tm,true,UB,d)::D) d1 d2 H0 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + apply Nat.eqb_neq in Ex.
      eapply s_tvar_refl.
      * rewrite <- (indexr_prefix_other P D (bind_tm,true,UB,d) (bind_tm,true,UB',d) x); [exact H|exact Ex].
      * apply (qstp_ctx_fun_repl Σ (P++(bind_tm,true,UB,d)::D) d1 d2 H0 P D UB UB' d HUB HUB' HcUB' eq_refl).
  - (* s_tvar_trans *) destruct (Nat.eqb x (length D)) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst x.
      rewrite indexr_prefix_head in H. inversion H.
    + apply Nat.eqb_neq in Ex.
      eapply s_tvar_trans.
      * rewrite <- (indexr_prefix_other P D (bind_tm,true,UB,d) (bind_tm,true,UB',d) x); [exact H|exact Ex].
      * exact H0.
      * apply (IHstp P D UB UB' d HUB HUB' HcUB' eq_refl).
  - (* s_all *) eapply s_all.
    + exact H.
    + exact H0.
    + apply (qstp_ctx_fun_repl Σ (P++(bind_tm,true,UB,d)::D) d5 d6 H1 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + apply (IHstp1 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + pose proof (IHstp2 ((bind_ty,false,T3,d3)::(bind_tm,true,(TAll d1 d2 T1 T2),{♦})::P) D UB UB' d HUB HUB' HcUB' eq_refl) as Hbody.
      replace (T2 <~²ᵀ (P++(bind_tm,true,UB,d)::D)) with (T2 <~²ᵀ (P++(bind_tm,true,UB',d)::D)) in Hbody by (apply open_ty'_ctx_len; rewrite !app_length; reflexivity).
      replace (T4 <~²ᵀ (P++(bind_tm,true,UB,d)::D)) with (T4 <~²ᵀ (P++(bind_tm,true,UB',d)::D)) in Hbody by (apply open_ty'_ctx_len; rewrite !app_length; reflexivity).
      replace (d2 <~²ᵈ (P++(bind_tm,true,UB,d)::D)) with (d2 <~²ᵈ (P++(bind_tm,true,UB',d)::D)) in Hbody by (apply openq'_ctx_len; rewrite !app_length; reflexivity).
      replace (d4 <~²ᵈ (P++(bind_tm,true,UB,d)::D)) with (d4 <~²ᵈ (P++(bind_tm,true,UB',d)::D)) in Hbody by (apply openq'_ctx_len; rewrite !app_length; reflexivity).
      exact Hbody.
  - (* s_base *) eapply s_base.
    apply (qstp_ctx_fun_repl Σ (P++(bind_tm,true,UB,d)::D) d1 d2 H P D UB UB' d HUB HUB' HcUB' eq_refl).
  - (* s_ref *) eapply s_ref.
    + apply (qstp_ctx_fun_repl Σ (P++(bind_tm,true,UB,d)::D) d1 d2 H P D UB UB' d HUB HUB' HcUB' eq_refl).
    + apply (IHstp1 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + apply (IHstp2 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + apply (qstp_ctx_fun_repl Σ (P++(bind_tm,true,UB,d)::D) q1 q2 H2 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + apply (qstp_ctx_fun_repl Σ (P++(bind_tm,true,UB,d)::D) q2 q1 H3 P D UB UB' d HUB HUB' HcUB' eq_refl).
  - (* s_fun *) eapply s_fun.
    + exact H.
    + exact H0.
    + apply (qstp_ctx_fun_repl Σ (P++(bind_tm,true,UB,d)::D) d5 d6 H1 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + apply (IHstp1 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + pose proof (IHstp2 ((bind_tm,false,T3,d3)::(bind_tm,true,(TFun d1 d2 T1 T2),{♦})::P) D UB UB' d HUB HUB' HcUB' eq_refl) as Hbody.
      replace (T2 <~²ᵀ (P++(bind_tm,true,UB,d)::D)) with (T2 <~²ᵀ (P++(bind_tm,true,UB',d)::D)) in Hbody by (apply open_ty'_ctx_len; rewrite !app_length; reflexivity).
      replace (T4 <~²ᵀ (P++(bind_tm,true,UB,d)::D)) with (T4 <~²ᵀ (P++(bind_tm,true,UB',d)::D)) in Hbody by (apply open_ty'_ctx_len; rewrite !app_length; reflexivity).
      replace (d2 <~²ᵈ (P++(bind_tm,true,UB,d)::D)) with (d2 <~²ᵈ (P++(bind_tm,true,UB',d)::D)) in Hbody by (apply openq'_ctx_len; rewrite !app_length; reflexivity).
      replace (d4 <~²ᵈ (P++(bind_tm,true,UB,d)::D)) with (d4 <~²ᵈ (P++(bind_tm,true,UB',d)::D)) in Hbody by (apply openq'_ctx_len; rewrite !app_length; reflexivity).
      exact Hbody.
  - (* s_trans *) eapply s_trans.
    + apply (IHstp1 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + apply (IHstp2 P D UB UB' d HUB HUB' HcUB' eq_refl).
Qed.

Lemma qstp_ctx_all_repl : forall (Σ:senv) (Γ:tenv) q1 q2,
  qstp Γ Σ q1 q2 ->
  forall P D UB UB' d,
  (exists d1 d2 T1 T2, UB = TAll d1 d2 T1 T2) ->
  (exists d1 d2 T1 T2, UB' = TAll d1 d2 T1 T2) ->
  closed_ty 0 0 (‖Σ‖) UB' ->
  Γ = P ++ (bind_tm,true,UB,d) :: D ->
  qstp (P ++ (bind_tm,true,UB',d) :: D) Σ q1 q2.
Proof.
  intros Σ Γ q1 q2 H. induction H; intros P D UB UB' d HUB HUB' HcUB' E;
    rewrite E in *; pose proof (ctx_len_fun_repl P D UB UB' d) as Hlen; try rewrite Hlen in *.
  - (* qs_sq *) eapply qs_sq; eassumption.
  - (* qs_self *) destruct (Nat.eqb f (length D)) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst f.
      rewrite indexr_prefix_head in H. inversion H; subst.
      destruct HUB as (a & b & c & e & EU). discriminate EU.
    + apply Nat.eqb_neq in Ex.
      eapply qs_self.
      * rewrite <- (indexr_prefix_other P D (bind_tm,true,UB,d) (bind_tm,true,UB',d) f); [exact H|exact Ex].
      * exact H0.
      * exact H1.
  - (* qs_self_all *) destruct (Nat.eqb f (length D)) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst f.
      rewrite indexr_prefix_head in H. inversion H; subst.
      destruct HUB' as (a' & b' & c' & e' & EU'). subst UB'.
      eapply qs_self_all.
      * rewrite indexr_prefix_head. reflexivity.
      * exact H0.
      * exact H1.
    + apply Nat.eqb_neq in Ex.
      eapply qs_self_all.
      * rewrite <- (indexr_prefix_other P D (bind_tm,true,UB,d) (bind_tm,true,UB',d) f); [exact H|exact Ex].
      * exact H0.
      * exact H1.
  - (* qs_qvar *) destruct (Nat.eqb x (length D)) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst x.
      rewrite indexr_prefix_head in H. inversion H; subst.
      eapply qs_qvar.
      * rewrite indexr_prefix_head. reflexivity.
      * eapply closed_ty_weaken; [exact HcUB'|lia|lia].
      * exact H1.
      * exact H2.
    + apply Nat.eqb_neq in Ex.
      eapply qs_qvar.
      * rewrite <- (indexr_prefix_other P D (bind_tm,true,UB,d) (bind_tm,true,UB',d) x); [exact H|exact Ex].
      * exact H0.
      * exact H1.
      * exact H2.
  - (* qs_qvar_ty *) destruct (Nat.eqb x (length D)) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst x.
      rewrite indexr_prefix_head in H. inversion H.
    + apply Nat.eqb_neq in Ex.
      eapply qs_qvar_ty.
      * rewrite <- (indexr_prefix_other P D (bind_tm,true,UB,d) (bind_tm,true,UB',d) x); [exact H|exact Ex].
      * exact H0.
      * exact H1.
      * exact H2.
  - (* qs_cong *) eapply qs_cong.
    + apply (IHqstp P D UB UB' d HUB HUB' HcUB' eq_refl).
    + exact H0.
  - (* qs_trans *) eapply qs_trans.
    + apply (IHqstp1 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + apply (IHqstp2 P D UB UB' d HUB HUB' HcUB' eq_refl).
Qed.

Lemma stp_ctx_all_repl : forall (Σ:senv) (Γ:tenv) T1 e1 T2 e2,
  stp Γ Σ T1 e1 T2 e2 ->
  forall P D UB UB' d,
  (exists d1 d2 T1 T2, UB = TAll d1 d2 T1 T2) ->
  (exists d1 d2 T1 T2, UB' = TAll d1 d2 T1 T2) ->
  closed_ty 0 0 (‖Σ‖) UB' ->
  Γ = P ++ (bind_tm,true,UB,d) :: D ->
  stp (P ++ (bind_tm,true,UB',d) :: D) Σ T1 e1 T2 e2.
Proof.
  intros Σ Γ T1 e1 T2 e2 H. induction H; intros P D UB UB' d HUB HUB' HcUB' E;
    rewrite E in *; pose proof (ctx_len_fun_repl P D UB UB' d) as Hlen;
    try rewrite Hlen in *.
  - (* s_top *) eapply s_top.
    + exact H.
    + apply (qstp_ctx_all_repl Σ (P++(bind_tm,true,UB,d)::D) d1 d2 H0 P D UB UB' d HUB HUB' HcUB' eq_refl).
  - (* s_tvar_refl *) destruct (Nat.eqb x (length D)) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst x.
      eapply s_tvar_refl.
      * rewrite indexr_prefix_head. reflexivity.
      * apply (qstp_ctx_all_repl Σ (P++(bind_tm,true,UB,d)::D) d1 d2 H0 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + apply Nat.eqb_neq in Ex.
      eapply s_tvar_refl.
      * rewrite <- (indexr_prefix_other P D (bind_tm,true,UB,d) (bind_tm,true,UB',d) x); [exact H|exact Ex].
      * apply (qstp_ctx_all_repl Σ (P++(bind_tm,true,UB,d)::D) d1 d2 H0 P D UB UB' d HUB HUB' HcUB' eq_refl).
  - (* s_tvar_trans *) destruct (Nat.eqb x (length D)) eqn:Ex.
    + apply Nat.eqb_eq in Ex. subst x.
      rewrite indexr_prefix_head in H. inversion H.
    + apply Nat.eqb_neq in Ex.
      eapply s_tvar_trans.
      * rewrite <- (indexr_prefix_other P D (bind_tm,true,UB,d) (bind_tm,true,UB',d) x); [exact H|exact Ex].
      * exact H0.
      * apply (IHstp P D UB UB' d HUB HUB' HcUB' eq_refl).
  - (* s_all *) eapply s_all.
    + exact H.
    + exact H0.
    + apply (qstp_ctx_all_repl Σ (P++(bind_tm,true,UB,d)::D) d5 d6 H1 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + apply (IHstp1 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + pose proof (IHstp2 ((bind_ty,false,T3,d3)::(bind_tm,true,(TAll d1 d2 T1 T2),{♦})::P) D UB UB' d HUB HUB' HcUB' eq_refl) as Hbody.
      replace (T2 <~²ᵀ (P++(bind_tm,true,UB,d)::D)) with (T2 <~²ᵀ (P++(bind_tm,true,UB',d)::D)) in Hbody by (apply open_ty'_ctx_len; rewrite !app_length; reflexivity).
      replace (T4 <~²ᵀ (P++(bind_tm,true,UB,d)::D)) with (T4 <~²ᵀ (P++(bind_tm,true,UB',d)::D)) in Hbody by (apply open_ty'_ctx_len; rewrite !app_length; reflexivity).
      replace (d2 <~²ᵈ (P++(bind_tm,true,UB,d)::D)) with (d2 <~²ᵈ (P++(bind_tm,true,UB',d)::D)) in Hbody by (apply openq'_ctx_len; rewrite !app_length; reflexivity).
      replace (d4 <~²ᵈ (P++(bind_tm,true,UB,d)::D)) with (d4 <~²ᵈ (P++(bind_tm,true,UB',d)::D)) in Hbody by (apply openq'_ctx_len; rewrite !app_length; reflexivity).
      exact Hbody.
  - (* s_base *) eapply s_base.
    apply (qstp_ctx_all_repl Σ (P++(bind_tm,true,UB,d)::D) d1 d2 H P D UB UB' d HUB HUB' HcUB' eq_refl).
  - (* s_ref *) eapply s_ref.
    + apply (qstp_ctx_all_repl Σ (P++(bind_tm,true,UB,d)::D) d1 d2 H P D UB UB' d HUB HUB' HcUB' eq_refl).
    + apply (IHstp1 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + apply (IHstp2 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + apply (qstp_ctx_all_repl Σ (P++(bind_tm,true,UB,d)::D) q1 q2 H2 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + apply (qstp_ctx_all_repl Σ (P++(bind_tm,true,UB,d)::D) q2 q1 H3 P D UB UB' d HUB HUB' HcUB' eq_refl).
  - (* s_fun *) eapply s_fun.
    + exact H.
    + exact H0.
    + apply (qstp_ctx_all_repl Σ (P++(bind_tm,true,UB,d)::D) d5 d6 H1 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + apply (IHstp1 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + pose proof (IHstp2 ((bind_tm,false,T3,d3)::(bind_tm,true,(TFun d1 d2 T1 T2),{♦})::P) D UB UB' d HUB HUB' HcUB' eq_refl) as Hbody.
      replace (T2 <~²ᵀ (P++(bind_tm,true,UB,d)::D)) with (T2 <~²ᵀ (P++(bind_tm,true,UB',d)::D)) in Hbody by (apply open_ty'_ctx_len; rewrite !app_length; reflexivity).
      replace (T4 <~²ᵀ (P++(bind_tm,true,UB,d)::D)) with (T4 <~²ᵀ (P++(bind_tm,true,UB',d)::D)) in Hbody by (apply open_ty'_ctx_len; rewrite !app_length; reflexivity).
      replace (d2 <~²ᵈ (P++(bind_tm,true,UB,d)::D)) with (d2 <~²ᵈ (P++(bind_tm,true,UB',d)::D)) in Hbody by (apply openq'_ctx_len; rewrite !app_length; reflexivity).
      replace (d4 <~²ᵈ (P++(bind_tm,true,UB,d)::D)) with (d4 <~²ᵈ (P++(bind_tm,true,UB',d)::D)) in Hbody by (apply openq'_ctx_len; rewrite !app_length; reflexivity).
      exact Hbody.
  - (* s_trans *) eapply s_trans.
    + apply (IHstp1 P D UB UB' d HUB HUB' HcUB' eq_refl).
    + apply (IHstp2 P D UB UB' d HUB HUB' HcUB' eq_refl).
Qed.

Lemma closed_ty_all_domain : forall b f L d1 d2 T1 T2,
  closed_ty b f L (TAll d1 d2 T1 T2) ->
  closed_ty b f L T1 /\ closed_Qual b f L (Q_lift d1).
Proof. intros. inversion H; subst; auto. Qed.

Lemma closed_ty_fun_domain : forall b f L d1 d2 T1 T2,
  closed_ty b f L (TFun d1 d2 T1 T2) ->
  closed_ty b f L T1 /\ closed_Qual b f L (Q_lift d1).
Proof. intros. inversion H; subst; auto. Qed.

Lemma closed_ty_ref_inv : forall b f L q T,
  closed_ty b f L (TRef q T) ->
  closed_ty b f L T /\ closed_Qual b f L (Q_lift q).
Proof. intros. inversion H; subst; auto. Qed.

Lemma stp_closed_both_nl : forall Γ (Σ:senv) T1 d1 T2 d2,
  no_lookup Γ -> stp Γ Σ T1 d1 T2 d2 ->
  (closed_ty 0 (‖Γ‖) (‖Σ‖) T1 -> closed_ty 0 (‖Γ‖) (‖Σ‖) T2) /\
  (closed_ty 0 (‖Γ‖) (‖Σ‖) T2 -> closed_ty 0 (‖Γ‖) (‖Σ‖) T1).
Proof.
  intros Γ Σ T1 d1 T2 d2 Hnl H. induction H; simpl in *; intros; split; intros Hc.
  - (* s_top forward *) apply cl_TTop.
  - (* s_top backward *) exact H.
  - (* s_tvar_refl *) exfalso. eapply Hnl; eauto.
  - (* s_tvar_refl *) exfalso. eapply Hnl; eauto.
  - (* s_tvar_trans *) exfalso. eapply Hnl; eauto.
  - (* s_tvar_trans *) exfalso. eapply Hnl; eauto.
  - (* s_all forward *) exact H0.
  - (* s_all backward *) exact H.
  - (* s_base forward *) apply cl_TUnit.
  - (* s_base backward *) apply cl_TUnit.
  - (* s_ref forward *)
    destruct (closed_ty_ref_inv 0 (‖Γ‖) (‖Σ‖) q1 T1 Hc) as [Hct1 Hcq1].
    assert (Hct2 : closed_ty 0 (‖Γ‖) (‖Σ‖) T2).
    { eapply (proj2 (IHstp2 Hnl)). exact Hct1. }
    assert (Hcq2 : closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift q2)).
    { eapply qstp_closed_both_nl; [exact Hnl|exact H2|exact H3|exact Hcq1]. }
    eapply cl_TRef; [exact Hct2|exact Hcq2].
  - (* s_ref backward *)
    destruct (closed_ty_ref_inv 0 (‖Γ‖) (‖Σ‖) q2 T2 Hc) as [Hct2 Hcq2].
    assert (Hct1 : closed_ty 0 (‖Γ‖) (‖Σ‖) T1).
    { eapply (proj2 (IHstp1 Hnl)). exact Hct2. }
    assert (Hcq1 : closed_Qual 0 (‖Γ‖) (‖Σ‖) (Q_lift q1)).
    { eapply qstp_closed_both_nl; [exact Hnl|exact H3|exact H2|exact Hcq2]. }
    eapply cl_TRef; [exact Hct1|exact Hcq1].
  - (* s_fun forward *) exact H0.
  - (* s_fun backward *) exact H.
  - (* s_trans forward *)
    eapply (proj1 (IHstp2 Hnl)). eapply (proj1 (IHstp1 Hnl)). exact Hc.
  - (* s_trans backward *)
    eapply (proj2 (IHstp1 Hnl)). eapply (proj2 (IHstp2 Hnl)). exact Hc.
Qed.

Lemma stp_closed_source_nl : forall Γ (Σ:senv) T1 d1 T2 d2,
  no_lookup Γ -> stp Γ Σ T1 d1 T2 d2 ->
  closed_ty 0 (‖Γ‖) (‖Σ‖) T2 -> closed_ty 0 (‖Γ‖) (‖Σ‖) T1.
Proof. intros. eapply (proj2 (stp_closed_both_nl Γ Σ T1 d1 T2 d2 H H0)); exact H1. Qed.

Lemma stp_closed_source_nil : forall (Σ:senv) T1 d1 T2 d2,
  stp [] Σ T1 d1 T2 d2 ->
  closed_ty 0 0 (‖Σ‖) T2 -> closed_ty 0 0 (‖Σ‖) T1.
Proof. intros. exact (stp_closed_source_nl [] Σ T1 d1 T2 d2 no_lookup_nil H H0). Qed.

Lemma closed_ty_all_codomain : forall b f L d1 d2 T1 T2,
  closed_ty b f L (TAll d1 d2 T1 T2) ->
  closed_ty (S (S b)) f L T2 /\ closed_Qual (S (S b)) f L (Q_lift d2).
Proof. intros. inversion H; subst; auto. Qed.

Lemma closed_ty_fun_codomain : forall b f L d1 d2 T1 T2,
  closed_ty b f L (TFun d1 d2 T1 T2) ->
  closed_ty (S (S b)) f L T2 /\ closed_Qual (S (S b)) f L (Q_lift d2).
Proof. intros. inversion H; subst; auto. Qed.

Lemma qstp_tenv_weaken_closed : forall (Σ:senv) q d,
  closed_Qual 0 0 (‖Σ‖) (Q_lift q) ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift d) ->
  qstp [] Σ q d ->
  forall Γ, qstp Γ Σ q d.
Proof.
  intros Σ q d Hq Hd H Γ.
  pose proof (qstp_nil_subq nil Σ q d eq_refl H) as Hsub.
  eapply qs_sq.
  - exact Hsub.
  - eapply closed_Qual_weaken; [exact Hd|lia|lia].
Qed.

Lemma qstp_tenv_weaken_closed_nil : forall (Σ:senv) q d,
  closed_Qual 0 0 (‖Σ‖) (Q_lift q) ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift d) ->
  qstp [] Σ q d -> qstp [] Σ q d.
Proof. intros. exact H1. Qed.

Lemma vtp_abs_sfun_retarget : forall (Σ:senv) ϰ φ t sd sq SD SB d5
  td tq TD TB d6,
  vtp Σ ϰ φ (tabs t) (TFun sd sq SD SB) d5 ->
  closed_ty 0 0 (‖Σ‖) (TFun sd sq SD SB) ->
  closed_ty 0 0 (‖Σ‖) (TFun td tq TD TB) ->
  qstp [] Σ d5 d6 ->
  stp [] Σ TD td SD sd ->
  stp [(bind_tm,false,TD,td);(bind_tm,true,(TFun sd sq SD SB),{♦})] Σ
    (SB <~²ᵀ ([]:tenv)) (sq <~²ᵈ ([]:tenv)) (TB <~²ᵀ ([]:tenv)) (tq <~²ᵈ ([]:tenv)) ->
  d6 ⊑↑ (qor φ {♦}) ->
  closed_Qual 0 0 (‖Σ‖) (Q_lift d6) ->
  kill_sep ϰ φ -> local_locs t = ∅ ->
  vtp Σ ϰ φ (tabs t) (TFun td tq TD TB) d6.
Proof.
  intros Σ ϰ φ t sd sq SD SB d5 td tq TD TB d6 Hv Hcsrc Hctgt Hq Hdom Hbody Hsub Hcl Hk HL.
  inversion Hv; subst.
  assert (HctTD : closed_ty 0 0 (‖Σ‖) TD).
  { destruct (closed_ty_fun_domain 0 0 (‖Σ‖) td tq TD TB Hctgt) as [Hc _]. exact Hc. }
  assert (Hctd : closed_Qual 0 0 (‖Σ‖) (Q_lift td)).
  { destruct (closed_ty_fun_domain 0 0 (‖Σ‖) td tq TD TB Hctgt) as [_ Hc]. exact Hc. }
  assert (Hcsd : closed_Qual 0 0 (‖Σ‖) (Q_lift sd)).
  { destruct (closed_ty_fun_domain 0 0 (‖Σ‖) sd sq SD SB Hcsrc) as [_ Hc]. exact Hc. }
  assert (Hsubt : td ⊑↑ sd).
  { apply (qstp_nil_subq nil Σ td sd eq_refl). eapply stp_qstp; exact Hdom. }
  eapply vtp_abs.
  - exact H4.
  - exact Hcl.
  - exact Hctgt.
  - exact H7.
  - exact H8.
  - eapply s_trans; [exact Hdom|exact H9].
  - eapply qs_trans; [exact H10|exact Hq].
  - pose proof (stp_ctx_false_repl Σ ((bind_tm,false,SD,sd)::(bind_tm,true,(TFun d1 d2 T1 T2),{♦})::nil)
      (T2 <~²ᵀ ([]:tenv)) (d2 <~²ᵈ ([]:tenv)) (SB <~²ᵀ ([]:tenv)) (sq <~²ᵈ ([]:tenv)) H14
      nil ((bind_tm,true,(TFun d1 d2 T1 T2),{♦})::nil) SD sd TD td
      HctTD Hctd Hcsd Hsubt eq_refl) as A.
    pose proof (stp_ctx_fun_repl Σ ((bind_tm,false,TD,td)::(bind_tm,true,(TFun sd sq SD SB),{♦})::nil)
      (SB <~²ᵀ ([]:tenv)) (sq <~²ᵈ ([]:tenv)) (TB <~²ᵀ ([]:tenv)) (tq <~²ᵈ ([]:tenv)) Hbody
      ((bind_tm,false,TD,td)::nil) nil (TFun sd sq SD SB) (TFun d1 d2 T1 T2) {♦}
      (ex_intro _ sd (ex_intro _ sq (ex_intro _ SD (ex_intro _ SB eq_refl))))
      (ex_intro _ d1 (ex_intro _ d2 (ex_intro _ T1 (ex_intro _ T2 eq_refl)))) H7 eq_refl) as B.
    eapply s_trans; [exact A|exact B].
  - exact H15.
  - exact H17.
  - eapply kill_sep_subq_or_diamond; [exact Hk|exact Hsub].
  - simpl in HL. rewrite HL. apply kill_sep_empty_l.
Qed.

(* ===== End partial proof infrastructure ===== *)

Theorem type_safety: forall {Σ ϰ t T d φ},
  has_type [] φ Σ t T d -> wf_senv Σ -> wf_step t -> (
    value t \/
    (forall {σ} , CtxOK [] φ Σ ϰ σ -> wf_store σ ->
      (exists t' σ',
        step t σ t' σ' /\ preserve [] Σ ϰ φ (local_locs t) t' T d σ'
      )
    )
  ).
