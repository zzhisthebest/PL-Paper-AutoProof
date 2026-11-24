Require Export Arith.EqNat.

Require Export PeanoNat.

Require Import Coq.Arith.Arith.

Require Import Coq.Bool.Bool.

Require Import Coq.Program.Equality.

Require Import Coq.Lists.List.

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

Local Ltac qual_simpl :=
  cbn [closed_Qual closed_Nats Subq N_sub kill_sep qdom qdom' qmem
       Q_lift qfresh qfvs qbvs qlocs N_lift qand qor qdiff
       q_empty n_empty n_one n_and n_or n_diff n_dom n_dom'
       fst snd] in *.

Local Lemma safety_indexr_bound {A} (xs : list A) k x :
  indexr k xs = Some x -> k < length xs.
Proof.
  induction xs as [|a xs IH]; simpl; [discriminate|].
  destruct (k =? length xs) eqn:Heq.
  - apply Nat.eqb_eq in Heq. lia.
  - intros H. specialize (IH H). lia.
Qed.

Local Lemma safety_indexr_exists {A} (xs : list A) k :
  k < length xs -> exists x, indexr k xs = Some x.
Proof.
  induction xs as [|a xs IH]; simpl; [lia|].
  destruct (k =? length xs) eqn:Heq.
  - eauto.
  - apply Nat.eqb_neq in Heq. intros H. apply IH. lia.
Qed.

Local Lemma safety_sindexr {A} (ss : list (list A)) l o x :
  sindexr l o ss = Some x ->
  exists s, indexr l ss = Some s /\ indexr o s = Some x.
Proof.
  induction ss as [|s ss IH]; simpl; [discriminate|].
  destruct (l =? length ss); eauto.
Qed.

Local Lemma safety_closed_qstp Σ d d' :
  qstp [] Σ d d' -> d ⊑↑ d'.
Proof.
  intros H. remember ([] : tenv) as Γ eqn:HΓ.
  induction H; subst; try discriminate; auto.
  - specialize (IHqstp eq_refl).
    qual_simpl. destruct IHqstp as (HF & Hfv & Hbv & Hl).
    repeat split.
    + change (Is_true (qfresh q || qfresh d1) -> Is_true (qfresh q || qfresh d2)).
      change (Is_true (qfresh d1) -> Is_true (qfresh d2)) in HF.
      destruct (qfresh q), (qfresh d1), (qfresh d2); simpl in *; tauto.
    + intros x. change (n_or (qfvs q) (qfvs d1) x = true -> n_or (qfvs q) (qfvs d2) x = true).
      unfold n_or. rewrite !orb_true_iff. specialize (Hfv x). tauto.
    + intros x. change (n_or (qbvs q) (qbvs d1) x = true -> n_or (qbvs q) (qbvs d2) x = true).
      unfold n_or. rewrite !orb_true_iff. specialize (Hbv x). tauto.
    + intros x. change (n_or (qlocs q) (qlocs d1) x = true -> n_or (qlocs q) (qlocs d2) x = true).
      unfold n_or. rewrite !orb_true_iff. specialize (Hl x). tauto.
  - specialize (IHqstp1 eq_refl). specialize (IHqstp2 eq_refl).
    qual_simpl. destruct IHqstp1 as (? & ? & ? & ?).
    destruct IHqstp2 as (? & ? & ? & ?). firstorder.
Qed.

Local Lemma safety_subqual_of_stp Σ T d T' d' :
  stp [] Σ T d T' d' -> d ⊑↑ d'.
Proof.
  intros H. remember ([] : tenv) as Γ eqn:HΓ.
  induction H; subst; try discriminate; eauto using safety_closed_qstp.
  specialize (IHstp1 eq_refl). specialize (IHstp2 eq_refl).
  qual_simpl. destruct IHstp1 as (? & ? & ? & ?).
  destruct IHstp2 as (? & ? & ? & ?). firstorder.
Qed.

Local Definition safety_type_head (T : ty) : nat :=
  match T with
  | TTop => 0
  | TVar _ => 1
  | TUnit => 2
  | TAll _ _ _ _ => 3
  | TFun _ _ _ _ => 4
  | TRef _ _ => 5
  end.

Local Lemma safety_stp_head Σ T S d e :
  stp [] Σ T d S e -> safety_type_head S <> 0 ->
  safety_type_head T = safety_type_head S.
Proof.
  intros H. remember ([] : tenv) as Γ eqn:HΓ.
  induction H; subst; simpl in *; try discriminate; try congruence.
  intros Hn. specialize (IHstp2 eq_refl Hn).
  rewrite <- IHstp2. apply IHstp1; congruence.
Qed.

Local Definition safety_value_head (t : tm) : nat :=
  match t with
  | tunit => 2
  | ttabs _ => 3
  | tabs _ => 4
  | tloc _ _ => 5
  | _ => 0
  end.

Local Lemma safety_typed_value_head φ Σ t T d :
  has_type [] φ Σ t T d -> value t -> safety_type_head T <> 0 ->
  safety_value_head t = safety_type_head T.
Proof.
  intros H. remember ([] : tenv) as Γ eqn:HΓ.
  induction H; subst; simpl in *; intros Hv Hn;
    try reflexivity; try solve [inversion Hv].
  pose proof (safety_stp_head _ _ _ _ _ H0 Hn) as Heq.
  rewrite <- Heq. apply IHhas_type; congruence.
Qed.

Local Lemma safety_loc_lookup φ Σ l o T d :
  has_type [] φ Σ &(l,o) T d ->
  l ∈ₗ φ /\ exists U q, sindexr l o Σ = Some (U,q).
Proof.
  intros H. remember ([] : tenv) as Γ eqn:HΓ.
  remember (&(l,o)) as v eqn:Hv.
  induction H; subst; try discriminate; eauto.
  inversion Hv; subst. split; [|eauto].
  destruct H3 as (_ & _ & _ & Hl).
  apply Hl. apply Nat.eqb_refl.
Qed.

Local Lemma safety_live_lookup Σ ϰ φ σ t T d l o :
  CtxOK [] φ Σ ϰ σ -> has_type [] φ Σ t T d -> t = &(l,o) ->
  exists s v, indexr l σ = Some (Some s) /\ indexr o s = Some v.
Proof.
  intros (Hd & Hlen & Hφ & Hϰ & Hsep & Hctx) Hty ->.
  destruct (safety_loc_lookup _ _ _ _ _ _ Hty) as (Hl & U & q & Hcell).
  destruct (safety_sindexr _ _ _ _ Hcell) as (sU & HsU & Hq).
  assert (Hnot : ~ l ∈ₗ ϰ).
  { intro Hdead. destruct Hsep as (_ & _ & _ & Hsep).
    specialize (Hsep l). change (n_and (qlocs φ) (qlocs ϰ) l = true -> false = true) in Hsep.
    change (qlocs φ l = true) in Hl. change (qlocs ϰ l = true) in Hdead.
    unfold n_and in Hsep. rewrite Hl, Hdead in Hsep. discriminate (Hsep eq_refl). }
  destruct (Hctx l o sU U q) as (_ & Hlive).
  destruct (Hlive Hnot Hl HsU) as (s & (Hs & _) & Hget).
  destruct (Hget Hq) as (v & Hv & _).
  eauto.
Qed.

Local Lemma safety_subscope_ctx Σ ϰ φ ψ σ :
  ψ ⊑↑ φ -> CtxOK [] φ Σ ϰ σ -> CtxOK [] ψ Σ ϰ σ.
Proof.
  intros Hsub (Hdom & Hlen & Hφ & Hϰ & Hsep & Hstore).
  destruct Hsub as (HF & Hfv & Hbv & Hl).
  refine (conj Hdom (conj Hlen (conj _ (conj Hϰ (conj _ _))))).
  - destruct Hφ as (? & ? & ? & ?).
    unfold Subq in *. firstorder.
  - destruct Hsep as (_ & Hsf & Hsb & Hsl).
    unfold kill_sep, Subq.
    split; [intros _; exact I|].
    split; [|split].
    + intros x Hx. apply (Hsf x).
      change (qfvs ψ x && qfvs ϰ x = true) in Hx.
      change (qfvs φ x && qfvs ϰ x = true).
      apply andb_true_iff in Hx as [Hψ Hϰx].
      rewrite (Hfv x Hψ), Hϰx. reflexivity.
    + intros x Hx. apply (Hsb x).
      change (qbvs ψ x && qbvs ϰ x = true) in Hx.
      change (qbvs φ x && qbvs ϰ x = true).
      apply andb_true_iff in Hx as [Hψ Hϰx].
      rewrite (Hbv x Hψ), Hϰx. reflexivity.
    + intros x Hx. apply (Hsl x).
      change (qlocs ψ x && qlocs ϰ x = true) in Hx.
      change (qlocs φ x && qlocs ϰ x = true).
      apply andb_true_iff in Hx as [Hψ Hϰx].
      rewrite (Hl x Hψ), Hϰx. reflexivity.
  - intros l o cty T q.
    destruct (Hstore l o cty T q) as [Hdead Hlive].
    split; [exact Hdead|].
    intros Hnot Hmem Hlook.
    destruct (Hlive Hnot (Hl l Hmem) Hlook) as (ctm & Hctm & Hvalue).
    exists ctm. split; [exact Hctm|].
    intros Hcell. destruct (Hvalue Hcell) as (v & Hv & Hval & Hvtp).
    exists v. repeat split; try assumption.
    intros Hqs.
    assert (Hq : q ⊑↑ φ).
    { destruct Hqs as (? & ? & ? & ?). unfold Subq in *. firstorder. }
    specialize (Hvtp Hq).
    clear - Hvtp Hqs.
    induction Hvtp; eauto using vtp.
    eapply vtp_loc with (q1 := q1); try eassumption.
    destruct (safety_closed_qstp _ _ _ H7) as (_ & _ & _ & Hd).
    destruct Hqs as (_ & _ & _ & Hqs).
    apply Hqs, Hd, Nat.eqb_refl.
Qed.

Local Lemma safety_diff_le φ K : qdiff φ K ⊑↑ φ.
Proof.
  unfold Subq. split.
  - change (Is_true (qfresh φ && negb (qfresh K)) -> Is_true (qfresh φ)).
    destruct (qfresh φ); simpl; auto.
  - repeat split; intros x Hx;
      apply andb_true_iff in Hx as [Hx _]; exact Hx.
Qed.

(* Store compatibility provides a live arena and an in-bounds offset whenever a typed reference is used. *)
Local Lemma safety_progress Σ φ ϰ σ t T d :
  has_type [] φ Σ t T d -> CtxOK [] φ Σ ϰ σ ->
  value t \/ exists t' σ', step t σ t' σ'.
Proof.
  intros H. remember ([] : tenv) as Γ eqn:HΓ.
  induction H; subst; intros HC; try discriminate;
    try solve [left; constructor];
    try solve [eauto].
  all: right.
  - destruct (IHhas_type eq_refl HC) as [Hv | (t' & σ' & Hstep)].
    + pose proof (safety_typed_value_head _ _ _ _ _ H Hv ltac:(discriminate)) as Hshape.
      destruct t; simpl in Hshape; try discriminate.
      eauto using step_ttapp.
    + eauto using step_c_tapp.
  - destruct (IHhas_type eq_refl HC) as [Hv | (t' & σ' & Hstep)].
    + pose proof (safety_typed_value_head _ _ _ _ _ H Hv ltac:(discriminate)) as Hshape.
      destruct t; simpl in Hshape; try discriminate.
      eauto using step_ttapp.
    + eauto using step_c_tapp.
  - destruct (IHhas_type1 eq_refl HC) as [Hv | (t' & σ' & Hstep)].
    + destruct (IHhas_type2 eq_refl (safety_subscope_ctx _ _ _ _ _ (safety_diff_le _ _) HC))
        as [Hv2 | (t' & σ' & Hstep)].
      * pose proof (safety_typed_value_head _ _ _ _ _ H Hv ltac:(discriminate)) as Hshape.
        destruct t1; simpl in Hshape; try discriminate.
        eauto using step_beta.
      * eauto using step_c_app_r.
    + eauto using step_c_app_l.
  - destruct (IHhas_type1 eq_refl HC) as [Hv | (t' & σ' & Hstep)].
    + destruct (IHhas_type2 eq_refl (safety_subscope_ctx _ _ _ _ _ (safety_diff_le _ _) HC))
        as [Hv2 | (t' & σ' & Hstep)].
      * pose proof (safety_typed_value_head _ _ _ _ _ H Hv ltac:(discriminate)) as Hshape.
        destruct t1; simpl in Hshape; try discriminate.
        eauto using step_beta.
      * eauto using step_c_app_r.
    + eauto using step_c_app_l.
  - destruct (IHhas_type eq_refl HC) as [Hv | (t' & σ' & Hstep)];
      eauto using step_ref, step_c_ref.
  - destruct (IHhas_type2 eq_refl HC) as [Hv | (t' & σ' & Hstep)].
    + destruct (IHhas_type1 eq_refl (safety_subscope_ctx _ _ _ _ _ (safety_diff_le _ _) HC))
        as [Hv1 | (t' & σ' & Hstep)].
      * pose proof (safety_typed_value_head _ _ _ _ _ H1 Hv ltac:(discriminate)) as Hshape.
        destruct t2; simpl in Hshape; try discriminate.
        destruct (safety_live_lookup _ _ _ _ _ _ _ _ _ HC H1 eq_refl) as (s & v & Hs & _).
        eauto using step_refat.
      * eauto using step_c_refat_l.
    + eauto using step_c_refat_r.
  - destruct (IHhas_type eq_refl HC) as [Hv | (t' & σ' & Hstep)].
    + pose proof (safety_typed_value_head _ _ _ _ _ H Hv ltac:(discriminate)) as Hshape.
      destruct t; simpl in Hshape; try discriminate.
      destruct (safety_live_lookup _ _ _ _ _ _ _ _ _ HC H eq_refl) as (s & v & Hs & Hvs).
      eauto using step_deref.
    + eauto using step_c_deref.
  - destruct (IHhas_type1 eq_refl HC) as [Hv | (t' & σ' & Hstep)].
    + destruct (IHhas_type2 eq_refl (safety_subscope_ctx _ _ _ _ _ (safety_diff_le _ _) HC))
        as [Hv2 | (t' & σ' & Hstep)].
      * pose proof (safety_typed_value_head _ _ _ _ _ H Hv ltac:(discriminate)) as Hshape.
        destruct t1; simpl in Hshape; try discriminate.
        destruct (safety_live_lookup _ _ _ _ _ _ _ _ _ HC H eq_refl) as (s & v & Hs & Hvs).
        eexists _, _. eapply step_assign with (s := s); eauto using safety_indexr_bound.
      * eauto using step_c_assign_r.
    + eauto using step_c_assign_l.
  - destruct (IHhas_type1 eq_refl HC) as [Hv | (t' & σ' & Hstep)];
      eauto using step_twithr, step_c_twithr_l.
  - destruct (IHhas_type eq_refl HC) as [Hv | (t' & σ' & Hstep)];
      eauto using step_twithc, step_c_twithc.
Qed.

Local Lemma safety_no_scopes t :
  (forall l, ~ l ∈ₗ local_locs t) ->
  local_locs t = ∅ /\ wf_step t.
Proof.
  induction t; simpl; intros H;
    try solve [split; [reflexivity|exact I]];
    try solve [apply IHt; exact H];
    try solve [destruct (IHt H) as [Heq _]; auto].
  all: try match goal with
  | |- (?a ⊔ ?b) = ∅ /\ _ =>
    let Hl := fresh "Hl" in let Hr := fresh "Hr" in
    assert (Hl : forall l, ~ l ∈ₗ a)
      by (intros l Hmem; apply (H l); apply orb_true_iff; left; exact Hmem);
    assert (Hr : forall l, ~ l ∈ₗ b)
      by (intros l Hmem; apply (H l); apply orb_true_iff; right; exact Hmem);
    destruct (IHt1 Hl) as [Hleft Wleft];
    destruct (IHt2 Hr) as [Hright Wright];
    rewrite Hleft, Hright; repeat split; try assumption; auto
  end.
  exfalso. apply (H l), orb_true_iff. left. apply Nat.eqb_refl.
Qed.

Local Lemma safety_empty_scopes_wf t : local_locs t = ∅ -> wf_step t.
Proof.
  intro H. apply safety_no_scopes. rewrite H. discriminate.
Qed.

Local Lemma safety_open_scopes t k u :
  local_locs u = ∅ -> local_locs ([[k ~> u]]ᵗ t) = local_locs t.
Proof.
  revert k. induction t; intros k Hu; simpl; try rewrite ?IHt, ?IHt1, ?IHt2 by assumption;
    try reflexivity.
  destruct v; simpl; [reflexivity|].
  destruct (k =? i); auto.
Qed.

Local Lemma safety_value_scopes v :
  value v -> wf_step v -> local_locs v = ∅.
Proof. intros H; inversion H; simpl; auto. Qed.

Local Lemma safety_sindexr_store {A} (ss : list (option (list A))) l o s :
  indexr l ss = Some (Some s) -> sindexr' l o ss = indexr o s.
Proof.
  induction ss as [|a ss IH]; simpl; [discriminate|].
  destruct (l =? length ss).
  - intros H. inversion H. reflexivity.
  - apply IH.
Qed.

Local Lemma safety_indexr_update {A} (xs : list A) l k v :
  indexr k (update xs l v) =
    if k =? l then option_map (fun _ => v) (indexr k xs) else indexr k xs.
Proof.
  assert (Hlen : forall ys : list A, length (update ys l v) = length ys).
  { induction ys; simpl; auto. destruct (l =? length ys); simpl; congruence. }
  induction xs as [|a xs IH]; simpl.
  - destruct (k =? l); reflexivity.
  - destruct (l =? length xs) eqn:Hl; simpl.
    + apply Nat.eqb_eq in Hl. subst.
      destruct (k =? length xs); reflexivity.
    + rewrite Hlen. destruct (k =? length xs) eqn:Hk; [|exact IH].
      apply Nat.eqb_eq in Hk. subst. rewrite Nat.eqb_sym, Hl. reflexivity.
Qed.

Local Lemma safety_lookup_store {A} (ss : list (option (list A))) l o :
  sindexr' l o ss =
    match indexr l ss with Some s => indexr' o s | None => None end.
Proof.
  induction ss as [|a ss IH]; simpl; auto.
  destruct (l =? length ss); auto.
Qed.

Local Lemma safety_update_store_wf σ l :
  wf_store σ -> wf_store (update σ l None).
Proof.
  intros Hs k o v H.
  rewrite safety_lookup_store, safety_indexr_update in H.
  destruct (k =? l).
  - destruct (indexr k σ); discriminate.
  - apply (Hs k o v). rewrite safety_lookup_store. exact H.
Qed.

Local Lemma safety_cons_store_wf σ v :
  wf_step v -> value v -> wf_store σ -> wf_store (Some [v] :: σ).
Proof.
  intros Hwf Hval Hs l o w H.
  simpl in H. destruct (l =? length σ); [|eauto].
  simpl in H. destruct (o =? 0); inversion H; subst; auto.
Qed.

Local Lemma safety_supdate_as_update {A} (ss : list (option (list A))) l o s v :
  indexr l ss = Some (Some s) ->
  supdate ss l o v = update ss l (Some (update s o v)).
Proof.
  induction ss as [|a ss IH]; simpl; [discriminate|].
  destruct (l =? length ss).
  - intros H. inversion H. reflexivity.
  - intros H. now rewrite (IH H).
Qed.

Local Lemma safety_cinsert_as_update {A} (ss : list (option (list A))) l s v :
  indexr l ss = Some (Some s) ->
  cinsert ss l v = update ss l (Some (v :: s)).
Proof.
  induction ss as [|a ss IH]; simpl; [discriminate|].
  destruct (l =? length ss).
  - intros H. inversion H. reflexivity.
  - intros H. now rewrite (IH H).
Qed.

Local Lemma safety_change_cell_wf σ l s s' :
  indexr l σ = Some (Some s) ->
  (forall o v, indexr o s' = Some v ->
    indexr o s = Some v \/ (wf_step v /\ value v)) ->
  wf_store σ -> wf_store (update σ l (Some s')).
Proof.
  intros Hs Hchanged Hσ k o v Hv.
  rewrite safety_lookup_store, safety_indexr_update in Hv.
  destruct (k =? l) eqn:Hk.
  - apply Nat.eqb_eq in Hk. subst k. rewrite Hs in Hv.
    destruct (Hchanged o v Hv) as [Hold | Hwf]; [|exact Hwf].
    apply (Hσ l o v). rewrite (safety_sindexr_store _ _ _ _ Hs). exact Hold.
  - apply (Hσ k o v). rewrite safety_lookup_store. exact Hv.
Qed.

Local Lemma safety_step_wf t σ t' σ' :
  step t σ t' σ' -> wf_step t -> wf_store σ -> wf_step t' /\ wf_store σ'.
Proof.
  intros H. induction H; simpl; intros Hw Hs.
  - split; [|exact Hs].
    apply safety_empty_scopes_wf. unfold open_tm.
    rewrite !safety_open_scopes; simpl; auto.
  - destruct Hw as (Ht & Hv & _).
    split; [|exact Hs].
    apply safety_empty_scopes_wf. unfold open_tm.
    rewrite !safety_open_scopes; simpl; eauto using safety_value_scopes.
  - split; [exact I|eauto using safety_cons_store_wf].
  - destruct Hw as (Hv & _ & _). split; [exact I|].
    rewrite (safety_cinsert_as_update _ _ _ _ H0).
    eapply safety_change_cell_wf; [exact H0| |exact Hs].
    simpl. intros o' w.
    destruct (o' =? length s); [intros Heq; inversion Heq; subst; auto|auto].
  - split; [|exact Hs].
    assert (Hlookup : sindexr' l o σ = Some v).
    { rewrite (safety_sindexr_store _ _ _ _ H). exact H0. }
    exact (proj1 (Hs _ _ _ Hlookup)).
  - destruct Hw as (_ & Hv & _). split; [exact I|].
    rewrite (safety_supdate_as_update _ _ _ _ _ H0).
    eapply safety_change_cell_wf; [exact H0| |exact Hs].
    intros o' w. rewrite safety_indexr_update.
    destruct (o' =? o); [|auto].
    destruct (indexr o' s); [intros Heq; inversion Heq; subst; auto|discriminate].
  - destruct Hw as (Hv & Ht & Hlocal).
    split; [|eauto using safety_cons_store_wf].
    apply safety_empty_scopes_wf. unfold open_tm.
    now rewrite !safety_open_scopes.
  - split; [exact Hw|eauto using safety_update_store_wf].
  - now apply IHstep.
  - now apply IHstep.
  - destruct Hw as (H1 & H2 & _).
    destruct (IHstep H1 Hs) as [H1' Hs'].
    auto.
  - destruct Hw as (H1 & H2 & [Hloc | Hval]).
    + destruct (IHstep H2 Hs) as [H2' Hs']. auto.
    + inversion H; subst; inversion Hval.
  - now apply IHstep.
  - destruct Hw as (H1 & H2 & [Hv | Hloc]).
    + inversion H; subst; inversion Hv.
    + destruct (IHstep H1 Hs) as [H1' Hs']. auto.
  - destruct Hw as (H1 & H2 & _).
    destruct (IHstep H2 Hs) as [H2' Hs']. auto.
  - destruct Hw as (H1 & H2 & [Hv | Hloc]).
    + inversion H; subst; inversion Hv.
    + destruct (IHstep H1 Hs) as [H1' Hs']. auto.
  - destruct Hw as (H1 & H2 & _).
    destruct (IHstep H2 Hs) as [H2' Hs']. auto.
  - destruct Hw as (H1 & H2 & Hloc).
    destruct (IHstep H1 Hs) as [H1' Hs']. auto.
  - now apply IHstep.
Qed.

Local Lemma safety_senv_length Σ Σ' :
  Σ' ⊇₂ Σ -> length Σ <= length Σ'.
Proof.
  intros Hext.
  destruct Σ as [|c Σ]; [simpl; lia|].
  assert (Hlook : indexr (length Σ) (c :: Σ) = Some c)
    by (simpl; rewrite Nat.eqb_refl; reflexivity).
  destruct (Hext _ _ Hlook) as (c' & Hc' & _).
  pose proof (safety_indexr_bound _ _ _ Hc'). simpl. lia.
Qed.

Local Lemma safety_indexr_prefix {A} (ys xs : list A) k x :
  indexr k xs = Some x -> indexr k (ys ++ xs) = Some x.
Proof.
  intros H. pose proof (safety_indexr_bound _ _ _ H).
  induction ys; simpl; auto.
  rewrite length_app.
  assert (k =? length ys + length xs = false)
    by (apply Nat.eqb_neq; lia).
  now rewrite H1.
Qed.

Local Lemma safety_sindexr_intro {A} (ss : list (list A)) l o s x :
  indexr l ss = Some s -> indexr o s = Some x ->
  sindexr l o ss = Some x.
Proof.
  induction ss as [|a ss IH]; simpl; [discriminate|].
  destruct (l =? length ss) eqn:Hl.
  - intros H. inversion H; auto.
  - apply IH.
Qed.

Local Lemma safety_sindexr_weaken Σ Σ' l o x :
  Σ' ⊇₂ Σ -> sindexr l o Σ = Some x -> sindexr l o Σ' = Some x.
Proof.
  intros Hext Hx.
  destruct (safety_sindexr _ _ _ _ Hx) as (c & Hc & Ho).
  destruct (Hext _ _ Hc) as (c' & Hc' & ys & ->).
  eapply safety_sindexr_intro; eauto using safety_indexr_prefix.
Qed.

Local Lemma safety_locs_closed_weaken b f l l' q :
  l <= l' -> closed_Qual b f l q -> closed_Qual b f l' q.
Proof.
  intros Hle (Hf & Hb & Hl).
  split; [exact Hf|]. split; [exact Hb|].
  intros k Hk. specialize (Hl k Hk). lia.
Qed.

Local Lemma safety_ty_closed_weaken b f l l' T :
  l <= l' -> closed_ty b f l T -> closed_ty b f l' T.
Proof.
  intros Hle H. induction H; constructor; eauto using safety_locs_closed_weaken.
Qed.

Local Lemma safety_tm_closed_weaken b f l l' t :
  l <= l' -> closed_tm b f l t -> closed_tm b f l' t.
Proof.
  intros Hle H. induction H; eauto using closed_tm, Nat.lt_le_trans.
Qed.

Local Lemma safety_qstp_weaken Γ Σ Σ' q d :
  Σ' ⊇₂ Σ -> qstp Γ Σ q d -> qstp Γ Σ' q d.
Proof.
  intros Hext H.
  pose proof (safety_senv_length _ _ Hext).
  induction H; eauto using qstp, safety_locs_closed_weaken, safety_ty_closed_weaken.
Qed.

Local Lemma safety_stp_weaken Γ Σ Σ' T d U e :
  Σ' ⊇₂ Σ -> stp Γ Σ T d U e -> stp Γ Σ' T d U e.
Proof.
  intros Hext H.
  pose proof (safety_senv_length _ _ Hext).
  induction H; [eapply s_top | eapply s_tvar_refl | eapply s_tvar_trans |
    eapply s_all | eapply s_base | eapply s_ref | eapply s_fun | eapply s_trans];
    eauto using safety_qstp_weaken, safety_ty_closed_weaken.
Qed.

Local Lemma safety_typing_weaken Γ φ Σ Σ' t T d :
  Σ' ⊇₂ Σ -> has_type Γ φ Σ t T d -> has_type Γ φ Σ' t T d.
Proof.
  intros Hext H.
  pose proof (safety_senv_length _ _ Hext).
  induction H; [eapply t_tabs | eapply t_tapp | eapply t_tapp_fresh |
    eapply t_base | eapply t_var | eapply t_abs | eapply t_app |
    eapply t_app_fresh | eapply t_loc | eapply t_ref | eapply t_refat |
    eapply t_deref | eapply t_assign | eapply t_sub | eapply t_withr | eapply t_withc];
    eauto using safety_locs_closed_weaken, safety_ty_closed_weaken,
      safety_tm_closed_weaken, safety_sindexr_weaken, safety_stp_weaken, Nat.lt_le_trans.
Qed.

Local Lemma safety_vtp_weaken Σ Σ' ϰ φ v T d :
  Σ' ⊇₂ Σ -> vtp Σ ϰ φ v T d -> vtp Σ' ϰ φ v T d.
Proof.
  intros Hext H.
  pose proof (safety_senv_length _ _ Hext).
  induction H; [eapply vtp_tabs | eapply vtp_base | eapply vtp_loc with (q1 := q1) |
    eapply vtp_abs | eapply vtp_top];
    eauto using safety_locs_closed_weaken, safety_ty_closed_weaken,
      safety_tm_closed_weaken, safety_sindexr_weaken, safety_stp_weaken,
      safety_qstp_weaken, safety_typing_weaken.
Qed.

Local Lemma safety_subq_refl a : a ⊑↑ a.
Proof. unfold Subq, N_sub. intuition. Qed.

Local Lemma safety_subq_trans a b c :
  a ⊑↑ b -> b ⊑↑ c -> a ⊑↑ c.
Proof. unfold Subq, N_sub. firstorder. Qed.

Local Lemma safety_qual_le a b :
  a ⊑↑ b <->
  (qfresh a = true -> qfresh b = true) /\
  n_sub (qfvs a) (qfvs b) /\
  n_sub (qbvs a) (qbvs b) /\
  n_sub (qlocs a) (qlocs b).
Proof.
  unfold Subq, N_sub, n_sub, Q_lift, N_lift.
  cbn [qfresh qfvs qbvs qlocs fst snd].
  destruct (qfresh a), (qfresh b); simpl; intuition congruence.
Qed.

Local Ltac safety_qpoint :=
  repeat rewrite safety_qual_le in *;
  unfold closed_Qual, closed_Nats, kill_sep in *;
  repeat rewrite safety_qual_le in *;
  unfold n_sub, qmem, Q_lift, N_lift, qor, qand, qdiff, q_empty,
    n_empty, n_one, n_diff, n_or, n_and in *;
  cbn [qfresh qfvs qbvs qlocs fst snd] in *;
  repeat first [setoid_rewrite andb_true_iff | setoid_rewrite orb_true_iff
               | setoid_rewrite negb_true_iff | setoid_rewrite Nat.eqb_eq
               | match goal with H : _ |- _ =>
                   first [setoid_rewrite andb_true_iff in H
                         | setoid_rewrite orb_true_iff in H
                         | setoid_rewrite negb_true_iff in H
                         | setoid_rewrite Nat.eqb_eq in H]
                 end];
  try firstorder congruence.

Local Lemma safety_join_l a b : a ⊑↑ a ⊔ b.
Proof. safety_qpoint. Qed.

Local Lemma safety_join_r a b : b ⊑↑ a ⊔ b.
Proof. safety_qpoint. Qed.

Local Lemma safety_join_bound a b c :
  a ⊑↑ c -> b ⊑↑ c -> a ⊔ b ⊑↑ c.
Proof. safety_qpoint. Qed.

Local Lemma safety_empty_bound a : ∅ ⊑↑ a.
Proof. safety_qpoint. Qed.

Local Lemma safety_diff_ambient φ ψ K :
  φ ⊑↑ ψ -> qdiff φ K ⊑↑ qdiff ψ K.
Proof. safety_qpoint. Qed.

Local Lemma safety_qual_closed_of_sub b f l a c :
  a ⊑↑ c -> closed_Qual b f l c↑ -> closed_Qual b f l a↑.
Proof. safety_qpoint. Qed.

Local Lemma safety_qual_join_closed b f l a c :
  closed_Qual b f l a↑ -> closed_Qual b f l c↑ ->
  closed_Qual b f l (a ⊔ c)↑.
Proof. safety_qpoint. Qed.

Local Lemma safety_qual_const_closed b f l fresh :
  closed_Qual b f l (∅{fresh})↑.
Proof. safety_qpoint. Qed.

Local Lemma safety_typing_phi_closed Γ φ Σ t T d :
  has_type Γ φ Σ t T d -> closed_Qual 0 (length Γ) (length Σ) φ↑.
Proof. intros H. induction H; assumption. Qed.

Local Lemma safety_openq_bound k d a φ :
  open_qual k ∅ d ⊑↑ φ ->
  a ⊑↑ φ -> open_qual k a d ⊑↑ φ.
Proof.
  unfold open_qual. destruct (qbvs d k); [|auto].
  intros H Ha. apply safety_join_bound; [|exact Ha].
  eapply safety_subq_trans; [apply safety_join_l|exact H].
Qed.

Local Lemma safety_openq2_bound d a b φ :
  (d <~ᵈ ∅ ; ∅) ⊑↑ φ ->
  a ⊑↑ φ -> b ⊑↑ φ -> (d <~ᵈ a ; b) ⊑↑ φ.
Proof.
  unfold openq, open_qual.
  destruct (qbvs d 0) eqn:H0.
  - cbn [qor qbvs fst snd].
    replace (n_or (n_diff (qbvs d) (n_one 0)) (qbvs ∅) 1) with (qbvs d 1)
      by (unfold n_or, n_diff, n_one; rewrite Bool.orb_false_r, Bool.andb_true_r; reflexivity).
    replace (n_or (n_diff (qbvs d) (n_one 0)) (qbvs a) 1) with (qbvs d 1 || qbvs a 1)
      by (unfold n_or, n_diff, n_one; rewrite Bool.andb_true_r; reflexivity).
    destruct (qbvs d 1), (qbvs a 1); cbn [orb]; safety_qpoint.
  - intros H _ Hb. exact (safety_openq_bound 1 d b φ H Hb).
Qed.

Local Lemma safety_le_fresh_variant a φ :
  a ⊑↑ φ -> a ⊑↑ φ ⊔ {♦}.
Proof. eauto using safety_subq_trans, safety_join_l. Qed.

Local Lemma safety_le_fresh_trans a b c :
  a ⊑↑ b ⊔ {♦} -> b ⊑↑ c -> a ⊑↑ c ⊔ {♦}.
Proof.
  intros Ha Hb. eapply safety_subq_trans; [exact Ha|].
  eauto using safety_join_bound, safety_le_fresh_variant, safety_join_r.
Qed.

Local Lemma safety_bound_without_fresh d φ :
  ♦∉ d -> d ⊑↑ φ ⊔ {♦} -> d ⊑↑ φ.
Proof.
  change (~ Is_true (qfresh d) -> d ⊑↑ φ ⊔ {♦} -> d ⊑↑ φ). destruct (qfresh d) eqn:H; cbn [Is_true].
  - tauto.
  - safety_qpoint. exact 0.
Qed.

Local Lemma safety_typing_qual_bound Γ φ Σ t T d :
  has_type Γ φ Σ t T d -> d ⊑↑ φ ⊔ {♦}.
Proof.
  intros H. induction H;
    try solve [eauto using safety_le_fresh_variant, safety_join_r, safety_empty_bound].
  all: try solve [eapply safety_openq2_bound;
    eauto using safety_le_fresh_variant, safety_diff_le, safety_le_fresh_trans].
  - subst φd. apply safety_openq2_bound; try assumption.
    eapply safety_le_fresh_trans; [exact IHhas_type2|apply safety_diff_le].
  - subst φd. apply safety_openq2_bound; try assumption.
    eapply safety_le_fresh_trans; [exact IHhas_type2|apply safety_diff_le].
  - clear - H2 H5 IHhas_type2.
    apply safety_qual_le in IHhas_type2.
    apply safety_qual_le in H5.
    destruct H2 as [Hcl _].
    destruct IHhas_type2 as (HF & Hfv & Hbv & Hl).
    destruct H5 as (_ & Hfv' & Hbv' & Hl').
    apply safety_qual_le. repeat split.
    + intros _. apply orb_true_r.
    + intros x Hx. change (qfvs φ x || false = true).
      rewrite orb_false_r. apply Hfv'.
      pose proof (Hcl x Hx) as Hlt.
      apply Hfv in Hx.
      change ((qfvs φd x || (x =? S (length Γ))) || false = true) in Hx.
      rewrite orb_false_r, orb_true_iff, Nat.eqb_eq in Hx.
      destruct Hx as [Hmem | Heq]; [exact Hmem|].
      lia.
    + intros x Hx. change (qbvs φ x || false = true).
      rewrite orb_false_r. apply Hbv'.
      apply Hbv in Hx.
      change ((qbvs φd x || false) || false = true) in Hx.
      now rewrite !orb_false_r in Hx.
    + intros x Hx. change (qlocs φ x || false = true).
      rewrite orb_false_r. apply Hl'.
      apply Hl in Hx.
      change ((qlocs φd x || false) || false = true) in Hx.
      now rewrite !orb_false_r in Hx.
Qed.

Local Lemma safety_typing_scope_weaken Γ φ Σ t T d :
  has_type Γ φ Σ t T d ->
  forall ψ, φ ⊑↑ ψ -> closed_Qual 0 (length Γ) (length Σ) ψ↑ ->
    has_type Γ ψ Σ t T d.
Proof.
  intros H.
  induction H; intros ψ Hle Hcl;
    [eapply t_tabs | eapply t_tapp | eapply t_tapp_fresh |
     eapply t_base | eapply t_var | eapply t_abs |
     eapply t_app with (φd := qdiff ψ (local_locs t1)) |
     eapply t_app_fresh with (φd := qdiff ψ (local_locs t1)) |
     eapply t_loc | eapply t_ref |
     eapply t_refat with (φd := qdiff ψ (local_locs t2)) |
     eapply t_deref | eapply t_assign with (φd := qdiff ψ (local_locs t1)) |
     eapply t_sub | eapply t_withr | eapply t_withc];
    try subst φd;
    try reflexivity;
    eauto 6 using safety_subq_trans, safety_le_fresh_trans, safety_diff_ambient,
      safety_qual_closed_of_sub, safety_diff_le.
Qed.

Local Lemma safety_value_scope Γ φ Σ v T d :
  Γ = [] -> has_type Γ φ Σ v T d -> value v ->
  forall ψ, d ⊑↑ ψ ⊔ {♦} -> closed_Qual 0 0 (length Σ) ψ↑ ->
    has_type [] ψ Σ v T d.
Proof.
  intros HΓ H. induction H; subst; intros Hv ψ Hle Hcl;
    try solve [inversion Hv].
  - eapply t_tabs; eauto using safety_bound_without_fresh.
  - eapply t_base; exact Hcl.
  - eapply t_abs; eauto using safety_bound_without_fresh.
  - eapply t_loc; eauto using safety_bound_without_fresh.
  - eapply t_sub; eauto using safety_subq_trans, safety_subqual_of_stp.
Qed.

Local Lemma safety_vtp_rescope Σ ϰ ϰ' φ φ' v T q :
  vtp Σ ϰ φ v T q ->
  q ⊑↑ φ' -> kill_sep ϰ' q -> vtp Σ ϰ' φ' v T q.
Proof.
  intros H. induction H; intros Hq Hsep; eauto using vtp.
  eapply vtp_loc with (q1 := q1); try eassumption.
  destruct (safety_closed_qstp _ _ _ H7) as (_ & _ & _ & Hl).
  destruct Hq as (_ & _ & _ & Hq).
  apply Hq, Hl, Nat.eqb_refl.
Qed.

Local Lemma safety_sep_of_sub a b K :
  a ⊑↑ b -> kill_sep K b -> kill_sep K a.
Proof. safety_qpoint. Qed.

Local Lemma safety_dom_bound (Σ : senv) φ x :
  φ ⊑↑ qdom Σ -> x ∈ₗ φ -> x < length Σ.
Proof.
  intros (_ & _ & _ & Hloc) Hx.
  apply Nat.ltb_lt. exact (Hloc x Hx).
Qed.

Local Lemma safety_remove_locs Σ k q fuel x :
  x ∈ₗ q_remove' Σ k q fuel <->
  x < fuel /\ x <> k /\ x ∈ₗ q.
Proof.
  induction fuel; [simpl; split; [discriminate|lia]|].
  simpl q_remove'.
  destruct ((qlocs q fuel) && negb (n_one fuel k)) eqn:Hsel.
  - change (qlocs q fuel && negb (k =? fuel) = true) in Hsel.
    apply andb_true_iff in Hsel as [Hq Hneq].
    apply negb_true_iff, Nat.eqb_neq in Hneq.
    change (n_or (qlocs (q_remove' Σ k q fuel)) (n_one fuel) x = true <-> x < S fuel /\ x <> k /\ x ∈ₗ q).
    unfold n_or, n_one. rewrite orb_true_iff, Nat.eqb_eq.
    change ((x ∈ₗ q_remove' Σ k q fuel \/ x = fuel) <-> x < S fuel /\ x <> k /\ x ∈ₗ q).
    rewrite IHfuel.
    change (fuel ∈ₗ q) in Hq. split.
    + intros [(? & ? & ?) | ->]; repeat split; try assumption; lia.
    + intros (? & ? & ?). destruct (Nat.eq_dec x fuel); [auto|left; repeat split; try assumption; lia].
  - rewrite IHfuel. split; [intros (? & ? & ?); repeat split; try assumption; lia|].
    intros (? & ? & Hin). destruct (Nat.eq_dec x fuel) as [->|Hne].
    + change (qlocs q fuel = true) in Hin.
      change (qlocs q fuel && negb (k =? fuel) = false) in Hsel.
      rewrite Hin in Hsel. simpl in Hsel. apply negb_false_iff, Nat.eqb_eq in Hsel. lia.
    + repeat split; try assumption; lia.
Qed.

Local Lemma safety_remove_components Σ k q n :
  qfresh (q_remove' Σ k q n) = false /\
  (forall x, qfvs (q_remove' Σ k q n) x = false) /\
  (forall x, qbvs (q_remove' Σ k q n) x = false).
Proof.
  induction n; [repeat split; reflexivity|].
  simpl q_remove'. destruct ((qlocs q n) && negb (n_one n k)); [|exact IHn].
  destruct IHn as (HF & Hfv & Hbv).
  repeat split.
  - change (qfresh (q_remove' Σ k q n) || false = false). now rewrite HF.
  - intros x. change (qfvs (q_remove' Σ k q n) x || false = false). now rewrite Hfv.
  - intros x. change (qbvs (q_remove' Σ k q n) x || false = false). now rewrite Hbv.
Qed.

Local Lemma safety_remove_spec Σ k φ :
  φ ⊑↑ qdom Σ ->
  qfresh (q_remove Σ k φ) = qfresh φ /\
  (forall x, qfvs (q_remove Σ k φ) x = qfvs φ x) /\
  (forall x, qbvs (q_remove Σ k φ) x = qbvs φ x) /\
  (forall x, x ∈ₗ q_remove Σ k φ <-> x ∈ₗ φ /\ x <> k).
Proof.
  intros Hdom.
  destruct (safety_remove_components Σ k φ (length Σ)) as (HF & Hfv & Hbv).
  unfold q_remove. refine (conj _ (conj _ (conj _ _))).
  - change (qfresh (q_remove' Σ k φ (length Σ)) || qfresh φ = qfresh φ).
    now rewrite HF.
  - intros x. change (qfvs (q_remove' Σ k φ (length Σ)) x || qfvs φ x = qfvs φ x).
    now rewrite Hfv.
  - intros x. change (qbvs (q_remove' Σ k φ (length Σ)) x || qbvs φ x = qbvs φ x).
    now rewrite Hbv.
  - intros x. split.
    + intros Hx.
      change (qlocs (q_remove' Σ k φ (length Σ)) x || false = true) in Hx.
      rewrite orb_false_r in Hx.
      apply safety_remove_locs in Hx. tauto.
    + intros [Hx Hne].
      change (qlocs (q_remove' Σ k φ (length Σ)) x || false = true).
      rewrite orb_false_r. apply safety_remove_locs.
      eauto using safety_dom_bound.
Qed.

Local Lemma safety_remove_sub Σ k φ :
  φ ⊑↑ qdom Σ -> q_remove Σ k φ ⊑↑ φ.
Proof.
  intros Hdom.
  destruct (safety_remove_spec Σ k φ Hdom) as (HF & Hfv & Hbv & Hl).
  apply safety_qual_le.
  unfold n_sub. rewrite HF.
  refine (conj _ (conj _ (conj _ _))); try solve [intros x; rewrite ?Hfv, ?Hbv; auto].
  intros x Hx. apply Hl in Hx. exact (proj1 Hx).
Qed.

Local Lemma safety_update_length {A} (xs : list A) l a :
  length (update xs l a) = length xs.
Proof.
  induction xs; simpl; [reflexivity|].
  destruct (l =? length xs); simpl; congruence.
Qed.

Local Lemma safety_ctx_dom (Σ : senv) (σ : store) :
  length σ = length Σ -> qdom' σ ⊑↑ qdom Σ.
Proof.
  intro Hlen. apply safety_qual_le.
  refine (conj _ (conj _ (conj _ _))).
  1: exact (fun H => H).
  1,2: intros x Hx; discriminate Hx.
  intros x Hx.
  change ((x <? length σ) && (match indexr x σ with Some (Some _) => true | _ => false end) = true) in Hx.
  apply andb_true_iff in Hx as [Hlt _].
  change (x <? length Σ = true). now rewrite <- Hlen.
Qed.

Local Lemma safety_dom_closed (Σ : senv) φ :
  φ ⊑↑ qdom Σ -> closed_Qual 0 0 (length Σ) φ↑.
Proof.
  intros H. eapply safety_qual_closed_of_sub; [exact H|].
  unfold qdom. safety_qpoint.
  split; [intros x Hx; discriminate Hx|].
  split; [intros x Hx; discriminate Hx|].
  intros x Hx. apply Nat.ltb_lt. exact Hx.
Qed.

Local Lemma safety_kill_ctx Σ ϰ φ σ l :
  l < length Σ -> CtxOK [] φ Σ ϰ σ ->
  CtxOK [] (q_remove Σ l φ) Σ (ϰ ⊔ &!l) (update σ l None).
Proof.
  intros Hl (Hdom & Hlen & Hφ & Hϰ & Hsep & Hstore).
  pose proof (safety_remove_sub Σ l φ Hφ) as Hremove.
  pose proof (safety_subq_trans _ _ _ Hremove Hφ) as Hφ'.
  destruct (safety_remove_spec Σ l φ Hφ) as (_ & _ & _ & Hmem).
  assert (Hlen' : length (update σ l None) = length Σ)
    by now rewrite safety_update_length.
  assert (Hcl : closed_Qual 0 0 (length Σ) (ϰ ⊔ &!l)↑).
  { apply safety_qual_join_closed; [exact Hϰ|].
    safety_qpoint. }
  assert (Hsep' : kill_sep (ϰ ⊔ &!l) (q_remove Σ l φ)).
  { pose proof (safety_sep_of_sub _ _ _ Hremove Hsep) as Hold.
    pose proof (fun x => proj1 (Hmem x)) as Hall.
    clear - Hold Hall.
    safety_qpoint. }
  refine (conj (safety_ctx_dom _ _ Hlen') (conj Hlen' (conj Hφ' (conj Hcl (conj Hsep' _))))).
  intros k o c T q. split.
  - intros Hdead.
    apply orb_true_iff in Hdead as [Hk | Heq].
    + destruct (Hstore k o c T q) as [Hk' _].
      rewrite safety_indexr_update, (Hk' Hk).
      destruct (k =? l); reflexivity.
    + change (k =? l = true) in Heq. apply Nat.eqb_eq in Heq. subst k.
      assert (Hbl : l < length σ) by lia.
      destruct (safety_indexr_exists _ _ Hbl) as [cell Hcell].
      now rewrite safety_indexr_update, Nat.eqb_refl, Hcell.
  - intros Hlive Hscope Hcty.
    destruct (proj1 (Hmem k) Hscope) as [Hscope' Hneq].
    assert (Hlive' : ~ k ∈ₗ ϰ).
    { intro Hin. apply Hlive. apply orb_true_iff. left. exact Hin. }
    destruct (Hstore k o c T q) as [_ Htyped].
    destruct (Htyped Hlive' Hscope' Hcty) as (s & (Hindex & Hsize) & Hv).
    exists s. split.
    + rewrite safety_indexr_update, (proj2 (Nat.eqb_neq _ _) Hneq).
      auto.
    + intro Ho. destruct (Hv Ho) as (v & Hvo & Hval & Hvtp).
      exists v. repeat split; try assumption.
      intros Hq. apply (safety_vtp_rescope Σ ϰ (ϰ ⊔ &!l) φ); auto.
      * apply Hvtp. eauto using safety_subq_trans.
      * eauto using safety_sep_of_sub.
Qed.

Local Lemma safety_senv_cons_ext Σ c :
  (c :: Σ) ⊇₂ Σ.
Proof.
  intros l s Hl.
  pose proof (safety_indexr_bound _ _ _ Hl) as Hlt.
  exists s. split.
  - simpl. rewrite (proj2 (Nat.eqb_neq l (length Σ)) ltac:(lia)). exact Hl.
  - exists []. reflexivity.
Qed.

Local Lemma safety_senv_cons_wf Σ T q :
  wf_senv Σ -> closed_ty 0 0 (length Σ) T ->
  closed_Qual 0 0 (length Σ) q↑ -> ♦∉ q ->
  wf_senv ([(T,q)] :: Σ).
Proof.
  intros Hwf HT Hq Hnf l s Hl.
  simpl in Hl. destruct (l =? length Σ) eqn:Hl'.
  - inversion Hl; subst. split; [simpl; lia|].
    intros o U r Ho. simpl in Ho. destruct (o =? 0); [|discriminate].
    inversion Ho; subst. simpl. refine (conj Hnf (conj _ _));
      eauto using safety_ty_closed_weaken, safety_locs_closed_weaken, Nat.le_succ_diag_r.
  - destruct (Hwf _ _ Hl) as [Hlen Hcells].
    split; [exact Hlen|].
    intros o U r Ho. destruct (Hcells _ _ _ Ho) as (Hnf' & HU & Hr).
    simpl. refine (conj Hnf' (conj _ _));
      eauto using safety_ty_closed_weaken, safety_locs_closed_weaken, Nat.le_succ_diag_r.
Qed.

Local Lemma safety_remove_avoid Σ k φ q :
  φ ⊑↑ qdom Σ -> q ⊑↑ φ ⊔ {♦} -> kill_sep &!k q ->
  q ⊑↑ q_remove Σ k φ ⊔ {♦}.
Proof.
  intros Hdom Hsub Hsep.
  destruct (safety_remove_spec Σ k φ Hdom) as (HF & Hfv & Hbv & Hloc).
  clear Hdom. safety_qpoint.
Qed.

Local Lemma safety_senv_refl Σ : Σ ⊇₂ Σ.
Proof. intros l c H. exists c. split; [exact H|exists []; reflexivity]. Qed.

Local Lemma safety_old_scope_after_alloc (Σ : senv) q φ :
  closed_Qual 0 0 (length Σ) q↑ ->
  q ⊑↑ φ ⊔ &!(length Σ) -> q ⊑↑ φ.
Proof.
  intros (_ & _ & Hlt) Hsub.
  apply safety_qual_le in Hsub as (HF & Hfv & Hbv & Hl).
  apply safety_qual_le. unfold n_sub in *.
  refine (conj _ (conj _ (conj _ _))); try solve [intros ?; specialize (HF ltac:(assumption));
    change (qfresh φ || false = true) in HF; now rewrite orb_false_r in HF].
  - intros x Hx. specialize (Hfv x Hx).
    change (qfvs φ x || false = true) in Hfv. now rewrite orb_false_r in Hfv.
  - intros x Hx. specialize (Hbv x Hx).
    change (qbvs φ x || false = true) in Hbv. now rewrite orb_false_r in Hbv.
  - intros x Hx. specialize (Hl x Hx). specialize (Hlt x Hx).
    change (qlocs φ x || (x =? length Σ) = true) in Hl.
    apply orb_true_iff in Hl as [Hmem | Heq]; [exact Hmem|].
    apply Nat.eqb_eq in Heq. lia.
Qed.

Local Lemma safety_alloc_scope_dom (Σ : senv) (c : senvs) φ :
  φ ⊑↑ qdom Σ -> φ ⊔ &!(length Σ) ⊑↑ qdom (c :: Σ).
Proof.
  intro Hφ. apply safety_join_bound.
  - eapply safety_subq_trans; [exact Hφ|].
    unfold qdom. apply safety_qual_le. repeat split; try tauto; try discriminate.
    intros x Hx. apply Nat.ltb_lt in Hx. apply Nat.ltb_lt. simpl. lia.
  - unfold qdom. apply safety_qual_le. repeat split; try discriminate.
    intros x Hx. change (x =? length Σ = true) in Hx. apply Nat.eqb_eq in Hx.
    apply Nat.ltb_lt. simpl. lia.
Qed.

Local Lemma safety_alloc_scope_sep (Σ : senv) ϰ φ :
  closed_Qual 0 0 (length Σ) ϰ↑ ->
  kill_sep ϰ φ -> kill_sep ϰ (φ ⊔ &!(length Σ)).
Proof.
  intros (_ & _ & Hlt) Hsep.
  unfold kill_sep in Hsep |- *.
  apply safety_qual_le in Hsep as (_ & Hfv & Hbv & Hl).
  apply safety_qual_le.
  refine (conj (fun _ => eq_refl) (conj _ (conj _ _))).
  - intros x Hx. apply (Hfv x).
    change ((qfvs φ x || false) && qfvs ϰ x = true) in Hx.
    now rewrite orb_false_r in Hx.
  - intros x Hx. apply (Hbv x).
    change ((qbvs φ x || false) && qbvs ϰ x = true) in Hx.
    now rewrite orb_false_r in Hx.
  - intros x Hx.
    change ((qlocs φ x || (x =? length Σ)) && qlocs ϰ x = true) in Hx.
    apply andb_true_iff in Hx as [Hx Hdead].
    apply orb_true_iff in Hx as [Hmem | Heq].
    + apply (Hl x). apply andb_true_iff. auto.
    + apply Nat.eqb_eq in Heq. apply (Hlt x) in Hdead. lia.
Qed.

Local Lemma safety_alloc_ctx Σ ϰ φ σ T q v :
  wf_senv Σ -> CtxOK [] φ Σ ϰ σ ->
  value v ->
  vtp ([(T,q)] :: Σ) ϰ (φ ⊔ &!(length Σ)) v T q ->
  CtxOK [] (φ ⊔ &!(length Σ)) ([(T,q)] :: Σ) ϰ (Some [v] :: σ).
Proof.
  intros Hwf (Hdom & Hlen & Hφ & Hϰ & Hsep & Hstore) Hv Hvtp.
  pose proof (safety_senv_cons_ext Σ [(T,q)]) as Hext.
  set (Σ' := [(T,q)] :: Σ).
  set (φ' := φ ⊔ &!(length Σ)).
  set (σ' := Some [v] :: σ).
  assert (Hlen' : length σ' = length Σ') by (exact (f_equal S Hlen)).
  assert (Hφ' : φ' ⊑↑ qdom Σ') by (unfold φ', Σ'; eauto using safety_alloc_scope_dom).
  assert (Hϰ' : closed_Qual 0 0 (length Σ') ϰ↑)
    by (unfold Σ'; simpl; eauto using safety_locs_closed_weaken, Nat.le_succ_diag_r).
  assert (Hsep' : kill_sep ϰ φ') by (unfold φ'; eauto using safety_alloc_scope_sep).
  refine (conj (safety_ctx_dom _ _ Hlen') (conj Hlen' (conj Hφ' (conj Hϰ' (conj Hsep' _))))).
  intros l o c U r. unfold σ', Σ'. simpl indexr. rewrite Hlen.
  destruct (l =? length Σ) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst l.
    split.
    + intros Hdead. destruct Hϰ as (_ & _ & Hlt).
      specialize (Hlt _ Hdead). lia.
    + intros _ _ Hc. inversion Hc; subst c.
      exists [v]. split; [auto|].
      simpl. destruct (o =? 0); [|discriminate].
      intros Hr. inversion Hr; subst. eauto.
  - split.
    + exact (proj1 (Hstore l o c U r)).
    + intros Hlive Hscope Hc.
      assert (Hscope0 : l ∈ₗ φ).
      { unfold φ' in Hscope.
        change (qlocs φ l || (l =? length Σ) = true) in Hscope.
        rewrite Heq, orb_false_r in Hscope. exact Hscope. }
      destruct (proj2 (Hstore l o c U r) Hlive Hscope0 Hc)
        as (s & Hs & Hcells).
      exists s. split; [exact Hs|].
      intros Hr. destruct (Hcells Hr) as (w & Hw & Hwval & Hwvtp).
      exists w. repeat split; try assumption.
      intro Hq'. apply (safety_vtp_rescope Σ' ϰ ϰ φ).
      * eapply safety_vtp_weaken; [exact Hext|].
        apply Hwvtp. destruct (Hwf _ _ Hc) as [_ Hclosed].
        destruct (Hclosed _ _ _ Hr) as (_ & _ & Hcl).
        eauto using safety_old_scope_after_alloc.
      * exact Hq'.
      * eauto using safety_sep_of_sub.
Qed.

Local Lemma safety_fv_closed b f l x :
  x < f -> closed_Qual b f l ($!x)↑.
Proof.
  intros H. unfold closed_Qual. refine (conj _ (conj _ _)).
  - intros y Hy. change (y =? x = true) in Hy. apply Nat.eqb_eq in Hy. now subst y.
  - intros y Hy. discriminate Hy.
  - intros y Hy. discriminate Hy.
Qed.

Local Lemma safety_fv_closed_weaken b f f' l q :
  f <= f' -> closed_Qual b f l q -> closed_Qual b f' l q.
Proof.
  intros Hle (Hf & Hb & Hl).
  refine (conj _ (conj Hb Hl)).
  intros x Hx. specialize (Hf x Hx). lia.
Qed.

Local Lemma safety_qstp_closed Γ Σ q d :
  qstp Γ Σ q d -> closed_Qual 0 (length Γ) (length Σ) d↑.
Proof.
  intros H. induction H; try assumption;
    eauto using safety_fv_closed, safety_qual_join_closed, safety_indexr_bound.
  - eapply safety_fv_closed_weaken; [|exact H1].
    pose proof (safety_indexr_bound _ _ _ H); lia.
  - eapply safety_fv_closed_weaken; [|exact H1].
    pose proof (safety_indexr_bound _ _ _ H); lia.
Qed.

Local Lemma safety_stp_closed Γ Σ T d U e :
  stp Γ Σ T d U e ->
  closed_ty 0 (length Γ) (length Σ) T /\ closed_ty 0 (length Γ) (length Σ) U.
Proof.
  intros H. induction H; try solve [split; eauto using closed_ty].
  - pose proof (safety_indexr_bound _ _ _ H). split; now constructor.
  - destruct IHstp as [_ HR]. split; [|exact HR].
    pose proof (safety_indexr_bound _ _ _ H). now constructor.
  - destruct IHstp1 as [HT HU], IHstp2 as [HU' HT'].
    split; constructor; eauto using safety_qstp_closed.
  - tauto.
Qed.

Local Lemma safety_empty_sep K : kill_sep ∅ K.
Proof. safety_qpoint. Qed.

Local Lemma safety_nonfresh_loc l : ♦∉ &!l.
Proof. simpl. tauto. Qed.

Local Lemma safety_loc_in_scope l φ : l ∈ₗ φ -> &!l ⊑↑ φ.
Proof. safety_qpoint. Qed.

Local Lemma safety_vtp_typing Σ ϰ φ v T d :
  vtp Σ ϰ φ v T d ->
  d ⊑↑ φ -> closed_Qual 0 0 (length Σ) φ↑ -> wf_step v ->
  has_type [] φ Σ v T d.
Proof.
  intros H. induction H; intros Hle Hcl Hwf.
  - eapply t_sub.
    + eapply t_tabs; try eassumption.
      * eapply safety_subq_trans; [|exact Hle]. now apply safety_closed_qstp in H4.
      * simpl in Hwf. rewrite Hwf. apply safety_empty_sep.
    + eapply s_all; eassumption.
    + apply safety_le_fresh_variant. exact Hle.
    + simpl in *. rewrite Hwf. apply safety_empty_sep.
  - eapply t_sub; [apply t_base; exact Hcl| |eauto using safety_le_fresh_variant|apply safety_empty_sep].
    apply s_base, qs_sq; eauto using safety_empty_bound.
  - eapply t_sub.
    + eapply t_loc with (q := q1) (T := T); try eassumption. now apply safety_loc_in_scope.
    + eapply s_ref; eassumption.
    + apply safety_le_fresh_variant. exact Hle.
    + apply safety_empty_sep.
  - eapply t_sub.
    + eapply t_abs; try eassumption.
      * eapply safety_subq_trans; [|exact Hle]. now apply safety_closed_qstp in H5.
      * simpl in Hwf. rewrite Hwf. apply safety_empty_sep.
    + eapply s_fun; eassumption.
    + apply safety_le_fresh_variant. exact Hle.
    + simpl in *. rewrite Hwf. apply safety_empty_sep.
  - eapply t_sub; [eauto| |eauto using safety_le_fresh_variant|].
    + apply s_top.
      * clear - H. induction H; try solve [auto using closed_ty].
        destruct (safety_stp_closed _ _ _ _ _ _ H5). now constructor.
      * apply qs_sq; [apply safety_subq_refl|].
        eapply safety_qual_closed_of_sub; eassumption.
    + assert (Hv : value t) by (clear - H; induction H; auto using value).
      rewrite (safety_value_scopes _ Hv Hwf). apply safety_empty_sep.
Qed.

Local Lemma safety_stp_requalify Γ Σ T U d e a b :
  stp Γ Σ T d U e ->
  qstp Γ Σ a b -> stp Γ Σ T a U b.
Proof.
  intros H. revert a b. induction H; intros a b HQ;
    [eapply s_top | eapply s_tvar_refl | eapply s_tvar_trans | eapply s_all |
     eapply s_base | eapply s_ref | eapply s_fun | eapply s_trans];
    try eassumption; try now eapply IHstp.
  - apply IHstp1. exact HQ.
  - apply IHstp2. apply qs_sq.
    + apply safety_subq_refl.
    + eauto using safety_qstp_closed.
Qed.

Local Lemma safety_stp_ref_inv Σ S d U q e :
  stp [] Σ S d (TRef q U) e ->
  exists T r, S = TRef r T /\ stp [] Σ T ∅ U ∅ /\ r ⊑↑ q.
Proof.
  intros H.
  remember ([] : tenv) as Γ eqn:HΓ. remember (TRef q U) as R eqn:HR.
  revert U q HR.
  induction H; subst; intros U q HR; try discriminate.
  - inversion HR; subst. exists T1, q1. refine (conj eq_refl (conj _ _)); eauto using safety_closed_qstp.
  - destruct (IHstp2 eq_refl U q HR) as (V & r & HV & HUV & Hqr).
    destruct (IHstp1 eq_refl V r HV) as (T & r' & HS & HTV & Hr).
    exists T, r'. split; [exact HS|]. split.
    + eauto using s_trans.
    + eauto using safety_subq_trans.
Qed.

Local Lemma safety_loc_ref_inv Σ φ l o U q d :
  has_type [] φ Σ &(l,o) (TRef q U) d ->
  exists T r, sindexr l o Σ = Some (T,r) /\ r ⊑↑ q /\
    (T = U \/ stp [] Σ T ∅ U ∅).
Proof.
  intros H.
  remember ([] : tenv) as Γ eqn:HΓ. remember (&(l,o)) as v eqn:Hv.
  remember (TRef q U) as R eqn:HR. revert U q HR.
  induction H; subst; intros U r HR; try discriminate.
  - inversion Hv; inversion HR; subst.
    exists U, r. refine (conj H0 (conj (safety_subq_refl r) (or_introl eq_refl))).
  - destruct (safety_stp_ref_inv _ _ _ _ _ _ ltac:(rewrite <- HR; exact H0))
      as (T & r' & HT & Hstp & Hr).
    destruct (IHhas_type eq_refl eq_refl T r' HT)
      as (V & r'' & Hlook & Hr' & [-> | Hstp']).
    + exists T, r''. refine (conj Hlook (conj _ (or_intror Hstp))).
      exact (safety_subq_trans _ _ _ Hr' Hr).
    + exists V, r''. refine (conj Hlook (conj _ _)).
      * exact (safety_subq_trans _ _ _ Hr' Hr).
      * right. exact (s_trans _ _ _ _ _ _ _ _ Hstp' Hstp).
Qed.

Local Lemma safety_vtp_requalify Σ ϰ φ v T r q :
  vtp Σ ϰ φ v T r -> wf_step v -> qstp [] Σ r q ->
  kill_sep ϰ q -> vtp Σ ϰ φ v T q.
Proof.
  intros H. induction H; intros Hwf Hsub Hkill;
    pose proof (safety_qstp_closed _ _ _ _ Hsub) as Hclosed.
  - eapply vtp_tabs with (df1 := df1) (T1 := T1) (T2 := T2) (d1 := d1) (d2 := d2);
      try eassumption.
    + eapply qs_trans; eassumption.
    + simpl in Hwf. rewrite Hwf. apply safety_empty_sep.
  - apply vtp_base; [exact (safety_qstp_closed _ _ _ _ Hsub)|exact Hkill].
  - eapply vtp_loc with (T := T) (q1 := q1);
      try eassumption; eauto using safety_qstp_closed.
    eapply qs_trans; eassumption.
  - eapply vtp_abs with (df1 := df1) (T1 := T1) (T2 := T2) (d1 := d1) (d2 := d2);
      try eassumption; eauto using safety_qstp_closed.
    + eapply qs_trans; eassumption.
    + simpl in Hwf. rewrite Hwf. apply safety_empty_sep.
  - apply vtp_top with (T := T). eauto.
Qed.

Local Lemma safety_deref_redex Σ φ ϰ σ l o U q d :
  has_type [] φ Σ &(l,o) (TRef q U) d ->
  q ⊑↑ φ -> ♦∉ q -> CtxOK [] φ Σ ϰ σ ->
  wf_senv Σ -> wf_store σ ->
  exists v, step (! &(l,o)) σ v σ /\
    preserve [] Σ ϰ φ (local_locs (! &(l,o))) v U q σ.
Proof.
  intros Ht Hq Hnf Hctx Hwf Hσ.
  destruct (safety_loc_ref_inv _ _ _ _ _ _ _ Ht) as (T & r & Hcell & Hr & Hsub).
  destruct (safety_loc_lookup _ _ _ _ _ _ Ht) as (Hl & _).
  destruct (safety_sindexr _ _ _ _ Hcell) as (s & Hs & Ho).
  destruct Hctx as (Hdom & Hlen & Hφ & Hϰ & Hsep & Hstore).
  assert (Hlive : ~ l ∈ₗ ϰ).
  { pose proof (safety_sep_of_sub _ _ _ (safety_loc_in_scope _ _ Hl) Hsep) as Hsep'.
    clear - Hsep'. safety_qpoint. }
  destruct (proj2 (Hstore l o s T r) Hlive Hl Hs) as (c & (Hc & Hsize) & Hv).
  destruct (Hv Ho) as (v & Hvo & Hval & Hvtp).
  specialize (Hvtp (safety_subq_trans _ _ _ Hr Hq)).
  assert (Hwv : wf_step v).
  { apply (proj1 (Hσ l o v ltac:(rewrite (safety_sindexr_store _ _ _ _ Hc); exact Hvo))). }
  exists v. split; [eauto using step_deref|].
  apply (Preserve Σ ∅ φ ϰ); try assumption.
  - apply safety_senv_refl.
  - apply env_phi; [apply safety_senv_refl|reflexivity].
  - apply safety_empty_bound.
  - repeat (split; try assumption).
  - apply disj_bot.
  - assert (Hrφ : r ⊑↑ φ) by eauto using safety_subq_trans.
    pose proof (safety_vtp_typing _ _ _ _ _ _ Hvtp Hrφ (safety_dom_closed _ _ Hφ) Hwv) as Hty.
    unfold qqplus. destruct (qfresh q) eqn:HQ; [exfalso; exact (Hnf I)|].
    assert (Hqc : closed_Qual 0 0 (length Σ) q↑)
      by eauto using safety_qual_closed_of_sub, safety_dom_closed.
    destruct Hsub as [-> | Hsub].
    + eapply safety_vtp_typing with (ϰ := ϰ); try eassumption.
      * eapply safety_vtp_requalify; try eassumption.
        -- apply qs_sq; assumption.
        -- eauto using safety_sep_of_sub.
      * eauto using safety_dom_closed.
    + eapply t_sub; [exact Hty| |eauto using safety_le_fresh_variant|].
      * eapply safety_stp_requalify; [exact Hsub|apply qs_sq; assumption].
      * rewrite (safety_value_scopes _ Hval Hwv). apply safety_empty_sep.
Qed.

Local Lemma safety_q_closed_weaken b b' f f' L q :
  b <= b' -> f <= f' -> closed_Qual b f L q↑ -> closed_Qual b' f' L q↑.
Proof.
  intros Hb Hf (HF & HB & HL). refine (conj _ (conj _ HL)).
  - intros x Hx. specialize (HF x Hx). lia.
  - intros x Hx. specialize (HB x Hx). lia.
Qed.

Local Lemma safety_ty_vars_weaken b b' f f' L T :
  closed_ty b f L T -> b <= b' -> f <= f' -> closed_ty b' f' L T.
Proof.
  intros H. revert b' f'. induction H; intros b' f' HB HF;
    constructor; eauto using safety_q_closed_weaken; try lia.
  all: try (eapply safety_q_closed_weaken; [|exact HF|exact H0]; lia).
  all: try (apply IHclosed_ty2; lia).
  all: try (apply IHclosed_ty1; lia).
  all: try (apply IHclosed_ty; lia).
Qed.

Local Lemma safety_q_open_skip q b f L k a :
  closed_Qual b f L q↑ -> b <= k -> open_qual k a q = q.
Proof.
  intros (_ & HB & _) Hk. unfold open_qual.
  destruct (qbvs q k) eqn:H; [|reflexivity].
  specialize (HB k H). lia.
Qed.

Local Lemma safety_ty_open_skip T b f L k U a :
  closed_ty b f L T -> b <= k -> open_rec_ty k U a T = T.
Proof.
  intros H. revert k. induction H; intros k Hk; simpl;
    try reflexivity; try solve [f_equal; eauto using safety_q_open_skip; eauto with arith].
  - replace (k =? x) with false by (symmetry; apply Nat.eqb_neq; lia).
    reflexivity.
  - f_equal.
    + eapply safety_q_open_skip; eassumption.
    + eapply safety_q_open_skip; [eassumption|lia].
    + eauto.
    + apply IHclosed_ty2. lia.
  - f_equal.
    + eapply safety_q_open_skip; eassumption.
    + eapply safety_q_open_skip; [eassumption|lia].
    + eauto.
    + apply IHclosed_ty2. lia.
Qed.

Local Lemma safety_q_open_named k b f F L q a :
  closed_Qual b f L q↑ ->
  closed_Qual 0 F L a↑ ->
  f <= F ->
  closed_Qual b F L (open_qual k a q)↑ /\ qbvs (open_qual k a q) k = false.
Proof.
  intros Hq Ha Hf.
  unfold open_qual. destruct (qbvs q k) eqn:Htest.
  - assert (Hr : closed_Qual b F L
      (qfresh q, qfvs q, n_diff (qbvs q) (n_one k), qlocs q)↑).
    { destruct Hq as (HF & HB & HL).
      refine (conj _ (conj _ HL)).
      - intros x Hx. specialize (HF x Hx). lia.
      - intros x Hx. apply andb_true_iff in Hx as [Hx _]. now apply HB. }
    split.
    + apply safety_qual_join_closed; [exact Hr|eauto using safety_q_closed_weaken, Nat.le_0_l].
    + change ((qbvs q k && negb (k =? k)) || qbvs a k = false).
      destruct Ha as (_ & HB & _).
      destruct (qbvs a k) eqn:H; [specialize (HB k H); lia|].
      now rewrite Nat.eqb_refl, Htest.
  - split; [eauto using safety_fv_closed_weaken|exact Htest].
Qed.

Local Lemma safety_q_open_two k f F L q a b :
  closed_Qual (S (S k)) f L q↑ -> f <= F ->
  closed_Qual 0 F L a↑ -> closed_Qual 0 F L b↑ ->
  closed_Qual k F L (open_qual (S k) b (open_qual k a q))↑.
Proof.
  intros Hq Hf Ha Hb.
  destruct (safety_q_open_named k _ _ _ _ _ _ Hq Ha Hf) as (Hqa & Hk).
  destruct (safety_q_open_named (S k) _ _ _ _ _ _ Hqa Hb (Nat.le_refl F)) as
    ((HF & HB & HL) & HS).
  refine (conj HF (conj _ HL)).
  intros x Hx.
  pose proof (HB x Hx) as Hlt.
  assert (Hneq : x <> S k) by congruence.
  assert (Hx' : x <> k).
  { intros ->. unfold open_qual at 1 in Hx.
    destruct (qbvs (open_qual k a q) (S k)).
    - change ((qbvs (open_qual k a q) k && negb (k =? S k)) || qbvs b k = true) in Hx.
      rewrite Hk in Hx. destruct Hb as (_ & Hb & _).
      specialize (Hb k Hx). lia.
    - congruence. }
  lia.
Qed.

Local Lemma safety_ty_open_two T k f F L U V a b :
  closed_ty (S (S k)) f L T -> f <= F ->
  closed_ty 0 F L U -> closed_ty 0 F L V ->
  closed_Qual 0 F L a↑ -> closed_Qual 0 F L b↑ ->
  closed_ty k F L (open_rec_ty (S k) V b (open_rec_ty k U a T)).
Proof.
  revert k. induction T; intros k HC Hle HU HV Ha Hb; inversion HC; subst; simpl;
    try solve [constructor; eauto using safety_q_open_two].
  - constructor. lia.
  - destruct (k =? x) eqn:Hx.
    + rewrite (safety_ty_open_skip _ _ _ _ _ V b HU) by lia.
      eauto using safety_ty_vars_weaken, Nat.le_0_l, Nat.le_refl.
    + change (closed_ty k F L (if S k =? x then V else TVar (varB x))).
      destruct (S k =? x) eqn:Hy.
      * eauto using safety_ty_vars_weaken, Nat.le_0_l, Nat.le_refl.
      * apply Nat.eqb_neq in Hx, Hy. constructor. lia.
Qed.

Local Lemma safety_ty_size_open_name T k x q :
  ty_size (open_rec_ty k (TVar (varF x)) q T) = ty_size T.
Proof.
  revert k. induction T; intros k; simpl; try reflexivity;
    try (rewrite ?IHT1, ?IHT2, ?IHT; reflexivity).
  destruct v; simpl; [reflexivity|]. destruct (k =? i); reflexivity.
Qed.

Local Lemma safety_stp_refl Γ Σ T d e :
  closed_ty 0 (length Γ) (length Σ) T -> qstp Γ Σ d e -> stp Γ Σ T d T e.
Proof.
  remember (ty_size T) as n eqn:Hn.
  revert Γ T d e Hn.
  induction n using lt_wf_ind.
  intros Γ T d e Hn Hcl HQ. destruct T; inversion Hcl; subst; simpl in *; try lia.
  - now apply s_top.
  - match goal with Hx : ?x < length Γ |- _ =>
      destruct (safety_indexr_exists Γ x Hx) as [entry Hentry]
    end.
    eapply s_tvar_refl; eassumption.
  - apply s_all; try assumption.
    + eapply H; [|reflexivity|eassumption|]; [lia|].
      apply qs_sq; [apply safety_subq_refl|assumption].
    + eapply H; [|reflexivity| |].
      * unfold open_ty', open_ty. rewrite !safety_ty_size_open_name. lia.
      * unfold open_ty', open_ty. eapply safety_ty_open_two; simpl;
          eauto using safety_fv_closed, cl_ttvarf; lia.
      * apply qs_sq; [apply safety_subq_refl|].
        unfold openq', openq. eapply safety_q_open_two; simpl;
          eauto using safety_fv_closed; lia.
  - now apply s_base.
  - apply s_fun; try assumption.
    + eapply H; [|reflexivity|eassumption|]; [lia|].
      apply qs_sq; [apply safety_subq_refl|assumption].
    + eapply H; [|reflexivity| |].
      * unfold open_ty', open_ty. rewrite !safety_ty_size_open_name. lia.
      * unfold open_ty', open_ty. eapply safety_ty_open_two; simpl;
          eauto using safety_fv_closed, cl_ttvarf; lia.
      * apply qs_sq; [apply safety_subq_refl|].
        unfold openq', openq. eapply safety_q_open_two; simpl;
          eauto using safety_fv_closed; lia.
  - apply s_ref; try assumption;
      try solve [eapply H; [|reflexivity|eassumption|]; [lia|];
        apply qs_sq; [apply safety_subq_refl|apply safety_qual_const_closed]].
    all: apply qs_sq; [apply safety_subq_refl|assumption].
Qed.

Local Lemma safety_typing_qual_closed Γ φ Σ t T d :
  has_type Γ φ Σ t T d -> closed_Qual 0 (length Γ) (length Σ) d↑.
Proof.
  intros H.
  eapply safety_qual_closed_of_sub; [apply (safety_typing_qual_bound _ _ _ _ _ _ H)|].
  apply safety_qual_join_closed.
  - eauto using safety_typing_phi_closed.
  - apply safety_qual_const_closed.
Qed.

Local Lemma safety_typing_type_closed Γ φ Σ t T d :
  has_type Γ φ Σ t T d -> closed_ty 0 (length Γ) (length Σ) T.
Proof.
  intros H. induction H; try assumption;
    try solve [constructor; eauto using safety_typing_qual_closed, safety_fv_closed_weaken].
  - inversion IHhas_type; subst.
    unfold open_ty. eapply safety_ty_open_two;
      eauto using closed_ty, safety_qual_const_closed, Nat.le_refl.
  - inversion IHhas_type; subst.
    unfold open_ty. eapply safety_ty_open_two;
      eauto using closed_ty, safety_qual_const_closed, Nat.le_refl.
  - eapply safety_ty_vars_weaken; [eassumption|lia|].
    eauto using Nat.lt_le_incl, safety_indexr_bound.
  - inversion IHhas_type1; subst.
    unfold open_ty. eapply safety_ty_open_two;
      eauto using closed_ty, safety_qual_const_closed, Nat.le_refl.
  - inversion IHhas_type1; subst.
    unfold open_ty. eapply safety_ty_open_two;
      eauto using closed_ty, safety_qual_const_closed, Nat.le_refl, safety_typing_qual_closed.
  - apply cl_TRef.
    + eapply safety_ty_vars_weaken; [eassumption|lia|lia].
    + eapply safety_fv_closed_weaken; [|eassumption]; lia.
  - inversion IHhas_type; assumption.
  - exact (proj2 (safety_stp_closed _ _ _ _ _ _ H0)).
Qed.

Local Lemma safety_qual_cast Γ φ Σ t T d e :
  has_type Γ φ Σ t T d ->
  d ⊑↑ e -> e ⊑↑ φ ⊔ {♦} -> kill_sep (local_locs t) e ->
  has_type Γ φ Σ t T e.
Proof.
  intros H Hle Hφ Hkill. eapply t_sub; try eassumption.
  apply safety_stp_refl.
  - eauto using safety_typing_type_closed.
  - apply qs_sq; [exact Hle|].
    eapply safety_qual_closed_of_sub; [exact Hφ|].
    apply safety_qual_join_closed; eauto using safety_typing_phi_closed, safety_qual_const_closed.
Qed.

Local Lemma safety_plus_empty q : q ⋓ ∅ ⊑↑ q /\ q ⊑↑ q ⋓ ∅.
Proof. unfold qqplus. destruct (qfresh q); safety_qpoint. Qed.

Local Lemma safety_sep_left K K' q :
  K' ⊑↑ K -> kill_sep K q -> kill_sep K' q.
Proof. safety_qpoint. Qed.

Local Lemma safety_sep_join_left K L q :
  kill_sep K q -> kill_sep L q -> kill_sep (K ⊔ L) q.
Proof. safety_qpoint. Qed.

Local Lemma safety_sep_join_right K q r :
  kill_sep K q -> kill_sep K r -> kill_sep K (q ⊔ r).
Proof. safety_qpoint. Qed.

Local Lemma safety_sep_fresh K : kill_sep K {♦}.
Proof. safety_qpoint. Qed.

Local Lemma safety_sep_empty K : kill_sep K ∅.
Proof. safety_qpoint. Qed.

Local Lemma safety_sep_open K k q a :
  kill_sep K q -> kill_sep K a -> kill_sep K (open_qual k a q).
Proof.
  unfold open_qual. destruct (qbvs q k); [|auto].
  intros Hq Ha.
  apply safety_sep_join_right; [|exact Ha].
  eapply safety_sep_of_sub; [|exact Hq].
  clear - q k. safety_qpoint.
Qed.

Local Lemma safety_sep_open2 K q a b :
  kill_sep K q -> kill_sep K a -> kill_sep K b ->
  kill_sep K (q <~ᵈ a ; b).
Proof. unfold openq. eauto using safety_sep_open. Qed.

Local Lemma safety_sep_diff K φ q :
  q ⊑↑ qdiff φ K ⊔ {♦} -> kill_sep K q.
Proof.
  intros H. eapply safety_sep_of_sub; [exact H|].
  clear H. safety_qpoint.
Qed.

Local Lemma safety_drop_scope_name b f L x q p :
  f <= x -> closed_Qual b f L q↑ ->
  q ⊑↑ (p ⊔ $!x) ⊔ {♦} -> q ⊑↑ p ⊔ {♦}.
Proof.
  intros Hle (Hclosed & _ & _) Hsub.
  apply safety_qual_le in Hsub as (_ & HF & HB & HL).
  apply safety_qual_le. refine (conj _ (conj _ (conj _ _))).
  - intros _. change (qfresh p || true = true). apply orb_true_r.
  - intros y Hy. pose proof (Hclosed y Hy) as Hlt.
    specialize (HF y Hy). change ((qfvs p y || (y =? x)) || false = true) in HF.
    rewrite orb_false_r, orb_true_iff, Nat.eqb_eq in HF.
    change (qfvs p y || false = true). rewrite orb_false_r.
    destruct HF; [assumption|lia].
  - intros y Hy. specialize (HB y Hy).
    change ((qbvs p y || false) || false = true) in HB.
    change (qbvs p y || false = true). now rewrite orb_false_r in HB.
  - intros y Hy. specialize (HL y Hy).
    change ((qlocs p y || false) || false = true) in HL.
    change (qlocs p y || false = true). now rewrite orb_false_r in HL.
Qed.

Local Lemma safety_typing_sep Γ φ Σ t T q :
  has_type Γ φ Σ t T q -> wf_step t -> kill_sep (local_locs t) q.
Proof.
  intros H. induction H; simpl; intros Hwf; try assumption;
    try solve [apply safety_empty_sep | apply safety_sep_empty | apply safety_sep_fresh].
  - eapply safety_sep_open2; eauto.
  - eapply safety_sep_open2; eauto.
  - subst φd. destruct Hwf as (Hw1 & Hw2 & _).
    apply safety_sep_open2; try assumption;
      apply safety_sep_join_left; eauto using safety_sep_diff, safety_typing_qual_bound.
  - subst φd. destruct Hwf as (Hw1 & Hw2 & _).
    apply safety_sep_open2; try assumption;
      apply safety_sep_join_left; eauto using safety_sep_diff, safety_typing_qual_bound.
  - destruct Hwf as (_ & Hw2 & _). apply safety_sep_join_left; eauto.
  - destruct Hwf as (Hw1 & Hw2 & Hlocal). rewrite Hlocal.
    apply safety_sep_join_left; [|apply safety_empty_sep].
    eapply safety_sep_of_sub.
    + eapply safety_drop_scope_name; [| eassumption | apply (safety_typing_qual_bound _ _ _ _ _ _ H4)].
      lia.
    + apply safety_sep_join_right; [assumption|apply safety_sep_fresh].
  - apply safety_sep_join_left; auto.
Qed.

Local Lemma safety_typing_plus_empty Γ φ Σ t T q :
  has_type Γ φ Σ t T q -> wf_step t -> has_type Γ φ Σ t T (q ⋓ ∅).
Proof.
  intros H Hw. apply safety_qual_cast with (d := q).
  - exact H.
  - exact (proj2 (safety_plus_empty q)).
  - eapply safety_subq_trans; [exact (proj1 (safety_plus_empty q))|].
    exact (safety_typing_qual_bound _ _ _ _ _ _ H).
  - eapply safety_sep_of_sub; [exact (proj1 (safety_plus_empty q))|].
    exact (safety_typing_sep _ _ _ _ _ _ H Hw).
Qed.

Local Lemma safety_typing_tm_closed Γ φ Σ t T q :
  has_type Γ φ Σ t T q -> closed_tm 0 (length Γ) (length Σ) t.
Proof.
  intros H. induction H; try assumption; try solve [constructor; eauto].
  - constructor. eauto using safety_indexr_bound.
  - destruct (safety_sindexr _ _ _ _ H0) as (c & Hc & _).
    constructor. eauto using safety_indexr_bound.
Qed.

Local Lemma safety_scope_locs_closed t b f L :
  closed_tm b f L t -> closed_Qual 0 0 L (local_locs t)↑.
Proof.
  intros H. induction H; simpl; try apply safety_qual_const_closed;
    try assumption; eauto using safety_qual_join_closed.
  apply safety_qual_join_closed; [|assumption].
  clear - H. safety_qpoint.
Qed.

Local Lemma safety_one_loc_closed l L :
  l < L -> closed_Qual 0 0 L (&!l)↑.
Proof. safety_qpoint. Qed.

Local Lemma safety_sep_new_loc (Σ : senv) q :
  closed_Qual 0 0 (length Σ) q↑ -> kill_sep (&!(length Σ)) q.
Proof.
  intros (_ & _ & Hl). unfold kill_sep. apply safety_qual_le.
  refine (conj (fun _ => eq_refl) (conj _ (conj _ _))).
  - intros x Hx. apply andb_true_iff in Hx as [_ Hx]. discriminate Hx.
  - intros x Hx. apply andb_true_iff in Hx as [_ Hx]. discriminate Hx.
  - intros x Hx. change (qlocs q x && (x =? length Σ) = true) in Hx.
    apply andb_true_iff in Hx as [Hmem Hx].
    apply Nat.eqb_eq in Hx. specialize (Hl x Hmem). lia.
Qed.

Local Lemma safety_subq_join_left a a' b c :
  a' ⊑↑ a ⊔ c -> a' ⊔ b ⊑↑ (a ⊔ b) ⊔ c.
Proof. safety_qpoint. Qed.

Local Lemma safety_subq_join_right a b b' c :
  b' ⊑↑ b ⊔ c -> a ⊔ b' ⊑↑ (a ⊔ b) ⊔ c.
Proof. safety_qpoint. Qed.

Local Lemma safety_step_scope_growth t σ t' σ' :
  step t σ t' σ' -> wf_step t -> wf_store σ ->
  local_locs t' ⊑↑ local_locs t ⊔ &!(length σ).
Proof.
  intros H. induction H; simpl; intros Hw Hσ;
    try solve [apply safety_empty_bound];
    try solve [apply safety_join_l].
  - unfold open_tm. rewrite !safety_open_scopes by (simpl; auto).
    apply safety_join_l.
  - destruct Hw as (Ht & Hv & _). unfold open_tm.
    rewrite !safety_open_scopes by (simpl; auto using safety_value_scopes).
    eapply safety_subq_trans; apply safety_join_l.
  - assert (Hvo : sindexr' l o σ = Some v)
      by (rewrite (safety_sindexr_store _ _ _ _ H); assumption).
    destruct (Hσ _ _ _ Hvo) as [Hwf Hval].
    rewrite (safety_value_scopes _ Hval Hwf). apply safety_empty_bound.
  - destruct Hw as (Hv & Ht & Hloc). unfold open_tm.
    rewrite !safety_open_scopes by reflexivity. rewrite Hloc.
    clear - σ. safety_qpoint.
  - eapply safety_subq_trans; [apply safety_join_r|apply safety_join_l].
  - now apply IHstep.
  - now apply IHstep.
  - destruct Hw as (Hw & _). now apply safety_subq_join_left, IHstep.
  - destruct Hw as (_ & Hw & _). now apply safety_subq_join_right, IHstep.
  - now apply IHstep.
  - destruct Hw as (Hw & _). now apply safety_subq_join_left, IHstep.
  - destruct Hw as (_ & Hw & _). now apply safety_subq_join_right, IHstep.
  - destruct Hw as (Hw & _). now apply safety_subq_join_left, IHstep.
  - destruct Hw as (_ & Hw & _). now apply safety_subq_join_right, IHstep.
  - destruct Hw as (Hw & _). now apply safety_subq_join_left, IHstep.
  - now apply safety_subq_join_right, IHstep.
Qed.

Local Lemma safety_step_carries_sep (Σ : senv) t σ t' σ' q :
  length σ = length Σ ->
  step t σ t' σ' -> wf_step t -> wf_store σ ->
  closed_Qual 0 0 (length Σ) q↑ ->
  kill_sep (local_locs t) q ->
  kill_sep (local_locs t') q.
Proof.
  intros Hlen Hstep Hwf Hstore Hq Hsep.
  eapply safety_sep_left.
  - eapply safety_step_scope_growth; eassumption.
  - rewrite Hlen. apply safety_sep_join_left; auto using safety_sep_new_loc.
Qed.

Local Lemma safety_update_scope_sub Σ φ ϰ K Σ' φ' ϰ' q :
  envUpdate Σ φ ϰ K Σ' φ' ϰ' ->
  φ ⊑↑ qdom Σ ->
  kill_sep K q ->
  q ⊑↑ φ -> q ⊑↑ φ'.
Proof.
  intros H. induction H; intros Hφ HK Hq; auto.
  - eauto using safety_subq_trans, safety_join_l.
  - destruct (safety_remove_spec Σ l φ Hφ) as (HF & Hfv & Hbv & Hl).
    assert (Hsep : kill_sep &!l q)
      by eauto using safety_sep_left, safety_loc_in_scope.
    destruct Hsep as (_ & _ & _ & Hsep).
    assert (Havoids : ~ l ∈ₗ q).
    { intros Hmem. specialize (Hsep l).
      change (qlocs q l && (l =? l) = true -> false = true) in Hsep.
      change (qlocs q l = true) in Hmem.
      rewrite Hmem, Nat.eqb_refl in Hsep. discriminate (Hsep eq_refl). }
    apply safety_qual_le in Hq as (Hfresh & Hfree & Hbound & Hloc).
    apply safety_qual_le. refine (conj _ (conj _ (conj _ _))).
    + now rewrite HF.
    + intros x Hx. rewrite Hfv. now apply Hfree.
    + intros x Hx. rewrite Hbv. now apply Hbound.
    + intros x Hx. apply Hl. split.
      * apply Hloc. exact Hx.
      * intro Heq. subst x. contradiction.
Qed.

Local Lemma safety_withc_redex Σ φ ϰ σ l v T q :
  l < length Σ -> has_type [] φ Σ v T q -> kill_sep &!l q ->
  value v -> wf_step v -> wf_senv Σ -> CtxOK [] φ Σ ϰ σ -> wf_store σ ->
  step (twithc l v) σ v (update σ l None) /\
  preserve [] Σ ϰ φ (local_locs (twithc l v)) v T q (update σ l None).
Proof.
  intros Hl Hty Hsep Hv Hwv HΣ HC Hσ. split; [now constructor|].
  assert (Hφ : φ ⊑↑ qdom Σ) by (destruct HC as (_ & _ & ? & _); assumption).
  assert (HC' : CtxOK [] (q_remove Σ l φ) Σ (ϰ ⊔ &!l) (update σ l None))
    by eauto using safety_kill_ctx.
  apply (Preserve Σ ∅ (q_remove Σ l φ) (ϰ ⊔ &!l)); try assumption.
  - apply safety_senv_refl.
  - apply env_kill; [exact Hl|].
    change ((l =? l) || qlocs (local_locs v) l = true).
    now rewrite Nat.eqb_refl.
  - apply safety_empty_bound.
  - apply disj_bot.
  - apply safety_typing_plus_empty; [|exact Hwv].
    apply (safety_value_scope [] φ); try assumption; try reflexivity.
    + eauto using safety_remove_avoid, safety_typing_qual_bound.
    + apply safety_dom_closed.
      destruct HC' as (_ & _ & ? & _). assumption.
  - now apply safety_update_store_wf.
Qed.

Local Lemma safety_subq_loc a b l : a ⊑↑ b -> l ∈ₗ a -> l ∈ₗ b.
Proof. intros (_ & _ & _ & H) Hl. exact (H l Hl). Qed.

Local Lemma safety_sep_at K q l :
  kill_sep K q -> l ∈ₗ K -> kill_sep &!l q.
Proof. eauto using safety_sep_left, safety_loc_in_scope. Qed.

Local Lemma safety_update_locs Σ φ ϰ K K' Σ' φ' ϰ' :
  envUpdate Σ φ ϰ K Σ' φ' ϰ' -> K ⊑↑ K' ->
  envUpdate Σ φ ϰ K' Σ' φ' ϰ'.
Proof.
  intros H Hsub. inversion H; subst;
    eauto using envUpdate, safety_subq_loc.
Qed.

Local Lemma safety_update_scope_fresh Σ φ ϰ K Σ' φ' ϰ' q :
  envUpdate Σ φ ϰ K Σ' φ' ϰ' ->
  φ ⊑↑ qdom Σ ->
  kill_sep K q ->
  q ⊑↑ φ ⊔ {♦} -> q ⊑↑ φ' ⊔ {♦}.
Proof.
  intros H. inversion H; subst; intros; eauto using safety_le_fresh_trans, safety_join_l,
    safety_remove_avoid, safety_sep_at.
Qed.

Local Lemma safety_qqplus_bound q r φ :
  q ⊑↑ φ ⊔ {♦} -> r ⊑↑ φ -> q ⋓ r ⊑↑ φ ⊔ {♦}.
Proof.
  unfold qqplus. destruct (qfresh q); eauto using safety_join_bound, safety_le_fresh_variant.
Qed.

Local Lemma safety_qqplus_monotone q r δ :
  q ⊑↑ r -> q ⋓ δ ⊑↑ r ⋓ δ.
Proof.
  intros H. unfold qqplus. destruct (qfresh q) eqn:Hq, (qfresh r) eqn:Hr.
  - apply safety_join_bound; [eauto using safety_subq_trans, safety_join_l|apply safety_join_r].
  - destruct H as (HF & _). change (Is_true (qfresh q) -> Is_true (qfresh r)) in HF.
    rewrite Hq, Hr in HF. exact (False_rect _ (HF I)).
  - eauto using safety_subq_trans, safety_join_l.
  - exact H.
Qed.

Local Lemma safety_qqplus_sep K q r :
  kill_sep K q -> kill_sep K r -> kill_sep K (q ⋓ r).
Proof.
  unfold qqplus. destruct (qfresh q); eauto using safety_sep_join_right.
Qed.

Local Lemma safety_preserve_unpack Σ φ ϰ K t T q σ :
  preserve [] Σ ϰ φ K t T q σ ->
  exists Σ' d' φ' ϰ',
    Σ' ⊇₂ Σ /\ envUpdate Σ φ ϰ K Σ' φ' ϰ' /\
    d' ⊑↑ φ' /\ wf_senv Σ' /\ CtxOK [] φ' Σ' ϰ' σ /\
    (Σ → Σ' ∋ q ⊕ d') /\ has_type [] φ' Σ' t T (q ⋓ d') /\
    wf_store σ /\ wf_step t /\ kill_sep (local_locs t) d'.
Proof.
  intros H. destruct H as [Σ' d' φ' ϰ' He Hu Hδ HW HC Hd HT HS HTw].
  destruct (qfresh q) eqn:Hq.
  - exists Σ', d', φ', ϰ'.
    refine (conj He (conj Hu (conj Hδ (conj HW (conj HC (conj Hd (conj HT
      (conj HS (conj HTw _))))))))).
    eapply safety_sep_of_sub with (b := q ⋓ d').
    + unfold qqplus. rewrite Hq. apply safety_join_r.
    + exact (safety_typing_sep _ _ _ _ _ _ HT HTw).
  - exists Σ', (∅), φ', ϰ'.
    refine (conj He (conj Hu (conj _ (conj HW (conj HC (conj _ (conj _
      (conj HS (conj HTw _))))))))).
    + apply safety_empty_bound.
    + apply disj_bot.
    + unfold qqplus in *. now rewrite Hq in *.
    + apply safety_sep_empty.
Qed.

Local Lemma safety_disjointq_old Σ Σ' q r d :
  (Σ → Σ' ∋ q ⊕ d) -> (Σ → Σ' ∋ r ⊕ d).
Proof. intros H. inversion H; subst; eauto using disjointq. Qed.

Local Lemma safety_preserve_sub Σ φ ϰ σ σ' t t' T d U e :
  step t σ t' σ' -> wf_step t -> wf_store σ -> CtxOK [] φ Σ ϰ σ ->
  stp [] Σ T d U e -> e ⊑↑ φ ⊔ {♦} -> kill_sep (local_locs t) e ->
  preserve [] Σ ϰ φ (local_locs t) t' T d σ' ->
  preserve [] Σ ϰ φ (local_locs t) t' U e σ'.
Proof.
  intros Hstep Hwf Hσ HC Hsub Hle Hsep Hpres.
  destruct (safety_preserve_unpack _ _ _ _ _ _ _ _ Hpres)
    as (Σ' & d' & φ' & ϰ' & He & Hu & Hδ & HΣ' & HC' & Hd & Hty & Hσ' & Hw' & Hsepδ).
  destruct HC as (_ & Hlen & Hφ & _).
  assert (Hlen' : φ' ⊑↑ qdom Σ') by (destruct HC' as (_ & _ & ? & _); assumption).
  assert (Hbound : e ⋓ d' ⊑↑ φ' ⊔ {♦}).
  { eapply safety_qqplus_bound; [|exact Hδ].
    eapply safety_update_scope_fresh; eassumption. }
  assert (Hclosed : closed_Qual 0 0 (length Σ) e↑).
  { eapply safety_qual_closed_of_sub; [exact Hle|].
    eauto using safety_qual_join_closed, safety_dom_closed, safety_qual_const_closed. }
  apply (Preserve Σ' d' φ' ϰ'); try assumption.
  - eauto using safety_disjointq_old.
  - eapply t_sub; [exact Hty | | exact Hbound |].
    + eapply safety_stp_requalify.
      * eapply safety_stp_weaken; eassumption.
      * apply qs_sq.
        -- apply safety_qqplus_monotone. eauto using safety_subqual_of_stp.
        -- eapply safety_qual_closed_of_sub; [exact Hbound|].
           eauto using safety_qual_join_closed, safety_dom_closed, safety_qual_const_closed.
    + apply safety_qqplus_sep; [|exact Hsepδ].
      eapply safety_step_carries_sep; eassumption.
Qed.

Local Lemma safety_preserve_ref_ctx Σ φ ϰ σ' t t' T d :
  closed_ty 0 0 (length Σ) T -> ♦∉ d ->
  preserve [] Σ ϰ φ (local_locs t) t' T d σ' ->
  preserve [] Σ ϰ φ (local_locs (tref t)) (tref t') (TRef d T) {♦} σ'.
Proof.
  intros HT Hnf HP.
  inversion HP; subst.
  apply (Preserve Σ' ∅ φ' ϰ'); try assumption.
  - apply safety_empty_bound.
  - apply disj_bot.
  - apply safety_typing_plus_empty; [|exact H7].
    apply t_ref; [| |exact Hnf].
    + unfold qqplus in H5. destruct (qfresh d); [exfalso; exact (Hnf I)|assumption].
    + eapply safety_ty_closed_weaken; [|exact HT].
      eauto using safety_senv_length.
Qed.

Local Lemma safety_preserve_deref_ctx Σ φ ϰ σ σ' t t' T q d :
  step t σ t' σ' -> wf_step t -> wf_store σ -> CtxOK [] φ Σ ϰ σ ->
  ♦∉ q -> q ⊑↑ φ -> kill_sep (local_locs t) q ->
  preserve [] Σ ϰ φ (local_locs t) t' (TRef q T) d σ' ->
  preserve [] Σ ϰ φ (local_locs (!t)) (!t') T q σ'.
Proof.
  intros Hstep Hwf Hσ HC Hnf Hq Hsep HP.
  destruct HC as (_ & Hlen & Hφ & _).
  destruct (safety_preserve_unpack _ _ _ _ _ _ _ _ HP)
    as (Σ' & δ & φ' & ϰ' & He & Hu & Hδ & HΣ' & HC' & Hd & Hty & Hσ' & Hw' & Hsepδ).
  apply (Preserve Σ' ∅ φ' ϰ'); try assumption.
  - apply safety_empty_bound.
  - apply disj_bot.
  - apply safety_typing_plus_empty; [|exact Hw'].
    eapply t_deref; [exact Hty | exact Hnf | |].
    + eapply safety_update_scope_sub; eassumption.
    + eapply safety_step_carries_sep; try eassumption.
      eapply safety_qual_closed_of_sub; [exact Hq|eauto using safety_dom_closed].
Qed.

Local Lemma safety_sep_sym a b : kill_sep a b -> kill_sep b a.
Proof. safety_qpoint. Qed.

Local Lemma safety_preserve_withc_ctx Σ φ ϰ σ' t t' T q l :
  l < length Σ -> kill_sep &!l q ->
  preserve [] Σ ϰ φ (local_locs t) t' T q σ' ->
  preserve [] Σ ϰ φ (local_locs (twithc l t)) (twithc l t') T q σ'.
Proof.
  intros Hl Hsep HP.
  destruct (safety_preserve_unpack _ _ _ _ _ _ _ _ HP)
    as (Σ' & δ & φ' & ϰ' & He & Hu & Hδ & HΣ' & HC' & Hd & Hty & Hσ' & Hw' & Hsepδ).
  apply (Preserve Σ' δ φ' ϰ'); try assumption.
  - eapply safety_update_locs; [exact Hu|apply safety_join_r].
  - simpl. apply t_withc.
    + pose proof (safety_senv_length _ _ He). lia.
    + exact Hty.
    + exact (safety_typing_type_closed _ _ _ _ _ _ Hty).
    + exact (safety_typing_qual_closed _ _ _ _ _ _ Hty).
    + apply safety_qqplus_sep; [exact Hsep|].
      inversion Hd; subst.
      * apply safety_sep_empty.
      * apply safety_sep_sym, safety_sep_new_loc, safety_one_loc_closed.
        exact Hl.
Qed.

Local Lemma safety_preserve_withr_ctx Σ φ φd ϰ σ σ' t1 t1' t2 T1 d1 T2 d2 :
  step t1 σ t1' σ' -> wf_step t1 -> wf_store σ -> CtxOK [] φ Σ ϰ σ ->
  wf_step t2 -> local_locs t2 = ∅ -> ♦∉ d1 ->
  closed_ty 0 0 (length Σ) T2 -> closed_Qual 0 0 (length Σ) d2↑ ->
  closed_tm 2 0 (length Σ) t2 ->
  has_type [(bind_tm, false, TRef d1 T1, {♦}); (bind_tm, true, TUnit, {♦})]
    (φd ⊔ $!1) Σ (t2 <~²ᵗ ([] : tenv)) T2 d2 ->
  φd ⊑↑ φ -> kill_sep (local_locs t1) φd ->
  preserve [] Σ ϰ φ (local_locs t1) t1' T1 d1 σ' ->
  preserve [] Σ ϰ φ (local_locs (twithr t1 t2)) (twithr t1' t2) T2 d2 σ'.
Proof.
  intros Hstep Hw1 Hσ HC Hw2 Hloc Hnf HT2 Hd2 HTm Hbody Hφd Hsep HP.
  destruct HC as (_ & Hlen & Hφ & _).
  destruct (safety_preserve_unpack _ _ _ _ _ _ _ _ HP)
    as (Σ' & δ & φ' & ϰ' & He & Hu & Hδ & HΣ' & HC' & Hd & Hty & Hσ' & Hw' & Hsepδ).
  pose proof (safety_senv_length _ _ He) as HL.
  assert (Hinit : has_type [] φ' Σ' t1' T1 d1).
  { unfold qqplus in Hty. destruct (qfresh d1); [exfalso; exact (Hnf I)|exact Hty]. }
  apply (Preserve Σ' ∅ φ' ϰ'); try assumption.
  - eapply safety_update_locs; [exact Hu|apply safety_join_l].
  - apply safety_empty_bound.
  - apply disj_bot.
  - apply safety_typing_plus_empty; [|simpl; auto].
    eapply t_withr with (φd := φd); try eassumption.
    + eauto using safety_ty_closed_weaken.
    + eauto using safety_locs_closed_weaken.
    + eauto using safety_tm_closed_weaken.
    + eauto using safety_typing_weaken.
    + eapply safety_update_scope_sub; eassumption.
    + eapply safety_step_carries_sep; try eassumption.
      eapply safety_qual_closed_of_sub; [exact Hφd|eauto using safety_dom_closed].
  - simpl. auto.
Qed.

Local Lemma safety_scope_fresh t : qfresh (local_locs t) = false.
Proof.
  induction t; cbn [local_locs qor qfresh fst]; try reflexivity; try assumption;
    change ((qfresh (local_locs t1) || qfresh (local_locs t2)) = false);
    now rewrite IHt1, IHt2.
Qed.

Local Lemma safety_scope_diff_intro a p K :
  qfresh K = false -> a ⊑↑ p -> kill_sep K a -> a ⊑↑ qdiff p K.
Proof.
  intros Hfalse Hle Hsep.
  apply safety_qual_le in Hle as (HQ & HF & HB & HL).
  unfold kill_sep in Hsep. apply safety_qual_le in Hsep as (_ & HSf & HSb & HSl).
  apply safety_qual_le. refine (conj _ (conj _ (conj _ _))).
  - intro H. change (qfresh p && negb (qfresh K) = true).
    now rewrite (HQ H), Hfalse.
  - intros x Hx. change (qfvs p x && negb (qfvs K x) = true).
    rewrite (HF x Hx). destruct (qfvs K x) eqn:Hk; [|reflexivity].
    specialize (HSf x ltac:(change (qfvs a x && qfvs K x = true); now rewrite Hx, Hk)).
    discriminate.
  - intros x Hx. change (qbvs p x && negb (qbvs K x) = true).
    rewrite (HB x Hx). destruct (qbvs K x) eqn:Hk; [|reflexivity].
    specialize (HSb x ltac:(change (qbvs a x && qbvs K x = true); now rewrite Hx, Hk)).
    discriminate.
  - intros x Hx. change (qlocs p x && negb (qlocs K x) = true).
    rewrite (HL x Hx). destruct (qlocs K x) eqn:Hk; [|reflexivity].
    specialize (HSl x ltac:(change (qlocs a x && qlocs K x = true); now rewrite Hx, Hk)).
    discriminate.
Qed.

Local Lemma safety_step_scope_difference Σ Σ' φ φ' ϰ ϰ' t t' σ σ' :
  CtxOK [] φ Σ ϰ σ -> wf_store σ -> wf_step t -> step t σ t' σ' ->
  envUpdate Σ φ ϰ (local_locs t) Σ' φ' ϰ' ->
  qdiff φ (local_locs t) ⊑↑ qdiff φ' (local_locs t').
Proof.
  intros (_ & Hlen & Hφ & _) Hσ Hwf Hstep Hu.
  set (p := qdiff φ (local_locs t)).
  assert (Hp : p ⊑↑ φ) by apply safety_diff_le.
  assert (Hs : kill_sep (local_locs t) p)
    by (apply (safety_sep_diff (local_locs t) φ p); apply safety_join_l).
  apply safety_scope_diff_intro.
  - apply safety_scope_fresh.
  - eauto using safety_update_scope_sub.
  - eapply safety_step_carries_sep; eauto.
    eapply safety_qual_closed_of_sub; [exact Hp|now apply safety_dom_closed].
Qed.

Local Lemma safety_disjointq_sep_old Σ Σ' q δ K :
  (Σ → Σ' ∋ q ⊕ δ) ->
  closed_Qual 0 0 (length Σ) K↑ -> kill_sep K δ.
Proof.
  intros H HK. inversion H; subst; [apply safety_sep_empty|].
  assert (Hsep : kill_sep (&!(length Σ)) K) by now apply safety_sep_new_loc.
  clear - Hsep. safety_qpoint.
Qed.

Local Lemma safety_alloc_initial Σ φ ϰ σ v T q :
  has_type [] φ Σ v T q -> ♦∉ q ->
  wf_step v -> value v -> vtp Σ ϰ φ v T q ->
  wf_store σ -> wf_senv Σ -> CtxOK [] φ Σ ϰ σ ->
  wf_senv ([(T,q)] :: Σ) /\
  CtxOK [] (φ ⊔ &!(length Σ)) ([(T,q)] :: Σ) ϰ (Some [v] :: σ) /\
  wf_store (Some [v] :: σ) /\ kill_sep ϰ q.
Proof.
  intros Hty Hnf Hw Hv Hvtp Hσ HΣ HC.
  assert (Hq : q ⊑↑ φ).
  { apply safety_bound_without_fresh; [exact Hnf|eauto using safety_typing_qual_bound]. }
  assert (Hsep : kill_sep ϰ q).
  { destruct HC as (_ & _ & _ & _ & Hsep & _). eauto using safety_sep_of_sub. }
  refine (conj _ (conj _ (conj _ Hsep))).
  - apply safety_senv_cons_wf; try assumption.
    + exact (safety_typing_type_closed _ _ _ _ _ _ Hty).
    + exact (safety_typing_qual_closed _ _ _ _ _ _ Hty).
  - apply safety_alloc_ctx; try assumption.
    eapply safety_vtp_rescope.
    + eapply safety_vtp_weaken; [apply safety_senv_cons_ext|exact Hvtp].
    + eauto using safety_subq_trans, safety_join_l.
    + exact Hsep.
  - eauto using safety_cons_store_wf.
Qed.

Local Lemma safety_ref_redex_typed_value Σ φ ϰ σ v T q :
  has_type [] φ Σ v T q -> ♦∉ q ->
  wf_step v -> value v -> vtp Σ ϰ φ v T q ->
  wf_store σ -> wf_senv Σ -> CtxOK [] φ Σ ϰ σ ->
  exists t' σ', step (tref v) σ t' σ' /\
    preserve [] Σ ϰ φ (local_locs (tref v)) t' (TRef q T) {♦} σ'.
Proof.
  intros Hty Hnf Hw Hv Hvtp Hσ HΣ HC.
  destruct (safety_alloc_initial _ _ _ _ _ _ _ Hty Hnf Hw Hv Hvtp Hσ HΣ HC)
    as (HΣ' & HC' & Hσ' & Hsep).
  assert (Hlen : length σ = length Σ) by (destruct HC as (_ & ? & _); assumption).
  pose proof (safety_typing_type_closed _ _ _ _ _ _ Hty) as HT.
  pose proof (safety_typing_qual_closed _ _ _ _ _ _ Hty) as Hq.
  exists (&‖σ‖), (Some [v] :: σ). split; [now constructor|].
  rewrite Hlen.
  set (l := length Σ).
  set (Σ' := [(T,q)] :: Σ).
  set (φ' := φ ⊔ &!l).
  assert (HA : &!l ⊑↑ φ') by apply safety_join_r.
  assert (Hφ' : φ' ⊑↑ qdom Σ') by (destruct HC' as (_ & _ & ? & _); assumption).
  apply (Preserve Σ' (&!l) φ' ϰ); try assumption.
  - apply safety_senv_cons_ext.
  - now apply env_fresh.
  - eapply disj_loc; eassumption || reflexivity.
  - eapply safety_qual_cast with (d := &!l).
    + apply t_loc; try assumption.
      * now apply safety_dom_closed.
      * unfold Σ', l. simpl. now rewrite Nat.eqb_refl.
      * unfold Σ'. simpl. eauto using safety_ty_closed_weaken, Nat.le_succ_diag_r.
      * unfold Σ'. simpl. eauto using safety_locs_closed_weaken, Nat.le_succ_diag_r.
    + apply safety_join_r.
    + apply safety_join_bound; [apply safety_join_r|auto using safety_le_fresh_variant].
    + apply safety_empty_sep.
  - exact I.
Qed.

Local Lemma safety_withr_redex_opened_body Σ φ ϰ σ v body T q U d :
  has_type [] φ Σ v T q -> ♦∉ q ->
  wf_step v -> value v -> vtp Σ ϰ φ v T q ->
  wf_store σ -> wf_senv Σ -> CtxOK [] φ Σ ϰ σ ->
  closed_Qual 0 0 (length Σ) d↑ ->
  wf_step (twithr v body) ->
  has_type [] (φ ⊔ &!(length Σ)) ([(T,q)] :: Σ)
    (body <~ᵗ tunit ; (tloc (length Σ) 0)) U d ->
  exists t' σ', step (twithr v body) σ t' σ' /\
    preserve [] Σ ϰ φ (local_locs (twithr v body)) t' U d σ'.
Proof.
  intros Hty Hnf Hw Hv Hvtp Hσ HΣ HC Hd Hwsrc Hopened.
  assert (Hlen : length σ = length Σ) by (destruct HC as (_ & ? & _); assumption).
  destruct (safety_alloc_initial _ _ _ _ _ _ _ Hty Hnf Hw Hv Hvtp Hσ HΣ HC)
    as (HΣ' & HC' & Hσ' & Hsep).
  exists (twithc (length σ) (body <~ᵗ tunit ; (tloc (length σ) 0))), (Some [v] :: σ).
  assert (Hstep : step (twithr v body) σ (twithc (length σ) (body <~ᵗ tunit ; (tloc (length σ) 0))) (Some [v] :: σ))
    by now constructor.
  destruct (safety_step_wf _ _ _ _ Hstep Hwsrc Hσ) as [Hw' _].
  split; [exact Hstep|].
  rewrite Hlen in Hw' |- *.
  apply (Preserve ([(T,q)] :: Σ) ∅ (φ ⊔ &!(length Σ)) ϰ); try assumption.
  - apply safety_senv_cons_ext.
  - now apply env_fresh.
  - apply safety_empty_bound.
  - apply disj_bot.
  - apply safety_typing_plus_empty; [|exact Hw'].
    apply t_withc; try assumption.
    + simpl. lia.
    + exact (safety_typing_type_closed _ _ _ _ _ _ Hopened).
    + simpl. eauto using safety_locs_closed_weaken, Nat.le_succ_diag_r.
    + now apply safety_sep_new_loc.
Qed.

Local Lemma safety_ctx_live_not_killed Σ ϰ φ σ l :
  CtxOK [] φ Σ ϰ σ -> l ∈ₗ φ -> ~ l ∈ₗ ϰ.
Proof.
  intros (_ & _ & _ & _ & Hsep & _) Hlive Hdead.
  destruct Hsep as (_ & _ & _ & Hsep).
  specialize (Hsep l).
  change (qlocs φ l && qlocs ϰ l = true -> false = true) in Hsep.
  change (qlocs φ l = true) in Hlive.
  change (qlocs ϰ l = true) in Hdead.
  rewrite Hlive, Hdead in Hsep. discriminate (Hsep eq_refl).
Qed.

Local Lemma safety_extend_arena (Σ : senv) l (c c' : senvs) :
  indexr l Σ = Some c -> c' ⊇ c -> (update Σ l c') ⊇₂ Σ.
Proof.
  intros Hc Hprefix k cp Hk.
  rewrite safety_indexr_update, Hk.
  destruct (k =? l) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst k. rewrite Hc in Hk. inversion Hk; subst cp.
    exists c'. auto.
  - exists cp. split; [reflexivity|exists []; reflexivity].
Qed.

Local Lemma safety_ctx_replace_arena Σ ϰ φ σ l c c' s s' :
  CtxOK [] φ Σ ϰ σ -> l ∈ₗ φ ->
  indexr l Σ = Some c -> indexr l σ = Some (Some s) ->
  c' ⊇ c -> length c' = length s' ->
  (forall o T q, indexr o c' = Some (T,q) ->
    exists v, indexr o s' = Some v /\ value v /\
       (q ⊑↑ φ -> vtp (update Σ l c') ϰ φ v T q)) ->
  (update Σ l c') ⊇₂ Σ /\
  length (update Σ l c') = length Σ /\
  CtxOK [] φ (update Σ l c') ϰ (update σ l (Some s')).
Proof.
  intros HC Hlive Hc Hs Hprefix Hlen' Hvals.
  pose proof (safety_ctx_live_not_killed _ _ _ _ _ HC Hlive) as Hnot.
  destruct HC as (_ & Hlen & Hφ & Hϰ & Hsep & Hstore).
  pose proof (safety_extend_arena Σ l c c' Hc Hprefix) as Hext.
  refine (conj Hext _).
  assert (HL : length (update Σ l c') = length Σ) by apply safety_update_length.
  split; [exact HL|].
  assert (HL' : length (update σ l (Some s')) = length (update Σ l c')).
  { now rewrite !safety_update_length. }
  assert (Hdom : qdom (update Σ l c') = qdom Σ)
    by (unfold qdom, n_dom; now rewrite HL).
  assert (Hφ' : φ ⊑↑ qdom (update Σ l c')) by now rewrite Hdom.
  assert (Hϰ' : closed_Qual 0 0 (length (update Σ l c')) ϰ↑) by now rewrite HL.
  refine (conj (safety_ctx_dom _ _ HL') (conj HL' (conj Hφ' (conj Hϰ' (conj Hsep _))))).
  intros k o cp T q. rewrite !safety_indexr_update.
  destruct (k =? l) eqn:Heq.
  - apply Nat.eqb_eq in Heq. subst k. rewrite Hc, Hs. simpl.
    split; [tauto|].
    intros _ _ HCp. inversion HCp; subst cp.
    exists s'. split; [auto|exact (Hvals o T q)].
  - destruct (Hstore k o cp T q) as [Hdead Hctx].
    split; [exact Hdead|].
    intros Hk Hp Hcp.
    destruct (Hctx Hk Hp Hcp) as (sp & Hsp & HV).
    exists sp. split; [exact Hsp|].
    intros Ho. destruct (HV Ho) as (v & Hv & Hval & Hvt).
    exists v. refine (conj Hv (conj Hval _)).
    intros Hq. eapply safety_vtp_weaken; eauto.
Qed.

Local Lemma safety_loc_qualifier Σ φ t T d l o :
  has_type [] φ Σ t T d -> t = &(l,o) -> &!l ⊑↑ d.
Proof.
  intros H. remember ([] : tenv) as Γ eqn:HG.
  induction H; subst; intros Ht; try discriminate.
  - inversion Ht; subst. apply safety_subq_refl.
  - eapply safety_subq_trans; [now apply IHhas_type|eauto using safety_subqual_of_stp].
Qed.

Local Lemma safety_refat_redex_typed_value Σ φ ϰ σ v l o T q U e d :
  has_type [] φ Σ v T q -> ♦∉ q ->
  has_type [] φ Σ &(l,o) (TRef e U) d ->
  wf_step v -> value v -> vtp Σ ϰ φ v T q ->
  wf_store σ -> wf_senv Σ -> CtxOK [] φ Σ ϰ σ ->
  exists t' σ', step (trefat v &(l,o)) σ t' σ' /\
    preserve [] Σ ϰ φ (local_locs (trefat v &(l,o))) t' (TRef q T) d σ'.
Proof.
  intros Hty Hnf Htarget Hw Hv Hvtp Hσ HΣ HC.
  pose proof (safety_typing_type_closed _ _ _ _ _ _ Hty) as HT.
  pose proof (safety_typing_qual_closed _ _ _ _ _ _ Hty) as HQ.
  destruct (safety_loc_lookup _ _ _ _ _ _ Htarget) as (Hl & W & r & Hlook).
  destruct (safety_sindexr _ _ _ _ Hlook) as (c & Hc & Ho).
  pose proof (safety_ctx_live_not_killed _ _ _ _ _ HC Hl) as Hnot.
  destruct HC as (_ & Hlen & Hφ & Hϰ & Hsep & Hstore).
  destruct (proj2 (Hstore l o c W r) Hnot Hl Hc) as (s & (Hs & Hsize) & _).
  assert (HC : CtxOK [] φ Σ ϰ σ).
  { refine (conj (safety_ctx_dom _ _ Hlen) (conj Hlen (conj Hφ (conj Hϰ (conj Hsep Hstore))))). }
  set (c' := (T,q) :: c).
  set (Σ' := update Σ l c').
  assert (HP : c' ⊇ c) by (exists [(T,q)]; reflexivity).
  assert (HL : length c' = length (v :: s)) by exact (f_equal S Hsize).
  pose proof (safety_extend_arena Σ l c c' Hc HP) as Hext.
  destruct (safety_ctx_replace_arena _ _ _ _ _ _ _ _ _ HC Hl Hc Hs HP HL)
    as (_ & HL' & HC').
  { intros i V p Hlookup.
    unfold c' in Hlookup. simpl in Hlookup. destruct (i =? length c) eqn:Hi.
    - inversion Hlookup; subst V p. exists v. split.
      + simpl. rewrite <- Hsize, Hi. reflexivity.
      + split; [exact Hv|]. intros _. eapply safety_vtp_weaken; eassumption.
    - destruct (proj2 (Hstore l i c V p) Hnot Hl Hc)
        as (ss & (Hss & _) & Hget).
      rewrite Hs in Hss. inversion Hss; subst ss.
      destruct (Hget Hlookup) as (w & Hwo & Hval & HV).
      exists w. split.
      + simpl. now rewrite <- Hsize, Hi.
      + split; [exact Hval|]. intros Hproj.
        eapply safety_vtp_weaken; [exact Hext|now apply HV]. }
  change (length Σ' = length Σ) in HL'.
  change (@indexr senvs l Σ = Some c) in Hc.
  exists &(l,length s), (cinsert σ l v). split; [eauto using step_refat|].
  rewrite (safety_cinsert_as_update _ _ _ _ Hs).
  apply (Preserve Σ' ∅ φ ϰ); try assumption.
  - now apply env_phi.
  - apply safety_empty_bound.
  - intros k ck Hlook'.
    unfold Σ' in Hlook'. rewrite safety_indexr_update in Hlook'.
    rewrite HL'. destruct (k =? l) eqn:Hk.
    + apply Nat.eqb_eq in Hk. subst k. rewrite Hc in Hlook'.
      inversion Hlook'; subst ck. split; [simpl; lia|].
      intros i V p Hi. unfold c' in Hi. simpl in Hi.
      destruct (i =? length c).
      * inversion Hi; subst. auto.
      * destruct (HΣ _ _ Hc) as [_ Hcells]. eapply Hcells; eassumption.
    + now apply (HΣ k ck).
  - apply disj_bot.
  - apply safety_typing_plus_empty; [|exact I].
    eapply safety_qual_cast with (d := &!l).
    + apply t_loc; try assumption.
      * change (closed_Qual 0 0 (length Σ') φ↑).
        rewrite HL'. now apply safety_dom_closed.
      * assert (Hix : indexr l Σ' = Some c').
        { unfold Σ'. now rewrite safety_indexr_update, Nat.eqb_refl, Hc. }
        eapply safety_sindexr_intro; [exact Hix|].
        unfold c'. simpl. now rewrite <- Hsize, Nat.eqb_refl.
      * change (closed_ty 0 0 (length Σ') T). now rewrite HL'.
      * change (closed_Qual 0 0 (length Σ') q↑). now rewrite HL'.
      * now apply safety_loc_in_scope.
    + eapply safety_loc_qualifier; [exact Htarget|reflexivity].
    + exact (safety_typing_qual_bound _ _ _ _ _ _ Htarget).
    + apply safety_empty_sep.
  - eapply safety_change_cell_wf; [exact Hs| |exact Hσ].
    intros i w Hlookup. simpl in Hlookup.
    destruct (i =? length s).
    + inversion Hlookup; subst. auto.
    + auto.
  - exact I.
Qed.

Local Lemma safety_ctx_scope Σ φ ϰ σ :
  CtxOK [] φ Σ ϰ σ -> φ ⊑↑ qdom Σ.
Proof. intros (_ & _ & H & _). exact H. Qed.

Local Lemma safety_ctx_length Σ φ ϰ σ :
  CtxOK [] φ Σ ϰ σ -> length σ = length Σ.
Proof. intros (_ & H & _). exact H. Qed.

Local Lemma safety_keep_value Σ Σ' φ φ' ϰ ϰ' σ σ' K v T d :
  CtxOK [] φ Σ ϰ σ -> CtxOK [] φ' Σ' ϰ' σ' ->
  Σ' ⊇₂ Σ -> envUpdate Σ φ ϰ K Σ' φ' ϰ' ->
  has_type [] φ Σ v T d -> value v -> kill_sep K d ->
  has_type [] φ' Σ' v T d.
Proof.
  intros HC HC' HE HU HT HV HS.
  apply (safety_value_scope [] φ); try assumption; try reflexivity.
  - eapply safety_typing_weaken; eassumption.
  - eapply safety_update_scope_fresh; try eassumption.
    + exact (safety_ctx_scope _ _ _ _ HC).
    + exact (safety_typing_qual_bound _ _ _ _ _ _ HT).
  - apply safety_dom_closed. exact (safety_ctx_scope _ _ _ _ HC').
Qed.

Local Lemma safety_carry_scoped_typing Σ Σ' φ φ' ϰ ϰ' σ σ' a a' b T d :
  CtxOK [] φ Σ ϰ σ -> CtxOK [] φ' Σ' ϰ' σ' -> wf_store σ ->
  wf_step a -> step a σ a' σ' ->
  Σ' ⊇₂ Σ -> envUpdate Σ φ ϰ (local_locs a) Σ' φ' ϰ' ->
  has_type [] (qdiff φ (local_locs a)) Σ b T d ->
  has_type [] (qdiff φ' (local_locs a')) Σ' b T d.
Proof.
  intros HC HC' Hσ HW HR HE HU HT.
  apply (safety_typing_scope_weaken _ _ _ _ _ _
    (safety_typing_weaken _ _ _ _ _ _ _ HE HT)).
  - eapply safety_step_scope_difference; eassumption.
  - eapply safety_qual_closed_of_sub; [apply safety_diff_le|].
    apply safety_dom_closed. exact (safety_ctx_scope _ _ _ _ HC').
Qed.

Local Lemma safety_scope_over_value Σ φ t T d v :
  value v -> wf_step v -> has_type [] φ Σ t T d ->
  has_type [] (qdiff φ (local_locs v)) Σ t T d.
Proof.
  intros Hv Hw Ht.
  apply (safety_typing_scope_weaken _ _ _ _ _ _ Ht).
  - apply safety_scope_diff_intro;
      auto using safety_scope_fresh, safety_subq_refl.
    rewrite (safety_value_scopes _ Hv Hw). apply safety_empty_sep.
  - eapply safety_qual_closed_of_sub; [apply safety_diff_le|].
    exact (safety_typing_phi_closed _ _ _ _ _ _ Ht).
Qed.

Local Lemma safety_preserve_assign_l_ctx Σ φ ϰ σ σ' a a' b T d q :
  CtxOK [] φ Σ ϰ σ -> wf_store σ -> wf_step (tassign a b) ->
  step a σ a' σ' -> ♦∉ q ->
  has_type [] (qdiff φ (local_locs a)) Σ b T q ->
  kill_sep (local_locs b) d ->
  preserve [] Σ ϰ φ (local_locs a) a' (TRef q T) d σ' ->
  preserve [] Σ ϰ φ (local_locs (tassign a b)) (tassign a' b) TUnit ∅ σ'.
Proof.
  intros HC Hσ HW HR Hnf HT HB HP.
  destruct (safety_preserve_unpack _ _ _ _ _ _ _ _ HP)
    as (Σ' & δ & φ' & ϰ' & HE & HU & Hδ & HF & HC' & HD & HT' & Hσ' & HA' & Hextra).
  pose proof (step_c_assign_l a a' b σ σ' HR) as Hstep.
  destruct (safety_step_wf _ _ _ _ Hstep HW Hσ) as [HW' _].
  apply (Preserve Σ' ∅ φ' ϰ'); try assumption.
  - eapply safety_update_locs; [exact HU|apply safety_join_l].
  - apply safety_empty_bound.
  - apply disj_bot.
  - eapply t_assign with (φd := qdiff φ' (local_locs a')); try eassumption; try reflexivity.
    + exact (safety_carry_scoped_typing Σ Σ' φ φ' ϰ ϰ' σ σ' a a' b T q
        HC HC' Hσ (proj1 HW) HR HE HU HT).
    + apply safety_qqplus_sep; [exact HB|].
      eapply safety_disjointq_sep_old; [exact HD|].
      eapply safety_scope_locs_closed.
      exact (safety_typing_tm_closed _ _ _ _ _ _ HT).
Qed.

Local Lemma safety_preserve_refat_r_ctx Σ φ ϰ σ σ' a b b' T q U r d :
  CtxOK [] φ Σ ϰ σ -> wf_store σ -> wf_step (trefat a b) ->
  step b σ b' σ' -> ♦∉ q ->
  has_type [] (qdiff φ (local_locs b)) Σ a T q ->
  kill_sep (local_locs a) d ->
  preserve [] Σ ϰ φ (local_locs b) b' (TRef r U) d σ' ->
  preserve [] Σ ϰ φ (local_locs (trefat a b)) (trefat a b') (TRef q T) d σ'.
Proof.
  intros HC Hσ HW HR Hnf HT HB HP.
  destruct (safety_preserve_unpack _ _ _ _ _ _ _ _ HP)
    as (Σ' & δ & φ' & ϰ' & HE & HU & Hδ & HF & HC' & HD & HT' & Hσ' & HA' & Hextra).
  pose proof (step_c_refat_r a b b' σ σ' HR) as Hstep.
  destruct (safety_step_wf _ _ _ _ Hstep HW Hσ) as [HW' _].
  apply (Preserve Σ' δ φ' ϰ'); try assumption.
  - eapply safety_update_locs; [exact HU|apply safety_join_r].
  - eapply t_refat with (φd := qdiff φ' (local_locs b')); try eassumption; try reflexivity.
    + exact (safety_carry_scoped_typing Σ Σ' φ φ' ϰ ϰ' σ σ' b b' a T q
        HC HC' Hσ (proj1 (proj2 HW)) HR HE HU HT).
    + apply safety_qqplus_sep; [exact HB|].
      eapply safety_disjointq_sep_old; [exact HD|].
      eapply safety_scope_locs_closed.
      exact (safety_typing_tm_closed _ _ _ _ _ _ HT).
Qed.

Local Lemma safety_preserve_assign_r_ctx Σ φ ϰ σ σ' v b b' T d q :
  CtxOK [] φ Σ ϰ σ -> wf_store σ -> wf_step (tassign v b) ->
  value v -> step b σ b' σ' -> ♦∉ q ->
  has_type [] φ Σ v (TRef q T) d ->
  kill_sep (local_locs b) d ->
  preserve [] Σ ϰ φ (local_locs b) b' T q σ' ->
  preserve [] Σ ϰ φ (local_locs (tassign v b)) (tassign v b') TUnit ∅ σ'.
Proof.
  intros HC Hσ HW HV HR Hnf HT Hsep HP.
  pose proof (step_c_assign_r v b b' σ σ' HV HR) as Hstep.
  destruct (safety_step_wf _ _ _ _ Hstep HW Hσ) as [HW' _].
  simpl in HW. destruct HW as (HwV & HwB & _).
  destruct (safety_preserve_unpack _ _ _ _ _ _ _ _ HP)
    as (Σ' & δ & φ' & ϰ' & HE & HU & Hδ & HF & HC' & HD & HT' & Hσ' & HA' & Hextra).
  assert (Hq : has_type [] φ' Σ' b' T q).
  { unfold qqplus in HT'. destruct (qfresh q); [exfalso; exact (Hnf I)|exact HT']. }
  apply (Preserve Σ' ∅ φ' ϰ'); try assumption.
  - eapply safety_update_locs; [exact HU|apply safety_join_r].
  - apply safety_empty_bound.
  - apply disj_bot.
  - eapply t_assign with (φd := qdiff φ' (local_locs v)) (T := T) (d := d) (d1 := q); try eassumption; try reflexivity.
    + exact (safety_keep_value Σ Σ' φ φ' ϰ ϰ' σ σ' (local_locs b) v (TRef q T) d
        HC HC' HE HU HT HV Hsep).
    + eapply safety_scope_over_value; eassumption.
    + exact (safety_step_carries_sep Σ b σ b' σ' d
        (safety_ctx_length _ _ _ _ HC) HR HwB Hσ (safety_typing_qual_closed _ _ _ _ _ _ HT) Hsep).
Qed.

Local Lemma safety_preserve_refat_l_ctx Σ φ ϰ σ σ' a a' v T q U r d :
  CtxOK [] φ Σ ϰ σ -> wf_store σ -> wf_step (trefat a v) ->
  value v -> step a σ a' σ' -> ♦∉ q ->
  has_type [] φ Σ v (TRef r U) d ->
  kill_sep (local_locs a) d ->
  preserve [] Σ ϰ φ (local_locs a) a' T q σ' ->
  preserve [] Σ ϰ φ (local_locs (trefat a v)) (trefat a' v) (TRef q T) d σ'.
Proof.
  intros HC Hσ HW HV HR Hnf HT Hsep HP.
  pose proof (step_c_refat_l a a' v σ σ' HV HR) as Hstep.
  destruct (safety_step_wf _ _ _ _ Hstep HW Hσ) as [HW' _].
  simpl in HW. destruct HW as (HwA & HwV & _).
  destruct (safety_preserve_unpack _ _ _ _ _ _ _ _ HP)
    as (Σ' & δ & φ' & ϰ' & HE & HU & Hδ & HF & HC' & HD & HT' & Hσ' & HA' & Hextra).
  assert (Hq : has_type [] φ' Σ' a' T q).
  { unfold qqplus in HT'. destruct (qfresh q); [exfalso; exact (Hnf I)|exact HT']. }
  apply (Preserve Σ' ∅ φ' ϰ'); try assumption.
  - eapply safety_update_locs; [exact HU|apply safety_join_l].
  - apply safety_empty_bound.
  - apply disj_bot.
  - apply safety_typing_plus_empty; [|exact HW'].
    eapply t_refat with (φd := qdiff φ' (local_locs v)); try eassumption; try reflexivity.
    + eapply safety_scope_over_value; eassumption.
    + exact (safety_keep_value Σ Σ' φ φ' ϰ ϰ' σ σ' (local_locs a) v (TRef r U) d
        HC HC' HE HU HT HV Hsep).
    + exact (safety_step_carries_sep Σ a σ a' σ' d
        (safety_ctx_length _ _ _ _ HC) HR HwA Hσ (safety_typing_qual_closed _ _ _ _ _ _ HT) Hsep).
Qed.

Local Lemma safety_plus_extensive q δ : q ⊑↑ q ⋓ δ.
Proof. unfold qqplus. destruct (qfresh q); auto using safety_subq_refl, safety_join_l. Qed.

Local Lemma safety_q_open_mono k q r a :
  q ⊑↑ r -> open_qual k a q ⊑↑ open_qual k a r.
Proof.
  intro Hsub. unfold open_qual.
  destruct (qbvs q k) eqn:Hq, (qbvs r k) eqn:Hr.
  - safety_qpoint.
  - exfalso. destruct Hsub as (_ & _ & HB & _).
    specialize (HB k Hq). change (qbvs r k = true) in HB. congruence.
  - safety_qpoint.
    destruct Hsub as (HF & Hfv & Hbv & Hl).
    refine (conj _ (conj _ (conj _ _))); try solve [eauto].
    intros x Hx. left. split; [now apply Hbv|].
    apply Nat.eqb_neq. congruence.
  - exact Hsub.
Qed.

Local Lemma safety_q_open_plus_arg k q a δ :
  open_qual k (a ⋓ δ) q ⊑↑ open_qual k a q ⋓ δ.
Proof.
  unfold open_qual. destruct (qbvs q k); [|apply safety_plus_extensive].
  unfold qqplus at 1. destruct (qfresh a) eqn:Ha; [|apply safety_plus_extensive].
  assert (H : qfresh ((qfresh q, qfvs q, n_diff (qbvs q) (n_one k), qlocs q) ⊔ a) = true).
  { change (qfresh q || qfresh a = true). rewrite Ha. apply orb_true_r. }
  unfold qqplus. rewrite H. clear H Ha. safety_qpoint.
Qed.

Local Lemma safety_q_open_plus_base k q a δ :
  qbvs δ k = false ->
  open_qual k a (q ⋓ δ) ⊑↑ open_qual k a q ⋓ δ.
Proof.
  intro Hδ. unfold qqplus at 1. destruct (qfresh q) eqn:Hq;
    [|apply safety_plus_extensive].
  unfold open_qual.
  assert (HB : qbvs (q ⊔ δ) k = qbvs q k).
  { change (qbvs q k || qbvs δ k = qbvs q k). rewrite Hδ. apply orb_false_r. }
  rewrite HB. destruct (qbvs q k); [|unfold qqplus; now rewrite Hq].
  assert (H : qfresh ((qfresh q, qfvs q, n_diff (qbvs q) (n_one k), qlocs q) ⊔ a) = true).
  { change (qfresh q || qfresh a = true). now rewrite Hq. }
  unfold qqplus. rewrite H. clear H HB Hδ Hq. safety_qpoint.
Qed.

Local Lemma safety_openq_plus_fun q a b δ :
  qbvs δ 1 = false ->
  (q <~ᵈ (a ⋓ δ) ; b) ⊑↑ (q <~ᵈ a ; b) ⋓ δ.
Proof.
  intros H. unfold openq.
  eapply safety_subq_trans.
  - apply safety_q_open_mono, safety_q_open_plus_arg.
  - now apply safety_q_open_plus_base.
Qed.

Local Lemma safety_openq_plus_arg q a b δ :
  (q <~ᵈ a ; (b ⋓ δ)) ⊑↑ (q <~ᵈ a ; b) ⋓ δ.
Proof. unfold openq. apply safety_q_open_plus_arg. Qed.

Local Lemma safety_q_not_free k q :
  open_qual k ∅ q = q -> qbvs q k = false.
Proof.
  intro H. destruct (qbvs q k) eqn:Hq; [|reflexivity].
  apply (f_equal (fun p => qbvs p k)) in H.
  unfold open_qual in H. rewrite Hq in H.
  change ((qbvs q k && negb (k =? k)) || false = qbvs q k) in H.
  rewrite Hq, Nat.eqb_refl in H. discriminate.
Qed.

Local Lemma safety_q_not_free_open k q p :
  open_qual k ∅ q = q -> open_qual k p q = q.
Proof. intro H. unfold open_qual. now rewrite (safety_q_not_free k q H). Qed.

Local Lemma safety_not_free_open T k U p :
  not_free k T -> open_rec_ty k U p T = T.
Proof.
  unfold not_free. revert k.
  induction T; intros k H; simpl in *; try reflexivity.
  - destruct v; simpl in *; [reflexivity|].
    destruct (k =? i); [discriminate|reflexivity].
  - injection H as H1 H2 H3 H4. f_equal.
    + exact (safety_q_not_free_open k q p H1).
    + exact (safety_q_not_free_open (S (S k)) q0 p H2).
    + now apply IHT1.
    + now apply IHT2.
  - injection H as H1 H2 H3 H4. f_equal.
    + exact (safety_q_not_free_open k q p H1).
    + exact (safety_q_not_free_open (S (S k)) q0 p H2).
    + now apply IHT1.
    + now apply IHT2.
  - injection H as H1 H2. f_equal.
    + exact (safety_q_not_free_open k q p H1).
    + now apply IHT.
Qed.

Local Lemma safety_open_name_ty (Γ : tenv) L T :
  closed_ty 2 (length Γ) L T ->
  closed_ty 0 (S (S (length Γ))) L (T <~²ᵀ Γ).
Proof.
  unfold open_ty', open_ty. intro H.
  eapply safety_ty_open_two; eauto using safety_fv_closed, cl_ttvarf; lia.
Qed.

Local Lemma safety_open_name_qual (Γ : tenv) L q :
  closed_Qual 2 (length Γ) L q↑ ->
  closed_Qual 0 (S (S (length Γ))) L (q <~²ᵈ Γ)↑.
Proof.
  unfold openq', openq. intro H.
  eapply safety_q_open_two; eauto using safety_fv_closed; lia.
Qed.

Local Lemma safety_sub_all_domain Γ Σ T1 T2 q q' d2 df :
  closed_ty 0 (length Γ) (length Σ) (TAll q d2 T1 T2) ->
  closed_Qual 0 (length Γ) (length Σ) df↑ ->
  closed_Qual 0 (length Γ) (length Σ) q'↑ -> q' ⊑↑ q ->
  stp Γ Σ (TAll q d2 T1 T2) df (TAll q' d2 T1 T2) df.
Proof.
  intros HT Hdf Hq Hle. inversion HT; subst.
  apply s_all.
  - exact HT.
  - constructor; assumption.
  - apply qs_sq; auto using safety_subq_refl.
  - apply safety_stp_refl; [assumption|now apply qs_sq].
  - apply safety_stp_refl.
    + apply safety_open_name_ty. assumption.
    + apply qs_sq; [apply safety_subq_refl|].
      apply safety_open_name_qual. assumption.
Qed.

Local Lemma safety_sub_fun_domain Γ Σ T1 T2 q q' d2 df :
  closed_ty 0 (length Γ) (length Σ) (TFun q d2 T1 T2) ->
  closed_Qual 0 (length Γ) (length Σ) df↑ ->
  closed_Qual 0 (length Γ) (length Σ) q'↑ -> q' ⊑↑ q ->
  stp Γ Σ (TFun q d2 T1 T2) df (TFun q' d2 T1 T2) df.
Proof.
  intros HT Hdf Hq Hle. inversion HT; subst.
  apply s_fun.
  - exact HT.
  - constructor; assumption.
  - apply qs_sq; auto using safety_subq_refl.
  - apply safety_stp_refl; [assumption|now apply qs_sq].
  - apply safety_stp_refl.
    + apply safety_open_name_ty. assumption.
    + apply qs_sq; [apply safety_subq_refl|].
      apply safety_open_name_qual. assumption.
Qed.

Local Lemma safety_overlap_plus_l a b δ :
  kill_sep δ b -> ((a ⋓ δ) ⋒ b) ⊑↑ (a ⋒ b).
Proof. unfold qqplus. destruct (qfresh a); safety_qpoint. Qed.

Local Lemma safety_overlap_plus_r a b δ :
  kill_sep δ a -> (a ⋒ (b ⋓ δ)) ⊑↑ (a ⋒ b).
Proof. unfold qqplus. destruct (qfresh b); safety_qpoint. Qed.

Local Lemma safety_sep_new_loc_general (Σ : senv) b f q :
  closed_Qual b f (length Σ) q↑ -> kill_sep (&!(length Σ)) q.
Proof.
  intros (_ & _ & Hl). unfold kill_sep. apply safety_qual_le.
  refine (conj (fun _ => eq_refl) (conj _ (conj _ _))).
  - intros x Hx. apply andb_true_iff in Hx as [_ Hx]. discriminate Hx.
  - intros x Hx. apply andb_true_iff in Hx as [_ Hx]. discriminate Hx.
  - intros x Hx. change (qlocs q x && (x =? length Σ) = true) in Hx.
    apply andb_true_iff in Hx as [Hmem Hx].
    apply Nat.eqb_eq in Hx. specialize (Hl x Hmem). lia.
Qed.

Local Lemma safety_step_carries_sep_general (Σ : senv) t σ t' σ' b f q :
  length σ = length Σ ->
  step t σ t' σ' -> wf_step t -> wf_store σ ->
  closed_Qual b f (length Σ) q↑ ->
  kill_sep (local_locs t) q ->
  kill_sep (local_locs t') q.
Proof.
  intros Hlen Hstep Hwf Hstore Hq Hsep.
  eapply safety_sep_left.
  - exact (safety_step_scope_growth _ _ _ _ Hstep Hwf Hstore).
  - rewrite Hlen. apply safety_sep_join_left; [exact Hsep|].
    eapply safety_sep_new_loc_general; eassumption.
Qed.

Local Lemma safety_cast_in_step Σ Σ' φ φ' ϰ ϰ' σ σ' t t' T d d' δ :
  CtxOK [] φ Σ ϰ σ -> wf_store σ -> wf_step t ->
  step t σ t' σ' ->
  envUpdate Σ φ ϰ (local_locs t) Σ' φ' ϰ' ->
  δ ⊑↑ φ' -> kill_sep (local_locs t') δ ->
  has_type [] φ Σ t T d ->
  has_type [] φ' Σ' t' T d' -> d' ⊑↑ d ⋓ δ ->
  has_type [] φ' Σ' t' T (d ⋓ δ).
Proof.
  intros HC Hσ Hwf Hstep HU Hδ Hsepδ HT HT' Hle.
  apply (safety_qual_cast _ _ _ _ _ _ _ HT'); [exact Hle| |].
  - apply safety_qqplus_bound; [|exact Hδ].
    exact (safety_update_scope_fresh _ _ _ _ _ _ _ _ HU (safety_ctx_scope _ _ _ _ HC)
      (safety_typing_sep _ _ _ _ _ _ HT Hwf) (safety_typing_qual_bound _ _ _ _ _ _ HT)).
  - apply safety_qqplus_sep; [|exact Hsepδ].
    exact (safety_step_carries_sep Σ t σ t' σ' d (safety_ctx_length _ _ _ _ HC)
      Hstep Hwf Hσ (safety_typing_qual_closed _ _ _ _ _ _ HT)
      (safety_typing_sep _ _ _ _ _ _ HT Hwf)).
Qed.

Local Lemma safety_q_has_no_bvar b L q x :
  closed_Qual 0 b L q↑ -> qbvs q x = false.
Proof.
  intros (_ & H & _).
  destruct (qbvs q x) eqn:Hd; [specialize (H x Hd); lia|reflexivity].
Qed.

Local Lemma safety_preserve_ttapp_ctx Σ φ ϰ σ σ' t t' T1 T2 d1 d2 df :
  CtxOK [] φ Σ ϰ σ -> wf_store σ -> wf_step t ->
  step t σ t' σ' ->
  has_type [] φ Σ t (TAll d1 d2 T1 T2) df ->
  closed_ty 0 0 (length Σ) T1 -> closed_Qual 0 0 (length Σ) d1↑ ->
  (d2 <~ᵈ ∅ ; ∅) ⊑↑ φ ⊔ {♦} ->
  ♦∉ d1 -> d1 ⊑↑ φ -> not_free 0 T2 ->
  kill_sep (local_locs t) d1 -> kill_sep (local_locs t) d2 ->
  preserve [] Σ ϰ φ (local_locs t) t' (TAll d1 d2 T1 T2) df σ' ->
  preserve [] Σ ϰ φ (local_locs (ttapp t)) (ttapp t')
    (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1) σ'.
Proof.
  intros HC Hσ HW HR HT HT1 HC1 HB Hnf Hlive Hfree HS1 HS2 HP.
  destruct (safety_preserve_unpack _ _ _ _ _ _ _ _ HP)
    as (Σ' & δ & φ' & ϰ' & HE & HU & Hδ & HF & HC' & HD & HT' & Hσ' & HW' & Hsepδ).
  pose proof (safety_ctx_length _ _ _ _ HC) as HL.
  pose proof (safety_ctx_scope _ _ _ _ HC) as Hφ.
  pose proof (safety_senv_length _ _ HE) as Hle.
  assert (HC2 : closed_Qual 2 0 (length Σ) d2↑).
  { pose proof (safety_typing_type_closed _ _ _ _ _ _ HT) as Hcl.
    inversion Hcl; assumption. }
  assert (HSB : kill_sep (local_locs t) (d2 <~ᵈ ∅ ; ∅))
    by eauto using safety_sep_open2, safety_sep_empty.
  assert (HTA : has_type [] φ Σ (ttapp t)
      (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1))
    by (eapply t_tapp; eassumption).
  apply (Preserve Σ' δ φ' ϰ'); try assumption.
  - eauto using safety_disjointq_old.
  - eapply safety_cast_in_step with (t := ttapp t) (σ := σ) (σ' := σ')
        (d' := d2 <~ᵈ (df ⋓ δ) ; d1); try eassumption.
    + exact (step_c_tapp t t' σ σ' HR).
    + eapply t_tapp; [exact HT'| | | |exact Hnf| |exact Hfree| |].
      * eauto using safety_ty_closed_weaken.
      * eauto using safety_locs_closed_weaken.
      * exact (safety_update_scope_fresh _ _ _ _ _ _ _ _ HU Hφ HSB HB).
      * exact (safety_update_scope_sub _ _ _ _ _ _ _ _ HU Hφ HS1 Hlive).
      * exact (safety_step_carries_sep _ _ _ _ _ _ HL HR HW Hσ HC1 HS1).
      * exact (safety_step_carries_sep_general _ _ _ _ _ _ _ _ HL HR HW Hσ HC2 HS2).
    + apply safety_openq_plus_fun.
      eapply safety_q_has_no_bvar.
      eapply safety_qual_closed_of_sub; [exact Hδ|].
      apply safety_dom_closed. exact (safety_ctx_scope _ _ _ _ HC').
Qed.

Local Lemma safety_preserve_ttapp_fresh_ctx Σ φ ϰ σ σ' t t' T1 T2 d1 d2 df :
  CtxOK [] φ Σ ϰ σ -> wf_store σ -> wf_step t ->
  step t σ t' σ' ->
  has_type [] φ Σ t (TAll (df ⋒ d1) d2 T1 T2) df ->
  closed_ty 0 0 (length Σ) T1 -> closed_Qual 0 0 (length Σ) d1↑ ->
  d1 ⊑↑ φ ⊔ {♦} -> (♦∈ d1 -> not_free 1 T2) -> not_free 0 T2 ->
  (d2 <~ᵈ ∅ ; ∅) ⊑↑ φ ⊔ {♦} -> (d1 ⋒ df) ⊑↑ φ ⊔ {♦} ->
  kill_sep (local_locs t) d1 -> kill_sep (local_locs t) d2 ->
  kill_sep (local_locs t) (d1 ⋒ df) ->
  preserve [] Σ ϰ φ (local_locs t) t' (TAll (df ⋒ d1) d2 T1 T2) df σ' ->
  preserve [] Σ ϰ φ (local_locs (ttapp t)) (ttapp t')
    (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1) σ'.
Proof.
  intros HC Hσ HW HR HT HT1 HC1 HB1 Hfree1 Hfree0 HB HO HS1 HS2 HSO HP.
  destruct (safety_preserve_unpack _ _ _ _ _ _ _ _ HP)
    as (Σ' & δ & φ' & ϰ' & HE & HU & Hδ & HF & HC' & HD & HT' & Hσ' & HW' & Hsepδ).
  pose proof (safety_ctx_length _ _ _ _ HC) as HL.
  pose proof (safety_ctx_scope _ _ _ _ HC) as Hφ.
  pose proof (safety_senv_length _ _ HE) as Hle.
  assert (HC2 : closed_Qual 2 0 (length Σ) d2↑).
  { pose proof (safety_typing_type_closed _ _ _ _ _ _ HT) as Hcl.
    inversion Hcl; assumption. }
  assert (HCO : closed_Qual 0 0 (length Σ) (d1 ⋒ df)↑).
  { eapply safety_qual_closed_of_sub; [exact HO|].
    apply safety_qual_join_closed; auto using safety_dom_closed, safety_qual_const_closed. }
  assert (Hsep : kill_sep δ d1).
  { apply safety_sep_sym. eapply safety_disjointq_sep_old; [exact HD|exact HC1]. }
  pose proof (safety_overlap_plus_l df d1 δ Hsep) as Hnarrow.
  pose proof (safety_overlap_plus_r d1 df δ Hsep) as Hnarrow'.
  assert (HCl : closed_ty 0 0 (length Σ') (TAll (df ⋒ d1) d2 T1 T2))
    by exact (safety_typing_type_closed _ _ _ _ _ _ HT').
  assert (Hcal : has_type [] φ' Σ' t' (TAll ((df ⋓ δ) ⋒ d1) d2 T1 T2) (df ⋓ δ)).
  { eapply t_sub; [exact HT'| |exact (safety_typing_qual_bound _ _ _ _ _ _ HT')|].
    - apply safety_sub_all_domain; try assumption.
      + exact (safety_typing_qual_closed _ _ _ _ _ _ HT').
      + eapply safety_qual_closed_of_sub; [exact Hnarrow|].
        inversion HCl; assumption.
    - exact (safety_typing_sep _ _ _ _ _ _ HT' HW'). }
  assert (HSB : kill_sep (local_locs t) (d2 <~ᵈ ∅ ; ∅))
    by eauto using safety_sep_open2, safety_sep_empty.
  assert (HTA : has_type [] φ Σ (ttapp t)
      (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1))
    by (eapply t_tapp_fresh; eassumption).
  apply (Preserve Σ' δ φ' ϰ'); try assumption.
  - eauto using safety_disjointq_old.
  - eapply safety_cast_in_step with (t := ttapp t) (σ := σ) (σ' := σ')
        (d' := d2 <~ᵈ (df ⋓ δ) ; d1); try eassumption.
    + exact (step_c_tapp t t' σ σ' HR).
    + eapply t_tapp_fresh; [exact Hcal| | | |exact Hfree1|exact Hfree0| | | | |].
      * eauto using safety_ty_closed_weaken.
      * eauto using safety_locs_closed_weaken.
      * exact (safety_update_scope_fresh _ _ _ _ _ _ _ _ HU Hφ HS1 HB1).
      * exact (safety_update_scope_fresh _ _ _ _ _ _ _ _ HU Hφ HSB HB).
      * eapply safety_subq_trans; [exact Hnarrow'|].
        exact (safety_update_scope_fresh _ _ _ _ _ _ _ _ HU Hφ HSO HO).
      * exact (safety_step_carries_sep _ _ _ _ _ _ HL HR HW Hσ HC1 HS1).
      * exact (safety_step_carries_sep_general _ _ _ _ _ _ _ _ HL HR HW Hσ HC2 HS2).
      * eapply safety_sep_of_sub; [exact Hnarrow'|].
        exact (safety_step_carries_sep _ _ _ _ _ _ HL HR HW Hσ HCO HSO).
    + apply safety_openq_plus_fun.
      eapply safety_q_has_no_bvar.
      eapply safety_qual_closed_of_sub; [exact Hδ|].
      apply safety_dom_closed. exact (safety_ctx_scope _ _ _ _ HC').
Qed.

Local Lemma safety_preserve_app_l_ctx Σ φ ϰ σ σ' a a' b T1 T2 d1 d2 df :
  CtxOK [] φ Σ ϰ σ -> wf_store σ -> wf_step (tapp a b) ->
  step a σ a' σ' ->
  has_type [] φ Σ a (TFun d1 d2 T1 T2) df ->
  has_type [] (qdiff φ (local_locs a)) Σ b T1 d1 ->
  (d2 <~ᵈ ∅ ; ∅) ⊑↑ φ ⊔ {♦} ->
  ♦∉ d1 -> not_free 0 T2 -> kill_sep (local_locs b) df ->
  kill_sep (local_locs (tapp a b)) d2 ->
  preserve [] Σ ϰ φ (local_locs a) a' (TFun d1 d2 T1 T2) df σ' ->
  preserve [] Σ ϰ φ (local_locs (tapp a b)) (tapp a' b)
    (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1) σ'.
Proof.
  intros HC Hσ HW HR HA HB HD1 Hnf Hfree HS1 HS2 HP.
  destruct (safety_preserve_unpack _ _ _ _ _ _ _ _ HP)
    as (Σ' & δ & φ' & ϰ' & HE & HU & Hδ & HF & HC' & HD & HA' & Hσ' & HW' & Hsepδ).
  pose proof (step_c_app_l a a' b σ σ' HR) as Hstep.
  destruct (safety_step_wf _ _ _ _ Hstep HW Hσ) as [HWsrc _].
  assert (HU' : envUpdate Σ φ ϰ (local_locs (tapp a b)) Σ' φ' ϰ')
    by (eapply safety_update_locs; [exact HU|apply safety_join_l]).
  assert (HTA : has_type [] φ Σ (tapp a b)
      (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1))
    by (eapply t_app; eassumption || reflexivity).
  assert (HSbδ : kill_sep (local_locs b) δ).
  { eapply safety_disjointq_sep_old; [exact HD|].
    eapply safety_scope_locs_closed. exact (safety_typing_tm_closed _ _ _ _ _ _ HB). }
  assert (HC2 : closed_Qual 2 0 (length Σ) d2↑).
  { pose proof (safety_typing_type_closed _ _ _ _ _ _ HA) as Hcl.
    inversion Hcl; assumption. }
  assert (HSB : kill_sep (local_locs (tapp a b)) (d2 <~ᵈ ∅ ; ∅))
    by eauto using safety_sep_open2, safety_sep_empty.
  apply (Preserve Σ' δ φ' ϰ'); try assumption.
  - eauto using safety_disjointq_old.
  - eapply safety_cast_in_step with (t := tapp a b) (σ := σ) (σ' := σ')
        (d' := d2 <~ᵈ (df ⋓ δ) ; d1); try eassumption.
    + now apply safety_sep_join_left.
    + eapply t_app with (φd := qdiff φ' (local_locs a')); [exact HA'| | |exact Hnf|exact Hfree|reflexivity| |].
      * exact (safety_carry_scoped_typing Σ Σ' φ φ' ϰ ϰ' σ σ' a a' b T1 d1
          HC HC' Hσ (proj1 HW) HR HE HU HB).
      * exact (safety_update_scope_fresh _ _ _ _ _ _ _ _ HU' (safety_ctx_scope _ _ _ _ HC) HSB HD1).
      * now apply safety_qqplus_sep.
      * exact (safety_step_carries_sep_general _ _ _ _ _ _ _ _ (safety_ctx_length _ _ _ _ HC)
          Hstep HW Hσ HC2 HS2).
    + apply safety_openq_plus_fun.
      eapply safety_q_has_no_bvar.
      eapply safety_qual_closed_of_sub; [exact Hδ|].
      apply safety_dom_closed. exact (safety_ctx_scope _ _ _ _ HC').
Qed.

Local Lemma safety_preserve_app_r_ctx Σ φ ϰ σ σ' v b b' T1 T2 d1 d2 df :
  CtxOK [] φ Σ ϰ σ -> wf_store σ -> wf_step (tapp v b) ->
  value v -> step b σ b' σ' ->
  has_type [] φ Σ v (TFun d1 d2 T1 T2) df ->
  (d2 <~ᵈ ∅ ; ∅) ⊑↑ φ ⊔ {♦} ->
  ♦∉ d1 -> not_free 0 T2 -> kill_sep (local_locs b) df ->
  kill_sep (local_locs (tapp v b)) d2 ->
  preserve [] Σ ϰ φ (local_locs b) b' T1 d1 σ' ->
  preserve [] Σ ϰ φ (local_locs (tapp v b)) (tapp v b')
    (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1) σ'.
Proof.
  intros HC Hσ HW HV HR HA HB Hnf Hfree HS1 HS2 HP.
  destruct (safety_preserve_unpack _ _ _ _ _ _ _ _ HP)
    as (Σ' & δ & φ' & ϰ' & HE & HU & Hδ & HF & HC' & HD & HB' & Hσ' & HW' & Hsepδ).
  pose proof (step_c_app_r v b b' σ σ' HV HR) as Hstep.
  destruct (safety_step_wf _ _ _ _ Hstep HW Hσ) as [HWsrc _].
  assert (HU' : envUpdate Σ φ ϰ (local_locs (tapp v b)) Σ' φ' ϰ')
    by (eapply safety_update_locs; [exact HU|apply safety_join_r]).
  assert (HArg : has_type [] φ' Σ' b' T1 d1).
  { unfold qqplus in HB'. destruct (qfresh d1); [exfalso; exact (Hnf I)|exact HB']. }
  assert (HC2 : closed_Qual 2 0 (length Σ) d2↑).
  { pose proof (safety_typing_type_closed _ _ _ _ _ _ HA) as Hcl.
    inversion Hcl; assumption. }
  assert (HSB : kill_sep (local_locs (tapp v b)) (d2 <~ᵈ ∅ ; ∅))
    by eauto using safety_sep_open2, safety_sep_empty.
  apply (Preserve Σ' ∅ φ' ϰ'); try assumption.
  - apply safety_empty_bound.
  - apply disj_bot.
  - apply safety_typing_plus_empty; [|exact HWsrc].
    eapply t_app with (φd := qdiff φ' (local_locs v)); [| | |exact Hnf|exact Hfree|reflexivity| |].
    + exact (safety_keep_value _ _ _ _ _ _ _ _ _ _ _ _ HC HC' HE HU HA HV HS1).
    + exact (safety_scope_over_value _ _ _ _ _ _ HV (proj1 HW) HArg).
    + exact (safety_update_scope_fresh _ _ _ _ _ _ _ _ HU' (safety_ctx_scope _ _ _ _ HC) HSB HB).
    + exact (safety_step_carries_sep _ _ _ _ _ _ (safety_ctx_length _ _ _ _ HC) HR
        (proj1 (proj2 HW)) Hσ (safety_typing_qual_closed _ _ _ _ _ _ HA) HS1).
    + exact (safety_step_carries_sep_general _ _ _ _ _ _ _ _ (safety_ctx_length _ _ _ _ HC)
        Hstep HW Hσ HC2 HS2).
Qed.

Local Lemma safety_overlap_right_bound a b : a ⋒ b ⊑↑ b ⊔ {♦}.
Proof. safety_qpoint. Qed.

Local Lemma safety_fresh_type_unchanged T U q δ :
  not_free 0 T -> (♦∈ q -> not_free 1 T) ->
  (T <~ᵀ TUnit ~ ∅ ; U ~ (q ⋓ δ)) = (T <~ᵀ TUnit ~ ∅ ; U ~ q).
Proof.
  intros H0 H1.
  unfold qqplus. destruct (qfresh q) eqn:Hq; [|reflexivity].
  assert (Hf : not_free 1 T).
  { exact (H1 I). }
  unfold open_ty. rewrite (safety_not_free_open T 0 TUnit ∅ H0).
  now rewrite (safety_not_free_open T 1 U (q ⊔ δ) Hf), (safety_not_free_open T 1 U q Hf).
Qed.

Local Lemma safety_fresh_remains_monotone q δ :
  ♦∈ q ⋓ δ -> ♦∈ q.
Proof.
  change (Is_true (qfresh (q ⋓ δ)) -> Is_true (qfresh q)).
  unfold qqplus. destruct (qfresh q) eqn:H; intros Hx; [exact I|now rewrite H in Hx].
Qed.

Local Lemma safety_preserve_app_fresh_l_ctx Σ φ ϰ σ σ' a a' b T1 T2 d1 d2 df :
  CtxOK [] φ Σ ϰ σ -> wf_store σ -> wf_step (tapp a b) ->
  step a σ a' σ' ->
  has_type [] φ Σ a (TFun (df ⋒ d1) d2 T1 T2) df ->
  has_type [] (qdiff φ (local_locs a)) Σ b T1 d1 ->
  (♦∈ d1 -> not_free 1 T2) -> not_free 0 T2 ->
  (d2 <~ᵈ ∅ ; ∅) ⊑↑ φ ⊔ {♦} -> (d1 ⋒ df) ⊑↑ φ ⊔ {♦} ->
  kill_sep (local_locs b) df -> kill_sep (local_locs (tapp a b)) d2 ->
  kill_sep (local_locs a) (d1 ⋒ df) ->
  preserve [] Σ ϰ φ (local_locs a) a' (TFun (df ⋒ d1) d2 T1 T2) df σ' ->
  preserve [] Σ ϰ φ (local_locs (tapp a b)) (tapp a' b)
    (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1) σ'.
Proof.
  intros HC Hσ HW HR HA HB Hfree1 Hfree0 HD1 HO HS1 HS2 HSO HP.
  destruct (safety_preserve_unpack _ _ _ _ _ _ _ _ HP)
    as (Σ' & δ & φ' & ϰ' & HE & HU & Hδ & HF & HC' & HD & HA' & Hσ' & HW' & Hsepδ).
  pose proof (step_c_app_l a a' b σ σ' HR) as Hstep.
  destruct (safety_step_wf _ _ _ _ Hstep HW Hσ) as [HWsrc _].
  assert (HU' : envUpdate Σ φ ϰ (local_locs (tapp a b)) Σ' φ' ϰ')
    by (eapply safety_update_locs; [exact HU|apply safety_join_l]).
  assert (HTA : has_type [] φ Σ (tapp a b)
      (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1))
    by (eapply t_app_fresh; eassumption || reflexivity).
  assert (HSbδ : kill_sep (local_locs b) δ).
  { eapply safety_disjointq_sep_old; [exact HD|].
    eapply safety_scope_locs_closed. exact (safety_typing_tm_closed _ _ _ _ _ _ HB). }
  assert (HC2 : closed_Qual 2 0 (length Σ) d2↑).
  { pose proof (safety_typing_type_closed _ _ _ _ _ _ HA) as Hcl.
    inversion Hcl; assumption. }
  assert (HSB : kill_sep (local_locs (tapp a b)) (d2 <~ᵈ ∅ ; ∅))
    by eauto using safety_sep_open2, safety_sep_empty.
  pose proof (safety_ctx_scope _ _ _ _ HC) as Hφ.
  assert (HCO : closed_Qual 0 0 (length Σ) (d1 ⋒ df)↑).
  { eapply safety_qual_closed_of_sub; [exact HO|].
    apply safety_qual_join_closed; auto using safety_dom_closed, safety_qual_const_closed. }
  assert (Hsep : kill_sep δ d1).
  { apply safety_sep_sym. eapply safety_disjointq_sep_old; [exact HD|].
    exact (safety_typing_qual_closed _ _ _ _ _ _ HB). }
  pose proof (safety_overlap_plus_l df d1 δ Hsep) as Hnarrow.
  pose proof (safety_overlap_plus_r d1 df δ Hsep) as Hnarrow'.
  pose proof (safety_typing_type_closed _ _ _ _ _ _ HA') as HCl.
  assert (Hcal : has_type [] φ' Σ' a' (TFun ((df ⋓ δ) ⋒ d1) d2 T1 T2) (df ⋓ δ)).
  { eapply t_sub; [exact HA'| |exact (safety_typing_qual_bound _ _ _ _ _ _ HA')|].
    - apply safety_sub_fun_domain; try assumption.
      + exact (safety_typing_qual_closed _ _ _ _ _ _ HA').
      + eapply safety_qual_closed_of_sub; [exact Hnarrow|].
        inversion HCl; assumption.
    - exact (safety_typing_sep _ _ _ _ _ _ HA' HW'). }
  apply (Preserve Σ' δ φ' ϰ'); try assumption.
  - eauto using safety_disjointq_old.
  - eapply safety_cast_in_step with (t := tapp a b) (σ := σ) (σ' := σ')
        (d' := d2 <~ᵈ (df ⋓ δ) ; d1); try eassumption.
    + now apply safety_sep_join_left.
    + eapply t_app_fresh with (φd := qdiff φ' (local_locs a'));
        [exact Hcal| |exact Hfree1|exact Hfree0| | |reflexivity| | |].
      * exact (safety_carry_scoped_typing Σ Σ' φ φ' ϰ ϰ' σ σ' a a' b T1 d1
          HC HC' Hσ (proj1 HW) HR HE HU HB).
      * exact (safety_update_scope_fresh _ _ _ _ _ _ _ _ HU' Hφ HSB HD1).
      * eapply safety_subq_trans; [exact Hnarrow'|].
        exact (safety_update_scope_fresh _ _ _ _ _ _ _ _ HU Hφ HSO HO).
      * now apply safety_qqplus_sep.
      * exact (safety_step_carries_sep_general _ _ _ _ _ _ _ _ (safety_ctx_length _ _ _ _ HC)
          Hstep HW Hσ HC2 HS2).
      * eapply safety_sep_of_sub; [exact Hnarrow'|].
        exact (safety_step_carries_sep _ _ _ _ _ _ (safety_ctx_length _ _ _ _ HC)
          HR (proj1 HW) Hσ HCO HSO).
    + apply safety_openq_plus_fun.
      eapply safety_q_has_no_bvar.
      eapply safety_qual_closed_of_sub; [exact Hδ|].
      apply safety_dom_closed. exact (safety_ctx_scope _ _ _ _ HC').
Qed.

Local Lemma safety_preserve_app_fresh_r_ctx Σ φ ϰ σ σ' v b b' T1 T2 d1 d2 df :
  CtxOK [] φ Σ ϰ σ -> wf_store σ -> wf_step (tapp v b) ->
  value v -> step b σ b' σ' ->
  has_type [] φ Σ v (TFun (df ⋒ d1) d2 T1 T2) df ->
  has_type [] (qdiff φ (local_locs v)) Σ b T1 d1 ->
  (♦∈ d1 -> not_free 1 T2) -> not_free 0 T2 ->
  (d2 <~ᵈ ∅ ; ∅) ⊑↑ φ ⊔ {♦} -> (d1 ⋒ df) ⊑↑ φ ⊔ {♦} ->
  kill_sep (local_locs b) df -> kill_sep (local_locs (tapp v b)) d2 ->
  preserve [] Σ ϰ φ (local_locs b) b' T1 d1 σ' ->
  preserve [] Σ ϰ φ (local_locs (tapp v b)) (tapp v b')
    (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1) σ'.
Proof.
  intros HC Hσ HW HV HR HA HB Hfree1 Hfree0 HD1 HO HS1 HS2 HP.
  pose proof (safety_value_scopes _ HV (proj1 HW)) as HL.
  destruct (safety_preserve_unpack _ _ _ _ _ _ _ _ HP)
    as (Σ' & δ & φ' & ϰ' & HE & HU & Hδ & HF & HC' & HD & HB' & Hσ' & HW' & Hsepδ).
  pose proof (step_c_app_r v b b' σ σ' HV HR) as Hstep.
  destruct (safety_step_wf _ _ _ _ Hstep HW Hσ) as [HWsrc _].
  assert (HU' : envUpdate Σ φ ϰ (local_locs (tapp v b)) Σ' φ' ϰ')
    by (eapply safety_update_locs; [exact HU|apply safety_join_r]).
  assert (HTA : has_type [] φ Σ (tapp v b)
      (T2 <~ᵀ TUnit ~ ∅ ; T1 ~ d1) (d2 <~ᵈ df ; d1)).
  { eapply t_app_fresh; try eassumption; try reflexivity.
    rewrite HL. apply safety_empty_sep. }
  assert (HC2 : closed_Qual 2 0 (length Σ) d2↑).
  { pose proof (safety_typing_type_closed _ _ _ _ _ _ HA) as Hcl.
    inversion Hcl; assumption. }
  assert (HSB : kill_sep (local_locs (tapp v b)) (d2 <~ᵈ ∅ ; ∅))
    by eauto using safety_sep_open2, safety_sep_empty.
  pose proof (safety_ctx_scope _ _ _ _ HC) as Hφ.
  assert (HSO : kill_sep (local_locs b) (d1 ⋒ df)).
  { eapply safety_sep_of_sub; [apply safety_overlap_right_bound|].
    eauto using safety_sep_join_right, safety_sep_fresh. }
  assert (Hsep : kill_sep δ df).
  { apply safety_sep_sym. eapply safety_disjointq_sep_old; [exact HD|].
    exact (safety_typing_qual_closed _ _ _ _ _ _ HA). }
  pose proof (safety_overlap_plus_r df d1 δ Hsep) as Hnarrow.
  pose proof (safety_overlap_plus_l d1 df δ Hsep) as Hnarrow'.
  pose proof (safety_keep_value _ _ _ _ _ _ _ _ _ _ _ _ HC HC' HE HU HA HV HS1) as HA'.
  pose proof (safety_typing_type_closed _ _ _ _ _ _ HA') as HCl.
  assert (Hcal : has_type [] φ' Σ' v (TFun (df ⋒ (d1 ⋓ δ)) d2 T1 T2) df).
  { eapply t_sub; [exact HA'| |exact (safety_typing_qual_bound _ _ _ _ _ _ HA')|].
    - apply safety_sub_fun_domain; try assumption.
      + exact (safety_typing_qual_closed _ _ _ _ _ _ HA').
      + eapply safety_qual_closed_of_sub; [exact Hnarrow|].
        inversion HCl; assumption.
    - rewrite HL. apply safety_empty_sep. }
  apply (Preserve Σ' δ φ' ϰ'); try assumption.
  - eauto using safety_disjointq_old.
  - eapply safety_cast_in_step with (t := tapp v b) (σ := σ) (σ' := σ')
        (d' := d2 <~ᵈ df ; (d1 ⋓ δ)); try eassumption.
    + apply safety_sep_join_left; [|exact Hsepδ].
      change (kill_sep (local_locs v) δ). now rewrite HL; apply safety_empty_sep.
    + rewrite <- (safety_fresh_type_unchanged T2 T1 d1 δ Hfree0 Hfree1).
      eapply t_app_fresh with (φd := qdiff φ' (local_locs v)); [exact Hcal| | |exact Hfree0| | |reflexivity| | |].
      * exact (safety_scope_over_value _ _ _ _ _ _ HV (proj1 HW) HB').
      * intros HD'. apply Hfree1. now apply (safety_fresh_remains_monotone d1 δ).
      * exact (safety_update_scope_fresh _ _ _ _ _ _ _ _ HU' Hφ HSB HD1).
      * eapply safety_subq_trans; [exact Hnarrow'|].
        exact (safety_update_scope_fresh _ _ _ _ _ _ _ _ HU Hφ HSO HO).
      * exact (safety_step_carries_sep _ _ _ _ _ _ (safety_ctx_length _ _ _ _ HC) HR
          (proj1 (proj2 HW)) Hσ (safety_typing_qual_closed _ _ _ _ _ _ HA) HS1).
      * exact (safety_step_carries_sep_general _ _ _ _ _ _ _ _ (safety_ctx_length _ _ _ _ HC)
          Hstep HW Hσ HC2 HS2).
      * rewrite HL. apply safety_empty_sep.
    + apply safety_openq_plus_arg.
Qed.

Local Definition safety_ready_redex (t : tm) : Prop :=
  match t with
  | ttapp v | tref v | tderef v | twithc _ v | twithr v _ => value v
  | tapp a b | trefat a b | tassign a b => value a /\ value b
  | _ => False
  end.

Local Definition safety_preservation_statement : Prop :=
  forall t σ t' σ', step t σ t' σ' ->
  forall Σ φ ϰ T d,
    has_type [] φ Σ t T d -> wf_step t ->
    CtxOK [] φ Σ ϰ σ -> wf_store σ -> wf_senv Σ ->
    preserve [] Σ ϰ φ (local_locs t) t' T d σ'.

Local Definition safety_redex_preservation_statement : Prop :=
  forall t σ t' σ', step t σ t' σ' -> safety_ready_redex t ->
  forall Σ φ ϰ T d,
    has_type [] φ Σ t T d -> wf_step t ->
    CtxOK [] φ Σ ϰ σ -> wf_store σ -> wf_senv Σ ->
    preserve [] Σ ϰ φ (local_locs t) t' T d σ'.

Local Ltac safety_rebuild_frame outerStep ht hctx henv :=
  let G := fresh "G" in let HG := fresh "HG" in
  let s := fresh "subject" in let HS := fresh "HS" in
  let HT := type of ht in
  lazymatch HT with
  | has_type [] ?φ ?Σ ?t ?T ?d =>
    remember ([] : tenv) as G eqn:HG in ht;
    remember t as s eqn:HS in ht;
    revert hctx henv;
    induction ht;
      try match goal with HE : @eq tenv ?g [] |- _ => subst g end;
      intros hctx henv;
      try match goal with HE : @eq tm _ _ |- _ => discriminate HE end;
      try solve [
        match goal with
        | Hsub : stp [] _ ?A ?q _ _, HE : @eq tm ?lhs _ |- _ =>
          subst lhs;
          eapply safety_preserve_sub with (T := A) (d := q);
            [exact outerStep|eassumption|eassumption|exact hctx|exact Hsub|
             assumption|assumption|];
          eauto
        end
      ];
      match goal with HE : @eq tm _ _ |- _ => inversion HE; subst end
  end.

(* Lift preservation of the root reductions through the evaluation contexts.
   The context lemmas transport typing and separation across store changes. *)
Local Lemma safety_preservation_from_redexes :
  safety_redex_preservation_statement -> safety_preservation_statement.
Proof.
  intros Hred t σ t' σ' HR.
  induction HR; intros Σ φ ϰ T d HT HW HC Hσ HΣ.
  - eapply Hred; [apply step_ttapp|apply value_ttabs|exact HT|exact HW|exact HC|exact Hσ|exact HΣ].
  - eapply Hred; [eapply step_beta; eassumption|simpl; auto using value_abs|
      exact HT|exact HW|exact HC|exact Hσ|exact HΣ].
  - eapply Hred; [eapply step_ref; eassumption|exact H|exact HT|exact HW|exact HC|exact Hσ|exact HΣ].
  - eapply Hred; [eapply step_refat; eassumption|simpl; auto using value_loc|
      exact HT|exact HW|exact HC|exact Hσ|exact HΣ].
  - eapply Hred; [eapply step_deref; eassumption|apply value_loc|
      exact HT|exact HW|exact HC|exact Hσ|exact HΣ].
  - eapply Hred; [eapply step_assign; eassumption|simpl; auto using value_loc|
      exact HT|exact HW|exact HC|exact Hσ|exact HΣ].
  - eapply Hred; [eapply step_twithr; eassumption|exact H|exact HT|exact HW|exact HC|exact Hσ|exact HΣ].
  - eapply Hred; [eapply step_twithc; eassumption|exact H|exact HT|exact HW|exact HC|exact Hσ|exact HΣ].
  - pose proof (step_c_tapp _ _ _ _ HR) as Houter.
    safety_rebuild_frame Houter HT HC HΣ.
    + eapply safety_preserve_ttapp_ctx; eauto.
    + eapply safety_preserve_ttapp_fresh_ctx; eauto.
  - pose proof (step_c_ref _ _ _ _ HR) as Houter.
    safety_rebuild_frame Houter HT HC HΣ.
    eapply safety_preserve_ref_ctx; eauto.
  - pose proof (step_c_refat_l _ _ _ _ _ H HR) as Houter.
    safety_rebuild_frame Houter HT HC HΣ.
    eapply safety_preserve_refat_l_ctx; try eassumption.
    eapply IHHR; try eassumption.
    + eapply safety_typing_scope_weaken; [eassumption|apply safety_diff_le|].
      apply safety_dom_closed. exact (safety_ctx_scope _ _ _ _ HC).
    + exact (proj1 HW).
  - pose proof (step_c_refat_r t1 t2 t2' σ σ' HR) as Houter.
    safety_rebuild_frame Houter HT HC HΣ.
    eapply safety_preserve_refat_r_ctx; try eassumption.
    eapply IHHR; try eassumption. exact (proj1 (proj2 HW)).
  - pose proof (step_c_deref _ _ _ _ HR) as Houter.
    safety_rebuild_frame Houter HT HC HΣ.
    eapply safety_preserve_deref_ctx; eauto.
  - pose proof (step_c_app_l t1 t1' t2 σ σ' HR) as Houter.
    safety_rebuild_frame Houter HT HC HΣ.
    + eapply safety_preserve_app_l_ctx; try eassumption.
      eapply IHHR; try eassumption. exact (proj1 HW).
    + eapply safety_preserve_app_fresh_l_ctx; try eassumption.
      eapply IHHR; try eassumption. exact (proj1 HW).
  - pose proof (step_c_app_r _ _ _ _ _ H HR) as Houter.
    safety_rebuild_frame Houter HT HC HΣ.
    + eapply safety_preserve_app_r_ctx; try eassumption.
      eapply IHHR; try eassumption.
      * eapply safety_typing_scope_weaken; [eassumption|apply safety_diff_le|].
        apply safety_dom_closed. exact (safety_ctx_scope _ _ _ _ HC).
      * exact (proj1 (proj2 HW)).
    + eapply safety_preserve_app_fresh_r_ctx; try eassumption.
      eapply IHHR; try eassumption.
      * eapply safety_typing_scope_weaken; [eassumption|apply safety_diff_le|].
        apply safety_dom_closed. exact (safety_ctx_scope _ _ _ _ HC).
      * exact (proj1 (proj2 HW)).
  - pose proof (step_c_assign_l t1 t1' t2 σ σ' HR) as Houter.
    safety_rebuild_frame Houter HT HC HΣ.
    eapply safety_preserve_assign_l_ctx; try eassumption.
    eapply IHHR; try eassumption. exact (proj1 HW).
  - pose proof (step_c_assign_r _ _ _ _ _ H HR) as Houter.
    safety_rebuild_frame Houter HT HC HΣ.
    eapply safety_preserve_assign_r_ctx; try eassumption.
    eapply IHHR; try eassumption.
    + eapply safety_typing_scope_weaken; [eassumption|apply safety_diff_le|].
      apply safety_dom_closed. exact (safety_ctx_scope _ _ _ _ HC).
    + exact (proj1 (proj2 HW)).
  - pose proof (step_c_twithr_l t1 t2 t1' σ σ' HR) as Houter.
    safety_rebuild_frame Houter HT HC HΣ.
    eapply safety_preserve_withr_ctx; try eassumption;
      try exact (proj1 HW); try exact (proj1 (proj2 HW)); try exact (proj2 (proj2 HW)).
    eapply IHHR; try eassumption. exact (proj1 HW).
  - pose proof (step_c_twithc l t t' σ σ' HR) as Houter.
    safety_rebuild_frame Houter HT HC HΣ.
    eapply safety_preserve_withc_ctx; eauto.
Qed.

Local Definition safety_value_storage : Prop :=
  forall Σ φ ϰ σ v T q,
    CtxOK [] φ Σ ϰ σ -> wf_senv Σ -> wf_step v -> value v ->
    has_type [] φ Σ v T q -> ♦∉ q -> vtp Σ ϰ φ v T q.

Local Lemma safety_stp_ref_inv_full Σ S d U q e :
  stp [] Σ S d (TRef q U) e ->
  exists T r, S = TRef r T /\
    stp [] Σ T ∅ U ∅ /\ stp [] Σ U ∅ T ∅ /\ r ⊑↑ q /\ q ⊑↑ r.
Proof.
  intros H.
  remember ([] : tenv) as Γ eqn:HΓ. remember (TRef q U) as R eqn:HR.
  revert U q HR.
  induction H; subst; intros U q HR; try discriminate.
  - inversion HR; subst. exists T1, q1.
    refine (conj eq_refl (conj H0 (conj H1 (conj _ _))));
      eauto using safety_closed_qstp.
  - destruct (IHstp2 eq_refl U q HR) as (V & r & HV & HVU & HUV & Hrq & Hqr).
    destruct (IHstp1 eq_refl V r HV) as (T & r' & HS & HTV & HVT & Hr'r & Hrr').
    exists T, r'. refine (conj HS (conj _ (conj _ (conj _ _)))).
    + eapply s_trans; [exact HTV|exact HVU].
    + eapply s_trans; [exact HUV|exact HVT].
    + exact (safety_subq_trans _ _ _ Hr'r Hrq).
    + exact (safety_subq_trans _ _ _ Hqr Hrr').
Qed.

Local Lemma safety_loc_ref_inv_full Σ φ l o U q d :
  has_type [] φ Σ &(l,o) (TRef q U) d ->
  exists T r, sindexr l o Σ = Some (T,r) /\ r ⊑↑ q /\ q ⊑↑ r /\
    (T = U \/ (stp [] Σ T ∅ U ∅ /\ stp [] Σ U ∅ T ∅)).
Proof.
  intros H.
  remember ([] : tenv) as Γ eqn:HΓ. remember (&(l,o)) as v eqn:Hv.
  remember (TRef q U) as R eqn:HR. revert U q HR.
  induction H; subst; intros U r HR; try discriminate.
  - inversion Hv; inversion HR; subst.
    exists U, r. refine (conj H0 (conj (safety_subq_refl r) (conj (safety_subq_refl r) (or_introl eq_refl)))).
  - destruct (safety_stp_ref_inv_full _ _ _ _ _ _ ltac:(rewrite <- HR; exact H0))
      as (T & r' & HT & Hstp & Hrev & Hr & Hrr').
    destruct (IHhas_type eq_refl eq_refl T r' HT)
      as (V & r'' & Hlook & Hr' & Hr'' & [-> | (Hstp' & Hrev')]).
    + exists T, r''. refine (conj Hlook (conj _ (conj _ (or_intror (conj Hstp Hrev))))).
      * exact (safety_subq_trans _ _ _ Hr' Hr).
      * exact (safety_subq_trans _ _ _ Hrr' Hr'').
    + exists V, r''. refine (conj Hlook (conj _ (conj _ _))).
      * exact (safety_subq_trans _ _ _ Hr' Hr).
      * exact (safety_subq_trans _ _ _ Hrr' Hr'').
      * right. split.
        -- eapply s_trans; [exact Hstp'|exact Hstp].
        -- eapply s_trans; [exact Hrev|exact Hrev'].
Qed.

Local Lemma safety_update_identity {A} (xs : list A) k x :
  indexr k xs = Some x -> update xs k x = xs.
Proof.
  induction xs as [|a xs IH]; simpl; [discriminate|].
  destruct (k =? length xs).
  - intros H. inversion H; reflexivity.
  - intro H. now rewrite (IH H).
Qed.

Local Lemma safety_assign_redex_with_storage Σ φ ϰ σ l o v T q d :
  safety_value_storage ->
  has_type [] φ Σ &(l,o) (TRef q T) d ->
  has_type [] φ Σ v T q -> ♦∉ q -> value v -> wf_step v ->
  CtxOK [] φ Σ ϰ σ -> wf_senv Σ -> wf_store σ ->
  exists σ', step (tassign &(l,o) v) σ tunit σ' /\
    preserve [] Σ ϰ φ (local_locs (tassign &(l,o) v)) tunit TUnit ∅ σ'.
Proof.
  intros Store HT HV Hnf Hv Hw HC HΣ Hσ.
  destruct (safety_loc_ref_inv_full _ _ _ _ _ _ _ HT) as (U & r & Hcell & Hrq & Hqr & Hsub).
  destruct (safety_loc_lookup _ _ _ _ _ _ HT) as (Hl & _).
  destruct (safety_sindexr _ _ _ _ Hcell) as (c & Hc & Ho).
  pose proof (safety_ctx_live_not_killed _ _ _ _ _ HC Hl) as Hnot.
  pose proof (safety_ctx_scope _ _ _ _ HC) as Hφ.
  pose proof (safety_ctx_length _ _ _ _ HC) as Hlen.
  destruct HC as (_ & _ & _ & Hdead & HS & Hstore).
  assert (HC : CtxOK [] φ Σ ϰ σ).
  { refine (conj (safety_ctx_dom _ _ Hlen) (conj Hlen (conj Hφ (conj Hdead (conj HS Hstore))))). }
  destruct (proj2 (Hstore l o c U r) Hnot Hl Hc) as (s & (Hs & Hsize) & Hget).
  destruct (Hget Ho) as (w & Hwo & _).
  pose proof (safety_indexr_bound _ _ _ Hwo) as Hoffset.
  change (@indexr senvs l Σ = Some c) in Hc.
  destruct (proj2 (HΣ l c Hc) o U r Ho) as (Hrnf & HU & Hrclosed).
  pose proof (safety_typing_qual_bound _ _ _ _ _ _ HV) as HQbound.
  assert (Hrbound : r ⊑↑ φ ⊔ {♦}) by exact (safety_subq_trans _ _ _ Hrq HQbound).
  assert (Hvr : has_type [] φ Σ v U r).
  { destruct Hsub as [-> | [_ Hcast]].
    - eapply safety_qual_cast; [exact HV|exact Hqr|exact Hrbound|].
      rewrite (safety_value_scopes _ Hv Hw). apply safety_empty_sep.
    - eapply t_sub; [exact HV| |exact Hrbound|].
      + eapply safety_stp_requalify; [exact Hcast|apply qs_sq; assumption].
      + rewrite (safety_value_scopes _ Hv Hw). apply safety_empty_sep. }
  pose proof (Store _ _ _ _ _ _ _ HC HΣ Hw Hv Hvr Hrnf) as Hvt.
  assert (HΣid : @update senvs Σ l c = Σ) by now apply safety_update_identity.
  assert (HL' : length c = length (update s o v)) by now rewrite safety_update_length.
  destruct (safety_ctx_replace_arena Σ ϰ φ σ l c c s (update s o v) HC Hl Hc Hs
      ltac:(exists []; reflexivity) HL') as (_ & _ & HC').
  { intros i V p Hi. rewrite safety_indexr_update, HΣid.
    destruct (i =? o) eqn:Heq.
    - apply Nat.eqb_eq in Heq. subst i. rewrite Ho in Hi. inversion Hi; subst V p.
      exists v. rewrite Hwo. auto.
    - destruct (proj2 (Hstore l i c V p) Hnot Hl Hc)
        as (ss & (Hss & _) & Hvals).
      rewrite Hs in Hss. inversion Hss; subst ss. exact (Hvals Hi). }
  rewrite HΣid in HC'.
  exists (supdate σ l o v). split.
  - eapply step_assign with (s := s); try assumption.
    exact (safety_indexr_bound _ _ _ Hs).
  - rewrite (safety_supdate_as_update _ _ _ _ _ Hs).
    apply (Preserve Σ ∅ φ ϰ); try assumption.
    + apply safety_senv_refl.
    + apply env_phi; [apply safety_senv_refl|reflexivity].
    + apply safety_empty_bound.
    + apply disj_bot.
    + apply t_base. now apply safety_dom_closed.
    + eapply safety_change_cell_wf; [exact Hs| |exact Hσ].
      intros i x Hx. rewrite safety_indexr_update in Hx.
      destruct (i =? o); [|auto].
      destruct (indexr i s); [|discriminate].
      inversion Hx; subst. auto.
    + exact I.
Qed.

Local Lemma safety_value_no_step v σ t' σ' :
  value v -> ~ step v σ t' σ'.
Proof. intros Hval Hstep. inversion Hval; subst; inversion Hstep. Qed.

Local Lemma safety_step_deterministic :
  deterministic step.
Proof.
  unfold deterministic.
  intros t t1 t2 σ σ1 σ2 H.
  revert t2 σ2. induction H; intros u σ'' HR; inversion HR; subst;
    try solve [split; congruence];
    try solve [
      exfalso; eapply safety_value_no_step; [eassumption|eassumption]
    ];
    try solve [
      exfalso; eapply safety_value_no_step; [constructor|eassumption]
    ].
  all: try solve [
    match goal with Hs : step ?v ?s ?u ?s' |- _ =>
      exfalso; exact (safety_value_no_step v s u s' ltac:(eassumption || constructor) Hs)
    end].
  all: match goal with
  | IH : forall u s, step ?x ?σ u s -> _,
    Hs : step ?x ?σ ?y ?s |- _ =>
      specialize (IH y s Hs); destruct IH; subst; split; reflexivity
  end.
Qed.

Local Definition safety_beta_substitution : Prop :=
  (forall Σ φ body T q,
    has_type [] φ Σ (ttapp (ttabs body)) T q -> wf_step (ttabs body) ->
    has_type [] φ Σ (body <~ᵗ (ttabs body) ; tunit) T q) /\
  (forall Σ φ body v T q,
    value v -> has_type [] φ Σ (tapp (tabs body) v) T q -> wf_step (tapp (tabs body) v) ->
    has_type [] φ Σ (body <~ᵗ (tabs body) ; v) T q).

Local Definition safety_arena_substitution : Prop :=
  forall Σ φ φd b v T q U d,
    wf_senv Σ ->
    has_type [] φ Σ v T q -> value v -> ♦∉ q ->
    closed_ty 0 0 (length Σ) U -> closed_Qual 0 0 (length Σ) d↑ ->
    closed_tm 2 0 (length Σ) b -> wf_step (twithr v b) ->
    φd ⊑↑ φ ->
    has_type [(bind_tm, false, TRef q T, {♦}); (bind_tm, true, TUnit, {♦})]
      (φd ⊔ $!1) Σ (b <~²ᵗ ([] : tenv)) U d ->
    has_type [] (φ ⊔ &!(length Σ)) ([(T,q)] :: Σ)
      (b <~ᵗ tunit ; (tloc (length Σ) 0)) U d.

Local Lemma safety_preserve_pure Σ φ ϰ σ t t' T q :
  wf_senv Σ -> CtxOK [] φ Σ ϰ σ -> wf_store σ -> wf_step t' ->
  has_type [] φ Σ t' T q ->
  preserve [] Σ ϰ φ (local_locs t) t' T q σ.
Proof.
  intros HΣ HC Hσ Hw HT.
  apply (Preserve Σ ∅ φ ϰ); try assumption.
  - apply safety_senv_refl.
  - apply env_phi; [apply safety_senv_refl|reflexivity].
  - apply safety_empty_bound.
  - apply disj_bot.
  - now apply safety_typing_plus_empty.
Qed.

Local Ltac safety_align_reduct :=
  match goal with
  | H1 : step ?t ?σ ?u1 ?s1, H2 : step ?t ?σ ?u2 ?s2,
    HP : preserve [] _ _ _ _ ?u1 _ _ ?s1
    |- preserve [] _ _ _ _ ?u2 _ _ ?s2 =>
      destruct (safety_step_deterministic _ _ _ _ _ _ H1 H2) as [Heq1 Heq2];
      try rewrite <- Heq1; try rewrite <- Heq2; exact HP
  end.

Local Lemma safety_redexes_from_substitution :
  safety_value_storage -> safety_beta_substitution -> safety_arena_substitution ->
  safety_redex_preservation_statement.
Proof.
  intros Store (Htabs & Hbeta) Harena t σ t' σ' HR Hval Σ φ ϰ T d HT HW HC Hσ HΣ.
  destruct HR; simpl in Hval;
    try solve [
      try destruct Hval as [? ?];
      match goal with Hs : step ?a ?s ?a' ?s' |- _ =>
        exfalso; exact (safety_value_no_step a s a' s' ltac:(eassumption) Hs)
      end
    ].
  - pose proof (step_ttapp t σ) as Houter.
    destruct (safety_step_wf _ _ _ _ Houter HW Hσ) as [HW' _].
    apply safety_preserve_pure; try assumption.
    now apply Htabs.
  - pose proof (step_beta t v σ H) as Houter.
    destruct (safety_step_wf _ _ _ _ Houter HW Hσ) as [HW' _].
    apply safety_preserve_pure; try assumption.
    now apply Hbeta.
  - pose proof (step_ref v σ H) as Houter.
    safety_rebuild_frame Houter HT HC HΣ.
    edestruct safety_ref_redex_typed_value as (? & ? & ? & ?);
      try eassumption; [|safety_align_reduct].
    eapply Store; eassumption.
  - pose proof (step_refat v l o s σ H H0) as Houter.
    safety_rebuild_frame Houter HT HC HΣ.
    destruct HW as (Hw & _ & _).
    assert (Hinit : has_type [] φ Σ v T d).
    { eapply safety_typing_scope_weaken; [eassumption|apply safety_diff_le|].
      apply safety_dom_closed. exact (safety_ctx_scope _ _ _ _ HC). }
    edestruct safety_refat_redex_typed_value as (? & ? & ? & ?);
      try eassumption; [|safety_align_reduct].
    eapply Store; eassumption.
  - pose proof (step_deref σ l o s v H H0) as Houter.
    safety_rebuild_frame Houter HT HC HΣ.
    edestruct safety_deref_redex as (? & ? & ?); try eassumption.
    safety_align_reduct.
  - pose proof (step_assign σ l o v s H H0 H1 H2) as Houter.
    safety_rebuild_frame Houter HT HC HΣ.
    destruct HW as (_ & Hw & _).
    assert (Hinit : has_type [] φ Σ v T d1).
    { eapply safety_typing_scope_weaken; [eassumption|apply safety_diff_le|].
      apply safety_dom_closed. exact (safety_ctx_scope _ _ _ _ HC). }
    edestruct safety_assign_redex_with_storage as (? & ? & ?);
      try eassumption.
    safety_align_reduct.
  - pose proof (step_twithr σ v t H) as Houter.
    safety_rebuild_frame Houter HT HC HΣ.
    edestruct safety_withr_redex_opened_body as (? & ? & ? & ?);
      try eassumption; try exact (proj1 HW).
    + eapply Store; try eassumption. exact (proj1 HW).
    + eapply Harena; eassumption.
    + safety_align_reduct.
  - pose proof (step_twithc σ v l H) as Houter.
    safety_rebuild_frame Houter HT HC HΣ.
    apply (proj2 (safety_withc_redex _ _ _ _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)
      ltac:(eassumption) H HW HΣ HC Hσ)).
Qed.

Local Lemma safety_type_safety_from_substitution :
  safety_value_storage -> safety_beta_substitution -> safety_arena_substitution ->
  forall {Σ ϰ t T d φ},
    has_type [] φ Σ t T d -> wf_senv Σ -> wf_step t ->
    value t \/ (forall {σ}, CtxOK [] φ Σ ϰ σ -> wf_store σ ->
      exists t' σ', step t σ t' σ' /\ preserve [] Σ ϰ φ (local_locs t) t' T d σ').
Proof.
  intros Hvalues Hbeta Harena Σ ϰ t T d φ HT HΣ Hw.
  assert (Hdec : value t \/ ~ value t).
  { destruct t; try solve [right; intro H; inversion H]; left; constructor. }
  destruct Hdec as [Hv | Hnv]; [now left|right].
  intros σ HC Hσ. destruct (safety_progress _ _ _ _ _ _ _ HT HC) as [Hv | (t' & σ' & Hstep)].
  - contradiction.
  - exists t', σ'. split; [exact Hstep|].
    eapply (safety_preservation_from_redexes
      (safety_redexes_from_substitution Hvalues Hbeta Harena)); eassumption.
Qed.

Local Definition arena_shift_bits (n : nat) (f : nats) : nats :=
  fun x => if x <? n then false else f (x - n).

Local Definition arena_shift_qual (n : nat) (q : qual) : qual :=
  (qfresh q, arena_shift_bits n (qfvs q), qbvs q, qlocs q).

(* Describe renaming by the bits of a qualifier so the proofs can use its
   membership behavior without equating the underlying Boolean functions. *)
Local Definition arena_qual_shifted (n : nat) (p q : qual) : Prop :=
  qfresh q = qfresh p /\
  (forall x, qfvs q x = arena_shift_bits n (qfvs p) x) /\
  (forall x, qbvs q x = qbvs p x) /\
  (forall x, qlocs q x = qlocs p x).

Local Lemma arena_shift_qual_spec n q :
  arena_qual_shifted n q (arena_shift_qual n q).
Proof. repeat split; reflexivity. Qed.

Local Lemma arena_shift_qual_rigid n b L q :
  closed_Qual b 0 L q↑ -> arena_qual_shifted n q q.
Proof.
  intros (Hf & _ & _). repeat split; try reflexivity.
  intro x. unfold arena_shift_bits.
  assert (H : forall i, qfvs q i = false).
  { intro i. destruct (qfvs q i) eqn:Hi; [specialize (Hf i Hi); lia|reflexivity]. }
  rewrite (H x). destruct (x <? n); [reflexivity|now rewrite H].
Qed.

Local Lemma arena_shift_qual_le n p p' q q' :
  arena_qual_shifted n p p' -> arena_qual_shifted n q q' ->
  p ⊑↑ q -> p' ⊑↑ q'.
Proof.
  intros (Hp & Hpf & Hpb & Hpl) (Hq & Hqf & Hqb & Hql) H.
  apply safety_qual_le in H as (H & Hf & Hb & Hl).
  apply safety_qual_le. repeat split.
  - now rewrite Hp, Hq.
  - intros x. rewrite Hpf, Hqf. unfold arena_shift_bits.
    destruct (x <? n); [auto|apply Hf].
  - intros x. rewrite Hpb, Hqb. apply Hb.
  - intros x. rewrite Hpl, Hql. apply Hl.
Qed.

Local Lemma arena_shift_qual_closed n b f L p q :
  arena_qual_shifted n p q ->
  closed_Qual b f L p↑ -> closed_Qual b (n + f) L q↑.
Proof.
  intros (_ & HF & HB & HL) (Hf & Hb & Hl). repeat split.
  - intros x Hx. change (qfvs q x = true) in Hx. rewrite HF in Hx.
    unfold arena_shift_bits in Hx.
    destruct (x <? n) eqn:Hxlt; [discriminate|].
    apply Nat.ltb_ge in Hxlt. specialize (Hf _ Hx). lia.
  - intros x Hx. change (qbvs q x = true) in Hx. rewrite HB in Hx. now apply Hb.
  - intros x Hx. change (qlocs q x = true) in Hx. rewrite HL in Hx. now apply Hl.
Qed.

Local Lemma arena_shift_qual_closed_rigid n b L p q :
  arena_qual_shifted n p q ->
  closed_Qual b 0 L p↑ -> closed_Qual b 0 L q↑.
Proof.
  intros (_ & HF & HB & HL) (Hf & Hb & Hl). repeat split.
  - intros x Hx. change (qfvs q x = true) in Hx. rewrite HF in Hx.
    unfold arena_shift_bits in Hx.
    destruct (x <? n); [discriminate|].
    specialize (Hf _ Hx). lia.
  - intros x Hx. change (qbvs q x = true) in Hx. rewrite HB in Hx. now apply Hb.
  - intros x Hx. change (qlocs q x = true) in Hx. rewrite HL in Hx. now apply Hl.
Qed.

Local Lemma arena_shift_qual_join n p p' q q' :
  arena_qual_shifted n p p' -> arena_qual_shifted n q q' ->
  arena_qual_shifted n (p ⊔ q) (p' ⊔ q').
Proof.
  intros (Hp & Hpf & Hpb & Hpl) (Hq & Hqf & Hqb & Hql).
  unfold arena_qual_shifted. cbn [qor qfresh qfvs qbvs qlocs fst snd].
  repeat split.
  - now rewrite Hp, Hq.
  - intros x. unfold n_or. rewrite Hpf, Hqf. unfold arena_shift_bits.
    destruct (x <? n); reflexivity.
  - intros x. unfold n_or. now rewrite Hpb, Hqb.
  - intros x. unfold n_or. now rewrite Hpl, Hql.
Qed.

Local Lemma arena_shift_name_qual n x :
  arena_qual_shifted n ($!x) ($!(n+x)).
Proof.
  repeat split; try reflexivity.
  intro y. change ((y =? n+x) = arena_shift_bits n (n_one x) y).
  unfold arena_shift_bits, n_one.
  destruct (y <? n) eqn:Hlt.
  - apply Nat.eqb_neq. apply Nat.ltb_lt in Hlt. lia.
  - apply Nat.ltb_ge in Hlt.
    destruct (y =? n+x) eqn:H1, (y - n =? x) eqn:H2; try reflexivity.
    all: rewrite ?Nat.eqb_eq, ?Nat.eqb_neq in *; lia.
Qed.

Local Lemma arena_shift_open_qual n k q q' a a' :
  arena_qual_shifted n q q' -> arena_qual_shifted n a a' ->
  arena_qual_shifted n (open_qual k a q) (open_qual k a' q').
Proof.
  intros Hq Ha. pose proof Hq as (HF & Hf & Hb & Hl).
  unfold open_qual. rewrite Hb. destruct (qbvs q k); [|exact Hq].
  apply arena_shift_qual_join; [|exact Ha].
  repeat split; try assumption.
  intro x. change (n_diff (qbvs q') (n_one k) x = n_diff (qbvs q) (n_one k) x).
  unfold n_diff. now rewrite Hb.
Qed.

Inductive arena_ty_shifted (n : nat) : ty -> ty -> Prop :=
| arena_shift_top : arena_ty_shifted n TTop TTop
| arena_shift_unit : arena_ty_shifted n TUnit TUnit
| arena_shift_free : forall x,
    arena_ty_shifted n (TVar (varF x)) (TVar (varF (n+x)))
| arena_shift_bound : forall x,
    arena_ty_shifted n (TVar (varB x)) (TVar (varB x))
| arena_shift_ref : forall q q' T T',
    arena_qual_shifted n q q' -> arena_ty_shifted n T T' ->
    arena_ty_shifted n (TRef q T) (TRef q' T')
| arena_shift_fun : forall q r q' r' T U T' U',
    arena_qual_shifted n q q' -> arena_qual_shifted n r r' ->
    arena_ty_shifted n T T' -> arena_ty_shifted n U U' ->
    arena_ty_shifted n (TFun q r T U) (TFun q' r' T' U')
| arena_shift_all : forall q r q' r' T U T' U',
    arena_qual_shifted n q q' -> arena_qual_shifted n r r' ->
    arena_ty_shifted n T T' -> arena_ty_shifted n U U' ->
    arena_ty_shifted n (TAll q r T U) (TAll q' r' T' U').

Local Lemma arena_shift_ty_rigid n b L T :
  closed_ty b 0 L T -> arena_ty_shifted n T T.
Proof.
  intro H. remember 0 as f eqn:HF.
  induction H; subst; try lia; constructor; eauto using arena_shift_qual_rigid.
Qed.

Local Lemma arena_shift_ty_exists n T : exists T', arena_ty_shifted n T T'.
Proof.
  induction T; try (eexists; constructor; fail).
  - destruct v.
    + exists (TVar (varF (n+i))). constructor.
    + exists (TVar (varB i)). constructor.
  - destruct IHT1 as [T1' HT], IHT2 as [T2' HU].
    exists (TAll (arena_shift_qual n q) (arena_shift_qual n q0) T1' T2').
    constructor; auto using arena_shift_qual_spec.
  - destruct IHT1 as [T1' HT], IHT2 as [T2' HU].
    exists (TFun (arena_shift_qual n q) (arena_shift_qual n q0) T1' T2').
    constructor; auto using arena_shift_qual_spec.
  - destruct IHT as [T' HT]. exists (TRef (arena_shift_qual n q) T').
    constructor; auto using arena_shift_qual_spec.
Qed.

Local Lemma arena_shift_ty_closed n T T' :
  arena_ty_shifted n T T' ->
  forall b f L, closed_ty b f L T -> closed_ty b (n+f) L T'.
Proof.
  intros H. induction H; intros b f L HC; inversion HC; subst; constructor;
    eauto using arena_shift_qual_closed; lia.
Qed.

Local Lemma arena_shift_ty_closed_rigid n T T' :
  arena_ty_shifted n T T' ->
  forall b L, closed_ty b 0 L T -> closed_ty b 0 L T'.
Proof.
  intros H. induction H; intros b L HC; inversion HC; subst; try lia; constructor;
    eauto using arena_shift_qual_closed_rigid.
Qed.

Local Lemma arena_shift_open_ty n k T T' U U' q q' :
  arena_ty_shifted n T T' -> arena_ty_shifted n U U' -> arena_qual_shifted n q q' ->
  arena_ty_shifted n (open_rec_ty k U q T) (open_rec_ty k U' q' T').
Proof.
  intros H HU Hq. revert k. induction H; intros k; simpl;
    try solve [constructor; eauto using arena_shift_open_qual].
  destruct (k =? x); [exact HU|constructor].
Qed.

Local Definition arena_env_shifted n (Γ Δ : tenv) : Prop :=
  length Δ = n + length Γ /\
  forall x k b T q, indexr x Γ = Some (k,b,T,q) ->
    exists T' q', indexr (n+x) Δ = Some (k,b,T',q') /\
      arena_ty_shifted n T T' /\ arena_qual_shifted n q q'.

Local Lemma arena_env_shift_cons n Γ Δ k b T T' q q' :
  arena_env_shifted n Γ Δ -> arena_ty_shifted n T T' -> arena_qual_shifted n q q' ->
  arena_env_shifted n ((k,b,T,q)::Γ) ((k,b,T',q')::Δ).
Proof.
  intros (Hlen & Hget) HT HQ. split; [simpl; lia|].
  intros x k0 b0 U p HI. simpl in HI.
  destruct (x =? length Γ) eqn:Hx.
  - apply Nat.eqb_eq in Hx. subst x. inversion HI; subst.
    exists T', q'. split; [|auto]. simpl. now rewrite Hlen, Nat.eqb_refl.
  - destruct (Hget _ _ _ _ _ HI) as (U' & p' & HU & HUT & HP).
    exists U', p'. split; [|auto]. simpl. rewrite Hlen.
    assert ((n+x =? n+length Γ) = false)
      by (apply Nat.eqb_neq; apply Nat.eqb_neq in Hx; lia).
    now rewrite H.
Qed.

Local Lemma arena_shift_open_name_qual n (Γ Δ : tenv) q q' :
  length Δ = n + length Γ -> arena_qual_shifted n q q' ->
  arena_qual_shifted n (q <~²ᵈ Γ) (q' <~²ᵈ Δ).
Proof.
  intros HL HQ. unfold openq', openq.
  apply arena_shift_open_qual.
  - apply arena_shift_open_qual; [exact HQ|rewrite HL; apply arena_shift_name_qual].
  - replace (S (length Δ)) with (n+S (length Γ)) by lia.
    apply arena_shift_name_qual.
Qed.

Local Lemma arena_shift_open_name_ty n (Γ Δ : tenv) T T' :
  length Δ = n + length Γ -> arena_ty_shifted n T T' ->
  arena_ty_shifted n (T <~²ᵀ Γ) (T' <~²ᵀ Δ).
Proof.
  intros HL HQ. unfold open_ty', open_ty.
  apply arena_shift_open_ty.
  - apply arena_shift_open_ty; [exact HQ|rewrite HL; constructor|rewrite HL; apply arena_shift_name_qual].
  - replace (S (length Δ)) with (n+S (length Γ)) by lia. constructor.
  - replace (S (length Δ)) with (n+S (length Γ)) by lia. apply arena_shift_name_qual.
Qed.

Local Lemma arena_qstp_input_closed Γ Σ a b :
  qstp Γ Σ a b -> closed_Qual 0 (length Γ) (length Σ) a↑.
Proof.
  intros H. induction H; try assumption;
    eauto using safety_qual_closed_of_sub, safety_fv_closed,
      safety_indexr_bound, safety_qual_join_closed.
  - apply safety_qual_join_closed.
    + eapply safety_fv_closed_weaken; [|exact H0].
      eauto using safety_indexr_bound, Nat.lt_le_incl.
    + eauto using safety_fv_closed, safety_indexr_bound.
  - apply safety_qual_join_closed.
    + eapply safety_fv_closed_weaken; [|exact H0].
      eauto using safety_indexr_bound, Nat.lt_le_incl.
    + eauto using safety_fv_closed, safety_indexr_bound.
Qed.

Local Lemma arena_shift_qual_nonfresh n a b :
  arena_qual_shifted n a b -> ♦∉ a -> ♦∉ b.
Proof.
  intros (H & _) HA. change (~ Is_true (qfresh a)) in HA.
  change (~ Is_true (qfresh b)). now rewrite H.
Qed.

Local Lemma arena_qstp_shifted_endpoints n Γ Σ a b a' b' c d :
  arena_qual_shifted n a a' -> arena_qual_shifted n b b' ->
  arena_qual_shifted n a c -> arena_qual_shifted n b d ->
  qstp Γ Σ c d -> qstp Γ Σ a' b'.
Proof.
  intros HA HB HC HD H.
  assert (Hac : a' ⊑↑ c).
  { eapply arena_shift_qual_le; [exact HA|exact HC|apply safety_subq_refl]. }
  assert (Hdb : d ⊑↑ b').
  { eapply arena_shift_qual_le; [exact HD|exact HB|apply safety_subq_refl]. }
  assert (Hbd : b' ⊑↑ d).
  { eapply arena_shift_qual_le; [exact HB|exact HD|apply safety_subq_refl]. }
  eapply qs_trans.
  - apply qs_sq; [exact Hac|exact (arena_qstp_input_closed _ _ _ _ H)].
  - eapply qs_trans; [exact H|].
    apply qs_sq; [exact Hdb|].
    eapply safety_qual_closed_of_sub; [exact Hbd|exact (safety_qstp_closed _ _ _ _ H)].
Qed.

Local Lemma arena_shift_qstp n Γ Δ Σ a b a' b' :
  qstp Γ Σ a b -> arena_env_shifted n Γ Δ ->
  arena_qual_shifted n a a' -> arena_qual_shifted n b b' ->
  qstp Δ Σ a' b'.
Proof.
  intros H. revert Δ a' b'. induction H; intros Δ a' b' HE HA HB.
  - apply qs_sq.
    + eapply arena_shift_qual_le; eassumption.
    + rewrite (proj1 HE). eapply arena_shift_qual_closed; eassumption.
  - destruct (proj2 HE _ _ _ _ _ H) as (U & p & Hget & Hty & Hp).
    inversion Hty; subst.
    eapply arena_qstp_shifted_endpoints with (n:=n) (a:=df ⊔ $!f) (b:=$!f);
      [exact HA|exact HB| |apply arena_shift_name_qual|].
    + apply arena_shift_qual_join; [exact Hp|apply arena_shift_name_qual].
    + eapply qs_self; [exact Hget| |].
      * exact (arena_shift_qual_closed _ _ _ _ _ _ Hp H0).
      * eapply arena_shift_qual_nonfresh; eassumption.
  - destruct (proj2 HE _ _ _ _ _ H) as (U & p & Hget & Hty & Hp).
    inversion Hty; subst.
    eapply arena_qstp_shifted_endpoints with (n:=n) (a:=df ⊔ $!f) (b:=$!f);
      [exact HA|exact HB| |apply arena_shift_name_qual|].
    + apply arena_shift_qual_join; [exact Hp|apply arena_shift_name_qual].
    + eapply qs_self_all; [exact Hget| |].
      * exact (arena_shift_qual_closed _ _ _ _ _ _ Hp H0).
      * eapply arena_shift_qual_nonfresh; eassumption.
  - destruct (proj2 HE _ _ _ _ _ H) as (U' & p & Hget & Hty & Hp).
    eapply arena_qstp_shifted_endpoints with (n:=n) (a:=$!x) (b:=q1);
      [exact HA|exact HB|apply arena_shift_name_qual|exact Hp|].
    eapply qs_qvar; [exact Hget| | |].
    + exact (arena_shift_ty_closed _ _ _ Hty _ _ _ H0).
    + exact (arena_shift_qual_closed _ _ _ _ _ _ Hp H1).
    + eapply arena_shift_qual_nonfresh; eassumption.
  - destruct (proj2 HE _ _ _ _ _ H) as (U' & p & Hget & Hty & Hp).
    eapply arena_qstp_shifted_endpoints with (n:=n) (a:=$!x) (b:=q1);
      [exact HA|exact HB|apply arena_shift_name_qual|exact Hp|].
    eapply qs_qvar_ty; [exact Hget| | |].
    + exact (arena_shift_ty_closed _ _ _ Hty _ _ _ H0).
    + exact (arena_shift_qual_closed _ _ _ _ _ _ Hp H1).
    + eapply arena_shift_qual_nonfresh; eassumption.
  - pose proof (arena_shift_qual_spec n q) as Hq.
    pose proof (arena_shift_qual_spec n d1) as Hd1.
    pose proof (arena_shift_qual_spec n d2) as Hd2.
    eapply arena_qstp_shifted_endpoints with (n := n) (a := q ⊔ d1) (b := q ⊔ d2);
      [exact HA|exact HB| | |].
    + exact (arena_shift_qual_join _ _ _ _ _ Hq Hd1).
    + exact (arena_shift_qual_join _ _ _ _ _ Hq Hd2).
    + apply qs_cong.
      * now apply IHqstp.
      * rewrite (proj1 HE). exact (arena_shift_qual_closed _ _ _ _ _ _ Hq H0).
  - eapply qs_trans.
    + exact (IHqstp1 _ _ _ HE HA (arena_shift_qual_spec n d2)).
    + exact (IHqstp2 _ _ _ HE (arena_shift_qual_spec n d2) HB).
Qed.

Local Lemma arena_shift_empty n : arena_qual_shifted n ∅ ∅.
Proof. eapply arena_shift_qual_rigid; apply (safety_qual_const_closed 0 0 0 false). Qed.

Local Lemma arena_shift_fresh n : arena_qual_shifted n {♦} {♦}.
Proof. eapply arena_shift_qual_rigid; apply (safety_qual_const_closed 0 0 0 true). Qed.

Local Lemma arena_shift_stp n Γ Δ Σ T a U b T' a' U' b' :
  stp Γ Σ T a U b -> arena_env_shifted n Γ Δ ->
  arena_ty_shifted n T T' -> arena_ty_shifted n U U' ->
  arena_qual_shifted n a a' -> arena_qual_shifted n b b' ->
  stp Δ Σ T' a' U' b'.
Proof.
  intros H. revert Δ T' a' U' b'.
  induction H; intros Δ A a' B b' HE HA HB HF HL.
  - inversion HB; subst. apply s_top.
    + rewrite (proj1 HE). eapply arena_shift_ty_closed; eassumption.
    + eapply arena_shift_qstp; eassumption.
  - inversion HA; inversion HB; subst.
    destruct v as [ [ [k f] U] q].
    destruct (proj2 HE _ _ _ _ _ H) as (U' & q' & Hget & _ & _).
    eapply s_tvar_refl; [exact Hget|].
    eapply arena_shift_qstp; eassumption.
  - inversion HA; subst.
    destruct (proj2 HE _ _ _ _ _ H) as (U' & q' & Hget & HU & Hq).
    eapply s_tvar_trans; [exact Hget| |].
    + eapply arena_shift_ty_closed_rigid; eassumption.
    + eapply IHstp; eassumption.
  - pose proof HA as HSA. pose proof HB as HSB.
    inversion HA; inversion HB; subst. apply s_all.
    + rewrite (proj1 HE). eapply arena_shift_ty_closed; eassumption.
    + rewrite (proj1 HE). eapply arena_shift_ty_closed; eassumption.
    + eapply arena_shift_qstp; eassumption.
    + eapply IHstp1; eassumption.
    + eapply IHstp2.
      * apply arena_env_shift_cons; try eassumption.
        apply arena_env_shift_cons; eauto using arena_shift_fresh.
      * apply arena_shift_open_name_ty; [exact (proj1 HE)|assumption].
      * apply arena_shift_open_name_ty; [exact (proj1 HE)|assumption].
      * apply arena_shift_open_name_qual; [exact (proj1 HE)|assumption].
      * apply arena_shift_open_name_qual; [exact (proj1 HE)|assumption].
  - inversion HA; inversion HB; subst. apply s_base.
    eapply arena_shift_qstp; eassumption.
  - inversion HA; inversion HB; subst. apply s_ref.
    + exact (arena_shift_qstp n Γ Δ Σ d1 d2 a' b' H HE HF HL).
    + eapply IHstp1; eauto using arena_shift_empty.
    + eapply IHstp2; eauto using arena_shift_empty.
    + eapply (arena_shift_qstp n Γ Δ Σ q1 q2); eassumption.
    + eapply (arena_shift_qstp n Γ Δ Σ q2 q1); eassumption.
  - pose proof HA as HSA. pose proof HB as HSB.
    inversion HA; inversion HB; subst. apply s_fun.
    + rewrite (proj1 HE). eapply arena_shift_ty_closed; eassumption.
    + rewrite (proj1 HE). eapply arena_shift_ty_closed; eassumption.
    + eapply arena_shift_qstp; eassumption.
    + eapply IHstp1; eassumption.
    + eapply IHstp2.
      * apply arena_env_shift_cons; try eassumption.
        apply arena_env_shift_cons; eauto using arena_shift_fresh.
      * apply arena_shift_open_name_ty; [exact (proj1 HE)|assumption].
      * apply arena_shift_open_name_ty; [exact (proj1 HE)|assumption].
      * apply arena_shift_open_name_qual; [exact (proj1 HE)|assumption].
      * apply arena_shift_open_name_qual; [exact (proj1 HE)|assumption].
  - destruct (arena_shift_ty_exists n T2) as (M & HM).
    pose proof (arena_shift_qual_spec n d2) as HQ.
    eapply s_trans.
    + exact (IHstp1 _ _ _ _ _ HE HA HM HF HQ).
    + exact (IHstp2 _ _ _ _ _ HE HM HB HQ HL).
Qed.

Local Lemma arena_stp_qualifiers Γ Σ T d U e :
  stp Γ Σ T d U e -> qstp Γ Σ d e.
Proof. intros H. induction H; eauto using qs_trans. Qed.

Local Lemma arena_stp_under_context Γ Σ T d U e :
  stp [] Σ T d U e -> stp Γ Σ T d U e.
Proof.
  intros H.
  destruct (safety_stp_closed _ _ _ _ _ _ H) as (HT & HU).
  eapply arena_shift_stp with (n := length Γ); [exact H| | | | |].
  - split; [simpl; lia|]. intros. discriminate.
  - eapply arena_shift_ty_rigid. exact HT.
  - eapply arena_shift_ty_rigid. exact HU.
  - eapply arena_shift_qual_rigid. exact (arena_qstp_input_closed _ _ _ _ (arena_stp_qualifiers _ _ _ _ _ _ H)).
  - eapply arena_shift_qual_rigid. exact (safety_qstp_closed _ _ _ _ (arena_stp_qualifiers _ _ _ _ _ _ H)).
Qed.

Inductive arena_binding_narrow (Σ : senv) :
  (binding * bool * ty * qual) -> (binding * bool * ty * qual) -> Prop :=
| arena_binding_keep : forall a, arena_binding_narrow Σ a a
| arena_binding_self : forall T U,
    arena_binding_narrow Σ (bind_tm,true,T,{♦}) (bind_tm,true,U,{♦})
| arena_binding_argument : forall k T U q p,
    stp [] Σ U p T q ->
    arena_binding_narrow Σ (k,false,T,q) (k,false,U,p).

Local Definition arena_env_narrow Σ (Γ Δ : tenv) : Prop :=
  length Δ = length Γ /\
  forall x a, indexr x Γ = Some a ->
    exists b, indexr x Δ = Some b /\ arena_binding_narrow Σ a b.

Local Lemma arena_narrow_cons Σ Γ Δ a b :
  arena_env_narrow Σ Γ Δ -> arena_binding_narrow Σ a b ->
  arena_env_narrow Σ (a::Γ) (b::Δ).
Proof.
  intros (Hlen & Hget) Hab.
  split; [simpl; lia|].
  intros x u Hu. simpl in Hu |- *. rewrite Hlen.
  destruct (x =? length Γ).
  - inversion Hu; subst. eauto.
  - exact (Hget x u Hu).
Qed.

Local Lemma arena_narrow_cons_keep Σ Γ Δ a :
  arena_env_narrow Σ Γ Δ -> arena_env_narrow Σ (a::Γ) (a::Δ).
Proof. intros. now apply arena_narrow_cons; [|constructor]. Qed.

Local Lemma arena_qual_nonfresh_down p q :
  p ⊑↑ q -> ♦∉ q -> ♦∉ p.
Proof.
  intros (HF & _) Hq Hp. apply Hq. exact (HF Hp).
Qed.

Local Lemma arena_narrow_qvar Σ Γ Δ k x b U q :
  arena_env_narrow Σ Γ Δ ->
  indexr x Γ = Some (k,b,U,q) ->
  closed_ty 0 x (length Σ) U -> closed_Qual 0 x (length Σ) q↑ -> ♦∉ q ->
  qstp Δ Σ $!x q.
Proof.
  intros (Hlen & Hlookup) Hx HU HQ Hnf.
  destruct (Hlookup _ _ Hx) as (a & Ha & Hn).
  inversion Hn; subst.
  - destruct k; [eapply qs_qvar|eapply qs_qvar_ty]; eassumption.
  - exfalso. exact (Hnf I).
  - match goal with HH : stp [] Σ _ _ U q |- _ =>
      pose proof (arena_stp_qualifiers _ _ _ _ _ _ HH) as Hstq;
      pose proof (proj1 (safety_stp_closed _ _ _ _ _ _ HH)) as HU';
      pose proof (arena_qstp_input_closed _ _ _ _ Hstq) as HQ';
      pose proof (safety_closed_qstp _ _ _ Hstq) as Hle
    end.
    eapply qs_trans; [|apply qs_sq; [exact Hle|]].
    + destruct k; [eapply qs_qvar; [exact Ha| | |]|eapply qs_qvar_ty; [exact Ha| | |]].
      all: try solve [eapply safety_ty_vars_weaken; [exact HU'|lia|simpl; lia]].
      all: try solve [eapply safety_fv_closed_weaken; [|exact HQ']; simpl; lia].
      all: eauto using arena_qual_nonfresh_down.
    + eapply safety_fv_closed_weaken; [|exact HQ].
      rewrite Hlen. eauto using safety_indexr_bound, Nat.lt_le_incl.
Qed.

Local Lemma arena_qstp_narrow Σ Γ Δ a b :
  arena_env_narrow Σ Γ Δ -> qstp Γ Σ a b -> qstp Δ Σ a b.
Proof.
  intros HE H. revert Δ HE. induction H; intros Δ HE.
  - apply qs_sq; [assumption|now rewrite (proj1 HE)].
  - destruct (proj2 HE _ _ H) as (v & Hv & Hn).
    inversion Hn; subst.
    + eapply qs_self; eassumption.
    + exfalso. exact (H1 I).
  - destruct (proj2 HE _ _ H) as (v & Hv & Hn).
    inversion Hn; subst.
    + eapply qs_self_all; eassumption.
    + exfalso. exact (H1 I).
  - eapply arena_narrow_qvar; eassumption.
  - eapply arena_narrow_qvar; eassumption.
  - eapply qs_cong; [eauto|now rewrite (proj1 HE)].
  - eauto using qs_trans.
Qed.

Local Lemma arena_stp_narrow Σ Γ Δ T a U b :
  arena_env_narrow Σ Γ Δ -> stp Γ Σ T a U b -> stp Δ Σ T a U b.
Proof.
  intros HE H. revert Δ HE. induction H; intros Δ HE.
  - apply s_top; [now rewrite (proj1 HE)|eauto using arena_qstp_narrow].
  - destruct (proj2 HE _ _ H) as (w & Hw & _).
    eapply s_tvar_refl; [exact Hw|eauto using arena_qstp_narrow].
  - destruct (proj2 HE _ _ H) as (w & Hw & Hn).
    inversion Hn; subst.
    + eapply s_tvar_trans; eauto.
    + match goal with HP : stp [] Σ _ _ T1 d0 |- _ =>
        pose proof (proj1 (safety_stp_closed _ _ _ _ _ _ HP)) as HU;
        pose proof (arena_stp_under_context Δ _ _ _ _ _ HP) as Hunder
      end.
      eapply s_tvar_trans; [exact Hw | exact HU |].
      pose proof (IHstp Δ HE) as Ht.
      eapply s_trans; [|exact Ht].
      eapply safety_stp_requalify; [exact Hunder|].
      apply qs_sq; [apply safety_subq_refl|].
      exact (arena_qstp_input_closed _ _ _ _ (arena_stp_qualifiers _ _ _ _ _ _ Ht)).
  - apply s_all; try (now rewrite (proj1 HE)); eauto using arena_qstp_narrow.
    pose proof (IHstp2 _ (arena_narrow_cons_keep _ _ _ _
      (arena_narrow_cons_keep _ _ _ _ HE))) as Hret.
    unfold open_ty', openq' in *. now rewrite (proj1 HE).
  - apply s_base. eauto using arena_qstp_narrow.
  - apply s_ref; eauto using arena_qstp_narrow.
  - apply s_fun; try (now rewrite (proj1 HE)); eauto using arena_qstp_narrow.
    pose proof (IHstp2 _ (arena_narrow_cons_keep _ _ _ _
      (arena_narrow_cons_keep _ _ _ _ HE))) as Hret.
    unfold open_ty', openq' in *. now rewrite (proj1 HE).
  - eauto using s_trans.
Qed.

Local Lemma arena_narrow_empty Σ : arena_env_narrow Σ [] [].
Proof. split; [reflexivity|discriminate]. Qed.

Local Lemma arena_covariance_trans Σ k T q U p A B S C R a b d :
  stp [] Σ U p T q ->
  stp [(k,false,T,q); (bind_tm,true,A,{♦})] Σ S a C b ->
  stp [(k,false,U,p); (bind_tm,true,B,{♦})] Σ C b R d ->
  stp [(k,false,U,p); (bind_tm,true,A,{♦})] Σ S a R d.
Proof.
  intros Hbound H1 H2. eapply s_trans with (T2 := C) (d2 := b).
  - eapply arena_stp_narrow; [|exact H1].
    apply arena_narrow_cons.
    + apply arena_narrow_cons_keep, arena_narrow_empty.
    + now apply arena_binding_argument.
  - eapply arena_stp_narrow; [|exact H2].
    apply arena_narrow_cons_keep, arena_narrow_cons;
      [apply arena_narrow_empty|apply arena_binding_self].
Qed.

Local Lemma arena_vtp_sub Σ ϰ φ v T d U e :
  stp [] Σ T d U e ->
  vtp Σ ϰ φ v T d -> wf_step v -> kill_sep ϰ e ->
  vtp Σ ϰ φ v U e.
Proof.
  intros H. remember ([] : tenv) as Γ eqn:HG.
  revert v. induction H; subst; intros w HT HW HS; try discriminate.
  - eapply vtp_top. exact (safety_vtp_requalify _ _ _ _ _ _ _ HT HW H0 HS).
  - inversion HT; subst.
    eapply vtp_tabs; try eassumption.
    + eapply s_trans; eassumption.
    + eapply qs_trans; eassumption.
    + eapply arena_covariance_trans; eassumption.
    + simpl in HW. now rewrite HW; apply safety_empty_sep.
  - exact (safety_vtp_requalify _ _ _ _ _ _ _ HT HW H HS).
  - inversion HT; subst.
    eapply vtp_loc with (T := T) (q1 := q0); try eassumption.
    + exact (safety_qstp_closed _ _ _ _ H).
    + exact (safety_qstp_closed _ _ _ _ H2).
    + eapply s_trans with (T2 := T1) (d2 := ∅); eassumption.
    + eapply s_trans with (T2 := T1) (d2 := ∅); eassumption.
    + eapply qs_trans with (d2 := d1); eassumption.
    + eapply qs_trans with (d2 := q1); eassumption.
    + eapply qs_trans with (d2 := q1); eassumption.
  - inversion HT; subst.
    eapply vtp_abs; try eassumption.
    + exact (safety_qstp_closed _ _ _ _ H1).
    + eapply s_trans; eassumption.
    + eapply qs_trans; eassumption.
    + eapply arena_covariance_trans; eassumption.
    + simpl in HW. now rewrite HW; apply safety_empty_sep.
  - eapply IHstp2; try assumption; try reflexivity.
    eapply IHstp1; try assumption; try reflexivity.
    eapply safety_sep_of_sub; [exact (safety_subqual_of_stp _ _ _ _ _ H0)|exact HS].
Qed.

(* Normalize subsumption on values into the subtyping premises of store typing. *)
Local Lemma arena_value_vtp Σ ϰ φ v T q :
  has_type [] φ Σ v T q -> value v -> wf_step v -> kill_sep ϰ q ->
  vtp Σ ϰ φ v T q.
Proof.
  intros HT. remember ([] : tenv) as Γ eqn:HG.
  induction HT; subst; intros HV HW HS; try solve [inversion HV].
  - assert (Hdf : closed_Qual 0 0 (length Σ) df↑).
    { eapply safety_qual_closed_of_sub; eassumption. }
    eapply vtp_tabs with (T1 := T1) (T2 := T2) (df1 := df) (d1 := d1) (d2 := d2);
      try eassumption.
    + inversion H0. apply safety_stp_refl; [assumption|apply qs_sq; auto using safety_subq_refl].
    + apply qs_sq; auto using safety_subq_refl.
    + inversion H0. apply safety_stp_refl.
      * apply safety_open_name_ty. assumption.
      * apply qs_sq; [apply safety_subq_refl|].
        apply safety_open_name_qual. assumption.
  - apply vtp_base; [apply safety_qual_const_closed|exact HS].
  - assert (Hdf : closed_Qual 0 0 (length Σ) df↑).
    { eapply safety_qual_closed_of_sub; eassumption. }
    eapply vtp_abs with (T1 := T1) (T2 := T2) (df1 := df) (d1 := d1) (d2 := d2);
      try eassumption.
    + inversion H0. apply safety_stp_refl; [assumption|apply qs_sq; auto using safety_subq_refl].
    + apply qs_sq; auto using safety_subq_refl.
    + inversion H0. apply safety_stp_refl.
      * apply safety_open_name_ty. assumption.
      * apply qs_sq; [apply safety_subq_refl|].
        apply safety_open_name_qual. assumption.
  - assert (Hl : closed_Qual 0 0 (length Σ) (&!l)↑).
    { eapply safety_qual_closed_of_sub; eassumption. }
    eapply vtp_loc with (T := T) (q1 := q); try eassumption.
    + eapply safety_subq_loc; [eassumption|apply Nat.eqb_refl].
    + apply safety_stp_refl; [assumption|apply qs_sq; [apply safety_subq_refl|apply safety_qual_const_closed]].
    + apply safety_stp_refl; [assumption|apply qs_sq; [apply safety_subq_refl|apply safety_qual_const_closed]].
    + apply qs_sq; auto using safety_subq_refl.
    + apply qs_sq; auto using safety_subq_refl.
    + apply qs_sq; auto using safety_subq_refl.
  - eapply arena_vtp_sub; [exact H| |exact HW|exact HS].
    apply IHHT; try assumption; try reflexivity.
    eapply safety_sep_of_sub; [exact (safety_subqual_of_stp _ _ _ _ _ H)|exact HS].
Qed.

Local Lemma arena_value_storage_proved : safety_value_storage.
Proof.
  intros Σ φ ϰ σ v T q HC HΣ HW HV HT Hnf.
  apply arena_value_vtp; try assumption.
  destruct HC as (_ & _ & _ & _ & HS & _).
  eapply safety_sep_of_sub; [|exact HS].
  apply safety_bound_without_fresh; [exact Hnf|].
  exact (safety_typing_qual_bound _ _ _ _ _ _ HT).
Qed.

Local Lemma arena_subq_free a b x : a ⊑↑ b -> qfvs a x = true -> qfvs b x = true.
Proof. intros (_ & H & _) HX. exact (H x HX). Qed.

Local Definition arena_saturated (Γ : tenv) (p : qual) : Prop :=
  forall x a, indexr x Γ = Some a -> qfvs p x = true -> snd a ⊑↑ p.

Local Lemma arena_index_cons {A} (Γ : list A) a x b :
  indexr x Γ = Some b -> indexr x (a::Γ) = Some b.
Proof.
  intro H. pose proof (safety_indexr_bound _ _ _ H) as Hlt. simpl.
  replace (x =? length Γ) with false by (symmetry; apply Nat.eqb_neq; lia).
  exact H.
Qed.

Local Lemma arena_qone_extensive (Γ : tenv) q : q ⊑↑ q_trans_one Γ q.
Proof.
  induction Γ as [|a Γ IH]; [apply safety_subq_refl|].
  change (q ⊑↑ if qfvs q (length Γ) then q_trans_one Γ q ⊔ snd a else q_trans_one Γ q).
  destruct (qfvs q (length Γ)); [eauto using safety_subq_trans, safety_join_l|exact IH].
Qed.

Local Lemma arena_qone_mono (Γ : tenv) a b :
  a ⊑↑ b -> q_trans_one Γ a ⊑↑ q_trans_one Γ b.
Proof.
  intro H. induction Γ as [|c Γ IH]; [exact H|].
  change ((if qfvs a (length Γ) then q_trans_one Γ a ⊔ snd c else q_trans_one Γ a)
    ⊑↑ (if qfvs b (length Γ) then q_trans_one Γ b ⊔ snd c else q_trans_one Γ b)).
  destruct (qfvs a (length Γ)) eqn:Ha, (qfvs b (length Γ)) eqn:Hb.
  - apply safety_join_bound; [eauto using safety_subq_trans, safety_join_l|apply safety_join_r].
  - pose proof (arena_subq_free _ _ _ H Ha). congruence.
  - eauto using safety_subq_trans, safety_join_l.
  - exact IH.
Qed.

Local Lemma arena_qone_saturated_bound Γ q p :
  q ⊑↑ p -> arena_saturated Γ p -> q_trans_one Γ q ⊑↑ p.
Proof.
  intros Hq. induction Γ as [|a Γ IH]; [auto|].
  intros Hsat.
  assert (HE : arena_saturated Γ p).
  { intros x b Hx HF. eapply Hsat; [eapply arena_index_cons; exact Hx|exact HF]. }
  change ((if qfvs q (length Γ) then q_trans_one Γ q ⊔ snd a else q_trans_one Γ q) ⊑↑ p).
  destruct (qfvs q (length Γ)) eqn:HQ; [|now apply IH].
  apply safety_join_bound; [now apply IH|].
  eapply Hsat.
  - simpl. now rewrite Nat.eqb_refl.
  - exact (arena_subq_free _ _ _ Hq HQ).
Qed.

Local Lemma arena_qtrans_extensive (Γ : tenv) q n :
  q ⊑↑ q_trans'' Γ q n.
Proof.
  revert q. induction n as [|n IH]; intros q; simpl; [apply safety_subq_refl|].
  eapply safety_subq_trans; [apply arena_qone_extensive|apply IH].
Qed.

Local Lemma arena_qtrans_saturated_bound (Γ : tenv) q p n :
  q ⊑↑ p -> arena_saturated Γ p -> q_trans'' Γ q n ⊑↑ p.
Proof.
  revert q. induction n as [|n IH]; intros q Hq HS; simpl; [assumption|].
  apply IH; [now apply arena_qone_saturated_bound|assumption].
Qed.

Local Lemma arena_qtrans_cons_super (Γ : tenv) a n p q :
  p ⊑↑ q -> q_trans'' Γ p n ⊑↑ q_trans'' (a::Γ) q n.
Proof.
  revert p q. induction n as [|n IH]; intros p q HP; simpl; [assumption|].
  apply IH. eapply safety_subq_trans; [exact (arena_qone_mono _ _ _ HP)|].
  change (q_trans_one Γ q ⊑↑
    if qfvs q (length Γ) then q_trans_one Γ q ⊔ snd a else q_trans_one Γ q).
  destruct (qfvs q (length Γ)); auto using safety_subq_refl, safety_join_l.
Qed.

(* Each context binding can mention only earlier bindings. Saturation uses
   this ordering to account for the locations reached through free variables. *)
Local Definition arena_ordered_quals (Γ : tenv) : Prop :=
  forall x a, indexr x Γ = Some a -> forall y, qfvs (snd a) y = true -> y < x.

Local Lemma arena_ordered_tail (Γ : tenv) a :
  arena_ordered_quals (a::Γ) -> arena_ordered_quals Γ.
Proof. intros H x b Hb. apply H. now apply arena_index_cons. Qed.

Local Lemma arena_qone_free_high (Γ : tenv) x q :
  (forall y a, indexr y Γ = Some a -> qfvs (snd a) x = false) ->
  qfvs (q_trans_one Γ q) x = qfvs q x.
Proof.
  induction Γ as [|a Γ IH]; intro H; [reflexivity|].
  assert (HA : qfvs (snd a) x = false).
  { eapply H. simpl. now rewrite Nat.eqb_refl. }
  specialize (IH (fun y b HB => H y b (arena_index_cons _ _ _ _ HB))).
  change (qfvs (if qfvs q (length Γ) then q_trans_one Γ q ⊔ snd a
    else q_trans_one Γ q) x = qfvs q x).
  destruct (qfvs q (length Γ)); [|exact IH].
  change (qfvs (q_trans_one Γ q) x || qfvs (snd a) x = qfvs q x).
  now rewrite IH, HA, orb_false_r.
Qed.

Local Lemma arena_qtrans_free_high (Γ : tenv) n x q :
  (forall y a, indexr y Γ = Some a -> qfvs (snd a) x = false) ->
  qfvs (q_trans'' Γ q n) x = qfvs q x.
Proof.
  revert q. induction n as [|n IH]; intros q H; simpl; [reflexivity|].
  now rewrite IH by exact H; apply arena_qone_free_high.
Qed.

Local Lemma arena_ordered_no_high (Γ : tenv) x :
  arena_ordered_quals Γ ->
  (forall y a, indexr y Γ = Some a -> y <= x) ->
  forall y a, indexr y Γ = Some a -> qfvs (snd a) x = false.
Proof.
  intros Hord Hle y a Hy. destruct (qfvs (snd a) x) eqn:H; [|reflexivity].
  specialize (Hord _ _ Hy _ H). specialize (Hle _ _ Hy). lia.
Qed.

Local Lemma arena_q_trans_saturates (Γ : tenv) q :
  arena_ordered_quals Γ -> arena_saturated Γ (q_trans_tenv Γ q).
Proof.
  revert q. induction Γ as [|a Γ IH]; intros q Hord; [intros x b H; discriminate|].
  unfold q_trans_tenv. cbn [length q_trans''].
  set (r := q_trans_one (a::Γ) q).
  set (z := q_trans'' Γ r (length Γ)).
  set (w := q_trans'' (a::Γ) r (length Γ)).
  assert (Hz : arena_saturated Γ z).
  { apply (IH r). eauto using arena_ordered_tail. }
  assert (Hzw : z ⊑↑ w) by (unfold z, w; apply arena_qtrans_cons_super, safety_subq_refl).
  assert (Hrz : r ⊑↑ z) by apply arena_qtrans_extensive.
  assert (Hqr : q ⊑↑ r) by apply arena_qone_extensive.
  assert (Hzs : arena_saturated (a::Γ) z).
  { intros x b HX HF. simpl in HX.
    destruct (x =? length Γ) eqn:HX'.
    - apply Nat.eqb_eq in HX'. subst x. inversion HX; subst b.
      assert (HFq : qfvs q (length Γ) = true).
      { unfold z, r in HF.
        rewrite (arena_qtrans_free_high Γ) in HF.
        - rewrite (arena_qone_free_high (a::Γ)) in HF.
          + exact HF.
          + apply arena_ordered_no_high; [exact Hord|].
            intros y c HY. pose proof (safety_indexr_bound _ _ _ HY). simpl in *. lia.
        - apply arena_ordered_no_high; [eauto using arena_ordered_tail|].
          intros y c HY. pose proof (safety_indexr_bound _ _ _ HY). lia. }
      eapply safety_subq_trans; [|exact Hrz].
      unfold r. change (snd a ⊑↑ if qfvs q (length Γ) then q_trans_one Γ q ⊔ snd a else q_trans_one Γ q).
      now rewrite HFq; apply safety_join_r.
    - exact (Hz _ _ HX HF). }
  assert (Hwz : w ⊑↑ z) by (unfold w; now apply arena_qtrans_saturated_bound).
  intros x b HX HF. eapply safety_subq_trans; [|exact Hzw].
  exact (Hzs x b HX (arena_subq_free _ _ _ Hwz HF)).
Qed.

Inductive arena_closed_env : tenv -> senv -> Prop :=
| arena_closed_env_nil : forall Σ, arena_closed_env [] Σ
| arena_closed_env_cons : forall Γ Σ k b T q,
    arena_closed_env Γ Σ ->
    closed_ty 0 (length Γ) (length Σ) T ->
    closed_Qual 0 (length Γ) (length Σ) q↑ ->
    arena_closed_env ((k,b,T,q)::Γ) Σ.

Local Lemma arena_ordered_arena_closed_env Γ Σ :
  arena_closed_env Γ Σ -> arena_ordered_quals Γ.
Proof.
  intro H. induction H; [intros x a Hnone; discriminate Hnone|].
  intros x a HI y HY. simpl in HI.
  destruct (x =? length Γ) eqn:HX.
  - apply Nat.eqb_eq in HX. subst x. inversion HI; subst a.
    destruct H1 as (HF & _ & _). now apply HF.
  - eauto.
Qed.

(* Remove free slot zero and add the replacement locations wherever that
   slot occurs. Bound-variable membership stays fixed. *)
Local Definition arena_qual_substitution (δ q r : qual) : Prop :=
  qfresh r = qfresh q /\
  (forall x, qfvs r x = qfvs q (S x)) /\
  (forall x, qbvs r x = qbvs q x) /\
  (forall l, qlocs r l = (qlocs q l || (qfvs q 0 && qlocs δ l))).

Local Definition arena_sub_qual (δ q : qual) : qual :=
  (qfresh q, fun x => qfvs q (S x), qbvs q,
    fun l => qlocs q l || (qfvs q 0 && qlocs δ l)).

Local Lemma arena_sub_qual_image δ q :
  arena_qual_substitution δ q (arena_sub_qual δ q).
Proof. repeat split; reflexivity. Qed.

Local Lemma arena_qsub_rigid δ q b L :
  closed_Qual b 0 L q↑ -> arena_qual_substitution δ q q.
Proof.
  intros (HF & _ & _).
  assert (H : forall x, qfvs q x = false).
  { intro x. destruct (qfvs q x) eqn:Hx; [specialize (HF x Hx); lia|reflexivity]. }
  repeat split; try reflexivity.
  - intros x. now rewrite (H x), (H (S x)).
  - intros x. now rewrite (H 0), orb_false_r.
Qed.

Local Lemma arena_qsub_empty δ : arena_qual_substitution δ ∅ ∅.
Proof. eapply arena_qsub_rigid; apply (safety_qual_const_closed 0 0 0 false). Qed.

Local Lemma arena_qsub_marker δ : arena_qual_substitution δ {♦} {♦}.
Proof. eapply arena_qsub_rigid; apply (safety_qual_const_closed 0 0 0 true). Qed.

Local Lemma arena_qsub_name δ x :
  arena_qual_substitution δ ($!(S x)) ($!x).
Proof. repeat split; reflexivity. Qed.

Local Lemma arena_qsub_zero δ L :
  closed_Qual 0 0 L δ↑ -> ♦∉ δ -> arena_qual_substitution δ ($!0) δ.
Proof.
  intros (HF & HB & _) Hnf. repeat split.
  - change (qfresh δ = false). destruct (qfresh δ) eqn:HD; [exfalso; apply Hnf|reflexivity].
    exact I.
  - intros x. change (qfvs δ x = false).
    destruct (qfvs δ x) eqn:HX; [specialize (HF x HX); lia|reflexivity].
  - intros x. change (qbvs δ x = false).
    destruct (qbvs δ x) eqn:HX; [specialize (HB x HX); lia|reflexivity].
Qed.

Local Lemma arena_qsub_nonfresh δ q r :
  arena_qual_substitution δ q r -> ♦∉ q -> ♦∉ r.
Proof.
  intros (HQ & _) H. change (~ Is_true (qfresh r)). now rewrite HQ.
Qed.

Local Lemma arena_qsub_hasfresh δ q r :
  arena_qual_substitution δ q r -> ♦∈ r -> ♦∈ q.
Proof.
  intros (HQ & _). change (Is_true (qfresh r) -> Is_true (qfresh q)). now rewrite HQ.
Qed.

Local Lemma arena_qsub_subset δ q q' r r' :
  arena_qual_substitution δ q q' -> arena_qual_substitution δ r r' ->
  q ⊑↑ r -> q' ⊑↑ r'.
Proof.
  intros (HQ & HQF & HQB & HQL) (HR & HRF & HRB & HRL) Hsub.
  apply safety_qual_le in Hsub as (HF & Hfv & Hbv & Hl).
  apply safety_qual_le. repeat split.
  - now rewrite HQ, HR.
  - intros x. rewrite HQF, HRF. apply Hfv.
  - intros x. rewrite HQB, HRB. apply Hbv.
  - intros l. rewrite HQL, HRL, !orb_true_iff, !andb_true_iff.
    specialize (Hl l). specialize (Hfv 0). tauto.
Qed.

Local Lemma arena_qsub_closed δ q q' b f L L' :
  arena_qual_substitution δ q q' ->
  closed_Qual b (S f) L q↑ -> closed_Qual 0 0 L' δ↑ -> L <= L' ->
  closed_Qual b f L' q'↑.
Proof.
  intros (_ & HF & HB & HL) (Hf & Hb & Hl) (_ & _ & Hδ) Hle.
  repeat split.
  - intros x Hx. change (qfvs q' x = true) in Hx. rewrite HF in Hx.
    specialize (Hf _ Hx). lia.
  - intros x Hx. change (qbvs q' x = true) in Hx. rewrite HB in Hx. now apply Hb.
  - intros l Hx. change (qlocs q' l = true) in Hx.
    rewrite HL, orb_true_iff, andb_true_iff in Hx.
    destruct Hx as [Hx | [_ Hx]].
    + specialize (Hl _ Hx). lia.
    + now apply Hδ.
Qed.

Local Lemma arena_qsub_join δ q q' r r' :
  arena_qual_substitution δ q q' -> arena_qual_substitution δ r r' ->
  arena_qual_substitution δ (q ⊔ r) (q' ⊔ r').
Proof.
  intros (HQ & HQF & HQB & HQL) (HR & HRF & HRB & HRL).
  unfold arena_qual_substitution. cbn [qor qfresh qfvs qbvs qlocs fst snd].
  repeat split.
  - now rewrite HQ, HR.
  - intro x. unfold n_or. now rewrite HQF, HRF.
  - intro x. unfold n_or. now rewrite HQB, HRB.
  - intro x. unfold n_or. rewrite HQL, HRL.
    destruct (qlocs δ x), (qlocs q x), (qlocs r x), (qfvs q 0), (qfvs r 0); reflexivity.
Qed.

Local Lemma arena_qsub_open δ k q q' a a' :
  arena_qual_substitution δ q q' -> arena_qual_substitution δ a a' ->
  arena_qual_substitution δ (open_qual k a q) (open_qual k a' q').
Proof.
  intros Hq Ha. pose proof Hq as (HqF & HQ & HB & HL).
  unfold open_qual. rewrite HB. destruct (qbvs q k); [|exact Hq].
  apply arena_qsub_join; [|exact Ha].
  repeat split; try assumption.
  intro x. change (n_diff (qbvs q') (n_one k) x = n_diff (qbvs q) (n_one k) x).
  unfold n_diff. now rewrite HB.
Qed.

Local Lemma arena_qsub_open_named δ (Γ Δ : tenv) q q' :
  length Γ = S (length Δ) -> arena_qual_substitution δ q q' ->
  arena_qual_substitution δ (q <~²ᵈ Γ) (q' <~²ᵈ Δ).
Proof.
  intros HL Hq. unfold openq', openq. rewrite HL.
  apply arena_qsub_open; [apply arena_qsub_open; [exact Hq|]|];
    apply arena_qsub_name.
Qed.

Inductive arena_ty_substitution (U : ty) (δ : qual) : ty -> ty -> Prop :=
| arena_sub_top : arena_ty_substitution U δ TTop TTop
| arena_sub_unit : arena_ty_substitution U δ TUnit TUnit
| arena_sub_zero : arena_ty_substitution U δ (TVar (varF 0)) U
| arena_sub_free : forall x,
    arena_ty_substitution U δ (TVar (varF (S x))) (TVar (varF x))
| arena_sub_bound : forall x,
    arena_ty_substitution U δ (TVar (varB x)) (TVar (varB x))
| arena_sub_ref : forall q q' A A',
    arena_qual_substitution δ q q' -> arena_ty_substitution U δ A A' ->
    arena_ty_substitution U δ (TRef q A) (TRef q' A')
| arena_sub_fun : forall q r q' r' A B A' B',
    arena_qual_substitution δ q q' -> arena_qual_substitution δ r r' ->
    arena_ty_substitution U δ A A' -> arena_ty_substitution U δ B B' ->
    arena_ty_substitution U δ (TFun q r A B) (TFun q' r' A' B')
| arena_sub_all : forall q r q' r' A B A' B',
    arena_qual_substitution δ q q' -> arena_qual_substitution δ r r' ->
    arena_ty_substitution U δ A A' -> arena_ty_substitution U δ B B' ->
    arena_ty_substitution U δ (TAll q r A B) (TAll q' r' A' B').

Local Lemma arena_tsub_rigid U δ b L T :
  closed_ty b 0 L T -> arena_ty_substitution U δ T T.
Proof.
  intro H. remember 0 as f eqn:HF.
  induction H; subst; try lia; constructor; eauto using arena_qsub_rigid.
Qed.

Local Lemma arena_tsub_exists U δ T : exists T', arena_ty_substitution U δ T T'.
Proof.
  induction T; try solve [eexists; constructor].
  - destruct v as [x|x].
    + destruct x; [exists U|exists (TVar (varF x))]; constructor.
    + exists (TVar (varB x)); constructor.
  - destruct IHT1 as [T1' HT], IHT2 as [T2' HB].
    exists (TAll (arena_sub_qual δ q) (arena_sub_qual δ q0) T1' T2').
    constructor; auto using arena_sub_qual_image.
  - destruct IHT1 as [T1' HT], IHT2 as [T2' HB].
    exists (TFun (arena_sub_qual δ q) (arena_sub_qual δ q0) T1' T2').
    constructor; auto using arena_sub_qual_image.
  - destruct IHT as [T' HT].
    exists (TRef (arena_sub_qual δ q) T'). constructor; auto using arena_sub_qual_image.
Qed.

Local Lemma arena_tsub_closed U δ T T' :
  arena_ty_substitution U δ T T' ->
  forall b f L L', L <= L' -> closed_ty 0 0 L' U ->
  closed_Qual 0 0 L' δ↑ -> closed_ty b (S f) L T ->
  closed_ty b f L' T'.
Proof.
  intros H. induction H; intros b f L L' Hle HU HQ HT; inversion HT; subst;
    try solve [constructor; eauto using arena_qsub_closed; lia].
  apply (safety_ty_vars_weaken _ _ _ _ _ _ HU); lia.
Qed.

Local Lemma arena_tsub_closed_rigid_loc U δ T T' :
  arena_ty_substitution U δ T T' ->
  forall b L, closed_ty b 0 L T -> closed_ty b 0 L T'.
Proof.
  intros H. induction H; intros b L HC; inversion HC; subst; try lia; constructor;
    eauto using arena_qsub_closed, Nat.le_refl.
  all: match goal with
    HR : arena_qual_substitution _ ?q ?r, HT : closed_Qual ?b 0 ?L ?q↑
      |- closed_Qual ?b 0 ?L ?r↑ =>
      destruct HR as (_ & HF & HB & HL);
      destruct HT as (Hf & Hb & Hl);
      assert (H0f : qfvs q 0 = false)
        by (destruct (qfvs q 0) eqn:He; [specialize (Hf 0 He); lia|reflexivity]);
      split; [intros x HX; change (qfvs r x = true) in HX; rewrite HF in HX; specialize (Hf _ HX); lia|];
      split; [intros x HX; change (qbvs r x = true) in HX; rewrite HB in HX; now apply Hb|];
      intros x HX; change (qlocs r x = true) in HX; rewrite HL, H0f, orb_false_r in HX;
      now apply Hl
  end.
Qed.

Local Lemma arena_tsub_open U δ L T T' A A' q q' k :
  closed_ty 0 0 L U ->
  arena_ty_substitution U δ T T' -> arena_ty_substitution U δ A A' ->
  arena_qual_substitution δ q q' ->
  arena_ty_substitution U δ (open_rec_ty k A q T) (open_rec_ty k A' q' T').
Proof.
  intros HU H HA HQ. revert k. induction H; intros k; simpl;
    try solve [constructor; eauto using arena_qsub_open].
  - rewrite (safety_ty_open_skip _ _ _ _ _ A' q' HU) by lia. constructor.
  - destruct (k =? x); [exact HA|constructor].
Qed.

Local Lemma arena_tsub_open_named U δ L (Γ Δ : tenv) T T' :
  closed_ty 0 0 L U -> length Γ = S (length Δ) ->
  arena_ty_substitution U δ T T' ->
  arena_ty_substitution U δ (T <~²ᵀ Γ) (T' <~²ᵀ Δ).
Proof.
  intros HU HL HT. unfold open_ty', open_ty. rewrite HL.
  eapply arena_tsub_open with (L := L); [exact HU| |constructor|apply arena_qsub_name].
  eapply arena_tsub_open with (L := L);
    [exact HU|exact HT|constructor|apply arena_qsub_name].
Qed.

Local Definition arena_env_substitution U δ a (Γ Δ : tenv) : Prop :=
  length Γ = S (length Δ) /\ indexr 0 Γ = Some a /\
  forall x k b T q, indexr (S x) Γ = Some (k,b,T,q) ->
    exists T' q', indexr x Δ = Some (k,b,T',q') /\
      arena_ty_substitution U δ T T' /\ arena_qual_substitution δ q q'.

Local Lemma arena_env_sub_base U δ a : arena_env_substitution U δ a [a] [].
Proof. split; [reflexivity|split; [reflexivity|intros; discriminate]]. Qed.

Local Lemma arena_env_sub_cons U δ a Γ Δ k b T T' q q' :
  arena_env_substitution U δ a Γ Δ ->
  arena_ty_substitution U δ T T' -> arena_qual_substitution δ q q' ->
  arena_env_substitution U δ a ((k,b,T,q)::Γ) ((k,b,T',q')::Δ).
Proof.
  intros (HL & Hbase & Henv) HT HQ.
  refine (conj _ (conj (arena_index_cons _ _ _ _ Hbase) _)).
  - simpl; lia.
  - intros x k0 b0 V p HI.
    change ((if S x =? length Γ then Some (k,b,T,q) else indexr (S x) Γ) = Some (k0,b0,V,p)) in HI.
    rewrite HL in HI.
    change ((if x =? length Δ then Some (k,b,T,q) else indexr (S x) Γ) = Some (k0,b0,V,p)) in HI.
    simpl. destruct (x =? length Δ).
    + inversion HI; subst. exists T', q'. auto.
    + exact (Henv _ _ _ _ _ HI).
Qed.

Local Definition arena_substitution_binding (Σ : senv) (U : ty) (δ : qual)
  (a : binding * bool * ty * qual) : Prop :=
  let '(k,b,T,q) := a in
    (♦∉ q -> δ ⊑↑ q) /\
    (b = true -> ♦∉ q -> q ⊑↑ δ) /\
    (k = bind_ty -> b = false -> stp [] Σ U ∅ T ∅).

Local Lemma arena_qstp_representatives Γ Σ a b c d :
  a ⊑↑ b -> qstp Γ Σ b c -> c ⊑↑ d -> d ⊑↑ c -> qstp Γ Σ a d.
Proof.
  intros Hab H Hcd Hdc. eapply qs_trans.
  - apply qs_sq; [exact Hab|exact (arena_qstp_input_closed _ _ _ _ H)].
  - eapply qs_trans; [exact H|].
    apply qs_sq; [exact Hcd|].
    eapply safety_qual_closed_of_sub; [exact Hdc|exact (safety_qstp_closed _ _ _ _ H)].
Qed.

Local Lemma arena_sub_qstp_endpoints δ Γ Σ a b a' b' c d :
  arena_qual_substitution δ a a' -> arena_qual_substitution δ b b' ->
  arena_qual_substitution δ a c -> arena_qual_substitution δ b d ->
  qstp Γ Σ c d -> qstp Γ Σ a' b'.
Proof.
  intros HA HB HC HD H.
  eapply arena_qstp_representatives; [|exact H| |].
  - eapply arena_qsub_subset; [exact HA|exact HC|apply safety_subq_refl].
  - eapply arena_qsub_subset; [exact HD|exact HB|apply safety_subq_refl].
  - eapply arena_qsub_subset; [exact HB|exact HD|apply safety_subq_refl].
Qed.

Local Lemma arena_qsub_in_env U δ a Γ Δ (Σ : senv) p p' :
  arena_env_substitution U δ a Γ Δ ->
  arena_qual_substitution δ p p' ->
  closed_Qual 0 (length Γ) (length Σ) p↑ ->
  closed_Qual 0 0 (length Σ) δ↑ -> closed_Qual 0 (length Δ) (length Σ) p'↑.
Proof.
  intros HE Hq Hp Hδ.
  rewrite (proj1 HE) in Hp.
  eapply arena_qsub_closed; eauto using Nat.le_refl.
Qed.

Local Lemma arena_tsub_in_env U δ a Γ Δ (Σ : senv) T T' :
  arena_env_substitution U δ a Γ Δ ->
  arena_ty_substitution U δ T T' ->
  closed_ty 0 (length Γ) (length Σ) T ->
  closed_ty 0 0 (length Σ) U ->
  closed_Qual 0 0 (length Σ) δ↑ ->
  closed_ty 0 (length Δ) (length Σ) T'.
Proof.
  intros HE Hq Hp HU Hδ. rewrite (proj1 HE) in Hp.
  eapply arena_tsub_closed; eauto using Nat.le_refl.
Qed.

Local Lemma arena_qsub_self_zero U δ a Γ Δ Σ T d p' q' :
  arena_env_substitution U δ a Γ Δ ->
  arena_substitution_binding Σ U δ a ->
  closed_Qual 0 0 (length Σ) δ↑ -> ♦∉ δ ->
  indexr 0 Γ = Some (bind_tm,true,T,d) ->
  closed_Qual 0 0 (length Σ) d↑ -> ♦∉ d ->
  arena_qual_substitution δ (d ⊔ $!0) p' ->
  arena_qual_substitution δ ($!0) q' ->
  qstp Δ Σ p' q'.
Proof.
  intros (_ & Hbase & _) Hok Hδ Hnf Hget Hd Hnd HA HB.
  rewrite Hget in Hbase. inversion Hbase; subst a.
  destruct Hok as (_ & Hst & _).
  pose proof (arena_qsub_rigid δ d 0 _ Hd) as HD.
  pose proof (arena_qsub_zero _ _ Hδ Hnf) as HZ.
  eapply arena_sub_qstp_endpoints with (δ := δ)
    (a := d ⊔ $!0) (b := $!0) (c := d ⊔ δ) (d := δ);
    eauto using arena_qsub_join.
  apply qs_sq.
  - apply safety_join_bound; [apply Hst; auto|apply safety_subq_refl].
  - eapply safety_fv_closed_weaken; [|exact Hδ]. lia.
Qed.

Local Lemma arena_qsub_qvar U δ a Γ Δ Σ x k b T q p' q' :
  arena_env_substitution U δ a Γ Δ ->
  arena_substitution_binding Σ U δ a ->
  closed_ty 0 0 (length Σ) U ->
  closed_Qual 0 0 (length Σ) δ↑ -> ♦∉ δ ->
  indexr x Γ = Some (k,b,T,q) ->
  closed_ty 0 x (length Σ) T ->
  closed_Qual 0 x (length Σ) q↑ -> ♦∉ q ->
  arena_qual_substitution δ ($!x) p' -> arena_qual_substitution δ q q' ->
  qstp Δ Σ p' q'.
Proof.
  intros (HL & Hbase & Henv) Hok HU Hδ Hnf Hget HT HQ Hnq HA HB.
  destruct x as [|x].
  - rewrite Hget in Hbase. inversion Hbase; subst a.
    destruct Hok as (Hle & _ & _).
    eapply arena_sub_qstp_endpoints with (δ := δ) (a := $!0) (b := q) (c := δ) (d := q);
      eauto using arena_qsub_zero, arena_qsub_rigid.
    apply qs_sq; [auto|].
    eapply safety_fv_closed_weaken; [|exact HQ]. lia.
  - destruct (Henv _ _ _ _ _ Hget) as (T' & r & HI & HT' & HQ').
    eapply arena_sub_qstp_endpoints with (δ := δ) (a := $!(S x)) (b := q) (c := $!x) (d := r);
      eauto using arena_qsub_name.
    assert (HC : closed_ty 0 x (length Σ) T').
    { eapply arena_tsub_closed; eauto using Nat.le_refl. }
    assert (HCr : closed_Qual 0 x (length Σ) r↑).
    { eapply arena_qsub_closed; eauto using Nat.le_refl. }
    destruct k; [eapply qs_qvar|eapply qs_qvar_ty]; eauto using arena_qsub_nonfresh.
Qed.

Local Lemma arena_qstp_substitute U δ a Γ Δ Σ p q p' q' :
  qstp Γ Σ p q -> arena_env_substitution U δ a Γ Δ ->
  arena_substitution_binding Σ U δ a ->
  closed_ty 0 0 (length Σ) U -> closed_Qual 0 0 (length Σ) δ↑ -> ♦∉ δ ->
  arena_qual_substitution δ p p' -> arena_qual_substitution δ q q' ->
  qstp Δ Σ p' q'.
Proof.
  intros H. revert Δ p' q'. induction H; intros Δ p' q' HE Hok HU Hδ Hnf HA HB.
  - apply qs_sq.
    + eapply arena_qsub_subset; eassumption.
    + eapply arena_qsub_in_env; eassumption.
  - destruct f as [|x].
    + eapply arena_qsub_self_zero; eassumption.
    + destruct HE as (HL & HBase & Henv).
      destruct (Henv _ _ _ _ _ H) as (T & d & Hget & HT & HD).
      inversion HT; subst.
      eapply arena_sub_qstp_endpoints with (δ := δ) (a := df ⊔ $!(S x))
        (b := $!(S x)) (c := d ⊔ $!x) (d := $!x);
        eauto using arena_qsub_join, arena_qsub_name.
      eapply qs_self; [exact Hget| |eauto using arena_qsub_nonfresh].
      eapply arena_qsub_closed; eauto using Nat.le_refl.
  - destruct f as [|x].
    + eapply arena_qsub_self_zero; eassumption.
    + destruct HE as (HL & HBase & Henv).
      destruct (Henv _ _ _ _ _ H) as (T & d & Hget & HT & HD).
      inversion HT; subst.
      eapply arena_sub_qstp_endpoints with (δ := δ) (a := df ⊔ $!(S x))
        (b := $!(S x)) (c := d ⊔ $!x) (d := $!x);
        eauto using arena_qsub_join, arena_qsub_name.
      eapply qs_self_all; [exact Hget| |eauto using arena_qsub_nonfresh].
      eapply arena_qsub_closed; eauto using Nat.le_refl.
  - eapply arena_qsub_qvar; eassumption.
  - eapply arena_qsub_qvar; eassumption.
  - pose proof (arena_sub_qual_image δ q) as HQ.
    pose proof (arena_sub_qual_image δ d1) as HD1.
    pose proof (arena_sub_qual_image δ d2) as HD2.
    eapply arena_sub_qstp_endpoints with (δ := δ) (a := q ⊔ d1) (b := q ⊔ d2);
      [exact HA|exact HB| | |].
    + exact (arena_qsub_join _ _ _ _ _ HQ HD1).
    + exact (arena_qsub_join _ _ _ _ _ HQ HD2).
    + apply qs_cong.
      * eapply IHqstp; eassumption.
      * eapply arena_qsub_in_env; eassumption.
  - eapply qs_trans.
    + exact (IHqstp1 _ _ _ HE Hok HU Hδ Hnf HA (arena_sub_qual_image δ d2)).
    + exact (IHqstp2 _ _ _ HE Hok HU Hδ Hnf (arena_sub_qual_image δ d2) HB).
Qed.

Local Lemma arena_stp_substitute U δ a Γ Δ Σ T p V q T' p' V' q' :
  stp Γ Σ T p V q -> arena_env_substitution U δ a Γ Δ ->
  arena_substitution_binding Σ U δ a ->
  closed_ty 0 0 (length Σ) U -> closed_Qual 0 0 (length Σ) δ↑ -> ♦∉ δ ->
  arena_ty_substitution U δ T T' -> arena_ty_substitution U δ V V' ->
  arena_qual_substitution δ p p' -> arena_qual_substitution δ q q' ->
  stp Δ Σ T' p' V' q'.
Proof.
  intros H. revert Δ T' p' V' q'.
  induction H; intros Δ A p' B q' HE Hok HU Hδ Hnf HA HB HF HL.
  - inversion HB; subst. apply s_top.
    + eapply arena_tsub_in_env; eassumption.
    + eapply arena_qstp_substitute; eassumption.
  - destruct x as [|x]; inversion HA; inversion HB; subst.
    + apply safety_stp_refl.
      * eapply safety_ty_vars_weaken; [exact HU|lia|lia].
      * eapply arena_qstp_substitute; eassumption.
    + destruct v as [ [ [k b] V] q].
      destruct (proj2 (proj2 HE) _ _ _ _ _ H) as (V' & r & HI & _ & _).
      eapply s_tvar_refl; [exact HI|].
      eapply arena_qstp_substitute; eassumption.
  - destruct x as [|x]; inversion HA; subst.
    + pose proof (proj1 (proj2 HE)) as HC.
      rewrite H in HC. inversion HC; subst a.
      pose proof Hok as Hok'. destruct Hok as (_ & _ & Hbound).
      assert (Hs : stp Δ Σ T1 p' B q').
      { eapply IHstp; try eassumption. eapply arena_tsub_rigid. exact H0. }
      eapply s_trans; [|exact Hs].
      eapply safety_stp_requalify.
      * apply arena_stp_under_context. auto.
      * apply qs_sq; [apply safety_subq_refl|].
        exact (arena_qstp_input_closed _ _ _ _ (arena_stp_qualifiers _ _ _ _ _ _ Hs)).
    + destruct (proj2 (proj2 HE) _ _ _ _ _ H) as (V' & r & HI & HV' & Hr).
      eapply s_tvar_trans; [exact HI| |].
      * eapply arena_tsub_closed_rigid_loc; eassumption.
      * eapply IHstp; eassumption.
  - pose proof HA as HSA. pose proof HB as HSB.
    inversion HA; inversion HB; subst. apply s_all.
    + eapply arena_tsub_in_env; eassumption.
    + eapply arena_tsub_in_env; eassumption.
    + eapply arena_qstp_substitute; eassumption.
    + eapply IHstp1; eassumption.
    + eapply IHstp2.
      * apply arena_env_sub_cons; try eassumption.
        apply arena_env_sub_cons; eauto using arena_qsub_marker.
      * exact Hok.
      * exact HU.
      * exact Hδ.
      * exact Hnf.
      * eapply arena_tsub_open_named; [exact HU|exact (proj1 HE)|assumption].
      * eapply arena_tsub_open_named; [exact HU|exact (proj1 HE)|assumption].
      * apply arena_qsub_open_named; [exact (proj1 HE)|assumption].
      * apply arena_qsub_open_named; [exact (proj1 HE)|assumption].
  - inversion HA; inversion HB; subst. apply s_base.
    eapply arena_qstp_substitute; eassumption.
  - inversion HA; inversion HB; subst. apply s_ref.
    + exact (arena_qstp_substitute _ _ _ _ _ _ _ _ _ _ H HE Hok HU Hδ Hnf HF HL).
    + eapply IHstp1; eauto using arena_qsub_empty.
    + eapply IHstp2; eauto using arena_qsub_empty.
    + eapply (arena_qstp_substitute U δ a Γ Δ Σ q1 q2); eassumption.
    + eapply (arena_qstp_substitute U δ a Γ Δ Σ q2 q1); eassumption.
  - pose proof HA as HSA. pose proof HB as HSB.
    inversion HA; inversion HB; subst. apply s_fun.
    + eapply arena_tsub_in_env; eassumption.
    + eapply arena_tsub_in_env; eassumption.
    + eapply arena_qstp_substitute; eassumption.
    + eapply IHstp1; eassumption.
    + eapply IHstp2.
      * apply arena_env_sub_cons; try eassumption.
        apply arena_env_sub_cons; eauto using arena_qsub_marker.
      * exact Hok.
      * exact HU.
      * exact Hδ.
      * exact Hnf.
      * eapply arena_tsub_open_named; [exact HU|exact (proj1 HE)|assumption].
      * eapply arena_tsub_open_named; [exact HU|exact (proj1 HE)|assumption].
      * apply arena_qsub_open_named; [exact (proj1 HE)|assumption].
      * apply arena_qsub_open_named; [exact (proj1 HE)|assumption].
  - destruct (arena_tsub_exists U δ T2) as (M & HM).
    pose proof (arena_sub_qual_image δ d2) as HQ.
    eapply s_trans.
    + exact (IHstp1 _ _ _ _ _ HE Hok HU Hδ Hnf HA HM HF HQ).
    + exact (IHstp2 _ _ _ _ _ HE Hok HU Hδ Hnf HM HB HQ HL).
Qed.

(* Locations introduced beyond the declared qualifier must be absent from
   the ambient scope and from the qualifiers of the old context. *)
Local Definition arena_sub_guard (δ : qual) (a : binding * bool * ty * qual) (Γ : tenv) (φ : qual) :=
  forall l, qlocs δ l = true -> qlocs (snd a) l = false ->
    qlocs φ l = false /\
    forall x b, indexr x Γ = Some b -> qlocs (snd b) l = false.

Local Lemma arena_qual_loc_false_sub q p l :
  q ⊑↑ p ⊔ {♦} -> qlocs p l = false -> qlocs q l = false.
Proof.
  intros (_ & _ & _ & Hloc) Hp.
  destruct (qlocs q l) eqn:HQ; [|reflexivity].
  specialize (Hloc l HQ). change (qlocs p l || false = true) in Hloc.
  rewrite Hp in Hloc. discriminate.
Qed.

Local Lemma arena_sub_guard_scope δ a Γ φ ψ :
  arena_sub_guard δ a Γ φ -> ψ ⊑↑ φ ⊔ {♦} ->
  arena_sub_guard δ a Γ ψ.
Proof.
  intros HS HQ l Hl Hl'.
  destruct (HS l Hl Hl') as (HF & HD).
  split; [eauto using arena_qual_loc_false_sub|exact HD].
Qed.

Local Lemma arena_sub_guard_cons δ a Γ φ e :
  arena_sub_guard δ a Γ φ -> snd e ⊑↑ φ ⊔ {♦} ->
  arena_sub_guard δ a (e::Γ) φ.
Proof.
  intros HS HQ l Hl Hl'.
  destruct (HS l Hl Hl') as (HF & HD).
  split; [exact HF|].
  intros x b Hx. simpl in Hx. destruct (x =? length Γ).
  - inversion Hx; subst. eauto using arena_qual_loc_false_sub.
  - exact (HD _ _ Hx).
Qed.

Local Lemma arena_qone_loc_absent (Γ : tenv) q l :
  qlocs q l = false ->
  (forall x b, indexr x Γ = Some b -> qlocs (snd b) l = false) ->
  qlocs (q_trans_one Γ q) l = false.
Proof.
  intro HQ. induction Γ as [|a Γ IH]; intros HE; [exact HQ|].
  specialize (IH (fun x b Hx => HE x b (arena_index_cons _ _ _ _ Hx))).
  assert (HA : qlocs (snd a) l = false)
    by (eapply HE; simpl; now rewrite Nat.eqb_refl).
  change (qlocs (if qfvs q (length Γ) then q_trans_one Γ q ⊔ snd a
                 else q_trans_one Γ q) l = false).
  destruct (qfvs q (length Γ)); [|exact IH].
  change (qlocs (q_trans_one Γ q) l || qlocs (snd a) l = false).
  now rewrite IH, HA.
Qed.

Local Lemma arena_qtrans_loc_absent (Γ : tenv) n q l :
  qlocs q l = false ->
  (forall x b, indexr x Γ = Some b -> qlocs (snd b) l = false) ->
  qlocs (q_trans'' Γ q n) l = false.
Proof.
  revert q. induction n; intros q Hq HE; [exact Hq|].
  simpl. apply IHn; auto using arena_qone_loc_absent.
Qed.

Local Lemma arena_qsub_reaches U δ a Γ Δ q q' p :
  arena_env_substitution U δ a Γ Δ -> arena_ordered_quals Γ ->
  arena_qual_substitution δ q q' -> arena_qual_substitution δ (q_trans_tenv Γ q) p ->
  q_trans_tenv Δ q' ⊑↑ p.
Proof.
  intros (HL & HBase & Henv) Hord HQ HP.
  pose proof (arena_q_trans_saturates Γ q Hord) as Hsat.
  unfold q_trans_tenv at 1. apply arena_qtrans_saturated_bound.
  - eapply arena_qsub_subset; [exact HQ|exact HP|apply arena_qtrans_extensive].
  - intros x e HE HF.
    destruct e as [ [ [k b] T] r].
    destruct (safety_indexr_exists Γ (S x)) as [orig HI].
    { pose proof (safety_indexr_bound _ _ _ HE). lia. }
    destruct orig as [ [ [k0 b0] T0] r0].
    destruct (Henv _ _ _ _ _ HI) as (TX & rx & HE' & _ & HR).
    rewrite HE in HE'. inversion HE'; subst rx.
    eapply arena_qsub_subset; [exact HR|exact HP|].
    apply (Hsat _ _ HI).
    destruct HP as (_ & HP & _).
    now rewrite HP in HF.
Qed.

Local Lemma arena_qsub_overlap_bound U δ a Γ Δ φ q q' r r' p :
  arena_env_substitution U δ a Γ Δ -> arena_ordered_quals Γ ->
  arena_sub_guard δ a Γ φ ->
  q ⊑↑ φ ⊔ {♦} -> r ⊑↑ φ ⊔ {♦} ->
  arena_qual_substitution δ q q' -> arena_qual_substitution δ r r' ->
  arena_qual_substitution δ (q_trans_tenv Γ q ⋒ q_trans_tenv Γ r) p ->
  (q_trans_tenv Δ q' ⋒ q_trans_tenv Δ r') ⊑↑ p.
Proof.
  intros HE HO HG HQ HR HQ' HR' HP.
  set (Q := q_trans_tenv Γ q).
  set (R := q_trans_tenv Γ r).
  pose proof (arena_qsub_reaches _ _ _ _ _ _ _ _ HE HO HQ' (arena_sub_qual_image δ Q)) as Hq.
  pose proof (arena_qsub_reaches _ _ _ _ _ _ _ _ HE HO HR' (arena_sub_qual_image δ R)) as Hr.
  assert (Hcap : (q_trans_tenv Δ q' ⋒ q_trans_tenv Δ r') ⊑↑
     (arena_sub_qual δ Q ⋒ arena_sub_qual δ R)).
  { clear - Hq Hr. unfold qqplus. safety_qpoint. }
  eapply safety_subq_trans; [exact Hcap|].
  destruct HP as (HF & Hfv & Hbv & Hl).
  apply safety_qual_le.
  refine (conj _ (conj _ (conj _ _))).
  - intros _. rewrite HF. change ((qfresh Q && qfresh R) || true = true). apply orb_true_r.
  - intros x. rewrite Hfv.
    change ((qfvs Q (S x) && qfvs R (S x)) || false = true ->
      (qfvs Q (S x) && qfvs R (S x)) || false = true). auto.
  - intros x. rewrite Hbv.
    change ((qbvs Q x && qbvs R x) || false = true ->
      (qbvs Q x && qbvs R x) || false = true). auto.
  - intros l. rewrite Hl.
    change (((qlocs Q l || qfvs Q 0 && qlocs δ l) &&
       (qlocs R l || qfvs R 0 && qlocs δ l)) || false = true ->
      ((qlocs Q l && qlocs R l) || false) ||
      (((qfvs Q 0 && qfvs R 0) || false) && qlocs δ l) = true).
    rewrite !orb_false_r.
    assert (HnoneQ : qlocs δ l = true -> qlocs (snd a) l = false -> qlocs Q l = false).
    { intros Hδ Hdecl. destruct (HG l Hδ Hdecl) as (HFφ & Henv).
      unfold Q, q_trans_tenv. apply arena_qtrans_loc_absent; [|exact Henv].
      exact (arena_qual_loc_false_sub _ _ _ HQ HFφ). }
    assert (HnoneR : qlocs δ l = true -> qlocs (snd a) l = false -> qlocs R l = false).
    { intros Hδ Hdecl. destruct (HG l Hδ Hdecl) as (HFφ & Henv).
      unfold R, q_trans_tenv. apply arena_qtrans_loc_absent; [|exact Henv].
      exact (arena_qual_loc_false_sub _ _ _ HR HFφ). }
    assert (HincQ : qfvs Q 0 = true -> qlocs (snd a) l = true -> qlocs Q l = true).
    { intros Hf Hdecl.
      pose proof (arena_q_trans_saturates Γ q HO _ _ (proj1 (proj2 HE)) Hf) as Hle.
      exact (safety_subq_loc _ _ _ Hle Hdecl). }
    assert (HincR : qfvs R 0 = true -> qlocs (snd a) l = true -> qlocs R l = true).
    { intros Hf Hdecl.
      pose proof (arena_q_trans_saturates Γ r HO _ _ (proj1 (proj2 HE)) Hf) as Hle.
      exact (safety_subq_loc _ _ _ Hle Hdecl). }
    destruct (qlocs δ l), (qlocs (snd a) l), (qfvs Q 0), (qfvs R 0), (qlocs Q l), (qlocs R l);
      cbn in *; try (intro H; discriminate H); try reflexivity;
      try discriminate (HnoneQ eq_refl eq_refl); try discriminate (HnoneR eq_refl eq_refl);
      try discriminate (HincQ eq_refl eq_refl); try discriminate (HincR eq_refl eq_refl).
Qed.

Local Lemma arena_qsub_diff_empty δ q r :
  arena_qual_substitution δ q r ->
  arena_qual_substitution δ (qdiff q ∅) (qdiff r ∅).
Proof.
  intros (HQ & HF & HB & HL).
  unfold arena_qual_substitution.
  cbn [qdiff q_empty qfresh qfvs qbvs qlocs fst snd negb].
  unfold n_diff, n_empty. cbn [negb].
  refine (conj _ (conj _ (conj _ _)));
    try intro x; now rewrite !andb_true_r.
Qed.

Local Lemma arena_qsub_preserves_not_free δ k q q' :
  arena_qual_substitution δ q q' ->
  open_qual k ∅ q = q -> open_qual k ∅ q' = q'.
Proof.
  intros (_ & _ & HB & _) HH.
  unfold open_qual. rewrite HB, (safety_q_not_free _ _ HH). reflexivity.
Qed.

Local Lemma arena_tsub_preserves_not_free U δ L T T' k :
  closed_ty 0 0 L U -> arena_ty_substitution U δ T T' ->
  not_free k T -> not_free k T'.
Proof.
  intros HU H. unfold not_free. revert k. induction H; intros k HK; simpl in *;
    try reflexivity.
  - apply (safety_ty_open_skip _ _ _ _ _ _ _ HU). lia.
  - now destruct (k =? x).
  - injection HK as HQ HA. f_equal; eauto using arena_qsub_preserves_not_free.
  - injection HK as HQ HR HA HB. f_equal; eauto using arena_qsub_preserves_not_free.
  - injection HK as HQ HR HA HB. f_equal; eauto using arena_qsub_preserves_not_free.
Qed.

Local Lemma arena_tm_vars_weaken t b f L :
  closed_tm b f L t ->
  forall b' f' L', b <= b' -> f <= f' -> L <= L' -> closed_tm b' f' L' t.
Proof.
  intro H. induction H; intros b' f' L' HB HF HL; constructor; try lia;
    eauto; try (eapply IHclosed_tm; lia);
    try (eapply IHclosed_tm1; lia); try (eapply IHclosed_tm2; lia).
Qed.

Local Lemma arena_sub_tm_closed t u b f L L' :
  closed_tm b (S f) L t -> closed_tm 0 0 L' u -> L <= L' ->
  closed_tm b f L' (subst_tm t 0 u).
Proof.
  intros H Hu HL. remember (S f) as F eqn:HF.
  revert f HF. induction H; intros f0 HF; subst; simpl;
    try solve [constructor; eauto; lia].
  destruct x as [|x].
  - simpl. eapply arena_tm_vars_weaken; [exact Hu|lia|lia|lia].
  - constructor; lia.
Qed.

Local Lemma arena_open_tm_skip t b f L k u :
  closed_tm b f L t -> b <= k -> open_rec_tm k u t = t.
Proof.
  intros HT. revert k. induction HT; intros k HK; simpl; try reflexivity;
    try solve [f_equal; eauto; try (apply IHHT; lia);
      try (apply IHHT1; lia); try (apply IHHT2; lia)].
  destruct (k =? x) eqn:HE; [apply Nat.eqb_eq in HE; lia|reflexivity].
Qed.

Local Lemma arena_sub_tm_open u L t v k :
  closed_tm 0 0 L u ->
  subst_tm (open_rec_tm k v t) 0 u =
    open_rec_tm k (subst_tm v 0 u) (subst_tm t 0 u).
Proof.
  intros HU. revert k. induction t; intros k; simpl; try rewrite ?IHt, ?IHt1, ?IHt2;
    try reflexivity.
  destruct v0 as [x|x].
  - destruct x; simpl; [|reflexivity].
    symmetry. apply (arena_open_tm_skip _ _ _ _ _ _ HU). lia.
  - simpl. destruct (k =? x); reflexivity.
Qed.

Local Lemma arena_sub_tm_open_named u L (Γ Δ : tenv) t :
  closed_tm 0 0 L u -> length Γ = S (length Δ) ->
  subst_tm (t <~²ᵗ Γ) 0 u = (subst_tm t 0 u) <~²ᵗ Δ.
Proof.
  intros HU HL. unfold open_tm'. rewrite !arena_sub_tm_open with (L := L) by exact HU.
  rewrite HL. reflexivity.
Qed.

Local Lemma arena_sub_tm_locs u t :
  local_locs u = ∅ ->
  local_locs (subst_tm t 0 u) = local_locs t.
Proof.
  intro Hu. induction t; simpl; try rewrite ?IHt, ?IHt1, ?IHt2; try reflexivity.
  destruct v; simpl; [destruct i; simpl; auto|reflexivity].
Qed.

Local Lemma arena_empty_join_parts t u :
  (local_locs t ⊔ local_locs u) = ∅ ->
  local_locs t = ∅ /\ local_locs u = ∅.
Proof.
  intros H. split; apply safety_no_scopes;
    intros l Hl; assert (HX : l ∈ₗ local_locs t ⊔ local_locs u)
    by (apply orb_true_iff; auto);
    rewrite H in HX; discriminate.
Qed.

Local Lemma arena_open_named_locs Γ t :
  local_locs (t <~²ᵗ (Γ : tenv)) = local_locs t.
Proof. unfold open_tm'. rewrite !safety_open_scopes by reflexivity. reflexivity. Qed.

Local Lemma arena_empty_twithc l t :
  local_locs (twithc l t) <> ∅.
Proof.
  intro H. assert (Hloc : l ∈ₗ local_locs (twithc l t)).
  { change ((l =? l) || qlocs (local_locs t) l = true).
    now rewrite Nat.eqb_refl. }
  rewrite H in Hloc. discriminate Hloc.
Qed.

Local Definition arena_sub_guard_local (φ ψ : qual) : Prop :=
  forall l, qlocs φ l = false -> qlocs ψ l = false.

Local Lemma arena_sub_guard_locs δ a Γ φ ψ :
  arena_sub_guard δ a Γ φ -> arena_sub_guard_local φ ψ ->
  arena_sub_guard δ a Γ ψ.
Proof.
  intros H HS l Hl Ha. destruct (H l Hl Ha) as (Hφ & Henv). auto.
Qed.

Local Lemma arena_sub_guard_names δ a Γ φ df x y :
  arena_sub_guard δ a Γ φ -> df ⊑↑ φ ->
  arena_sub_guard δ a Γ (df ⊔ $!x ⊔ $!y).
Proof.
  intros H Hdf. eapply arena_sub_guard_locs; [exact H|].
  intro l. change (qlocs φ l = false -> qlocs df l || (false || false) = false).
  rewrite orb_false_r. apply arena_qual_loc_false_sub, safety_le_fresh_variant. exact Hdf.
Qed.

Local Lemma arena_sub_guard_one_name δ a Γ φ df x :
  arena_sub_guard δ a Γ φ -> df ⊑↑ φ ->
  arena_sub_guard δ a Γ (df ⊔ $!x).
Proof.
  intros H Hdf.
  eapply arena_sub_guard_locs; [exact H|].
  intro l. change (qlocs φ l = false -> qlocs df l || false = false).
  rewrite orb_false_r. apply arena_qual_loc_false_sub, safety_le_fresh_variant. exact Hdf.
Qed.

Record arena_substitution_data (Σ Σ' : senv) (U : ty) (δ : qual) (u : tm)
  (a : binding * bool * ty * qual) : Prop :=
  ArenaSubstitutionData {
    arena_sub_extend : Σ' ⊇₂ Σ;
    arena_sub_U_closed : closed_ty 0 0 (length Σ') U;
    arena_sub_delta_closed : closed_Qual 0 0 (length Σ') δ↑;
    arena_sub_delta_nonfresh : ♦∉ δ;
    arena_sub_term_closed : closed_tm 0 0 (length Σ') u;
    arena_sub_term_no_scopes : local_locs u = ∅;
    arena_sub_binding_valid : arena_substitution_binding Σ' U δ a;
    arena_sub_term_available : fst (fst (fst a)) = bind_tm -> forall Γ φ,
      closed_Qual 0 (length Γ) (length Σ') φ↑ -> δ ⊑↑ φ ->
      has_type Γ φ Σ' u (snd (fst a)) δ
  }.

Local Lemma arena_sub_qual_at_env Σ Σ' U δ u a Γ Δ n q q' :
  arena_substitution_data Σ Σ' U δ u a -> arena_env_substitution U δ a Γ Δ ->
  closed_Qual n (length Γ) (length Σ) q↑ -> arena_qual_substitution δ q q' ->
  closed_Qual n (length Δ) (length Σ') q'↑.
Proof.
  intros D (HL & _ & _) Hq HQ. rewrite HL in Hq.
  eapply arena_qsub_closed; [exact HQ|exact Hq|exact (arena_sub_delta_closed _ _ _ _ _ _ D)|].
  apply safety_senv_length. exact (arena_sub_extend _ _ _ _ _ _ D).
Qed.

Local Lemma arena_sub_type_at_env Σ Σ' U δ u a Γ Δ n T T' :
  arena_substitution_data Σ Σ' U δ u a -> arena_env_substitution U δ a Γ Δ ->
  closed_ty n (length Γ) (length Σ) T -> arena_ty_substitution U δ T T' ->
  closed_ty n (length Δ) (length Σ') T'.
Proof.
  intros D (HL & _ & _) HT HT'. rewrite HL in HT.
  eapply arena_tsub_closed; [exact HT'| |exact (arena_sub_U_closed _ _ _ _ _ _ D)
    |exact (arena_sub_delta_closed _ _ _ _ _ _ D)|exact HT].
  apply safety_senv_length. exact (arena_sub_extend _ _ _ _ _ _ D).
Qed.

Local Lemma arena_sub_stp Σ Σ' U δ u a Γ Δ T q R r T' q' R' r' :
  arena_substitution_data Σ Σ' U δ u a ->
  arena_env_substitution U δ a Γ Δ ->
  stp Γ Σ T q R r ->
  arena_ty_substitution U δ T T' -> arena_ty_substitution U δ R R' ->
  arena_qual_substitution δ q q' -> arena_qual_substitution δ r r' ->
  stp Δ Σ' T' q' R' r'.
Proof.
  intros D HE HS HT HR HQ Hr.
  eapply arena_stp_substitute;
    [eapply safety_stp_weaken; [exact (arena_sub_extend _ _ _ _ _ _ D)|exact HS]|
     exact HE|exact (arena_sub_binding_valid _ _ _ _ _ _ D)|
     exact (arena_sub_U_closed _ _ _ _ _ _ D)|
     exact (arena_sub_delta_closed _ _ _ _ _ _ D)|
     exact (arena_sub_delta_nonfresh _ _ _ _ _ _ D)|exact HT|exact HR|exact HQ|exact Hr].
Qed.

Local Lemma arena_sub_fresh_bound δ q q' φ φ' :
  arena_qual_substitution δ q q' ->
  arena_qual_substitution δ φ φ' ->
  q ⊑↑ φ ⊔ {♦} -> q' ⊑↑ φ' ⊔ {♦}.
Proof.
  intros HQ HP HB.
  eapply arena_qsub_subset; [exact HQ| |exact HB].
  now apply arena_qsub_join, arena_qsub_marker.
Qed.

Local Lemma arena_sub_type_cast Σ Σ' U δ u a Γ Δ φ φ' t T d T0 d0 T' d' :
  arena_substitution_data Σ Σ' U δ u a ->
  arena_env_substitution U δ a Γ Δ ->
  has_type Γ φ Σ t T d -> local_locs (subst_tm t 0 u) = ∅ ->
  arena_qual_substitution δ φ φ' ->
  arena_ty_substitution U δ T T0 -> arena_qual_substitution δ d d0 ->
  arena_ty_substitution U δ T T' -> arena_qual_substitution δ d d' ->
  has_type Δ φ' Σ' (subst_tm t 0 u) T0 d0 ->
  has_type Δ φ' Σ' (subst_tm t 0 u) T' d'.
Proof.
  intros D HE HT HS Hφ HT0 HD0 HT' HD' HT0'.
  eapply t_sub; [exact HT0'| | |].
  - eapply arena_sub_stp; [exact D|exact HE| |exact HT0|exact HT'|exact HD0|exact HD'].
    apply safety_stp_refl.
    + exact (safety_typing_type_closed _ _ _ _ _ _ HT).
    + apply qs_sq; [apply safety_subq_refl|exact (safety_typing_qual_closed _ _ _ _ _ _ HT)].
  - exact (arena_sub_fresh_bound _ _ _ _ _ HD' Hφ (safety_typing_qual_bound _ _ _ _ _ _ HT)).
  - rewrite HS. apply safety_empty_sep.
Qed.

Local Lemma arena_sub_type_open_result U δ L A A' B B' q q' :
  closed_ty 0 0 L U ->
  arena_ty_substitution U δ A A' -> arena_ty_substitution U δ B B' ->
  arena_qual_substitution δ q q' ->
  arena_ty_substitution U δ (A <~ᵀ TUnit ~ ∅ ; B ~ q) (A' <~ᵀ TUnit ~ ∅ ; B' ~ q').
Proof.
  intros HU HA HB HQ. unfold open_ty.
  eapply arena_tsub_open with (L := L); [exact HU| |exact HB|exact HQ].
  eapply arena_tsub_open with (L := L); [exact HU|exact HA|constructor|apply arena_qsub_empty].
Qed.

Local Lemma arena_sub_qual_open_result δ q q' a a' b b' :
  arena_qual_substitution δ q q' -> arena_qual_substitution δ a a' -> arena_qual_substitution δ b b' ->
  arena_qual_substitution δ (q <~ᵈ a ; b) (q' <~ᵈ a' ; b').
Proof. unfold openq. intros. eauto using arena_qsub_open. Qed.

Local Lemma arena_sub_senv_bounds Γ φ Σ t T q :
  has_type Γ φ Σ t T q -> forall ψ, φ ⊑↑ ψ -> q ⊑↑ ψ ⊔ {♦}.
Proof.
  intros H ψ Hle.
  eapply safety_le_fresh_trans; [exact (safety_typing_qual_bound _ _ _ _ _ _ H)|exact Hle].
Qed.

Local Lemma arena_sub_fresh_call_domain (allcall : bool) δ Γ Δ Σ' φ' df df' d1 d1' d2 e2 T1 T1' T2 T2' t p :
  arena_qual_substitution δ df df' -> arena_qual_substitution δ d1 d1' ->
  arena_ty_substitution p δ T1 T1' -> arena_ty_substitution p δ T2 T2' ->
  arena_qual_substitution δ d2 e2 ->
  (q_trans_tenv Δ df' ⋒ q_trans_tenv Δ d1') ⊑↑
     arena_sub_qual δ (q_trans_tenv Γ df ⋒ q_trans_tenv Γ d1) ->
  has_type Δ φ' Σ' t
    (if allcall then TAll (arena_sub_qual δ (q_trans_tenv Γ df ⋒ q_trans_tenv Γ d1)) e2 T1' T2'
                else TFun (arena_sub_qual δ (q_trans_tenv Γ df ⋒ q_trans_tenv Γ d1)) e2 T1' T2') df' ->
  local_locs t = ∅ ->
  has_type Δ φ' Σ' t
    (if allcall then TAll (q_trans_tenv Δ df' ⋒ q_trans_tenv Δ d1') e2 T1' T2'
                else TFun (q_trans_tenv Δ df' ⋒ q_trans_tenv Δ d1') e2 T1' T2') df'.
Proof.
  intros HF HA H1 H2 HE Hle HT HLC. destruct allcall.
  all: eapply t_sub; [exact HT| |exact (safety_typing_qual_bound _ _ _ _ _ _ HT)|
                      rewrite HLC; apply safety_empty_sep].
  - apply safety_sub_all_domain; try assumption.
    + exact (safety_typing_type_closed _ _ _ _ _ _ HT).
    + exact (safety_typing_qual_closed _ _ _ _ _ _ HT).
    + eapply safety_qual_closed_of_sub; [exact Hle|].
      pose proof (safety_typing_type_closed _ _ _ _ _ _ HT) as HC.
      inversion HC; assumption.
  - apply safety_sub_fun_domain; try assumption.
    + exact (safety_typing_type_closed _ _ _ _ _ _ HT).
    + exact (safety_typing_qual_closed _ _ _ _ _ _ HT).
    + eapply safety_qual_closed_of_sub; [exact Hle|].
      pose proof (safety_typing_type_closed _ _ _ _ _ _ HT) as HC.
      inversion HC; assumption.
Qed.

Local Lemma arena_sub_abstract_wf Σ Γ kind A d1 S df φ :
  arena_closed_env Γ Σ -> closed_ty 0 (length Γ) (length Σ) A ->
  closed_Qual 0 (length Γ) (length Σ) d1↑ ->
  closed_ty 0 (length Γ) (length Σ) S ->
  df ⊑↑ φ -> closed_Qual 0 (length Γ) (length Σ) φ↑ ->
  arena_closed_env ((kind,false,A,d1)::(bind_tm,true,S,df)::Γ) Σ.
Proof.
  intros W HA HD HS Hdf Hφ. apply arena_closed_env_cons.
  - apply arena_closed_env_cons; try assumption.
    eapply safety_qual_closed_of_sub; eassumption.
  - eapply safety_ty_vars_weaken; [exact HA|lia|simpl; lia].
  - eapply safety_fv_closed_weaken; [|exact HD]. simpl. lia.
Qed.

Local Lemma arena_sub_abstract_guard δ a Γ kind A d1 S df φ :
  arena_sub_guard δ a Γ φ -> df ⊑↑ φ -> d1 ⊑↑ df ⊔ {♦} ->
  arena_sub_guard δ a ((kind,false,A,d1)::(bind_tm,true,S,df)::Γ)
    (df ⊔ $!(length Γ) ⊔ $!(Nat.succ (length Γ))).
Proof.
  intros H Hdf H1. eapply arena_sub_guard_names; [|exact Hdf].
  apply arena_sub_guard_cons; [|eauto using safety_le_fresh_trans].
  apply arena_sub_guard_cons; [exact H|].
  apply safety_le_fresh_variant. exact Hdf.
Qed.

Local Lemma arena_sub_named_env U δ a Γ Δ k A A' d d' S S' df df' :
  arena_env_substitution U δ a Γ Δ ->
  arena_ty_substitution U δ A A' -> arena_qual_substitution δ d d' ->
  arena_ty_substitution U δ S S' -> arena_qual_substitution δ df df' ->
  arena_env_substitution U δ a
    ((k,false,A,d)::(bind_tm,true,S,df)::Γ)
    ((k,false,A',d')::(bind_tm,true,S',df')::Δ).
Proof. intros. apply arena_env_sub_cons; [now apply arena_env_sub_cons|assumption|assumption]. Qed.

Local Lemma arena_sub_locs_typing_unchanged t u :
  local_locs t = ∅ -> local_locs u = ∅ ->
  local_locs (subst_tm t 0 u) = ∅.
Proof. intros H U. now rewrite arena_sub_tm_locs. Qed.

Local Lemma arena_has_type_substitute_core U δ u a Σ' Γ φ Σ t T d :
  has_type Γ φ Σ t T d ->
  has_type Γ φ Σ t T d ->
  arena_substitution_data Σ Σ' U δ u a ->
  forall Δ φ' T' d',
    arena_env_substitution U δ a Γ Δ -> arena_closed_env Γ Σ ->
    arena_sub_guard δ a Γ φ -> local_locs t = ∅ ->
    arena_qual_substitution δ φ φ' ->
    arena_ty_substitution U δ T T' -> arena_qual_substitution δ d d' ->
    has_type Δ φ' Σ' (subst_tm t 0 u) T' d'.
Proof.
  intros HT. induction HT; intros Horig Data Δ φ' T' d' E W G Z P X Y;
    pose proof (proj1 E) as Len;
    pose proof (arena_sub_U_closed _ _ _ _ _ _ Data) as HU;
    pose proof (arena_sub_delta_closed _ _ _ _ _ _ Data) as Hδ;
    pose proof (arena_sub_delta_nonfresh _ _ _ _ _ _ Data) as Hδnf;
    pose proof (arena_sub_term_closed _ _ _ _ _ _ Data) as Hu;
    pose proof (arena_sub_term_no_scopes _ _ _ _ _ _ Data) as HLu;
    pose proof (arena_sub_extend _ _ _ _ _ _ Data) as Ext;
    pose proof (safety_senv_length _ _ Ext) as HLe;
    pose proof (arena_sub_qual_at_env _ _ _ _ _ _ _ _ _ _ _
      Data E (safety_typing_phi_closed _ _ _ _ _ _ Horig) P) as CP;
    pose proof (arena_sub_locs_typing_unchanged _ _ Z HLu) as Z'.
  - change (local_locs t = ∅) in Z.
    pose proof (arena_sub_type_at_env _ _ _ _ _ _ _ _ _ _ _ Data E H0 X) as CT.
    inversion X; subst T'. simpl.
    eapply t_tabs; [ |exact CT|exact CP| | | | |].
    + rewrite Len in H. exact (arena_sub_tm_closed _ _ _ _ _ _ H Hu HLe).
    + eapply arena_sub_fresh_bound; eassumption.
    + eapply arena_qsub_subset; eassumption.
    + eapply arena_qsub_nonfresh; eassumption.
    + rewrite arena_sub_tm_locs by exact HLu. rewrite Z. apply safety_empty_sep.
    + rewrite <- (arena_sub_tm_open_named _ _ _ _ _ Hu Len).
      eapply IHHT; [exact HT|exact Data| | | | | | |].
      * eapply arena_sub_named_env; eauto using arena_sub_all.
      * eapply arena_sub_abstract_wf; try eassumption; inversion H0; assumption.
      * eapply arena_sub_abstract_guard; eassumption.
      * now rewrite arena_open_named_locs.
      * rewrite Len. apply arena_qsub_join; [exact Y|].
        apply arena_qsub_join; apply arena_qsub_name.
      * eapply arena_tsub_open_named; eassumption.
      * apply arena_qsub_open_named; assumption.
  - change (local_locs t = ∅) in Z.
    destruct (arena_tsub_exists U δ T1) as [A HA].
    destruct (arena_tsub_exists U δ T2) as [B HB].
    set (g1 := arena_sub_qual δ d1).
    set (g2 := arena_sub_qual δ d2).
    set (gf := arena_sub_qual δ df).
    assert (HG1 : arena_qual_substitution δ d1 g1) by apply arena_sub_qual_image.
    assert (HG2 : arena_qual_substitution δ d2 g2) by apply arena_sub_qual_image.
    assert (HGF : arena_qual_substitution δ df gf) by apply arena_sub_qual_image.
    eapply arena_sub_type_cast with (T0 := B <~ᵀ TUnit ~ ∅ ; A ~ g1) (d0 := g2 <~ᵈ gf ; g1);
      [exact Data|exact E|exact Horig|exact Z'|exact P| | |exact X|exact Y|].
    + eapply arena_sub_type_open_result; eassumption.
    + now apply arena_sub_qual_open_result.
    + simpl. eapply t_tapp; [| | | | | | | |].
      * eapply IHHT; try eassumption. now constructor.
      * eapply arena_sub_type_at_env; eassumption.
      * eapply arena_sub_qual_at_env; eassumption.
      * eapply (arena_sub_fresh_bound δ (d2 <~ᵈ ∅ ; ∅)); [|exact P|eassumption].
        apply arena_sub_qual_open_result; [exact HG2|apply arena_qsub_empty|apply arena_qsub_empty].
      * eapply arena_qsub_nonfresh; eassumption.
      * eapply arena_qsub_subset; eassumption.
      * eapply arena_tsub_preserves_not_free; eassumption.
      * rewrite arena_sub_tm_locs, Z by exact HLu. apply safety_empty_sep.
      * rewrite arena_sub_tm_locs, Z by exact HLu. apply safety_empty_sep.
  - change (local_locs t = ∅) in Z.
    destruct (arena_tsub_exists U δ T1) as [A HA].
    destruct (arena_tsub_exists U δ T2) as [B HB].
    set (g1 := arena_sub_qual δ d1).
    set (g2 := arena_sub_qual δ d2).
    set (gf := arena_sub_qual δ df).
    assert (HG1 : arena_qual_substitution δ d1 g1) by apply arena_sub_qual_image.
    assert (HG2 : arena_qual_substitution δ d2 g2) by apply arena_sub_qual_image.
    assert (HGF : arena_qual_substitution δ df gf) by apply arena_sub_qual_image.
    assert (Hdf : df ⊑↑ φ ⊔ {♦}) by exact (safety_typing_qual_bound _ _ _ _ _ _ HT).
    pose proof (arena_ordered_arena_closed_env _ _ W) as Ord.
    eapply arena_sub_type_cast with (T0 := B <~ᵀ TUnit ~ ∅ ; A ~ g1) (d0 := g2 <~ᵈ gf ; g1);
      [exact Data|exact E|exact Horig|exact Z'|exact P| | |exact X|exact Y|].
    + eapply arena_sub_type_open_result; eassumption.
    + now apply arena_sub_qual_open_result.
    + simpl. eapply t_tapp_fresh; [| | | | | | | | | |].
      * change (has_type Δ φ' Σ' (subst_tm t 0 u)
            (if true then TAll (q_trans_tenv Δ gf ⋒ q_trans_tenv Δ g1) g2 A B else TFun ∅ ∅ A B) gf).
        eapply (arena_sub_fresh_call_domain true δ Γ Δ Σ' φ' df gf d1 g1 d2 g2 T1 A T2 B);
          try eassumption.
        -- eapply (arena_qsub_overlap_bound U δ a Γ Δ φ df gf d1 g1); try eassumption.
           apply arena_sub_qual_image.
        -- eapply IHHT; try eassumption.
           constructor; try assumption. apply arena_sub_qual_image.
      * eapply arena_sub_type_at_env; eassumption.
      * eapply arena_sub_qual_at_env; eassumption.
      * eapply arena_sub_fresh_bound; eassumption.
      * intro Hfresh. eapply arena_tsub_preserves_not_free; [exact HU|exact HB|].
        apply H2. eapply arena_qsub_hasfresh; eassumption.
      * eapply arena_tsub_preserves_not_free; eassumption.
      * eapply (arena_sub_fresh_bound δ (d2 <~ᵈ ∅ ; ∅)); [|exact P|eassumption].
        apply arena_sub_qual_open_result; [exact HG2|apply arena_qsub_empty|apply arena_qsub_empty].
      * eapply safety_subq_trans.
        -- eapply (arena_qsub_overlap_bound U δ a Γ Δ φ d1 g1 df gf); try eassumption.
           apply arena_sub_qual_image.
        -- eapply arena_sub_fresh_bound; [apply arena_sub_qual_image|exact P|eassumption].
      * rewrite arena_sub_tm_locs, Z by exact HLu. apply safety_empty_sep.
      * rewrite arena_sub_tm_locs, Z by exact HLu. apply safety_empty_sep.
      * rewrite arena_sub_tm_locs, Z by exact HLu. apply safety_empty_sep.
  - inversion X; subst T'.
    eapply arena_sub_type_cast with (T0 := TUnit) (d0 := ∅);
      [exact Data|exact E|exact Horig|exact Z'|exact P|constructor|apply arena_qsub_empty|exact X|exact Y|].
    simpl. exact (t_base Δ Σ' φ' CP).
  - destruct x as [|x].
    + pose proof (proj1 (proj2 E)) as HA. rewrite H in HA. inversion HA; subst a.
      eapply arena_sub_type_cast with (T0 := T) (d0 := δ);
        [exact Data|exact E|exact Horig|exact Z'|exact P| | |exact X|exact Y|].
      * eapply arena_tsub_rigid. eassumption.
      * eapply arena_qsub_zero; eassumption.
      * change (has_type Δ φ' Σ' u T δ).
        apply (arena_sub_term_available _ _ _ _ _ _ Data); [reflexivity|exact CP|].
        eapply arena_qsub_subset; [eapply arena_qsub_zero; eassumption|exact P|eassumption].
    + destruct (proj2 (proj2 E) _ _ _ _ _ H) as (A & r & Hget & HA & HR).
      eapply arena_sub_type_cast with (T0 := A) (d0 := $!x);
        [exact Data|exact E|exact Horig|exact Z'|exact P|exact HA|apply arena_qsub_name|exact X|exact Y|].
      change (has_type Δ φ' Σ' (tvar (varF x)) A $!x).
      eapply t_var; [exact Hget| |exact CP| |].
      * eapply arena_qsub_subset; [apply arena_qsub_name|exact P|eassumption].
      * eapply arena_tsub_closed; eassumption.
      * eapply arena_qsub_closed; eassumption.
  - change (local_locs t = ∅) in Z.
    pose proof (arena_sub_type_at_env _ _ _ _ _ _ _ _ _ _ _ Data E H0 X) as CT.
    inversion X; subst T'. simpl.
    eapply t_abs; [ |exact CT|exact CP| | | | |].
    + rewrite Len in H. exact (arena_sub_tm_closed _ _ _ _ _ _ H Hu HLe).
    + eapply arena_sub_fresh_bound; eassumption.
    + eapply arena_qsub_subset; eassumption.
    + eapply arena_qsub_nonfresh; eassumption.
    + rewrite arena_sub_tm_locs by exact HLu. rewrite Z. apply safety_empty_sep.
    + rewrite <- (arena_sub_tm_open_named _ _ _ _ _ Hu Len).
      eapply IHHT; [exact HT|exact Data| | | | | | |].
      * eapply arena_sub_named_env; eauto using arena_sub_fun.
      * eapply arena_sub_abstract_wf; try eassumption; inversion H0; assumption.
      * eapply arena_sub_abstract_guard; eassumption.
      * now rewrite arena_open_named_locs.
      * rewrite Len. apply arena_qsub_join; [exact Y|].
        apply arena_qsub_join; apply arena_qsub_name.
      * eapply arena_tsub_open_named; eassumption.
      * apply arena_qsub_open_named; assumption.
  - change ((local_locs t1 ⊔ local_locs t2) = ∅) in Z.
    destruct (arena_empty_join_parts _ _ Z) as [L1 L2]. subst φd.
    destruct (arena_tsub_exists U δ T1) as [A HA].
    destruct (arena_tsub_exists U δ T2) as [B HB].
    set (g1 := arena_sub_qual δ d1).
    set (g2 := arena_sub_qual δ d2).
    set (gf := arena_sub_qual δ df).
    assert (HG1 : arena_qual_substitution δ d1 g1) by apply arena_sub_qual_image.
    assert (HG2 : arena_qual_substitution δ d2 g2) by apply arena_sub_qual_image.
    assert (HGF : arena_qual_substitution δ df gf) by apply arena_sub_qual_image.
    eapply arena_sub_type_cast with (T0 := B <~ᵀ TUnit ~ ∅ ; A ~ g1) (d0 := g2 <~ᵈ gf ; g1);
      [exact Data|exact E|exact Horig|exact Z'|exact P| | |exact X|exact Y|].
    + eapply arena_sub_type_open_result; eassumption.
    + now apply arena_sub_qual_open_result.
    + simpl. eapply t_app with (φd := qdiff φ' (local_locs (subst_tm t1 0 u)));
        [| | | | |reflexivity| |].
      * eapply IHHT1; try eassumption. now constructor.
      * eapply IHHT2; try eassumption.
        -- eapply arena_sub_guard_scope; [exact G|].
           apply safety_le_fresh_variant, safety_diff_le.
        -- rewrite arena_sub_tm_locs by exact HLu. rewrite L1.
           now apply arena_qsub_diff_empty.
      * eapply (arena_sub_fresh_bound δ (d2 <~ᵈ ∅ ; ∅)); [|exact P|eassumption].
        apply arena_sub_qual_open_result; [exact HG2|apply arena_qsub_empty|apply arena_qsub_empty].
      * eapply arena_qsub_nonfresh; eassumption.
      * eapply arena_tsub_preserves_not_free; eassumption.
      * rewrite arena_sub_tm_locs, L2 by exact HLu. apply safety_empty_sep.
      * rewrite !arena_sub_tm_locs, Z by exact HLu. apply safety_empty_sep.
  - change ((local_locs t1 ⊔ local_locs t2) = ∅) in Z.
    destruct (arena_empty_join_parts _ _ Z) as [L1 L2]. subst φd.
    destruct (arena_tsub_exists U δ T1) as [A HA].
    destruct (arena_tsub_exists U δ T2) as [B HB].
    set (g1 := arena_sub_qual δ d1).
    set (g2 := arena_sub_qual δ d2).
    set (gf := arena_sub_qual δ df).
    assert (HG1 : arena_qual_substitution δ d1 g1) by apply arena_sub_qual_image.
    assert (HG2 : arena_qual_substitution δ d2 g2) by apply arena_sub_qual_image.
    assert (HGF : arena_qual_substitution δ df gf) by apply arena_sub_qual_image.
    assert (Hdf : df ⊑↑ φ ⊔ {♦}) by exact (safety_typing_qual_bound _ _ _ _ _ _ HT1).
    assert (Hd1 : d1 ⊑↑ φ ⊔ {♦})
      by exact (arena_sub_senv_bounds _ _ _ _ _ _ HT2 _ (safety_diff_le _ _)).
    pose proof (arena_ordered_arena_closed_env _ _ W) as Ord.
    eapply arena_sub_type_cast with (T0 := B <~ᵀ TUnit ~ ∅ ; A ~ g1) (d0 := g2 <~ᵈ gf ; g1);
      [exact Data|exact E|exact Horig|exact Z'|exact P| | |exact X|exact Y|].
    + eapply arena_sub_type_open_result; eassumption.
    + now apply arena_sub_qual_open_result.
    + simpl. eapply t_app_fresh with (φd := qdiff φ' (local_locs (subst_tm t1 0 u)));
        [| | | | | |reflexivity| | |].
      * change (has_type Δ φ' Σ' (subst_tm t1 0 u)
            (if false then TAll ∅ ∅ A B else TFun (q_trans_tenv Δ gf ⋒ q_trans_tenv Δ g1) g2 A B) gf).
        eapply (arena_sub_fresh_call_domain false δ Γ Δ Σ' φ' df gf d1 g1 d2 g2 T1 A T2 B);
          try eassumption.
        -- eapply (arena_qsub_overlap_bound U δ a Γ Δ φ df gf d1 g1); try eassumption.
           apply arena_sub_qual_image.
        -- eapply IHHT1; try eassumption.
           constructor; try assumption. apply arena_sub_qual_image.
        -- now rewrite arena_sub_tm_locs.
      * eapply IHHT2; try eassumption.
        -- eapply arena_sub_guard_scope; [exact G|].
           apply safety_le_fresh_variant, safety_diff_le.
        -- rewrite arena_sub_tm_locs by exact HLu. rewrite L1.
           now apply arena_qsub_diff_empty.
      * intro Hfresh. eapply arena_tsub_preserves_not_free; [exact HU|exact HB|].
        apply H. exact (arena_qsub_hasfresh _ _ _ HG1 Hfresh).
      * eapply arena_tsub_preserves_not_free; eassumption.
      * eapply (arena_sub_fresh_bound δ (d2 <~ᵈ ∅ ; ∅)); [|exact P|eassumption].
        apply arena_sub_qual_open_result; [exact HG2|apply arena_qsub_empty|apply arena_qsub_empty].
      * eapply safety_subq_trans.
        -- eapply (arena_qsub_overlap_bound U δ a Γ Δ φ d1 g1 df gf); try eassumption.
           apply arena_sub_qual_image.
        -- eapply arena_sub_fresh_bound; [apply arena_sub_qual_image|exact P|eassumption].
      * rewrite arena_sub_tm_locs, L2 by exact HLu. apply safety_empty_sep.
      * rewrite !arena_sub_tm_locs, Z by exact HLu. apply safety_empty_sep.
      * rewrite arena_sub_tm_locs, L1 by exact HLu. apply safety_empty_sep.
  - assert (Hloc : closed_Qual 0 0 (length Σ) (&!l)↑).
    { destruct (safety_sindexr _ _ _ _ H0) as (s & Hs & _).
      apply safety_one_loc_closed. exact (safety_indexr_bound _ _ _ Hs). }
    pose proof (arena_qsub_rigid δ _ _ _ Hloc) as HL.
    eapply arena_sub_type_cast with (T0 := TRef q T) (d0 := &!l);
      [exact Data|exact E|exact Horig|exact Z'|exact P| |exact HL|exact X|exact Y|].
    + constructor; [eapply arena_qsub_rigid|eapply arena_tsub_rigid]; eassumption.
    + simpl. apply t_loc; [exact CP| | | | |assumption].
      * eapply safety_sindexr_weaken; eassumption.
      * eapply safety_ty_closed_weaken; eassumption.
      * eapply safety_locs_closed_weaken; eassumption.
      * eapply arena_qsub_subset; [exact HL|exact P|eassumption].
  - change (local_locs t = ∅) in Z.
    eapply arena_sub_type_cast with (T0 := T') (d0 := {♦});
      [exact Data|exact E|exact Horig|exact Z'|exact P|exact X|apply arena_qsub_marker|exact X|exact Y|].
    inversion X; subst T'. simpl. apply t_ref.
    + eapply IHHT; eassumption.
    + eapply arena_sub_type_at_env; eassumption.
    + eapply arena_qsub_nonfresh; eassumption.
  - change ((local_locs t1 ⊔ local_locs t2) = ∅) in Z.
    destruct (arena_empty_join_parts _ _ Z) as [L1 L2]. subst φd.
    inversion X; subst T'.
    destruct (arena_tsub_exists U δ T1) as [ArenaType HAtarget].
    set (g := arena_sub_qual δ d1).
    simpl. eapply t_refat with (φd := qdiff φ' (local_locs (subst_tm t2 0 u))) (T1 := ArenaType) (d1 := g);
      [| | |reflexivity|].
    + eapply IHHT1; try eassumption.
      * eapply arena_sub_guard_scope; [exact G|].
        apply safety_le_fresh_variant, safety_diff_le.
      * rewrite arena_sub_tm_locs by exact HLu. rewrite L2. now apply arena_qsub_diff_empty.
    + eapply arena_qsub_nonfresh; eassumption.
    + eapply IHHT2; try eassumption.
      constructor; [apply arena_sub_qual_image|exact HAtarget].
    + rewrite arena_sub_tm_locs, L1 by exact HLu. apply safety_empty_sep.
  - change (local_locs t = ∅) in Z.
    simpl. eapply t_deref with (d := arena_sub_qual δ d).
    + eapply IHHT; try eassumption.
      * now constructor.
      * apply arena_sub_qual_image.
    + eapply arena_qsub_nonfresh; eassumption.
    + eapply arena_qsub_subset; eassumption.
    + rewrite arena_sub_tm_locs, Z by exact HLu. apply safety_empty_sep.
  - change ((local_locs t1 ⊔ local_locs t2) = ∅) in Z.
    destruct (arena_empty_join_parts _ _ Z) as [L1 L2]. subst φd.
    inversion X; subst T'.
    destruct (arena_tsub_exists U δ T) as [A HA].
    set (g1 := arena_sub_qual δ d1).
    set (g := arena_sub_qual δ d).
    eapply arena_sub_type_cast with (T0 := TUnit) (d0 := ∅);
      [exact Data|exact E|exact Horig|exact Z'|exact P|constructor|apply arena_qsub_empty|exact X|exact Y|].
    simpl. eapply t_assign with (φd := qdiff φ' (local_locs (subst_tm t1 0 u)))
      (d := g) (d1 := g1) (T := A); [| | |reflexivity|].
    + eapply IHHT1; try eassumption.
      * constructor; [apply arena_sub_qual_image|exact HA].
      * apply arena_sub_qual_image.
    + eapply IHHT2; try eassumption.
      * eapply arena_sub_guard_scope; [exact G|].
        apply safety_le_fresh_variant, safety_diff_le.
      * rewrite arena_sub_tm_locs by exact HLu. rewrite L1. now apply arena_qsub_diff_empty.
      * apply arena_sub_qual_image.
    + eapply arena_qsub_nonfresh; [apply arena_sub_qual_image|eassumption].
    + rewrite arena_sub_tm_locs, L2 by exact HLu. apply safety_empty_sep.
  - destruct (arena_tsub_exists U δ T1) as [A HA].
    set (g := arena_sub_qual δ d1).
    eapply t_sub with (T1 := A) (d1 := g).
    + eapply IHHT; try eassumption. apply arena_sub_qual_image.
    + eapply arena_sub_stp; try eassumption. apply arena_sub_qual_image.
    + eapply arena_sub_fresh_bound; eassumption.
    + rewrite Z'. apply safety_empty_sep.
  - change ((local_locs t1 ⊔ local_locs t2) = ∅) in Z.
    destruct (arena_empty_join_parts _ _ Z) as [L1 L2].
    destruct (arena_tsub_exists U δ T1) as [A HA].
    set (g := arena_sub_qual δ d1).
    set (ψ := arena_sub_qual δ φd).
    simpl. eapply t_withr with (φd := ψ) (T1 := A) (d1 := g).
    + eapply IHHT1; try eassumption. apply arena_sub_qual_image.
    + eapply arena_qsub_nonfresh; [apply arena_sub_qual_image|eassumption].
    + eapply arena_sub_type_at_env; eassumption.
    + eapply arena_sub_qual_at_env; eassumption.
    + match goal with Htm : closed_tm 2 (length Γ) (length Σ) t2 |- _ =>
        rewrite Len in Htm; exact (arena_sub_tm_closed _ _ _ _ _ _ Htm Hu HLe)
      end.
    + rewrite <- (arena_sub_tm_open_named _ _ _ _ _ Hu Len).
      eapply IHHT2; [exact HT2|exact Data| | | | | | |].
      * apply arena_env_sub_cons; [apply arena_env_sub_cons; [exact E|constructor|apply arena_qsub_marker]| |apply arena_qsub_marker].
        constructor; [apply arena_sub_qual_image|exact HA].
      * apply arena_closed_env_cons.
        -- apply arena_closed_env_cons; [exact W|constructor|apply safety_qual_const_closed].
        -- apply cl_TRef.
           eapply safety_ty_vars_weaken; [exact (safety_typing_type_closed _ _ _ _ _ _ HT1)|lia|simpl; lia].
           eapply safety_fv_closed_weaken; [|exact (safety_typing_qual_closed _ _ _ _ _ _ HT1)]; simpl; lia.
        -- apply safety_qual_const_closed.
      * eapply arena_sub_guard_one_name; [|eassumption].
        apply arena_sub_guard_cons; [|apply safety_join_r].
        apply arena_sub_guard_cons; [exact G|apply safety_join_r].
      * now rewrite arena_open_named_locs.
      * rewrite Len. apply arena_qsub_join; [apply arena_sub_qual_image|apply arena_qsub_name].
      * exact X.
      * exact Y.
    + eapply arena_qsub_subset; [apply arena_sub_qual_image|exact P|eassumption].
    + rewrite arena_sub_tm_locs, L1 by exact HLu. apply safety_empty_sep.
  - exfalso. exact (arena_empty_twithc _ _ Z).
Qed.

Local Lemma arena_has_type_substitute U δ u a Σ' Γ φ Σ t T d Δ φ' T' d' :
  has_type Γ φ Σ t T d -> arena_substitution_data Σ Σ' U δ u a ->
  arena_env_substitution U δ a Γ Δ -> arena_closed_env Γ Σ ->
  arena_sub_guard δ a Γ φ -> local_locs t = ∅ ->
  arena_qual_substitution δ φ φ' ->
  arena_ty_substitution U δ T T' -> arena_qual_substitution δ d d' ->
  has_type Δ φ' Σ' (subst_tm t 0 u) T' d'.
Proof.
  intros H Data E W G K P X Y. exact (arena_has_type_substitute_core _ _ _ _ _ _ _ _ _ _ _ H H Data _ _ _ _ E W G K P X Y).
Qed.

Local Lemma arena_sub_tm_no_free t u b L :
  closed_tm b 0 L t -> subst_tm t 0 u = t.
Proof.
  intros H. remember 0 as f eqn:HE.
  induction H; subst; simpl;
    try lia; try rewrite ?IHclosed_tm, ?IHclosed_tm1, ?IHclosed_tm2; reflexivity.
Qed.

Local Lemma arena_double_inst_tm b v w L L' :
  closed_tm 2 0 L b -> closed_tm 0 0 L' v -> closed_tm 0 0 L' w ->
  subst_tm (subst_tm (b <~²ᵗ ([] : tenv)) 0 v) 0 w =
  (b <~ᵗ (subst_tm v 0 w) ; w).
Proof.
  intros Hb Hv Hw. unfold open_tm', open_tm.
  rewrite !arena_sub_tm_open with (L := L') by assumption.
  rewrite (arena_sub_tm_no_free _ _ _ _ Hb).
  rewrite (arena_sub_tm_no_free _ _ _ _ Hb).
  reflexivity.
Qed.

Local Lemma arena_empty_guard a Γ φ : arena_sub_guard ∅ a Γ φ.
Proof. intros l H; discriminate H. Qed.

Local Lemma arena_unit_sub_data Σ :
  arena_substitution_data Σ Σ TUnit ∅ tunit (bind_tm,true,TUnit,{♦}).
Proof.
  constructor.
  - apply safety_senv_refl.
  - constructor.
  - apply safety_qual_const_closed.
  - simpl. tauto.
  - constructor.
  - reflexivity.
  - simpl. split; [intros H; exfalso; exact (H I)|].
    split; [intros _ H; exfalso; exact (H I)|discriminate].
  - intros _ Γ φ HC _. now apply t_base.
Qed.

Local Lemma arena_handle_sub_data Σ T q :
  closed_ty 0 0 (length Σ) T -> closed_Qual 0 0 (length Σ) q↑ -> ♦∉ q ->
  arena_substitution_data Σ ([(T,q)]::Σ) TUnit (&!(length Σ))
    (tloc (length Σ) 0) (bind_tm,false,TRef q T,{♦}).
Proof.
  intros HT HQ Hnf.
  constructor.
  - apply safety_senv_cons_ext.
  - constructor.
  - apply safety_one_loc_closed. simpl. lia.
  - apply safety_nonfresh_loc.
  - constructor. simpl. lia.
  - reflexivity.
  - simpl. split; [intros H; exfalso; exact (H I)|].
    split; [intros H; discriminate H|discriminate].
  - intros _ Γ φ Hφ Hloc. cbn.
    apply t_loc; [exact Hφ| | | |exact Hloc|exact Hnf].
    + simpl. now rewrite Nat.eqb_refl.
    + eapply safety_ty_closed_weaken; [simpl; apply Nat.le_succ_diag_r|exact HT].
    + eapply safety_locs_closed_weaken; [simpl; apply Nat.le_succ_diag_r|exact HQ].
Qed.

(* Open the arena body with unit for self and with the handle to the newly allocated arena. *)
Local Lemma arena_arena_substitution_proved : safety_arena_substitution.
Proof.
  intros Σ φ φd b v T q U d W HT HV Hnf CT Cd Cb HW Hφd HB.
  destruct HW as (_ & _ & HL).
  pose proof (safety_typing_type_closed _ _ _ _ _ _ HT) as CA.
  pose proof (safety_typing_qual_closed _ _ _ _ _ _ HT) as Cq.
  pose proof (safety_typing_phi_closed _ _ _ _ _ _ HT) as Cφ.
  pose proof (safety_qual_closed_of_sub _ _ _ _ _ Hφd Cφ) as Cφd.
  set (self := (bind_tm,true,TUnit,{♦})).
  set (handle := (bind_tm,false,TRef q T,{♦})).
  assert (Hhandle : closed_ty 0 0 (length Σ) (TRef q T)) by (constructor; assumption).
  assert (WF : arena_closed_env [handle; self] Σ).
  { unfold handle, self. apply arena_closed_env_cons.
    - apply arena_closed_env_cons; [now constructor|constructor|apply safety_qual_const_closed].
    - eapply safety_ty_vars_weaken; [exact Hhandle|lia|simpl; lia].
    - apply safety_qual_const_closed. }
  assert (WF1 : arena_closed_env [handle] Σ).
  { unfold handle. apply arena_closed_env_cons; [now constructor|exact Hhandle|apply safety_qual_const_closed]. }
  assert (E1 : arena_env_substitution TUnit ∅ self [handle; self] [handle]).
  { unfold handle. apply arena_env_sub_cons; [apply arena_env_sub_base| |apply arena_qsub_marker].
    eapply arena_tsub_rigid. exact Hhandle. }
  set (body := b <~²ᵗ ([] : tenv)).
  assert (EL : local_locs body = ∅) by (unfold body; now rewrite arena_open_named_locs).
  assert (B1 : has_type [handle] (φd ⊔ $!0) Σ (subst_tm body 0 tunit) U d).
  { eapply arena_has_type_substitute; [exact HB|apply arena_unit_sub_data|exact E1|exact WF
    |apply arena_empty_guard|exact EL| | |].
    - change (arena_qual_substitution ∅ (φd ⊔ $!1) (φd ⊔ $!0)).
      apply arena_qsub_join; [eapply arena_qsub_rigid; exact Cφd|apply arena_qsub_name].
    - eapply arena_tsub_rigid. exact CT.
    - eapply arena_qsub_rigid. exact Cd. }
  set (l := length Σ).
  set (Σ' := [(T,q)]::Σ).
  set (w := tloc l 0).
  set (δ := &!l).
  assert (E2 : arena_env_substitution TUnit δ handle [handle] []) by apply arena_env_sub_base.
  assert (D : arena_substitution_data Σ Σ' TUnit δ w handle)
    by (unfold Σ', δ, w, l, handle; now apply arena_handle_sub_data).
  assert (G : arena_sub_guard δ handle [handle] (φd ⊔ $!0)).
  { intros x HX _. change (x =? l = true) in HX.
    apply Nat.eqb_eq in HX. subst x. split.
    - change (qlocs φd l || false = false).
      rewrite orb_false_r.
      destruct Cφd as (_ & _ & HF).
      destruct (qlocs φd l) eqn:Hz; [specialize (HF _ Hz); unfold l in *; lia|reflexivity].
    - intros x a HA. simpl in HA. destruct (x =? 0); [|discriminate].
      inversion HA; reflexivity. }
  assert (B2 : has_type [] (φd ⊔ δ) Σ' (subst_tm (subst_tm body 0 tunit) 0 w) U d).
  { eapply arena_has_type_substitute; [exact B1|exact D|exact E2|exact WF1|exact G| | | |].
    - now apply arena_sub_locs_typing_unchanged.
    - apply arena_qsub_join; [eapply arena_qsub_rigid; exact Cφd|].
      eapply arena_qsub_zero.
      + exact (arena_sub_delta_closed _ _ _ _ _ _ D).
      + exact (arena_sub_delta_nonfresh _ _ _ _ _ _ D).
    - eapply arena_tsub_rigid. exact CT.
    - eapply arena_qsub_rigid. exact Cd. }
  assert (B3 : has_type [] (φ ⊔ δ) Σ' (subst_tm (subst_tm body 0 tunit) 0 w) U d).
  { apply (safety_typing_scope_weaken _ _ _ _ _ _ B2).
    - apply safety_join_bound; [eauto using safety_subq_trans, safety_join_l|apply safety_join_r].
    - apply safety_qual_join_closed.
      + eapply safety_locs_closed_weaken; [|exact Cφ]. unfold Σ'; simpl; lia.
      + exact (arena_sub_delta_closed _ _ _ _ _ _ D). }
  unfold body in B3.
  rewrite (arena_double_inst_tm b tunit w (length Σ) (length Σ') Cb
    ltac:(constructor) (arena_sub_term_closed _ _ _ _ _ _ D)) in B3.
  exact B3.
Qed.

(* Shift free names to make room for an older context. Closed values can
   then be typed under the binders traversed by substitution. *)
Local Fixpoint arena_raise_tm (n : nat) (t : tm) : tm :=
  match t with
  | tvar (varF x) => tvar (varF (n+x))
  | tvar (varB x) => tvar (varB x)
  | ttabs b => ttabs (arena_raise_tm n b)
  | tabs b => tabs (arena_raise_tm n b)
  | ttapp u => ttapp (arena_raise_tm n u)
  | tapp f x => tapp (arena_raise_tm n f) (arena_raise_tm n x)
  | tunit => tunit
  | tloc l o => tloc l o
  | tref u => tref (arena_raise_tm n u)
  | trefat u s => trefat (arena_raise_tm n u) (arena_raise_tm n s)
  | tderef u => tderef (arena_raise_tm n u)
  | tassign u v => tassign (arena_raise_tm n u) (arena_raise_tm n v)
  | twithr u t => twithr (arena_raise_tm n u) (arena_raise_tm n t)
  | twithc l t => twithc l (arena_raise_tm n t)
  end.

Local Lemma arena_raise_locs n t :
  local_locs (arena_raise_tm n t) = local_locs t.
Proof.
  induction t; simpl; try rewrite ?IHt, ?IHt1, ?IHt2; try reflexivity.
  destruct v; reflexivity.
Qed.

Local Lemma arena_raise_closed n b f L t :
  closed_tm b f L t -> closed_tm b (n+f) L (arena_raise_tm n t).
Proof. intros H. induction H; simpl; constructor; try lia; auto. Qed.

Local Lemma arena_raise_rigid n b L t :
  closed_tm b 0 L t -> arena_raise_tm n t = t.
Proof.
  intro H. remember 0 as f eqn:HF.
  induction H; subst; simpl; try lia; rewrite ?IHclosed_tm, ?IHclosed_tm1, ?IHclosed_tm2; reflexivity.
Qed.

Local Lemma arena_raise_open n k t v :
  arena_raise_tm n (open_rec_tm k v t) =
    open_rec_tm k (arena_raise_tm n v) (arena_raise_tm n t).
Proof.
  revert k. induction t; intros k; simpl; try rewrite ?IHt, ?IHt1, ?IHt2;
    try reflexivity.
  destruct v0; simpl; [reflexivity|]. destruct (k =? i); reflexivity.
Qed.

Local Lemma arena_raise_open_named n (Γ Δ : tenv) t :
  length Δ = n + length Γ ->
  arena_raise_tm n (t <~²ᵗ Γ) = (arena_raise_tm n t) <~²ᵗ Δ.
Proof.
  intro H. unfold open_tm'. rewrite !arena_raise_open. simpl. rewrite H.
  replace (S (n + length Γ)) with (n + S (length Γ)) by lia. reflexivity.
Qed.

Local Lemma arena_shift_q_at_env n Γ Δ (Σ : senv) b q r :
  arena_env_shifted n Γ Δ ->
  closed_Qual b (length Γ) (length Σ) q↑ -> arena_qual_shifted n q r ->
  closed_Qual b (length Δ) (length Σ) r↑.
Proof. intros HE Hq HQ. rewrite (proj1 HE). eapply arena_shift_qual_closed; eassumption. Qed.

Local Lemma arena_shift_ty_at_env n Γ Δ (Σ : senv) b T T' :
  arena_env_shifted n Γ Δ ->
  closed_ty b (length Γ) (length Σ) T -> arena_ty_shifted n T T' ->
  closed_ty b (length Δ) (length Σ) T'.
Proof. intros HE HT HI. rewrite (proj1 HE). eapply arena_shift_ty_closed; eassumption. Qed.

Local Lemma arena_shift_q_fresh_bound n q q' p p' :
  arena_qual_shifted n q q' -> arena_qual_shifted n p p' ->
  q ⊑↑ p ⊔ {♦} -> q' ⊑↑ p' ⊔ {♦}.
Proof. intros Hq Hp H. eapply arena_shift_qual_le; [exact Hq| |exact H].
  now apply arena_shift_qual_join, arena_shift_fresh.
Qed.

Local Lemma arena_shift_q_hasfresh n q q' :
  arena_qual_shifted n q q' -> ♦∈ q' -> ♦∈ q.
Proof.
  intros (H & _). change (Is_true (qfresh q') -> Is_true (qfresh q)).
  now rewrite H.
Qed.

Local Lemma arena_shift_q_not_free n k q q' :
  arena_qual_shifted n q q' -> open_qual k ∅ q = q -> open_qual k ∅ q' = q'.
Proof.
  intros (_ & _ & HB & _) H.
  unfold open_qual. rewrite HB, (safety_q_not_free _ _ H). reflexivity.
Qed.

Local Lemma arena_shift_ty_not_free n T T' k :
  arena_ty_shifted n T T' -> not_free k T -> not_free k T'.
Proof.
  intros H. unfold not_free. revert k. induction H; intros k HK; simpl in *;
    try reflexivity.
  - now destruct (k =? x).
  - injection HK as HP HU. f_equal; eauto using arena_shift_q_not_free.
  - injection HK as HP HQ HT HU. f_equal; eauto using arena_shift_q_not_free.
  - injection HK as HP HQ HT HU. f_equal; eauto using arena_shift_q_not_free.
Qed.

Local Lemma arena_shift_diff_empty n p p' :
  arena_qual_shifted n p p' -> arena_qual_shifted n (qdiff p ∅) (qdiff p' ∅).
Proof.
  intros (H & HF & HB & HL).
  unfold arena_qual_shifted. cbn [qdiff q_empty qfresh qfvs qbvs qlocs fst snd negb].
  unfold n_diff, n_empty. cbn [negb].
  refine (conj _ (conj _ (conj _ _))).
  - now rewrite H.
  - intros x. unfold arena_shift_bits in *. rewrite HF.
    destruct (x <? n); reflexivity.
  - intros x. now rewrite HB.
  - intros x. now rewrite HL.
Qed.

Local Lemma arena_shift_q_overlap n p p' q q' :
  arena_qual_shifted n p p' -> arena_qual_shifted n q q' ->
  arena_qual_shifted n (p ⋒ q) (p' ⋒ q').
Proof.
  intros (HF & Hfv & Hb & Hl) (HR & Hrfv & Hrb & Hrl).
  unfold arena_qual_shifted. cbn [qand qor qfresh qfvs qbvs qlocs fst snd].
  unfold n_and, n_or, n_empty.
  repeat split.
  - now rewrite HF, HR.
  - intros x. rewrite Hfv, Hrfv. unfold arena_shift_bits. now destruct (x <? n).
  - intros x. now rewrite Hb, Hrb.
  - intros x. now rewrite Hl, Hrl.
Qed.

Local Lemma arena_shift_reaches n Γ Δ q q' Q :
  arena_env_shifted n Γ Δ -> arena_ordered_quals Γ ->
  arena_qual_shifted n q q' -> arena_qual_shifted n (q_trans_tenv Γ q) Q ->
  q_trans_tenv Δ q' ⊑↑ Q.
Proof.
  intros (HL & Henv) Ord HQ HS.
  pose proof (arena_q_trans_saturates Γ q Ord) as Hfull.
  unfold q_trans_tenv at 1. apply arena_qtrans_saturated_bound.
  - eapply arena_shift_qual_le; [exact HQ|exact HS|apply arena_qtrans_extensive].
  - intros x b Hx HF.
    pose proof (proj1 (proj2 HS) x) as H.
    rewrite H in HF. unfold arena_shift_bits in HF.
    destruct (x <? n) eqn:Hlt; [discriminate|].
    apply Nat.ltb_ge in Hlt.
    assert (Hx' : x-n < length Γ).
    { pose proof (safety_indexr_bound _ _ _ Hx). lia. }
    destruct (safety_indexr_exists Γ (x-n) Hx') as [a Ha].
    destruct a as [ [ [kind self] A] d].
    destruct (Henv _ _ _ _ _ Ha) as (A' & d' & HD & _ & HI).
    replace (n + (x-n)) with x in HD by lia. rewrite Hx in HD. inversion HD; subst b.
    eapply arena_shift_qual_le; [exact HI|exact HS|].
    exact (Hfull _ _ Ha HF).
Qed.

Local Lemma arena_overlap_mono a a' b b' :
  a ⊑↑ a' -> b ⊑↑ b' -> a ⋒ b ⊑↑ a' ⋒ b'.
Proof. safety_qpoint. Qed.

Local Lemma arena_shift_overlap_bound n Γ Δ a a' b b' r :
  arena_env_shifted n Γ Δ -> arena_ordered_quals Γ ->
  arena_qual_shifted n a a' -> arena_qual_shifted n b b' ->
  arena_qual_shifted n (q_trans_tenv Γ a ⋒ q_trans_tenv Γ b) r ->
  q_trans_tenv Δ a' ⋒ q_trans_tenv Δ b' ⊑↑ r.
Proof.
  intros HE HO HA HB HR.
  pose proof (arena_shift_qual_spec n (q_trans_tenv Γ a)) as HA'.
  pose proof (arena_shift_qual_spec n (q_trans_tenv Γ b)) as HB'.
  eapply safety_subq_trans.
  - apply arena_overlap_mono.
    + exact (arena_shift_reaches _ _ _ _ _ _ HE HO HA HA').
    + exact (arena_shift_reaches _ _ _ _ _ _ HE HO HB HB').
  - eapply arena_shift_qual_le; [exact (arena_shift_q_overlap _ _ _ _ _ HA' HB')|exact HR|apply safety_subq_refl].
Qed.

Local Lemma arena_shift_ty_open_result n A A' B B' q q' :
  arena_ty_shifted n A A' -> arena_ty_shifted n B B' -> arena_qual_shifted n q q' ->
  arena_ty_shifted n (A <~ᵀ TUnit ~ ∅ ; B ~ q) (A' <~ᵀ TUnit ~ ∅ ; B' ~ q').
Proof.
  unfold open_ty. intros HA HB HQ.
  apply arena_shift_open_ty; [apply arena_shift_open_ty; [exact HA|constructor|apply arena_shift_empty]|assumption|assumption].
Qed.

Local Lemma arena_shift_q_open_result n q q' a a' b b' :
  arena_qual_shifted n q q' -> arena_qual_shifted n a a' -> arena_qual_shifted n b b' ->
  arena_qual_shifted n (q <~ᵈ a ; b) (q' <~ᵈ a' ; b').
Proof. unfold openq. intros. eauto using arena_shift_open_qual. Qed.

Local Lemma arena_shift_change_type n Σ Γ Δ φ φ' t T d T0 d0 T' d' :
  arena_env_shifted n Γ Δ ->
  has_type Γ φ Σ t T d -> local_locs (arena_raise_tm n t) = ∅ ->
  arena_qual_shifted n φ φ' ->
  arena_ty_shifted n T T0 -> arena_qual_shifted n d d0 ->
  arena_ty_shifted n T T' -> arena_qual_shifted n d d' ->
  has_type Δ φ' Σ (arena_raise_tm n t) T0 d0 ->
  has_type Δ φ' Σ (arena_raise_tm n t) T' d'.
Proof.
  intros HE HT HS Hφ HT0 HD0 HT' HD' HT0'.
  eapply t_sub; [exact HT0'| | |].
  - eapply arena_shift_stp; [|exact HE|exact HT0|exact HT'|exact HD0|exact HD'].
    apply safety_stp_refl.
    + exact (safety_typing_type_closed _ _ _ _ _ _ HT).
    + apply qs_sq; [apply safety_subq_refl|exact (safety_typing_qual_closed _ _ _ _ _ _ HT)].
  - exact (arena_shift_q_fresh_bound _ _ _ _ _ HD' Hφ (safety_typing_qual_bound _ _ _ _ _ _ HT)).
  - rewrite HS. apply safety_empty_sep.
Qed.

Local Lemma arena_shift_fresh_call_domain (allcall : bool) n Γ Δ Σ φ df df' d1 d1' e2 T1' T2' t :
  (q_trans_tenv Δ df' ⋒ q_trans_tenv Δ d1') ⊑↑
     arena_shift_qual n (q_trans_tenv Γ df ⋒ q_trans_tenv Γ d1) ->
  has_type Δ φ Σ t
    (if allcall then TAll (arena_shift_qual n (q_trans_tenv Γ df ⋒ q_trans_tenv Γ d1)) e2 T1' T2'
                else TFun (arena_shift_qual n (q_trans_tenv Γ df ⋒ q_trans_tenv Γ d1)) e2 T1' T2') df' ->
  local_locs t = ∅ ->
  has_type Δ φ Σ t
    (if allcall then TAll (q_trans_tenv Δ df' ⋒ q_trans_tenv Δ d1') e2 T1' T2'
                else TFun (q_trans_tenv Δ df' ⋒ q_trans_tenv Δ d1') e2 T1' T2') df'.
Proof.
  intros Hle HT HLC. destruct allcall.
  all: eapply t_sub; [exact HT| |exact (safety_typing_qual_bound _ _ _ _ _ _ HT)|
                      rewrite HLC; apply safety_empty_sep].
  - apply safety_sub_all_domain; try assumption.
    + exact (safety_typing_type_closed _ _ _ _ _ _ HT).
    + exact (safety_typing_qual_closed _ _ _ _ _ _ HT).
    + eapply safety_qual_closed_of_sub; [exact Hle|].
      pose proof (safety_typing_type_closed _ _ _ _ _ _ HT) as HC.
      inversion HC; assumption.
  - apply safety_sub_fun_domain; try assumption.
    + exact (safety_typing_type_closed _ _ _ _ _ _ HT).
    + exact (safety_typing_qual_closed _ _ _ _ _ _ HT).
    + eapply safety_qual_closed_of_sub; [exact Hle|].
      pose proof (safety_typing_type_closed _ _ _ _ _ _ HT) as HC.
      inversion HC; assumption.
Qed.


Local Lemma arena_has_type_raise_core n Γ φ Σ t T d :
  has_type Γ φ Σ t T d -> has_type Γ φ Σ t T d ->
  forall Δ φ' T' d',
    arena_env_shifted n Γ Δ -> arena_closed_env Γ Σ -> local_locs t = ∅ ->
    arena_qual_shifted n φ φ' -> arena_ty_shifted n T T' -> arena_qual_shifted n d d' ->
    has_type Δ φ' Σ (arena_raise_tm n t) T' d'.
Proof.
  intros HT. induction HT; intros Horig Δ φ' T' d' E W Z P X Y;
    pose proof (proj1 E) as Len;
    pose proof (arena_shift_q_at_env _ _ _ _ _ _ _
      E (safety_typing_phi_closed _ _ _ _ _ _ Horig) P) as CP;
    match type of Horig with has_type _ _ _ ?src _ _ =>
      assert (Z' : local_locs (arena_raise_tm n src) = ∅) by (rewrite arena_raise_locs; exact Z)
    end.
  - change (local_locs t = ∅) in Z.
    pose proof (arena_shift_ty_at_env _ _ _ _ _ _ _ E H0 X) as CT.
    inversion X; subst T'. simpl.
    eapply t_tabs; [ |exact CT|exact CP| | | | |].
    + rewrite Len. now apply arena_raise_closed.
    + eapply arena_shift_q_fresh_bound; eassumption.
    + eapply arena_shift_qual_le; eassumption.
    + eapply arena_shift_qual_nonfresh; eassumption.
    + rewrite arena_raise_locs. rewrite Z. apply safety_empty_sep.
    + rewrite <- (arena_raise_open_named n Γ Δ _ Len).
      eapply IHHT; [exact HT| | | | | |].
      * apply arena_env_shift_cons; try eassumption. apply arena_env_shift_cons; eauto using arena_shift_all.
      * eapply arena_sub_abstract_wf; try eassumption; inversion H0; assumption.
      * now rewrite arena_open_named_locs.
      * rewrite Len. apply arena_shift_qual_join; [exact Y|].
        apply arena_shift_qual_join; [apply arena_shift_name_qual|].
        replace (S (n + length Γ)) with (n + S (length Γ)) by lia. apply arena_shift_name_qual.
      * eapply arena_shift_open_name_ty; eassumption.
      * apply arena_shift_open_name_qual; assumption.
  - change (local_locs t = ∅) in Z.
    destruct (arena_shift_ty_exists n T1) as [A HA].
    destruct (arena_shift_ty_exists n T2) as [B HB].
    set (g1 := arena_shift_qual n d1).
    set (g2 := arena_shift_qual n d2).
    set (gf := arena_shift_qual n df).
    assert (HG1 : arena_qual_shifted n d1 g1) by apply arena_shift_qual_spec.
    assert (HG2 : arena_qual_shifted n d2 g2) by apply arena_shift_qual_spec.
    assert (HGF : arena_qual_shifted n df gf) by apply arena_shift_qual_spec.
    eapply arena_shift_change_type with (T0 := B <~ᵀ TUnit ~ ∅ ; A ~ g1) (d0 := g2 <~ᵈ gf ; g1);
      [exact E|exact Horig|exact Z'|exact P| | |exact X|exact Y|].
    + eapply arena_shift_ty_open_result; eassumption.
    + now apply arena_shift_q_open_result.
    + simpl. eapply t_tapp; [| | | | | | | |].
      * eapply IHHT; try eassumption. now constructor.
      * eapply arena_shift_ty_at_env; eassumption.
      * eapply arena_shift_q_at_env; eassumption.
      * eapply (arena_shift_q_fresh_bound n (d2 <~ᵈ ∅ ; ∅)); [|exact P|eassumption].
        apply arena_shift_q_open_result; [exact HG2|apply arena_shift_empty|apply arena_shift_empty].
      * eapply arena_shift_qual_nonfresh; eassumption.
      * eapply arena_shift_qual_le; eassumption.
      * eapply arena_shift_ty_not_free; eassumption.
      * rewrite arena_raise_locs, Z. apply safety_empty_sep.
      * rewrite arena_raise_locs, Z. apply safety_empty_sep.
  - change (local_locs t = ∅) in Z.
    destruct (arena_shift_ty_exists n T1) as [A HA].
    destruct (arena_shift_ty_exists n T2) as [B HB].
    set (g1 := arena_shift_qual n d1).
    set (g2 := arena_shift_qual n d2).
    set (gf := arena_shift_qual n df).
    assert (HG1 : arena_qual_shifted n d1 g1) by apply arena_shift_qual_spec.
    assert (HG2 : arena_qual_shifted n d2 g2) by apply arena_shift_qual_spec.
    assert (HGF : arena_qual_shifted n df gf) by apply arena_shift_qual_spec.
    assert (Hdf : df ⊑↑ φ ⊔ {♦}) by exact (safety_typing_qual_bound _ _ _ _ _ _ HT).
    pose proof (arena_ordered_arena_closed_env _ _ W) as Ord.
    eapply arena_shift_change_type with (T0 := B <~ᵀ TUnit ~ ∅ ; A ~ g1) (d0 := g2 <~ᵈ gf ; g1);
      [exact E|exact Horig|exact Z'|exact P| | |exact X|exact Y|].
    + eapply arena_shift_ty_open_result; eassumption.
    + now apply arena_shift_q_open_result.
    + simpl. eapply t_tapp_fresh; [| | | | | | | | | |].
      * change (has_type Δ φ' Σ (arena_raise_tm n t)
            (if true then TAll (q_trans_tenv Δ gf ⋒ q_trans_tenv Δ g1) g2 A B else TFun ∅ ∅ A B) gf).
        eapply (arena_shift_fresh_call_domain true n Γ Δ Σ φ' df gf d1 g1 g2 A B);
          try eassumption.
        -- eapply (arena_shift_overlap_bound n Γ Δ df gf d1 g1); try eassumption.
           apply arena_shift_qual_spec.
        -- eapply IHHT; try eassumption.
           constructor; try assumption. apply arena_shift_qual_spec.
      * eapply arena_shift_ty_at_env; eassumption.
      * eapply arena_shift_q_at_env; eassumption.
      * eapply arena_shift_q_fresh_bound; eassumption.
      * intro Hfresh. eapply arena_shift_ty_not_free; [exact HB|].
        apply H2. eapply arena_shift_q_hasfresh; eassumption.
      * eapply arena_shift_ty_not_free; eassumption.
      * eapply (arena_shift_q_fresh_bound n (d2 <~ᵈ ∅ ; ∅)); [|exact P|eassumption].
        apply arena_shift_q_open_result; [exact HG2|apply arena_shift_empty|apply arena_shift_empty].
      * eapply safety_subq_trans.
        -- eapply (arena_shift_overlap_bound n Γ Δ d1 g1 df gf); try eassumption.
           apply arena_shift_qual_spec.
        -- eapply arena_shift_q_fresh_bound; [apply arena_shift_qual_spec|exact P|eassumption].
      * rewrite arena_raise_locs, Z. apply safety_empty_sep.
      * rewrite arena_raise_locs, Z. apply safety_empty_sep.
      * rewrite arena_raise_locs, Z. apply safety_empty_sep.
  - inversion X; subst T'.
    eapply arena_shift_change_type with (T0 := TUnit) (d0 := ∅);
      [exact E|exact Horig|exact Z'|exact P|constructor|apply arena_shift_empty|exact X|exact Y|].
    simpl. exact (t_base Δ Σ φ' CP).
  - destruct (proj2 E _ _ _ _ _ H) as (A & r & Hget & HA & HR).
    eapply arena_shift_change_type with (T0 := A) (d0 := $!(n+x));
        [exact E|exact Horig|exact Z'|exact P|exact HA|apply arena_shift_name_qual|exact X|exact Y|].
    change (has_type Δ φ' Σ (tvar (varF (n+x))) A $!(n+x)).
    eapply t_var; [exact Hget| |exact CP| |].
    + eapply arena_shift_qual_le; [apply arena_shift_name_qual|exact P|eassumption].
    + eapply arena_shift_ty_closed; eassumption.
    + eapply arena_shift_qual_closed; eassumption.
  - change (local_locs t = ∅) in Z.
    pose proof (arena_shift_ty_at_env _ _ _ _ _ _ _ E H0 X) as CT.
    inversion X; subst T'. simpl.
    eapply t_abs; [ |exact CT|exact CP| | | | |].
    + rewrite Len. now apply arena_raise_closed.
    + eapply arena_shift_q_fresh_bound; eassumption.
    + eapply arena_shift_qual_le; eassumption.
    + eapply arena_shift_qual_nonfresh; eassumption.
    + rewrite arena_raise_locs. rewrite Z. apply safety_empty_sep.
    + rewrite <- (arena_raise_open_named n Γ Δ _ Len).
      eapply IHHT; [exact HT| | | | | |].
      * apply arena_env_shift_cons; try eassumption. apply arena_env_shift_cons; eauto using arena_shift_fun.
      * eapply arena_sub_abstract_wf; try eassumption; inversion H0; assumption.
      * now rewrite arena_open_named_locs.
      * rewrite Len. apply arena_shift_qual_join; [exact Y|].
        apply arena_shift_qual_join; [apply arena_shift_name_qual|].
        replace (S (n + length Γ)) with (n + S (length Γ)) by lia. apply arena_shift_name_qual.
      * eapply arena_shift_open_name_ty; eassumption.
      * apply arena_shift_open_name_qual; assumption.
  - change ((local_locs t1 ⊔ local_locs t2) = ∅) in Z.
    destruct (arena_empty_join_parts _ _ Z) as [L1 L2]. subst φd.
    destruct (arena_shift_ty_exists n T1) as [A HA].
    destruct (arena_shift_ty_exists n T2) as [B HB].
    set (g1 := arena_shift_qual n d1).
    set (g2 := arena_shift_qual n d2).
    set (gf := arena_shift_qual n df).
    assert (HG1 : arena_qual_shifted n d1 g1) by apply arena_shift_qual_spec.
    assert (HG2 : arena_qual_shifted n d2 g2) by apply arena_shift_qual_spec.
    assert (HGF : arena_qual_shifted n df gf) by apply arena_shift_qual_spec.
    eapply arena_shift_change_type with (T0 := B <~ᵀ TUnit ~ ∅ ; A ~ g1) (d0 := g2 <~ᵈ gf ; g1);
      [exact E|exact Horig|exact Z'|exact P| | |exact X|exact Y|].
    + eapply arena_shift_ty_open_result; eassumption.
    + now apply arena_shift_q_open_result.
    + simpl. eapply t_app with (φd := qdiff φ' (local_locs (arena_raise_tm n t1)));
        [| | | | |reflexivity| |].
      * eapply IHHT1; try eassumption. now constructor.
      * eapply IHHT2; try eassumption.
        -- rewrite arena_raise_locs. rewrite L1.
           now apply arena_shift_diff_empty.
      * eapply (arena_shift_q_fresh_bound n (d2 <~ᵈ ∅ ; ∅)); [|exact P|eassumption].
        apply arena_shift_q_open_result; [exact HG2|apply arena_shift_empty|apply arena_shift_empty].
      * eapply arena_shift_qual_nonfresh; eassumption.
      * eapply arena_shift_ty_not_free; eassumption.
      * rewrite arena_raise_locs, L2. apply safety_empty_sep.
      * rewrite !arena_raise_locs, Z. apply safety_empty_sep.
  - change ((local_locs t1 ⊔ local_locs t2) = ∅) in Z.
    destruct (arena_empty_join_parts _ _ Z) as [L1 L2]. subst φd.
    destruct (arena_shift_ty_exists n T1) as [A HA].
    destruct (arena_shift_ty_exists n T2) as [B HB].
    set (g1 := arena_shift_qual n d1).
    set (g2 := arena_shift_qual n d2).
    set (gf := arena_shift_qual n df).
    assert (HG1 : arena_qual_shifted n d1 g1) by apply arena_shift_qual_spec.
    assert (HG2 : arena_qual_shifted n d2 g2) by apply arena_shift_qual_spec.
    assert (HGF : arena_qual_shifted n df gf) by apply arena_shift_qual_spec.
    assert (Hdf : df ⊑↑ φ ⊔ {♦}) by exact (safety_typing_qual_bound _ _ _ _ _ _ HT1).
    assert (Hd1 : d1 ⊑↑ φ ⊔ {♦})
      by exact (arena_sub_senv_bounds _ _ _ _ _ _ HT2 _ (safety_diff_le _ _)).
    pose proof (arena_ordered_arena_closed_env _ _ W) as Ord.
    eapply arena_shift_change_type with (T0 := B <~ᵀ TUnit ~ ∅ ; A ~ g1) (d0 := g2 <~ᵈ gf ; g1);
      [exact E|exact Horig|exact Z'|exact P| | |exact X|exact Y|].
    + eapply arena_shift_ty_open_result; eassumption.
    + now apply arena_shift_q_open_result.
    + simpl. eapply t_app_fresh with (φd := qdiff φ' (local_locs (arena_raise_tm n t1)));
        [| | | | | |reflexivity| | |].
      * change (has_type Δ φ' Σ (arena_raise_tm n t1)
            (if false then TAll ∅ ∅ A B else TFun (q_trans_tenv Δ gf ⋒ q_trans_tenv Δ g1) g2 A B) gf).
        eapply (arena_shift_fresh_call_domain false n Γ Δ Σ φ' df gf d1 g1 g2 A B);
          try eassumption.
        -- eapply (arena_shift_overlap_bound n Γ Δ df gf d1 g1); try eassumption.
           apply arena_shift_qual_spec.
        -- eapply IHHT1; try eassumption.
           constructor; try assumption. apply arena_shift_qual_spec.
        -- now rewrite arena_raise_locs.
      * eapply IHHT2; try eassumption.
        -- rewrite arena_raise_locs. rewrite L1.
           now apply arena_shift_diff_empty.
      * intro Hfresh. eapply arena_shift_ty_not_free; [exact HB|].
        apply H. exact (arena_shift_q_hasfresh _ _ _ HG1 Hfresh).
      * eapply arena_shift_ty_not_free; eassumption.
      * eapply (arena_shift_q_fresh_bound n (d2 <~ᵈ ∅ ; ∅)); [|exact P|eassumption].
        apply arena_shift_q_open_result; [exact HG2|apply arena_shift_empty|apply arena_shift_empty].
      * eapply safety_subq_trans.
        -- eapply (arena_shift_overlap_bound n Γ Δ d1 g1 df gf); try eassumption.
           apply arena_shift_qual_spec.
        -- eapply arena_shift_q_fresh_bound; [apply arena_shift_qual_spec|exact P|eassumption].
      * rewrite arena_raise_locs, L2. apply safety_empty_sep.
      * rewrite !arena_raise_locs, Z. apply safety_empty_sep.
      * rewrite arena_raise_locs, L1. apply safety_empty_sep.
  - assert (Hloc : closed_Qual 0 0 (length Σ) (&!l)↑).
    { destruct (safety_sindexr _ _ _ _ H0) as (s & Hs & _).
      apply safety_one_loc_closed. exact (safety_indexr_bound _ _ _ Hs). }
    pose proof (arena_shift_qual_rigid n _ _ _ Hloc) as HL.
    eapply arena_shift_change_type with (T0 := TRef q T) (d0 := &!l);
      [exact E|exact Horig|exact Z'|exact P| |exact HL|exact X|exact Y|].
    + constructor; [eapply arena_shift_qual_rigid|eapply arena_shift_ty_rigid]; eassumption.
    + simpl. apply t_loc; [exact CP| | | | |assumption].
      * assumption.
      * assumption.
      * assumption.
      * eapply arena_shift_qual_le; [exact HL|exact P|eassumption].
  - change (local_locs t = ∅) in Z.
    eapply arena_shift_change_type with (T0 := T') (d0 := {♦});
      [exact E|exact Horig|exact Z'|exact P|exact X|apply arena_shift_fresh|exact X|exact Y|].
    inversion X; subst T'. simpl. apply t_ref.
    + eapply IHHT; eassumption.
    + eapply arena_shift_ty_at_env; eassumption.
    + eapply arena_shift_qual_nonfresh; eassumption.
  - change ((local_locs t1 ⊔ local_locs t2) = ∅) in Z.
    destruct (arena_empty_join_parts _ _ Z) as [L1 L2]. subst φd.
    inversion X; subst T'.
    destruct (arena_shift_ty_exists n T1) as [ArenaType HAtarget].
    set (g := arena_shift_qual n d1).
    simpl. eapply t_refat with (φd := qdiff φ' (local_locs (arena_raise_tm n t2))) (T1 := ArenaType) (d1 := g);
      [| | |reflexivity|].
    + eapply IHHT1; try eassumption.
      * rewrite arena_raise_locs. rewrite L2. now apply arena_shift_diff_empty.
    + eapply arena_shift_qual_nonfresh; eassumption.
    + eapply IHHT2; try eassumption.
      constructor; [apply arena_shift_qual_spec|exact HAtarget].
    + rewrite arena_raise_locs, L1. apply safety_empty_sep.
  - change (local_locs t = ∅) in Z.
    simpl. eapply t_deref with (d := arena_shift_qual n d).
    + eapply IHHT; try eassumption.
      * now constructor.
      * apply arena_shift_qual_spec.
    + eapply arena_shift_qual_nonfresh; eassumption.
    + eapply arena_shift_qual_le; eassumption.
    + rewrite arena_raise_locs, Z. apply safety_empty_sep.
  - change ((local_locs t1 ⊔ local_locs t2) = ∅) in Z.
    destruct (arena_empty_join_parts _ _ Z) as [L1 L2]. subst φd.
    inversion X; subst T'.
    destruct (arena_shift_ty_exists n T) as [A HA].
    set (g1 := arena_shift_qual n d1).
    set (g := arena_shift_qual n d).
    eapply arena_shift_change_type with (T0 := TUnit) (d0 := ∅);
      [exact E|exact Horig|exact Z'|exact P|constructor|apply arena_shift_empty|exact X|exact Y|].
    simpl. eapply t_assign with (φd := qdiff φ' (local_locs (arena_raise_tm n t1)))
      (d := g) (d1 := g1) (T := A); [| | |reflexivity|].
    + eapply IHHT1; try eassumption.
      * constructor; [apply arena_shift_qual_spec|exact HA].
      * apply arena_shift_qual_spec.
    + eapply IHHT2; try eassumption.
      * rewrite arena_raise_locs. rewrite L1. now apply arena_shift_diff_empty.
      * apply arena_shift_qual_spec.
    + eapply arena_shift_qual_nonfresh; [apply arena_shift_qual_spec|eassumption].
    + rewrite arena_raise_locs, L2. apply safety_empty_sep.
  - destruct (arena_shift_ty_exists n T1) as [A HA].
    set (g := arena_shift_qual n d1).
    eapply t_sub with (T1 := A) (d1 := g).
    + eapply IHHT; try eassumption. apply arena_shift_qual_spec.
    + eapply arena_shift_stp; try eassumption. apply arena_shift_qual_spec.
    + eapply arena_shift_q_fresh_bound; eassumption.
    + rewrite Z'. apply safety_empty_sep.
  - change ((local_locs t1 ⊔ local_locs t2) = ∅) in Z.
    destruct (arena_empty_join_parts _ _ Z) as [L1 L2].
    destruct (arena_shift_ty_exists n T1) as [A HA].
    set (g := arena_shift_qual n d1).
    set (ψ := arena_shift_qual n φd).
    simpl. eapply t_withr with (φd := ψ) (T1 := A) (d1 := g).
    + eapply IHHT1; try eassumption. apply arena_shift_qual_spec.
    + eapply arena_shift_qual_nonfresh; [apply arena_shift_qual_spec|eassumption].
    + eapply arena_shift_ty_at_env; eassumption.
    + eapply arena_shift_q_at_env; eassumption.
    + match goal with Htm : closed_tm 2 (length Γ) (length Σ) t2 |- _ =>
        rewrite Len; exact (arena_raise_closed n _ _ _ _ Htm)
      end.
    + rewrite <- (arena_raise_open_named n Γ Δ _ Len).
      eapply IHHT2; [exact HT2| | | | | |].
      * apply arena_env_shift_cons; [apply arena_env_shift_cons; [exact E|constructor|apply arena_shift_fresh]| |apply arena_shift_fresh].
        constructor; [apply arena_shift_qual_spec|exact HA].
      * apply arena_closed_env_cons.
        -- apply arena_closed_env_cons; [exact W|constructor|apply safety_qual_const_closed].
        -- apply cl_TRef.
           eapply safety_ty_vars_weaken; [exact (safety_typing_type_closed _ _ _ _ _ _ HT1)|lia|simpl; lia].
           eapply safety_fv_closed_weaken; [|exact (safety_typing_qual_closed _ _ _ _ _ _ HT1)]; simpl; lia.
        -- apply safety_qual_const_closed.
      * now rewrite arena_open_named_locs.
      * rewrite Len. apply arena_shift_qual_join; [apply arena_shift_qual_spec|].
        replace (S (n+length Γ)) with (n+S (length Γ)) by lia. apply arena_shift_name_qual.
      * exact X.
      * exact Y.
    + eapply arena_shift_qual_le; [apply arena_shift_qual_spec|exact P|eassumption].
    + rewrite arena_raise_locs, L1. apply safety_empty_sep.
  - exfalso. exact (arena_empty_twithc _ _ Z).
Qed.

Local Lemma arena_lift_closed_typing Δ φ Σ v T d :
  has_type [] φ Σ v T d -> local_locs v = ∅ ->
  has_type Δ φ Σ v T d.
Proof.
  intros HT HL.
  pose proof (safety_typing_tm_closed _ _ _ _ _ _ HT) as CV.
  rewrite <- (arena_raise_rigid (length Δ) _ _ _ CV).
  eapply arena_has_type_raise_core; [exact HT|exact HT| |constructor|exact HL| | |].
  - split; [simpl; lia|intros x k b A q H; discriminate H].
  - eapply arena_shift_qual_rigid. exact (safety_typing_phi_closed _ _ _ _ _ _ HT).
  - eapply arena_shift_ty_rigid. exact (safety_typing_type_closed _ _ _ _ _ _ HT).
  - eapply arena_shift_qual_rigid. exact (safety_typing_qual_closed _ _ _ _ _ _ HT).
Qed.

Local Lemma arena_available_closed_value Δ φ ψ Σ v T d :
  has_type [] φ Σ v T d -> value v -> wf_step v ->
  closed_Qual 0 (length Δ) (length Σ) ψ↑ -> d ⊑↑ ψ ->
  has_type Δ ψ Σ v T d.
Proof.
  intros HT HV HW CP Hle.
  pose proof (safety_typing_qual_closed _ _ _ _ _ _ HT) as CD.
  set (p := (qfresh ψ,n_empty,n_empty,qlocs ψ)).
  assert (PC : closed_Qual 0 0 (length Σ) p↑).
  { unfold p. destruct CP as (_ & _ & HL). repeat split; try discriminate; exact HL. }
  assert (DP : d ⊑↑ p).
  { rewrite safety_qual_le in Hle |- *.
    unfold p. destruct Hle as (Hf & HF & HB & HL), CD as (CF & CB & CL).
    cbn in CF. repeat split; simpl; try assumption.
    - intros x Hx. specialize (CF x Hx). lia.
    - intros x Hx. specialize (CB x Hx). lia. }
  eapply safety_typing_scope_weaken.
  - apply arena_lift_closed_typing.
    + eapply safety_value_scope with (φ := φ); [reflexivity|exact HT|exact HV| |exact PC].
      now apply safety_le_fresh_variant.
    + now apply safety_value_scopes.
  - rewrite safety_qual_le. unfold p, n_sub, n_empty. cbn [qfresh qfvs qbvs qlocs fst snd]. intuition congruence.
  - exact CP.
Qed.

Local Definition arena_clear_fresh (q : qual) : qual :=
  if qfresh q then (false,qfvs q,qbvs q,qlocs q) else q.

Local Lemma arena_clear_nonfresh q : ♦∉ arena_clear_fresh q.
Proof. unfold arena_clear_fresh. destruct (qfresh q) eqn:H; simpl; try rewrite H; tauto. Qed.

Local Lemma arena_clear_locs q l : qlocs (arena_clear_fresh q) l = qlocs q l.
Proof. unfold arena_clear_fresh. now destruct (qfresh q). Qed.

Local Lemma arena_clear_le q : arena_clear_fresh q ⊑↑ q.
Proof.
  unfold arena_clear_fresh. destruct (qfresh q); [|apply safety_subq_refl].
  rewrite safety_qual_le.
  cbn [qfresh qfvs qbvs qlocs fst snd]. unfold n_sub. intuition congruence.
Qed.

Local Lemma arena_clear_lower_bound p q : ♦∉ p -> p ⊑↑ q -> p ⊑↑ arena_clear_fresh q.
Proof.
  unfold arena_clear_fresh. destruct (qfresh q); [|auto].
  intros NF H. rewrite safety_qual_le in H |- *.
  destruct H as (_ & HF & HB & HL).
  cbn [qfresh qfvs qbvs qlocs fst snd]. repeat split; try assumption.
  intro HP. exfalso. apply NF. now rewrite HP.
Qed.

Local Lemma arena_vtp_clear_fresh Σ φ v T d :
  vtp Σ ∅ φ v T d -> vtp Σ ∅ φ v T (arena_clear_fresh d).
Proof.
  intros HT. remember (∅ : qual) as K eqn:EK.
  induction HT; subst.
  - eapply vtp_tabs; try eassumption.
    + apply qs_sq; [apply arena_clear_lower_bound; eauto using safety_closed_qstp|].
      eapply safety_qual_closed_of_sub; [apply arena_clear_le|eauto using safety_qstp_closed].
    + apply safety_empty_sep.
    + eapply safety_sep_of_sub; [apply arena_clear_le|assumption].
  - constructor; [|apply safety_empty_sep].
    eapply safety_qual_closed_of_sub; [apply arena_clear_le|assumption].
  - eapply vtp_loc with (q1 := q1); try eassumption.
    + eapply safety_qual_closed_of_sub; [apply arena_clear_le|assumption].
    + apply qs_sq; [apply arena_clear_lower_bound; eauto using safety_closed_qstp, safety_nonfresh_loc|].
      eapply safety_qual_closed_of_sub; [apply arena_clear_le|assumption].
    + apply safety_empty_sep.
  - eapply vtp_abs; try eassumption.
    + eapply safety_qual_closed_of_sub; [apply arena_clear_le|assumption].
    + apply qs_sq; [apply arena_clear_lower_bound; eauto using safety_closed_qstp|].
      eapply safety_qual_closed_of_sub; [apply arena_clear_le|assumption].
    + apply safety_empty_sep.
    + eapply safety_sep_of_sub; [apply arena_clear_le|assumption].
  - eapply vtp_top. now apply IHHT.
Qed.

Local Lemma arena_typing_clear_fresh φ Σ v T d :
  has_type [] φ Σ v T d -> value v -> wf_step v ->
  has_type [] φ Σ v T (arena_clear_fresh d).
Proof.
  intros HT HV HW.
  eapply safety_vtp_typing with (ϰ := ∅).
  - apply arena_vtp_clear_fresh. eapply arena_value_vtp; eauto using safety_empty_sep.
  - apply safety_bound_without_fresh; [apply arena_clear_nonfresh|].
    eapply safety_subq_trans; [apply arena_clear_le|].
    exact (safety_typing_qual_bound _ _ _ _ _ _ HT).
  - exact (safety_typing_phi_closed _ _ _ _ _ _ HT).
  - exact HW.
Qed.

Local Definition arena_callable_type k :=
  match k with bind_tm => TFun | bind_ty => TAll end.

Local Definition arena_callable_term k :=
  match k with bind_tm => tabs | bind_ty => ttabs end.

Local Lemma arena_callable_closed k L p r A B :
  closed_ty 0 0 L (arena_callable_type k p r A B) ->
  closed_ty 0 0 L A /\ closed_ty 2 0 L B /\
  closed_Qual 0 0 L p↑ /\ closed_Qual 2 0 L r↑.
Proof. destruct k; simpl; intro H; inversion H; subst; auto. Qed.

Inductive arena_callable_view k Σ body p r A B df : Prop :=
| arena_callable_intro : forall T1 T2 d1 d2 df0,
  let self := arena_callable_type k d1 d2 T1 T2 in
  closed_tm 2 0 (length Σ) body ->
  closed_ty 0 0 (length Σ) self ->
  has_type [(k,false,T1,d1); (bind_tm,true,self,df0)]
    (df0 ⊔ $!0 ⊔ $!1) Σ (body <~²ᵗ ([] : tenv)) (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv)) ->
  stp [] Σ A p T1 d1 ->
  qstp [] Σ df0 df ->
  stp [(k,false,A,p); (bind_tm,true,self,{♦})] Σ
    (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv))
    (B <~²ᵀ ([] : tenv)) (r <~²ᵈ ([] : tenv)) ->
  d1 ⊑↑ df0 ⊔ {♦} -> ♦∉ df0 ->
  arena_callable_view k Σ body p r A B df.

Local Lemma arena_callable_inv k Σ φ body p r A B df :
  has_type [] φ Σ (arena_callable_term k body) (arena_callable_type k p r A B) df ->
  wf_step (arena_callable_term k body) ->
  arena_callable_view k Σ body p r A B df.
Proof.
  intros HT HW.
  assert (HV : value (arena_callable_term k body)) by (destruct k; constructor).
  pose proof (arena_value_vtp _ _ _ _ _ _ HT HV HW (safety_empty_sep df)) as H.
  destruct k; simpl in H; inversion H; subst; econstructor; eassumption.
Qed.

Local Lemma arena_callable_type_value k Σ φ body p r A B df :
  closed_tm 2 0 (length Σ) body ->
  closed_ty 0 0 (length Σ) (arena_callable_type k p r A B) ->
  closed_Qual 0 0 (length Σ) φ↑ ->
  p ⊑↑ df ⊔ {♦} -> df ⊑↑ φ -> ♦∉ df ->
  local_locs body = ∅ ->
  has_type [(k,false,A,p);(bind_tm,true,arena_callable_type k p r A B,df)]
    (df ⊔ $!0 ⊔ $!1) Σ (body <~²ᵗ ([] : tenv)) (B <~²ᵀ ([] : tenv)) (r <~²ᵈ ([] : tenv)) ->
  has_type [] φ Σ (arena_callable_term k body) (arena_callable_type k p r A B) df.
Proof.
  intros CT CS CP HB HD NF HL HT. destruct k.
  - apply t_abs; try assumption. now rewrite HL; apply safety_empty_sep.
  - apply t_tabs; try assumption. now rewrite HL; apply safety_empty_sep.
Qed.

Local Definition arena_first_type (df : qual) (T : ty) : ty :=
  T <~ᵀ TUnit ~ df ; (TVar (varF 0)) ~ $!0.

Local Lemma arena_beta_first_images L df T q :
  closed_Qual 0 0 L df↑ -> ♦∉ df -> closed_ty 2 0 L T -> closed_Qual 2 0 L q↑ ->
  arena_ty_substitution TUnit df (T <~²ᵀ ([] : tenv)) (arena_first_type df T) /\
  arena_qual_substitution df (q <~²ᵈ ([] : tenv)) (q <~ᵈ df ; $!0).
Proof.
  intros Cdf NF CT CQ. split.
  - unfold open_ty', arena_first_type, open_ty. cbn [length].
    eapply arena_tsub_open with (L := L); [constructor| |constructor|apply arena_qsub_name].
    eapply arena_tsub_open with (L := L).
    + constructor.
    + eapply arena_tsub_rigid. exact CT.
    + constructor.
    + eapply arena_qsub_zero; eassumption.
  - unfold openq'; cbn [length].
    apply arena_sub_qual_open_result.
    + eapply arena_qsub_rigid. exact CQ.
    + eapply arena_qsub_zero; eassumption.
    + apply arena_qsub_name.
Qed.

Local Lemma arena_beta_second_images L df A δ T q :
  closed_ty 0 0 L A -> closed_Qual 0 0 L df↑ ->
  closed_Qual 0 0 L δ↑ -> ♦∉ δ -> closed_ty 2 0 L T -> closed_Qual 2 0 L q↑ ->
  arena_ty_substitution A δ (arena_first_type df T) (T <~ᵀ TUnit ~ df ; A ~ δ) /\
  arena_qual_substitution δ (q <~ᵈ df ; $!0) (q <~ᵈ df ; δ).
Proof.
  intros CA Cdf Cδ NF CT CQ. split.
  - unfold arena_first_type, open_ty.
    eapply arena_tsub_open with (L := L); [exact CA| |constructor|eapply arena_qsub_zero; eassumption].
    eapply arena_tsub_open with (L := L); [exact CA| |constructor|].
    + eapply arena_tsub_rigid. exact CT.
    + eapply arena_qsub_rigid. exact Cdf.
  - apply arena_sub_qual_open_result.
    + eapply arena_qsub_rigid. exact CQ.
    + eapply arena_qsub_rigid. exact Cdf.
    + eapply arena_qsub_zero; eassumption.
Qed.

Local Lemma arena_open_arg_mono k q a b :
  a ⊑↑ b -> open_qual k a q ⊑↑ open_qual k b q.
Proof.
  intro H. unfold open_qual. destruct (qbvs q k); [|apply safety_subq_refl].
  apply safety_join_bound; [apply safety_join_l|].
  eapply safety_subq_trans; [exact H|apply safety_join_r].
Qed.

Local Lemma arena_open_args_mono q a a' b b' :
  a ⊑↑ a' -> b ⊑↑ b' -> (q <~ᵈ a ; b) ⊑↑ (q <~ᵈ a' ; b').
Proof.
  intros HA HB. unfold openq. eapply safety_subq_trans.
  - apply safety_q_open_mono, arena_open_arg_mono. exact HA.
  - now apply arena_open_arg_mono.
Qed.

Local Lemma arena_beta_result_type df A d B :
  not_free 0 B -> (♦∈ d -> not_free 1 B) ->
  (B <~ᵀ TUnit ~ df ; A ~ (arena_clear_fresh d)) =
  (B <~ᵀ TUnit ~ ∅ ; A ~ d).
Proof.
  intros H0 H1. unfold open_ty.
  rewrite (safety_not_free_open B 0 TUnit df H0),
    (safety_not_free_open B 0 TUnit ∅ H0).
  destruct (qfresh d) eqn:HD.
  - assert (HB : not_free 1 B).
    { apply H1. exact I. }
    rewrite !safety_not_free_open by exact HB. reflexivity.
  - unfold arena_clear_fresh. now rewrite HD.
Qed.

Local Lemma arena_two_bindings_closed Σ k A p S df :
  closed_ty 0 0 (length Σ) A -> closed_Qual 0 0 (length Σ) p↑ ->
  closed_ty 0 0 (length Σ) S -> closed_Qual 0 0 (length Σ) df↑ ->
  arena_closed_env [(k,false,A,p);(bind_tm,true,S,df)] Σ.
Proof.
  intros CA CP CS CD. constructor.
  - now constructor; [constructor| |].
  - eapply safety_ty_vars_weaken; [exact CA|lia|simpl; lia].
  - eapply safety_fv_closed_weaken; [|exact CP]; simpl; lia.
Qed.

Local Lemma arena_beta_runtime_scopes k body v :
  wf_step (arena_callable_term k body) -> value v -> wf_step v ->
  local_locs (body <~ᵗ (arena_callable_term k body) ; v) = ∅.
Proof.
  intros HW HV WV.
  assert (HB : local_locs body = ∅) by (destruct k; exact HW).
  unfold open_tm. rewrite !safety_open_scopes.
  - exact HB.
  - destruct k; exact HW.
  - now apply safety_value_scopes.
Qed.

Local Lemma arena_arg_binding Σ k A p δ B q :
  stp [] Σ A p B q -> (♦∉ q -> δ ⊑↑ q) ->
  arena_substitution_binding Σ A δ (k,false,B,q).
Proof.
  intros HT HD. cbn. split; [exact HD|].
  split; [discriminate|intros _ _].
  eapply safety_stp_requalify; [exact HT|].
  apply qs_sq; [apply safety_subq_refl|apply safety_qual_const_closed].
Qed.

Local Lemma arena_closed_value_sub_data Σ φ U δ k b A q v :
  closed_ty 0 0 (length Σ) U ->
  closed_Qual 0 0 (length Σ) δ↑ -> ♦∉ δ -> arena_substitution_binding Σ U δ (k,b,A,q) ->
  closed_tm 0 0 (length Σ) v -> local_locs v = ∅ ->
  (k = bind_tm -> has_type [] φ Σ v A δ /\ value v /\ wf_step v) ->
  arena_substitution_data Σ Σ U δ v (k,b,A,q).
Proof.
  intros CU CD NF HB CV HL HV. constructor; try assumption.
  - apply safety_senv_refl.
  - cbn. intros HK Γ ψ CP HD.
    destruct (HV HK) as (HT & VV & WV).
    eapply arena_available_closed_value; eassumption.
Qed.

(* Substitute self before the argument to match the order of operational opening. *)
Local Lemma arena_beta_original_body k Σ φ body v A T1 T2 d1 d2 df δ :
  let F := arena_callable_term k body in
  let S := arena_callable_type k d1 d2 T1 T2 in
  let a := (k,false,T1,d1) in
  closed_tm 2 0 (length Σ) body ->
  closed_ty 0 0 (length Σ) S ->
  has_type [a;(bind_tm,true,S,df)] (df ⊔ $!0 ⊔ $!1) Σ
    (body <~²ᵗ ([] : tenv)) (T2 <~²ᵀ ([] : tenv)) (d2 <~²ᵈ ([] : tenv)) ->
  has_type [] φ Σ F S df -> wf_step F -> df ⊑↑ φ -> ♦∉ df ->
  closed_Qual 0 0 (length Σ) φ↑ -> δ ⊑↑ φ ->
  arena_substitution_data Σ Σ A δ v a ->
  (forall l, qlocs δ l = true -> qlocs d1 l = false -> qlocs df l = false) ->
  has_type [] φ Σ (body <~ᵗ F ; v)
    (T2 <~ᵀ TUnit ~ df ; A ~ δ) (d2 <~ᵈ df ; δ).
Proof.
  cbn zeta. set (F := arena_callable_term k body).
  set (S := arena_callable_type k d1 d2 T1 T2).
  set (a := (k,false,T1,d1)).
  set (self := (bind_tm,true,S,df)).
  intros CB CS HB HF WF Hdf NF CP HD D G.
  destruct (arena_callable_closed _ _ _ _ _ _ CS) as (CT1 & CT2 & CD1 & CD2).
  pose proof (safety_typing_qual_closed _ _ _ _ _ _ HF) as Cdf.
  assert (CF : closed_tm 0 0 (length Σ) F) by (destruct k; constructor; exact CB).
  assert (VF : value F) by (destruct k; constructor).
  assert (LF : local_locs F = ∅) by now apply safety_value_scopes.
  assert (LB : local_locs body = ∅) by (destruct k; exact WF).
  assert (Dself : arena_substitution_data Σ Σ TUnit df F self).
  { unfold self. eapply arena_closed_value_sub_data with (φ := φ); try assumption.
    - constructor.
    - cbn. split; [intros _; apply safety_subq_refl|]. split; [intros _ _; apply safety_subq_refl|discriminate].
    - auto. }
  assert (E : arena_env_substitution TUnit df self [a;self] [a]).
  { unfold a. apply arena_env_sub_cons; [apply arena_env_sub_base| |].
    - eapply arena_tsub_rigid. exact CT1.
    - eapply arena_qsub_rigid. exact CD1. }
  destruct (arena_beta_first_images _ _ _ _ Cdf NF CT2 CD2) as (X1 & Y1).
  set (b := body <~²ᵗ ([] : tenv)).
  assert (L0 : local_locs b = ∅) by (unfold b; rewrite arena_open_named_locs; exact LB).
  assert (H1 : has_type [a] (df ⊔ df ⊔ $!0) Σ (subst_tm b 0 F)
    (arena_first_type df T2) (d2 <~ᵈ df ; $!0)).
  { eapply arena_has_type_substitute; [exact HB|exact Dself|exact E| | |exact L0| |exact X1|exact Y1].
    - unfold a, self. apply arena_two_bindings_closed; assumption.
    - intros l Htrue Hfalse. change (qlocs df l = false) in Hfalse. congruence.
    - repeat apply arena_qsub_join.
      + eapply arena_qsub_rigid. exact Cdf.
      + eapply arena_qsub_zero; eassumption.
      + apply arena_qsub_name. }
  pose proof (arena_sub_U_closed _ _ _ _ _ _ D) as CA.
  pose proof (arena_sub_delta_closed _ _ _ _ _ _ D) as CD.
  pose proof (arena_sub_delta_nonfresh _ _ _ _ _ _ D) as ND.
  destruct (arena_beta_second_images _ _ _ _ _ _ CA Cdf CD ND CT2 CD2) as (X2 & Y2).
  assert (H2 : has_type [] (df ⊔ df ⊔ δ) Σ (subst_tm (subst_tm b 0 F) 0 v)
    (T2 <~ᵀ TUnit ~ df ; A ~ δ) (d2 <~ᵈ df ; δ)).
  { eapply arena_has_type_substitute; [exact H1|exact D|apply arena_env_sub_base| | | | |exact X2|exact Y2].
    - unfold a. constructor; [constructor|exact CT1|exact CD1].
    - intros l HT HL. change (qlocs d1 l = false) in HL.
      specialize (G l HT HL). split.
      + change (qlocs df l || (qlocs df l || false) = false).
        now rewrite G.
      + intros x e HE. simpl in HE. destruct (x =? 0); [|discriminate].
        inversion HE; exact HL.
    - eapply arena_sub_locs_typing_unchanged; eassumption.
    - repeat apply arena_qsub_join.
      + eapply arena_qsub_rigid. exact Cdf.
      + eapply arena_qsub_rigid. exact Cdf.
      + eapply arena_qsub_zero; eassumption. }
  unfold b in H2.
  rewrite (arena_double_inst_tm body F v (length Σ) (length Σ) CB CF
    (arena_sub_term_closed _ _ _ _ _ _ D)), (arena_sub_tm_no_free _ _ _ _ CF) in H2.
  apply (safety_typing_scope_weaken _ _ _ _ _ _ H2); [|exact CP].
  repeat apply safety_join_bound; assumption.
Qed.

(* Apply the same openings to the return-type subtyping derivation. *)
Local Lemma arena_beta_covariance Σ k A p S df δ T q B r :
  closed_ty 0 0 (length Σ) A -> closed_Qual 0 0 (length Σ) p↑ ->
  closed_Qual 0 0 (length Σ) df↑ -> ♦∉ df ->
  closed_Qual 0 0 (length Σ) δ↑ -> ♦∉ δ ->
  closed_ty 2 0 (length Σ) T -> closed_Qual 2 0 (length Σ) q↑ ->
  closed_ty 2 0 (length Σ) B -> closed_Qual 2 0 (length Σ) r↑ ->
  (♦∉ p -> δ ⊑↑ p) ->
  stp [(k,false,A,p);(bind_tm,true,S,{♦})] Σ
    (T <~²ᵀ ([] : tenv)) (q <~²ᵈ ([] : tenv))
    (B <~²ᵀ ([] : tenv)) (r <~²ᵈ ([] : tenv)) ->
  stp [] Σ (T <~ᵀ TUnit ~ df ; A ~ δ) (q <~ᵈ df ; δ)
    (B <~ᵀ TUnit ~ df ; A ~ δ) (r <~ᵈ df ; δ).
Proof.
  intros CA CP Cdf NF Cδ Nδ CT CQ CB CR HP HS.
  destruct (arena_beta_first_images _ _ _ _ Cdf NF CT CQ) as (X1 & Y1).
  destruct (arena_beta_first_images _ _ _ _ Cdf NF CB CR) as (X1' & Y1').
  destruct (arena_beta_second_images _ _ _ _ _ _ CA Cdf Cδ Nδ CT CQ) as (X2 & Y2).
  destruct (arena_beta_second_images _ _ _ _ _ _ CA Cdf Cδ Nδ CB CR) as (X2' & Y2').
  set (a := (k,false,A,p)).
  set (self := (bind_tm,true,S,{♦})).
  assert (E1 : arena_env_substitution TUnit df self [a;self] [a]).
  { unfold a. apply arena_env_sub_cons; [apply arena_env_sub_base| |].
    - eapply arena_tsub_rigid. exact CA.
    - eapply arena_qsub_rigid. exact CP. }
  assert (B1 : arena_substitution_binding Σ TUnit df self).
  { unfold self. cbn. split; [intros H; exfalso; apply H; exact I|].
    split; [intros _ H; exfalso; apply H; exact I|discriminate]. }
  pose proof (arena_stp_substitute _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS E1 B1
    ltac:(constructor) Cdf NF X1 X1' Y1 Y1') as H1.
  assert (B2 : arena_substitution_binding Σ A δ a).
  { unfold a. eapply arena_arg_binding; [|exact HP].
    apply safety_stp_refl; [exact CA|].
    apply qs_sq; [apply safety_subq_refl|exact CP]. }
  eapply arena_stp_substitute; [exact H1|apply arena_env_sub_base|exact B2|
    exact CA|exact Cδ|exact Nδ|exact X2|exact X2'|exact Y2|exact Y2'].
Qed.

Local Lemma arena_beta_apply k Σ φ body A B p r df v d :
  has_type [] φ Σ (arena_callable_term k body) (arena_callable_type k p r A B) df ->
  wf_step (arena_callable_term k body) ->
  (match k with
   | bind_tm => has_type [] φ Σ v A d /\ value v /\ wf_step v
   | bind_ty => v = tunit
   end) ->
  closed_Qual 0 0 (length Σ) d↑ ->
  d ⊑↑ φ ⊔ {♦} ->
  (♦∉ p -> d ⊑↑ p) ->
  (forall l, qlocs df l = true -> qlocs d l = true -> qlocs p l = true) ->
  not_free 0 B -> (♦∈ d -> not_free 1 B) ->
  (r <~ᵈ ∅ ; ∅) ⊑↑ φ ⊔ {♦} ->
  has_type [] φ Σ (body <~ᵗ (arena_callable_term k body) ; v)
    (B <~ᵀ TUnit ~ ∅ ; A ~ d) (r <~ᵈ df ; d).
Proof.
  intros HF WF HV CD HD HP Hcap Free0 Free1 HR.
  destruct (arena_callable_inv _ _ _ _ _ _ _ _ _ HF WF)
    as [T1 T2 d1 d2 df0 Self CB CS HB HA HQ HC Hbound NF].
  unfold Self in CS, HB, HC.
  pose proof (safety_typing_phi_closed _ _ _ _ _ _ HF) as Cφ.
  pose proof (safety_typing_qual_bound _ _ _ _ _ _ HF) as Hdf.
  pose proof (safety_typing_type_closed _ _ _ _ _ _ HF) as CPub.
  destruct (arena_callable_closed _ _ _ _ _ _ CPub) as (CA & CRes & CP & CR).
  destruct (arena_callable_closed _ _ _ _ _ _ CS) as (_ & CT2 & _ & CD2).
  pose proof (safety_closed_qstp _ _ _ HQ) as Qle.
  assert (DF : df0 ⊑↑ φ).
  { apply safety_bound_without_fresh; [exact NF|].
    eapply safety_subq_trans; eassumption. }
  assert (Cdf : closed_Qual 0 0 (length Σ) df0↑)
    by (eapply safety_qual_closed_of_sub; eassumption).
  set (F := arena_callable_term k body).
  assert (DFtyp : has_type [] φ Σ F (arena_callable_type k d1 d2 T1 T2) df0).
  { apply arena_callable_type_value; try assumption. destruct k; exact WF. }
  set (δ := arena_clear_fresh d).
  assert (Cδ : closed_Qual 0 0 (length Σ) δ↑)
    by (eapply safety_qual_closed_of_sub; [apply arena_clear_le|exact CD]).
  assert (Nδ : ♦∉ δ) by apply arena_clear_nonfresh.
  assert (Hδ : δ ⊑↑ φ).
  { apply safety_bound_without_fresh; [exact Nδ|].
    eapply safety_subq_trans; [apply arena_clear_le|exact HD]. }
  pose proof (safety_subqual_of_stp _ _ _ _ _ HA) as AP.
  assert (BP : ♦∉ p -> δ ⊑↑ p)
    by (intro H; eapply safety_subq_trans; [apply arena_clear_le|auto]).
  assert (BD : ♦∉ d1 -> δ ⊑↑ d1).
  { intro N. eapply safety_subq_trans; [apply BP|exact AP].
    intro P. apply N. apply safety_qual_le in AP as (H & _).
    assert (PE : qfresh p = true) by (destruct (qfresh p); [reflexivity|contradiction]).
    specialize (H PE). rewrite H. exact I. }
  assert (AB : arena_substitution_binding Σ A δ (k,false,T1,d1)).
  { eapply arena_arg_binding; [exact HA|exact BD]. }
  assert (VB : value v /\ wf_step v /\ closed_tm 0 0 (length Σ) v).
  { destruct k; simpl in HV.
    - destruct HV as (HT & V & W). repeat split; try assumption.
      exact (safety_typing_tm_closed _ _ _ _ _ _ HT).
    - subst v; repeat split; constructor. }
  destruct VB as (V & W & CV).
  assert (D : arena_substitution_data Σ Σ A δ v (k,false,T1,d1)).
  { eapply arena_closed_value_sub_data with (φ := φ); try assumption.
    - now apply safety_value_scopes.
    - intros K. subst k. destruct HV as (HT & _ & _). split; [|auto].
      eapply t_sub.
      + exact (arena_typing_clear_fresh φ Σ v A d HT V W).
      + eapply safety_stp_requalify; [exact HA|].
        apply qs_sq; [apply safety_subq_refl|exact Cδ].
      + now apply safety_le_fresh_variant.
      + rewrite (safety_value_scopes _ V W). apply safety_empty_sep. }
  assert (G : forall l, qlocs δ l = true -> qlocs d1 l = false -> qlocs df0 l = false).
  { intros l Hδl Hd1. unfold δ in Hδl. rewrite arena_clear_locs in Hδl.
    destruct (qlocs df0 l) eqn:Hdf0; [exfalso|reflexivity].
    apply safety_qual_le in Qle as (_ & _ & _ & HQl).
    apply safety_qual_le in AP as (_ & _ & _ & HPl).
    specialize (HPl l (Hcap l (HQl l Hdf0) Hδl)). congruence. }
  pose proof (arena_beta_original_body k Σ φ body v A T1 T2 d1 d2 df0 δ
    CB CS HB DFtyp WF DF NF Cφ Hδ D G) as Hbody.
  pose proof (arena_beta_covariance Σ k A p _ df0 δ T2 d2 B r
    CA CP Cdf NF Cδ Nδ CT2 CD2 CRes CR BP HC) as Hstp.
  assert (Bound : (r <~ᵈ df ; d) ⊑↑ φ ⊔ {♦})
    by (apply safety_openq2_bound; assumption).
  rewrite <- (arena_beta_result_type df0 A d B Free0 Free1).
  eapply t_sub; [exact Hbody| |exact Bound|].
  - eapply s_trans; [exact Hstp|].
    apply safety_stp_refl.
    + exact (proj2 (safety_stp_closed _ _ _ _ _ _ Hstp)).
    + apply qs_sq.
      * apply arena_open_args_mono; [exact Qle|apply arena_clear_le].
      * eapply safety_qual_closed_of_sub; [exact Bound|].
        apply safety_qual_join_closed; [exact Cφ|apply safety_qual_const_closed].
  - change (kill_sep (local_locs (body <~ᵗ (arena_callable_term k body) ; v)) (r <~ᵈ df ; d)).
    rewrite (arena_beta_runtime_scopes k body v WF V W). apply safety_empty_sep.
Qed.

Local Lemma arena_exact_call_overlap (df d : qual) l :
  qlocs df l = true -> qlocs d l = true -> qlocs d l = true.
Proof. auto. Qed.

Local Lemma arena_fresh_call_bound df d :
  ♦∉ (q_trans_tenv [] df ⋒ q_trans_tenv [] d) -> d ⊑↑ (q_trans_tenv [] df ⋒ q_trans_tenv [] d).
Proof.
  intro H. exfalso. apply H. change (Is_true ((qfresh df && qfresh d) || true)).
  now rewrite orb_true_r.
Qed.

Local Lemma arena_fresh_call_overlap df d l :
  qlocs df l = true -> qlocs d l = true ->
  qlocs (q_trans_tenv [] df ⋒ q_trans_tenv [] d) l = true.
Proof.
  intros HF HD. change ((qlocs df l && qlocs d l) || false = true).
  now rewrite HF, HD.
Qed.

Local Lemma arena_call_arg_scope Σ φ t v A p df d r B :
  has_type [] φ Σ t (TFun p r A B) df ->
  has_type [] (qdiff φ (local_locs t)) Σ v A d -> has_type [] φ Σ v A d.
Proof.
  intros HT HV. apply (safety_typing_scope_weaken _ _ _ _ _ _ HV).
  - apply safety_diff_le.
  - exact (safety_typing_phi_closed _ _ _ _ _ _ HT).
Qed.

Local Lemma arena_type_beta Σ φ body T q :
  has_type [] φ Σ (ttapp (ttabs body)) T q -> wf_step (ttabs body) ->
  has_type [] φ Σ (body <~ᵗ (ttabs body) ; tunit) T q.
Proof.
  intro HT. remember ([] : tenv) as Γ eqn:EG.
  remember (ttapp (ttabs body)) as src eqn:ET.
  induction HT; subst Γ; inversion ET; subst; try clear ET; intros WF.
  - eapply arena_beta_apply with (k := bind_ty) (p := d1);
      try eassumption; try reflexivity.
    + now apply safety_le_fresh_variant.
    + intros _; apply safety_subq_refl.
    + apply arena_exact_call_overlap.
    + contradiction.
  - eapply arena_beta_apply with (k := bind_ty) (p := q_trans_tenv [] df ⋒ q_trans_tenv [] d1);
      try eassumption; try reflexivity.
    + apply arena_fresh_call_bound.
    + apply arena_fresh_call_overlap.
  - eapply t_sub; [eapply IHHT; eauto|eassumption|eassumption|].
    change (kill_sep (local_locs (body <~ᵗ arena_callable_term bind_ty body ; tunit)) d2).
    rewrite (arena_beta_runtime_scopes bind_ty body tunit WF ltac:(constructor) I).
    apply safety_empty_sep.
Qed.

Local Lemma arena_term_beta Σ φ body v T q :
  value v -> has_type [] φ Σ (tapp (tabs body) v) T q -> wf_step (tapp (tabs body) v) ->
  has_type [] φ Σ (body <~ᵗ (tabs body) ; v) T q.
Proof.
  intros V HT. remember ([] : tenv) as Γ eqn:EG.
  remember (tapp (tabs body) v) as src eqn:ET.
  induction HT; subst Γ; inversion ET; subst; try clear ET; intros (WF & WV & _).
  - assert (AV : has_type [] φ Σ v T1 d1) by (eapply arena_call_arg_scope; eassumption).
    eapply arena_beta_apply with (k := bind_tm) (p := d1); try eassumption.
    + simpl; auto.
    + exact (safety_typing_qual_closed _ _ _ _ _ _ AV).
    + exact (safety_typing_qual_bound _ _ _ _ _ _ AV).
    + intros _; apply safety_subq_refl.
    + apply arena_exact_call_overlap.
    + contradiction.
  - assert (AV : has_type [] φ Σ v T1 d1) by (eapply arena_call_arg_scope; eassumption).
    eapply arena_beta_apply with (k := bind_tm) (p := q_trans_tenv [] df ⋒ q_trans_tenv [] d1);
      try eassumption.
    + simpl; auto.
    + exact (safety_typing_qual_closed _ _ _ _ _ _ AV).
    + exact (safety_typing_qual_bound _ _ _ _ _ _ AV).
    + apply arena_fresh_call_bound.
    + apply arena_fresh_call_overlap.
  - eapply t_sub.
    + eapply IHHT; try reflexivity. split; [exact WF|]. split; [exact WV|left; constructor].
    + eassumption.
    + eassumption.
    + change (kill_sep (local_locs (body <~ᵗ arena_callable_term bind_tm body ; v)) d2).
      rewrite (arena_beta_runtime_scopes bind_tm body v WF V WV).
      apply safety_empty_sep.
Qed.

Local Lemma arena_beta_substitution_proved : safety_beta_substitution.
Proof. split; [exact arena_type_beta|exact arena_term_beta]. Qed.

Theorem type_safety: forall {Σ ϰ t T d φ},
  has_type [] φ Σ t T d -> wf_senv Σ -> wf_step t -> (
    value t \/
    (forall {σ} , CtxOK [] φ Σ ϰ σ -> wf_store σ ->
      (exists t' σ',
        step t σ t' σ' /\ preserve [] Σ ϰ φ (local_locs t) t' T d σ'
      )
    )
  ).
Proof.
  exact (@safety_type_safety_from_substitution
    arena_value_storage_proved arena_beta_substitution_proved arena_arena_substitution_proved).
Qed.
