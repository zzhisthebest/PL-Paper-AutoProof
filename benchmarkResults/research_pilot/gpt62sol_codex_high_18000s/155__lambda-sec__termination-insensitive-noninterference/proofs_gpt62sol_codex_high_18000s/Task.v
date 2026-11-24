From stdpp Require Import gmap fin_maps.
From stdpp Require Import relations.

From logrel_ifc.lambda_sec Require Export lang typing.

From logrel_ifc.lambda_sec Require Import lattice.

From Stdlib Require Import Lia.

Local Notation "'run' n e s v t" :=
  (nsteps pstep n (e, s) (#v, t)) (at level 10, n, e, s, v, t at next level).

Lemma tini_to_of v : to_val (#v) = Some v.
Proof. induction v; simpl; by repeat (rewrite ?IHv, ?IHv1, ?IHv2). Qed.

Lemma tini_of_to e v : to_val e = Some v → e = #v.
Proof.
  revert v. induction e; intros v Hv; simpl in Hv; try discriminate;
    repeat match type of Hv with
    | context [to_val ?e] =>
      let q := fresh "q" in let Hq := fresh in
      destruct (to_val e) as [q|] eqn:Hq; simpl in Hv; try discriminate
    end;
    inversion Hv; subst; simpl; f_equal; eauto.
Qed.

Lemma tini_item_val K e v :
  to_val (fill_item K e) = Some v → ∃ w, to_val e = Some w.
Proof.
  destruct K; simpl; try discriminate;
    destruct (to_val e) eqn:He; eauto;
    try (rewrite tini_to_of; simpl); discriminate.
Qed.

Lemma tini_fill_val K e v :
  to_val (fill K e) = Some v → ∃ w, to_val e = Some w.
Proof.
  revert e. induction K as [|K Ks IH]; simpl; eauto.
  intros e [w Hw]%IH. by eapply tini_item_val.
Qed.

Lemma tini_head_nonval e s e' s' k ef :
  head_step e s k e' s' ef → to_val e = None.
Proof. by destruct 1. Qed.

Lemma tini_head_item K e s e' s' k ef :
  head_step (fill_item K e) s k e' s' ef → ∃ w, to_val e = Some w.
Proof.
  destruct K; simpl; inversion 1; subst; simpl;
    repeat match goal with H : to_val _ = Some _ |- _ => rewrite H; clear H end;
    eauto.
Qed.

Lemma tini_item_unique K K' e e' :
  to_val e = None → to_val e' = None →
  fill_item K e = fill_item K' e' → K = K' ∧ e = e'.
Proof.
  intros H H'. destruct K, K'; simpl; intros E; inversion E; subst;
    try (rewrite tini_to_of in H || rewrite tini_to_of in H'; discriminate);
    auto.
  all: repeat match goal with E : #_ = #_ |- _ =>
    apply (f_equal to_val) in E; rewrite !tini_to_of in E; injection E as <-
  end; auto.
Qed.

Lemma tini_fill_snoc K Ks e :
  fill (Ks ++ [K]) e = fill_item K (fill Ks e).
Proof. revert e. induction Ks; simpl; auto. Qed.

Lemma tini_step_nonval e s e' s' : pstep (e,s) (e',s') → to_val e = None.
Proof.
  intros H. inversion H as [K a b E _ Hhead]; simpl in E; subst e.
  destruct (to_val (fill K a)) eqn:E; last done.
  apply tini_fill_val in E as [w Hw].
  rewrite (tini_head_nonval _ _ _ _ _ _ Hhead) in Hw. discriminate.
Qed.

Lemma tini_step_item K e s z t :
  to_val e = None →
  pstep (fill_item K e,s) (z,t) →
  ∃ e', z = fill_item K e' ∧ pstep (e,s) (e',t).
Proof.
  intros H Hstep. inversion Hstep as [Ks a b E Ez Hhead]; simpl in *; subst z.
  destruct Ks as [|K' Ks] using rev_ind.
  - simpl in E. rewrite <- E in Hhead.
    apply tini_head_item in Hhead as [? Hw]. congruence.
  - rewrite !tini_fill_snoc in *.
    assert (to_val (fill Ks a) = None) as H'.
    { destruct (to_val (fill Ks a)) eqn:Ev; last done.
      apply tini_fill_val in Ev as [w Hw].
      rewrite (tini_head_nonval _ _ _ _ _ _ Hhead) in Hw. discriminate. }
    destruct (tini_item_unique _ _ _ _ H H' E) as [-> ->].
    exists (fill Ks b). split; first done. econstructor; simpl; eauto.
Qed.

Local Lemma tini_run_zero e s v t : run 0 e s v t → (#v,t) = (e,s).
Proof. inversion 1; congruence. Qed.

Lemma tini_run_value n v s w t :
  run n (#v) s w t → n = 0 ∧ w = v ∧ t = s.
Proof.
  intros H. destruct n.
  - apply tini_run_zero in H. simpl in H. injection H as E <-.
    split; first done. split; last done.
    by apply (f_equal to_val) in E; rewrite !tini_to_of in E; inversion E.
  - inversion H as [|? ? [e u] ? Hstep ?]; subst.
    apply tini_step_nonval in Hstep. rewrite tini_to_of in Hstep. discriminate.
Qed.

Lemma tini_run_item n K e s v t :
  run n (fill_item K e) s v t →
  ∃ i j w u, n = i + j ∧ run i e s w u ∧ run j (fill_item K (#w)) u v t.
Proof.
  revert e s. induction n as [|n IH]; intros e s Hr.
  - destruct (to_val e) as [w|] eqn:He.
    + apply tini_of_to in He; subst e. exists 0, 0, w, s. repeat split; [constructor|exact Hr].
    + apply tini_run_zero in Hr. injection Hr as E _.
      assert (to_val (fill_item K e) = Some v) as Hv by (by rewrite <- E, tini_to_of).
      apply tini_item_val in Hv as [? Hw]. congruence.
  - destruct (to_val e) as [w|] eqn:He.
    + apply tini_of_to in He; subst e. exists 0, (S n), w, s. repeat split; [constructor|exact Hr].
    + inversion Hr as [|? ? [z u] ? Hstep Htail]; subst.
      destruct (tini_step_item _ _ _ _ _ He Hstep) as [e' [-> Hstep']].
      destruct (IH _ _ Htail) as (i & j & w & u' & -> & Hi & Hj).
      exists (S i), j, w, u'. repeat split; eauto using nsteps_l.
Qed.

Lemma tini_pstep_head e s z t :
  (∀ K a, e = fill_item K a → is_Some (to_val a)) →
  pstep (e,s) (z,t) → head_step e s [] z t [].
Proof.
  intros Hv Hstep. inversion Hstep as [Ks a b E Ez Hhead]; simpl in *; subst z.
  destruct Ks as [|K Ks] using rev_ind; first (by subst).
  rewrite tini_fill_snoc in E.
  destruct (Hv _ _ E) as [w Hw]. apply tini_fill_val in Hw as [w' Hw'].
  rewrite (tini_head_nonval _ _ _ _ _ _ Hhead) in Hw'. discriminate.
Qed.

Lemma tini_run_head n e s v t :
  to_val e = None →
  (∀ K a, e = fill_item K a → is_Some (to_val a)) →
  run n e s v t →
  ∃ i z u, n = S i ∧ head_step e s [] z u [] ∧ run i z u v t.
Proof.
  intros Hnv Hv Hr. destruct n.
  - apply tini_run_zero in Hr. injection Hr as E _. rewrite <- E, tini_to_of in Hnv. discriminate.
  - inversion Hr as [|? ? [z u] ? Hstep Htail]; subst.
    exists n, z, u. repeat split; eauto using tini_pstep_head.
Qed.

Local Ltac tini_ready :=
  let K := fresh "K" in let hole := fresh "hole" in let E := fresh "Ectx" in
  intros K hole E; destruct K; simpl in E; inversion E; subst;
  simpl; repeat rewrite tini_to_of; eauto; solve [eexists; reflexivity].

Local Lemma tini_eren_ext e (a b : var → var) :
  (∀ x, a x = b x) → rename a e = rename b e.
Proof.
  revert a b. induction e; simpl; intros; f_equal; eauto;
    match goal with IH : _ |- _ => solve [apply IH; intros [|x]; try unfold up; cbn [upren scons]; simpl; congruence] end.
Qed.

Local Lemma tini_eren_comp e (a b : var → var) :
  rename b (rename a e) = rename (λ x, b (a x)) e.
Proof.
  revert a b. induction e; simpl; intros; f_equal; auto.
  all: etrans; [eauto|apply tini_eren_ext; intros [|x]; reflexivity].
Qed.

Local Lemma tini_esub_ext e (a b : var → expr) :
  (∀ x, a x = b x) → e.[a] = e.[b].
Proof.
  revert a b. induction e; simpl; intros; f_equal; eauto;
    match goal with IH : _ |- _ => solve [apply IH; intros [|x]; try unfold up; cbn [upren scons]; simpl; congruence] end.
Qed.

Local Lemma tini_esub_ren e (a : var → var) (b : var → expr) :
  (rename a e).[b] = e.[λ x, b (a x)].
Proof.
  revert a b. induction e; simpl; intros; f_equal; auto.
  all: etrans; [eauto|apply tini_esub_ext; intros [|x]; reflexivity].
Qed.

Local Lemma tini_eren_sub e (a : var → expr) (b : var → var) :
  rename b (e.[a]) = e.[λ x, rename b (a x)].
Proof.
  revert a b. induction e; simpl; intros; f_equal; auto.
  all: etrans; [eauto|apply tini_esub_ext; intros [|x]; try unfold up; cbn [upren scons]; simpl; try rewrite !tini_eren_comp; reflexivity].
Qed.

Local Lemma tini_esub_id e : e.[ids] = e.
Proof.
  induction e; simpl; f_equal; auto.
  all: etrans; [|eassumption]; apply tini_esub_ext; intros [|x]; reflexivity.
Qed.

Local Lemma tini_esub_comp e (a b : var → expr) :
  e.[a].[b] = e.[λ x, (a x).[b]].
Proof.
  revert a b. induction e; simpl; intros; f_equal; auto.
  all: etrans; [eauto|apply tini_esub_ext; intros [|x]; try unfold up; cbn [upren scons]; simpl; try rewrite tini_esub_ren, tini_eren_sub; reflexivity].
Qed.

Local Lemma tini_beta e (a : var → expr) w : e.[up a].[#w/] = e.[#w .: a].
Proof.
  rewrite tini_esub_comp. apply tini_esub_ext. intros [|x]; first done.
  change ((rename S (a x)).[#w/] = a x).
  rewrite tini_esub_ren. apply tini_esub_id.
Qed.

Section soundness.

Context `{SecurityLattice label}.
Local Existing Instances lat_equiv_equiv lat_equiv_dec.

(* Simultaneous instantiation of the two kinds of type parameters. *)
Local Notation "f ≐ g" := (∀ x, f x = g x) (at level 70).
Local Notation "f ∘ₜ g" := (λ x, f (g x)) (at level 45).

Local Lemma tini_label_ext (l : label_term) (a b : var → label_term) :
  a ≐ b → l.[a] = l.[b].
Proof. induction l; simpl; intros Hext; f_equal; auto. Qed.

Local Lemma tini_label_id (l : label_term) : l.[LVar] = l.
Proof. induction l; simpl; congruence. Qed.

Local Lemma tini_label_comp (l : label_term) (a b : var → label_term) :
  l.[a].[b] = l.[λ x, (a x).[b]].
Proof. induction l; simpl; congruence. Qed.

Local Lemma tini_label_single (a : var → label_term) (p l : label_term) :
  p.[l/].[a] = p.[l.[a] .: a].
Proof. rewrite tini_label_comp. apply tini_label_ext. intros [|]; reflexivity. Qed.

Local Lemma tini_label_ren (l : label_term) (a : var → var) :
  rename a l = l.[LVar ∘ₜ a].
Proof. induction l; simpl; congruence. Qed.

Local Fixpoint tini_ren (a b : var → var) (t : type) : type :=
  match t with
  | TUnit => TUnit | TBool => TBool | TNat => TNat | TVar x => TVar (b x)
  | TRef τ => TRef (tini_sren a b τ)
  | TArrow l τ ν => TArrow l.[LVar ∘ₜ a] (tini_sren a b τ) (tini_sren a b ν)
  | TProd τ ν => TProd (tini_sren a b τ) (tini_sren a b ν)
  | TSum τ ν => TSum (tini_sren a b τ) (tini_sren a b ν)
  | TForall l τ => TForall l.[LVar ∘ₜ a] (tini_sren a (upren b) τ)
  | TLForall l τ => TLForall l.[LVar ∘ₜ upren a] (tini_sren (upren a) b τ)
  | TExist τ => TExist (tini_sren a (upren b) τ)
  | TRec τ => TRec (tini_sren a (upren b) τ)
  end
with tini_sren (a b : var → var) (τ : sectype) : sectype :=
  match τ with t @ l => tini_ren a b t @ l.[LVar ∘ₜ a] end.

Local Definition tini_tup (b : var → type) := TVar 0 .: (tini_ren id S ∘ₜ b).
Local Definition tini_lup (b : var → type) := tini_ren S id ∘ₜ b.

Local Fixpoint tini_inst (a : var → label_term) (b : var → type) (t : type) : type :=
  match t with
  | TUnit => TUnit | TBool => TBool | TNat => TNat | TVar x => b x
  | TRef τ => TRef (tini_sinst a b τ)
  | TArrow l τ ν => TArrow l.[a] (tini_sinst a b τ) (tini_sinst a b ν)
  | TProd τ ν => TProd (tini_sinst a b τ) (tini_sinst a b ν)
  | TSum τ ν => TSum (tini_sinst a b τ) (tini_sinst a b ν)
  | TForall l τ => TForall l.[a] (tini_sinst a (tini_tup b) τ)
  | TLForall l τ => TLForall l.[up a] (tini_sinst (up a) (tini_lup b) τ)
  | TExist τ => TExist (tini_sinst a (tini_tup b) τ)
  | TRec τ => TRec (tini_sinst a (tini_tup b) τ)
  end
with tini_sinst (a : var → label_term) (b : var → type) (τ : sectype) : sectype :=
  match τ with t @ l => tini_inst a b t @ l.[a] end.

Combined Scheme tini_type_ind from type_mut, sectype_mut.
Local Ltac tini_ext := intros [|x]; unfold tini_tup, tini_lup; try unfold up; cbn [upren scons]; simpl; congruence.

Local Lemma tini_ren_ext :
  (∀ t a b c d, a ≐ c → b ≐ d → tini_ren a b t = tini_ren c d t) ∧
  (∀ τ a b c d, a ≐ c → b ≐ d → tini_sren a b τ = tini_sren c d τ).
Proof.
  apply tini_type_ind; simpl; intros; f_equal; eauto using tini_label_ext;
    try solve [eauto using tini_label_ext | intros x; simpl; congruence |
      eapply tini_label_ext; tini_ext | match goal with IH : ∀ _ _ _ _, _ → _ → _ = _ |- _ => apply IH; tini_ext end].
Qed.

Local Lemma tini_inst_ext :
  (∀ t a b c d, a ≐ c → b ≐ d → tini_inst a b t = tini_inst c d t) ∧
  (∀ τ a b c d, a ≐ c → b ≐ d → tini_sinst a b τ = tini_sinst c d τ).
Proof.
  apply tini_type_ind; simpl; intros; f_equal; eauto using tini_label_ext;
    try solve [eapply tini_label_ext; tini_ext | match goal with IH : ∀ _ _ _ _, _ → _ → _ = _ |- _ => apply IH; tini_ext end].
Qed.

Local Lemma tini_ren_comp :
  (∀ t a b c d, tini_ren c d (tini_ren a b t) = tini_ren (c ∘ₜ a) (d ∘ₜ b) t) ∧
  (∀ τ a b c d, tini_sren c d (tini_sren a b τ) = tini_sren (c ∘ₜ a) (d ∘ₜ b) τ).
Proof.
  apply tini_type_ind; simpl; intros; f_equal; auto;
    try solve [rewrite tini_label_comp; apply tini_label_ext; tini_ext].
  all: etrans; [eauto|apply (proj2 tini_ren_ext); tini_ext].
Qed.

Local Lemma tini_up_label (a : var → label_term) :
  up a ≐ LVar 0 .: (λ x, (a x).[LVar ∘ₜ S]).
Proof. intros [|x]; first done. apply tini_label_ren. Qed.

Local Lemma tini_inst_ren :
  (∀ t a b c d, tini_inst c d (tini_ren a b t) = tini_inst (c ∘ₜ a) (d ∘ₜ b) t) ∧
  (∀ τ a b c d, tini_sinst c d (tini_sren a b τ) = tini_sinst (c ∘ₜ a) (d ∘ₜ b) τ).
Proof.
  apply tini_type_ind; simpl; intros; f_equal; auto;
    try solve [rewrite tini_label_comp; apply tini_label_ext; intros [|]; reflexivity].
  all: etrans; [eauto|apply (proj2 tini_inst_ext); intros [|]; reflexivity].
Qed.

Local Lemma tini_ren_inst :
  (∀ t a b c d, tini_ren c d (tini_inst a b t) =
    tini_inst (λ x, (a x).[LVar ∘ₜ c]) (tini_ren c d ∘ₜ b) t) ∧
  (∀ τ a b c d, tini_sren c d (tini_sinst a b τ) =
    tini_sinst (λ x, (a x).[LVar ∘ₜ c]) (tini_ren c d ∘ₜ b) τ).
Proof.
  assert (Hup : ∀ a c, (λ x, (up a x).[LVar ∘ₜ upren c]) ≐ up (λ x, (a x).[LVar ∘ₜ c])).
  { intros a c [|x]; first done. rewrite !tini_up_label.
    change (((a x).[LVar ∘ₜ S]).[LVar ∘ₜ upren c] = (a x).[LVar ∘ₜ c].[LVar ∘ₜ S]).
    rewrite !tini_label_comp. apply tini_label_ext. intros ?. try rewrite tini_up_label. done. }
  apply tini_type_ind; simpl; intros; f_equal; auto;
    try solve [rewrite tini_label_comp; auto].
  all: try solve [rewrite tini_label_comp; apply tini_label_ext; apply Hup].
  all: etrans; [eauto|apply (proj2 tini_inst_ext); try (apply Hup || done)];
    unfold tini_tup, tini_lup; intros [|x]; try unfold up; cbn [upren scons]; simpl;
    try rewrite !(proj1 tini_ren_comp); reflexivity.
Qed.

Local Lemma tini_inst_comp :
  (∀ t a b c d, tini_inst c d (tini_inst a b t) =
    tini_inst (λ x, (a x).[c]) (tini_inst c d ∘ₜ b) t) ∧
  (∀ τ a b c d, tini_sinst c d (tini_sinst a b τ) =
    tini_sinst (λ x, (a x).[c]) (tini_inst c d ∘ₜ b) τ).
Proof.
  assert (Hup : ∀ (a c : var → label_term), (λ x, (up a x).[up c]) ≐ up (λ x, (a x).[c])).
  { intros a c [|x]; first done. rewrite (tini_up_label a), tini_up_label.
    change (((a x).[LVar ∘ₜ S]).[up c] = (a x).[c].[LVar ∘ₜ S]).
    rewrite !tini_label_comp. apply tini_label_ext. intros k. exact (tini_up_label c (S k)). }
  apply tini_type_ind; simpl; intros; f_equal; auto;
    try solve [rewrite tini_label_comp; auto].
  all: try solve [rewrite tini_label_comp; apply tini_label_ext; apply Hup].
  all: etrans; [eauto|apply (proj2 tini_inst_ext); try (apply Hup || done)];
    unfold tini_tup, tini_lup; intros [|x]; try unfold up; cbn [upren scons]; simpl;
    try rewrite (proj1 tini_inst_ren), (proj1 tini_ren_inst);
    try reflexivity; apply (proj1 tini_inst_ext); intros k; try reflexivity;
    first [symmetry; apply tini_label_id | exact (tini_up_label c (S k))].
Qed.

Local Lemma tini_ren_type :
  (∀ t b, tini_ren id b t = rename_type b t) ∧
  (∀ τ b, tini_sren id b τ = rename_sectype b τ).
Proof.
  apply tini_type_ind; simpl; intros; f_equal; auto using tini_label_id;
    try solve [etrans; [|apply tini_label_id]; apply tini_label_ext; intros [|]; reflexivity].
  all: etrans; [|eauto]; apply (proj2 tini_ren_ext); intros [|]; reflexivity.
Qed.

Local Lemma tini_inst_label :
  (∀ t a, tini_inst a TVar t = hsubst_label_type a t) ∧
  (∀ τ a, tini_sinst a TVar τ = hsubst_label_sectype a τ).
Proof.
  apply tini_type_ind; simpl; intros; f_equal; auto.
  all: etrans; [|eauto]; apply (proj2 tini_inst_ext); first done; intros [|]; reflexivity.
Qed.

Local Lemma tini_ren_label :
  (∀ t a, tini_ren a id t = hsubst_label_type (LVar ∘ₜ a) t) ∧
  (∀ τ a, tini_sren a id τ = hsubst_label_sectype (LVar ∘ₜ a) τ).
Proof.
  apply tini_type_ind; simpl; intros; f_equal; auto.
  all: try solve [apply tini_label_ext; intros [|]; reflexivity].
  all: try solve [etrans; [apply H0|];
    change (hsubst_label_sectype (LVar ∘ₜ upren a) τ =
      hsubst_label_sectype (up (LVar ∘ₜ a)) τ);
    rewrite <- !(proj2 tini_inst_label);
    apply (proj2 tini_inst_ext); intros [|]; reflexivity].
  all: etrans; [|eauto]; apply (proj2 tini_ren_ext); intros [|]; reflexivity.
Qed.

Local Lemma tini_inst_type :
  (∀ t b, tini_inst LVar b t = subst_type b t) ∧
  (∀ τ b, tini_sinst LVar b τ = hsubst_sectype b τ).
Proof.
  apply tini_type_ind; simpl; intros; f_equal; auto using tini_label_id;
    try solve [etrans; [|apply tini_label_id]; apply tini_label_ext; intros [|]; reflexivity].
  all: etrans; [|eauto]; apply (proj2 tini_inst_ext); try (intros [|]; reflexivity).
  all: unfold tini_tup, tini_lup; intros x;
    first [apply (proj1 tini_ren_label)
      | destruct x; try reflexivity; apply (proj1 tini_ren_type)].
Qed.

Local Lemma tini_order_refl a : a ⊑ a.
Proof. apply join_idempotent. Qed.

Local Lemma tini_order_trans a b c : a ⊑ b → b ⊑ c → a ⊑ c.
Proof.
  unfold order. intros Hab Hbc.
  transitivity (a ⊔ (b ⊔ c)); first (apply join_proper; [reflexivity|by symmetry]).
  transitivity ((a ⊔ b) ⊔ c); first apply join_associative.
  transitivity (b ⊔ c); [apply join_proper; [exact Hab|reflexivity]|exact Hbc].
Qed.

Local Lemma tini_join_elim a b c : a ⊑ c → b ⊑ c → a ⊔ b ⊑ c.
Proof.
  unfold order. intros Ha Hb.
  transitivity (a ⊔ (b ⊔ c)); first (symmetry; apply join_associative).
  transitivity (a ⊔ c); [apply join_proper; [reflexivity|exact Hb]|exact Ha].
Qed.

Local Lemma tini_join_left a b : a ⊑ a ⊔ b.
Proof.
  unfold order. transitivity ((a ⊔ a) ⊔ b); first apply join_associative.
  apply join_proper; [apply join_idempotent|reflexivity].
Qed.

Local Lemma tini_join_right a b : b ⊑ a ⊔ b.
Proof.
  unfold order.
  transitivity (b ⊔ (b ⊔ a)); first (apply join_proper; [reflexivity|apply join_commutative]).
  transitivity (b ⊔ a); [apply tini_join_left|apply join_commutative].
Qed.

Local Fixpoint tini_level (a : var → label) (l : label_term) : label :=
  match l with
  | LVar x => a x
  | LLabel l => l
  | LJoin l l' => tini_level a l ⊔ tini_level a l'
  end.

Local Lemma tini_flow a l l' : l ⊑ₛ l' → tini_level a l ⊑ tini_level a l'.
Proof.
  induction 1; simpl; eauto using tini_order_refl, tini_order_trans, tini_join_elim.
  - apply bot_left_id.
  - apply top_right_absorb.
Qed.

Local Lemma tini_flow_subst (a : var → label_term) l l' :
  l ⊑ₛ l' → l.[a] ⊑ₛ l'.[a].
Proof. induction 1; simpl; eauto using flowsto. Qed.

Local Definition tini_low (l : label_term) := tini_level (λ _, ⊥) l ⊑ ζ.
Local Definition tini_lat (τ : sectype) := match τ with _ @ l => l end.
Local Definition tini_visible τ := tini_low (tini_lat τ).

Local Lemma tini_low_join l l' : tini_low (l ⊔ₛ l') ↔ tini_low l ∧ tini_low l'.
Proof.
  unfold tini_low; simpl. split; [intros Hab; split|intros []];
    eauto using tini_order_trans, tini_join_left, tini_join_right, tini_join_elim.
Qed.

Local Lemma tini_low_flow l l' : l ⊑ₛ l' → tini_low l' → tini_low l.
Proof. unfold tini_low. intros Hf Hl. eapply tini_order_trans; [apply tini_flow; exact Hf|exact Hl]. Qed.

Local Lemma tini_low_dec l : Decision (tini_low l).
Proof. unfold tini_low, order. apply _. Defined.

Local Lemma tini_inst_flow a b τ l : τ ↘ l → tini_sinst a b τ ↘ l.[a].
Proof. destruct τ. apply tini_flow_subst. Qed.

Local Lemma tini_guard τ l : τ ↘ l → tini_visible τ → tini_low l.
Proof. destruct τ. apply tini_low_flow. Qed.

Local Lemma tini_effect pc l l' : pc ⊔ₛ l ⊑ₛ l' → tini_low l' → tini_low pc ∧ tini_low l.
Proof. intros Hf Hl. apply tini_low_join. by eapply tini_low_flow. Qed.

Local Lemma tini_inst_id :
  (∀ t, tini_inst LVar TVar t = t) ∧ (∀ τ, tini_sinst LVar TVar τ = τ).
Proof.
  apply tini_type_ind; simpl; intros; f_equal; auto using tini_label_id.
  all: try (etrans; [|apply tini_label_id]; apply tini_label_ext; intros [|]; reflexivity).
  all: etrans; [|eassumption]; apply (proj2 tini_inst_ext); intros [|]; reflexivity.
Qed.

Local Lemma tini_type_natural a b τ t :
  tini_sinst a b (τ.|[t/]) = tini_sinst a (tini_inst a b t .: b) τ.
Proof.
  change (tini_sinst a b (hsubst_sectype (t .: TVar) τ) = tini_sinst a (tini_inst a b t .: b) τ).
  rewrite <- (proj2 tini_inst_type), (proj2 tini_inst_comp).
  apply (proj2 tini_inst_ext); intros [|]; reflexivity.
Qed.

Local Lemma tini_label_natural a b τ l :
  tini_sinst a b (τ.|[l/]) = tini_sinst (l.[a] .: a) b τ.
Proof.
  change (tini_sinst a b (hsubst_label_sectype (l .: LVar) τ) = tini_sinst (l.[a] .: a) b τ).
  rewrite <- (proj2 tini_inst_label), (proj2 tini_inst_comp).
  apply (proj2 tini_inst_ext); intros [|]; reflexivity.
Qed.

Local Lemma tini_type_beta a b τ t :
  (tini_sinst a (tini_tup b) τ).|[t/] = tini_sinst a (t .: b) τ.
Proof.
  change (hsubst_sectype (t .: TVar) (tini_sinst a (tini_tup b) τ) = tini_sinst a (t .: b) τ).
  rewrite <- (proj2 tini_inst_type), (proj2 tini_inst_comp).
  apply (proj2 tini_inst_ext); first (intros x; apply tini_label_id).
  intros [|x]; first done. unfold tini_tup, scons.
  rewrite (proj1 tini_inst_ren).
  etrans; last apply (proj1 tini_inst_id).
  apply (proj1 tini_inst_ext); reflexivity.
Qed.

Local Lemma tini_label_beta a b τ l :
  (tini_sinst (up a) (tini_lup b) τ).|[l/] = tini_sinst (l .: a) b τ.
Proof.
  change (hsubst_label_sectype (l .: LVar) (tini_sinst (up a) (tini_lup b) τ) = tini_sinst (l .: a) b τ).
  rewrite <- (proj2 tini_inst_label), (proj2 tini_inst_comp).
  apply (proj2 tini_inst_ext).
  - intros [|x]; first done. rewrite tini_up_label.
    change ((a x).[LVar ∘ₜ S].[l .: LVar] = a x).
    rewrite tini_label_comp. etrans; last apply tini_label_id.
    apply tini_label_ext. done.
  - intros x. unfold tini_lup, scons.
    rewrite (proj1 tini_inst_ren).
    etrans; last apply (proj1 tini_inst_id).
    apply (proj1 tini_inst_ext); reflexivity.
Qed.

Local Lemma tini_label_beta_pc (a : var → label_term) (l' l : label_term) :
  l.[up a].[l' .: LVar] = l.[l' .: a].
Proof.
  rewrite tini_label_comp. apply tini_label_ext. intros [|x]; first done. rewrite tini_up_label.
  change ((a x).[LVar ∘ₜ S].[l' .: LVar] = a x).
  rewrite tini_label_comp. etrans; last apply tini_label_id.
  apply tini_label_ext. done.
Qed.

Local Lemma tini_type_shift a b τ t :
  tini_sinst a (t .: b) (hsubst_sectype (ren (+1)) τ) = tini_sinst a b τ.
Proof.
  replace (hsubst_sectype (ren (+1)) τ) with (tini_sren id S τ).
  - rewrite (proj2 tini_inst_ren). apply (proj2 tini_inst_ext); reflexivity.
  - change (tini_sren id S τ = hsubst_sectype (TVar ∘ₜ S) τ).
    symmetry. rewrite <- (proj2 tini_inst_type), <- (proj2 tini_inst_ren).
    etrans; first apply (proj2 tini_inst_ext); try reflexivity.
    apply (proj2 tini_inst_id).
Qed.

Local Lemma tini_label_shift a b τ l :
  tini_sinst (l .: a) b (hsubst_label_sectype (ren (+1)) τ) = tini_sinst a b τ.
Proof.
  rewrite <- (proj2 tini_inst_label), (proj2 tini_inst_comp).
  apply (proj2 tini_inst_ext); reflexivity.
Qed.

(* A world records the invariant type of each allocated cell.  Bounds count
   head reductions.  A computation at a high pc preserves every visible cell. *)
Local Definition tini_world := gmap loc sectype.
Local Definition tini_extends (W W' : tini_world) :=
  ∀ l τ, W !! l = Some τ → W' !! l = Some τ.

Local Lemma tini_ext_refl W : tini_extends W W.
Proof. intros l τ Hl. exact Hl. Qed.

Local Lemma tini_ext_trans W W' W'' :
  tini_extends W W' → tini_extends W' W'' → tini_extends W W''.
Proof. unfold tini_extends. eauto. Qed.

Local Definition tini_U := tini_world → sectype → val → Prop.
Local Definition tini_UHeap (R : tini_U) W (s : state) :=
  ∀ l τ, W !! l = Some τ → ∃ v, s !! l = Some v ∧ R W τ v.

Local Definition tini_frame (W : tini_world) pc (s t : state) :=
  ¬ tini_low pc → ∀ l τ, W !! l = Some τ → tini_visible τ → t !! l = s !! l.

Local Definition tini_UE (V : nat → tini_U) n W pc τ e :=
  ∀ i s v t, i ≤ n → tini_UHeap (V n) W s → run i e s v t →
    ∃ W', tini_extends W W' ∧ tini_UHeap (V (n-i)) W' t ∧
      V (n-i) W' τ v ∧ tini_frame W pc s t.

Local Definition tini_Ulayer (V : nat → tini_U) n W τ v : Prop :=
  let '(t @ _) := τ in
  match t, v with
  | TUnit, UnitV | TBool, BoolV _ | TNat, NatV _ => True
  | TRef τ, LocV l => W !! l = Some τ
  | TProd τ ν, PairV u v => V n W τ u ∧ V n W ν v
  | TSum τ _, InjLV v | TSum _ τ, InjRV v => V n W τ v
  | TRec τ, FoldV v => V n W (τ.|[TRec τ/]) v
  | TExist τ, PackV v => ∃ t, V n W (τ.|[t/]) v
  | TArrow pc τ ν, LamV e =>
    ∀ m W' v, m ≤ n → tini_extends W W' → V m W' τ v →
      tini_UE V m W' pc ν e.[#v/]
  | TForall pc τ, TLamV e =>
    ∀ m W' t, m ≤ n → tini_extends W W' → tini_UE V m W' pc (τ.|[t/]) e
  | TLForall pc τ, TLLamV e =>
    ∀ m W' l, m ≤ n → tini_extends W W' → tini_UE V m W' pc.[l/] (τ.|[l/]) e
  | _, _ => False
  end.

(* Each layer can query all smaller bounds. The list preserves these
   predicates as the bound grows, so the definition recurses on a natural. *)
Local Definition tini_Uzero : tini_U := λ _ _ _, True.
Local Fixpoint tini_Utable n : list tini_U :=
  match n with
  | 0 => [tini_Uzero]
  | S n => let table := tini_Utable n in
    table ++ [tini_Ulayer (λ m, List.nth m table tini_Uzero) n]
  end.

Local Definition tini_uv n : tini_U := List.nth n (tini_Utable n) tini_Uzero.

Local Lemma tini_Ulength n : length (tini_Utable n) = S n.
Proof. induction n; simpl; [done|rewrite length_app, IHn; simpl; lia]. Qed.

Local Lemma tini_Ulookup m n : m ≤ n → List.nth m (tini_Utable n) tini_Uzero = tini_uv m.
Proof.
  induction 1 as [|n Hmn IH]; first done.
  simpl. rewrite List.app_nth1; first done. rewrite tini_Ulength. lia.
Qed.

Local Lemma tini_UE_ext V V' n W pc τ e :
  (∀ i, i ≤ n → V i = V' i) →
  tini_UE V n W pc τ e → tini_UE V' n W pc τ e.
Proof.
  intros HE HR i s v t Hi Hs Hr.
  rewrite <- (HE _ (Nat.le_refl n)) in Hs.
  rewrite <- (HE (n-i) ltac:(lia)). by eapply HR.
Qed.

Local Lemma tini_Ulayer_ext V V' n W τ v :
  (∀ i, i ≤ n → V i = V' i) →
  tini_Ulayer V n W τ v → tini_Ulayer V' n W τ v.
Proof.
  intros HE. destruct τ as [l t]; destruct t, v; simpl; try tauto;
    try (rewrite (HE _ (Nat.le_refl n)); tauto).
  - intros HR m W' v Hm HW Hv.
    eapply tini_UE_ext; first (intros; apply HE; lia).
    eapply HR; eauto. by rewrite (HE _ Hm).
  - intros HR m W' t Hm HW. eapply tini_UE_ext; [intros; apply HE; lia|eapply HR; eauto].
  - intros HR m W' l' Hm HW. eapply tini_UE_ext; [intros; apply HE; lia|eapply HR; eauto].
Qed.

Local Lemma tini_Ustep n W τ v :
  tini_uv (S n) W τ v ↔ tini_Ulayer tini_uv n W τ v.
Proof.
  unfold tini_uv at 1. simpl. rewrite List.app_nth2; last (rewrite tini_Ulength; lia). rewrite tini_Ulength.
  replace (S n - S n) with 0 by lia. simpl.
  split; apply tini_Ulayer_ext; intros; [apply tini_Ulookup|symmetry; apply tini_Ulookup]; done.
Qed.

Local Lemma tini_Umono n m W W' τ v :
  m ≤ n → tini_extends W W' → tini_uv n W τ v → tini_uv m W' τ v.
Proof.
  revert m W W' τ v. induction n as [|n IH]; intros [|m] W W' [l t] v Hm HW Hv; try done; try lia.
  apply tini_Ustep in Hv. apply tini_Ustep.
  destruct t, v; cbn [tini_Ulayer] in Hv |- *; try contradiction; try exact I.
  all: try solve [exact (HW _ _ Hv)].
  all: try solve [eapply IH; [lia|exact HW|exact Hv]].
  all: try solve [destruct Hv as [H1 H2];
    split; (eapply (IH m W W'); [lia|exact HW|eassumption])].
  all: try solve [destruct Hv as [t Ht]; exists t; eapply IH; [lia|exact HW|exact Ht]].
  all: intros; eapply Hv; try lia; try eassumption;
    eapply tini_ext_trans; eassumption.
Qed.

Local Lemma tini_Uheap_mono n m W s :
  m ≤ n → tini_UHeap (tini_uv n) W s → tini_UHeap (tini_uv m) W s.
Proof.
  intros Hm Hs l τ Hl. destruct (Hs l τ Hl) as (v & Hlookup & Hv).
  exists v. eauto using tini_Umono, tini_ext_refl.
Qed.

Local Lemma tini_frame_refl W pc s : tini_frame W pc s s.
Proof. unfold tini_frame. intros. reflexivity. Qed.

Local Lemma tini_frame_trans W W' pc s s' t :
  tini_extends W W' → tini_frame W pc s s' → tini_frame W' pc s' t →
  tini_frame W pc s t.
Proof.
  intros HW HF HF' Hh l τ Hl Hvis.
  rewrite (HF' Hh _ _ (HW _ _ Hl) Hvis).
  exact (HF Hh _ _ Hl Hvis).
Qed.

Local Lemma tini_frame_flow W pc pc' s t :
  (tini_low pc' → tini_low pc) → tini_frame W pc' s t → tini_frame W pc s t.
Proof. unfold tini_frame. intros HF Hframe Hhigh. apply Hframe. by auto. Qed.

Local Notation "'UE' n W pc τ e" := (tini_UE tini_uv n W pc τ e)
  (at level 10, n, W, pc, τ, e at next level).
Local Notation "'UV' n W τ v" := (tini_uv n W τ v)
  (at level 10, n, W, τ, v at next level).

Local Lemma tini_uval n W pc τ v : UV n W τ v → UE n W pc τ (#v).
Proof.
  intros Hv i s w t Hi Hs Hr. destruct (tini_run_value _ _ _ _ _ Hr) as (-> & -> & ->).
  rewrite Nat.sub_0_r. exists W. eauto using tini_ext_refl, tini_frame_refl.
Qed.

Local Lemma tini_ustep n W pc τ e :
  to_val e = None →
  (∀ K a, e = fill_item K a → is_Some (to_val a)) →
  (∀ m s z t, S m = n → tini_UHeap (tini_uv n) W s →
     head_step e s [] z t [] →
     ∃ W', tini_extends W W' ∧ tini_UHeap (tini_uv m) W' t ∧
       tini_frame W pc s t ∧ UE m W' pc τ z) →
  UE n W pc τ e.
Proof.
  intros Hnv Hv Hstep i s v t Hi Hs Hr.
  destruct (tini_run_head _ _ _ _ _ Hnv Hv Hr) as (j & z & u & -> & Hh & Hj).
  destruct n as [|n]; first lia.
  destruct (Hstep _ _ _ _ eq_refl Hs Hh) as (W' & HW & Hu & HF & HE).
  destruct (HE j u v t ltac:(lia) Hu Hj) as (W'' & HW' & Ht & Hval & HF').
  change (S n - S j) with (n-j).
  exists W''. split; first exact (tini_ext_trans _ _ _ HW HW').
  split; first exact Ht. split; first exact Hval.
  exact (tini_frame_trans _ _ _ _ _ _ HW HF HF').
Qed.

Local Lemma tini_ubind n W pc τ ν K e :
  UE n W pc τ e →
  (∀ m W' w, m ≤ n → tini_extends W W' → UV m W' τ w →
    UE m W' pc ν (fill_item K (#w))) →
  UE n W pc ν (fill_item K e).
Proof.
  intros HE HK i s v t Hi Hs Hr.
  destruct (tini_run_item _ _ _ _ _ _ Hr) as (j & k & w & u & -> & Hj & Hk).
  destruct (HE j s w u ltac:(lia) Hs Hj) as (W' & HW & Hu & Hv & HF).
  destruct (HK (n-j) W' w ltac:(lia) HW Hv k u v t ltac:(lia) Hu Hk) as
    (W'' & HW' & Ht & Hval & HF').
  replace (n - (j + k)) with (n-j-k) by lia.
  exists W''. split; first exact (tini_ext_trans _ _ _ HW HW').
  split; first exact Ht. split; first exact Hval.
  exact (tini_frame_trans _ _ _ _ _ _ HW HF HF').
Qed.

Local Lemma tini_Uflow n W pc pc' τ e :
  (tini_low pc' → tini_low pc) → UE n W pc' τ e → UE n W pc τ e.
Proof.
  intros Hf HE i s v t Hi Hs Hr. destruct (HE _ _ _ _ Hi Hs Hr) as (W' & HW & Ht & Hv & HF).
  exists W'. eauto 8 using tini_frame_flow.
Qed.

Local Lemma tini_uheap_insert n W W' s l τ v :
  W' !! l = Some τ →
  tini_extends W W' →
  (∀ j ν, W' !! j = Some ν → j = l ∧ ν = τ ∨ W !! j = Some ν) →
  tini_UHeap (tini_uv n) W s → UV n W' τ v →
  tini_UHeap (tini_uv n) W' (<[l:=v]> s).
Proof.
  intros Hl HW Hnew Hs Hv j ν Hj.
  destruct (decide (l = j)) as [<-|Hne].
  - exists v. split; first apply lookup_insert_eq.
    assert (ν = τ) as ->; last done.
    congruence.
  - rewrite (lookup_insert_ne s l j v Hne).
    destruct (Hnew _ _ Hj) as [[Heq _]|Hj']; first congruence.
    destruct (Hs _ _ Hj') as (w & Hlookup & Hval).
    exists w. eauto using tini_Umono.
Qed.

Local Lemma tini_ufresh W s n l :
  tini_UHeap (tini_uv n) W s → s !! l = None → W !! l = None.
Proof.
  intros Hs Hl. destruct (W !! l) eqn:HW; last done.
  destruct (Hs _ _ HW) as (v & E & _). congruence.
Qed.

Local Lemma tini_ext_insert W l τ :
  W !! l = None → tini_extends W (<[l:=τ]>W).
Proof.
  intros Hl j ν Hj. rewrite (lookup_insert_ne W l j τ); first done. intros ->. congruence.
Qed.

Local Lemma tini_uheap_write n W s l τ v :
  W !! l = Some τ →
  tini_UHeap (tini_uv n) W s → UV n W τ v →
  tini_UHeap (tini_uv n) W (<[l:=v]>s).
Proof.
  intros. eapply tini_uheap_insert; eauto using tini_ext_refl.
Qed.

Local Lemma tini_uheap_alloc n W s l τ v :
  W !! l = None →
  tini_UHeap (tini_uv n) W s → UV n W τ v →
  tini_UHeap (tini_uv n) (<[l:=τ]>W) (<[l:=v]>s).
Proof.
  intros Hl Hs Hv. eapply tini_uheap_insert; eauto using tini_ext_insert, tini_Umono.
  - apply lookup_insert_eq.
  - intros j ν. destruct (decide (l = j)) as [<-|Hne].
    + rewrite (lookup_insert_eq W l τ). intros [= <-]. auto.
    + rewrite (lookup_insert_ne W l j τ); auto.
Qed.

Local Lemma tini_frame_write W pc s l τ v :
  (∀ ν, W !! l = Some ν → ν = τ) →
  (tini_visible τ → tini_low pc) → tini_frame W pc s (<[l:=v]>s).
Proof.
  intros HW HF Hhigh j ν Hj Hlow. rewrite (lookup_insert_ne s l j v); first done.
  intros ->. apply Hhigh, HF. by rewrite <- (HW _ Hj).
Qed.

Local Lemma tini_frame_alloc W pc s l v :
  W !! l = None → tini_frame W pc s (<[l:=v]>s).
Proof.
  intros Hfresh Hhigh j ν Hj Hlow. rewrite (lookup_insert_ne s l j v); first done.
  intros ->. congruence.
Qed.

Local Lemma tini_umap n W pc τ ν e :
  (∀ m W' v, UV m W' τ v → UV m W' ν v) →
  UE n W pc τ e → UE n W pc ν e.
Proof.
  intros Hsub HE i s v t Hi Hs Hr.
  destruct (HE _ _ _ _ Hi Hs Hr) as (W' & HW & Ht & Hv & HF).
  exists W'. eauto 8.
Qed.

Local Lemma tini_urel_lab n W l l' t v :
  UV n W (t @ l) v → UV n W (t @ l') v.
Proof. destruct n; first done. rewrite !tini_Ustep. done. Qed.

Combined Scheme tini_sub_ind from subtype_mut, secsubtype_mut.

Local Lemma tini_usub_all :
  (∀ t t', t <: t' → ∀ a b n W l v,
    UV n W (tini_inst a b t @ l) v → UV n W (tini_inst a b t' @ l) v) ∧
  (∀ τ τ', τ <:ₛ τ' → ∀ a b n W v,
    UV n W (tini_sinst a b τ) v → UV n W (tini_sinst a b τ') v).
Proof.
  apply tini_sub_ind.
  - done.
  - intros. eauto.
  - intros τ1 τ1' τ2 τ2' pc1 pc2 _ IH1 _ IH2 Hflow a b [|n] W l v Hv; first done.
    apply tini_Ustep in Hv. apply tini_Ustep. destruct v; simpl in *; try contradiction.
    intros m W' w Hm HW Hw.
    eapply (tini_Uflow _ _ _ pc1.[a]); first by eauto using tini_low_flow, tini_flow_subst.
    eapply tini_umap; [intros; eapply IH2; eauto|].
    eapply Hv; eauto.
  - intros τ1 τ2 pc1 pc2 HF _ IH a b [|n] W l v Hv; first done.
    apply tini_Ustep in Hv. apply tini_Ustep. destruct v; simpl in *; try contradiction.
    intros m W' t Hm HW. rewrite tini_type_beta.
    eapply (tini_Uflow _ _ _ pc1.[a]); first by eauto using tini_low_flow, tini_flow_subst.
    eapply tini_umap; [intros; eapply IH; eauto|].
    specialize (Hv _ _ t Hm HW). rewrite tini_type_beta in Hv. done.
  - intros τ1 τ2 pc1 pc2 HF _ IH a b [|n] W l v Hv; first done.
    apply tini_Ustep in Hv. apply tini_Ustep. destruct v; simpl in *; try contradiction.
    intros m W' l' Hm HW. rewrite tini_label_beta, tini_label_beta_pc.
    eapply (tini_Uflow _ _ _ pc1.[l' .: a]); first by eauto using tini_low_flow, tini_flow_subst.
    eapply tini_umap; [intros; eapply IH; eauto|].
    specialize (Hv _ _ l' Hm HW). rewrite tini_label_beta, tini_label_beta_pc in Hv. done.
  - intros τ1 τ1' τ2 τ2' _ IH1 _ IH2 a b [|n] W l v Hv; first done.
    apply tini_Ustep in Hv. apply tini_Ustep. destruct v; simpl in *; intuition eauto.
  - intros τ1 τ1' τ2 τ2' _ IH1 _ IH2 a b [|n] W l v Hv; first done.
    apply tini_Ustep in Hv. apply tini_Ustep. destruct v; simpl in *; intuition eauto.
  - intros τ1 τ2 _ IH a b [|n] W l v Hv; first done.
    apply tini_Ustep in Hv. apply tini_Ustep. destruct v; simpl in *; try contradiction.
    specialize (IH a b n W v).
    rewrite !tini_type_natural in IH. simpl in IH.
    rewrite !tini_type_beta in *. eauto.
  - simpl. intros l l' t t' _ _ IH a b n W v Hv.
    eapply tini_urel_lab. eapply IH. exact Hv.
Qed.

Local Lemma tini_usub τ τ' a b n W v :
  τ <:ₛ τ' → UV n W (tini_sinst a b τ) v → UV n W (tini_sinst a b τ') v.
Proof. intros Hs. exact ((proj2 tini_usub_all) τ τ' Hs a b n W v). Qed.

Local Definition tini_UEnv (Γ : list sectype) a b n W (γ : var → expr) :=
  ∀ x τ, Γ !! x = Some τ → ∃ v, γ x = #v ∧ UV n W (tini_sinst a b τ) v.

Local Lemma tini_UEnv_mono Γ a b n m W W' γ :
  m ≤ n → tini_extends W W' → tini_UEnv Γ a b n W γ → tini_UEnv Γ a b m W' γ.
Proof.
  intros Hm HW Hγ x τ Hx. destruct (Hγ _ _ Hx) as (v & -> & Hv).
  exists v. eauto using tini_Umono.
Qed.

Local Lemma tini_UEnv_cons Γ a b n W γ τ v :
  UV n W (tini_sinst a b τ) v → tini_UEnv Γ a b n W γ →
  tini_UEnv (τ :: Γ) a b n W (#v .: γ).
Proof.
  intros Hv Hγ [|x] ν; simpl; first (intros [= <-]; eauto).
  apply Hγ.
Qed.

Local Lemma tini_UEnv_type Γ a b n W γ t :
  tini_UEnv Γ a b n W γ →
  tini_UEnv (hsubst_sectype (ren (+1)) <$> Γ) a (t .: b) n W γ.
Proof.
  intros Hγ x τ Hx. apply list_lookup_fmap_Some in Hx as (ν & -> & E). rewrite tini_type_shift. by eapply Hγ.
Qed.

Local Lemma tini_UEnv_label Γ a b n W γ l :
  tini_UEnv Γ a b n W γ →
  tini_UEnv (hsubst_label_sectype (ren (+1)) <$> Γ) (l .: a) b n W γ.
Proof.
  intros Hγ x τ Hx. apply list_lookup_fmap_Some in Hx as (ν & -> & E). rewrite tini_label_shift. by eapply Hγ.
Qed.

Local Ltac tini_ux :=
  solve [assumption | apply tini_ext_refl | eapply tini_ext_trans; eassumption].
Local Ltac tini_uv_down :=
  solve [assumption |
    eapply tini_Umono; [ | | eassumption]; [lia|tini_ux]].
Local Ltac tini_uenv :=
  first [solve [assumption |
    eapply tini_UEnv_mono; [ | | eassumption]; [lia|tini_ux]]
    | solve [apply tini_UEnv_type; tini_uenv]
    | solve [apply tini_UEnv_label; tini_uenv]
    | solve [apply tini_UEnv_cons; [tini_uv_down|tini_uenv]]].
Local Ltac tini_uvw := first [tini_uenv|tini_uv_down].
Local Ltac tini_ub K IH v :=
  eapply (tini_ubind _ _ _ _ _ K); [eapply IH; tini_uvw|intros ? ? v ? ? ?].
Local Ltac tini_ushape v :=
  let H := fresh "Hshape" in
  match goal with H0 : UV (S _) _ _ v |- _ =>
    pose proof H0 as H; apply tini_Ustep in H; destruct v; simpl in H; try contradiction
  end.
Local Ltac tini_lift_uv v :=
  match goal with |- UE ?n ?W _ _ _ =>
    match goal with H : UV _ _ ?τ v |- _ =>
      let Hv := fresh "Hval" in assert (UV n W τ v) as Hv by tini_uvw; clear H
    end
  end.
Local Ltac tini_uhead_with shape :=
  eapply tini_ustep; [reflexivity|tini_ready|];
  let Hs := fresh "Hheap" in let Hh := fresh "Hhead" in
  let remaining := fresh "remaining" in
  intros remaining ? ? ? ? Hs Hh; subst; try shape;
  inversion Hh; clear Hh; subst;
  repeat match goal with H : to_val (#_) = Some _ |- _ =>
    rewrite tini_to_of in H; injection H as <-
  end.
Local Ltac tini_upure_with shape :=
  tini_uhead_with shape;
  (eexists; split; [apply tini_ext_refl|];
   split; [eapply tini_Uheap_mono; [|eassumption]; lia|];
   split; [apply tini_frame_refl|]).
Local Ltac tini_app_IH IH := eapply IH; tini_uenv.

Local Lemma tini_ufund Γ pc e τ :
  Γ # pc ⊢ₜ e : τ →
  ∀ a b n W γ, tini_UEnv Γ a b n W γ → UE n W pc.[a] (tini_sinst a b τ) e.[γ].
Proof.
  induction 1 as
    [Γ pc|Γ pc c|Γ pc k|Γ pc x τ Hx
    |Γ pc e p τ ν Hbody IH
    |Γ pc e1 e2 op l1 l2 H1 IH1 H2 IH2
    |Γ pc e1 e2 τ ν l p H1 IH1 H2 IH2 Hg Hf
    |Γ pc e1 e2 τ ν H1 IH1 H2 IH2
    |Γ pc e1 e2 τ ν H1 IH1 H2 IH2
    |Γ pc e τ p Hbody IH
    |Γ pc e τ t l p Hf Hg H1 IH1
    |Γ pc e τ p Hbody IH
    |Γ pc e τ l l' p Hf Hg H1 IH1
    |Γ pc e e1 e2 τ l H0 IH0 H1 IH1 H2 IH2 Hg
    |Γ pc e1 e2 τ ν H1 IH1 H2 IH2
    |Γ pc e τ ν l H1 IH1 Hg
    |Γ pc e τ ν l H1 IH1 Hg
    |Γ pc e τ ν H1 IH1
    |Γ pc e τ ν H1 IH1
    |Γ pc e e1 e2 τ ν υ l H0 IH0 H1 IH1 H2 IH2 Hg
    |Γ pc e τ H1 IH1 Hg
    |Γ pc e1 e2 τ l H1 IH1 H2 IH2 Hg
    |Γ pc e τ ν l H1 IH1 Hs Hg
    |Γ pc e τ t H1 IH1
    |Γ pc e1 e2 τ ν l Hg H1 IH1 H2 IH2
    |Γ pc e τ H1 IH1
    |Γ pc e τ l Hg H1 IH1
    |Γ pc e τ ν p H1 IH1 Hf Hs];
    intros a b n W γ Hγ; simpl.
  - apply (tini_uval _ _ _ _ UnitV). destruct n; first done. by apply tini_Ustep.
  - apply (tini_uval _ _ _ _ (BoolV c)). destruct n; first done. by apply tini_Ustep.
  - apply (tini_uval _ _ _ _ (NatV k)). destruct n; first done. by apply tini_Ustep.
  - destruct (Hγ _ _ Hx) as (v & -> & Hv). by apply tini_uval.
  - apply (tini_uval _ _ _ _ (LamV e.[up γ])).
    destruct n as [|n]; first done. apply tini_Ustep; simpl.
    intros m W' v Hm HW Hv. rewrite tini_beta. tini_app_IH IH.
  - tini_ub (BinOpLCtx op e2.[γ]) IH1 v1.
    tini_ub (BinOpRCtx op v1) IH2 v2. tini_lift_uv v1.
    tini_upure_with ltac:(try (tini_ushape v1; tini_ushape v2)).
    apply tini_uval. destruct remaining; first done. apply tini_Ustep. by destruct op.
  - tini_ub (AppLCtx e2.[γ]) IH1 f.
    tini_ub (AppRCtx f) IH2 w. tini_lift_uv f.
    tini_upure_with ltac:(try (tini_ushape f)).
    eapply (tini_Uflow _ _ _ p.[a]).
    + apply (tini_flow_subst a) in Hf. simpl in Hf.
      intros Hp. by apply (tini_effect _ _ _ Hf) in Hp as [].
    + eapply Hshape; [lia|apply tini_ext_refl|].
      eapply tini_Umono; [|apply tini_ext_refl|eassumption]; lia.
  - tini_ub (LetInCtx e2.[up γ]) IH1 v.
    tini_upure_with idtac. rewrite tini_beta. tini_app_IH IH2.
  - tini_ub (SeqCtx e2.[γ]) IH1 v. tini_upure_with idtac. tini_app_IH IH2.
  - apply (tini_uval _ _ _ _ (TLamV e.[γ])).
    destruct n as [|n]; first done. apply tini_Ustep; simpl.
    intros m W' t Hm HW. rewrite tini_type_beta. tini_app_IH IH.
  - rewrite tini_type_natural.
    tini_ub TAppCtx IH1 f. tini_upure_with ltac:(try (tini_ushape f)).
    specialize (Hshape remaining _ (tini_inst a b t) (Nat.le_refl _) (tini_ext_refl _)).
    rewrite tini_type_beta in Hshape. eapply tini_Uflow; last exact Hshape.
    apply (tini_flow_subst a) in Hf. simpl in Hf.
    intros Hp. by apply (tini_effect _ _ _ Hf) in Hp as [].
  - apply (tini_uval _ _ _ _ (TLLamV e.[γ])).
    destruct n as [|n]; first done. apply tini_Ustep; simpl.
    intros m W' l Hm HW. rewrite tini_label_beta, tini_label_beta_pc. tini_app_IH IH.
  - rewrite tini_label_natural.
    tini_ub TLAppCtx IH1 f. tini_upure_with ltac:(try (tini_ushape f)).
    specialize (Hshape remaining _ l'.[a] (Nat.le_refl _) (tini_ext_refl _)).
    rewrite tini_label_beta, tini_label_beta_pc in Hshape. eapply tini_Uflow; last exact Hshape.
    apply (tini_flow_subst a) in Hf. simpl in Hf. rewrite tini_label_single in Hf.
    intros Hp. by apply (tini_effect _ _ _ Hf) in Hp as [].
  - tini_ub (IfCtx e1.[γ] e2.[γ]) IH0 v.
    tini_upure_with ltac:(try (tini_ushape v)).
    all: eapply (tini_Uflow _ _ _ (pc.[a] ⊔ₛ l.[a]));
      [intros Hp; by apply tini_low_join in Hp as []|first [solve [tini_app_IH IH1]|tini_app_IH IH2]].
  - tini_ub (PairLCtx e2.[γ]) IH1 v1.
    tini_ub (PairRCtx v1) IH2 v2. tini_lift_uv v1.
    apply (tini_uval _ _ _ _ (PairV v1 v2)).
    match goal with |- UV ?n _ _ _ => destruct n; first done end.
    apply tini_Ustep; simpl. split; tini_uvw.
  - tini_ub Proj1Ctx IH1 v. tini_upure_with ltac:(try (tini_ushape v)).
    destruct Hshape. by apply tini_uval.
  - tini_ub Proj2Ctx IH1 v. tini_upure_with ltac:(try (tini_ushape v)).
    destruct Hshape. by apply tini_uval.
  - tini_ub InjLCtx IH1 v. apply (tini_uval _ _ _ _ (InjLV v)).
    match goal with |- UV ?n _ _ _ => destruct n; first done end.
    apply tini_Ustep; simpl; tini_uvw.
  - tini_ub InjRCtx IH1 v. apply (tini_uval _ _ _ _ (InjRV v)).
    match goal with |- UV ?n _ _ _ => destruct n; first done end.
    apply tini_Ustep; simpl; tini_uvw.
  - tini_ub (CaseCtx e1.[up γ] e2.[up γ]) IH0 v.
    tini_upure_with ltac:(try (tini_ushape v)).
    all: rewrite tini_beta; eapply (tini_Uflow _ _ _ (pc.[a] ⊔ₛ l.[a]));
      [intros Hp; by apply tini_low_join in Hp as []|first [solve [tini_app_IH IH1]|tini_app_IH IH2]].
  - tini_ub AllocCtx IH1 v. tini_uhead_with idtac.
    match goal with H : ?s !! ?l = None, HH : tini_UHeap _ ?W ?s |- _ =>
      pose proof (tini_ufresh _ _ _ _ HH H) as Hfresh;
      exists (<[l:=tini_sinst a b τ]>W)
    end.
    split; [by apply tini_ext_insert|].
    split.
    + apply tini_uheap_alloc; [exact Hfresh|eapply tini_Uheap_mono; [|eassumption]; lia|tini_uv_down].
    + split; first by apply tini_frame_alloc.
      apply (tini_uval _ _ _ _ (LocV l)). destruct remaining; first done.
      apply tini_Ustep. apply lookup_insert_eq.
  - tini_ub (StoreLCtx e2.[γ]) IH1 r.
    tini_ub (StoreRCtx r) IH2 v. tini_lift_uv r.
    tini_uhead_with ltac:(try (tini_ushape r)). eexists.
    split; [apply tini_ext_refl|]. split.
    + eapply tini_uheap_write; [exact Hshape|eapply tini_Uheap_mono; [|eassumption]; lia|tini_uv_down].
    + split.
      * eapply (tini_frame_write _ _ _ _ (tini_sinst a b τ)); [intros; congruence|].
        intros Hl. pose proof (tini_inst_flow a b _ _ Hg) as Hguard.
        apply (tini_guard _ _ Hguard) in Hl. by apply tini_low_join in Hl as [].
      * apply (tini_uval _ _ _ _ UnitV). destruct remaining; first done. by apply tini_Ustep.
  - tini_ub LoadCtx IH1 r. tini_upure_with ltac:(try (tini_ushape r)).
    apply tini_uval. eapply tini_usub; first exact Hs.
    match goal with HH : tini_UHeap _ _ ?s, Hl : ?s !! ?l = Some ?w |- _ =>
      let v := fresh "stored" in
      destruct (HH _ _ Hshape) as (v & ? & ?); assert (v = w) by congruence; subst v
    end.
    tini_uvw.
  - specialize (IH1 a b). rewrite tini_type_natural in IH1.
    tini_ub PackCtx IH1 v. apply (tini_uval _ _ _ _ (PackV v)).
    match goal with |- UV ?n _ _ _ => destruct n; first done end.
    apply tini_Ustep; simpl. exists (tini_inst a b t). rewrite tini_type_beta. tini_uvw.
  - tini_ub (UnpackCtx e2.[up γ]) IH1 v.
    tini_upure_with ltac:(try (tini_ushape v)).
    destruct Hshape as [witness Hv]. rewrite tini_type_beta in Hv.
    rewrite tini_beta. eapply (tini_Uflow _ _ _ (pc.[a] ⊔ₛ l.[a])); first (intros Hp; by apply tini_low_join in Hp as []).
    specialize (IH2 a (witness .: b)). rewrite tini_type_shift in IH2. tini_app_IH IH2.
  - specialize (IH1 a b). rewrite tini_type_natural in IH1.
    tini_ub FoldCtx IH1 v. apply (tini_uval _ _ _ _ (FoldV v)).
    match goal with |- UV ?n _ _ _ => destruct n; first done end.
    apply tini_Ustep; simpl. rewrite tini_type_beta. simpl in *. tini_uvw.
  - rewrite tini_type_natural.
    tini_ub UnfoldCtx IH1 v. tini_upure_with ltac:(try (tini_ushape v)).
    rewrite tini_type_beta in Hshape. simpl in Hshape. by apply tini_uval.
  - eapply (tini_Uflow _ _ _ p.[a]); first by eauto using tini_low_flow, tini_flow_subst.
    eapply tini_umap; [intros; eapply tini_usub; eauto|tini_app_IH IH1].
Qed.

(* Linked locations identify corresponding visible cells even when the two
   allocators choose different concrete addresses. *)
Record tini_bw := {
  tini_left : tini_world;
  tini_right : tini_world;
  tini_links : gmap (loc * loc) sectype
}.

Local Definition tini_bext W W' :=
  tini_extends (tini_left W) (tini_left W') ∧
  tini_extends (tini_right W) (tini_right W') ∧
  ∀ k τ, tini_links W !! k = Some τ → tini_links W' !! k = Some τ.

Local Lemma tini_bext_refl W : tini_bext W W.
Proof. repeat split; apply tini_ext_refl || done. Qed.

Local Lemma tini_bext_trans W W' W'' :
  tini_bext W W' → tini_bext W' W'' → tini_bext W W''.
Proof. intros (H1 & H2 & H3) (H4 & H5 & H6).
  repeat split; eauto using tini_ext_trans. Qed.

Local Definition tini_B := tini_bw → sectype → val → val → Prop.

Local Definition tini_bij (W : tini_bw) :=
  ∀ x y x' y' τ ν, tini_links W !! (x,y) = Some τ →
    tini_links W !! (x',y') = Some ν →
    x = x' ∨ y = y' → (x,y) = (x',y').

Local Definition tini_Blinks (R : tini_B) W (s1 s2 : state) :=
  ∀ x y τ, tini_links W !! (x,y) = Some τ →
    tini_visible τ ∧ tini_left W !! x = Some τ ∧ tini_right W !! y = Some τ ∧
    ∃ v1 v2, s1 !! x = Some v1 ∧ s2 !! y = Some v2 ∧ R W τ v1 v2.

Local Definition tini_BHeap (U : tini_U) (R : tini_B) W s1 s2 :=
  tini_UHeap U (tini_left W) s1 ∧ tini_UHeap U (tini_right W) s2 ∧
  tini_bij W ∧ tini_Blinks R W s1 s2.

Local Definition tini_BE (R : nat → tini_B) n W τ e1 e2 :=
  ∀ i j s1 s2 v1 v2 t1 t2, i+j ≤ n →
    tini_BHeap (tini_uv n) (R n) W s1 s2 →
    run i e1 s1 v1 t1 → run j e2 s2 v2 t2 →
    ∃ W', tini_bext W W' ∧
      tini_BHeap (tini_uv (n-i-j)) (R (n-i-j)) W' t1 t2 ∧
      R (n-i-j) W' τ v1 v2.

Local Definition tini_Blayer (R : nat → tini_B) n W τ v1 v2 : Prop :=
  let '(t @ l) := τ in
  tini_low l →
  match t, v1, v2 with
  | TUnit, UnitV, UnitV => True
  | TBool, BoolV b, BoolV b' => b = b'
  | TNat, NatV k, NatV k' => k = k'
  | TRef τ, LocV l1, LocV l2 => tini_visible τ → tini_links W !! (l1,l2) = Some τ
  | TProd τ ν, PairV a b, PairV a' b' => R n W τ a a' ∧ R n W ν b b'
  | TSum τ _, InjLV a, InjLV b | TSum _ τ, InjRV a, InjRV b => R n W τ a b
  | TRec τ, FoldV a, FoldV b => R n W (τ.|[TRec τ/]) a b
  | TExist τ, PackV a, PackV b => ∃ t, R n W (τ.|[t/]) a b
  | TArrow _ τ ν, LamV e1, LamV e2 =>
    ∀ m W' a b, m ≤ n → tini_bext W W' → R m W' τ a b →
      tini_BE R m W' ν e1.[#a/] e2.[#b/]
  | TForall _ τ, TLamV e1, TLamV e2 =>
    ∀ m W' t, m ≤ n → tini_bext W W' → tini_BE R m W' (τ.|[t/]) e1 e2
  | TLForall _ τ, TLLamV e1, TLLamV e2 =>
    ∀ m W' (l : label_term), m ≤ n → tini_bext W W' → tini_BE R m W' (τ.|[l/]) e1 e2
  | _, _, _ => False
  end.

Local Definition tini_Bun n W τ v1 v2 :=
  UV n (tini_left W) τ v1 ∧ UV n (tini_right W) τ v2.
Local Definition tini_Bzero : tini_B := λ W τ v1 v2, tini_Bun 0 W τ v1 v2.
Local Definition tini_Bentry R n : tini_B := λ W τ v1 v2,
  tini_Bun (S n) W τ v1 v2 ∧ tini_Blayer R n W τ v1 v2.
Local Fixpoint tini_Btable n : list tini_B :=
  match n with
  | 0 => [tini_Bzero]
  | S n => let table := tini_Btable n in
    table ++ [tini_Bentry (λ m, List.nth m table tini_Bzero) n]
  end.
Local Definition tini_bv n : tini_B := List.nth n (tini_Btable n) tini_Bzero.

Local Lemma tini_Blength n : length (tini_Btable n) = S n.
Proof. induction n; simpl; [done|rewrite length_app, IHn; simpl; lia]. Qed.

Local Lemma tini_Blookup m n : m ≤ n → List.nth m (tini_Btable n) tini_Bzero = tini_bv m.
Proof.
  induction 1 as [|n Hmn IH]; first done.
  simpl. rewrite List.app_nth1; first done. rewrite tini_Blength. lia.
Qed.

Local Lemma tini_BE_ext R R' n W τ e1 e2 :
  (∀ i, i ≤ n → R i = R' i) →
  tini_BE R n W τ e1 e2 → tini_BE R' n W τ e1 e2.
Proof.
  intros HE HR i j s1 s2 v1 v2 t1 t2 Hij Hs Hr1 Hr2.
  rewrite <- (HE _ (Nat.le_refl n)) in Hs.
  rewrite <- (HE (n-i-j) ltac:(lia)). by eapply HR.
Qed.

Local Lemma tini_Blayer_ext R R' n W τ v1 v2 :
  (∀ i, i ≤ n → R i = R' i) →
  tini_Blayer R n W τ v1 v2 → tini_Blayer R' n W τ v1 v2.
Proof.
  intros HE. destruct τ as [l t]; destruct t, v1, v2; simpl; try tauto;
    try (rewrite (HE _ (Nat.le_refl n)); tauto).
  - intros HR Hl m W' a b Hm HW Hv.
    eapply tini_BE_ext; first (intros; apply HE; lia).
    eapply HR; eauto. by rewrite (HE _ Hm).
  - intros HR Hl m W' t Hm HW. eapply tini_BE_ext; [intros; apply HE; lia|eapply HR; eauto].
  - intros HR Hl m W' l' Hm HW. eapply tini_BE_ext; [intros; apply HE; lia|eapply HR; eauto].
Qed.

Local Lemma tini_Bstep n W τ v1 v2 :
  tini_bv (S n) W τ v1 v2 ↔ tini_Bun (S n) W τ v1 v2 ∧ tini_Blayer tini_bv n W τ v1 v2.
Proof.
  unfold tini_bv at 1. simpl. rewrite List.app_nth2; last (rewrite tini_Blength; lia). rewrite tini_Blength.
  replace (S n - S n) with 0 by lia. simpl.
  unfold tini_Bentry. split; intros [Hu Hb]; split; try exact Hu.
  - eapply (tini_Blayer_ext _ tini_bv); last exact Hb.
    intros i Hi. exact (tini_Blookup i n Hi).
  - eapply (tini_Blayer_ext tini_bv _); last exact Hb.
    intros i Hi. symmetry. exact (tini_Blookup i n Hi).
Qed.

Local Lemma tini_Bun_of n W τ v1 v2 : tini_bv n W τ v1 v2 → tini_Bun n W τ v1 v2.
Proof. destruct n; first done. intros [Hu _]%tini_Bstep. done. Qed.

Local Lemma tini_Bhigh n W τ v1 v2 :
  ¬ tini_visible τ → tini_Bun n W τ v1 v2 → tini_bv n W τ v1 v2.
Proof. intros Hh Hu. destruct n; first done. apply tini_Bstep. split; first done.
  destruct τ. simpl in *. tauto.
Qed.

Local Lemma tini_Bmono n m W W' τ v1 v2 :
  m ≤ n → tini_bext W W' → tini_bv n W τ v1 v2 → tini_bv m W' τ v1 v2.
Proof.
  revert m W W' τ v1 v2. induction n as [|n IH];
    intros [|m] W W' [l t] v1 v2 Hm HW Hv; try done; try lia.
  apply tini_Bstep in Hv as [[Hu1 Hu2] Hv]. apply tini_Bstep. split.
  { destruct HW as (HE1 & HE2 & _). split; eauto using tini_Umono. }
  cbn [tini_Blayer] in Hv |- *. intros Hl. specialize (Hv Hl).
  apply tini_Ustep in Hu1, Hu2.
  destruct t, v1; cbn [tini_Ulayer] in Hu1; try contradiction.
  all: destruct v2; cbn [tini_Ulayer] in Hu2; try contradiction.
  all: cbn in Hv |- *; try contradiction; try exact Hv.
  all: try solve [destruct HW as (_ & _ & HW); intro; eapply HW, Hv; assumption].
  all: try solve [eapply (IH m W W'); [lia|exact HW|exact Hv]].
  all: try solve [destruct Hv as [Ha Hb]; split;
    (eapply (IH m W W'); [lia|exact HW|eassumption])].
  all: try solve [destruct Hv as [t Ht]; exists t;
    eapply (IH m W W'); [lia|exact HW|exact Ht]].
  all: intros; eapply Hv; try lia; try eassumption;
    eapply tini_bext_trans; eassumption.
Qed.

Local Lemma tini_Bheap_mono n m W s1 s2 :
  m ≤ n → tini_BHeap (tini_uv n) (tini_bv n) W s1 s2 →
  tini_BHeap (tini_uv m) (tini_bv m) W s1 s2.
Proof.
  intros Hm (H1 & H2 & Hb & Hs).
  split; first by eapply tini_Uheap_mono.
  split; first by eapply tini_Uheap_mono.
  split; first done.
  intros x y τ Hxy. destruct (Hs _ _ _ Hxy) as (Hl & Hx & Hy & v1 & v2 & E1 & E2 & Hv).
  repeat split; try assumption. exists v1, v2.
  eauto using tini_Bmono, tini_bext_refl.
Qed.

Local Notation "'BE' n W τ e1 e2" := (tini_BE tini_bv n W τ e1 e2)
  (at level 10, n, W, τ, e1, e2 at next level).
Local Notation "'BV' n W τ v1 v2" := (tini_bv n W τ v1 v2)
  (at level 10, n, W, τ, v1, v2 at next level).

Local Lemma tini_bval n W τ v1 v2 : BV n W τ v1 v2 → BE n W τ (#v1) (#v2).
Proof.
  intros Hv i j s1 s2 w1 w2 t1 t2 Hij Hs Hr1 Hr2.
  destruct (tini_run_value _ _ _ _ _ Hr1) as (-> & -> & ->).
  destruct (tini_run_value _ _ _ _ _ Hr2) as (-> & -> & ->).
  rewrite !Nat.sub_0_r. exists W. eauto using tini_bext_refl.
Qed.

Local Lemma tini_bstep n W τ e1 e2 :
  to_val e1 = None → to_val e2 = None →
  (∀ K a, e1 = fill_item K a → is_Some (to_val a)) →
  (∀ K a, e2 = fill_item K a → is_Some (to_val a)) →
  (∀ m s1 s2 z1 z2 t1 t2, S (S m) = n → tini_BHeap (tini_uv n) (tini_bv n) W s1 s2 →
     head_step e1 s1 [] z1 t1 [] → head_step e2 s2 [] z2 t2 [] →
     ∃ W', tini_bext W W' ∧ tini_BHeap (tini_uv m) (tini_bv m) W' t1 t2 ∧ BE m W' τ z1 z2) →
  BE n W τ e1 e2.
Proof.
  intros Hv1 Hv2 Hctx1 Hctx2 Hstep i j s1 s2 v1 v2 t1 t2 Hij Hs Hr1 Hr2.
  destruct (tini_run_head _ _ _ _ _ Hv1 Hctx1 Hr1) as (i' & z1 & u1 & -> & Hh1 & Hi').
  destruct (tini_run_head _ _ _ _ _ Hv2 Hctx2 Hr2) as (j' & z2 & u2 & -> & Hh2 & Hj').
  destruct n as [|[|n]]; try lia.
  destruct (Hstep _ _ _ _ _ _ _ eq_refl Hs Hh1 Hh2) as (W' & HW & Hu & HE).
  destruct (HE i' j' u1 u2 v1 v2 t1 t2 ltac:(lia) Hu Hi' Hj') as (W'' & HW' & Ht & Hval).
  replace (S (S n) - S i' - S j') with (n-i'-j') by lia.
  exists W''. eauto using tini_bext_trans.
Qed.

Local Lemma tini_bbind n W τ ν K1 K2 e1 e2 :
  BE n W τ e1 e2 →
  (∀ m W' w1 w2, m ≤ n → tini_bext W W' → BV m W' τ w1 w2 →
    BE m W' ν (fill_item K1 (#w1)) (fill_item K2 (#w2))) →
  BE n W ν (fill_item K1 e1) (fill_item K2 e2).
Proof.
  intros HE HK i j s1 s2 v1 v2 t1 t2 Hij Hs Hr1 Hr2.
  destruct (tini_run_item _ _ _ _ _ _ Hr1) as (i' & k & w1 & u1 & -> & Hi' & Hk).
  destruct (tini_run_item _ _ _ _ _ _ Hr2) as (j' & l & w2 & u2 & -> & Hj' & Hl).
  destruct (HE i' j' s1 s2 w1 w2 u1 u2 ltac:(lia) Hs Hi' Hj') as (W' & HW & Hu & Hv).
  destruct (HK (n-i'-j') W' w1 w2 ltac:(lia) HW Hv k l u1 u2 v1 v2 t1 t2 ltac:(lia) Hu Hk Hl) as
    (W'' & HW' & Ht & Hval).
  replace (n - (i'+k) - (j'+l)) with (n-i'-j'-k-l) by lia.
  exists W''. eauto using tini_bext_trans.
Qed.

Local Lemma tini_bmap n W τ ν e1 e2 :
  (∀ m W' v1 v2, BV m W' τ v1 v2 → BV m W' ν v1 v2) →
  BE n W τ e1 e2 → BE n W ν e1 e2.
Proof.
  intros Hf HE i j s1 s2 v1 v2 t1 t2 Hij Hs Hr1 Hr2.
  destruct (HE _ _ _ _ _ _ _ _ Hij Hs Hr1 Hr2) as (W' & HW & Ht & Hv).
  exists W'. eauto.
Qed.

(* At a high branch or call, execute each side using unary confinement.
   The linked cells retain their contents while each world can grow. *)
Local Lemma tini_bsplit n W pc1 pc2 τ e1 e2 :
  ¬ tini_low pc1 → ¬ tini_low pc2 → ¬ tini_visible τ →
  UE n (tini_left W) pc1 τ e1 → UE n (tini_right W) pc2 τ e2 →
  BE n W τ e1 e2.
Proof.
  intros Hp1 Hp2 Hτ HE1 HE2 i j s1 s2 v1 v2 t1 t2 Hij (Hs1 & Hs2 & Hb & Hs) Hr1 Hr2.
  destruct (HE1 i s1 v1 t1 ltac:(lia) Hs1 Hr1) as (W1 & HW1 & Ht1 & Hv1 & Hf1).
  destruct (HE2 j s2 v2 t2 ltac:(lia) Hs2 Hr2) as (W2 & HW2 & Ht2 & Hv2 & Hf2).
  set (W' := {| tini_left := W1; tini_right := W2; tini_links := tini_links W |}).
  assert (tini_bext W W') as HW by (repeat split; eauto).
  exists W'. split; first done. split.
  - split; first (eapply tini_Uheap_mono; [|apply Ht1]; lia).
    split; first (eapply tini_Uheap_mono; [|apply Ht2]; lia).
    split; first exact Hb.
    intros x y ν Hxy.
    destruct (Hs _ _ _ Hxy) as (Hl & Hx & Hy & w1 & w2 & E1 & E2 & Hv).
    repeat split; try done; try by apply HW1 || apply HW2.
    exists w1, w2.
    rewrite (Hf1 Hp1 _ _ Hx Hl), (Hf2 Hp2 _ _ Hy Hl).
    repeat split; try done. eapply tini_Bmono; [|apply HW|apply Hv]; lia.
  - apply tini_Bhigh; first done. split; eapply tini_Umono;
      try apply tini_ext_refl; [|apply Hv1| |apply Hv2]; lia.
Qed.

Local Lemma tini_bstamp_sub n W l l' t t' v1 v2 :
  (tini_low l' → tini_low l) →
  (UV n (tini_left W) (t @ l) v1 → UV n (tini_left W) (t' @ l') v1) →
  (UV n (tini_right W) (t @ l) v2 → UV n (tini_right W) (t' @ l') v2) →
  (BV n W (t @ l) v1 v2 → BV n W (t' @ l) v1 v2) →
  BV n W (t @ l) v1 v2 → BV n W (t' @ l') v1 v2.
Proof.
  intros Hflow H1 H2 Hs Hv. destruct n; first done.
  pose proof (Hs Hv) as Ht. apply tini_Bstep in Hv as [[Hu1 Hu2] _].
  apply tini_Bstep in Ht as [_ Ht]. apply tini_Bstep. split.
  - split; auto.
  - cbn [tini_Blayer] in Ht |- *. intro Hl. exact (Ht (Hflow Hl)).
Qed.

Local Lemma tini_bsub_all :
  (∀ t t', t <: t' → ∀ a b n W l v1 v2,
    BV n W (tini_inst a b t @ l) v1 v2 → BV n W (tini_inst a b t' @ l) v1 v2) ∧
  (∀ τ τ', τ <:ₛ τ' → ∀ a b n W v1 v2,
    BV n W (tini_sinst a b τ) v1 v2 → BV n W (tini_sinst a b τ') v1 v2).
Proof.
  apply tini_sub_ind.
  - done.
  - intros. eauto.
  - intros τ1 τ1' τ2 τ2' p1 p2 H1 IH1 H2 IH2 Hf a b [|n] W l v1 v2 Hv; first done.
    apply tini_Bstep in Hv as [[Hu1 Hu2] Hv]. apply tini_Bstep. split.
    { split; eapply (proj1 tini_usub_all); eauto using TArrowSub. }
    simpl in *. intros Hl. specialize (Hv Hl). destruct v1, v2; try contradiction.
    intros m W' x y Hm HW Hxy. eapply tini_bmap; [intros; eapply IH2; eauto|].
    eapply Hv; eauto.
  - intros τ1 τ2 p1 p2 HF Hs IH a b [|n] W l v1 v2 Hv; first done.
    apply tini_Bstep in Hv as [[Hu1 Hu2] Hv]. apply tini_Bstep. split.
    { split; eapply (proj1 tini_usub_all); eauto using TForallSub. }
    simpl in *. intros Hl. specialize (Hv Hl). destruct v1, v2; try contradiction.
    intros m W' t Hm HW. rewrite tini_type_beta.
    eapply tini_bmap; [intros; eapply IH; eauto|].
    specialize (Hv _ _ t Hm HW). by rewrite tini_type_beta in Hv.
  - intros τ1 τ2 p1 p2 HF Hs IH a b [|n] W l v1 v2 Hv; first done.
    apply tini_Bstep in Hv as [[Hu1 Hu2] Hv]. apply tini_Bstep. split.
    { split; eapply (proj1 tini_usub_all); eauto using TLForallSub. }
    simpl in *. intros Hl. specialize (Hv Hl). destruct v1, v2; try contradiction.
    intros m W' l' Hm HW. rewrite tini_label_beta.
    eapply tini_bmap; [intros; eapply IH; eauto|].
    specialize (Hv _ _ l' Hm HW). by rewrite tini_label_beta in Hv.
  - intros τ1 τ1' τ2 τ2' H1 IH1 H2 IH2 a b [|n] W l v1 v2 Hv; first done.
    apply tini_Bstep in Hv as [[Hu1 Hu2] Hv]. apply tini_Bstep. split.
    { split; eapply (proj1 tini_usub_all); eauto using TProdSub. }
    simpl in *. intros Hl. specialize (Hv Hl). destruct v1, v2; intuition eauto.
  - intros τ1 τ1' τ2 τ2' H1 IH1 H2 IH2 a b [|n] W l v1 v2 Hv; first done.
    apply tini_Bstep in Hv as [[Hu1 Hu2] Hv]. apply tini_Bstep. split.
    { split; eapply (proj1 tini_usub_all); eauto using TSumSub. }
    simpl in *. intros Hl. specialize (Hv Hl). destruct v1, v2; intuition eauto.
  - intros τ1 τ2 Hs IH a b [|n] W l v1 v2 Hv; first done.
    apply tini_Bstep in Hv as [[Hu1 Hu2] Hv]. apply tini_Bstep. split.
    { split; eapply (proj1 tini_usub_all); eauto using TRecSub. }
    simpl in *. intros Hl. specialize (Hv Hl). destruct v1, v2; try contradiction.
    specialize (IH a b n W v1 v2). rewrite !tini_type_natural in IH. simpl in IH.
    rewrite !tini_type_beta in *. eauto.
  - simpl. intros l l' t t' HF Hs IH a b n W v1 v2 Hv.
    eapply tini_bstamp_sub; last exact Hv.
    + eauto using tini_low_flow, tini_flow_subst.
    + exact (tini_usub _ _ a b n (tini_left W) v1 (TSubsec _ _ _ _ HF Hs)).
    + exact (tini_usub _ _ a b n (tini_right W) v2 (TSubsec _ _ _ _ HF Hs)).
    + apply IH.
Qed.

Local Lemma tini_bsub τ τ' a b n W v1 v2 :
  τ <:ₛ τ' → BV n W (tini_sinst a b τ) v1 v2 → BV n W (tini_sinst a b τ') v1 v2.
Proof. intros Hs. exact ((proj2 tini_bsub_all) τ τ' Hs a b n W v1 v2). Qed.

Local Definition tini_BEnv (Γ : list sectype) a b n W (γ1 γ2 : var → expr) :=
  ∀ x τ, Γ !! x = Some τ →
    ∃ v1 v2, γ1 x = #v1 ∧ γ2 x = #v2 ∧ BV n W (tini_sinst a b τ) v1 v2.

Local Lemma tini_BEnv_un Γ a b n W γ1 γ2 :
  tini_BEnv Γ a b n W γ1 γ2 →
  tini_UEnv Γ a b n (tini_left W) γ1 ∧ tini_UEnv Γ a b n (tini_right W) γ2.
Proof.
  intros Hγ. split; intros x τ Hx;
    destruct (Hγ _ _ Hx) as (v1 & v2 & E1 & E2 & [Hv1 Hv2]%tini_Bun_of);
    eauto.
Qed.

Local Lemma tini_BEnv_mono Γ a b n m W W' γ1 γ2 :
  m ≤ n → tini_bext W W' → tini_BEnv Γ a b n W γ1 γ2 → tini_BEnv Γ a b m W' γ1 γ2.
Proof.
  intros Hm HW Hγ x τ Hx. destruct (Hγ _ _ Hx) as (v1 & v2 & -> & -> & Hv).
  exists v1, v2. eauto using tini_Bmono.
Qed.

Local Lemma tini_BEnv_cons Γ a b n W γ1 γ2 τ v1 v2 :
  BV n W (tini_sinst a b τ) v1 v2 → tini_BEnv Γ a b n W γ1 γ2 →
  tini_BEnv (τ :: Γ) a b n W (#v1 .: γ1) (#v2 .: γ2).
Proof.
  intros Hv Hγ [|x] ν; simpl; first (intros [= <-]; eauto).
  apply Hγ.
Qed.

Local Lemma tini_BEnv_type Γ a b n W γ1 γ2 t :
  tini_BEnv Γ a b n W γ1 γ2 →
  tini_BEnv (hsubst_sectype (ren (+1)) <$> Γ) a (t .: b) n W γ1 γ2.
Proof.
  intros Hγ x τ Hx. apply list_lookup_fmap_Some in Hx as (ν & -> & E). rewrite tini_type_shift. by eapply Hγ.
Qed.

Local Lemma tini_BEnv_label Γ a b n W γ1 γ2 l :
  tini_BEnv Γ a b n W γ1 γ2 →
  tini_BEnv (hsubst_label_sectype (ren (+1)) <$> Γ) (l .: a) b n W γ1 γ2.
Proof.
  intros Hγ x τ Hx. apply list_lookup_fmap_Some in Hx as (ν & -> & E). rewrite tini_label_shift. by eapply Hγ.
Qed.

Local Lemma tini_Balloc n m W s1 s2 l1 l2 τ v1 v2 :
  m ≤ n → tini_BHeap (tini_uv n) (tini_bv n) W s1 s2 →
  s1 !! l1 = None → s2 !! l2 = None → BV n W τ v1 v2 →
  ∃ W', tini_bext W W' ∧
    tini_BHeap (tini_uv m) (tini_bv m) W' (<[l1:=v1]>s1) (<[l2:=v2]>s2) ∧
    BV m W' (TRef τ @ ⊥ₛ) (LocV l1) (LocV l2).
Proof.
  intros Hm (Hs1 & Hs2 & Hb & Hs) Hf1 Hf2 Hvs.
  pose proof (tini_ufresh _ _ _ _ Hs1 Hf1) as HW1.
  pose proof (tini_ufresh _ _ _ _ Hs2 Hf2) as HW2.
  assert (Hlink : ∀ x y ν, tini_links W !! (x,y) = Some ν → l1 ≠ x ∧ l2 ≠ y).
  { intros x y ν Hxy. destruct (Hs _ _ _ Hxy) as (_ & Hx & Hy & _).
    split; intros <-; congruence. }
  assert (Hnot : tini_links W !! (l1,l2) = None).
  { destruct (tini_links W !! (l1,l2)) eqn:E; last done. by destruct (Hlink _ _ _ E). }
  destruct (tini_low_dec (tini_lat τ)) as [Hl|Hl].
  1: pose (W' := {| tini_left := <[l1:=τ]> (tini_left W);
                  tini_right := <[l2:=τ]> (tini_right W);
                  tini_links := <[(l1,l2):=τ]> (tini_links W) |}).
  2: pose (W' := {| tini_left := <[l1:=τ]> (tini_left W);
                  tini_right := <[l2:=τ]> (tini_right W); tini_links := tini_links W |}).
  all: assert (tini_bext W W') as HW by
    (split; [exact (tini_ext_insert _ _ _ HW1)|];
     split; [exact (tini_ext_insert _ _ _ HW2)|];
     simpl; intros k ν Hk;
     first [exact Hk |
       rewrite (lookup_insert_ne (tini_links W) (l1,l2) k τ); [exact Hk|intros <-; congruence]]).
  all: destruct (tini_Bun_of _ _ _ _ _ Hvs) as [Hu1 Hu2]; exists W'; split; first done; split.
  2,4: (destruct m as [|m]; first done; apply tini_Bstep; split;
    [split; apply tini_Ustep; apply lookup_insert_eq| simpl; intros _ Hvis;
    first [apply lookup_insert_eq|contradiction]]).
  all: split; first (apply tini_uheap_alloc; eauto using tini_Uheap_mono, tini_Umono, tini_ext_refl);
    split; first (apply tini_uheap_alloc; eauto using tini_Uheap_mono, tini_Umono, tini_ext_refl);
    split; simpl in *.
  - intros x y x' y' ν ν' Hxy Hxy' E.
    cbn [W' tini_links] in Hxy, Hxy'.
    destruct (decide ((l1,l2) = (x,y))) as [He|Hne],
      (decide ((l1,l2) = (x',y'))) as [He'|Hne']; try congruence.
    + rewrite (lookup_insert_ne (tini_links W) (l1,l2) (x',y') τ Hne') in Hxy'. destruct (Hlink _ _ _ Hxy').
      injection He as <- <-. tauto.
    + rewrite (lookup_insert_ne (tini_links W) (l1,l2) (x,y) τ Hne) in Hxy. destruct (Hlink _ _ _ Hxy).
      injection He' as <- <-. destruct E; congruence.
    + rewrite (lookup_insert_ne (tini_links W) (l1,l2) (x,y) τ Hne) in Hxy.
      rewrite (lookup_insert_ne (tini_links W) (l1,l2) (x',y') τ Hne') in Hxy'.
      eapply Hb; eassumption.
  - intros x y ν Hxy. cbn [W' tini_links tini_left tini_right] in Hxy |- *.
    destruct (decide ((l1,l2) = (x,y))) as [E|Hne].
    + injection E as <- <-. rewrite (lookup_insert_eq (tini_links W) (l1,l2) τ) in Hxy. injection Hxy as <-.
      repeat split; try assumption; try apply lookup_insert_eq.
      exists v1, v2. rewrite (lookup_insert_eq s1 l1 v1), (lookup_insert_eq s2 l2 v2). eauto using tini_Bmono.
    + rewrite (lookup_insert_ne (tini_links W) (l1,l2) (x,y) τ Hne) in Hxy.
      destruct (Hlink _ _ _ Hxy) as [Hne1 Hne2].
      destruct (Hs _ _ _ Hxy) as (Hv & Hx & Hy & w1 & w2 & E1 & E2 & Hvs').
      rewrite (lookup_insert_ne (tini_left W) l1 x τ Hne1),
        (lookup_insert_ne (tini_right W) l2 y τ Hne2),
        (lookup_insert_ne s1 l1 x v1 Hne1), (lookup_insert_ne s2 l2 y v2 Hne2).
      repeat split; try assumption. exists w1, w2.
      repeat split; eauto using tini_Bmono.
  - exact Hb.
  - intros x y ν Hxy. cbn [W' tini_links tini_left tini_right] in Hxy |- *.
    destruct (Hlink _ _ _ Hxy) as [Hne1 Hne2].
    destruct (Hs _ _ _ Hxy) as (Hv & Hx & Hy & w1 & w2 & E1 & E2 & Hvs').
    rewrite (lookup_insert_ne (tini_left W) l1 x τ Hne1),
        (lookup_insert_ne (tini_right W) l2 y τ Hne2),
        (lookup_insert_ne s1 l1 x v1 Hne1), (lookup_insert_ne s2 l2 y v2 Hne2).
      repeat split; try assumption. exists w1, w2.
      repeat split; eauto using tini_Bmono.
Qed.

Local Lemma tini_Bwrite n m W s1 s2 l1 l2 τ v1 v2 :
  m ≤ n → tini_BHeap (tini_uv n) (tini_bv n) W s1 s2 →
  tini_left W !! l1 = Some τ → tini_right W !! l2 = Some τ →
  (tini_visible τ → tini_links W !! (l1,l2) = Some τ) →
  BV n W τ v1 v2 →
  tini_BHeap (tini_uv m) (tini_bv m) W (<[l1:=v1]>s1) (<[l2:=v2]>s2).
Proof.
  intros Hm (Hs1 & Hs2 & Hb & Hs) H1 H2 Hl Hvs.
  destruct (tini_Bun_of _ _ _ _ _ Hvs) as [Hu1 Hu2].
  split; first (eapply tini_uheap_write; eauto using tini_Uheap_mono, tini_Umono, tini_ext_refl).
  split; first (eapply tini_uheap_write; eauto using tini_Uheap_mono, tini_Umono, tini_ext_refl).
  split; first done.
  intros x y ν Hxy.
  destruct (Hs _ _ _ Hxy) as (Hvis & Hx & Hy & w1 & w2 & E1 & E2 & Hw).
  destruct (decide (l1 = x ∨ l2 = y)) as [He|Hne].
  - assert (ν = τ) as -> by (destruct He as [<-|<-]; congruence).
    pose proof (Hb _ _ _ _ _ _ (Hl Hvis) Hxy He) as E.
    inversion E; subst x y.
    repeat split; try assumption. exists v1, v2.
    rewrite (lookup_insert_eq s1 l1 v1), (lookup_insert_eq s2 l2 v2).
    eauto using tini_Bmono, tini_bext_refl.
  - rewrite (lookup_insert_ne s1 l1 x v1), (lookup_insert_ne s2 l2 y v2); try tauto.
    repeat split; try assumption. exists w1, w2.
    repeat split; eauto using tini_Bmono, tini_bext_refl.
Qed.

Local Lemma tini_BEnv_left Γ a b n m W W' γ1 γ2 :
  m ≤ n → tini_bext W W' → tini_BEnv Γ a b n W γ1 γ2 →
  tini_UEnv Γ a b m (tini_left W') γ1.
Proof.
  intros Hm HW Hγ. exact (proj1 (tini_BEnv_un _ _ _ _ _ _ _
    (tini_BEnv_mono _ _ _ _ _ _ _ _ _ Hm HW Hγ))).
Qed.
Local Lemma tini_BEnv_right Γ a b n m W W' γ1 γ2 :
  m ≤ n → tini_bext W W' → tini_BEnv Γ a b n W γ1 γ2 →
  tini_UEnv Γ a b m (tini_right W') γ2.
Proof.
  intros Hm HW Hγ. exact (proj2 (tini_BEnv_un _ _ _ _ _ _ _
    (tini_BEnv_mono _ _ _ _ _ _ _ _ _ Hm HW Hγ))).
Qed.

Local Lemma tini_BEnv_uleft Γ a b n m W W' γ1 γ2 :
  m ≤ n → tini_extends (tini_left W) W' → tini_BEnv Γ a b n W γ1 γ2 →
  tini_UEnv Γ a b m W' γ1.
Proof.
  intros Hm HW Hγ. eapply tini_UEnv_mono; [exact Hm|exact HW|].
  exact (proj1 (tini_BEnv_un _ _ _ _ _ _ _ Hγ)).
Qed.

Local Lemma tini_BEnv_uright Γ a b n m W W' γ1 γ2 :
  m ≤ n → tini_extends (tini_right W) W' → tini_BEnv Γ a b n W γ1 γ2 →
  tini_UEnv Γ a b m W' γ2.
Proof.
  intros Hm HW Hγ. eapply tini_UEnv_mono; [exact Hm|exact HW|].
  exact (proj2 (tini_BEnv_un _ _ _ _ _ _ _ Hγ)).
Qed.

Local Ltac tini_bx :=
  solve [assumption | apply tini_bext_refl | eapply tini_bext_trans; eassumption].
Local Ltac tini_bv_down :=
  solve [assumption |
    eapply tini_Bmono; [ | | eassumption]; [lia|tini_bx]].
Local Ltac tini_benv :=
  first [solve [assumption |
    eapply tini_BEnv_mono; [ | | eassumption]; [lia|tini_bx]]
    | solve [apply tini_BEnv_type; tini_benv]
    | solve [apply tini_BEnv_label; tini_benv]
    | solve [apply tini_BEnv_cons; [tini_bv_down|tini_benv]]].
Local Ltac tini_bvw :=
  lazymatch goal with
  | |- tini_BEnv _ _ _ _ _ _ _ => tini_benv
  | |- BV _ _ _ _ _ => tini_bv_down
  end.
Local Ltac tini_uenv_bin :=
  first [solve [tini_uenv]
    | solve [eapply tini_BEnv_uleft; [ | | eassumption]; [lia|tini_ux]]
    | solve [eapply tini_BEnv_uright; [ | | eassumption]; [lia|tini_ux]]
    | solve [eapply tini_BEnv_left; [ | | eassumption]; [lia|tini_bx]]
    | solve [eapply tini_BEnv_right; [ | | eassumption]; [lia|tini_bx]]
    | solve [apply tini_UEnv_type; tini_uenv_bin]
    | solve [apply tini_UEnv_label; tini_uenv_bin]
    | solve [apply tini_UEnv_cons; [tini_uv_down|tini_uenv_bin]]].
Local Ltac tini_bb K1 K2 IH v1 v2 :=
  eapply (tini_bbind _ _ _ _ K1 K2); [eapply IH; tini_bvw|intros ? ? v1 v2 ? ? ?].
Local Ltac tini_bshape x y :=
  let H := fresh "Hshape" in let Hu1 := fresh "Hu1" in let Hu2 := fresh "Hu2" in
  match goal with H0 : BV (S _) _ _ x y |- _ =>
    pose proof H0 as H; apply tini_Bstep in H as [[Hu1 Hu2] H];
    apply tini_Ustep in Hu1, Hu2; destruct x, y; simpl in H, Hu1, Hu2; try contradiction
  end.
Local Ltac tini_lift_bv x y :=
  match goal with |- BE ?n ?W _ _ _ =>
    match goal with H : BV _ _ ?τ x y |- _ =>
      let Hv := fresh "Hvals" in assert (BV n W τ x y) as Hv by tini_bvw; clear H
    end
  end.
Local Ltac tini_bhead_with shape :=
  eapply tini_bstep; [reflexivity|reflexivity|tini_ready|tini_ready|];
  let Hs := fresh "Hheap" in let Hh1 := fresh "Hhead1" in let Hh2 := fresh "Hhead2" in
  let remaining := fresh "remaining" in
  intros remaining ? ? ? ? ? ? ? Hs Hh1 Hh2; subst; try shape;
  inversion Hh1; clear Hh1; subst;
  inversion Hh2; clear Hh2; subst;
  repeat match goal with H : to_val (#_) = Some _ |- _ =>
    rewrite tini_to_of in H; injection H as <-
  end.
Local Ltac tini_bpure_with shape :=
  tini_bhead_with shape;
  (eexists; split; [apply tini_bext_refl|];
   split; [eapply tini_Bheap_mono; [|eassumption]; lia|]).
Local Ltac tini_bI IH := eapply IH; tini_benv.
Local Ltac tini_uI Ht := eapply (tini_ufund _ _ _ _ Ht); tini_uenv_bin.
Local Ltac tini_high_result Hh Hg :=
  intros Hobs; apply Hh; eapply tini_guard; [apply tini_inst_flow; exact Hg|exact Hobs].
Local Ltac tini_udown := tini_uv_down.
Local Ltac tini_bdown := tini_bv_down.

Local Lemma tini_bfund Γ pc e τ :
  Γ # pc ⊢ₜ e : τ →
  ∀ a b n W γ1 γ2, tini_BEnv Γ a b n W γ1 γ2 →
  BE n W (tini_sinst a b τ) e.[γ1] e.[γ2].
Proof.
  induction 1 as
    [Γ pc|Γ pc c|Γ pc k|Γ pc x τ Hx
    |Γ pc e p τ ν Hbody IH
    |Γ pc e1 e2 op l1 l2 H1 IH1 H2 IH2
    |Γ pc e1 e2 τ ν l p H1 IH1 H2 IH2 Hg Hf
    |Γ pc e1 e2 τ ν H1 IH1 H2 IH2
    |Γ pc e1 e2 τ ν H1 IH1 H2 IH2
    |Γ pc e τ p Hbody IH
    |Γ pc e τ t l p Hf Hg H1 IH1
    |Γ pc e τ p Hbody IH
    |Γ pc e τ l l' p Hf Hg H1 IH1
    |Γ pc e e1 e2 τ l H0 IH0 H1 IH1 H2 IH2 Hg
    |Γ pc e1 e2 τ ν H1 IH1 H2 IH2
    |Γ pc e τ ν l H1 IH1 Hg
    |Γ pc e τ ν l H1 IH1 Hg
    |Γ pc e τ ν H1 IH1
    |Γ pc e τ ν H1 IH1
    |Γ pc e e1 e2 τ ν υ l H0 IH0 H1 IH1 H2 IH2 Hg
    |Γ pc e τ H1 IH1 Hg
    |Γ pc e1 e2 τ l H1 IH1 H2 IH2 Hg
    |Γ pc e τ ν l H1 IH1 Hs Hg
    |Γ pc e τ t H1 IH1
    |Γ pc e1 e2 τ ν l Hg H1 IH1 H2 IH2
    |Γ pc e τ H1 IH1
    |Γ pc e τ l Hg H1 IH1
    |Γ pc e τ ν p H1 IH1 Hf Hs];
    intros a b n W γ1 γ2 Hγ; simpl.
  - apply (tini_bval _ _ _ UnitV UnitV). destruct n; first done.
    apply tini_Bstep; split; [split; by apply tini_Ustep|done].
  - apply (tini_bval _ _ _ (BoolV c) (BoolV c)). destruct n; first done.
    apply tini_Bstep; split; [split; by apply tini_Ustep|done].
  - apply (tini_bval _ _ _ (NatV k) (NatV k)). destruct n; first done.
    apply tini_Bstep; split; [split; by apply tini_Ustep|done].
  - destruct (Hγ _ _ Hx) as (v1 & v2 & -> & -> & Hv). by apply tini_bval.
  - apply (tini_bval _ _ _ (LamV e.[up γ1]) (LamV e.[up γ2])).
    destruct n as [|n]; first done. apply tini_Bstep. split.
    + split; apply tini_Ustep; simpl; intros; rewrite tini_beta; tini_uI Hbody.
    + simpl. intros _ m W' v1 v2 Hm HW Hv. rewrite !tini_beta. tini_bI IH.
  - tini_bb (BinOpLCtx op e2.[γ1]) (BinOpLCtx op e2.[γ2]) IH1 x1 x2.
    tini_bb (BinOpRCtx op x1) (BinOpRCtx op x2) IH2 y1 y2. tini_lift_bv x1 x2.
    tini_bpure_with ltac:(try (tini_bshape x1 x2; tini_bshape y1 y2)).
    apply tini_bval. destruct remaining; first done. apply tini_Bstep.
    split; first (split; apply tini_Ustep; by destruct op).
    intros Hl. apply tini_low_join in Hl as [Hl1 Hl2].
    specialize (Hshape Hl1). specialize (Hshape0 Hl2). subst.
    by destruct op.
  - tini_bb (AppLCtx e2.[γ1]) (AppLCtx e2.[γ2]) IH1 f1 f2.
    tini_bb (AppRCtx f1) (AppRCtx f2) IH2 x1 x2. tini_lift_bv f1 f2.
    tini_bpure_with ltac:(try (tini_bshape f1 f2)).
    destruct (tini_low_dec l.[a]) as [Hl|Hh].
    + eapply Hshape; [exact Hl|lia|apply tini_bext_refl|tini_bdown].
    + apply (tini_flow_subst a) in Hf. simpl in Hf.
      assert (¬ tini_low p.[a]) as Hp.
      { intros Hp. apply Hh. by apply (tini_effect _ _ _ Hf) in Hp as []. }
      eapply (tini_bsplit _ _ (p.[a]) (p.[a]));
        [exact Hp|exact Hp|tini_high_result Hh Hg| |].
      * eapply Hu1; [lia|apply tini_ext_refl|].
        match goal with H : BV _ _ _ x1 x2 |- _ => apply tini_Bun_of in H as [? ?] end. tini_udown.
      * eapply Hu2; [lia|apply tini_ext_refl|].
        match goal with H : BV _ _ _ x1 x2 |- _ => apply tini_Bun_of in H as [? ?] end. tini_udown.
  - tini_bb (LetInCtx e2.[up γ1]) (LetInCtx e2.[up γ2]) IH1 v1 v2.
    tini_bpure_with idtac. rewrite !tini_beta. tini_bI IH2.
  - tini_bb (SeqCtx e2.[γ1]) (SeqCtx e2.[γ2]) IH1 v1 v2.
    tini_bpure_with idtac. tini_bI IH2.
  - apply (tini_bval _ _ _ (TLamV e.[γ1]) (TLamV e.[γ2])).
    destruct n as [|n]; first done. apply tini_Bstep. split.
    + split; apply tini_Ustep; simpl; intros; rewrite tini_type_beta; tini_uI Hbody.
    + simpl. intros _ m W' t Hm HW. rewrite tini_type_beta. tini_bI IH.
  - rewrite tini_type_natural.
    tini_bb TAppCtx TAppCtx IH1 f1 f2. tini_bpure_with ltac:(try (tini_bshape f1 f2)).
    destruct (tini_low_dec l.[a]) as [Hl|Hh].
    + specialize (Hshape Hl remaining _ (tini_inst a b t) ltac:(lia) (tini_bext_refl _)).
      by rewrite tini_type_beta in Hshape.
    + apply (tini_flow_subst a) in Hf. simpl in Hf.
      assert (¬ tini_low p.[a]) as Hp.
      { intros Hp. apply Hh. by apply (tini_effect _ _ _ Hf) in Hp as []. }
      eapply (tini_bsplit _ _ (p.[a]) (p.[a]));
        [exact Hp|exact Hp|rewrite <- tini_type_natural; tini_high_result Hh Hg| |].
      * specialize (Hu1 remaining _ (tini_inst a b t) ltac:(lia) (tini_ext_refl _)).
        by rewrite tini_type_beta in Hu1.
      * specialize (Hu2 remaining _ (tini_inst a b t) ltac:(lia) (tini_ext_refl _)).
        by rewrite tini_type_beta in Hu2.
  - apply (tini_bval _ _ _ (TLLamV e.[γ1]) (TLLamV e.[γ2])).
    destruct n as [|n]; first done. apply tini_Bstep. split.
    + split; apply tini_Ustep; simpl; intros; rewrite tini_label_beta, tini_label_beta_pc; tini_uI Hbody.
    + simpl. intros _ m W' l Hm HW. rewrite tini_label_beta. tini_bI IH.
  - rewrite tini_label_natural.
    tini_bb TLAppCtx TLAppCtx IH1 f1 f2. tini_bpure_with ltac:(try (tini_bshape f1 f2)).
    destruct (tini_low_dec l.[a]) as [Hl|Hh].
    + specialize (Hshape Hl remaining _ l'.[a] ltac:(lia) (tini_bext_refl _)).
      by rewrite tini_label_beta in Hshape.
    + apply (tini_flow_subst a) in Hf. simpl in Hf. rewrite tini_label_single in Hf.
      assert (¬ tini_low p.[l'.[a] .: a]) as Hp.
      { intros Hp. apply Hh. by apply (tini_effect _ _ _ Hf) in Hp as []. }
      eapply (tini_bsplit _ _ (p.[l'.[a] .: a]) (p.[l'.[a] .: a]));
        [exact Hp|exact Hp|rewrite <- tini_label_natural; tini_high_result Hh Hg| |].
      * specialize (Hu1 remaining _ l'.[a] ltac:(lia) (tini_ext_refl _)).
        by rewrite tini_label_beta, tini_label_beta_pc in Hu1.
      * specialize (Hu2 remaining _ l'.[a] ltac:(lia) (tini_ext_refl _)).
        by rewrite tini_label_beta, tini_label_beta_pc in Hu2.
  - tini_bb (IfCtx e1.[γ1] e2.[γ1]) (IfCtx e1.[γ2] e2.[γ2]) IH0 x y.
    tini_bpure_with ltac:(try (tini_bshape x y)).
    all: destruct (tini_low_dec l.[a]) as [Hl|Hh].
    all: try solve [specialize (Hshape Hl); try discriminate;
      first [solve [tini_bI IH1]|tini_bI IH2]].
    all: eapply (tini_bsplit _ _ (pc.[a] ⊔ₛ l.[a]) (pc.[a] ⊔ₛ l.[a]));
      try solve [intros Hp; apply tini_low_join in Hp; tauto | tini_high_result Hh Hg |
        solve [tini_uI H1] | tini_uI H2].
  - tini_bb (PairLCtx e2.[γ1]) (PairLCtx e2.[γ2]) IH1 x1 x2.
    tini_bb (PairRCtx x1) (PairRCtx x2) IH2 y1 y2. tini_lift_bv x1 x2.
    apply (tini_bval _ _ _ (PairV x1 y1) (PairV x2 y2)).
    match goal with |- BV ?n _ _ _ _ => destruct n; first done end.
    apply tini_Bstep. split.
    + repeat match goal with H : BV _ _ _ _ _ |- _ =>
        apply tini_Bun_of in H as [? ?] end.
      split; apply tini_Ustep; simpl; split; tini_udown.
    + intros _. split; tini_bdown.
  - tini_bb Proj1Ctx Proj1Ctx IH1 x y. tini_bpure_with ltac:(try (tini_bshape x y)).
    apply tini_bval. destruct (tini_low_dec l.[a]) as [Hl|Hh].
    + destruct (Hshape Hl). tini_bdown.
    + apply tini_Bhigh; first tini_high_result Hh Hg.
      destruct Hu1, Hu2. split; tini_udown.
  - tini_bb Proj2Ctx Proj2Ctx IH1 x y. tini_bpure_with ltac:(try (tini_bshape x y)).
    apply tini_bval. destruct (tini_low_dec l.[a]) as [Hl|Hh].
    + destruct (Hshape Hl). tini_bdown.
    + apply tini_Bhigh; first tini_high_result Hh Hg.
      destruct Hu1, Hu2. split; tini_udown.
  - tini_bb InjLCtx InjLCtx IH1 x y. apply (tini_bval _ _ _ (InjLV x) (InjLV y)).
    match goal with |- BV ?n _ _ _ _ => destruct n; first done end.
    apply tini_Bstep. split.
    + match goal with H : BV _ _ _ _ _ |- _ => apply tini_Bun_of in H as [? ?] end.
      split; apply tini_Ustep; simpl; tini_udown.
    + intros _. tini_bdown.
  - tini_bb InjRCtx InjRCtx IH1 x y. apply (tini_bval _ _ _ (InjRV x) (InjRV y)).
    match goal with |- BV ?n _ _ _ _ => destruct n; first done end.
    apply tini_Bstep. split.
    + match goal with H : BV _ _ _ _ _ |- _ => apply tini_Bun_of in H as [? ?] end.
      split; apply tini_Ustep; simpl; tini_udown.
    + intros _. tini_bdown.
  - tini_bb (CaseCtx e1.[up γ1] e2.[up γ1]) (CaseCtx e1.[up γ2] e2.[up γ2]) IH0 x y.
    tini_bpure_with ltac:(try (tini_bshape x y)).
    all: rewrite !tini_beta; destruct (tini_low_dec l.[a]) as [Hl|Hh].
    all: try solve [specialize (Hshape Hl); try contradiction;
      first [solve [tini_bI IH1]|tini_bI IH2]].
    all: eapply (tini_bsplit _ _ (pc.[a] ⊔ₛ l.[a]) (pc.[a] ⊔ₛ l.[a]));
      try solve [intros Hp; apply tini_low_join in Hp; tauto | tini_high_result Hh Hg |
        solve [tini_uI H1] | tini_uI H2].
  - tini_bb AllocCtx AllocCtx IH1 x y. tini_bhead_with idtac.
    edestruct (tini_Balloc (S (S remaining)) remaining) as (Wnext & HW & Hheap' & Hv);
      [lia|exact Hheap|eassumption|eassumption|eassumption|].
    exists Wnext. split; [exact HW|split; [exact Hheap'|]].
    match goal with |- BE _ _ _ (Loc ?l1) (Loc ?l2) =>
      by apply (tini_bval _ _ _ (LocV l1) (LocV l2))
    end.
  - tini_bb (StoreLCtx e2.[γ1]) (StoreLCtx e2.[γ2]) IH1 x1 x2.
    tini_bb (StoreRCtx x1) (StoreRCtx x2) IH2 y1 y2. tini_lift_bv x1 x2.
    tini_bhead_with ltac:(try (tini_bshape x1 x2)).
    eexists. split; first apply tini_bext_refl. split.
    + eapply (tini_Bwrite (S (S remaining)) remaining); [lia|exact Hheap|exact Hu1|exact Hu2| |eassumption].
      intros Hl. apply Hshape; last done.
      pose proof (tini_inst_flow a b _ _ Hg) as Hguard.
      apply (tini_guard _ _ Hguard) in Hl. by apply tini_low_join in Hl as [].
    + apply (tini_bval _ _ _ UnitV UnitV). destruct remaining; first done.
      apply tini_Bstep; split; [split; by apply tini_Ustep|done].
  - tini_bb LoadCtx LoadCtx IH1 x y. tini_bpure_with ltac:(try (tini_bshape x y)).
    apply tini_bval.
    destruct (tini_low_dec (tini_lat (tini_sinst a b ν))) as [Hl|Hh].
    + assert (tini_visible (tini_sinst a b τ)) as Hlcell.
      { destruct Hs as [cell_label result_label raw_cell raw_result HF HS].
        change (tini_low cell_label.[a]).
        exact (tini_low_flow _ _ (tini_flow_subst a _ _ HF) Hl). }
      pose proof (tini_guard _ _ (tini_inst_flow a b _ _ Hg) Hl) as Hlref.
      destruct Hheap as (_ & _ & _ & Hlinks).
      destruct (Hlinks _ _ _ (Hshape Hlref Hlcell)) as (_ & _ & _ & u1 & u2 & E1 & E2 & Hv).
      match goal with |- BV _ _ _ ?v1 ?v2 =>
        assert (u1 = v1) as -> by congruence; assert (u2 = v2) as -> by congruence
      end.
      eapply tini_bsub; first exact Hs. tini_bdown.
    + apply tini_Bhigh; first exact Hh.
      destruct Hheap as (Hs1 & Hs2 & _).
      destruct (Hs1 _ _ Hu1) as (u1 & E1 & Hv1).
      destruct (Hs2 _ _ Hu2) as (u2 & E2 & Hv2).
      match goal with |- tini_Bun _ _ _ ?v1 ?v2 =>
        assert (u1 = v1) as -> by congruence; assert (u2 = v2) as -> by congruence
      end.
      split; eapply tini_usub; [exact Hs|tini_udown|exact Hs|tini_udown].
  - specialize (IH1 a b). rewrite tini_type_natural in IH1.
    tini_bb PackCtx PackCtx IH1 x y. apply (tini_bval _ _ _ (PackV x) (PackV y)).
    match goal with |- BV ?n _ _ _ _ => destruct n; first done end.
    apply tini_Bstep. split.
    + match goal with H : BV _ _ _ _ _ |- _ => apply tini_Bun_of in H as [? ?] end.
      split; apply tini_Ustep; simpl; exists (tini_inst a b t); rewrite tini_type_beta; tini_udown.
    + intros _. exists (tini_inst a b t). rewrite tini_type_beta. tini_bdown.
  - tini_bb (UnpackCtx e2.[up γ1]) (UnpackCtx e2.[up γ2]) IH1 x y.
    tini_bpure_with ltac:(try (tini_bshape x y)). rewrite !tini_beta.
    destruct (tini_low_dec l.[a]) as [Hl|Hh].
    + destruct (Hshape Hl) as [witness Hv]. rewrite tini_type_beta in Hv.
      specialize (IH2 a (witness .: b)). rewrite tini_type_shift in IH2. tini_bI IH2.
    + destruct Hu1 as [witness1 Hu1], Hu2 as [witness2 Hu2]. rewrite tini_type_beta in Hu1, Hu2.
      eapply (tini_bsplit _ _ (pc.[a] ⊔ₛ l.[a]) (pc.[a] ⊔ₛ l.[a]));
        try solve [intros Hp; apply tini_low_join in Hp; tauto | tini_high_result Hh Hg].
      * pose proof (tini_ufund _ _ _ _ H2 a (witness1 .: b)) as HE.
        rewrite tini_type_shift in HE. eapply HE.
        tini_uenv_bin.
      * pose proof (tini_ufund _ _ _ _ H2 a (witness2 .: b)) as HE.
        rewrite tini_type_shift in HE. eapply HE.
        tini_uenv_bin.
  - specialize (IH1 a b). rewrite tini_type_natural in IH1.
    tini_bb FoldCtx FoldCtx IH1 x y. apply (tini_bval _ _ _ (FoldV x) (FoldV y)).
    match goal with |- BV ?n _ _ _ _ => destruct n; first done end.
    apply tini_Bstep. split.
    + match goal with H : BV _ _ _ _ _ |- _ => apply tini_Bun_of in H as [? ?] end.
      split; apply tini_Ustep; simpl; rewrite tini_type_beta; simpl in *; tini_udown.
    + intros _. rewrite tini_type_beta. simpl in *. tini_bdown.
  - tini_bb UnfoldCtx UnfoldCtx IH1 x y. tini_bpure_with ltac:(try (tini_bshape x y)).
    apply tini_bval. destruct (tini_low_dec l.[a]) as [Hl|Hh].
    + specialize (Hshape Hl). rewrite tini_type_beta in Hshape. rewrite tini_type_natural.
      simpl in *. tini_bdown.
    + apply tini_Bhigh; first tini_high_result Hh Hg.
      rewrite tini_type_beta in Hu1, Hu2. rewrite tini_type_natural. simpl in *.
      split; tini_udown.
  - eapply tini_bmap; [intros; eapply tini_bsub; eauto|tini_bI IH1].
Qed.

Theorem soundness_tini (e : expr) v1 v2 v1' v2' ℓ ℓ' :
    ℓ' ⋢ ζ →
    ℓ  ⊑ ζ →
    [TBool @ (LLabel ℓ')] # (LLabel ℓ) ⊢ₜ e : TBool @ (LLabel ℓ) →
    [] # (LLabel ℓ) ⊢ₜ #v1 : TBool @ (LLabel ℓ') →
    [] # (LLabel ℓ) ⊢ₜ #v2 : TBool @ (LLabel ℓ') →
    ((∃ σ1, rtc pstep (e.[# v1/], ∅) (# v1', σ1)) ∧
     (∃ σ2, rtc pstep (e.[# v2/], ∅) (# v2', σ2))) →
    v1' = v2'.

Proof.
  intros Hhigh Hlow He Hv1 Hv2 [[s1 Hr1] [s2 Hr2]].
  apply rtc_nsteps in Hr1 as [i Hr1]. apply rtc_nsteps in Hr2 as [j Hr2].
  set (n := S (i+j)).
  set (W := {| tini_left := ∅; tini_right := ∅; tini_links := ∅ |}).
  assert (tini_BHeap (tini_uv n) (tini_bv n) W ∅ ∅) as Hheap.
  { unfold W, tini_BHeap.
    repeat split; unfold tini_UHeap, tini_bij, tini_Blinks; intros;
      cbn [tini_left tini_right tini_links] in *;
      first [discriminate |
        match goal with Hempty : ∅ !! _ = Some _ |- _ =>
          rewrite lookup_empty in Hempty; discriminate end]. }
  assert (∀ v, [] # (LLabel ℓ) ⊢ₜ #v : TBool @ (LLabel ℓ') →
     ∃ c, v = BoolV c) as Hbool.
  { intros v Hv.
    assert (tini_UEnv [] LVar TVar n (tini_left W) ids) as Hempty by (intros ? ? Hx; discriminate).
    pose proof (tini_ufund _ _ _ _ Hv _ _ _ _ _ Hempty) as HE.
    rewrite tini_esub_id, (proj2 tini_inst_id) in HE.
    destruct Hheap as (Hs & _).
    destruct (HE 0 ∅ v ∅ ltac:(lia) Hs (nsteps_O _ _)) as (W' & _ & _ & HUV & _).
    rewrite Nat.sub_0_r in HUV. unfold n in HUV. apply tini_Ustep in HUV.
    destruct v; simpl in HUV; try contradiction. eauto. }
  destruct (Hbool _ Hv1) as [c1 ->], (Hbool _ Hv2) as [c2 ->].
  assert (tini_BEnv [TBool @ LLabel ℓ'] LVar TVar n W
    (#(BoolV c1) .: ids) (#(BoolV c2) .: ids)) as Henv.
  { apply tini_BEnv_cons; last (intros ? ? Hx; discriminate).
    rewrite (proj2 tini_inst_id). apply tini_Bhigh; first exact Hhigh.
    split; unfold n; by apply tini_Ustep. }
  pose proof (tini_bfund _ _ _ _ He _ _ _ _ _ _ Henv) as HE.
  rewrite (proj2 tini_inst_id) in HE.
  destruct (HE i j ∅ ∅ v1' v2' s1 s2 ltac:(unfold n; lia) Hheap Hr1 Hr2) as (W' & _ & _ & Hval).
  replace (n-i-j) with 1 in Hval by (unfold n; lia).
  apply tini_Bstep in Hval as [[H1 H2] Hobs].
  apply tini_Ustep in H1, H2. specialize (Hobs Hlow).
  destruct v1', v2'; simpl in *; try contradiction. congruence.
Qed.

End soundness.
