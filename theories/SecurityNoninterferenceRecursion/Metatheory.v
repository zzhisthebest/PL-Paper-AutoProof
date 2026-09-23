From AutoProof.SecurityNoninterferenceRecursion Require Export Typing.
From AutoProof.SecurityNoninterferenceRecursion Require Import Evaluation.
Import ListNotations.

Lemma lookup_update_eq : forall Gamma x T,
  lookup_context x (update Gamma x T) = Some T.
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma lookup_update_neq : forall Gamma x y T,
  x <> y -> lookup_context x (update Gamma y T) = lookup_context x Gamma.
Proof.
  intros Gamma x y T Hneq. simpl.
  destruct (Nat.eqb x y) eqn:Heq; [apply Nat.eqb_eq in Heq; contradiction | reflexivity].
Qed.

Definition context_included (Gamma Gamma' : context) : Prop :=
  forall x T, lookup_context x Gamma = Some T -> lookup_context x Gamma' = Some T.

Lemma context_included_update : forall Gamma Gamma' x T,
  context_included Gamma Gamma' ->
  context_included (update Gamma x T) (update Gamma' x T).
Proof.
  intros Gamma Gamma' x T H y U Hy. simpl in *.
  destruct (Nat.eqb y x); [exact Hy | apply H; exact Hy].
Qed.

Lemma typing_weaken : forall Gamma t T,
  has_type Gamma t T -> forall Gamma', context_included Gamma Gamma' -> has_type Gamma' t T.
Proof.
  intros Gamma t T H. induction H; intros Gamma' Hinc.
  - apply T_Var; [apply Hinc; exact H | exact H0].
  - apply T_Unit; exact H.
  - apply T_Abs with (L := L); try assumption.
    intros x Hfresh. apply H2; [exact Hfresh | apply context_included_update; exact Hinc].
  - eapply T_App; eauto.
  - apply T_Pair; eauto.
  - eapply T_Fst; eauto.
  - eapply T_Snd; eauto.
  - apply T_Inl; eauto.
  - apply T_Inr; eauto.
  - eapply T_Case with (L := L); try eassumption.
    + apply IHhas_type; exact Hinc.
    + intros x Hfresh. apply H2; [exact Hfresh | apply context_included_update; exact Hinc].
    + intros x Hfresh. apply H4; [exact Hfresh | apply context_included_update; exact Hinc].
  - apply T_Protect; auto.
  - eapply T_Sub; eauto.
  - apply T_Nat; assumption.
  - eapply T_Succ; eauto.
  - eapply T_NatRec; eauto.
Qed.

Lemma typing_weaken_empty : forall t T Gamma,
  has_type empty t T -> has_type Gamma t T.
Proof.
  intros t T Gamma H. eapply typing_weaken; [exact H | ].
  intros x U Hlookup. discriminate Hlookup.
Qed.

Lemma context_substitution_update : forall Gamma Gamma' x y U A,
  x <> y -> lookup_context x Gamma = Some U ->
  (forall z T, z <> x -> lookup_context z Gamma = Some T ->
    lookup_context z Gamma' = Some T) ->
  lookup_context x (update Gamma y A) = Some U /\
  (forall z T, z <> x -> lookup_context z (update Gamma y A) = Some T ->
    lookup_context z (update Gamma' y A) = Some T).
Proof.
  intros Gamma Gamma' x y U A Hneq Hlookup Hinc. split.
  - rewrite lookup_update_neq; assumption.
  - intros z T Hneqz Hlookupz. simpl in *.
    destruct (Nat.eqb z y); [exact Hlookupz | apply Hinc; assumption].
Qed.

Lemma subst_open_fresh : forall body x y u,
  x <> y -> locally_closed u ->
  subst x u (open body (tm_fvar y)) = open (subst x u body) (tm_fvar y).
Proof.
  intros body x y u Hneq Hlc. unfold open.
  rewrite subst_open_rec by exact Hlc. simpl.
  destruct (Nat.eqb x y) eqn:Heq; [apply Nat.eqb_eq in Heq; contradiction | reflexivity].
Qed.

Lemma typing_subst_closed : forall Gamma t T,
  has_type Gamma t T -> forall x U u Gamma',
  lookup_context x Gamma = Some U ->
  (forall y A, y <> x -> lookup_context y Gamma = Some A ->
    lookup_context y Gamma' = Some A) ->
  has_type empty u U -> has_type Gamma' (subst x u t) T.
Proof.
  intros Gamma t T Htyped. induction Htyped; intros z Us u Gamma' Hz Hinc Hu; simpl.
  - destruct (Nat.eqb z x) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst z. rewrite H in Hz. inversion Hz; subst.
      apply typing_weaken_empty; exact Hu.
    + apply T_Var; [apply Hinc; [apply Nat.eqb_neq in Heq; congruence | exact H] | exact H0].
  - apply T_Unit; exact H.
  - apply T_Abs with (L := z :: L); try assumption.
    intros y Hfresh. assert (z <> y /\ ~ In y L) as [Hneq Hy] by (simpl in Hfresh; tauto).
    destruct (context_substitution_update _ _ _ _ _ T1 Hneq Hz Hinc) as [Hz' Hinc'].
    rewrite <- subst_open_fresh by (try exact Hneq; exact (proj1 (typing_regular _ _ _ Hu))).
    eapply H2; eassumption.
  - eapply T_App; eauto.
  - apply T_Pair; eauto.
  - eapply T_Fst; eauto.
  - eapply T_Snd; eauto.
  - apply T_Inl; eauto.
  - apply T_Inr; eauto.
  - eapply T_Case with (L := z :: L); try eassumption.
    + eapply IHHtyped; eassumption.
    + intros y Hfresh. assert (z <> y /\ ~ In y L) as [Hneq Hy] by (simpl in Hfresh; tauto).
      destruct (context_substitution_update _ _ _ _ _ T1 Hneq Hz Hinc) as [Hz' Hinc'].
      rewrite <- subst_open_fresh by (try exact Hneq; exact (proj1 (typing_regular _ _ _ Hu))).
      eapply H1; eassumption.
    + intros y Hfresh. assert (z <> y /\ ~ In y L) as [Hneq Hy] by (simpl in Hfresh; tauto).
      destruct (context_substitution_update _ _ _ _ _ T2 Hneq Hz Hinc) as [Hz' Hinc'].
      rewrite <- subst_open_fresh by (try exact Hneq; exact (proj1 (typing_regular _ _ _ Hu))).
      eapply H3; eassumption.
  - apply T_Protect. eapply IHHtyped; eassumption.
  - eapply T_Sub; [eapply IHHtyped; eassumption | exact H].
  - apply T_Nat; assumption.
  - eapply T_Succ; eauto.
  - eapply T_NatRec; eauto.
Qed.

Lemma typing_open_closed : forall Gamma body T U L u,
  (forall x, ~ In x L -> has_type (update Gamma x U) (open body (tm_fvar x)) T) ->
  has_type empty u U -> has_type Gamma (open body u) T.
Proof.
  intros Gamma body T U L u Hbody Hu.
  destruct (fresh_atom (L ++ fv body)) as [x Hfresh].
  rewrite in_app_iff in Hfresh.
  rewrite (open_subst_intro body x u) by (try tauto; exact (proj1 (typing_regular _ _ _ Hu))).
  eapply typing_subst_closed.
  - apply Hbody; tauto.
  - apply lookup_update_eq.
  - intros y A Hneq Hlookup. rewrite lookup_update_neq in Hlookup by exact Hneq. exact Hlookup.
  - exact Hu.
Qed.

Lemma typing_abs_inv : forall Gamma t T,
  has_type Gamma t T -> forall A body k,
  t = tm_abs A body k ->
  exists B L, subtype (Ty_Arrow A B k) T /\
    (forall x, ~ In x L -> has_type (update Gamma x A) (open body (tm_fvar x)) B).
Proof.
  intros Gamma t T Htyped. induction Htyped; intros AA bb kk Heq; inversion Heq; subst.
  - exists T2, L. split; [apply subtype_refl | exact H1].
    destruct (fresh_atom L) as [x Hx].
    pose proof (proj2 (typing_regular _ _ _ (H1 x Hx))). simpl. tauto.
  - destruct (IHHtyped _ _ _ eq_refl) as [B [L [Hs Hb]]].
    exists B, L. split; [eapply S_Trans; eassumption | exact Hb].
Qed.

Lemma typing_pair_inv : forall Gamma t T,
  has_type Gamma t T -> forall a b k,
  t = tm_pair a b k ->
  exists A B, has_type Gamma a A /\ has_type Gamma b B /\ subtype (Ty_Prod A B k) T.
Proof.
  intros Gamma t T Htyped. induction Htyped; intros aa bb kk Heq; inversion Heq; subst.
  - exists T1, T2. repeat split; try assumption. apply subtype_refl. simpl.
    pose proof (proj2 (typing_regular _ _ _ Htyped1)).
    pose proof (proj2 (typing_regular _ _ _ Htyped2)). tauto.
  - destruct (IHHtyped _ _ _ eq_refl) as [A [B [Ha [Hb Hs]]]].
    exists A, B. repeat split; try assumption. eapply S_Trans; eassumption.
Qed.

Lemma typing_inl_inv : forall Gamma t T,
  has_type Gamma t T -> forall a k,
  t = tm_inl a k ->
  exists A B, has_type Gamma a A /\ subtype (Ty_Sum A B k) T.
Proof.
  intros Gamma t T Htyped. induction Htyped; intros a kk Heq; inversion Heq; subst.
  - exists T1, T2. split; [exact Htyped | apply subtype_refl].
    pose proof (proj2 (typing_regular _ _ _ Htyped)). simpl. tauto.
  - destruct (IHHtyped _ _ eq_refl) as [A [B [Ha Hs]]].
    exists A, B. split; [exact Ha | eapply S_Trans; eassumption].
Qed.

Lemma typing_inr_inv : forall Gamma t T,
  has_type Gamma t T -> forall a k,
  t = tm_inr a k ->
  exists A B, has_type Gamma a B /\ subtype (Ty_Sum A B k) T.
Proof.
  intros Gamma t T Htyped. induction Htyped; intros a kk Heq; inversion Heq; subst.
  - exists T1, T2. split; [exact Htyped | apply subtype_refl].
    pose proof (proj2 (typing_regular _ _ _ Htyped)). simpl. tauto.
  - destruct (IHHtyped _ _ eq_refl) as [A [B [Ha Hs]]].
    exists A, B. split; [exact Ha | eapply S_Trans; eassumption].
Qed.

Lemma typing_protect_value : forall Gamma v T,
  has_type Gamma v T -> value v -> forall l,
  has_type Gamma (protect_value v l) (ty_protect l T).
Proof.
  intros Gamma v T Htyped. induction Htyped; intros Hv lp;
    try solve [inversion Hv]; simpl;
    try solve [apply T_Unit; apply protect_security_wf; assumption];
    try solve [apply T_Abs with (L := L); auto using protect_security_wf];
    try solve [apply T_Pair; auto using protect_security_wf];
    try solve [apply T_Inl; auto using protect_security_wf];
    try solve [apply T_Inr; auto using protect_security_wf];
    try solve [apply T_Nat; auto using protect_security_wf].
  eapply T_Sub; [apply IHHtyped; exact Hv | apply subtype_protect; [exact H | apply flows_to_refl]].
Qed.

Lemma typing_beta : forall A body k v T1 T2 kt,
  has_type empty (tm_abs A body k) (Ty_Arrow T1 T2 kt) ->
  has_type empty v T1 ->
  has_type empty (tm_protect k.(indirect_reader) (open body v))
    (ty_protect kt.(indirect_reader) T2).
Proof.
  intros A body k v T1 T2 kt Hfun Hv.
  destruct (typing_abs_inv _ _ _ Hfun _ _ _ eq_refl) as [B [L [Hsub Hbody]]].
  destruct (subtype_arrow_inv _ _ Hsub _ _ _ eq_refl) as [C [D [kc [Heq [Ha [Hb Hk]]]]]].
  inversion Heq; subst.
  eapply T_Sub.
  - apply T_Protect. eapply typing_open_closed; [exact Hbody | eapply T_Sub; eassumption].
  - apply subtype_protect; [exact Hb | exact (proj2 Hk)].
Qed.

Lemma typing_project_left : forall a b k T1 T2 kt,
  has_type empty (tm_pair a b k) (Ty_Prod T1 T2 kt) ->
  has_type empty (tm_protect k.(indirect_reader) a) (ty_protect kt.(indirect_reader) T1).
Proof.
  intros a b k T1 T2 kt Hpair.
  destruct (typing_pair_inv _ _ _ Hpair _ _ _ eq_refl) as [A [B [Ha [Hb Hsub]]]].
  destruct (subtype_prod_inv _ _ Hsub _ _ _ eq_refl) as [C [D [kc [Heq [Hs1 [Hs2 Hk]]]]]].
  inversion Heq; subst. eapply T_Sub; [apply T_Protect; exact Ha | ].
  apply subtype_protect; [exact Hs1 | exact (proj2 Hk)].
Qed.

Lemma typing_project_right : forall a b k T1 T2 kt,
  has_type empty (tm_pair a b k) (Ty_Prod T1 T2 kt) ->
  has_type empty (tm_protect k.(indirect_reader) b) (ty_protect kt.(indirect_reader) T2).
Proof.
  intros a b k T1 T2 kt Hpair.
  destruct (typing_pair_inv _ _ _ Hpair _ _ _ eq_refl) as [A [B [Ha [Hb Hsub]]]].
  destruct (subtype_prod_inv _ _ Hsub _ _ _ eq_refl) as [C [D [kc [Heq [Hs1 [Hs2 Hk]]]]]].
  inversion Heq; subst. eapply T_Sub; [apply T_Protect; exact Hb | ].
  apply subtype_protect; [exact Hs2 | exact (proj2 Hk)].
Qed.

Lemma typing_case_left : forall a k T1 T2 kt body T L,
  has_type empty (tm_inl a k) (Ty_Sum T1 T2 kt) ->
  (forall x, ~ In x L -> has_type (update empty x T1) (open body (tm_fvar x)) T) ->
  has_type empty (tm_protect k.(indirect_reader) (open body a))
    (ty_protect kt.(indirect_reader) T).
Proof.
  intros a k T1 T2 kt body T L Hinj Hbody.
  destruct (typing_inl_inv _ _ _ Hinj _ _ eq_refl) as [A [B [Ha Hsub]]].
  destruct (subtype_sum_inv _ _ Hsub _ _ _ eq_refl) as [C [D [kc [Heq [Hs1 [Hs2 Hk]]]]]].
  inversion Heq; subst.
  assert (has_type empty (open body a) T) as Hopen.
  { eapply typing_open_closed; [exact Hbody | eapply T_Sub; eassumption]. }
  eapply T_Sub; [apply T_Protect; exact Hopen | ].
  apply subtype_protect; [apply subtype_refl; exact (proj2 (typing_regular _ _ _ Hopen)) | exact (proj2 Hk)].
Qed.

Lemma typing_case_right : forall a k T1 T2 kt body T L,
  has_type empty (tm_inr a k) (Ty_Sum T1 T2 kt) ->
  (forall x, ~ In x L -> has_type (update empty x T2) (open body (tm_fvar x)) T) ->
  has_type empty (tm_protect k.(indirect_reader) (open body a))
    (ty_protect kt.(indirect_reader) T).
Proof.
  intros a k T1 T2 kt body T L Hinj Hbody.
  destruct (typing_inr_inv _ _ _ Hinj _ _ eq_refl) as [A [B [Ha Hsub]]].
  destruct (subtype_sum_inv _ _ Hsub _ _ _ eq_refl) as [C [D [kc [Heq [Hs1 [Hs2 Hk]]]]]].
  inversion Heq; subst.
  assert (has_type empty (open body a) T) as Hopen.
  { eapply typing_open_closed; [exact Hbody | eapply T_Sub; eassumption]. }
  eapply T_Sub; [apply T_Protect; exact Hopen | ].
  apply subtype_protect; [apply subtype_refl; exact (proj2 (typing_regular _ _ _ Hopen)) | exact (proj2 Hk)].
Qed.

Lemma typing_nat_shape : forall Gamma t T, has_type Gamma t T ->
  forall n k, t = tm_nat n k -> exists kt, T = Ty_Nat kt /\ security_le k kt.
Proof.
  intros Gamma t T H. induction H; intros m kn Et; inversion Et; subst.
  - destruct (IHhas_type _ _ eq_refl) as [km [-> Hm]].
    destruct (subtype_nat_inv _ _ H0 _ eq_refl) as [ku [-> Hu]].
    exists ku. split; [reflexivity | eapply security_le_trans; eassumption].
  - exists kn. split; [reflexivity | apply security_le_refl].
Qed.

Lemma typing_nat_inv : forall Gamma n k kt,
  has_type Gamma (tm_nat n k) (Ty_Nat kt) -> security_le k kt.
Proof.
  intros Gamma n k kt H.
  destruct (typing_nat_shape _ _ _ H _ _ eq_refl) as [ku [E Hk]].
  inversion E; subst. exact Hk.
Qed.

Lemma typing_unroll : forall n Gamma b s T r,
  has_type Gamma b T ->
  has_type Gamma s (Ty_Arrow (Ty_Nat public) (Ty_Arrow T T public) public) ->
  has_type Gamma (natrec_unroll n b s r) T.
Proof.
  induction n; intros Gamma b s T r Hb Hs; simpl; [exact Hb |].
  rewrite <- (ty_protect_low T).
  eapply T_App with (T1 := T) (kappa := public).
  - change (has_type Gamma (tm_app s (tm_nat n public) r)
      (ty_protect Low (Ty_Arrow T T public))).
    eapply T_App with (T1 := Ty_Nat public) (kappa := public);
      [exact Hs | apply T_Nat; exact I | exact I].
  - apply IHn; assumption.
  - exact I.
Qed.

Theorem preservation : forall t T,
  has_type empty t T -> forall t', step t t' -> has_type empty t' T.
Proof.
  intros t T Htyped. remember empty as Gamma eqn:Hempty.
  induction Htyped; intros t' Hstep; subst Gamma;
    try solve [inversion Hstep];
    try solve [eapply T_Sub; [eapply IHHtyped; [reflexivity | exact Hstep] | exact H]].
  all: inversion Hstep; subst;
    eauto using typing_beta, typing_project_left, typing_project_right,
      typing_case_left, typing_case_right, typing_protect_value,
      T_App, T_Pair, T_Fst, T_Snd, T_Inl, T_Inr, T_Protect, T_Succ, T_NatRec.
  - eapply T_Case with (L := L); eauto.
  - eapply T_Sub.
    + apply T_Protect. apply T_Nat. exact I.
    + apply subtype_protect; [apply subtype_refl; exact I |].
      exact (proj2 (typing_nat_inv _ _ _ _ Htyped)).
  - eapply T_Sub.
    + apply T_Protect. apply typing_unroll; eassumption.
    + apply subtype_protect.
      * apply subtype_refl. exact (proj2 (typing_regular _ _ _ Htyped2)).
      * exact (proj2 (typing_nat_inv _ _ _ _ Htyped1)).
Qed.

Lemma preservation_multi : forall t t' T,
  t -->* t' -> has_type empty t T -> has_type empty t' T.
Proof.
  intros t t' T Hmulti. induction Hmulti; intros Htyped.
  - exact Htyped.
  - apply IHHmulti. eapply preservation; eassumption.
Qed.

Definition erase_context (Gamma : context) : context :=
  map (fun entry => (fst entry, erase_type (snd entry))) Gamma.

Lemma erase_type_wf : forall T, wf_ty (erase_type T).
Proof. induction T; simpl; repeat split; auto; exact I. Qed.

Lemma erase_ty_protect : forall T l, erase_type (ty_protect l T) = erase_type T.
Proof. destruct T; reflexivity. Qed.

Lemma lookup_erase_context : forall Gamma x T,
  lookup_context x Gamma = Some T -> lookup_context x (erase_context Gamma) = Some (erase_type T).
Proof.
  induction Gamma as [ | [y U] Gamma IH]; intros x T H; simpl in *; [discriminate H | ].
  destruct (Nat.eqb x y); [inversion H; reflexivity | apply IH; exact H].
Qed.

Lemma erase_open_rec : forall t k u,
  erase_security (open_rec k u t) = open_rec k (erase_security u) (erase_security t).
Proof.
  induction t; intros k u; simpl; try reflexivity;
    try (f_equal; eauto).
  destruct (Nat.eqb k n); reflexivity.
Qed.

Lemma typing_erasure : forall Gamma t T,
  has_type Gamma t T -> has_type (erase_context Gamma) (erase_security t) (erase_type T).
Proof.
  intros Gamma t T Htyped. induction Htyped; simpl.
  - apply T_Var; [apply lookup_erase_context; exact H | apply erase_type_wf].
  - apply T_Unit; exact I.
  - apply T_Abs with (L := L); [apply erase_type_wf | exact I | ].
    intros x Hx. specialize (H2 x Hx). unfold open in *.
    rewrite erase_open_rec in H2. exact H2.
  - rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type T2)) at 1.
    eapply T_App with (kappa := public); [exact IHHtyped1 | exact IHHtyped2 | exact I].
  - apply T_Pair; [exact IHHtyped1 | exact IHHtyped2 | exact I].
  - rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type T1)) at 1.
    eapply T_Fst with (kappa := public); [exact IHHtyped | exact I].
  - rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type T2)) at 1.
    eapply T_Snd with (kappa := public); [exact IHHtyped | exact I].
  - apply T_Inl; [exact IHHtyped | apply erase_type_wf | exact I].
  - apply T_Inr; [apply erase_type_wf | exact IHHtyped | exact I].
  - rewrite erase_ty_protect.
    rewrite <- (ty_protect_low (erase_type T)) at 1.
    eapply T_Case with (L := L) (kappa := public); [exact IHHtyped | exact I | | ].
    + intros x Hx. specialize (H1 x Hx). unfold open in *. rewrite erase_open_rec in H1. exact H1.
    + intros x Hx. specialize (H3 x Hx). unfold open in *. rewrite erase_open_rec in H3. exact H3.
  - rewrite erase_ty_protect. exact IHHtyped.
  - rewrite <- (subtype_erasure _ _ H). exact IHHtyped.
  - apply T_Nat. exact I.
  - change (has_type (erase_context Gamma) (tm_succ (erase_security t) Low)
      (ty_protect Low (Ty_Nat public))).
    eapply T_Succ with (k := public); [exact IHHtyped | exact I].
  - rewrite erase_ty_protect. rewrite <- (ty_protect_low (erase_type T)) at 1.
    eapply T_NatRec with (k := public);
      [exact IHHtyped1 | exact IHHtyped2 | exact IHHtyped3 | exact I].
Qed.

Lemma erase_lc_at : forall t k, lc_at k t -> lc_at k (erase_security t).
Proof.
  induction t; intros k H; simpl in *; intuition eauto.
Qed.

Lemma protect_value_low : forall v, protect_value v Low = v.
Proof.
  destruct v; simpl; try reflexivity;
    match goal with k : security |- _ => destruct k as [r ir] end;
    destruct r, ir; reflexivity.
Qed.

Lemma erase_unroll : forall n b s r,
  erase_security (natrec_unroll n b s r) =
  natrec_unroll n (erase_security b) (erase_security s) Low.
Proof. induction n; intros; simpl; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma big_step_erasure : forall t v,
  big_step t v -> big_step (erase_security t) (erase_security v).
Proof.
  intros t v Heval. induction Heval; simpl.
  - apply B_Unit.
  - apply B_Abs. apply erase_lc_at; exact H.
  - rewrite erase_protect_value.
    rewrite <- (protect_value_low (erase_security w)).
    eapply B_App with (k := public);
      [exact IHHeval1 | exact IHHeval2 | exact I |].
    unfold open in *. rewrite <- erase_open_rec. exact IHHeval3.
  - apply B_Pair; assumption.
  - rewrite erase_protect_value.
    rewrite <- (protect_value_low (erase_security a)).
    eapply B_Fst with (k := public); [exact IHHeval | exact I].
  - rewrite erase_protect_value.
    rewrite <- (protect_value_low (erase_security b)).
    eapply B_Snd with (k := public); [exact IHHeval | exact I].
  - apply B_Inl; assumption.
  - apply B_Inr; assumption.
  - rewrite erase_protect_value.
    rewrite <- (protect_value_low (erase_security w)).
    eapply B_CaseLeft with (k := public);
      [exact IHHeval1 | exact I |].
    unfold open in *. rewrite <- erase_open_rec. exact IHHeval2.
  - rewrite erase_protect_value.
    rewrite <- (protect_value_low (erase_security w)).
    eapply B_CaseRight with (k := public);
      [exact IHHeval1 | exact I |].
    unfold open in *. rewrite <- erase_open_rec. exact IHHeval2.
  - rewrite erase_protect_value. exact IHHeval.
  - apply B_Nat.
  - change (big_step (tm_succ (erase_security t) Low)
      (protect_value (tm_nat (S n) public) Low)).
    eapply B_Succ with (k := public); [exact IHHeval | exact I].
  - rewrite erase_protect_value.
    rewrite <- (protect_value_low (erase_security result)).
    eapply B_NatRec with (k := public).
    + exact IHHeval1.
    + exact IHHeval2.
    + exact IHHeval3.
    + exact I.
    + rewrite <- erase_unroll with (r := r). exact IHHeval4.
Qed.

Lemma evaluates_erasure : forall t v,
  evaluates t v -> evaluates (erase_security t) (erase_security v).
Proof.
  intros t v H. apply big_step_iff_evaluates.
  apply big_step_erasure. apply big_step_iff_evaluates. exact H.
Qed.
