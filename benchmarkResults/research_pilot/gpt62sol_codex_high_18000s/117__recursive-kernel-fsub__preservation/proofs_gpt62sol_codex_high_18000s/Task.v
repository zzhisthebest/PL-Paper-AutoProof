Require Import Rules.

Set Implicit Arguments.

Require Import Metalib.Metatheory.

Require Import Program.Equality.

From Stdlib Require Import Lia.

Ltac fresh_atom x L :=
  let H := fresh "Fr" in
  destruct (atom_fresh L) as [x H].

Lemma record_lookup_labels : forall T i,
  (exists U, Tlookup i T = Some U) <-> i `in` collectLabel T.
Proof.
  induction T; intros j; simpl; try (split; [intros [? H]; discriminate|fsetdec]).
  destruct (a == j); subst.
  - split; [fsetdec|eauto].
  - rewrite IHT2. fsetdec.
Qed.

Lemma record_lookup_WF : forall E T i U,
  WF E T -> Tlookup i T = Some U -> WF E U.
Proof.
  intros E T i U H. induction H; simpl; intros Heq; try discriminate.
  destruct (i0 == i); [inversion Heq; subst; assumption|eauto].
Qed.

Lemma WF_mono : forall E T, WF E T -> forall F,
  (forall X U, binds X (bind_sub U) E -> exists V, binds X (bind_sub V) F) ->
  WF F T.
Proof.
  intros E T H. induction H; intros F HM; eauto using WF.
  - destruct (HM _ _ H) as [V HV]. eauto using WF.
  - eapply WF_all with (L := L); eauto.
    intros X HX. apply H1; auto.
    intros Y U HB. apply binds_cons_1 in HB as [[? ?]|HB]; subst.
    + eauto using binds_cons_2.
    + destruct (HM _ _ HB); eauto using binds_cons_3.
  - eapply WF_rec with (L := L); intros X HX; [apply H0|apply H2]; auto;
      intros Y U HB; apply binds_cons_1 in HB as [[? ?]|HB]; subst; try destruct (HM _ _ HB); eauto using binds_cons_2, binds_cons_3.
Qed.

Lemma WF_same : forall E F T, WF E T ->
  (forall X U, binds X (bind_sub U) E -> binds X (bind_sub U) F) -> WF F T.
Proof. eauto using WF_mono. Qed.

Lemma WF_drop_typ : forall F E x U T,
  WF (F ++ x ~ bind_typ U ++ E) T -> WF (F ++ E) T.
Proof.
  intros. eapply WF_same; [eassumption|].
  intros X V HB. apply binds_app_iff in HB as [HB|HB]; auto using binds_app_2.
  apply binds_cons_1 in HB as [[? Hbad]|HB]; [discriminate|auto using binds_app_3].
Qed.

Lemma WF_change_bound : forall F E x U V T,
  WF (F ++ x ~ bind_sub U ++ E) T -> WF (F ++ x ~ bind_sub V ++ E) T.
Proof.
  intros. eapply WF_mono; [eassumption|].
  intros X W HB. apply binds_app_iff in HB as [HB|HB].
  - eauto using binds_app_2.
  - apply binds_cons_1 in HB as [[? ?]|HB]; subst; eauto using binds_cons_2, binds_cons_3, binds_app_3.
Qed.

Lemma WF_bound : forall E x b, wf_env E -> binds x b E ->
  WF E (match b with bind_sub T | bind_typ T => T end).
Proof.
  intros E x b HE. induction HE; intros HB; [inversion HB| |];
    apply binds_cons_1 in HB as [[? ?]|HB]; subst;
    eapply WF_same; eauto using binds_cons_3.
Qed.

Lemma wf_env_ok : forall E, wf_env E -> uniq E.
Proof. induction 1; simpl; auto using uniq. Qed.

Lemma sub_wf_env : forall E S T, sub E S T -> wf_env E.
Proof.
  intros E S T H. induction H; eauto.
  fresh_atom X L. specialize (H2 X Fr). inversion H2; auto.
Qed.

Lemma sub_WF : forall E S T, sub E S T -> WF E S /\ WF E T.
Proof.
  intros E S T H. induction H.
  - split; constructor.
  - auto.
  - split; auto using WF_top.
  - destruct IHsub. split; eauto using WF_var.
  - destruct IHsub1, IHsub2. split; auto using WF_arrow.
  - destruct IHsub1, IHsub2. split.
    + eapply WF_all with (L := L); eauto. intros X HX.
      exact (@WF_change_bound nil E X S2 S1 _ (proj1 (H2 X HX))).
    + eapply WF_all with (L := L); eauto. intros X HX. now destruct (H2 X HX).
  - split; eapply WF_rec with (L := L); eauto; intros X HX; now destruct (H2 X HX).
  - destruct IHsub. split; auto using WF_label.
  - auto.
Qed.

Lemma sub_WF_l : forall E S T, sub E S T -> WF E S.
Proof. intros E S T H; exact (proj1 (sub_WF H)). Qed.

Lemma sub_WF_r : forall E S T, sub E S T -> WF E T.
Proof. intros E S T H; exact (proj2 (sub_WF H)). Qed.

Lemma sub_weaken_by : forall E S T, sub E S T -> forall F,
  wf_env F -> (forall X b, binds X b E -> binds X b F) -> sub F S T.
Proof.
  intros E S T H. induction H; intros F HF HM;
    try solve [eauto using sub, WF_same].
  - eapply sa_all with (L := L \u dom F); eauto.
    intros X HX. apply H2; auto.
    + apply wf_env_sub; eauto using sub_WF_l.
    + intros Y U HB. apply binds_cons_1 in HB as [[? ?]|HB]; subst; eauto using binds_cons_2, binds_cons_3.
  - eapply sa_rec with (L := L \u dom F).
    + intros X HX. eapply WF_same; [eauto|].
      intros Y U HB. apply binds_cons_1 in HB as [[? ?]|HB]; subst; eauto using binds_cons_2, binds_cons_3.
    + intros X HX. eapply WF_same; [eauto|].
      intros Y U HB. apply binds_cons_1 in HB as [[? ?]|HB]; subst; eauto using binds_cons_2, binds_cons_3.
    + intros X HX. apply H2.
      * fsetdec.
      * apply wf_env_sub; [exact HF|constructor|fsetdec].
      * intros Y U HB. apply binds_cons_1 in HB as [[? ?]|HB]; subst; eauto using binds_cons_2, binds_cons_3.
  - eapply sa_rcd; eauto using WF_same.
Qed.

(* The weight of a recursive type exceeds the weight of the labelled
   opening used by sa_rec. The index assignment accounts for both openings. *)
Definition push_weight (n : nat) (w : nat -> nat) (k : nat) :=
  match k with 0 => n | S j => w j end.

Fixpoint type_weight (w : nat -> nat) (T : typ) : nat :=
  match T with
  | typ_bvar k => w k
  | typ_arrow A B | typ_rcd_cons _ A B =>
      S (type_weight w A + type_weight w B)
  | typ_all A B => S (type_weight w A + type_weight (push_weight 1 w) B)
  | typ_mu A =>
      S (type_weight (push_weight (S (type_weight (push_weight 1 w) A)) w) A)
  | typ_label _ A => S (type_weight w A)
  | _ => 1
  end.

Fixpoint scoped_tt (k : nat) (T : typ) : Prop :=
  match T with
  | typ_bvar j => j < k
  | typ_arrow A B | typ_rcd_cons _ A B => scoped_tt k A /\ scoped_tt k B
  | typ_all A B => scoped_tt k A /\ scoped_tt (S k) B
  | typ_mu A => scoped_tt (S k) A
  | typ_label _ A => scoped_tt k A
  | _ => True
  end.

Lemma scoped_tt_from_open : forall T k X,
  scoped_tt k (open_tt_rec k (typ_fvar X) T) -> scoped_tt (S k) T.
Proof.
  induction T; simpl; intros k X H; intuition eauto.
  destruct (k === n); simpl in *; lia.
Qed.

Lemma WF_scoped : forall E T, WF E T -> scoped_tt 0 T.
Proof.
  induction 1; simpl; intuition.
  - fresh_atom X L. eapply scoped_tt_from_open. eauto.
  - fresh_atom X L. eapply scoped_tt_from_open. eauto.
Qed.

Lemma scoped_tt_open_id : forall T k U,
  scoped_tt k T -> open_tt_rec k U T = T.
Proof.
  induction T; simpl; intros k U H; try solve [intuition (f_equal; eauto)].
  destruct (k === n); [lia|reflexivity].
Qed.

Lemma weight_eq_at : forall T k w v,
  scoped_tt k T -> (forall j, j < k -> w j = v j) ->
  type_weight w T = type_weight v T.
Proof.
  induction T; simpl; intros k w v Hsc H; auto.
  - destruct Hsc as [HA HB]. rewrite (IHT1 k w v HA H), (IHT2 k w v HB H). reflexivity.
  - destruct Hsc as [HA HB]. rewrite (IHT1 k w v HA H).
    rewrite (IHT2 (S k) (push_weight 1 w) (push_weight 1 v) HB); auto.
    intros [|j] Hj; simpl; auto with arith.
  - assert (HP : forall n, type_weight (push_weight n w) T =
                          type_weight (push_weight n v) T).
    { intro n. eapply IHT; eauto. intros [|j] Hj; simpl; auto with arith. }
    rewrite (HP 1), HP. reflexivity.
  - rewrite (IHT k w v Hsc H). reflexivity.
  - destruct Hsc as [HA HB]. rewrite (IHT1 k w v HA H), (IHT2 k w v HB H). reflexivity.
Qed.

Lemma weight_open : forall T U n,
  (forall w, type_weight w U = n) ->
  forall k w v,
  v k = n ->
  (forall j, j <> k -> v j = w j) ->
  type_weight w (open_tt_rec k U T) = type_weight v T.
Proof.
  induction T; simpl; intros U b HU k w v Hv Hvw; auto.
  - destruct (k === n); subst; [auto|simpl; symmetry; apply Hvw; congruence].
  - f_equal. f_equal; eauto.
  - f_equal. f_equal; eauto.
    eapply IHT2 with (n := b); eauto.
    intros [|j] Hj; simpl; auto.
  - f_equal.
    assert (Heq : type_weight (push_weight 1 w) (open_tt_rec (S k) U T) =
                  type_weight (push_weight 1 v) T).
    { eapply IHT with (n := b); eauto.
      intros [|j] Hj; simpl; auto. }
    rewrite Heq.
    eapply IHT with (n := b); eauto.
    intros [|j] Hj; simpl; auto.
  - f_equal; eauto.
  - f_equal. f_equal; eauto.
Qed.

Definition sub_weight := type_weight (fun _ => 1).

Lemma weight_all_open : forall A B (X : atom),
  sub_weight (open_tt B X) < sub_weight (typ_all A B).
Proof.
  intros A B X. unfold sub_weight, open_tt; simpl.
  pose proof (@weight_open B X 1 (fun _ => eq_refl) 0 (fun _ => 1)
    (push_weight 1 (fun _ => 1)) eq_refl ltac:(intros []; simpl; congruence)) as H.
  rewrite H. lia.
Qed.

Lemma weight_rec_open : forall E A (X : atom),
  WF E (open_tt A X) ->
  sub_weight (open_tt A (typ_label X (open_tt A X))) < sub_weight (typ_mu A).
Proof.
  intros E A X H.
  pose proof (@weight_open A X 1 (fun _ => eq_refl) 0 (fun _ => 1)
    (push_weight 1 (fun _ => 1)) eq_refl ltac:(intros []; simpl; congruence)) as Heq.
  assert (HC : forall w, type_weight w (typ_label X (open_tt A X)) =
                         S (sub_weight (open_tt A X))).
  { intros. simpl. f_equal. unfold sub_weight.
    eapply weight_eq_at with (k := 0); [eauto using WF_scoped|lia]. }
  pose proof (@weight_open A _ _ HC 0 (fun _ => 1)
    (push_weight _ (fun _ => 1)) eq_refl ltac:(intros []; simpl; congruence)) as HO.
  unfold sub_weight at 1 2. simpl. unfold open_tt at 1.
  rewrite HO. unfold sub_weight, open_tt. rewrite Heq. lia.
Qed.

Lemma weight_lookup : forall T i U,
  Tlookup i T = Some U -> sub_weight U < sub_weight T.
Proof.
  induction T; simpl; intros j U HU; try discriminate.
  destruct (a == j).
  - inversion HU; subst. unfold sub_weight; simpl; lia.
  - specialize (IHT2 _ _ HU). unfold sub_weight in *; simpl; lia.
Qed.

Lemma wf_env_change_bound : forall F E X U V,
  wf_env (F ++ X ~ bind_sub U ++ E) -> WF E V ->
  wf_env (F ++ X ~ bind_sub V ++ E).
Proof.
  induction F as [|[y b] F IH]; simpl; intros E X U V HE HV.
  - inversion HE; subst. constructor; auto.
  - inversion HE; subst; constructor.
    all: try (eapply (IH E X U V); eassumption).
    all: try (eapply (@WF_change_bound F E X U V); eassumption).
    all: autorewrite with rewr_dom in *; simpl in *; assumption.
Qed.

Definition trans_at Q :=
  forall E S T, sub E S Q -> sub E Q T -> sub E S T.

Lemma sub_narrow_with : forall Q, trans_at Q -> forall E S T,
  sub E S T -> forall F G X P,
  E = F ++ X ~ bind_sub Q ++ G ->
  sub G P Q -> sub (F ++ X ~ bind_sub P ++ G) S T.
Proof.
  intros Q HT E S T H. induction H; intros F G Y P Heq HP; subst E;
    try solve [eauto 7 using sub, WF_change_bound, wf_env_change_bound, sub_WF_l].
  - apply binds_app_iff in H as [HB|HB].
    + eapply sa_trans_tvar; eauto using binds_app_2.
    + apply binds_cons_1 in HB as [[? ?]|HB]; subst.
      * injection H1 as <-.
        eapply sa_trans_tvar; [eauto using binds_app_3, binds_cons_2|].
        eapply HT; [|eauto].
        eapply sub_weaken_by; [exact HP| |eauto using binds_app_3, binds_cons_3].
        eapply wf_env_change_bound; eauto using sub_wf_env, sub_WF_l.
      * eapply sa_trans_tvar; eauto using binds_app_3, binds_cons_3.
  - eapply sa_all with (L := L); eauto.
    intros Z HZ. eapply (H2 Z HZ ((Z,bind_sub S2)::F)); eauto.
  - eapply sa_rec with (L := L).
    + intros Z HZ. exact (@WF_change_bound ((Z,bind_sub typ_top)::F) G Y Q P _ (H Z HZ)).
    + intros Z HZ. exact (@WF_change_bound ((Z,bind_sub typ_top)::F) G Y Q P _ (H0 Z HZ)).
    + intros Z HZ. eapply (H2 Z HZ ((Z,bind_sub typ_top)::F)); eauto.
Qed.

Lemma sub_trans_smaller : forall Q,
  (forall R, sub_weight R < sub_weight Q -> trans_at R) -> trans_at Q.
Proof.
  unfold trans_at. intros Q IH E S T HS HT.
  remember Q as Q' eqn:HQ in HS. revert HQ HT.
  induction HS; intros HQ HT; subst;
    try solve [eapply sa_trans_tvar; eauto | exact HT].
  all: inversion HT; subst;
    try match goal with HR : rt_type _ |- _ => solve [inversion HR] end;
    try solve [eapply sa_top; eauto using sub_WF_l, sa_top, sa_arrow, sa_all, sa_rec, sa_label, sa_rcd].
  - eapply sa_arrow; eapply IH; eauto; unfold sub_weight; simpl; lia.
  - eapply sa_all with (L := L \u L0).
    + eapply IH; eauto. unfold sub_weight; simpl; lia.
    + eapply IH; eauto. unfold sub_weight; simpl; lia.
    + intros X HX.
      specialize (H X ltac:(fsetdec)). specialize (H7 X ltac:(fsetdec)).
      eapply IH; [apply weight_all_open| |exact H7].
      exact (@sub_narrow_with S2 (IH S2 ltac:(unfold sub_weight; simpl; lia))
        _ _ _ H nil E X S3 eq_refl H5).
  - eapply sa_rec with (L := L \u L0); intros X HX.
    + eapply H. fsetdec.
    + eapply H5. fsetdec.
    + specialize (H0 X ltac:(fsetdec)).
      eapply (IH (open_tt A2 (typ_label X (open_tt A2 X))));
        [exact (@weight_rec_open _ A2 X H0)|apply H1; fsetdec|apply H7; fsetdec].
  - constructor. eapply IH; eauto. unfold sub_weight; simpl; lia.
  - eapply sa_rcd; eauto.
    + etransitivity; eassumption.
    + intros i U V HU HV.
      assert (Hmem : i \in collectLabel Q).
      { apply H10. apply record_lookup_labels. eauto. }
      apply record_lookup_labels in Hmem as [W HW].
      eapply IH; [eapply weight_lookup; exact HW|eauto|eauto].
Qed.

Lemma sub_trans : forall E S Q T, sub E S Q -> sub E Q T -> sub E S T.
Proof.
  assert (H : forall n Q, sub_weight Q = n -> trans_at Q).
  { induction n using lt_wf_ind. intros Q HQ. apply sub_trans_smaller.
    intros R HR. apply (H (sub_weight R)); [lia|reflexivity]. }
  intros E S Q T. exact (H _ _ eq_refl E S T).
Qed.

Lemma sub_refl : forall E T, WF E T -> wf_env E -> sub E T T.
Proof.
  intros E T H. induction H; intros HE; try solve [eauto using sub, WF].
  - eapply sa_all with (L := L \u dom E); eauto.
    intros X HX. apply H1; [fsetdec|constructor; auto; fsetdec].
  - eapply sa_rec with (L := L \u dom E); eauto.
    intros X HX. apply H2; [fsetdec|constructor; auto using WF_top; fsetdec].
  - eapply sa_rcd; eauto using rt_type, WF_rcd_nil; try reflexivity. intros i t1 t2 HH. discriminate.
  - eapply sa_rcd; eauto using rt_type, WF_rcd_cons; try reflexivity.
    intros j U V HU HV. rewrite HU in HV. inversion HV; subst.
    simpl in HU. destruct (i == j).
    + inversion HU; subst; auto.
    + inversion H1; subst.
      * discriminate.
      * eapply IHWF2 in HE. inversion HE; subst; try discriminate.
        eapply (H9 j); eassumption.
Qed.

Lemma incl_binds_cons : forall (E F : env) X b,
  (forall Y c, binds Y c E -> binds Y c F) ->
  forall Y c, binds Y c (X ~ b ++ E) -> binds Y c (X ~ b ++ F).
Proof.
  intros E F X b HI Y c HB.
  apply binds_cons_1 in HB as [[? ?]|HB]; subst; eauto using binds_cons_2, binds_cons_3.
Qed.

Lemma WF_push : forall E X b T, WF E T -> WF (X ~ b ++ E) T.
Proof. eauto using WF_same, binds_cons_3. Qed.

Lemma sub_push : forall E X b S T,
  sub E S T -> wf_env (X ~ b ++ E) -> sub (X ~ b ++ E) S T.
Proof. eauto using sub_weaken_by, binds_cons_3. Qed.

(* Type substitution and replacement of recursive labels share the same
   transport proof. The predicate on labels specifies where replacement applies. *)
Fixpoint translate (f : atom -> typ) (g : atom -> typ -> typ -> typ) (T : typ) : typ :=
  match T with
  | typ_fvar X => f X
  | typ_arrow A B => typ_arrow (translate f g A) (translate f g B)
  | typ_all A B => typ_all (translate f g A) (translate f g B)
  | typ_mu A => typ_mu (translate f g A)
  | typ_label l A => g l A (translate f g A)
  | typ_rcd_cons i A B => typ_rcd_cons i (translate f g A) (translate f g B)
  | _ => T
  end.

Fixpoint acceptable (p : atom -> typ -> Prop) (T : typ) : Prop :=
  match T with
  | typ_arrow A B | typ_all A B | typ_rcd_cons _ A B => acceptable p A /\ acceptable p B
  | typ_mu A => acceptable p A
  | typ_label l A => p l A /\ acceptable p A
  | _ => True
  end.

Section Translation.
  Variables (f : atom -> typ) (g : atom -> typ -> typ -> typ)
            (p : atom -> typ -> Prop) (avoid : atoms).
  Local Notation M := (translate f g).
  Local Notation good := (acceptable p).

  Hypothesis good_open : forall A U, good A -> good U -> good (open_tt A U).
  Hypothesis map_open : forall A U, good A -> M (open_tt A U) = open_tt (M A) (M U).
  Hypothesis map_var_fresh : forall X, X `notin` avoid -> f X = typ_fvar X.
  Hypothesis map_label_fresh : forall X A B, X `notin` avoid -> g X A B = typ_label X B.
  Hypothesis good_label_fresh : forall X A, X `notin` avoid -> p X A.

  Variables (E0 F0 : env).
  Local Notation extends E F := (forall X b, binds X b E -> binds X b F).
  Local Notation good_env E := (forall X U, binds X (bind_sub U) E -> good U).
  Local Notation wf_vars E F :=
    (forall X U, binds X (bind_sub U) E -> WF F (f X)).
  Local Notation sub_vars E F :=
    (forall X U, binds X (bind_sub U) E -> sub F (f X) (M U)).

  Hypothesis map_label_WF : forall F X A,
    extends F0 F -> wf_env F -> p X A -> WF F (M A) -> WF F (g X A (M A)).
  Hypothesis map_label_sub : forall E F X A B,
    extends E0 E -> extends F0 F -> wf_env F -> p X A -> p X B ->
    sub E A B -> sub F (M A) (M B) ->
    sub F (g X A (M A)) (g X B (M B)).

  Lemma translate_lookup_any : forall A i B,
    Tlookup i A = Some B -> Tlookup i (M A) = Some (M B).
  Proof.
    induction A; simpl; intros i B HB; try discriminate.
    destruct (a == i); [inversion HB; auto|eauto].
  Qed.

  Lemma translate_lookup_inv : forall E A i B, WF E A -> rt_type A ->
    Tlookup i (M A) = Some B ->
    exists C, Tlookup i A = Some C /\ B = M C.
  Proof.
    intros E A i B HW. induction HW; inversion 1; subst; simpl; intros HB; try discriminate.
    destruct (i0 == i); [inversion HB; eauto|eauto].
  Qed.

  Lemma good_lookup : forall A i B, good A -> Tlookup i A = Some B -> good B.
  Proof.
    induction A; simpl; intros i B HG HB; try discriminate.
    destruct HG, (a == i); [inversion HB; subst; auto|eauto].
  Qed.

  Lemma translate_rcd : forall E A, WF E A -> rt_type A ->
    collectLabel (M A) = collectLabel A.
  Proof.
    induction 1; inversion 1; subst; simpl; auto. now rewrite IHWF2.
  Qed.

  Lemma translated_vars_push : forall E F X A,
    wf_vars E F -> X `notin` avoid ->
    wf_vars (X ~ bind_sub A ++ E) (X ~ bind_sub (M A) ++ F).
  Proof.
    intros E F X A HV HX Y U HB. apply binds_cons_1 in HB as [[? ?]|HB]; subst.
    - rewrite map_var_fresh by assumption. eauto using WF_var, binds_cons_2.
    - eauto using WF_push.
  Qed.

  Lemma good_env_push : forall E X A,
    good_env E -> good A -> good_env (X ~ bind_sub A ++ E).
  Proof.
    intros E X A HE HA Y U HB. apply binds_cons_1 in HB as [[-> Heq]|HB].
    - now inversion Heq.
    - exact (HE _ _ HB).
  Qed.

  Lemma translate_WF : forall E A, WF E A -> forall F,
    extends F0 F -> wf_env F -> wf_vars E F -> good A -> WF F (M A).
  Proof.
    intros E A H. induction H; intros F HF HWF HV HG; simpl in *;
      try solve [intuition eauto 4 using WF_top, WF_nat, WF_arrow, WF_rcd_nil].
    - destruct HG as [HG1 HG2].
      assert (HB : WF F (M T1)) by eauto.
      eapply WF_all with (L := L \u dom F \u avoid); eauto.
      intros X HX. assert (HXa : X `notin` avoid) by fsetdec.
      rewrite <- (@map_var_fresh X HXa) at 1.
      change (WF (X ~ bind_sub (M T1) ++ F) (open_tt (M T2) (M X))).
      rewrite <- map_open by assumption.
      apply (H1 X ltac:(fsetdec)).
      + eauto using binds_cons_3.
      + constructor; auto; fsetdec.
      + exact (@translated_vars_push E F X T1 HV HXa).
      + apply good_open; [exact HG2|exact I].
    - eapply WF_rec with (L := L \u dom F \u avoid); intros X HX;
        assert (HXa : X `notin` avoid) by fsetdec;
        assert (HE : wf_env (X ~ bind_sub typ_top ++ F)) by
          (constructor; [assumption|constructor|fsetdec]).
      + pose proof (@map_open A (typ_fvar X) HG) as HO.
        simpl in HO. rewrite (@map_var_fresh X HXa) in HO. rewrite <- HO.
        apply (H0 X ltac:(fsetdec)).
        * eauto using binds_cons_3.
        * exact HE.
        * exact (@translated_vars_push E F X typ_top HV HXa).
        * apply good_open; [exact HG|exact I].
      + pose proof (@map_open A (typ_label X (open_tt A X)) HG) as HO.
        pose proof (@map_open A (typ_fvar X) HG) as Hinner.
        simpl in HO, Hinner. rewrite (@map_label_fresh X _ _ HXa), Hinner,
          (@map_var_fresh X HXa) in HO. rewrite <- HO.
        apply (H2 X ltac:(fsetdec)).
        * eauto using binds_cons_3.
        * exact HE.
        * exact (@translated_vars_push E F X typ_top HV HXa).
        * apply good_open; [exact HG|]. split.
          -- exact (@good_label_fresh X _ HXa).
          -- apply good_open; [exact HG|exact I].
    - destruct HG as [HG1 HG2]. apply WF_rcd_cons; eauto.
      + inversion H1; simpl; constructor.
      + rewrite (translate_rcd H0 H1). assumption.
  Qed.

  Lemma translated_sub_vars_push : forall E F X A,
    sub_vars E F -> X `notin` avoid -> wf_env (X ~ bind_sub (M A) ++ F) ->
    sub_vars (X ~ bind_sub A ++ E) (X ~ bind_sub (M A) ++ F).
  Proof.
    intros E F X A HV HX HF Y U HB. apply binds_cons_1 in HB as [[? ?]|HB]; subst.
    - inversion H0; subst. rewrite map_var_fresh by assumption.
      eapply sa_trans_tvar; [eauto using binds_cons_2|].
      apply sub_refl; eauto. eapply (@WF_bound _ _ (bind_sub (M A))); eauto using binds_cons_2.
    - eauto using sub_push.
  Qed.

  Lemma translate_sub : forall E A B, sub E A B -> forall F,
    extends E0 E -> extends F0 F -> wf_env F ->
    sub_vars E F -> good_env E -> good A -> good B -> sub F (M A) (M B).
  Proof.
    intros E A B H. induction H; intros F HE HF HW HV HEg HA HB; simpl in *.
    - apply sa_nat. exact HW.
    - inversion H0; subst. eauto using sub_refl, sub_WF_l.
    - apply sa_top; [exact HW|].
      apply (@translate_WF E A H0 F); eauto using sub_WF_l.
    - eapply sub_trans with (Q := M U).
      + exact (HV _ _ H).
      + apply IHsub; auto. exact (HEg _ _ H).
    - destruct HA, HB. apply sa_arrow; auto.
    - destruct HA as [HA1 HA2], HB as [HB1 HB2].
      assert (HD : sub F (M S1) (M S2)) by eauto.
      eapply sa_all with (L := L \u dom F \u avoid); eauto.
      intros X HX. assert (HXa : X `notin` avoid) by fsetdec.
      pose proof (@map_open T1 (typ_fvar X) HA2) as HO1.
      pose proof (@map_open T2 (typ_fvar X) HB2) as HO2.
      simpl in HO1, HO2. rewrite (@map_var_fresh X HXa) in HO1, HO2.
      rewrite <- HO1, <- HO2.
      assert (HF' : wf_env (X ~ bind_sub (M S2) ++ F)).
      { constructor; [exact HW|exact (sub_WF_r HD)|fsetdec]. }
      apply (H2 X ltac:(fsetdec)).
      + eauto using binds_cons_3.
      + eauto using binds_cons_3.
      + exact HF'.
      + exact (@translated_sub_vars_push E F X S2 HV HXa HF').
      + exact (@good_env_push E X S2 HEg HB1).
      + apply good_open; [exact HA2|exact I].
      + apply good_open; [exact HB2|exact I].
    - assert (Hwfvar : wf_vars E F) by (intros Y U Hbind; exact (sub_WF_l (HV Y U Hbind))).
      eapply sa_rec with (L := L \u dom F \u avoid); intros X HX;
        assert (HXa : X `notin` avoid) by fsetdec;
        assert (HF' : wf_env (X ~ bind_sub typ_top ++ F)) by
          (constructor; [assumption|constructor|fsetdec]);
        pose proof (@map_open A1 (typ_fvar X) HA) as HO1;
        pose proof (@map_open A2 (typ_fvar X) HB) as HO2;
        simpl in HO1, HO2; rewrite (@map_var_fresh X HXa) in HO1, HO2.
      + rewrite <- HO1.
        apply (@translate_WF _ _ (H X ltac:(fsetdec))); eauto using binds_cons_3.
        * exact (@translated_vars_push E F X typ_top Hwfvar HXa).
        * apply good_open; [exact HA|exact I].
      + rewrite <- HO2.
        apply (@translate_WF _ _ (H0 X ltac:(fsetdec))); eauto using binds_cons_3.
        * exact (@translated_vars_push E F X typ_top Hwfvar HXa).
        * apply good_open; [exact HB|exact I].
      + pose proof (@map_open A1 (typ_label X (open_tt A1 X)) HA) as HO1'.
        pose proof (@map_open A2 (typ_label X (open_tt A2 X)) HB) as HO2'.
        simpl in HO1', HO2'.
        rewrite (@map_label_fresh X _ _ HXa), HO1 in HO1'.
        rewrite (@map_label_fresh X _ _ HXa), HO2 in HO2'.
        rewrite <- HO1', <- HO2'.
        apply (H2 X ltac:(fsetdec)); eauto using binds_cons_3.
        * exact (@translated_sub_vars_push E F X typ_top HV HXa HF').
        * exact (@good_env_push E X typ_top HEg I).
        * apply good_open; [exact HA|]. split.
          -- exact (@good_label_fresh X _ HXa).
          -- apply good_open; [exact HA|exact I].
        * apply good_open; [exact HB|]. split.
          -- exact (@good_label_fresh X _ HXa).
          -- apply good_open; [exact HB|exact I].
    - destruct HA, HB. eapply map_label_sub; eauto.
    - assert (Hwfvar : wf_vars E F) by (intros Y U Hbind; exact (sub_WF_l (HV Y U Hbind))).
      eapply sa_rcd.
      + exact HW.
      + inversion H0; simpl; constructor.
      + inversion H1; simpl; constructor.
      + rewrite (translate_rcd H4 H1), (translate_rcd H3 H0). assumption.
      + apply (@translate_WF _ _ H3); assumption.
      + apply (@translate_WF _ _ H4); assumption.
      + intros i U V HU HV'.
        destruct (@translate_lookup_inv E A1 i U H3 H0 HU) as [C [HC ->]].
        destruct (@translate_lookup_inv E A2 i V H4 H1 HV') as [D [HD ->]].
        eauto using good_lookup.
  Qed.
End Translation.

Lemma sub_strengthen : forall E A B, sub E A B -> forall F,
  (forall X b, binds X b F -> binds X b E) ->
  wf_env F -> WF F A -> WF F B -> sub F A B.
Proof.
  intros E A B HS. induction HS; intros F HI HF HA HB;
    try solve [eauto using sub].
  - inversion HA; subst.
    assert (Eqa : bind_sub U = bind_sub U0).
    { eapply binds_unique; eauto using wf_env_ok, sub_wf_env. }
    injection Eqa as <-.
    eapply sa_trans_tvar; eauto.
    apply IHHS; auto. exact (@WF_bound _ _ _ HF H2).
  - inversion HA; inversion HB; subst. eauto using sa_arrow.
  - inversion HA; inversion HB; subst.
    eapply sa_all with (L := L \u L0 \u L1 \u dom F); eauto.
    intros X HX. apply (H0 X ltac:(fsetdec)).
    + apply incl_binds_cons; exact HI.
    + constructor; auto; fsetdec.
    + apply (@WF_change_bound nil F X S1 S2). apply H5. fsetdec.
    + apply H10. fsetdec.
  - inversion HA; inversion HB; subst.
    eapply sa_rec with (L := L \u L0 \u L1 \u dom F); eauto.
    intros X HX. eapply H2; eauto using incl_binds_cons.
    + constructor; auto using WF_top; fsetdec.
  - inversion HA; inversion HB; subst. eauto using sa_label.
  - eapply sa_rcd; eauto using record_lookup_WF.
Qed.

Lemma wf_env_drop_typ : forall F E x U,
  wf_env (F ++ x ~ bind_typ U ++ E) -> wf_env (F ++ E).
Proof.
  induction F as [|[y b] F IH]; simpl; intros E x U HE.
  - inversion HE; subst; auto.
  - inversion HE; subst; constructor.
    all: try (eapply (IH E x U); eassumption).
    all: try (eapply (@WF_drop_typ F E x U); eassumption).
    all: autorewrite with rewr_dom in *; simpl in *; fsetdec.
Qed.

Lemma sub_drop_typ : forall F E x U A B,
  sub (F ++ x ~ bind_typ U ++ E) A B -> sub (F ++ E) A B.
Proof.
  intros F E x U A B H.
  eapply sub_strengthen; [exact H| | | |].
  - intros. eauto using binds_weaken.
  - eapply (@wf_env_drop_typ F E x U), sub_wf_env; eauto.
  - exact (@WF_drop_typ F E x U A (sub_WF_l H)).
  - exact (@WF_drop_typ F E x U B (sub_WF_r H)).
Qed.

Lemma scoped_tt_mono : forall T j k, scoped_tt j T -> j <= k -> scoped_tt k T.
Proof.
  induction T; simpl; intuition eauto with arith.
Qed.

Lemma subst_tt_open_rec : forall A X P U k, scoped_tt 0 P ->
  subst_tt X P (open_tt_rec k U A) =
  open_tt_rec k (subst_tt X P U) (subst_tt X P A).
Proof.
  induction A; simpl; intros X P U k HP; try solve [f_equal; eauto].
  - destruct (k === n); reflexivity.
  - destruct (a == X); simpl; auto.
    symmetry. apply scoped_tt_open_id. eauto using scoped_tt_mono, Nat.le_0_l.
Qed.

Lemma subst_tt_fresh : forall T X P, X `notin` fv_tt T -> subst_tt X P T = T.
Proof.
  induction T; simpl; intros X P H; try reflexivity;
    try solve [f_equal; eauto; apply IHT1 || apply IHT2; fsetdec].
  - destruct (a == X); [fsetdec|reflexivity].
Qed.

Lemma subst_tt_intro : forall A X P, X `notin` fv_tt A -> scoped_tt 0 P ->
  subst_tt X P (open_tt A X) = open_tt A P.
Proof.
  unfold open_tt. intros A X P Hfresh HP.
  rewrite subst_tt_open_rec by assumption.
  rewrite (@subst_tt_fresh A X P Hfresh).
  simpl. destruct (X == X); congruence.
Qed.

Definition subst_var (X : atom) (P : typ) (Y : atom) : typ :=
  if Y == X then P else typ_fvar Y.

Lemma translate_subst : forall X P A,
  translate (subst_var X P) (fun l _ B => typ_label l B) A = subst_tt X P A.
Proof. induction A; simpl; try reflexivity; f_equal; assumption. Qed.

Lemma acceptable_all : forall A, acceptable (fun _ _ => True) A.
Proof. induction A; simpl; intuition. Qed.

Lemma WF_substitute_into : forall E F X P A,
  WF E A -> wf_env F -> scoped_tt 0 P ->
  (forall Y U, binds Y (bind_sub U) E -> WF F (subst_var X P Y)) ->
  WF F (subst_tt X P A).
Proof.
  intros E F X P A HA HF HP HV.
  rewrite <- translate_subst.
  refine (@translate_WF (subst_var X P) (fun l _ B => typ_label l B)
    (fun _ _ => True) {{X}} _ _ _ _ _ nil _ E A HA F _ HF HV (acceptable_all A)).
  - intros. apply acceptable_all.
  - intros. unfold open_tt. rewrite !translate_subst. auto using subst_tt_open_rec.
  - intros Y HY. unfold subst_var. destruct (Y == X); [fsetdec|reflexivity].
  - reflexivity.
  - intros; exact I.
  - eauto using WF_label.
  - intros ? ? HB; inversion HB.
Qed.

Lemma sub_substitute_into : forall E F X P A B,
  sub E A B -> wf_env F -> scoped_tt 0 P ->
  (forall Y U, binds Y (bind_sub U) E -> sub F (subst_var X P Y) (subst_tt X P U)) ->
  sub F (subst_tt X P A) (subst_tt X P B).
Proof.
  intros E F X P A B HS HF HP HV.
  rewrite <- !translate_subst.
  refine (@translate_sub (subst_var X P) (fun l _ B => typ_label l B)
    (fun _ _ => True) {{X}} _ _ _ _ _ nil nil _ _ E A B HS F _ _ HF _ _
    (acceptable_all A) (acceptable_all B)).
  - intros. apply acceptable_all.
  - intros. unfold open_tt. rewrite !translate_subst. auto using subst_tt_open_rec.
  - intros Y HY. unfold subst_var. destruct (Y == X); [fsetdec|reflexivity].
  - reflexivity.
  - intros; exact I.
  - eauto using WF_label.
  - eauto using sa_label.
  - intros ? ? HB; inversion HB.
  - intros ? ? HB; inversion HB.
  - intros. rewrite translate_subst. eauto.
  - intros. apply acceptable_all.
Qed.

Lemma WF_open_single : forall X A U Q E,
  WF (X ~ bind_sub Q) (open_tt A X) -> WF E U -> wf_env E ->
  X `notin` fv_tt A -> WF E (open_tt A U).
Proof.
  intros X A U Q E HA HU HE HX.
  rewrite <- (@subst_tt_intro A X U) by eauto using WF_scoped.
  eapply WF_substitute_into; eauto using WF_scoped.
  intros Y T HB. apply binds_cons_1 in HB as [[-> _]|HB]; [|inversion HB].
  unfold subst_var. destruct (X == X); [assumption|congruence].
Qed.

Lemma sub_open_single : forall X A B Q U E,
  sub (X ~ bind_sub Q) (open_tt A X) (open_tt B X) ->
  sub E U Q -> X `notin` fv_tt A -> X `notin` fv_tt B ->
  subst_tt X U Q = Q -> sub E (open_tt A U) (open_tt B U).
Proof.
  intros X A B Q U E HS HU HA HB HQ.
  rewrite <- (@subst_tt_intro A X U), <- (@subst_tt_intro B X U)
    by eauto using WF_scoped, sub_WF_l.
  eapply sub_substitute_into; eauto using sub_wf_env, sub_WF_l, WF_scoped.
  intros Y T Hbind. apply binds_cons_1 in Hbind as [[-> Heq]|Hbind]; [|inversion Hbind].
  inversion Heq; subst. unfold subst_var. destruct (X == X); [now rewrite HQ|congruence].
Qed.

Lemma binds_subst_env : forall F E X U P Y b,
  X <> Y -> binds Y b (F ++ X ~ bind_sub U ++ E) ->
  (forall Z c, binds Z c E -> subst_tb X P c = c) ->
  binds Y (subst_tb X P b) (map (subst_tb X P) F ++ E).
Proof.
  intros F E X U P Y b Hne HB HE.
  apply binds_app_iff in HB as [HB|HB].
  - apply binds_app_2. eauto using binds_map.
  - apply binds_cons_1 in HB as [[? ?]|HB]; [congruence|].
    rewrite (HE Y b HB). eauto using binds_app_3.
Qed.

Lemma wf_env_subst : forall F E X U P,
  wf_env (F ++ X ~ bind_sub U ++ E) -> WF E P ->
  (forall Z c, binds Z c E -> subst_tb X P c = c) ->
  wf_env (map (subst_tb X P) F ++ E).
Proof.
  induction F as [|[Y b] F IH]; simpl; intros E X U P HE HP HEq.
  - inversion HE; auto.
  - inversion HE; subst; simpl; constructor.
    all: try solve [eapply (IH E X U); eassumption].
    all: try solve [autorewrite with rewr_dom in *; simpl in *; fsetdec].
    all: eapply WF_substitute_into; eauto using WF_scoped.
    all: try solve [apply (IH E X U P); assumption].
    all: intros Z C HB; unfold subst_var; destruct (Z == X); subst.
    all: try solve [eapply WF_same; [exact HP|eauto using binds_app_3]].
    all: eapply WF_var with (U := subst_tt X P C);
      exact (@binds_subst_env F E X U P Z (bind_sub C) ltac:(congruence) HB HEq).
Qed.

Lemma sub_subst : forall F E X U P A B,
  sub (F ++ X ~ bind_sub U ++ E) A B -> sub E P U ->
  subst_tt X P U = U ->
  (forall Z c, binds Z c E -> subst_tb X P c = c) ->
  sub (map (subst_tb X P) F ++ E) (subst_tt X P A) (subst_tt X P B).
Proof.
  intros F E X U P A B HS HP HU HE.
  assert (HF : wf_env (map (subst_tb X P) F ++ E)).
  { eapply (@wf_env_subst F E X U); eauto using sub_wf_env, sub_WF_l. }
  eapply sub_substitute_into; eauto using WF_scoped, sub_WF_l.
  intros Y C HB. unfold subst_var. destruct (Y == X); subst.
  - assert (HC : bind_sub C = bind_sub U).
    { eapply binds_mid_eq; eauto using wf_env_ok, sub_wf_env. }
    injection HC as ->. rewrite HU. eapply sub_weaken_by; eauto using binds_app_3.
  - assert (HB' := @binds_subst_env F E X U P Y (bind_sub C) ltac:(congruence) HB HE).
    eapply sa_trans_tvar; [exact HB'|].
    apply sub_refl; eauto. exact (@WF_bound _ _ _ HF HB').
Qed.

Lemma value_expr : forall e, value e -> expr e.
Proof. induction 1; eauto using expr. Qed.

Fixpoint scoped_ee (k : nat) (e : exp) : Prop :=
  match e with
  | exp_bvar j => j < k
  | exp_abs _ b => scoped_ee (S k) b
  | exp_tabs _ b | exp_tapp b _ | exp_fold _ b | exp_unfold _ b | exp_rcd_proj b _ =>
      scoped_ee k b
  | exp_app a b | exp_rcd_cons _ a b => scoped_ee k a /\ scoped_ee k b
  | _ => True
  end.

Fixpoint scoped_te (k : nat) (e : exp) : Prop :=
  match e with
  | exp_abs T b | exp_tapp b T | exp_fold T b | exp_unfold T b =>
      scoped_tt k T /\ scoped_te k b
  | exp_tabs T b => scoped_tt k T /\ scoped_te (S k) b
  | exp_rcd_proj b _ => scoped_te k b
  | exp_app a b | exp_rcd_cons _ a b => scoped_te k a /\ scoped_te k b
  | _ => True
  end.

Lemma type_scoped : forall T, type T -> scoped_tt 0 T.
Proof.
  induction 1; simpl; intuition.
  all: fresh_atom X L; eapply scoped_tt_from_open; eauto.
Qed.

Lemma scoped_ee_from_open : forall e k x,
  scoped_ee k (open_ee_rec k (exp_fvar x) e) -> scoped_ee (S k) e.
Proof.
  induction e; simpl; intros k x H; intuition eauto.
  destruct (k == n); simpl in *; lia.
Qed.

Lemma scoped_ee_open_te : forall e j k U,
  scoped_ee j (open_te_rec k U e) -> scoped_ee j e.
Proof. induction e; simpl; intuition eauto. Qed.

Lemma scoped_te_open_ee : forall e j k x,
  scoped_te j (open_ee_rec k (exp_fvar x) e) -> scoped_te j e.
Proof. induction e; simpl; intuition eauto. Qed.

Lemma scoped_te_from_open : forall e k X,
  scoped_te k (open_te_rec k (typ_fvar X) e) -> scoped_te (S k) e.
Proof. induction e; simpl; intuition eauto using scoped_tt_from_open. Qed.

Lemma expr_scoped : forall e, expr e -> scoped_ee 0 e /\ scoped_te 0 e.
Proof.
  induction 1; simpl; intuition eauto using type_scoped.
  - fresh_atom x L. eapply scoped_ee_from_open. exact (proj1 (H1 x Fr)).
  - fresh_atom x L. eapply scoped_te_open_ee. exact (proj2 (H1 x Fr)).
  - fresh_atom X L. eapply scoped_ee_open_te. exact (proj1 (H1 X Fr)).
  - fresh_atom X L. eapply scoped_te_from_open. exact (proj2 (H1 X Fr)).
Qed.

Lemma scoped_ee_open_id : forall e k u,
  scoped_ee k e -> open_ee_rec k u e = e.
Proof.
  induction e; simpl; intros k u H; try solve [intuition (f_equal; eauto)].
  destruct (k == n); [lia|reflexivity].
Qed.

Lemma scoped_te_open_id : forall e k U,
  scoped_te k e -> open_te_rec k U e = e.
Proof. induction e; simpl; intuition (f_equal; eauto using scoped_tt_open_id). Qed.

Lemma scoped_ee_mono : forall e j k, scoped_ee j e -> j <= k -> scoped_ee k e.
Proof.
  induction e; simpl; intuition eauto with arith.
Qed.

Lemma scoped_te_mono : forall e j k, scoped_te j e -> j <= k -> scoped_te k e.
Proof.
  induction e; simpl; intuition eauto using scoped_tt_mono with arith.
Qed.

Lemma subst_ee_open_rec : forall e z v k u, scoped_ee 0 v ->
  subst_ee z v (open_ee_rec k u e) =
  open_ee_rec k (subst_ee z v u) (subst_ee z v e).
Proof.
  induction e; simpl; intros z v k u HC; try solve [f_equal; eauto].
  - destruct (k == n); reflexivity.
  - destruct (a == z); simpl; auto.
    symmetry. apply scoped_ee_open_id.
    eauto using scoped_ee_mono, Nat.le_0_l.
Qed.

Lemma subst_ee_open_te_rec : forall e z v k U, scoped_te 0 v ->
  subst_ee z v (open_te_rec k U e) = open_te_rec k U (subst_ee z v e).
Proof.
  induction e; simpl; intros z v k U HC; try solve [f_equal; eauto].
  destruct (a == z); simpl; auto.
  symmetry. apply scoped_te_open_id.
  eauto using scoped_te_mono, Nat.le_0_l.
Qed.

Lemma subst_ee_fresh : forall e z v, z `notin` fv_ee e -> subst_ee z v e = e.
Proof.
  induction e; simpl; intros z v H; try reflexivity;
    try solve [f_equal; eauto; (apply IHe1 || apply IHe2); fsetdec].
  destruct (a == z); [fsetdec|reflexivity].
Qed.

Lemma subst_te_fresh : forall e Z P, Z `notin` fv_te e -> subst_te Z P e = e.
Proof.
  induction e; simpl; intros Z P H; try reflexivity;
    f_equal; eauto using subst_tt_fresh;
    (apply IHe || apply IHe1 || apply IHe2 || apply subst_tt_fresh); fsetdec.
Qed.

Lemma subst_ee_intro : forall e z v, expr v -> z `notin` fv_ee e ->
  subst_ee z v (open_ee e z) = open_ee e v.
Proof.
  unfold open_ee. intros e z v HV Hfresh.
  rewrite subst_ee_open_rec by exact (proj1 (expr_scoped HV)).
  rewrite (@subst_ee_fresh e z v Hfresh).
  simpl. destruct (z == z); congruence.
Qed.

Lemma subst_te_open_rec : forall e Z P k U, scoped_tt 0 P ->
  subst_te Z P (open_te_rec k U e) =
  open_te_rec k (subst_tt Z P U) (subst_te Z P e).
Proof.
  induction e; simpl; intros; f_equal; eauto using subst_tt_open_rec.
Qed.

Lemma subst_te_open_ee_rec : forall e Z P k u,
  subst_te Z P (open_ee_rec k u e) =
  open_ee_rec k (subst_te Z P u) (subst_te Z P e).
Proof.
  induction e; simpl; intros; try solve [f_equal; eauto].
  destruct (k == n); reflexivity.
Qed.

Lemma subst_te_intro : forall e Z P, scoped_tt 0 P -> Z `notin` fv_te e ->
  subst_te Z P (open_te e Z) = open_te e P.
Proof.
  unfold open_te. intros e Z P HP Hfresh.
  rewrite subst_te_open_rec, subst_te_fresh by assumption.
  simpl. destruct (Z == Z); congruence.
Qed.

Lemma typing_wf_env : forall E e T, typing E e T -> wf_env E.
Proof.
  intros E e T H. induction H; eauto.
  all: fresh_atom Z L; specialize (H0 Z Fr); inversion H0; auto.
Qed.

Lemma typing_weaken_by : forall E e T, typing E e T -> forall F,
  wf_env F -> (forall X b, binds X b E -> binds X b F) -> typing F e T.
Proof.
  intros E e T H. induction H; intros F HF HM;
    try solve [eauto using typing, sub_weaken_by].
  - fresh_atom x (L \u dom E).
    assert (HW := typing_wf_env (H x ltac:(fsetdec))).
    inversion HW; subst.
    eapply typing_abs with (L := L \u dom F). intros y HY.
    apply H0.
    + fsetdec.
    + constructor; eauto using WF_same; fsetdec.
    + apply incl_binds_cons; auto.
  - fresh_atom X (L \u dom E).
    assert (HW := typing_wf_env (H X ltac:(fsetdec))).
    inversion HW; subst.
    eapply typing_tabs with (L := L \u dom F). intros Y HY.
    apply H0.
    + fsetdec.
    + constructor; eauto using WF_same; fsetdec.
    + apply incl_binds_cons; auto.
Qed.

(* A typed record has a record constructor at every point along its tail. *)
Inductive record_spine : exp -> Prop :=
| spine_nil : record_spine exp_rcd_nil
| spine_cons : forall i e r, record_spine r -> record_spine (exp_rcd_cons i e r).

Lemma spine_rt : forall e, record_spine e -> rt_expr e.
Proof. inversion 1; constructor. Qed.

Lemma typing_spine : forall E e T, typing E e T -> rt_expr e -> record_spine e.
Proof.
  induction 1; intros HR; try solve [inversion HR]; eauto using record_spine.
Qed.

Lemma spine_subst_ee : forall e z v, record_spine e ->
  record_spine (subst_ee z v e) /\ collectLabele (subst_ee z v e) = collectLabele e.
Proof.
  intros e z v HS. induction HS as [|i e r HS [IH HR]]; simpl.
  - split; constructor.
  - split; [constructor; exact IH|now rewrite HR].
Qed.

Lemma collect_subst_te : forall e X P,
  collectLabele (subst_te X P e) = collectLabele e.
Proof. intros e X P; induction e; simpl; congruence. Qed.

Lemma rt_subst_te : forall e X P, rt_expr e -> rt_expr (subst_te X P e).
Proof. intros e X P H. inversion H; simpl; constructor. Qed.

Lemma typing_subst_ee : forall E e T, typing E e T -> forall F G z U v,
  E = F ++ z ~ bind_typ U ++ G -> typing G v U -> expr v ->
  typing (F ++ G) (subst_ee z v e) T.
Proof.
  intros E e T H. induction H; intros F K z U v Heq Hv HV; subst; simpl.
  - constructor. exact (@wf_env_drop_typ F K z U H).
  - assert (HF := @wf_env_drop_typ F K z U H).
    destruct (x == z); subst.
    + assert (HT : bind_typ T = bind_typ U)
        by (eapply binds_mid_eq; eauto using wf_env_ok).
      inversion HT; subst. eapply typing_weaken_by; eauto using binds_app_3.
    + constructor; eauto using binds_remove_mid.
  - eapply typing_abs with (L := L \u {{z}}). intros x HX.
    assert (Hx : subst_ee z v (exp_fvar x) = exp_fvar x)
      by (simpl; destruct (x == z); [fsetdec|reflexivity]).
    pose proof (@subst_ee_open_rec e1 z v 0 (exp_fvar x) (proj1 (expr_scoped HV))) as HO.
    rewrite Hx in HO. unfold open_ee. rewrite <- HO.
    exact (H0 x ltac:(fsetdec) ((x,bind_typ V)::F) K z U v eq_refl Hv HV).
  - eauto using typing_app.
  - eapply typing_tabs with (L := L). intros X HX.
    unfold open_te. rewrite <- subst_ee_open_te_rec by exact (proj2 (expr_scoped HV)).
    exact (H0 X HX ((X,bind_sub V)::F) K z U v eq_refl Hv HV).
  - eapply typing_tapp; eauto. exact (@sub_drop_typ F K z U _ _ H0).
  - eapply typing_fold; eauto. exact (@sub_drop_typ F K z U _ _ H).
  - eapply typing_unfold; eauto. exact (@sub_drop_typ F K z U _ _ H0).
  - eapply typing_sub; eauto. exact (@sub_drop_typ F K z U _ _ H0).
  - eauto using typing_proj.
  - constructor. exact (@wf_env_drop_typ F K z U H).
  - destruct (spine_subst_ee z v (typing_spine H0 H2)) as [HS Hlabels].
    eapply typing_rcd_cons; eauto using spine_rt. now rewrite Hlabels.
Qed.

Lemma typing_subst_te : forall E e T, typing E e T -> forall F G X U P,
  E = F ++ X ~ bind_sub U ++ G -> sub G P U ->
  subst_tt X P U = U ->
  (forall Y b, binds Y b G -> subst_tb X P b = b) ->
  typing (map (subst_tb X P) F ++ G) (subst_te X P e) (subst_tt X P T).
Proof.
  intros E e T H. induction H; intros F K Z U P Heq HP HU HK; subst; simpl;
    assert (HS : scoped_tt 0 P) by eauto using WF_scoped, sub_WF_l.
  - constructor. eauto using wf_env_subst, sub_WF_l.
  - assert (Hne : Z <> x).
    { intro Heq. subst x.
      assert (Heq : bind_typ T = bind_sub U)
        by (eapply binds_mid_eq; eauto using wf_env_ok).
      discriminate. }
    constructor.
    + eauto using wf_env_subst, sub_WF_l.
    + exact (@binds_subst_env F K Z U P x (bind_typ T) Hne H0 HK).
  - eapply typing_abs with (L := L). intros x HX.
    unfold open_ee. change (typing
      (map (subst_tb Z P) ((x,bind_typ V)::F) ++ K)
      (open_ee_rec 0 (subst_te Z P (exp_fvar x)) (subst_te Z P e1)) (subst_tt Z P T1)).
    rewrite <- subst_te_open_ee_rec.
    exact (H0 x HX ((x,bind_typ V)::F) K Z U P eq_refl HP HU HK).
  - eauto using typing_app.
  - eapply typing_tabs with (L := L \u {{Z}}). intros X HX.
    assert (HX' : subst_tt Z P X = typ_fvar X).
    { simpl. destruct (X == Z); [fsetdec|reflexivity]. }
    unfold open_te, open_tt. rewrite <- HX' at 1 2.
    rewrite <- subst_te_open_rec, <- subst_tt_open_rec by assumption.
    exact (H0 X ltac:(fsetdec) ((X,bind_sub V)::F) K Z U P eq_refl HP HU HK).
  - unfold open_tt. rewrite subst_tt_open_rec by assumption.
    eapply typing_tapp; eauto.
    exact (@sub_subst F K Z U P _ _ H0 HP HU HK).
  - eapply typing_fold.
    + exact (@sub_subst F K Z U P _ _ H HP HU HK).
    + unfold open_tt in *. rewrite <- subst_tt_open_rec by assumption. eauto.
  - unfold open_tt. rewrite subst_tt_open_rec by assumption.
    eapply typing_unfold; eauto.
    exact (@sub_subst F K Z U P _ _ H0 HP HU HK).
  - eapply typing_sub; eauto. exact (@sub_subst F K Z U P _ _ H0 HP HU HK).
  - eapply typing_proj; eauto.
    rewrite <- !translate_subst.
    eapply translate_lookup_any; eassumption.
  - constructor. eauto using wf_env_subst, sub_WF_l.
  - eapply typing_rcd_cons; eauto using rt_subst_te.
    + inversion H1; simpl; constructor.
    + now rewrite collect_subst_te.
Qed.

Lemma sub_record_fields : forall E A B, sub E A B -> rt_type A -> rt_type B ->
  collectLabel B [<=] collectLabel A /\
  (forall i U V, Tlookup i A = Some U -> Tlookup i B = Some V -> sub E U V).
Proof.
  intros E A B H HA HB. inversion H; subst;
    try match goal with HR : rt_type _ |- _ => solve [inversion HR] end.
  auto.
Qed.

(* Replacing a closed type by a mutually subtyping type is compatible with
   all type constructors, including the invariant bounds of universals. *)
Inductive compatible (P Q : typ) : typ -> typ -> Prop :=
| compat_hole : compatible P Q P Q
| compat_nat : compatible P Q typ_nat typ_nat
| compat_top : compatible P Q typ_top typ_top
| compat_bvar : forall k, compatible P Q (typ_bvar k) (typ_bvar k)
| compat_fvar : forall X, compatible P Q (typ_fvar X) (typ_fvar X)
| compat_arrow : forall A A' B B', compatible P Q A A' -> compatible P Q B B' ->
    compatible P Q (typ_arrow A B) (typ_arrow A' B')
| compat_all : forall A A' B B', compatible P Q A A' -> compatible P Q B B' ->
    compatible P Q (typ_all A B) (typ_all A' B')
| compat_mu : forall A A', compatible P Q A A' -> compatible P Q (typ_mu A) (typ_mu A')
| compat_label : forall l A A', compatible P Q A A' ->
    compatible P Q (typ_label l A) (typ_label l A')
| compat_nil : compatible P Q typ_rcd_nil typ_rcd_nil
| compat_cons : forall i A A' B B', compatible P Q A A' -> compatible P Q B B' ->
    compatible P Q (typ_rcd_cons i A B) (typ_rcd_cons i A' B').

Lemma compatible_refl : forall P Q A, compatible P Q A A.
Proof. induction A; constructor; auto. Qed.

Lemma compatible_open_rec : forall P Q A B U V k,
  scoped_tt 0 P -> scoped_tt 0 Q ->
  compatible P Q A B -> compatible P Q U V ->
  compatible P Q (open_tt_rec k U A) (open_tt_rec k V B).
Proof.
  intros P Q A B U V k HP HQ HC HV. revert k.
  induction HC; intros j; simpl; try solve [constructor; auto].
  - rewrite !scoped_tt_open_id by eauto using scoped_tt_mono, Nat.le_0_l. constructor.
  - destruct (j === k); auto using compatible.
Qed.

Lemma compatible_open : forall P Q A B U V,
  scoped_tt 0 P -> scoped_tt 0 Q -> compatible P Q A B -> compatible P Q U V ->
  compatible P Q (open_tt A U) (open_tt B V).
Proof. unfold open_tt; eauto using compatible_open_rec. Qed.

Lemma compatible_sub : forall E P Q, sub E P Q -> sub E Q P ->
  forall A B F, compatible P Q A B ->
  (forall X b, binds X b E -> binds X b F) -> wf_env F ->
  WF F A -> WF F B -> sub F A B /\ sub F B A.
Proof.
  intros E P Q HPQ HQP.
  assert (HP : scoped_tt 0 P) by eauto using WF_scoped, sub_WF_l.
  assert (HQ : scoped_tt 0 Q) by eauto using WF_scoped, sub_WF_r.
  assert (Hmain : forall n A B F, sub_weight A = n -> compatible P Q A B ->
    (forall X b, binds X b E -> binds X b F) -> wf_env F ->
    WF F A -> WF F B -> sub F A B /\ sub F B A).
  2: { intros. eapply Hmain; eauto. }
  induction n using lt_wf_ind.
  intros A B F Hn HC HI HF HA HB. subst n.
  inversion HC; subst; try solve [split; eauto using sub_refl, sub_weaken_by].
  - inversion HA; inversion HB; subst.
    assert (Hdom : sub F A0 A' /\ sub F A' A0).
    { apply (H (sub_weight A0)); eauto; unfold sub_weight; simpl; lia. }
    assert (Hcod : sub F B0 B' /\ sub F B' B0).
    { apply (H (sub_weight B0)); eauto; unfold sub_weight; simpl; lia. }
    destruct Hdom, Hcod. split; constructor; auto.
  - inversion HA; inversion HB; subst.
    assert (Hdom : sub F A0 A' /\ sub F A' A0).
    { apply (H (sub_weight A0)); eauto; unfold sub_weight; simpl; lia. }
    destruct Hdom as [HAB HBA].
    split; eapply sa_all with (L := L \u L0 \u dom F); eauto;
      intros X HX;
      pose proof (H6 X ltac:(fsetdec)) as HAx;
      pose proof (H11 X ltac:(fsetdec)) as HBx;
      assert (Hrel : compatible P Q (open_tt B0 X) (open_tt B' X))
        by (eapply compatible_open; eauto using compatible_refl);
      pose proof (@weight_all_open A0 B0 X) as HW;
      assert (HI' : forall b Y c, binds Y c E -> binds Y c (X ~ bind_sub b ++ F))
        by eauto using binds_cons_3.
    + assert (HF' : wf_env (X ~ bind_sub A' ++ F)) by (constructor; auto; fsetdec).
      exact (proj1 (H _ HW _ _ _ eq_refl Hrel (HI' _) HF'
        (@WF_change_bound nil F X A0 A' _ HAx) HBx)).
    + assert (HF' : wf_env (X ~ bind_sub A0 ++ F)) by (constructor; auto; fsetdec).
      exact (proj2 (H _ HW _ _ _ eq_refl Hrel (HI' _) HF'
        HAx (@WF_change_bound nil F X A' A0 _ HBx))).
  - inversion HA as [| | | | |L G C Hleft Hleft'| | |]; subst.
    inversion HB as [| | | | |L0 G C Hright Hright'| | |]; subst.
    assert (Hcomparison : forall X, X `notin` (L \u L0 \u dom F) ->
      let Aopen := open_tt A0 (typ_label X (open_tt A0 X)) in
      let Bopen := open_tt A' (typ_label X (open_tt A' X)) in
      sub (X ~ bind_sub typ_top ++ F) Aopen Bopen /\
      sub (X ~ bind_sub typ_top ++ F) Bopen Aopen).
    { intros X HX. simpl.
      pose proof (Hleft X ltac:(fsetdec)) as HAx.
      pose proof (@weight_rec_open _ A0 X HAx) as HW.
      assert (HCx : compatible P Q (open_tt A0 X) (open_tt A' X))
        by (eapply compatible_open; eauto using compatible_refl).
      eapply (H _ HW); [reflexivity| | | | |].
      - eapply compatible_open; eauto using compat_label.
      - eauto using binds_cons_3.
      - constructor; auto using WF_top; fsetdec.
      - apply Hleft'; fsetdec.
      - apply Hright'; fsetdec. }
    split; eapply sa_rec with (L := L \u L0 \u dom F); intros X HX;
      try solve [apply Hleft; fsetdec | apply Hright; fsetdec].
    + exact (proj1 (Hcomparison X HX)).
    + exact (proj2 (Hcomparison X HX)).
  - inversion HA; inversion HB; subst.
    assert (Hbody : sub F A0 A' /\ sub F A' A0).
    { apply (H (sub_weight A0)); eauto; unfold sub_weight; simpl; lia. }
    destruct Hbody. split; constructor; auto.
  - inversion HA; inversion HB; subst.
    assert (Hhead : sub F A0 A' /\ sub F A' A0).
    { apply (H (sub_weight A0)); eauto; unfold sub_weight; simpl; lia. }
    assert (Htail : sub F B0 B' /\ sub F B' B0).
    { apply (H (sub_weight B0)); eauto; unfold sub_weight; simpl; lia. }
    destruct Hhead as [Hh Hh'], Htail as [Ht Ht'].
    destruct (sub_record_fields Ht ltac:(assumption) ltac:(assumption)) as [Hwidth Hfields].
    destruct (sub_record_fields Ht' ltac:(assumption) ltac:(assumption)) as [Hwidth' Hfields'].
    split; eapply sa_rcd; eauto using rt_type.
    all: try solve [simpl; fsetdec].
    all: intros j U V HU HV; simpl in *; destruct (i == j);
      [inversion HU; inversion HV; subst; assumption|eauto].
Qed.

Lemma sub_open_equiv : forall E A P Q,
  sub E P Q -> sub E Q P -> WF E (open_tt A P) -> WF E (open_tt A Q) ->
  sub E (open_tt A P) (open_tt A Q).
Proof.
  intros E A P Q HPQ HQP HA HB.
  assert (HC : compatible P Q (open_tt A P) (open_tt A Q)).
  { eapply compatible_open; eauto using compatible_refl, compat_hole, WF_scoped, sub_WF_l. }
  destruct (compatible_sub HPQ HQP HC (fun _ _ H => H) (sub_wf_env HPQ) HA HB); assumption.
Qed.

Definition typ_eq_dec : forall A B : typ, {A = B} + {A <> B}.
Proof. decide equality; first [apply Nat.eq_dec | match goal with |- {?a = ?b} + {_} => exact (a == b) end]. Defined.

Definition marker_ok (X : atom) (P Q : typ) (Y : atom) (A : typ) : Prop :=
  Y = X -> A = P \/ A = Q.

Definition marker_value (P U V A : typ) : typ :=
  if typ_eq_dec A P then U else V.

Definition marker_map (X : atom) (P U V : typ) (Y : atom) (A B : typ) : typ :=
  if Y == X then marker_value P U V A else typ_label Y B.

Lemma marker_map_hit : forall X P U V A B,
  marker_map X P U V X A B = marker_value P U V A.
Proof. intros. unfold marker_map. destruct (X == X); congruence. Qed.

Lemma marker_map_miss : forall X Y P U V A B, Y <> X ->
  marker_map X P U V Y A B = typ_label Y B.
Proof. intros. unfold marker_map. destruct (Y == X); congruence. Qed.

Lemma marker_good_fresh : forall A X P Q,
  X `notin` fl_tt A -> acceptable (marker_ok X P Q) A.
Proof.
  induction A; simpl; intros X P Q H; try exact I;
    try solve [split; [apply IHA1|apply IHA2]; fsetdec].
  - auto.
  - split; [unfold marker_ok; fsetdec|apply IHA; fsetdec].
Qed.

Lemma marker_map_fresh : forall A X P U V,
  X `notin` fl_tt A -> translate typ_fvar (marker_map X P U V) A = A.
Proof.
  induction A; simpl; intros X P U V H; try reflexivity;
    try solve [f_equal; [apply IHA1|apply IHA2]; fsetdec].
  - f_equal. auto.
  - unfold marker_map. destruct (a == X); [fsetdec|].
    f_equal. apply IHA. fsetdec.
Qed.

Lemma marker_payload_scoped : forall X P Q A,
  scoped_tt 0 P -> scoped_tt 0 Q -> marker_ok X P Q X A -> scoped_tt 0 A.
Proof. intros X P Q A HP HQ H. destruct (H eq_refl) as [-> | ->]; assumption. Qed.

Lemma marker_good_open_rec : forall A X P Q k W,
  scoped_tt 0 P -> scoped_tt 0 Q ->
  acceptable (marker_ok X P Q) A -> acceptable (marker_ok X P Q) W ->
  acceptable (marker_ok X P Q) (open_tt_rec k W A).
Proof.
  induction A; simpl; intros X P Q k W HP HQ HA HW; intuition eauto.
  - destruct (k === n); simpl; auto.
  - unfold marker_ok in *. intros ->.
    rewrite scoped_tt_open_id; [auto|].
    apply (@scoped_tt_mono A 0 k); [exact (@marker_payload_scoped X P Q A HP HQ H)|apply Nat.le_0_l].
Qed.

Lemma marker_map_open_rec : forall A X P Q U V k W,
  scoped_tt 0 P -> scoped_tt 0 Q -> scoped_tt 0 U -> scoped_tt 0 V ->
  acceptable (marker_ok X P Q) A ->
  translate typ_fvar (marker_map X P U V) (open_tt_rec k W A) =
  open_tt_rec k (translate typ_fvar (marker_map X P U V) W)
    (translate typ_fvar (marker_map X P U V) A).
Proof.
  induction A; simpl; intros X P Q U V k W HP HQ HU HV HA;
    try solve [intuition (f_equal; eauto)].
  - destruct (k === n); reflexivity.
  - destruct (a == X) as [-> | Hneq].
    + rewrite !marker_map_hit. destruct HA as [Hok HA].
      assert (HC : scoped_tt k A).
      { apply (@scoped_tt_mono A 0 k); [exact (@marker_payload_scoped X P Q A HP HQ Hok)|apply Nat.le_0_l]. }
      rewrite (@scoped_tt_open_id _ _ _ HC).
      symmetry. apply scoped_tt_open_id. unfold marker_value.
      destruct (typ_eq_dec A P); eauto using scoped_tt_mono, Nat.le_0_l.
    + rewrite !marker_map_miss by assumption. simpl.
      intuition (f_equal; eauto).
Qed.

Lemma wf_marker_env : forall X, wf_env (X ~ bind_sub typ_top).
Proof. intros. constructor; [constructor|constructor|fsetdec]. Qed.

Lemma sub_marker_map : forall X P Q U V A B,
  WF (X ~ bind_sub typ_top) P -> WF (X ~ bind_sub typ_top) Q ->
  WF (X ~ bind_sub typ_top) U -> WF (X ~ bind_sub typ_top) V ->
  (forall C D, (C = P \/ C = Q) -> (D = P \/ D = Q) ->
    sub (X ~ bind_sub typ_top) C D ->
    sub (X ~ bind_sub typ_top) (marker_value P U V C) (marker_value P U V D)) ->
  sub (X ~ bind_sub typ_top) A B ->
  acceptable (marker_ok X P Q) A -> acceptable (marker_ok X P Q) B ->
  sub (X ~ bind_sub typ_top)
    (translate typ_fvar (marker_map X P U V) A)
    (translate typ_fvar (marker_map X P U V) B).
Proof.
  intros X P Q U V A B HP HQ HU HV Hconvert HS HA HB.
  refine (@translate_sub typ_fvar (marker_map X P U V) (marker_ok X P Q)
    {{X}} _ _ _ _ _ (X ~ bind_sub typ_top) (X ~ bind_sub typ_top) _ _ _ _ _ HS
    (X ~ bind_sub typ_top) (fun _ _ HB => HB) (fun _ _ HB => HB)
    (wf_marker_env X) _ _ HA HB).
  - intros C D. exact (@marker_good_open_rec C X P Q 0 D (WF_scoped HP) (WF_scoped HQ)).
  - intros C D. exact (@marker_map_open_rec C X P Q U V 0 D
      (WF_scoped HP) (WF_scoped HQ) (WF_scoped HU) (WF_scoped HV)).
  - reflexivity.
  - intros Y C D HY. unfold marker_map. destruct (Y == X); [fsetdec|reflexivity].
  - unfold marker_ok; intros; fsetdec.
  - intros F Y C HI HF HC HW.
    unfold marker_map. destruct (Y == X); [|eauto using WF_label].
    unfold marker_value. destruct (typ_eq_dec C P); eauto using WF_same.
  - intros E F Y C D HE HF HW HC HD HCD HM.
    unfold marker_map. destruct (Y == X) as [-> | Hneq]; [|eauto using sa_label].
    specialize (HC eq_refl). specialize (HD eq_refl).
    eapply sub_weaken_by; [|exact HW|exact HF].
    apply Hconvert; auto.
    eapply sub_strengthen; [exact HCD|exact HE|apply wf_marker_env| |];
      destruct HC, HD; subst; assumption.
  - intros Y C Hbind. apply binds_cons_1 in Hbind as [[-> Heq]|Hbind]; [|inversion Hbind].
    inversion Heq; subst. simpl. apply sa_top; auto using wf_marker_env.
    eapply WF_var; eauto using binds_cons_2.
  - intros Y C Hbind. apply binds_cons_1 in Hbind as [[_ Heq]|Hbind]; [|inversion Hbind].
    inversion Heq; simpl; auto.
Qed.

Lemma marker_open_image : forall A X P Q U V W,
  X `notin` fl_tt A -> scoped_tt 0 P -> scoped_tt 0 Q ->
  scoped_tt 0 U -> scoped_tt 0 V ->
  translate typ_fvar (marker_map X P U V) (open_tt A (typ_label X W)) =
  open_tt A (marker_value P U V W).
Proof.
  intros A X P Q U V W Hfresh HP HQ HU HV. unfold open_tt at 1.
  rewrite (@marker_map_open_rec A X P Q U V 0 _ HP HQ HU HV) by auto using marker_good_fresh.
  rewrite (@marker_map_fresh A X P U V Hfresh).
  simpl. now rewrite marker_map_hit.
Qed.

Lemma marked_open_good : forall X P Q A,
  X `notin` fl_tt A -> scoped_tt 0 P -> scoped_tt 0 Q ->
  (open_tt A X = P \/ open_tt A X = Q) ->
  acceptable (marker_ok X P Q) (open_tt A (typ_label X (open_tt A X))).
Proof.
  intros X P Q A HF HP HQ Heq.
  apply (@marker_good_open_rec A X P Q 0 _ HP HQ); [auto using marker_good_fresh|].
  split; [intros _; exact Heq|].
  apply (@marker_good_open_rec A X P Q 0 _ HP HQ); [auto using marker_good_fresh|exact I].
Qed.

(* Erasing the fresh recursive labels recovers comparison of the bodies
   opened with an ordinary type variable. *)
Lemma marker_strip : forall X A B,
  X `notin` fl_tt A -> X `notin` fl_tt B ->
  WF (X ~ bind_sub typ_top) (open_tt A X) ->
  WF (X ~ bind_sub typ_top) (open_tt B X) ->
  sub (X ~ bind_sub typ_top)
    (open_tt A (typ_label X (open_tt A X)))
    (open_tt B (typ_label X (open_tt B X))) ->
  sub (X ~ bind_sub typ_top) (open_tt A X) (open_tt B X).
Proof.
  intros X A B HAf HBf HA HB HS.
  assert (HX : WF (X ~ bind_sub typ_top) (typ_fvar X))
    by eauto using WF_var, binds_cons_2.
  assert (HP := WF_scoped HA). assert (HQ := WF_scoped HB).
  pose (P := open_tt A X). pose (Q := open_tt B X).
  pose proof (@sub_marker_map X P Q X X (open_tt A (typ_label X P))
    (open_tt B (typ_label X Q)) HA HB HX HX) as HM.
  assert (HV : forall W, marker_value P X X W = typ_fvar X)
    by (intro W; unfold marker_value; destruct (typ_eq_dec W P); reflexivity).
  specialize (HM ltac:(intros; rewrite !HV; auto using sub_refl, wf_marker_env) HS).
  specialize (HM (@marked_open_good X P Q A HAf HP HQ (or_introl eq_refl))
                 (@marked_open_good X P Q B HBf HP HQ (or_intror eq_refl))).
  rewrite !(@marker_open_image _ X P Q X X) in HM by eauto using WF_scoped.
  now rewrite !HV in HM.
Qed.

Lemma roll_equivalent_bodies : forall X A B,
  X `notin` fv_tt A -> X `notin` fv_tt B ->
  sub (X ~ bind_sub typ_top) (open_tt A X) (open_tt B X) ->
  sub (X ~ bind_sub typ_top) (open_tt B X) (open_tt A X) ->
  sub nil (typ_mu A) (typ_mu B).
Proof.
  intros X A B HAf HBf HAB HBA.
  assert (Htop : forall Y : atom, sub (Y ~ bind_sub typ_top) Y typ_top).
  { intros. apply sa_top; auto using wf_marker_env. eapply WF_var; eauto using binds_cons_2. }
  assert (HA : forall Y : atom, WF (Y ~ bind_sub typ_top) (open_tt A Y)).
  { intros. eapply sub_WF_l. eapply (@sub_open_single X A B typ_top); eauto. }
  assert (HB : forall Y : atom, WF (Y ~ bind_sub typ_top) (open_tt B Y)).
  { intros. eapply sub_WF_r. eapply (@sub_open_single X A B typ_top); eauto. }
  eapply sa_rec with (L := {}); [intros; apply HA|intros; apply HB|].
  intros Y HY.
  pose (C := typ_label Y (open_tt A Y)).
  pose (D := typ_label Y (open_tt B Y)).
  assert (HCD : sub (Y ~ bind_sub typ_top) C D).
  { unfold C, D. constructor. eapply (@sub_open_single X A B typ_top); eauto. }
  assert (HDC : sub (Y ~ bind_sub typ_top) D C).
  { unfold C, D. constructor. eapply (@sub_open_single X B A typ_top); eauto. }
  assert (HWF : forall W, WF (Y ~ bind_sub typ_top) W ->
                          WF (Y ~ bind_sub typ_top) (open_tt A W)).
  { intros. eapply (@WF_open_single X A _ typ_top); eauto using sub_WF_l, wf_marker_env. }
  change (sub (Y ~ bind_sub typ_top) (open_tt A C) (open_tt B D)).
  eapply sub_trans with (Q := open_tt A D).
  - eapply sub_open_equiv; eauto using sub_WF_l, sub_WF_r.
  - eapply (@sub_open_single X A B typ_top); eauto.
    apply sa_top; eauto using sub_WF_r, wf_marker_env.
Qed.

Lemma empty_sub_recursive : forall T A,
  sub nil T (typ_mu A) ->
  exists B L, T = typ_mu B /\
    (forall X, X `notin` L -> WF (X ~ bind_sub typ_top) (open_tt B X)) /\
    (forall X, X `notin` L -> WF (X ~ bind_sub typ_top) (open_tt A X)) /\
    (forall X, X `notin` L -> sub (X ~ bind_sub typ_top)
      (open_tt B (typ_label X (open_tt B X)))
      (open_tt A (typ_label X (open_tt A X)))).
Proof.
  intros T A H. inversion H; subst; eauto 8.
  - inversion H0.
  - match goal with HR : rt_type (typ_mu _) |- _ => inversion HR end.
Qed.

Lemma sub_unfold_chain : forall A B U V,
  sub nil (typ_mu A) U -> sub nil U V -> sub nil V (typ_mu B) ->
  sub nil (open_tt A U) (open_tt B V).
Proof.
  intros A B U V HAU HUV HVB.
  assert (HAB : sub nil (typ_mu A) (typ_mu B)) by eauto using sub_trans.
  destruct (empty_sub_recursive HAB) as [C [L [Heq [HA [HB Hmark]]]]].
  inversion Heq; subst C.
  fresh_atom X (L \u fv_tt A \u fv_tt B \u fl_tt A \u fl_tt B).
  assert (HXL : X `notin` L) by fsetdec.
  specialize (HA X HXL). specialize (HB X HXL). specialize (Hmark X HXL).
  assert (Hfaf : X `notin` fv_tt A) by fsetdec.
  assert (Hfbf : X `notin` fv_tt B) by fsetdec.
  assert (Hfal : X `notin` fl_tt A) by fsetdec.
  assert (Hfbl : X `notin` fl_tt B) by fsetdec.
  pose (P := open_tt A X). pose (Q := open_tt B X).
  assert (Hnaked : sub (X ~ bind_sub typ_top) P Q) by eauto using marker_strip.
  (* A comparison of the markers in reverse order gives the reverse
     comparison of their bodies. Rolling it yields the reverse subtyping
     between the fold and unfold annotations. *)
  assert (Hreverse : sub (X ~ bind_sub typ_top) Q P -> sub nil V U).
  { intros. eapply sub_trans; [exact HVB|].
    eapply sub_trans; [eapply (@roll_equivalent_bodies X B A); eauto|exact HAU]. }
  assert (HU : WF nil U) by eauto using sub_WF_l.
  assert (HV : WF nil V) by eauto using sub_WF_r.
  assert (HWP := WF_scoped HA). assert (HWQ := WF_scoped HB).
  assert (HWU := WF_scoped HU). assert (HWV := WF_scoped HV).
  assert (Hsub : forall C D, (C = P \/ C = Q) -> (D = P \/ D = Q) ->
    sub (X ~ bind_sub typ_top) C D ->
    sub (X ~ bind_sub typ_top) (marker_value P U V C) (marker_value P U V D)).
  { intros C D [-> | ->] [-> | ->] HCD; unfold marker_value;
      destruct (typ_eq_dec P P); try contradiction;
      destruct (typ_eq_dec Q P);
      apply (@sub_push nil X (bind_sub typ_top)); [..|apply wf_marker_env].
    all: try apply wf_marker_env.
    all: first [exact HUV | exact (Hreverse HCD) | apply sub_refl; [assumption|constructor]]. }
  pose proof (@sub_marker_map X P Q U V _ _ HA HB
    (@WF_push nil X (bind_sub typ_top) U HU) (@WF_push nil X (bind_sub typ_top) V HV)
    Hsub Hmark
    (@marked_open_good X P Q A Hfal HWP HWQ (or_introl eq_refl))
    (@marked_open_good X P Q B Hfbl HWP HWQ (or_intror eq_refl))) as HM.
  rewrite !(@marker_open_image _ X P Q U V) in HM by assumption.
  unfold marker_value in HM. fold P Q in HM. destruct (typ_eq_dec P P); [|congruence].
  assert (HAU' : WF nil (open_tt A U)).
  { eapply (@WF_open_single X A _ typ_top); auto using wf_env_empty. }
  assert (HB' : forall W, WF nil W -> WF nil (open_tt B W)).
  { intros. eapply (@WF_open_single X B _ typ_top); auto using wf_env_empty. }
  destruct (typ_eq_dec Q P) as [HeqQP|Hne].
  - eapply sub_trans with (Q := open_tt B U).
    + apply (sub_strengthen HM); [intros ? ? HH; inversion HH|constructor|exact HAU'|auto].
    + apply sub_open_equiv; auto.
      apply Hreverse. rewrite HeqQP. apply sub_refl; [exact HA|apply wf_marker_env].
  - apply (sub_strengthen HM); [intros ? ? HH; inversion HH|constructor|exact HAU'|auto].
Qed.

Lemma empty_sub_arrow : forall T A B, sub nil T (typ_arrow A B) ->
  exists C D, T = typ_arrow C D /\ sub nil A C /\ sub nil D B.
Proof.
  intros T A B H. inversion H; subst; eauto 8.
  - inversion H0.
  - match goal with HR : rt_type (typ_arrow _ _) |- _ => inversion HR end.
Qed.

Lemma empty_sub_all : forall T A B, sub nil T (typ_all A B) ->
  exists C D L, T = typ_all C D /\ sub nil A C /\
    (forall X, X `notin` L -> sub (X ~ bind_sub A) (open_tt D X) (open_tt B X)).
Proof.
  intros T A B H. inversion H; subst; eauto 8.
  - inversion H0.
  - match goal with HR : rt_type (typ_all _ _) |- _ => inversion HR end.
Qed.

Lemma apply_typed_abs : forall E f T, typing E f T ->
  forall V body Arg Res v, E = nil -> f = exp_abs V body -> T = typ_arrow Arg Res ->
  typing nil v Arg -> expr v -> typing nil (open_ee body v) Res.
Proof.
  intros E f T H. induction H; intros V' body Arg Res v HE Hf HT Hv HV;
    lazymatch type of HE with ?G = _ => subst G end; try discriminate.
  - inversion Hf; inversion HT; subst.
    fresh_atom x (L \u fv_ee body).
    pose proof (H x ltac:(fsetdec)) as HT'.
    pose proof (@typing_subst_ee _ _ _ HT' nil nil x Arg v eq_refl Hv HV) as HF.
    simpl in HF. rewrite subst_ee_intro in HF by (auto; fsetdec).
    exact HF.
  - subst e T.
    destruct (empty_sub_arrow H0) as [C [D [-> [Hdom Hcod]]]].
    eapply typing_sub; [|exact Hcod].
    eapply IHtyping; eauto using typing_sub.
Qed.

Lemma apply_typed_tabs : forall E f T, typing E f T ->
  forall V body Arg Res P, E = nil -> f = exp_tabs V body -> T = typ_all Arg Res ->
  sub nil P Arg -> typing nil (open_te body P) (open_tt Res P).
Proof.
  intros E f T H. induction H; intros V' body Arg Res P HE Hf HT HP;
    lazymatch type of HE with ?G = _ => subst G end; try discriminate.
  - inversion Hf; inversion HT; subst.
    fresh_atom X (L \u fv_te body \u fv_tt Res \u fv_tt Arg).
    pose proof (H X ltac:(fsetdec)) as HT'.
    pose proof (@typing_subst_te _ _ _ HT' nil nil X Arg P eq_refl HP
      (@subst_tt_fresh Arg X P ltac:(fsetdec)) ltac:(intros ? ? Hnil; inversion Hnil)) as HF.
    simpl in HF.
    rewrite subst_te_intro, subst_tt_intro in HF
      by (eauto using WF_scoped, sub_WF_l; fsetdec).
    exact HF.
  - subst e T.
    destruct (empty_sub_all H0) as [C [D [L [-> [Hdom Hcod]]]]].
    eapply typing_sub with (S := open_tt D P).
    + eapply IHtyping; eauto using sub_trans.
    + fresh_atom X (L \u fv_tt D \u fv_tt Res \u fv_tt Arg).
      eapply (@sub_open_single X D Res Arg P nil); eauto;
        try solve [apply Hcod; fsetdec | apply subst_tt_fresh; fsetdec | fsetdec].
Qed.

Lemma invert_typed_fold : forall E f T, typing E f T ->
  forall U e, E = nil -> f = exp_fold U e ->
  exists A, sub nil (typ_mu A) U /\ typing nil e (open_tt A U) /\ sub nil U T.
Proof.
  intros E f T H. induction H; intros U b HE Hf; lazymatch type of HE with ?G = _ => subst G end; try discriminate.
  - inversion Hf; subst. eauto 8 using sub_refl, sub_WF_r, sub_wf_env.
  - subst e.
    destruct (IHtyping U b eq_refl eq_refl) as [A [HA [Hb HT]]].
    eauto 8 using sub_trans.
Qed.

Lemma lookup_rt : forall A i B, Tlookup i A = Some B -> rt_type A.
Proof. destruct A; simpl; try discriminate; constructor. Qed.

Lemma empty_sub_record : forall A B,
  sub nil A B -> rt_type B -> rt_type A.
Proof.
  intros A B H HB. inversion H; subst; auto;
    try match goal with HR : rt_type _ |- _ => solve [inversion HR] end.
  inversion H0.
Qed.

Lemma typed_record_lookup : forall E e T, typing E e T ->
  forall i v U, E = nil -> tlookup i e = Some v -> Tlookup i T = Some U ->
  typing nil v U.
Proof.
  intros E e T H. induction H; intros j v U HE Heq HT; lazymatch type of HE with ?G = _ => subst G end; simpl in Heq;
    try discriminate.
  - assert (HT' : rt_type T) by eauto using lookup_rt.
    assert (HS : rt_type S) by eauto using empty_sub_record.
    destruct (sub_record_fields H0 HS HT') as [Hsubset Hfields].
    assert (Hin : j `in` collectLabel S).
    { apply Hsubset, record_lookup_labels. eauto. }
    apply record_lookup_labels in Hin as [V HV].
    eapply typing_sub; eauto.
  - simpl in HT. destruct (i == j).
    + inversion Heq; inversion HT; subst; assumption.
    + eauto.
Qed.

Lemma step_record_spine : forall e e', step e e' -> record_spine e ->
  record_spine e' /\ collectLabele e' = collectLabele e.
Proof.
  intros e e' HS. induction HS; intros HR; inversion HR; subst; simpl.
  - split; auto using record_spine.
  - destruct (IHHS H1) as [Hspine Hlabels]. split; auto using record_spine.
    now rewrite Hlabels.
Qed.

Theorem preservation : forall e e' T,
    typing nil e T ->
    step e e' ->
    typing nil e' T.
Proof.
  intros e e' T HT. generalize dependent e'.
  remember nil as E eqn:HE in HT.
  induction HT; intros e' HS; lazymatch type of HE with ?G = _ => subst G end;
    try solve [inversion HS; subst; eauto using typing_app, typing_tapp, typing_fold,
                typing_unfold, typing_proj, typing_rcd_cons].
  - inversion HS; subst; eauto using typing_app, apply_typed_abs, value_expr.
  - inversion HS; subst; eauto using typing_tapp, apply_typed_tabs.
  - inversion HS; subst; eauto using typing_unfold.
    match goal with
    | HF : typing nil (exp_fold ?U ?v) ?S |- _ =>
        destruct (@invert_typed_fold _ _ _ HF U v eq_refl eq_refl) as [B [HB [Hv HUS]]]
    end.
    eapply typing_sub; [exact Hv|].
    eapply sub_unfold_chain; eassumption.
  - eauto using typing_sub.
  - inversion HS; subst; eauto using typing_proj, typed_record_lookup.
  - inversion HS; subst; eauto using typing_rcd_cons.
    match goal with
    | HTail : typing nil ?r ?R, HR : rt_expr ?r, Hstep : step ?r ?r' |- _ =>
        destruct (step_record_spine Hstep (typing_spine HTail HR)) as [Hspine Hlabels]
    end.
    eapply typing_rcd_cons; eauto using spine_rt. now rewrite Hlabels.
Qed.
