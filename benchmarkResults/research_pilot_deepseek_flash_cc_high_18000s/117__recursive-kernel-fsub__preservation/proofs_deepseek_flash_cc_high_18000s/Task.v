Require Import Rules.

Set Implicit Arguments.

Require Import Metalib.Metatheory.

Require Import Program.Equality.
Require Import Lia.

Lemma subst_tt_fvar_eq : forall X U, subst_tt X U (typ_fvar X) = U.
Proof. intros. simpl. destruct (X == X); [reflexivity|contradiction]. Qed.

Lemma subst_tt_fvar_neq : forall X Y U, X <> Y -> subst_tt X U (typ_fvar Y) = typ_fvar Y.
Proof. intros. simpl. destruct (Y == X) as [E|E]; [exfalso; apply H; symmetry; exact E | reflexivity]. Qed.

Lemma subst_tt_open_tt_rec_diff : forall X U K Y T,
  X <> Y -> X \notin fv_tt T ->
  subst_tt X U (open_tt_rec K (typ_fvar Y) T) = open_tt_rec K (typ_fvar Y) (subst_tt X U T).
Proof.
  intros X U K Y T Hneq Hfv.
  generalize dependent K.
  induction T; intros K; simpl in *.
  - reflexivity.
  - reflexivity.
  - (* bvar *) destruct (K === n); [ apply subst_tt_fvar_neq; auto | reflexivity ].
  - (* fvar a: Hfv : a \notin {{X}}? actually fv_tt (fvar a) = {{a}}; H : X \notin {{a}} *)
    apply notin_singleton_1 in Hfv. simpl. destruct (a == X) as [E|E].
    + exfalso. exact (Hfv E).
    + reflexivity.
  - (* arrow *) apply notin_union_1 in Hfv as H1. apply notin_union_2 in Hfv as H2.
    rewrite IHT1, IHT2; auto.
  - (* all *) apply notin_union_1 in Hfv as H1. apply notin_union_2 in Hfv as H2.
    rewrite IHT1, IHT2; auto.
  - (* mu *) rewrite IHT; auto.
  - (* label *) rewrite IHT; auto.
  - (* rcd_nil *) reflexivity.
  - (* rcd_cons *) apply notin_union_1 in Hfv as H1. apply notin_union_2 in Hfv as H2.
    rewrite IHT1, IHT2; auto.
Qed.

Lemma subst_tt_open_tt_rec_same : forall X U K T,
  X \notin fv_tt T ->
  subst_tt X U (open_tt_rec K (typ_fvar X) T) = open_tt_rec K U T.
Proof.
  intros X U K T Hfv.
  generalize dependent K.
  induction T; intros K; simpl in *.
  - reflexivity.
  - reflexivity.
  - (* bvar *) destruct (K === n).
    + simpl. destruct (X == X) as [E|E]; [reflexivity|contradiction].
    + reflexivity.
  - (* fvar a *) apply notin_singleton_1 in Hfv. simpl. destruct (a == X) as [E|E].
    + exfalso. exact (Hfv E).
    + reflexivity.
  - apply notin_union_1 in Hfv as H1. apply notin_union_2 in Hfv as H2.
    rewrite IHT1, IHT2; auto.
  - apply notin_union_1 in Hfv as H1. apply notin_union_2 in Hfv as H2.
    rewrite IHT1, IHT2; auto.
  - rewrite IHT; auto.
  - rewrite IHT; auto.
  - reflexivity.
  - apply notin_union_1 in Hfv as H1. apply notin_union_2 in Hfv as H2.
    rewrite IHT1, IHT2; auto.
Qed.

(* wf_env facts *)
Lemma wf_env_sub_inv : forall E X T,
  wf_env (X ~ bind_sub T ++ E) -> wf_env E /\ WF E T /\ X \notin dom E.
Proof. intros E X T H. inversion H; subst; auto. Qed.

Lemma wf_env_typ_inv : forall E x T,
  wf_env (x ~ bind_typ T ++ E) -> wf_env E /\ WF E T /\ x \notin dom E.
Proof. intros E x T H. inversion H; subst; auto. Qed.

Lemma typing_wf_env : forall E e T, typing E e T -> wf_env E.
Proof.
  intros E e T H. induction H.
  - assumption.
  - assumption.
  - destruct (atom_fresh L) as [x Hx]. pose proof (H0 x Hx) as Hw. apply wf_env_typ_inv in Hw. tauto.
  - assumption.
  - destruct (atom_fresh L) as [X HX]. pose proof (H0 X HX) as Hw. apply wf_env_sub_inv in Hw. tauto.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

Lemma wf_env_uniq : forall E, wf_env E -> uniq E.
Proof. intros E H. induction H; constructor; assumption. Qed.

Lemma binds_sub_cons_incl : forall (X : atom) (T : typ) E E',
  (forall Z V, binds Z (bind_sub V) E -> exists V', binds Z (bind_sub V') E') ->
  forall Z V, binds Z (bind_sub V) (X ~ bind_sub T ++ E) ->
    exists V', binds Z (bind_sub V') (X ~ bind_sub T ++ E').
Proof.
  intros X T E E' Hinc Z V Hb.
  apply binds_cons_1 in Hb as [[Heq Hveq]|Hb].
  - subst. exists T. simpl. left. reflexivity.
  - destruct (Hinc Z V Hb) as [V' HV']. exists V'. simpl. right. exact HV'.
Qed.

Lemma WF_binds_irrel : forall E T, WF E T ->
  forall E', (forall Z V, binds Z (bind_sub V) E -> exists V', binds Z (bind_sub V') E') -> WF E' T.
Proof.
  intros E T H. induction H; intros E' Hinc.
  - apply WF_top.
  - apply WF_nat.
  - destruct (Hinc X U H) as [U' HU']. apply WF_var with U'; auto.
  - apply WF_arrow; auto.
  - apply WF_all with (L := L).
    + auto.
    + intros X HX. apply H1; auto. apply binds_sub_cons_incl; auto.
  - apply WF_rec with (L := L).
    + intros X HX. apply H0; auto. apply binds_sub_cons_incl; auto.
    + intros X HX. apply H2; auto. apply binds_sub_cons_incl; auto.
  - apply WF_label; auto.
  - apply WF_rcd_nil.
  - apply WF_rcd_cons; auto.
Qed.


Lemma binds_sub_head_change : forall (X : atom) (T1 T2 : typ) E Z V,
  binds Z (bind_sub V) (X ~ bind_sub T1 ++ E) ->
  exists V', binds Z (bind_sub V') (X ~ bind_sub T2 ++ E).
Proof.
  intros X T1 T2 E Z V Hb.
  apply binds_cons_1 in Hb as [[Heq Hveq]|Hb].
  - subst. exists T2. simpl. left. reflexivity.
  - exists V. simpl. right. exact Hb.
Qed.

Lemma sub_wf : forall E A B, sub E A B -> WF E A /\ WF E B.
Proof.
  intros E A B H. induction H.
  - split; apply WF_nat.
  - split; assumption.
  - split; [assumption|apply WF_top].
  - split.
    + apply WF_var with U; tauto.
    + tauto.
  - split; apply WF_arrow; tauto.
  - split.
    + apply WF_all with (L := L).
      * tauto.
      * intros X HX.
        eapply WF_binds_irrel.
        -- destruct (H2 X HX) as [Hl _]. exact Hl.
        -- intros Z V' Hb. eapply binds_sub_head_change; eauto.
    + apply WF_all with (L := L).
      * tauto.
      * intros X HX.
        destruct (H2 X HX) as [_ Hr]. exact Hr.
  - split.
    + apply WF_rec with (L := L).
      * exact H.
      * intros X HX.
        destruct (H2 X HX) as [Hl _]. exact Hl.
    + apply WF_rec with (L := L).
      * exact H0.
      * intros X HX.
        destruct (H2 X HX) as [_ Hr]. exact Hr.
  - split; apply WF_label; tauto.
  - split; assumption.
Qed.


(* ============================================================ *)
(* Part 4: reflexivity and weakening of subtyping               *)
(* ============================================================ *)

Lemma sub_refl_strong : forall E T, WF E T -> wf_env E ->
  sub E T T /\ (rt_type T -> forall l t, Tlookup l T = Some t -> sub E t t).
Proof.
  intros E T Hwf. induction Hwf as
    [ E
    | E
    | U E X b
    | E A B w0 IH0 w1 IH1
    | L E T1 T2 w0 IH0 wbody IHbody
    | L E A w0 IH0 w1 IH1
    | E A X w0 IH0
    | E
    | E i T1 T2 w0 IH0 w1 IH1 r n ];
    intros Hwe.
  - split.
    + apply sa_top; [assumption|apply WF_top].
    + intros Hrt; inversion Hrt.
  - split.
    + apply sa_nat; assumption.
    + intros Hrt; inversion Hrt.
  - split.
    + apply sa_fvar; [assumption|apply WF_var with U; assumption].
    + intros Hrt; inversion Hrt.
  - split.
    + apply sa_arrow; [apply (proj1 (IH0 Hwe)) | apply (proj1 (IH1 Hwe))].
    + intros Hrt; inversion Hrt.
  - split.
    + apply sa_all with (L := L \u dom E).
      * apply (proj1 (IH0 Hwe)).
      * apply (proj1 (IH0 Hwe)).
      * intros X HX.
        assert (HXL : X \notin L) by (exact (notin_union_1 X L (dom E) HX)).
        assert (HXd : X \notin dom E) by (exact (notin_union_2 X L (dom E) HX)).
        pose proof (wf_env_sub E X T1 Hwe w0 HXd) as Hext.
        apply (proj1 (IHbody X HXL Hext)).
    + intros Hrt; inversion Hrt.
  - split.
    + apply sa_rec with (L := L \u dom E).
      * intros X HX. apply w0. exact (notin_union_1 X L (dom E) HX).
      * intros X HX. apply w0. exact (notin_union_1 X L (dom E) HX).
      * intros X HX.
        assert (HXL : X \notin L) by (exact (notin_union_1 X L (dom E) HX)).
        assert (HXd : X \notin dom E) by (exact (notin_union_2 X L (dom E) HX)).
        pose proof (wf_env_sub E X typ_top Hwe (WF_top E) HXd) as Hext.
        apply (proj1 (IH1 X HXL Hext)).
    + intros Hrt; inversion Hrt.
  - split.
    + apply sa_label. apply (proj1 (IH0 Hwe)).
    + intros Hrt; inversion Hrt.
  - split.
    + apply sa_rcd with (A1 := typ_rcd_nil) (A2 := typ_rcd_nil).
      * assumption. * constructor. * constructor. * simpl; fsetdec.
      * apply WF_rcd_nil. * apply WF_rcd_nil.
      * intros i0 t1 t2 H1 H2. simpl in H1. discriminate.
    + intros Hrt l t Hlu. simpl in Hlu. discriminate.
  - split.
    + assert (Hf : forall l t, Tlookup l (typ_rcd_cons i T1 T2) = Some t -> sub E t t).
      { intros l t Hlu. simpl in Hlu. destruct (i == l) as [Eq|Ne].
        - inversion Hlu; subst. apply (proj1 (IH0 Hwe)).
        - exact (proj2 (IH1 Hwe) r l t Hlu). }
      apply sa_rcd with (A1 := typ_rcd_cons i T1 T2) (A2 := typ_rcd_cons i T1 T2).
      * assumption. * constructor. * constructor. * simpl; fsetdec.
      * apply WF_rcd_cons; assumption.
      * apply WF_rcd_cons; assumption.
      * intros l t1 t2 H1 H2. assert (t1 = t2) as Heq by congruence. subst t2. apply (Hf l t1 H1).
    + intros Hrt l t Hlu.
      simpl in Hlu. destruct (i == l) as [Eq|Ne].
      * inversion Hlu; subst. apply (proj1 (IH0 Hwe)).
      * exact (proj2 (IH1 Hwe) r l t Hlu).
Qed.

Lemma sub_refl : forall E T, wf_env E -> WF E T -> sub E T T.
Proof. intros. apply (proj1 (sub_refl_strong H0 H)). Qed.


(* ============================================================ *)
(* Part 5: weakening of subtyping under a binding inclusion     *)
(* ============================================================ *)

Lemma binds_sub_incl_cons_any : forall (X : atom) (b : binding) E Z V,
  binds Z (bind_sub V) E -> binds Z (bind_sub V) (X ~ b ++ E).
Proof. intros. apply binds_cons. exact H. Qed.

Lemma binds_sub_cons_incl_same : forall (X : atom) (T : typ) E E',
  (forall Z V, binds Z (bind_sub V) E -> binds Z (bind_sub V) E') ->
  forall Z V, binds Z (bind_sub V) (X ~ bind_sub T ++ E) ->
              binds Z (bind_sub V) (X ~ bind_sub T ++ E').
Proof.
  intros X T E E' Hinc Z V Hb.
  apply binds_cons_1 in Hb as [[Heq Hveq]|Ht].
  - subst Z. injection Hveq as HVT. subst V. simpl. left. reflexivity.
  - simpl. right. apply Hinc. exact Ht.
Qed.
Arguments binds_sub_cons_incl_same [X] [T] [E] [E'] _ Z V _.

Lemma inc_to_exists : forall E E',
  (forall Z V, binds Z (bind_sub V) E -> binds Z (bind_sub V) E') ->
  forall Z V, binds Z (bind_sub V) E -> exists V', binds Z (bind_sub V') E'.
Proof. intros. exists V. auto. Qed.

Lemma sub_weaken_binds : forall E A B, sub E A B ->
  forall E', wf_env E' ->
    (forall Z V, binds Z (bind_sub V) E -> binds Z (bind_sub V) E') ->
    sub E' A B.
Proof.
  intros E A B H. induction H as
    [ E0 Hwe0
    | E0 X Hwe0 Hwf0
    | E0 A0 Hwe0 Hwf0
    | U E0 T X Hb Hsub IHsub
    | E0 A1 A2 B1 B2 h1 IH1 h2 IH2
    | L E0 S1 S2 T1 T2 h12 IH12 h21 IH21 hbody IHbody
    | L A1 A2 E0 w1 w2 hbody IHbody
    | E0 X A0 B0 h1 IH1
    | A1 A2 E0 Hwe0 Hrt1 Hrt2 HsubL Hwf1 Hwf2 hpt IHpt ];
    intros E' Hwe' Hinc.
  - apply sa_nat; assumption.
  - apply sa_fvar; [assumption|].
    apply (WF_binds_irrel Hwf0 E' (fun Z V Hb => ex_intro (fun V' => binds Z (bind_sub V') E') V (Hinc Z V Hb))).
  - apply sa_top; [assumption|].
    apply (WF_binds_irrel Hwf0 E' (fun Z V Hb => ex_intro (fun V' => binds Z (bind_sub V') E') V (Hinc Z V Hb))).
  - eapply sa_trans_tvar.
    + apply Hinc. exact Hb.
    + apply IHsub; assumption.
  - apply sa_arrow; [apply IH1; assumption | apply IH2; assumption].
  - apply sa_all with (L := L \u dom E').
    + apply IH12; assumption.
    + apply IH21; assumption.
    + intros X HX.
      assert (HXL : X \notin L) by (exact (notin_union_1 X L (dom E') HX)).
      assert (HXd : X \notin dom E') by (exact (notin_union_2 X L (dom E') HX)).
      assert (HwfS2 : WF E' S2).
      { apply (WF_binds_irrel (proj2 (sub_wf h12)) E' (fun Z V Hb => ex_intro (fun V' => binds Z (bind_sub V') E') V (Hinc Z V Hb))). }
      pose proof (wf_env_sub E' X S2 Hwe' HwfS2 HXd) as Hext.
      exact (IHbody X HXL (X ~ bind_sub S2 ++ E') Hext (binds_sub_cons_incl_same Hinc)).
  - apply sa_rec with (L := L \u dom E').
    + intros X HX.
      assert (HXL : X \notin L) by (exact (notin_union_1 X L (dom E') HX)).
      apply (WF_binds_irrel (w1 X HXL) (X ~ bind_sub typ_top ++ E')
                            (fun Z V Hb => ex_intro (fun V' => binds Z (bind_sub V') (X ~ bind_sub typ_top ++ E')) V (binds_sub_cons_incl_same Hinc Z V Hb))).
    + intros X HX.
      assert (HXL : X \notin L) by (exact (notin_union_1 X L (dom E') HX)).
      apply (WF_binds_irrel (w2 X HXL) (X ~ bind_sub typ_top ++ E')
                            (fun Z V Hb => ex_intro (fun V' => binds Z (bind_sub V') (X ~ bind_sub typ_top ++ E')) V (binds_sub_cons_incl_same Hinc Z V Hb))).
    + intros X HX.
      assert (HXL : X \notin L) by (exact (notin_union_1 X L (dom E') HX)).
      assert (HXd : X \notin dom E') by (exact (notin_union_2 X L (dom E') HX)).
      pose proof (wf_env_sub E' X typ_top Hwe' (WF_top E') HXd) as Hext.
      exact (IHbody X HXL (X ~ bind_sub typ_top ++ E') Hext (binds_sub_cons_incl_same Hinc)).
  - apply sa_label. apply IH1; assumption.
  - apply sa_rcd with (A1 := A1) (A2 := A2).
    + assumption.
    + assumption.
    + assumption.
    + assumption.
    + apply (WF_binds_irrel Hwf1 E' (fun Z V Hb => ex_intro (fun V' => binds Z (bind_sub V') E') V (Hinc Z V Hb))).
    + apply (WF_binds_irrel Hwf2 E' (fun Z V Hb => ex_intro (fun V' => binds Z (bind_sub V') E') V (Hinc Z V Hb))).
    + intros i t1 t2 Hl1 Hl2. apply (IHpt i t1 t2 Hl1 Hl2 E' Hwe' Hinc).
Qed.



(* ============================================================ *)
(* Part 6: inversion principles for subtyping                  *)
(* ============================================================ *)

Lemma sub_arrow_inv : forall E A1 A2 B1 B2,
  sub E (typ_arrow A1 A2) (typ_arrow B1 B2) -> sub E B1 A1 /\ sub E A2 B2.
Proof.
  intros. inversion H; subst; auto;
  try (exfalso; match goal with
       | Hr : rt_type (typ_arrow _ _) |- _ => inversion Hr
       | He : typ_arrow _ _ = typ_top |- _ => discriminate He
       | He : typ_arrow _ _ = typ_fvar _ |- _ => discriminate He
       end).
Qed.

Lemma sub_all_inv : forall E S1 S2 T1 T2,
  sub E (typ_all S1 T1) (typ_all S2 T2) ->
  exists L, sub E S1 S2 /\ sub E S2 S1 /\
    (forall X, X \notin L -> sub (X ~ bind_sub S2 ++ E) (open_tt T1 X) (open_tt T2 X)).
Proof.
  intros. inversion H; subst; eauto;
  try (exfalso; match goal with
       | Hr : rt_type (typ_all _ _) |- _ => inversion Hr
       | He : typ_all _ _ = typ_top |- _ => discriminate He
       | He : typ_all _ _ = typ_fvar _ |- _ => discriminate He
       end).
Qed.

Lemma sub_mu_inv : forall E A1 A2,
  sub E (typ_mu A1) (typ_mu A2) ->
  exists L,
    (forall X, X \notin L -> WF (X ~ bind_sub typ_top ++ E) (open_tt A1 X)) /\
    (forall X, X \notin L -> WF (X ~ bind_sub typ_top ++ E) (open_tt A2 X)) /\
    (forall X, X \notin L -> sub (X ~ bind_sub typ_top ++ E)
        (open_tt A1 (typ_label X (open_tt A1 X)))
        (open_tt A2 (typ_label X (open_tt A2 X)))).
Proof.
  intros. inversion H; subst; eauto;
  try (exfalso; match goal with
       | Hr : rt_type (typ_mu _) |- _ => inversion Hr
       | He : typ_mu _ = typ_top |- _ => discriminate He
       | He : typ_mu _ = typ_fvar _ |- _ => discriminate He
       end).
Qed.



(* ============================================================ *)
(* Part 7: typing weakening                                     *)
(* ============================================================ *)

Lemma binds_incl_cons_same : forall (X : atom) (b : binding) E E',
  (forall Z c, binds Z c E -> binds Z c E') ->
  forall Z c, binds Z c (X ~ b ++ E) -> binds Z c (X ~ b ++ E').
Proof.
  intros X b E E' Hinc Z c Hb.
  apply binds_cons_1 in Hb as [[Heq Hbeq]|Ht].
  - subst Z. subst c. simpl. left. reflexivity.
  - simpl. right. apply Hinc. exact Ht.
Qed.

Lemma typing_weaken_binds : forall E e T, typing E e T ->
  forall E', wf_env E' ->
    (forall Z b, binds Z b E -> binds Z b E') ->
    typing E' e T.
Proof.
  intros E e T H. induction H; intros E' Hwe Hinc.
  - apply typing_nat; assumption.
  - apply typing_var; [assumption| apply Hinc; assumption].
  - (* abs *)
    apply typing_abs with (L := L \u dom E').
    intros x Hx.
    assert (HXL : x \notin L) by (exact (notin_union_1 x L (dom E') Hx)).
    assert (HXd : x \notin dom E') by (exact (notin_union_2 x L (dom E') Hx)).
    (* need WF E' V *)
    assert (HwfV : WF E' V).
    { (* from typing_wf_env of the premise at some fresh x *)
      destruct (atom_fresh (L \u dom E')) as [y Hy].
      assert (HyL : y \notin L) by (exact (notin_union_1 y L (dom E') Hy)).
      pose proof (typing_wf_env (H y HyL)) as Hwext.
      apply wf_env_typ_inv in Hwext. destruct Hwext as [_ [HwfEV _]].
      apply (WF_binds_irrel HwfEV E' (fun Z Vb Hb => ex_intro (fun U => binds Z (bind_sub U) E') Vb (Hinc Z (bind_sub Vb) Hb))). }
    assert (Hext : wf_env (x ~ bind_typ V ++ E')) by (apply wf_env_typ; assumption).
    apply (H0 x HXL (x ~ bind_typ V ++ E') Hext).
    apply binds_incl_cons_same. exact Hinc.
  - (* app *)
    apply typing_app with (T1 := T1); [apply IHtyping1; assumption | apply IHtyping2; assumption].
  - (* tabs *)
    apply typing_tabs with (L := L \u dom E').
    intros X HX.
    assert (HXL : X \notin L) by (exact (notin_union_1 X L (dom E') HX)).
    assert (HXd : X \notin dom E') by (exact (notin_union_2 X L (dom E') HX)).
    assert (HwfV : WF E' V).
    { destruct (atom_fresh (L \u dom E')) as [Y HY].
      assert (HYL : Y \notin L) by (exact (notin_union_1 Y L (dom E') HY)).
      pose proof (typing_wf_env (H Y HYL)) as Hwext.
      apply wf_env_sub_inv in Hwext. destruct Hwext as [_ [HwfEV _]].
      apply (WF_binds_irrel HwfEV E' (fun Z Vb Hb => ex_intro (fun U => binds Z (bind_sub U) E') Vb (Hinc Z (bind_sub Vb) Hb))). }
    assert (Hext : wf_env (X ~ bind_sub V ++ E')) by (apply wf_env_sub; assumption).
    apply (H0 X HXL (X ~ bind_sub V ++ E') Hext).
    apply binds_incl_cons_same. exact Hinc.
  - (* tapp *)
    apply typing_tapp with (T1 := T1).
    + apply IHtyping; assumption.
    + eapply sub_weaken_binds; [exact H0 | exact Hwe | intros Z V Hb; apply Hinc; exact Hb].
  - (* fold *)
    apply typing_fold with (A := A).
    + eapply sub_weaken_binds; [exact H | exact Hwe | intros Z V Hb; apply Hinc; exact Hb].
    + apply IHtyping; assumption.
  - (* unfold *)
    apply typing_unfold with (T := T).
    + apply IHtyping; assumption.
    + eapply sub_weaken_binds; [exact H0 | exact Hwe | intros Z V Hb; apply Hinc; exact Hb].
  - (* sub *)
    apply typing_sub with (S := S).
    + apply IHtyping; assumption.
    + eapply sub_weaken_binds; [exact H0 | exact Hwe | intros Z V Hb; apply Hinc; exact Hb].
  - (* proj *)
    apply typing_proj with (T := T). apply IHtyping; assumption. assumption.
  - (* rcd_nil *) apply typing_rcd_nil; assumption.
  - (* rcd_cons *)
    apply typing_rcd_cons with (T1 := T1) (T2 := T2).
    + apply IHtyping1; assumption.
    + apply IHtyping2; assumption.
    + assumption. + assumption. + assumption.
Qed.


Fixpoint lc_at (k : nat) (e : exp) : Prop :=
  match e with
  | exp_nat => True | exp_bvar i => i < k | exp_fvar _ => True
  | exp_abs _ e1 => lc_at (S k) e1
  | exp_app e1 e2 => lc_at k e1 /\ lc_at k e2
  | exp_tabs _ e1 => lc_at k e1
  | exp_tapp e1 _ => lc_at k e1
  | exp_unfold _ e1 => lc_at k e1
  | exp_fold _ e1 => lc_at k e1
  | exp_rcd_nil => True
  | exp_rcd_cons _ e1 e2 => lc_at k e1 /\ lc_at k e2
  | exp_rcd_proj e1 _ => lc_at k e1
  end.
Lemma lc_at_mono : forall k e, lc_at k e -> lc_at (S k) e.
Proof.
  intros k e. revert k. induction e; simpl; intros k H; try tauto.
  - lia.
  - apply IHe. exact H.
  - simpl in H; destruct H as [H1 H2]. split; [apply IHe1 with (k:=k)|apply IHe2 with (k:=k)]; assumption.
  - apply IHe. exact H.
  - apply IHe. exact H.
  - apply IHe. exact H.
  - apply IHe. exact H.
  - simpl in H; destruct H as [H1 H2]. split; [apply IHe1 with (k:=k)|apply IHe2 with (k:=k)]; assumption.
  - apply IHe. exact H.
Qed.
Lemma lc_at_ge : forall k e, lc_at 0 e -> lc_at k e.
Proof.
  intros k. induction k; intros e H.
  - exact H.
  - apply lc_at_mono. apply IHk. exact H.
Qed.
Lemma lc_open_ee_id : forall j f e, lc_at j e -> open_ee_rec j f e = e.
Proof.
  intros j f e. revert j. induction e; simpl; intros j H; auto.
  - remember (j == n) as b eqn:E. destruct b as [E1|E1]; simpl in *.
    + exfalso. lia.
    + reflexivity.
  - rewrite (IHe (S j) H). reflexivity.
  - simpl in H; destruct H as [H1 H2]. rewrite (IHe1 j H1), (IHe2 j H2). reflexivity.
  - rewrite (IHe j H). reflexivity.
  - rewrite (IHe j H). reflexivity.
  - rewrite (IHe j H). reflexivity.
  - rewrite (IHe j H). reflexivity.
  - simpl in H; destruct H as [H1 H2]. rewrite (IHe1 j H1), (IHe2 j H2). reflexivity.
  - rewrite (IHe j H). reflexivity.
Qed.
Lemma lc_open_ee_inv : forall j f e, lc_at j (open_ee_rec j f e) -> lc_at (S j) e.
Proof.
  intros j f e. revert j. induction e; simpl; intros j H; auto.
  - remember (j == n) as b eqn:E. destruct b as [E1|E1]; simpl in *; lia.
  - simpl in H; destruct H as [H1 H2]; split; [apply IHe1 with (j:=j)|apply IHe2 with (j:=j)]; assumption.
  - simpl in H; destruct H as [H1 H2]; split; [apply IHe1 with (j:=j)|apply IHe2 with (j:=j)]; assumption.
Qed.
Lemma lc_open_te : forall j X e k, lc_at k (open_te_rec j X e) -> lc_at k e.
Proof.
  intros j X e. revert j. induction e; simpl; intros j k H; auto.
  - apply IHe with (j:=j) (k:=S k). exact H.
  - simpl in H; destruct H as [H1 H2]; split; [apply IHe1 with (j:=j)|apply IHe2 with (j:=j)]; assumption.
  - apply IHe with (j:=S j). exact H.
  - apply IHe with (j:=j). exact H.
  - apply IHe with (j:=j). exact H.
  - apply IHe with (j:=j). exact H.
  - simpl in H; destruct H as [H1 H2]; split; [apply IHe1 with (j:=j)|apply IHe2 with (j:=j)]; assumption.
  - apply IHe with (j:=j). exact H.
Qed.

(* locally closed expressions *)
Lemma typing_lc : forall E e T, typing E e T -> lc_at 0 e.
Proof.
  intros E e T H. induction H.
  - simpl. exact I.
  - simpl. exact I.
  - (* abs *)
    simpl. destruct (atom_fresh L) as [x Hx].
    pose proof (H0 x Hx) as Ht. apply lc_open_ee_inv with (j:=0) (f:=x). exact Ht.
  - simpl. split; assumption.
  - (* tabs *)
    simpl. destruct (atom_fresh L) as [X HX].
    pose proof (H0 X HX) as Ht. apply lc_open_te with (j:=0) (X:=X). exact Ht.
  - simpl. assumption.
  - simpl. assumption.
  - simpl. assumption.
  - simpl. assumption.
  - simpl. assumption.
  - simpl. exact I.
  - simpl. split; assumption.
Qed.

Lemma subst_ee_open_ee_rec : forall j x y u e,
  x <> y -> lc_at j u ->
  subst_ee x u (open_ee_rec j y e) = open_ee_rec j y (subst_ee x u e).
Proof.
  intros j x y u e. revert j. induction e; simpl; intros j Hxy Hu.
  - (* bvar *)
    destruct (j == n) as [E1|E1]; simpl.
    + simpl. destruct (y == x) as [E2|E2].
      * exfalso. apply Hxy. symmetry. exact E2.
      * reflexivity.
    + simpl. reflexivity.
  - (* fvar *)
    destruct (a == x) as [E1|E1]; simpl.
    + destruct (a == y) as [E2|E2].
      * subst a. exfalso. apply Hxy. exact E2.
      * rewrite lc_open_ee_id with (j:=j) (f:=y); [reflexivity|exact Hu].
    + destruct (a == y) as [E2|E2]; reflexivity.
  - (* abs *)
    rewrite (IHe (S j) Hxy (lc_at_mono j u Hu)). reflexivity.
  - (* app *)
    rewrite (IHe1 j Hxy Hu), (IHe2 j Hxy Hu). reflexivity.
  - (* tabs *)
    rewrite (IHe j Hxy Hu). reflexivity.
  - (* tapp *)
    rewrite (IHe j Hxy Hu). reflexivity.
  - (* nat *) reflexivity.
  - (* unfold *)
    rewrite (IHe j Hxy Hu). reflexivity.
  - (* fold *)
    rewrite (IHe j Hxy Hu). reflexivity.
  - (* rcd_nil *) reflexivity.
  - (* rcd_cons *)
    rewrite (IHe1 j Hxy Hu), (IHe2 j Hxy Hu). reflexivity.
  - (* rcd_proj *)
    rewrite (IHe j Hxy Hu). reflexivity.
Qed.

Fixpoint lc_tt (k : nat) (T : typ) : Prop :=
  match T with
  | typ_nat | typ_top | typ_fvar _ | typ_rcd_nil => True
  | typ_bvar i => i < k
  | typ_arrow A B => lc_tt k A /\ lc_tt k B
  | typ_all A B => lc_tt k A /\ lc_tt (S k) B
  | typ_mu A => lc_tt (S k) A
  | typ_label _ A => lc_tt k A
  | typ_rcd_cons _ A B => lc_tt k A /\ lc_tt k B
  end.

Lemma lc_tt_open_id : forall k j X T,
  lc_tt k T -> k <= j -> open_tt_rec j X T = T.
Proof.
  intros k j X T. revert k j. induction T; intros k j H Hle; simpl; try reflexivity.
  - (* bvar *) destruct (j === n) as [E|E]; [exfalso; simpl in H; lia|reflexivity].
  - (* arrow *) destruct H as [H1 H2]. rewrite (IHT1 k j H1 Hle), (IHT2 k j H2 Hle). reflexivity.
  - (* all *) destruct H as [H1 H2]. rewrite (IHT1 k j H1 Hle), (IHT2 (S k) (S j) H2 (le_n_S k j Hle)). reflexivity.
  - (* mu *) rewrite (IHT (S k) (S j) H (le_n_S k j Hle)). reflexivity.
  - (* label *) rewrite (IHT k j H Hle). reflexivity.
  - (* rcd_cons *) destruct H as [H1 H2]. rewrite (IHT1 k j H1 Hle), (IHT2 k j H2 Hle). reflexivity.
Qed.

Lemma lc_tt_open_inv_same : forall k X T,
  lc_tt k (open_tt_rec k X T) -> lc_tt (S k) T.
Proof.
  intros k X T. revert k. induction T; simpl; intros k H; try tauto.
  - (* bvar *) destruct (k === n) as [E|E]; simpl in *; lia.
  - (* arrow *) destruct H as [H1 H2]. split; [apply IHT1; exact H1|apply IHT2; exact H2].
  - (* all *) destruct H as [H1 H2]. split.
    + apply IHT1; exact H1.
    + apply (IHT2 (S k)); exact H2.
  - (* mu *) apply (IHT (S k)); exact H.
  - (* label *) apply IHT; exact H.
  - (* rcd_cons *) destruct H as [H1 H2]. split; [apply IHT1; exact H1|apply IHT2; exact H2].
Qed.

Lemma wf_lc_tt : forall E T, WF E T -> lc_tt 0 T.
Proof.
  intros E T H. induction H.
  - simpl; exact I.
  - simpl; exact I.
  - simpl; exact I.
  - simpl. split; assumption.
  - simpl. split.
    + assumption.
    + destruct (atom_fresh L) as [X HX]. apply lc_tt_open_inv_same with (X:=X). apply H1. exact HX.
  - simpl. destruct (atom_fresh L) as [X HX]. apply lc_tt_open_inv_same with (X:=X). apply H0. exact HX.
  - simpl. assumption.
  - simpl; exact I.
  - simpl. split; assumption.
Qed.

Fixpoint lc_exp (k : nat) (e : exp) : Prop :=
  match e with
  | exp_bvar _ | exp_fvar _ | exp_nat | exp_rcd_nil => True
  | exp_abs V e1 => lc_tt k V /\ lc_exp k e1
  | exp_app e1 e2 => lc_exp k e1 /\ lc_exp k e2
  | exp_tabs V e1 => lc_tt k V /\ lc_exp (S k) e1
  | exp_tapp e1 V => lc_exp k e1 /\ lc_tt k V
  | exp_unfold V e1 => lc_tt k V /\ lc_exp k e1
  | exp_fold V e1 => lc_tt k V /\ lc_exp k e1
  | exp_rcd_cons _ e1 e2 => lc_exp k e1 /\ lc_exp k e2
  | exp_rcd_proj e1 _ => lc_exp k e1
  end.

Lemma lc_exp_open_te_id : forall j X e k,
  lc_exp k e -> k <= j -> open_te_rec j X e = e.
Proof.
  intros j X e. revert j. induction e; intros j k H Hle; simpl in H; simpl; try reflexivity; try exact I.
  - (* abs *) destruct H as [H1 H2]. rewrite (@lc_tt_open_id k j X t H1 Hle), (IHe j k H2 Hle). reflexivity.
  - (* app *) destruct H as [H1 H2]. rewrite (IHe1 j k H1 Hle), (IHe2 j k H2 Hle). reflexivity.
  - (* tabs *) destruct H as [H1 H2]. rewrite (@lc_tt_open_id k j X t H1 Hle), (IHe (S j) (S k) H2 (le_n_S k j Hle)). reflexivity.
  - (* tapp *) destruct H as [H1 H2]. rewrite (IHe j k H1 Hle), (@lc_tt_open_id k j X t H2 Hle). reflexivity.
  - (* unfold *) destruct H as [H1 H2]. rewrite (@lc_tt_open_id k j X t H1 Hle), (IHe j k H2 Hle). reflexivity.
  - (* fold *) destruct H as [H1 H2]. rewrite (@lc_tt_open_id k j X t H1 Hle), (IHe j k H2 Hle). reflexivity.
  - (* rcd_cons *) destruct H as [H1 H2]. rewrite (IHe1 j k H1 Hle), (IHe2 j k H2 Hle). reflexivity.
  - (* rcd_proj *) rewrite (IHe j k H Hle). reflexivity.
Qed.

Lemma lc_exp_open_te_inv : forall k X e,
  lc_exp k (open_te_rec k X e) -> lc_exp (S k) e.
Proof.
  intros k X e. revert k. induction e; simpl; intros k H; try tauto.
  - (* abs *) destruct H as [H1 H2]. split.
    + apply lc_tt_open_inv_same with (X:=X). exact H1.
    + apply IHe. exact H2.
  - (* app *) destruct H as [H1 H2]. split; [apply IHe1; exact H1|apply IHe2; exact H2].
  - (* tabs *) destruct H as [H1 H2]. split.
    + apply lc_tt_open_inv_same with (X:=X). exact H1.
    + apply (IHe (S k)). exact H2.
  - (* tapp *) destruct H as [H1 H2]. split.
    + apply IHe. exact H1.
    + apply lc_tt_open_inv_same with (X:=X). exact H2.
  - (* unfold *) destruct H as [H1 H2]. split.
    + apply lc_tt_open_inv_same with (X:=X). exact H1.
    + apply IHe. exact H2.
  - (* fold *) destruct H as [H1 H2]. split.
    + apply lc_tt_open_inv_same with (X:=X). exact H1.
    + apply IHe. exact H2.
  - (* rcd_cons *) destruct H as [H1 H2]. split; [apply IHe1; exact H1|apply IHe2; exact H2].
  - (* rcd_proj *) apply IHe. exact H.
Qed.

Lemma lc_exp_open_ee_inv : forall j x e k,
  lc_exp k (open_ee_rec j x e) -> lc_exp k e.
Proof.
  intros j x e. revert j. induction e; simpl; intros j k H; try tauto.
  - (* abs *) destruct H as [H1 H2]. split; [exact H1|apply (IHe (S j)); exact H2].
  - (* app *) destruct H as [H1 H2]. split; [apply (IHe1 j); exact H1|apply (IHe2 j); exact H2].
  - (* tabs *) destruct H as [H1 H2]. split; [exact H1|apply (IHe j); exact H2].
  - (* tapp *) destruct H as [H1 H2]. split; [apply (IHe j); exact H1|exact H2].
  - (* unfold *) destruct H as [H1 H2]. split; [exact H1|apply (IHe j); exact H2].
  - (* fold *) destruct H as [H1 H2]. split; [exact H1|apply (IHe j); exact H2].
  - (* rcd_cons *) destruct H as [H1 H2]. split; [apply (IHe1 j); exact H1|apply (IHe2 j); exact H2].
  - (* rcd_proj *) apply (IHe j). exact H.
Qed.

Lemma typing_lc_exp : forall E e T, typing E e T -> lc_exp 0 e.
Proof.
  intros E e T H. induction H.
  - simpl; exact I.
  - simpl; exact I.
  - (* abs *) simpl. split.
    + destruct (atom_fresh L) as [x Hx].
      pose proof (typing_wf_env (H x Hx)) as Hw. apply wf_env_typ_inv in Hw.
      destruct Hw as [_ [Hwf _]]. exact (@wf_lc_tt E V Hwf).
    + destruct (atom_fresh L) as [x Hx].
      apply (lc_exp_open_ee_inv 0 x e1 0). apply H0. exact Hx.
  - (* app *) simpl. split; assumption.
  - (* tabs *) simpl. split.
    + destruct (atom_fresh L) as [X HX].
      pose proof (typing_wf_env (H X HX)) as Hw. apply wf_env_sub_inv in Hw.
      destruct Hw as [_ [Hwf _]]. exact (@wf_lc_tt E V Hwf).
    + destruct (atom_fresh L) as [X HX].
      apply (lc_exp_open_te_inv 0 X e1). apply H0. exact HX.
  - (* tapp *) simpl. split.
    + assumption.
    + exact (@wf_lc_tt E T (proj1 (sub_wf H0))).
  - (* fold *) simpl. split.
    + exact (@wf_lc_tt G T (proj2 (sub_wf H))).
    + assumption.
  - (* unfold *) simpl. split.
    + exact (@wf_lc_tt G A (proj1 (sub_wf H0))).
    + assumption.
  - (* sub *) simpl. assumption.
  - (* proj *) simpl. assumption.
  - (* rcd_nil *) simpl; exact I.
  - (* rcd_cons *) simpl. split; assumption.
Qed.

Lemma binds_cons_any : forall (A : Type) (x y : atom) (a b : A) (E : list (atom * A)),
  binds x a E -> binds x a ((y, b) :: E).
Proof.
  intros. exact (@binds_cons A x y a b E H).
Qed.
Lemma subst_ee_open_te_rec : forall j X u x e,
  lc_exp 0 u ->
  subst_ee x u (open_te_rec j X e) = open_te_rec j X (subst_ee x u e).
Proof.
  intros j X u x e. revert j. induction e; simpl; intros j Hlc.
  - reflexivity.
  - destruct (a == x) as [E1|E1]; simpl.
    + subst a. symmetry. exact (@lc_exp_open_te_id j X u 0 Hlc (Nat.le_0_l j)).
    + reflexivity.
  - (* abs *) rewrite (IHe j Hlc). reflexivity.
  - (* app *) rewrite (IHe1 j Hlc), (IHe2 j Hlc). reflexivity.
  - (* tabs *) rewrite (IHe (S j) Hlc). reflexivity.
  - (* tapp *) rewrite (IHe j Hlc). reflexivity.
  - reflexivity.
  - (* unfold *) rewrite (IHe j Hlc). reflexivity.
  - (* fold *) rewrite (IHe j Hlc). reflexivity.
  - reflexivity.
  - (* rcd_cons *) rewrite (IHe1 j Hlc), (IHe2 j Hlc). reflexivity.
  - (* rcd_proj *) rewrite (IHe j Hlc). reflexivity.
Qed.


Lemma rt_expr_subst_ee : forall z u e,
  rt_expr e -> rt_expr (subst_ee z u e).
Proof.
  intros z u e H. inversion H; subst; simpl.
  - apply rt_expr_rcd_nil.
  - apply rt_expr_rcd_cons.
Qed.

Lemma collectLabele_subst_ee_typed : forall E e T, typing E e T ->
  rt_expr e -> forall z u, collectLabele (subst_ee z u e) = collectLabele e.
Proof.
  intros E e T H. induction H; intros Hr z u;
  try (inversion Hr; subst; simpl; reflexivity).
  - (* sub *) simpl. apply IHtyping. exact Hr.
  - (* rcd_cons *) simpl.
  first [ apply (f_equal (fun S => {{i}} \u S)); exact (IHtyping2 H2 z u)
        | symmetry; apply (f_equal (fun S => {{i}} \u S)); exact (IHtyping2 H2 z u) ].
Qed.

Lemma typing_subst_ee_aux : forall E e T, typing E e T ->
  forall z u W, typing E u W -> lc_at 0 u -> lc_exp 0 u ->
  binds z (bind_typ W) E ->
  typing E (subst_ee z u e) T.
Proof.
  intros E e T H. induction H; intros z u W Hu HlcA HlcE Hb.
  - (* nat *) apply typing_nat; assumption.
  - (* var x *) destruct (x == z) as [Eeq|Eneq].
    + subst x. simpl. destruct (z == z) as [E2|E2]; [|contradiction].
      assert (Heq : bind_typ T = bind_typ W) by (eapply binds_unique; eauto using wf_env_uniq).
      injection Heq as HTV. subst T. exact Hu.
    + simpl. destruct (x == z) as [E2|E2]; [contradiction|].
      apply typing_var; assumption.
  - (* abs *) simpl.
    apply typing_abs with (L := L \u {{z}}).
    intros z0 Hx0.
    assert (Hx0L : z0 \notin L) by (exact (notin_union_1 z0 L {{z}} Hx0)).
    assert (Hne : z <> z0) by (apply (notin_singleton_1 z z0); apply (notin_union_2 z0 L {{z}}); exact Hx0).
    assert (Hb' : binds z (bind_typ W) (z0 ~ bind_typ V ++ E)) by (apply binds_cons_any; exact Hb).
    pose proof (typing_wf_env (H z0 Hx0L)) as Hwext.
    pose proof (typing_weaken_binds (E' := z0 ~ bind_typ V ++ E) Hu Hwext
                  (fun Z b Hbz => @binds_cons_any binding Z z0 b (bind_typ V) E Hbz)) as Hu'.
    pose proof (H0 z0 Hx0L z u W Hu' HlcA HlcE Hb') as Hres.
    unfold open_ee in Hres.
    rewrite (@subst_ee_open_ee_rec 0 z z0 u e1 Hne HlcA) in Hres.
    exact Hres.
  - (* app *) simpl. apply typing_app with (T1:=T1);
      [apply (IHtyping1 z u W Hu HlcA HlcE Hb)|apply (IHtyping2 z u W Hu HlcA HlcE Hb)].
  - (* tabs *) simpl.
    apply typing_tabs with (L := L \u {{z}}).
    intros X HX.
    assert (HXL : X \notin L) by (exact (notin_union_1 X L {{z}} HX)).
    assert (Hb' : binds z (bind_typ W) (X ~ bind_sub V ++ E)) by (apply binds_cons_any; exact Hb).
    pose proof (typing_wf_env (H X HXL)) as Hwext.
    pose proof (typing_weaken_binds (E' := X ~ bind_sub V ++ E) Hu Hwext
                  (fun Z b Hbz => @binds_cons_any binding Z X b (bind_sub V) E Hbz)) as Hu'.
    pose proof (H0 X HXL z u W Hu' HlcA HlcE Hb') as Hres.
    unfold open_te in Hres.
    rewrite (@subst_ee_open_te_rec 0 X u z e1 HlcE) in Hres.
    exact Hres.
  - (* tapp *) simpl. eapply typing_tapp;
      [apply (IHtyping z u W Hu HlcA HlcE Hb)|exact H0].
  - (* fold *) simpl. eapply typing_fold;
      [exact H | apply (IHtyping z u W Hu HlcA HlcE Hb)].
  - (* unfold *) simpl. eapply typing_unfold;
      [apply (IHtyping z u W Hu HlcA HlcE Hb)|exact H0].
  - (* sub *) simpl. eapply typing_sub;
      [apply (IHtyping z u W Hu HlcA HlcE Hb)|exact H0].
  - (* proj *) simpl. eapply typing_proj;
      [apply (IHtyping z u W Hu HlcA HlcE Hb)|exact H0].
  - (* rcd_nil *) apply typing_rcd_nil; assumption.
  - (* rcd_cons *) simpl. eapply typing_rcd_cons;
      [apply (IHtyping1 z u W Hu HlcA HlcE Hb)|apply (IHtyping2 z u W Hu HlcA HlcE Hb)|exact H1|apply rt_expr_subst_ee; exact H2|rewrite (collectLabele_subst_ee_typed H0 H2 z u); exact H3].
Qed.

Lemma fv_ee_open_ee_remove : forall j (y : atom) e x,
  x \notin fv_ee (open_ee_rec j y e) -> x <> y -> x \notin fv_ee e.
Proof.
  intros j y e. revert j. induction e; simpl in *; intros j x H Hxy.
  - (* bvar *) apply notin_empty_1.
  - (* fvar *) fsetdec.
  - (* abs *) apply IHe with (j:=S j); assumption.
  - (* app *) apply notin_union_1 in H as H1; apply notin_union_2 in H as H2.
    apply notin_union_3.
    + apply IHe1 with (j:=j); [exact H1|exact Hxy].
    + apply IHe2 with (j:=j); [exact H2|exact Hxy].
  - (* tabs *) apply IHe with (j:=j); assumption.
  - (* tapp *) apply IHe with (j:=j); assumption.
  - (* nat *) apply notin_empty_1.
  - (* unfold *) apply IHe with (j:=j); assumption.
  - (* fold *) apply IHe with (j:=j); assumption.
  - (* rcd_nil *) apply notin_empty_1.
  - (* rcd_cons *) apply notin_union_1 in H as H1; apply notin_union_2 in H as H2.
    apply notin_union_3.
    + apply IHe1 with (j:=j); [exact H1|exact Hxy].
    + apply IHe2 with (j:=j); [exact H2|exact Hxy].
  - (* rcd_proj *) apply IHe with (j:=j); assumption.
Qed.

Lemma fv_ee_open_te : forall j X e, fv_ee (open_te_rec j X e) = fv_ee e.
Proof.
  intros j X e. revert j. induction e; simpl; intros j; try reflexivity;
  try (rewrite IHe; reflexivity);
  try (rewrite IHe1, IHe2; reflexivity).
Qed.

Lemma fv_ee_typing : forall E e T, typing E e T ->
  forall z, z \notin dom E -> z \notin fv_ee e.
Proof.
  intros E e T H. induction H; intros z Hz.
  - simpl. apply notin_empty_1.
  - (* var *) simpl. intro He. apply AtomSetImpl.singleton_1 in He. subst z.
    exact (@binds_dom_contradiction binding x (bind_typ T) E H0 Hz).
  - (* abs *)
    assert (Hf : z \notin dom E) by exact Hz.
    destruct (atom_fresh (L \u dom E \u {{z}})) as [y Hy].
    assert (HyL : y \notin L) by fsetdec.
    assert (Hyd : y \notin dom E) by fsetdec.
    assert (Hyz' : y <> z) by fsetdec.
    assert (Hzdom : z \notin dom (y ~ bind_typ V ++ E)) by (simpl; fsetdec).
    pose proof (H0 y HyL z Hzdom) as Hfv.
    apply (@fv_ee_open_ee_remove 0 y e1 z Hfv (fun He => Hyz' (eq_sym He))).
  - (* app *) simpl. apply notin_union_3.
    + apply IHtyping1. exact Hz.
    + apply IHtyping2. exact Hz.
  - (* tabs *)
    destruct (atom_fresh (L \u dom E \u {{z}})) as [X HX].
    assert (HXL : X \notin L) by fsetdec.
    assert (HXd : X \notin dom E) by fsetdec.
    assert (HXz' : X <> z) by fsetdec.
    assert (Hzdom : z \notin dom (X ~ bind_sub V ++ E)) by (simpl; fsetdec).
    pose proof (H0 X HXL z Hzdom) as Hfv.
    unfold open_te in Hfv. rewrite fv_ee_open_te in Hfv. exact Hfv.
  - (* tapp *) simpl. apply IHtyping. exact Hz.
  - (* fold *) simpl. apply IHtyping. exact Hz.
  - (* unfold *) simpl. apply IHtyping. exact Hz.
  - (* sub *) simpl. apply IHtyping. exact Hz.
  - (* proj *) simpl. apply IHtyping. exact Hz.
  - (* rcd_nil *) simpl. apply notin_empty_1.
  - (* rcd_cons *) simpl. apply notin_union_3.
    + apply IHtyping1. exact Hz.
    + apply IHtyping2. exact Hz.
Qed.

Lemma binds_remove_typ : forall (D : env) E z W (Y : atom) b,
  binds Y b (D ++ z ~ bind_typ W ++ E) -> Y <> z -> binds Y b (D ++ E).
Proof.
  induction D as [| [a c] D IH]; intros E z W Y b Hb Hne; simpl in *.
  - apply binds_cons_1 in Hb as [[Heq Hbeq]|Ht].
    + subst Y. exfalso. apply Hne. reflexivity.
    + exact Ht.
  - apply binds_cons_1 in Hb as [[Heq Hbeq]|Ht].
    + subst Y. subst b. simpl. left. reflexivity.
    + simpl. right. apply IH with (z:=z) (W:=W); assumption.
Qed.

Lemma notin_dom_remove_typ : forall (D : env) E z W (y : atom),
  y \notin dom (D ++ z ~ bind_typ W ++ E) -> y \notin dom (D ++ E).
Proof.
  induction D as [| [a c] D IH]; intros E z W y Hy; simpl in *.
  - apply notin_add_2 in Hy. exact Hy.
  - apply notin_add_1 in Hy as Hya. apply notin_add_2 in Hy as Hy'.
    apply notin_add_3.
    + exact Hya.
    + apply IH with (z:=z) (W:=W). exact Hy'.
Qed.

Lemma binds_sub_remove_typ : forall (D : env) E z W (Y : atom) V,
  wf_env (D ++ z ~ bind_typ W ++ E) ->
  binds Y (bind_sub V) (D ++ z ~ bind_typ W ++ E) ->
  exists V', binds Y (bind_sub V') (D ++ E).
Proof.
  intros D E z W Y V Hwe Hb.
  destruct (Y == z) as [Heq|Hne].
  - exfalso. subst Y.
    assert (Huniq : uniq (D ++ z ~ bind_typ W ++ E)) by (apply wf_env_uniq; assumption).
    assert (Hcontra : bind_sub V = bind_typ W) by (eapply binds_unique; eauto).
    discriminate Hcontra.
  - exists V. exact (@binds_remove_typ D E z W Y (bind_sub V) Hb Hne).
Qed.

Lemma wf_env_remove_typ : forall (D : env) E z W,
  wf_env (D ++ z ~ bind_typ W ++ E) -> wf_env (D ++ E).
Proof.
  induction D as [| [a c] D IH]; intros E z W Hwe; simpl in *.
  - apply wf_env_typ_inv in Hwe. tauto.
  - inversion Hwe as [| EE X T HweE HwfT Hfresh | EE x T HweE HwfT Hfresh]; subst.
    + (* bind_sub *) apply wf_env_sub.
      * apply IH with (z:=z) (W:=W). exact HweE.
      * eapply WF_binds_irrel; [exact HwfT|].
        intros Y V Hb. apply (binds_sub_remove_typ D E z W Y V).
        -- exact HweE.
        -- exact Hb.
      * exact (@notin_dom_remove_typ D E z W a Hfresh).
    + (* bind_typ *) apply wf_env_typ.
      * apply IH with (z:=z) (W:=W). exact HweE.
      * eapply WF_binds_irrel; [exact HwfT|].
        intros Y V Hb. apply (binds_sub_remove_typ D E z W Y V).
        -- exact HweE.
        -- exact Hb.
      * exact (@notin_dom_remove_typ D E z W a Hfresh).
Qed.

Lemma binds_mid_typ : forall (D : env) E z W,
  binds z (bind_typ W) (D ++ z ~ bind_typ W ++ E).
Proof.
  induction D as [| [a c] D IH]; simpl.
  - left. reflexivity.
  - right. exact (IH E z W).
Qed.

Lemma binds_remove_typ_same : forall (D : env) E z W (Y : atom) V,
  wf_env (D ++ z ~ bind_typ W ++ E) ->
  binds Y (bind_sub V) (D ++ z ~ bind_typ W ++ E) ->
  binds Y (bind_sub V) (D ++ E).
Proof.
  intros D E z W Y V Hwe Hb.
  destruct (Y == z) as [Heq|Hne].
  - exfalso. subst Y.
    assert (Huniq : uniq (D ++ z ~ bind_typ W ++ E)) by (apply wf_env_uniq; assumption).
    assert (Hmid : binds z (bind_typ W) (D ++ z ~ bind_typ W ++ E)) by (apply binds_mid_typ).
    assert (Hcontra : bind_sub V = bind_typ W) by (eapply binds_unique; eauto).
    discriminate Hcontra.
  - exact (@binds_remove_typ D E z W Y (bind_sub V) Hb Hne).
Qed.

Lemma sub_remove_typ : forall (D : env) E z W A B,
  wf_env (D ++ z ~ bind_typ W ++ E) ->
  sub (D ++ z ~ bind_typ W ++ E) A B ->
  sub (D ++ E) A B.
Proof.
  intros D E z W A B Hwe Hsub.
  eapply sub_weaken_binds with (E' := D ++ E).
  - exact Hsub.
  - apply wf_env_remove_typ with (z:=z) (W:=W). exact Hwe.
  - intros Y V Hb. exact (@binds_remove_typ_same D E z W Y V Hwe Hb).
Qed.

Lemma fv_ee_open_ee_intro : forall j (y : atom) e x,
  x \notin fv_ee e -> x <> y -> x \notin fv_ee (open_ee_rec j y e).
Proof.
  intros j y e. revert j. induction e; simpl in *; intros j x H Hxy.
  - (* bvar *) destruct (j == n) as [E1|E1]; simpl.
    + fsetdec.
    + apply notin_empty_1.
  - (* fvar *) exact H.
  - (* abs *) apply IHe with (j:=S j); assumption.
  - (* app *) apply notin_union_1 in H as H1; apply notin_union_2 in H as H2.
    apply notin_union_3.
    + apply IHe1 with (j:=j); [exact H1|exact Hxy].
    + apply IHe2 with (j:=j); [exact H2|exact Hxy].
  - (* tabs *) apply IHe with (j:=j); assumption.
  - (* tapp *) apply IHe with (j:=j); assumption.
  - (* nat *) apply notin_empty_1.
  - (* unfold *) apply IHe with (j:=j); assumption.
  - (* fold *) apply IHe with (j:=j); assumption.
  - (* rcd_nil *) apply notin_empty_1.
  - (* rcd_cons *) apply notin_union_1 in H as H1; apply notin_union_2 in H as H2.
    apply notin_union_3.
    + apply IHe1 with (j:=j); [exact H1|exact Hxy].
    + apply IHe2 with (j:=j); [exact H2|exact Hxy].
  - (* rcd_proj *) apply IHe with (j:=j); assumption.
Qed.

Lemma typing_remove_typ_gen : forall G e T, typing G e T ->
  forall (D : env) E0 z W,
    G = D ++ z ~ bind_typ W ++ E0 ->
    z \notin fv_ee e ->
    typing (D ++ E0) e T.
Proof.
  intros G e T H. induction H; intros D E0 z W Heq Hz.
  - (* nat *) apply typing_nat. subst. apply wf_env_remove_typ with (z:=z) (W:=W). assumption.
  - (* var *) simpl in Hz.
    assert (Hxz : x <> z) by (intro He; subst x; apply Hz; apply AtomSetImpl.singleton_2; reflexivity).
    apply typing_var.
    + subst. apply wf_env_remove_typ with (z:=z) (W:=W). assumption.
    + subst. exact (@binds_remove_typ D E0 z W x (bind_typ T) H0 Hxz).
  - (* abs *) subst.
    apply typing_abs with (L := L \u {{z}}).
    intros y Hy.
    assert (HyL : y \notin L) by fsetdec.
    assert (Hyz : y <> z) by fsetdec.
    assert (Hzy : z <> y) by (intro He; apply Hyz; symmetry; exact He).
    apply (H0 y HyL (y ~ bind_typ V ++ D) E0 z W eq_refl).
    simpl in Hz.
    apply (@fv_ee_open_ee_intro 0 y e1 z).
    + exact Hz.
    + exact Hzy.
  - (* app *) simpl in Hz.
    apply notin_union_1 in Hz as Hz1; apply notin_union_2 in Hz as Hz2.
    apply typing_app with (T1:=T1).
    + exact (IHtyping1 D E0 z W Heq Hz1).
    + exact (IHtyping2 D E0 z W Heq Hz2).
  - (* tabs *) subst.
    apply typing_tabs with (L := L \u {{z}}).
    intros X HX.
    assert (HXL : X \notin L) by fsetdec.
    apply (H0 X HXL (X ~ bind_sub V ++ D) E0 z W eq_refl).
    simpl. unfold open_te. rewrite fv_ee_open_te. exact Hz.
  - (* tapp *) pose proof (IHtyping D E0 z W Heq Hz) as Ht.
    assert (HweS : wf_env (D ++ z ~ bind_typ W ++ E0)) by (rewrite <- Heq; exact (typing_wf_env H)).
    subst. eapply typing_tapp.
    + exact Ht.
    + eapply sub_remove_typ; [exact HweS|exact H0].
  - (* fold *) pose proof (IHtyping D E0 z W Heq Hz) as Ht.
    subst. eapply typing_fold.
    + eapply sub_remove_typ; [exact (typing_wf_env H0)|exact H].
    + exact Ht.
  - (* unfold *) pose proof (IHtyping D E0 z W Heq Hz) as Ht.
    subst. eapply typing_unfold.
    + exact Ht.
    + eapply sub_remove_typ; [exact (typing_wf_env H)|exact H0].
  - (* sub *) pose proof (IHtyping D E0 z W Heq Hz) as Ht.
    subst. eapply typing_sub.
    + exact Ht.
    + eapply sub_remove_typ; [exact (typing_wf_env H)|exact H0].
  - (* proj *) eapply typing_proj.
    + exact (IHtyping D E0 z W Heq Hz).
    + exact H0.
  - (* rcd_nil *) apply typing_rcd_nil. subst.
    apply wf_env_remove_typ with (z:=z) (W:=W). assumption.
  - (* rcd_cons *) simpl in Hz.
    apply notin_union_1 in Hz as Hz1; apply notin_union_2 in Hz as Hz2.
    eapply typing_rcd_cons.
    + exact (IHtyping1 D E0 z W Heq Hz1).
    + exact (IHtyping2 D E0 z W Heq Hz2).
    + exact H1. + exact H2. + exact H3.
Qed.

Lemma typing_remove_typ : forall (D : env) E0 z W e T,
  typing (D ++ z ~ bind_typ W ++ E0) e T ->
  z \notin fv_ee e ->
  typing (D ++ E0) e T.
Proof.
  intros D E0 z W e T Hty Hfv.
  exact (@typing_remove_typ_gen (D ++ z ~ bind_typ W ++ E0) e T Hty D E0 z W eq_refl Hfv).
Qed.

Lemma fv_ee_open_ee_exp : forall j (u e : exp) x,
  x \notin fv_ee e -> x \notin fv_ee u -> x \notin fv_ee (open_ee_rec j u e).
Proof.
  intros j u e. revert j. induction e; simpl in *; intros j x He Hu.
  - (* bvar *) destruct (j == n) as [E1|E1]; simpl.
    + exact Hu.
    + apply notin_empty_1.
  - (* fvar *) exact He.
  - (* abs *) apply IHe with (j:=S j); assumption.
  - (* app *) apply notin_union_1 in He as He1; apply notin_union_2 in He as He2.
    apply notin_union_3.
    + apply IHe1 with (j:=j); assumption.
    + apply IHe2 with (j:=j); assumption.
  - (* tabs *) apply IHe with (j:=j); assumption.
  - (* tapp *) apply IHe with (j:=j); assumption.
  - (* nat *) apply notin_empty_1.
  - (* unfold *) apply IHe with (j:=j); assumption.
  - (* fold *) apply IHe with (j:=j); assumption.
  - (* rcd_nil *) apply notin_empty_1.
  - (* rcd_cons *) apply notin_union_1 in He as He1; apply notin_union_2 in He as He2.
    apply notin_union_3.
    + apply IHe1 with (j:=j); assumption.
    + apply IHe2 with (j:=j); assumption.
  - (* rcd_proj *) apply IHe with (j:=j); assumption.
Qed.

Lemma subst_ee_open_ee_same : forall j x u e,
  x \notin fv_ee e ->
  subst_ee x u (open_ee_rec j x e) = open_ee_rec j u e.
Proof.
  intros j x u e. revert j. induction e; simpl in *; intros j Hx.
  - (* bvar *) destruct (j == n) as [E1|E1]; simpl.
    + destruct (x == x) as [E2|E2]; [reflexivity|contradiction].
    + reflexivity.
  - (* fvar *) apply notin_singleton_1 in Hx. simpl.
    destruct (a == x) as [E2|E2]; [exfalso; apply Hx; exact E2|reflexivity].
  - (* abs *) rewrite (IHe (S j) Hx). reflexivity.
  - (* app *) apply notin_union_1 in Hx as H1; apply notin_union_2 in Hx as H2.
    rewrite (IHe1 j H1), (IHe2 j H2). reflexivity.
  - (* tabs *) rewrite (IHe j Hx). reflexivity.
  - (* tapp *) rewrite (IHe j Hx). reflexivity.
  - (* nat *) reflexivity.
  - (* unfold *) rewrite (IHe j Hx). reflexivity.
  - (* fold *) rewrite (IHe j Hx). reflexivity.
  - (* rcd_nil *) reflexivity.
  - (* rcd_cons *) apply notin_union_1 in Hx as H1; apply notin_union_2 in Hx as H2.
    rewrite (IHe1 j H1), (IHe2 j H2). reflexivity.
  - (* rcd_proj *) rewrite (IHe j Hx). reflexivity.
Qed.


Lemma sub_nil_arrow_inv : forall X A1 A2,
  sub nil X (typ_arrow A1 A2) ->
  exists B1 B2, X = typ_arrow B1 B2 /\ sub nil A1 B1 /\ sub nil B2 A2.
Proof.
  intros X A1 A2 H. inversion H; subst; try discriminate.
  - (* trans_tvar *) exfalso. inversion H0.
  - (* arrow *) eauto.
  - (* rcd *) exfalso. inversion H2.
Qed.

Lemma typing_abs_apply_gen : forall E e T, typing E e T ->
  E = nil -> forall V e1, e = exp_abs V e1 ->
  forall A1 A2, T = typ_arrow A1 A2 ->
  forall u, typing nil u A1 -> typing nil (open_ee e1 u) A2.
Proof.
  intros E e T H. induction H; intros Enil Vx ex Ee A1 A2 ET u Hu.
  - (* nat *) discriminate Ee.
  - (* var *) discriminate Ee.
  - (* abs *) injection Ee as HV He. injection ET as HA1 HA2.
    subst E. rewrite <- He. rewrite <- HA1 in Hu. rewrite <- HA2.
    destruct (atom_fresh (L \u fv_ee e1 \u fv_ee u)) as [x Hx].
    assert (HxL : x \notin L) by fsetdec.
    assert (Hxe : x \notin fv_ee e1) by fsetdec.
    assert (Hxu : x \notin fv_ee u) by fsetdec.
    pose proof (H x HxL) as Hbody.
    pose proof (typing_lc Hu) as HlcA.
    pose proof (typing_lc_exp Hu) as HlcE.
    assert (Hwen : wf_env (x ~ bind_typ V ++ nil)) by (apply typing_wf_env in Hbody; exact Hbody).
    pose proof (typing_weaken_binds (E' := x ~ bind_typ V ++ nil) Hu Hwen
                  (fun Z b Hb => @binds_cons_any binding Z x b (bind_typ V) nil Hb)) as Hu'.
    pose proof (@typing_subst_ee_aux (x ~ bind_typ V ++ nil) (open_ee e1 x) T1 Hbody
                  x u V Hu' HlcA HlcE (binds_mid_typ nil nil x V)) as Hres.
    simpl in Hres.
    unfold open_ee in Hres.
    rewrite (@subst_ee_open_ee_same 0 x u e1 Hxe) in Hres.
    unfold open_ee in Hres |- *.
    eapply typing_remove_typ with (D:=nil) (E0:=nil) (z:=x) (W:=V).
    + exact Hres.
    + apply (@fv_ee_open_ee_exp 0 u e1 x Hxe Hxu).
  - (* app *) discriminate Ee.
  - (* tabs *) discriminate Ee.
  - (* tapp *) discriminate Ee.
  - (* fold *) discriminate Ee.
  - (* unfold *) discriminate Ee.
  - (* sub *) subst E. rewrite ET in H0.
    destruct (@sub_nil_arrow_inv S A1 A2 H0) as [B1 [B2 [Heq [Hdom Hcod]]]].
    assert (HuB1 : typing nil u B1) by (apply typing_sub with (S:=A1); assumption).
    pose proof (IHtyping eq_refl Vx ex Ee B1 B2 Heq u HuB1) as Hbody.
    simpl in Hbody.
    eapply typing_sub; [exact Hbody|exact Hcod].
  - (* proj *) discriminate Ee.
  - (* rcd_nil *) discriminate Ee.
  - (* rcd_cons *) discriminate Ee.
Qed.

Lemma typing_abs_apply_nil : forall V e1 U,
  typing nil (exp_abs V e1) U ->
  forall A1 A2, U = typ_arrow A1 A2 ->
  forall u, typing nil u A1 -> typing nil (open_ee e1 u) A2.
Proof.
  intros V e1 U H A1 A2 EU u Hu.
  exact (@typing_abs_apply_gen nil (exp_abs V e1) U H eq_refl V e1 eq_refl A1 A2 EU u Hu).
Qed.

Lemma preservation_beta : forall V e1 e2 A1 A2,
  typing nil (exp_abs V e1) (typ_arrow A1 A2) ->
  typing nil e2 A1 ->
  typing nil (open_ee e1 e2) A2.
Proof.
  intros V e1 e2 A1 A2 H Hu.
  exact (@typing_abs_apply_nil V e1 (typ_arrow A1 A2) H A1 A2 eq_refl e2 Hu).
Qed.

Lemma typing_app1_step_gen : forall E e T, typing E e T ->
  E = nil -> forall e1 e2 e1', e = exp_app e1 e2 ->
  (forall A1 A2, typing nil e1 (typ_arrow A1 A2) -> typing nil e1' (typ_arrow A1 A2)) ->
  typing nil (exp_app e1' e2) T.
Proof.
  intros E e T H. induction H; intros Enil x1 x2 y1 Ee Hstep.
  - (* nat *) discriminate Ee.
  - (* var *) discriminate Ee.
  - (* abs *) discriminate Ee.
  - (* app *) injection Ee as He1 He2. subst x1. subst x2. subst E.
    simpl. eapply typing_app.
    + apply Hstep. exact H.
    + exact H0.
  - (* tabs *) discriminate Ee.
  - (* tapp *) discriminate Ee.
  - (* fold *) discriminate Ee.
  - (* unfold *) discriminate Ee.
  - (* sub *) subst E. eapply typing_sub.
    + apply (IHtyping eq_refl x1 x2 y1 Ee Hstep).
    + exact H0.
  - (* proj *) discriminate Ee.
  - (* rcd_nil *) discriminate Ee.
  - (* rcd_cons *) discriminate Ee.
Qed.

Lemma typing_app1_step : forall e1 e2 e1' T,
  typing nil (exp_app e1 e2) T ->
  (forall A1 A2, typing nil e1 (typ_arrow A1 A2) -> typing nil e1' (typ_arrow A1 A2)) ->
  typing nil (exp_app e1' e2) T.
Proof.
  intros. exact (@typing_app1_step_gen nil (exp_app e1 e2) T H eq_refl e1 e2 e1' eq_refl H0).
Qed.

Lemma typing_app2_step_gen : forall E e T, typing E e T ->
  E = nil -> forall v x y, e = exp_app v x ->
  (forall A, typing nil x A -> typing nil y A) ->
  typing nil (exp_app v y) T.
Proof.
  intros E e T H. induction H; intros Enil v0 x0 y0 Ee Hstep.
  - discriminate Ee. - discriminate Ee. - discriminate Ee.
  - (* app *) injection Ee as Hv Hx. subst v0. subst x0. subst E.
    simpl. eapply typing_app.
    + exact H.
    + apply Hstep. exact H0.
  - discriminate Ee. - discriminate Ee. - discriminate Ee. - discriminate Ee.
  - (* sub *) subst E. eapply typing_sub.
    + apply (IHtyping eq_refl v0 x0 y0 Ee Hstep).
    + exact H0.
  - discriminate Ee. - discriminate Ee. - discriminate Ee.
Qed.

Lemma typing_app2_step : forall v x y T,
  typing nil (exp_app v x) T ->
  (forall A, typing nil x A -> typing nil y A) ->
  typing nil (exp_app v y) T.
Proof.
  intros. exact (@typing_app2_step_gen nil (exp_app v x) T H eq_refl v x y eq_refl H0).
Qed.

Lemma typing_tapp_step_gen : forall E e T, typing E e T ->
  E = nil -> forall x y V, e = exp_tapp x V ->
  (forall A1 A2, typing nil x (typ_all A1 A2) -> typing nil y (typ_all A1 A2)) ->
  typing nil (exp_tapp y V) T.
Proof.
  intros E e T H. induction H; intros Enil x0 y0 V0 Ee Hstep.
  - discriminate Ee. - discriminate Ee. - discriminate Ee. - discriminate Ee.
  - (* tabs case subject mismatch *) discriminate Ee.
  - (* tapp *) injection Ee as Hx HV. subst x0. subst V0. subst E.
    simpl. eapply typing_tapp.
    + apply Hstep. exact H.
    + exact H0.
  - discriminate Ee. - discriminate Ee.
  - (* sub *) subst E. eapply typing_sub.
    + apply (IHtyping eq_refl x0 y0 V0 Ee Hstep).
    + exact H0.
  - discriminate Ee. - discriminate Ee. - discriminate Ee.
Qed.

Lemma typing_tapp_step : forall x y V T,
  typing nil (exp_tapp x V) T ->
  (forall A1 A2, typing nil x (typ_all A1 A2) -> typing nil y (typ_all A1 A2)) ->
  typing nil (exp_tapp y V) T.
Proof.
  intros. exact (@typing_tapp_step_gen nil (exp_tapp x V) T H eq_refl x y V eq_refl H0).
Qed.

Lemma typing_fold_step_gen : forall E e T, typing E e T ->
  E = nil -> forall F x0 y0, e = exp_fold F x0 ->
  (forall A, typing nil x0 A -> typing nil y0 A) ->
  typing nil (exp_fold F y0) T.
Proof.
  intros E e T H. induction H; intros Enil F x0 y0 Ee Hstep.
  - discriminate Ee. - discriminate Ee. - discriminate Ee. - discriminate Ee. - discriminate Ee. - discriminate Ee.
  - (* fold *) injection Ee as HT He. subst F. subst x0. subst G.
    simpl. eapply typing_fold.
    + exact H.
    + apply Hstep. exact H0.
  - discriminate Ee.
  - (* sub *) subst E. eapply typing_sub.
    + apply (IHtyping eq_refl F x0 y0 Ee Hstep).
    + exact H0.
  - discriminate Ee. - discriminate Ee. - discriminate Ee.
Qed.

Lemma typing_fold_step : forall F x y T,
  typing nil (exp_fold F x) T ->
  (forall A, typing nil x A -> typing nil y A) ->
  typing nil (exp_fold F y) T.
Proof. intros. exact (@typing_fold_step_gen nil (exp_fold F x) T H eq_refl F x y eq_refl H0). Qed.

Lemma typing_unfold_step_gen : forall E e T, typing E e T ->
  E = nil -> forall S0 x0 y0, e = exp_unfold S0 x0 ->
  (forall A, typing nil x0 A -> typing nil y0 A) ->
  typing nil (exp_unfold S0 y0) T.
Proof.
  intros E e T H. induction H; intros Enil S0 x0 y0 Ee Hstep.
  - discriminate Ee. - discriminate Ee. - discriminate Ee. - discriminate Ee. - discriminate Ee. - discriminate Ee. - discriminate Ee.
  - (* unfold *) injection Ee as HS He. subst S0. subst x0. subst G.
    simpl. eapply typing_unfold.
    + apply Hstep. exact H.
    + exact H0.
  - (* sub *) subst E. eapply typing_sub.
    + apply (IHtyping eq_refl S0 x0 y0 Ee Hstep).
    + exact H0.
  - discriminate Ee. - discriminate Ee. - discriminate Ee.
Qed.

Lemma typing_unfold_step : forall S x y T,
  typing nil (exp_unfold S x) T ->
  (forall A, typing nil x A -> typing nil y A) ->
  typing nil (exp_unfold S y) T.
Proof. intros. exact (@typing_unfold_step_gen nil (exp_unfold S x) T H eq_refl S x y eq_refl H0). Qed.

Lemma typing_proj_step_gen : forall E e T, typing E e T ->
  E = nil -> forall x0 y0 i0, e = exp_rcd_proj x0 i0 ->
  (forall A, typing nil x0 A -> typing nil y0 A) ->
  typing nil (exp_rcd_proj y0 i0) T.
Proof.
  intros E e T H. induction H; intros Enil x0 y0 i0 Ee Hstep.
  - discriminate Ee. - discriminate Ee. - discriminate Ee. - discriminate Ee. - discriminate Ee. - discriminate Ee. - discriminate Ee. - discriminate Ee.
  - (* sub *) subst E. eapply typing_sub.
    + apply (IHtyping eq_refl x0 y0 i0 Ee Hstep).
    + exact H0.
  - (* proj *) injection Ee as Hx Hi. subst x0. subst i0. subst G.
    simpl. eapply typing_proj.
    + apply Hstep. exact H.
    + exact H0.
  - discriminate Ee. - discriminate Ee.
Qed.

Lemma typing_proj_step : forall x y i T,
  typing nil (exp_rcd_proj x i) T ->
  (forall A, typing nil x A -> typing nil y A) ->
  typing nil (exp_rcd_proj y i) T.
Proof. intros. exact (@typing_proj_step_gen nil (exp_rcd_proj x i) T H eq_refl x y i eq_refl H0). Qed.

Lemma typing_rcd_head_step_gen : forall E e T, typing E e T ->
  E = nil -> forall i0 x0 z0 y0, e = exp_rcd_cons i0 x0 z0 ->
  (forall A, typing nil x0 A -> typing nil y0 A) ->
  typing nil (exp_rcd_cons i0 y0 z0) T.
Proof.
  intros E e T H. induction H; intros Enil i0 x0 z0 y0 Ee Hstep.
  - discriminate Ee. - discriminate Ee. - discriminate Ee. - discriminate Ee.
  - discriminate Ee. - discriminate Ee. - discriminate Ee. - discriminate Ee.
  - (* sub *) subst E. eapply typing_sub.
    + apply (IHtyping eq_refl i0 x0 z0 y0 Ee Hstep).
    + exact H0.
  - discriminate Ee. - discriminate Ee.
  - (* rcd_cons *) injection Ee as Hi Hx Hz. subst i0. subst x0. subst z0. subst G.
    simpl. eapply typing_rcd_cons.
    + apply Hstep. exact H.
    + exact H0. + exact H1. + exact H2. + exact H3.
Qed.

Lemma typing_rcd_head_step : forall i x z y T,
  typing nil (exp_rcd_cons i x z) T ->
  (forall A, typing nil x A -> typing nil y A) ->
  typing nil (exp_rcd_cons i y z) T.
Proof. intros. exact (@typing_rcd_head_step_gen nil (exp_rcd_cons i x z) T H eq_refl i x z y eq_refl H0). Qed.

Lemma typing_rcd_cons_step_gen : forall E e T, typing E e T ->
  E = nil -> forall i0 v1 x0 y0, e = exp_rcd_cons i0 v1 x0 ->
  (forall A, typing nil x0 A -> typing nil y0 A) ->
  rt_expr y0 -> i0 \notin collectLabele y0 ->
  typing nil (exp_rcd_cons i0 v1 y0) T.
Proof.
  intros E e T H. induction H; intros Enil i0 v1 x0 y0 Ee Hstep Hyrt Hlab.
  - discriminate Ee. - discriminate Ee. - discriminate Ee. - discriminate Ee.
  - discriminate Ee. - discriminate Ee. - discriminate Ee. - discriminate Ee.
  - (* sub *) subst E. eapply typing_sub.
    + apply (IHtyping eq_refl i0 v1 x0 y0 Ee Hstep Hyrt Hlab).
    + exact H0.
  - discriminate Ee. - discriminate Ee.
  - (* rcd_cons *) injection Ee as Hi Hv Hx. subst i0. subst v1. subst x0. subst G.
    simpl. eapply typing_rcd_cons.
    + exact H.
    + apply Hstep. exact H0.
    + exact H1. + exact Hyrt. + exact Hlab.
Qed.

Lemma typing_rcd_cons_step : forall i v x y T,
  typing nil (exp_rcd_cons i v x) T ->
  (forall A, typing nil x A -> typing nil y A) ->
  rt_expr y -> i \notin collectLabele y ->
  typing nil (exp_rcd_cons i v y) T.
Proof. intros. exact (@typing_rcd_cons_step_gen nil (exp_rcd_cons i v x) T H eq_refl i v x y eq_refl H0 H1 H2). Qed.

Lemma wf_env_binds_typ : forall E x T,
  wf_env E -> binds x (bind_typ T) E -> WF E T.
Proof.
  intros E x T Hwe. induction Hwe; intros Hb.
  - inversion Hb.
  - simpl in Hb. apply binds_cons_1 in Hb as [[Heq Hbeq]|Ht].
    + subst x. discriminate Hbeq.
    + apply (WF_binds_irrel (IHHwe Ht) (X ~ bind_sub T0 ++ E)
             (fun Z V Hbs => ex_intro (fun V' => binds Z (bind_sub V') (X ~ bind_sub T0 ++ E)) V (@binds_cons_any binding Z X (bind_sub V) (bind_sub T0) E Hbs))).
  - simpl in Hb. apply binds_cons_1 in Hb as [[Heq Hbeq]|Ht].
    + subst x. injection Hbeq as HT. subst T.
      eapply WF_binds_irrel; [exact H|].
      intros Z V Hbs. simpl. exists V. right. exact Hbs.
    + apply (WF_binds_irrel (IHHwe Ht) (x0 ~ bind_typ T0 ++ E)
             (fun Z V Hbs => ex_intro (fun V' => binds Z (bind_sub V') (x0 ~ bind_typ T0 ++ E)) V (@binds_cons_any binding Z x0 (bind_sub V) (bind_typ T0) E Hbs))).
Qed.

Fixpoint erase (X : atom) (W : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_top => typ_top
  | typ_nat => typ_nat
  | typ_bvar i => typ_bvar i
  | typ_fvar Y => if Y == X then W else typ_fvar Y
  | typ_arrow A B => typ_arrow (erase X W A) (erase X W B)
  | typ_all A B => typ_all (erase X W A) (erase X W B)
  | typ_mu A => typ_mu (erase X W A)
  | typ_label Y A => if Y == X then W else typ_label Y (erase X W A)
  | typ_rcd_nil => typ_rcd_nil
  | typ_rcd_cons i A B => typ_rcd_cons i (erase X W A) (erase X W B)
  end.

Definition erase_binding X W b :=
  match b with
  | bind_sub T => bind_sub (erase X W T)
  | bind_typ T => bind_typ (erase X W T)
  end.

Fixpoint erase_env X W E {struct E} : env :=
  match E with
  | nil => nil
  | (Y, b) :: E' =>
      if Y == X then erase_env X W E'
      else (Y, erase_binding X W b) :: erase_env X W E'
  end.

Lemma lc_tt_open_any_gen : forall k T, lc_tt k T ->
  forall K (L : typ), k <= K -> open_tt_rec K L T = T.
Proof.
  intros k T. revert k. induction T; intros k Hc K L Hle; simpl in *; try reflexivity.
  - (* bvar *) destruct (K === n) as [E|E]; [exfalso; lia|reflexivity].
  - (* arrow *) destruct Hc as [H1 H2]. rewrite (IHT1 k H1 K L Hle), (IHT2 k H2 K L Hle). reflexivity.
  - (* all *) destruct Hc as [H1 H2]. rewrite (IHT1 k H1 K L Hle), (IHT2 (S k) H2 (S K) L (le_n_S k K Hle)). reflexivity.
  - (* mu *) apply f_equal. apply (IHT (S k) Hc (S K) L (le_n_S k K Hle)).
  - (* label *) apply f_equal. apply (IHT k Hc K L Hle).
  - (* rcd_cons *) destruct Hc as [H1 H2]. rewrite (IHT1 k H1 K L Hle), (IHT2 k H2 K L Hle). reflexivity.
Qed.

Lemma lc_tt_open_any : forall T, lc_tt 0 T ->
  forall K (L : typ), open_tt_rec K L T = T.
Proof. intros. apply (@lc_tt_open_any_gen 0 T H K L). lia. Qed.

Lemma erase_id : forall X W T,
  X \notin fv_tt T -> X \notin fl_tt T -> erase X W T = T.
Proof.
  intros X W T. induction T; simpl; intros Hfv Hfl; try reflexivity.
  - (* fvar *) destruct (a == X) as [E|E].
    + exfalso. apply Hfv. apply AtomSetImpl.singleton_2. exact E.
    + simpl. reflexivity.
  - (* arrow *) apply notin_union_1 in Hfv as Hf1; apply notin_union_2 in Hfv as Hf2.
    apply notin_union_1 in Hfl as Hg1; apply notin_union_2 in Hfl as Hg2.
    rewrite (IHT1 Hf1 Hg1), (IHT2 Hf2 Hg2). reflexivity.
  - (* all *) apply notin_union_1 in Hfv as Hf1; apply notin_union_2 in Hfv as Hf2.
    apply notin_union_1 in Hfl as Hg1; apply notin_union_2 in Hfl as Hg2.
    rewrite (IHT1 Hf1 Hg1), (IHT2 Hf2 Hg2). reflexivity.
  - (* mu *) rewrite (IHT Hfv Hfl). reflexivity.
  - (* label *) destruct (a == X) as [E|E].
    + exfalso. apply notin_union_1 in Hfl as Hg1. exact (notin_singleton_1 a X Hg1 E).
    + apply notin_union_2 in Hfl as Hg2. simpl. rewrite (IHT Hfv Hg2). reflexivity.
  - (* rcd_cons *) apply notin_union_1 in Hfv as Hf1; apply notin_union_2 in Hfv as Hf2.
    apply notin_union_2 in Hfl as Hgtail.
    apply notin_union_1 in Hgtail as Hg1; apply notin_union_2 in Hgtail as Hg2.
    rewrite (IHT1 Hf1 Hg1), (IHT2 Hf2 Hg2). reflexivity.
Qed.

Lemma erase_open : forall X W K L T,
  lc_tt 0 W ->
  erase X W (open_tt_rec K L T) = open_tt_rec K (erase X W L) (erase X W T).
Proof.
  intros X W K L T Hc. revert K. induction T; simpl; intros K; try reflexivity.
  - (* bvar *) destruct (K === n); simpl; reflexivity.
  - (* fvar *) destruct (a == X) as [E|E]; simpl.
    + symmetry. apply lc_tt_open_any. exact Hc.
    + reflexivity.
  - (* arrow *) rewrite (IHT1 K), (IHT2 K). reflexivity.
  - (* all *) rewrite (IHT1 K), (IHT2 (S K)). reflexivity.
  - (* mu *) rewrite (IHT (S K)); reflexivity.
  - (* label *) destruct (a == X) as [E|E]; simpl.
    + symmetry. apply lc_tt_open_any. exact Hc.
    + rewrite IHT; reflexivity.
  - (* rcd_cons *) rewrite (IHT1 K), (IHT2 K). reflexivity.
Qed.

Lemma erase_env_cons_eq : forall X W (Y : atom) b E,
  Y = X -> erase_env X W ((Y, b) :: E) = erase_env X W E.
Proof.
  intros. subst Y. simpl. destruct (X == X) as [E1|E1]; [reflexivity|contradiction].
Qed.

Lemma erase_env_cons_neq : forall X W (Y : atom) b E,
  Y <> X -> erase_env X W ((Y, b) :: E) = (Y, erase_binding X W b) :: erase_env X W E.
Proof.
  intros. simpl. destruct (Y == X) as [E1|E1]; [exfalso; apply H; exact E1|reflexivity].
Qed.

Lemma notin_dom_erase : forall E X W (y : atom),
  y \notin dom E -> y \notin dom (erase_env X W E).
Proof.
  induction E as [| [Z b] E' IH]; intros X W y Hy; simpl in *.
  - apply notin_empty_1.
  - destruct (Z == X) as [E1|E1]; simpl in *.
    + apply IH. apply notin_add_2 in Hy. exact Hy.
    + apply notin_add_1 in Hy as Hne. apply notin_add_2 in Hy as Htail.
      apply notin_add_3; [exact Hne | apply IH; exact Htail].
Qed.

Lemma binds_erase : forall E (Y : atom) b,
  binds Y b E ->
  forall X W, Y <> X -> binds Y (erase_binding X W b) (erase_env X W E).
Proof.
  induction E as [| [Z c] E' IH]; intros Y b Hb X W Hne; simpl in *.
  - inversion Hb.
  - apply binds_cons_1 in Hb as [[Heq Hbeq]|Ht].
    + subst Y. subst b.
      destruct (Z == X) as [E1|E1].
      * exfalso. apply Hne. exact E1.
      * simpl. left. reflexivity.
    + destruct (Z == X) as [E1|E1]; simpl.
      * apply IH; assumption.
      * right. apply IH; assumption.
Qed.

Lemma wf_nil_any : forall E T, WF nil T -> WF E T.
Proof.
  intros E T H. apply (WF_binds_irrel H E).
  intros Z V Hb. inversion Hb.
Qed.

Lemma rt_type_erase : forall X W T, rt_type T -> rt_type (erase X W T).
Proof.
  intros X W T H. inversion H; subst; simpl.
  - apply rt_type_rcd_nil.
  - apply rt_type_rcd_cons.
Qed.

Lemma collectLabel_erase_rt : forall E T,
  WF E T -> rt_type T -> forall X W, collectLabel (erase X W T) = collectLabel T.
Proof.
  intros E T. revert E. induction T; intros E Hwf Hrt X W; simpl; try (inversion Hrt).
  - (* rcd_nil *) reflexivity.
  - (* rcd_cons *) inversion Hwf; subst.
    rewrite (IHT2 E H7 H8 X W). reflexivity.
Qed.

Lemma erase_fvar_neq : forall X W (Y : atom), Y <> X -> erase X W (typ_fvar Y) = typ_fvar Y.
Proof. intros. simpl. destruct (Y == X) as [E|E]; [exfalso; apply H; exact E|reflexivity]. Qed.

Lemma erase_label_neq : forall X W (Y : atom) T,
  Y <> X -> erase X W (typ_label Y T) = typ_label Y (erase X W T).
Proof. intros. simpl. destruct (Y == X) as [E|E]; [exfalso; apply H; exact E|reflexivity]. Qed.

Lemma wf_erase : forall E T, WF E T ->
  forall Xs Wt, WF nil Wt -> WF (erase_env Xs Wt E) (erase Xs Wt T).
Proof.
  intros E T H. induction H as
    [ E0
    | E0
    | U E0 X Hb
    | E0 A B w0 IH0 w1 IH1
    | L E0 T1 T2 w0 IH0 wbody IHbody
    | L E0 A w0 IH0 w1 IH1
    | E0 A X w0 IH0
    | E0
    | E0 i T1 T2 w0 IH0 w1 IH1 r n ];
    intros Xs Wt Hwnil.
  - simpl. apply WF_top.
  - simpl. apply WF_nat.
  - simpl. destruct (X == Xs) as [E1|E1].
    + subst X. apply wf_nil_any. exact Hwnil.
    + eapply WF_var. exact (@binds_erase E0 X (bind_sub U) Hb Xs Wt E1).
  - simpl. apply WF_arrow; [apply IH0|apply IH1]; exact Hwnil.
  - simpl. apply WF_all with (L := L \u {{Xs}}).
    + apply IH0. exact Hwnil.
    + intros Y HY. assert (HYL : Y \notin L) by fsetdec.
      assert (HYX : Y <> Xs) by fsetdec.
      pose proof (IHbody Y HYL Xs Wt Hwnil) as Hres.
      change (WF (erase_env Xs Wt ((Y, bind_sub T1) :: E0))
                (erase Xs Wt (open_tt T2 Y))) in Hres.
      rewrite (@erase_env_cons_neq Xs Wt Y (bind_sub T1) E0 HYX) in Hres.
      unfold open_tt in Hres.
      rewrite (@erase_open Xs Wt 0 (typ_fvar Y) T2 (wf_lc_tt Hwnil)) in Hres.
      rewrite (@erase_fvar_neq Xs Wt Y HYX) in Hres.
      exact Hres.
  - simpl. apply WF_rec with (L := L \u {{Xs}}).
    + intros Y HY. assert (HYL : Y \notin L) by fsetdec.
      assert (HYX : Y <> Xs) by fsetdec.
      pose proof (IH0 Y HYL Xs Wt Hwnil) as Hres.
      change (WF (erase_env Xs Wt ((Y, bind_sub typ_top) :: E0))
                (erase Xs Wt (open_tt A Y))) in Hres.
      rewrite (@erase_env_cons_neq Xs Wt Y (bind_sub typ_top) E0 HYX) in Hres.
      unfold open_tt in Hres.
      rewrite (@erase_open Xs Wt 0 (typ_fvar Y) A (wf_lc_tt Hwnil)) in Hres.
      rewrite (@erase_fvar_neq Xs Wt Y HYX) in Hres.
      exact Hres.
    + intros Y HY. assert (HYL : Y \notin L) by fsetdec.
      assert (HYX : Y <> Xs) by fsetdec.
      pose proof (IH1 Y HYL Xs Wt Hwnil) as Hres.
      change (WF (erase_env Xs Wt ((Y, bind_sub typ_top) :: E0))
                (erase Xs Wt (open_tt_rec 0 (typ_label Y (open_tt_rec 0 (typ_fvar Y) A)) A))) in Hres.
      rewrite (@erase_env_cons_neq Xs Wt Y (bind_sub typ_top) E0 HYX) in Hres.
      rewrite (@erase_open Xs Wt 0 (typ_label Y (open_tt_rec 0 (typ_fvar Y) A)) A (wf_lc_tt Hwnil)) in Hres.
      rewrite (@erase_label_neq Xs Wt Y (open_tt_rec 0 (typ_fvar Y) A) HYX) in Hres.
      rewrite (@erase_open Xs Wt 0 (typ_fvar Y) A (wf_lc_tt Hwnil)) in Hres.
      rewrite (@erase_fvar_neq Xs Wt Y HYX) in Hres.
      exact Hres.
  - simpl. destruct (X == Xs) as [E1|E1].
    + subst X. apply wf_nil_any. exact Hwnil.
    + eapply WF_label. apply IH0. exact Hwnil.
  - simpl. apply WF_rcd_nil.
  - simpl. apply WF_rcd_cons.
    + apply IH0. exact Hwnil.
    + apply IH1. exact Hwnil.
    + apply rt_type_erase. exact r.
    + rewrite (@collectLabel_erase_rt E0 T2 w1 r Xs Wt). exact n.
Qed.

Lemma wf_env_erase : forall E, wf_env E ->
  forall Xs Wt, WF nil Wt -> wf_env (erase_env Xs Wt E).
Proof.
  intros E Hwe. induction Hwe; intros Xs Wt Hwnil.
  - simpl. apply wf_env_empty.
  - (* bind_sub *) simpl. destruct (X == Xs) as [E1|E1].
    + subst X. simpl. apply IHHwe. exact Hwnil.
    + simpl. apply wf_env_sub.
      * apply IHHwe. exact Hwnil.
      * exact (@wf_erase E T H Xs Wt Hwnil).
      * apply notin_dom_erase. exact H0.
  - (* bind_typ *) simpl. destruct (x == Xs) as [E1|E1].
    + subst x. simpl. apply IHHwe. exact Hwnil.
    + simpl. apply wf_env_typ.
      * apply IHHwe. exact Hwnil.
      * exact (@wf_erase E T H Xs Wt Hwnil).
      * apply notin_dom_erase. exact H0.
Qed.

Lemma Tlookup_erase_rt_wf : forall E T, WF E T -> rt_type T ->
  forall Xs Wt i,
    Tlookup i (erase Xs Wt T) = option_map (erase Xs Wt) (Tlookup i T).
Proof.
  intros E T. revert E. induction T; intros E Hwf Hrt Xs Wt i; simpl; try (inversion Hrt).
  - (* rcd_nil *) reflexivity.
  - (* rcd_cons *) inversion Hwf; subst. simpl.
    destruct (a == i) as [E1|E1]; simpl.
    + reflexivity.
    + apply (IHT2 E H7 H8 Xs Wt i).
Qed.

Lemma sub_top_inv : forall E T, sub E typ_top T -> T = typ_top.
Proof.
  intros E T H. inversion H; subst; try discriminate; try reflexivity;
  try (exfalso; match goal with
       | Hr : rt_type typ_top |- _ => inversion Hr
       | Hb : binds _ (bind_sub _) _ |- _ => inversion Hb
       end).
Qed.

Lemma erase_fvar_eq : forall X W, erase X W (typ_fvar X) = W.
Proof. intros. simpl. destruct (X == X) as [E|E]; [reflexivity|contradiction]. Qed.

Lemma erase_label_eq : forall X W T, erase X W (typ_label X T) = W.
Proof. intros. simpl. destruct (X == X) as [E|E]; [reflexivity|contradiction]. Qed.

Lemma sub_erase : forall E, wf_env E -> forall Xs,
  binds Xs (bind_sub typ_top) E ->
  forall A B, sub E A B ->
  forall Wt, WF nil Wt ->
  sub (erase_env Xs Wt E) (erase Xs Wt A) (erase Xs Wt B).
Proof.
  intros E Hwe Xs Hb A B H. induction H; intros Wt Hwnil.
  - (* nat *) simpl. apply sa_nat. apply (@wf_env_erase E Hwe Xs Wt Hwnil).
  - (* fvar *) destruct (X == Xs) as [E1|E1].
    + subst X. rewrite erase_fvar_eq.
      apply sub_refl; [apply (@wf_env_erase E Hwe Xs Wt Hwnil)|apply wf_nil_any; exact Hwnil].
    + rewrite (@erase_fvar_neq Xs Wt X E1).
      apply sa_fvar.
      * apply (@wf_env_erase E Hwe Xs Wt Hwnil).
      * pose proof (@wf_erase E (typ_fvar X) H0 Xs Wt Hwnil) as HwfE.
        rewrite (@erase_fvar_neq Xs Wt X E1) in HwfE. exact HwfE.
  - (* top *) simpl. apply sa_top.
    + apply (@wf_env_erase E Hwe Xs Wt Hwnil).
    + apply (@wf_erase E A H0 Xs Wt Hwnil).
  - (* trans_tvar *) destruct (X == Xs) as [E1|E1].
    + subst X. assert (Heq : bind_sub U = bind_sub typ_top) by (eapply binds_unique; eauto using wf_env_uniq).
      injection Heq as HU. subst U. rewrite (sub_top_inv H0). rewrite erase_fvar_eq. simpl.
      apply sa_top.
      * apply (@wf_env_erase E Hwe Xs Wt Hwnil).
      * apply wf_nil_any. exact Hwnil.
    + rewrite (@erase_fvar_neq Xs Wt X E1).
      eapply sa_trans_tvar.
      * apply (@binds_erase E X (bind_sub U) H Xs Wt E1).
      * apply (IHsub Hwe Hb Wt Hwnil).
  - (* arrow *) simpl. apply sa_arrow; [apply (IHsub1 Hwe Hb Wt Hwnil)|apply (IHsub2 Hwe Hb Wt Hwnil)].
  - (* all *) simpl. apply sa_all with (L := L \u dom E \u {{Xs}}).
    + apply (IHsub1 Hwe Hb Wt Hwnil).
    + apply (IHsub2 Hwe Hb Wt Hwnil).
    + intros Y HY. assert (HYL : Y \notin L) by fsetdec.
      assert (HYd : Y \notin dom E) by fsetdec.
      assert (HYX : Y <> Xs) by fsetdec.
      assert (HwfS2 : WF E S2) by (apply (proj2 (sub_wf H))).
      assert (HweY : wf_env (Y ~ bind_sub S2 ++ E)) by (apply wf_env_sub; assumption).
      assert (HbY : binds Xs (bind_sub typ_top) (Y ~ bind_sub S2 ++ E)) by (apply binds_cons; exact Hb).
      pose proof (H2 Y HYL HweY HbY Wt Hwnil) as Hres.
      change (sub (erase_env Xs Wt ((Y, bind_sub S2) :: E))
                 (erase Xs Wt (open_tt T1 Y)) (erase Xs Wt (open_tt T2 Y))) in Hres.
      rewrite (@erase_env_cons_neq Xs Wt Y (bind_sub S2) E HYX) in Hres.
      unfold open_tt in Hres |- *.
      rewrite (@erase_open Xs Wt 0 (typ_fvar Y) T1 (wf_lc_tt Hwnil)) in Hres.
      rewrite (@erase_open Xs Wt 0 (typ_fvar Y) T2 (wf_lc_tt Hwnil)) in Hres.
      rewrite (@erase_fvar_neq Xs Wt Y HYX) in Hres.
      exact Hres.
  - (* rec *) simpl. apply sa_rec with (L := L \u dom E \u {{Xs}}).
    + intros Y HY. assert (HYL : Y \notin L) by fsetdec.
      assert (HYd : Y \notin dom E) by fsetdec.
      assert (HYX : Y <> Xs) by fsetdec.
      pose proof (@wf_erase (Y ~ bind_sub typ_top ++ E) (open_tt A1 Y) (H Y HYL) Xs Wt Hwnil) as Hres.
      change (WF (erase_env Xs Wt ((Y, bind_sub typ_top) :: E))
                (erase Xs Wt (open_tt A1 Y))) in Hres.
      rewrite (@erase_env_cons_neq Xs Wt Y (bind_sub typ_top) E HYX) in Hres.
      unfold open_tt in Hres |- *.
      rewrite (@erase_open Xs Wt 0 (typ_fvar Y) A1 (wf_lc_tt Hwnil)) in Hres.
      rewrite (@erase_fvar_neq Xs Wt Y HYX) in Hres.
      exact Hres.
    + intros Y HY. assert (HYL : Y \notin L) by fsetdec.
      assert (HYd : Y \notin dom E) by fsetdec.
      assert (HYX : Y <> Xs) by fsetdec.
      pose proof (@wf_erase (Y ~ bind_sub typ_top ++ E) (open_tt A2 Y) (H0 Y HYL) Xs Wt Hwnil) as Hres.
      change (WF (erase_env Xs Wt ((Y, bind_sub typ_top) :: E))
                (erase Xs Wt (open_tt A2 Y))) in Hres.
      rewrite (@erase_env_cons_neq Xs Wt Y (bind_sub typ_top) E HYX) in Hres.
      unfold open_tt in Hres |- *.
      rewrite (@erase_open Xs Wt 0 (typ_fvar Y) A2 (wf_lc_tt Hwnil)) in Hres.
      rewrite (@erase_fvar_neq Xs Wt Y HYX) in Hres.
      exact Hres.
    + intros Y HY. assert (HYL : Y \notin L) by fsetdec.
      assert (HYd : Y \notin dom E) by fsetdec.
      assert (HYX : Y <> Xs) by fsetdec.
      assert (HweY : wf_env (Y ~ bind_sub typ_top ++ E)) by (apply wf_env_sub; [exact Hwe|apply WF_top|exact HYd]).
      assert (HbY : binds Xs (bind_sub typ_top) (Y ~ bind_sub typ_top ++ E)) by (apply binds_cons; exact Hb).
      pose proof (H2 Y HYL HweY HbY Wt Hwnil) as Hres.
      change (sub (erase_env Xs Wt ((Y, bind_sub typ_top) :: E))
                 (erase Xs Wt (open_tt_rec 0 (typ_label Y (open_tt_rec 0 (typ_fvar Y) A1)) A1))
                 (erase Xs Wt (open_tt_rec 0 (typ_label Y (open_tt_rec 0 (typ_fvar Y) A2)) A2))) in Hres.
      rewrite (@erase_env_cons_neq Xs Wt Y (bind_sub typ_top) E HYX) in Hres.
      rewrite (@erase_open Xs Wt 0 (typ_label Y (open_tt_rec 0 (typ_fvar Y) A1)) A1 (wf_lc_tt Hwnil)) in Hres.
      rewrite (@erase_open Xs Wt 0 (typ_label Y (open_tt_rec 0 (typ_fvar Y) A2)) A2 (wf_lc_tt Hwnil)) in Hres.
      rewrite (@erase_label_neq Xs Wt Y (open_tt_rec 0 (typ_fvar Y) A1) HYX) in Hres.
      rewrite (@erase_label_neq Xs Wt Y (open_tt_rec 0 (typ_fvar Y) A2) HYX) in Hres.
      rewrite (@erase_open Xs Wt 0 (typ_fvar Y) A1 (wf_lc_tt Hwnil)) in Hres.
      rewrite (@erase_open Xs Wt 0 (typ_fvar Y) A2 (wf_lc_tt Hwnil)) in Hres.
      rewrite (@erase_fvar_neq Xs Wt Y HYX) in Hres.
      exact Hres.
  - (* label *) destruct (X == Xs) as [E1|E1].
    + subst X. rewrite erase_label_eq. rewrite erase_label_eq.
      apply sub_refl; [apply (@wf_env_erase E Hwe Xs Wt Hwnil)|apply wf_nil_any; exact Hwnil].
    + rewrite (@erase_label_neq Xs Wt X A E1).
      rewrite (@erase_label_neq Xs Wt X B E1).
      apply sa_label. apply (IHsub Hwe Hb Wt Hwnil).
  - (* rcd *) simpl. apply sa_rcd with (A1 := erase Xs Wt A1) (A2 := erase Xs Wt A2).
    + apply (@wf_env_erase E Hwe Xs Wt Hwnil).
    + apply rt_type_erase. exact H0.
    + apply rt_type_erase. exact H1.
    + rewrite (@collectLabel_erase_rt E A2 H4 H1 Xs Wt).
      rewrite (@collectLabel_erase_rt E A1 H3 H0 Xs Wt). exact H2.
    + apply (@wf_erase E A1 H3 Xs Wt Hwnil).
    + apply (@wf_erase E A2 H4 Xs Wt Hwnil).
    + intros i t1 t2 Hl1 Hl2.
      rewrite (@Tlookup_erase_rt_wf E A1 H3 H0 Xs Wt i) in Hl1.
      rewrite (@Tlookup_erase_rt_wf E A2 H4 H1 Xs Wt i) in Hl2.
      destruct (Tlookup i A1) as [u1|] eqn:Lu1; [|discriminate Hl1].
      destruct (Tlookup i A2) as [u2|] eqn:Lu2; [|discriminate Hl2].
      simpl in Hl1, Hl2. injection Hl1 as Ht1. injection Hl2 as Ht2. subst t1 t2.
      apply (H6 i u1 u2 Lu1 Lu2 Hwe Hb Wt Hwnil).
Qed.

Lemma sub_unroll_same : forall (A B : typ) (X : atom) (W : typ),
  X \notin fv_tt A -> X \notin fl_tt A ->
  X \notin fv_tt B -> X \notin fl_tt B ->
  WF nil W ->
  sub (X ~ bind_sub typ_top ++ nil)
      (open_tt A (typ_label X (open_tt A X)))
      (open_tt B (typ_label X (open_tt B X))) ->
  sub nil (open_tt A W) (open_tt B W).
Proof.
  intros A B X W HfvA HflA HfvB HflB Hwnil Hk.
  assert (Hwe : wf_env (X ~ bind_sub typ_top ++ nil)).
  { apply wf_env_sub.
    - apply wf_env_empty.
    - apply WF_top.
    - apply notin_empty_1. }
  assert (Hbind : binds X (bind_sub typ_top) (X ~ bind_sub typ_top ++ nil)).
  { simpl. left. reflexivity. }
  pose proof (@sub_erase (X ~ bind_sub typ_top ++ nil) Hwe X Hbind
     (open_tt A (typ_label X (open_tt A X)))
     (open_tt B (typ_label X (open_tt B X))) Hk W Hwnil) as Hres.
  assert (Heenv : erase_env X W (X ~ bind_sub typ_top ++ nil) = nil).
  { change (erase_env X W ((X, bind_sub typ_top) :: nil) = nil).
    rewrite erase_env_cons_eq with (Y := X) (b := bind_sub typ_top) (E := nil) by reflexivity.
    reflexivity. }
  rewrite Heenv in Hres.
  unfold open_tt in Hres.
  rewrite (@erase_open X W 0 (typ_label X (open_tt_rec 0 X A)) A (wf_lc_tt Hwnil)) in Hres.
  rewrite (@erase_open X W 0 (typ_label X (open_tt_rec 0 X B)) B (wf_lc_tt Hwnil)) in Hres.
  rewrite erase_label_eq in Hres.
  rewrite erase_label_eq in Hres.
  rewrite (@erase_id X W A HfvA HflA) in Hres.
  rewrite (@erase_id X W B HfvB HflB) in Hres.
  unfold open_tt in *. exact Hres.
Qed.

Lemma lookup_some_in_collect : forall T i Ti,
  Tlookup i T = Some Ti -> i \in collectLabel T.
Proof.
  intros T. induction T; intros i Ti H; simpl in *; try discriminate.
  - (* rcd_cons *)
    destruct (a == i) as [E|E]; subst; simpl in *.
    + injection H as H. subst Ti.
      apply AtomSetImpl.union_2. apply AtomSetImpl.singleton_2. reflexivity.
    + apply AtomSetImpl.union_3. exact (IHT2 i Ti H).
Qed.

Lemma collect_lookup_some : forall T i,
  i \in collectLabel T -> exists Ti, Tlookup i T = Some Ti.
Proof.
  intros T. induction T; intros i H; simpl in *;
    try (exfalso; apply (notin_empty_1 i); exact H).
  - (* rcd_cons *)
    apply AtomSetImpl.union_1 in H as [H|H].
    + apply AtomSetImpl.singleton_1 in H. subst i.
      exists T1. simpl. destruct (a == a) as [E|E]; [reflexivity|contradiction].
    + destruct (a == i) as [E|E].
      * exists T1. simpl. destruct (a == i) as [E'|E']; [reflexivity|contradiction].
      * apply IHT2 in H as [Ti Hi]. exists Ti. simpl.
        destruct (a == i) as [E'|E']; [contradiction|exact Hi].
Qed.

Lemma lookup_subset : forall S T i Ti,
  collectLabel T [<=] collectLabel S ->
  Tlookup i T = Some Ti ->
  exists Si, Tlookup i S = Some Si.
Proof.
  intros S T i Ti Hsub Hl.
  assert (Hin : i \in collectLabel T) by (exact (@lookup_some_in_collect T i Ti Hl)).
  apply Hsub in Hin.
  apply collect_lookup_some. exact Hin.
Qed.

Lemma sub_rcd_inv_nil : forall S T i Ti,
  sub nil S T ->
  Tlookup i T = Some Ti ->
  exists Si, Tlookup i S = Some Si /\ sub nil Si Ti.
Proof.
  intros S T i Ti H Hl. inversion H; subst;
    try (simpl in Hl; discriminate).
  - (* trans_tvar *) inversion H0.
  - (* rcd *)
    destruct (@lookup_subset S T i Ti H3 Hl) as [Si HSi].
    exists Si. split; [exact HSi|].
    exact (H6 i Si Ti HSi Hl).
Qed.

Lemma typing_tlookup : forall E e T, typing E e T -> E = nil ->
  forall idx Ty, Tlookup idx T = Some Ty ->
  forall val, tlookup idx e = Some val -> typing nil val Ty.
Proof.
  intros E e T H. induction H; intros Enil idx Ty Hl val Ht; subst.
  - (* nat *) simpl in Ht. discriminate.
  - (* var *) simpl in H0. inversion H0.
  - (* abs *) simpl in Ht. discriminate.
  - (* app *) simpl in Ht. discriminate.
  - (* tabs *) simpl in Ht. discriminate.
  - (* tapp *) simpl in Ht. discriminate.
  - (* fold *) simpl in Ht. discriminate.
  - (* unfold *) simpl in Ht. discriminate.
  - (* sub *) simpl in Ht.
    destruct (@sub_rcd_inv_nil S T idx Ty H0 Hl) as [Si HSi].
    destruct HSi as [HSi Hsubi].
    eapply typing_sub.
    + apply (IHtyping eq_refl idx Si HSi val Ht).
    + exact Hsubi.
  - (* proj *) simpl in Ht. discriminate.
  - (* rcd_nil *) simpl in Ht. discriminate.
  - (* rcd_cons *) simpl in Hl, Ht.
    destruct (i == idx) as [E|E].
    + injection Hl as Hl. injection Ht as Ht. subst Ty. subst val.
      exact H.
    + exact (IHtyping2 eq_refl idx Ty Hl val Ht).
Qed.

Lemma typing_proj_lookup : forall E e T, typing E e T -> E = nil ->
  forall (x0 : exp) (i0 : atom) (v0 : exp),
    e = exp_rcd_proj x0 i0 -> tlookup i0 x0 = Some v0 ->
    typing nil v0 T.
Proof.
  intros E e T H. induction H; intros Enil x0 i0 v0 Ee Hlook; subst;
    try discriminate Ee.
  - (* sub *)
    eapply typing_sub.
    + apply (IHtyping eq_refl x0 i0 v0 eq_refl Hlook).
    + exact H0.
  - (* proj *)
    injection Ee as He Hi. subst x0. subst i0.
    exact (@typing_tlookup nil e T H eq_refl i Ti H0 v0 Hlook).
Qed.

Lemma typing_beta_step_gen : forall E e T, typing E e T ->
  E = nil -> forall V0 x0 y0, e = exp_app (exp_abs V0 x0) y0 ->
  typing nil (open_ee x0 y0) T.
Proof.
  intros E e T H. induction H; intros Enil V0 x0 y0 Ee.
  - discriminate Ee. - discriminate Ee. - discriminate Ee.
  - (* app *) injection Ee as He1 He2. subst e1. subst e2. subst E.
    simpl. eapply preservation_beta.
    + exact H.
    + exact H0.
  - discriminate Ee. - discriminate Ee. - discriminate Ee. - discriminate Ee.
  - (* sub *) subst E. eapply typing_sub.
    + apply (IHtyping eq_refl V0 x0 y0 Ee).
    + exact H0.
  - discriminate Ee. - discriminate Ee. - discriminate Ee.
Qed.

Lemma typing_beta_step : forall V0 x0 y0 T,
  typing nil (exp_app (exp_abs V0 x0) y0) T ->
  typing nil (open_ee x0 y0) T.
Proof.
  intros. exact (@typing_beta_step_gen nil (exp_app (exp_abs V0 x0) y0) T H eq_refl V0 x0 y0 eq_refl).
Qed.

Lemma preservation_projrcd : forall e i vi T,
  typing nil (exp_rcd_proj e i) T ->
  tlookup i e = Some vi ->
  typing nil vi T.
Proof.
  intros e i vi T H Hlook.
  exact (@typing_proj_lookup nil (exp_rcd_proj e i) T H eq_refl e i vi eq_refl Hlook).
Qed.

Lemma subset_refl : forall (S : atoms), S [<=] S.
Proof. intros S x Hx. exact Hx. Qed.

Lemma subset_trans : forall (S T U : atoms),
  S [<=] T -> T [<=] U -> S [<=] U.
Proof. intros S T U H1 H2 x Hx. apply H2. apply H1. exact Hx. Qed.

Lemma subset_notin : forall (S T : atoms) (x : atom),
  S [<=] T -> x \notin T -> x \notin S.
Proof. intros S T x Hsub Hn Hx. apply Hn. apply Hsub. exact Hx. Qed.

Lemma rt_expr_step : forall e e', rt_expr e -> step e e' -> rt_expr e'.
Proof.
  intros e e' Hrt Hstep. inversion Hrt; subst.
  - inversion Hstep.
  - inversion Hstep; subst; apply rt_expr_rcd_cons.
Qed.

Inductive sub_chain : env -> typ -> typ -> Prop :=
  | sc_refl : forall E T, sub_chain E T T
  | sc_step : forall E S T U, sub E S T -> sub_chain E T U -> sub_chain E S U.

Lemma sub_chain_from_top : forall E U, sub_chain E typ_top U -> U = typ_top.
Proof.
  intros E U H. remember typ_top as S eqn:HS. revert HS.
  induction H; intros HS.
  - reflexivity.
  - subst S.
    assert (HT : T = typ_top) by (eapply sub_top_inv; eassumption).
    subst T. apply IHsub_chain. reflexivity.
Qed.

Lemma sub_record_labels : forall E S T,
  rt_type S -> sub E S T -> rt_type T ->
  collectLabel T [<=] collectLabel S.
Proof.
  intros E S T HrtS Hsub HrtT.
  inversion Hsub; subst.
  - inversion HrtS.
  - inversion HrtS.
  - inversion HrtT.
  - inversion HrtS.
  - inversion HrtS.
  - inversion HrtS.
  - inversion HrtS.
  - inversion HrtS.
  - assumption.
Qed.

Lemma sub_record_rt : forall E S T,
  rt_type S -> sub E S T -> rt_type T \/ T = typ_top.
Proof.
  intros E S T HrtS Hsub.
  inversion Hsub; subst.
  - inversion HrtS.
  - inversion HrtS.
  - right. reflexivity.
  - inversion HrtS.
  - inversion HrtS.
  - inversion HrtS.
  - inversion HrtS.
  - inversion HrtS.
  - left. eassumption.
Qed.

Lemma sub_chain_rt_labels : forall E S T,
  rt_type S -> sub_chain E S T -> rt_type T ->
  collectLabel T [<=] collectLabel S.
Proof.
  intros E S T HrtS Hch. induction Hch; intros HrtT.
  - apply subset_refl.
  - destruct (@sub_record_rt E S T HrtS H) as [HrtT0|Htop].
    + eapply subset_trans.
      * apply (IHHch HrtT0 HrtT).
      * apply (@sub_record_labels E S T HrtS H HrtT0).
    + subst T. exfalso.
      pose proof (@sub_chain_from_top E U Hch) as Heq. subst U.
      inversion HrtT.
Qed.

Lemma typing_collect_chain : forall E e T, typing E e T -> rt_expr e ->
  forall U, sub_chain E T U -> rt_type U -> collectLabel U [<=] collectLabele e.
Proof.
  intros E e T H. induction H; intros Hrt U Hch HrtU.
  - (* nat *) inversion Hrt.
  - (* var *) inversion Hrt.
  - (* abs *) inversion Hrt.
  - (* app *) inversion Hrt.
  - (* tabs *) inversion Hrt.
  - (* tapp *) inversion Hrt.
  - (* fold *) inversion Hrt.
  - (* unfold *) inversion Hrt.
  - (* sub *) eapply IHtyping; [exact Hrt| |exact HrtU].
    apply sc_step with (T := T); assumption.
  - (* proj *) inversion Hrt.
  - (* rcd_nil *)
    assert (Hl : collectLabel U [<=] collectLabel typ_rcd_nil).
    { apply (sub_chain_rt_labels (rt_type_rcd_nil) Hch HrtU). }
    simpl in Hl. simpl. exact Hl.
  - (* rcd_cons *)
    assert (HrtT : rt_type (typ_rcd_cons i T1 T2)) by apply rt_type_rcd_cons.
    assert (Hl : collectLabel U [<=] collectLabel (typ_rcd_cons i T1 T2)).
    { apply (sub_chain_rt_labels HrtT Hch HrtU). }
    simpl in Hl. simpl.
    eapply subset_trans; [exact Hl|].
    intros x Hx. apply AtomSetImpl.union_1 in Hx as [Hj|Hx].
    + apply AtomSetImpl.union_2. exact Hj.
    + apply AtomSetImpl.union_3.
      apply (IHtyping2 H2 T2 (sc_refl G T2) H1). exact Hx.
Qed.

Lemma collectLabele_step_rt : forall E x S,
  typing E x S -> rt_expr x ->
  forall y, step x y -> collectLabele y = collectLabele x.
Proof.
  intros E x S H. induction H; intros Hrt y Hstep.
  - (* nat *) inversion Hrt.
  - (* var *) inversion Hrt.
  - (* abs *) inversion Hrt.
  - (* app *) inversion Hrt.
  - (* tabs *) inversion Hrt.
  - (* tapp *) inversion Hrt.
  - (* fold *) inversion Hrt.
  - (* unfold *) inversion Hrt.
  - (* sub *) apply IHtyping; assumption.
  - (* proj *) inversion Hrt.
  - (* rcd_nil *) inversion Hstep.
  - (* rcd_cons *) inversion Hstep; subst.
    + simpl. reflexivity.
    + simpl. rewrite (IHtyping2 H2 e3 H9). reflexivity.
Qed.

Lemma typing_rcd_cons_step2 : forall E ee T, typing E ee T -> E = nil ->
  forall i v x y,
    ee = exp_rcd_cons i v x ->
    (forall A, typing nil x A -> typing nil y A) ->
    rt_expr x -> step x y ->
    typing nil (exp_rcd_cons i v y) T.
Proof.
  intros E ee T H. induction H; intros Enil i0 v0 x0 y0 Ee Hcb Hrtx Hstep; subst;
    try discriminate Ee.
  - (* sub *) eapply typing_sub.
    + apply (IHtyping eq_refl i0 v0 x0 y0 eq_refl Hcb Hrtx Hstep).
    + exact H0.
  - (* rcd_cons *) injection Ee as Hi Hv Hx. subst i0. subst v0. subst x0.
    assert (Hrty : rt_expr y0) by (eapply rt_expr_step; eassumption).
    assert (HyEq : collectLabele y0 = collectLabele e2)
      by (eapply collectLabele_step_rt; [exact H0|exact H2|exact Hstep]).
    assert (HnotY : i \notin collectLabele y0) by (rewrite HyEq; exact H3).
    eapply typing_rcd_cons.
    + exact H.
    + apply Hcb. exact H0.
    + exact H1.
    + exact Hrty.
    + exact HnotY.
Qed.

Lemma typing_rcd_cons_tail_rt : forall E e T, typing E e T ->
  forall i v x, e = exp_rcd_cons i v x -> rt_expr x.
Proof.
  intros E e T H. induction H; intros i0 v0 x0 Ee; try discriminate Ee.
  - (* sub *) apply (IHtyping i0 v0 x0 Ee).
  - (* rcd_cons *) injection Ee as Hi Hv Hx. subst x0. exact H2.
Qed.

Lemma sub_left_mu_or_top : forall E A T,
  sub E (typ_mu A) T -> T = typ_top \/ exists T1, T = typ_mu T1.
Proof.
  intros E A T H. inversion H; subst; eauto;
    try (exfalso; match goal with
         | Hr : rt_type (typ_mu _) |- _ => inversion Hr
         | He : typ_mu _ = typ_arrow _ _ |- _ => discriminate He
         | He : typ_mu _ = typ_all _ _ |- _ => discriminate He
         | He : typ_mu _ = typ_label _ _ |- _ => discriminate He
         | He : typ_mu _ = typ_fvar _ |- _ => discriminate He
         | He : typ_mu _ = typ_nat |- _ => discriminate He
         | He : typ_mu _ = typ_rcd_nil |- _ => discriminate He
         | He : typ_mu _ = typ_rcd_cons _ _ _ |- _ => discriminate He
         end).
Qed.

Lemma sub_nil_mu_left : forall T B,
  sub nil T (typ_mu B) -> exists F1, T = typ_mu F1.
Proof.
  intros T B H. dependent destruction H; eauto;
    try (exfalso; match goal with
         | H : binds _ (bind_sub _) nil |- _ => inversion H
         | H : rt_type (typ_mu _) |- _ => inversion H
         | H : typ_mu _ = typ_top |- _ => discriminate H
         | H : typ_mu _ = typ_arrow _ _ |- _ => discriminate H
         | H : typ_mu _ = typ_all _ _ |- _ => discriminate H
         | H : typ_mu _ = typ_label _ _ |- _ => discriminate H
         | H : typ_mu _ = typ_fvar _ |- _ => discriminate H
         | H : typ_mu _ = typ_nat |- _ => discriminate H
         end).
Qed.

Lemma type_lc_tt : forall T, type T -> lc_tt 0 T.
Proof.
  intros T H. induction H.
  - (* top *) simpl. exact I.
  - (* nat *) simpl. exact I.
  - (* var *) simpl. exact I.
  - (* arrow *) simpl. split; assumption.
  - (* mu *) simpl.
    destruct (atom_fresh L) as [X HX].
    apply (@lc_tt_open_inv_same 0 X T).
    apply (H0 X HX).
  - (* all *) simpl. split.
    + exact IHtype.
    + destruct (atom_fresh L) as [X HX].
      apply (@lc_tt_open_inv_same 0 X T2).
      apply (H1 X HX).
  - (* label *) simpl. exact IHtype.
  - (* rcd_nil *) simpl. exact I.
  - (* rcd_cons *) simpl. split; assumption.
Qed.

Definition subst_binding (X : atom) (U : typ) (b : binding) : binding :=
  match b with
  | bind_sub T => bind_sub (subst_tt X U T)
  | bind_typ T => bind_typ (subst_tt X U T)
  end.

Fixpoint subst_env (X : atom) (U : typ) (E : env) {struct E} : env :=
  match E with
  | nil => nil
  | (Y, b) :: E' =>
      if Y == X then subst_env X U E'
      else (Y, subst_binding X U b) :: subst_env X U E'
  end.

Lemma subst_env_app : forall X U E1 E2,
  subst_env X U (E1 ++ E2) = subst_env X U E1 ++ subst_env X U E2.
Proof.
  intros X U E1. induction E1 as [|[Y b] E1 IH]; intros E2; simpl.
  - reflexivity.
  - destruct (Y == X) as [e|e]; simpl; rewrite IH; reflexivity.
Qed.

Lemma subst_env_dist : forall X U b,
  subst_env X U ((X, b) :: nil) = nil.
Proof.
  intros. simpl. destruct (X == X) as [e|e]; [reflexivity|contradiction].
Qed.

Lemma subst_env_cons_neq : forall X U (Y : atom) b E,
  Y <> X -> subst_env X U ((Y, b) :: E) = (Y, subst_binding X U b) :: subst_env X U E.
Proof.
  intros. simpl. destruct (Y == X) as [e|e]; [exfalso; apply H; exact e|reflexivity].
Qed.

Lemma subst_env_cons_eq : forall X U (Y : atom) b E,
  Y = X -> subst_env X U ((Y, b) :: E) = subst_env X U E.
Proof.
  intros. subst Y. simpl. destruct (X == X) as [e|e]; [reflexivity|contradiction].
Qed.

Lemma neq_of_notin_singleton : forall x y,
  x \notin {{y}} -> x <> y.
Proof.
  intros x y H He. apply (notin_singleton_1 y x H). symmetry. exact He.
Qed.

Lemma notin_union_both : forall (x : atom) (S T : atoms),
  x \notin (S \u T) -> x \notin S /\ x \notin T.
Proof.
  intros. split; [apply notin_union_1 in H | apply notin_union_2 in H]; exact H.
Qed.

(* ============================================================ *)
(* Part 2: commutation / identity for type instances             *)
(* ============================================================ *)

Lemma subst_tt_open_tt_rec_gen : forall X U K L T,
  lc_tt 0 U ->
  subst_tt X U (open_tt_rec K L T) = open_tt_rec K (subst_tt X U L) (subst_tt X U T).
Proof.
  intros X U K L T. revert K. induction T; intros K Hlc; simpl.
  - reflexivity.
  - reflexivity.
  - destruct (K === n); reflexivity.
  - destruct (a == X) as [e|e]; simpl.
    + symmetry. apply (@lc_tt_open_id 0 K (subst_tt X U L) U Hlc). lia.
    + reflexivity.
  - rewrite (IHT1 K Hlc), (IHT2 K Hlc). reflexivity.
  - rewrite (IHT1 K Hlc), (IHT2 (S K) Hlc). reflexivity.
  - rewrite (IHT (S K) Hlc). reflexivity.
  - rewrite (IHT K Hlc). reflexivity.
  - reflexivity.
  - rewrite (IHT1 K Hlc), (IHT2 K Hlc). reflexivity.
Qed.

Lemma subst_te_open_te_rec_gen : forall X U K L e,
  lc_tt 0 U ->
  subst_te X U (open_te_rec K L e) = open_te_rec K (subst_tt X U L) (subst_te X U e).
Proof.
  intros X U K L e. revert K. induction e; intros K Hlc; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite (@subst_tt_open_tt_rec_gen X U K L t Hlc).
    rewrite (IHe K Hlc). reflexivity.
  - rewrite (IHe1 K Hlc), (IHe2 K Hlc). reflexivity.
  - rewrite (@subst_tt_open_tt_rec_gen X U K L t Hlc).
    rewrite (IHe (S K) Hlc). reflexivity.
  - rewrite (IHe K Hlc).
    rewrite (@subst_tt_open_tt_rec_gen X U K L t Hlc). reflexivity.
  - reflexivity.
  - rewrite (@subst_tt_open_tt_rec_gen X U K L t Hlc).
    rewrite (IHe K Hlc). reflexivity.
  - rewrite (@subst_tt_open_tt_rec_gen X U K L t Hlc).
    rewrite (IHe K Hlc). reflexivity.
  - reflexivity.
  - rewrite (IHe1 K Hlc), (IHe2 K Hlc). reflexivity.
  - rewrite (IHe K Hlc). reflexivity.
Qed.

Lemma subst_te_open_ee_rec_gen : forall X U K u e,
  subst_te X U (open_ee_rec K u e) = open_ee_rec K (subst_te X U u) (subst_te X U e).
Proof.
  intros X U K u e. revert K. induction e; intros K; simpl.
  - destruct (K == n); simpl; reflexivity.
  - reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
  - reflexivity.
  - rewrite IHe. reflexivity.
  - rewrite IHe. reflexivity.
  - reflexivity.
  - rewrite IHe1, IHe2. reflexivity.
  - rewrite IHe. reflexivity.
Qed.

Lemma subst_tt_id : forall X U T, X \notin fv_tt T -> subst_tt X U T = T.
Proof.
  intros X U T. induction T; simpl; intros Hfv; try reflexivity.
  - (* fvar *) destruct (a == X) as [e|e].
    + exfalso. exact ((notin_singleton_1 a X Hfv) e).
    + reflexivity.
  - (* arrow *) apply notin_union_1 in Hfv as H1. apply notin_union_2 in Hfv as H2.
    rewrite (IHT1 H1), (IHT2 H2). reflexivity.
  - (* all *) apply notin_union_1 in Hfv as H1. apply notin_union_2 in Hfv as H2.
    rewrite (IHT1 H1), (IHT2 H2). reflexivity.
  - (* mu *) rewrite IHT; auto.
  - (* label *) rewrite IHT; auto.
  - (* rcd_cons *) apply notin_union_1 in Hfv as H1. apply notin_union_2 in Hfv as H2.
    rewrite (IHT1 H1), (IHT2 H2). reflexivity.
Qed.

Lemma subst_te_id : forall X U e, X \notin fv_te e -> subst_te X U e = e.
Proof.
  intros X U e. induction e; simpl; intros Hfv; try reflexivity.
  - (* abs *) apply notin_union_1 in Hfv as H1. apply notin_union_2 in Hfv as H2.
    rewrite (@subst_tt_id X U t H1), (IHe H2). reflexivity.
  - (* app *) apply notin_union_1 in Hfv as H1. apply notin_union_2 in Hfv as H2.
    rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - (* tabs *) apply notin_union_1 in Hfv as H1. apply notin_union_2 in Hfv as H2.
    rewrite (@subst_tt_id X U t H1), (IHe H2). reflexivity.
  - (* tapp *) apply notin_union_1 in Hfv as H1. apply notin_union_2 in Hfv as H2.
    rewrite (@subst_tt_id X U t H1), (IHe H2). reflexivity.
  - (* unfold *) apply notin_union_1 in Hfv as H1. apply notin_union_2 in Hfv as H2.
    rewrite (@subst_tt_id X U t H1), (IHe H2). reflexivity.
  - (* fold *) apply notin_union_1 in Hfv as H1. apply notin_union_2 in Hfv as H2.
    rewrite (@subst_tt_id X U t H1), (IHe H2). reflexivity.
  - (* rcd_cons *) apply notin_union_1 in Hfv as H1. apply notin_union_2 in Hfv as H2.
    rewrite (IHe1 H1), (IHe2 H2). reflexivity.
  - (* proj *) rewrite IHe; auto.
Qed.

(* ============================================================ *)
(* Part 3: structural helpers for rt/collect/Tlookup              *)
(* ============================================================ *)

Lemma rt_type_subst_tt : forall X U T, rt_type T -> rt_type (subst_tt X U T).
Proof. intros X U T H. inversion H; subst; simpl; constructor. Qed.

(* collectLabel only sees the record spine; a well-formed record type has a
   proper record tail, so substitution cannot change the set of labels. *)
Lemma collectLabel_subst_tt_wf : forall E T, WF E T -> forall X U,
  rt_type T -> collectLabel (subst_tt X U T) = collectLabel T.
Proof.
  intros E T Hwf. induction Hwf; intros Xs Us Hrt.
  - inversion Hrt.
  - inversion Hrt.
  - inversion Hrt.
  - inversion Hrt.
  - inversion Hrt.
  - inversion Hrt.
  - inversion Hrt.
  - reflexivity.
  - simpl. rewrite (IHHwf2 Xs Us H). reflexivity.
Qed.

(* If a field is present in T, substitution preserves the lookup. *)
Lemma Tlookup_subst_tt : forall X U T i Ti,
  Tlookup i T = Some Ti ->
  Tlookup i (subst_tt X U T) = Some (subst_tt X U Ti).
Proof.
  intros X U T. induction T; intros i Ti h; simpl in *; try discriminate h.
  - (* rcd_cons *) destruct (a == i) as [e|e]; simpl in *.
    + injection h as hTi. subst Ti. reflexivity.
    + apply IHT2. exact h.
Qed.

Lemma Tlookup_subst_tt_wf : forall E T, WF E T -> forall X U i,
  rt_type T -> Tlookup i (subst_tt X U T) = option_map (subst_tt X U) (Tlookup i T).
Proof.
  intros E T Hwf. induction Hwf; intros Xs Us lbl Hrt.
  - inversion Hrt.
  - inversion Hrt.
  - inversion Hrt.
  - inversion Hrt.
  - inversion Hrt.
  - inversion Hrt.
  - inversion Hrt.
  - reflexivity.
  - simpl. destruct (i == lbl) as [e|e].
    + reflexivity.
    + exact (IHHwf2 Xs Us lbl H).
Qed.

Lemma collectLabele_subst_te : forall X U e,
  collectLabele (subst_te X U e) = collectLabele e.
Proof.
  intros X U e. induction e; simpl; try reflexivity.
  - (* rcd_cons *) simpl. f_equal. assumption.
Qed.

Lemma rt_expr_subst_te : forall X U e, rt_expr e -> rt_expr (subst_te X U e).
Proof. intros X U e H. inversion H; subst; simpl; constructor. Qed.

Lemma option_map_Some_inv : forall (A B : Type) (f : A -> B) (o : option A) (y : B),
  option_map f o = Some y -> exists x, o = Some x /\ y = f x.
Proof.
  intros A B f o. destruct o as [x|]; intros y H.
  - exists x. injection H as H. split; [reflexivity| symmetry; exact H].
  - discriminate H.
Qed.

(* ============================================================ *)
(* Part 4: inserting/removing the distinguished binder            *)
(* ============================================================ *)

Lemma notin_dom_app_cons : forall D X V (Y : atom),
  Y \notin dom D -> Y <> X -> Y \notin dom (D ++ (X, bind_sub V) :: nil).
Proof.
  induction D as [|[Z b] D IH]; intros X V Y Hd Hne; simpl.
  - apply notin_add_3; [symmetry; exact Hne | apply notin_empty_1].
  - apply notin_add_3.
    + apply notin_add_1 in Hd. exact Hd.
    + apply IH; [apply notin_add_2 in Hd; exact Hd | exact Hne].
Qed.

Lemma notin_dom_app_cons_inv : forall D X V (Y : atom),
  Y \notin dom (D ++ (X, bind_sub V) :: nil) -> Y \notin dom D /\ Y <> X.
Proof.
  induction D as [|[Z b] D IH]; intros X V Y H; simpl in *.
  - split.
    + apply notin_empty_1.
    + apply notin_add_1 in H. intro e. apply H. symmetry. exact e.
  - apply notin_add_1 in H as HZY.
    apply notin_add_2 in H as Htail.
    apply IH in Htail. destruct Htail as [Hdom Hne].
    split.
    + apply notin_add_3; [exact HZY | exact Hdom].
    + exact Hne.
Qed.

Lemma notin_dom_subst_env : forall D X U (Y : atom),
  Y \notin dom D -> Y <> X -> Y \notin dom (subst_env X U D).
Proof.
  induction D as [|[Z b] D IH]; intros X U Y Hd Hne; simpl.
  - apply notin_empty_1.
  - destruct (Z == X) as [e|e].
    + apply IH; [apply notin_add_2 in Hd; exact Hd | exact Hne].
    + apply notin_add_3.
      * apply notin_add_1 in Hd. exact Hd.
      * apply IH; [apply notin_add_2 in Hd; exact Hd | exact Hne].
Qed.

Lemma binds_subst_env_gen : forall X U E (Y : atom) b,
  binds Y b E -> Y <> X ->
  binds Y (match b with
           | bind_sub T => bind_sub (subst_tt X U T)
           | bind_typ T => bind_typ (subst_tt X U T)
           end) (subst_env X U E).
Proof.
  intros X U E. induction E as [|[Z c] E IH]; intros Y b Hb Hne.
  - inversion Hb.
  - apply binds_cons_1 in Hb as [[Heq Hbeq]|Ht].
    + subst Y. subst b. simpl. destruct (Z == X) as [eZ|eZ].
      * exfalso. exact (Hne eZ).
      * left. reflexivity.
    + simpl. destruct (Z == X) as [eZ|eZ].
      * apply IH; assumption.
      * right. apply IH; assumption.
Qed.

Lemma binds_subst_env : forall X U E (Y : atom) T,
  binds Y (bind_sub T) E -> Y <> X ->
  binds Y (bind_sub (subst_tt X U T)) (subst_env X U E).
Proof. intros. apply binds_subst_env_gen with (b := bind_sub T); auto. Qed.

Lemma binds_typ_subst_env : forall X U E (Y : atom) T,
  binds Y (bind_typ T) E -> Y <> X ->
  binds Y (bind_typ (subst_tt X U T)) (subst_env X U E).
Proof. intros. apply binds_subst_env_gen with (b := bind_typ T); auto. Qed.

Lemma binds_distinguished_sub : forall D X V b,
  X \notin dom D -> binds X b (D ++ (X, bind_sub V) :: nil) -> b = bind_sub V.
Proof.
  induction D as [|[Z c] D IH]; intros X V b Hd Hb; simpl in Hd.
  - apply binds_cons_1 in Hb as [[Heq Hbeq]|Ht].
    + exact Hbeq.
    + inversion Ht.
  - apply notin_add_1 in Hd as HXZ.
    apply notin_add_2 in Hd as Hd'.
    apply binds_cons_1 in Hb as [[Heq Hbeq]|Ht].
    + exfalso. apply HXZ. symmetry. exact Heq.
    + apply (IH X V b); assumption.
Qed.

Lemma binds_typ_neq_distinguished : forall D X V (x : atom) T,
  X \notin dom D -> binds x (bind_typ T) (D ++ (X, bind_sub V) :: nil) -> x <> X.
Proof.
  intros D X V x T Hd Hb Heq. subst x.
  pose proof (@binds_distinguished_sub D X V (bind_typ T) Hd Hb) as He. discriminate He.
Qed.

(* ============================================================ *)
(* Part 5: WF is stable under type substitution                  *)
(* ============================================================ *)

Lemma WF_subst_gen : forall D X V T,
  WF (D ++ (X, bind_sub V) :: nil) T ->
  forall U, WF nil U -> WF (subst_env X U D) (subst_tt X U T).
Proof.
  intros D0 X0 V0 T0 H0 U0 HU0.
  assert (Hind : forall E T, WF E T -> forall D X V U,
      E = D ++ (X, bind_sub V) :: nil -> WF nil U ->
      WF (subst_env X U D) (subst_tt X U T)).
  { apply (Rules.WF_ind
      (fun E T => forall D X V U,
        E = D ++ (X, bind_sub V) :: nil -> WF nil U ->
        WF (subst_env X U D) (subst_tt X U T))).
  - (* top *) intros E D X V U Heq HU. subst E. simpl. apply WF_top.
  - (* nat *) intros E D X V U Heq HU. subst E. simpl. apply WF_nat.
  - (* var *) intros Uv E Z Hb D X V U Heq HU. subst E.
    simpl. destruct (Z == X) as [eZ|eZ].
    + apply wf_nil_any. exact HU.
    + eapply WF_var.
      pose proof (@binds_subst_env X U (D ++ (X, bind_sub V) :: nil) Z Uv Hb eZ) as Hbs.
      rewrite subst_env_app, subst_env_dist, app_nil_r in Hbs. exact Hbs.
  - (* arrow *) intros E A B Ha IHa Hb IHb D X V U Heq HU. subst E. simpl.
    apply WF_arrow.
    + apply IHa with (D := D) (X := X) (V := V) (U := U); auto.
    + apply IHb with (D := D) (X := X) (V := V) (U := U); auto.
  - (* all *) intros L E T1 T2 Hwf1 IH1 Hbody IHbody D X V U Heq HU. subst E. simpl.
    apply WF_all with (L := L \u {{X}}).
    + apply IH1 with (D := D) (X := X) (V := V) (U := U); auto.
    + intros Y HY.
      apply notin_union_1 in HY as HYL.
      apply notin_union_2 in HY as HYXs.
      pose proof (@neq_of_notin_singleton Y X HYXs) as HYX.
      assert (HlcU : lc_tt 0 U) by (exact (@wf_lc_tt nil U HU)).
      pose proof (IHbody Y HYL ((Y, bind_sub T1) :: D) X V U eq_refl HU) as Hres.
      rewrite (@subst_env_cons_neq X U Y _ D HYX) in Hres.
      unfold open_tt in Hres.
      rewrite (@subst_tt_open_tt_rec_gen X U 0 Y T2 HlcU) in Hres.
      rewrite (@subst_tt_fvar_neq X Y U (fun H => HYX (eq_sym H))) in Hres.
      simpl in Hres. exact Hres.
  - (* rec *) intros L E A Hw1 IH1 Hw2 IH2 D X V U Heq HU. subst E. simpl.
    apply WF_rec with (L := L \u {{X}}).
    + intros Y HY.
      apply notin_union_1 in HY as HYL.
      apply notin_union_2 in HY as HYXs.
      pose proof (@neq_of_notin_singleton Y X HYXs) as HYX.
      assert (HlcU : lc_tt 0 U) by (exact (@wf_lc_tt nil U HU)).
      pose proof (IH1 Y HYL ((Y, bind_sub typ_top) :: D) X V U eq_refl HU) as Hres.
      rewrite (@subst_env_cons_neq X U Y _ D HYX) in Hres.
      unfold open_tt in Hres.
      rewrite (@subst_tt_open_tt_rec_gen X U 0 Y A HlcU) in Hres.
      rewrite (@subst_tt_fvar_neq X Y U (fun H => HYX (eq_sym H))) in Hres.
      simpl in Hres. exact Hres.
    + intros Y HY.
      apply notin_union_1 in HY as HYL.
      apply notin_union_2 in HY as HYXs.
      pose proof (@neq_of_notin_singleton Y X HYXs) as HYX.
      assert (HlcU : lc_tt 0 U) by (exact (@wf_lc_tt nil U HU)).
      pose proof (IH2 Y HYL ((Y, bind_sub typ_top) :: D) X V U eq_refl HU) as Hres.
      rewrite (@subst_env_cons_neq X U Y _ D HYX) in Hres.
      unfold open_tt in Hres.
      rewrite (@subst_tt_open_tt_rec_gen X U 0 (typ_label Y (open_tt_rec 0 Y A)) A HlcU) in Hres.
      simpl in Hres.
      rewrite (@subst_tt_open_tt_rec_gen X U 0 Y A HlcU) in Hres.
      rewrite (@subst_tt_fvar_neq X Y U (fun H => HYX (eq_sym H))) in Hres.
      simpl in Hres. exact Hres.
  - (* label *) intros E A Z Ha IHa D X V U Heq HU. subst E. simpl.
    apply WF_label. apply IHa with (D := D) (X := X) (V := V) (U := U); auto.
  - (* rcd_nil *) intros E D X V U Heq HU. subst E. simpl. apply WF_rcd_nil.
  - (* rcd_cons *) intros E i T1 T2 Ha IHa Hb IHb Hrt Hn D X V U Heq HU. subst E. simpl.
    apply WF_rcd_cons.
    + apply IHa with (D := D) (X := X) (V := V) (U := U); auto.
    + apply IHb with (D := D) (X := X) (V := V) (U := U); auto.
    + apply rt_type_subst_tt. exact Hrt.
    + rewrite (@collectLabel_subst_tt_wf (D ++ (X, bind_sub V) :: nil) T2 Hb X U Hrt).
      exact Hn.
  }
  apply (Hind (D0 ++ (X0, bind_sub V0) :: nil) T0 H0 D0 X0 V0 U0 eq_refl HU0).
Qed.

Lemma wf_env_subst_env : forall D X V,
  X \notin dom D ->
  wf_env (D ++ (X, bind_sub V) :: nil) ->
  forall U, sub nil U V -> lc_tt 0 U -> wf_env (subst_env X U D).
Proof.
  induction D as [|[Y b] D IH]; intros X V Hdom Hwf U Hsub Hlc.
  - simpl. apply wf_env_empty.
  - simpl in Hdom.
    apply notin_add_1 in Hdom as HYX.
    apply notin_add_2 in Hdom as HdomX.
    destruct b as [T|T].
    + (* bind_sub *)
      inversion Hwf as [| E0 X0 T0 Hwe HWF Hnotin|]; subst.
      assert (HYdom : Y \notin dom D).
      { destruct (@notin_dom_app_cons_inv D X V Y Hnotin) as [H1 _]. exact H1. }
      pose proof (IH X V HdomX Hwe U Hsub Hlc) as IHw.
      pose proof (@WF_subst_gen D X V T HWF U (proj1 (sub_wf Hsub))) as HWFsub.
      rewrite (@subst_env_cons_neq X U Y (bind_sub T) D HYX). simpl.
      apply wf_env_sub.
      * exact IHw.
      * exact HWFsub.
      * apply notin_dom_subst_env; [exact HYdom | exact HYX].
    + (* bind_typ *)
      inversion Hwf as [| | E0 x0 T0 Hwe HWF Hnotin]; subst.
      assert (HYdom : Y \notin dom D).
      { destruct (@notin_dom_app_cons_inv D X V Y Hnotin) as [H1 _]. exact H1. }
      pose proof (IH X V HdomX Hwe U Hsub Hlc) as IHw.
      pose proof (@WF_subst_gen D X V T HWF U (proj1 (sub_wf Hsub))) as HWFsub.
      rewrite (@subst_env_cons_neq X U Y (bind_typ T) D HYX). simpl.
      apply wf_env_typ.
      * exact IHw.
      * exact HWFsub.
      * apply notin_dom_subst_env; [exact HYdom | exact HYX].
Qed.

Lemma WF_fvar_binds : forall E X, WF E (typ_fvar X) ->
  exists U, binds X (bind_sub U) E.
Proof.
  intros E X H. inversion H; subst. eexists. eassumption.
Qed.

(* ============================================================ *)

Lemma erase_env_id : forall E (X : atom) (W : typ),
  X \notin dom E ->
  X \notin fv_env E ->
  X \notin fl_env E ->
  erase_env X W E = E.
Proof.
  induction E as [| [Y b] E IH]; intros X W Hd Hfv Hfl.
  - reflexivity.
  - destruct b as [T|T]; simpl in Hd, Hfv, Hfl.
    + (* bind_sub *)
      apply notin_add_1 in Hd as Hne.
      apply notin_add_2 in Hd as Hd'.
      apply notin_union_1 in Hfv as HfvT.
      apply notin_union_2 in Hfv as HfvE.
      apply notin_union_1 in Hfl as HflT.
      apply notin_union_2 in Hfl as HflE.
      destruct (Y == X) as [Heq|Hneq].
      * exfalso. exact (Hne Heq).
      * rewrite (@erase_env_cons_neq X W Y (bind_sub T) E Hneq).
        change ((Y, bind_sub (erase X W T)) :: erase_env X W E
                = (Y, bind_sub T) :: E).
        rewrite (@erase_id X W T HfvT HflT).
        rewrite (IH X W Hd' HfvE HflE). reflexivity.
    + (* bind_typ *)
      apply notin_add_1 in Hd as Hne.
      apply notin_add_2 in Hd as Hd'.
      apply notin_union_1 in Hfv as HfvT.
      apply notin_union_2 in Hfv as HfvE.
      apply notin_union_1 in Hfl as HflT.
      apply notin_union_2 in Hfl as HflE.
      destruct (Y == X) as [Heq|Hneq].
      * exfalso. exact (Hne Heq).
      * rewrite (@erase_env_cons_neq X W Y (bind_typ T) E Hneq).
        change ((Y, bind_typ (erase X W T)) :: erase_env X W E
                = (Y, bind_typ T) :: E).
        rewrite (@erase_id X W T HfvT HflT).
        rewrite (IH X W Hd' HfvE HflE). reflexivity.
Qed.

(* ============================================================ *)
(* Part 2.  Kernel unrolling with a fresh knot variable X:       *)
(* erasing the knot by ANY closed W gives the same-argument      *)
(* unrolling of an arbitrary kernel derivation.                  *)
(* This is exactly the tool suggested by the coordinator's hint: *)
(* it applies to arrow/label subderivations too, not only to the *)
(* top-level kernel.                                             *)
(* ============================================================ *)

Lemma kernel_unroll : forall (E : env) (X : atom) (A B : typ),
  wf_env E ->
  X \notin dom E ->
  X \notin fv_env E ->
  X \notin fl_env E ->
  X \notin fv_tt A ->
  X \notin fl_tt A ->
  X \notin fv_tt B ->
  X \notin fl_tt B ->
  sub (X ~ bind_sub typ_top ++ E)
      (open_tt A (typ_label X (open_tt A X)))
      (open_tt B (typ_label X (open_tt B X))) ->
  forall W, WF nil W -> sub E (open_tt A W) (open_tt B W).
Proof.
  intros E X A B Hwe HXd HXfvE HXflE HXfvA HXflA HXfvB HXflB HK W Hwnil.
  assert (HweX : wf_env (X ~ bind_sub typ_top ++ E)).
  { apply wf_env_sub.
    - exact Hwe.
    - apply WF_top.
    - exact HXd. }
  assert (HbX : binds X (bind_sub typ_top) (X ~ bind_sub typ_top ++ E)).
  { simpl. left. reflexivity. }
  pose proof (@sub_erase (X ~ bind_sub typ_top ++ E) HweX X HbX
     (open_tt A (typ_label X (open_tt A X)))
     (open_tt B (typ_label X (open_tt B X))) HK W Hwnil) as Hres.
  assert (Heenv : erase_env X W (X ~ bind_sub typ_top ++ E) = E).
  { change (erase_env X W ((X, bind_sub typ_top) :: E) = E).
    rewrite erase_env_cons_eq with (Y := X) (b := bind_sub typ_top) (E := E)
      by reflexivity.
    apply erase_env_id; assumption. }
  rewrite Heenv in Hres.
  unfold open_tt in Hres.
  rewrite (@erase_open X W 0 (typ_label X (open_tt_rec 0 X A)) A
             (wf_lc_tt Hwnil)) in Hres.
  rewrite (@erase_open X W 0 (typ_label X (open_tt_rec 0 X B)) B
             (wf_lc_tt Hwnil)) in Hres.
  rewrite erase_label_eq in Hres.
  rewrite erase_label_eq in Hres.
  rewrite (@erase_id X W A HXfvA HXflA) in Hres.
  rewrite (@erase_id X W B HXfvB HXflB) in Hres.
  unfold open_tt in *. exact Hres.
Qed.

(* ============================================================ *)
(* Part 3.  Same-argument unrolling for an arbitrary env,        *)
(* directly from the hypothesis  sub E (mu A) (mu B).           *)
(* This generalises Task.v's sub_unroll_same and is the piece    *)
(* that discharges every component in which the recursive        *)
(* variable is absent / when a closed W can be used.             *)
(* ============================================================ *)

Lemma sub_unroll_same_E : forall (E : env) (A B : typ),
  wf_env E ->
  sub E (typ_mu A) (typ_mu B) ->
  forall W, WF nil W -> sub E (open_tt A W) (open_tt B W).
Proof.
  intros E A B Hwe H W Hwnil.
  destruct (sub_mu_inv H) as [L [HwfA [HwfB HK]]].
  destruct (atom_fresh (L \u dom E \u fv_env E \u fl_env E
                          \u fv_tt A \u fl_tt A \u fv_tt B \u fl_tt B))
    as [X HX].
  assert (HXL : X \notin L) by fsetdec.
  assert (HXd : X \notin dom E) by fsetdec.
  assert (HXfvE : X \notin fv_env E) by fsetdec.
  assert (HXflE : X \notin fl_env E) by fsetdec.
  assert (HXfvA : X \notin fv_tt A) by fsetdec.
  assert (HXflA : X \notin fl_tt A) by fsetdec.
  assert (HXfvB : X \notin fv_tt B) by fsetdec.
  assert (HXflB : X \notin fl_tt B) by fsetdec.
  eapply kernel_unroll; eauto.
Qed.

Lemma sub_label_inv : forall E X Y A B,
  sub E (typ_label X A) (typ_label Y B) ->
  X = Y /\ sub E A B.
Proof.
  intros E X Y A B H.
  inversion H; subst; eauto.
  exfalso.
  match goal with
  | Hr : rt_type (typ_label _ _) |- _ => inversion Hr
  | He : typ_label _ _ = typ_top |- _ => discriminate He
  | He : typ_label _ _ = typ_nat |- _ => discriminate He
  | He : typ_label _ _ = typ_fvar _ |- _ => discriminate He
  | He : typ_label _ _ = typ_mu _ |- _ => discriminate He
  | He : typ_label _ _ = typ_arrow _ _ |- _ => discriminate He
  | He : typ_label _ _ = typ_all _ _ |- _ => discriminate He
  end.
Qed.

(* If A = arrow (bvar 0) A2 and B = arrow (bvar 0) B2, then the
   target for this pair is EXACTLY the pair (reverse mu subtyping,
   mixed codomain subtyping).  The reverse-mu component is the
   first obligation that cannot be discharged by
   sub_unroll_same_E / erase alone.  Fully proved (no Admitted). *)
Lemma sub_unroll_self_nil_arrow_bvar0_iff : forall (A2 B2 : typ),
  sub nil
    (open_tt (typ_arrow (typ_bvar 0) A2) (typ_mu (typ_arrow (typ_bvar 0) A2)))
    (open_tt (typ_arrow (typ_bvar 0) B2) (typ_mu (typ_arrow (typ_bvar 0) B2)))
  <->
  sub nil (typ_mu (typ_arrow (typ_bvar 0) B2))
          (typ_mu (typ_arrow (typ_bvar 0) A2)) /\
  sub nil (open_tt A2 (typ_mu (typ_arrow (typ_bvar 0) A2)))
          (open_tt B2 (typ_mu (typ_arrow (typ_bvar 0) B2))).
Proof.
  intros A2 B2. split.
  - intros Ht. unfold open_tt in Ht. simpl in Ht.
    apply sub_arrow_inv in Ht as [Hdom Hcod].
    split; assumption.
  - intros [Hdom Hcod]. unfold open_tt. simpl.
    apply sa_arrow; assumption.
Qed.

Definition four (E : env) (C D Y UA UB : typ) : Prop :=
  sub E (open_tt C Y) (open_tt D Y) /\
  sub E (open_tt D Y) (open_tt C Y) /\
  sub E (open_tt C UA) (open_tt D UB) /\
  sub E (open_tt D UB) (open_tt C UA).

Lemma four_arrow_decomp : forall E C1 C2 D1 D2 Y UA UB,
  four E (typ_arrow C1 C2) (typ_arrow D1 D2) Y UA UB <->
  four E C1 D1 Y UA UB /\ four E C2 D2 Y UA UB.
Proof.
  intros E C1 C2 D1 D2 Y UA UB.
  unfold four. unfold open_tt. simpl.
  split.
  - intros (H1 & H2 & H3 & H4).
    apply sub_arrow_inv in H1 as [H1d H1c].
    apply sub_arrow_inv in H2 as [H2d H2c].
    apply sub_arrow_inv in H3 as [H3d H3c].
    apply sub_arrow_inv in H4 as [H4d H4c].
    split.
    + repeat split; assumption.
    + repeat split; assumption.
  - intros [[F1 [R1 [M1 N1]]] [F2 [R2 [M2 N2]]]].
    repeat split; apply sa_arrow; assumption.
Qed.

(* At a hole pair the package degenerates exactly to the two    *)
(* argument relations.  The kernel supplies UB<:UA (K1), but    *)
(* never UA<:UB; the latter is equivalent to FS of the whole    *)
(* pair.  This is the irreducible coinductive/circular step.     *)
Lemma four_hole : forall E Y UA UB,
  four E (typ_bvar 0) (typ_bvar 0) Y UA UB <->
  sub E Y Y /\ sub E UA UB /\ sub E UB UA.
Proof.
  intros. unfold four. unfold open_tt. simpl.
  split.
  - intros (H1 & H2 & H3 & H4). repeat split; assumption.
  - intros (H1 & H3 & H4). repeat split; assumption.
Qed.

(* ============================================================ *)
(* Part 9.  Concrete record tool used by the composite-domain    *)
(* example: records with the same labels and pointwise subtyping *)
(* in both directions are mutually subtypes.  This is what       *)
(* closes RS/FM on reordered-record domains once the label       *)
(* forward relation D is available.                              *)
(* ============================================================ *)

Lemma sub_rcd_mutual : forall E A1 A2,
  wf_env E ->
  rt_type A1 -> rt_type A2 ->
  WF E A1 -> WF E A2 ->
  collectLabel A1 [<=] collectLabel A2 ->
  collectLabel A2 [<=] collectLabel A1 ->
  (forall i t1 t2, Tlookup i A1 = Some t1 -> Tlookup i A2 = Some t2 ->
      sub E t1 t2) ->
  (forall i t1 t2, Tlookup i A2 = Some t1 -> Tlookup i A1 = Some t2 ->
      sub E t1 t2) ->
  sub E A1 A2 /\ sub E A2 A1.
Proof.
  intros E A1 A2 Hwe Hrt1 Hrt2 Hwf1 Hwf2 Hinc12 Hinc21 Hf12 Hf21.
  split.
  - eapply sa_rcd; eauto.
  - eapply sa_rcd; eauto.
Qed.

(* ============================================================ *)
(* Target theorem (proof under construction)                    *)

Theorem preservation : forall e e' T,
    typing nil e T ->
    step e e' ->
    typing nil e' T.
