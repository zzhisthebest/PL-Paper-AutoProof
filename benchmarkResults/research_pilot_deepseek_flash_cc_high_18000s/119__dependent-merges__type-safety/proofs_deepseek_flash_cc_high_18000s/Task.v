Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Import Lia.

Require Import Language Infra.

(* ================= basic subtyping ================= *)

Lemma size_typ_ge1 : forall A, 1 <= size_typ A.
Proof. induction A; simpl; lia. Qed.

Lemma sub_refl : forall A, sub A A.
Proof. induction A; eauto using sub. Qed.

Lemma sub_top_gen : forall A C, sub top C -> sub A C.
Proof.
  intros A C H. remember top as T eqn:ET.
  revert A. induction H; intros A0; subst; try discriminate.
  - apply stop.
  - apply sand; [ apply IHsub1 | apply IHsub2 ]; auto.
Qed.

Lemma sub_and_inv : forall A T, sub A T -> forall X Y, T = and X Y -> sub A X /\ sub A Y.
Proof.
  intros A T H. induction H; intros X Y E; try discriminate.
  - injection E as h1 h2. subst. split; assumption.
  - subst. destruct (IHsub X Y eq_refl) as [h1 h2]. split; eauto using sub.
  - subst. destruct (IHsub X Y eq_refl) as [h1 h2]. split; eauto using sub.
Qed.

Lemma sub_trans_aux : forall n A B C,
  size_typ A + size_typ B + size_typ C <= n -> sub A B -> sub B C -> sub A C.
Proof.
  intros n. induction n as [| n IH]; intros A B C Hn HAB HBC.
  - pose proof (size_typ_ge1 A). pose proof (size_typ_ge1 B). pose proof (size_typ_ge1 C). lia.
  - destruct HAB.
    + exact HBC.
    + apply sub_top_gen. exact HBC.
    + inversion HBC; subst.
      * apply stop.
      * apply sand.
        -- apply (IH A (and B C0) B0). simpl in *; lia. apply sand; assumption. exact H.
        -- apply (IH A (and B C0) C1). simpl in *; lia. apply sand; assumption. exact H0.
      * apply (IH A B C). simpl in *; lia. exact HAB1. exact H2.
      * apply (IH A C0 C). simpl in *; lia. exact HAB2. exact H2.
    + apply sandl. apply (IH A C0 C). simpl in *; lia. exact HAB. exact HBC.
    + apply sandr. apply (IH B C0 C). simpl in *; lia. exact HAB. exact HBC.
    + inversion HBC; subst.
      * apply stop.
      * apply sand.
        -- apply (IH (rcd x A) (rcd x B) B0). simpl in *; lia. apply srcd. exact HAB. exact H.
        -- apply (IH (rcd x A) (rcd x B) C0). simpl in *; lia. apply srcd. exact HAB. exact H0.
      * apply srcd. apply (IH A B B0). simpl in *; lia. exact HAB. exact H2.
    + inversion HBC; subst.
      * apply stop.
      * apply sand.
        -- apply (IH (arr A B) (arr C0 D) B0). simpl in *; lia. apply sarr; assumption. exact H.
        -- apply (IH (arr A B) (arr C0 D) C1). simpl in *; lia. apply sarr; assumption. exact H0.
      * apply sarr.
        -- apply (IH C1 C0 A). simpl in *; lia. exact H1. exact HAB1.
        -- apply (IH B D D0). simpl in *; lia. exact HAB2. exact H3.
Qed.

Lemma sub_trans : forall A B C, sub A B -> sub B C -> sub A C.
Proof.
  intros A B C H1 H2. apply (sub_trans_aux (size_typ A + size_typ B + size_typ C) A B C).
  lia. exact H1. exact H2.
Qed.

(* ================= Shape ================= *)

Fixpoint Shape (A : typ) (v : exp) : Prop :=
  match A with
  | int => exists i, v = lit i
  | top => v = unit
  | and A1 A2 => exists v1 v2, v = merge v1 v2 /\ Shape A1 v1 /\ Shape A2 v2
  | rcd l A1 => exists v0, v = rec l v0 /\ Shape A1 v0
  | arr A1 A2 => exists v0 e fm A0 A',
        v = box v0 (ann (lam fm e) (arr A0 A2)) /\
        value v0 /\ ext A0 fm A' /\ sub A1 A' /\ value v
  end.

Lemma shape_value : forall A v, Shape A v -> value v.
Proof.
  induction A; simpl; intros v H.
  - destruct H as [i ->]. apply vlit.
  - subst. apply vunit.
  - destruct H as [v1 [v2 [-> [h1 h2]]]]. apply vmrg; [apply IHA1|apply IHA2]; assumption.
  - destruct H as [v0 [-> h]]. apply vrec. apply IHA. assumption.
  - destruct H as [v0 [e [fm [A0 [A' [-> [hv [hext [hsub hval]]]]]]]]]. assumption.
Qed.

(* ================= genv basic ================= *)

Lemma genv_value : forall A v, genv A v -> value v.
Proof.
  intros A v H. induction H.
  - apply vunit.
  - apply vclos. apply vunit.
  - apply vmrg; assumption.
  - apply vrec. assumption.
Qed.

Lemma ext_wh_inv : forall A A', ext A wh A' -> exists l A0, A = rcd l A0 /\ A' = A0.
Proof. intros A A' H. inversion H. eauto. Qed.

Lemma ext_functional : forall A fm A1 A2, ext A fm A1 -> ext A fm A2 -> A1 = A2.
Proof. intros A fm A1 A2 H1 H2. inversion H1; subst; inversion H2; subst; reflexivity. Qed.

(* ================= casting: value and shape ================= *)

Lemma casting_value : forall v A v', casting v A v' -> value v -> value v'.
Proof.
  intros v A v' H. induction H; intros hv.
  - apply vunit.
  - apply vlit.
  - apply IHcasting. inversion hv. assumption.
  - apply IHcasting. inversion hv. assumption.
  - apply vmrg; [ apply IHcasting1 | apply IHcasting2 ]; assumption.
  - apply vrec. apply IHcasting. inversion hv. assumption.
  - (* cast_arr *) inversion hv; subst.
    + apply vclos. assumption.
    + apply vsclos. assumption.
  - eapply genv_value. eassumption.
Qed.

Lemma casting_shape : forall v A v', casting v A v' -> Shape A v'.
Proof.
  intros v A v' H. induction H; simpl.
  - (* cast_top *) reflexivity.
  - (* cast_int *) exists i; reflexivity.
  - (* cast_mrgl *) assumption.
  - (* cast_mrgr *) assumption.
  - (* cast_and *) exists v1, v2; auto.
  - (* cast_rcd *) exists v'; auto.
  - (* cast_arr *)
    exists v, e, fm, A, A'. split; [ reflexivity | ].
    split; [ assumption | ]. split; [ exact H1 | ]. split; [ exact H2 | ].
    inversion H1; subst.
    + apply vclos. assumption.
    + apply vsclos. assumption.
  - (* cast_arr_tl *)
    inversion H4; subst.
    exists unit, v0, bl, C, C. split; [ reflexivity | ].
    split; [ constructor | ]. split; [ constructor | ]. split; [ apply sub_refl | ].
    apply vclos. apply vunit.
Qed.

(* ================= toplike and genv ================= *)

Lemma toplike_genv : forall A, toplike A -> exists v, genv A v.
Proof.
  intros A H. induction H.
  - exists unit. apply genv_top.
  - destruct IHtoplike1 as [v1 g1]. destruct IHtoplike2 as [v2 g2].
    exists (merge v1 v2). apply genv_and; assumption.
  - destruct IHtoplike as [v g]. exists (box unit (ann (lam bl v) (arr A B))).
    apply genv_arr. assumption.
  - destruct IHtoplike as [v g]. exists (rec x v). apply genv_rcd. assumption.
Qed.

Lemma toplike_dec : forall A, toplike A \/ ~ toplike A.
Proof.
  induction A; simpl.
  - right. intro H. inversion H.
  - left. apply TL_top.
  - destruct IHA1 as [h1|h1]; destruct IHA2 as [h2|h2].
    + left. apply TL_and; assumption.
    + right. intro H. inversion H. tauto.
    + right. intro H. inversion H. tauto.
    + right. intro H. inversion H. tauto.
  - destruct IHA as [h|h].
    + left. apply TL_rcd. assumption.
    + right. intro H. inversion H. tauto.
  - destruct IHA2 as [h|h].
    + left. apply TL_arr. assumption.
    + right. intro H. inversion H. tauto.
Qed.

(* ================= Shape implies castability ================= *)

Lemma shape_castable_aux : forall n A B,
  size_typ A + size_typ B <= n -> sub A B -> forall v, Shape A v -> exists v', casting v B v'.
Proof.
  intros n. induction n as [| n IH]; intros A B Hn Hsub v Hsh.
  - pose proof (size_typ_ge1 A); pose proof (size_typ_ge1 B); lia.
  - destruct B.
    + (* int *) inversion Hsub; subst.
      * simpl in Hsh. destruct Hsh as [i ->]. exists (lit i). apply cast_int.
      * simpl in Hsh. destruct Hsh as [v1 [v2 [-> [h1 h2]]]].
        assert (Hm : size_typ A0 + size_typ int <= n) by (simpl in *; lia).
        destruct (IH A0 int Hm H v1 h1) as [w Hw].
        exists w. apply cast_mrgl. exact Hw. apply O_int.
      * simpl in Hsh. destruct Hsh as [v1 [v2 [-> [h1 h2]]]].
        assert (Hm : size_typ B + size_typ int <= n) by (simpl in *; lia).
        destruct (IH B int Hm H v2 h2) as [w Hw].
        exists w. apply cast_mrgr. exact Hw. apply O_int.
    + (* top *) exists unit. apply cast_top.
    + (* and *)
      destruct (sub_and_inv A (and B1 B2) Hsub B1 B2 eq_refl) as [hs1 hs2].
      assert (Hm1 : size_typ A + size_typ B1 <= n) by (simpl in *; lia).
      assert (Hm2 : size_typ A + size_typ B2 <= n) by (simpl in *; lia).
      destruct (IH A B1 Hm1 hs1 v Hsh) as [w1 Hw1].
      destruct (IH A B2 Hm2 hs2 v Hsh) as [w2 Hw2].
      exists (merge w1 w2). apply cast_and; assumption.
    + (* rcd *) inversion Hsub; subst.
      * simpl in Hsh. destruct Hsh as [v1 [v2 [-> [h1 h2]]]].
        assert (Hm : size_typ A0 + size_typ (rcd n0 B) <= n) by (simpl in *; lia).
        destruct (IH A0 (rcd n0 B) Hm H v1 h1) as [w Hw].
        exists w. apply cast_mrgl. exact Hw. apply O_rcd.
      * simpl in Hsh. destruct Hsh as [v1 [v2 [-> [h1 h2]]]].
        assert (Hm : size_typ B0 + size_typ (rcd n0 B) <= n) by (simpl in *; lia).
        destruct (IH B0 (rcd n0 B) Hm H v2 h2) as [w Hw].
        exists w. apply cast_mrgr. exact Hw. apply O_rcd.
      * simpl in Hsh. destruct Hsh as [v0 [-> h]].
        assert (Hm : size_typ A0 + size_typ B <= n) by (simpl in *; lia).
        destruct (IH A0 B Hm H1 v0 h) as [w Hw].
        exists (rec n0 w). apply cast_rcd. exact Hw.
    + (* arr *) inversion Hsub; subst.
      * simpl in Hsh. destruct Hsh as [v1 [v2 [-> [h1 h2]]]].
        assert (Hm : size_typ A0 + size_typ (arr B1 B2) <= n) by (simpl in *; lia).
        destruct (IH A0 (arr B1 B2) Hm H v1 h1) as [w Hw].
        exists w. apply cast_mrgl. exact Hw. apply O_arrow.
      * simpl in Hsh. destruct Hsh as [v1 [v2 [-> [h1 h2]]]].
        assert (Hm : size_typ B + size_typ (arr B1 B2) <= n) by (simpl in *; lia).
        destruct (IH B (arr B1 B2) Hm H v2 h2) as [w Hw].
        exists w. apply cast_mrgr. exact Hw. apply O_arrow.
      * destruct Hsh as [v0 [e0 [fm0 [Aann [Ae [-> [hv0 [hext [hsubAr hval]]]]]]]]].
        destruct (toplike_dec B2) as [htl | hntl].
        -- destruct (toplike_genv (arr B1 B2)) as [w gw].
           { apply TL_arr. assumption. }
           exists w. eapply cast_arr_tl; [ exact hv0 | exact htl | exact hext | apply (sub_trans B1 A0 Ae H2 hsubAr) | exact H3 | exact gw ].
        -- exists (box v0 (ann (lam fm0 e0) (arr Aann B2))).
           eapply cast_arr; [ exact hv0 | exact hntl | exact hext | apply (sub_trans B1 A0 Ae H2 hsubAr) | exact H3 ].
Qed.

Lemma shape_castable : forall A B, sub A B -> forall v, Shape A v -> exists v', casting v B v'.
Proof.
  intros A B Hsub v Hsh. apply (shape_castable_aux (size_typ A + size_typ B) A B).
  lia. exact Hsub. exact Hsh.
Qed.

Lemma lam_untypable_inf : forall G fm e A, has_type G (lam fm e) inf A -> False.
Proof. intros G fm e A H. inversion H. Qed.

Lemma lam_untypable : forall G fm e m A, has_type G (lam fm e) m A -> False.
Proof.
  intros G fm e m A H. destruct m.
  - eapply lam_untypable_inf; eassumption.
  - inversion H. eapply lam_untypable_inf; eassumption.
Qed.

(* ================= value_shape: inf typing gives Shape ================= *)

Lemma value_shape : forall v, value v -> forall G T, has_type G v inf T -> Shape T v.
Proof.
  intros v Hv. induction Hv; intros G T Hty.
  - (* vlit *) inversion Hty; subst. simpl. exists i. reflexivity.
  - (* vunit *) inversion Hty; subst. simpl. reflexivity.
  - (* vmrg *) inversion Hty; subst.
    + (* tmrg *) simpl. exists e1, e2. split; [ reflexivity | split ].
      * apply IHHv1 with (G:=G). exact H1.
      * apply IHHv2 with (G:=(and G A)). exact H2.
    + (* tcon *) simpl. exists e1, e2. split; [ reflexivity | split ].
      * apply IHHv1 with (G:=G). exact H1.
      * apply IHHv2 with (G:=G). exact H2.
  - (* vrec *) inversion Hty; subst. simpl. exists e. split; [ reflexivity | ].
    apply IHHv with (G:=G). exact H1.
  - (* vclos *) inversion Hty; subst. inversion H3; subst.
    + (* tann *) exfalso. eapply lam_untypable. eassumption.
    + (* tlam *) simpl. exists e1, e, bl, A, A'. split; [ reflexivity | ].
      split; [ exact Hv | ]. split; [ exact H7 | ]. split; [ exact H9 | ].
      apply vclos. exact Hv.
  - (* vsclos *) inversion Hty; subst. inversion H3; subst.
    + (* tann *) exfalso. eapply lam_untypable. eassumption.
    + (* tlam *) simpl. exists e1, e, wh, (rcd l A), A'. split; [ reflexivity | ].
      split; [ exact Hv | ]. split; [ exact H7 | ]. split; [ exact H9 | ].
      apply vsclos. exact Hv.
Qed.

(* ================= genv structure ================= *)

Lemma genv_functional : forall A v1, genv A v1 -> forall v2, genv A v2 -> v1 = v2.
Proof.
  intros A v1 H. induction H; intros w H2; inversion H2; subst; try reflexivity.
  - (* arr *) assert (v = v0) as -> by (apply IHgenv; assumption). reflexivity.
  - (* and *) assert (v1 = v0) as -> by (apply IHgenv1; assumption).
    assert (v2 = v3) as -> by (apply IHgenv2; assumption). reflexivity.
  - (* rcd *) assert (v = v0) as -> by (apply IHgenv; assumption). reflexivity.
Qed.

Lemma genv_toplike : forall A v, genv A v -> toplike A.
Proof.
  intros A v H. induction H.
  - apply TL_top.
  - apply TL_arr. assumption.
  - apply TL_and; assumption.
  - apply TL_rcd. assumption.
Qed.

Lemma sub_toplike : forall A B, sub A B -> toplike A -> toplike B.
Proof.
  intros A B H. induction H; intros ht.
  - inversion ht.
  - apply TL_top.
  - apply TL_and; [ apply IHsub1 | apply IHsub2 ]; assumption.
  - inversion ht. apply IHsub. assumption.
  - inversion ht. apply IHsub. assumption.
  - inversion ht. apply TL_rcd. apply IHsub. assumption.
  - inversion ht. apply TL_arr. apply IHsub2. assumption.
Qed.

Lemma toplike_and_inv : forall A B, toplike (and A B) -> toplike A /\ toplike B.
Proof. intros A B H. inversion H; subst; auto. Qed.

Lemma toplike_arr_inv : forall A B, toplike (arr A B) -> toplike B.
Proof. intros A B H. inversion H; subst; auto. Qed.

Lemma toplike_rcd_inv : forall x A, toplike (rcd x A) -> toplike A.
Proof. intros x A H. inversion H; subst; auto. Qed.

Lemma sub_top_gord_false : forall C, gord C -> sub top C -> False.
Proof.
  intros C Hg. induction Hg as [| A B HgB IHgB | l B HgB IHgB]; intros Hs.
  - inversion Hs.
  - inversion Hs.
  - inversion Hs.
Qed.

Lemma disjoint_top_l : forall A, disjoint top A.
Proof.
  intros A [C [Hg [H1 H2]]]. eapply sub_top_gord_false; eassumption.
Qed.

Lemma disjoint_top_r : forall A, disjoint A top.
Proof.
  intros A [C [Hg [H1 H2]]]. eapply sub_top_gord_false; eassumption.
Qed.

Lemma non_toplike_gord : forall A, ~ toplike A -> exists D, gord D /\ sub A D.
Proof.
  induction A; intros hnt.
  - exists int. split; [ apply GO_int | apply sint ].
  - exfalso. apply hnt. apply TL_top.
  - destruct (toplike_dec A1) as [h1 | h1].
    + destruct (toplike_dec A2) as [h2 | h2].
      * exfalso. apply hnt. apply TL_and; assumption.
      * destruct (IHA2 h2) as [D [Hg Hs]]. exists D. split; [ assumption | ].
        apply sandr. assumption.
    + destruct (IHA1 h1) as [D [Hg Hs]]. exists D. split; [ assumption | ].
      apply sandl. assumption.
  - destruct (IHA (fun h => hnt (TL_rcd n A h))) as [D [Hg Hs]].
    exists (rcd n D). split; [ apply GO_rcd; assumption | apply srcd; assumption ].
  - destruct (IHA2 (fun h => hnt (TL_arr A1 A2 h))) as [D [Hg Hs]].
    exists (arr A1 D). split; [ apply GO_arrow; assumption | ].
    apply sarr; [ apply sub_refl | assumption ].
Qed.

(* ================= genv and casting ================= *)

Lemma genv_cast_genv : forall v C x, casting v C x -> forall A, genv A v -> genv C x.
Proof.
  intros v C x H. induction H; intros A0 Hg.
  - apply genv_top.
  - inversion Hg.
  - inversion Hg; subst. eapply IHcasting; eassumption.
  - inversion Hg; subst. eapply IHcasting; eassumption.
  - apply genv_and; [ eapply IHcasting1; exact Hg | eapply IHcasting2; exact Hg ].
  - inversion Hg; subst. apply genv_rcd. eapply IHcasting; eassumption.
  - inversion Hg; subst.
    exfalso. eapply H0. apply sub_toplike with (A:=B).
    + exact H3.
    + eapply genv_toplike. eassumption.
  - inversion Hg; subst. assumption.
Qed.

Lemma genv_consistency : forall A v1, genv A v1 -> forall B v2, genv B v2 -> consistencySpec v1 v2.
Proof.
  intros A v1 H1 B v2 H2 C w1 w2 Hc1 Hc2.
  pose proof (genv_cast_genv _ _ _ Hc1 _ H1) as g1.
  pose proof (genv_cast_genv _ _ _ Hc2 _ H2) as g2.
  assert (w1 = w2) by (eapply genv_functional; eassumption). assumption.
Qed.

Lemma genv_typing : forall A v, genv A v -> forall G, has_type G v inf A.
Proof.
  intros A v H. induction H; intros G.
  - apply tunit.
  - (* arr *) eapply tbox.
    + apply tunit.
    + eapply tlam.
      * apply disjoint_top_l.
      * apply ext_bl.
      * apply sub_refl.
      * eapply tsub; [ apply IHgenv | apply sub_refl ].
  - (* and *) eapply tcon.
    + apply IHgenv1.
    + apply IHgenv2.
    + eapply genv_value; eassumption.
    + eapply genv_value; eassumption.
    + eapply genv_consistency; eassumption.
  - (* rcd *) apply trec. apply IHgenv.
Qed.

Lemma cast_toplike_genv : forall v C x, casting v C x -> toplike C -> genv C x.
Proof.
  intros v C x H. induction H; intros ht.
  - apply genv_top.
  - inversion ht.
  - apply IHcasting. assumption.
  - apply IHcasting. assumption.
  - destruct (toplike_and_inv _ _ ht) as [h1 h2].
    apply genv_and; [ apply IHcasting1 | apply IHcasting2 ]; assumption.
  - apply genv_rcd. apply IHcasting. inversion ht; subst; assumption.
  - exfalso. apply H0. apply toplike_arr_inv in ht. assumption.
  - assumption.
Qed.

(* ================= more casting structure ================= *)

Lemma merge_cast_exact : forall v1 v2 B x, casting v1 B x -> casting (merge v1 v2) B x.
Proof.
  intros v1 v2 B. induction B; intros x Hc.
  - apply cast_mrgl; [ exact Hc | apply O_int ].
  - inversion Hc; subst; try apply cast_top;
    try (exfalso; match goal with H : ord top |- _ => inversion H end).
  - inversion Hc; subst.
    + exfalso. match goal with H : ord (and _ _) |- _ => inversion H end.
    + exfalso. match goal with H : ord (and _ _) |- _ => inversion H end.
    + apply cast_and; [ apply IHB1 | apply IHB2 ]; assumption.
  - apply cast_mrgl; [ exact Hc | apply O_rcd ].
  - apply cast_mrgl; [ exact Hc | apply O_arrow ].
Qed.

Lemma merge_cast_exact_r : forall v1 v2 B x, casting v2 B x -> casting (merge v1 v2) B x.
Proof.
  intros v1 v2 B. induction B; intros x Hc.
  - apply cast_mrgr; [ exact Hc | apply O_int ].
  - inversion Hc; subst; try apply cast_top;
    try (exfalso; match goal with H : ord top |- _ => inversion H end).
  - inversion Hc; subst.
    + exfalso. match goal with H : ord (and _ _) |- _ => inversion H end.
    + exfalso. match goal with H : ord (and _ _) |- _ => inversion H end.
    + apply cast_and; [ apply IHB1 | apply IHB2 ]; assumption.
  - apply cast_mrgr; [ exact Hc | apply O_rcd ].
  - apply cast_mrgr; [ exact Hc | apply O_arrow ].
Qed.

(* ================= cast composition ================= *)

Lemma cast_unit_comp : forall v T x, casting unit T x -> casting v T x.
Proof.
  intros v T x H. remember unit as u eqn:E.
  induction H; subst; try discriminate.
  - apply cast_top.
  - apply cast_and; [ apply IHcasting1; reflexivity | apply IHcasting2; reflexivity ].
Qed.

Lemma cast_comp : forall v A v', casting v A v' -> forall T w, casting v' T w -> casting v T w.
Proof.
  intros v A v' H1. induction H1; intros T w Hc.
  - (* cast_top *) apply cast_unit_comp. assumption.
  - (* cast_int *) inversion Hc; subst; eauto using casting.
  - (* cast_mrgl *) inversion Hc; subst.
    + apply cast_top.
    + apply cast_mrgl. apply IHcasting. assumption. apply O_int.
    + apply cast_mrgl. apply IHcasting. assumption. assumption.
    + apply cast_mrgl. apply IHcasting. assumption. assumption.
    + apply cast_and.
      * apply merge_cast_exact. apply IHcasting. assumption.
      * apply merge_cast_exact. apply IHcasting. assumption.
    + apply cast_mrgl. apply IHcasting. assumption. apply O_rcd.
    + apply cast_mrgl. apply IHcasting. assumption. apply O_arrow.
    + apply cast_mrgl. apply IHcasting. assumption. apply O_arrow.
  - (* cast_mrgr *) inversion Hc; subst.
    + apply cast_top.
    + apply cast_mrgr. apply IHcasting. assumption. apply O_int.
    + apply cast_mrgr. apply IHcasting. assumption. assumption.
    + apply cast_mrgr. apply IHcasting. assumption. assumption.
    + apply cast_and.
      * apply merge_cast_exact_r. apply IHcasting. assumption.
      * apply merge_cast_exact_r. apply IHcasting. assumption.
    + apply cast_mrgr. apply IHcasting. assumption. apply O_rcd.
    + apply cast_mrgr. apply IHcasting. assumption. apply O_arrow.
    + apply cast_mrgr. apply IHcasting. assumption. apply O_arrow.
  - (* cast_and *) remember (merge v1 v2) as m eqn:Em.
    induction Hc; subst; try discriminate.
    + apply cast_top.
    + injection Em as E1 E2. subst. apply IHcasting1. assumption.
    + injection Em as E1 E2. subst. apply IHcasting2. assumption.
    + apply cast_and; [ apply IHHc1; reflexivity | apply IHHc2; reflexivity ].
  - (* cast_rcd *) remember (rec x v') as m eqn:Em.
    induction Hc; subst; try discriminate; try (apply cast_top).
    + apply cast_and; [ apply IHHc1; reflexivity | apply IHHc2; reflexivity ].
    + injection Em as Ex Ev. subst. apply cast_rcd. apply IHcasting. assumption.
  - (* cast_arr *) remember (box v (ann (lam fm e) (arr A D))) as m eqn:Em.
    induction Hc; subst; try discriminate.
    + apply cast_top.
    + apply cast_and; [ apply IHHc1; reflexivity | apply IHHc2; reflexivity ].
    + injection Em as E1 E2 E3 E4 E5. subst.
      eapply cast_arr; eauto. eapply sub_trans; eauto.
    + injection Em as E1 E2 E3 E4 E5. subst.
      eapply cast_arr_tl; eauto. eapply sub_trans; eauto.
  - (* cast_arr_tl *) dependent destruction H4.
    remember (box unit (ann (lam bl v0) (arr C D))) as m eqn:Em.
    induction Hc; subst; try discriminate.
    + apply cast_top.
    + apply cast_and; [ apply IHHc1; reflexivity | apply IHHc2; reflexivity ].
    + injection Em as E1 E2 E3 E4 E5. subst.
      exfalso. eapply H6. eapply sub_toplike; eassumption.
    + injection Em as E1 E2 E3 E4 E5. subst.
      eapply cast_arr_tl; eauto.
      inversion H7; subst.
      * apply (sub_trans C0 A'0 A'); assumption.
      * apply (sub_trans B D D0); assumption.
Qed.

(* ================= typing inversions for values ================= *)

Lemma merge_typing_left : forall G u1 u2 A, has_type G (merge u1 u2) inf A ->
  exists T1 T2, A = and T1 T2 /\ has_type G u1 inf T1.
Proof.
  intros G u1 u2 A H. inversion H; subst; eauto.
Qed.

Lemma merge_typing_right : forall G u1 u2 A, has_type G (merge u1 u2) inf A ->
  exists G' T1 T2, A = and T1 T2 /\ has_type G' u2 inf T2.
Proof.
  intros G u1 u2 A H. inversion H; subst; eauto 6.
Qed.

Lemma rec_typing_inv : forall G l v0 A, has_type G (rec l v0) inf A ->
  exists T0, A = rcd l T0 /\ has_type G v0 inf T0.
Proof.
  intros G l v0 A H. inversion H; subst; eauto.
Qed.

Lemma box_typing_inv : forall G v0 e2 A, has_type G (box v0 e2) inf A ->
  exists B, has_type G v0 inf B /\ has_type B e2 inf A.
Proof.
  intros G v0 e2 A H. inversion H; subst; eauto.
Qed.

Lemma lit_typing_inv : forall G i A, has_type G (lit i) inf A -> A = int.
Proof. intros G i A H. inversion H; subst; reflexivity. Qed.

Lemma unit_typing_inv : forall G A, has_type G unit inf A -> A = top.
Proof. intros G A H. inversion H; subst; reflexivity. Qed.

Lemma cast_int_sub : forall v, value v -> forall w, casting v int w -> forall G T, has_type G v inf T -> sub T int.
Proof.
  intros v Hv. induction Hv; intros w Hc G T Hty.
  - (* lit *) inversion Hc; subst.
    rewrite (lit_typing_inv G i T Hty). apply sint.
  - (* unit *) inversion Hc.
  - (* merge *) inversion Hc; subst.
    + destruct (merge_typing_left G e1 e2 T Hty) as [T1 [T2 [Heq Hu]]]. subst.
      apply sandl. eapply IHHv1; [ eassumption | exact Hu ].
    + destruct (merge_typing_right G e1 e2 T Hty) as [G' [T1 [T2 [Heq Hu]]]]. subst.
      apply sandr. eapply IHHv2; [ eassumption | exact Hu ].
  - (* rec *) inversion Hc.
  - (* vclos *) inversion Hc.
  - (* vsclos *) inversion Hc.
Qed.
(* ================= canonical gord supertype ================= *)

Fixpoint toplike_decS (A : typ) : {toplike A} + {~ toplike A}.
Proof.
  destruct A as [ | | A1 A2 | l A0 | A1 A2].
  - right. intro H. inversion H.
  - left. apply TL_top.
  - destruct (toplike_decS A1) as [h1 | h1].
    + destruct (toplike_decS A2) as [h2 | h2].
      * left. apply TL_and; assumption.
      * right. intro H. inversion H. tauto.
    + right. intro H. inversion H. tauto.
  - destruct (toplike_decS A0) as [h | h].
    + left. apply TL_rcd. assumption.
    + right. intro H. inversion H. tauto.
  - destruct (toplike_decS A2) as [h | h].
    + left. apply TL_arr. assumption.
    + right. intro H. inversion H. tauto.
Defined.

Fixpoint gsup (A : typ) : typ :=
  match A with
  | int => int
  | top => top
  | and A1 A2 =>
      if toplike_decS A1 then (if toplike_decS A2 then top else gsup A2) else gsup A1
  | rcd l A0 => rcd l (gsup A0)
  | arr A1 A2 => arr A1 (gsup A2)
  end.

Lemma toplike_not_and : forall A B, ~ toplike (and A B) -> ~ toplike A \/ ~ toplike B.
Proof.
  intros A B H. destruct (toplike_decS A) as [ha | ha]; destruct (toplike_decS B) as [hb | hb].
  - exfalso. apply H. apply TL_and; assumption.
  - right. assumption.
  - left. assumption.
  - left. assumption.
Qed.

Lemma gsup_gord : forall A, ~ toplike A -> gord (gsup A).
Proof.
  induction A; simpl; intros h.
  - apply GO_int.
  - exfalso. apply h. apply TL_top.
  - destruct (toplike_decS A1) as [h1 | h1]; simpl.
    + destruct (toplike_decS A2) as [h2 | h2]; simpl.
      * exfalso. apply h. apply TL_and; assumption.
      * apply IHA2. assumption.
    + apply IHA1. assumption.
  - apply GO_rcd. apply IHA. intro hh. apply h. apply TL_rcd. assumption.
  - apply GO_arrow. apply IHA2. intro hh. apply h. apply TL_arr. assumption.
Qed.

Lemma gsup_sub : forall A, ~ toplike A -> sub A (gsup A).
Proof.
  induction A; simpl; intros h.
  - apply sint.
  - exfalso. apply h. apply TL_top.
  - destruct (toplike_decS A1) as [h1 | h1]; simpl.
    + destruct (toplike_decS A2) as [h2 | h2]; simpl.
      * exfalso. apply h. apply TL_and; assumption.
      * apply sandr. apply IHA2. assumption.
    + apply sandl. apply IHA1. assumption.
  - apply srcd. apply IHA. intro hh. apply h. apply TL_rcd. assumption.
  - apply sarr; [ apply sub_refl | apply IHA2 ]. intro hh. apply h. apply TL_arr. assumption.
Qed.

(* cost_spec introductions *)
Lemma cost_and_l : forall T1 T2 B, cost_spec T1 B -> cost_spec (and T1 T2) B.
Proof. intros T1 T2 B [D [Hg [H1 H2]]]. exists D. split; [ assumption | split ]; [ apply sandl; assumption | assumption ]. Qed.

Lemma cost_and_r : forall T1 T2 B, cost_spec T2 B -> cost_spec (and T1 T2) B.
Proof. intros T1 T2 B [D [Hg [H1 H2]]]. exists D. split; [ assumption | split ]; [ apply sandr; assumption | assumption ]. Qed.

Lemma cost_r_and_l : forall A B1 B2, cost_spec A B1 -> cost_spec A (and B1 B2).
Proof. intros A B1 B2 [D [Hg [H1 H2]]]. exists D. split; [ assumption | split ]; [ assumption | apply sandl; assumption ]. Qed.

Lemma cost_r_and_r : forall A B1 B2, cost_spec A B2 -> cost_spec A (and B1 B2).
Proof. intros A B1 B2 [D [Hg [H1 H2]]]. exists D. split; [ assumption | split ]; [ assumption | apply sandr; assumption ]. Qed.

Lemma cost_rcd : forall l A0 B0, cost_spec A0 B0 -> cost_spec (rcd l A0) (rcd l B0).
Proof. intros l A0 B0 [D [Hg [H1 H2]]]. exists (rcd l D). split; [ apply GO_rcd; assumption | split; apply srcd; assumption ]. Qed.

Lemma cost_arr : forall CA CB BA BB, cost_spec BA BB -> cost_spec (arr CA BA) (arr CB BB).
Proof.
  intros CA CB BA BB [D [Hg [H1 H2]]].
  exists (arr (and CA CB) D). split; [ apply GO_arrow; assumption | split ].
  - apply sarr; [ apply sandl; apply sub_refl | assumption ].
  - apply sarr; [ apply sandr; apply sub_refl | assumption ].
Qed.

(* disjointness descent *)
Lemma disjoint_and_l : forall T1 T2 B, disjoint (and T1 T2) B -> disjoint T1 B.
Proof. intros T1 T2 B H Hc. apply H. apply cost_and_l. assumption. Qed.

Lemma disjoint_and_r : forall T1 T2 B, disjoint (and T1 T2) B -> disjoint T2 B.
Proof. intros T1 T2 B H Hc. apply H. apply cost_and_r. assumption. Qed.

Lemma disjoint_r_and_l : forall A B1 B2, disjoint A (and B1 B2) -> disjoint A B1.
Proof. intros A B1 B2 H Hc. apply H. apply cost_r_and_l. assumption. Qed.

Lemma disjoint_r_and_r : forall A B1 B2, disjoint A (and B1 B2) -> disjoint A B2.
Proof. intros A B1 B2 H Hc. apply H. apply cost_r_and_r. assumption. Qed.

Lemma disjoint_rcd : forall l A0 B0, disjoint (rcd l A0) (rcd l B0) -> disjoint A0 B0.
Proof. intros l A0 B0 H Hc. apply H. apply cost_rcd. assumption. Qed.

Lemma disjoint_arr : forall CA CB BA BB, disjoint (arr CA BA) (arr CB BB) -> disjoint BA BB.
Proof. intros CA CB BA BB H Hc. apply H. apply cost_arr. assumption. Qed.

(* ================= disjointness excludes common non-toplike casts ================= *)

Lemma size_exp_ge1 : forall e, 1 <= size_exp e.
Proof. induction e; simpl; lia. Qed.

Lemma no_common_cast_aux : forall n C v1 v2,
  size_typ C + size_exp v1 + size_exp v2 <= n ->
  value v1 -> value v2 ->
  forall G1 A1, has_type G1 v1 inf A1 ->
  forall G2 A2, has_type G2 v2 inf A2 ->
  disjoint A1 A2 ->
  forall w1, casting v1 C w1 -> forall w2, casting v2 C w2 -> ~ toplike C -> False.
Proof.
  intros n. induction n as [| n IH]; intros C v1 v2 Hn hv1 hv2 G1 A1 Hty1 G2 A2 Hty2 Hdis w1 Hc1 w2 Hc2 Hnt.
  - pose proof (size_typ_ge1 C). pose proof (size_exp_ge1 v1). pose proof (size_exp_ge1 v2). lia.
  - destruct C.
    + (* int *) pose proof (cast_int_sub v1 hv1 w1 Hc1 G1 A1 Hty1) as Hs1.
      pose proof (cast_int_sub v2 hv2 w2 Hc2 G2 A2 Hty2) as Hs2.
      apply Hdis. exists int. split; [ apply GO_int | split; assumption ].
    + (* top *) exfalso. apply Hnt. apply TL_top.
    + (* and *) inversion Hc1; subst;
      try (exfalso; match goal with H : ord (and _ _) |- _ => inversion H end).
      * inversion Hc2; subst;
        try (exfalso; match goal with H : ord (and _ _) |- _ => inversion H end).
        -- (* both cast_and *) destruct (toplike_decS C1) as [ha | ha].
           ++ assert (hny : ~ toplike C2).
              { intro hb. apply Hnt. apply TL_and; assumption. }
              assert (Hm : size_typ C2 + size_exp v1 + size_exp v2 <= n) by (simpl in *; lia).
              eapply IH; [ exact Hm | exact hv1 | exact hv2 | exact Hty1 | exact Hty2 | exact Hdis | exact H4 | exact H6 | exact hny ].
           ++ assert (Hm : size_typ C1 + size_exp v1 + size_exp v2 <= n) by (simpl in *; lia).
              eapply IH; [ exact Hm | exact hv1 | exact hv2 | exact Hty1 | exact Hty2 | exact Hdis | exact H2 | exact H3 | exact ha ].
    + (* rcd *) inversion Hc1; subst.
      * (* mrgl *) inversion hv1; subst.
        destruct (merge_typing_left G1 v0 v3 A1 Hty1) as [T1 [T2 [Heq Hu]]]. subst.
        assert (Hd : disjoint T1 A2) by (apply disjoint_and_l in Hdis; exact Hdis).
        assert (Hm : size_typ (rcd n0 C) + size_exp v0 + size_exp v2 <= n) by (simpl in *; lia).
        eapply IH; [ exact Hm | exact H3 | exact hv2 | exact Hu | exact Hty2 | exact Hd | exact H | exact Hc2 | exact Hnt ].
      * (* mrgr *) inversion hv1; subst.
        destruct (merge_typing_right G1 v0 v3 A1 Hty1) as [G0 [T1 [T2 [Heq Hu]]]]. subst.
        assert (Hd : disjoint T2 A2) by (apply disjoint_and_r in Hdis; exact Hdis).
        assert (Hm : size_typ (rcd n0 C) + size_exp v3 + size_exp v2 <= n) by (simpl in *; lia).
        eapply IH; [ exact Hm | exact H4 | exact hv2 | exact Hu | exact Hty2 | exact Hd | exact H | exact Hc2 | exact Hnt ].
      * (* cast_rcd *) inversion Hc2; subst.
        -- (* mrgl *) inversion hv2; subst.
           destruct (merge_typing_left G2 v1 v0 A2 Hty2) as [T1 [T2 [Heq Hu]]]. subst.
           assert (Hd : disjoint A1 T1) by (apply disjoint_r_and_l in Hdis; exact Hdis).
           assert (Hm : size_typ (rcd n0 C) + size_exp (rec n0 v) + size_exp v1 <= n) by (simpl in *; lia).
           eapply IH; [ exact Hm | exact hv1 | exact H4 | exact Hty1 | exact Hu | exact Hd | exact Hc1 | exact H | exact Hnt ].
        -- (* mrgr *) inversion hv2; subst.
           destruct (merge_typing_right G2 v1 v0 A2 Hty2) as [G0 [T1 [T2 [Heq Hu]]]]. subst.
           assert (Hd : disjoint A1 T2) by (apply disjoint_r_and_r in Hdis; exact Hdis).
           assert (Hm : size_typ (rcd n0 C) + size_exp (rec n0 v) + size_exp v0 <= n) by (simpl in *; lia).
           eapply IH; [ exact Hm | exact hv1 | exact H5 | exact Hty1 | exact Hu | exact Hd | exact Hc1 | exact H | exact Hnt ].
        -- (* both rec *) inversion hv1; subst. inversion hv2; subst.
           destruct (rec_typing_inv G1 n0 v A1 Hty1) as [A0 [EA0 Hv0t]]. subst.
           destruct (rec_typing_inv G2 n0 v0 A2 Hty2) as [B0 [EB0 Hv0t2]]. subst.
           assert (Hd : disjoint A0 B0) by (apply disjoint_rcd in Hdis; exact Hdis).
           assert (Hnt0 : ~ toplike C) by (intro hh; apply Hnt; apply TL_rcd; assumption).
           assert (Hm : size_typ C + size_exp v + size_exp v0 <= n) by (simpl in *; lia).
           eapply IH; [ exact Hm | exact H0 | exact H1 | exact Hv0t | exact Hv0t2 | exact Hd | exact H3 | exact H4 | exact Hnt0 ].
    + (* arr *) inversion Hc1; subst.
      * (* mrgl *) inversion hv1; subst.
        destruct (merge_typing_left G1 v0 v3 A1 Hty1) as [T1 [T2 [Heq Hu]]]. subst.
        assert (Hd : disjoint T1 A2) by (apply disjoint_and_l in Hdis; exact Hdis).
        assert (Hm : size_typ (arr C1 C2) + size_exp v0 + size_exp v2 <= n) by (simpl in *; lia).
        eapply IH; [ exact Hm | exact H3 | exact hv2 | exact Hu | exact Hty2 | exact Hd | exact H | exact Hc2 | exact Hnt ].
      * (* mrgr *) inversion hv1; subst.
        destruct (merge_typing_right G1 v0 v3 A1 Hty1) as [G0 [T1 [T2 [Heq Hu]]]]. subst.
        assert (Hd : disjoint T2 A2) by (apply disjoint_and_r in Hdis; exact Hdis).
        assert (Hm : size_typ (arr C1 C2) + size_exp v3 + size_exp v2 <= n) by (simpl in *; lia).
        eapply IH; [ exact Hm | exact H4 | exact hv2 | exact Hu | exact Hty2 | exact Hd | exact H | exact Hc2 | exact Hnt ].
      * (* cast_arr *) inversion Hc2; subst.
        -- (* mrgl *) inversion hv2; subst.
           destruct (merge_typing_left G2 v1 v0 A2 Hty2) as [T1 [T2 [Heq Hu]]]. subst.
           assert (Hd : disjoint A1 T1) by (apply disjoint_r_and_l in Hdis; exact Hdis).
           assert (Hm : size_typ (arr C1 C2) + size_exp (box v (ann (lam fm e) (arr A B))) + size_exp v1 <= n) by (simpl in *; lia).
           eapply IH; [ exact Hm | exact hv1 | exact H8 | exact Hty1 | exact Hu | exact Hd | exact Hc1 | exact H | exact Hnt ].
        -- (* mrgr *) inversion hv2; subst.
           destruct (merge_typing_right G2 v1 v0 A2 Hty2) as [G0 [T1 [T2 [Heq Hu]]]]. subst.
           assert (Hd : disjoint A1 T2) by (apply disjoint_r_and_r in Hdis; exact Hdis).
           assert (Hm : size_typ (arr C1 C2) + size_exp (box v (ann (lam fm e) (arr A B))) + size_exp v0 <= n) by (simpl in *; lia).
           eapply IH; [ exact Hm | exact hv1 | exact H9 | exact Hty1 | exact Hu | exact Hd | exact Hc1 | exact H | exact Hnt ].
        -- (* both box *)
           destruct (box_typing_inv G1 v (ann (lam fm e) (arr A B)) A1 Hty1) as [B1 [Hvt1 Hann1]].
           destruct (box_typing_inv G2 v0 (ann (lam fm0 e0) (arr A0 B0)) A2 Hty2) as [B2 [Hvt2 Hann2]].
           inversion Hann1; subst; [ exfalso; eapply lam_untypable; eassumption | ].
           inversion Hann2; subst; [ exfalso; eapply lam_untypable; eassumption | ].
           apply Hdis. exists (arr (and C C0) (gsup C2)). split.
           ++ apply GO_arrow. apply gsup_gord. exact H2.
           ++ split.
              ** apply sarr; [ apply sandl; apply sub_refl | ].
                 eapply sub_trans; [ exact H7 | apply gsup_sub; exact H2 ].
              ** apply sarr; [ apply sandr; apply sub_refl | ].
                 eapply sub_trans; [ exact H12 | apply gsup_sub; exact H2 ].
        -- (* cast_arr_tl *) exfalso.
           match goal with Ht : toplike C2 |- _ => apply H2; exact Ht end.
      * (* arr_tl *) exfalso. apply Hnt. apply TL_arr. assumption.
Qed.

(* ================= disjoint types => consistency ================= *)

Lemma disjoint_consistency : forall G1 G2 A B v1 v2,
  disjoint A B -> value v1 -> value v2 ->
  has_type G1 v1 inf A -> has_type G2 v2 inf B ->
  consistencySpec v1 v2.
Proof.
  intros G1 G2 A B v1 v2 Hdis hv1 hv2 Ht1 Ht2 C w1 w2 Hc1 Hc2.
  destruct (toplike_decS C) as [ht | hnt].
  - pose proof (cast_toplike_genv _ _ _ Hc1 ht) as g1.
    pose proof (cast_toplike_genv _ _ _ Hc2 ht) as g2.
    eapply genv_functional; eassumption.
  - exfalso.
    eapply no_common_cast_aux with (n := size_typ C + size_exp v1 + size_exp v2)
                                     (C := C) (v1 := v1) (v2 := v2)
                                     (G1 := G1) (A1 := A) (G2 := G2) (A2 := B)
                                     (w1 := w1) (w2 := w2).
    + lia.
    + exact hv1. + exact hv2. + exact Ht1. + exact Ht2. + exact Hdis.
    + exact Hc1. + exact Hc2. + exact hnt.
Qed.

(* ================= value typing is environment independent ================= *)

Lemma value_typing_indep_inf : forall v, value v -> forall G T, has_type G v inf T -> forall G', has_type G' v inf T.
Proof.
  intros v Hv. induction Hv; intros G T Hty G'.
  - inversion Hty; subst; apply tlit.
  - inversion Hty; subst; apply tunit.
  - inversion Hty; subst.
    + (* tmrg *) eapply tcon.
      * apply (IHHv1 G A H1).
      * apply (IHHv2 (and G A) B H2).
      * exact Hv1.
      * exact Hv2.
      * eapply disjoint_consistency with (G1:=G) (A:=A) (G2:=(and G A)) (B:=B) (v1:=e1) (v2:=e2); eassumption.
    + (* tcon *) eapply tcon; [ apply (IHHv1 G A H1) | apply (IHHv2 G B H2) | exact Hv1 | exact Hv2 | assumption ].
  - inversion Hty; subst. apply trec. eapply IHHv; eassumption.
  - inversion Hty; subst. eapply tbox. eapply IHHv; eassumption. eassumption.
  - inversion Hty; subst. eapply tbox. eapply IHHv; eassumption. eassumption.
Qed.

Lemma has_type_chk_inv : forall G e T, has_type G e chk T -> exists T0, has_type G e inf T0 /\ sub T0 T.
Proof. intros G e T H. inversion H. eauto. Qed.

Lemma value_typing_indep : forall v, value v -> forall G m T, has_type G v m T -> forall G', has_type G' v m T.
Proof.
  intros v Hv G m T Hty G'. destruct m.
  - eapply value_typing_indep_inf with (v:=v) (G:=G) (T:=T).
    exact Hv. exact Hty.
  - apply has_type_chk_inv in Hty as [T0 [Hinf Hsub]].
    eapply tsub.
    eapply value_typing_indep_inf with (v:=v) (G:=G) (T:=T0).
    exact Hv. exact Hinf.
    exact Hsub.
Qed.
(* ================= determinism of casting ================= *)

Lemma merge_consistency : forall G u1 u2 T,
  has_type G (merge u1 u2) inf T -> value u1 -> value u2 -> consistencySpec u1 u2.
Proof.
  intros G u1 u2 T Hty hv1 hv2.
  inversion Hty; subst.
  - (* tmrg *) eapply disjoint_consistency with (G1:=G) (A:=A) (G2:=(and G A)) (B:=B) (v1:=u1) (v2:=u2); eassumption.
  - (* tcon *) assumption.
Qed.

Lemma cast_det_aux : forall n C v,
  size_typ C + size_exp v <= n ->
  value v -> forall G T, has_type G v inf T ->
  forall x, casting v C x -> forall y, casting v C y -> x = y.
Proof.
  intros n. induction n as [| n IH]; intros C v Hn hv G T Hty x Hc1 y Hc2.
  - pose proof (size_typ_ge1 C). pose proof (size_exp_ge1 v). lia.
  - destruct C.
    + (* int *) inversion Hc1; subst.
      * (* cast_int *) inversion Hc2; subst; reflexivity.
      * (* mrgl *) inversion Hc2; subst.
        -- (* mrgl *) inversion hv; subst.
           destruct (merge_typing_left G v1 v2 T Hty) as [T1 [T2 [Heq Hu]]]. subst.
           assert (Hm : size_typ int + size_exp v1 <= n) by (simpl in *; lia).
           eapply IH; [ exact Hm | exact H4 | exact Hu | exact H | exact H3 ].
        -- (* mrgr *) inversion hv; subst.
           pose proof (merge_consistency G v1 v2 T Hty H4 H5) as Hcons.
           eapply Hcons; eassumption.
      * (* mrgr *) inversion Hc2; subst.
        -- (* mrgl *) inversion hv; subst.
           pose proof (merge_consistency G v1 v2 T Hty H4 H5) as Hcons.
           symmetry. eapply Hcons; eassumption.
        -- (* mrgr *) inversion hv; subst.
           destruct (merge_typing_right G v1 v2 T Hty) as [G0 [T1 [T2 [Heq Hu]]]]. subst.
           assert (Hm : size_typ int + size_exp v2 <= n) by (simpl in *; lia).
           eapply IH; [ exact Hm | exact H5 | exact Hu | exact H | exact H3 ].
    + (* top *) inversion Hc1; subst; try (exfalso; match goal with H : ord top |- _ => inversion H end).
      inversion Hc2; subst; try reflexivity; try (exfalso; match goal with H : ord top |- _ => inversion H end).
    + (* and *) inversion Hc1; subst;
      try (exfalso; match goal with H : ord (and _ _) |- _ => inversion H end).
      * inversion Hc2; subst;
        try (exfalso; match goal with H : ord (and _ _) |- _ => inversion H end).
        -- assert (Hm1 : size_typ C1 + size_exp v <= n) by (simpl in *; lia).
           assert (E1 : v1 = v3) by (eapply IH; [ exact Hm1 | exact hv | exact Hty | exact H2 | exact H3 ]).
           assert (Hm2 : size_typ C2 + size_exp v <= n) by (simpl in *; lia).
           assert (E2 : v2 = v4) by (eapply IH; [ exact Hm2 | exact hv | exact Hty | exact H4 | exact H6 ]).
           subst. reflexivity.
    + (* rcd *) inversion Hc1; subst.
      * (* mrgl *) inversion Hc2; subst.
        -- (* mrgl *) inversion hv; subst.
           destruct (merge_typing_left G v1 v2 T Hty) as [T1 [T2 [Heq Hu]]]. subst.
           assert (Hm : size_typ (rcd n0 C) + size_exp v1 <= n) by (simpl in *; lia).
           eapply IH; [ exact Hm | exact H4 | exact Hu | exact H | exact H3 ].
        -- (* mrgr *) inversion hv; subst.
           pose proof (merge_consistency G v1 v2 T Hty H4 H5) as Hcons.
           eapply Hcons; eassumption.
      * (* mrgr *) inversion Hc2; subst.
        -- (* mrgl *) inversion hv; subst.
           pose proof (merge_consistency G v1 v2 T Hty H4 H5) as Hcons.
           symmetry. eapply Hcons; eassumption.
        -- (* mrgr *) inversion hv; subst.
           destruct (merge_typing_right G v1 v2 T Hty) as [G0 [T1 [T2 [Heq Hu]]]]. subst.
           assert (Hm : size_typ (rcd n0 C) + size_exp v2 <= n) by (simpl in *; lia).
           eapply IH; [ exact Hm | exact H5 | exact Hu | exact H | exact H3 ].
      * (* cast_rcd *) inversion Hc2; subst; try reflexivity.
        -- (* cast_rcd *) inversion hv; subst.
           destruct (rec_typing_inv G n0 v0 T Hty) as [T0 [Heq Hv0]]. subst.
           assert (Hm : size_typ C + size_exp v0 <= n) by (simpl in *; lia).
           assert (E : v' = v'0) by (eapply IH; [ exact Hm | exact H0 | exact Hv0 | exact H3 | exact H4 ]).
           subst. reflexivity.
    + (* arr *) inversion Hc1; subst.
      * (* mrgl *) inversion Hc2; subst.
        -- (* mrgl *) inversion hv; subst.
           destruct (merge_typing_left G v1 v2 T Hty) as [T1 [T2 [Heq Hu]]]. subst.
           assert (Hm : size_typ (arr C1 C2) + size_exp v1 <= n) by (simpl in *; lia).
           eapply IH; [ exact Hm | exact H4 | exact Hu | exact H | exact H3 ].
        -- (* mrgr *) inversion hv; subst.
           pose proof (merge_consistency G v1 v2 T Hty H4 H5) as Hcons.
           eapply Hcons; eassumption.
      * (* mrgr *) inversion Hc2; subst.
        -- (* mrgl *) inversion hv; subst.
           pose proof (merge_consistency G v1 v2 T Hty H4 H5) as Hcons.
           symmetry. eapply Hcons; eassumption.
        -- (* mrgr *) inversion hv; subst.
           destruct (merge_typing_right G v1 v2 T Hty) as [G0 [T1 [T2 [Heq Hu]]]]. subst.
           assert (Hm : size_typ (arr C1 C2) + size_exp v2 <= n) by (simpl in *; lia).
           eapply IH; [ exact Hm | exact H5 | exact Hu | exact H | exact H3 ].
      * (* cast_arr *) inversion Hc2; subst.
        -- reflexivity.
        -- exfalso. match goal with Ht : toplike C2, Hnt : ~ toplike C2 |- _ => exact (Hnt Ht) end.
      * (* arr_tl *) inversion Hc2; subst.
        -- exfalso. match goal with Ht : toplike C2, Hnt : ~ toplike C2 |- _ => exact (Hnt Ht) end.
        -- eapply genv_functional; eassumption.
Qed.
(* ================= casting preserves typability ================= *)

Lemma cast_det : forall v, value v -> forall G T, has_type G v inf T ->
  forall C x, casting v C x -> forall y, casting v C y -> x = y.
Proof.
  intros v hv G T Hty C x Hc1 y Hc2.
  refine (cast_det_aux (size_typ C + size_exp v) C v _ hv G T Hty x Hc1 y Hc2).
  lia.
Qed.

Lemma casts_consistent : forall v, value v -> forall G T, has_type G v inf T ->
  forall A1 w1, casting v A1 w1 -> forall A2 w2, casting v A2 w2 -> consistencySpec w1 w2.
Proof.
  intros v hv G T Hty A1 w1 H1 A2 w2 H2 C x y Hx Hy.
  pose proof (cast_comp v A1 w1 H1 C x Hx) as Hcx.
  pose proof (cast_comp v A2 w2 H2 C y Hy) as Hcy.
  eapply cast_det; eassumption.
Qed.

Lemma cast_arr_box_typing : forall G v0 e fm A_ann B_ann A' C D B1,
  value v0 -> ~ toplike D -> ext A_ann fm A' -> sub C A' -> sub B_ann D ->
  has_type G v0 inf B1 ->
  (exists Tann, has_type B1 (ann (lam fm e) (arr A_ann B_ann)) inf Tann) ->
  has_type G (box v0 (ann (lam fm e) (arr A_ann D))) inf (arr C D).
Proof.
  intros G v0 e fm A_ann B_ann A' C D B1 hv0 hnt hext hsubC hsubB hvt [Tann Htann].
  inversion Htann; subst.
  - exfalso. eapply lam_untypable. eassumption.
  - eapply tbox; [ exact hvt | ].
    eapply tlam.
    + eassumption.
    + eassumption.
    + assert (A' = A'0) by (eapply ext_functional; eassumption). subst. exact hsubC.
    + match goal with Hb : has_type (and B1 A_ann) e chk B_ann |- _ =>
        destruct (has_type_chk_inv _ _ _ Hb) as [T0 [Hinf Hsub0]];
        eapply tsub; [ exact Hinf | eapply sub_trans; [ exact Hsub0 | exact hsubB ] ]
      end.
Qed.

Lemma casting_typing : forall v A v', casting v A v' -> value v ->
  forall G T, has_type G v inf T -> has_type G v' inf A.
Proof.
  intros v A v' Hc. induction Hc; intros hv G T Hty.
  - (* cast_top *) apply tunit.
  - (* cast_int *) apply tlit.
  - (* cast_mrgl *) inversion hv; subst.
    destruct (merge_typing_left G v1 v2 T Hty) as [T1 [T2 [Heq Hu]]]. subst.
    eapply IHHc; eassumption.
  - (* cast_mrgr *) inversion hv; subst.
    destruct (merge_typing_right G v1 v2 T Hty) as [G0 [T1 [T2 [Heq Hu]]]]. subst.
    eapply IHHc.
    + exact H3.
    + apply (value_typing_indep v2 H3 G0 inf T2 Hu G).
  - (* cast_and *) eapply tcon.
    + eapply IHHc1; eassumption.
    + eapply IHHc2; eassumption.
    + eapply casting_value; [ exact Hc1 | exact hv ].
    + eapply casting_value; [ exact Hc2 | exact hv ].
    + eapply casts_consistent; eassumption.
  - (* cast_rcd *) inversion hv; subst.
    destruct (rec_typing_inv G x v T Hty) as [T0 [Heq Hv0]]; subst.
    apply trec. eapply IHHc; eassumption.
  - (* cast_arr *) inversion hv; subst.
    + destruct (box_typing_inv G v (ann (lam bl e) (arr A B)) T Hty) as [B1 [Hvt Hann]].
      eapply cast_arr_box_typing; [ exact H5 | exact H0 | exact H1 | exact H2 | exact H3 | exact Hvt | eexists; exact Hann ].
    + destruct (box_typing_inv G v (ann (lam wh e) (arr (rcd l A0) B)) T Hty) as [B1 [Hvt Hann]].
      eapply cast_arr_box_typing; [ exact H5 | exact H0 | eassumption | eassumption | eassumption | exact Hvt | eexists; exact Hann ].
  - (* cast_arr_tl *) eapply genv_typing. eassumption.
Qed.

(* ================= decidability of value ================= *)

Lemma value_ctx_false : value ctx -> False.
Proof. intros H. inversion H. Qed.
Lemma value_lam_false : forall fm e, value (lam fm e) -> False.
Proof. intros fm e H. inversion H. Qed.
Lemma value_ann_false : forall e A, value (ann e A) -> False.
Proof. intros e A H. inversion H. Qed.
Lemma value_app_false : forall e1 e2, value (app e1 e2) -> False.
Proof. intros e1 e2 H. inversion H. Qed.
Lemma value_proj_false : forall e x, value (proj e x) -> False.
Proof. intros e x H. inversion H. Qed.

Lemma value_dec : forall e, {value e} + {~ value e}.
Proof.
  induction e as [ i | | | e1 IHe1 e2 IHe2 | e0 IHe0 A | n e0 IHe0 | e0 IHe0 x | fm e0 IHe0 | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2 ].
  - left. apply vlit.
  - left. apply vunit.
  - right. intro H. inversion H.
  - destruct IHe1 as [h1|h1]; destruct IHe2 as [h2|h2].
    + left. apply vmrg; assumption.
    + right. intro H. inversion H. contradiction.
    + right. intro H. inversion H. contradiction.
    + right. intro H. inversion H. contradiction.
  - right. intro H. inversion H.
  - destruct IHe0 as [h|h].
    + left. apply vrec. assumption.
    + right. intro H. inversion H. contradiction.
  - right. intro H. inversion H.
  - right. intro H. inversion H.
  - right. intro H. inversion H.
  - destruct IHe1 as [h1|h1].
    + destruct e2 as [ i2 | | | m1 m2 | a A | n2 e2' | pr l | fm2 e2' | a1 a2 | b1 b2 ].
      * right. intro H. inversion H.
      * right. intro H. inversion H.
      * right. intro H. inversion H.
      * right. intro H. inversion H.
      * (* ann *) destruct a as [ i3 | | | m3 m4 | a0 A0b | n3 e3' | pr2 l3 | fm3 e3' | a3 a4 | b3 b4 ].
        -- right. intro H. inversion H.
        -- right. intro H. inversion H.
        -- right. intro H. inversion H.
        -- right. intro H. inversion H.
        -- right. intro H. inversion H.
        -- right. intro H. inversion H.
        -- right. intro H. inversion H.
        -- (* lam *) destruct A as [ | | Aa Ab | lab Cc | Aa Ab ].
           ++ right. intro H. inversion H.
           ++ right. intro H. inversion H.
           ++ right. intro H. inversion H.
           ++ right. intro H. inversion H.
           ++ destruct fm3.
              ** left. apply vclos. exact h1.
              ** destruct Aa as [ | | B1 B2 | l2 B0 | B1 B2 ].
                 --- right. intro H. inversion H.
                 --- right. intro H. inversion H.
                 --- right. intro H. inversion H.
                 --- left. apply vsclos. exact h1.
                 --- right. intro H. inversion H.
        -- right. intro H. inversion H.
        -- right. intro H. inversion H.
      * right. intro H. inversion H.
      * right. intro H. inversion H.
      * right. intro H. inversion H.
      * right. intro H. inversion H.
      * right. intro H. inversion H.
    + right. intro H. inversion H; contradiction.
Qed.

(* ================= totality of casting ================= *)

Lemma value_cast_exists : forall v, value v -> forall G A, has_type G v chk A -> exists v', casting v A v'.
Proof.
  intros v hv G A Hty. apply has_type_chk_inv in Hty as [T0 [Hinf Hsub]].
  pose proof (value_shape v hv G T0 Hinf) as Hsh.
  eapply shape_castable; eassumption.
Qed.

(* ================= progress ================= *)

Lemma progress : forall G e m T, has_type G e m T -> forall v, value v ->
  value e \/ (exists e', step v e e').
Proof.
  intros G e m T Hty. induction Hty; intros v hv.
  - (* tlit *) left. apply vlit.
  - (* tunit *) left. apply vunit.
  - (* tctx *) right. exists v. apply step_ctx. exact hv.
  - (* tmrg *) destruct (value_dec e1) as [h1|h1].
    + destruct (value_dec e2) as [h2|h2].
      * left. apply vmrg; assumption.
      * right. destruct (IHHty2 (merge v e1) (vmrg v e1 hv h1)) as [hval | [e2' Hstep]].
        -- contradiction.
        -- exists (merge e1 e2'). apply step_mrgr; assumption.
    + right. destruct (IHHty1 v hv) as [hval | [e1' Hstep]].
      * contradiction.
      * exists (merge e1' e2). apply step_mrgl. exact Hstep.
  - (* tcon *) left. apply vmrg; assumption.
  - (* tann *) destruct (value_dec e) as [h0|h0].
    + right. destruct (value_cast_exists e h0 G A Hty) as [v' Hcast].
      exists v'. apply step_annv; assumption.
    + right. destruct (IHHty v hv) as [hval | [e' Hstep]].
      * contradiction.
      * exists (ann e' A). apply step_anne. exact Hstep.
  - (* tlam *) right. exists (box v (ann (lam fm e) (arr A B))). apply step_switch. exact hv.
  - (* tapp *) destruct (value_dec e1) as [h1|h1].
    + destruct (value_shape e1 h1 G (arr A B) Hty1) as [v0 [e [fm [A0 [A' [Heq [hv0 [Hext [HsubA hval0]]]]]]]]]. subst.
      destruct (value_dec e2) as [h2|h2].
      * right. destruct (has_type_chk_inv G e2 A Hty2) as [T0 [Hinf Hsub0]].
        pose proof (value_shape e2 h2 G T0 Hinf) as Hsh.
        pose proof (sub_trans T0 A A' Hsub0 HsubA) as HsubT.
        destruct (shape_castable T0 A' HsubT e2 Hsh) as [v1' Hcast].
        destruct fm.
        -- exists (box (merge v0 v1') (ann e B)). eapply step_beta; eauto. apply constr_bl.
        -- destruct (ext_wh_inv A0 A' Hext) as [x [A0c [E1 E2]]]. subst.
           exists (box (merge v0 (rec x v1')) (ann e B)).
           eapply step_beta; eauto. apply constr_wh.
      * right. destruct (IHHty2 v hv) as [hval | [e2' Hstep]].
        -- contradiction.
        -- exists (app (box v0 (ann (lam fm e) (arr A0 B))) e2'). apply step_appr; [ exact Hstep | exact h1 ].
    + right. destruct (IHHty1 v hv) as [hval | [e1' Hstep]].
      * contradiction.
      * exists (app e1' e2). apply step_appl. exact Hstep.
  - (* tbox *) destruct (value_dec e1) as [h1|h1].
    + destruct (value_dec e2) as [h2|h2].
      * right. exists e2. apply step_boxv; assumption.
      * destruct (value_dec (box e1 e2)) as [hb|hb].
        { left. exact hb. }
        { right. destruct (IHHty2 e1 h1) as [hval | [e2' Hstep]].
          - contradiction.
          - exists (box e1 e2'). apply step_boxe; assumption. }
    + right. destruct (IHHty1 v hv) as [hval | [e1' Hstep]].
      * contradiction.
      * exists (box e1' e2). apply step_boxc; assumption.
  - (* tsub *) apply IHHty. exact hv.
  - (* trec *) destruct (value_dec e) as [h|h].
    + left. apply vrec. exact h.
    + right. destruct (IHHty v hv) as [hval | [e' Hstep]].
      * contradiction.
      * exists (rec x e'). apply step_rcde. exact Hstep.
  - (* tproj *) destruct (value_dec e) as [h|h].
    + destruct (value_shape e h G (rcd x A) Hty) as [v0 [Heq Hsh]]. subst.
      right. exists v0. apply step_projv; [ exact hv | eapply shape_value; exact Hsh ].
    + right. destruct (IHHty v hv) as [hval | [e' Hstep]].
      * contradiction.
      * exists (proj e' x). apply step_proje. exact Hstep.
Qed.

(* Any step derivation forces its environment to be a value. *)
Lemma step_value_env : forall v e e', step v e e' -> value v.
Proof.
  intros v e e' H. induction H; auto.
  - (* step_mrgr *) match goal with IH : value (merge _ _) |- value _ => inversion IH; assumption end.
Qed.

(* Values are normal forms: no step applies to them. *)
Lemma value_steps_false : forall e, value e -> forall v e', step v e e' -> False.
Proof.
  intros e Hv. induction Hv; intros v e' Hs.
  - inversion Hs.
  - inversion Hs.
  - inversion Hs; subst; eauto using IHHv1, IHHv2.
  - inversion Hs; subst; eauto using IHHv.
  - inversion Hs; subst.
    all: try solve [ eapply value_ann_false; eassumption ].
    all: try solve [ match goal with H : ~ value _ |- False => exact (H (vclos _ _ _ _ Hv)) end ].
    all: eauto using IHHv.
  - inversion Hs; subst.
    all: try solve [ eapply value_ann_false; eassumption ].
    all: try solve [ match goal with H : ~ value _ |- False => exact (H (vsclos _ _ _ _ _ Hv)) end ].
    all: eauto using IHHv.
Qed.

(* ================= preservation ================= *)

Lemma preservation : forall G e m T, has_type G e m T -> forall v e',
  has_type top v inf G -> step v e e' -> has_type G e' m T.
Proof.
  intros G e m T Hty. induction Hty; intros v e' Henv Hstep.
  - (* tlit *) inversion Hstep.
  - (* tunit *) inversion Hstep.
  - (* tctx *) inversion Hstep; subst.
    eapply value_typing_indep_inf; eassumption.
  - (* tmrg *) inversion Hstep; subst.
    + (* step_mrgr *)
      assert (Henv' : has_type top (merge v e1) inf (and G A)).
      { eapply tmrg.
        - exact Henv.
        - eapply value_typing_indep_inf with (v:=e1) (G:=G) (T:=A) (G':=and top G); eassumption.
        - eassumption.
        - apply disjoint_top_l. }
      eapply tmrg.
      * exact Hty1.
      * eapply IHHty2; eassumption.
      * eassumption.
      * eassumption.
    + (* step_mrgl *)
      eapply tmrg; [ eapply IHHty1; eassumption | exact Hty2 | eassumption | eassumption ].
  - (* tcon *) inversion Hstep; subst.
    + exfalso. eapply value_steps_false with (e:=v2); eassumption.
    + exfalso. eapply value_steps_false with (e:=v1); eassumption.
  - (* tann *) inversion Hstep; subst.
    + (* step_annv *)
      destruct (has_type_chk_inv G e A Hty) as [T0 [Hinf Hsub0]].
      exact (casting_typing e A e' H3 H5 G T0 Hinf).
    + (* step_anne *) exact (tann G e'0 A (IHHty v e'0 Henv H3)).
    + (* step_switch *) apply (tbox v (ann (lam fm e0) (arr A0 B)) (arr A0 B) G).
      * eapply value_typing_indep_inf; eassumption.
      * exact (tann G (lam fm e0) (arr A0 B) Hty).
  - (* tlam *) inversion Hstep; subst.
    + (* step_annv *) exfalso. eapply value_lam_false. eassumption.
    + (* step_anne *) match goal with H : step _ (lam _ _) _ |- _ => inversion H end.
    + (* step_switch *) apply (tbox v (ann (lam fm e) (arr A B)) (arr C B) G).
      * eapply value_typing_indep_inf; eassumption.
      * exact (tlam A e B G C fm A' H H0 H1 Hty).
  - (* tapp *) inversion Hstep; subst.
    + (* step_beta *)
      destruct (box_typing_inv G v2 (ann (lam fm e) (arr A0 B0)) (arr A B) Hty1) as [B1 [Hvt Hann]].
      inversion Hann; subst.
      * (* tann *) exfalso. eapply lam_untypable. eassumption.
      * (* tlam *)
        assert (Heq : A' = A'0) by (eapply ext_functional; eassumption). subst A'0.
        inversion H8; subst.
        -- (* constr_bl *)
           inversion H1; subst.
           destruct (has_type_chk_inv G e2 A Hty2) as [T0 [Hinf Hsub0]].
           assert (Hv3 : has_type G v3 inf A') by (exact (casting_typing e2 A' v3 H2 H4 G T0 Hinf)).
           assert (Hval3 : value v3) by (eapply casting_value; eassumption).
           assert (Hcons : consistencySpec v2 v3).
           { eapply disjoint_consistency with (G1:=G) (G2:=G) (A:=B1) (B:=A'); eassumption. }
           apply (tbox (merge v2 v3) (ann e B) B (and B1 A') G).
           { exact (tcon G v2 v3 B1 A' Hvt Hv3 H6 Hval3 Hcons). }
           { exact (tann (and B1 A') e B H15). }
        -- (* constr_wh *)
           destruct (ext_wh_inv (rcd x A1) A' H1) as [l [A0 [Heq1 Heq2]]].
           injection Heq1 as Hxl HA. subst l. subst A0. subst A'.
           destruct (has_type_chk_inv G e2 A Hty2) as [T0 [Hinf Hsub0]].
           assert (Hc : has_type G v1' inf A1) by (exact (casting_typing e2 A1 v1' H2 H4 G T0 Hinf)).
           assert (Hval3 : value (rec x v1')) by (apply vrec; eapply casting_value; eassumption).
           assert (Hv3 : has_type G (rec x v1') inf (rcd x A1)) by (exact (trec G v1' x A1 Hc)).
           assert (Hcons : consistencySpec v2 (rec x v1')).
           { eapply disjoint_consistency with (G1:=G) (G2:=G) (A:=B1) (B:=rcd x A1); eassumption. }
           apply (tbox (merge v2 (rec x v1')) (ann e B) B (and B1 (rcd x A1)) G).
           { exact (tcon G v2 (rec x v1') B1 (rcd x A1) Hvt Hv3 H6 Hval3 Hcons). }
           { exact (tann (and B1 (rcd x A1)) e B H15). }
    + (* step_appl *) exact (tapp G e1' e2 A B (IHHty1 v e1' Henv H3) Hty2).
    + (* step_appr *) exact (tapp G e1 e2' A B Hty1 (IHHty2 v e2' Henv H2)).
  - (* tbox *) inversion Hstep; subst.
    + (* step_boxv *) exact (value_typing_indep_inf e' H5 B A Hty2 G).
    + (* step_boxe *)
      assert (Hval1 : value e1) by (eapply step_value_env; eassumption).
      assert (Henv' : has_type top e1 inf B).
      { eapply value_typing_indep_inf with (v:=e1) (G:=G) (T:=B); eassumption. }
      eapply tbox.
      * exact Hty1.
      * eapply IHHty2; eassumption.
    + (* step_boxc *) eapply tbox; [ eapply IHHty1; eassumption | exact Hty2 ].
  - (* tsub *) eapply tsub; [ eapply IHHty; eassumption | exact H ].
  - (* trec *) inversion Hstep; subst. exact (trec G e'0 x A (IHHty v e'0 Henv H3)).
  - (* tproj *) inversion Hstep; subst.
    + (* step_projv *)
      destruct (rec_typing_inv G x e' (rcd x A) Hty) as [T0 [Heq Hv]].
      injection Heq as Heq. subst. exact Hv.
    + (* step_proje *) exact (tproj G e'0 x A (IHHty v e'0 Henv H3)).
Qed.

(* ================= type safety ================= *)

Lemma star_safety : forall G m A v, value v -> has_type top v inf G ->
  forall e e', star exp (step v) e e' -> has_type G e m A ->
  value e' \/ (exists e'', step v e' e'').
Proof.
  intros G m A v hv Henv e e' Hstar.
  induction Hstar; intros Hty.
  - eapply progress; eassumption.
  - eapply IHHstar. eapply preservation; eassumption.
Qed.

Notation "v |- e ->* e'" := ((star exp (step v)) e e') (at level 68).

Theorem gen_type_safety : forall G e m A,
  has_type G e m A -> forall v e',
  value v ->
  has_type top v inf G ->
  v |- e ->* e' ->
  value e' \/
  (exists e'', step v e' e'').
Proof.
  intros G e m A Hty v e' hv Henv Hstar.
  eapply star_safety; eassumption.
Qed.
