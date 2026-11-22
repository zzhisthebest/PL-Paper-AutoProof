Require Import Program.Equality.

Require Import Metalib.Metatheory.

Require Import Language Infra SubDis.

Fixpoint principal_type (v:exp) : typ :=
  match v with
  | unit => top
  | lit i5 => int
  | box e1 (ann (lam bl e) (arr A B)) => arr A B
  | box e1 (ann (lam wh e) (arr (rcd l A) B)) => arr A B
  | merge v1 v2 => and (principal_type v1) (principal_type v2)
  | rec l v1 => rcd l (principal_type v1)
  | _ => top
  end.

Definition old_dis A B :=
  forall C, sub A C -> sub B C -> toplike C.

(* ============ subtype basics ============ *)

Lemma sub_refl: forall A, sub A A.
Proof.
  induction A; eauto using sub, sandl, sandr.
Qed.

(* A computable "gord witness" inside a type *)
Fixpoint gordpart (A:typ) : option typ :=
  match A with
  | int => Some int
  | top => None
  | and A1 A2 => match gordpart A1 with Some C => Some C | None => gordpart A2 end
  | rcd n B => match gordpart B with Some C => Some (rcd n C) | None => None end
  | arr A1 B => match gordpart B with Some C => Some (arr A1 C) | None => None end
  end.

Lemma gordpart_gord_aux: forall A, match gordpart A with Some C => gord C | None => True end.
Proof.
  induction A; simpl.
  - constructor.
  - exact I.
  - destruct (gordpart A1) as [C1|] eqn:E; simpl in *; auto.
  - destruct (gordpart A) as [C1|] eqn:E; simpl in *.
    + constructor; auto.
    + exact I.
  - destruct (gordpart A2) as [C1|] eqn:E; simpl in *.
    + constructor; auto.
    + exact I.
Qed.

Lemma gordpart_gord: forall A C, gordpart A = Some C -> gord C.
Proof. intros A C E. pose proof (gordpart_gord_aux A). rewrite E in H. exact H. Qed.

Lemma gordpart_none_aux: forall A, match gordpart A with Some _ => True | None => toplike A end.
Proof.
  induction A; simpl.
  - exact I.
  - constructor.
  - destruct (gordpart A1) as [C1|] eqn:E; simpl in *.
    + exact I.
    + destruct (gordpart A2) as [C2|] eqn:E2; simpl in *.
      * exact I.
      * apply TL_and; auto.
  - destruct (gordpart A) as [C1|] eqn:E; simpl in *.
    + exact I.
    + apply TL_rcd; auto.
  - destruct (gordpart A2) as [C1|] eqn:E; simpl in *.
    + exact I.
    + apply TL_arr; auto.
Qed.

Lemma gordpart_none_toplike: forall A, gordpart A = None -> toplike A.
Proof. intros A E. pose proof (gordpart_none_aux A). rewrite E in H. exact H. Qed.

Lemma gordpart_some: forall A, ~ toplike A -> exists C, gordpart A = Some C.
Proof.
  intros A H. destruct (gordpart A) as [C|] eqn:E.
  - exists C; auto.
  - exfalso; apply H; apply gordpart_none_toplike; auto.
Qed.

Lemma sub_gordpart_aux: forall A D, sub A D ->
  match gordpart D with Some C => sub A C | None => True end.
Proof.
  intros A D H. induction H; simpl.
  - apply sint.
  - exact I.
  - destruct (gordpart B) as [C1|] eqn:E; simpl in *; auto.
  - destruct (gordpart C) as [C1|] eqn:E; simpl in *.
    + apply sandl; auto.
    + exact I.
  - destruct (gordpart C) as [C1|] eqn:E; simpl in *.
    + apply sandr; auto.
    + exact I.
  - destruct (gordpart B) as [C1|] eqn:E; simpl in *.
    + apply srcd; auto.
    + exact I.
  - destruct (gordpart D) as [C1|] eqn:E; simpl in *.
    + eapply sarr; eauto.
    + exact I.
Qed.

Lemma sub_gordpart: forall A D C, sub A D -> gordpart D = Some C -> sub A C.
Proof. intros A D C H E. pose proof (sub_gordpart_aux A D H). rewrite E in H0. exact H0. Qed.

Lemma gord_of_nontoplike: forall A, ~ toplike A -> exists C, gord C /\ sub A C.
Proof.
  intros A H. destruct (gordpart_some A H) as [C E].
  exists C; split.
  - apply gordpart_gord with (A:=A); auto.
  - apply sub_gordpart with (D:=A); [apply sub_refl | auto].
Qed.

Lemma sub2_gord: forall A B D,
  sub A D -> sub B D -> ~ toplike D ->
  exists C, gord C /\ sub A C /\ sub B C.
Proof.
  intros A B D HA HB Hnt.
  destruct (gordpart_some D Hnt) as [C E].
  exists C; split.
  - apply gordpart_gord with (A:=D); auto.
  - split.
    + apply sub_gordpart with (D:=D); auto.
    + apply sub_gordpart with (D:=D); auto.
Qed.

(* ============ genv ============ *)
Lemma genv_value: forall A v, genv A v -> value v.
Proof.
  intros A v H. induction H.
  - constructor.
  - apply vclos; constructor.
  - apply vmrg; assumption.
  - apply vrec; assumption.
Qed.

Lemma genv_functional: forall A v1, genv A v1 -> forall v2, genv A v2 -> v1 = v2.
Proof.
  intros A v1 H. induction H; intros w2 H2.
  - inversion H2; subst; reflexivity.
  - inversion H2; subst. repeat f_equal. eapply IHgenv. eassumption.
  - inversion H2; subst. f_equal; eauto.
  - inversion H2; subst. repeat f_equal. eapply IHgenv. eassumption.
Qed.

(* ============ casting basics ============ *)
Lemma casting_value: forall v A v', casting v A v' -> value v'.
Proof.
  intros v A v' H. induction H.
  - constructor.
  - constructor.
  - assumption.
  - assumption.
  - apply vmrg; assumption.
  - apply vrec; assumption.
  - destruct fm.
    + apply vclos; assumption.
    + inversion H1; subst. apply vsclos; assumption.
  - apply genv_value with (A:=arr C D); assumption.
Qed.

Lemma ord_top_false: ord top -> False.
Proof. intros H; inversion H. Qed.

Lemma ord_and_false: forall A B, ord (and A B) -> False.
Proof. intros A B H; inversion H. Qed.

Lemma casting_top_res: forall v v', casting v top v' -> v' = unit.
Proof.
  intros v v' H. inversion H; subst; try reflexivity; exfalso; eauto using ord_top_false.
Qed.

Lemma int_sub: forall v X v', casting v X v' -> X = int ->
  forall G A, has_type G v inf A -> sub A int.
Proof.
  intros v X v' H. induction H; intros Heq G A0 Hty.
  - (* cast_top *) discriminate Heq.
  - (* cast_int *) inversion Hty; subst; apply sub_refl.
  - (* cast_mrgl *) inversion Heq; subst; inversion Hty; subst.
    all: (eapply sandl; eapply IHcasting; [reflexivity | eassumption]).
  - (* cast_mrgr *) inversion Heq; subst; inversion Hty; subst.
    all: (eapply sandr; eapply IHcasting; [reflexivity | eassumption]).
  - (* cast_and *) discriminate Heq.
  - (* cast_rcd *) discriminate Heq.
  - (* cast_arr *) discriminate Heq.
  - (* cast_arr_tl *) discriminate Heq.
Qed.

Lemma casting_arr_tl_genv: forall v X v',
  casting v X v' -> forall C0 D0, X = arr C0 D0 -> toplike D0 -> genv (arr C0 D0) v'.
Proof.
  intros v X v' H. induction H; intros C0 D0 Heq Htl.
  - (* cast_top *) discriminate Heq.
  - (* cast_int *) discriminate Heq.
  - (* cast_mrgl *) inversion Heq; subst.
    eapply IHcasting; [reflexivity | assumption].
  - (* cast_mrgr *) inversion Heq; subst.
    eapply IHcasting; [reflexivity | assumption].
  - (* cast_and *) discriminate Heq.
  - (* cast_rcd *) discriminate Heq.
  - (* cast_arr *) inversion Heq; subst. exfalso; auto.
  - (* cast_arr_tl *) inversion Heq; subst. assumption.
Qed.

(* ============ irreducibility of values ============ *)
Lemma value_irred: forall v, value v -> forall w e, step w v e -> False.
Proof.
  intros v H. induction H; intros w e' Hstep.
  - inversion Hstep.
  - inversion Hstep.
  - inversion Hstep; subst; eauto.
  - inversion Hstep; subst; eauto.
  - inversion Hstep; subst.
    + match goal with Hv : value (ann _ _) |- False => inversion Hv end.
    + exfalso. apply H6. apply vclos. exact H.
    + eapply IHvalue; eassumption.
  - inversion Hstep; subst.
    + match goal with Hv : value (ann _ _) |- False => inversion Hv end.
    + exfalso. apply H6. apply vsclos. exact H.
    + eapply IHvalue; eassumption.
Qed.

Lemma step_value_env: forall v e e', step v e e' -> value v.
Proof.
  intros v e e' H. induction H.
  - assumption.
  - assumption.
  - assumption.
  - (* mrgr *) inversion IHstep; subst; assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
  - assumption.
Qed.

(* ============ ext / constr functionality ============ *)
Lemma ext_functional: forall A fm A1, ext A fm A1 -> forall A2, ext A fm A2 -> A1 = A2.
Proof.
  intros A fm A1 H. induction H; intros A2 H2; inversion H2; subst; reflexivity.
Qed.

Lemma constr_functional: forall A v fm v1, constr A v fm v1 -> forall v2, constr A v fm v2 -> v1 = v2.
Proof.
  intros A v fm v1 H. destruct H; intros v2 H2; inversion H2; subst; reflexivity.
Qed.

(* ============ disjointness helpers ============ *)
Lemma disjoint_sym: forall A B, disjoint A B -> disjoint B A.
Proof.
  intros A B H [C [Hg [H1 H2]]]. apply H. exists C; auto.
Qed.

Lemma disjoint_and_l: forall A B C, disjoint (and A B) C -> disjoint A C.
Proof.
  intros A B C H [D [Hg [H1 H2]]]. apply H.
  exists D; split; [auto|]. split; [apply sandl; auto|auto].
Qed.

Lemma disjoint_and_r: forall A B C, disjoint (and A B) C -> disjoint B C.
Proof.
  intros A B C H [D [Hg [H1 H2]]]. apply H.
  exists D; split; [auto|]. split; [apply sandr; auto|auto].
Qed.

Lemma disjoint_rcd: forall n A B, disjoint (rcd n A) (rcd n B) -> disjoint A B.
Proof.
  intros n A B H [D [Hg [H1 H2]]]. apply H.
  exists (rcd n D); split; [constructor; auto|]. split; apply srcd; auto.
Qed.

Lemma disjoint_to_and_l: forall A B C, disjoint A (and B C) -> disjoint A B.
Proof.
  intros A B C H. apply disjoint_sym in H. apply disjoint_sym.
  apply disjoint_and_l in H. auto.
Qed.

Lemma disjoint_to_and_r: forall A B C, disjoint A (and B C) -> disjoint A C.
Proof.
  intros A B C H. apply disjoint_sym in H. apply disjoint_sym.
  apply disjoint_and_r in H. auto.
Qed.

(* ============ typing inversion for values ============ *)
Lemma rec_inf_ty: forall G n w A, has_type G (rec n w) inf A ->
  exists A0, A = rcd n A0 /\ has_type G w inf A0.
Proof. intros G n w A H. inversion H; subst; eauto. Qed.

Lemma merge_inf_comp: forall G a1 a2 A, has_type G (merge a1 a2) inf A ->
  exists A1 A2 G', A = and A1 A2 /\ has_type G a1 inf A1 /\ has_type G' a2 inf A2.
Proof.
  intros G a1 a2 A H. inversion H; subst.
  - eexists A0, B, (and G A0); eauto.
  - eexists A0, B, G; eauto.
Qed.

Lemma box_inf_arr: forall G e1 fm e Aa Ba A,
  has_type G (box e1 (ann (lam fm e) (arr Aa Ba))) inf A ->
  exists C, A = arr C Ba.
Proof.
  intros G e1 fm e Aa Ba A H. inversion H; subst.
  match goal with
  | Hann : has_type _ (ann (lam _ _) (arr _ _)) inf _ |- _ =>
      inversion Hann; subst
  end.
  - eexists; reflexivity.
  - eexists; reflexivity.
Qed.

Lemma disj_and_and_l: forall A1 A2 B1 B2, disjoint (and A1 A2) (and B1 B2) -> disjoint A1 B1.
Proof. intros A1 A2 B1 B2 H. apply (disjoint_to_and_l A1 B1 B2). apply disjoint_and_l in H. exact H. Qed.
Lemma disj_and_and_lr: forall A1 A2 B1 B2, disjoint (and A1 A2) (and B1 B2) -> disjoint A1 B2.
Proof. intros A1 A2 B1 B2 H. apply (disjoint_to_and_r A1 B1 B2). apply disjoint_and_l in H. exact H. Qed.
Lemma disj_and_and_rl: forall A1 A2 B1 B2, disjoint (and A1 A2) (and B1 B2) -> disjoint A2 B1.
Proof. intros A1 A2 B1 B2 H. apply (disjoint_to_and_l A2 B1 B2). apply disjoint_and_r in H. exact H. Qed.
Lemma disj_and_and_r: forall A1 A2 B1 B2, disjoint (and A1 A2) (and B1 B2) -> disjoint A2 B2.
Proof. intros A1 A2 B1 B2 H. apply (disjoint_to_and_r A2 B1 B2). apply disjoint_and_r in H. exact H. Qed.

(* ============ value shape inversion ============ *)
Lemma value_merge_inv: forall a b, value (merge a b) -> value a /\ value b.
Proof. intros a b H; inversion H; subst; auto. Qed.

Lemma value_rec_inv: forall n w, value (rec n w) -> value w.
Proof. intros n w H; inversion H; subst; auto. Qed.

Lemma value_box_inv: forall e1 e2, value (box e1 e2) ->
  value e1 /\ exists fm e Aa Ba, e2 = ann (lam fm e) (arr Aa Ba).
Proof.
  intros e1 e2 H. inversion H; subst.
  - split; [assumption|]. eexists bl, e, A, B; reflexivity.
  - split; [assumption|]. eexists wh, e, (rcd l A), B; reflexivity.
Qed.

(* ============ cast shape inversion ============ *)
Lemma casting_merge_ord_inv: forall a1 a2 X v,
  ord X -> casting (merge a1 a2) X v ->
  (exists v1, casting a1 X v1 /\ v = v1) \/ (exists v2, casting a2 X v2 /\ v = v2).
Proof.
  intros a1 a2 X v Hord Hc. inversion Hc; subst.
  - exfalso; inversion Hord.
  - left; eauto.
  - right; eauto.
  - exfalso; inversion Hord.
Qed.

Lemma casting_rec_ord_inv: forall n w X v,
  ord X -> casting (rec n w) X v ->
  exists X0 v0, X = rcd n X0 /\ casting w X0 v0 /\ v = rec n v0.
Proof.
  intros n w X v Hord Hc. inversion Hc; subst.
  - exfalso; inversion Hord.
  - exfalso; inversion Hord.
  - exists A, v'; repeat split; auto.
Qed.

Lemma casting_box_arr_inv: forall v0 fm e Aa Ba X1 X2 v,
  casting (box v0 (ann (lam fm e) (arr Aa Ba))) (arr X1 X2) v ->
  ( exists A', value v0 /\ ~ toplike X2 /\ ext Aa fm A' /\ sub X1 A' /\ sub Ba X2 /\
       v = box v0 (ann (lam fm e) (arr Aa X2)))
  \/ (toplike X2 /\ genv (arr X1 X2) v).
Proof.
  intros v0 fm e Aa Ba X1 X2 v H. inversion H; subst.
  - left. eexists. repeat split; eauto.
  - right. split; eauto.
Qed.

(* ============ pairwise casting determinism for disjoint values ============ *)
Lemma cast_det_disj : forall X,
  forall a, value a -> forall Ga A, has_type Ga a inf A ->
  forall b, value b -> forall Gb B, has_type Gb b inf B ->
  disjoint A B ->
  forall va vb, casting a X va -> casting b X vb -> va = vb.
Proof.
  induction X as [| |X1 IH1 X2 IH2|n X0 IH0|X1 IH1 X2 IH2].
  - (* int *)
    intros a Hva Ga A Hta b Hvb Gb B Htb Hdisj va vb Ca Cb.
    exfalso. apply Hdisj. exists int. split; [constructor|].
    split.
    + exact (int_sub a int va Ca eq_refl Ga A Hta).
    + exact (int_sub b int vb Cb eq_refl Gb B Htb).
  - (* top *)
    intros a Hva Ga A Hta b Hvb Gb B Htb Hdisj va vb Ca Cb.
    rewrite (casting_top_res a va Ca), (casting_top_res b vb Cb). reflexivity.
  - (* and X1 X2 *)
    intros a Hva Ga A Hta b Hvb Gb B Htb Hdisj va vb Ca Cb.
    inversion Ca; subst;
      try match goal with Ho : ord (and _ _) |- _ => exfalso; inversion Ho end.
    inversion Cb; subst;
      try match goal with Ho : ord (and _ _) |- _ => exfalso; inversion Ho end.
    f_equal.
    + exact (IH1 a Hva Ga A Hta b Hvb Gb B Htb Hdisj v1 v0 H2 H3).
    + exact (IH2 a Hva Ga A Hta b Hvb Gb B Htb Hdisj v2 v3 H4 H6).
  - (* rcd n X0 *)
    intros a. induction a as [i| | |m1 IHm1 m2 IHm2|eann IHeann tann|nr wr IHwr|eproj IHeproj nproj|fma ebody IHebody|q1 IHq1 q2 IHq2|bv IHbv be2 IHbe2].
    + intros Hva Ga A Hta b Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Ca.
    + intros Hva Ga A Hta b Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Ca.
    + intros Hva Ga A Hta b Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Ca.
    + (* merge m1 m2 *) intros Hva Ga A Hta.
      destruct (value_merge_inv m1 m2 Hva) as (Hva1 & Hva2).
      destruct (merge_inf_comp Ga m1 m2 A Hta) as (A1 & A2 & G' & Heq & Hta1 & Hta2). subst A.
      intros b Hvb Gb B Htb Hdisj va vb Ca Cb.
      assert (D1 : disjoint A1 B) by (apply (disjoint_and_l A1 A2 B); exact Hdisj).
      assert (D2 : disjoint A2 B) by (apply (disjoint_and_r A1 A2 B); exact Hdisj).
      destruct (casting_merge_ord_inv m1 m2 (rcd n X0) va (O_rcd n X0) Ca)
        as [[v1 [Ha1 Heq]]|[v2 [Ha2 Heq]]]; subst va.
      * exact (IHm1 Hva1 Ga A1 Hta1 b Hvb Gb B Htb D1 v1 vb Ha1 Cb).
      * exact (IHm2 Hva2 G' A2 Hta2 b Hvb Gb B Htb D2 v2 vb Ha2 Cb).
    + intros Hva Ga A Hta b Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Ca.
    + (* rec nr wr *) intros Hva Ga A Hta.
      destruct (rec_inf_ty Ga nr wr A Hta) as (A0 & Heq & Hta0). subst A.
      intros b. induction b as [ib| | |c1 IHc1 c2 IHc2|ecc IHecc tcc|nc wc IHwc|ecc2 IHecc2 nc2|fmc ecc3 IHecc3|qc1 IHqc1 qc2 IHqc2|cb1 IHcb1 cb2 IHcb2].
      * intros Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Cb.
      * intros Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Cb.
      * intros Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Cb.
      * (* b merge c1 c2 *) intros Hvb Gb B Htb Hdisj va vb Ca Cb.
        destruct (value_merge_inv c1 c2 Hvb) as (Hvb1 & Hvb2).
        destruct (merge_inf_comp Gb c1 c2 B Htb) as (B1 & B2 & Gb' & HeqB & Htb1 & Htb2). subst B.
        destruct (casting_merge_ord_inv c1 c2 (rcd n X0) vb (O_rcd n X0) Cb)
          as [[w1 [Hb1 Heq]]|[w2 [Hb2 Heq]]]; subst vb;
        destruct (casting_rec_ord_inv nr wr (rcd n X0) va (O_rcd n X0) Ca)
          as (Xa & v0 & HeqX & Cw & Heqva); inversion HeqX; subst;
        assert (D1 : disjoint (rcd nr A0) B1) by
          (apply (disjoint_to_and_l (rcd nr A0) B1 B2); exact Hdisj);
        assert (D2 : disjoint (rcd nr A0) B2) by
          (apply (disjoint_to_and_r (rcd nr A0) B1 B2); exact Hdisj).
        all: (solve [eapply IHc1; eauto] || solve [eapply IHc2; eauto]).
      * intros Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Cb.
      * (* b rec nc wc *) intros Hvb Gb B Htb Hdisj va vb Ca Cb.
        destruct (rec_inf_ty Gb nc wc B Htb) as (B0 & HeqB & Htb0). subst B.
        pose proof (value_rec_inv nc wc Hvb) as Hvwb.
        pose proof (value_rec_inv nr wr Hva) as Hvw.
        destruct (casting_rec_ord_inv nr wr (rcd n X0) va (O_rcd n X0) Ca)
          as (Xa & v0 & HeqX & Cw & Heqva).
        destruct (casting_rec_ord_inv nc wc (rcd n X0) vb (O_rcd n X0) Cb)
          as (Xb & v0' & HeqX2 & Cw2 & Heqvb).
        inversion HeqX; subst. inversion HeqX2; subst.
        match goal with HD : disjoint (rcd ?k A0) (rcd ?k B0) |- _ =>
          assert (D0 : disjoint A0 B0) by (apply (disjoint_rcd k A0 B0); exact HD) end.
        f_equal.
        exact (IH0 wr Hvw Ga A0 Hta0 wc Hvwb Gb B0 Htb0 D0 v0 v0' Cw Cw2).
      * intros Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Cb.
      * intros Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Cb.
      * intros Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Cb.
      * intros Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Cb.
    + intros Hva Ga A Hta b Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Ca.
    + intros Hva Ga A Hta b Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Ca.
    + intros Hva Ga A Hta b Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Ca.
    + intros Hva Ga A Hta b Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Ca.
  - (* arr X1 X2 *)
    intros a. induction a as [i| | |m1 IHm1 m2 IHm2|eann IHeann tann|nr wr IHwr|eproj IHeproj nproj|fma ebody IHebody|q1 IHq1 q2 IHq2|bv IHbv be2 IHbe2].
    + intros Hva Ga A Hta b Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Ca.
    + intros Hva Ga A Hta b Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Ca.
    + intros Hva Ga A Hta b Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Ca.
    + (* merge m1 m2 *) intros Hva Ga A Hta.
      destruct (value_merge_inv m1 m2 Hva) as (Hva1 & Hva2).
      destruct (merge_inf_comp Ga m1 m2 A Hta) as (A1 & A2 & G' & Heq & Hta1 & Hta2). subst A.
      intros b Hvb Gb B Htb Hdisj va vb Ca Cb.
      assert (D1 : disjoint A1 B) by (apply (disjoint_and_l A1 A2 B); exact Hdisj).
      assert (D2 : disjoint A2 B) by (apply (disjoint_and_r A1 A2 B); exact Hdisj).
      destruct (casting_merge_ord_inv m1 m2 (arr X1 X2) va (O_arrow X1 X2) Ca)
        as [[v1 [Ha1 Heq]]|[v2 [Ha2 Heq]]]; subst va.
      * exact (IHm1 Hva1 Ga A1 Hta1 b Hvb Gb B Htb D1 v1 vb Ha1 Cb).
      * exact (IHm2 Hva2 G' A2 Hta2 b Hvb Gb B Htb D2 v2 vb Ha2 Cb).
    + intros Hva Ga A Hta b Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Ca.
    + intros Hva Ga A Hta b Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Ca.
    + intros Hva Ga A Hta b Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Ca.
    + intros Hva Ga A Hta b Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Ca.
    + intros Hva Ga A Hta b Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Ca.
    + (* box bv be2 *) intros Hva Ga A Hta.
      destruct (value_box_inv bv be2 Hva) as (Hva1 & fm & eb & Aa & Ba & Heq2). subst be2.
      destruct (box_inf_arr Ga bv fm eb Aa Ba A Hta) as (C & HeqA). subst A.
      intros b. induction b as [ib| | |c1 IHc1 c2 IHc2|ecc IHecc tcc|nc wc IHwc|ecc2 IHecc2 nc2|fmc ecc3 IHecc3|qc1 IHqc1 qc2 IHqc2|cb1 IHcb1 cb2 IHcb2].
      * intros Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Cb.
      * intros Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Cb.
      * intros Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Cb.
      * (* b merge c1 c2 *) intros Hvb Gb B Htb Hdisj va vb Ca Cb.
        destruct (value_merge_inv c1 c2 Hvb) as (Hvb1 & Hvb2).
        destruct (merge_inf_comp Gb c1 c2 B Htb) as (B1 & B2 & Gb' & HeqB & Htb1 & Htb2). subst B.
        assert (D1 : disjoint (arr C Ba) B1) by (apply (disjoint_to_and_l (arr C Ba) B1 B2); exact Hdisj).
        assert (D2 : disjoint (arr C Ba) B2) by (apply (disjoint_to_and_r (arr C Ba) B1 B2); exact Hdisj).
        destruct (casting_merge_ord_inv c1 c2 (arr X1 X2) vb (O_arrow X1 X2) Cb)
          as [[w1 [Hb1 Heq]]|[w2 [Hb2 Heq]]]; subst vb.
        -- eapply IHc1; eauto.
        -- eapply IHc2; eauto.
      * intros Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Cb.
      * intros Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Cb.
      * intros Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Cb.
      * intros Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Cb.
      * intros Hvb Gb B Htb Hdisj va vb Ca Cb. inversion Cb.
      * (* b box cb1 cb2 *) intros Hvb Gb B Htb Hdisj va vb Ca Cb.
        destruct (value_box_inv cb1 cb2 Hvb) as (Hvb1 & fmb & ebb & Ab & Bb & Heq2b). subst cb2.
        destruct (box_inf_arr Gb cb1 fmb ebb Ab Bb B Htb) as (C' & HeqB). subst B.
        destruct (casting_box_arr_inv bv fm eb Aa Ba X1 X2 va Ca)
          as [(A' & Hva1' & Hntl & Hext & HsubX & HsubBa & Heqva) |
              (Htl & Hgv)].
        -- destruct (casting_box_arr_inv cb1 fmb ebb Ab Bb X1 X2 vb Cb)
             as [(B' & Hvb1' & Hntl2 & Hext2 & HsubX2 & HsubBb & Heqvb) |
                 (Htl2 & Hgv2)].
           ++ (* arr/arr *) subst va; subst vb. exfalso. apply Hdisj.
              destruct (sub2_gord Ba Bb X2 HsubBa HsubBb Hntl) as (Y & HgY & HBa & HBb).
              exists (arr (and C C') Y). split; [constructor; assumption|]. split.
              ** apply sarr with (C:=and C C'); [apply sandl; apply sub_refl | assumption].
              ** apply sarr with (C:=and C C'); [apply sandr; apply sub_refl | assumption].
           ++ (* arr / tl *) exfalso; auto.
        -- destruct (casting_box_arr_inv cb1 fmb ebb Ab Bb X1 X2 vb Cb)
             as [(B' & Hvb1' & Hntl2 & Hext2 & HsubX2 & HsubBb & Heqvb) |
                 (Htl2 & Hgv2)].
           ++ (* tl / arr *) exfalso; auto.
           ++ (* tl / tl *)
              exact (genv_functional (arr X1 X2) va Hgv vb Hgv2).
Qed.

Lemma merge_inf_cases: forall G a1 a2 A, has_type G (merge a1 a2) inf A ->
  (exists A1 A2, A = and A1 A2 /\ has_type G a1 inf A1 /\ has_type G a2 inf A2 /\
     consistencySpec a1 a2)
  \/ (exists A1 A2 G', A = and A1 A2 /\ has_type G a1 inf A1 /\ has_type G' a2 inf A2 /\
     disjoint A1 A2).
Proof.
  intros G a1 a2 A H. inversion H; subst.
  - right. eexists A0, B, (and G A0). repeat split; eassumption.
  - left. eexists A0, B. repeat split; eassumption.
Qed.

(* ============ casting determinism for inf-typable values ============ *)
Lemma cast_det_typed : forall X, forall v, value v -> forall G A, has_type G v inf A ->
  forall v1 v2, casting v X v1 -> casting v X v2 -> v1 = v2.
Proof.
  induction X as [| |X1 IH1 X2 IH2|n X0 IH0|X1 IH1 X2 IH2].
  - (* int *)
    intros v. induction v as [i| | |m1 IHm1 m2 IHm2|ea ta|nr wr IHwr|ep npr|fm eb IHfb|q1 IHq1 q2 IHq2|bv IHvb be2 IHbe2];
      intros Hva G A Hta v1 v2 C1 C2.
    + inversion C1; subst; inversion C2; subst; reflexivity.
    + inversion C1.
    + inversion C1.
    + (* merge *)
      destruct (value_merge_inv m1 m2 Hva) as (Hv1 & Hv2).
      destruct (merge_inf_cases G m1 m2 A Hta) as
        [(A1 & A2 & Heq & Ht1 & Ht2 & Hcons) | (A1 & A2 & G' & Heq & Ht1 & Ht2 & Hdisj)].
      * assert (E12 : forall x y, casting m1 int x -> casting m2 int y -> x = y)
          by (intros x y Cx Cy; exact (Hcons _ x y Cx Cy)).
        assert (E21 : forall x y, casting m2 int x -> casting m1 int y -> x = y)
          by (intros x y Cx Cy; symmetry; exact (Hcons _ y x Cy Cx)).
        inversion C1; subst; inversion C2; subst.
        all: try solve [eapply IHm1; eauto].
        all: try solve [eapply IHm2; eauto].
        all: try solve [eapply E12; eauto].
        all: try solve [eapply E21; eauto].
      * inversion C1; subst; inversion C2; subst.
        all: try solve [eapply IHm1; eauto].
        all: try solve [eapply IHm2; eauto].
        all: try solve [eauto 15 using IHm1, IHm2, cast_det_disj, disjoint_sym].
    + inversion C1.
    + inversion C1.
    + inversion C1.
    + inversion C1.
    + inversion C1.
    + inversion C1.
  - (* top *)
    intros v Hva G A Hta v1 v2 C1 C2.
    rewrite (casting_top_res v v1 C1). rewrite (casting_top_res v v2 C2). reflexivity.
  - (* and X1 X2 *)
    intros v Hva G A Hta v1 v2 C1 C2.
    inversion C1; subst;
      try match goal with Ho : ord (and _ _) |- _ => exfalso; inversion Ho end.
    inversion C2; subst;
      try match goal with Ho : ord (and _ _) |- _ => exfalso; inversion Ho end.
    f_equal.
    + eapply IH1; eauto.
    + eapply IH2; eauto.
  - (* rcd n X0 *)
    intros v. induction v as [i| | |m1 IHm1 m2 IHm2|ea ta|nr wr IHwr|ep npr|fm eb IHfb|q1 IHq1 q2 IHq2|bv IHvb be2 IHbe2];
      intros Hva G A Hta v1 v2 C1 C2.
    + inversion C1.
    + inversion C1.
    + inversion C1.
    + (* merge *)
      destruct (value_merge_inv m1 m2 Hva) as (Hv1 & Hv2).
      destruct (merge_inf_cases G m1 m2 A Hta) as
        [(A1 & A2 & Heq & Ht1 & Ht2 & Hcons) | (A1 & A2 & G' & Heq & Ht1 & Ht2 & Hdisj)].
      * assert (E12 : forall x y, casting m1 (rcd n X0) x -> casting m2 (rcd n X0) y -> x = y)
          by (intros x y Cx Cy; exact (Hcons _ x y Cx Cy)).
        assert (E21 : forall x y, casting m2 (rcd n X0) x -> casting m1 (rcd n X0) y -> x = y)
          by (intros x y Cx Cy; symmetry; exact (Hcons _ y x Cy Cx)).
        inversion C1; subst; inversion C2; subst.
        all: try solve [eapply IHm1; eauto].
        all: try solve [eapply IHm2; eauto].
        all: try solve [eapply E12; eauto].
        all: try solve [eapply E21; eauto].
      * inversion C1; subst; inversion C2; subst.
        all: try solve [eapply IHm1; eauto].
        all: try solve [eapply IHm2; eauto].
        all: try solve [eauto 15 using IHm1, IHm2, cast_det_disj, disjoint_sym].
    + inversion C1.
    + (* rec nr wr *)
      destruct (rec_inf_ty G nr wr A Hta) as (A0 & Heq & Hta0). subst A.
      pose proof (value_rec_inv nr wr Hva) as Hvw.
      inversion C1; subst; inversion C2; subst. f_equal.
      eapply IH0; eauto.
    + inversion C1.
    + inversion C1.
    + inversion C1.
    + inversion C1.
  - (* arr X1 X2 *)
    intros v. induction v as [i| | |m1 IHm1 m2 IHm2|ea ta|nr wr IHwr|ep npr|fm eb IHfb|q1 IHq1 q2 IHq2|bv IHvb be2 IHbe2];
      intros Hva G A Hta v1 v2 C1 C2.
    + inversion C1.
    + inversion C1.
    + inversion C1.
    + (* merge *)
      destruct (value_merge_inv m1 m2 Hva) as (Hv1 & Hv2).
      destruct (merge_inf_cases G m1 m2 A Hta) as
        [(A1 & A2 & Heq & Ht1 & Ht2 & Hcons) | (A1 & A2 & G' & Heq & Ht1 & Ht2 & Hdisj)].
      * assert (E12 : forall x y, casting m1 (arr X1 X2) x -> casting m2 (arr X1 X2) y -> x = y)
          by (intros x y Cx Cy; exact (Hcons _ x y Cx Cy)).
        assert (E21 : forall x y, casting m2 (arr X1 X2) x -> casting m1 (arr X1 X2) y -> x = y)
          by (intros x y Cx Cy; symmetry; exact (Hcons _ y x Cy Cx)).
        inversion C1; subst; inversion C2; subst.
        all: try solve [eapply IHm1; eauto].
        all: try solve [eapply IHm2; eauto].
        all: try solve [eapply E12; eauto].
        all: try solve [eapply E21; eauto].
      * inversion C1; subst; inversion C2; subst.
        all: try solve [eapply IHm1; eauto].
        all: try solve [eapply IHm2; eauto].
        all: try solve [eauto 15 using IHm1, IHm2, cast_det_disj, disjoint_sym].
    + inversion C1.
    + inversion C1.
    + inversion C1.
    + inversion C1.
    + inversion C1.
    + (* box bv be2 *)
      destruct (value_box_inv bv be2 Hva) as (Hbv & fm & eb0 & Aa & Ba & Heq2). subst be2.
      inversion C1; subst; inversion C2; subst.
      * reflexivity.
      * exfalso; auto.
      * exfalso; auto.
      * eapply genv_functional; eassumption.
Qed.

(* ============ typing inversion helpers for subterms ============ *)
Lemma chk_inf: forall G e T, has_type G e chk T -> exists A, has_type G e inf A.
Proof. intros G e T H. inversion H; subst; eauto. Qed.

Lemma proj_inf_ty: forall G e n T, has_type G (proj e n) inf T ->
  exists A0, T = A0 /\ has_type G e inf (rcd n A0).
Proof. intros G e n T H. inversion H; subst; eauto. Qed.

Lemma app_inf_ty: forall G f a T, has_type G (app f a) inf T ->
  exists A B, T = B /\ has_type G f inf (arr A B) /\ has_type G a chk A.
Proof. intros G f a T H. inversion H; subst; eauto. Qed.

Lemma box_inf_ty: forall G e1 e2 T, has_type G (box e1 e2) inf T ->
  exists B A', has_type G e1 inf B /\ has_type B e2 inf A'.
Proof. intros G e1 e2 T H. inversion H; subst; eauto. Qed.

Lemma merge_typing_sub: forall G a b m T, has_type G (merge a b) m T ->
  exists A1 A2 Ge, has_type G a inf A1 /\ has_type Ge b inf A2.
Proof.
  intros G a b m T H. destruct m.
  - destruct (merge_inf_comp G a b T H) as (A1 & A2 & Ge & _ & H1 & H2). eauto.
  - destruct (chk_inf _ _ _ H) as (X & Hi).
    destruct (merge_inf_comp G a b X Hi) as (A1 & A2 & Ge & _ & H1 & H2). eauto.
Qed.

Lemma rec_typing_sub: forall G n e m T, has_type G (rec n e) m T ->
  exists A0, has_type G e inf A0.
Proof.
  intros G n e m T H. destruct m.
  - destruct (rec_inf_ty G n e T H) as (A0 & _ & Ht). eauto.
  - destruct (chk_inf _ _ _ H) as (X & Hi).
    destruct (rec_inf_ty G n e X Hi) as (A0 & _ & Ht). eauto.
Qed.

Lemma proj_typing_sub: forall G e n m T, has_type G (proj e n) m T ->
  exists A0, has_type G e inf (rcd n A0).
Proof.
  intros G e n m T H. destruct m.
  - destruct (proj_inf_ty G e n T H) as (A0 & _ & Ht). eauto.
  - destruct (chk_inf _ _ _ H) as (X & Hi).
    destruct (proj_inf_ty G e n X Hi) as (A0 & _ & Ht). eauto.
Qed.

Lemma app_typing_sub: forall G f a m T, has_type G (app f a) m T ->
  exists A B, has_type G f inf (arr A B) /\ has_type G a chk A.
Proof.
  intros G f a m T H. destruct m.
  - destruct (app_inf_ty G f a T H) as (A & B & _ & H1 & H2). eauto.
  - destruct (chk_inf _ _ _ H) as (X & Hi).
    destruct (app_inf_ty G f a X Hi) as (A & B & _ & H1 & H2). eauto.
Qed.

Lemma box_typing_sub: forall G e1 e2 m T, has_type G (box e1 e2) m T ->
  exists B A', has_type G e1 inf B /\ has_type B e2 inf A'.
Proof.
  intros G e1 e2 m T H. destruct m.
  - destruct (box_inf_ty G e1 e2 T H) as (B & A' & H1 & H2). eauto.
  - destruct (chk_inf _ _ _ H) as (X & Hi).
    destruct (box_inf_ty G e1 e2 X Hi) as (B & A' & H1 & H2). eauto.
Qed.

Lemma ann_inf_chk_or_lam: forall G e t T, has_type G (ann e t) inf T ->
  has_type G e chk t \/ (exists fm eb Aa Ba, e = lam fm eb /\ t = arr Aa Ba).
Proof.
  intros G e t T H. inversion H; subst.
  all: try solve [left; assumption].
  all: right; eexists; eexists; eexists; eexists; split; reflexivity.
Qed.

Lemma ann_chk_or_lam: forall G e t m T, has_type G (ann e t) m T ->
  has_type G e chk t \/ (exists fm eb Aa Ba, e = lam fm eb /\ t = arr Aa Ba).
Proof.
  intros G e t m T H. destruct m.
  - eapply ann_inf_chk_or_lam. exact H.
  - destruct (chk_inf _ _ _ H) as (X & Hi).
    eapply ann_inf_chk_or_lam. exact Hi.
Qed.

Lemma step_lam_false: forall w fm e e', step w (lam fm e) e' -> False.
Proof. intros w fm e e' H. inversion H. Qed.

Lemma box_value_closure: forall v2 fm e A B A', value v2 -> ext A fm A' ->
  value (box v2 (ann (lam fm e) (arr A B))).
Proof.
  intros v2 fm e A B A' Hv Hext. destruct fm.
  - apply vclos; assumption.
  - inversion Hext; subst. apply vsclos; assumption.
Qed.

Lemma step_box_e_false: forall (w vv : exp) (fm : fmode) (eb : exp) (A B A' : typ) (res : exp),
  value vv -> ext A fm A' -> step w (box vv (ann (lam fm eb) (arr A B))) res -> False.
Proof.
  intros w vv fm eb A B A' res Hv Hext Hs.
  eapply value_irred.
  - eapply box_value_closure; eassumption.
  - eassumption.
Qed.

Lemma step_rec_irred: forall w n v1 e', value v1 -> step w (rec n v1) e' -> False.
Proof. intros w n v1 e' Hv H. inversion H; subst. eapply value_irred; eassumption. Qed.

Lemma ann_value_chk: forall G e t m T, value e -> has_type G (ann e t) m T ->
  exists A0, has_type G e inf A0.
Proof.
  intros G e t m T Hv Ht.
  destruct (ann_chk_or_lam G e t m T Ht) as [Hchk | (fm & eb & Aa & Ba & Heq & _)].
  - exact (chk_inf G e t Hchk).
  - subst e. inversion Hv.
Qed.

Lemma ann_substep_typing: forall G e t m T, has_type G (ann e t) m T ->
  forall w x, step w e x -> has_type G e chk t.
Proof.
  intros G e t m T Ht w x Hstep.
  destruct (ann_chk_or_lam G e t m T Ht) as [Hchk | (fm & eb & Aa & Ba & Heq & _)].
  - exact Hchk.
  - subst e. exfalso. eapply step_lam_false; eassumption.
Qed.

Lemma step_det_typed : forall e, forall m A G, has_type G e m A ->
  forall v u1 u2, value v -> step v e u1 -> step v e u2 -> u1 = u2.
Proof.
  induction e as [i| | |e1 IHe1 e2 IHe2|e0 IHe0 t|n e0 IHe0|e0 IHe0 n|fm e0 IHe0|e1 IHe1 e2 IHe2|e1 IHe1 e2 IHe2];
    intros m A G Hty v u1 u2 Hv S1 S2.
  - inversion S1.
  - inversion S1.
  - inversion S1; subst; inversion S2; subst; reflexivity.
  - (* merge *)
    destruct (merge_typing_sub G e1 e2 m A Hty) as (A1 & A2 & Ge & Ht1 & Ht2).
    inversion S1; subst; inversion S2; subst.
    + f_equal.
      match goal with
      | Hp1 : step ?w ?tm ?a, Hp2 : step ?w ?tm ?b |- ?a = ?b =>
          let Hm := constr:(step_value_env w tm a Hp1) in
          exact (IHe2 inf A2 Ge Ht2 w a b Hm Hp1 Hp2)
      end.
    + exfalso. eapply value_irred; eauto.
    + exfalso. eapply value_irred; eauto.
    + f_equal. eapply IHe1; eauto.
  - (* ann *)
    inversion S1; subst.
    + (* annv *) inversion S2; subst.
      * match goal with Hval0 : value e0 |- _ =>
          destruct (ann_value_chk G e0 t m A Hval0 Hty) as (A0 & Ht0);
          eapply cast_det_typed; eauto end.
      * exfalso; eapply value_irred; eauto.
      * exfalso; match goal with Hvl : value (lam _ _) |- _ => inversion Hvl end.
    + (* anne *) inversion S2; subst.
      * exfalso; eapply value_irred; eauto.
      * destruct (ann_chk_or_lam G e0 t m A Hty) as [Hchk | (fmb & ebb & Aab & Bab & Heq & _)].
        -- f_equal. eapply IHe0; eauto.
        -- subst e0. exfalso.
           match goal with Hp : step _ (lam _ _) _ |- _ => eapply step_lam_false; exact Hp end.
      * exfalso.
        match goal with Hp : step _ (lam _ _) _ |- _ => eapply step_lam_false; exact Hp end.
    + (* switch *) inversion S2; subst.
      * exfalso; match goal with Hvl : value (lam _ _) |- _ => inversion Hvl end.
      * exfalso; eapply step_lam_false; eauto.
      * reflexivity.
  - (* rec *)
    destruct (rec_typing_sub G n e0 m A Hty) as (A0 & Ht0).
    inversion S1; subst; inversion S2; subst. f_equal.
    match goal with Hp1 : step ?w e0 ?a, Hp2 : step ?w e0 ?b |- ?a = ?b =>
      exact (IHe0 inf A0 G Ht0 w a b Hv Hp1 Hp2) end.
  - (* proj *)
    destruct (proj_typing_sub G e0 n m A Hty) as (A0 & Ht0).
    inversion S1; subst; inversion S2; subst.
    all: try reflexivity.
    all: try solve [exfalso; eapply value_irred; eauto].
    all: try solve [f_equal; eapply IHe0; eauto].
    all: try solve [exfalso; eapply step_rec_irred; eauto].
  - (* lam *) inversion S1.
  - (* app *)
    destruct (app_typing_sub G e1 e2 m A Hty) as (Aa & Bb & Htf & Hta).
    inversion S1; subst; inversion S2; subst.
    + (* beta/beta *)
      match goal with
      | E1 : ext ?Ax ?fx ?T1, E2 : ext ?Ax ?fx ?T2,
        C1 : casting ?ar ?T1 ?r1, C2 : casting ?ar ?T2 ?r2,
        K1 : constr ?Ax ?r1 ?fx ?w1, K2 : constr ?Ax ?r2 ?fx ?w2 |- _ =>
          assert (He : T2 = T1) by (symmetry; eapply ext_functional; [exact E1|exact E2]);
          subst T2;
          destruct (chk_inf G e2 Aa Hta) as (Aarg & Htarg);
          assert (Hr : r2 = r1) by
            (symmetry;
             match goal with Hval : value ar |- _ =>
               exact (cast_det_typed T1 ar Hval G Aarg Htarg r1 r2 C1 C2) end);
          subst r2;
          assert (Hw : w2 = w1) by (symmetry; eapply constr_functional; [exact K1|exact K2]);
          subst w2;
          reflexivity
      end.
    + exfalso. refine (step_box_e_false v v2 fm e A0 B A' e1' _ _ _). all: assumption.
    + exfalso. refine (value_irred e2 _ v e2' _). all: assumption.
    + exfalso. refine (step_box_e_false v v2 fm e A0 B A' e1' _ _ _). all: assumption.
    + f_equal. eapply IHe1; eauto.
    + exfalso. refine (value_irred e1 _ v e1' _). all: assumption.
    + exfalso. refine (value_irred e2 _ v e2' _). all: assumption.
    + exfalso. refine (value_irred e1 _ v e1' _). all: assumption.
    + f_equal.
      match goal with Hp1 : step ?w ?tm ?a, Hp2 : step ?w ?tm ?b |- ?a = ?b =>
        exact (IHe2 chk Aa G Hta w a b Hv Hp1 Hp2) end.
  - (* box *)
    destruct (box_typing_sub G e1 e2 m A Hty) as (B & A' & Ht1 & Ht2).
    inversion S1; subst; inversion S2; subst.
    + reflexivity.
    + exfalso. exact (value_irred u1 H5 e1 e' H2).
    + exfalso. exact (value_irred e1 H3 v e2 H4).
    + exfalso. exact (value_irred u2 H8 e1 e' H1).
    + f_equal. exact (IHe2 inf A' B Ht2 e1 e' e'0 (step_value_env e1 e2 e' H1) H1 H2).
    + exfalso. exact (value_irred e1 (step_value_env e1 e2 e' H1) v e3 H4).
    + exfalso. exact (value_irred e1 H5 v e3 H2).
    + exfalso. exact (value_irred e1 (step_value_env e1 e2 e' H1) v e3 H2).
    + f_equal. exact (IHe1 inf B G Ht1 v e3 e4 Hv H2 H3).
Qed.

Theorem gen_step_unique: forall e m A G,
  has_type G e m A -> forall v e1 e2,
  has_type top v inf G ->
  step v e e1 ->
  step v e e2 ->
  e1 = e2.
Proof.
  intros e m A G Hty v u1 u2 Htv S1 S2.
  exact (step_det_typed e m A G Hty v u1 u2 (step_value_env v e u1 S1) S1 S2).
Qed.
