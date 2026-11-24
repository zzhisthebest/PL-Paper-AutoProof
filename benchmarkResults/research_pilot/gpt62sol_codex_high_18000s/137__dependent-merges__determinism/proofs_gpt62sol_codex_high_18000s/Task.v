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

(* A path follows function codomains and record fields to an integer,
   choosing one branch at each intersection. *)
Inductive cast_path : Type :=
  | path_int
  | path_arr (p : cast_path)
  | path_rcd (l : nat) (p : cast_path).

Fixpoint has_cast_path (A : typ) (p : cast_path) : Prop :=
  match A with
  | int => p = path_int
  | top => False
  | and A B => has_cast_path A p \/ has_cast_path B p
  | arr _ B =>
      match p with
      | path_arr q => has_cast_path B q
      | _ => False
      end
  | rcd l A =>
      match p with
      | path_rcd k q => l = k /\ has_cast_path A q
      | _ => False
      end
  end.

Lemma sub_preserves_cast_path : forall A B,
  sub A B -> forall p, has_cast_path B p -> has_cast_path A p.
Proof.
  intros A B Hsub.
  induction Hsub; intros p Hp; destruct p; simpl in *; intuition eauto.
Qed.

Lemma toplike_or_cast_path : forall A,
  toplike A \/ exists p, has_cast_path A p.
Proof.
  induction A as [| | A IHA B IHB | l A IHA | A IHA B IHB].
  - right. exists path_int. reflexivity.
  - left. constructor.
  - destruct IHA as [HA | [p Hp]], IHB as [HB | [q Hq]].
    + left. constructor; assumption.
    + right. exists q. right. exact Hq.
    + right. exists p. left. exact Hp.
    + right. exists p. left. exact Hp.
  - destruct IHA as [HA | [p Hp]].
    + left. constructor. exact HA.
    + right. exists (path_rcd l p). split; auto.
  - destruct IHB as [HB | [p Hp]].
    + left. constructor. exact HB.
    + right. exists (path_arr p). exact Hp.
Qed.

Lemma sub_reflexive : forall A, sub A A.
Proof.
  induction A; auto using sint, stop, sand, sandl, sandr, srcd, sarr.
Qed.

Lemma shared_cast_path_cost : forall A B p,
  has_cast_path A p -> has_cast_path B p -> cost_spec A B.
Proof.
  induction A as [| | A IHA A' IHA' | l A IHA | A IHA A' IHA'];
    intros B p HA HB; simpl in HA; try contradiction.
  - subst p. induction B; simpl in HB; try contradiction.
    + exists int. repeat split; constructor.
    + destruct HB as [HB | HB].
      * destruct (IHB1 HB) as [C [HC [HAC HBC]]].
        exists C. repeat split; auto using sandl.
      * destruct (IHB2 HB) as [C [HC [HAC HBC]]].
        exists C. repeat split; auto using sandr.
  - destruct HA as [HA | HA].
    + destruct (IHA B p HA HB) as [C [HC [HAC HBC]]].
      exists C. repeat split; auto using sandl.
    + destruct (IHA' B p HA HB) as [C [HC [HAC HBC]]].
      exists C. repeat split; auto using sandr.
  - destruct p as [| p | k p]; try contradiction.
    destruct HA as [<- HA].
    induction B as [| | B IHB B' IHB' | k B IHB | B IHB B' IHB'];
      simpl in HB; try discriminate; try contradiction.
    + destruct HB as [HB | HB].
      * destruct (IHB HB) as [C [HC [HAC HBC]]].
        exists C. repeat split; auto using sandl.
      * destruct (IHB' HB) as [C [HC [HAC HBC]]].
        exists C. repeat split; auto using sandr.
    + destruct HB as [-> HB].
      destruct (IHA B p HA HB) as [C [HC [HAC HBC]]].
      exists (rcd l C). repeat split; auto using GO_rcd, srcd.
  - destruct p as [| p | k p]; try contradiction.
    induction B as [| | B IHB B' IHB' | k B IHB | B IHB B' IHB'];
      simpl in HB; try discriminate; try contradiction.
    + destruct HB as [HB | HB].
      * destruct (IHB HB) as [C [HC [HAC HBC]]].
        exists C. repeat split; auto using sandl.
      * destruct (IHB' HB) as [C [HC [HAC HBC]]].
        exists C. repeat split; auto using sandr.
    + destruct (IHA' B' p HA HB) as [C [HC [HAC HBC]]].
      exists (arr (and A B) C).
      repeat split; auto using GO_arrow, sarr, sandl, sandr, sub_reflexive.
Qed.

Lemma lam_has_no_type : forall G fm e m A,
  ~ has_type G (lam fm e) m A.
Proof.
  intros G fm e m A Htype.
  inversion Htype; subst.
  match goal with
  | H : has_type _ (lam _ _) inf _ |- _ => inversion H
  end.
Qed.

Lemma lambda_annotation_type : forall G fm e A B T,
  has_type G (ann (lam fm e) (arr A B)) inf T ->
  exists C, T = arr C B.
Proof.
  intros G fm e A B T Htype.
  inversion Htype; subst; eauto.
Qed.

Lemma casting_preserves_cast_path : forall v B w,
  casting v B w -> forall G A p,
  has_type G v inf A -> has_cast_path B p -> has_cast_path A p.
Proof.
  intros v B w Hcast.
  induction Hcast; intros G T p Htype Hp.
  - contradiction.
  - inversion Htype; subst. exact Hp.
  - inversion Htype; subst; simpl; left; eauto.
  - inversion Htype; subst; simpl; right; eauto.
  - destruct Hp; eauto.
  - inversion Htype; subst. destruct p; try contradiction.
    destruct Hp as [Hlabel Hp]. split; eauto.
  - inversion Htype; subst.
    match goal with
    | H : has_type _ (ann (lam _ _) _) inf _ |- _ =>
        destruct (lambda_annotation_type _ _ _ _ _ _ H) as [E ->]
    end.
    destruct p; try contradiction. simpl in *.
    eapply sub_preserves_cast_path; eauto.
  - inversion Htype; subst.
    match goal with
    | H : has_type _ (ann (lam _ _) _) inf _ |- _ =>
        destruct (lambda_annotation_type _ _ _ _ _ _ H) as [E ->]
    end.
    destruct p; try contradiction. simpl in *.
    eapply sub_preserves_cast_path; eauto.
Qed.

Lemma genv_unique : forall A v,
  genv A v -> forall w, genv A w -> v = w.
Proof.
  intros A v Hgen.
  induction Hgen; intros w Hw; inversion Hw; subst;
    repeat f_equal; eauto.
Qed.

Lemma toplike_cast_genv : forall v A w,
  casting v A w -> toplike A -> genv A w.
Proof.
  intros v A w Hcast.
  induction Hcast; intros Htop; inversion Htop; subst;
    eauto using genv; contradiction.
Qed.

Lemma merge_cast_agree : forall G v1 v2 T,
  has_type G (merge v1 v2) inf T ->
  forall A w1 w2, casting v1 A w1 -> casting v2 A w2 -> w1 = w2.
Proof.
  intros G v1 v2 T Htype A w1 w2 Hleft Hright.
  inversion Htype; subst.
  (* A disjoint merge can cast both branches only at a toplike type. *)
  - destruct (toplike_or_cast_path A) as [Htop | [p Hp]].
    + eapply genv_unique; eauto using toplike_cast_genv.
    + exfalso.
      match goal with
      | HL : has_type _ v1 inf ?B, HR : has_type _ v2 inf ?C,
        Hdis : disjoint ?B ?C |- _ =>
          apply Hdis; eapply shared_cast_path_cost with (p := p);
            [eapply casting_preserves_cast_path; [exact Hleft | exact HL | exact Hp]
            |eapply casting_preserves_cast_path; [exact Hright | exact HR | exact Hp]]
      end.
  - eauto.
Qed.

Lemma typed_casting_unique : forall G v T A w1 w2,
  has_type G v inf T -> casting v A w1 -> casting v A w2 -> w1 = w2.
Proof.
  intros G v T A w1 w2 Htype Hcast.
  revert G T Htype w2.
  induction Hcast; intros G T Htype w2 Hother;
    inversion Hother; subst; try reflexivity; try contradiction.
  all: try solve [
    match goal with
    | H : ord top |- _ => inversion H
    | H : ord (and _ _) |- _ => inversion H
    end ].
  all: try solve [eapply merge_cast_agree; [exact Htype | eassumption | eassumption]
                 | symmetry; eapply merge_cast_agree; [exact Htype | eassumption | eassumption]].
  all: try solve [f_equal; eauto].
  all: try solve [inversion Htype; subst; f_equal; eauto].
  all: eauto using genv_unique.
Qed.

Lemma checked_casting_unique : forall G v T A w1 w2,
  has_type G v chk T -> casting v A w1 -> casting v A w2 -> w1 = w2.
Proof.
  intros G v T A w1 w2 Htype Hcast Hother.
  inversion Htype; subst. eauto using typed_casting_unique.
Qed.

Lemma step_environment_value : forall v e e',
  step v e e' -> value v.
Proof.
  intros v e e' Hstep.
  induction Hstep; try assumption.
  match goal with
  | H : value (merge _ _) |- _ => inversion H; assumption
  end.
Qed.

Lemma value_cannot_step : forall e,
  value e -> forall v e', ~ step v e e'.
Proof.
  intros e Hvalue.
  induction Hvalue; intros v e' Hstep; inversion Hstep; subst;
    try solve [eauto using value].
  all: match goal with
       | H : value (ann _ _) |- _ => inversion H
       | H : ~ value (box _ _) |- _ => apply H; constructor; assumption
       | IH : forall v r, ~ step v ?e r, H : step ?v ?e ?r |- _ =>
           exact (IH v r H)
       end.
Qed.

Lemma ext_unique : forall A fm A1 A2,
  ext A fm A1 -> ext A fm A2 -> A1 = A2.
Proof.
  intros A fm A1 A2 H1 H2.
  inversion H1; subst; inversion H2; reflexivity.
Qed.

Lemma constr_unique : forall A v fm v1 v2,
  constr A v fm v1 -> constr A v fm v2 -> v1 = v2.
Proof.
  intros A v fm v1 v2 H1 H2.
  inversion H1; subst; inversion H2; reflexivity.
Qed.

Lemma extended_closure_is_value : forall A fm A' B e v,
  ext A fm A' -> value v -> value (box v (ann (lam fm e) (arr A B))).
Proof.
  intros A fm A' B e v Hext Hv.
  inversion Hext; subst; constructor; assumption.
Qed.

Lemma typed_step_unique : forall G e m A,
  has_type G e m A -> forall v e1 e2,
  step v e e1 -> step v e e2 -> e1 = e2.
Proof.
  intros G e m A Htype.
  induction Htype; intros v r1 r2 Hstep1 Hstep2.
  all: try solve [eauto
                 | exfalso; eapply value_cannot_step;
                     [apply vmrg; eassumption | exact Hstep1]].
  all: inversion Hstep1; subst; inversion Hstep2; subst; try reflexivity.
  all: try solve [
    match goal with
    | Hv : value ?e, Hs : step _ ?e _ |- _ =>
        exfalso; exact (value_cannot_step _ Hv _ _ Hs)
    (* A box can step its body only when its captured environment is a value. *)
    | Hinner : step ?e _ _, Houter : step _ ?e _ |- _ =>
        exfalso; exact (value_cannot_step _ (step_environment_value _ _ _ Hinner) _ _ Houter)
    | Hv : value ?e, Hs : step _ (rec ?l ?e) _ |- _ =>
        exfalso; exact (value_cannot_step _ (vrec l e Hv) _ _ Hs)
    | Hext : ext ?A ?fm _, Hv : value ?v,
      Hs : step _ (box ?v (ann (lam ?fm _) (arr ?A _))) _ |- _ =>
        exfalso;
        exact (value_cannot_step _ (extended_closure_is_value _ _ _ _ _ _ Hext Hv) _ _ Hs)
    | H : has_type _ (lam _ _) _ _ |- _ =>
        exfalso; eapply lam_has_no_type; exact H
    | H : value (lam _ _) |- _ => inversion H
    | H : step _ (lam _ _) _ |- _ => inversion H
    end ].
  all: try solve [f_equal; eauto using value, value_cannot_step
                 | eauto using checked_casting_unique].
  all: match goal with
  | Hext1 : ext ?A ?fm ?A1, Hext2 : ext ?A ?fm ?A2 |- _ =>
      assert (A1 = A2) by (eapply ext_unique; [exact Hext1 | exact Hext2]); subst
  end.
  all: match goal with
  | Hcast1 : casting ?e ?A ?w1, Hcast2 : casting ?e ?A ?w2 |- _ =>
      assert (w1 = w2) by (eapply checked_casting_unique;
                           [eassumption | exact Hcast1 | exact Hcast2]); subst
  end.
  all: f_equal; f_equal; eauto using constr_unique.
Qed.

Theorem gen_step_unique: forall e m A G,
  has_type G e m A -> forall v e1 e2,
  has_type top v inf G ->
  step v e e1 ->
  step v e e2 ->
  e1 = e2.
Proof.
  intros e m A G Htype v e1 e2 Henv Hstep1 Hstep2.
  eauto using typed_step_unique.
Qed.
