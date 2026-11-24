Set Implicit Arguments.

Require Import Definitions.

Require Import Step.

Require Import Misc.

From Stdlib Require Import Lia.

Reserved Notation "[ L ] G ⊢k S <⦂ U" (at level 70).

Inductive subtykn : vars -> env -> typ -> typ -> Prop :=

| snf_vrefl : forall L G x,
    [ L ] G ⊢k typ_sel x <⦂ typ_sel x

| snf_top : forall L G T,
    [ L ] G ⊢k T <⦂ typ_top

| snf_bot : forall L G T,
    [ L ] G ⊢k typ_bot <⦂ T

| snf_bnd : forall L G S T1 T2 U,
    [ L ] G ⊢k S <⦂ T1 ->
    [ L ] G ⊢k T2 <⦂ U ->
    [ L ] G ⊢k typ_bnd T1 T2 <⦂ typ_bnd S U

| snf_all : forall L G T U1 U2 x,
    x `notin` union (fv G)
      (union (fv T) (union (fv U1) (union (fv U2) L))) ->
    [ union L (union (singleton x) (fv T)) ]
      x ~ T ++ G ⊢k open x U1 <⦂ open x U2 ->
    [ L ] G ⊢k typ_all T U1 <⦂ typ_all T U2

| snf_sel1 : forall L G x T S,
    binds x T G ->
    [ L ] G ⊢k T <⦂ typ_bnd S typ_top ->
    [ L ] G ⊢k S <⦂ (typ_sel $ avar_f x)

| snf_sel2 : forall L G x T U,
    binds x T G ->
    [ L ] G ⊢k T <⦂ typ_bnd typ_bot U ->
    [ L ] G ⊢k typ_sel $ avar_f x <⦂ U
where "[ L ] G ⊢k S <⦂ U" := (subtykn L G S U).

(* These structural changes can be composed on either side of a kernel
   judgment. The lower bound reverses the direction of the change. *)
Inductive structural_subty : typ -> typ -> Prop :=
| structural_refl : forall T, structural_subty T T
| structural_top : forall T, structural_subty T typ_top
| structural_bot : forall T, structural_subty typ_bot T
| structural_bnd : forall A B C D,
    structural_subty C A -> structural_subty B D ->
    structural_subty (typ_bnd A B) (typ_bnd C D).

Local Lemma subtykn_structural : forall L G S U,
    subtykn L G S U -> forall S' U',
    structural_subty S' S -> structural_subty U U' -> subtykn L G S' U'.
Proof.
  intros L G S U H. induction H; intros S' U' HL HR.
  - inversion HL; subst; try solve [apply snf_bot].
    inversion HR; subst; auto using snf_vrefl, snf_top.
  - inversion HR; subst; apply snf_top.
  - inversion HL; subst; apply snf_bot.
  - inversion HL; subst; try solve [apply snf_bot];
      inversion HR; subst; eauto using snf_top, snf_bnd, structural_refl.
  - inversion HL; subst; try solve [apply snf_bot].
    inversion HR; subst; eauto using snf_top, snf_all.
  - inversion HR; subst; try solve [apply snf_top].
    eapply snf_sel1; [eassumption |].
    eapply IHsubtykn; [apply structural_refl |].
    apply structural_bnd; auto using structural_refl.
  - inversion HL; subst; try solve [apply snf_bot].
    eapply snf_sel2; [eassumption |].
    eapply IHsubtykn; [apply structural_refl |].
    apply structural_bnd; auto using structural_refl.
Qed.

Local Lemma binds_at_split : forall (P G : env) x T,
    binds x T (P ++ x ~ T ++ G).
Proof.
  intros. apply binds_app_3, binds_cons_2; reflexivity.
Qed.

(* Exposure uses suffixes for lookups, while the kernel comparisons stay
   in the surrounding context. *)
Local Lemma exposure_subtykn_bound : forall E T V,
    exposure E T V -> forall L G A B,
    (forall x W, binds x W E -> binds x W G) ->
    subtykn L G V (typ_bnd A B) -> subtykn L G T (typ_bnd A B).
Proof.
  intros E T V H. induction H; intros M G' A B Hbind Hsub.
  - exact Hsub.
  - inversion Hsub.
  - eapply snf_sel2.
    + apply Hbind, binds_at_split.
    + eapply IHexposure.
      * intros y W Hy. apply Hbind, binds_app_3, binds_app_3, Hy.
      * apply snf_bot.
  - eapply snf_sel2.
    + apply Hbind, binds_at_split.
    + assert (Htail : forall y W, binds y W G1 -> binds y W G').
      { intros y W Hy. apply Hbind, binds_app_3, binds_app_3, Hy. }
      eapply IHexposure1; [exact Htail |].
      apply snf_bnd; [apply snf_bot |].
      eapply IHexposure2; eassumption.
Qed.

Local Lemma stp_subty_to_subtykn : forall L G S U,
    stp_subty L G S U -> subtykn L G S U.
Proof.
  intros L G S U H. induction H.
  - apply snf_top.
  - apply snf_bot.
  - apply snf_vrefl.
  - destruct H.
    + eapply subtykn_structural; eauto using structural_top, structural_refl.
    + eapply snf_sel2; [apply binds_at_split |].
      eapply exposure_subtykn_bound; [eassumption | | apply snf_bot].
      intros y W Hy. apply binds_app_3, binds_app_3, Hy.
    + eapply snf_sel2; [apply binds_at_split |].
      eapply exposure_subtykn_bound; [eassumption | |].
      * intros y W Hy. apply binds_app_3, binds_app_3, Hy.
      * apply snf_bnd; [apply snf_bot | exact IHstp_subty].
  - destruct H.
    + eapply subtykn_structural; eauto using structural_bot, structural_refl.
    + eapply snf_sel1; [apply binds_at_split |].
      eapply exposure_subtykn_bound; [eassumption | | apply snf_bot].
      intros y W Hy. apply binds_app_3, binds_app_3, Hy.
    + eapply snf_sel1; [apply binds_at_split |].
      eapply exposure_subtykn_bound; [eassumption | |].
      * intros y W Hy. apply binds_app_3, binds_app_3, Hy.
      * apply snf_bnd; [exact IHstp_subty | apply snf_top].
  - auto using snf_bnd.
  - eapply snf_all; eassumption.
Qed.

Local Lemma wf_env_uniq : forall G, wf_env G -> uniq G.
Proof.
  intros G H. induction H.
  - constructor.
  - apply uniq_push; [assumption |].
    cbn [fv FvEnv] in H. fsetdec.
Qed.

Local Lemma wf_env_split : forall (P G : env) x T,
    wf_env (P ++ x ~ T ++ G) -> wf_env G /\ fv T [<=] dom G /\ lc T.
Proof.
  induction P as [|[y V] P IH]; intros G x T H; simpl in H;
    inversion H; subst.
  - repeat split; assumption.
  - apply IH with (x := x). assumption.
Qed.

Local Lemma binding_in_suffix : forall (P G Q E : env) x T,
    wf_env (Q ++ x ~ T ++ E) -> Q ++ x ~ T ++ E = P ++ G -> x `in` dom G ->
    exists R, G = R ++ x ~ T ++ E.
Proof.
  intros P G Q E x T Hwf Heq Hin.
  apply wf_env_uniq in Hwf.
  destruct (binds_In_inv typ x G Hin) as [V Hbind].
  destruct (binds_split typ x V G Hbind) as [F [R ->]].
  rewrite <- (app_assoc _ P R (x ~ V ++ F)) in Heq.
  destruct (uniq_mid typ x T Q E V (P ++ R) F Hwf Heq) as [_ [<- <-]].
  eauto.
Qed.

Local Lemma exposure_scope : forall G T V,
    exposure G T V -> wf_env G -> fv T [<=] dom G -> fv V [<=] dom G.
Proof.
  intros G T V H. induction H; intros Hwf HT.
  - exact HT.
  - cbn [fv FvTyp fv_typ]. fsetdec.
  - cbn [fv FvTyp fv_typ]. fsetdec.
  - destruct (@wf_env_split G2 G1 x T Hwf) as [Htail [Hbinding _]].
    specialize (IHexposure1 Htail Hbinding).
    cbn [fv FvTyp fv_typ] in IHexposure1.
    assert (HU : fv U [<=] dom G1) by (cbn [fv FvTyp] in *; fsetdec).
    specialize (IHexposure2 Htail HU).
    rewrite !dom_app. fsetdec.
Qed.

(* Follow the left selection steps in a comparison with a member type.
   Each lookup is restricted to the suffix that scopes its input. *)
Local Lemma stp_subty_exposes_bound : forall L G T V,
    stp_subty L G T V -> forall P E A B,
    G = P ++ E -> wf_env G -> fv T [<=] dom E -> V = typ_bnd A B ->
    exposure E T typ_bot \/
    exists C D, exposure E T (typ_bnd C D) /\
                stp_subty L G A C /\ stp_subty L G D B.
Proof.
  intros L G T V H. induction H; intros P E A B HG Hwf HT HV;
    try discriminate HV.
  - left. apply exp_stop. simpl. tauto.
  - destruct H as [G' x' | G1 G2 x' T' Hexp | G1 G2 x' T' Lo Hi Hexp].
    + subst U. inversion H0.
    + assert (Hx : x' `in` dom E).
      { apply HT. cbn [fv FvTyp fv_typ fv_avar]. fsetdec. }
      destruct (@binding_in_suffix P E G2 G1 x' T' Hwf HG Hx) as [R ->].
      left. eauto using exp_bot.
    + assert (Hx : x' `in` dom E).
      { apply HT. cbn [fv FvTyp fv_typ fv_avar]. fsetdec. }
      destruct (@binding_in_suffix P E G2 G1 x' T' Hwf HG Hx) as [R ->].
      destruct (@wf_env_split G2 G1 x' T' Hwf) as [Htail [Hbinding _]].
      pose proof (exposure_scope Hexp Htail Hbinding) as Hbounds.
      assert (HU : fv Hi [<=] dom G1).
      { cbn [fv FvTyp fv_typ] in *. fsetdec. }
      destruct (IHstp_subty (G2 ++ x' ~ T') G1 A B
        (eq_sym (app_assoc _ G2 (x' ~ T') G1)) Hwf HU HV)
        as [Hbot | [C [D [Hupper [Hlo Hhi]]]]].
      * left. eauto using exp_bnd.
      * right. exists C, D. eauto using exp_bnd.
  - inversion HV; subst. right. exists S1, U1.
    repeat split; auto. apply exp_stop. simpl. tauto.
Qed.

Local Lemma lc_open_rec : forall U k x,
    lc_at (S k) U -> lc_at k (open_rec k x U).
Proof.
  induction U; intros k x H; inversion H as [| |n v Hv| |]; subst;
    cbn [open_rec OpenTyp open_rec_typ]; constructor.
  - destruct a as [i|y]; cbn [open_rec_avar].
    + destruct (k == i); constructor. inversion Hv. lia.
    + constructor.
  - apply (IHU1 k x). assumption.
  - apply (IHU2 (S k) x). assumption.
  - apply (IHU1 k x). assumption.
  - apply (IHU2 k x). assumption.
Qed.

Local Lemma fv_open_rec : forall U k x,
    fv (open_rec k x U) [<=] singleton x `union` fv U.
Proof.
  induction U; intros k x;
    cbn [open_rec OpenTyp open_rec_typ fv FvTyp fv_typ].
  - fsetdec.
  - fsetdec.
  - destruct a as [i|y]; cbn [open_rec_avar fv_avar].
    + destruct (k == i); simpl; fsetdec.
    + fsetdec.
  - specialize (IHU1 k x). specialize (IHU2 (S k) x).
    cbn [fv FvTyp] in *. fsetdec.
  - specialize (IHU1 k x). specialize (IHU2 k x).
    cbn [fv FvTyp] in *. fsetdec.
Qed.

Local Definition scoped_typ (G : env) (T : typ) := fv T [<=] dom G /\ lc T.

Local Lemma scoped_bnd : forall G S U,
    scoped_typ G (typ_bnd S U) -> scoped_typ G S /\ scoped_typ G U.
Proof.
  intros G S U [Hfv Hlc]. inversion Hlc; subst.
  cbn [fv FvTyp fv_typ] in Hfv.
  unfold scoped_typ. repeat split; auto; cbn [fv FvTyp] in *; fsetdec.
Qed.

Local Lemma scoped_all : forall G T U x,
    scoped_typ G (typ_all T U) ->
    scoped_typ G T /\ scoped_typ (x ~ T ++ G) (open x U).
Proof.
  intros G T U x [Hfv Hlc]. inversion Hlc; subst.
  pose proof (fv_open_rec U 0 x) as Hopen.
  unfold scoped_typ. repeat split; auto using lc_open_rec.
  - cbn [fv FvTyp fv_typ] in *. fsetdec.
  - rewrite dom_app, dom_one. cbn [fv FvTyp fv_typ] in *. fsetdec.
Qed.

Local Lemma scoped_binding : forall G x T,
    wf_env G -> binds x T G -> scoped_typ G T.
Proof.
  intros G x T Hwf Hbind.
  destruct (binds_split typ x T G Hbind) as [E [P ->]].
  destruct (@wf_env_split P E x T Hwf) as [_ [Hfv Hlc]].
  split; [rewrite !dom_app; fsetdec | exact Hlc].
Qed.

Local Lemma subtykn_to_stp_subty : forall L G S U,
    subtykn L G S U -> wf_env G -> scoped_typ G S -> scoped_typ G U ->
    stp_subty L G S U.
Proof.
  intros L G S U H. induction H; intros Hwf HS HU.
  - apply ss_sel_refl.
  - apply ss_top.
  - apply ss_bot.
  - destruct (scoped_bnd HS), (scoped_bnd HU). auto using ss_bnd.
  - destruct (scoped_all x HS) as [[HTfv HTlc] HU1].
    destruct (scoped_all x HU) as [_ HU2].
    eapply ss_all; [eassumption |].
    apply IHsubtykn; [ | assumption | assumption].
    apply wf_cons; auto.
  - assert (HT : scoped_typ G T) by (eapply scoped_binding; eassumption).
    assert (Hbound : scoped_typ G (typ_bnd S typ_top)).
    { destruct HS as [HSfv HSlc]. split.
      - cbn [fv FvTyp fv_typ] in *. fsetdec.
      - constructor; [exact HSlc | constructor]. }
    specialize (IHsubtykn Hwf HT Hbound).
    destruct (binds_split typ x T G H) as [E [P ->]].
    destruct (@wf_env_split P E x T Hwf) as [_ [Hfv _]].
    destruct (stp_subty_exposes_bound IHsubtykn (P ++ x ~ T) E
      (eq_sym (app_assoc _ P (x ~ T) E)) Hwf Hfv eq_refl)
      as [Hbot | [C [D [Hexp [Hlo Hhi]]]]].
    + eapply ss_sel_right; [eauto using dce_top | apply ss_top].
    + eapply ss_sel_right; [eauto using dce_bnd | exact Hlo].
  - assert (HT : scoped_typ G T) by (eapply scoped_binding; eassumption).
    assert (Hbound : scoped_typ G (typ_bnd typ_bot U)).
    { destruct HU as [HUfv HUlc]. split.
      - cbn [fv FvTyp fv_typ] in *. fsetdec.
      - constructor; [constructor | assumption]. }
    specialize (IHsubtykn Hwf HT Hbound).
    destruct (binds_split typ x T G H) as [E [P ->]].
    destruct (@wf_env_split P E x T Hwf) as [_ [Hfv _]].
    destruct (stp_subty_exposes_bound IHsubtykn (P ++ x ~ T) E
      (eq_sym (app_assoc _ P (x ~ T) E)) Hwf Hfv eq_refl)
      as [Hbot | [C [D [Hexp [Hlo Hhi]]]]].
    + eapply ss_sel_left; [eauto using uce_bot | apply ss_bot].
    + eapply ss_sel_left; [eauto using uce_bnd | exact Hhi].
Qed.

Theorem subtykn_equiv_stp_subty : forall L G S U,
    wf_env G ->
    fv S [<=] dom G -> lc S ->
    fv U [<=] dom G -> lc U ->
    [ L ] G ⊢k S <⦂ U <->
    [ L ] G ⊢s S <⦂ U.
Proof.
  intros L G S U Hwf HSfv HSlc HUfv HUlc. split.
  - intro H. apply (subtykn_to_stp_subty H Hwf); split; assumption.
  - apply stp_subty_to_subtykn.
Qed.
