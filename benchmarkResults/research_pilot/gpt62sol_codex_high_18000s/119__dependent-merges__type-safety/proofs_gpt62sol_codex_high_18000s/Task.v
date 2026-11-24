Require Import Program.Equality.
From Stdlib Require Import Lia.

Require Import Metalib.Metatheory.

Require Import Language Infra.

#[local] Hint Constructors sub ord gord toplike value genv has_type casting step
  : safety.

Lemma sub_refl : forall A, sub A A.
Proof. induction A; eauto with safety. Qed.

Lemma sub_to_and : forall A B C,
  sub A (and B C) -> sub A B /\ sub A C.
Proof.
  intros A B C H.
  remember (and B C) as D in H.
  induction H; inversion HeqD; subst; firstorder eauto with safety.
Qed.

Lemma sub_from_and : forall A B C,
  ord C -> sub (and A B) C -> sub A C \/ sub B C.
Proof.
  intros A B C HO HS. inversion HS; subst; try solve [auto]; inversion HO.
Qed.

Lemma sub_trans : forall A B C, sub A B -> sub B C -> sub A C.
Proof.
  assert (Htrans : forall n B, size_typ B < n ->
    forall A C, sub A B -> sub B C -> sub A C).
  {
    induction n as [|n IH]; intros B Hsize X C H K; [lia |].
    revert X H.
    induction K; intros X H; eauto with safety.
    - apply sub_to_and in H as [H _].
      eapply IH; [| exact H | eassumption]. simpl in Hsize; lia.
    - apply sub_to_and in H as [_ H].
      eapply IH; [| exact H | eassumption]. simpl in Hsize; lia.
    - remember (rcd x A) as T in H.
      induction H; inversion HeqT; subst; eauto with safety.
      constructor. eapply IH; [| eassumption | eassumption]. simpl in Hsize; lia.
    - remember (arr A B) as T in H.
      induction H; inversion HeqT; subst; eauto with safety.
      constructor; eapply IH; [| eassumption | eassumption
                              | | eassumption | eassumption]; simpl in Hsize; lia.
  }
  intros A B C. apply (Htrans (S (size_typ B)) B). lia.
Qed.

Lemma check_sub : forall G e A B,
  has_type G e chk A -> sub A B -> has_type G e chk B.
Proof.
  intros G e A B H HS. inversion H; subst.
  eauto using sub_trans with safety.
Qed.

Lemma gord_ord : forall A, gord A -> ord A.
Proof. intros A H; inversion H; auto with safety. Qed.

Lemma top_disjoint : forall A, disjoint top A.
Proof.
  intros A [C [HC [HS _]]]. inversion HS; subst; inversion HC.
Qed.

Lemma toplike_or_gord : forall A,
  toplike A \/ exists C, gord C /\ sub A C.
Proof.
  induction A.
  - right. eauto with safety.
  - left. constructor.
  - destruct IHA1 as [H1|[C [HC HS]]].
    + destruct IHA2 as [H2|[C [HC HS]]]; eauto with safety.
    + right. eauto with safety.
  - destruct IHA as [H|[C [HC HS]]].
    + left. auto with safety.
    + right. exists (rcd n C). auto with safety.
  - destruct IHA2 as [H|[C [HC HS]]].
    + left. auto with safety.
    + right. exists (arr A1 C). auto using sub_refl with safety.
Qed.

Lemma sub_preserves_toplike : forall A B, sub A B -> toplike A -> toplike B.
Proof.
  intros A B H. induction H; intro HT; inversion HT; subst; eauto with safety.
Qed.

Lemma genv_unique : forall A v w, genv A v -> genv A w -> v = w.
Proof.
  intros A v w H; revert w.
  induction H; intros w HW; inversion HW; subst; repeat f_equal; eauto.
Qed.

Lemma genv_exists : forall A, toplike A -> exists v, genv A v.
Proof.
  intros A H. induction H as [|A B HA [v Hv] HB [w Hw]|A B HB [v Hv]|l B HB [v Hv]];
    eauto with safety.
Qed.

Lemma genv_value : forall A v, genv A v -> value v.
Proof. intros A v H; induction H; eauto with safety. Qed.

Lemma gord_not_toplike : forall A, gord A -> ~ toplike A.
Proof.
  intros A H. induction H; intro HT; inversion HT; subst; auto.
Qed.

Lemma toplike_disjoint : forall A B, toplike B -> disjoint A B.
Proof.
  intros A B HT [C [HC [_ HS]]].
  eapply gord_not_toplike; [exact HC | eapply sub_preserves_toplike; eauto].
Qed.

Lemma genv_toplike : forall A v, genv A v -> toplike A.
Proof. intros A v H; induction H; auto with safety. Qed.

Lemma genv_typing : forall A v, genv A v -> forall G, has_type G v inf A.
Proof.
  intros A v H. induction H; intro G.
  - constructor.
  - eapply tbox.
    + apply tunit.
    + eapply tlam with (A' := A).
      * apply top_disjoint.
      * constructor.
      * apply sub_refl.
      * eapply tsub; [apply IHgenv | apply sub_refl].
  - eapply tmrg.
    + apply IHgenv1.
    + apply IHgenv2.
    + apply toplike_disjoint. eauto using genv_toplike.
    + apply toplike_disjoint. eauto using genv_toplike.
  - constructor. apply IHgenv.
Qed.

Lemma cast_toplike : forall v A w,
  casting v A w -> toplike A -> genv A w.
Proof.
  intros v A w H. induction H; intro HT;
    try solve [inversion HT]; eauto with safety.
  - inversion HT; subst; eauto with safety.
  - inversion HT; subst; eauto with safety.
  - inversion HT; subst; contradiction.
Qed.

Lemma cast_value : forall v A w, casting v A w -> value w.
Proof.
  intros v A w H. induction H; eauto using genv_value with safety.
  inversion H1; subst; eauto with safety.
Qed.

Lemma merge_typing : forall G v w T,
  has_type G (merge v w) inf T ->
  exists A B E, T = and A B /\ has_type G v inf A /\ has_type E w inf B /\
    (disjoint A B \/ consistencySpec v w).
Proof.
  intros G v w T H. inversion H; subst; eauto 12.
Qed.

Lemma lam_untyped : forall G fm e m T, ~ has_type G (lam fm e) m T.
Proof.
  intros G fm e m T H. inversion H; subst.
  match goal with H : has_type _ (lam _ _) inf _ |- _ => inversion H end.
Qed.

Lemma lambda_typing : forall G fm e A B T,
  has_type G (ann (lam fm e) (arr A B)) inf T ->
  exists C A', T = arr C B /\ disjoint G A /\ ext A fm A' /\
    sub C A' /\ has_type (and G A) e chk B.
Proof.
  intros G fm e A B T H. inversion H; subst; eauto 10.
  exfalso. eapply lam_untyped; eassumption.
Qed.

Lemma closure_typing : forall G v fm e A B T,
  has_type G (box v (ann (lam fm e) (arr A B))) inf T ->
  exists E C A', T = arr C B /\ has_type G v inf E /\ disjoint E A /\
    ext A fm A' /\ sub C A' /\ has_type (and E A) e chk B.
Proof.
  intros G v fm e A B T H. inversion H; subst.
  match goal with
  | H : has_type _ (ann (lam _ _) _) inf _ |- _ =>
      destruct (lambda_typing _ _ _ _ _ _ H) as [C [A' [? [? [? [? ?]]]]]]
  end.
  eauto 12.
Qed.

(* Ground types can share a supertype when their result types and record
   labels agree in shape. Arrow domains can be intersected. *)
Fixpoint ground_shape (A : typ) : typ :=
  match A with
  | rcd l B => rcd l (ground_shape B)
  | arr _ B => arr top (ground_shape B)
  | _ => A
  end.

Lemma common_ground_shape : forall A B,
  gord A -> gord B -> ground_shape A = ground_shape B -> cost_spec A B.
Proof.
  intros A B HA. revert B.
  induction HA as [|A B HB IH|l A HA IH]; intros T HT HE;
    inversion HT; subst; simpl in HE; try discriminate.
  - exists int. auto with safety.
  - injection HE as HE.
    destruct (IH _ H HE) as [C [HC [HBC HTC]]].
    eexists (arr (and A A0) C). repeat split;
      auto using sub_refl with safety.
  - injection HE as Hlabel HE; subst x.
    destruct (IH _ H HE) as [C [HC [HAC HTC]]].
    eexists (rcd l C). auto with safety.
Qed.

(* A cast may use the closure's full argument type, even if inference used
   a narrower domain. A ground supertype of the same shape still exists. *)
Lemma cast_ground_shape : forall v T w, casting v T w ->
  forall G A C, has_type G v inf A -> gord C -> sub T C ->
  exists D, gord D /\ sub A D /\ ground_shape D = ground_shape C.
Proof.
  intros v T w H.
  induction H; intros G T Q HT HQ HS.
  - exfalso. eapply top_disjoint. exists Q. auto using sub_refl.
  - inversion HT; subst. exists Q. auto.
  - destruct (merge_typing _ _ _ _ HT) as [L [R [E [-> [HL [HR _]]]]]].
    destruct (IHcasting _ _ _ HL HQ HS) as [D [HD [HL' HE]]].
    exists D. auto with safety.
  - destruct (merge_typing _ _ _ _ HT) as [L [R [E [-> [HL [HR _]]]]]].
    destruct (IHcasting _ _ _ HR HQ HS) as [D [HD [HR' HE]]].
    exists D. auto with safety.
  - destruct (sub_from_and _ _ _ (gord_ord _ HQ) HS); eauto.
  - inversion HT; subst. inversion HQ; subst; inversion HS; subst.
    match goal with
    | HT' : has_type G v inf ?S, HQ' : gord ?Q', HS' : sub A ?Q' |- _ =>
        destruct (IHcasting _ S Q' HT' HQ' HS') as [D [HD [HD' HE]]]
    end.
    exists (rcd x0 D). simpl. rewrite HE. auto with safety.
  - destruct (closure_typing _ _ _ _ _ _ _ HT)
      as [E [Dom [Arg [-> [_ [_ [_ [_ _]]]]]]]].
    inversion HQ; subst; inversion HS; subst.
    eexists (arr Dom _). repeat split; simpl; eauto using sub_refl, sub_trans with safety.
  - destruct (closure_typing _ _ _ _ _ _ _ HT)
      as [E [Dom [Arg [-> [_ [_ [_ [_ _]]]]]]]].
    inversion HQ; subst; inversion HS; subst.
    eexists (arr Dom _). repeat split; simpl; eauto using sub_refl, sub_trans with safety.
Qed.

Lemma disjoint_consistent : forall G E v w A B,
  has_type G v inf A -> has_type E w inf B -> disjoint A B ->
  consistencySpec v w.
Proof.
  intros G E v w A B HV HW HD T u z Hu Hz.
  destruct (toplike_or_gord T) as [HT | [C [HC HS]]].
  - eapply genv_unique; eauto using cast_toplike.
  - exfalso. apply HD.
    destruct (cast_ground_shape _ _ _ Hu _ _ _ HV HC HS) as [U [HU [HA HUC]]].
    destruct (cast_ground_shape _ _ _ Hz _ _ _ HW HC HS) as [Z [HZ [HB HZC]]].
    destruct (common_ground_shape U Z HU HZ) as [D [HD' [HUD HZD]]].
    + congruence.
    + exists D. eauto using sub_trans.
Qed.

(* Casting a result again can be realized as a cast of the original input. *)
Lemma cast_compose : forall v A w, casting v A w ->
  forall B u, casting w B u -> casting v B u.
Proof.
  intros v A w H.
  induction H; intro T; induction T; intros u K;
    try solve [constructor | inversion K; subst; eauto 8 with safety].
  - inversion K; subst; eauto 8 using sub_trans with safety.
  - inversion H4; subst. inversion K.
  - inversion K; subst; try apply cast_top;
      match goal with Hord : ord top |- _ => inversion Hord end.
  - inversion K; subst; try solve [match goal with Hord : ord (and _ _) |- _ => inversion Hord end].
    apply cast_and; eauto.
  - inversion H4; subst. inversion K.
  - inversion H4; subst. inversion K; subst.
    + match goal with Hext : ext _ bl _ |- _ => inversion Hext; subst end.
      exfalso.
      eauto using sub_preserves_toplike, genv_toplike with safety.
    + match goal with Hext : ext _ bl _ |- _ => inversion Hext; subst end.
      eauto 8 using sub_trans with safety.
Qed.

Lemma cast_deterministic : forall v T w, casting v T w ->
  forall u G A, has_type G v inf A -> casting v T u -> w = u.
Proof.
  intros v T w H.
  induction H; intros u G T HT K;
    try solve [inversion K; subst; try contradiction;
      try match goal with HO : ord top |- _ => inversion HO end;
      eauto using genv_unique].
  - destruct (merge_typing _ _ _ _ HT) as [L [R [E [-> [HL [HR HC]]]]]].
    inversion K; subst;
      try solve [inversion H0 | eauto].
    destruct HC as [HD | HC].
    + eapply (disjoint_consistent _ _ _ _ _ _ HL HR HD); eassumption.
    + eapply HC; eassumption.
  - destruct (merge_typing _ _ _ _ HT) as [L [R [E [-> [HL [HR HC]]]]]].
    inversion K; subst;
      try solve [inversion H0 | eauto].
    symmetry. destruct HC as [HD | HC].
    + eapply (disjoint_consistent _ _ _ _ _ _ HL HR HD); eassumption.
    + eapply HC; eassumption.
  - inversion K; subst;
      try solve [match goal with HO : ord (and _ _) |- _ => inversion HO end].
    f_equal; eauto.
  - inversion HT; subst. inversion K; subst. f_equal; eauto.
Qed.

Lemma value_retyping : forall v, value v ->
  forall G A, has_type G v inf A -> forall E, has_type E v inf A.
Proof.
  intros v HV. induction HV; intros G T HT E; inversion HT; subst;
    eauto with safety.
  eapply tcon; eauto using disjoint_consistent.
Qed.

Lemma typed_merge_values : forall G v w A B,
  value v -> value w ->
  has_type G v inf A -> has_type G w inf B -> disjoint A B ->
  has_type G (merge v w) inf (and A B).
Proof. intros. eauto using disjoint_consistent with safety. Qed.

Lemma cast_typing : forall v A w, casting v A w ->
  forall G T, has_type G v inf T -> has_type G w inf A.
Proof.
  intros v A w H.
  induction H; intros G T HT; try solve [eauto using genv_typing with safety].
  - destruct (merge_typing _ _ _ _ HT) as [L [R [E [_ [HL _]]]]].
    eauto.
  - destruct (merge_typing _ _ _ _ HT) as [L [R [E [_ [_ [HR _]]]]]].
    eauto using value_retyping, cast_value.
  - apply tcon; eauto using cast_value.
    intros S u z Hu Hz.
    eapply cast_deterministic with (v := v) (T := S);
      eauto using cast_compose.
  - inversion HT; subst; eauto with safety.
  - destruct (closure_typing _ _ _ _ _ _ _ HT)
      as [E [Dom [Arg [-> [HV [HD [HE [HS HB]]]]]]]].
    eapply tbox; [exact HV |].
    eapply tlam with (A' := A'); eauto using check_sub.
Qed.

Lemma closure_cast_exists : forall G v fm e A B S C D,
  value v ->
  has_type G (box v (ann (lam fm e) (arr A B))) inf S ->
  sub S (arr C D) ->
  exists w, casting (box v (ann (lam fm e) (arr A B))) (arr C D) w.
Proof.
  intros G v fm e A B S C D HV HT HS.
  destruct (closure_typing _ _ _ _ _ _ _ HT)
    as [E [Dom [Arg [-> [_ [_ [HE [HA _]]]]]]]].
  inversion HS; subst.
  assert (sub C Arg) by eauto using sub_trans.
  destruct (toplike_or_gord D) as [HD | [Q [HQ HD]]].
  - destruct (genv_exists _ (TL_arr C D HD)) as [w HW].
    exists w. eapply cast_arr_tl; eassumption.
  - assert (~ toplike D).
    { intro Htop. eapply gord_not_toplike.
      - exact HQ.
      - eapply sub_preserves_toplike; eassumption. }
    eexists. eapply cast_arr; eassumption.
Qed.

Lemma cast_exists : forall v, value v ->
  forall B G A, has_type G v inf A -> sub A B ->
  exists w, casting v B w.
Proof.
  intros v HV. induction HV; intro T; induction T; intros G S HT HS;
    try solve [exists unit; apply cast_top |
      destruct (sub_to_and _ _ _ HS) as [HL HR];
      destruct (IHT1 _ _ HT HL) as [v' HV'];
      destruct (IHT2 _ _ HT HR) as [w' HW'];
      exists (merge v' w'); apply cast_and; assumption].
  all: try solve [inversion HT; subst; inversion HS; subst; eauto with safety].
  all: try solve [
    match type of HT with
    | has_type _ (merge _ _) _ _ =>
      destruct (merge_typing _ _ _ _ HT) as [L [R [E [-> [HL [HR _]]]]]];
      match goal with
      | |- exists w, casting _ ?Tgt w =>
        let HO := fresh "HO" in
        assert (HO : ord Tgt) by constructor;
        destruct (sub_from_and _ _ _ HO HS) as [Hleft | Hright];
        [destruct (IHHV1 _ _ _ HL Hleft) as [w HW];
         exists w; apply cast_mrgl; assumption
        |destruct (IHHV2 _ _ _ HR Hright) as [w HW];
         exists w; apply cast_mrgr; assumption]
      end
    end].
  all: try solve [eapply closure_cast_exists; eassumption].
  all: try solve [
    destruct (closure_typing _ _ _ _ _ _ _ HT) as [? [? [? [-> _]]]];
    inversion HS].
  inversion HT; subst. inversion HS; subst.
  match goal with
  | H : has_type G e inf ?A, K : sub ?A T |- _ =>
      destruct (IHHV _ _ _ H K) as [w HW]
  end.
  eauto with safety.
Qed.

Lemma check_cast : forall G v A,
  value v -> has_type G v chk A -> exists w, casting v A w.
Proof. intros G v A HV HT. inversion HT; subst. eauto using cast_exists. Qed.

Lemma value_no_step : forall v e e', step v e e' -> ~ value e.
Proof.
  intros v e e' H. induction H; intro HV; inversion HV; subst; eauto;
    match goal with H : value (ann _ _) |- _ => inversion H end.
Qed.

Lemma value_dec : forall e, {value e} + {~ value e}.
Proof.
  induction e as [i | | |e1 IH1 e2 IH2| e IH A |l e IH | e IH l |
                   fm e IH | e1 IH1 e2 IH2 | e1 IH1 e2 IH2];
    try solve [left; constructor | right; intro H; inversion H].
  - destruct IH1, IH2; try solve [left; constructor; assumption];
      right; intro H; inversion H; contradiction.
  - destruct IH; [left; constructor; assumption |
      right; intro H; inversion H; contradiction].
  - destruct IH1 as [HV | HNV]; [|right; intro H; inversion H; contradiction].
    destruct e2 as [| | | | body A | | | | |];
      try solve [right; intro H; inversion H].
    destruct body as [| | | | | | |fm e | |];
      try solve [right; intro H; inversion H].
    destruct A as [| | | |A B]; try solve [right; intro H; inversion H].
    destruct fm.
    + left. apply vclos. exact HV.
    + destruct A; try solve [right; intro H; inversion H].
      left. apply vsclos. exact HV.
Qed.

Lemma arrow_value_form : forall G v C B,
  value v -> has_type G v inf (arr C B) ->
  exists env fm e A, v = box env (ann (lam fm e) (arr A B)) /\ value env.
Proof.
  intros G v C B HV HT. inversion HV; subst;
    try solve [inversion HT].
  all: destruct (closure_typing _ _ _ _ _ _ _ HT) as [? [? [? [HE _]]]];
    injection HE as _ ->; eauto 8.
Qed.

Lemma record_value_form : forall G v l A,
  value v -> has_type G v inf (rcd l A) ->
  exists e, v = rec l e /\ value e.
Proof.
  intros G v l A HV HT. inversion HV; subst;
    try solve [inversion HT; subst; eauto].
  all: destruct (closure_typing _ _ _ _ _ _ _ HT) as [? [? [? [HE _]]]];
    discriminate.
Qed.

Lemma constr_exists : forall A fm A' v, ext A fm A' ->
  exists w, constr A v fm w.
Proof. intros A fm A' v H. inversion H; subst; eauto using constr. Qed.

Lemma constr_typing : forall A fm A' v w, ext A fm A' ->
  constr A v fm w -> forall G, has_type G v inf A' -> has_type G w inf A.
Proof.
  intros A fm A' v w HE HC G HT.
  inversion HE; subst; inversion HC; subst; eauto with safety.
Qed.

Lemma constr_value : forall A fm v w,
  constr A v fm w -> value v -> value w.
Proof. intros A fm v w HC HV. inversion HC; subst; auto with safety. Qed.

Lemma typing_progress : forall G e m A, has_type G e m A ->
  forall v, value v -> has_type top v inf G ->
  value e \/ exists e', step v e e'.
Proof.
  intros G e m A HT. induction HT; intros v HV HE;
    try solve [eauto with safety].
  - destruct (IHHT1 _ HV HE) as [HV1 | [e1' HS1]].
    + assert (value (merge v e1)) as HVE by auto with safety.
      assert (has_type top (merge v e1) inf (and G A)) as HTE by
        (eapply typed_merge_values; eauto using value_retyping).
      destruct (IHHT2 _ HVE HTE) as [HV2 | [e2' HS2]]; eauto with safety.
    + right. eauto with safety.
  - destruct (IHHT _ HV HE) as [HVal | [e' HS]].
    + destruct (check_cast _ _ _ HVal HT) as [w HC]. eauto with safety.
    + eauto with safety.
  - destruct (IHHT1 _ HV HE) as [HV1 | [e1' HS1]].
    + destruct (IHHT2 _ HV HE) as [HV2 | [e2' HS2]].
      * destruct (arrow_value_form _ _ _ _ HV1 HT1)
          as [env [fm [body [Dom [-> HEnv]]]]].
        destruct (closure_typing _ _ _ _ _ _ _ HT1)
          as [E [C [Arg [HTy [HEnvTy [HD [Hext [HSub HBody]]]]]]]].
        injection HTy as <-.
        destruct (check_cast G e2 Arg HV2 (check_sub _ _ _ _ HT2 HSub)) as [w HC].
        destruct (constr_exists _ _ _ w Hext) as [w' HC'].
        right. eexists. eapply step_beta; eassumption.
      * eauto with safety.
    + eauto with safety.
  - destruct (value_dec (box e1 e2)) as [HVal | HNot]; [auto | right].
    destruct (IHHT1 _ HV HE) as [HV1 | [e1' HS1]].
    + destruct (IHHT2 _ HV1 (value_retyping _ HV1 _ _ HT1 top))
        as [HV2 | [e2' HS2]]; eauto with safety.
    + eauto with safety.
  - destruct (IHHT _ HV HE) as [HVal | [e' HS]]; eauto with safety.
  - destruct (IHHT _ HV HE) as [HVal | [e' HS]]; [|eauto with safety].
    destruct (record_value_form _ _ _ _ HVal HT) as [w [-> HW]].
    eauto with safety.
Qed.

Lemma step_environment_value : forall v e e', step v e e' -> value v.
Proof.
  intros v e e' H. induction H; auto. inversion IHstep; assumption.
Qed.

Lemma check_transport : forall G e e' B,
  has_type G e chk B ->
  (forall A, has_type G e inf A -> has_type G e' inf A) ->
  has_type G e' chk B.
Proof. intros G e e' B HT H. inversion HT; subst; eauto with safety. Qed.

Lemma inferred_preservation : forall v e e', step v e e' ->
  forall G T, has_type top v inf G -> has_type G e inf T ->
  has_type G e' inf T.
Proof.
  intros v e e' HS. induction HS; intros G T HE HT.
  - inversion HT; subst. eauto using value_retyping.
  - inversion HT; subst.
    + match goal with H : has_type _ _ chk _ |- _ => inversion H; subst end.
      eauto using cast_typing.
    + match goal with H : value (lam _ _) |- _ => inversion H end.
  - inversion HT; subst.
    + apply tann. eapply check_transport; eauto.
    + inversion HS.
  - inversion HT; subst.
    + apply tmrg; try assumption.
      eapply IHHS; [| eassumption].
      assert (value v) by
        (pose proof (step_environment_value _ _ _ HS) as HM; inversion HM; assumption).
      eapply typed_merge_values; eauto using value_retyping.
    + exfalso. eapply value_no_step; eassumption.
  - inversion HT; subst; eauto with safety.
    exfalso. eapply value_no_step; eassumption.
  - inversion HT; subst; eauto with safety.
  - inversion HT; subst.
    match goal with H : has_type _ (rec _ _) inf _ |- _ => inversion H; subst end.
    assumption.
  - inversion HT; subst; eauto with safety.
  - eapply tbox; [| exact HT]. eauto using value_retyping.
  - inversion HT; subst.
    match goal with
    | HF : has_type _ (box _ _) inf _ |- _ =>
        destruct (closure_typing _ _ _ _ _ _ _ HF)
          as [E [Dom [Arg [HTy [HEnv [HD [HExt [HSub HBody]]]]]]]]
    end.
    inversion HTy; subst.
    eapply tbox with (B := and E A).
    + eapply typed_merge_values; eauto using constr_typing, constr_value, cast_value.
      match goal with H : has_type _ v1 chk _ |- _ => inversion H; subst end.
      eauto using cast_typing, constr_typing.
    + apply tann. exact HBody.
  - inversion HT; subst; eauto with safety.
  - inversion HT; subst. eapply tapp; [eassumption |].
    eapply check_transport; eauto.
  - inversion HT; subst; eauto using value_retyping.
  - inversion HT; subst. eapply tbox; [eassumption |].
    eapply IHHS; [|eassumption].
    eauto using value_retyping, step_environment_value.
  - inversion HT; subst; eauto with safety.
Qed.

Lemma typing_preservation : forall v e e', step v e e' ->
  forall G m T, has_type top v inf G -> has_type G e m T ->
  has_type G e' m T.
Proof.
  intros v e e' HS G m T HE HT. destruct m.
  - eauto using inferred_preservation.
  - eapply check_transport; eauto using inferred_preservation.
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
  intros G e m A HT v e' HV HE HS.
  induction HS.
  - eapply typing_progress; eassumption.
  - apply IHHS. eapply typing_preservation; eassumption.
Qed.
