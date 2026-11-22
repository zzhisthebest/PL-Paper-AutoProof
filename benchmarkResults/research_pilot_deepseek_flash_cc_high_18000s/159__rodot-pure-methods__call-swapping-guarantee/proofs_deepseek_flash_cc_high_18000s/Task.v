Set Implicit Arguments.

Require Import LibExtra AbstractSyntax GeneralTyping.
Require Import Transformation TransformationTerm TransformationLifting.
Require Import TransformationConfig TransformationSwapCalls TransformationIterateSim.
Require Import ConfigTyping OperationalSemantics TypedOperationalSemantics.

Section WithTypingMode.

Context (typing_mode: Mode).

Context (Hms : mode_has_sef typing_mode).

Context (Hmm : mode_has_mutability typing_mode).

(* A variable cannot be typed under the empty context.  This rules out the
   local swap rule firing directly at the top-level empty context. *)
Lemma ctx_binds_empty_nil x T : ctx_binds x T ctx_empty -> False.
Proof.
  intros H. remember ctx_empty as G eqn:E. induction H; discriminate.
Qed.

Lemma ty_var_empty_nil_gen G e (x : var) T :
  G = ctx_empty -> G⁏e ⊢ x ∶ T -> False.
Proof.
  intros HG H. induction H; eauto using ctx_binds_empty_nil.
  all: try (subst; eauto using ctx_binds_empty_nil).
  all: eauto 10 using ctx_binds_empty_nil.
Qed.

Lemma ty_var_empty_nil (x : var) T : ctx_empty ⁏ empty ⊢ x ∶ T -> False.
Proof. intros. eapply ty_var_empty_nil_gen; eauto. Qed.

(* The base call-swapping rule cannot fire directly over the empty context:
   its receiver-typing premise would require typing a variable under ctx_empty. *)
Lemma swap_at_empty_contra (x1 x2 : var) (m1 m2 : met_label)
      (xp1 xp2 y1 y2 : var) (t : trm) (T1 T2 T TZ1 TZ2 : typ) :
  〈 ctx_empty ⁏ empty
    ⊢ trm_let (trm_call (avar_f x1) m1 (avar_f xp1))
        (trm_let (trm_call (avar_f x2) m2 (avar_f xp2)) t /[<- y2]) /[<- y1]
    ∶ T 〉
  ∼(trf_swap_calls_local typing_mode)∼>
  〈 ctx_empty ⁏ empty
    ⊢ trm_let (trm_call (avar_f x2) m2 (avar_f xp2))
        (trm_let (trm_call (avar_f x1) m1 (avar_f xp1)) t /[<- y1]) /[<- y2]
    ∶ T 〉 -> False.
Proof.
  intros H. unfold transform in H.
  inversion H; subst.
  eapply ty_var_empty_nil; eauto.
Qed.

(* The lifted similarity is reflexive on any typed configuration.  This is the
   base case of `trf_iterate` and is what the "identical final configurations"
   outcome of the termination branch uses. *)
Lemma trf_lift_sim_conf_refl (TL : TermTransform)
      (TE : TypedElement ctx typ config) :
  TransformCondConfTyped typing_mode TE ->
  TE ∼(trf_lift_sim_conf typing_mode TL)∼> TE.
Proof.
  intros H. unfold trf_lift_sim_conf. eapply trf_iterate_0. exact H.
Qed.

(* The standard initial `Lv = {null} ∪ fv t ∪ fv T` satisfies the two
   freshness-related components of `ty_config`. *)
Lemma initial_nothing_fresh_T (t : trm) (T : typ) (null : var) :
  nothing_fresh_in_config T
    (t ; stack_nil ; empty ; empty ; (\{null} \u fv t \u fv T)).
Proof.
  unfold nothing_fresh_in_config. cbn.
  intros x Hx. repeat rewrite in_union in *. intuition.
Qed.

Lemma initial_has_null (t : trm) (T : typ) (null : var) :
  ex (fun v => v \in (\{null} \u fv t \u fv T)).
Proof.
  apply (ex_intro _ null).
  repeat rewrite in_union. left. apply in_singleton_self.
Qed.

(* Permuting two fresh adjacent context pushes preserves name lookup,
   visibility and well-formedness.  These are the first prerequisites for
   reconciling the two context-extension orders used by the swap rule. *)
Lemma ctx_binds_swap G y1 vk1 T1 y2 vk2 T2 x T :
  y1 <> y2 ->
  ctx_binds x T ((G § y2 / vk2 ~ T2) § y1 / vk1 ~ T1) ->
  ctx_binds x T ((G § y1 / vk1 ~ T1) § y2 / vk2 ~ T2).
Proof.
  intros Hneq H. inversion H as [| v v2 vk t t2 G0 Hne Hb | v t G0 Hb]; subst.
  - eapply ctx_binds_n. exact Hneq. eapply ctx_binds_e.
  - inversion Hb as [| v v2 vk t t2 G0 Hne2 Hb2 | v t G0 Hb2]; subst.
    + eapply ctx_binds_e.
    + eapply ctx_binds_n. exact Hne2. eapply ctx_binds_n. exact Hne. exact Hb2.
Qed.

Lemma ctx_vis_swap G y1 vk1 T1 y2 vk2 T2 x :
  y1 <> y2 ->
  ctx_vis ((G § y2 / vk2 ~ T2) § y1 / vk1 ~ T1) x ->
  ctx_vis ((G § y1 / vk1 ~ T1) § y2 / vk2 ~ T2) x.
Proof.
  intros Hneq H. inversion H as [| v v2 vk t G0 Hne Hv]; subst.
  - eapply ctx_vis_n. exact Hneq. eapply ctx_vis_e.
  - inversion Hv as [| v v2 vk t G0 Hne2 Hv2]; subst.
    + eapply ctx_vis_e.
    + eapply ctx_vis_n. exact Hne2. eapply ctx_vis_n. exact Hne. exact Hv2.
Qed.

Lemma ctx_ok_swap G y1 vk1 T1 y2 vk2 T2 :
  y1 <> y2 ->
  ctx_ok ((G § y2 / vk2 ~ T2) § y1 / vk1 ~ T1) ->
  ctx_ok ((G § y1 / vk1 ~ T1) § y2 / vk2 ~ T2).
Proof.
  intros Hneq Hok.
  inversion Hok as [| G0 v vk t Hok0 Hv | |]; subst.
  inversion Hok0 as [| G0 v vk t HokG Hv2 | |]; subst.
  apply notin_union_r in Hv. destruct Hv as [Hv_a Hv_b].
  assert (Hy1 : y1 §# G) by exact Hv_b.
  assert (Hy2 : y2 §# (G § y1 / vk1 ~ T1)).
  { apply notin_union_l.
    - apply notin_singleton_l. intros Heq. apply Hneq. symmetry. exact Heq.
    - exact Hv2. }
  eapply ctx_ok_push.
  - eapply ctx_ok_push. exact HokG. exact Hy1.
  - exact Hy2.
Qed.

(* Concatenation algebra used by the suffix-generalized typing permutation. *)
Lemma ctx_concat_empty_r G : G §& ctx_empty = G.
Proof. reflexivity. Qed.

Lemma ctx_concat_empty_l G : ctx_empty §& G = G.
Proof. induction G; cbn; congruence. Qed.

Lemma ctx_concat_assoc G1 G2 G3 :
  (G1 §& G2) §& G3 = G1 §& (G2 §& G3).
Proof. induction G3; cbn; congruence. Qed.

Lemma ctx_binds_swap_S G y1 vk1 T1 y2 vk2 T2 :
  y1 <> y2 ->
  forall S x T,
    ctx_binds x T (((G § y2 / vk2 ~ T2) § y1 / vk1 ~ T1) §& S) ->
    ctx_binds x T (((G § y1 / vk1 ~ T1) § y2 / vk2 ~ T2) §& S).
Proof.
  intros Hneq S.
  induction S as [| S0 IHS v vk t | S0 IHS | S0 IHS];
   [ intros x T H; cbn in H; eapply ctx_binds_swap; eauto
   | intros x T H; cbn in H;
     inversion H as [| v' v2' vk' t' t2' G0' Hne Hb | v' t' G0' Hb]; subst;
     [ eapply ctx_binds_e
     | eapply ctx_binds_n; eauto; eapply IHS; eauto ]
   | intros x T H; cbn in H; inversion H
   | intros x T H; cbn in H; inversion H; subst; eapply ctx_binds_hide; eapply IHS; eauto ].
Qed.
Lemma ctx_vis_swap_S G y1 vk1 T1 y2 vk2 T2 :
  y1 <> y2 ->
  forall S x,
    ctx_vis (((G § y2 / vk2 ~ T2) § y1 / vk1 ~ T1) §& S) x ->
    ctx_vis (((G § y1 / vk1 ~ T1) § y2 / vk2 ~ T2) §& S) x.
Proof.
  intros Hneq S.
  induction S as [| S0 IHS v vk t | S0 IHS | S0 IHS];
   [ intros x H; cbn in H; eapply ctx_vis_swap; eauto
   | intros x H; cbn in H;
     inversion H as [| v' v2' vk' t' G0' Hne Hv]; subst;
     [ eapply ctx_vis_e
     | eapply ctx_vis_n; eauto; eapply IHS; eauto ]
   | intros x H; cbn in H; inversion H
   | intros x H; cbn in H; inversion H ].
Qed.

Lemma ctx_dom_swap_S G y1 vk1 T1 y2 vk2 T2 S :
  ctx_dom (((G § y2 / vk2 ~ T2) § y1 / vk1 ~ T1) §& S)
  = ctx_dom (((G § y1 / vk1 ~ T1) § y2 / vk2 ~ T2) §& S).
Proof.
  induction S as [| S0 IHS v vk t | S0 IHS | S0 IHS]; cbn.
  - apply union_comm_assoc.
  - rewrite IHS. reflexivity.
  - rewrite IHS. reflexivity.
  - rewrite IHS. reflexivity.
Qed.
Lemma ctx_ok_swap_S G y1 vk1 T1 y2 vk2 T2 :
  y1 <> y2 ->
  forall S,
    ctx_ok (((G § y2 / vk2 ~ T2) § y1 / vk1 ~ T1) §& S) ->
    ctx_ok (((G § y1 / vk1 ~ T1) § y2 / vk2 ~ T2) §& S).
Proof.
  intros Hneq S.
  induction S as [| S0 IHS v vk t | S0 IHS | S0 IHS];
   [ intros H; cbn in H; eapply ctx_ok_swap; eauto
   | intros H; cbn in H; inversion H as [| G0 v' vk' t' Hok0 Hv | |]; subst;
     eapply ctx_ok_push;
     [ eapply IHS; exact Hok0
     | rewrite ctx_dom_swap_S in Hv; exact Hv ]
   | intros H; cbn in H; inversion H; subst; eapply ctx_ok_stop; eapply IHS; eauto
   | intros H; cbn in H; inversion H; subst; eapply ctx_ok_hide; eapply IHS; eauto ].
Qed.

Theorem swap_calls_transformation_guarantee ta tb Ta Tb:
  〈ctx_empty⁏empty ⊢ ta ∶ Ta〉 ∼(trf_local_idtyp_trm typing_mode (trf_swap_calls_local typing_mode))∼> 〈ctx_empty⁏empty ⊢ tb ∶ Tb〉 ->
  closed ta ->
  closed tb ->
  closed Ta ->
  closed Tb ->

  exists Ca Cb,
    config_initial ta Ca /\
    config_initial tb Cb /\
    (
      ( exists  na nb Ga2 Gb2 Ca2 Cb2,

        nb <= na /\

        ctx_empty ⊢ Ca ∶ Ta ⊣na↦* Ga2 ⊢ Ca2 /\
        ctx_empty ⊢ Cb ∶ Tb ⊣nb↦* Gb2 ⊢ Cb2 /\
        answer Ca2 /\
        answer Cb2 /\

        〈Ga2 ⊢ Ca2 ∶ Ta〉 ∼(trf_lift_sim_conf typing_mode (trf_swap_calls_local typing_mode))∼> 〈Gb2 ⊢ Cb2 ∶ Tb〉
      ) \/ (
         forall (n : nat),
         exists (Ca2 Cb2 : config),
           Ca ⊣n↦* Ca2 /\
           Cb ⊣n↦* Cb2
      )
    ).

End WithTypingMode.
