Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.LocalClosure.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsSubstitution.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SystemFLemmasWeaken.
Require Import AutoProof.SystemRF.SystemRF.Typing.
Require Import AutoProof.SystemRF.SystemRF.PrimitivesWFType.
Require Import AutoProof.SystemRF.SystemRF.LemmasWeakenWF.
Require Import AutoProof.SystemRF.SystemRF.LemmasWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SubstitutionLemmaWF.
Require Import AutoProof.SystemRF.SystemRF.LemmasTyping.
Require Import AutoProof.SystemRF.SystemRF.LemmasSubtyping. 

Lemma lem_self_idempotent_upper : forall (g:env) (t:type) (k:kind) (e:expr),
    WFtype g t k -> HasFtype (erase_env g) e (erase t)
                 -> Subtype g (self t e k) (self (self t e k) e k).
Proof. intros g t k e p_g_t; induction p_g_t; intros p_e_t; simpl.
  - (* WFBase *) apply SBase with (binds g); intros. apply IRepeat.
  - (* WFRefn *) apply SBase with (binds g); intros. apply IRepeat.
  - (* WFVar  *) destruct k; simpl.
    * (* Base *) apply SBase with (binds g); intros. apply IRepeat.
    * (* Star *) apply lem_sub_refl with Star; apply WFVar; assumption.
  - (* WFFunc *) apply lem_sub_refl with Star; apply WFFunc with k_x k nms;
    assumption.
  - (* WFExis *) destruct k; simpl.
    * (* Base *) apply lem_subtype_in_exists with k_x (union nms (bindsF (erase_env g)));
      assert (TExists t_x (self (self t e Base) e Base) 
                = self (self (TExists t_x t) e Base) e Base) as HTEx by reflexivity;
        try rewrite HTEx;
      try apply lem_wftype_islct with g Base; 
      try apply lem_selfify_wf; try apply lem_selfify_wf; try apply WFExis with k_x nms;
      simpl; simpl in p_e_t; try rewrite lem_erase_self; try assumption; intros;
      repeat rewrite lem_unbindT_self; try apply H0;
      try rewrite lem_erase_unbind;
      assert (erase_env (Cons y t_x g) = concatF (FCons y (erase t_x) (erase_env g)) FEmpty)
        as Henv by reflexivity; try rewrite Henv;
      try apply lem_weaken_ftyp; simpl;
      apply not_elem_union_elim in H1; destruct H1;
      try apply intersect_empty_r;
      try apply lem_ftyp_islc with (erase_env g) (erase t); intuition.
    * (* Star *) apply lem_sub_refl with Star; apply WFExis with k_x nms; assumption.
  - (* WFPoly *) apply lem_sub_refl with Star; apply WFPoly with k_t nms; assumption.
  - (* WFKind *) assert (self t e Star = t) as Hself by (destruct t; reflexivity);
    repeat rewrite Hself; apply lem_sub_refl with Base; apply p_g_t.
  Qed.

Lemma lem_exact_subtype : forall (g:env) (s:type) (k_s:kind) (t:type) (k:kind) (e:expr),
    Subtype g s t -> WFEnv g -> WFtype g s k_s -> WFtype g t k -> isLC e 
                  -> HasFtype (erase_env g) e (erase t)
                  -> Subtype g (self s e k) (self t e k).
Proof. intros g s k_x t k e p_s_t; induction p_s_t; intros p_g p_g_s p_g_t He p_e_t.
  - (* SBase *) destruct k; simpl; apply SBase with (union nms (binds g)); intros;
    apply not_elem_union_elim in H0; destruct H0.
    * (* Base *) assert (unbindP y (PCons (eqlPred b e) p2)
                          = strengthen (unbindP y (PCons (eqlPred b e) PEmpty)) (unbindP y p2) )
          as Hp2' by reflexivity; rewrite Hp2';
      apply IConj; try apply ICons1; apply ITrans with (unbindP y p1); try apply ICons2; intuition.
    * (* Star *) intuition.
  - (* SFunc *) destruct k; simpl; apply SFunc with nms; trivial.
  - (* SWitn *) assert (self (TExists t_x t') e k = TExists t_x (self t' e k))
        as Hex by (destruct k; destruct t'; reflexivity); rewrite Hex;
    apply SWitn with v_x; try rewrite lem_tsubBV_self; try apply IHp_s_t;
    inversion p_g_t; try inversion H1;
    pose proof (fresh_var_not_elem nms g) as Hy; 
      set (y := fresh_var nms g) in Hy; destruct Hy as [Hy Hy'];
    try rewrite lem_erase_tsubBV;
    try rewrite lem_tsubFV_unbindT with y v_x t'; try apply lem_subst_wf_top with t_x; 
    try apply H6; try (apply WFKind; apply H10); simpl in p_e_t;
    pose proof (lem_free_bound_in_env g (TExists t_x t') k y p_g_t Hy') 
      as Ht'; simpl in Ht'; destruct Ht' as [Ht' Ht''];
    apply not_elem_union_elim in Ht'; destruct Ht';
    try apply wfenv_unique; try (apply p_e_t || apply lem_typing_hasftype); trivial. 
  - (* SBind *) inversion p_g_s; try inversion H2; 
    assert (self (TExists t_x t) e k = TExists t_x (self t e k))
        as Hex by (destruct k; destruct t; reflexivity); rewrite Hex;
    apply SBind with (union (union nms nms0) (binds g)); 
    try apply lem_self_islct; try apply lem_wftype_islct with g k; trivial; intros y Hy;
    apply not_elem_union_elim in Hy; destruct Hy as [Hy Hy''];
    apply not_elem_union_elim in Hy; destruct Hy as [Hy Hy'];
    rewrite lem_unbindT_self; try apply H1; simpl;
    try apply WFEBind with k_x0; try apply H7; 
    try (destruct k_x; try apply H11; try (apply WFKind; apply H11));
    try apply lem_weaken_wf_top; try apply lem_weaken_ftyp_top;
    try apply lem_ftyp_islc with (erase_env g) (erase t');
    unfold in_envF; try rewrite <- binds_erase_env; trivial.
  - (* SPoly *) destruct k; simpl; apply SPoly with nms; trivial.
  Qed.

Lemma lem_exact_type : forall (g:env) (v:expr) (t:type) (k:kind),
    isValue v -> Hastype g v t -> WFtype g t k -> WFEnv g -> Hastype g v (self t v k).
Proof. intros g v t k Hv p_v_t; induction p_v_t; intros p_g_t p_g.
  - (* T_BC *) apply T_Sub with (tybc b) Base; try apply T_BC; destruct k;
    try apply lem_selfify_wf; try apply lem_wf_tybc; try apply lem_tybc_exact;
    assert (self (tybc b) (Bool_constant b) Star = tybc b) by reflexivity; try rewrite H;
    simpl; try apply FTBC; apply lem_sub_refl with Star; apply p_g_t.
  - (* T_IC *) apply T_Sub with (tyic m) Base; try apply T_IC; destruct k;
    try apply lem_selfify_wf; try apply lem_wf_tyic; try apply lem_tyic_exact;
    assert (self (tyic m) (Int_constant m) Star = tyic m) by reflexivity; try rewrite H;
    simpl; try apply FTIC; apply lem_sub_refl with Star; apply p_g_t.
  - (* T_Var *) destruct k0.
    * apply T_Sub with (self T (FV x) Base) Base; try apply T_Var; destruct k;
      try rewrite lem_self_star; try apply p_g_t;
      try apply lem_selfify_wf; try rewrite lem_erase_self;
      try apply lem_self_idempotent_upper; 
      try apply FTVar; try apply boundin_erase_env;
      try apply lem_sub_refl with Star; trivial.
    * rewrite lem_self_star; apply T_Var; rewrite lem_self_star in p_g_t; trivial.
  - (* T_Prm *) destruct k; try rewrite lem_self_star; try apply T_Prm;
    destruct c; unfold primitive_type in p_g_t; inversion p_g_t. 
  - (* T_Abs *) destruct k; try inversion p_g_t; try rewrite lem_self_star;
    apply T_Abs with k0 nms; intuition.
  - (* T_App *) simpl in Hv; contradiction.
  - (* T_AbsT *) destruct k; try inversion p_g_t; try rewrite lem_self_star;
    apply T_AbsT with nms; trivial.
  - (* T_AppT *) simpl in Hv; contradiction.
  - (* T_Let *) simpl in Hv; contradiction.
  - (* T_Ann *) simpl in Hv; contradiction.
  - (* T_If *) simpl in Hv; contradiction.
  - (* T_Sub *) apply T_Sub with (self T1 t k) Star; try apply IHp_v_t;
    try apply lem_exact_subtype with k; try apply lem_typ_islc with g T1;
    apply lem_typing_wf in p_v_t as p_g_s; trivial;
    destruct k; try apply lem_sub_pullback_wftype with T2;
    try apply lem_selfify_wf; try (apply WFKind; apply lem_selfify_wf);
    try rewrite <- lem_erase_subtype with g T1 T2; try apply lem_typing_hasftype; trivial. 
  Qed.
