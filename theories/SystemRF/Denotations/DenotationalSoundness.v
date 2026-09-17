Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.Strengthenings.
Require Import AutoProof.SystemRF.SystemRF.Semantics.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.PrimitivesFTyping.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsSubstitution.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SystemFLemmasWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.Typing.
Require Import AutoProof.SystemRF.SystemRF.LemmasWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.LemmasTyping.
Require Import AutoProof.SystemRF.SystemRF.LemmasWeakenWF.
Require Import AutoProof.SystemRF.SystemRF.SubstitutionLemmaWF.
Require Import AutoProof.SystemRF.SystemRF.LemmasWeakenTyp.
Require Import AutoProof.SystemRF.Denotations.ClosingSubstitutions.
Require Import AutoProof.SystemRF.Denotations.Denotations.
Require Import AutoProof.SystemRF.Denotations.BasicPropsCSubst.
Require Import AutoProof.SystemRF.Denotations.BasicPropsDenotes.
Require Import AutoProof.SystemRF.Denotations.BasicPropsSemantics.
Require Import AutoProof.SystemRF.Denotations.LemmasWidening.
Require Import AutoProof.SystemRF.Denotations.EnvironmentSubstitutions.
Require Import AutoProof.SystemRF.Denotations.MultiSubstitutionLemmas.
Require Import AutoProof.SystemRF.Denotations.LemmasDenotesEnv.
Require Import AutoProof.SystemRF.Denotations.PrimitivesDenotations.
Require Import AutoProof.SystemRF.Denotations.SelfifyDenotations.

Require Import Arith.
Require Import Lists.ListSet.

Lemma lem_denote_sound : ( forall (g:env) (e:expr) (t:type),
    Hastype g e t -> forall (th:csub),
        WFEnv g -> DenotesEnv g th 
            -> EvalsDenotes (ctsubst th t) (csubst th e) ) /\ ((
  forall (g:env) (t1 t2:type),
    Subtype g t1 t2 -> forall (k1:kind) (k2:kind) (th:csub),
        WFEnv g -> WFtype g t1 k1 -> WFtype g t2 k2 -> DenotesEnv g th
            -> (forall (v:expr), isValue v
                -> Denotes (ctsubst th t1) v -> Denotes (ctsubst th t2) v) ) /\ (
  forall (g:env) (ps qs:preds),
    Implies g ps qs -> DImplies g ps qs)).  
Proof. apply ( judgments_mutind3
  (fun (g:env) (e:expr) (t:type) (p_e_t : Hastype g e t) =>
    forall (th:csub), WFEnv g -> DenotesEnv g th 
        -> EvalsDenotes (ctsubst th t) (csubst th e) )
  (fun (g:env) (t1 t2:type) (p_t1_t2 : Subtype g t1 t2) =>
    forall (k1 k2:kind) (th:csub),
      WFEnv g -> WFtype g t1 k1 -> WFtype g t2 k2 -> DenotesEnv g th
        -> (forall (v:expr), isValue v
              -> Denotes (ctsubst th t1) v -> Denotes (ctsubst th t2) v) )
  (fun (g:env) (ps qs:preds) (p_ps_qs : Implies g ps qs) => DImplies g ps qs));
  intros.
  - (* T_BC *) rewrite lem_csubst_bc; rewrite lem_ctsubst_nofree;
    try apply lem_den_evalsdenotes; try apply lem_den_tybc;
    unfold tybc; simpl; reflexivity.
  - (* T_IC *) rewrite lem_csubst_ic; rewrite lem_ctsubst_nofree;
    try apply lem_den_evalsdenotes; try apply lem_den_tyic;
    unfold tyic; simpl; reflexivity.
  - (* T_Var *) unfold EvalsDenotes; exists (csubst th (FV x));
    repeat split; try apply Refl;
    try apply lem_denotes_ctsubst_self;
    try apply lem_denotations_selfify;
    try apply lem_den_hasftype;
    try apply lem_bound_in_denotesenv with g;
    try apply lem_csubst_value;
    try apply lem_ctsubst_wf with g;
    try apply lem_denotesenv_closed with g;
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g;
    try apply lem_denotesenv_uniqueC with g;
    try apply wfenv_unique;
    unfold isLC; simpl; trivial.
  - (* T_Prm *) rewrite lem_csubst_prim; unfold EvalsDenotes;
    exists (Prim c); repeat split; try apply Refl.
    apply lem_den_ty with g; apply H0.
  - (* T_Abs *) rename t into e; rename T1 into t_x;
    rename k into k_x; rename T2 into t;
    rewrite lem_csubst_lambda; rewrite lem_ctsubst_func;
    unfold EvalsDenotes; exists (Lambda (csubst th e));
    split; try split; try apply Refl;
    rewrite Denotes_equation_2; repeat split.
    * rewrite <- lem_csubst_lambda; rewrite <- lem_ctsubst_func;
      apply lem_csubst_hasftype with g;
      try apply lem_typing_hasftype; try apply T_Abs with k_x nms;
      try apply lem_erase_env_wfenv; try apply wfenv_unique; trivial.
    * intros; pose proof (fresh_var_not_elem nms g) as Hy; 
      set (y := fresh_var nms g) in Hy; destruct Hy as [Hy Hyg]; 
      apply H with y (CCons y v_x th) in Hy;
      try apply WFEBind with k_x; try apply DExt; trivial.
      unfold EvalsDenotes in Hy; destruct Hy as [v' Hy];
      destruct Hy; simpl in H5; destruct H5;
      rewrite <- lem_subFV_unbind in H5;
      rewrite <- lem_tsubFV_unbindT in H6;
      assert (Hastype g (Lambda e) (TFunc t_x t)) as Het
        by (apply T_Abs with k_x nms; trivial);
      apply lem_typing_wf in Het as Ht; try apply H0;
      apply lem_fv_subset_binds in Het; try apply H0;
      apply lem_free_subset_binds in Ht; 
      destruct Het; destruct Ht; simpl in H7; simpl in H9;
      assert (Subset (free t) (union (free t_x) (free t)))
        by apply subset_union_intro_r;
      pose proof (vbinds_subset g);
      try apply not_elem_subset with (vbinds g);
      try apply not_elem_subset with (binds g); trivial; 
      try apply subset_trans with (union (free t_x) (free t)); trivial.
      exists v'; repeat split; try apply H4;
      try apply AddStep with (csubst th (subBV v_x e)); 
      try apply H5; try rewrite lem_csubst_subBV;
      try rewrite lem_csubst_nofv with th v_x; try apply EAppAbs;
      try apply lem_den_nofv in H3 as Hvx; destruct Hvx;
      try rewrite lem_ctsubst_tsubBV in H6;
      try rewrite lem_csubst_nofv with th v_x in H6;
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g; 
      trivial.
  - (* T_App *) rename t1 into e; rename T1 into t_x;
    rename T2 into t; rename t2 into e';
    rewrite lem_csubst_app; rewrite lem_ctsubst_exis;
    unfold EvalsDenotes; apply H in H2 as den_thtxt_the;
    apply H0 in H2 as den_thtx_the'; try apply H1;
    unfold EvalsDenotes in den_thtx_the'; 
    unfold EvalsDenotes in den_thtxt_the; 
    destruct den_thtx_the' as [v_x Hvx]; destruct Hvx; 
    destruct H4 as [ev_the'_vx den_thtx_vx];
    destruct den_thtxt_the as [v Hv]; destruct Hv;
    destruct H5 as [ev_the_v den_thtxt_v];
    rewrite lem_ctsubst_func in den_thtxt_v;
    rewrite Denotes_equation_2 in den_thtxt_v;
    destruct den_thtxt_v as [_ Hv];
    destruct Hv as [p_v_thtxt den_func];
    apply den_func in den_thtx_vx as Hv'; try apply H3;
    destruct Hv' as [v' [Hv' [ev_vvx_v' den_v']]];
    exists v'; split; try split; try apply Hv';
    try apply lemma_evals_trans with (App v v_x);
    try apply lemma_app_both_many; trivial.
    rewrite Denotes_equation_3; repeat split;
    apply lem_den_hasftype in den_v' as p_v'_tvx;
    rewrite lem_erase_tsubBV in p_v'_tvx; simpl; trivial.
    exists v_x; split; try split; trivial.
  - (* T_AbsT *) rename t into e; rename T into t;
    rewrite lem_csubst_lambdaT; rewrite lem_ctsubst_poly;
    unfold EvalsDenotes; exists (LambdaT k (csubst th e));
    split; try split; try apply Refl;
    rewrite Denotes_equation_4; repeat split.
    * rewrite <- lem_csubst_lambdaT; rewrite <- lem_ctsubst_poly;
      apply lem_csubst_hasftype with g;
      try apply lem_typing_hasftype; try apply T_AbsT with nms;
      try apply lem_erase_env_wfenv; try apply wfenv_unique; trivial.
    * intros; pose proof (fresh_var_not_elem nms g) as Ha; 
      set (a := fresh_var nms g) in Ha; destruct Ha as [Ha Ha'];
      apply H with a (CConsT a t_a th) in Ha;
      try apply WFEBindT; try apply DExtT; trivial.
      unfold EvalsDenotes in Ha; destruct Ha as [v' [Hv' [ev_the_v' den_v']]];
      simpl in ev_the_v'; rewrite <- lem_subFTV_unbind_tv in ev_the_v';
      simpl in den_v'; rewrite <- lem_tsubFTV_unbind_tvT in den_v';
      assert (Hastype g (LambdaT k e) (TPoly k t)) as Het
        by (apply T_AbsT with nms; trivial);
      apply lem_typing_wf in Het as Ht; try apply H0;
      apply lem_fv_subset_binds in Het; try apply H0;
      apply lem_free_subset_binds in Ht; 
      destruct Het; destruct Ht; simpl in H5; simpl in H7;
      pose proof (tvbinds_subset g);
      try apply not_elem_subset with (tvbinds g);
      try apply not_elem_subset with (binds g); trivial.
      exists v'; repeat split; try apply Hv';
      try apply AddStep with (csubst th (subBTV t_a e)); 
      try apply ev_the_v'; try rewrite lem_csubst_subBTV;
      try rewrite lem_ctsubst_nofree with th t_a; try apply EAppTAbs;
      try apply lem_free_subset_binds in H3; simpl in H3; destruct H3;
      try rewrite lem_ctsubst_tsubBTV in den_v';
      try rewrite lem_ctsubst_nofree with th t_a in den_v';
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g; 
      try apply no_elem_empty; trivial. 
  - (* T_AppT *) rename t into e; rename T1 into s; rename T2 into t;
    rewrite lem_csubst_appT; rewrite lem_ctsubst_tsubBTV;
    unfold EvalsDenotes; apply H in H1 as den_thks_the;
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g; trivial;
    unfold EvalsDenotes in den_thks_the.
    destruct den_thks_the as [v' [Hv' [ev_the_v' den_v']]].
    rewrite lem_ctsubst_poly in den_v';
    rewrite Denotes_equation_4 in den_v';
    destruct den_v' as [_ [p_v'_ks den_func]].
    assert (WFtype Empty (ctsubst th t) k) as p_tht
      by (apply lem_ctsubst_wf with g; 
          try apply wfenv_unique; trivial);
    apply den_func in p_tht as Htht;
    try apply lem_ctsubst_isMono;
    try apply lem_ctsubst_noExists; 
    try apply lem_denotesenv_substitutable with g; trivial.
    destruct Htht as [v'' [Hv'' [ev_thet_v'' den_v'']]];
    exists v''; split; try split; try apply Hv'';
    try apply lemma_evals_trans with (AppT v' (ctsubst th t));
    try apply lemma_appT_many; 
    try apply lem_ctsubst_noExists;
    try apply lem_denotesenv_substitutable with g; trivial.
  - (* T_Let *) rename t1 into e_x; rename T1 into t_x;
    rename t2 into e; rename T2 into t;
    rewrite lem_csubst_let; 
    unfold EvalsDenotes in H; apply H in H2 as Hvx; try apply H1;
    destruct Hvx as [v_x [Hvx [ev_thex_vx den_thtx_vx]]].
    pose proof (fresh_var_not_elem nms g) as Hy; 
    set (y := fresh_var nms g) in Hy; destruct Hy as [Hy Hyg].
    apply H0 with y (CCons y v_x th) in Hy;
    apply lem_typing_wf in h as p_tx;
    try apply WFEBind with Star; try apply DExt; trivial.
    unfold EvalsDenotes in Hy; 
    destruct Hy as [v' [Hy [ev_thvxe_v' den_thvxt_v']]];
    simpl in ev_thvxe_v'; simpl in den_thvxt_v';
    rewrite <- lem_subFV_unbind in ev_thvxe_v';
    rewrite <- lem_tsubFV_unbindT in den_thvxt_v';
    try rewrite lem_ctsubst_tsubBV in den_thvxt_v';
    try rewrite lem_csubst_nofv in den_thvxt_v';
    try rewrite lem_tsubBV_lct in den_thvxt_v';
    try apply lem_ctsubst_isLCT;
    try apply lem_wftype_islct with g k;
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g;
    try apply lem_den_nofv in den_thtx_vx; destruct den_thtx_vx;
    assert (Hastype g (Let e_x e) t) as Het
      by (apply T_Let with t_x k nms; trivial);
    apply lem_fv_subset_binds in Het;
    apply lem_free_subset_binds in w as Ht; try apply H1;
    destruct Het; destruct Ht; simpl in H5;     
    assert (Subset (fv e) (union (fv e_x) (fv e)))
      by apply subset_union_intro_r;
    pose proof (vbinds_subset g);
    try apply not_elem_subset with (vbinds g);
    try apply not_elem_subset with (binds g); trivial;
    try apply subset_trans with (union (fv e_x) (fv e)); trivial.
    unfold EvalsDenotes;
    try exists v'; try repeat split; try assumption.         
    apply lemma_evals_trans with (Let v_x (csubst th e));
    try apply lemma_let_many; try apply ev_thex_vx.
    try apply AddStep with (csubst th (subBV v_x e));
    try apply ev_thvxe_v'; rewrite lem_csubst_subBV;
    try rewrite lem_csubst_nofv with th v_x; try apply ELetV;
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g; trivial.
  - (* T_Ann *) rename t into e; rename T into t;
    rewrite lem_csubst_annot; unfold EvalsDenotes;
    apply H in H1 as Hthe; try apply H0;
    unfold EvalsDenotes in Hthe; 
    destruct Hthe as [v [Hv [ev_the_v den_tht_v]]].
    exists v; repeat split; try assumption.
    apply lemma_evals_trans with (Annot v (ctsubst th t));
    try apply lemma_annot_many; try apply ev_the_v.
    apply lem_step_evals; apply EAnnV; apply Hv.
  - (* T_If *) rename t1 into e0; rename t2 into e1;
    rename t3 into e2; rename T into t;
    rewrite lem_csubst_if;
    try apply lem_typing_wf in h as p_ps; 
    try inversion p_ps; try subst g0 t0;
    apply H in H3 as Hv0; try apply H2;
    unfold EvalsDenotes in Hv0;
    destruct Hv0 as [v0 [Hv0 [ev_the0_v0 den_v0]]];
    rewrite lem_ctsubst_refn in den_v0; simpl; auto;
    rewrite Denotes_equation_1 in den_v0; simpl in den_v0;
    destruct den_v0 as [_ [p_v0_bl pev_psv0]].
    apply (lem_bool_values v0 Hv0) in p_v0_bl as Hb;
    destruct v0; simpl in Hb; try contradiction;
    destruct b.
    * (* True *) 
      pose proof (fresh_varE_not_elem nms g e1) as Hy; 
      set (y := fresh_varE nms g e1) in Hy; 
      destruct Hy as [Hye1 [_ [Hy Hyg]]];
      apply H0 with y (CCons y (Bool_constant true) th) in Hy as He1;
      try apply WFEBind with Base; 
      try apply lem_selfify_wf;
      try apply DExt;
      try apply lem_denotes_ctsubst_self;
      try rewrite lem_csubst_bc;
      try apply lem_denotations_selfify;
      try apply lem_ctsubst_wf with g;
      try rewrite lem_ctsubst_refn; simpl;
      try rewrite Denotes_equation_1;
      try apply FTBC;
      try apply lem_denotesenv_closed with g;
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g;
      try apply lem_denotesenv_uniqueC with g;
      try apply wfenv_unique; auto. 
      unfold EvalsDenotes; unfold EvalsDenotes in He1;
      destruct He1 as [v [Hv [ev_th'e1_v den_th't_v]]];
      exists v; repeat split; try apply Hv;
      try apply lemma_evals_trans 
          with (If (Bool_constant true) (csubst th e1) (csubst th e2));
      try apply lemma_if_many; try apply ev_the0_v0;
      try apply AddStep with (csubst th e1); try apply EIfT;
      simpl in ev_th'e1_v; rewrite lem_subFV_notin' in ev_th'e1_v;
      simpl in den_th't_v; rewrite lem_tsubFV_notin in den_th't_v;
      apply lem_free_subset_binds in w; destruct w; 
      pose proof vbinds_subset; trivial;
      apply not_elem_subset with (vbinds g);
      try apply not_elem_subset with (binds g); trivial.      
    * (* False *) 
      pose proof (fresh_varE_not_elem nms g e2) as Hy; 
      set (y := fresh_varE nms g e2) in Hy; 
      destruct Hy as [Hye2 [_ [Hy Hyg]]];
      apply H1 with y (CCons y (Bool_constant false) th) in Hy as He2;
      try apply WFEBind with Base; 
      try apply lem_selfify_wf; 
      try apply DExt; 
      try apply lem_denotes_ctsubst_self;
      try rewrite lem_csubst_bc;
      try apply lem_denotations_selfify;
      try apply lem_ctsubst_wf with g;
      try rewrite lem_ctsubst_refn; simpl;
      try rewrite Denotes_equation_1;
      try apply FTBC;
      try apply lem_denotesenv_closed with g;
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g;
      try apply lem_denotesenv_uniqueC with g;
      try apply wfenv_unique; auto. 
      unfold EvalsDenotes; unfold EvalsDenotes in He2;
      destruct He2 as [v [Hv [ev_th'e2_v den_th't_v]]];
      exists v; repeat split; try apply Hv;
      try apply lemma_evals_trans 
          with (If (Bool_constant false) (csubst th e1) (csubst th e2));
      try apply lemma_if_many; try apply ev_the0_v0;
      try apply AddStep with (csubst th e2); try apply EIfF;
      simpl in ev_th'e2_v; rewrite lem_subFV_notin' in ev_th'e2_v;
      simpl in den_th't_v; rewrite lem_tsubFV_notin in den_th't_v;
      apply lem_free_subset_binds in w; destruct w; 
      pose proof vbinds_subset; trivial;
      apply not_elem_subset with (vbinds g);
      try apply not_elem_subset with (binds g); trivial.
  - (* T_Sub *) rename s into hsub; rename t into e;
    rename T1 into s; rename T2 into t;
    unfold EvalsDenotes; apply H in H2 as H'; 
    try apply H1; try unfold EvalsDenotes in H';
    destruct H' as [v [Hv [ev_the_v den_ths_v]]];
    exists v; repeat split; try apply H0 with Star k;
    try apply lem_typing_wf with e; trivial.
  - (* SBase *) destruct b eqn:B.
    * (* TBool *) rewrite lem_ctsubst_refn; 
      try rewrite Denotes_equation_1;
      rewrite lem_ctsubst_refn in H5;
      try rewrite Denotes_equation_1 in H5; 
      simpl in H5; simpl; intuition.
      pose proof (fresh_var_not_elem nms g) as Hy; 
      set (y := fresh_var nms g) in Hy; destruct Hy as [Hy Hyg].
      apply H in Hy as IH; inversion IH.
      assert (Denotes (TRefn TBool PEmpty) v).
        rewrite Denotes_equation_1; unfold psubBV;
        simpl; repeat split; try apply PEEmp; trivial.
      assert (DenotesEnv (Cons y (TRefn TBool PEmpty) g) (CCons y v th)).
        apply DExt; try rewrite lem_ctsubst_refn; 
        try rewrite lem_cpsubst_pempty; simpl; auto. 
      apply lem_den_nofv in H12 as Hv; destruct Hv.
      assert (v = csubst th v)
        by (symmetry; apply lem_csubst_nofv; trivial).
      rewrite H16; rewrite <- lem_cpsubst_psubBV;
      try rewrite lem_psubFV_unbindP with y v p2;
      pose proof (H7 (CCons y v th) H13) as H'; 
      simpl in H'; try apply H';
      try rewrite <- lem_psubFV_unbindP;
      try rewrite lem_cpsubst_psubBV; try rewrite <- H16;
      apply lem_free_subset_binds in H1; simpl in H1;
      apply lem_free_subset_binds in H2; simpl in H2;
      destruct H1; destruct H2;
      try apply not_elem_subset with (vbinds g);
      try apply not_elem_subset with (binds g);
      pose proof vbinds_subset;
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g;
      trivial.
    * (* TInt *) rewrite lem_ctsubst_refn; 
      try rewrite Denotes_equation_1;
      rewrite lem_ctsubst_refn in H5;
      try rewrite Denotes_equation_1 in H5; 
      simpl in H5; simpl; intuition.
      pose proof (fresh_var_not_elem nms g) as Hy; 
      set (y := fresh_var nms g) in Hy; destruct Hy as [Hy Hyg].
      apply H in Hy as IH; inversion IH.
      assert (Denotes (TRefn TInt PEmpty) v).
        rewrite Denotes_equation_1; unfold psubBV;
        simpl; repeat split; try apply PEEmp; trivial.
      assert (DenotesEnv (Cons y (TRefn TInt PEmpty) g) (CCons y v th)).
        apply DExt; try rewrite lem_ctsubst_refn; 
        try rewrite lem_cpsubst_pempty; simpl; auto. 
      apply lem_den_nofv in H12 as Hv; destruct Hv.
      assert (v = csubst th v)
        by (symmetry; apply lem_csubst_nofv; trivial).
      rewrite H16; rewrite <- lem_cpsubst_psubBV;
      try rewrite lem_psubFV_unbindP with y v p2;
      pose proof (H7 (CCons y v th) H13) as H'; 
      simpl in H'; try apply H';
      try rewrite <- lem_psubFV_unbindP;
      try rewrite lem_cpsubst_psubBV; try rewrite <- H16;
      apply lem_free_subset_binds in H1; simpl in H1;
      apply lem_free_subset_binds in H2; simpl in H2;
      destruct H1; destruct H2;
      try apply not_elem_subset with (vbinds g);
      try apply not_elem_subset with (binds g);
      pose proof vbinds_subset;
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g;
      trivial.
    * (* BTV *) inversion H1; try simpl in H10; 
      try inversion H8; try simpl in H15;
      try inversion H6; try inversion H13; try contradiction.
    * (* FTV *)
      apply lem_free_subset_binds in H1 as Ha; simpl in Ha;
      destruct Ha as [Hfv1 Ha].
      assert (In a (tvbinds g))
        by (apply Ha; apply set_add_intro2; reflexivity).
      apply lem_tvbinds_denotesenv with a g th in H6 as H';
      try destruct H' as [t_a [Hta' [p_ta Hta]]];
      try rewrite lem_ctsubst_refn_tv with th a t_a p1 in H5;
      try rewrite lem_ctsubst_refn_tv with th a t_a p2;
      try apply lem_denotesenv_closed with g;
      try apply lem_denotesenv_substitutable with g;
      try apply lem_denotesenv_uniqueC with g; trivial.
      (* WTS: Denotes (push (cpsubst th p1) t_a) v
           -> Denotes (push (cpsubst th p2) t_a) v*)
      destruct t_a eqn:TA; simpl in Hta'; try contradiction;
      simpl; simpl in H5; try apply H5. 
      (* the case that remains: t_a is b0{ps}.
        WTS: Denotes (TRefn b0 (strengthen (cpsubst th p1) ps)) v
          -> Denotes (TRefn b0 (strengthen (cpsubst th p2) ps)) v*)
      rewrite Denotes_equation_1; rewrite Denotes_equation_1 in H5.
      simpl in H5; destruct H5 as [_ [p_v_b0 ev_p1]];
      simpl; repeat split; try assumption;
      rewrite lem_psubBV_strengthen;
      rewrite lem_psubBV_strengthen in ev_p1.
      apply lemma_strengthen_semantics;
      apply lemma_semantics_strengthen in ev_p1; 
      destruct ev_p1 as [ev_p1 ev_ps]; try apply ev_ps.

      pose proof (fresh_var_not_elem nms g) as Hy; 
      set (y := fresh_var nms g) in Hy; destruct Hy as [Hy Hyg].
      apply H in Hy as IH; inversion IH.

      assert (Denotes (TRefn b0 ps) v).
        rewrite Denotes_equation_1; unfold psubBV;
        simpl; repeat split; try apply PEEmp; trivial.
      assert (DenotesEnv (Cons y (TRefn (FTV a) PEmpty) g) (CCons y v th)).
        apply DExt; try rewrite lem_ctsubst_refn_tv with th a t_a PEmpty;
        try rewrite lem_cpsubst_pempty; subst t_a;
        try rewrite lem_push_empty;
        try apply lem_denotesenv_closed with g;
        try apply lem_denotesenv_substitutable with g;
        try apply lem_denotesenv_uniqueC with g;
        trivial.
      apply lem_fv_subset_bindsF in p_v_b0; destruct p_v_b0;
      simpl in H12; simpl in H13.
      assert (v = csubst th v)
        by (symmetry; apply lem_csubst_nofv; 
            apply no_elem_empty; trivial).
      rewrite H14; rewrite <- lem_cpsubst_psubBV;
      try rewrite lem_psubFV_unbindP with y v p2;
      pose proof (H5 (CCons y v th) H11) as H';
      simpl in H'; try apply H';
      try rewrite <- lem_psubFV_unbindP;
      try rewrite lem_cpsubst_psubBV; try rewrite <- H14;
      apply lem_free_subset_binds in H1; simpl in H1;
      apply lem_free_subset_binds in H2; simpl in H2;
      destruct H1; destruct H2;
      try apply not_elem_subset with (vbinds g);
      try apply not_elem_subset with (binds g);
      pose proof vbinds_subset;
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g;
      trivial.
  - (* SFunc *) inversion H2; try inversion H7;
    inversion H3; try inversion H14;
    rewrite lem_ctsubst_func;
    rewrite Denotes_equation_2; simpl;
    rewrite lem_ctsubst_func in H6;
    rewrite Denotes_equation_2 in H6; simpl in H6;
    destruct H6 as [_ [p_v_s1t1 den_func]]; repeat split;
    apply lem_erase_subtype in s as Hs;
    apply lem_erase_ctsubst with th s2 s1 in Hs;
    pose proof (fresh_varT_not_elem (union nms (union nms0 nms1)) 
                                    g (TFunc t1 t2)) as Hy; 
    set (y := fresh_varT (union nms (union nms0 nms1)) g (TFunc t1 t2)) 
        in Hy; simpl in Hy;
    destruct Hy as [Hfv [Hftv [Hy Hyg]]];
    apply not_elem_union_elim in Hy as [Hy Hy0];
    apply not_elem_union_elim in Hy0 as [Hy0 Hy1];
    apply not_elem_union_elim in Hfv; destruct Hfv;
    apply s0 in Hy as p_t1_t2;
    apply lem_erase_subtype in p_t1_t2;
    repeat rewrite lem_erase_unbind in p_t1_t2;
    apply lem_erase_ctsubst with th t1 t2 in p_t1_t2 as Ht;
    try rewrite Hs; try rewrite <- Ht;
    try apply lem_denotesenv_substitutable with g; trivial.
    intros; apply lem_den_nofv in H23 as Hvx; destruct Hvx;
    apply H with k_x0 k_x th v_x in H23 as H''; trivial.
    apply den_func in H''; try apply H22. 
    destruct H'' as [v' [Hv' [ev_vvx_v' den_v']]];
    exists v'; repeat split; trivial.
    assert (Denotes (ctsubst (CCons y v_x th) (unbindT y t1)) v' 
              -> Denotes (ctsubst (CCons y v_x th) (unbindT y t2)) v') as Hden.
        apply H0 with k k0; try apply WFEBind with k_x0;
        try apply H19; try apply lem_narrow_wf_top with s1; 
        try apply H12; try apply DExt; 
        try apply wfenv_unique; trivial.
    simpl in Hden; rewrite <- lem_tsubFV_unbindT in Hden;
    rewrite <- lem_tsubFV_unbindT in Hden;
    try rewrite lem_ctsubst_tsubBV in Hden;
    try rewrite lem_ctsubst_tsubBV in Hden;
    try rewrite lem_csubst_nofv in Hden; 
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g; trivial;
    apply Hden; apply den_v'.
  - (* SWtin *) rewrite lem_ctsubst_exis;
    rewrite Denotes_equation_3; simpl; repeat split;
    apply lem_erase_subtype in s as Htt';
    rewrite lem_erase_tsubBV in Htt';
    apply lem_erase_ctsubst with th t t' in Htt';
    try rewrite <- Htt'; try apply lem_den_hasftype;
    try apply lem_denotesenv_substitutable with g; trivial.

    unfold EvalsDenotes in H; 
    destruct H with th as [vx' [Hvx' [ev_thvx den_vx']]];
    trivial; apply lem_evals_val_det
      with (csubst th v_x) (csubst th v_x) vx' in ev_thvx;
    try apply Refl; try apply lem_csubst_value; 
    try apply lem_denotesenv_substitutable with g; trivial.
    subst vx'; exists (csubst th v_x); repeat split;
    try apply lem_csubst_value;
    try rewrite <- lem_ctsubst_tsubBV; 
    try apply H0 with k1 k2;
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g; trivial.

    inversion H3; try inversion H7;
    pose proof (fresh_varT_not_elem nms g t') as Hy;
    set (y := fresh_varT nms g t') in Hy; destruct Hy as [Ht [Ht' [Hy Hyg]]];
    apply H12 in Hy || apply H16 in Hy;
    rewrite lem_tsubFV_unbindT with y v_x t';
    try apply lem_subst_wf_top with t_x;
    try apply lem_typing_hasftype;
    try apply WFKind;
    try apply wfenv_unique; trivial. 
  - (* SBind *) rewrite lem_ctsubst_exis in H5;
    rewrite Denotes_equation_3 in H5; simpl in H5;
    destruct H5 as [_ [p_v_tht ex_vx]];
    destruct ex_vx as [v_x [Hvx [den_thtx_vx dentht_v]]].
    inversion H1; try inversion H5;
    pose proof (fresh_varT_not_elem (union nms nms0) g 
                                    (TExists t t')) as Hy;
    set (y := fresh_varT (union nms nms0) g (TExists t t')) in Hy;
    simpl in Hy; destruct Hy as [Ht [_ [Hy Hyg]]];
    apply not_elem_union_elim in Ht; destruct Ht as [Ht Ht'];
    apply not_elem_union_elim in Hy; destruct Hy as [Hy Hy0];
    assert (ctsubst th t' = ctsubst (CCons y v_x th) t')
      by (simpl; try rewrite lem_tsubFV_notin; trivial);
    rewrite H12 || rewrite H15; apply H with y k1 k2;
    try apply WFEBind with k_x;
    try apply H10; try rewrite <- H8; 
    try apply WFKind; try apply H14;
    try apply DExt; simpl;
    try rewrite <- lem_tsubFV_unbindT;
    try apply lem_weaken_wf_top; 
    try rewrite lem_ctsubst_tsubBV; 
    try rewrite lem_csubst_nofv;
    apply lem_den_nofv in den_thtx_vx as Hfr; destruct Hfr;
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g; trivial. 
  - (* SPoly *) inversion H1; try inversion H6;
    inversion H2; try inversion H12;
    rewrite lem_ctsubst_poly;
    rewrite Denotes_equation_4; simpl;
    rewrite lem_ctsubst_poly in H5;
    rewrite Denotes_equation_4 in H5; simpl in H5;
    destruct H5 as [_ [p_v_kt1 den_func]]; repeat split;
    pose proof (fresh_varT_not_elem (union nms (union nms0 nms1)) 
                                    g (TFunc t1 t2)) as Ha;
    set (a := fresh_varT (union nms (union nms0 nms1)) 
                           g (TFunc t1 t2)) 
        in Ha; simpl in Ha;
    destruct Ha as [_ [Hftv [Ha Hg]]];
    apply not_elem_union_elim in Ha as [Ha Ha0];
    apply not_elem_union_elim in Ha0 as [Ha0 Ha1];
    apply not_elem_union_elim in Hftv; destruct Hftv;
    apply s in Ha as p_t1_t2;
    apply lem_erase_subtype in p_t1_t2;
    repeat rewrite lem_erase_unbind_tvT in p_t1_t2;
    apply lem_openFT_at_equals in p_t1_t2;
    pose proof (lem_erase_freeTV t1);
    pose proof (lem_erase_freeTV t2);
    try (apply not_elem_subset with (freeTV t1); apply H5 || apply H19);
    try (apply not_elem_subset with (freeTV t2); apply H18 || apply H20);
    try apply lem_erase_ctsubst with th t1 t2 in p_t1_t2 as Ht;
    try rewrite <- Ht;
    try apply lem_denotesenv_substitutable with g; trivial.

    intros; subst k1 k2 g0 k0 t g1 k3 t0;
    apply den_func in H22 as H''; try assumption;
    destruct H'' as [v' [Hv' [ev_vta_v' den_v']]];
    exists v'; repeat split; trivial.

    assert (Denotes (ctsubst (CConsT a t_a th) (unbind_tvT a t1)) v' 
              -> Denotes (ctsubst (CConsT a t_a th) (unbind_tvT a t2)) v') as Hden.
        apply H with k_t k_t0; try apply WFEBindT;
        try apply H10; try apply H16; 
        try apply DExtT; trivial.
    simpl in Hden; rewrite <- lem_tsubFTV_unbind_tvT in Hden;
    rewrite <- lem_tsubFTV_unbind_tvT in Hden;
    try rewrite lem_ctsubst_tsubBTV in Hden;
    try rewrite lem_ctsubst_tsubBTV in Hden;
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g; trivial;
    try rewrite lem_ctsubst_nofree in Hden;
    try apply lem_free_subset_binds in H22; 
    simpl in H22; destruct H22;
    try apply no_elem_empty; trivial.
    apply Hden; apply den_v'.
  - (* IRefl *) apply DImp; trivial.
  - (* ITrans *) apply DImp; inversion H; inversion H0.
    intros; apply H5; try apply H1; apply H9 || apply H10.
  - (* IFaith *) apply DImp; intros;
    rewrite lem_cpsubst_pempty; apply PEEmp.
  - (* IConj *) apply DImp; intros;
    rewrite lem_cpsubst_strengthen;
    apply lemma_strengthen_semantics;
    inversion H; inversion H0;
    apply H3 || apply H7; trivial.

  - (* ICons1 *) apply DImp; intros;
    rewrite lem_cpsubst_pcons;
    rewrite lem_cpsubst_pcons in H0;
    rewrite lem_cpsubst_pempty;
    inversion H0; apply PECons; try apply PEEmp; trivial.
  - (* ICons2 *) apply DImp; intros;
    rewrite lem_cpsubst_pcons in H0;
    inversion H0; apply H4.
  - (* IRepeat *) apply DImp; intro th;
    repeat rewrite lem_cpsubst_pcons; intros;
    inversion H0; repeat apply PECons; trivial.
  - (* INarrow *) apply DImp; intros th Hden.
    inversion H0; apply H1.
    apply lem_widen_denotes with s_x; trivial; 
    intros; apply H with k_sx k_tx; trivial.

  - (* IWeak *) apply DImp; intros th Hden Hps;
    inversion H; 
    rewrite lem_remove_cpsubst with th x ps in Hps;
    try rewrite lem_remove_cpsubst with th x qs;
    try apply H0;
    try apply lem_remove_var_denote_env with t_x;
    try rewrite <- lem_binds_env_th 
      with (concatE (Cons x t_x g) g') th;
    try apply lem_binds_concat;
    try apply set_union_intro1; 
    try apply set_add_intro2;
    try apply lem_denotesenv_closed 
      with (concatE (Cons x t_x g) g');
    try apply lem_denotesenv_substitutable 
      with (concatE (Cons x t_x g) g');
    try apply lem_denotesenv_uniqueC
      with (concatE (Cons x t_x g) g');  auto.
  - (* IWeakTV *) apply DImp; intros th Hden Hps;
    inversion H;
    rewrite lem_remove_cpsubst with th a ps in Hps;
    try rewrite lem_remove_cpsubst with th a qs;
    try apply H0;
    try apply lem_remove_tvar_denote_env with k_a;
    try rewrite <- lem_binds_env_th 
      with (concatE (ConsT a k_a g) g') th;
    try apply lem_binds_concat;
    try apply set_union_intro1; 
    try apply set_add_intro2;
    try apply lem_denotesenv_closed 
      with (concatE (ConsT a k_a g) g');
    try apply lem_denotesenv_substitutable 
      with (concatE (ConsT a k_a g) g');
    try apply lem_denotesenv_uniqueC
      with (concatE (ConsT a k_a g) g');  auto.
  - (* ISub *) apply DImp; intros th Hden Hps;
    inversion H0; 
    apply lem_add_var_denote_env with g g' x v_x t_x th 
      in Hden as Hth';
    try destruct Hth' as [th' [den_env_th' [Hcs [Hcs' Hcs'']]]];
    try pose proof (H1 _ den_env_th') as ev_func;
    repeat rewrite Hcs'' in ev_func; try apply ev_func; auto.
    apply lem_extend_denotes with g (esubFV x v_x g');
    try apply lem_typing_wf with v_x; intros;
    try apply lem_evalsdenotes_value; try apply H;
    try apply lem_csubst_value; 
    try apply lem_denotesenv_substitutable with g; auto.
  - (* ISubTV *) apply DImp; intros th Hden Hps.
    inversion H;  subst g0 ps0 qs0.
    apply lem_add_tvar_denote_env with g g' a t_a k_a th 
      in Hden as Hth';
    try destruct Hth' as [th' [den_env_th' [Hcs [Hcs' Hcs'']]]];
    try pose proof (H0 _ den_env_th') as ev_func;
    repeat rewrite Hcs'' in ev_func; try apply ev_func; auto.
  
  - (* IEqlSub *) apply DImp; intros th den_g_th.
    repeat rewrite lem_cpsubst_pcons;
    rewrite lem_cpsubst_pempty;
    repeat rewrite lem_csubst_app;
    repeat rewrite lem_csubst_appT;
    rewrite lem_csubst_prim; intros;
    inversion H; inversion H2; subst ps0 e3.
    apply PECons; try apply PEEmp.
    apply AddStep with e2; try apply H5.
    (* investigate e2 *)
    inversion H4;  simpl in H8;  try contradiction.
    inversion H9;  simpl in H12; try contradiction.
    inversion H13; try apply lem_value_stuck in H18;
                   try simpl in H18; try contradiction. 
    apply EApp1; apply EApp1; 
    assert (isCompatT Eql (ctsubst th (TRefn b ps))) as pf'
      by (inversion pf; 
          (apply isCptT_EqlB; rewrite <- H18) || 
              (apply isCptT_EqlZ; rewrite <- H18);
          apply lem_erase_ctsubst;
          try apply lem_denotesenv_substitutable with g; auto). 
    pose proof (deltaT_exchange_type Eql (ctsubst th (TRefn b PEmpty)) 
                                         (ctsubst th (TRefn b ps)) pf pf');
    rewrite H18; try apply lem_erase_ctsubst; 
    try apply EPrimT; try apply lem_ctsubst_noExists;
    try apply lem_denotesenv_substitutable with g; simpl; trivial.
  - (* IStren *) apply DImp; intros; inversion H.
    rewrite lem_cpsubst_strengthen;
    rewrite lem_cpsubst_strengthen in H1.
    apply lemma_strengthen_semantics;
    apply lemma_semantics_strengthen in H1;
    destruct H1; try apply H6; apply H2; try apply H1.
    inversion H0; apply DExt; try assumption.
    subst th; simpl in H6; rewrite <- lem_psubFV_unbindP in H6;
    try rewrite lem_cpsubst_psubBV in H6;
    try rewrite lem_csubst_nofv in H6;
    apply lem_den_nofv in H13 as Hfv; destruct Hfv;
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g; 
    auto; destruct b' eqn:B;
    try ( assert (isConcreteBasic b' \/ isBTV b') 
            by (subst b'; simpl; auto);
          rewrite lem_ctsubst_refn in H13;
          try rewrite lem_ctsubst_refn;
          try rewrite Denotes_equation_1 in H13;
          try rewrite Denotes_equation_1;
          simpl; simpl in H13; intuition ).
    * (* FTV a *) 
      pose proof (set_In_dec Nat.eq_dec a (tvbinds g));
      destruct H15. (* a \in tvbinds g *)
      apply lem_tvbinds_denotesenv with a g th0 in s;
      try destruct s as [t_a [Hta [p_ta_s Ha]]];
      try rewrite lem_ctsubst_refn_tv with th0 a t_a qs;
      try rewrite lem_ctsubst_refn_tv with th0 a t_a PEmpty in H13;
      try rewrite lem_cpsubst_pempty in H13; 
      try rewrite lem_push_empty in H13; 
      try apply lem_denotesenv_closed with g;
      try apply lem_denotesenv_loc_closed with g;
      try apply lem_denotesenv_substitutable with g; 
      try apply lem_denotesenv_uniqueC with g; auto.
      destruct t_a; simpl in Hta; try contradiction; simpl;
      try apply H13; rewrite Denotes_equation_1 in H13;
      rewrite Denotes_equation_1; intuition;
      rewrite lem_psubBV_strengthen;
      apply lemma_strengthen_semantics; trivial.
      (* a \not\in tvbinds g *)
      rewrite lem_ctsubst_refn_tv_notin';
      try rewrite lem_ctsubst_refn_tv_notin' in H13;
      try rewrite <- lem_tvbinds_env_th with g th0; trivial.
      rewrite Denotes_equation_1 in H13;
      rewrite Denotes_equation_1; intuition.
  - (* IEvals  *) apply DImp; intros;
    rewrite lem_cpsubst_pcons in H0;
    rewrite lem_cpsubst_pcons; inversion H0;
    apply PECons;
    apply lem_csubst_evals with th p p' in m;
    try apply lem_decompose_evals with (csubst th p);
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g; 
    simpl; auto.
  - (* IEvals2 *) apply DImp; intros;
    rewrite lem_cpsubst_pcons in H0;
    rewrite lem_cpsubst_pcons; inversion H0;
    apply PECons;
    apply lem_csubst_evals with th p' p in m;
    try apply lemma_evals_trans with (csubst th p);
    try apply lem_denotesenv_loc_closed with g;
    try apply lem_denotesenv_substitutable with g; auto.
  Qed.
