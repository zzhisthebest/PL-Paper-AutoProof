Require Import Arith.

Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions. 
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.LocalClosure.
Require Import AutoProof.SystemRF.SystemRF.SystemFWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.

(*------------------------------------------------------------------------------------------
-- | LEMMAS relating REFINEMENT ERASURE and WELL FORMEDNESS notions
------------------------------------------------------------------------------------------*)

Lemma lem_strengthen_wfft' : forall (g'xg : fenv) (t : ftype) (k : kind),
    WFFT g'xg t k -> ( forall (g:fenv) (x:var_name) (t_x:ftype) (g':fenv),
        g'xg = concatF (FCons x t_x g) g' 
                           -> intersect (bindsF g) (bindsF g') = empty
                           -> ~ (in_envF x g) -> ~ (in_envF x g') 
                           -> WFFT (concatF g g') t k ).
Proof. apply ( WFFT_ind 
  (fun (g'xg : fenv) (t : ftype) (k : kind) => 
      forall (g:fenv) (x:var_name) (t_x:ftype) (g':fenv),
          g'xg = concatF (FCons x t_x g) g' 
                         -> intersect (bindsF g) (bindsF g') = empty
                         -> ~ (in_envF x g) -> ~ (in_envF x g') 
                         -> WFFT (concatF g g') t k  ));
  intro env; intros; subst env.
  - apply WFFTBasic; assumption.
  - (* WFFTFV *) apply WFFTFV;
    apply lem_tvboundinF_strengthen in H; assumption.
  - (* WFFTFunc *) apply WFFTFunc with k1 k2; 
    apply H0 with x t_x || apply H2 with x t_x; intuition.
  - (* WFFTPoly *) apply WFFTPoly with k_t (names_add x (union nms (bindsF (concatF g g'))));
    intros; apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H5; destruct H5;
    apply not_elem_concatF_elim in H6; destruct H6;
    assert (FConsT a k (concatF g g') = concatF g (FConsT a k g')) by reflexivity;
    rewrite H8; apply H0 with x t_x; unfold in_envF; simpl;
    try (apply not_elem_names_add_intro); try split; 
    try (apply intersect_names_add_intro_r);
    try assumption; intuition.
  - (* WFFTKind *) apply WFFTKind; apply H0 with x t_x; intuition.
  Qed.

Lemma lem_strengthen_wfft : 
  forall (g:fenv) (x:var_name) (t_x:ftype) (g':fenv) (t:ftype) (k:kind),
    WFFT (concatF (FCons x t_x g) g') t k -> intersect (bindsF g) (bindsF g') = empty
                                          -> ~ (in_envF x g) -> ~ (in_envF x g') 
                                          -> WFFT (concatF g g') t k.
Proof. intros; apply lem_strengthen_wfft' with (concatF (FCons x t_x g) g') x t_x;
  intuition. Qed.

Lemma lem_strengthen_hasftype' : forall (g'xg : fenv) (e : expr) (t : ftype),
    HasFtype g'xg e t -> ( forall (g:fenv) (x:var_name) (t_x:ftype) (g':fenv),
        g'xg = concatF (FCons x t_x g) g' 
                           -> intersect (bindsF g) (bindsF g') = empty
                           -> ~ (in_envF x g) -> ~ (in_envF x g') 
                           -> ~ In x (fv e)
                           -> HasFtype (concatF g g') e t ).
Proof. apply ( HasFtype_ind
  (fun (g'xg : fenv) (e : expr) (t : ftype) => 
      forall (g:fenv) (x:var_name) (t_x:ftype) (g':fenv),
          g'xg = concatF (FCons x t_x g) g' 
                         -> intersect (bindsF g) (bindsF g') = empty
                         -> ~ (in_envF x g) -> ~ (in_envF x g') 
                         -> ~ In x (fv e)
                         -> HasFtype (concatF g g') e t ));
  intro env; intros; subst env.
  - (* FTBC *) apply FTBC.
  - (* FTIC *) apply FTIC.
  - (* FTVar *) apply FTVar; apply lem_boundinF_concatF in H;
    simpl in H; rewrite or_assoc in H; destruct H.
    * (* x = x0 *) destruct H; subst x0; simpl in H4; intuition.
    * (* otherw *) apply lem_boundinF_concatF in H; apply H.
  - (* FTPrm *) apply FTPrm.
  - (* FTAbs *) apply FTAbs with k (names_add x (union nms (bindsF (concatF g g'))));
    try apply lem_strengthen_wfft with x t_x; try assumption; intros;
    apply not_elem_names_add_elim in H2; destruct H2;
    apply not_elem_union_elim in H7; destruct H7;
    apply not_elem_concatF_elim in H8; destruct H8;
    assert (FCons y b (concatF g g') = concatF g (FCons y b g')) by reflexivity;
    rewrite H10; apply H1 with x t_x; unfold in_envF; simpl;
    try (apply not_elem_names_add_intro); try split; trivial;
    try apply not_elem_subset with (names_add y (fv e));
    try (apply not_elem_names_add_intro); try split; 
    try (apply intersect_names_add_intro_r); try apply fv_unbind_elim; intuition.
  - (* FTApp *) apply FTApp with b; apply H0 with x t_x || apply H2 with x t_x;
    simpl in H7; apply not_elem_union_elim in H7; destruct H7; trivial.
  - (* FTAbsT *) apply FTAbsT with (names_add x (union nms (bindsF (concatF g g'))));
    intros; apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H6; destruct H6;
    apply not_elem_concatF_elim in H7; destruct H7;
    assert (FConsT a' k (concatF g g') = concatF g (FConsT a' k g')) by reflexivity;
    rewrite H9; apply H0 with x t_x; unfold in_envF; simpl;
    try (apply not_elem_names_add_intro); try split; trivial;
    try apply not_elem_subset with (names_add a' (fv e));
    try (apply not_elem_names_add_intro);
    try (apply intersect_names_add_intro_r); try apply fv_unbind_tv_elim; intuition.
  - (* FTAppT *) apply FTAppT with k; try apply H0 with x t_x;
    try apply lem_strengthen_wfft with x t_x; simpl in H11;
    apply not_elem_union_elim in H11; destruct H11;
    pose proof (lem_vbinds_cons_concatF g g' x t_x) as Hv; destruct Hv as [Hv Hvx];
    pose proof (lem_tvbinds_cons_concatF g g' x t_x) as Htv; destruct Htv as [Htv Htvx];
    trivial.
      * apply subset_add_elim with x; 
        try apply subset_trans with (vbindsF (concatF (FCons x t_x g) g')); trivial.
      * apply subset_trans with (tvbindsF (concatF (FCons x t_x g) g')); trivial.
  - (* FTLet *) apply FTLet with b (names_add x (union nms (bindsF (concatF g g'))));
    try apply H0 with x t_x; simpl in H7; 
    apply not_elem_union_elim in H7; destruct H7; trivial; intros;
    apply not_elem_names_add_elim in H8; destruct H8;
    apply not_elem_union_elim in H9; destruct H9;
    apply not_elem_concatF_elim in H10; destruct H10;
    assert (FCons y b (concatF g g') = concatF g (FCons y b g')) by reflexivity;
    rewrite H12; apply H2 with x t_x; unfold in_envF; simpl;
    try (apply not_elem_names_add_intro); try split; trivial;
    try apply not_elem_subset with (names_add y (fv e));
    try (apply not_elem_names_add_intro); try split; 
    try (apply intersect_names_add_intro_r); try apply fv_unbind_elim; intuition.
  - (* FTAnn *) apply FTAnn; try apply H4 with x t_x;
    simpl in H9; apply not_elem_union_elim in H9; destruct H9;
    pose proof (lem_vbinds_cons_concatF g g' x t_x) as Hv; destruct Hv as [Hv Hvx];
    pose proof (lem_tvbinds_cons_concatF g g' x t_x) as Htv; destruct Htv as [Htv Htvx];
    trivial.
    * apply subset_add_elim with x; 
      try apply subset_trans with (vbindsF (concatF (FCons x t_x g) g')); trivial.
    * apply subset_trans with (tvbindsF (concatF (FCons x t_x g) g')); trivial.
  - (* FTIf  *) apply FTIf; 
    apply H0 with x t_x || apply H2 with x t_x || apply H4 with x t_x;
    simpl in H9; apply not_elem_union_elim in H9; destruct H9;
    apply not_elem_union_elim in H9; destruct H9; trivial.
  Qed.

Lemma lem_strengthen_hasftype : 
  forall (g:fenv) (x:var_name) (t_x:ftype) (g':fenv) (e:expr) (t:ftype),
    HasFtype (concatF (FCons x t_x g) g') e t 
                            -> intersect (bindsF g) (bindsF g') = empty
                            -> ~ (in_envF x g) -> ~ (in_envF x g') 
                            -> ~ In x (fv e)
                            -> HasFtype (concatF g g') e t.
Proof. intros; apply lem_strengthen_hasftype' with (concatF (FCons x t_x g) g') x t_x;
  intuition. Qed.

Lemma lem_erase_wftype : forall (g:env) (t:type) (k:kind),
    WFtype g t k -> WFFT (erase_env g) (erase t) k.
Proof. intros g t k p_g_t ; induction p_g_t; simpl.
  - (* WFBase *) apply WFFTBasic; assumption.
  - (* WFRefn *) simpl in IHp_g_t; apply IHp_g_t; assumption.
  - (* WFVar *) apply WFFTFV; apply tvboundin_erase_env; assumption.
  - (* WFFunc *) apply WFFTFunc with k_x k; try apply IHp_g_t;
    assert (erase_env g = concatF (erase_env g) FEmpty) by reflexivity; rewrite H1;
    apply lem_strengthen_wfft with (fresh_varF nms (erase_env g)) (erase t_x);
    simpl; simpl in H0;
    try rewrite <- lem_erase_unbind with (fresh_varF nms (erase_env g)) t;
    try apply H0; pose proof (fresh_varF_not_elem nms (erase_env g));
    destruct H2; try apply intersect_empty_r; intuition.
  - (* WFExis *) assert (erase_env g = concatF (erase_env g) FEmpty) by reflexivity; rewrite H1;
    apply lem_strengthen_wfft with (fresh_varF nms (erase_env g)) (erase t_x);
    simpl; simpl in H0;
    try rewrite <- lem_erase_unbind with (fresh_varF nms (erase_env g)) t;
    try apply H0; pose proof (fresh_varF_not_elem nms (erase_env g));
    destruct H2; try apply intersect_empty_r; intuition.
  - (* WFPoly *) apply WFFTPoly with k_t (union nms (bindsF (erase_env g))); intros;
    simpl in H0; rewrite <-lem_erase_unbind_tvT; apply H0;
    apply not_elem_union_elim in H1; destruct H1; assumption.
  - (* WFKind *) apply WFFTKind; apply IHp_g_t; apply H. 
  Qed.

Lemma lem_erase_env_wfenv : forall (g:env), WFEnv g -> WFFE (erase_env g).
Proof. induction g; intro p_wf_g; simpl.
  - apply WFFEmpty.
  - inversion p_wf_g. apply WFFBind with k; unfold in_envF; 
    try rewrite <- binds_erase_env; try apply lem_erase_wftype; 
    try apply wfenv_unique; intuition.
  - inversion p_wf_g; apply WFFBindT; unfold in_envF;
    try rewrite <- binds_erase_env; intuition. 
  Qed.

Lemma lem_truncate_wfenv : forall (g g':env),(* -> { g':env | Set_emp (Set_cap (binds g) (binds g')) }*)
    WFEnv (concatE g g') -> WFEnv g.
Proof. intro g; induction g'; intro p_wf_g'g.
  - simpl in p_wf_g'g; assumption.
  - simpl in p_wf_g'g; inversion p_wf_g'g; intuition.
  - simpl in p_wf_g'g; inversion p_wf_g'g; intuition.
  Qed.

(*-------------------------------------------------------------------------------------------
-- | TECHNICAL LEMMAS relating to FREE VARIABLES and WELL FORMEDNESS judgments
-------------------------------------------------------------------------------------------*)

Lemma lem_free_subset_binds : forall (g:env) (t:type) (k:kind),
    WFtype g t k -> Subset (free t) (vbinds g) /\ Subset (freeTV t) (tvbinds g).
Proof. intros g t k p_g_t; induction p_g_t. 
  - (* WFBase *) destruct b; split; try apply subset_empty_l; simpl in H; try contradiction.
  - (* WFRefn *) 
    pose proof (fresh_varT_not_elem nms g (TRefn b ps)) as Hfv.
    set (z := (fresh_varT nms g (TRefn b ps))) in Hfv;
    destruct Hfv as [Hfv Hftv]; destruct Hftv as [Hftv Hnms];
    destruct Hnms as [Hnms Hg]; simpl in Hfv; simpl in Hftv;
    pose proof (lem_fvp_subset_bindsF (FCons z (FTBasic b) (erase_env g))
                                      (unbindP z ps) (H0 z Hnms)); 
    destruct H1 as [HfvP HftvP]; simpl in HfvP; simpl in HftvP; split.
    * (* free *) rewrite vbinds_erase_env; destruct b eqn:B; simpl;
      apply subset_add_elim with z; try apply Hfv;
      apply subset_trans with (fvP (unbindP z ps));
      try apply fv_unbind_intro; apply HfvP.
    * (* freeTV *) rewrite tvbinds_erase_env; destruct b eqn:B; simpl;
      try ( apply subset_trans with (ftvP (unbindP z ps));
            try apply ftv_unbind_intro; apply HftvP);
      apply subset_trans with (names_add a (ftvP (unbindP z ps)));
      try apply subset_add_both_intro; try apply ftv_unbind_intro;
      apply subset_add_intro_l; simpl in IHp_g_t; destruct IHp_g_t as [IH1 IH2];
      rewrite tvbinds_erase_env in IH2; try apply IH2; try apply elem_sing; intuition. 
  - (* WFVar *) simpl; apply lem_tvboundin_inenv in H; split;
    try apply subset_empty_l; apply subset_sing_l; apply H. 
  - (* WFFunc *) simpl; split; apply subset_union_intro_l; try apply IHp_g_t;
    pose proof (fresh_varT_not_elem nms g t) as Hfv;
    set (z := (fresh_varT nms g t)) in Hfv;
    destruct Hfv as [Hfv Hftv]; destruct Hftv as [Hftv Hnms];
    destruct Hnms as [Hnms Hg]; simpl in Hfv; simpl in Hftv;
    apply (H0 z) in Hnms; simpl in Hnms; destruct Hnms.
    * apply subset_add_elim with z; try apply Hfv; 
      apply subset_trans with (free (unbindT z t)); try apply fv_unbind_intro; apply H1.
    * apply subset_trans with (freeTV (unbindT z t)); try apply ftv_unbind_intro; apply H2.
  - (* WFExis *) simpl; split; apply subset_union_intro_l; try apply IHp_g_t;
    pose proof (fresh_varT_not_elem nms g t) as Hfv;
    set (z := (fresh_varT nms g t)) in Hfv;
    destruct Hfv as [Hfv Hftv]; destruct Hftv as [Hftv Hnms];
    destruct Hnms as [Hnms Hg]; simpl in Hfv; simpl in Hftv;
    apply (H0 z) in Hnms; simpl in Hnms; destruct Hnms.
    * apply subset_add_elim with z; try apply Hfv; 
      apply subset_trans with (free (unbindT z t)); try apply fv_unbind_intro; apply H1.
    * apply subset_trans with (freeTV (unbindT z t)); try apply ftv_unbind_intro; apply H2.
  - (* WFPoly *) simpl; split; simpl in H0;
    pose proof (fresh_varT_not_elem nms g t) as Hfv;
    set (a := (fresh_varT nms g t)) in Hfv;
    destruct Hfv as [Hfv Hftv]; destruct Hftv as [Hftv Hnms];
    destruct Hnms as [Hnms Hg]; apply (H0 a) in Hnms; destruct Hnms.
    * apply subset_trans with (free (unbind_tvT a t)); try apply fv_unbind_tv_intro; apply H1.
    * apply subset_add_elim with a; try apply Hftv; 
      apply subset_trans with (freeTV (unbind_tvT a t)); try apply ftv_unbind_tv_intro; apply H2.
  - (* WFKind *) apply IHp_g_t. 
  Qed.
  
Lemma lem_free_bound_in_env : forall (g:env) (t:type) (k:kind) (x:var_name),
    WFtype g t k -> ~ in_env x g -> ~ In x (free t) /\ ~ In x (freeTV t).
Proof. unfold in_env; intros; apply lem_free_subset_binds in H; destruct H; split; 
  pose proof (vbinds_subset g); pose proof (tvbinds_subset g); intuition. Qed. 

(*-------------------------------------------------------------------------------------------
-- | TECHNICAL LEMMAS relating to the abscence of dangling BOUND VARIABLES without a binder
-------------------------------------------------------------------------------------------*)

Lemma lem_ftyp_islc : forall (g:fenv) (e:expr) (t:ftype),
    HasFtype g e t -> isLC e.
Proof. intros; induction H; unfold isLC; simpl; intuition. 
  - (* FTAbs *) pose proof (fresh_not_elem nms);
    set (y := fresh nms) in H2; apply H1 in H2.
    revert H2; unfold isLC.
    apply lem_islc_at_after_open_at.
  - (* FTAbsT *) pose proof (fresh_not_elem nms);
    set (a' := fresh nms) in H1; apply H0 in H1.
    revert H1; unfold isLC.
    apply lem_islc_at_after_open_tv_at.
  - (* FTLet *) pose proof (fresh_not_elem nms);
    set (y := fresh nms) in H2; apply H1 in H2.
    revert H2; unfold isLC.
    apply lem_islc_at_after_open_at.
  Qed.

Lemma lem_pftyp_islcp : forall (g:fenv) (ps:preds),
    PredicatesHaveBoolType g ps -> isLCP ps.
Proof. intros; induction H; unfold isLCP; simpl; try split.
  apply lem_ftyp_islc with g (FTBasic TBool); apply H.
  apply IHPredicatesHaveBoolType. Qed.

Lemma lem_wfft_islcft : forall (g:fenv) (t:ftype) (k:kind),
    WFFT g t k -> isLCFT t.
Proof. intros; induction H; unfold isLCFT; simpl; intuition.
  - (* WFFTBasic *) destruct b; simpl in H; intuition.
  - (* WFFTPoly  *) assert (1 = 0 + 1) by intuition; rewrite H1.
    pose proof (fresh_varF_not_elem nms g); destruct H2.
    apply lem_islcft_at_after_openFT_at with (fresh_varF nms g).
    apply H0; assumption.
  Qed.

Lemma lem_wftype_islct : forall (g:env) (t:type) (k:kind),
    WFtype g t k -> isLCT t.
Proof. intros; induction H; unfold isLCT; simpl; intuition.
  - (* WFBase *) destruct b; simpl in H; intuition.
  - (* WFRefn *) pose proof (fresh_not_elem nms);
    set (y := fresh nms) in H2; apply H1 in H2;  
    apply lem_pftyp_islcp in H2; revert H2;
    destruct b; try apply lem_islc_at_after_open_at.
    (* BTV *) unfold isLCT in IHWFtype; simpl in IHWFtype;
      destruct IHWFtype; unfold lt in H2; apply Nat.le_0_r in H2; discriminate H2.
  - (* WFFunc *) pose proof (fresh_not_elem nms);
    set (y := fresh nms) in H2; apply H1 in H2; revert H2;
    apply lem_islc_at_after_open_at.
  - (* WFExis *) pose proof (fresh_not_elem nms);
    set (y := fresh nms) in H2; apply H1 in H2; revert H2;
    apply lem_islc_at_after_open_at.
  - (* WFPoly *) pose proof (fresh_not_elem nms);
    set (a := fresh nms) in H1; apply H0 in H1; revert H1;
    apply lem_islc_at_after_open_tv_at.
  Qed.