Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.Semantics.
Require Import AutoProof.SystemRF.SystemRF.SystemFWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.SystemFLemmasWeaken.
Require Import AutoProof.SystemRF.SystemRF.SystemFLemmasSubstitution.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.Typing.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.LemmasWeakenWFTV.
Require Import AutoProof.SystemRF.SystemRF.SubstitutionLemmaWF.
Require Import AutoProof.SystemRF.SystemRF.SubstitutionLemmaWFTV.
Require Import AutoProof.SystemRF.Denotations.ClosingSubstitutions.
Require Import AutoProof.SystemRF.Denotations.Denotations.
Require Import AutoProof.SystemRF.Denotations.BasicPropsCSubst.
Require Import AutoProof.SystemRF.Denotations.BasicPropsDenotes.
Require Import AutoProof.SystemRF.Denotations.EnvironmentSubstitutions.

Lemma lem_csubst_hasftype' : forall (g g':env) (e:expr) (t:type) (th:csub),
    HasFtype (erase_env (concatE g g')) e (erase t) -> WFFE (erase_env g) 
        -> unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> DenotesEnv g th
        -> HasFtype (erase_env (csubst_env th g')) (csubst th e) (erase (ctsubst th t)).
Proof. induction g; intros; inversion H4. 
  - (* Empty *) rewrite lem_empty_concatE in H; subst th; simpl; apply H.
  - (* Cons *) subst x0 t1 g0; try rewrite lem_unroll_csubst_env_left;
    try rewrite lem_erase_esubFV;
    try rewrite lem_unroll_csubst_left;
    try rewrite lem_unroll_ctsubst_left;
    try rewrite lem_erase_tsubFV;
    try rewrite <- (lem_empty_concatE (csubst_env th0 g'));
    try rewrite lem_erase_concat; simpl;
    try apply lem_subst_ftyp with (erase (ctsubst th0 t));
    assert (FCons x (erase (ctsubst th0 t)) FEmpty 
              = erase_env (csubst_env th0 (Cons x t Empty)))
      by (rewrite lem_csubst_cons_env; rewrite lem_csubst_env_empty; 
          reflexivity); try rewrite H5;
    try rewrite <- lem_erase_concat;
    try rewrite <- lem_csubst_env_concat; try apply IHg;
    try rewrite <- lem_concat_shift;
    apply lem_den_isvalue in H11 as Hv;
    apply lem_den_hasftype in H11 as p_v_tht;
    apply lem_fv_subset_bindsF in p_v_tht as Hfv;
    simpl in Hfv; destruct Hfv as [Hfv Hftv];
    simpl in H1; destruct H1; simpl; 
    try apply intersect_names_add_elim_l in H3; 
    fold binds in H3; destruct H3; try apply H3;
    pose proof (lem_binds_concat (Cons x t Empty) g'); 
    unfold binds in H12; fold binds in H12; destruct H12;  
    try apply subset_in_intersect with (union (names_add x empty) (binds g'));
    pose proof (subset_union_names_add_l empty (binds g') x); destruct H14;
    try apply subset_in_intersect with (names_add x (union empty (binds g')));
    try apply intersect_names_add_intro_r;
    try apply subset_in_intersect with (binds g'); try apply union_empty_l;
    try apply lem_denotesenv_closed with g;
    try apply lem_denotesenv_substitutable with g;
    try apply unique_concat; try (unfold unique; split);
    try apply unique_erase_env;
    try apply csubst_env_unique;    
    unfold binds; fold binds;
    try apply intersect_names_add_intro_l;
    unfold in_csubst; unfold in_envF;
    try rewrite <- binds_erase_env;
    try rewrite csubst_env_binds; 
    try rewrite <- lem_binds_env_th with g th0;
    try apply H3; try apply no_elem_empty; auto;
    inversion H0; subst x0 t1 g0; apply H19.
  - (* ConsT *) subst a0 k0 g0; simpl; apply IHg;
    try rewrite lem_erase_concat;
    try rewrite lem_erase_esubFTV;
    try rewrite lem_erase_tsubFTV;
    try apply lem_subst_tv_ftyp with k;
    rewrite lem_erase_concat in H; simpl in H;
    simpl in H1; destruct H1;
    apply intersect_names_add_elim_l in H3;
    fold binds in H3; destruct H3;
    try apply esubFTV_unique; try rewrite esubFTV_binds;
    try apply lem_wftype_islct with Empty k;
    try apply unique_erase_env;
    unfold in_envF; repeat rewrite <- binds_erase_env;
    inversion H0; subst a0 k0 g0;
    apply lem_weaken_many_wf with Empty g t0 k in H13 as Ht0;
    try rewrite lem_empty_concatE in Ht0;
    try apply lem_erase_wftype;
    try apply lem_free_subset_binds in Ht0 as Hfr;
    try destruct Hfr as [Hfr Hfrtv];
    try rewrite <- vbinds_erase_env;
    try rewrite <- tvbinds_erase_env;
    unfold unique; trivial.
  Qed.  
                                    
Lemma lem_csubst_hasftype : forall (g:env) (e:expr) (t:type) (th:csub),
    HasFtype (erase_env g) e (erase t) -> WFFE (erase_env g) 
        -> unique g -> DenotesEnv g th
        -> HasFtype FEmpty (csubst th e) (erase (ctsubst th t)).
Proof. intros; assert (FEmpty = erase_env (csubst_env th Empty))
      by (rewrite lem_csubst_env_empty; reflexivity);
  rewrite H3; apply lem_csubst_hasftype' with g; simpl;
  try apply intersect_empty_r; trivial. Qed.

Lemma lem_ctsubst_wf' : forall (g g':env) (t:type) (k:kind) (th:csub),
    WFtype (concatE g g') t k -> WFEnv g
        -> unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> DenotesEnv g th
        -> WFtype (csubst_env th g') (ctsubst th t) k.
Proof. induction g; intros.
  - (* Empty *) inversion H4; simpl; 
    rewrite lem_empty_concatE in H; apply H.
  - (* Cons *)  inversion H4; subst x0 t1 g0;
    rewrite lem_unroll_csubst_env_left;
    try rewrite lem_unroll_ctsubst_left;
    try rewrite <- (lem_empty_concatE (esubFV x v (csubst_env th0 g')));
    try apply lem_subst_wf with (ctsubst th0 t); 
    assert (Cons x (ctsubst th0 t) Empty = csubst_env th0 (Cons x t Empty))
      by (symmetry; rewrite <- (lem_csubst_env_empty th0) at 2;
          apply lem_csubst_cons_env); try rewrite H5;
    try rewrite <- lem_csubst_env_concat; try apply IHg;
    apply lem_den_isvalue in H11 as Hv;
    apply lem_den_hasftype in H11 as p_v_tht;
    apply lem_fv_subset_bindsF in p_v_tht as Hfv; 
    simpl in Hfv; destruct Hfv as [Hfv Hftv];
    try rewrite <- lem_concat_shift; 
    simpl in H1;
    try apply intersect_names_add_elim_l in H3; fold binds in H3;
    inversion H0; destruct H1; destruct H3; subst x0 t1 g0;
    try apply unique_concat;
    try (unfold unique; split);
    unfold binds; fold binds;
    try apply intersect_names_add_intro_l;
    try apply intersect_empty_l; try apply H3;
    pose proof (lem_binds_concat (Cons x t Empty) g'); 
    unfold binds in H6; fold binds in H6; destruct H6;    
    try apply subset_in_intersect with (union (names_add x empty) (binds g'));
    pose proof (subset_union_names_add_l empty (binds g') x); destruct H12;
    try apply subset_in_intersect with (names_add x (union empty (binds g')));
    try apply intersect_names_add_intro_r;
    try apply subset_in_intersect with (binds g'); try apply union_empty_l;
    try apply csubst_env_unique;
    try apply lem_denotesenv_closed with g;
    try apply lem_denotesenv_substitutable with g;
    unfold in_csubst; unfold in_env; 
    try rewrite csubst_env_binds; 
    try rewrite <- lem_binds_env_th with g th0; auto;
    apply no_elem_empty; intros;
    try apply not_elem_subset with empty; auto.
  - (* ConsT *) inversion H4; subst a0 k1 g0; simpl;
    apply IHg; try apply lem_subst_tv_wf with k;
    inversion H0; subst a0 k1 g0;
    simpl in H1; destruct H1;
    apply intersect_names_add_elim_l in H3;
    fold binds in H3; destruct H3;
    try apply lem_erase_env_wfenv;
    try apply esubFTV_unique; try rewrite esubFTV_binds;
    trivial; rewrite <- lem_empty_concatE at 1;
    apply lem_weaken_many_wf; unfold unique; trivial.
  Qed.  
    
Lemma lem_ctsubst_wf : forall (g:env) (t:type) (k:kind) (th:csub),
    WFtype g t k -> WFEnv g -> unique g -> DenotesEnv g th
        -> WFtype Empty (ctsubst th t) k.
Proof. intros; assert (Empty = csubst_env th Empty)
      by (symmetry; apply lem_csubst_env_empty);
  rewrite H3; apply lem_ctsubst_wf' with g; simpl;
  try apply intersect_empty_r; trivial. Qed.