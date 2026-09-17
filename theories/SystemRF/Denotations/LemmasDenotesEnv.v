Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.Strengthenings.
Require Import AutoProof.SystemRF.SystemRF.LocalClosure.
Require Import AutoProof.SystemRF.SystemRF.Semantics.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsSubstitution.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.Typing.
Require Import AutoProof.SystemRF.SystemRF.LemmasWeakenWFTV.
Require Import AutoProof.SystemRF.SystemRF.LemmasWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.LemmasTyping.
Require Import AutoProof.SystemRF.SystemRF.LemmasTransitive.
Require Import AutoProof.SystemRF.Denotations.ClosingSubstitutions.
Require Import AutoProof.SystemRF.Denotations.Denotations.
Require Import AutoProof.SystemRF.Denotations.PrimitivesSemantics.
Require Import AutoProof.SystemRF.Denotations.BasicPropsCSubst.
Require Import AutoProof.SystemRF.Denotations.BasicPropsDenotes.
Require Import AutoProof.SystemRF.Denotations.EnvironmentSubstitutions.
Require Import AutoProof.SystemRF.Denotations.MultiSubstitutionLemmas.

Require Import Arith.
Require Import Lists.ListSet.

Lemma lem_remove_var_denote : forall (th:csub) (t:type) (v:expr) (x:var_name),
    Denotes (ctsubst th t) v -> In x (bindsC th) 
        -> ~ In x (free t) -> ~ In x (freeTV t)
        -> closed th -> uniqueC th -> substitutable th
        -> Denotes (ctsubst (remove_fromCS th x) t) v.
Proof. intros; rewrite <- lem_remove_ctsubst; trivial. Qed.

Lemma lem_remove_var_denote_env : forall (g g':env) (x:var_name) (t_x:type) (th:csub),
    unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env x g) -> ~ (in_env x g') 
        -> WFEnv (concatE g g')
        -> closed th -> uniqueC th -> substitutable th
        -> DenotesEnv (concatE (Cons x t_x g) g') th
        -> DenotesEnv (concatE g g') (remove_fromCS th x).
Proof. intro g; induction g'; simpl; intros.
  - (* CEmpty *) inversion H8; simpl;
    assert (x = x) by reflexivity;
    apply Nat.eqb_eq in H16; rewrite H16; apply H12.
  - (* CCons  *) inversion H4; inversion H8; 
    unfold in_env in H3; simpl in *;
    apply not_elem_names_add_elim in H3; destruct H3;
    apply Nat.eqb_neq in H3; rewrite H3.
    apply DExt; try apply IHg' with t_x;
    try apply lem_remove_var_denote;
    subst th; simpl in *; destruct H0;
    destruct H5; destruct H6; destruct H7; destruct H23;
    try rewrite <- lem_binds_env_th with (concatE (Cons x0 t_x g) g') th0;
    pose proof (lem_binds_concat (Cons x0 t_x g) g'); destruct H27;
    try apply H28; try apply set_union_intro1; 
    try apply set_add_intro2;
    try apply intersect_names_add_elim_r in H1; destruct H1;
    apply lem_free_subset_binds in H14; destruct H14;
    auto; apply not_elem_subset with (binds (concatE g g'));
    try apply not_elem_concat_intro;
    pose proof (vbinds_subset (concatE g g'));
    pose proof (tvbinds_subset (concatE g g'));
    try (apply subset_trans with (vbinds (concatE g g')); assumption);
    try (apply subset_trans with (tvbinds (concatE g g')); assumption); auto.
  - (* CConsT *) inversion H4; inversion H8; 
    unfold in_env in H3; simpl in *;
    apply not_elem_names_add_elim in H3; destruct H3;
    apply Nat.eqb_neq in H3; rewrite H3;
    apply DExtT; try apply IHg' with t_x;
    subst th; simpl in *; destruct H0;
    destruct H5 as [_ [_ H5]]; destruct H6; destruct H7; destruct H25;
    apply intersect_names_add_elim_r in H1; destruct H1; auto.
  Qed.
    
Lemma lem_remove_tvar_denote_env : forall (g g':env) (a:var_name) (k_a:kind) (th:csub),
    unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env a g) -> ~ (in_env a g') 
        -> WFEnv (concatE g g')
        -> closed th -> uniqueC th -> substitutable th
        -> DenotesEnv (concatE (ConsT a k_a g) g') th
        -> DenotesEnv (concatE g g') (remove_fromCS th a).
Proof. intro g; induction g'; simpl; intros.
  - (* CEmpty *) inversion H8; simpl;
    assert (a = a) by reflexivity;
    apply Nat.eqb_eq in H18; rewrite H18; apply H12.
  - (* CCons  *) inversion H4; inversion H8; 
    unfold in_env in H3; simpl in *;
    apply not_elem_names_add_elim in H3; destruct H3;
    apply Nat.eqb_neq in H3; rewrite H3.
    apply DExt; try apply IHg' with k_a;
    try apply lem_remove_var_denote;
    subst th; simpl in *; destruct H0;
    destruct H5; destruct H6; destruct H7; destruct H23;
    try rewrite <- lem_binds_env_th with (concatE (ConsT a k_a g) g') th0;
    pose proof (lem_binds_concat (ConsT a k_a g) g'); destruct H27;
    try apply H28; try apply set_union_intro1; 
    try apply set_add_intro2;
    try apply intersect_names_add_elim_r in H1; destruct H1;
    apply lem_free_subset_binds in H14; destruct H14;
    auto; apply not_elem_subset with (binds (concatE g g'));
    try apply not_elem_concat_intro;
    pose proof (vbinds_subset (concatE g g'));
    pose proof (tvbinds_subset (concatE g g'));
    try (apply subset_trans with (vbinds (concatE g g')); assumption);
    try (apply subset_trans with (tvbinds (concatE g g')); assumption); auto.
  - (* CConsT *) inversion H4; inversion H8; 
    unfold in_env in H3; simpl in *;
    apply not_elem_names_add_elim in H3; destruct H3;
    apply Nat.eqb_neq in H3; rewrite H3;
    apply DExtT; try apply IHg' with k_a;
    subst th; simpl in *; destruct H0;
    destruct H5 as [_ [_ H5]]; destruct H6; destruct H7; destruct H25;
    apply intersect_names_add_elim_r in H1; destruct H1; auto.
  Qed.

Lemma lem_add_var_denote_env : 
  forall (g g':env) (x:var_name) (v_x:expr) (t_x:type) (th:csub),
    unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env x g) -> ~ (in_env x g') -> WFEnv g
        -> Hastype g v_x t_x 
        -> Denotes (ctsubst th t_x) (csubst th v_x)
        -> DenotesEnv (concatE g (esubFV x v_x g')) th
        -> exists th', DenotesEnv (concatE (Cons x t_x g) g') th' /\
                  (forall e, csubst th' e = csubst th (subFV x v_x e)) /\        
                  (forall t, ctsubst th' t = ctsubst th (tsubFV x v_x t)) /\ 
                  (forall ps, cpsubst th' ps = cpsubst th (psubFV x v_x ps)).
Proof. intro g; induction g'; simpl; intros.
  - (* CEmpty *) exists (CCons x (csubst th v_x) th); repeat split; 
    try apply DExt; intros; simpl;
    try apply lem_csubst_subFV;
    try apply lem_ctsubst_tsubFV;
    try apply lem_cpsubst_psubFV;
    unfold in_csubst; try rewrite <- lem_binds_env_th with g th;
    try rewrite <- lem_vbinds_env_th with g th;
    try rewrite <- lem_tvbinds_env_th with g th;
    try apply lem_fv_subset_binds with t_x;
    try apply lem_denotesenv_closed with g;
    try apply lem_denotesenv_substitutable with g;
    try apply lem_denotesenv_uniqueC with g; trivial.  
  - (* CCons  *) destruct H0;
    apply intersect_names_add_elim_r in H1; destruct H1;
    apply not_elem_names_add_elim in H3; destruct H3;
    inversion H7; apply IHg' with x0 v_x t_x th0 in H14 as IH;
    fold binds in H10; auto.
    (* exists th', DenotesEnv (Cons x t (concatE (Cons x0 t_x g) g')) th' *)
    destruct IH as [th' [d_env_th' [Hcs [Hcs' Hcs'']]]].
    exists (CCons x v th'); simpl; repeat split; 
    try apply DExt;
    try apply not_elem_concat_intro;
    try apply not_elem_names_add_intro; try split; 
    try rewrite (Hcs' t); auto;
    intros; try rewrite lem_commute_tsubFV; try apply Hcs';
    try rewrite lem_commute_subFV; try apply Hcs;
    try rewrite lem_commute_psubFV; try apply Hcs'';
    apply lem_den_nofv in H17 as Hv; destruct Hv;
    try rewrite H18; auto;
    try apply not_elem_subset with (vbinds g);
    try apply not_elem_subset with (binds g);
    try apply lem_fv_subset_binds with t_x;
    try apply vbinds_subset; auto.    
    (* Denotes (ctsubst th0 t_x) (csubst th0 v_x) *)
    subst th; simpl in H6;
    rewrite lem_subFV_notin' in H6;
    rewrite lem_tsubFV_notin in H6;
    apply lem_typing_wf in H5 as Htx;
    try apply not_elem_subset with (vbinds g);
    try apply not_elem_subset with (binds g);
    try apply lem_fv_subset_binds with t_x;
    try apply lem_free_subset_binds with Star;
    try apply vbinds_subset; auto.    
  - (* CConsT*) destruct H0;
    apply intersect_names_add_elim_r in H1; destruct H1;
    apply not_elem_names_add_elim in H3; destruct H3;
    inversion H7; apply IHg' with x v_x t_x th0 in H14 as IH;
    fold binds in H10; auto.
    (* exists th', DenotesEnv (ConsT a k (concatE (Cons x t_x g) g')) th' *)
    destruct IH as [th' [d_env_th' [Hcs [Hcs' Hcs'']]]].
    exists (CConsT a t th'); simpl; repeat split; 
    try apply DExtT;
    try apply not_elem_concat_intro;
    try apply not_elem_names_add_intro; try split; auto;
    intros; try rewrite <- lem_commute_tsubFV_tsubFTV; try apply Hcs';
    try rewrite <- lem_commute_subFV_subFTV; try apply Hcs;
    try rewrite <- lem_commute_psubFV_psubFTV; try apply Hcs'';
    try ( apply not_elem_subset with (tvbinds g);
          try apply not_elem_subset with (binds g);
          try apply lem_fv_subset_binds with t_x;
          try apply tvbinds_subset; assumption );
    try apply not_elem_subset with empty;
    apply lem_free_subset_binds in H19 as Ht; 
    simpl in Ht; destruct Ht; auto.          
    (* Denotes (ctsubst th0 t_x) (csubst th0 v_x) *)
    subst th; simpl in H6;
    rewrite lem_subFTV_notin' in H6;
    rewrite lem_tsubFTV_notin in H6;
    apply lem_typing_wf in H5 as Htx;
    try apply not_elem_subset with (tvbinds g);
    try apply not_elem_subset with (binds g);
    try apply lem_fv_subset_binds with t_x;
    try apply lem_free_subset_binds with Star;
    try apply tvbinds_subset; auto.    
  Qed.

Lemma lem_add_tvar_denote_env : 
  forall (g g':env) (a:var_name) (t_a:type) (k_a:kind) (th:csub),
    unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env a g) -> ~ (in_env a g') -> WFEnv g
        -> WFtype g t_a k_a
        -> isMono t_a -> noExists t_a
        -> DenotesEnv (concatE g (esubFTV a t_a g')) th
        -> exists th', DenotesEnv (concatE (ConsT a k_a g) g') th' /\
                  (forall e, csubst th' e = csubst th (subFTV a t_a e)) /\
                  (forall t, ctsubst th' t = ctsubst th (tsubFTV a t_a t)) /\ 
                  (forall ps, cpsubst th' ps = cpsubst th (psubFTV a t_a ps)).
Proof. intro g; induction g'; simpl; intros.
  - (* CEmpty *) exists (CConsT a (ctsubst th t_a) th); repeat split; 
    try apply DExtT; intros; simpl;
    try apply lem_csubst_subFTV;
    try apply lem_ctsubst_tsubFTV;
    try apply lem_cpsubst_psubFTV;
    try apply lem_ctsubst_wf with g;
    try apply lem_ctsubst_isMono;
    try apply lem_ctsubst_noExists;     
    unfold in_csubst; 
    try rewrite <- lem_binds_env_th with g th;
    try rewrite <- lem_vbinds_env_th with g th;
    try rewrite <- lem_tvbinds_env_th with g th;
    try apply lem_free_subset_binds with k_a;
    try apply lem_denotesenv_closed with g;
    try apply lem_denotesenv_substitutable with g;
    try apply lem_denotesenv_uniqueC with g; trivial. 
  - (* CCons  *) destruct H0;
    apply intersect_names_add_elim_r in H1; destruct H1;
    apply not_elem_names_add_elim in H3; destruct H3;
    inversion H8; apply IHg' with a t_a k_a th0 in H15 as IH;
    fold binds in H11; auto.
    (* exists th', DenotesEnv (Cons x t (concatE (Cons x0 t_x g) g')) th' *)
    destruct IH as [th' [d_env_th' [Hcs [Hcs' Hcs'']]]].
    exists (CCons x v th'); simpl; repeat split; 
    try apply DExt;
    try apply not_elem_concat_intro;
    try apply not_elem_names_add_intro; try split;
    try rewrite (Hcs' t); auto;
    intros; try rewrite lem_commute_tsubFV_tsubFTV; try apply Hcs';
    try rewrite lem_commute_subFV_subFTV; try apply Hcs;
    try rewrite lem_commute_psubFV_psubFTV; try apply Hcs'';
    apply lem_den_nofv in H18 as Hv; destruct Hv;
    try rewrite H20; auto;
    apply not_elem_subset with (vbinds g);
    try apply not_elem_subset with (binds g);
    try apply lem_free_subset_binds with k_a;
    try apply vbinds_subset; auto.  
  - (* CConsT*) destruct H0;
    apply intersect_names_add_elim_r in H1; destruct H1;
    apply not_elem_names_add_elim in H3; destruct H3;
    inversion H8; apply IHg' with a0 t_a k_a th0 in H15 as IH;
    fold binds in H11; auto.
    (* exists th', DenotesEnv (ConsT a k (concatE (Cons x t_x g) g')) th' *)
    destruct IH as [th' [d_env_th' [Hcs [Hcs' Hcs'']]]].
    exists (CConsT a t th'); simpl; repeat split; 
    try apply DExtT;
    try apply not_elem_concat_intro;
    try apply not_elem_names_add_intro; try split; auto;
    intros; try rewrite <- lem_commute_tsubFTV; try apply Hcs';
    try rewrite <- lem_commute_subFTV; try apply Hcs;
    try rewrite <- lem_commute_psubFTV; try apply Hcs'';
    try ( apply not_elem_subset with (tvbinds g);
          try apply not_elem_subset with (binds g);
          try apply lem_free_subset_binds with k_a;
          try apply tvbinds_subset; assumption );
    try apply not_elem_subset with empty;
    apply lem_free_subset_binds in H20 as Ht; 
    simpl in Ht; destruct Ht; auto.
  Qed.

Lemma lem_extend_denotes : forall (g g':env) (th:csub) (t:type) (v:expr),
    DenotesEnv (concatE g g') th
        -> WFtype g t Star
        -> ( forall th1, DenotesEnv g th1 
                  -> Denotes (ctsubst th1 t) (csubst th1 v) )
        -> Denotes (ctsubst th t) (csubst th v).
Proof. intro g; induction g'; simpl; intros.
  - apply H1; apply H.
  - inversion H; rewrite lem_unroll_csubst_left;
    try rewrite lem_unroll_ctsubst_left;
    try rewrite lem_subFV_notin';
    try rewrite lem_tsubFV_notin;
    assert (Denotes (ctsubst th0 t0) (csubst th0 v)) by auto;
    assert (free (ctsubst th0 t0) = empty)
      by (apply lem_ctsubst_no_more_fv;
          try rewrite <- lem_vbinds_env_th with (concatE g g') th0;
          try rewrite <- lem_tvbinds_env_th with (concatE g g') th0;
          try apply lem_free_subset_binds with Star;
          try apply lem_weaken_many_wf;
          try apply lem_denotesenv_closed with (concatE g g');
          try apply lem_denotesenv_substitutable with (concatE g g');
          apply lem_denotesenv_unique in H5 as Hu; 
          apply concat_unique in Hu as [Hg [Hg' Hi]]; auto); 
    try apply lem_den_nofv in H8 as Hv0;
    try apply lem_den_nofv in H9 as Hv; destruct Hv;
    try rewrite H10; try rewrite H11; unfold in_csubst;
    try rewrite <- lem_binds_env_th with (concatE g g') th0;
    try apply lem_denotesenv_closed with (concatE g g');
    try apply lem_denotesenv_substitutable with (concatE g g'); auto.
  - inversion H; rewrite lem_unroll_ctsubst_tv_left;
    try rewrite lem_unroll_csubst_tv_left;    
    try rewrite lem_subFTV_notin';
    try rewrite lem_tsubFTV_notin;
    assert (Denotes (ctsubst th0 t) (csubst th0 v)) by auto;
    assert (freeTV (ctsubst th0 t) = empty)
      by (apply lem_ctsubst_no_more_fv;
          try rewrite <- lem_vbinds_env_th with (concatE g g') th0;
          try rewrite <- lem_tvbinds_env_th with (concatE g g') th0;
          try apply lem_free_subset_binds with Star;
          try apply lem_weaken_many_wf;
          try apply lem_denotesenv_closed with (concatE g g');
          try apply lem_denotesenv_substitutable with (concatE g g');
          apply lem_denotesenv_unique in H5 as Hu; 
          apply concat_unique in Hu as [Hg [Hg' Hi]]; auto);
    try apply lem_free_subset_binds in H10 as Ht0; destruct Ht0;
    try split; try apply no_elem_empty;
    try apply lem_den_nofv in H11 as Hv; destruct Hv;
    try rewrite H12; try rewrite H16; unfold in_csubst;
    try rewrite <- lem_binds_env_th with (concatE g g') th0;
    try apply lem_denotesenv_closed with (concatE g g');
    try apply lem_denotesenv_substitutable with (concatE g g'); auto.
  Qed.
