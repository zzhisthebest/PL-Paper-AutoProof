Require Import Arith.

Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.LocalClosure. 
Require Import AutoProof.SystemRF.SystemRF.SystemFWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsSubstitution.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SystemFLemmasWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SystemFLemmasWeaken.

(*------------------------------------------------------------------------------
----- | METATHEORY Development for the Underlying System F Calculus
------------------------------------------------------------------------------*)

(* -- -- -- -- -- -- -- -- ---
   -- THE SUBSTITUTION LEMMA -
   -- -- -- -- -- -- -- -- --- *)

Lemma lem_subst_ftyp' : forall (g'xg : fenv) (e : expr) (t : ftype),
    HasFtype g'xg e t -> ( forall (g g':fenv) (x:var_name) (v_x:expr) (t_x:ftype),
       g'xg = concatF (FCons x t_x g) g' 
                     -> uniqueF g -> uniqueF g'
                     -> intersect (bindsF g) (bindsF g') = empty
                     -> ~ (in_envF x g) -> ~ (in_envF x g') 
                     -> isValue v_x -> HasFtype g v_x t_x
                     -> HasFtype (concatF g g') (subFV x v_x e) t ).
Proof. apply ( HasFtype_ind 
 (fun (g'xg : fenv) (e : expr) (t : ftype) => 
   forall (g g':fenv) (x:var_name) (v_x:expr) (t_x:ftype),
       g'xg = concatF (FCons x t_x g) g' 
             -> uniqueF g -> uniqueF g'
             -> intersect (bindsF g) (bindsF g') = empty
             -> ~ (in_envF x g) -> ~ (in_envF x g') 
             -> isValue v_x -> HasFtype g v_x t_x
             -> HasFtype (concatF g g') (subFV x v_x e) t  ));
  intros env; intros; subst env.
  - (* FTBC *) apply FTBC.
  - (* FTIC *) apply FTIC.
  - (* FTVar *) apply lem_boundinF_concatF in H; simpl in H; destruct H. destruct H.
    * (* x = x0 *) destruct H; subst x0; subst b; simpl.
      assert (x = x) by reflexivity; apply Nat.eqb_eq in H; rewrite H.
      apply lem_weaken_many_ftyp; assumption.       
    * (* x0 in g *) apply lem_boundin_inenvF in H as H'.
      pose proof vbindsF_subset as Htv; unfold Subset in Htv; apply Htv in H';
      assert (x0 <> x) by (unfold not; intro; subst x0; contradiction).
      apply Nat.eqb_neq in H0; simpl; rewrite H0.
      apply FTVar. apply lem_boundinF_concatF; intuition.
    * (* x0 in g' *) apply lem_boundin_inenvF in H as H'.
      pose proof vbindsF_subset as Htv; unfold Subset in Htv; apply Htv in H';
      assert (x0 <> x) by (unfold not; intro; subst x0; contradiction).
      apply Nat.eqb_neq in H0; simpl; rewrite H0.
      apply FTVar; apply lem_boundinF_concatF; intuition.
  - (* FTPrm *) apply FTPrm.
  - (* FTAbs *) apply FTAbs with k (names_add x (union nms (bindsF (concatF g g'))));
    try apply lem_strengthen_wfft with x t_x; try assumption;
     intros; fold subFV;
    assert (FCons y b (concatF g g') = concatF g (FCons y b g')) 
      by reflexivity; rewrite H10;
    apply not_elem_names_add_elim in H2; destruct H2;
    apply not_elem_union_elim in H11; destruct H11;
    apply not_elem_concatF_elim in H12; destruct H12.
    rewrite <- lem_commute_subFV_unbind;
    try apply H1 with t_x; 
    try apply intersect_names_add_intro_r;
    try apply lem_ftyp_islc with g t_x;
    unfold in_envF; try apply not_elem_names_add_intro;
    simpl; intuition.
  - (* FTApp *) apply FTApp with b; 
    apply H0 with t_x || apply H2 with t_x; intuition.
  - (* FTAbsT *) apply FTAbsT with (names_add x (union nms (bindsF (concatF g g'))));
    intros; fold subFV;
    assert (FConsT a' k (concatF g g') = concatF g (FConsT a' k g')) 
      by reflexivity.
    apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H10; destruct H10;
    apply not_elem_concatF_elim in H11; destruct H11.
    rewrite <- lem_commute_subFV_unbind_tv; try rewrite H9;
    try apply H0 with t_x;
    try apply intersect_names_add_intro_r;  
    try apply lem_ftyp_islc with g t_x;
    unfold in_envF; try apply not_elem_names_add_intro;
    simpl; intuition.
  - (* FTAppT *) rewrite <- (lem_erase_tsubFV x v_x rt);
    try apply FTAppT with k; fold subFV;
    try apply H0 with t_x;
    try apply lemma_tsubFV_isMono;
    try apply lemma_tsubFV_noExists;
    pose proof (lem_tvbinds_cons_concatF g g' x t_x); destruct H7;
    apply (subset_trans _ _ _ H4) in H15;
    pose proof (lem_vbinds_cons_concatF  g g' x t_x); destruct H16;
    apply (subset_trans _ _ _ H3) in H17;
    apply lem_fv_subset_bindsF in H14 as H18; destruct H18;
    assert (Subset (vbindsF g) (union (vbindsF g) (vbindsF g'))) 
      by apply subset_union_intro_r;
    assert (Subset (tvbindsF g) (union (tvbindsF g) (tvbindsF g'))) 
      by apply subset_union_intro_r;
    pose proof (lem_vbinds_concatF g g');
    pose proof (lem_tvbinds_concatF g g');
    apply (subset_trans3 _ _ _ _ H18 H20) in H22;
    apply (subset_trans3 _ _ _ _ H19 H21) in H23;
    try apply free_tsubFV_bounded;
    try apply freeTV_tsubFV_bounded;
    try apply lem_islc_at_subFV;
    try apply lem_ftyp_islc with g t_x;
    apply lem_strengthen_wfft in H6; 
    try rewrite lem_erase_tsubFV;  trivial.
  - (* FTLet *) apply FTLet with b (names_add x (union nms (bindsF (concatF g g'))));
    try apply H0 with t_x; trivial; intros; fold subFV;
    assert (FCons y b (concatF g g') = concatF g (FCons y b g')) 
      by reflexivity; rewrite H11;
    apply not_elem_names_add_elim in H3; destruct H3;
    apply not_elem_union_elim in H12; destruct H12;
    apply not_elem_concatF_elim in H13; destruct H13;
    rewrite <- lem_commute_subFV_unbind;
    try apply H2 with t_x; 
    try apply intersect_names_add_intro_r;
    try apply lem_ftyp_islc with g t_x;
    unfold in_envF; try apply not_elem_names_add_intro; simpl; intuition.
  - (* FTAnn *) apply FTAnn; fold tsubFV; fold subFV;
    try apply H4 with t_x;
    try rewrite lem_erase_tsubFV;
    pose proof (lem_tvbinds_cons_concatF g g' x t_x); destruct H5;
    apply (subset_trans _ _ _ H1) in H13;
    pose proof (lem_vbinds_cons_concatF  g g' x t_x); destruct H14;
    apply (subset_trans _ _ _ H0) in H15;
    apply lem_fv_subset_bindsF in H12 as H16; destruct H16;
    assert (Subset (vbindsF g) (union (vbindsF g) (vbindsF g'))) 
      by apply subset_union_intro_r;
    assert (Subset (tvbindsF g) (union (tvbindsF g) (tvbindsF g'))) 
      by apply subset_union_intro_r;
    pose proof (lem_vbinds_concatF g g');
    pose proof (lem_tvbinds_concatF g g');
    apply (subset_trans3 _ _ _ _ H16 H18) in H20;
    apply (subset_trans3 _ _ _ _ H17 H19) in H21;
    try apply free_tsubFV_bounded;
    try apply freeTV_tsubFV_bounded;
    try apply lem_islc_at_subFV;
    try apply lem_ftyp_islc with g t_x;  intuition.
  - (* FTIf *) apply FTIf; 
    apply H0 with t_x || apply H2 with t_x || apply H4 with t_x; trivial.
  Qed.

Lemma lem_subst_ftyp : 
  forall (g g':fenv) (e : expr) (t : ftype) (x:var_name) (v_x:expr) (t_x:ftype),
    HasFtype (concatF (FCons x t_x g) g') e t
                     -> uniqueF g -> uniqueF g'
                     -> intersect (bindsF g) (bindsF g') = empty
                     -> ~ (in_envF x g) -> ~ (in_envF x g') 
                     -> isValue v_x -> HasFtype g v_x t_x
                     -> HasFtype (concatF g g') (subFV x v_x e) t.
Proof. intros; apply lem_subst_ftyp' with (concatF (FCons x t_x g) g') t_x;
  trivial. Qed.

Lemma lem_subst_tv_ftyp' : forall (g'ag : fenv) (e : expr) (t : ftype),
    HasFtype g'ag e t -> ( forall (g g':fenv) (a:var_name) (t_a:type) (k_a:kind),
        g'ag = concatF (FConsT a k_a g) g' 
            -> uniqueF g -> uniqueF g'
            -> intersect (bindsF g) (bindsF g') = empty
            -> ~ (in_envF a g) -> ~ (in_envF a g') 
            -> isMono t_a -> noExists t_a -> isLCT t_a
            -> Subset (free t_a) (vbindsF g)
            -> Subset (freeTV t_a) (tvbindsF g)
            -> WFFT g (erase t_a) k_a -> WFFE g 
            -> HasFtype (concatF g (fesubFV a (erase t_a) g')) 
                  (subFTV a t_a e) (ftsubFV a (erase t_a) t) ).
Proof. apply ( HasFtype_ind 
 (fun (g'ag : fenv) (e : expr) (t : ftype) => 
   forall (g g':fenv) (a:var_name) (t_a:type) (k_a:kind),
      g'ag = concatF (FConsT a k_a g) g' 
            -> uniqueF g -> uniqueF g'
            -> intersect (bindsF g) (bindsF g') = empty
            -> ~ (in_envF a g) -> ~ (in_envF a g') 
            -> isMono t_a -> noExists t_a -> isLCT t_a
            -> Subset (free t_a) (vbindsF g)
            -> Subset (freeTV t_a) (tvbindsF g)
            -> WFFT g (erase t_a) k_a -> WFFE g 
            -> HasFtype (concatF g (fesubFV a (erase t_a) g')) 
                  (subFTV a t_a e) (ftsubFV a (erase t_a) t)  ));
  intros env; intros; subst env.
  - (* FTBC *) apply FTBC.
  - (* FTIC *) apply FTIC.
  - (* FTVar *) apply lem_boundinF_concatF in H; simpl in H; simpl;
    apply FTVar; apply lem_boundinF_concatF; destruct H.
    * (* x0 in g *) left; apply boundinF_wffe_wfft in H as H';
      try apply lem_ffreeTV_bound_in_fenv with g b Star a in H';
      try rewrite lem_ftsubFV_notin; assumption.
    * (* x0 in g' *) right; apply lem_boundinF_fesubFV; assumption.
  - (* FTPrm *) destruct c; simpl; apply FTPrm.
  - (* FTAbs *) apply FTAbs with k (names_add a (union nms (bindsF (concatF g g'))));
    fold ftsubFV; fold subFTV;
    try apply lem_subst_tv_wfft with k_a; try assumption; intros;
    apply not_elem_names_add_elim in H2; destruct H2;
    apply not_elem_union_elim in H15; destruct H15;
    apply not_elem_concatF_elim in H16; destruct H16;
    assert (FCons y (ftsubFV a (erase t_a) b) (concatF g (fesubFV a (erase t_a) g')) 
            = concatF g (fesubFV a (erase t_a) (FCons y b g')))
      by reflexivity; rewrite H18;
    rewrite <- lem_commute_subFTV_unbind;
    try apply H1 with k_a;
    try apply intersect_names_add_intro_r;  
    try apply lem_wfft_islc with g k_a;
    unfold in_envF; try apply not_elem_names_add_intro;
    simpl; intuition.
  - (* FTApp *) apply FTApp with (ftsubFV a (erase t_a) b); fold subFTV;
    apply H0 with k_a || apply H2 with k_a; intuition.
  - (* FTAbsT *) apply FTAbsT with (names_add a (union nms (bindsF (concatF g g'))));
    intros; fold subFTV; fold ftsubFV;
    apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H14; destruct H14;
    apply not_elem_concatF_elim in H15; destruct H15;
    assert (FConsT a' k (concatF g (fesubFV a (erase t_a) g')) 
            = concatF g (fesubFV a (erase t_a) (FConsT a' k g')))
      by reflexivity; rewrite H17;
    try rewrite <- lem_commute_subFTV_unbind_tv;
    try rewrite <- lem_commute_ftsubFV_unbindFT;
    try apply H0 with k_a;
    try apply intersect_names_add_intro_r;
    try apply lem_wfft_islcft with g k_a;
    unfold in_envF; try apply not_elem_names_add_intro;
    simpl; intuition.
  - (* FTAppT *) rewrite lem_commute_ftsubFV_ftsubBV; simpl;
    try rewrite <- (lem_erase_tsubFTV a t_a rt);
    try apply FTAppT with k;
    try apply H0 with k_a;
    try apply lemma_tsubFTV_isMono;
    try apply lemma_tsubFTV_noExists;
    try rewrite concatF_fesubFV_vbindsF;
    try rewrite concatF_fesubFV_tvbindsF;
    pose proof (lem_tvbinds_consT_concatF g g' a k_a); destruct H7;
    apply (subset_trans _ _ _ H4) in H20;
    pose proof (lem_vbinds_consT_concatF  g g' a k_a); destruct H21;
    apply (subset_trans _ _ _ H3) in H22;
    assert (Subset (vbindsF g) (union (vbindsF g) (vbindsF g'))) 
      by apply subset_union_intro_r;
    assert (Subset (tvbindsF g) (union (tvbindsF g) (tvbindsF g'))) 
      by apply subset_union_intro_r;
    pose proof (lem_vbinds_concatF g g');
    pose proof (lem_tvbinds_concatF g g');
    apply (subset_trans3 _ _ _ _ H16 H23) in H25;
    apply (subset_trans3 _ _ _ _ H17 H24) in H26;
    try apply free_tsubFTV_bounded;
    try apply freeTV_tsubFTV_bounded;
    try apply lem_islc_at_subFTV;
    try rewrite lem_erase_tsubFTV;
    try apply lem_subst_tv_wfft with k_a;
    try apply lem_wfft_islc with g k_a;
    try apply lem_wfft_islcft with g k_a;   
    assumption || reflexivity.
  - (* FTLet *) apply FTLet with (ftsubFV a (erase t_a) b) 
                  (names_add a (union nms (bindsF (concatF g g')))); 
    fold subFTV; try apply H0 with k_a; trivial; intros;
    apply not_elem_names_add_elim in H3; destruct H3;
    apply not_elem_union_elim in H16; destruct H16;
    apply not_elem_concatF_elim in H17; destruct H17;
    assert (FCons y (ftsubFV a (erase t_a) b) (concatF g (fesubFV a (erase t_a) g')) 
            = concatF g (fesubFV a (erase t_a) (FCons y b g')))
      by reflexivity; rewrite H19;
    rewrite <- lem_commute_subFTV_unbind;  
    try apply H2 with k_a;
    try apply intersect_names_add_intro_r;
    try apply lem_wfft_islcft with g k_a;
    unfold in_envF; try apply not_elem_names_add_intro; 
    simpl; auto.
  - (* FTAnn *) apply FTAnn; fold subFTV; fold tsubFTV;
    try apply H4 with k_a;
    try rewrite lem_erase_tsubFTV; subst b;
    try rewrite concatF_fesubFV_vbindsF;
    try rewrite concatF_fesubFV_tvbindsF;
    pose proof (lem_tvbinds_consT_concatF g g' a k_a); destruct H;
    apply (subset_trans _ _ _ H1) in H5;
    pose proof (lem_vbinds_consT_concatF  g g' a k_a); destruct H18;
    apply (subset_trans _ _ _ H0) in H19;
    assert (Subset (vbindsF g) (union (vbindsF g) (vbindsF g'))) 
      by apply subset_union_intro_r;
    assert (Subset (tvbindsF g) (union (tvbindsF g) (tvbindsF g'))) 
      by apply subset_union_intro_r;
    pose proof (lem_vbinds_concatF g g');
    pose proof (lem_tvbinds_concatF g g');
    apply (subset_trans3 _ _ _ _ H14 H20) in H22;
    apply (subset_trans3 _ _ _ _ H15 H21) in H23;
    try apply free_tsubFTV_bounded;
    try apply freeTV_tsubFTV_bounded;
    try apply lem_islc_at_subFTV;
    assumption || reflexivity.
  - (* FTIf *) apply FTIf; 
    apply H0 with k_a || apply H2 with k_a || apply H4 with k_a; trivial.
  Qed.   
    
Lemma lem_subst_tv_ftyp : 
    forall (g g': fenv) (e : expr) (t : ftype) (a:var_name) (t_a:type) (k_a:kind),
      HasFtype (concatF (FConsT a k_a g) g') e t 
            -> uniqueF g -> uniqueF g'
            -> intersect (bindsF g) (bindsF g') = empty
            -> ~ (in_envF a g) -> ~ (in_envF a g') 
            -> isMono t_a -> noExists t_a -> isLCT t_a
            -> Subset (free t_a) (vbindsF g)
            -> Subset (freeTV t_a) (tvbindsF g)
            -> WFFT g (erase t_a) k_a -> WFFE g 
            -> HasFtype (concatF g (fesubFV a (erase t_a) g')) 
                  (subFTV a t_a e) (ftsubFV a (erase t_a) t).
Proof. intros; apply lem_subst_tv_ftyp' with (concatF (FConsT a k_a g) g') k_a;
  trivial. Qed.

Lemma lem_subst_pftyp' : forall (g'xg : fenv) (ps : preds),
    PredicatesHaveBoolType g'xg ps -> ( forall (g g':fenv) (x:var_name) (v_x:expr) (t_x:ftype),
       g'xg = concatF (FCons x t_x g) g' 
                     -> uniqueF g -> uniqueF g'
                     -> intersect (bindsF g) (bindsF g') = empty
                     -> ~ (in_envF x g) -> ~ (in_envF x g') 
                     -> isValue v_x -> HasFtype g v_x t_x
                     -> PredicatesHaveBoolType (concatF g g') (psubFV x v_x ps) ).
Proof. apply ( PredicatesHaveBoolType_ind 
 (fun (g'xg : fenv) (ps : preds) => 
   forall (g g':fenv) (x:var_name) (v_x:expr) (t_x:ftype),
       g'xg = concatF (FCons x t_x g) g' 
             -> uniqueF g -> uniqueF g'
             -> intersect (bindsF g) (bindsF g') = empty
             -> ~ (in_envF x g) -> ~ (in_envF x g') 
             -> isValue v_x -> HasFtype g v_x t_x
             -> PredicatesHaveBoolType (concatF g g') (psubFV x v_x ps)  ));
  intros env; intros; subst env; simpl.
  - apply PFTEmp.
  - apply PFTCons; try apply lem_subst_ftyp with t_x;
    try apply H1 with t_x; trivial. Qed.

Lemma lem_subst_pftyp : forall (g g' : fenv) (ps : preds) (x:var_name) (v_x:expr) (t_x:ftype),
    PredicatesHaveBoolType (concatF (FCons x t_x g) g') ps 
                     -> uniqueF g -> uniqueF g'
                     -> intersect (bindsF g) (bindsF g') = empty
                     -> ~ (in_envF x g) -> ~ (in_envF x g') 
                     -> isValue v_x -> HasFtype g v_x t_x
                     -> PredicatesHaveBoolType (concatF g g') (psubFV x v_x ps).
Proof. intros; apply lem_subst_pftyp' with (concatF (FCons x t_x g) g') t_x; 
  trivial. Qed.

Lemma lem_subst_tv_pftyp' : forall (g'ag : fenv) (ps : preds),
    PredicatesHaveBoolType g'ag ps -> ( forall (g g':fenv) (a:var_name) (t_a:type) (k_a:kind),
        g'ag = concatF (FConsT a k_a g) g' 
            -> uniqueF g -> uniqueF g'
            -> intersect (bindsF g) (bindsF g') = empty
            -> ~ (in_envF a g) -> ~ (in_envF a g') 
            -> isMono t_a -> noExists t_a -> isLCT t_a
            -> Subset (free t_a) (vbindsF g)
            -> Subset (freeTV t_a) (tvbindsF g)
            -> WFFT g (erase t_a) k_a -> WFFE g 
            -> PredicatesHaveBoolType (concatF g (fesubFV a (erase t_a) g')) (psubFTV a t_a ps) ).
Proof. apply ( PredicatesHaveBoolType_ind 
 (fun (g'ag : fenv) (ps : preds) => 
   forall (g g':fenv) (a:var_name) (t_a:type) (k_a:kind),
      g'ag = concatF (FConsT a k_a g) g' 
            -> uniqueF g -> uniqueF g'
            -> intersect (bindsF g) (bindsF g') = empty
            -> ~ (in_envF a g) -> ~ (in_envF a g') 
            -> isMono t_a -> noExists t_a -> isLCT t_a
            -> Subset (free t_a) (vbindsF g)
            -> Subset (freeTV t_a) (tvbindsF g)
            -> WFFT g (erase t_a) k_a -> WFFE g 
            -> PredicatesHaveBoolType (concatF g (fesubFV a (erase t_a) g')) (psubFTV a t_a ps)  ));
  intros env; intros; subst env; simpl.
  - apply PFTEmp.
  - apply PFTCons; assert (ftsubFV a (erase t_a) (FTBasic TBool) = FTBasic TBool)
      by reflexivity; try rewrite <- H2;
    try apply lem_subst_tv_ftyp with k_a;
    try apply H1 with k_a; assumption || reflexivity. Qed.

Lemma lem_subst_tv_pftyp : 
    forall (g g' : fenv) (ps : preds) (a:var_name) (t_a:type) (k_a:kind),
        PredicatesHaveBoolType (concatF (FConsT a k_a g) g') ps 
            -> uniqueF g -> uniqueF g'
            -> intersect (bindsF g) (bindsF g') = empty
            -> ~ (in_envF a g) -> ~ (in_envF a g') 
            -> isMono t_a -> noExists t_a -> isLCT t_a
            -> Subset (free t_a) (vbindsF g)
            -> Subset (freeTV t_a) (tvbindsF g)
            -> WFFT g (erase t_a) k_a -> WFFE g 
            -> PredicatesHaveBoolType (concatF g (fesubFV a (erase t_a) g')) (psubFTV a t_a ps).
Proof. intros; apply lem_subst_tv_pftyp' with (concatF (FConsT a k_a g) g') k_a;
  trivial. Qed.