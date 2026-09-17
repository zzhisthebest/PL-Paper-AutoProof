Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions. 
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SystemFLemmasWellFormedness.

(*------------------------------------------------------------------------------
----- | METATHEORY Development for the Underlying System F :: Technical LEMMAS
------------------------------------------------------------------------------*)

Lemma lem_weaken_ftyp' : forall (g'g : fenv) (e : expr) (t : ftype),
    HasFtype g'g e t -> ( forall (g g':fenv) (x:var_name) (t_x:ftype),
        g'g = concatF g g' -> intersect (bindsF g) (bindsF g') = empty
                           -> ~ (in_envF x g) -> ~ (in_envF x g') 
                           -> HasFtype (concatF (FCons x t_x g) g') e t ).
Proof. apply ( HasFtype_ind 
  (fun (g'g : fenv) (e : expr) (t : ftype) => forall (g g':fenv) (x:var_name) (t_x:ftype),
      g'g = concatF g g' -> intersect (bindsF g) (bindsF g') = empty
                         -> ~ (in_envF x g) -> ~ (in_envF x g') 
                         -> HasFtype (concatF (FCons x t_x g) g') e t ));
  intro env; intros.
  - (* FTBC *) apply FTBC.
  - (* FTIC *) apply FTIC.
  - (* FTVar *) apply FTVar; apply lem_boundinF_weaken; subst env; assumption.
  - (* FTPrm *) apply FTPrm.
  - (* FTAbs *) apply FTAbs with k (names_add x (union nms (bindsF env)));
    intros; try apply lem_weaken_wfft; subst env; try assumption.
    assert (FCons y b (concatF (FCons x t_x g) g') = concatF (FCons x t_x g) (FCons y b g'))
      by reflexivity; rewrite H2;
    apply not_elem_names_add_elim in H6; destruct H6; 
    apply not_elem_union_elim in H7; destruct H7;
    apply not_elem_concatF_elim in H8; destruct H8;
    apply H1; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.    
  - (* FTApp *) apply FTApp with b; apply H0 || apply H2; assumption.
  - (* FTAbsT *) apply FTAbsT with (names_add x (union nms (bindsF env)));
    intros; subst env;
    assert (FConsT a' k (concatF (FCons x t_x g) g') = concatF (FCons x t_x g) (FConsT a' k g'))
      by reflexivity; rewrite H1;
    apply not_elem_names_add_elim in H5; destruct H5; 
    apply not_elem_union_elim in H6; destruct H6;
    apply not_elem_concatF_elim in H7; destruct H7;
    apply H0; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.  
  - (* FTAppT*) apply FTAppT with k; subst env;
    try apply H0; try apply lem_weaken_wfft;
    try (apply subset_trans with (vbindsF (concatF g g'));    
         apply lem_vbinds_cons_concatF || assumption);
    try (apply subset_trans with (tvbindsF (concatF g g'));    
         apply lem_tvbinds_cons_concatF || assumption);
    try assumption; try reflexivity.
  - (* FTLet *) apply FTLet with b (names_add x (union nms (bindsF env)));
    try apply H0; try assumption; intros; subst env.
    assert (FCons y b (concatF (FCons x t_x g) g') = concatF (FCons x t_x g) (FCons y b g'))
      by reflexivity; rewrite H3.
    apply not_elem_names_add_elim in H7; destruct H7; 
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concatF_elim in H9; destruct H9.
    apply H2; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.
  - (* FTAnn *) apply FTAnn; try apply H4; subst env;
    try (apply subset_trans with (vbindsF (concatF g g'));    
         apply lem_vbinds_cons_concatF || assumption);
    try (apply subset_trans with (tvbindsF (concatF g g'));    
         apply lem_tvbinds_cons_concatF || assumption);
    try assumption; try reflexivity.
  - (* FTIf *) apply FTIf; apply H0 || apply H2 || apply H4; assumption.
  Qed.

Lemma lem_weaken_ftyp : forall (g g' : fenv) (e : expr) (t : ftype) (x:var_name) (t_x:ftype),
  HasFtype (concatF g g') e t -> intersect (bindsF g) (bindsF g') = empty
                              -> ~ (in_envF x g) -> ~ (in_envF x g') 
                              -> HasFtype (concatF (FCons x t_x g) g') e t.
Proof. intros; apply lem_weaken_ftyp' with (concatF g g'); intuition. Qed.

Lemma lem_weaken_ftyp_top : forall (g : fenv) (e : expr) (t : ftype) (x:var_name) (t_x:ftype),
  HasFtype g e t -> ~ (in_envF x g) -> HasFtype (FCons x t_x g) e t.
Proof. intros; assert (FCons x t_x g = concatF (FCons x t_x g) FEmpty) by reflexivity;
  rewrite H1; apply lem_weaken_ftyp; simpl; try apply intersect_empty_r; intuition. Qed.

Lemma lem_weaken_tv_ftyp' : forall (g'g : fenv) (e : expr) (t : ftype),
    HasFtype g'g e t -> ( forall (g g':fenv) (a:var_name) (k:kind),
        g'g = concatF g g' -> intersect (bindsF g) (bindsF g') = empty
                           -> ~ (in_envF a g) -> ~ (in_envF a g') 
                           -> HasFtype (concatF (FConsT a k g) g') e t ).
Proof. apply ( HasFtype_ind 
  (fun (g'g : fenv) (e : expr) (t : ftype) => forall (g g':fenv) (a:var_name) (k:kind),
      g'g = concatF g g' -> intersect (bindsF g) (bindsF g') = empty
                         -> ~ (in_envF a g) -> ~ (in_envF a g') 
                         -> HasFtype (concatF (FConsT a k g) g') e t ));
  intro env; intros.
  - (* FTBC *) apply FTBC.
  - (* FTIC *) apply FTIC.
  - (* FTVar *) apply FTVar; apply lem_boundinF_weaken_tv; subst env; assumption.
  - (* FTPrm *) apply FTPrm.
  - (* FTAbs *) apply FTAbs with k (names_add a (union nms (bindsF env)));
    intros; try apply lem_weaken_tv_wfft; subst env; try assumption.
    assert (FCons y b (concatF (FConsT a k0 g) g') = concatF (FConsT a k0 g) (FCons y b g'))
      by reflexivity; rewrite H2.
    apply not_elem_names_add_elim in H6; destruct H6; 
    apply not_elem_union_elim in H7; destruct H7;
    apply not_elem_concatF_elim in H8; destruct H8.
    apply H1; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.    
  - (* FTApp *) apply FTApp with b; apply H0 || apply H2; assumption.
  - (* FTAbsT *) apply FTAbsT with (names_add a (union nms (bindsF env)));
    intros; subst env.
    assert (FConsT a' k (concatF (FConsT a k0 g) g') = concatF (FConsT a k0 g) (FConsT a' k g'))
      by reflexivity; rewrite H1;
    apply not_elem_names_add_elim in H5; destruct H5; 
    apply not_elem_union_elim in H6; destruct H6;
    apply not_elem_concatF_elim in H7; destruct H7;
    apply H0; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.  
  - (* FTAppT*) apply FTAppT with k; subst env;
    try apply H0; try apply lem_weaken_tv_wfft;
    try (apply subset_trans with (vbindsF (concatF g g'));    
         apply lem_vbinds_consT_concatF || assumption);
    try (apply subset_trans with (tvbindsF (concatF g g'));    
         apply lem_tvbinds_consT_concatF || assumption);
    try assumption; try reflexivity.
  - (* FTLet *) apply FTLet with b (names_add a (union nms (bindsF env)));
    try apply H0; try assumption; intros; subst env.
    assert (FCons y b (concatF (FConsT a k g) g') = concatF (FConsT a k g) (FCons y b g'))
      by reflexivity; rewrite H3.
    apply not_elem_names_add_elim in H7; destruct H7; 
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concatF_elim in H9; destruct H9.
    apply H2; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; intuition.
  - (* FTAnn *) apply FTAnn; try apply H4; subst env;
    try (apply subset_trans with (vbindsF (concatF g g'));    
         apply lem_vbinds_consT_concatF || assumption);
    try (apply subset_trans with (tvbindsF (concatF g g'));    
         apply lem_tvbinds_consT_concatF || assumption);
    try assumption; try reflexivity.
  - (* If *) apply FTIf; apply H0 || apply H2 || apply H4; assumption.
  Qed.

Lemma lem_weaken_tv_ftyp : forall (g g' : fenv) (e : expr) (t : ftype) (a:var_name) (k:kind),
  HasFtype (concatF g g') e t -> intersect (bindsF g) (bindsF g') = empty
                              -> ~ (in_envF a g) -> ~ (in_envF a g') 
                              -> HasFtype (concatF (FConsT a k g) g') e t.
Proof. intros; apply lem_weaken_tv_ftyp' with (concatF g g'); intuition. Qed.

Lemma lem_weaken_pftyp' : forall (g'g : fenv) (ps : preds),
    PredicatesHaveBoolType g'g ps -> ( forall (g g':fenv) (x:var_name) (t_x:ftype),
        g'g = concatF g g' -> intersect (bindsF g) (bindsF g') = empty
                           -> ~ (in_envF x g) -> ~ (in_envF x g') 
                           -> PredicatesHaveBoolType (concatF (FCons x t_x g) g') ps ).
Proof. apply ( PredicatesHaveBoolType_ind 
  (fun (g'g : fenv) (ps : preds) => forall (g g':fenv) (x:var_name) (t_x:ftype),
      g'g = concatF g g' -> intersect (bindsF g) (bindsF g') = empty
                         -> ~ (in_envF x g) -> ~ (in_envF x g') 
                         -> PredicatesHaveBoolType (concatF (FCons x t_x g) g') ps ));
  intro env; intros.
  - apply PFTEmp.
  - apply PFTCons; subst env; try apply lem_weaken_ftyp;
    try apply H1; intuition.
  Qed.

Lemma lem_weaken_many_ftyp : forall (g g':fenv) (e:expr) (t:ftype),
    HasFtype g e t -> uniqueF g -> uniqueF g'
                   -> intersect (bindsF g) (bindsF g') = empty
                   -> HasFtype (concatF g g') e t.
Proof. intros; induction g'; simpl; try assumption;
  simpl in H1; destruct H1;
  simpl in H2; apply intersect_names_add_elim_r in H2; destruct H2;
  apply IHg' in H2 as H'; try assumption;
  apply lem_weaken_ftyp with (concatF g g') FEmpty e t x t0 in H'
  || apply lem_weaken_tv_ftyp with (concatF g g') FEmpty e t a k in H';
  simpl in H'; unfold in_envF; simpl; 
  try (apply intersect_empty_r);
  try (apply uniqueF_concatF);
  try (apply not_elem_concatF_intro; assumption);  
  intuition. Qed.

Lemma lem_weaken_pftyp : forall (g g' : fenv) (ps : preds) (x:var_name) (t_x:ftype),
  PredicatesHaveBoolType (concatF g g') ps -> intersect (bindsF g) (bindsF g') = empty
                              -> ~ (in_envF x g) -> ~ (in_envF x g') 
                              -> PredicatesHaveBoolType (concatF (FCons x t_x g) g') ps.
Proof. intros; apply lem_weaken_pftyp' with (concatF g g'); intuition. Qed.

Lemma lem_weaken_tv_pftyp' : forall (g'g : fenv) (ps : preds),
    PredicatesHaveBoolType g'g ps -> ( forall (g g':fenv) (a:var_name) (k:kind),
        g'g = concatF g g' -> intersect (bindsF g) (bindsF g') = empty
                           -> ~ (in_envF a g) -> ~ (in_envF a g') 
                           -> PredicatesHaveBoolType (concatF (FConsT a k g) g') ps ).
Proof. apply ( PredicatesHaveBoolType_ind 
  (fun (g'g : fenv) (ps : preds) => forall (g g':fenv) (a:var_name) (k:kind),
      g'g = concatF g g' -> intersect (bindsF g) (bindsF g') = empty
                         -> ~ (in_envF a g) -> ~ (in_envF a g') 
                         -> PredicatesHaveBoolType (concatF (FConsT a k g) g') ps ));
  intro env; intros.
  - apply PFTEmp.
  - apply PFTCons; subst env; try apply lem_weaken_tv_ftyp;
    try apply H1; intuition.
  Qed.

Lemma lem_weaken_tv_pftyp : forall (g g' : fenv) (ps : preds) (a:var_name) (k:kind),
  PredicatesHaveBoolType (concatF g g') ps -> intersect (bindsF g) (bindsF g') = empty
                              -> ~ (in_envF a g) -> ~ (in_envF a g') 
                              -> PredicatesHaveBoolType (concatF (FConsT a k g) g') ps.
Proof. intros; apply lem_weaken_tv_pftyp' with (concatF g g'); intuition. Qed.