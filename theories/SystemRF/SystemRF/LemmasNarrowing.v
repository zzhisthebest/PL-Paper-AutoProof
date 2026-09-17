Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsSubstitution.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.Typing.
Require Import AutoProof.SystemRF.SystemRF.LemmasWeakenWF.
Require Import AutoProof.SystemRF.SystemRF.LemmasWeakenWFTV.
Require Import AutoProof.SystemRF.SystemRF.LemmasWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SubstitutionLemmaWF.
Require Import AutoProof.SystemRF.SystemRF.LemmasTyping.
Require Import AutoProof.SystemRF.SystemRF.LemmasSubtyping.
Require Import AutoProof.SystemRF.SystemRF.LemmasWeakenTyp.
Require Import AutoProof.SystemRF.SystemRF.LemmasWeakenTypTV.
Require Import AutoProof.SystemRF.SystemRF.LemmasExactness. 

Lemma lem_narrow_typ' : ( forall (g'xg : env) (e : expr) (t : type),
    Hastype g'xg e t -> ( forall (g g':env) (x:var_name) (s_x t_x:type) (k_sx k_tx:kind),
        g'xg = concatE (Cons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x 
            -> WFEnv (concatE (Cons x s_x g) g')
            -> Hastype (concatE (Cons x s_x g) g') e t )) /\ (
  forall (g'xg : env) (t : type) (t' : type),
    Subtype g'xg t t' -> ( forall (g g':env) (x:var_name) (s_x t_x:type) (k_sx k_tx k_t k_t':kind),
      g'xg = concatE (Cons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x 
            -> WFEnv (concatE (Cons x s_x g) g')
            -> WFtype (concatE (Cons x s_x g) g') t  k_t
            -> WFtype (concatE (Cons x s_x g) g') t' k_t'
            -> Subtype (concatE (Cons x s_x g) g') t t' )).
Proof. apply ( judgments_mutind 
  (fun (g'xg : env) (e : expr) (t : type) (p_e_t : Hastype g'xg e t) => 
    forall (g g':env) (x:var_name) (s_x t_x:type) (k_sx k_tx:kind),
      g'xg = concatE (Cons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x 
            -> WFEnv (concatE (Cons x s_x g) g')
            -> Hastype (concatE (Cons x s_x g) g') e t )
  (fun (g'xg : env) (t : type) (t' : type) (p_t_t' : Subtype g'xg t t') => 
    forall (g g':env) (x:var_name) (s_x t_x:type) (k_sx k_tx k_t k_t':kind),
      g'xg = concatE (Cons x t_x g) g' 
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x 
            -> WFEnv (concatE (Cons x s_x g) g')
            -> WFtype (concatE (Cons x s_x g) g') t  k_t
            -> WFtype (concatE (Cons x s_x g) g') t' k_t'            
            -> Subtype (concatE (Cons x s_x g) g') t t' ));
  intro env; intros; subst env.
  - (* T_BC *) apply T_BC.
  - (* T_IC *) apply T_IC.
  - (* T_Var *) 
    apply lem_truncate_wfenv in H8 as H8'; inversion H8'; subst;
    apply lem_boundin_concat in b; destruct b;
    try destruct H; try destruct H.
    * (* x = x0 *) subst x0; subst T; 
      apply T_Sub with (self s_x (FV x) k) k;
      try apply T_Var; try (apply lem_boundin_concat; left);
      try apply lem_weaken_many_subtype with k(*_sx*) k(*_tx*);
      try apply lem_selfify_wf;
      try apply lem_weaken_many_wf;
      
      try apply lem_exact_subtype with k_sx;
      try apply lem_weaken_subtype_top with k_sx k_tx;
      try (apply lem_weaken_wf_top; assumption);
      try apply WFEBind with k_sx; 
      try rewrite lem_erase_concat; simpl;
      try rewrite lem_erase_subtype with g s_x t_x;
      try apply FTVar; try apply lem_boundinF_concatF;
      try apply intersect_names_add_intro_l; 
      unfold isLC; simpl;  auto;
      (* WFtype of s_x and t_x, possibly with other kinds *)
      apply lem_weaken_wf_top with g s_x k_sx x s_x in H5 as Hsx;
      apply lem_weaken_wf_top with g t_x k_tx x s_x in H6 as Htx; trivial;
      destruct k eqn:K; destruct k_sx eqn:KSX; destruct k_tx eqn:KTX;
      try assumption; try (apply WFKind; assumption);
      (* k_sx = Star but k_tx = Base and k = Base *)
      try ( apply lem_sub_pullback_wftype with t_x;
            try apply lem_weaken_subtype_top with Star Base; 
            try apply WFEBind with Star; trivial; reflexivity  );
      (* k_tx = Star but k_sx = Base and k = Base *)
      try ( apply lem_strengthen_many_wftype_base with g';
            try apply lem_narrow_wf with t_x;
            try apply intersect_names_add_intro_l; 
            unfold unique; auto; reflexivity );
      (* k_sx = Star and k_tx = Star but k = Base *)
      try apply lem_sub_pullback_wftype with t_x;
      try apply lem_strengthen_many_wftype_base with g'; 
      try apply lem_narrow_wf with t_x;
      try apply lem_weaken_subtype_top with Star Star; 
      try apply intersect_names_add_intro_l; 
      unfold unique; auto.
    * (* x in g  *) apply T_Var; try apply lem_boundin_concat; simpl;
      try (left; right; apply H); apply lem_narrow_wf with t_x; assumption. 
    * (* x in g' *) apply T_Var; try apply lem_boundin_concat; simpl;
      try (right; apply H); apply lem_narrow_wf with t_x; assumption.
  - (* T_Prm *) apply T_Prm.
  - (* T_Abs *) apply T_Abs with k (names_add x (union nms (binds (concatE g g')))); 
    try apply lem_narrow_wf with t_x; trivial; intros;
    apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H10; destruct H10;
    apply not_elem_concat_elim in H11; destruct H11;
    assert (Cons y T1 (concatE (Cons x s_x g) g') = concatE (Cons x s_x g) (Cons y T1 g'))
      as Henv by reflexivity; rewrite Henv; 
    apply H with t_x k_sx k_tx; 
    try apply WFEBind with k;
    try apply lem_narrow_wf with t_x;
    try apply intersect_names_add_intro_r;  
    try apply not_elem_names_add_intro;
    pose proof (lem_binds_concat (Cons x s_x g) g') as Hc;
    destruct Hc; try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds (Cons x s_x g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; simpl; auto. 
  - (* T_App *) apply T_App;
    apply H with t_x k_sx k_tx || apply H0 with t_x k_sx k_tx; trivial.
  - (* T_AbsT *) apply T_AbsT with (names_add x (union nms (binds (concatE g g')))); intros;
    apply not_elem_names_add_elim in H0; destruct H0;
    apply not_elem_union_elim in H10; destruct H10;
    apply not_elem_concat_elim in H11; destruct H11;
    assert (ConsT a' k (concatE (Cons x s_x g) g') = concatE (Cons x s_x g) (ConsT a' k g'))
      as Henv by reflexivity; rewrite Henv; 
    apply H with t_x k_sx k_tx; try apply WFEBindT;
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro; 
    pose proof (lem_binds_concat (Cons x s_x g) g') as Hc;
    destruct Hc; try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds (Cons x s_x g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; simpl; auto.
  - (* T_AppT *) apply T_AppT with k; try apply H with t_x k_sx k_tx; 
    try apply lem_narrow_wf with t_x; trivial.
  - (* T_Let *) apply T_Let with T1 k (names_add x (union nms (binds (concatE g g'))));
    try apply lem_narrow_wf with t_x;  
    try apply H with t_x k_sx k_tx; trivial; intros;
    apply not_elem_names_add_elim in H1; destruct H1;
    apply not_elem_union_elim in H11; destruct H11;
    apply not_elem_concat_elim in H12; destruct H12;
    assert (Cons y T1 (concatE (Cons x s_x g) g') = concatE (Cons x s_x g) (Cons y T1 g'))
      as Henv by reflexivity; rewrite Henv; 
    apply H0 with t_x k_sx k_tx; 
    try apply WFEBind with Star;
    try apply lem_typing_wf with t1;
    try apply H with t_x k_sx k_tx; 
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro; 
    pose proof (lem_binds_concat (Cons x s_x g) g') as Hc;
    destruct Hc; try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds (Cons x s_x g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; simpl; auto.    
  - (* T_Ann *) apply T_Ann; try apply H with t_x k_sx k_tx; trivial.
  - (* T_If *) apply T_If with ps k (names_add x (union nms (binds (concatE g g'))));
    try apply H with t_x k_sx k_tx; 
    try apply lem_narrow_wf with t_x; intros;
    try apply not_elem_names_add_elim in H2; try destruct H2;
    try apply not_elem_union_elim in H12; try destruct H12;
    try apply not_elem_concat_elim in H13; try destruct H13;
    try assert (Cons y (self (TRefn TBool ps) (Bool_constant true) Base) (concatE (Cons x s_x g) g') 
                  = concatE (Cons x s_x g) (Cons y (self (TRefn TBool ps) (Bool_constant true) Base) g'))
      as Henv1 by reflexivity; try rewrite Henv1; 
    try assert (Cons y (self (TRefn TBool ps) (Bool_constant false) Base) (concatE (Cons x s_x g) g') 
                  = concatE (Cons x s_x g) (Cons y (self (TRefn TBool ps) (Bool_constant false) Base) g'))
      as Henv2 by reflexivity; try rewrite Henv2;     
    apply H with g g' x s_x t_x k_sx k_tx in H11 as H';
    try apply lem_typing_wf in H';  
    try apply H0 with y t_x k_sx k_tx; try apply H1 with y t_x k_sx k_tx;
    try apply WFEBind with Base;
    try apply lem_selfify_wf; try apply FTBC;
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro;
    pose proof (lem_binds_concat (Cons x s_x g) g') as Hc;
    try destruct Hc; try apply not_elem_names_add_intro; trivial;
    try apply not_elem_subset with (union (binds (Cons x s_x g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; 
    simpl; try discriminate; try split; auto;
    inversion H'; assumption.
  - (* T_Sub *) apply T_Sub with T1 k;
    try apply H0 with t_x k_sx k_tx Star k; 
    try apply lem_typing_wf with t;
    try apply H with t_x k_sx k_tx;
    try apply lem_narrow_wf with t_x; trivial.
  - (* SBase *) try apply SBase with (names_add x (union nms (binds (concatE g g')))); 
    apply lem_truncate_wfenv in H8 as H8'; inversion H8'; subst x0 t g0;
    intros; assert (Cons y (TRefn b PEmpty) (concatE (Cons x s_x g) g') 
                      = concatE (Cons x s_x g) (Cons y (TRefn b PEmpty) g'))
      as Henv by reflexivity; rewrite Henv;
    apply not_elem_names_add_elim in H; destruct H;
    apply not_elem_union_elim in H11; destruct H11;
    apply not_elem_concat_elim in H12; destruct H12;
    apply INarrow with t_x k_sx k_tx; try apply i;
    try apply intersect_names_add_intro_r; try apply not_elem_names_add_intro;
    simpl; intuition.
  - (* SFunc *) inversion H11; try inversion H1;
    inversion H12; try inversion H19;
    apply SFunc 
      with (names_add x (union (union nms0 nms1) (union nms (binds (concatE g g')))));
    try apply H with t_x k_sx k_tx k_x0 k_x; trivial; intros;
    apply not_elem_names_add_elim in H26; destruct H26;
    apply not_elem_union_elim in H27; destruct H27;
    apply not_elem_union_elim in H27; destruct H27;
    apply not_elem_union_elim in H28; destruct H28;
    apply not_elem_concat_elim in H30; destruct H30;
    assert (Cons y s2 (concatE (Cons x s_x g) g') = concatE (Cons x s_x g) (Cons y s2 g'))
      as Henv by reflexivity; rewrite Henv;
    apply H0 with t_x k_sx k_tx k k0;
    try apply WFEBind with k_x0; 
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro; simpl; auto;
    try apply lem_narrow_wf_top with s1;
    try apply H with t_x k_sx k_tx k_x0 k_x; 
    pose proof (lem_binds_concat (Cons x s_x g) g') as Hc;
    try destruct Hc; trivial;
    try apply not_elem_subset with (union (binds (Cons x s_x g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; 
    try apply unique_concat;
    try apply intersect_names_add_intro_l;
    try split; simpl; auto.
  - (* SWitn *) apply SWitn with v_x;
    try apply H with t_x0 k_sx k_tx;
    try apply H0 with t_x0 k_sx k_tx k_t k_t'; trivial.
    inversion H12; try inversion H1;
    pose proof (fresh_varT_not_elem nms (concatE (Cons x s_x g) g') t') as Hy; 
    set (y := fresh_varT nms (concatE (Cons x s_x g) g') t') in Hy; 
    destruct Hy as [Hyt' [_ [Hy Henv]]];
    rewrite lem_tsubFV_unbindT with y v_x t';
    try apply lem_subst_wf_top with t_x;
    try apply H17; try apply WFKind; try apply H21;
    try apply lem_typ_islc with g t_x0; 
    try apply lem_typing_hasftype;
    try apply H with t_x0 k_sx k_tx;
    try apply unique_concat; 
    try apply intersect_names_add_intro_l;
    simpl; try split; trivial.
  - (* SBind *) inversion H10; try inversion H0; subst t0 k g0; simpl;
    apply SBind with (names_add x (union (union nms nms0) (binds (concatE g g'))));
    trivial; intros; apply not_elem_names_add_elim in H12; destruct H12;
    apply not_elem_union_elim in H13; destruct H13 as [H13 H19]; 
    apply not_elem_union_elim in H13; destruct H13;
    apply not_elem_concat_elim in H19; destruct H19;
    assert (Cons y t_x (concatE (Cons x s_x g) g') = concatE (Cons x s_x g) (Cons y t_x g'))
      as Henv by reflexivity; rewrite Henv;
    apply H with t_x0 k_sx k_tx k_t k_t';
    try apply H16; destruct k_t; 
    try apply WFKind; try apply H20;
    try apply lem_weaken_wf_top;
    try apply WFEBind with k_x;
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro; 
    pose proof (lem_binds_concat (Cons x s_x g) g') as Hbin;
    try destruct Hbin; trivial;
    try apply not_elem_subset with (union (binds (Cons x s_x g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; 
    try apply unique_concat;
    try apply intersect_names_add_intro_l; simpl; auto.
  - (* SPoly *) inversion H10; try inversion H0;
    inversion H11; try inversion H17;
    apply SPoly 
      with (names_add x (union (union nms0 nms1) (union nms (binds (concatE g g')))));
    trivial; intros;
    apply not_elem_names_add_elim in H23; destruct H23;
    apply not_elem_union_elim in H24; destruct H24;
    apply not_elem_union_elim in H24; destruct H24;
    apply not_elem_union_elim in H25; destruct H25;
    apply not_elem_concat_elim in H27; destruct H27;
    assert (ConsT a k (concatE (Cons x s_x g) g') = concatE (Cons x s_x g) (ConsT a k g'))
      as Henv by reflexivity; rewrite Henv;
    apply H with t_x k_sx k_tx k_t0 k_t1;
    try apply WFEBindT;
    try apply intersect_names_add_intro_r; 
    try apply not_elem_names_add_intro; 
    pose proof (lem_binds_concat (Cons x s_x g) g') as Hbin;
    try destruct Hbin; trivial;
    try apply not_elem_subset with (union (binds (Cons x s_x g)) (binds g'));
    try apply not_elem_union_intro;
    try apply not_elem_names_add_intro; 
    try apply unique_concat;
    try apply intersect_names_add_intro_l; simpl; auto.
  Qed.

Lemma lem_narrow_typ : 
  forall (g g':env) (x:var_name) (s_x t_x:type) (k_sx k_tx:kind) (e:expr) (t:type),
    Hastype (concatE (Cons x t_x g) g') e t
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x 
            -> WFEnv (concatE (Cons x s_x g) g')
            -> Hastype (concatE (Cons x s_x g) g') e t .
Proof. intros; pose proof lem_narrow_typ'; destruct H9 as [Htyp Hsub];
  apply Htyp with (concatE (Cons x t_x g) g') t_x k_sx k_tx; trivial. Qed.

Lemma lem_narrow_subtype :
  forall (g g':env) (x:var_name) (s_x t_x:type) (k_sx k_tx:kind) (t t':type) (k_t k_t':kind),
    Subtype (concatE (Cons x t_x g) g') t t'
            -> unique g -> unique g'
            -> intersect (binds g) (binds g') = empty
            -> ~ (in_env x g) -> ~ (in_env x g') 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x
            -> WFEnv (concatE (Cons x s_x g) g')
            -> WFtype (concatE (Cons x s_x g) g') t  k_t
            -> WFtype (concatE (Cons x s_x g) g') t' k_t'
            -> Subtype (concatE (Cons x s_x g) g') t t' .
Proof. intros; pose proof lem_narrow_typ'; destruct H11 as [Htyp Hsub].
  apply Hsub with (concatE (Cons x t_x g) g') t_x k_sx k_tx k_t k_t'; trivial. Qed.

Lemma lem_narrow_typ_top : 
  forall (g:env) (x:var_name) (s_x t_x:type) (k_sx k_tx:kind) (e:expr) (t:type),
    Hastype (Cons x t_x g) e t
            -> unique g -> ~ (in_env x g) 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x -> WFEnv g
            -> Hastype (Cons x s_x g) e t .
Proof. intros; assert (Cons x s_x g = concatE (Cons x s_x g) Empty) by reflexivity;
  rewrite H6; apply lem_narrow_typ with t_x k_sx k_tx; 
  try apply intersect_empty_r; try apply WFEBind with k_sx;
  simpl; intuition. Qed.

Lemma lem_narrow_subtype_top :
  forall (g:env) (x:var_name) (s_x t_x:type) (k_sx k_tx:kind) (t t':type) (k_t k_t':kind),
    Subtype (Cons x t_x g) t t'
            -> unique g -> ~ (in_env x g) 
            -> WFtype g s_x k_sx -> WFtype g t_x k_tx -> Subtype g s_x t_x -> WFEnv g
            -> WFtype  (Cons x s_x g) t  k_t
            -> WFtype  (Cons x s_x g) t' k_t'
            -> Subtype (Cons x s_x g) t  t' .
Proof. intros; assert (Cons x s_x g = concatE (Cons x s_x g) Empty) by reflexivity;
  rewrite H8; apply lem_narrow_subtype with t_x k_sx k_tx k_t k_t'; 
  try apply intersect_empty_r; try apply WFEBind with k_sx;
  simpl; intuition. Qed.
