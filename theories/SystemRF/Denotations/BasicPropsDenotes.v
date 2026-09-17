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
Require Import AutoProof.SystemRF.SystemRF.LemmasWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.LemmasTyping.
Require Import AutoProof.SystemRF.SystemRF.LemmasTransitive.
Require Import AutoProof.SystemRF.Denotations.ClosingSubstitutions.
Require Import AutoProof.SystemRF.Denotations.Denotations.
Require Import AutoProof.SystemRF.Denotations.PrimitivesSemantics.
Require Import AutoProof.SystemRF.Denotations.BasicPropsCSubst.

Require Import Arith.
Require Import Lists.ListSet.

Lemma lem_denotesenv_loc_closed : forall (g:env) (th:csub), 
    DenotesEnv g th -> loc_closed th.
Proof. intros; induction H; simpl; try split; trivial.
  - (* CCons *) apply lem_den_hasftype in H1; 
    apply lem_ftyp_islc in H1; assumption.
  - (* CConsT *) apply lem_wftype_islct in H3; assumption. 
  Qed.

Lemma lem_denotesenv_closed : forall (g:env) (th:csub), 
    DenotesEnv g th -> closed th.
Proof. intros; induction H; simpl; trivial.
  - (* CCons *) apply lem_den_hasftype in H1;
    apply lem_fv_subset_bindsF in H1; repeat split;
    try apply IHDenotesEnv; apply no_elem_empty; intuition.
  - (* CConsT *) apply lem_free_subset_binds in H3; repeat split;
    try apply IHDenotesEnv; apply no_elem_empty; intuition.
  Qed.

Lemma lem_denotesenv_substitutable : forall (g:env) (th:csub), 
    DenotesEnv g th -> substitutable th.
Proof. intros; induction H; simpl; repeat split; trivial.
  apply lem_den_isvalue with (ctsubst th t); apply H1. Qed.

Lemma lem_denotesenv_unique : forall (g:env) (th:csub),
    DenotesEnv g th -> unique g.
Proof. intros g th den_g_th; induction den_g_th; simpl; 
  try split; trivial; unfold in_csubst;
  rewrite <- lem_binds_env_th with g th; trivial. Qed.

Lemma lem_denotesenv_uniqueC : forall (g:env) (th:csub),
    DenotesEnv g th -> uniqueC th.
Proof. intros g th den_g_th; induction den_g_th; simpl; 
  try split; trivial; unfold in_csubst;
  rewrite <- lem_binds_env_th with g th; trivial. Qed.

Lemma lem_bound_in_denotesenv : 
  forall (x:var_name) (t:type) (g:env) (th:csub),
    DenotesEnv g th -> bound_in x t g -> WFEnv g
        -> Denotes (ctsubst th t) (csubst th (FV x)).
Proof. intros x t; induction g.
  - simpl; intuition.
  - intros; inversion H;   subst x1 t1 g0;
    try apply H1;  simpl in H0; destruct H0.
    * (* x = x0 *) destruct H0; subst x0 t0;
      inversion H1; subst x0 t0 g0.
      simpl; destruct (x =? x) eqn:X;
      try apply Nat.eqb_neq in X; try unfold not in X; 
      try contradiction.
      apply lem_free_subset_binds in H10; destruct H10.
      assert (~ In x (free t))
        by (pose proof (vbinds_subset g);
            apply not_elem_subset with (vbinds g);
            try apply not_elem_subset with (binds g); trivial).
      rewrite lem_tsubFV_notin;
      apply lem_den_hasftype in H8 as H11;
      apply lem_fv_subset_bindsF in H11;
      simpl in H11; destruct H11;
      try apply no_elem_empty;
      try rewrite lem_csubst_nofv; 
      try apply no_elem_empty; trivial;
      intros; try apply not_elem_subset with empty.
    * (* x <> x0 *)
      apply boundin_wfenv_wftype in H0 as p_g_t; 
      pose proof (vbinds_subset g);
      assert (x0 <> x)
        by (apply lem_boundin_inenv in H0; 
            unfold in_env in H7; apply H2 in H0;
            unfold not; intros; subst x0; contradiction);
      apply Nat.eqb_neq in H3; simpl; try rewrite H3;
      try rewrite lem_tsubFV_notin;
      try apply lem_free_subset_binds in p_g_t; 
      try destruct p_g_t;
      try apply not_elem_subset with (vbinds g);
      try apply not_elem_subset with (binds g); 
      try apply IHg;
      inversion H1; trivial.
  - intros; simpl in H0;
    apply boundin_wfenv_wftype in H0 as p_g_t; 
    pose proof (tvbinds_subset g);
    try apply lem_free_subset_binds in p_g_t;
    try destruct p_g_t; 
    inversion H; subst a0 k0 g0; simpl;
    try rewrite lem_tsubFTV_notin;
    try apply IHg; 
    try apply not_elem_subset with (tvbinds g);
    try apply not_elem_subset with (binds g);
    inversion H1; trivial.
  Qed.

Lemma lem_tvbinds_denotesenv : 
  forall (a:var_name) (g:env) (th:csub),
    DenotesEnv g th -> substitutable th -> In a (tvbinds g)
        -> exists t_a, noExists t_a /\ WFtype Empty t_a Star 
                                    /\ tv_bound_inC a t_a th.
Proof. intro a; induction g; intros; simpl in H1.
  - contradiction.
  - inversion H; simpl; apply IHg; 
    try apply lem_denotesenv_substitutable with g; trivial.
  - inversion H; subst a1 k0 g0; 
    destruct (a =? a0) eqn:A.
    * apply Nat.eqb_eq in A; subst a0.
      exists t; simpl; repeat split; auto;
      destruct k; apply H10 || apply WFKind; apply H10.
    * apply set_add_elim2 in H1; 
      try apply Nat.eqb_neq; try apply A;
      apply IHg in H5; try apply H1;
      subst th; simpl in H0; destruct H0;
      destruct H2; try apply H3.
      destruct H5 as [t_a [Hta [Hta' Hta'']]];
      exists t_a; simpl; repeat split; auto.
  Qed.

(* Unfortunately, the self operator and tsubFTV do not quite 
   commute with each other, but are entirely semantically 
   equivalent. The next lemma shows that the denotation is
   unaffected (used to prove Denotational Soundness)
*)

Lemma lem_erase_tsubFTV_self :
  forall (a:var_name) (t_a t:type) (v:expr) (k :kind),
    noExists t_a -> erase (self (tsubFTV a t_a t) v k) 
                      = erase (tsubFTV a t_a (self t v k)).
Proof. intros a t_a; induction t; intros v k' H;
  destruct k'; repeat rewrite lem_self_star; trivial;
  try destruct b eqn:B; simpl;
  try destruct (a =? a0) eqn:A; simpl; try reflexivity.
  - (* TRefn Base *) destruct t_a; simpl in H; simpl;
    try contradiction; reflexivity.
  - (* TExists Base *) apply IHt2; apply H.
  Qed.

Lemma lem_denotes_tsubFTV_self' : 
  forall (n:nat) (a:var_name) (t_a t:type) (v v':expr) (k:kind),
    depth t <= n -> noExists t_a -> isLCT t_a -> freeTV t_a = empty
        -> subFTV a t_a v = v -> isLC v
        -> Denotes (self (tsubFTV a t_a t)  v  k) v'
        -> Denotes (tsubFTV a t_a (self t v k)) v'.
Proof. induction n.
  - (* n = 0 => TRefn *) intros; revert H5;
    assert (depth t = 0) by auto with *;
    destruct t; simpl in H5; try discriminate;
    destruct k; try rewrite lem_self_star; trivial. 
    destruct b; simpl; rewrite H3;
    unfold eqlPred; trivial. (* FTV a0 remains*)
    destruct (a =? a0) eqn:A; simpl; 
    unfold eqlPred; trivial.
    (* a = a0*) destruct t_a; simpl in A; try contradiction;
    simpl; trivial; unfold eqlPred.
    repeat rewrite Denotes_equation_1; intuition.
    apply PECons; fold subBV_at; fold psubBV_at;
    inversion H9; try apply H12. 
    destruct (0 =? 0) eqn:Z; simpl in Z; try discriminate;
    destruct b eqn:B; unfold isLCT in H1; simpl in H2;
    try destruct i; try destruct H1; try inversion H1;
    try apply (empty_no_elem (names_add a1 (ftvP ps0))) with a1 in H2;
    try apply not_elem_names_add_elim in H2; try destruct H2; intuition.
    * (* TBool *) 
      apply AddStep with (App (App (Prim Eqv) (subBV_at 0 v' v)) v').
      apply EApp1; apply EApp1; apply lem_step_eql_tbool.
      apply lem_decompose_evals with 
        (App (App (AppT (Prim Eql) (TRefn TBool PEmpty)) (subBV_at 0 v' v)) v');
      trivial; apply lem_step_evals;
      apply EApp1; apply EApp1; apply lem_step_eql_tbool.
    * (* TInt *) 
      apply AddStep with (App (App (Prim Eq) (subBV_at 0 v' v)) v').
      apply EApp1; apply EApp1; apply lem_step_eql_tint.
      apply lem_decompose_evals with 
        (App (App (AppT (Prim Eql) (TRefn TInt PEmpty)) (subBV_at 0 v' v)) v');
      trivial; apply lem_step_evals;
      apply EApp1; apply EApp1; apply lem_step_eql_tint.
  - (* n > 0 *) intros; destruct t.
    * (* TRefn *) apply IHn; revert H5; simpl; auto with *.
    * (* TFunc *) destruct k; simpl; simpl in H5; apply H5.
    * (* TExists *) revert H5; destruct k; simpl; trivial.
      (* Base *) repeat rewrite Denotes_equation_3;
      simpl; rewrite lem_erase_tsubFTV_self; intuition;
      destruct H8 as [v_x H8]; exists v_x; intuition.
      rewrite lem_tsubBV_self in H10; trivial.
      apply lem_den_hasftype in H8 as H9.
      apply lem_fv_subset_bindsF in H9 as H9;
      destruct H9; unfold Subset in H11; simpl in H11;
      assert (subFTV a t_a v_x = v_x)
        by (apply lem_subFTV_notin; unfold not; apply H11). 
      trivial || rewrite <- H12; rewrite <- H12 in H10.
      rewrite <- lem_commute_tsubFTV_tsubBV in H10;
      try rewrite <- lem_commute_tsubFTV_tsubBV;
      try assumption; rewrite lem_tsubBV_self;
      try apply IHn; simpl in H; apply Nat.succ_le_mono in H;
      try rewrite depth_tsubBV;
      try apply Nat.le_trans with (max (depth t1) (depth t2));
      try apply Nat.le_max_r;
      unfold isLC; simpl; trivial.
    * (* TPoly *) destruct k; simpl; simpl in H5; apply H5.
  Qed.
  
Lemma lem_denotes_tsubFTV_self : 
  forall (a:var_name) (t_a t:type) (v v':expr) (k:kind),
    noExists t_a -> isLCT t_a -> freeTV t_a = empty
        -> subFTV a t_a v = v -> isLC v
        -> Denotes (self (tsubFTV a t_a t) v k) v'
        -> Denotes (tsubFTV a t_a (self t v k)) v'.
Proof. intros a t_a t v v' k.
  apply lem_denotes_tsubFTV_self' with (depth t); trivial. Qed.

Lemma lem_denotes_ctsubst_self : 
  forall (th:csub) (t:type) (v v':expr) (k:kind),
    closed th -> loc_closed th -> substitutable th -> uniqueC th 
        -> isLC v -> ftv v = empty
        -> Denotes (self (ctsubst th t) (csubst th v) k) v'
        -> Denotes (ctsubst th (self t v k)) v'.
Proof. induction th; intros t v v' k H1 H2 H3 H4 H5 H6; trivial;
  simpl in H1; simpl in H2; simpl in H3; simpl in H4;
  destruct H1; destruct H0; destruct H2; destruct H3; destruct H4.
  - (* CCons *) simpl; rewrite lem_tsubFV_self; apply IHth; 
    try apply lem_islc_at_subFV; auto with *.
    assert (Subset (ftv (subFV x v_x v)) (union (ftv v) (ftv v_x)))
      by apply ftv_subFV_elim;
    rewrite H0 in H10; rewrite H6 in H10;
    apply no_elem_empty; unfold not; intros;
    apply H10 in H11; intuition. 
  - (* CConsT *) intros;  
    pose proof (matchesExFTV_dec a t) as Hm; destruct Hm.
    * (* Yes *) destruct t eqn:T; try destruct b; remember H11 as H12;
      simpl in H11; try contradiction; try subst a0.
      + rewrite lem_unroll_ctsubst_tv_left;
        try split; destruct H8; trivial;
        rewrite lem_ctsubst_self_FTV with th a (TRefn (FTV a) ps) v k;
        try apply lem_denotes_tsubFTV_self;
        try apply lem_subFTV_notin;
        try apply lem_csubst_isLC;
        assert (ftv (csubst th v) = empty)
          by (apply lem_csubst_pres_noftv; trivial);
        try rewrite H13; simpl; auto.
        rewrite <- lem_unroll_ctsubst_tv_left;
        unfold csubst in H10; fold csubst in H10;
        assert (subFTV a t_a v = v)
          by (apply lem_subFTV_notin; rewrite H6; auto);
          rewrite H14 in H10; try apply H10; intuition.
      + rewrite lem_unroll_ctsubst_tv_left;
        try split; destruct H8; trivial;
        rewrite lem_ctsubst_self_FTV with th a (TExists t0_1 t0_2) v k;
        try apply lem_denotes_tsubFTV_self;
        try apply lem_subFTV_notin;
        try apply lem_csubst_isLC;
        assert (ftv (csubst th v) = empty)
          by (apply lem_csubst_pres_noftv; trivial);
        try rewrite H14;  
        try rewrite <- lem_unroll_ctsubst_tv_left;
        unfold csubst in H10; fold csubst in H10;
        assert (subFTV a t_a v = v)
          by (apply lem_subFTV_notin; rewrite H6; auto);
        try rewrite H15 in H10; 
        try apply H10;
        simpl; auto.
    * (* No *) simpl; rewrite lem_tsubFTV_self_noFTV;
      try apply IHth; simpl in H10; destruct H8;
      assert (subFTV a t_a v = v)
          by (apply lem_subFTV_notin; rewrite H6; auto);
      try apply H10; try rewrite H13; trivial.
  Qed.
