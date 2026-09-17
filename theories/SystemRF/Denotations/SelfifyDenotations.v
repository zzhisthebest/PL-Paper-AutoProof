Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.Semantics.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.PrimitivesFTyping.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.Typing.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsSubstitution.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SubstitutionLemmaWF.
Require Import AutoProof.SystemRF.SystemRF.LemmasTransitive.
Require Import AutoProof.SystemRF.Denotations.ClosingSubstitutions.
Require Import AutoProof.SystemRF.Denotations.Denotations.
Require Import AutoProof.SystemRF.Denotations.BasicPropsCSubst.
Require Import AutoProof.SystemRF.Denotations.PrimitivesSemantics.
Require Import AutoProof.SystemRF.Denotations.PrimitivesDenotations.

Require Import ZArith.

Lemma lem_denotations_selfify' : forall (n:nat) (g:env) (t:type) (k:kind) (v:expr),
    depth t <= n -> WFtype g t k -> g = Empty 
        -> HasFtype FEmpty v (erase t) -> isValue v
        -> Denotes t v -> Denotes (self t v k) v.
Proof. induction n.
  - (* n = 0 => TRefn *) intros; 
    assert (depth t = 0) by auto with *.
    destruct t; simpl in H5; try discriminate;
    clear H H5; subst g;
    destruct k; simpl; simpl in H2.
    * (* k = Base *) rewrite Denotes_equation_1.
      unfold psubBV; simpl; inversion H4; destruct H1;    
      simpl in H1; repeat split; try apply PECons;
      try assumption.
      apply lem_ftyp_islc in H1 as Hv; rewrite lem_subBV_lc; 
      try apply Hv.
      assert (isConcreteBasic b) as Hb
        by (destruct b; inversion H0; simpl in H8; inversion H8; 
            try simpl in H14; try contradiction; trivial).
      destruct b eqn:B; simpl in Hb; try contradiction.
      + (* Bool *) assert (isBool v)
          by (apply lem_den_bools with (TRefn TBool ps); simpl; trivial);
        destruct v eqn:V; try contradiction.
        assert (true = Bool.eqb b0 b0) by (destruct b0; reflexivity);
        rewrite H7; apply lemma_eql_bool_semantics; apply Refl.
      + (* Int *) assert (isInt v)
          by (apply lem_den_ints with (TRefn TInt ps); simpl; trivial);
        destruct v eqn:V; try contradiction.
        assert ((Z.eqb n n) = true) by (apply Z.eqb_eq; reflexivity);
        rewrite <- H7; apply lemma_eql_int_semantics; apply Refl.
    * (* k = Star *) apply H4.
  - (* n > 0 *) intros; subst g; destruct t.
    * (* TRefn *) apply IHn with Empty; simpl in H2;
      simpl; auto with *. 
    * (* TFunc *) destruct k; simpl; apply H4.
    * (* TExis *) destruct k.
      + (* Base *) simpl; rewrite Denotes_equation_3; simpl; 
        rewrite lem_erase_self; repeat split; try assumption.
        rewrite Denotes_equation_3 in H4; simpl in H4;
        clear H2 H3; destruct H4; destruct H2.
        destruct H3 as [v_x H3]; exists v_x;
        repeat split; destruct H3; destruct H4;
        try rewrite lem_tsubBV_self; try apply IHn with Empty;
        simpl in H; apply Nat.succ_le_mono in H;
        try rewrite depth_tsubBV;
        try apply Nat.le_trans with (max (depth t1) (depth t2));
        try apply Nat.le_max_r;
        try rewrite lem_erase_tsubBV;
        try apply lem_ftyp_islc with FEmpty (erase t2);
        inversion H0; try apply H5;
        pose proof (fresh_not_elem (union nms (free t2))); 
        set (y := fresh (union (nms) (free t2))) in H12;        
        try rewrite lem_tsubFV_unbindT with y v_x t2;
        apply lem_den_hasftype in H4 as H13;
        try apply lem_subst_wf_top with t1;
        apply not_elem_union_elim in H12; destruct H12;
        try apply H11; simpl; auto. 
      + (* Star *) simpl; apply H4.
    * (* TPoly *) destruct k; simpl; apply H4.
Qed.

Lemma lem_denotations_selfify : forall (t:type) (k:kind) (v:expr),
    WFtype Empty t k -> HasFtype FEmpty v (erase t) -> isValue v
        -> Denotes t v -> Denotes (self t v k) v.
Proof. intros t k v p_emp_t. 
  apply lem_denotations_selfify' with (depth t) Empty; trivial. Qed.
