Require Import Arith.

Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsSubstitution.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.Typing.
Require Import AutoProof.SystemRF.SystemRF.LemmasWeakenWF.
Require Import AutoProof.SystemRF.SystemRF.LemmasWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SubstitutionLemmaWF.
Require Import AutoProof.SystemRF.SystemRF.LemmasTyping.
Require Import AutoProof.SystemRF.SystemRF.LemmasWeakenTyp.
Require Import AutoProof.SystemRF.SystemRF.SubstitutionLemmaTyp.
Require Import AutoProof.SystemRF.SystemRF.LemmasNarrowing.

(* Idea: We have to prove the Transitive Subtyping Lemma by induction on 
      the combined depth of the types involved *)

Fixpoint depth (t : type) : nat :=
    match t with
    | (TRefn b ps)    => 0
    | (TFunc tx t')   => 1 + max (depth tx) (depth t')
    | (TExists tx t') => 1 + max (depth tx) (depth t')
    | (TPoly k t')    => 1 + depth t'
    end.

Lemma depth_tsubBV_at : forall (j:index) (v:expr) (t:type),
    depth (tsubBV_at j v t) = depth t.
Proof. intros j v t; revert v; revert j; induction t; intros;
  simpl; reflexivity || f_equal; apply IHt || f_equal;
  try apply IHt1; try apply IHt2. Qed.

Lemma depth_tsubBV : forall (v:expr) (t:type),
    depth (tsubBV v t) = depth t.
Proof. intros; apply depth_tsubBV_at. Qed.

Lemma depth_open_tvT_at : forall (j:index) (a:var_name) (t:type),
    depth (open_tvT_at j a t) = depth t.
Proof. intros j a t; revert j; induction t; intros;
  simpl; try destruct b; try destruct (Nat.eqb j i); 
  reflexivity || f_equal; apply IHt || f_equal;
  try apply IHt1; try apply IHt2; apply H. Qed.

Lemma depth_unbind_tvT : forall (a:var_name) (t:type),
    depth (unbind_tvT a t) = depth t.
Proof. intros; apply depth_open_tvT_at; assumption. Qed.

Lemma depth_unbindT : forall (y:var_name) (t:type),
    depth (unbindT y t) = depth t.
Proof. intros; rewrite lem_unbindT_is_tsubBV; 
  apply depth_tsubBV_at; simpl; trivial. Qed.

Lemma lem_sub_trans' : forall (n:nat) (g:env) (t t' t'':type) (k k' k'':kind),
    depth t + depth t' + depth t'' <= n
                    -> WFEnv g -> WFtype g t k 
                    -> WFtype g t' k' -> WFtype g t'' k'' 
                    -> Subtype g t t' -> Subtype g t' t'' 
                    -> Subtype g t t''.
Proof. intros n; induction n.
  - (* Base *) intros; assert (depth t + depth t' + depth t'' = 0) 
      by auto with *.
    repeat (apply Nat.eq_add_0 in H6; destruct H6);
    destruct t;   simpl in H6; try discriminate H6;
    destruct t';  simpl in H8; try discriminate H8;
    destruct t''; simpl in H7; try discriminate H7;
    inversion H4; inversion H5; subst b0; subst b1;
    apply SBase with (union nms nms0); intros;
    apply not_elem_union_elim in H13; destruct H13;
    apply ITrans with (unbindP y ps0); apply H11 || apply H17; trivial.
  - (* Inductive *) intros; inversion H4; inversion H5;
    try (subst t'; discriminate);
    (* -ANY- SWitn *) try ( rewrite H9 || rewrite H8;
      apply SWitn with v_x; trivial;
      apply IHn with t' k k' k''; try rewrite depth_tsubBV;
      subst t''; simpl in H;
      repeat rewrite <- plus_n_Sm in H; rewrite <- Nat.succ_le_mono in H;
      assert (depth t'0 <= max (depth t_x) (depth t'0)) 
        as Hdep by apply Nat.le_max_r;
      apply Nat.add_le_mono_l with (depth t'0) (max (depth t_x) (depth t'0))
                                  (depth t + depth t') in Hdep;
      try apply Nat.le_trans with (depth t + depth t' + Init.Nat.max (depth t_x) 
                                                                 (depth t'0));
      trivial; inversion H3; 
      try inversion H16; try inversion H15; try apply WFKind;
      pose proof (fresh_var_not_elem (union nms nms0) g) as Hy;
      set (y := fresh_var (union nms nms0) g) in Hy; destruct Hy as [Hy Hy'];
      apply not_elem_union_elim in Hy; destruct Hy;  
      try rewrite lem_tsubFV_unbindT with y v_x t'0;
      try apply lem_subst_wf_top with t_x;
      try apply lem_typing_hasftype;
      pose proof (lem_free_bound_in_env g (TExists t_x t'0) k'' y H3 Hy') as Hfr;
      simpl in Hfr; destruct Hfr as [Hfr _];
      apply not_elem_union_elim in Hfr as [_ Hfr]; 
      try apply wfenv_unique; simpl; intuition );
    (* SBind -ANY- *) try ( subst t; try set (nms0 := g1); inversion H1; try inversion H9; 
      apply SBind with (union (union nms nms1) (binds g));
      try apply lem_wftype_islct with g k''; try (subst t''; assumption);
      intros y Hy; apply IHn with t' k k' k'';
      try rewrite H16; try rewrite H15; try rewrite H14;
      try rewrite depth_unbindT; subst t; simpl in H;
      rewrite <- Nat.succ_le_mono in H;
      assert (depth t0 <= max (depth t_x) (depth t0)) 
        as Hdep by apply Nat.le_max_r;
      apply Nat.add_le_mono_r with (depth t0) (max (depth t_x) (depth t0))
                                  (depth t' + depth t'') in Hdep;
      repeat rewrite Nat.add_assoc in Hdep;
      try apply Nat.le_trans with (max (depth t_x) (depth t0) + depth t' + depth t'');
      trivial; try apply WFEBind with k_x;
      try apply H19; try apply H20; try apply H21;
      try (destruct k; apply H23 || (apply WFKind; apply H23)); 
      try (destruct k; apply H24 || (apply WFKind; apply H24)); 
      try (destruct k; apply H25 || (apply WFKind; apply H25));
      try apply lem_weaken_wf_top;
      try apply H7; try apply lem_weaken_subtype_top with k' k'';
      apply not_elem_union_elim in Hy; destruct Hy as [Hy Hg];
      apply not_elem_union_elim in Hy; destruct Hy as [Hy Hy1];
      try apply wfenv_unique; trivial).
    * (* SBase SBase *) subst t'; injection H12 as Hb0 Hp0;
      subst b0; subst p0; apply SBase with (union nms nms0); 
      intros; apply not_elem_union_elim in H9; destruct H9;
      apply ITrans with (unbindP y p2); apply H6 || apply H10; trivial.
    * (* SFunc SFunc *) 
      subst t; subst t'; subst t''; inversion H1; try inversion H9;
      subst k; subst g1; subst t_x; subst t;
      inversion H2; try inversion H9;
      subst k'; subst g1; subst t_x; subst t;
      inversion H3; try inversion H9;
      subst k''; subst g1; subst t_x; subst t;  
      simpl in H; rewrite <- Nat.succ_le_mono in H;
      injection H14 as Hs2 Ht2; subst s0; subst t0;
      apply SFunc with (union (union (union (union (union nms nms0) 
                                                    nms1) nms2) nms3) (binds g));
      assert (Subtype g s3 s1) as p_s3_s1
      (* s3 <: s2 <: s1 *) by (apply IHn with s2 k_x1 k_x0 k_x;
        try rewrite Nat.add_comm; try rewrite (Nat.add_comm (depth s3) (depth s2));
        try rewrite Nat.add_assoc;
        assert (depth s1 <= max (depth s1) (depth t1)) 
          as Hdep1 by apply Nat.le_max_l;
        assert (depth s2 <= max (depth s2) (depth t2)) 
          as Hdep2 by apply Nat.le_max_l;
        assert (depth s3 <= max (depth s3) (depth t3)) 
          as Hdep3 by apply Nat.le_max_l;
        repeat rewrite <- plus_n_Sm in H; simpl in H; 
        apply Nat.lt_le_incl in H; apply Nat.lt_le_incl in H;
        assert (depth s1 + depth s2 + depth s3 <=
                  max (depth s1) (depth t1) + max (depth s2) (depth t2) +
                  max (depth s3) (depth t3)) as H'
          by (apply Nat.add_le_mono; try apply Nat.add_le_mono; trivial);
        try apply Nat.le_trans with (max (depth s1) (depth t1) + max (depth s2) (depth t2) +
                                 max (depth s3) (depth t3)); trivial ). apply p_s3_s1.
      + (* t1 <: t2 <: t3 *) intros; apply IHn with (unbindT y t2) k0 k k1;
        try (rewrite depth_unbindT; repeat rewrite depth_unbindT);
        assert (depth t1 <= max (depth s1) (depth t1)) 
          as Hdep1 by apply Nat.le_max_r;
        assert (depth t2 <= max (depth s2) (depth t2)) 
          as Hdep2 by apply Nat.le_max_r;
        assert (depth t3 <= max (depth s3) (depth t3)) 
          as Hdep3 by apply Nat.le_max_r;
        repeat rewrite <- plus_n_Sm in H; simpl in H; 
        apply Nat.lt_le_incl in H; apply Nat.lt_le_incl in H;
        assert (depth t1 + depth t2 + depth t3 <=
                  max (depth s1) (depth t1) + max (depth s2) (depth t2) +
                  max (depth s3) (depth t3)) as H'
          by (apply Nat.add_le_mono; try apply Nat.add_le_mono; trivial);
        try apply Nat.le_trans with (max (depth s1) (depth t1) + max (depth s2) (depth t2) +
                                 max (depth s3) (depth t3)); 
        try apply WFEBind with k_x1; try apply H24;
        try apply H12;
        try apply lem_narrow_subtype_top with s2 k_x1 k_x0 k0 k;
        try apply H7; 
        try apply lem_narrow_wf_top with s2; try apply H21;
        try apply lem_narrow_wf_top with s1; try apply H18;
        repeat (apply not_elem_union_elim in H9; destruct H9);
        try apply wfenv_unique; trivial. 
    * (* -ANY- SWitn *)  apply SWitn with v_x0; trivial;
      apply IHn with t' k k' k''; try rewrite depth_tsubBV;
      subst t''; simpl in H;
      repeat rewrite <- plus_n_Sm in H; rewrite <- Nat.succ_le_mono in H;
      assert (depth t'1 <= max (depth t_x0) (depth t'1)) 
        as Hdep by apply Nat.le_max_r;
      apply Nat.add_le_mono_l with (depth t'1) (max (depth t_x0) (depth t'1))
                                  (depth t + depth t') in Hdep;
      try apply Nat.le_trans with (depth t + depth t' + max (depth t_x0) 
                                                        (depth t'1));
      trivial; inversion H3;
      try inversion H17; try apply WFKind;
      pose proof (fresh_var_not_elem nms g) as Hy;
      set (y := fresh_var nms g) in Hy; destruct Hy as [Hy Hy'];
      try rewrite lem_tsubFV_unbindT with y v_x0 t'1;
      try apply lem_subst_wf_top with t_x0;
      try apply lem_typing_hasftype;
      pose proof (lem_free_bound_in_env g (TExists t_x0 t'1) k'' y H3 Hy') as Hfr;
      simpl in Hfr; destruct Hfr as [Hfr _];
      apply not_elem_union_elim in Hfr as [_ Hfr]; 
      try apply wfenv_unique; simpl; intuition.
    * (* SWitn SBind *) apply IHn with (tsubBV v_x t'0) k k' k'';
      try rewrite depth_tsubBV; subst t'; simpl in H;
      rewrite <- plus_n_Sm in H; simpl in H; rewrite <- Nat.succ_le_mono in H;
      assert (depth t'0 <= max (depth t_x) (depth t'0)) 
        as Hdep by apply Nat.le_max_r;
      apply Nat.add_le_mono_l with (depth t'0) (max (depth t_x) (depth t'0))
                                  (depth t) in Hdep;
      apply Nat.add_le_mono_r with (depth t + depth t'0) 
                                  (depth t + max (depth t_x) (depth t'0))
                                  (depth t'') in Hdep;
      try apply Nat.le_trans with (depth t + max (depth t_x) (depth t'0) + depth t'');
      trivial; inversion H2; try inversion H11;
      injection H15 as Htx0 Ht1; subst t_x0; subst t1;
      pose proof (fresh_var_not_elem (union nms nms0) g) as Hy;
      set (y := fresh_var (union nms nms0) g) in Hy; destruct Hy as [Hy Hy'];
      apply not_elem_union_elim in Hy; destruct Hy;  
      rewrite lem_tsubFV_unbindT with y v_x t'0;
      try apply lem_subst_wf_top with t_x; try apply WFKind;
      try apply H21; try apply H25;
      assert (t'' = tsubFV y v_x t'') as Ht''
        by (symmetry; apply lem_subFV_notin; 
            try apply lem_free_bound_in_env with g k''; trivial);
      try rewrite Ht''; try apply lem_subst_subtype_top with t_x k' k'';
      try apply H13; try apply H21;
      try (apply lem_weaken_wf_top; assumption);
      pose proof (lem_free_bound_in_env g (TExists t_x t'0) k' y H2 Hy') as Hfr;
      simpl in Hfr; destruct Hfr as [Hfr _];
      apply not_elem_union_elim in Hfr as [_ Hfr]; 
      try apply wfenv_unique; try apply lem_typing_hasftype;
      destruct k'; try apply WFKind; try apply H25; trivial.
    * (* SPoly SPoly *) subst t'; injection H12 as Hk0 Ht0;
      subst k0; subst t0; subst t; subst t'';
      inversion H1; try inversion H8;
      inversion H2; try inversion H16;
      inversion H3; try inversion H22;
      apply SPoly 
        with (union (union (union (union (union nms nms0) nms1) nms2) nms3) (binds g));
      intros; repeat (apply not_elem_union_elim in H28; destruct H28);
      apply IHn with (unbind_tvT a t2) k k' k''; subst k k' k'';
      try (rewrite depth_unbind_tvT; repeat rewrite depth_unbind_tvT);
      simpl in H; repeat rewrite <- plus_n_Sm in H;
      rewrite <- Nat.succ_le_mono in H;
      apply Nat.lt_le_incl in H; simpl in H; apply Nat.lt_le_incl in H; try apply H;
      try apply WFEBindT;
      try apply H6; try apply H10;
      destruct k_t;  try (apply H14 || (apply WFKind; apply H14));
      destruct k_t0; try (apply H20 || (apply WFKind; apply H20));
      destruct k_t1; try (apply H26 || (apply WFKind; apply H26));
      try apply wfenv_unique; trivial.
  Qed.
  
Lemma lem_sub_trans : forall (g:env) (t t' t'':type) (k k' k'':kind),
    WFEnv g -> WFtype g t k -> WFtype g t' k' -> WFtype g t'' k'' 
            -> Subtype g t t' -> Subtype g t' t'' 
            -> Subtype g t t''.
Proof. intros; 
  apply lem_sub_trans' with (depth t + depth t' + depth t'') t' k k' k'';
  trivial. Qed.