Require Import Arith.

Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.SystemFWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsSubstitution.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.SystemFLemmasSubstitution. 
Require Import AutoProof.SystemRF.SystemRF.BasicPropsWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.LemmasWeakenWFTV.
Require Import AutoProof.SystemRF.SystemRF.Typing.
Require Import AutoProof.SystemRF.SystemRF.LemmasWellFormedness.

(* -- -- -- -- -- -- -- -- -- -- -- ---
   -- Part of the Substitution Lemma -- 
   -- -- -- -- -- -- -- -- -- -- -- --- *)

Lemma lem_subst_tv_wf'' : forall (g'ag : env) (t : type) (k_t : kind),
   WFtype g'ag t k_t -> ( forall (g g':env) (a:var_name) (t_a:type) (k_a:kind),
       g'ag = concatE (ConsT a k_a g) g' 
                     -> unique g -> unique g'
                     -> intersect (binds g) (binds g') = empty
                     -> ~ (in_env a g) -> ~ (in_env a g') 
                     -> isMono t_a -> noExists t_a 
                     -> WFtype g t_a k_a -> WFFE (erase_env g)
                     -> WFtype (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k_t ).
Proof. apply ( WFtype_ind 
  (fun (g'ag : env) (t : type) (k_t : kind) => 
    forall (g g' : env) (a : var_name) (t_a : type) (k_a : kind),
        g'ag = concatE (ConsT a k_a g) g' 
              -> unique g -> unique g'
              -> intersect (binds g) (binds g') = empty
              -> ~ (in_env a g) -> ~ (in_env a g') 
              -> isMono t_a -> noExists t_a 
              -> WFtype g t_a k_a -> WFFE (erase_env g)
              -> WFtype (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k_t  )).
  - (* WFBase *) intros; destruct b; simpl;
    (apply WFBase; assumption) || (simpl in H; contradiction).
  - (* WFRefn *) intro env; intros; destruct b eqn:B; simpl; simpl in H0;
    try destruct (a =? a0) eqn:Ha0;
    try apply WFRefn with (names_add a (union nms (binds (concatE g g'))));
    try apply H0 with k_a;
    try (pose proof (H0 g g' a t_a k_a) as H0'; rewrite Ha0 in H0'; apply H0');
    try (destruct ps; simpl; contradiction || discriminate); try assumption;
    (* TBool / TInt / FTV a0 <> a *) try (
      intros; apply not_elem_names_add_elim in H13; try destruct H13;
      apply not_elem_union_elim in H14; try destruct H14;
      apply not_elem_concat_elim in H15; try destruct H15; try subst env;
      assert (FCons y (FTBasic b) (erase_env (concatE g (esubFTV a t_a g')))
            = concatF (erase_env g) (fesubFV a (erase t_a) (FCons y (FTBasic b) (erase_env g'))) ) as Henv
        by (subst b; rewrite lem_erase_concat; rewrite lem_erase_esubFTV; 
            simpl; try rewrite Ha0; reflexivity || assumption); 
      rewrite B in Henv; rewrite Henv;
      rewrite <- lem_commute_psubFTV_unbindP;
      try apply lem_subst_tv_pftyp with k_a;
      assert (concatF (FConsT a k_a (erase_env g)) (FCons y (FTBasic b) (erase_env g'))
            = FCons y (FTBasic b) (erase_env (concatE (ConsT a k_a g) g'))) as Henv'
        by (subst b; rewrite lem_erase_concat; reflexivity); rewrite B in Henv'; try rewrite Henv';
      try apply H2; simpl; try split; try unfold in_envF; simpl;
      try apply unique_erase_env; try rewrite <- binds_erase_env;
      try apply intersect_names_add_intro_r; try rewrite <- binds_erase_env;
      try apply not_elem_names_add_intro; try apply lem_wftype_islct with g k_a;
      try rewrite <- vbinds_erase_env; try rewrite <- tvbinds_erase_env;
      try apply lem_free_subset_binds with k_a;
      try apply lem_erase_wftype;
      apply Nat.neq_sym in H13; try split; trivial
    ).
    * (* FTV a0 *) (* a = a0 *) apply lem_push_wf with (names_add a (union nms (binds (concatE g g')))); 
      try apply H10;
      pose proof (H0 g g' a t_a k_a) as H0'; rewrite Ha0 in H0'; rewrite lem_push_empty in H0';
      try apply H0'; trivial; intros; subst env; apply Nat.eqb_eq in Ha0; subst a0;
      apply not_elem_names_add_elim in H13; destruct H13;
      apply not_elem_union_elim in H13;     destruct H13;
      apply not_elem_concat_elim in H14;    destruct H14.
      apply lem_erase_wftype in H11 as Her;  apply lem_wftype_islct in H11 as Hlc;
      assert (FCons y (erase t_a) (erase_env (concatE g (esubFTV a t_a g')))
          = concatF (erase_env g) (fesubFV a (erase t_a) (FCons y (FTBasic (FTV a)) (erase_env g'))) ) as Henv
        by (  rewrite lem_erase_concat; rewrite lem_erase_esubFTV; simpl; destruct (a =? a) eqn:A;
              try (apply Nat.eqb_neq in A; contradiction);
              reflexivity || assumption ); rewrite Henv.
      rewrite <- lem_commute_psubFTV_unbindP; try apply lem_subst_tv_pftyp with k_a;
      assert (concatF (FConsT a k_a (erase_env g)) (FCons y (FTBasic (FTV a)) (erase_env g'))
            = FCons y (FTBasic (FTV a)) (erase_env (concatE (ConsT a k_a g) g'))) as Henv'
        by (rewrite lem_erase_concat; reflexivity); try rewrite Henv';
      try apply H2;
      try apply intersect_names_add_intro_r; 
      simpl; unfold in_envF; try apply not_elem_names_add_intro; try split;
      try apply unique_erase_env; fold bindsF;
      repeat (try rewrite <- binds_erase_env);
      try rewrite <- vbinds_erase_env; try rewrite <- tvbinds_erase_env;
      pose proof (lem_free_subset_binds g t_a k_a);         intuition.
  - (* WFVar *) intros env a0 k0; intros; subst env. 
    apply lem_tvboundin_concat in H; simpl in H; destruct H. destruct H. 
    * (* a0 = a *) destruct H; subst a0; subst k0; simpl. 
      assert (a = a) by reflexivity; apply Nat.eqb_eq in H; rewrite H.
      apply lem_weaken_many_wf; try assumption; try rewrite lem_push_empty;
      try (apply esubFTV_unique); try (rewrite esubFTV_binds); assumption.      
    * (* a0 in g *) apply lem_tvboundin_inenv in H as H'.
      pose proof tvbinds_subset as Htv; unfold Subset in Htv; apply Htv in H';
      assert (a <> a0) by (unfold not; intro; subst a0; contradiction).
      apply Nat.eqb_neq in H0; simpl; rewrite H0.
      apply WFVar. apply lem_tvboundin_concat; intuition.
    * (* a0 in g' *) apply lem_tvboundin_inenv in H as H'.
      pose proof tvbinds_subset as Htv; unfold Subset in Htv; apply Htv in H';
      assert (a <> a0) by (unfold not; intro; subst a0; contradiction).
      apply Nat.eqb_neq in H0; simpl; rewrite H0.
      apply WFVar. apply (lem_tvboundin_esubFTV a0 k0 a t_a g') in H.
      apply lem_tvboundin_concat; intuition.
  - (* WFFunc *) intros env; intros; subst env;
    apply WFFunc with k_x k (names_add a (union nms (binds (concatE g g')))); fold tsubFTV;
    try apply H0 with k_a; trivial; intros;
    apply not_elem_names_add_elim in H3;  destruct H3;
    apply not_elem_union_elim in H13;     destruct H13;
    apply not_elem_concat_elim in H14;    destruct H14;
    assert (Cons y (tsubFTV a t_a t_x) (concatE g (esubFTV a t_a g')) 
              = concatE g (esubFTV a t_a (Cons y t_x g')) ) as Henv
      by reflexivity; rewrite Henv;
    rewrite <- lem_commute_tsubFTV_unbindT; try apply H2 with k_a; 
    try apply intersect_names_add_intro_r; unfold in_env; simpl;
    try apply not_elem_names_add_intro; try split;
    try apply lem_wftype_islct with g k_a; intuition.
  - (* WFExis *) intros env; intros; subst env;
    apply WFExis with k_x (names_add a (union nms (binds (concatE g g')))); fold tsubFTV;
    try apply H0 with k_a; trivial; intros;
    apply not_elem_names_add_elim in H3;  destruct H3;
    apply not_elem_union_elim in H13;     destruct H13;
    apply not_elem_concat_elim in H14;    destruct H14;
    assert (Cons y (tsubFTV a t_a t_x) (concatE g (esubFTV a t_a g')) 
              = concatE g (esubFTV a t_a (Cons y t_x g')) ) as Henv
      by reflexivity; rewrite Henv;
    rewrite <- lem_commute_tsubFTV_unbindT; try apply H2 with k_a; 
    try apply intersect_names_add_intro_r; unfold in_env; simpl;
    try apply not_elem_names_add_intro; try split;
    try apply lem_wftype_islct with g k_a; intuition.
  - (* WFPoly *) intros env k0; intros; subst env.
    apply WFPoly with k_t (names_add a (union nms (binds (concatE g g')))); fold tsubFTV; intros.
    apply not_elem_names_add_elim in H1;  destruct H1;
    apply not_elem_union_elim in H11;     destruct H11;
    apply not_elem_concat_elim in H12;    destruct H12;
    assert (ConsT a' k0 (concatE g (esubFTV a t_a g')) 
              = concatE g (esubFTV a t_a (ConsT a' k0 g')) ) as Henv
      by reflexivity; rewrite Henv.
    rewrite <- lem_commute_tsubFTV_unbind_tvT; try apply H0 with k_a;
    try apply intersect_names_add_intro_r; unfold in_env; simpl;
    try apply not_elem_names_add_intro; try split;
    try apply lem_wftype_islct with g k_a; intuition.
  - (* WFKind *) intros; apply WFKind; apply H0 with k_a; assumption.
  Qed.
  
Lemma lem_subst_tv_wf : forall (g g':env) (a:var_name) (t_a:type) (k_a:kind) (t:type) (k_t:kind),
   WFtype (concatE (ConsT a k_a g) g') t k_t 
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> ~ (in_env a g) -> ~ (in_env a g') 
                    -> isMono t_a -> noExists t_a 
                    -> WFtype g t_a k_a -> WFFE (erase_env g)
                    -> WFtype (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k_t.
Proof. intros; apply lem_subst_tv_wf'' with (concatE (ConsT a k_a g) g') k_a;
  assumption || reflexivity.  Qed.

Lemma lem_subst_tv_wf' : forall (g g':env) (a:var_name) (t_a:type) (k_a:kind) (t:type) (k_t:kind),
   WFtype (concatE (ConsT a k_a g) g') t k_t 
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> ~ (in_env a g) -> ~ (in_env a g') 
                    -> isMono t_a -> noExists t_a 
                    -> WFtype g t_a k_a -> WFEnv g
                    -> WFtype (concatE g (esubFTV a t_a g')) (tsubFTV a t_a t) k_t.
Proof. intros; apply lem_subst_tv_wf with k_a; try apply lem_erase_env_wfenv;
  assumption || reflexivity.  Qed.

Lemma lem_subst_tv_wfenv : forall (g g':env) (a:var_name) (t_a:type) (k_a:kind),
    WFEnv (concatE (ConsT a k_a g) g' )
        -> unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env a g) -> ~ (in_env a g') 
        -> isMono t_a -> noExists t_a -> WFtype g t_a k_a
        -> WFEnv (concatE g (esubFTV a t_a g')).
Proof. intro g; induction g'; simpl; intros.
  - (* Empty *) inversion H; assumption.
  - (* Cons  *) inversion H; apply WFEBind with k;
    try apply IHg' with k_a;
    try apply not_elem_concat_intro;
    try rewrite esubFTV_binds;
    try apply lem_subst_tv_wf with k_a;
    apply lem_truncate_wfenv in H11 as H';
    try apply lem_erase_env_wfenv;
    inversion H'; destruct H1;
    apply intersect_names_add_elim_r in H2; destruct H2;
    unfold in_env in H4; simpl in H4;
    apply not_elem_names_add_elim in H4; destruct H4;
    trivial. 
  - (* ConsT *) inversion H; apply WFEBindT;
    try apply IHg' with k_a;
    try apply not_elem_concat_intro; 
    try rewrite esubFTV_binds; destruct H1; 
    apply intersect_names_add_elim_r in H2; destruct H2;
    unfold in_env in H4; simpl in H4;
    apply not_elem_names_add_elim in H4; destruct H4;
    trivial.
  Qed.
    