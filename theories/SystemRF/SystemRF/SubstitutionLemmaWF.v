Require Import Arith.

Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsSubstitution.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.SystemFLemmasSubstitution. 
Require Import AutoProof.SystemRF.SystemRF.BasicPropsWellFormedness.

(* -- -- -- -- -- -- -- -- -- -- -- ---
   -- Part of the Substitution Lemma -- 
   -- -- -- -- -- -- -- -- -- -- -- --- *)

Lemma lem_subst_wf' : forall (g'xg : env) (t : type) (k_t : kind),
   WFtype g'xg t k_t -> ( forall (g g':env) (x:var_name) (v_x:expr) (t_x:type),
       g'xg = concatE (Cons x t_x g) g' 
                    -> unique g -> unique g'
                    -> intersect (binds g) (binds g') = empty
                    -> ~ (in_env x g) -> ~ (in_env x g') 
                    -> isValue v_x -> HasFtype (erase_env g) v_x (erase t_x)
                    -> WFtype (concatE g (esubFV x v_x g')) (tsubFV x v_x t) k_t ).
Proof. apply ( WFtype_ind 
  (fun (g'xg : env) (t : type) (k_t : kind) => 
    forall (g g' : env) (x : var_name) (v_x : expr) (t_x : type),
        g'xg = concatE (Cons x t_x g) g' 
              -> unique g -> unique g'
              -> intersect (binds g) (binds g') = empty
              -> ~ (in_env x g) -> ~ (in_env x g') 
              -> isValue v_x -> HasFtype (erase_env g) v_x (erase t_x)
              -> WFtype (concatE g (esubFV x v_x g')) (tsubFV x v_x t) k_t  )).
  - (* WFBase *) intros; destruct b; simpl;
    (apply WFBase; assumption) || (simpl in H; contradiction).
  - (* WFRefn *) intro env; intros; destruct b eqn:B; simpl; simpl in H0;
    try apply WFRefn with (names_add x (union nms (binds (concatE g g'))));
    try apply H0 with t_x;
    try (destruct ps; simpl; contradiction || discriminate); try assumption;
    (* TBool / TInt / FTV a *) try ( 
      intros; apply not_elem_names_add_elim in H11; try destruct H11;
      apply not_elem_union_elim in H12; try destruct H12;
      apply not_elem_concat_elim in H13; try destruct H13; try subst env;
      assert (FCons y (FTBasic b) (erase_env (concatE g (esubFV x v_x g')))
            = concatF (erase_env g) (FCons y (FTBasic b) (erase_env g')) ) as Henv
        by (subst b; rewrite lem_erase_concat; rewrite lem_erase_esubFV; reflexivity || assumption); 
      rewrite B in Henv; rewrite Henv;
      rewrite <- lem_commute_psubFV_unbindP;
      try apply lem_subst_pftyp with (erase t_x);
      assert (concatF (FCons x (erase t_x) (erase_env g)) (FCons y (FTBasic b) (erase_env g'))
            = FCons y (FTBasic b) (erase_env (concatE (Cons x t_x g) g'))) as Henv'
        by (subst b; rewrite lem_erase_concat; reflexivity); rewrite B in Henv'; try rewrite Henv';
      try apply H2; simpl; try split; try unfold in_envF; simpl;
      try apply unique_erase_env; try rewrite <- binds_erase_env;
      try apply intersect_names_add_intro_r; try rewrite <- binds_erase_env;
      try apply not_elem_names_add_intro; try apply lem_ftyp_islc with (erase_env g) (erase t_x);
      try split; intuition
    ).
  - (* WFVar *) intros env a0 k0; intros; subst env;
    apply lem_tvboundin_concat in H; simpl in H;
    apply WFVar; apply lem_tvboundin_concat; rewrite <- lem_tvboundin_esubFV; apply H.
  - (* WFFunc *) intros env t_y k_y; intros; subst env;
    apply WFFunc with k_y k (names_add x (union nms (binds (concatE g g')))); fold tsubFV;
    try apply H0 with t_x; trivial; intros;
    apply not_elem_names_add_elim in H3;  destruct H3;
    apply not_elem_union_elim in H11;     destruct H11;
    apply not_elem_concat_elim in H12;    destruct H12;
    assert (Cons y (tsubFV x v_x t_y) (concatE g (esubFV x v_x g')) 
              = concatE g (esubFV x v_x (Cons y t_y g')) ) as Henv
      by reflexivity; rewrite Henv;
    rewrite <- lem_commute_tsubFV_unbindT; try apply H2 with t_x; 
    try apply intersect_names_add_intro_r; unfold in_env; simpl;
    try apply not_elem_names_add_intro; try split;
    try apply lem_ftyp_islc with (erase_env g) (erase t_x); intuition.
  - (* WFExis *) intros env t_y k_y; intros; subst env;
    apply WFExis with k_y (names_add x (union nms (binds (concatE g g')))); fold tsubFV;
    try apply H0 with t_x; trivial; intros;
    apply not_elem_names_add_elim in H3;  destruct H3;
    apply not_elem_union_elim in H11;     destruct H11;
    apply not_elem_concat_elim in H12;    destruct H12;
    assert (Cons y (tsubFV x v_x t_y) (concatE g (esubFV x v_x g')) 
              = concatE g (esubFV x v_x (Cons y t_y g')) ) as Henv
      by reflexivity; rewrite Henv;
    rewrite <- lem_commute_tsubFV_unbindT; try apply H2 with t_x; 
    try apply intersect_names_add_intro_r; unfold in_env; simpl;
    try apply not_elem_names_add_intro; try split;
    try apply lem_ftyp_islc with (erase_env g) (erase t_x); intuition.
  - (* WFPoly *) intros env k; intros; subst env;
    apply WFPoly with k_t (names_add x (union nms (binds (concatE g g')))); fold tsubFV; intros;
    apply not_elem_names_add_elim in H1;  destruct H1;
    apply not_elem_union_elim in H9;      destruct H9;
    apply not_elem_concat_elim in H10;    destruct H10;
    assert (ConsT a' k (concatE g (esubFV x v_x g')) 
              = concatE g (esubFV x v_x (ConsT a' k g')) ) as Henv
      by reflexivity; rewrite Henv;
    rewrite <- lem_commute_tsubFV_unbind_tvT; try apply H0 with t_x;
    try apply intersect_names_add_intro_r; unfold in_env; simpl;
    try apply not_elem_names_add_intro; try split;
    try apply lem_ftyp_islc with (erase_env g) (erase t_x); intuition.
  - (* WFKind *) intros; apply WFKind; apply H0 with t_x; assumption.
  Qed.
  
Lemma lem_subst_wf : forall (g g':env) (x:var_name) (v_x:expr) (t_x:type) (t:type) (k_t:kind),
  WFtype (concatE (Cons x t_x g) g' ) t k_t
                  -> unique g -> unique g'
                  -> intersect (binds g) (binds g') = empty
                  -> ~ (in_env x g) -> ~ (in_env x g') 
                  -> isValue v_x -> HasFtype (erase_env g) v_x (erase t_x)
                  -> WFtype (concatE g (esubFV x v_x g')) (tsubFV x v_x t) k_t.
Proof. intros; apply lem_subst_wf' with (concatE (Cons x t_x g) g') t_x;
  assumption || reflexivity.  Qed.

Lemma lem_subst_wf_top : forall (g:env) (x:var_name) (v_x:expr) (t_x:type) (t:type) (k_t:kind),
  WFtype (Cons x t_x g) t k_t
                  -> unique g -> ~ (in_env x g)
                  -> isValue v_x -> HasFtype (erase_env g) v_x (erase t_x)
                  -> WFtype g (tsubFV x v_x t) k_t.
Proof. intros; assert (g = concatE g (esubFV x v_x Empty)) by reflexivity;
  rewrite H4; apply lem_subst_wf with t_x; simpl; 
  try apply intersect_empty_r; intuition. Qed.

Lemma lem_subst_wfenv : forall (g g':env) (x:var_name) (v_x:expr) (t_x:type),
    WFEnv (concatE (Cons x t_x g) g' )
        -> unique g -> unique g'
        -> intersect (binds g) (binds g') = empty
        -> ~ (in_env x g) -> ~ (in_env x g') 
        -> isValue v_x -> HasFtype (erase_env g) v_x (erase t_x)
        -> WFEnv (concatE g (esubFV x v_x g')).
Proof. intro g; induction g'; simpl; intros.
  - (* Empty *) inversion H; assumption.
  - (* Cons  *) inversion H; apply WFEBind with k;
    try apply IHg' with t_x;
    try apply not_elem_concat_intro; 
    try rewrite esubFV_binds;
    try apply lem_subst_wf with t_x;
    destruct H1; 
    apply intersect_names_add_elim_r in H2; destruct H2;
    unfold in_env in H4; simpl in H4;
    apply not_elem_names_add_elim in H4; destruct H4;
    trivial.
  - (* ConsT *) inversion H; apply WFEBindT;
    try apply IHg' with t_x;
    try apply not_elem_concat_intro; 
    try rewrite esubFV_binds; destruct H1; 
    apply intersect_names_add_elim_r in H2; destruct H2;
    unfold in_env in H4; simpl in H4;
    apply not_elem_names_add_elim in H4; destruct H4;
    trivial.
  Qed.