Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsSubstitution.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.Typing.
Require Import AutoProof.SystemRF.SystemRF.LemmasWeakenWF.
Require Import AutoProof.SystemRF.SystemRF.SubstitutionLemmaWF.
Require Import AutoProof.SystemRF.SystemRF.LemmasTyping.

(*------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------*)

Lemma lem_sub_refl : forall (g:env) (t:type) (k:kind),
    WFtype g t k -> Subtype g t t.
Proof. intros g t k p_g_t; induction p_g_t.
  - (* WFBase *) apply SBase with (binds g); intros; apply IRefl.
  - (* WFRefn *) apply SBase with (binds g); intros; apply IRefl.
  - (* WFVar  *) apply SBase with (binds g); intros; apply IRefl.
  - (* WFFunc *) apply SFunc with nms; try apply IHp_g_t;
    intros; apply H0; apply H1.
  - (* WFExis *) apply SBind with (union nms (binds g)); 
    try apply lem_wftype_islct with g k;
    try apply WFExis with k_x nms; try apply p_g_t; intros;
    try apply H; try apply H1; try apply SWitn with (FV y);
    assert (t_x = self t_x (FV y) Star) 
      by (destruct t_x; reflexivity); try rewrite H2 at 2;
    try apply T_Var; 
    assert (Cons y t_x g = concatE (Cons y t_x g) Empty) by reflexivity; try rewrite H3;
    try apply lem_weaken_wf;
    try (destruct k_x; apply p_g_t || (apply WFKind; apply p_g_t));
    try rewrite <- lem_unbindT_is_tsubBV; try apply H0;
    try apply not_elem_union_elim in H1; try destruct H1; 
    try apply intersect_empty_r; simpl; intuition.
  - (* WFPoly *) apply SPoly with nms; intros; apply H0; apply H1.
  - (* WFKind *) apply IHp_g_t.
  Qed.

Lemma lem_witness_sub : forall (g:env) (v_x:expr) (t_x:type) (t':type) (k:kind),
    isValue v_x -> Hastype g v_x t_x -> WFtype g (TExists t_x t') k -> WFEnv g
                -> Subtype g (tsubBV v_x t') (TExists t_x t').
Proof. intros; inversion H1; try inversion H3;
  apply SWitn with v_x; try apply lem_sub_refl with k;
  pose proof (fresh_var_not_elem nms g) as Hy; set (y := fresh_var nms g) in Hy;
  assert (g = concatE g (esubFV y v_x Empty)) as Hg by reflexivity;
  try ( rewrite Hg; rewrite lem_tsubFV_unbindT with y v_x t';
        try apply lem_subst_wf with t_x ); simpl;
  try apply H8; try (destruct k; apply H12 || (apply WFKind; apply H12));
  try destruct Hy as [Hy Hyg]; try apply wfenv_unique; try apply intersect_empty_r;
  try apply lem_typing_hasftype; trivial;
  pose proof (lem_free_bound_in_env g (TExists t_x t') k y H1 Hyg) 
    as Ht'; simpl in Ht'; destruct Ht' as [Ht' Ht''];
    apply not_elem_union_elim in Ht'; destruct Ht'; intuition. Qed.

(* -- Suppose we know that G |- s <: t, G |- s : Star and G |- t : Base. Then we
   --   can produce a judgment that G |- s : Base too.  *)
Lemma lem_sub_pullback_wftype : forall (g:env) (s t:type),
    WFEnv g -> Subtype g s t -> WFtype g s Star -> WFtype g t Base -> WFtype g s Base.
Proof. intros g s t p_g p_s_t; induction p_s_t.
  - (* SBase *) intros; inversion H0.
    * subst b; subst p1; inversion H1; try simpl in H7; try contradiction; 
      try apply H7; apply WFVar; apply H9.
    * apply H2.
  - (* SFunc *) intros; inversion H2. (* impossible *)
  - (* SWitn *) intros; apply IHp_s_t; try assumption;
    inversion H2;
    pose proof (fresh_var_not_elem nms g) as Hy; 
    set (y := fresh_var nms g) in Hy; destruct Hy;
    assert (Hg : g = concatE g (esubFV y v_x Empty)) by reflexivity; 
    rewrite Hg;
    rewrite lem_tsubFV_unbindT with y v_x t';
    try apply lem_subst_wf with t_x; simpl; try apply H8;
    try apply intersect_empty_r; try apply wfenv_unique; 
    try apply lem_typing_hasftype;
    pose proof (lem_free_bound_in_env g (TExists t_x t') Base y H2 H10) 
      as Ht'; simpl in Ht'; destruct Ht' as [Ht' Ht''];
    apply not_elem_union_elim in Ht'; destruct Ht';
    unfold unique; intuition.
  - (* SBind *) intros; inversion H2; try inversion H4;
    apply WFExis with k_x (union (union nms nms0) (binds g));
    try assumption; intros; apply H1;
    (apply not_elem_union_elim in H11; destruct H11 as [H' Hg]) ||
      (apply not_elem_union_elim in H13; destruct H13 as [H' Hg]);
    apply not_elem_union_elim in H'; destruct H';
    try apply WFEBind with k_x; try apply H9; try (apply WFKind; apply H12);
    assert (Cons y t_x g = concatE (Cons y t_x g) Empty) as Henv 
      by reflexivity; try rewrite Henv;
    try apply lem_weaken_wf;
    try apply intersect_empty_r; intuition.
  - (* SPoly *) intros; inversion H2. (* impossible *)
  Qed.

Lemma lem_subtype_in_exists : forall (g:env) (t_x t t':type) (k_x:kind) (nms:names),
    isLCT (TExists t_x t') -> WFtype g t_x k_x
        -> ( forall (y:var_name), ~ In y nms 
                -> Subtype (Cons y t_x g) (unbindT y t) (unbindT y t') )
        -> Subtype g (TExists t_x t) (TExists t_x t').
Proof. intros; apply SBind with (union nms (binds g)); try apply H; intros;
  apply not_elem_union_elim in H2; destruct H2;
  apply SWitn with (FV y); 
  assert (t_x = self t_x (FV y) Star) as Hself
      by (destruct t_x; reflexivity); try rewrite Hself at 2;
  try apply T_Var;
  assert (Cons y t_x g = concatE (Cons y t_x g) Empty) as Henv 
      by reflexivity; try rewrite Henv;
  try apply lem_weaken_wf; simpl; 
  destruct k_x; try (apply H0 || apply WFKind; apply H0);
  try rewrite <- lem_unbindT_is_tsubBV; try apply H1;
  try apply intersect_empty_r; intuition.
  Qed.