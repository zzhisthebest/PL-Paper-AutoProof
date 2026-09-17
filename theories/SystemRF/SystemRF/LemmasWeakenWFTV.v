Require Import Arith.

Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.SystemFLemmasWeaken. 
Require Import AutoProof.SystemRF.SystemRF.LemmasWeakenWF.

(*------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   174
------------------------------------------------------------------------------*)

Lemma lem_weaken_tv_wf' : forall (g'g : env) (t : type) (k : kind),
    WFtype g'g t k -> ( forall (g g' : env) (a : var_name) (k_a : kind),
        g'g = concatE g g' -> intersect (binds g) (binds g') = empty
                           -> ~ (in_env a g) -> ~ (in_env a g') 
                           -> WFtype (concatE (ConsT a k_a g) g') t k ).
Proof. apply ( WFtype_ind 
  (fun (g'g : env) (t : type) (k : kind) => forall (g g':env) (a:var_name) (k_a:kind),
      g'g = concatE g g' -> intersect (binds g) (binds g') = empty
                         -> ~ (in_env a g) -> ~ (in_env a g') 
                         -> WFtype (concatE (ConsT a k_a g) g') t k  )).
  - (* WFBase *) intros; apply WFBase; assumption.
  - (* WFRefn *) intro env; intros; 
    apply WFRefn with (names_add a (union nms (binds (concatE g g')))); 
    try apply H0; try assumption; intros;
    apply not_elem_names_add_elim in H7; destruct H7;
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concat_elim in H9; destruct H9;
    subst env;
    assert (FCons y (FTBasic b) (erase_env (concatE (ConsT a k_a g) g'))
            = concatF (FConsT a k_a (erase_env g)) (FCons y (FTBasic b) (erase_env g')) )
      by (rewrite lem_erase_concat; reflexivity); rewrite H3;
    apply lem_weaken_tv_pftyp; 
    assert (concatF (erase_env g) (FCons y (FTBasic b) (erase_env g'))
            = FCons y (FTBasic b) (erase_env (concatE g g')))
      by (rewrite lem_erase_concat; reflexivity); try rewrite H11;
    try apply H2; simpl; try split; try unfold in_envF; simpl;
    try apply unique_erase_env; try rewrite <- binds_erase_env;
    try apply intersect_names_add_intro_r; try rewrite <- binds_erase_env;
    try apply not_elem_names_add_intro;
    apply Nat.neq_sym in H7; try split;
    trivial.
  - (* WFVar    *) intros env a0 k0 Ha0 g g' a k_a; intros; subst env.
    apply lem_tvboundin_weaken_tv with a0 k0 g g' a k_a in Ha0;
    apply WFVar; assumption.
  - (* WFFunc  *) intro env; unfold in_env; intros;
    apply WFFunc with k_x k (names_add a (union nms (binds (concatE g g'))));
    try apply H0; try assumption; intros;
    apply not_elem_names_add_elim in H7; destruct H7;
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concat_elim in H9; destruct H9;
    assert (Cons y t_x (concatE (ConsT a k_a g) g') = concatE (ConsT a k_a g) (Cons y t_x g'))
      by reflexivity; rewrite H11;
    try apply H2; subst env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; try split;
    try apply Nat.neq_sym; trivial.
  - (* WFExis  *) intro env; unfold in_env; intros;
    apply WFExis with k_x (names_add a (union nms (binds (concatE g g'))));
    try apply H0; try assumption; intros;
    apply not_elem_names_add_elim in H7; destruct H7;
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concat_elim in H9; destruct H9;
    assert (Cons y t_x (concatE (ConsT a k_a g) g') = concatE (ConsT a k_a g) (Cons y t_x g'))
      by reflexivity; rewrite H11;
    try apply H2; subst env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; try split;
    try apply Nat.neq_sym; trivial.
  - (* WFPoly  *) intro env; unfold in_envF; intros; 
    apply WFPoly with k_t (names_add a (union nms (binds (concatE g g')))); intros;
    apply not_elem_names_add_elim in H5; destruct H5;
    apply not_elem_union_elim in H6; destruct H6;
    apply not_elem_concat_elim in H7; destruct H7;
    apply (H0 a' H6 g (ConsT a' k g') a k_a); subst env; simpl;
    try apply intersect_names_add_intro_r;
    unfold in_env; try apply not_elem_names_add_intro;
    try split; try apply Nat.neq_sym; trivial.
  - (* WFKind *) intros; apply WFKind; apply H0; assumption.
  Qed.

Lemma lem_weaken_tv_wf : forall (g g' : env) (t : type) (k : kind) (a : var_name) (k_a : kind),
    WFtype (concatE g g') t k -> intersect (binds g) (binds g') = empty
                              -> ~ (in_env a g) -> ~ (in_env a g') 
                              -> WFtype (concatE (ConsT a k_a g) g') t k.
Proof. intros; apply lem_weaken_tv_wf' with (concatE g g'); trivial. Qed.

Lemma lem_weaken_tv_wf_top : forall (g : env) (t : type) (k : kind) (a : var_name) (k_a : kind),
    WFtype g t k -> ~ (in_env a g) -> WFtype (ConsT a k_a g) t k.
Proof. intros; assert (ConsT a k_a g = concatE (ConsT a k_a g) Empty) by reflexivity;
  rewrite H1; apply lem_weaken_tv_wf; simpl; try apply intersect_empty_r; intuition. Qed.

Lemma lem_weaken_many_wf : forall (g g':env) (t:type) (k:kind),
    WFtype g t k -> unique g -> unique g'
                 -> intersect (binds g) (binds g') = empty 
                 -> WFtype (concatE g g') t k.
Proof. intros; induction g'; simpl; try assumption;
  simpl in H1; destruct H1;
  simpl in H2; apply intersect_names_add_elim_r in H2; destruct H2;
  apply IHg' in H2 as H'; try assumption;
  apply lem_weaken_wf with (concatE g g') Empty t k x t0 in H'
    || apply lem_weaken_tv_wf with (concatE g g') Empty t k a k0 in H';
  simpl in H'; unfold in_env; simpl; 
  try (apply intersect_empty_r);
  try (apply unique_concat);
  try (apply not_elem_concat_intro; assumption);  
  intuition. Qed.