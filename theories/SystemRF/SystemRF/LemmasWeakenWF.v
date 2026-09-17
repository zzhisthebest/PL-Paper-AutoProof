Require Import Arith.

Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.SystemFLemmasWeaken. 

(*------------------------------------------------------------------------------
----- | METATHEORY Development: Some technical Lemmas   
------------------------------------------------------------------------------*)

Lemma lem_weaken_wf' : forall (g'g : env) (t : type) (k : kind),
    WFtype g'g t k -> ( forall (g g' : env) (x : var_name) (t_x : type),
        g'g = concatE g g' -> intersect (binds g) (binds g') = empty
                           -> ~ (in_env x g) -> ~ (in_env x g') 
                           -> WFtype (concatE (Cons x t_x g) g') t k ).
Proof. apply ( WFtype_ind 
  (fun (g'g : env) (t : type) (k : kind) => forall (g g':env) (x:var_name) (t_x:type),
      g'g = concatE g g' -> intersect (binds g) (binds g') = empty
                         -> ~ (in_env x g) -> ~ (in_env x g') 
                         -> WFtype (concatE (Cons x t_x g) g') t k  )).
  - (* WFBase *) intros; apply WFBase; assumption.
  - (* WFRefn *) intro env; intros; 
    apply WFRefn with (names_add x (union nms (binds (concatE g g')))); 
    try apply H0; try assumption; intros;
    apply not_elem_names_add_elim in H7; destruct H7;
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concat_elim in H9; destruct H9;
    subst env; 
    assert (FCons y (FTBasic b) (erase_env (concatE (Cons x t_x g) g'))
            = concatF (FCons x (erase t_x) (erase_env g)) (FCons y (FTBasic b) (erase_env g')) )
      by (rewrite lem_erase_concat; reflexivity); rewrite H3;
    apply lem_weaken_pftyp; 
    assert (concatF (erase_env g) (FCons y (FTBasic b) (erase_env g'))
            = FCons y (FTBasic b) (erase_env (concatE g g')))
      by (rewrite lem_erase_concat; reflexivity); try rewrite H11;
    try apply H2; simpl; try split; try unfold in_envF; simpl;
    try apply unique_erase_env; try rewrite <- binds_erase_env;
    try apply intersect_names_add_intro_r; try rewrite <- binds_erase_env;
    try apply not_elem_names_add_intro;
    apply Nat.neq_sym in H7; try split; trivial.
  - (* WFVar    *) intros env a k Ha g g' x t_x; intros; subst env.
    apply lem_tvboundin_weaken with a k g g' x t_x in Ha ;
    apply WFVar; assumption.
  - (* WFFunc  *) intro env; unfold in_env; intros;
    apply WFFunc with k_x k (names_add x (union nms (binds (concatE g g'))));
    try apply H0; try assumption; intros;
    apply not_elem_names_add_elim in H7; destruct H7;
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concat_elim in H9; destruct H9;
    assert (Cons y t_x (concatE (Cons x t_x0 g) g') = concatE (Cons x t_x0 g) (Cons y t_x g'))
      by reflexivity; rewrite H11;
    try apply H2; subst env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; try split;
    try apply Nat.neq_sym; trivial.
  - (* WFExis  *) intro env; unfold in_env; intros;
    apply WFExis with k_x (names_add x (union nms (binds (concatE g g'))));
    try apply H0; try assumption; intros;
    apply not_elem_names_add_elim in H7; destruct H7;
    apply not_elem_union_elim in H8; destruct H8;
    apply not_elem_concat_elim in H9; destruct H9;
    assert (Cons y t_x (concatE (Cons x t_x0 g) g') = concatE (Cons x t_x0 g) (Cons y t_x g'))
      by reflexivity; rewrite H11;
    try apply H2; subst env; simpl;
    try apply intersect_names_add_intro_r;
    try apply not_elem_names_add_intro; try split;
    try apply Nat.neq_sym; trivial.
  - (* WFPoly  *) intro env; unfold in_envF; intros; 
    apply WFPoly with k_t (names_add x (union nms (binds (concatE g g')))); intros;
    apply not_elem_names_add_elim in H5; destruct H5;
    apply not_elem_union_elim in H6; destruct H6;
    apply not_elem_concat_elim in H7; destruct H7;
    apply (H0 a' H6 g (ConsT a' k g') x t_x); subst env; simpl;
    try apply intersect_names_add_intro_r;
    unfold in_env; try apply not_elem_names_add_intro;
    try split; try apply Nat.neq_sym; trivial.
  - (* WFKind *) intros; apply WFKind; apply H0; assumption.
  Qed.

Lemma lem_weaken_wf : forall (g g' : env) (t : type) (k : kind) (x : var_name) (t_x : type),
    WFtype (concatE g g') t k -> intersect (binds g) (binds g') = empty
                              -> ~ (in_env x g) -> ~ (in_env x g') 
                              -> WFtype (concatE (Cons x t_x g) g') t k.
Proof. intros; apply lem_weaken_wf' with (concatE g g'); trivial. Qed.

Lemma lem_weaken_wf_top : forall (g : env) (t : type) (k : kind) (x : var_name) (t_x : type),
    WFtype g t k -> ~ (in_env x g) -> WFtype (Cons x t_x g) t k.
Proof. intros; assert (Cons x t_x g = concatE (Cons x t_x g) Empty) by reflexivity;
  rewrite H1; apply lem_weaken_wf; simpl; try apply intersect_empty_r; intuition. Qed.