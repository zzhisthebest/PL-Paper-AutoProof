Require Import Arith.

Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.LocalClosure.
Require Import AutoProof.SystemRF.SystemRF.Strengthenings.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsSubstitution.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SystemFLemmasWeaken.
Require Import AutoProof.SystemRF.SystemRF.Typing.
Require Import AutoProof.SystemRF.SystemRF.LemmasWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.LemmasTyping.
Require Import AutoProof.SystemRF.SystemRF.LemmasSubtyping. 

(*  -- We need to show "equivalence" between eqlPred and eqlPred' because 
    --   eqlPred doesn't commute well with subFTV *)

Definition eqlPred' (b:basic) (ps:preds) (e:expr) : expr := 
  App (App (AppT (Prim Eql) (TRefn b ps)) e) (BV 0).

Lemma lem_open_at_eqlPred' : forall (y:var_name) (b:basic) (ps:preds) (e:expr),
    isLC e -> open_at 0 y (eqlPred' b ps e)
                = App (App (AppT (Prim Eql) (TRefn b (openP_at 1 y ps))) e) (FV y).
Proof. intros; simpl; repeat f_equal; apply lem_open_at_lc_at with 0; apply H. Qed.

Lemma lem_eqlPred_sub : forall (g:env) (b:basic) (ps:preds) (qs:preds) (e:expr),
    isLC e -> Subtype g (TRefn b (PCons (eqlPred b e) qs))
                        (TRefn b (PCons (eqlPred' b ps e) qs)).
Proof. intros; apply SBase with (union (binds g) (fvP qs)); 
  intros; apply not_elem_union_elim in H0; destruct H0;
  unfold unbindP; unfold openP_at; fold open_at; fold openP_at;
  rewrite <- (lem_strengthen_one (unbind y (eqlPred b e)));
  rewrite <- (lem_strengthen_one (unbind y (eqlPred' b ps e))); 
  apply IStren; try apply IEqlSub; trivial. Qed.

Lemma lem_self_push : forall (g:env) (a:var_name) (ps:preds) (b:basic) (qs:preds) (z:var_name),
    Subtype g (self (tsubFTV a (TRefn b qs) (TRefn (FTV a) ps)) (FV z) Base)
              (tsubFTV a (TRefn b qs) (self (TRefn (FTV a) ps)  (FV z) Base)).
Proof. intros; simpl; destruct (Nat.eqb a a) eqn:A; 
  try (rewrite Nat.eqb_neq in A; contradiction); simpl; unfold eqlPred;
  apply lem_eqlPred_sub; unfold isLC; simpl; trivial. Qed.

Lemma lem_self_subst_tv_sub' : forall (g : env) (tta : type) (k:kind),
    WFtype g tta k -> ( forall (a:var_name) (t_a t:type) (z:var_name),
        tta = tsubFTV a t_a t 
                -> noExists t_a -> isLCT t_a -> isLCT t 
                -> HasFtype (erase_env g) (FV z) (erase (tsubFTV a t_a t))
                -> Subtype g (self (tsubFTV a t_a t) (FV z) k) 
                             (tsubFTV a t_a (self t (FV z) k)) ).
Proof. apply ( WFtype_ind 
  (fun (g : env) (tta : type) (k : kind) => forall (a:var_name) (t_a t:type) (z:var_name),
        tta = tsubFTV a t_a t 
                -> noExists t_a -> isLCT t_a -> isLCT t 
                -> HasFtype (erase_env g) (FV z) (erase (tsubFTV a t_a t))
                -> Subtype g (self (tsubFTV a t_a t) (FV z) k) 
                             (tsubFTV a t_a (self t (FV z) k)) ));
  intros. (* next time, try rewrite <- H0/H3 first to clear tsubFTV a t_a t !!! *)
  - (* WFBase *) destruct t eqn:T; try (simpl in H0; discriminate H0); 
    destruct b0 eqn:B0; try destruct (Nat.eqb a a0) eqn:A;
    try ( simpl in H0; try rewrite A in H0; injection H0 as H0' H0''; 
          subst b; simpl in H; contradiction);
    try apply Nat.eqb_eq in A; try subst a0;
    try (simpl; unfold eqlPred; apply SBase with (binds g); intros; apply IRefl).
    destruct t_a; simpl in H1; try contradiction;
    try apply lem_self_push; simpl in H0;
    assert (a =? a = true) as A by (apply Nat.eqb_eq; reflexivity);
    rewrite A in H0; discriminate H0.
  - (* WFRefn *) destruct t eqn:T; try (simpl in H3; discriminate H3);
    destruct b0 eqn:B0; try destruct (Nat.eqb a a0) eqn:A;
    try ( simpl; try rewrite A; simpl; unfold eqlPred; 
          apply SBase with (binds g); intros; apply IRefl).
    try apply Nat.eqb_eq in A; try subst a0;
    destruct t_a; simpl in H4; try contradiction;
    try apply lem_self_push; simpl in H3;
    assert (a =? a = true) as A by (apply Nat.eqb_eq; reflexivity);
    rewrite A in H3; discriminate H3.
  - (* WFVar *) destruct t eqn:T; try (simpl in H0; discriminate H0);
    destruct b eqn:B0; try destruct (Nat.eqb a0 a1) eqn:A;
    try ( simpl in H0; injection H0 as H0' H0''; discriminate H0');
    try apply Nat.eqb_eq in A; try subst a0;
    try ( simpl; rewrite A; destruct k; simpl; rewrite A; unfold eqlPred;
          apply SBase with (binds g); intros; apply IRefl).
    destruct t_a; simpl in H1; try contradiction;
    assert (a1 =? a1 = true) as A1 by (apply Nat.eqb_eq; reflexivity);
    try ( simpl in H0; rewrite A1 in H0; discriminate H0) .
    destruct k; try apply lem_self_push; repeat rewrite lem_self_star; simpl; 
    rewrite A1; apply SBase with (binds g); intros; apply IRefl.
  - (* WFFunc *) repeat rewrite lem_self_star; apply lem_sub_refl with Star;
    rewrite <- H3; apply WFFunc with k_x k nms; assumption.
  - (* WFExis *) destruct t0 eqn:T0; try destruct b eqn:B;
    try destruct (Nat.eqb a a0) eqn:A; simpl in H3; try rewrite A in H3;
    try discriminate H3.
    * destruct t_a eqn:TA; simpl in H3; try discriminate; 
      simpl in H4; contradiction.
    * (* TExis *) destruct k; simpl; injection H3 as Htx Ht;   
      repeat rewrite <- Htx.
      + (* Base *) apply lem_subtype_in_exists 
            with k_x (names_add a (union nms (bindsF (erase_env g)))); try apply H.
        (* certain isLCT proof*)
        unfold isLCT; simpl; split; try apply lem_wftype_islct with g k_x;
        try apply H; apply lem_islc_at_subFTV; try apply lem_self_islct_at;
        unfold isLCT in H6; simpl in H6; destruct H6; unfold isLC; simpl; trivial.      
        (* inner subtyping *)
        intros; try rewrite lem_unbindT_self; 
        try repeat rewrite <- lem_commute_tsubFTV_unbindT; 
        try rewrite lem_unbindT_self; try apply H2;
        apply not_elem_names_add_elim in H3; destruct H3;
        apply not_elem_union_elim in H8; destruct H8;
        try rewrite Ht; try rewrite <- lem_commute_tsubFTV_unbindT;
        try rewrite lem_erase_tsubFTV; rewrite lem_erase_tsubFTV in H7;
        try rewrite lem_erase_unbind; simpl in H7; try apply lem_weaken_ftyp_top;
        unfold isLCT; try apply lem_islc_at_before_open_at; 
        unfold isLCT in H6; simpl in H6; destruct H6;
        unfold isLC; simpl; intuition.
      + (* Star *) repeat rewrite <- Ht; apply lem_sub_refl with Star;
        apply WFExis with k_x nms; trivial.
  - (* WFPoly *) repeat rewrite lem_self_star; apply lem_sub_refl with Star;
    rewrite <- H1; apply WFPoly with k_t nms; assumption.
  - (* WFKind *) repeat rewrite lem_self_star; apply lem_sub_refl with Star;
    rewrite <- H1; apply WFKind; assumption.
  Qed.
 
Lemma lem_self_subst_tv_sub : forall (g:env) (a:var_name) (t_a t:type) (z:var_name) (k:kind),
    WFtype g (tsubFTV a t_a t) k  
                -> noExists t_a -> isLCT t_a -> isLCT t 
                -> HasFtype (erase_env g) (FV z) (erase (tsubFTV a t_a t))
                -> Subtype g (self (tsubFTV a t_a t) (FV z) k) 
                             (tsubFTV a t_a (self t (FV z) k)).
Proof. intros; apply lem_self_subst_tv_sub' with (tsubFTV a t_a t); trivial. Qed.
