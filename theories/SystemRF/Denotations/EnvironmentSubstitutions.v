Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.Strengthenings.
Require Import AutoProof.SystemRF.SystemRF.Semantics.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsSubstitution.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.Typing.
Require Import AutoProof.SystemRF.Denotations.ClosingSubstitutions.
Require Import AutoProof.SystemRF.Denotations.Denotations.
Require Import AutoProof.SystemRF.Denotations.BasicPropsCSubst.

Require Import Arith.

Lemma lem_concat_shift : forall (g:env) (x:var_name) (t_x:type) (g':env),
    ~ (in_env x g) -> ~ (in_env x g') -> intersect (binds g) (binds g') = empty
        -> concatE (Cons x t_x g) g' = concatE g (concatE (Cons x t_x Empty) g').
Proof. intros g x t_x; induction g'; simpl; intros; try reflexivity;
  f_equal; apply IHg'; unfold in_env in H0; simpl in H0;
  apply not_elem_names_add_elim in H0; destruct H0; 
  apply intersect_names_add_elim_r in H1; destruct H1;  trivial. Qed.

Lemma lem_concat_shift_tv : forall (g:env) (a:var_name) (k_a:kind) (g':env),
    ~ (in_env a g) -> ~ (in_env a g') -> intersect (binds g) (binds g') = empty
        -> concatE (ConsT a k_a g) g' = concatE g (concatE (ConsT a k_a Empty) g').
Proof. intros g a k_a; induction g'; simpl; intros; try reflexivity;
  f_equal; apply IHg'; unfold in_env in H0; simpl in H0;
  apply not_elem_names_add_elim in H0; destruct H0; 
  apply intersect_names_add_elim_r in H1; destruct H1;  trivial. Qed.

Lemma lem_csubst_env_empty : forall (th:csub),
    csubst_env th Empty = Empty.
Proof. induction th; simpl; reflexivity || apply IHth. Qed.

Lemma lem_csubst_cons_env : forall (th:csub) (x:var_name) (t_x:type) (g:env),
    csubst_env th (Cons x t_x g) = Cons x (ctsubst th t_x) (csubst_env th g).
Proof. induction th; simpl; intros; reflexivity || apply IHth. Qed.

Lemma lem_csubst_consT_env : forall (th:csub) (a:var_name) (k_a:kind) (g:env), 
    csubst_env th (ConsT a k_a g) = ConsT a k_a (csubst_env th g).
Proof. induction th; simpl; intros; reflexivity || apply IHth. Qed.

Lemma lem_esubFV_concat : forall (x:var_name) (v:expr) (g g':env),
    esubFV x v (concatE g g') = concatE (esubFV x v g) (esubFV x v g').
Proof. intros; induction g'; simpl; try rewrite IHg'; reflexivity. Qed.

Lemma lem_esubFTV_concat : forall (a:var_name) (t_a:type) (g g':env),
    esubFTV a t_a (concatE g g') = concatE (esubFTV a t_a g) (esubFTV a t_a g').
Proof. intros; induction g'; simpl; try rewrite IHg'; reflexivity. Qed.

Lemma lem_csubst_env_concat : forall (th:csub) (g g':env),
    csubst_env th (concatE g g') = concatE (csubst_env th g) (csubst_env th g').
Proof. induction th; simpl; intros; try rewrite lem_esubFV_concat;
  try rewrite lem_esubFTV_concat; apply IHth || reflexivity. Qed.

Lemma csubst_env_binds : forall (th:csub) (g:env),
    binds (csubst_env th g) = binds g.
Proof. induction th; intros; simpl; try rewrite IHth;
  try apply esubFV_binds; try apply esubFTV_binds; reflexivity. Qed.

Lemma csubst_env_unique : forall (th:csub) (g:env),
    unique g -> unique (csubst_env th g).
Proof. induction th; intros; simpl; try apply IHth;
  try apply esubFV_unique; try apply esubFTV_unique; apply H. Qed.

Lemma lem_commute_esubFV : forall (g:env) (x:var_name) (v_x:expr) (y:var_name) (v_y:expr),
    y <> x -> ~ In x (fv v_y) -> ~ In y (fv v_x)
        -> esubFV y v_y (esubFV x v_x g) = esubFV x (subFV y v_y v_x) (esubFV y v_y g).
Proof. induction g; simpl; intros; reflexivity || rewrite <- IHg;
  try rewrite lem_commute_tsubFV; 
  try rewrite lem_subFV_notin'; trivial. Qed.
  
Lemma lem_commute_esubFV_esubFTV : 
  forall (g:env) (a:var_name) (t_a:type) (y:var_name) (v_y:expr),
    noExists t_a -> isValue v_y -> ~ In a (ftv v_y) -> ~ In y (free t_a)
        -> esubFV y v_y (esubFTV a t_a g) =
                    esubFTV a (tsubFV y v_y t_a) (esubFV y v_y g).
Proof. induction g; simpl; intros; reflexivity || rewrite <- IHg;
  try rewrite lem_commute_tsubFV_tsubFTV;
  try rewrite (lem_tsubFV_notin t_a); trivial. Qed.
  
Lemma lem_unroll_csubst_env_left : forall (th:csub) (x:var_name) (v_x:expr) (g:env),
    ~ in_csubst x th -> fv v_x = empty /\ ftv v_x = empty -> isValue v_x
        -> closed th -> substitutable th
        -> csubst_env (CCons x v_x th) g = esubFV x v_x (csubst_env th g).
Proof. induction th; simpl; intros; try reflexivity;
  unfold in_csubst in H; simpl in H; 
  apply not_elem_names_add_elim in H; destruct H;
  rewrite <- IHth; simpl; try f_equal;
  destruct H2; destruct H3; destruct H5; try destruct H6;
  trivial; destruct H0.
  - (* CCons *) rewrite lem_commute_esubFV;
    try rewrite lem_subFV_notin'; try apply Nat.neq_sym;
    try rewrite H0; try rewrite H2; auto.
  - (* CConsT *) rewrite lem_commute_esubFV_esubFTV;
    try rewrite lem_tsubFV_notin; 
    try rewrite H9; try rewrite H2; auto.
  Qed.
    
Lemma lem_erase_ctsubst : forall (th:csub) (t1 t2:type),
    substitutable th -> erase t1 = erase t2 
        -> erase (ctsubst th t1) = erase (ctsubst th t2).
Proof. induction th; simpl; intros.  
  - (* CEmpty *) apply H0.
  - (* CCons *) destruct H; apply IHth; 
    repeat rewrite lem_erase_tsubFV; assumption.
  - (* CConsT *) destruct H; destruct H1; apply IHth; 
    repeat rewrite lem_erase_tsubFTV; f_equal; assumption.
  Qed.