Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.Semantics.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.LemmasTransitive.
Require Import AutoProof.SystemRF.Denotations.ClosingSubstitutions.

From Equations Require Import Equations.

Require Import Arith.
Require Import ZArith.

Fixpoint quants (t : type) : nat :=
    match t with
    | (TRefn b ps)     => 0  
    | (TFunc  t_x t)   => max (quants t_x) (quants t)
    | (TExists  t_x t) => max (quants t_x) (quants t)
    | (TPoly  k   t)   => 1 + (quants t)
    end.

Definition quants_depth (t : type) : nat*nat := (quants t, depth t).

Lemma quants_tsubBV_at : forall (j:index) (v:expr) (t:type),
    quants (tsubBV_at j v t) = quants t.
Proof. intros j v t; revert v; revert j; induction t; intros;
  simpl; reflexivity || f_equal; 
  apply IHt1 || apply IHt2 || apply IHt. Qed.

Lemma quants_tsubBV : forall (v:expr) (t:type),
    quants (tsubBV v t) = quants t.
Proof. intros; apply quants_tsubBV_at. Qed.

Lemma quants_mono : forall (t_a: type),
    isMono t_a -> quants t_a = 0.
Proof. induction t_a; intro H; simpl in H; try contradiction;
  simpl; try reflexivity; destruct H as [H1 H2];
  apply IHt_a1 in H1; apply IHt_a2 in H2;
  rewrite H1; rewrite H2; reflexivity. Qed.

Lemma quants_push : forall (ps:preds) (t_a:type),
    quants (push ps t_a) = quants t_a.
Proof. intros ps t_a; revert ps; induction t_a; intros; simpl;
  try rewrite IHt_a2; reflexivity. Qed.

Lemma quants_tsubBTV_at : forall (j:index) (t_a:type) (t:type),
    isMono t_a -> quants (tsubBTV_at j t_a t) = quants t.
Proof. intros j t_a t; revert t_a; revert j; induction t; intros;
  try destruct b; simpl; try destruct (j =? i); simpl;
  try rewrite quants_push; 
  try rewrite IHt1; try rewrite IHt2; try rewrite IHt;
  trivial. rewrite quants_mono; trivial. Qed.

Lemma quants_tsubBTV : forall (t_a:type) (t:type),
    isMono t_a -> quants (tsubBTV t_a t) = quants t.
Proof. intros; apply quants_tsubBTV_at; assumption. Qed.

(*------------------------------------------------------------------------------
----- | DENOTATIONAL SEMANTICS 
------------------------------------------------------------------------------*)

Inductive PEvalsTrue : preds -> Prop :=
    | PEEmp  : PEvalsTrue PEmpty
    | PECons : forall (p : expr) (ps : preds),
        multistep p (Bool_constant true) -> PEvalsTrue ps -> PEvalsTrue (PCons p ps).

Equations Denotes  (t : type) (v : expr) : Prop
  by wf (quants_depth t) (lexprod _ _ lt lt)  :=
Denotes (TRefn   b   ps) v := 
    isValue v /\ HasFtype FEmpty v (erase (TRefn   b   ps)) /\ 
        PEvalsTrue (psubBV v ps) ;
Denotes (TFunc   t_x t') v := 
    isValue v /\ HasFtype FEmpty v (erase (TFunc   t_x t')) /\ 
        forall (v_x : expr), 
          isValue v_x -> Denotes t_x v_x -> (exists (v' : expr), 
            isValue v' /\ multistep (App v v_x) v' /\ Denotes (tsubBV v_x t') v'
        );
Denotes (TExists t_x t') v := 
    isValue v /\ HasFtype FEmpty v (erase (TExists t_x t')) /\ 
      exists (v_x : expr),
        isValue v_x /\ Denotes t_x v_x /\ Denotes (tsubBV v_x t') v;
Denotes (TPoly   k   t') v :=  
    isValue v /\ HasFtype FEmpty v (erase (TPoly   k   t')) /\ 
      forall (t_a : type) (pf : isMono t_a),
        noExists t_a ->  WFtype Empty t_a k -> (exists (v' : expr),
          isValue v' /\ multistep (AppT v t_a) v' /\ Denotes (tsubBTV t_a t') v').
  Obligation 1. (* quants_depth t_x "<" quants_depth t *) 
    pose proof Nat.le_max_l (quants t_x) (quants t') as Hq;
    pose proof Nat.le_max_l (depth  t_x) (depth  t') as Hd.
    apply Nat.lt_eq_cases in Hq; destruct Hq as [Hq|Hq]; simpl.
      * left. apply Hq.
      * unfold quants_depth; rewrite Hq. right; simpl;
        apply Nat.lt_succ_r; apply Hd.
  Defined.
  Obligation 2.  (* quants_depth (tsubBV v_x t') "<" quants_depth t *)
    pose proof Nat.le_max_r (quants t_x) (quants t') as Hq;
    pose proof Nat.le_max_r (depth  t_x) (depth  t') as Hd;
    unfold quants_depth.
    rewrite depth_tsubBV; rewrite quants_tsubBV. 
    apply Nat.lt_eq_cases in Hq; destruct Hq as [Hq|Hq]; simpl.
      * left. apply Hq.
      * rewrite <- Hq. right. apply Nat.lt_succ_r; apply Hd.
  Defined. (*Qed.*)
  Obligation 3.   (* quants_depth t_x "<" quants_depth t *)
    pose proof Nat.le_max_l (quants t_x) (quants t') as Hq;
    pose proof Nat.le_max_l (depth  t_x) (depth  t') as Hd;
    unfold quants_depth;
    apply Nat.lt_eq_cases in Hq; destruct Hq as [Hq|Hq]; simpl.
      * left. apply Hq.
      * rewrite <- Hq; right; apply Nat.lt_succ_r; apply Hd.
  Defined. (*Qed.*)
  Obligation 4.   (* quants_depth (tsubBV v_x t') "<" quants_depth t *)
    pose proof Nat.le_max_r (quants t_x) (quants t') as Hq;
    pose proof Nat.le_max_r (depth  t_x) (depth  t') as Hd;
    unfold quants_depth.
    rewrite depth_tsubBV; rewrite quants_tsubBV. 
    apply Nat.lt_eq_cases in Hq; destruct Hq as [Hq|Hq]; simpl.
      * left. apply Hq.
      * rewrite <- Hq; right; apply Nat.lt_succ_r; apply Hd.
  Defined. (*Qed.*)
  Obligation 5.   (* quants_depth (tsubBTV t_a t') "<" quants_depth t *)
    left; rewrite quants_tsubBTV; intuition. 
  Defined. 

Example zero_den_tint : Denotes (TRefn TInt PEmpty) (Int_constant 0).
Proof. rewrite Denotes_equation_1; simpl;
  repeat split; try apply FTIC; unfold psubBV; simpl; apply PEEmp.
  Qed.

Lemma lem_den_isvalue : forall (v:expr) (t:type),
    Denotes t v -> isValue v.
Proof. intros; destruct t.
  - rewrite Denotes_equation_1 in H; intuition.
  - rewrite Denotes_equation_2 in H; intuition.
  - rewrite Denotes_equation_3 in H; intuition.
  - rewrite Denotes_equation_4 in H; intuition.
  Qed.

Lemma lem_den_hasftype : forall (v:expr) (t:type),
    Denotes t v -> HasFtype FEmpty v (erase t).
Proof. intros; destruct t.
  - rewrite Denotes_equation_1 in H; intuition.
  - rewrite Denotes_equation_2 in H; intuition.
  - rewrite Denotes_equation_3 in H; intuition.
  - rewrite Denotes_equation_4 in H; intuition.
  Qed.
  
Definition EvalsDenotes (t : type) (e : expr) : Prop :=
  exists v, isValue v /\ multistep e v /\ Denotes t v.

Lemma lem_den_evalsdenotes : forall (t:type) (v:expr),
    Denotes t v -> EvalsDenotes t v.
Proof. intros; unfold EvalsDenotes; exists v; repeat split;
  try apply lem_den_isvalue with t; try apply Refl; apply H. Qed.

Lemma lem_evalsdenotes_value : forall (t:type) (v:expr),
    EvalsDenotes t v -> isValue v -> Denotes t v.
Proof. intros; unfold EvalsDenotes in H; 
  destruct H as [v' [Hv' [ev_v_v' den_t_v']]];
  assert (v = v')
    by (apply lem_evals_val_det with v; apply Refl || assumption);
  subst v'; apply den_t_v'. Qed.
  
(* Denotations of Environments, [[g]]. There are two cases:
--   1. [[ Empty ]] = { CEmpty }.
--   2. [[ Cons x t g ]] = { CCons x v_x th | Denotes th(t) v_x && th \in [[ g ]] } *)
Inductive DenotesEnv : env -> csub -> Prop :=
    | DEmp  : DenotesEnv Empty CEmpty
    | DExt  : forall (g:env) (th:csub) (x:var_name) (t:type) (v:expr), 
        DenotesEnv g th -> ~ in_env x g -> Denotes (ctsubst th t) v
              -> DenotesEnv (Cons x t g) (CCons x v th)
    | DExtT : forall (g:env) (th:csub) (a:var_name) (k:kind) (t:type),
        DenotesEnv g th -> ~ in_env a g 
              -> isMono t -> noExists t -> WFtype Empty t k
              -> DenotesEnv (ConsT a k g) (CConsT a t th).

Lemma lem_binds_env_th : forall (g:env) (th:csub), 
    DenotesEnv g th -> binds g = bindsC th.
Proof. intros g th den_g_th; induction den_g_th; simpl;
  try rewrite IHden_g_th; reflexivity. Qed.

Lemma lem_vbinds_env_th : forall (g:env) (th:csub), 
    DenotesEnv g th -> vbinds g = vbindsC th.
Proof. intros g th den_g_th; induction den_g_th; simpl;
  try rewrite IHden_g_th; reflexivity. Qed.
  
Lemma lem_tvbinds_env_th : forall (g:env) (th:csub), 
    DenotesEnv g th -> tvbinds g = tvbindsC th.
Proof. intros g th den_g_th; induction den_g_th; simpl;
  try rewrite IHden_g_th; reflexivity. Qed.  

(*------------------------------------------------------------------------------
----- | IMPILICATION from DENOTATIONAL SEMANTICS 
------------------------------------------------------------------------------*)

Inductive DImplies : env -> preds -> preds -> Prop :=
    | DImp : forall (g:env) (ps qs : preds),
        (forall (th:csub), DenotesEnv g th -> PEvalsTrue (cpsubst th ps) 
                                           -> PEvalsTrue (cpsubst th qs) )
            -> DImplies g ps qs.

Lemma lem_den_nofv : forall (v:expr) (t:type),
    Denotes t v -> fv v = empty /\ ftv v = empty.
Proof. intros v t den_t_v; apply lem_den_hasftype in den_t_v;
  apply lem_fv_subset_bindsF in den_t_v; simpl in den_t_v;
  destruct den_t_v; split; apply no_elem_empty; intro x;
  apply not_elem_subset with empty; auto. Qed.