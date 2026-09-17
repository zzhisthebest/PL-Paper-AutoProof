Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.Strengthenings.
Require Import AutoProof.SystemRF.SystemRF.Semantics.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsSubstitution.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.Denotations.ClosingSubstitutions.
Require Import AutoProof.SystemRF.Denotations.Denotations.
Require Import AutoProof.SystemRF.Denotations.BasicPropsCSubst.

Lemma lemma_strengthen_semantics : forall (ps qs:preds),
    PEvalsTrue ps -> PEvalsTrue qs -> PEvalsTrue (strengthen ps qs).
Proof. induction ps; simpl; trivial; intros.
  apply PECons; inversion H; try apply IHps; assumption. Qed.

Lemma lemma_semantics_strengthen : forall (ps qs:preds),
    PEvalsTrue (strengthen ps qs) -> PEvalsTrue ps /\ PEvalsTrue qs.
Proof. induction ps; simpl; intros; split;
  try apply PEEmp; try apply PECons; try apply H;
  inversion H; apply IHps in H3; destruct H3; assumption. Qed.  

  (* Lemma. If p ~> q then th(p) ~> th(q). *)

Lemma lem_csubst_isCompat : forall (c:prim) (w:expr) (th:csub),
    isCompat c w -> csubst th w = w.
Proof. intros; inversion H;
  try rewrite lem_csubst_bc; try rewrite lem_csubst_ic;
  reflexivity. Qed.

Lemma lem_csubst_delta : 
  forall (c:prim) (w:expr) (pf:isCompat c w) (th:csub),
    csubst th (delta c w pf) = delta c w pf.
Proof. intros; pose proof (delta_delta' c w pf);
  inversion pf; subst c; subst w; 
  try destruct b; simpl in H; injection H as H;
  rewrite H; try rewrite lem_csubst_lambda;
  try rewrite lem_csubst_bc; try rewrite lem_csubst_prim;
  try rewrite lem_csubst_bv; reflexivity. Qed.

Lemma lem_ctsubst_isCompatT : forall (c:prim) (t:type) (th:csub),
    isCompatT c t -> isCompatT c (ctsubst th t).
Proof. intros; inversion H.
  - apply isCptT_EqlB; apply lem_ctsubst_erase_basic; simpl; auto.
  - apply isCptT_EqlZ; apply lem_ctsubst_erase_basic; simpl; auto.
  - apply isCptT_LeqlB; apply lem_ctsubst_erase_basic; simpl; auto.
  - apply isCptT_LeqlZ; apply lem_ctsubst_erase_basic; simpl; auto.
  Qed.

Lemma lem_ctsubst_deltaT : 
  forall (th:csub) (c:prim) (t:type) (pf:isCompatT c t) (pf':isCompatT c (ctsubst th t)),
    csubst th (deltaT c t pf) = deltaT c (ctsubst th t) pf'.
Proof. intros; pose proof (deltaT_deltaT' c t pf);
  pose proof (deltaT_deltaT' c (ctsubst th t) pf');
  inversion pf; subst c; simpl in H; simpl in H0;
  apply (lem_ctsubst_erase_basic th) in H1 as H2; 
  rewrite H1 in H; try rewrite H2 in H0;
  injection H as H; try injection H0 as H0;
  try rewrite <- H; try rewrite <- H0;
  try rewrite lem_csubst_prim; simpl; try left; trivial. Qed.

Lemma lem_csubst_step : forall (th:csub) (p q:expr),
    loc_closed th -> substitutable th -> Step p q 
        -> Step (csubst th p) (csubst th q).
Proof. intros th p q Hlc Hth H; induction H.
  - (* EPrim *) rewrite lem_csubst_app; rewrite lem_csubst_prim;
    rewrite lem_csubst_isCompat with c w th; 
    try rewrite lem_csubst_delta; try apply EPrim; assumption.
  - (* EApp1 *) repeat rewrite lem_csubst_app; apply EApp1;
    apply IHStep.
  - (* EApp2 *) repeat rewrite lem_csubst_app; apply EApp2;
    try apply lem_csubst_value; try apply IHStep; assumption.
  - (* EAppAbs *) rewrite lem_csubst_app; rewrite lem_csubst_lambda;
    rewrite lem_csubst_subBV; try apply EAppAbs;
    try apply lem_csubst_value; assumption.
  - (* EPrimT *) rewrite lem_csubst_appT; rewrite lem_csubst_prim;
    apply lem_ctsubst_isCompatT with c t th in pf as pf';
    rewrite (lem_ctsubst_deltaT th c t pf pf'); apply EPrimT;
    apply lem_ctsubst_noExists; assumption.
  - (* EAppT *) repeat rewrite lem_csubst_appT; apply EAppT;
    try apply IHStep; apply lem_ctsubst_noExists; assumption.
  - (* EAppTAbs *) rewrite lem_csubst_appT; 
    rewrite lem_csubst_lambdaT; rewrite lem_csubst_subBTV;
    try apply EAppTAbs; try apply lem_ctsubst_noExists;
    assumption.
  - (* ELet *) repeat rewrite lem_csubst_let; apply ELet; apply IHStep.
  - (* ELetV *) rewrite lem_csubst_let; rewrite lem_csubst_subBV;
    try apply ELetV; try apply lem_csubst_value; assumption.
  - (* EAnn *) repeat rewrite lem_csubst_annot; apply EAnn; apply IHStep.
  - (* EAnnV *) rewrite lem_csubst_annot; apply EAnnV;
    apply lem_csubst_value; assumption. 
  - (* EIf *) repeat rewrite lem_csubst_if; apply EIf; apply IHStep.
  - (* EIfT *) rewrite lem_csubst_if; rewrite lem_csubst_bc; apply EIfT.
  - (* EIfF *) rewrite lem_csubst_if; rewrite lem_csubst_bc; apply EIfF.
  Qed.

Lemma lem_csubst_evals : forall (th:csub) (p q:expr),
    loc_closed th -> substitutable th -> multistep p q 
        -> multistep (csubst th p) (csubst th q).
Proof. intros th p q H1 H2 Hpq; induction Hpq.
  - apply Refl.
  - apply AddStep with (csubst th e2); try apply lem_csubst_step;
    assumption. Qed.