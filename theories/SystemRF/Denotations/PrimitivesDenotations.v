Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.Semantics.
Require Import AutoProof.SystemRF.SystemRF.SystemFWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.PrimitivesFTyping.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.Typing.
Require Import AutoProof.SystemRF.Denotations.ClosingSubstitutions.
Require Import AutoProof.SystemRF.Denotations.Denotations.
Require Import AutoProof.SystemRF.Denotations.BasicPropsCSubst.
Require Import AutoProof.SystemRF.Denotations.PrimitivesSemantics.

Require Import ZArith.

(*------------------------------------------------------------------------
  -- | Inverting Denotations of the Basic Types
  ------------------------------------------------------------------------*)
  
Lemma lem_den_bools : forall (t:type) (v:expr),
    isValue v -> erase t = FTBasic TBool -> Denotes t v -> isBool v.
Proof. intros; apply lem_den_hasftype in H1;
  apply lem_bool_values; try rewrite <- H0; assumption. Qed.

Lemma lem_den_ints : forall (t:type) (v:expr),
    isValue v -> erase t = FTBasic TInt -> Denotes t v -> isInt v.
Proof. intros; apply lem_den_hasftype in H1;
  apply lem_int_values; try rewrite <- H0; assumption. Qed.

  (* -- Lemmata. Denotations of Primitive/Constant Types *)

Lemma lem_den_tybc : forall (b:bool), Denotes (tybc b) (Bool_constant b).
Proof. intro b; unfold tybc; rewrite Denotes_equation_1;
  repeat split; unfold psubBV; simpl; trivial; try apply FTBC. 
  apply PECons; try apply PEEmp.
  assert (true = Bool.eqb b b) by (destruct b; reflexivity);
  rewrite H; apply lemma_eql_bool_semantics; apply Refl. Qed.

Lemma lem_den_tyic : forall (n:Z), Denotes (tyic n) (Int_constant n).
Proof. intro n; unfold tyic; rewrite Denotes_equation_1;
  repeat split; unfold psubBV; simpl; trivial; try apply FTIC. 
  apply PECons; try apply PEEmp.
  assert ((Z.eqb n n) = true) by (apply Z.eqb_eq; reflexivity).
  rewrite <- H; apply lemma_eql_int_semantics; apply Refl. Qed. 

Lemma lem_den_and : Denotes (primitive_type And) (Prim And).
Proof. unfold primitive_type; rewrite Denotes_equation_2;
  repeat split; unfold tsubBV; simpl; try apply FTPrm; intros.
  assert (isBool v_x)
    by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  destruct b eqn:B.
  - (* Bool_constant true *) exists (Lambda (BV 0)); split; try split;
    try apply lem_step_evals; try apply lem_step_and_tt.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTVar; unfold bound_inF; auto;
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bool_constant b0); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply EAppAbs;
    try apply FTBC; try apply PECons; try apply PEEmp; 
    try apply lemma_evals_trans with (Bool_constant (Bool.eqb (andb true b0) b0)); 
    try apply lemma_semantics_refn_and; destruct b0; simpl; 
    try apply Refl; auto.
  - (* Bool_constant false *) exists (Lambda (Bool_constant false)); split; try split;
    try apply lem_step_evals; try apply lem_step_and_ff.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTBC; trivial. 
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bool_constant false); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply EAppAbs; try apply H2;
    try apply FTBC; apply PECons; try apply PEEmp.
    apply lemma_evals_trans with (Bool_constant (Bool.eqb (andb false b0) false)); 
    try apply lemma_semantics_refn_and; destruct b0; simpl; apply Refl.
  Qed.

Lemma lem_den_or : Denotes (primitive_type Or) (Prim Or).
Proof. unfold primitive_type; rewrite Denotes_equation_2.
  repeat split; unfold tsubBV; simpl; try apply FTPrm; intros.
  assert (isBool v_x)
    by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  destruct b eqn:B.
  - (* Bool_constant true *) exists (Lambda (Bool_constant true)); split; try split;
    try apply lem_step_evals; try apply lem_step_or_tt.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTBC; trivial. 
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bool_constant true); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply EAppAbs; try apply H2;
    try apply FTBC; apply PECons; try apply PEEmp.
    apply lemma_evals_trans with (Bool_constant (Bool.eqb (andb false b0) false)); 
    try apply lemma_semantics_refn_or; destruct b0; simpl; apply Refl.  
  - (* Bool_constant false *) exists (Lambda (BV 0)); split; try split;
    try apply lem_step_evals; try apply lem_step_or_ff.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTVar; unfold bound_inF; auto;
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bool_constant b0); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply EAppAbs;
    try apply FTBC; try apply PECons; try apply PEEmp; 
    try apply lemma_evals_trans with (Bool_constant (Bool.eqb (andb true b0) b0)); 
    try apply lemma_semantics_refn_or; destruct b0; simpl; 
    try apply Refl; auto.
  Qed.

Lemma lem_den_not : Denotes (primitive_type Not) (Prim Not).
Proof. unfold primitive_type; rewrite Denotes_equation_2;
  repeat split; unfold tsubBV; simpl; try apply FTPrm; intros.
  assert (isBool v_x)
    by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  exists (Bool_constant (negb b)); repeat split; unfold psubBV; simpl;
  try apply lem_step_evals; try apply lem_step_not;
  try apply FTBC; apply PECons; try apply PEEmp;
  apply lemma_evals_trans with (Bool_constant (Bool.eqb (negb b) (negb b)));
  try apply lemma_semantics_refn_not; destruct b; simpl; apply Refl.
  Qed.  

Lemma lem_den_eqv : Denotes (primitive_type Eqv) (Prim Eqv).
Proof. unfold primitive_type; rewrite Denotes_equation_2;
  repeat split; unfold tsubBV; simpl; try apply FTPrm; intros.
  assert (isBool v_x)
    by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  destruct b eqn:B.
  - (* Bool_constant true *) exists (Lambda (BV 0)); split; try split;
    try apply lem_step_evals; try apply lem_step_eqv_tt.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTVar; unfold bound_inF; auto;
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bool_constant b0); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply EAppAbs;
    try apply FTBC; try apply PECons; try apply PEEmp; 
    try apply lemma_evals_trans with (Bool_constant (Bool.eqb (Bool.eqb true b0) b0)); 
    try apply lemma_semantics_refn_eqv; destruct b0; simpl; 
    try apply Refl; auto.
  - (* Bool_constant false *) exists (Prim Not); split; try split;
    try apply lem_step_evals; try apply lem_step_eqv_ff.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTPrm; trivial. 
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bool_constant (negb b0)); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply lem_step_not;
    try apply FTBC; apply PECons; try apply PEEmp.
    apply lemma_evals_trans with (Bool_constant (Bool.eqb (Bool.eqb false b0) (negb b0)));
    try apply lemma_semantics_refn_eqv; destruct b0; simpl; apply Refl.
  Qed.  

Lemma lem_den_imp : Denotes (primitive_type Imp) (Prim Imp).
Proof. unfold primitive_type; simpl; rewrite Denotes_equation_2;
  repeat split; unfold tsubBV; simpl; try apply FTPrm; intros.
  assert (isBool v_x)
    by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  destruct b eqn:B.
  - (* Bool_constant true *) exists (Lambda (BV 0)); split; try split;
    try apply lem_step_evals; try apply lem_step_imp_tt.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTVar; unfold bound_inF; auto;
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bool_constant b0); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply EAppAbs;
    try apply FTBC; try apply PECons; try apply PEEmp;
    try apply lemma_evals_trans with (Bool_constant (Bool.eqb (implb true b0) b0)); 
    try apply lemma_semantics_refn_imp; destruct b0; simpl; 
    try apply Refl; auto.
  - (* Bool_constant false *) exists (Lambda (Bool_constant true)); split; try split;
    try apply lem_step_evals; try apply lem_step_imp_ff.
    rewrite Denotes_equation_2; simpl; repeat split;
    try apply FTAbs with Base empty; try apply WFFTBasic;
    unfold unbind; unfold tsubBV; simpl; intros;
    try apply FTBC; trivial. 
    assert (isBool v_x0)
      by (apply lem_den_bools with (TRefn TBool PEmpty); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bool_constant true); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply EAppAbs; try apply H2;
    try apply FTBC; apply PECons; try apply PEEmp.
    apply lemma_evals_trans with (Bool_constant (Bool.eqb (implb false b0) true)); 
    try apply lemma_semantics_refn_imp; destruct b0; simpl; apply Refl.  
  Qed.  

Lemma lem_den_leqn : forall (n:Z), Denotes (primitive_type (Leqn n)) (Prim (Leqn n)).
Proof. intro n; unfold primitive_type; rewrite Denotes_equation_2;
  simpl; repeat split; try apply FTPrm; try apply WFFTBasic;
  unfold tsubBV; simpl; intros.
  assert (isInt v_x)
    by (apply lem_den_ints with (TRefn TInt PEmpty); simpl; trivial);
  destruct v_x eqn:E0; try contradiction.
  exists (Bool_constant (Z.leb n n0)); repeat split; unfold psubBV; simpl;
  try apply lem_step_evals; try apply lem_step_leqn;
  try apply FTBC; try apply PECons; try apply PEEmp; 
  apply lemma_evals_trans with (Bool_constant (Bool.eqb (Z.leb n n0) (Z.leb n n0)));
  try apply lemma_semantics_refn_leq;  
  set (b := Z.leb n n0); assert (Bool.eqb b b = true)
    by (pose proof (Bool.eqb_refl b); destruct (Bool.eqb b b); 
        try contradiction; reflexivity);
  rewrite H2; apply Refl. Qed.

Lemma lem_den_leq : Denotes (primitive_type Leq) (Prim Leq).
Proof. unfold primitive_type; rewrite Denotes_equation_2;
  repeat split; unfold tsubBV; simpl; try apply FTPrm; intros.
  assert (isInt v_x)
    by (apply lem_den_ints with (TRefn TInt PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  exists (Prim (Leqn n)); split; try split;
  try apply lem_step_evals; try apply lem_step_leq;
  apply lem_den_leqn. Qed. 

Lemma lem_den_eqn : forall (n:Z), Denotes (primitive_type (Eqn n)) (Prim (Eqn n)).
Proof. intro n; unfold primitive_type; rewrite Denotes_equation_2;
  simpl; repeat split; try apply FTPrm; try apply WFFTBasic;
  unfold tsubBV; simpl; intros.
  assert (isInt v_x)
    by (apply lem_den_ints with (TRefn TInt PEmpty); simpl; trivial);
  destruct v_x eqn:E0; try contradiction.
  exists (Bool_constant (Z.eqb n n0)); repeat split; unfold psubBV; simpl;
  try apply lem_step_evals; try apply lem_step_eqn;
  try apply FTBC; try apply PECons; try apply PEEmp; 
  apply lemma_evals_trans with (Bool_constant (Bool.eqb (Z.eqb n n0) (Z.eqb n n0)));
  try apply lemma_semantics_refn_eq;  
  set (b := Z.eqb n n0); assert (Bool.eqb b b = true)
    by (pose proof (Bool.eqb_refl b); destruct (Bool.eqb b b); 
        try contradiction; reflexivity);
  rewrite H2; apply Refl. Qed.

Lemma lem_den_eq : Denotes (primitive_type Eq) (Prim Eq).
Proof. unfold primitive_type; rewrite Denotes_equation_2;
  repeat split; unfold tsubBV; simpl; try apply FTPrm; intros.
  assert (isInt v_x)
    by (apply lem_den_ints with (TRefn TInt PEmpty); simpl; trivial).
  destruct v_x eqn:E; simpl in H1; try contradiction.
  exists (Prim (Eqn n)); split; try split;
  try apply lem_step_evals; try apply lem_step_eq;
  apply lem_den_eqn. Qed. 
  
Lemma lem_den_leql : Denotes (primitive_type Leql) (Prim Leql).
Proof. unfold primitive_type; rewrite Denotes_equation_4;
  repeat split; unfold tsubBTV; simpl; try apply FTPrm; intros.
  destruct (erase t_a) eqn:Heta; apply lem_erase_wftype in H0;
  rewrite Heta in H0; simpl in H0; inversion H0;
  try (simpl in H3; contradiction);
  destruct b eqn:B; simpl in H3; try contradiction;
  destruct t_a eqn:Hta; simpl in Heta; try discriminate;
  simpl in H; try contradiction; injection Heta as Heta;
  subst b1; subst t_a.
  - (* TBool *) exists (Prim Imp); split; try split; simpl;
    try apply lem_step_evals; try apply lem_step_leql_tbool;
    rewrite Denotes_equation_2; 
    repeat split; unfold tsubBV; simpl; try apply FTPrm; intros.
    assert (isBool v_x)
        by (apply lem_den_bools with (TRefn TBool ps); simpl; trivial).
    destruct v_x eqn:E; simpl in H1; try contradiction.
    destruct b1 eqn:B1.
    * (* Bool_constant true *) exists (Lambda (BV 0)); split; try split;
      try apply lem_step_evals; try apply lem_step_imp_tt.
      rewrite Denotes_equation_2; simpl; repeat split;
      try apply FTAbs with Base empty; try apply WFFTBasic;
      unfold unbind; unfold tsubBV; simpl; intros;
      try apply FTVar; unfold bound_inF; auto;
      assert (isBool v_x0)
        by (apply lem_den_bools with (TRefn TBool (psubBV_at 1 (Bool_constant true) ps)); 
            simpl; trivial);
      destruct v_x0 eqn:E0; try contradiction.
      exists (Bool_constant b2); repeat split; unfold psubBV; simpl;
      try apply lem_step_evals; try apply EAppAbs;
      try apply FTBC; try apply PECons; try apply PEEmp;
      try apply AddStep with  
        (App (App (Prim Eqv) (App (App (Prim Imp) (Bool_constant true)) (Bool_constant b2))) (Bool_constant b2));
      try apply EApp1; try apply EApp2; try apply EApp1; try apply EApp1;
      try apply lem_step_leql_tbool;
      try apply lemma_evals_trans with (Bool_constant (Bool.eqb (implb true b2) b2)); 
      try apply lemma_semantics_refn_imp; destruct b2; simpl; 
      try apply Refl; auto.
    * (* Bool_constant false *) exists (Lambda (Bool_constant true)); split; try split;
      try apply lem_step_evals; try apply lem_step_imp_ff.
      rewrite Denotes_equation_2; simpl; repeat split;
      try apply FTAbs with Base empty; try apply WFFTBasic;
      unfold unbind; unfold tsubBV; simpl; intros;
      try apply FTBC; trivial. 
      assert (isBool v_x0)
        by (apply lem_den_bools with (TRefn TBool (psubBV_at 1 (Bool_constant false) ps)); 
            simpl; trivial);
      destruct v_x0 eqn:E0; try contradiction.
      exists (Bool_constant true); repeat split; unfold psubBV; simpl;
      try apply lem_step_evals; try apply EAppAbs; try apply H8;
      try apply FTBC; apply PECons; try apply PEEmp.
      apply AddStep with  
        (App (App (Prim Eqv) (App (App (Prim Imp) (Bool_constant false)) (Bool_constant b2))) (Bool_constant true));
      try apply EApp1; try apply EApp2; try apply EApp1; try apply EApp1;
      try apply lem_step_leql_tbool;
      try apply lemma_evals_trans with (Bool_constant (Bool.eqb (implb false b2) true)); 
      try apply lemma_semantics_refn_imp; destruct b2; try apply Refl; simpl; exact I.  
  - (* TInt *) exists (Prim Leq); split; try split; simpl;
    try apply lem_step_evals; try apply lem_step_leql_tint;
    rewrite Denotes_equation_2; 
    repeat split; unfold tsubBV; simpl; try apply FTPrm; intros.
    assert (isInt v_x)
        by (apply lem_den_ints with (TRefn TInt ps); simpl; trivial).
    destruct v_x eqn:E; simpl in H1; try contradiction.
    exists (Prim (Leqn n)); split; try split;
    try apply lem_step_evals; try apply lem_step_leq.
    rewrite Denotes_equation_2; simpl; repeat split; 
    try apply FTPrm; unfold tsubBV; simpl; intros.
    assert (isInt v_x0)
      by (apply lem_den_ints with (TRefn TInt (psubBV_at 1 (Int_constant n) ps)); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bool_constant (Z.leb n n0)); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply lem_step_leqn;
    try apply FTBC; try apply PECons; try apply PEEmp.
    apply AddStep with  
        (App (App (Prim Eqv) (App (App (Prim Leq) (Int_constant n)) (Int_constant n0))) (Bool_constant (Z.leb n n0)));
    try apply EApp1; try apply EApp2; try apply EApp1; try apply EApp1;
    try apply lem_step_leql_tint;    
    try apply lemma_evals_trans with (Bool_constant (Bool.eqb (Z.leb n n0) (Z.leb n n0)));
    try apply lemma_semantics_refn_leq;  
    set (b' := Z.leb n n0); assert (Bool.eqb b' b' = true)
      by (pose proof (Bool.eqb_refl b'); destruct (Bool.eqb b' b'); 
          try contradiction; reflexivity);
    try rewrite H10; try apply Refl; auto. 
  Qed.

Lemma lem_den_eql : Denotes (primitive_type Eql) (Prim Eql).
Proof. unfold primitive_type; rewrite Denotes_equation_4;
  repeat split; unfold tsubBTV; simpl; try apply FTPrm; intros.
  destruct (erase t_a) eqn:Heta; apply lem_erase_wftype in H0;
  rewrite Heta in H0; simpl in H0; inversion H0;
  try (simpl in H3; contradiction);
  destruct b eqn:B; simpl in H3; try contradiction;
  destruct t_a eqn:Hta; simpl in Heta; try discriminate;
  simpl in H; try contradiction; injection Heta as Heta;
  subst b1; subst t_a.
  - (* TBool *) exists (Prim Eqv); split; try split; simpl;
    try apply lem_step_evals; try apply lem_step_eql_tbool;
    rewrite Denotes_equation_2; 
    repeat split; unfold tsubBV; simpl; try apply FTPrm; intros.
    assert (isBool v_x)
        by (apply lem_den_bools with (TRefn TBool ps); simpl; trivial).
    destruct v_x eqn:E; simpl in H1; try contradiction.
    destruct b1 eqn:B1.
    * (* Bool_constant true *) exists (Lambda (BV 0)); split; try split;
      try apply lem_step_evals; try apply lem_step_eqv_tt.
      rewrite Denotes_equation_2; simpl; repeat split;
      try apply FTAbs with Base empty; try apply WFFTBasic;
      unfold unbind; unfold tsubBV; simpl; intros;
      try apply FTVar; unfold bound_inF; auto;
      assert (isBool v_x0)
        by (apply lem_den_bools with (TRefn TBool (psubBV_at 1 (Bool_constant true) ps)); 
            simpl; trivial);
      destruct v_x0 eqn:E0; try contradiction.
      exists (Bool_constant b2); repeat split; unfold psubBV; simpl;
      try apply lem_step_evals; try apply EAppAbs;
      try apply FTBC; try apply PECons; try apply PEEmp;
      try apply AddStep with  
        (App (App (Prim Eqv) (App (App (Prim Eqv) (Bool_constant true)) (Bool_constant b2))) (Bool_constant b2));
      try apply EApp1; try apply EApp2; try apply EApp1; try apply EApp1;
      try apply lem_step_eql_tbool;
      try apply lemma_evals_trans with (Bool_constant (Bool.eqb (Bool.eqb true b2) b2)); 
      try apply lemma_semantics_refn_eqv; destruct b2; simpl; 
      try apply Refl; auto.
    * (* Bool_constant false *) exists (Prim Not); split; try split;
      try apply lem_step_evals; try apply lem_step_eqv_ff.
      rewrite Denotes_equation_2; simpl; repeat split;
      try apply FTPrm; unfold tsubBV; simpl; intros.
      assert (isBool v_x0)
        by (apply lem_den_bools with (TRefn TBool (psubBV_at 1 (Bool_constant false) ps)); 
            simpl; trivial);
      destruct v_x0 eqn:E0; try contradiction.
      exists (Bool_constant (negb b2)); repeat split; unfold psubBV; simpl;
      try apply lem_step_evals; try apply lem_step_not;
      try apply FTBC; apply PECons; try apply PEEmp.
      apply AddStep with  
        (App (App (Prim Eqv) (App (App (Prim Eqv) (Bool_constant false)) (Bool_constant b2))) (Bool_constant (negb b2)));
      try apply EApp1; try apply EApp2; try apply EApp1; try apply EApp1;
      try apply lem_step_eql_tbool;
      try apply lemma_evals_trans with (Bool_constant (Bool.eqb (Bool.eqb false b2) (negb b2)));
      try apply lemma_semantics_refn_eqv; destruct b2; try apply Refl; simpl; exact I.  
  - (* TInt *) exists (Prim Eq); split; try split; simpl;
    try apply lem_step_evals; try apply lem_step_eql_tint;
    rewrite Denotes_equation_2; 
    repeat split; unfold tsubBV; simpl; try apply FTPrm; intros.
    assert (isInt v_x)
        by (apply lem_den_ints with (TRefn TInt ps); simpl; trivial).
    destruct v_x eqn:E; simpl in H1; try contradiction.
    exists (Prim (Eqn n)); split; try split;
    try apply lem_step_evals; try apply lem_step_eq.
    rewrite Denotes_equation_2; simpl; repeat split; 
    try apply FTPrm; unfold tsubBV; simpl; intros.
    assert (isInt v_x0)
      by (apply lem_den_ints with (TRefn TInt (psubBV_at 1 (Int_constant n) ps)); simpl; trivial);
    destruct v_x0 eqn:E0; try contradiction.
    exists (Bool_constant (Z.eqb n n0)); repeat split; unfold psubBV; simpl;
    try apply lem_step_evals; try apply lem_step_eqn;
    try apply FTBC; try apply PECons; try apply PEEmp.
    apply AddStep with  
        (App (App (Prim Eqv) (App (App (Prim Eq) (Int_constant n)) (Int_constant n0))) (Bool_constant (Z.eqb n n0)));
    try apply EApp1; try apply EApp2; try apply EApp1; try apply EApp1;
    try apply lem_step_eql_tint;    
    try apply lemma_evals_trans with (Bool_constant (Bool.eqb (Z.eqb n n0) (Z.eqb n n0)));
    try apply lemma_semantics_refn_eq;  
    set (b' := Z.eqb n n0); assert (Bool.eqb b' b' = true)
      by (pose proof (Bool.eqb_refl b'); destruct (Bool.eqb b' b'); 
          try contradiction; reflexivity);
    try rewrite H10; try apply Refl; auto. 
  Qed.

Lemma lem_den_ty : forall (g:env) (th:csub) (c:prim),
    DenotesEnv g th -> Denotes (ctsubst th (primitive_type c)) (Prim c).
Proof. intros; rewrite lem_ctsubst_nofree; destruct c; 
  simpl; try reflexivity.
  - apply lem_den_and.
  - apply lem_den_or.
  - apply lem_den_not.
  - apply lem_den_eqv.
  - apply lem_den_imp.
  - apply lem_den_leq.
  - apply lem_den_leqn.
  - apply lem_den_eq.
  - apply lem_den_eqn.
  - apply lem_den_leql.
  - apply lem_den_eql.
  Qed.