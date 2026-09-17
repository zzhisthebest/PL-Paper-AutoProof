Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.Semantics.
Require Import AutoProof.SystemRF.SystemRF.SystemFWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.PrimitivesFTyping.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.Typing.
Require Import AutoProof.SystemRF.Denotations.ClosingSubstitutions.
Require Import AutoProof.SystemRF.Denotations.Denotations.

Require Import ZArith.

Lemma lem_step_and_tt : Step (App (Prim And) (Bool_constant true)) (Lambda (BV 0)).
Proof. assert (isCompat And (Bool_constant true)) as pfB by apply isCpt_And;
  assert (delta And (Bool_constant true) pfB = Lambda (BV 0))
      by (pose proof (delta_delta' And (Bool_constant true) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.

Lemma lem_step_and_ff : Step (App (Prim And) (Bool_constant false)) (Lambda (Bool_constant false)).
Proof. assert (isCompat And (Bool_constant false)) as pfB by apply isCpt_And;
  assert (delta And (Bool_constant false) pfB = Lambda (Bool_constant false))
      by (pose proof (delta_delta' And (Bool_constant false) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.

Lemma lem_step_or_tt : Step (App (Prim Or) (Bool_constant true)) (Lambda (Bool_constant true)).
Proof. assert (isCompat Or (Bool_constant true)) as pfB by apply isCpt_Or;
  assert (delta Or (Bool_constant true) pfB = Lambda (Bool_constant true))
      by (pose proof (delta_delta' Or (Bool_constant true) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.
  
Lemma lem_step_or_ff : Step (App (Prim Or) (Bool_constant false)) (Lambda (BV 0)).
Proof. assert (isCompat Or (Bool_constant false)) as pfB by apply isCpt_Or;
  assert (delta Or (Bool_constant false) pfB = Lambda (BV 0))
      by (pose proof (delta_delta' Or (Bool_constant false) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.

Lemma lem_step_not : forall (b:bool), 
    Step (App (Prim Not) (Bool_constant b)) (Bool_constant (negb b)).
Proof. intro b. assert (isCompat Not (Bool_constant b)) as pfB by apply isCpt_Not.
  assert (delta Not (Bool_constant b) pfB = Bool_constant (negb b))
      by (pose proof (delta_delta' Not (Bool_constant b) pfB) as D;
          destruct b; simpl in D; injection D; trivial ). 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.

Lemma lem_step_eqv_tt : Step (App (Prim Eqv) (Bool_constant true)) (Lambda (BV 0)).
Proof. assert (isCompat Eqv (Bool_constant true)) as pfB by apply isCpt_Eqv.
  assert (delta Eqv (Bool_constant true) pfB = Lambda (BV 0))
      by (pose proof (delta_delta' Eqv (Bool_constant true) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.

Lemma lem_step_eqv_ff : Step (App (Prim Eqv) (Bool_constant false)) (Prim Not).
Proof. assert (isCompat Eqv (Bool_constant false)) as pfB by apply isCpt_Eqv.
  assert (delta Eqv (Bool_constant false) pfB = Prim Not)
      by (pose proof (delta_delta' Eqv (Bool_constant false) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.  

Lemma lem_step_imp_tt : Step (App (Prim Imp) (Bool_constant true)) (Lambda (BV 0)).
Proof. assert (isCompat Imp (Bool_constant true)) as pfB by apply isCpt_Imp.
  assert (delta Imp (Bool_constant true) pfB = Lambda (BV 0))
      by (pose proof (delta_delta' Imp (Bool_constant true) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.

Lemma lem_step_imp_ff : Step (App (Prim Imp) (Bool_constant false)) (Lambda (Bool_constant true)).
Proof. assert (isCompat Imp (Bool_constant false)) as pfB by apply isCpt_Imp.
  assert (delta Imp (Bool_constant false) pfB = Lambda (Bool_constant true))
      by (pose proof (delta_delta' Imp (Bool_constant false) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.  

Lemma lem_step_leq : forall (n:Z), 
    Step (App (Prim Leq) (Int_constant n)) (Prim (Leqn n)).
Proof. intro n. assert (isCompat Leq (Int_constant n)) as pfB by apply isCpt_Leq.
  assert (delta Leq (Int_constant n) pfB = Prim (Leqn n))
      by (pose proof (delta_delta' Leq (Int_constant n) pfB) as D;
          simpl in D; injection D; trivial ). 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.  

Lemma lem_step_leqn : forall (n m:Z), 
    Step (App (Prim (Leqn n)) (Int_constant m)) (Bool_constant (Z.leb n m)).
Proof. intros n m. assert (isCompat (Leqn n) (Int_constant m)) as pfB by apply isCpt_Leqn.
  assert (delta (Leqn n) (Int_constant m) pfB = (Bool_constant (Z.leb n m)))
      by (pose proof (delta_delta' (Leqn n) (Int_constant m) pfB) as D;
          simpl in D; injection D; trivial ). 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.  
  
Lemma lem_step_eq : forall (n:Z), 
    Step (App (Prim Eq) (Int_constant n)) (Prim (Eqn n)).
Proof. intro n. assert (isCompat Eq (Int_constant n)) as pfB by apply isCpt_Eq.
  assert (delta Eq (Int_constant n) pfB = Prim (Eqn n))
      by (pose proof (delta_delta' Eq (Int_constant n) pfB) as D;
          simpl in D; injection D; trivial ). 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.    

Lemma lem_step_eqn : forall (n m:Z), 
    Step (App (Prim (Eqn n)) (Int_constant m)) (Bool_constant (Z.eqb n m)).
Proof. intros n m. assert (isCompat (Eqn n) (Int_constant m)) as pfB by apply isCpt_Eqn.
  assert (delta (Eqn n) (Int_constant m) pfB = (Bool_constant (Z.eqb n m)))
      by (pose proof (delta_delta' (Eqn n) (Int_constant m) pfB) as D;
          simpl in D; injection D; trivial ). 
  rewrite <- H; apply EPrim; simpl; exact I. Qed.  

Lemma lem_step_leql_tbool : forall (ps:preds), 
    Step (AppT (Prim Leql) (TRefn TBool ps)) (Prim Imp).
Proof. intro ps;
  assert (isCompatT Leql (TRefn TBool ps)) as pfB
      by (apply isCptT_LeqlB; auto);
  assert (Prim Imp = deltaT Leql (TRefn TBool ps) pfB)
      by (pose proof (deltaT_deltaT' Leql (TRefn TBool ps) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite H; apply EPrimT; simpl; exact I. Qed.

Lemma lem_step_leql_tint : forall (ps:preds), 
    Step (AppT (Prim Leql) (TRefn TInt ps)) (Prim Leq).
Proof. intro ps;
  assert (isCompatT Leql (TRefn TInt ps)) as pfZ
      by (apply isCptT_LeqlZ; auto);
  assert (Prim Leq = deltaT Leql (TRefn TInt ps) pfZ)
      by (pose proof (deltaT_deltaT' Leql (TRefn TInt ps) pfZ) as D;
          simpl in D; injection D; trivial ); 
  rewrite H; apply EPrimT; simpl; exact I. Qed.

Lemma lem_step_eql_tbool : forall (ps:preds), 
    Step (AppT (Prim Eql) (TRefn TBool ps)) (Prim Eqv).
Proof. intro ps;
  assert (isCompatT Eql (TRefn TBool ps)) as pfB
      by (apply isCptT_EqlB; auto);
  assert (Prim Eqv = deltaT Eql (TRefn TBool ps) pfB)
      by (pose proof (deltaT_deltaT' Eql (TRefn TBool ps) pfB) as D;
          simpl in D; injection D; trivial ); 
  rewrite H; apply EPrimT; simpl; exact I. Qed.

Lemma lem_step_eql_tint : forall (ps:preds), 
    Step (AppT (Prim Eql) (TRefn TInt ps)) (Prim Eq).
Proof. intro ps;
  assert (isCompatT Eql (TRefn TInt ps)) as pfZ
      by (apply isCptT_EqlZ; auto);
  assert (Prim Eq = deltaT Eql (TRefn TInt ps) pfZ)
      by (pose proof (deltaT_deltaT' Eql (TRefn TInt ps) pfZ) as D;
          simpl in D; injection D; trivial ); 
  rewrite H; apply EPrimT; simpl; exact I. Qed.

Lemma lemma_and_semantics : forall (p q:expr) (b b':bool),
    multistep p (Bool_constant b) -> multistep q (Bool_constant b')
        -> multistep (App (App (Prim And) p) q) (Bool_constant (b && b')).
Proof. intros; apply lemma_evals_trans with (App (App (Prim And) (Bool_constant b)) q).
  - apply lemma_app_many; apply lemma_app_many2; simpl; trivial.
  - destruct b.
    * apply lemma_evals_trans with (App (Lambda (BV 0)) (Bool_constant b'));
      try apply lemma_app_both_many; destruct b'; simpl; trivial;
      apply lem_step_evals; apply lem_step_and_tt || apply EAppAbs; 
      simpl; trivial.
    * apply lemma_evals_trans with (App (Lambda (Bool_constant false)) (Bool_constant b'));
      try apply lemma_app_both_many; try apply H0;
      try apply lem_step_evals; try apply lem_step_and_ff;
      try apply EAppAbs; simpl; trivial. 
  Qed.

Lemma lemma_or_semantics : forall (p q:expr) (b b':bool),
    multistep p (Bool_constant b) -> multistep q (Bool_constant b')
        -> multistep (App (App (Prim Or) p) q) (Bool_constant (b || b')).
Proof. intros; apply lemma_evals_trans with (App (App (Prim Or) (Bool_constant b)) q).
  - apply lemma_app_many; apply lemma_app_many2; simpl; trivial.
  - destruct b.
    * apply lemma_evals_trans with (App (Lambda (Bool_constant true)) (Bool_constant b'));
      try apply lemma_app_both_many; try apply H0;
      try apply lem_step_evals; try apply lem_step_or_tt;
      try apply EAppAbs; simpl; trivial. 
    * apply lemma_evals_trans with (App (Lambda (BV 0)) (Bool_constant b'));
      try apply lemma_app_both_many; destruct b'; simpl; trivial;
      apply lem_step_evals; apply lem_step_or_ff || apply EAppAbs; 
      simpl; trivial.
  Qed.

Lemma lemma_not_semantics : forall (p:expr) (b:bool),
    multistep p (Bool_constant b) -> multistep (App (Prim Not) p) (Bool_constant (negb b)).
Proof. intros; apply lemma_evals_trans with (App (Prim Not) (Bool_constant b));
  try apply lemma_app_many2;
  try (apply lem_step_evals; apply lem_step_not); simpl; trivial. Qed.

Lemma lemma_eqv_semantics : forall (p q:expr) (b b':bool),
    multistep p (Bool_constant b) -> multistep q (Bool_constant b') 
        -> multistep (App (App (Prim Eqv) p) q) (Bool_constant (Bool.eqb b b')).
Proof. intros; apply lemma_evals_trans with (App (App (Prim Eqv) (Bool_constant b)) q).
  - apply lemma_app_many; apply lemma_app_many2; simpl; trivial.
  - destruct b.
    * apply lemma_evals_trans with (App (Lambda (BV 0)) (Bool_constant b'));
      try apply lemma_app_both_many; destruct b'; simpl; trivial;
      apply lem_step_evals; apply lem_step_eqv_tt || apply EAppAbs; 
      simpl; trivial.
    * apply lemma_evals_trans with (App (Prim Not) (Bool_constant b'));
      try apply lemma_app_both_many; destruct b'; simpl; trivial;
      apply lem_step_evals; apply lem_step_eqv_ff || apply lem_step_not. 
  Qed.
  
Lemma lemma_imp_semantics : forall (p q:expr) (b b':bool),
    multistep p (Bool_constant b) -> multistep q (Bool_constant b') 
        -> multistep (App (App (Prim Imp) p) q) (Bool_constant (implb b b')).
Proof. intros; apply lemma_evals_trans with (App (App (Prim Imp) (Bool_constant b)) q).
  - apply lemma_app_many; apply lemma_app_many2; simpl; trivial.
  - destruct b.
    * apply lemma_evals_trans with (App (Lambda (BV 0)) (Bool_constant b'));
      try apply lemma_app_both_many; destruct b'; simpl; trivial;
      apply lem_step_evals; apply lem_step_imp_tt || apply EAppAbs; 
      simpl; trivial.
    * apply lemma_evals_trans with (App (Lambda (Bool_constant true)) (Bool_constant b'));
      try apply lemma_app_both_many; destruct b'; simpl; trivial;
      apply lem_step_evals; apply lem_step_imp_ff || apply EAppAbs;
      simpl; trivial. 
  Qed.

Lemma lemma_leq_semantics : forall (p q:expr) (n m:Z),
    multistep p (Int_constant n) -> multistep q (Int_constant m)
        -> multistep (App (App (Prim Leq) p) q) (Bool_constant (Z.leb n m)).
Proof. intros; apply lemma_evals_trans with (App (App (Prim Leq) (Int_constant n)) q).
  - apply lemma_app_many; apply lemma_app_many2; simpl; trivial.
  - apply lemma_evals_trans with (App (Prim (Leqn n)) (Int_constant m));
    try apply lemma_app_both_many; simpl; trivial;
    apply lem_step_evals; apply lem_step_leq || apply lem_step_leqn.
  Qed.
  
Lemma lemma_leqn_semantics : forall (q:expr) (n m:Z),
    multistep q (Int_constant m) -> multistep (App (Prim (Leqn n)) q) (Bool_constant (Z.leb n m)).
Proof. intros; apply lemma_evals_trans with (App (Prim (Leqn n)) (Int_constant m));
  try apply lemma_app_many2; simpl; trivial;
  apply lem_step_evals; apply lem_step_leqn. Qed.
  
Lemma lemma_eq_semantics : forall (p q:expr) (n m:Z),
    multistep p (Int_constant n) -> multistep q (Int_constant m)
        -> multistep (App (App (Prim Eq) p) q) (Bool_constant (Z.eqb n m)).
Proof. intros; apply lemma_evals_trans with (App (App (Prim Eq) (Int_constant n)) q).
  - apply lemma_app_many; apply lemma_app_many2; simpl; trivial.
  - apply lemma_evals_trans with (App (Prim (Eqn n)) (Int_constant m));
    try apply lemma_app_both_many; simpl; trivial;
    apply lem_step_evals; apply lem_step_eq || apply lem_step_eqn.
  Qed.
    
Lemma lemma_eqn_semantics : forall (q:expr) (n m:Z),
    multistep q (Int_constant m) -> multistep (App (Prim (Eqn n)) q) (Bool_constant (Z.eqb n m)).
Proof. intros; apply lemma_evals_trans with (App (Prim (Eqn n)) (Int_constant m));
  try apply lemma_app_many2; simpl; trivial;
  apply lem_step_evals; apply lem_step_eqn. Qed.

Lemma lemma_leql_bool_semantics : forall (p q:expr) (b b':bool),
    multistep p (Bool_constant b) -> multistep q (Bool_constant b')  
        -> multistep (App (App (AppT (Prim Leql) (TRefn TBool PEmpty)) p) q) (Bool_constant (implb b b')).
Proof. intros. apply lemma_evals_trans with (App (App (Prim Imp) p) q).
  - apply lem_step_evals; apply EApp1; apply EApp1;
    apply lem_step_leql_tbool.
  - apply lemma_imp_semantics; trivial.
  Qed.

Lemma lemma_leql_int_semantics : forall (p q:expr) (n m:Z),
    multistep p (Int_constant n) -> multistep q (Int_constant m)  
        -> multistep (App (App (AppT (Prim Leql) (TRefn TInt PEmpty)) p) q) (Bool_constant (Z.leb n m)).
Proof. intros. apply lemma_evals_trans with (App (App (Prim Leq) p) q).
  - apply lem_step_evals; apply EApp1; apply EApp1;
    apply lem_step_leql_tint.
  - apply lemma_leq_semantics; trivial.
  Qed.

Lemma lemma_eql_bool_semantics : forall (p q:expr) (b b':bool),
    multistep p (Bool_constant b) -> multistep q (Bool_constant b')  
        -> multistep (App (App (AppT (Prim Eql) (TRefn TBool PEmpty)) p) q) (Bool_constant (Bool.eqb b b')).
Proof. intros. apply lemma_evals_trans with (App (App (Prim Eqv) p) q).
  - apply lem_step_evals; apply EApp1; apply EApp1;
    apply lem_step_eql_tbool.
  - apply lemma_eqv_semantics; trivial.
  Qed.

Lemma lemma_eql_int_semantics : forall (p q:expr) (n m:Z),
    multistep p (Int_constant n) -> multistep q (Int_constant m)  
        -> multistep (App (App (AppT (Prim Eql) (TRefn TInt PEmpty)) p) q) (Bool_constant (Z.eqb n m)).
Proof. intros. apply lemma_evals_trans with (App (App (Prim Eq) p) q).
  - apply lem_step_evals; apply EApp1; apply EApp1;
    apply lem_step_eql_tint.
  - apply lemma_eq_semantics; trivial.
  Qed.

(* ---------------------------------------------------------------------------
   -- | BUILT-IN PRIMITIVES : Big-Step-style SEMANTICS for ty(c)'s refinement 
   --------------------------------------------------------------------------- *)

Lemma lemma_semantics_refn_and : forall (b b' b'' : bool), 
    multistep (App (App (Prim Eqv) (App (App (Prim And) (Bool_constant b)) (Bool_constant b'))) (Bool_constant b'')) 
            (Bool_constant (Bool.eqb (andb b b') b'')).
Proof. intros. apply lemma_eqv_semantics; try apply lemma_and_semantics;
  apply Refl. Qed.

Lemma lemma_semantics_refn_or : forall (b b' b'' : bool), 
    multistep (App (App (Prim Eqv) (App (App (Prim Or) (Bool_constant b)) (Bool_constant b'))) (Bool_constant b''))
            (Bool_constant (Bool.eqb (orb b b') b'')).
Proof. intros. apply lemma_eqv_semantics; try apply lemma_or_semantics;
  apply Refl. Qed.

Lemma lemma_semantics_refn_not : forall (b b' : bool), 
    multistep (App (App (Prim Eqv) (App (Prim Not) (Bool_constant b))) (Bool_constant b'))
            (Bool_constant (Bool.eqb (negb b) b')).
Proof. intros; apply lemma_eqv_semantics; try apply lemma_not_semantics;
  apply Refl. Qed.
  
Lemma lemma_semantics_refn_eqv  : forall (b b' b'' : bool), 
    multistep (App (App (Prim Eqv) (App (App (Prim Eqv) (Bool_constant b)) (Bool_constant b'))) (Bool_constant b''))
            (Bool_constant (Bool.eqb (Bool.eqb b b') b'')).
Proof. intros; repeat apply lemma_eqv_semantics; apply Refl. Qed.

Lemma lemma_semantics_refn_imp  : forall (b b' b'' : bool), 
    multistep (App (App (Prim Eqv) (App (App (Prim Imp) (Bool_constant b)) (Bool_constant b'))) (Bool_constant b''))
            (Bool_constant (Bool.eqb (implb b b') b'')).
Proof. intros. apply lemma_eqv_semantics; try apply lemma_imp_semantics;
  apply Refl. Qed.      

Lemma lemma_semantics_refn_leq : forall (n m : Z) (b'':bool),
    multistep (App (App (Prim Eqv) (App (App (Prim Leq) (Int_constant n)) (Int_constant m))) (Bool_constant b''))
            (Bool_constant (Bool.eqb (Z.leb n m) b'')).
Proof. intros. apply lemma_eqv_semantics; try apply lemma_leq_semantics;
  apply Refl. Qed.

Lemma lemma_semantics_refn_leqn : forall (n m : Z) (b'':bool),
    multistep (App (App (Prim Eqv) (App (Prim (Leqn n)) (Int_constant m))) (Bool_constant b''))
            (Bool_constant (Bool.eqb (Z.leb n m) b'')).
Proof. intros. apply lemma_eqv_semantics; try apply lemma_leqn_semantics;
  apply Refl. Qed.

Lemma lemma_semantics_refn_eq : forall (n m : Z) (b'':bool),
    multistep (App (App (Prim Eqv) (App (App (Prim Eq) (Int_constant n)) (Int_constant m))) (Bool_constant b''))
            (Bool_constant (Bool.eqb (Z.eqb n m) b'')).
Proof. intros. apply lemma_eqv_semantics; try apply lemma_eq_semantics;
  apply Refl. Qed.

Lemma lemma_semantics_refn_eqn : forall (n m : Z) (b'':bool),
    multistep (App (App (Prim Eqv) (App (Prim (Eqn n)) (Int_constant m))) (Bool_constant b''))
            (Bool_constant (Bool.eqb (Z.eqb n m) b'')).
Proof. intros. apply lemma_eqv_semantics; try apply lemma_eqn_semantics;
  apply Refl. Qed.
