Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.Semantics.
Require Import AutoProof.SystemRF.SystemRF.SystemFWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsSubstitution.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.PrimitivesFTyping.
Require Import AutoProof.SystemRF.SystemRF.SystemFLemmasWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SystemFLemmasSubstitution.

(*-----------------------------------------------------------------------------
----- | SOUNDNESS of the SYSTEM F LAMBDA CALCULUS
-----------------------------------------------------------------------------*)

  (* -- The System F Progress Lemma   *)
Theorem lemma_progress' : forall (g:fenv) (e:expr) (t:ftype),
    HasFtype g e t -> g = FEmpty -> isValue e \/ exists e'', Step e e''.
Proof. intros g e t p_e_t emp; induction p_e_t; simpl; subst g;
    (* values *) auto; right.
  - (* App e e' *) destruct e eqn:E; inversion p_e_t1; 
    try (simpl in H1; contradiction);
    try (destruct IHp_e_t1 as [H'|H']; try reflexivity; simpl in H'; try contradiction;
         destruct H'; exists (App x e'); apply EApp1; trivial).
      * (* e = Prim *) destruct IHp_e_t2; try reflexivity.
        { apply lem_prim_compat_in_ftapp with p e' b' in H0 as pf;
          try apply compat_prop_set in pf; try exists (delta p e' pf); 
          try apply EPrim; try apply FTApp with b; assumption. }
        { destruct H0 as [e'' H0]; exists (App (Prim p) e''); apply EApp2; simpl; trivial. }
      * (* e = Lambda e0 *) destruct IHp_e_t2; try reflexivity.
        { exists (subBV e' e0); apply EAppAbs; assumption. }      (* Left *)
        { destruct H5 as [e'' H5]; exists (App (Lambda e0) e'');  (* Right *)
          apply EApp2; simpl; trivial. }
  - (* AppT e rt *) destruct e eqn:E; inversion p_e_t; 
    try (simpl in H1; contradiction);
    try (destruct IHp_e_t as [H'|H']; try reflexivity; simpl in H'; try contradiction;
             destruct H'; exists (AppT x rt); apply EAppT; trivial).
      * (* e = Prim p *) apply FTAppT with FEmpty (Prim p) k t' rt in p_e_t as pf;
        try apply lem_prim_compatT_in_ftappt in pf; try apply compatT_prop_set in pf;
        try exists (deltaT p rt pf); try apply EPrimT; assumption.
      * (* e = LambdaT k e0 *) exists (subBTV rt e0); apply EAppTAbs; assumption.
  - (* Let e_x e *) destruct IHp_e_t; try reflexivity.
      * (* e_x val *) exists (subBV e_x e); apply ELetV; apply H1.
      * (* otherw. *) destruct H1 as [e_x' H1]; exists (Let e_x' e);
        apply ELet; apply H1.
  - (* Annot e t1 *) destruct IHp_e_t; try reflexivity.
      * (* e val *) exists e; apply EAnnV; apply H3.
      * (* other *) destruct H3 as [e'' H3]; exists (Annot e'' t1); apply EAnn; apply H3.
  - (* If e0 e1 e2 *) destruct IHp_e_t1; try reflexivity.
      * (* e0 val *) apply lem_bool_values in p_e_t1 as H_bool; try assumption.
        destruct e0; simpl in H_bool; try contradiction;
        destruct b; (exists e1; apply EIfT) || (exists e2; apply EIfF).
      * (* otherw *) destruct H as [e0' st_e0_e0']; exists (If e0' e1 e2); 
        apply EIf; apply st_e0_e0'.
  Qed.

Theorem lemma_progress : forall (e:expr) (t:ftype),
    HasFtype FEmpty e t -> isValue e \/ exists e'', Step e e''.
Proof. intros; apply lemma_progress' with FEmpty t; apply H || reflexivity. Qed.
  
Theorem lemma_preservation' : forall (g:fenv) (e:expr) (t:ftype) (e':expr),
    HasFtype g e t -> g = FEmpty -> Step e e' -> HasFtype FEmpty e' t.
Proof. intros g e; induction e; intros t0 e' p_e_t emp st_e_e'; simpl; subst g;
  apply lem_value_stuck in st_e_e' as H'; simpl in H'; try contradiction.
  - (* FTApp e1 e2 *) inversion p_e_t; apply lemma_progress in H2 as Hprog;
    destruct e1 eqn:E1; simpl in Hprog;
    (* impossible cases: *)
    try assert (isValue e1) as Hval by (subst e1; simpl; tauto);
    try apply lemma_function_values with e1 b t0 in Hval as Hfval; 
    try (rewrite E1; assumption);
    try (subst e1; contradiction);
    (* e1 not value: *)
    rewrite <- E1 in H2;
    try assert (exists e'' : expr, Step e1 e'') as HStep1 
        by (rewrite E1; intuition; apply Hprog);
    try (destruct HStep1 as [e1' HStep1]; 
         rewrite <- E1 in IHe1;
         apply IHe1 with (FTFunc b t0) e1' in H2;
         apply EApp1 with e1 e1' e2 in HStep1 as HStep; rewrite <- E1 in st_e_e';
         apply lem_sem_det with (App e1 e2) e' (App e1' e2) in st_e_e' as He';
         try subst e'; try apply FTApp with b; intuition );
    (* e1 a value: *)
    apply lemma_progress in H4 as He2; destruct He2 as [He2|He2];
    try (destruct He2 as [e2' He2];
         apply IHe2 with b e2' in H4 as H4'; trivial;
         apply EApp2 with e2 e2' e1 in Hval as HStep; try assumption;
         rewrite <- E1 in st_e_e';
         assert (e' = App e1 e2')
           by (apply lem_sem_det with (App e1 e2); assumption);
         subst e'; try subst t0;
         try apply FTApp with b; trivial );
    subst e1; subst t0.         
    * (* App (Prim p) val *) 
      apply (lem_prim_compat_in_ftapp p e2 b' He2) in p_e_t as pf;
      apply compat_prop_set in pf;
      apply lem_delta_ftyp with p e2 b b' in He2 as He'; try assumption;
      destruct He' as [del He']; destruct He';
      assert (del = delta p e2 pf)
        by (rewrite <- (delta_delta' p e2 pf) in H3; injection H3 as H3; assumption);
      subst del; assert (e' = delta p e2 pf)
        by (apply lem_sem_det with (App (Prim p) e2); 
            try apply EPrim; assumption) ;
      subst e'; assumption.
    * (* App (Lambda e0) val *) assert (e' = subBV e2 e0)
        by (apply lem_sem_det with (App (Lambda e0) e2); 
            try apply EAppAbs; assumption);
      assert (FEmpty = concatF FEmpty FEmpty) as Hemp by reflexivity;
      subst e'; inversion H2; pose proof (fresh_not_elem nms);
      rewrite lem_subFV_unbind with (fresh nms) e2 e0; try rewrite Hemp;
      try apply lem_subst_ftyp with b; simpl;
      try apply H9;
      apply lem_fv_bound_in_fenv 
        with FEmpty (Lambda e0) (FTFunc b b') (fresh nms) in H2 as H11;
      try simpl in H11; try destruct H11 ; trivial. 
  - (* FTAppT e t *) inversion p_e_t; apply lemma_progress in H1 as Hprog;
    destruct e eqn:E; simpl in Hprog;
    (* impossible cases: *)
    try assert (isValue e) as Hval by (subst e; simpl; tauto);
    try apply lemma_tfunction_values with e k t' in Hval as Hfval; 
    try (rewrite E; assumption);
    try (subst e; contradiction);
    (* e not value: *)
    rewrite <- E in H1;
    try assert (exists e'' : expr, Step e e'') as HStep 
        by (rewrite E; intuition);
    try (destruct HStep as [e'' HStep]; 
         rewrite <- E in IHe;
         apply IHe with (FTPoly k t') e'' in H1;
         apply EAppT with e e'' t in HStep as HStep0;
         rewrite <- E in st_e_e'; trivial;
         apply lem_sem_det with (AppT e t) e' (AppT e'' t) in st_e_e' as He';
         try subst e'; try apply FTAppT with k; assumption );
    subst e0; subst t0; subst e.         
    * (* AppT (Prim p) t *) apply lem_prim_compatT_in_ftappt in p_e_t as pf;
      apply compatT_prop_set in pf;
      apply lem_deltaT_ftyp with p k t' t in H1 as He'; try assumption;
      destruct He' as [delT He']; destruct He'.
      assert (delT = deltaT p t pf)
        by (rewrite -> (deltaT_deltaT' p t pf) in H; injection H as H; assumption).
      subst delT; assert (e' = deltaT p t pf)
        by (apply lem_sem_det with (AppT (Prim p) t); 
            try apply EPrimT; assumption);
      subst e'; assumption.
    * (* AppT (LambdaT k0 e1) t *) assert (e' = subBTV t e1)
        by (apply lem_sem_det with (AppT (LambdaT k0 e1) t); 
            try apply EAppTAbs; assumption);
      subst e'; inversion H1; pose proof (fresh_not_elem nms);
      assert (FEmpty = concatF FEmpty (fesubFV (fresh nms) (erase t) FEmpty)) 
        as Hemp by reflexivity;
      rewrite lem_subFTV_unbind_tv with (fresh nms) t e1;
      try rewrite lem_ftsubFV_unbindFT with (fresh nms) (erase t) t';
      try rewrite Hemp; try apply lem_subst_tv_ftyp with k; simpl;
      try apply H10; trivial; 
      apply lem_fv_bound_in_fenv 
        with FEmpty (LambdaT k0 e1) (FTPoly k t') (fresh nms) in H1 as Hfr1;
      apply lem_ftyping_wfft in H1;
      try apply lem_ffreeTV_bound_in_fenv
        with FEmpty (FTPoly k t') Star (fresh nms) in H1 as Hfr2;
      try simpl in Hfr1; try simpl in Hfr2; try destruct Hfr1; trivial || apply WFFEmpty.
  - (* FTLet e1 e2 *) inversion p_e_t; apply lemma_progress in H2 as Hprog;
    destruct Hprog.
    * (* e1 value *) assert (e' = subBV e1 e2)
        by (apply lem_sem_det with (Let e1 e2); try apply ELetV; assumption);
      subst e';
      pose proof (fresh_not_elem nms);
      assert (FEmpty = concatF FEmpty FEmpty) as Hemp by reflexivity;
      rewrite Hemp; rewrite lem_subFV_unbind with (fresh nms) e1 e2;
      try apply lem_subst_ftyp with b; simpl; try apply H4;
      apply lem_fv_bound_in_fenv 
        with FEmpty (Let e1 e2) t0 (fresh nms) in p_e_t as Hfr; 
      try simpl in Hfr; try destruct Hfr; 
      try apply not_elem_union_elim in H7; try destruct H7; trivial.
    * (* otherw *) destruct H5 as [e1' H5]; assert (e' = Let e1' e2)
        by (apply lem_sem_det with (Let e1 e2); try apply ELet; assumption);
      subst e'; apply FTLet with b nms;
      try apply IHe1; assumption || reflexivity.
  - (* FTAnn e t *) inversion p_e_t; apply lemma_progress in H7 as Hprog;
    destruct Hprog.
    * (* e value *) assert (e' = e)
        by (apply lem_sem_det with (Annot e t); try apply EAnnV; assumption);
      subst e'; apply H7.
    * (* otherw *) destruct H8 as [e'' H8]; assert (e' = Annot e'' t)
        by (apply lem_sem_det with (Annot e t); try apply EAnn; assumption);
      subst e'; apply FTAnn; try apply IHe; assumption || reflexivity.
  - (* FTIf *) inversion p_e_t; apply lemma_progress in H3 as Hprog; 
    destruct Hprog.
    * (* e0 value *) apply lem_bool_values in H3 as H_bool; try assumption;
      destruct e1; simpl in H_bool; try contradiction;
      destruct b.
      + (* True  *) assert (e' = e2) 
          by (apply lem_sem_det with (If (Bool_constant true) e2 e3); try apply EIfT; assumption);
        subst e'; apply H5.
      + (* False *) assert (e' = e3) 
          by (apply lem_sem_det with (If (Bool_constant false) e2 e3); try apply EIfF; assumption);
        subst e'; apply H6.
    * (* otherw *) destruct H7 as [e1' st_e1_e1']; assert (e' = If e1' e2 e3)
        by (apply lem_sem_det with (If e1 e2 e3); try apply EIf; assumption);
      subst e'; apply FTIf; try assumption; apply IHe1; trivial.
  - (* Error *) inversion p_e_t.
  Qed.

Theorem lemma_preservation : forall (e:expr) (t:ftype) (e':expr),
    HasFtype FEmpty e t -> Step e e' -> HasFtype FEmpty e' t.
Proof. intros; apply lemma_preservation' with FEmpty e; assumption || reflexivity. Qed.

Theorem lemma_many_preservation : forall (e e':expr) (b:ftype),
    multistep e e' -> HasFtype FEmpty e b -> HasFtype FEmpty e' b.
Proof. intros; induction H; try assumption.
  apply IHmultistep; apply lemma_preservation with e1; assumption. Qed.

(* Lemma. The underlying bare type system is sound. This is the textbook
          soundness proof for the STLC. *)
Theorem lemma_soundness : forall (e e':expr) (t:ftype),
    multistep e e' -> HasFtype FEmpty e t -> isValue e' \/ exists e'', Step e' e''.
Proof. intros e e' t ev_ee' p_e_t; induction ev_ee'.
  - apply lemma_progress with t; apply p_e_t.
  - apply IHev_ee'; apply lemma_preservation with e1; assumption. Qed. 
