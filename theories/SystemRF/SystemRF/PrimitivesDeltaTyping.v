Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.LocalClosure.
Require Import AutoProof.SystemRF.SystemRF.Semantics.
Require Import AutoProof.SystemRF.SystemRF.SystemFWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsSubstitution.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.WellFormedness.
Require Import AutoProof.SystemRF.SystemRF.PrimitivesFTyping.
Require Import AutoProof.SystemRF.SystemRF.PrimitivesWFType.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.Typing.
Require Import AutoProof.SystemRF.SystemRF.LemmasWeakenWF.
Require Import AutoProof.SystemRF.SystemRF.LemmasWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SubstitutionLemmaWF.
Require Import AutoProof.SystemRF.SystemRF.LemmasTyping.
Require Import AutoProof.SystemRF.SystemRF.LemmasSubtyping.
Require Import AutoProof.SystemRF.SystemRF.LemmasExactness. 
Require Import AutoProof.SystemRF.SystemRF.SubstitutionLemmaTyp.
Require Import AutoProof.SystemRF.SystemRF.SubstitutionLemmaTypTV.
Require Import AutoProof.SystemRF.SystemRF.LemmasTransitive.
Require Import AutoProof.SystemRF.SystemRF.LemmasInversion.

Require Import ZArith.

(* -- Lemma. Typing of \delta(c,v) and \delta_T(c,t) *)
Lemma lem_delta_ty'c : forall (c:prim) (v:expr),
    ~ isPoly c -> isValue v -> Hastype Empty v (primitive_input_type c)
               -> exists e, Some e = delta' c v /\ Hastype Empty e (tsubBV v (primitive_remaining_type c)).
Proof. intros c v np val p_v_inc; destruct c eqn:C;
  simpl in np; try contradiction;
  apply lem_typing_hasftype in p_v_inc as Hv; try apply WFEEmpty;
  simpl in Hv; 
  try apply (lem_bool_values v val) in Hv;
  try apply (lem_int_values v val) in Hv;
  destruct v eqn:V; simpl in Hv; try contradiction;
  assert (isCompat c v) as pf by (rewrite C; rewrite V; constructor);
  assert (forall m:Z, isCompat Leq (Int_constant m)) as pfL by constructor;
  assert (forall m:Z, isCompat Eq  (Int_constant m)) as pfE by constructor;
  assert (isCompatT Eql (TRefn TBool PEmpty)) as pfB by (apply isCptT_EqlB; trivial);
  assert (isCompatT Eql (TRefn TInt  PEmpty)) as pfZ by (apply isCptT_EqlZ; trivial);
  assert (forall m:Z, delta Leq (Int_constant m) (pfL m) = Prim (Leqn m)) as delL
      by (intro m; pose proof (delta_delta' Leq (Int_constant m) (pfL m)) as D; 
          simpl in D; injection D; trivial);
  assert (forall m:Z, delta Eq  (Int_constant m) (pfE m) = Prim (Eqn m))  as delE
      by (intro m; pose proof (delta_delta' Eq  (Int_constant m) (pfE m)) as D; 
          simpl in D; injection D; trivial);
  assert ( Prim Eqv = deltaT Eql (TRefn TBool PEmpty) pfB ) as delTB
    by (pose proof (deltaT_deltaT' Eql (TRefn TBool PEmpty) pfB) as D;
        simpl in D; injection D; trivial );
  assert ( Prim Eq  = deltaT Eql (TRefn TInt PEmpty) pfZ ) as delTZ
    by (pose proof (deltaT_deltaT' Eql (TRefn TInt PEmpty) pfZ) as D;
        simpl in D; injection D; trivial );         
  try destruct b; unfold tsubBV;  simpl;
  ( match goal with
    | [ |- exists _, Some _ = Some ?term /\ _ ] 
           => assert (delta c v pf = term) as del
                by ( pose proof (delta_delta' c v pf) as D; 
                     subst c; subst v; simpl in D; injection D; trivial ) ; 
              exists term
    end )  
          ; split ; try reflexivity 
          ; try apply T_Abs with Base empty
          ; try apply WFBase; trivial; intros       (* remove? *)
          ; unfold unbind; unfold unbindT; simpl ;  (* remove? *) 
  ( try match goal with
    | [ |- Hastype _ (FV ?yy) _ ] =>
            apply T_Sub 
              with (TRefn TBool (PCons (App (App (Prim Eqv) (FV yy)) (BV 0)) 
                                       PEmpty)) Base
          ; try apply T_Sub with (self (TRefn TBool PEmpty) (FV yy)  Base) Base
          ; try apply SBase with (singleton y); intros; unfold unbindP ;
          try ( apply IEvals; rewrite delTB; apply lem_step_evals; 
                apply EApp1; apply EApp1; apply EPrimT; trivial ) ;
          try ( apply IEvals2;
                apply AddStep 
                  with (App (App (Prim Eqv) (App (delta c v pf) (FV y))) (FV y0));
                subst c; subst v;
                try apply EApp1; try apply EApp2; 
                  try apply EApp1; try apply EPrim; try rewrite del; 
                try apply lem_step_evals; try apply EApp1; 
                  try apply EApp2; try apply EAppAbs; intuition ) ;
          try apply T_Var
    | [ |- Hastype (Cons _ _ _) (Bool_constant ?bb) _ ] =>
            apply T_Sub 
              with (TRefn TBool (PCons (App (App (Prim Eqv) (Bool_constant bb)) (BV 0)) 
                                       PEmpty)) Base
          ; try apply T_Sub with (self (TRefn TBool PEmpty)    (Bool_constant bb)     Base) Base 
          ; try apply SBase with (singleton y); intros; unfold unbindP; 
          try ( apply IEvals; rewrite delTB; apply lem_step_evals; 
                apply EApp1; apply EApp1; apply EPrimT; trivial ) ;
          try ( apply IEvals2;
                apply AddStep 
                  with (App (App (Prim Eqv) (App (delta c v pf) (FV y))) (FV y0));
                subst c; subst v;
                try apply EApp1; try apply EApp2; 
                  try apply EApp1; try apply EPrim; try rewrite del; 
                try apply lem_step_evals; try apply EApp1; 
                  try apply EApp2; try apply EAppAbs; intuition ) ;
          try apply T_BC
    | [ |- Hastype Empty (Bool_constant ?bb) _ ] =>
            apply T_Sub 
              with (TRefn TBool (PCons (App (App (Prim Eqv) (Bool_constant bb)) (BV 0)) 
                                       PEmpty)) Base
          ; try apply T_Sub with (self (TRefn TBool PEmpty)    (Bool_constant bb)     Base) Base
          ; try apply SBase with empty; intros; unfold unbindP
          ; try ( apply IEvals; rewrite delTB; apply lem_step_evals; 
                  apply EApp1; apply EApp1; apply EPrimT; trivial ) 
          ; try ( apply IEvals2; rewrite <- del; 
                  ( match goal with
                    | [ |- multistep (App (App _ (App _ (Int_constant _))) _) _] 
                            => try apply AddStep with (App (App (Prim Eqv) (App (Prim c) v)) (FV y))
                    | [ |- _ ] => trivial
                    end
                  ) ; subst c; subst v;
                  try apply lem_step_evals; apply EApp1; apply EApp2; try apply EApp1; 
                  try (apply EPrim || (rewrite <- delL; try apply EPrim)
                                   || (rewrite <- delE; try apply EPrim)); 
                  intuition ) 
          ; try apply T_BC
    | [ |- Hastype _ (Prim ?c') _ ] =>
            apply T_Sub with (primitive_type c') Star; try apply SFunc with empty; unfold primitive_input_type;
          try apply lem_sub_refl with Base; intros;
          try apply SBase with (singleton y); intros; unfold unbindP; 
          try apply IRefl;
          try ( apply IEvals2; apply lem_step_evals; apply EApp1; apply EApp2;
                try apply EApp1; try rewrite <- del; subst c; subst v; 
                try apply EPrim; intuition );
          try apply T_Prm; 
          try apply WFFunc with Base Base empty; intros
    end )  
          ; try apply WFBase
          ; try (apply WFRefn with (singleton y); try apply WFBase)
          ; try apply WFRefn with empty
          ; try apply WFBase; intros; unfold unbindP; simpl
          ; try apply PFTCons; try apply PFTEmp
          ; try apply FTApp with (FTBasic TBool)
          ; try apply FTApp with (FTBasic TBool)
          ; try ( apply FTApp with (FTBasic TInt); 
                  try apply FTApp with (FTBasic TInt); 
                  apply FTPrm || apply FTIC || apply FTVar) 
          ; try apply FTApp with (FTBasic TBool) 
          ; try apply FTApp with (FTBasic TBool)
          ; try apply FTPrm; try apply FTVar; try apply FTBC
          ; try discriminate; simpl; intuition. 
  Qed.

Lemma lem_deltaT_ty'c : forall (c:prim) (t:type),
    isPoly c -> noExists t -> WFtype Empty t Base
               -> exists e, Some e = deltaT' c t /\ 
                            Hastype Empty e (tsubBTV t (TFunc (primitive_input_type c) (primitive_remaining_type c))).
Proof. intros c t ispo noex p_emp_t; destruct c eqn:C;
  simpl in ispo; try contradiction;
  apply lem_erase_wftype in p_emp_t as Ht;
  apply lem_base_types in Ht; destruct t eqn:T; try destruct b eqn:B;
  simpl in Ht; try contradiction;
  unfold deltaT'; unfold erase;
  ( match goal with
    | [ |- exists _, Some _ = Some ?term /\ _ ] => exists term
    end ) 
          ; split ; unfold tsubBTV; simpl
          ; try ( match goal with 
                  | [ |- Hastype _ (Prim ?c) _ ] => apply T_Sub with (primitive_type c) Star
                  end ) 
          ; try apply T_Prm
          ; try apply WFFunc with Base Star empty; intros
          ; try apply WFFunc with Base Base (singleton y) ; intros ; fold openP_at 
          ; try assert (openP_at (0 + 1) y ps = ps) as Hps
              by ( apply lem_wftype_islct in p_emp_t as lct;  
                   unfold isLCT in lct; simpl in lct;         
                   apply lem_open_at_lc_at with 0; assumption )
          ; try assert (openP_at (0 + 1 + 1 + 1) y ps = ps) as Hps3
              by ( apply lem_wftype_islct in p_emp_t as lct;  
                   unfold isLCT in lct; simpl in lct;         
                   apply lem_open_at_lc_at with 0; 
                   apply lem_islc_at_weaken with 1 0; auto with * )              
          ; try rewrite Hps ; try rewrite Hps3; try reflexivity 

          ; try apply WFRefn with (names_add y0 (singleton y))
          ; try apply WFBase; fold openP_at; fold open_at 
          ; try apply lem_weaken_wf_top; intros
          ; destruct (Nat.eqb (0 + 1 + 1) 0) eqn:E0
          ; destruct (Nat.eqb (0 + 1 + 1) 1) eqn:E1
          ; destruct (Nat.eqb (0 + 1 + 1) 2) eqn:E2
          ; try (simpl in E0; discriminate E0)
          ; try (simpl in E1; discriminate E1)
          ; try (simpl in E2; discriminate E2)
          ; unfold unbindP; simpl; try assumption 
          ; try assert (openP_at 2 y0 ps = ps) as Hps2
              by ( apply lem_wftype_islct in p_emp_t as lct;  
                   unfold isLCT in lct; simpl in lct;         
                   apply lem_open_at_lc_at with 0; 
                   apply lem_islc_at_weaken with 1 0; auto with *  )
          ; try assert (openP_at 1 y1 ps = ps) as Hps1
              by ( apply lem_wftype_islct in p_emp_t as lct;  
                   unfold isLCT in lct; simpl in lct;         
                   apply lem_open_at_lc_at with 0; assumption  ) 
          ; try rewrite Hps2; try rewrite Hps1

          ; try apply PFTCons; try apply PFTEmp; try discriminate 
          ; try apply FTApp with (FTBasic TBool) 
          ; try apply FTApp with (FTBasic TBool) 
          ; try ( apply FTApp with (FTBasic TBool); apply FTPrm || apply FTVar; 
                  simpl; intuition ) 
          ; try apply FTApp with (FTBasic b)
          ; try apply FTApp with (FTBasic b) 
          ; try assert ( FTFunc (FTBasic b) (FTFunc (FTBasic b) (FTBasic TBool)) 
                          = ftsubBV (erase (TRefn b ps)) 
                                    (FTFunc (FTBasic (BTV 0)) 
                                            (FTFunc (FTBasic (BTV 0)) (FTBasic TBool))))
              as H' by reflexivity
          ; try rewrite H' ; try rewrite B 
          ; try apply FTAppT with Base
          ; try apply FTVar ; try apply FTPrm 
          ; try apply WFFTBasic

          ; try pose proof (lem_free_subset_binds Empty (TRefn TBool ps) Base p_emp_t) as Hf
          ; try pose proof (lem_free_subset_binds Empty (TRefn TInt  ps) Base p_emp_t) as Hf
          ; simpl; simpl in Hf; destruct Hf as [Hfv Hftv]
          ; try (apply Hftv || apply subset_trans with empty)
          ; try apply subset_empty_l
          ; try apply lem_wftype_islct with Empty Base
          ; try discriminate
          ; simpl ; try rewrite B ; auto with *

          ; apply SFunc with empty 
          ; try apply SBase with empty; intros; try apply IFaith
          ; intros; unfold unbindT; simpl 
          ; apply SFunc with (singleton y)
          ; try apply SBase with (singleton y); intros; try apply IFaith
          ; intros; unfold unbindT; simpl
          ; apply SBase with (names_add y0 (singleton y)) 
          ; intros; unfold unbindP; simpl 
          ; apply IEvals2
          ; try set (qs := (openP_at 1 y1 (openP_at 2 y0 (openP_at 3 y ps)))) 
          ; ( match goal with 
              | [ |- multistep (App (App (Prim Eqv)
                                  (App (App (AppT (Prim ?c) (TRefn ?b _)) _) _)) _) 
                             (App (App (Prim Eqv) (App (App (Prim ?c') _) _)) _) ] 
                        => assert (isCompatT c (TRefn b qs)) 
                              as pf by (constructor; trivial) ;
                           assert ( Prim c' = deltaT c (TRefn b qs) pf ) as delT
                              by (pose proof (deltaT_deltaT' c (TRefn b qs) pf) as D;
                                  simpl in D; injection D; trivial ) 
              end )
          ; apply lem_step_evals
          ; apply EApp1; apply EApp2; try apply EApp1; try apply EApp1
          ; trivial ; try rewrite delT ; try apply EPrimT ; trivial.
  Qed.

Lemma lem_prim_compat_in_tapp : forall (p:prim) (v:expr) (t:type),
    isValue v -> Hastype Empty (App (Prim p) v) t -> isCompat' p v.
Proof. intros p v t val p_pv_t; apply lem_prim_compat_in_ftapp with (erase t);
  assert (erase_env Empty = FEmpty) by reflexivity; try rewrite <- H;
  try apply lem_typing_hasftype; try apply WFEEmpty; assumption. Qed.
  
Lemma lem_prim_compatT_in_tappT : forall (c:prim) (t_a t:type),
    noExists t_a -> Hastype Empty (AppT (Prim c) t_a) t -> isCompatT' c t_a.
Proof. intros c t_a t noex p_cta_t; apply lem_prim_compatT_in_ftappt with (erase t);
  assert (erase_env Empty = FEmpty) by reflexivity; try rewrite <- H;
  try apply lem_typing_hasftype; try apply WFEEmpty; assumption. Qed.

Lemma lem_invert_prim : forall (g:env) (pc:expr) (t:type),
  Hastype g pc t -> (forall (c : prim) (s_x s' : type),
    pc = Prim c -> WFEnv g -> Subtype g t (TFunc s_x s')
                -> WFtype g (TFunc s_x s') Star
                -> Subtype g (primitive_type c) (TFunc s_x s')).
Proof. apply ( Hastype_ind
    ( fun (g:env) (pc:expr) (t:type) => forall (c : prim) (s_x s' : type),
        pc = Prim c -> WFEnv g -> Subtype g t (TFunc s_x s')
                -> WFtype g (TFunc s_x s') Star
                -> Subtype g (primitive_type c) (TFunc s_x s'))
  ); try discriminate; intros.
  - (* isTPrm *) injection H as C; subst c0; assumption.
  - (* isTSub *)
    apply H0; try assumption.
    eapply lem_sub_trans with
      (t' := T2) (k := Star) (k' := k) (k'' := Star).
    + exact H4.
    + eapply lem_typing_wf; eassumption.
    + exact H1.
    + exact H6.
    + exact H2.
    + exact H5.
  Qed.
  
Lemma lem_delta_typ : forall (c:prim) (v:expr) (t_x t': type),
    isValue v -> Hastype Empty (Prim c) (TFunc t_x t') -> Hastype Empty v t_x
              -> exists e, Some e = delta' c v /\ Hastype Empty e (TExists t_x t').
Proof. intros c v t_x t' val p_c_txt' p_v_tx. inversion p_c_txt';
  assert (Hastype Empty (App (Prim c) v) (TExists t_x t')) as p_cv_txt'
    by (apply T_App; assumption);
  assert (isCompat c v) as pf 
    by (apply compat_prop_set;
        apply lem_prim_compat_in_tapp with (TExists t_x t'); assumption);
  exists (delta c v pf); rewrite delta_delta'; split; try reflexivity.
  - (* isTPrm *) assert (primitive_type c = TFunc (primitive_input_type c) (primitive_remaining_type c)) as Hty
        by (destruct c; simpl in H2; try discriminate H2; simpl; reflexivity);
    assert (~ isPoly c) as Hmono
        by (destruct c; simpl in Hty; try discriminate Hty; intuition);
    rewrite Hty in H2; injection H2 as Htx Ht'; subst t_x t';
    apply T_Sub with (tsubBV v (primitive_remaining_type c)) Star;
    (* Hastype Empty (delta c v pf) (tsubBV v (primitive_remaining_type c)) *)
    pose proof (lem_delta_ty'c c v Hmono val p_v_tx); destruct H0; destruct H0;
    rewrite <- delta_delta' with c v pf in H0; injection H0 as H0; 
    subst x ; try apply H2;
    (* Subtype Empty (tsubBV v (primitive_remaining_type c)) (TExists (primitive_input_type c) (primitive_remaining_type c)) *)
    try apply lem_witness_sub with Star; try apply WFEEmpty;
    (* WFtype Empty (TExists (primitive_input_type c) (primitive_remaining_type c)) Star *)
    pose proof (lem_wf_ty' c Hmono); destruct H0 as [nms Hty'];
    try apply WFExis with Base nms;
    try apply lem_wf_intype; try apply Hty'; trivial.
  - (* isTSub *) assert (Subtype Empty (primitive_type c) (TFunc t_x t')) as p_tyc_txt'
        by (apply lem_invert_prim with (Prim c) (TFunc t_x t'); 
            try apply WFEEmpty; try apply lem_sub_refl with Star;
            destruct k; try (apply H0 || (apply WFKind; apply H0)); trivial);
    inversion p_tyc_txt'; try (destruct c; simpl in H5; discriminate H5);
    assert (primitive_type c = TFunc (primitive_input_type c) (primitive_remaining_type c)) as Hty
        by (destruct c; simpl in H5; try discriminate H5; simpl; reflexivity);
    assert (~ isPoly c) as Hmono
        by (destruct c; simpl in Hty; try discriminate Hty; intuition);
    apply T_Sub with (tsubBV v (primitive_remaining_type c)) Star; subst g0 s2 t2;
    rewrite Hty in H5; injection H5 as Hs1 Ht1; subst s1 t1;
    assert (Hastype Empty v (primitive_input_type c)) as p_v_in
      by (apply T_Sub with t_x Base; try apply lem_wf_intype; assumption);
    (* Hastype Empty (delta c v pf) (tsubBV v (primitive_remaining_type c)) *)
    pose proof (lem_delta_ty'c c v Hmono val p_v_in) as H';
    rewrite <- delta_delta' with c v pf in H';
    destruct H' as [x H']; destruct H';
    try rewrite <- delta_delta' with c v pf in H5; injection H5 as H5; 
    subst x ; try apply H6;
    (* Subtype Empty (tsubBV v (primitive_remaining_type c)) (TExists t_x t' *)
    try apply lem_sub_trans with (TExists t_x (primitive_remaining_type c)) Star Star Star;
    pose proof (lem_wf_ty' c Hmono); destruct H5 as [nms' Hty'];
    pose proof (fresh_not_elem nms'); set (y := fresh nms') in H5;
    try apply lem_witness_sub with Star;
    try apply lem_subtype_in_exists with Star (union nms nms');
    try (intros y0 Hy0; apply not_elem_union_elim in Hy0;
         destruct Hy0; apply H10; assumption);    
    try apply lem_wftype_islct with Empty Star;
    try rewrite lem_tsubFV_unbindT with y v (primitive_remaining_type c);
    try (destruct c; simpl; unfold not; intro ff; apply ff);
    try apply lem_subst_wf_top with (primitive_input_type c); try apply Hty';
    try apply lem_witness_sub with Star;
    (* WFtype Empty (TExists (primitive_input_type c) (primitive_remaining_type c)) Star, etc *)
    inversion H0; try inversion H7;
    try apply WFExis with Star (union nms' nms0);
    try intros y0 Hy0; try apply not_elem_union_elim in Hy0;
    try destruct Hy0; destruct k0;
    try (apply H14 || (apply WFKind; apply H14));
    try apply lem_narrow_wf_top with (primitive_input_type c); try apply Hty';
    try apply lem_typing_wf with v;
    try apply lem_typing_hasftype;
    try apply WFEEmpty;   simpl; intuition.
  Qed.

Lemma lem_invert_primT : forall (g:env) (pc:expr) (t:type),
  Hastype g pc t -> (forall (c : prim) (k : kind) (s' : type),
    pc = Prim c -> WFEnv g -> Subtype g t (TPoly k s')
                -> WFtype g (TPoly k s') Star
                -> Subtype g (primitive_type c) (TPoly k s')).
Proof. apply ( Hastype_ind
  ( fun (g:env) (pc:expr) (t:type) => forall (c: prim) (k:kind) (s':type),
        pc = Prim c -> WFEnv g -> Subtype g t (TPoly k s')
                    -> WFtype g (TPoly k s') Star
                    -> Subtype g (primitive_type c) (TPoly k s'))
  ); try discriminate; intros.
  - (* isTPrm *) injection H as C; subst c0; assumption.
  - (* isTSub *) rename t into e; rename T1 into s; rename T2 into t;
    apply H0; try apply lem_sub_trans with t Star k Star;
    try (apply lem_typing_wf with e; assumption); assumption.
  Qed.

Lemma lem_tyeql_forallbase : forall (c:prim) (k:kind) (s:type),
    Subtype Empty (primitive_type c) (TPoly k s) -> k = Base.
Proof. intros c k s p_tyc_ks; inversion p_tyc_ks;
  destruct c; simpl in H; try discriminate H; 
  injection H as Hk Hty'; subst k0; intuition. Qed.

Lemma lem_deltaT_typ : forall (c:prim) (t:type) (k:kind) (s': type),
    isMono t -> noExists t -> Hastype Empty (Prim c) (TPoly k s') 
              -> WFtype Empty t k
              -> exists e, Some e = deltaT' c t /\ Hastype Empty e (tsubBTV t s').
Proof. intros c t k s' mono noex p_c_ks' p_emp_t. inversion p_c_ks';
  assert (Hastype Empty (AppT (Prim c) t) (tsubBTV t s')) as p_ct_s't
    by (apply T_AppT with k; assumption);
  assert (isCompatT c t) as pf 
    by (apply compatT_prop_set;
        apply lem_prim_compatT_in_tappT with (tsubBTV t s'); assumption);
  exists (deltaT c t pf); rewrite <- deltaT_deltaT'; split; try reflexivity;
  try assert (Subtype Empty (primitive_type c) (TPoly k s')) as p_tyc_ks' (* if T_Sub *)
        by (apply lem_invert_primT with (Prim c) (TPoly k s'); 
            try apply WFEEmpty; try apply lem_sub_refl with Star;
            destruct k0; try (apply H0 || (apply WFKind; apply H0)); trivial);
  try inversion p_tyc_ks'; try (destruct c; simpl in H5; discriminate H5);
  assert (primitive_type c = TPoly Base (TFunc (primitive_input_type c) (primitive_remaining_type c))) as Hty
    by (destruct c; simpl in H2; try discriminate H2; 
        try simpl in H5; try discriminate H5; simpl; reflexivity);
  assert (isPoly c) as Hpoly
    by (destruct c; simpl in Hty; try discriminate Hty; simpl; intuition);
  rewrite Hty in H2 || rewrite Hty in H5; 
  injection H2 as Hk Ht' || injection H5 as Hk Ht'.
  - (* isTPrm *) subst s'; subst k;
    pose proof (lem_deltaT_ty'c c t Hpoly noex p_emp_t); 
    destruct H0 as [e H0]; destruct H0;
    rewrite deltaT_deltaT' with c t pf in H0; injection H0 as H0; subst e; assumption.
  - (* isTSub *) inversion H0; try inversion H5; 
    pose proof (lem_wf_ty Empty c) as Htyc;
    rewrite Hty in Htyc; inversion Htyc; try inversion H15.
    subst k k0 k1 k2 k3 g0 g1 g2 t1 t2 t3 t4;
    apply T_Sub with (tsubBTV t (TFunc  (primitive_input_type c) (primitive_remaining_type c))) Star;
    (* Hastype Empty (deltaT c t pf) (tsubBTV t (TFunc (primitive_input_type c) (primitive_remaining_type c))) *)
    pose proof (lem_deltaT_ty'c c t Hpoly noex p_emp_t) as H';
    rewrite deltaT_deltaT' with c t pf in H';
    destruct H' as [x H']; destruct H'; injection H5 as H5; 
    subst x ; try apply H6;
    (* WFtype Empty (tsubFTV a t (unbind_tvT a s')) Star *)
    try apply lem_typing_wf with (AppT (Prim c) t); try apply p_ct_s't;
    (* Subtype Empty (tsubBTV t (TFunc (primitive_input_type c) (primitive_remaining_type c))) (tsubBTV t s') *)
    pose proof (fresh_not_elem (union nms (union nms0 nms1))) as Ha; 
    set (a := fresh (union nms (union nms0 nms1))) in Ha;
    apply not_elem_union_elim in Ha; destruct Ha;
    apply not_elem_union_elim in H7; destruct H7;
    try rewrite lem_tsubFTV_unbind_tvT with a t (TFunc (primitive_input_type c) (primitive_remaining_type c));
    try rewrite lem_tsubFTV_unbind_tvT with a t s';
    try apply lem_subst_tv_subtype_top with Base Star k_t; try apply H11;
    assert (~ in_env a Empty) as Htriv by intuition;
    pose proof (lem_free_bound_in_env Empty (TPoly Base s') Star a H0 Htriv) 
      as Hfr; simpl in Hfr; destruct Hfr;
      try (destruct c; simpl; unfold not; intro ff; apply ff);
    try apply WFEEmpty; simpl; auto;
    destruct k_t0; try apply H17; try apply WFKind; 
    try apply H17; auto.
  Qed.
