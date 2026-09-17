Require Import Arith.
Require Import Lists.ListSet.

Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions. 
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.SystemFWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.
Require Import AutoProof.SystemRF.SystemRF.PrimitivesFTyping.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsSubstitution.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsWellFormedness.

(*------------------------------------------------------------------------------
----- | METATHEORY Development for the Underlying STLC :: Technical LEMMAS
------------------------------------------------------------------------------*)

(* -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 
   -- Consequences of the System F Well-Formedness Judgments -
   -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --  *)

Lemma lem_weaken_wfft' : forall (g'g : fenv) (t : ftype) (k : kind),
    WFFT g'g t k -> ( forall (g g':fenv) (x:var_name) (t_x:ftype),
        g'g = concatF g g' -> intersect (bindsF g) (bindsF g') = empty
                           -> ~ (in_envF x g) -> ~ (in_envF x g') 
                           -> WFFT (concatF (FCons x t_x g) g') t k ).
Proof. apply ( WFFT_ind 
  (fun (g'g : fenv) (t : ftype) (k : kind) => forall (g g':fenv) (x:var_name) (t_x:ftype),
      g'g = concatF g g' -> intersect (bindsF g) (bindsF g') = empty
                         -> ~ (in_envF x g) -> ~ (in_envF x g') 
                         -> WFFT (concatF (FCons x t_x g) g') t k  )). 
  - (* WFFTBasic *) intros. apply WFFTBasic; assumption.
  - (* WFFTFV    *) intros env a k Ha g g' x t_x; intros; subst env.
    apply lem_tvboundinF_weaken with a k g g' x t_x in Ha ;
    apply WFFTFV; assumption.
  - (* WFFTFunc  *) intros. apply WFFTFunc with k1 k2; 
    apply H0 || apply H2; assumption.
  - (* WFFTPoly  *) intro env; unfold in_envF; intros; 
    apply WFFTPoly with k_t (names_add x (union nms (bindsF (concatF g g')))); 
    intros; apply not_elem_names_add_elim in H5; destruct H5;
    apply not_elem_union_elim in H6; destruct H6;
    apply (H0 a H6 g (FConsT a k g') x t_x); subst env; simpl;
    apply not_elem_concatF_elim in H7; destruct H7; intuition. 
    * apply intersect_names_add_intro_r; assumption.
    * apply set_add_elim in H8; intuition.
  - (* WFFTKind *) intros; apply WFFTKind; apply H0; assumption.
  Qed.

Lemma lem_weaken_wfft : forall (g g':fenv) (t:ftype) (k:kind) (x:var_name) (t_x:ftype),
    WFFT (concatF g g') t k -> intersect (bindsF g) (bindsF g') = empty
                            -> ~ (in_envF x g) -> ~ (in_envF x g') 
                            -> WFFT (concatF (FCons x t_x g) g') t k.
Proof. intros; apply lem_weaken_wfft' with (concatF g g'); assumption || reflexivity. 
Qed.

Lemma lem_weaken_tv_wfft' : forall (g'g : fenv) (t : ftype) (k_t : kind),
    WFFT g'g t k_t -> ( forall (g g':fenv) (a:var_name) (k:kind),
        g'g = concatF g g' -> intersect (bindsF g) (bindsF g') = empty
                           -> ~ (in_envF a g) -> ~ (in_envF a g') 
                           -> WFFT (concatF (FConsT a k g) g') t k_t ).
Proof. apply ( WFFT_ind 
  (fun (g'g : fenv) (t : ftype) (k_t : kind) => forall (g g':fenv) (a:var_name) (k:kind),
      g'g = concatF g g' -> intersect (bindsF g) (bindsF g') = empty
                         -> ~ (in_envF a g) -> ~ (in_envF a g') 
                         -> WFFT (concatF (FConsT a k g) g') t k_t  )). 
  - (* WFFTBasic *) intros. apply WFFTBasic; assumption.
  - (* WFFTFV    *) intros env a0 k0 Ha0 g g' a k; intros; subst env;
    apply lem_tvboundinF_weaken_tv with a0 k0 g g' a k in Ha0;
    apply WFFTFV; assumption.
  - (* WFFTFunc  *) intros; apply WFFTFunc with k1 k2; 
    apply H0 || apply H2; assumption.
  - (* WFFTPoly  *) intros env k0; unfold in_envF; intros; 
    apply WFFTPoly with k_t (names_add a (union nms (bindsF (concatF g g')))); 
    intros; apply not_elem_names_add_elim in H5; destruct H5;
    apply not_elem_union_elim in H6; destruct H6;
    apply (H0 a0 H6 g (FConsT a0 k0 g') a k); subst env; simpl;
    apply not_elem_concatF_elim in H7; destruct H7; intuition. 
    * apply intersect_names_add_intro_r; assumption.
    * apply set_add_elim in H8; intuition.
  - (* WFFTKind  *) intros; apply WFFTKind; apply H0; assumption. 
  Qed.

Lemma lem_weaken_tv_wfft : forall (g g':fenv) (t:ftype) (k_t:kind) (a:var_name) (k:kind),
    WFFT (concatF g g') t k_t -> intersect (bindsF g) (bindsF g') = empty
                              -> ~ (in_envF a g) -> ~ (in_envF a g') 
                              -> WFFT (concatF (FConsT a k g) g') t k_t.
Proof. intros; apply lem_weaken_tv_wfft' with (concatF g g'); assumption || reflexivity. 
Qed.

Lemma lem_weaken_many_wfft : forall (g g':fenv) (t:ftype) (k:kind),
    WFFT g t k -> uniqueF g -> uniqueF g'
               -> intersect (bindsF g) (bindsF g') = empty
               -> WFFT (concatF g g') t k.
Proof. intros; induction g'; simpl; try assumption;
  simpl in H1; destruct H1;
  simpl in H2; apply intersect_names_add_elim_r in H2; destruct H2;
  apply IHg' in H2 as H'; try assumption;
  apply lem_weaken_wfft with (concatF g g') FEmpty t k x t0 in H'
    || apply lem_weaken_tv_wfft with (concatF g g') FEmpty t k a k0 in H';
  simpl in H'; unfold in_envF; simpl; 
  try (apply intersect_empty_r);
  try (apply uniqueF_concatF);
  try (apply not_elem_concatF_intro; assumption);  
  intuition. Qed.

(* -- -- -- -- -- -- -- -- -- -- -- -- ---
   -- -- Part of the Substitution Lemma --
   -- -- -- -- -- -- -- -- -- -- -- -- --- *)

(* -- System F types have only type variables because there are no refineemnts, so there's only 
   --     one version of the substitution lemmas: *)
Lemma lem_subst_tv_wfft' : forall (g'ag : fenv) (t : ftype) (k_t : kind),
    WFFT g'ag t k_t -> ( forall (g g':fenv) (a:var_name) (t_a:ftype) (k_a:kind),
        g'ag = concatF (FConsT a k_a g) g' 
                      -> uniqueF g -> uniqueF g'
                      -> intersect (bindsF g) (bindsF g') = empty
                      -> ~ (in_envF a g) -> ~ (in_envF a g') 
                      -> WFFT g t_a k_a
                      -> WFFT (concatF g (fesubFV a t_a g')) (ftsubFV a t_a t) k_t ).
Proof. apply ( WFFT_ind 
  (fun (g'ag : fenv) (t : ftype) (k_t : kind) => 
    forall (g g':fenv) (a:var_name) (t_a:ftype) (k_a:kind),
        g'ag = concatF (FConsT a k_a g) g' 
              -> uniqueF g -> uniqueF g'
              -> intersect (bindsF g) (bindsF g') = empty
              -> ~ (in_envF a g) -> ~ (in_envF a g') 
              -> WFFT g t_a k_a
              -> WFFT (concatF g (fesubFV a t_a g')) (ftsubFV a t_a t) k_t  )).
  - (* WFFTBasic *) intros; destruct b; simpl;
    (apply WFFTBasic; assumption) || (simpl in H; contradiction). 
  - (* WFFTFV *) intros env a0 k0; intros; subst env. 
    apply lem_tvboundinF_concatF in H; simpl in H; destruct H. destruct H. 
      * (* a0 = a *) destruct H; subst a0; subst k0; simpl. 
        assert (a = a) by reflexivity; apply Nat.eqb_eq in H; rewrite H.
        apply lem_weaken_many_wfft; try assumption;
        try (apply fesubFV_uniqueF); try (rewrite fesubFV_bindsF); assumption.      
      * (* a0 in g *) apply lem_tvboundin_inenvF in H as H'.
        pose proof tvbindsF_subset as Htv; unfold Subset in Htv; apply Htv in H';
        assert (a <> a0) by (unfold not; intro; subst a0; contradiction).
        apply Nat.eqb_neq in H0; simpl; rewrite H0.
        apply WFFTFV. apply lem_tvboundinF_concatF; intuition.
      * (* a0 in g' *) apply lem_tvboundin_inenvF in H as H'.
        pose proof tvbindsF_subset as Htv; unfold Subset in Htv; apply Htv in H';
        assert (a <> a0) by (unfold not; intro; subst a0; contradiction).
        apply Nat.eqb_neq in H0; simpl; rewrite H0.
        apply WFFTFV. apply (lem_tvboundinF_fesubFV a0 k0 a t_a g') in H.
        apply lem_tvboundinF_concatF; intuition.
  - (* WFFTFunc *) intros; apply WFFTFunc with k1 k2;
    apply H0 with k_a || apply H2 with k_a; assumption.
  - (* WFFTPoly *) intros env k0; unfold in_envF; intros;
    apply WFFTPoly with k_t (names_add a (union nms (bindsF (concatF g g'))));
    intros; apply not_elem_names_add_elim in H8; destruct H8;
    apply not_elem_union_elim in H9; destruct H9.
    assert (FConsT a0 k0 (concatF g (fesubFV a t_a g')) 
              = concatF g (fesubFV a t_a (FConsT a0 k0 g'))) as Henv' by reflexivity.
    rewrite Henv'; fold ftsubFV; rewrite <- lem_commute_ftsubFV_unbindFT.
    apply (H0 a0 H9 g (FConsT a0 k0 g') a t_a k_a); subst env; simpl; 
    apply not_elem_concatF_elim in H10; destruct H10; intuition.
    * apply intersect_names_add_intro_r; assumption.
    * apply set_add_elim in H11; intuition.
    * intuition.
    * apply lem_wfft_islcft with g k_a; assumption.
  - (* WFFTKind *) intros; apply WFFTKind; apply H0 with k_a; assumption.
  Qed.
    
Lemma lem_subst_tv_wfft : 
  forall (g g':fenv) (a:var_name) (t_a:ftype) (k_a:kind) (t : ftype) (k_t : kind),
      WFFT (concatF (FConsT a k_a g) g') t k_t
                    -> uniqueF g -> uniqueF g'
                    -> intersect (bindsF g) (bindsF g') = empty
                    -> ~ (in_envF a g) -> ~ (in_envF a g') 
                    -> WFFT g t_a k_a
                    -> WFFT (concatF g (fesubFV a t_a g')) (ftsubFV a t_a t) k_t.
Proof. intros; apply lem_subst_tv_wfft' with (concatF (FConsT a k_a g) g') k_a;
  assumption || reflexivity. Qed.
    
(* -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 
   -- Consequences of the System F Well Formed Envs -
   -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- *)

Lemma boundinF_wffe_wfft : forall (x:var_name) (t:ftype) (g:fenv),
    bound_inF x t g -> WFFE g -> WFFT g t Star.
Proof. intros x t g H p_wf_g; induction p_wf_g; simpl in H.
  - contradiction.
  - assert (FCons x0 t0 g = concatF (FCons x0 t0 g) FEmpty) as Henv by reflexivity;
    rewrite Henv; apply lem_weaken_wfft; unfold in_envF; simpl;
    try (apply wffe_uniqueF);
    try (apply intersect_empty_r);
    intuition; 
    destruct H; subst t0; 
    destruct k; assumption || apply WFFTKind; assumption.
  - assert (FConsT a k g = concatF (FConsT a k g) FEmpty) as Henv by reflexivity;
    rewrite Henv; apply lem_weaken_tv_wfft; unfold in_envF; simpl;
    try (apply wffe_uniqueF);
    try (apply intersect_empty_r);
    intuition.
  Qed.

(* -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- 
   -- Consequences of the System F Typing Judgments -
   -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- *)

Lemma lem_ftyping_wfft : forall (g:fenv) (e:expr) (t:ftype),
    HasFtype g e t -> WFFE g -> WFFT g t Star.
Proof. intros g e t p_e_t p_g. induction p_e_t.
  - (* FTBC *) apply WFFTKind; apply WFFTBasic; simpl; trivial.
  - (* FTIC *) apply WFFTKind; apply WFFTBasic; simpl; trivial.
  - (* FTVar *) destruct p_g; simpl in H; try contradiction;
    try (assert (FCons x0 t g = concatF (FCons x0 t g) FEmpty) by reflexivity);
    try (assert (FConsT a k g = concatF (FConsT a k g) FEmpty) by reflexivity);
    rewrite H2 || rewrite H1;
    apply lem_weaken_wfft || apply lem_weaken_tv_wfft;
    apply wffe_uniqueF in p_g as Hunq;
    try (apply intersect_empty_r); simpl;
    try intuition.
    destruct k; try rewrite H4; try assumption.
    * apply WFFTKind; try assumption.
    * apply boundinF_wffe_wfft with x; assumption.
    * apply boundinF_wffe_wfft with x; assumption.
  - (* FTPrm *) apply lem_wfft_erase_ty.
  - (* FTAbs *) apply WFFTFunc with k Star;
    pose proof (fresh_varF_not_elem nms g); destruct H2; try assumption;
    assert (g = concatF g FEmpty) by reflexivity; rewrite H4;
    apply lem_strengthen_wfft with (fresh_varF nms g) b; simpl; 
    try (apply H1); 
    try (apply WFFBind with k);
    try (apply wffe_uniqueF);
    try (apply intersect_empty_r); intuition.
  - (* FTApp *) apply IHp_e_t1 in p_g as p_g_bb'; inversion p_g_bb'.
      * destruct k2; assumption || apply WFFTKind; assumption.
      * inversion H.
  - (* FTAbsT *) apply WFFTPoly with Star (union nms (bindsF g)).
    intros; apply not_elem_union_elim in H1; destruct H1.
    apply H0; try (apply WFFBindT); assumption.
  - (* FTAppT *) apply IHp_e_t in p_g as p_g_kt'; inversion p_g_kt'.
      * pose proof (fresh_varF_not_elem nms g). 
        set (a' := fresh_varF nms g) in H9; destruct H9;
        apply H7 in H9 as p_a'g_t'.
        assert (g = concatF g (fesubFV a' (erase rt) FEmpty)) by reflexivity; rewrite H11.
        rewrite lem_ftsubFV_unbindFT with a' (erase rt) t';
        try apply (lem_ffreeTV_bound_in_fenv g (FTPoly k t') Star a' p_g_kt');
        try apply lem_subst_tv_wfft with k; simpl;  
        try apply wffe_uniqueF;
        try apply intersect_empty_r; intuition;  
        destruct k_t; assumption || apply WFFTKind; assumption.
      * inversion H5.
  - (* FTLet *) assert (g = concatF g FEmpty) by reflexivity; rewrite H1.
      pose proof (fresh_varF_not_elem nms g). 
      set (y := fresh_varF nms g) in H2; destruct H2.
      apply lem_strengthen_wfft with y b; simpl; 
      try apply H0; try apply WFFBind with Star; 
      try apply wffe_uniqueF;
      try apply intersect_empty_r; intuition.
  - (* FTAnn *) apply IHp_e_t in p_g; assumption.
  - (* FTIf *) apply IHp_e_t2; assumption.
  Qed.