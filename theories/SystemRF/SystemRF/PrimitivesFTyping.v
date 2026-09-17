Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.Semantics.
Require Import AutoProof.SystemRF.SystemRF.SystemFWellFormedness.
Require Import AutoProof.SystemRF.SystemRF.SystemFTyping.           

(* -- | Well Formedness of System F PRIMITIVES *)

Lemma lem_wfft_erase_ty : forall (g:fenv) (c:prim),  WFFT g (erase_ty c) Star.
Proof. intros. destruct c; try (apply WFFTPoly with Star (bindsF g))
                         ; intros; unfold unbindFT; simpl
                         ; try (apply WFFTFunc with Base Star)
                         ; try (apply WFFTFunc with Base Base)
                         ; try (apply WFFTFV)
                         ; try (apply WFFTKind)
                         ; try (apply WFFTBasic)
                         ; simpl; intuition. Qed.

(*-----------------------------------------------------------------------------
-- | (System F) TYPES of DELTA (of Applications of primitives)
-----------------------------------------------------------------------------*)

Definition isBool (e:expr) : Prop :=
    match e with
    | (Bool_constant _ ) => True
    | _       => False
    end.

Lemma lem_bool_values : forall (v:expr), 
    isValue v -> HasFtype FEmpty v (FTBasic TBool) ->  isBool v.
Proof. intros v val p_v_bl. inversion p_v_bl; subst v; 
    simpl in val; try contradiction.
    - (* v = Bool_constant *) auto.
    - (* v = Prim *) destruct c; simpl in H2; discriminate.
    Qed. 

Definition isInt (e:expr) : Prop :=
    match e with
    | (Int_constant _ ) => True
    | _       => False
    end.

Lemma lem_int_values : forall (v:expr),
    isValue v -> HasFtype FEmpty v (FTBasic TInt) -> isInt v.
Proof. intros v val p_v_Z. inversion p_v_Z; subst v; 
    simpl in val; try contradiction.
    - (* v = Int_constant *) auto.
    - (* v = Prim *) destruct c; simpl in H2; discriminate.
    Qed. 

Definition isLambdaOrPrim (e:expr) : Prop :=
    match e with
    | (Prim _)   => True
    | (Lambda _) => True
    | _          => False
    end.

Definition isLambdaTOrPrim (e:expr) : Prop :=
    match e with
    | (Prim _)      => True
    | (LambdaT _ _) => True
    | _             => False
    end.

Definition isPoly (c:prim) : Prop :=
    match c with
    | Eql     => True
    | Leql    => True
    | _       => False
    end.

Lemma lemma_function_values : forall (v:expr) (t:ftype) (t':ftype),
    isValue v -> HasFtype FEmpty v (FTFunc t t') -> isLambdaOrPrim v.
Proof.  intros v t t' val p_v_tt'; inversion p_v_tt'; subst v;
  simpl in val; try contradiction; auto. Qed.    

Lemma lemma_tfunction_values : forall (v:expr) (k:kind) (t:ftype),
    isValue v -> HasFtype FEmpty v (FTPoly k t) -> isLambdaTOrPrim v.
Proof. intros v k t val p_v_kt; inversion p_v_kt; subst v;
  simpl in val; try contradiction; auto. Qed.

Lemma lem_prim_compat_in_ftapp : forall (p:prim) (v:expr) (t:ftype),
    isValue v -> HasFtype FEmpty (App (Prim p) v) t -> isCompat' p v.
Proof. intros p v t val p_pv_t. 
  destruct p; inversion p_pv_t; inversion H2; subst b;
  (apply lem_bool_values || apply lem_int_values); assumption. Qed.

Lemma lem_delta_ftyp : forall (c:prim) (v:expr) (t_x:ftype) (t':ftype),
    isValue v -> HasFtype FEmpty (Prim c) (FTFunc t_x t') -> HasFtype FEmpty v t_x
              -> exists e, Some e = delta' c v /\ HasFtype FEmpty e t'.
Proof. intros c v t_x t' val p_c_txt' p_v_tx. 
  destruct c; inversion p_c_txt'; subst t_x;
  try (apply (lem_bool_values v val) in p_v_tx as Hv);
  try (apply (lem_int_values v val) in p_v_tx as Hv);
  destruct v; try contradiction;
  try (destruct b); simpl;
  ( match goal with
    | [ |- exists _, Some _ = Some ?term /\ _ ] => exists term
    end )
         ; split    
         ; try (apply FTAbs with Base empty)
         ; intros; unfold unbind; simpl
         ; try (apply FTApp with (FTBasic TBool))
         ; try (apply WFFTBasic)
         ; try (apply FTVar)
         ; try (apply FTPrm)
         ; try (apply FTBC)
         ; simpl; auto.
  Qed.

Lemma lem_base_types : forall (t:ftype),
    WFFT FEmpty t Base -> isClosedBaseF t.
Proof. intros t p_t_b; inversion p_t_b; subst t;
  try (destruct b); simpl; simpl in H;
  (trivial || contradiction). Qed.

Lemma lem_prim_compatT_in_ftappt : forall (c:prim) (rt:type) (t:ftype),
    HasFtype FEmpty (AppT (Prim c) rt) t  ->  isCompatT' c rt.
Proof. intros c rt t p_crt_t. destruct c; inversion p_crt_t; inversion H1;
  subst k; apply lem_base_types in H9; 
  destruct (erase rt) eqn:Hrt; try contradiction; 
  simpl; rewrite Hrt; trivial. Qed.
  
Lemma lem_deltaT_ftyp : forall (c:prim) (k:kind) (s:ftype) (t:type),
    HasFtype FEmpty (Prim c) (FTPoly k s) -> WFFT FEmpty (erase t) k
        -> exists e, Some e = deltaT' c t /\ HasFtype FEmpty e (ftsubBV (erase t) s).
Proof. intros c k s t p_c_aks p_emp_t; 
  destruct c; inversion p_c_aks; subst k;
  apply lem_base_types in p_emp_t as Ht;
  destruct (erase t) eqn:E; try contradiction;
  destruct b; try contradiction;
  unfold deltaT'; rewrite E;
  ( match goal with
    | [ |- exists _, Some _ = Some ?term /\ _ ] => exists term
    end )
         ; split
         ; try (apply FTPrm)
         ; auto.
  Qed.