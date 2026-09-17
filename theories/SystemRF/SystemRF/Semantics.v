Require Import Arith.
Require Import ZArith.

Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.

(*------------------------------------------------------------------------
----- | OPERATIONAL SEMANTICS (Small Step)
------------------------------------------------------------------------*)

(* E-Prim    c v -> delta(c,v)
-- E-App1    e e1 -> e' e1 if e->e'
-- E-App2    v e  -> v e'  if e->e'
-- E-AppAbs  (\x. e) v -> e[v/x]
-- E-primT   c [t] -> deltaT(c,t)
-- E-AppT    e [t] -> e' [t] id e->e'
-- E-AppTAbs (/\a. e) [t] -> e[t/a]
-- E-Let     let x=e_x in e -> let x=e'_x in e if e_x->e'_x
-- E-LetV    let x=v in e -> e[v/x]
-- E-Ann     e:t -> e':t  if e->e'
-- E-AnnV    v:t -> v  
-- E-If      if e0 then e1 else e2 -> if e0' then e1 else e2 if e0->e0'
-- E-IfT     if true  then e1 else e2 -> e1
-- E-IfF     if false then e1 else e2 -> e2
*)

(* is compatible。isCompat p e 表示 primitive p 与参数 e 兼容 *)
Inductive isCompat : prim -> expr -> Set :=   (* can't use Prop here*)
    | isCpt_And  : forall b, isCompat And (Bool_constant b) 
    | isCpt_Or   : forall b, isCompat Or  (Bool_constant b)      
    | isCpt_Not  : forall b, isCompat Not (Bool_constant b)    
    | isCpt_Eqv  : forall b, isCompat Eqv (Bool_constant b)      
    | isCpt_Imp  : forall b, isCompat Imp (Bool_constant b)   
    | isCpt_Leq  : forall n, isCompat Leq (Int_constant n) 
    | isCpt_Leqn : forall n m, isCompat (Leqn n) (Int_constant m) 
    | isCpt_Eq   : forall n, isCompat Eq  (Int_constant n) 
    | isCpt_Eqn  : forall n m, isCompat (Eqn n) (Int_constant m).
    
Definition isCompat' (c:prim) (v:expr) : Prop := 
    match c, v with
    | And      , (Bool_constant _)  => True
    | Or       , (Bool_constant _)  => True
    | Not      , (Bool_constant _)  => True
    | Eqv      , (Bool_constant _)  => True
    | Imp      , (Bool_constant _)  => True
    | Leq      , (Int_constant n)     => True
    | (Leqn n) , (Int_constant m)     => True
    | Eq       , (Int_constant n)     => True
    | (Eqn n)  , (Int_constant m)     => True
    | _        , _          => False
    end.

Lemma compat_prop_set : forall (c:prim) (v:expr),
    isCompat' c v -> isCompat c v.
Proof. intros c v cpt'. destruct c; destruct v; 
  simpl in cpt'; try contradiction. 
  - apply isCpt_And.
  - apply isCpt_Or.
  - apply isCpt_Not.
  - apply isCpt_Eqv.
  - apply isCpt_Imp.
  - apply isCpt_Leq.
  - apply isCpt_Leqn.
  - apply isCpt_Eq.
  - apply isCpt_Eqn. 
  Qed.
    
(* primitive operation 的计算函数
输入：
  c   primitive
  v   已经收到的参数
  pf  c 和 v 确实兼容的证据
输出是计算后的 expr。 *)
Definition delta (c : prim) (v : expr) (pf : isCompat c v) : expr :=
    match pf with
    | isCpt_And b    => match b with 
                        | true  => Lambda (BV 0)
                        | false => Lambda (Bool_constant false)
                        end
    | isCpt_Or b     => match b with  
                        | true  => Lambda (Bool_constant true)
                        | false => Lambda (BV 0)
                        end
    | isCpt_Not b    => match b with 
                        | true  => Bool_constant false
                        | false => Bool_constant true
                        end
    | isCpt_Eqv b    => match b with
                        | true  => Lambda (BV 0)
                        | false => Prim Not   (* Lambda (App (Prim Not) (BV 0)) *)
                        end
    | isCpt_Imp b    => match b with 
                        | true  => Lambda (BV 0)
                        | false => Lambda (Bool_constant true)
                        end
    | isCpt_Leq  n   => Prim (Leqn n)
    | isCpt_Leqn n m => Bool_constant (Z.leb n m)
    | isCpt_Eq   n   => Prim (Eqn n)
    | isCpt_Eqn n m  => Bool_constant (Z.eqb n m)
    end. 

Definition delta' (c : prim) (v : expr) : option expr :=
    match c, v with
    | And      , (Bool_constant true)  => Some  (Lambda (BV 0))
    | And      , (Bool_constant false) => Some  (Lambda (Bool_constant false))
    | Or       , (Bool_constant true)  => Some  (Lambda (Bool_constant true))
    | Or       , (Bool_constant false) => Some  (Lambda (BV 0))
    | Not      , (Bool_constant true)  => Some  (Bool_constant false)
    | Not      , (Bool_constant false) => Some  (Bool_constant true)
    | Eqv      , (Bool_constant true)  => Some  (Lambda (BV 0))
    | Eqv      , (Bool_constant false) => Some  (Prim Not)  (* Lambda (App (Prim Not) (BV 0))*)
    | Imp      , (Bool_constant true)  => Some  (Lambda (BV 0))
    | Imp      , (Bool_constant false) => Some  (Lambda (Bool_constant true))
    | Leq      , (Int_constant n)     => Some  (Prim (Leqn n))
    | (Leqn n) , (Int_constant m)     => Some  (Bool_constant (Z.leb n m))
    | Eq       , (Int_constant n)     => Some  (Prim (Eqn n))
    | (Eqn n)  , (Int_constant m)     => Some  (Bool_constant (Z.eqb n m))
    | _        , _          => None 
    end.

Lemma delta_delta' : forall (c : prim) (v : expr) (pf : isCompat c v),
    Some (delta c v pf) = (delta' c v).
Proof. intros. destruct pf; try (destruct b); simpl; reflexivity. Qed.

Lemma delta_pf_indep : forall (c : prim) (v : expr) (pf pf' : isCompat c v),
    delta c v pf = delta c v pf'.
Proof. intros. assert (Some (delta c v pf) = Some (delta c v pf')).
  - transitivity (delta' c v); (apply delta_delta' || symmetry; apply delta_delta'). 
  - injection H. trivial. Qed. 

Inductive isCompatT : prim -> type -> Set :=
    | isCptT_EqlB  : forall t, erase t = FTBasic TBool  ->  isCompatT Eql t
    | isCptT_EqlZ  : forall t, erase t = FTBasic TInt   ->  isCompatT Eql t
    | isCptT_LeqlB : forall t, erase t = FTBasic TBool  ->  isCompatT Leql t
    | isCptT_LeqlZ : forall t, erase t = FTBasic TInt   ->  isCompatT Leql t.

Definition isCompatT' (c:prim) (t:type) : Prop := 
    match c, (erase t) with
    | Eql  , FTBasic TBool => True
    | Eql  , FTBasic TInt  => True
    | Leql , FTBasic TBool => True
    | Leql , FTBasic TInt  => True
    | _    , _             => False
    end. 

Lemma compatT_prop_set : forall (c:prim) (t:type),
    isCompatT' c t -> isCompatT c t.
Proof. intros c t cpt'. destruct c; destruct (erase t) eqn:T;  
  simpl in cpt'; try (rewrite T in cpt'); try contradiction;
  destruct b;  try contradiction.
  - apply isCptT_LeqlB; trivial.
  - apply isCptT_LeqlZ; trivial.
  - apply isCptT_EqlB; trivial.
  - apply isCptT_EqlZ; trivial.
  Qed.      

(*{ t:type | isCompatT c t } -> { e':Value | Set_emp (fv e') && Set_emp (ftv e') } *)
Definition deltaT (c : prim) (t : type) (pf : isCompatT c t) : expr :=
    match pf with
    | isCptT_EqlB  t _ => Prim Eqv
    | isCptT_EqlZ  t _ => Prim Eq
    | isCptT_LeqlB t _ => Prim Imp
    | isCptT_LeqlZ t _ => Prim Leq
    end.

Definition deltaT' (c : prim) (t : type) : option expr :=
    match c, (erase t) with
    | Eql  , FTBasic TBool  => Some (Prim Eqv)
    | Eql  , FTBasic TInt   => Some (Prim Eq)
    | Leql , FTBasic TBool  => Some (Prim Imp)
    | Leql , FTBasic TInt   => Some (Prim Leq)
    | _    , _              => None
    end.

Lemma deltaT_deltaT' : forall (c : prim) (t : type) (pf : isCompatT c t),
    deltaT' c t =  Some (deltaT c t pf).
Proof. intros. destruct pf as [t H|t H|t H|t H]; simpl; rewrite H; reflexivity. Qed.

Lemma deltaT_pf_indep : forall (c : prim) (t : type) (pf pf' : isCompatT c t),
    deltaT c t pf = deltaT c t pf'.
Proof. intros. assert (Some (deltaT c t pf) = Some (deltaT c t pf')).
  - apply eq_stepl with (deltaT' c t); apply deltaT_deltaT'.
  - injection H as H'; assumption. Qed.

Lemma deltaT_exchange_type : 
  forall (c:prim) (t t':type) (pf:isCompatT c t) (pf':isCompatT c t'),
    erase t = erase t' -> deltaT c t pf = deltaT c t' pf'.
Proof. intros. assert (deltaT' c t = deltaT' c t')
      by (inversion pf; simpl; rewrite <- H; rewrite H0; reflexivity);
  rewrite deltaT_deltaT' with c t  pf  in H0;
  rewrite deltaT_deltaT' with c t' pf' in H0;
  injection H0 as H0; apply H0. Qed.

(* 定义单步归约 *)
Inductive Step : expr -> expr -> Prop :=
    | EPrim : forall (c:prim) (w : expr) (pf : isCompat c w), 
          isValue w -> Step (App (Prim c) w) (delta c w pf)
    | EApp1 : forall (e e' e1 : expr),
          Step e e' -> Step (App e e1) (App e' e1)
    | EApp2 : forall (e e' v : expr),
          isValue v -> Step e e' -> Step (App v e) (App v e')
    | EAppAbs : forall (e v : expr),
          isValue v -> Step (App (Lambda e) v) (subBV v e)
    | EPrimT : forall (c : prim) (t : type) (pf : isCompatT c t),
          noExists t -> Step (AppT (Prim c) t) (deltaT c t pf) 
    | EAppT : forall (e e' : expr) (t : type),
          noExists t -> Step e e' -> Step (AppT e t) (AppT e' t)
    | EAppTAbs : forall (k : kind) (e : expr) (t : type),
          noExists t -> Step (AppT (LambdaT k e) t) (subBTV t e)
    | ELet  : forall (e_x e_x' e : expr),
          Step e_x e_x' -> Step (Let e_x e) (Let e_x' e)
    | ELetV : forall (v : expr) (e : expr), 
          isValue v -> Step (Let v e) (subBV v e)
    | EAnn  : forall (e e' : expr) (t : type),
          Step e e' -> Step (Annot e t) (Annot e' t)
    | EAnnV : forall (v : expr) (t : type),
          isValue v -> Step (Annot v t) v
    | EIf : forall (e0 e0' e1 e2 : expr),
          Step e0 e0' -> Step (If e0 e1 e2) (If e0' e1 e2)
    | EIfT : forall (e1 e2 : expr), Step (If (Bool_constant true ) e1 e2) e1    
    | EIfF : forall (e1 e2 : expr), Step (If (Bool_constant false) e1 e2) e2 .
    
(* 多步归约 *)
Inductive multistep : expr -> expr -> Prop := 
    | Refl     : forall (e : expr),  multistep e e
    | AddStep  : forall (e1 e2 e3 : expr), 
          Step e1 e2 -> multistep e2 e3 -> multistep e1 e3. 

(*--------------------------------------------------------------------------
----- | Properties of the OPERATIONAL SEMANTICS (Small Step)
--------------------------------------------------------------------------*)

(*  -- EvalsToP is the transitive/reflexive closure of StepP:  *)
Lemma lemma_evals_trans : forall (e1 e2 e3 : expr),
    multistep e1 e2 -> multistep e2 e3 -> multistep e1 e3.
Proof. intros e1 e3 e4 ev_e1e3 ev_e3e4. induction ev_e1e3 as [e|_e1 e2 _e3 st_e1e2 ev_e2e3 IH]. 
  - apply ev_e3e4.
  - apply IH in ev_e3e4. apply AddStep with e2; assumption. Qed.

Lemma lem_step_evals : forall (e e' : expr), 
    Step e e' -> multistep e e'.
Proof. intros e e' st_ee'. apply AddStep with e'. assumption. apply Refl. Qed.

Lemma lemma_add_step_after : forall (e e' e'' : expr),
    multistep e e'  -> Step e' e'' -> multistep e e''.
Proof. intros e e' e'' ev_e_e' st_e'_e''. induction ev_e_e' as [e|e e1 e' st_ee1 ev_e1e' IH].
  - apply AddStep with e''.  apply st_e'_e''.  apply Refl.
  - apply IH in st_e'_e'' as ev_e1_e''. apply AddStep with e1; assumption. Qed.
  
Lemma lemma_app_many : forall (e e' v : expr),
    multistep e e' -> multistep (App e v) (App e' v).
Proof. intros e e' v ev_e_e'. induction ev_e_e' as [e|e e1 e' st_ee1 ev_e1e' IH].
  - apply Refl.
  - apply AddStep with (App e1 v). 
      * apply EApp1; apply st_ee1.
      * apply IH. 
  Qed. 
  
Lemma lemma_app_many2 : forall (v : expr) (e e' : expr), 
    isValue v -> multistep e e' -> multistep (App v e) (App v e').
Proof. intros v e e' val ev_e_e'. induction ev_e_e' as [e|e e1 e' st_ee1 ev_e1e' IH].
  - apply Refl.
  - apply AddStep with (App v e1).
      * apply EApp2; assumption.
      * apply IH.
  Qed.

Lemma lemma_app_both_many : forall (e e' : expr) (v v' : expr),
    isValue v -> isValue v' -> multistep e v -> multistep e' v'
        -> multistep (App e e') (App v v').
Proof. intros e e' v v' val val' ev_e_v ev_e'_v'. 
  apply lemma_evals_trans with (App v e').
  - apply lemma_app_many; assumption.
  - apply lemma_app_many2; assumption. Qed. 

Lemma lemma_appT_many : forall (e e' : expr) (t : type), 
    noExists t -> multistep e e' -> multistep (AppT e t) (AppT e' t).
Proof. intros e e' t ut ev_e_e'. induction ev_e_e' as [e|e e1 e' st_ee1 ev_e1e' IH].
  - apply Refl.
  - apply AddStep with (AppT e1 t).
      * apply EAppT; assumption.
      * apply IH. Qed.

Lemma lemma_let_many : forall (e_x e_x' e : expr),
    multistep e_x e_x' -> multistep (Let e_x e) (Let e_x' e).
Proof. intros e_x e_x' e ev_ex_ex'. induction ev_ex_ex' as [|e_x e_x1 e_x' st_exex1 ev_ex1ex' IH].
  - apply Refl.
  - apply AddStep with (Let e_x1 e); try (apply ELet); assumption. Qed.

Lemma lemma_annot_many : forall (e e':expr) (t:type),
    multistep e e' -> multistep (Annot e t) (Annot e' t).
Proof. intros e e' t ev_e_e'. induction ev_e_e' as [|e e1 e' st_ee1 ev_e1e' IH].
  - apply Refl.
  - apply AddStep with (Annot e1 t); try (apply EAnn); assumption. Qed.

Lemma lemma_if_many : forall (e0 e0' e1 e2 : expr),
    multistep e0 e0' -> multistep (If e0 e1 e2) (If e0' e1 e2).
Proof. intros e0 e0' e1 e2 ev_e0_e0'; induction ev_e0_e0'.
  - apply Refl.
  - apply AddStep with (If e3 e1 e2); try apply EIf; assumption. Qed.

(*--------------------------------------------------------------------------
----- | Basic LEMMAS of the OPERATIONAL SEMANTICS (Small Step)
--------------------------------------------------------------------------*)

Theorem lem_value_stuck : forall (e e' : expr), 
    Step e e' -> ~ (isValue e).
Proof. intros e e' st_e_e'. destruct st_e_e' eqn:E; simpl; unfold not; trivial. Qed.

Lemma lem_value_refl : forall (v v' : expr),       (* unused: delete later! *)
    isValue v -> multistep v v' ->  v = v'.
Proof. intros v v' v_val ev_v_v'. destruct ev_v_v' as [|v e1 v' st_ve1 ev_e1v'] eqn:E.
  - reflexivity.
  - apply lem_value_stuck in st_ve1 as H. contradiction. Qed.

Theorem lem_sem_det : forall (e e1 e2 : expr),
    Step e e1 -> Step e e2 ->  e1 = e2.
Proof. intros e. induction e; intros e' e'' st_ee' st_ee''; inversion st_ee'.
  - (* e->e1 is EPrim *) inversion st_ee''; subst e1; subst e2. 
      * (* e->e2 is EPrim *) injection H3 as H3. subst c. apply delta_pf_indep.
      * (* e->e2 is EApp1 *) apply lem_value_stuck in H6; simpl in H6; contradiction. 
      * (* e->e2 is EApp2 *) apply lem_value_stuck in H7; contradiction.
      * (* e->e2 is EAppAbs *) discriminate.
  - (* e->e1 is EApp1 *) inversion st_ee''; subst e e1 e2.
      * (* e->e2 is EPrim *) apply lem_value_stuck in H2; simpl in H2; contradiction. 
      * (* e->e2 is EApp1 *) apply IHe1 with e'0 e'1 in H2 as H'. rewrite H'; reflexivity. assumption. 
      * (* e->e2 is EApp2 *) apply lem_value_stuck in H2; simpl in H2; contradiction. 
      * (* EAppAbs *) apply lem_value_stuck in H2; simpl in H2; contradiction.
  - (* e->e1 is EApp2 *) inversion st_ee''; subst e1 e2.
      * (* e->e2 is EPrim *) apply lem_value_stuck in H3; contradiction.
      * (* EApp1 *) apply lem_value_stuck in H7; contradiction.
      * (* EApp2 *) assert (e'0 = e'1). apply IHe2; assumption. rewrite H; reflexivity.
      * (* EAppAbs *) apply lem_value_stuck in H3; contradiction.
  - (* e->e1 is EAppAbs *) inversion st_ee''; subst e1 e2.
      * (* e->e2 is EPrim *) discriminate.
      * (* EApp1 *) apply lem_value_stuck in H6; simpl in H6. contradiction.
      * (* EApp2 *) apply lem_value_stuck in H7; contradiction.
      * (* EAppAbs *) injection H3 as H'; rewrite H'; reflexivity.
  - (* e->e1 is EPrimT *) inversion st_ee''; subst e.
      * (* e->e2 is EPrimT *) injection H3 as Hc. subst c. apply deltaT_pf_indep.
      * (* EAppT *) apply lem_value_stuck in H7; simpl in H7; contradiction.
      * (* EAppTAbs *) discriminate.
  - (* e->e1 is EAppT *) inversion st_ee''; subst e e0 t.
      * (* EPrimT *) apply lem_value_stuck in H3; simpl in H3. contradiction.
      * (* EAppT *) apply IHe with e'0 e'1 in H3 as H'. rewrite H'. reflexivity. assumption.
      * (* EAppTAbs *) apply lem_value_stuck in H3; simpl in H3; contradiction.
  - (* e->e1 is EAppTAbs*) inversion st_ee''; subst e t.
      * (* EPrimT *) discriminate.
      * (* EAppT *) apply lem_value_stuck in H7; simpl in H7; contradiction.
      * (* EAppTAbs *) injection H3 as H'; subst e0; reflexivity.
  - (* e->e1 is ELet *) inversion st_ee''; subst e1 e2.
      * (* ELet *) apply IHe1 with e_x' e_x'0 in H2 as H'. rewrite H'. reflexivity. assumption.
      * (* ELetV *) apply lem_value_stuck in H2; simpl in H2; contradiction.
  - (* e->e1 is ELetV *) inversion st_ee''; subst e1 e2.
      * (* ELet *) apply lem_value_stuck in H6; simpl in H6; contradiction.
      * (* ELetV *) reflexivity.
  - (* e->e1 is EAnn *) inversion st_ee''; subst e t.
      * (* EAnn *) apply IHe with e'0 e'1 in H2 as H'. rewrite H'; reflexivity. assumption.
      * (* EAnnV *) subst e0 e''. apply lem_value_stuck in H2; simpl in H2; contradiction.
  - (* e->e1 is EAnnV *) inversion st_ee''; subst e e' t.
      * (* EAnn *) apply lem_value_stuck in H6; simpl in H6; contradiction.
      * (* EAnnV *) assumption.
  - (* e->e1 is EIf  *) inversion st_ee''; subst e0 e1 e' e''.
      * (* EIf  *) apply IHe1 with e0' e0'0 in H3 as H'; try rewrite H'; trivial.
      * (* EIfT *) apply lem_value_stuck in H3; simpl in H3; contradiction.
      * (* EIfF *) apply lem_value_stuck in H3; simpl in H3; contradiction.
  - (* e->e1 is EIfT *) inversion st_ee''; subst e1 e' e''.
      * (* EIf  *) apply lem_value_stuck in H7; simpl in H7; contradiction.
      * (* EIfT *) reflexivity.
      * (* EIfF *) discriminate.
  - (* e->e1 is EIfF *) inversion st_ee''; subst e1 e' e''.
      * (* EIf  *) apply lem_value_stuck in H7; simpl in H7; contradiction.
      * (* EIfT *) discriminate.
      * (* EIfF *) reflexivity.
  Qed.

Lemma lem_evals_val_det : forall (e v1 v2 : expr), 
    isValue v1 -> isValue v2 -> multistep e v1 -> multistep e v2 ->  v1 = v2.
Proof. intros e v1 v2 val1 val2 ev_ev1 ev_ev2. 
  induction ev_ev1 as [v1|e e1 v1 st_ee1 ev_e1v1]; 
  inversion ev_ev2 as [_v2|_e e2 _v2 st_ee2 ev_e2v2].
  - (* Refl, Refl *) reflexivity. 
  - (* Refl, AddS *) apply lem_value_stuck in st_ee2; contradiction.
  - (* AddS, Refl *) subst v2. apply lem_value_stuck in st_ee1; contradiction.
  - (* AddS, AddS *) apply IHev_e1v1. assumption.
      apply lem_sem_det with e e1 e2 in st_ee1 as Heq. rewrite Heq. all : assumption. 
  Qed. 
  
Lemma lem_decompose_evals : forall (e e' v : expr), 
    isValue v -> multistep e e' -> multistep e v -> multistep e' v.
Proof. intros e e' v val ev_ee' ev_ev. induction ev_ee' as [ |e e1 e' st_ee1 ev_e1e' IH].
  - (* Refl *) assumption.
  - (* AddS *) inversion ev_ev as [ |_e e2 _v st_ee2 ev_e2v]. 
      * (* Refl *) subst e e0. apply lem_value_stuck in st_ee1; contradiction.
      * (* AddS *) apply IH. 
          apply lem_sem_det with e e1 e2 in st_ee1 as Heq. rewrite Heq. all:assumption. 
  Qed.