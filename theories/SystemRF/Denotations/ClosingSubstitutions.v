Require Import AutoProof.SystemRF.SystemRF.BasicDefinitions.
Require Import AutoProof.SystemRF.SystemRF.Names.
Require Import AutoProof.SystemRF.SystemRF.BasicPropsEnvironments.

Require Import Arith.
Require Import Lists.ListSet.

(*------------------------------------------------------------------------- 
----- | CLOSING SUBSTITUTIONS 
-------------------------------------------------------------------------*)

(* closing substitutions (i.e. th(x), th(e), th(t)) proceed from the top/right of
 *   the typing env downwards/leftwards. In order for a closing substitution to be
 *   "well formed" it must be an element of the denotation 
 *   of the corresponding enivornment *)

Inductive csub : Set :=
    | CEmpty
    | CCons  (x : var_name) (v_x : expr) (th : csub)
    | CConsT (a : var_name) (t_a : type) (th : csub).
  
Fixpoint bindsC (th : csub) : names := 
    match th with 
    | CEmpty            => empty
    | (CCons  x v_x th) => names_add x (bindsC th)
    | (CConsT a t_a th) => names_add a (bindsC th)
    end.

Fixpoint vbindsC (th : csub) : names := 
    match th with 
    | CEmpty            => empty
    | (CCons  x v_x th) => names_add x (vbindsC th)
    | (CConsT a t_a th) => vbindsC th
    end.

Fixpoint tvbindsC (th : csub) : names := 
    match th with 
    | CEmpty            => empty
    | (CCons  x v_x th) => tvbindsC th
    | (CConsT a t_a th) => names_add a (tvbindsC th)
    end.

Definition in_csubst (x : var_name) (th : csub) : Prop := In x (bindsC th).

Lemma vbindsC_subset : forall (th : csub), Subset (vbindsC th) (bindsC th).
Proof. unfold Subset; induction th; simpl.
  - trivial.
  - apply subset_add_both_intro; assumption.
  - apply subset_add_intro; assumption. Qed.
  
Lemma tvbindsC_subset : forall (th : csub), Subset (tvbindsC th) (bindsC th).
Proof. unfold Subset; induction th; simpl.
  - trivial.
  - apply subset_add_intro; assumption.
  - apply subset_add_both_intro; assumption. Qed. 

Lemma in_csubst_CCons : forall (x y : var_name) (v : expr) (th : csub),
   ~ in_csubst x (CCons y v th) -> x <> y /\ ~ in_csubst x th.
Proof. unfold in_csubst; simpl; intros; split; unfold not.
  - intro. apply set_add_intro2 with _ Nat.eq_dec x y (bindsC th) in H0; contradiction.
  - intro. apply set_add_intro1 with _ Nat.eq_dec x y (bindsC th) in H0; contradiction.
  Qed.

Lemma in_csubst_CConsT : forall (x a : var_name) (t : type) (th : csub),
    ~ in_csubst x (CConsT a t th) -> x <> a /\ ~ in_csubst x th.
Proof. unfold in_csubst; simpl; intros; split; unfold not.
  - intro. apply set_add_intro2 with _ Nat.eq_dec x a (bindsC th) in H0; contradiction.
  - intro. apply set_add_intro1 with _ Nat.eq_dec x a (bindsC th) in H0; contradiction.
  Qed.

Fixpoint bound_inC (x : var_name) (v_x : expr) (th : csub) : Prop := 
    match th with
    | CEmpty             => False
    | (CCons  y v_y th)  => (x = y /\ v_x = v_y) \/ bound_inC x v_x th
    | (CConsT a t_a th)  => bound_inC x v_x th
    end.

Fixpoint tv_bound_inC (a : var_name) (t_a : type) (th : csub) : Prop :=
    match th with
    | CEmpty               => False
    | (CCons  y  v_y  th)  => tv_bound_inC a t_a th
    | (CConsT a' t_a' th)  => (a = a' /\ t_a = t_a') \/ tv_bound_inC a t_a th
    end.

Lemma lem_tvboundinC_incsubst: forall (a:var_name) (t_a:type) (th:csub),
    tv_bound_inC a t_a th -> in_csubst a th.
Proof. intros. induction th; simpl in H; simpl; try contradiction;
  try (apply set_add_intro); try (destruct H); try (apply IHg in H); intuition. 
Qed.

Fixpoint closed (th0 : csub) : Prop :=
    match th0 with
    | CEmpty            => True
    | (CCons  x v_x th) => fv v_x = empty /\ ftv v_x = empty /\ closed th
    | (CConsT a t   th) => free t = empty /\ freeTV t = empty /\ closed th
    end.  

Fixpoint loc_closed (th0 : csub) : Prop :=
    match th0 with
    | CEmpty            => True
    | (CCons  x v_x th) => isLC v_x /\ loc_closed th
    | (CConsT a t   th) => isLCT t  /\ loc_closed th
    end.  

Fixpoint substitutable (th0 : csub) : Prop :=
    match th0 with
    | CEmpty            => True
    | (CCons  x v_x th) => isValue v_x /\ substitutable th
    | (CConsT a t   th) => isMono t /\ noExists t /\ substitutable th
    end.  

Fixpoint uniqueC (th0 : csub) : Prop :=
    match th0 with
    | CEmpty         => True
    | (CCons  x v_x th) => ~ in_csubst x th /\ uniqueC th
    | (CConsT a t_a th) => ~ in_csubst a th /\ uniqueC th
    end.   
    
Fixpoint csubst (th : csub) (e : expr) : expr := 
    match th with
    | CEmpty            => e
    | (CCons  x v_x th) => csubst th (subFV  x v_x e)
    | (CConsT a t_a th) => csubst th (subFTV a t_a e)
    end.

Fixpoint cpsubst (th : csub) (ps : preds) : preds := 
    match th with
    | CEmpty            => ps
    | (CCons  x v_x th) => cpsubst th (psubFV  x v_x ps)
    | (CConsT a t_a th) => cpsubst th (psubFTV a t_a ps)
    end.

Fixpoint ctsubst (th : csub) (t : type) : type :=
    match th with
    | CEmpty           => t
    | (CCons  x v  th) => ctsubst th (tsubFV x v t)
    | (CConsT a t' th) => ctsubst th (tsubFTV a t' t)
    end.

Fixpoint concatCS (th th'0 : csub) : csub :=
    match th'0 with
    | CEmpty           => th
    | (CCons  x v th') => CCons  x v (concatCS th th')
    | (CConsT a t th') => CConsT a t (concatCS th th')
    end.

Fixpoint remove_fromCS (th:csub) (x:var_name) : csub := 
    match th with 
    | CEmpty          => CEmpty
    | (CCons  y v th) => if x =? y then th else CCons  y v (remove_fromCS th x)
    | (CConsT a t th) => if x =? a then th else CConsT a t (remove_fromCS th x)
    end.
    
Fixpoint csubst_env (th0:csub) (g:env) : env :=
    match th0 with  
    | CEmpty            => g 
    | (CCons  z v_z th) => csubst_env th (esubFV  z v_z g)
    | (CConsT a t_a th) => csubst_env th (esubFTV a t_a g)
    end.
    