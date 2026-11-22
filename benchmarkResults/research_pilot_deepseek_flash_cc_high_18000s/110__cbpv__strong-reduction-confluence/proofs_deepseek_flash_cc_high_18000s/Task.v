From Stdlib Require Import Logic.Eqdep_dec PeanoNat.
From CBPV Require Import StrongReduction AbstractReductionSystems.
Import CommaNotation.

Lemma pointwise_upRen : forall n m (xi xi' : fin n -> fin m),
    (forall i, xi i = xi' i) ->
    forall i, (upRen_value_value xi) i = (upRen_value_value xi') i.
Proof.
  intros n m xi xi' H i. destruct i as [i|]; cbn.
  - unfold funcomp; cbn. f_equal. apply H.
  - reflexivity.
Qed.

Lemma pointwise_upSubst : forall n m (sigma tau : fin n -> value m),
    (forall i, sigma i = tau i) ->
    forall i, (up_value_value sigma) i = (up_value_value tau) i.
Proof.
  intros n m sigma tau H i. destruct i as [i|]; cbn.
  - unfold funcomp; cbn. f_equal. apply H.
  - reflexivity.
Qed.

Lemma ren_ext_lem : forall n,
  (forall (v : value n) (m : nat) (xi xi' : fin n -> fin m),
      (forall i, xi i = xi' i) -> ren_value xi v = ren_value xi' v)
  /\ (forall (c : comp n) (m : nat) (xi xi' : fin n -> fin m),
      (forall i, xi i = xi' i) -> ren_comp xi c = ren_comp xi' c).
Proof.
  apply mutind_val_comp.
  - intros n f m xi xi' H. cbn. f_equal. apply H.
  - intros n m xi xi' H. reflexivity.
  - intros n v IH1 v0 IH2 m xi xi' H. cbn. f_equal; [apply IH1 | apply IH2]; assumption.
  - intros n b v IH m xi xi' H. cbn. f_equal. apply IH. assumption.
  - intros n c IH m xi xi' H. cbn. f_equal. apply IH. assumption.
  - intros n m xi xi' H. reflexivity.
  - intros n v IH m xi xi' H. cbn. f_equal. apply IH. assumption.
  - intros n c IH m xi xi' H. cbn. f_equal. apply IH. apply pointwise_upRen. assumption.
  - intros n c IH v IHv m xi xi' H. cbn. f_equal; [apply IH | apply IHv]; assumption.
  - intros n c IH c0 IH0 m xi xi' H. cbn. f_equal; [apply IH | apply IH0]; assumption.
  - intros n v IH m xi xi' H. cbn. f_equal. apply IH. assumption.
  - intros n c IH c0 IH0 m xi xi' H. cbn. f_equal; [apply IH | apply IH0; apply pointwise_upRen]; assumption.
  - intros n b c IH m xi xi' H. cbn. f_equal. apply IH. assumption.
  - intros n v IH m xi xi' H. cbn. f_equal. apply IH. assumption.
  - intros n v IH c IHc c0 IH0 m xi xi' H. cbn. f_equal; [apply IH | apply IHc; apply pointwise_upRen | apply IH0; apply pointwise_upRen]; assumption.
  - intros n v IH c IHc m xi xi' H. cbn. f_equal; [apply IH | apply IHc; apply pointwise_upRen; apply pointwise_upRen]; assumption.
Qed.

Lemma ren_value_ext : forall n (v : value n) m (xi xi' : fin n -> fin m),
    (forall i, xi i = xi' i) -> ren_value xi v = ren_value xi' v.
Proof. intros. apply (ren_ext_lem n). assumption. Qed.

Lemma ren_comp_ext : forall n (c : comp n) m (xi xi' : fin n -> fin m),
    (forall i, xi i = xi' i) -> ren_comp xi c = ren_comp xi' c.
Proof. intros. apply (ren_ext_lem n). assumption. Qed.

Lemma subst_ext_lem : forall n,
  (forall (v : value n) (m : nat) (sigma tau : fin n -> value m),
      (forall i, sigma i = tau i) -> subst_value sigma v = subst_value tau v)
  /\ (forall (c : comp n) (m : nat) (sigma tau : fin n -> value m),
      (forall i, sigma i = tau i) -> subst_comp sigma c = subst_comp tau c).
Proof.
  apply mutind_val_comp.
  - intros n f m sigma tau H. cbn. apply H.
  - intros n m sigma tau H. reflexivity.
  - intros n v IH1 v0 IH2 m sigma tau H. cbn. f_equal; [apply IH1 | apply IH2]; assumption.
  - intros n b v IH m sigma tau H. cbn. f_equal. apply IH. assumption.
  - intros n c IH m sigma tau H. cbn. f_equal. apply IH. assumption.
  - intros n m sigma tau H. reflexivity.
  - intros n v IH m sigma tau H. cbn. f_equal. apply IH. assumption.
  - intros n c IH m sigma tau H. cbn. f_equal. apply IH. apply pointwise_upSubst. assumption.
  - intros n c IH v IHv m sigma tau H. cbn. f_equal; [apply IH | apply IHv]; assumption.
  - intros n c IH c0 IH0 m sigma tau H. cbn. f_equal; [apply IH | apply IH0]; assumption.
  - intros n v IH m sigma tau H. cbn. f_equal. apply IH. assumption.
  - intros n c IH c0 IH0 m sigma tau H. cbn. f_equal; [apply IH | apply IH0; apply pointwise_upSubst]; assumption.
  - intros n b c IH m sigma tau H. cbn. f_equal. apply IH. assumption.
  - intros n v IH m sigma tau H. cbn. f_equal. apply IH. assumption.
  - intros n v IH c IHc c0 IH0 m sigma tau H. cbn. f_equal; [apply IH | apply IHc; apply pointwise_upSubst | apply IH0; apply pointwise_upSubst]; assumption.
  - intros n v IH c IHc m sigma tau H. cbn. f_equal; [apply IH | apply IHc; apply pointwise_upSubst; apply pointwise_upSubst]; assumption.
Qed.

Lemma subst_value_ext : forall n (v : value n) m (sigma tau : fin n -> value m),
    (forall i, sigma i = tau i) -> subst_value sigma v = subst_value tau v.
Proof. intros. apply (subst_ext_lem n). assumption. Qed.

Lemma subst_comp_ext : forall n (c : comp n) m (sigma tau : fin n -> value m),
    (forall i, sigma i = tau i) -> subst_comp sigma c = subst_comp tau c.
Proof. intros. apply (subst_ext_lem n). assumption. Qed.

Lemma upRen_upRen : forall n m k (xi : fin n -> fin m) (xi' : fin m -> fin k),
    forall i, (upRen_value_value xi') ((upRen_value_value xi) i) =
              (upRen_value_value (fun i => xi' (xi i))) i.
Proof.
  intros n m k xi xi' i. destruct i as [j|]; cbn.
  - unfold funcomp; cbn. reflexivity.
  - reflexivity.
Qed.

Lemma ren_ren_lem : forall n,
  (forall (v : value n) (m k : nat) (xi : fin n -> fin m) (xi' : fin m -> fin k),
      ren_value xi' (ren_value xi v) = ren_value (fun i => xi' (xi i)) v)
  /\ (forall (c : comp n) (m k : nat) (xi : fin n -> fin m) (xi' : fin m -> fin k),
      ren_comp xi' (ren_comp xi c) = ren_comp (fun i => xi' (xi i)) c).
Proof.
  apply mutind_val_comp.
  - intros n f m k xi xi'. cbn. reflexivity.
  - intros n m k xi xi'. reflexivity.
  - intros n v IH1 v0 IH2 m k xi xi'. cbn. f_equal; [apply IH1 | apply IH2].
  - intros n b v IH m k xi xi'. cbn. f_equal. apply IH.
  - intros n c IH m k xi xi'. cbn. f_equal. apply IH.
  - intros n m k xi xi'. reflexivity.
  - intros n v IH m k xi xi'. cbn. f_equal. apply IH.
  - intros n c IH m k xi xi'. cbn. f_equal.
    rewrite IH. apply ren_comp_ext. intro i. apply upRen_upRen.
  - intros n c IH v IHv m k xi xi'. cbn. f_equal; [apply IH | apply IHv].
  - intros n c IH c0 IH0 m k xi xi'. cbn. f_equal; [apply IH | apply IH0].
  - intros n v IH m k xi xi'. cbn. f_equal. apply IH.
  - intros n c IH c0 IH0 m k xi xi'. cbn. f_equal. apply IH.
    rewrite IH0. apply ren_comp_ext. intro i. apply upRen_upRen.
  - intros n b c IH m k xi xi'. cbn. f_equal. apply IH.
  - intros n v IH m k xi xi'. cbn. f_equal. apply IH.
  - intros n v IH c IHc c0 IH0 m k xi xi'. cbn. f_equal. apply IH.
    rewrite IHc. apply ren_comp_ext. intro i. apply upRen_upRen.
    rewrite IH0. apply ren_comp_ext. intro i. apply upRen_upRen.
  - intros n v IH c IHc m k xi xi'. cbn. f_equal. apply IH.
    rewrite IHc. apply ren_comp_ext. intro i. rewrite upRen_upRen.
    apply pointwise_upRen. intro j. apply upRen_upRen.
Qed.


Lemma ren_ren_value_p : forall n (v : value n) m k (xi : fin n -> fin m) (xi' : fin m -> fin k),
    ren_value xi' (ren_value xi v) = ren_value (fun i => xi' (xi i)) v.
Proof. intros. destruct (ren_ren_lem n) as [H1 H2]. exact (H1 v m k xi xi'). Qed.

Lemma ren_ren_comp_p : forall n (c : comp n) m k (xi : fin n -> fin m) (xi' : fin m -> fin k),
    ren_comp xi' (ren_comp xi c) = ren_comp (fun i => xi' (xi i)) c.
Proof. intros. destruct (ren_ren_lem n) as [H1 H2]. exact (H2 c m k xi xi'). Qed.

Lemma upSubst_upRen : forall n m k (xi : fin n -> fin m) (sigma : fin m -> value k),
    forall i, (up_value_value sigma) ((upRen_value_value xi) i) =
              (up_value_value (fun i => sigma (xi i))) i.
Proof.
  intros n m k xi sigma i. destruct i as [j|]; cbn.
  - unfold funcomp; cbn. reflexivity.
  - reflexivity.
Qed.

Lemma upRen_upSubst : forall n m k (xi : fin m -> fin k) (sigma : fin n -> value m),
    forall i, (ren_value (upRen_value_value xi)) ((up_value_value sigma) i) =
              (up_value_value (fun i => ren_value xi (sigma i))) i.
Proof.
  intros n m k xi sigma i. destruct i as [j|]; cbn.
  - unfold funcomp; cbn.
    rewrite ren_ren_value_p. rewrite ren_ren_value_p.
    apply ren_value_ext. intro i'. unfold funcomp. cbn. reflexivity.
  - reflexivity.
Qed.

Lemma subst_ren_lem : forall n,
  (forall (v : value n) (m k : nat) (xi : fin n -> fin m) (sigma : fin m -> value k),
      subst_value sigma (ren_value xi v) = subst_value (fun i => sigma (xi i)) v)
  /\ (forall (c : comp n) (m k : nat) (xi : fin n -> fin m) (sigma : fin m -> value k),
      subst_comp sigma (ren_comp xi c) = subst_comp (fun i => sigma (xi i)) c).
Proof.
  apply mutind_val_comp.
  - intros n f m k xi sigma. cbn. reflexivity.
  - intros n m k xi sigma. reflexivity.
  - intros n v IH1 v0 IH2 m k xi sigma. cbn. f_equal; [apply IH1 | apply IH2].
  - intros n b v IH m k xi sigma. cbn. f_equal. apply IH.
  - intros n c IH m k xi sigma. cbn. f_equal. apply IH.
  - intros n m k xi sigma. reflexivity.
  - intros n v IH m k xi sigma. cbn. f_equal. apply IH.
  - intros n c IH m k xi sigma. cbn. f_equal.
    rewrite IH. apply subst_comp_ext. intro i. apply upSubst_upRen.
  - intros n c IH v IHv m k xi sigma. cbn. f_equal; [apply IH | apply IHv].
  - intros n c IH c0 IH0 m k xi sigma. cbn. f_equal; [apply IH | apply IH0].
  - intros n v IH m k xi sigma. cbn. f_equal. apply IH.
  - intros n c IH c0 IH0 m k xi sigma. cbn. f_equal. apply IH.
    rewrite IH0. apply subst_comp_ext. intro i. apply upSubst_upRen.
  - intros n b c IH m k xi sigma. cbn. f_equal. apply IH.
  - intros n v IH m k xi sigma. cbn. f_equal. apply IH.
  - intros n v IH c IHc c0 IH0 m k xi sigma. cbn. f_equal. apply IH.
    rewrite IHc. apply subst_comp_ext. intro i. apply upSubst_upRen.
    rewrite IH0. apply subst_comp_ext. intro i. apply upSubst_upRen.
  - intros n v IH c IHc m k xi sigma. cbn. f_equal. apply IH.
    rewrite IHc. apply subst_comp_ext. intro i. rewrite upSubst_upRen.
    apply pointwise_upSubst. intro j. apply upSubst_upRen.
Qed.

Lemma subst_value_ren : forall n (v : value n) m k (xi : fin n -> fin m) (sigma : fin m -> value k),
    subst_value sigma (ren_value xi v) = subst_value (fun i => sigma (xi i)) v.
Proof. intros. destruct (subst_ren_lem n) as [H1 H2]. apply H1. Qed.

Lemma subst_comp_ren : forall n (c : comp n) m k (xi : fin n -> fin m) (sigma : fin m -> value k),
    subst_comp sigma (ren_comp xi c) = subst_comp (fun i => sigma (xi i)) c.
Proof. intros. destruct (subst_ren_lem n) as [H1 H2]. apply H2. Qed.

Lemma ren_subst_lem : forall n,
  (forall (v : value n) (m k : nat) (sigma : fin n -> value m) (xi : fin m -> fin k),
      ren_value xi (subst_value sigma v) = subst_value (fun i => ren_value xi (sigma i)) v)
  /\ (forall (c : comp n) (m k : nat) (sigma : fin n -> value m) (xi : fin m -> fin k),
      ren_comp xi (subst_comp sigma c) = subst_comp (fun i => ren_value xi (sigma i)) c).
Proof.
  apply mutind_val_comp.
  - intros n f m k sigma xi. cbn. reflexivity.
  - intros n m k sigma xi. reflexivity.
  - intros n v IH1 v0 IH2 m k sigma xi. cbn. f_equal; [apply IH1 | apply IH2].
  - intros n b v IH m k sigma xi. cbn. f_equal. apply IH.
  - intros n c IH m k sigma xi. cbn. f_equal. apply IH.
  - intros n m k sigma xi. reflexivity.
  - intros n v IH m k sigma xi. cbn. f_equal. apply IH.
  - intros n c IH m k sigma xi. cbn. f_equal.
    rewrite IH. apply subst_comp_ext. intro i. apply upRen_upSubst.
  - intros n c IH v IHv m k sigma xi. cbn. f_equal; [apply IH | apply IHv].
  - intros n c IH c0 IH0 m k sigma xi. cbn. f_equal; [apply IH | apply IH0].
  - intros n v IH m k sigma xi. cbn. f_equal. apply IH.
  - intros n c IH c0 IH0 m k sigma xi. cbn. f_equal. apply IH.
    rewrite IH0. apply subst_comp_ext. intro i. apply upRen_upSubst.
  - intros n b c IH m k sigma xi. cbn. f_equal. apply IH.
  - intros n v IH m k sigma xi. cbn. f_equal. apply IH.
  - intros n v IH c IHc c0 IH0 m k sigma xi. cbn. f_equal. apply IH.
    rewrite IHc. apply subst_comp_ext. intro i. apply upRen_upSubst.
    rewrite IH0. apply subst_comp_ext. intro i. apply upRen_upSubst.
  - intros n v IH c IHc m k sigma xi. cbn. f_equal. apply IH.
    rewrite IHc. apply subst_comp_ext. intro i. rewrite upRen_upSubst.
    apply pointwise_upSubst. intro j. apply upRen_upSubst.
Qed.

Lemma ren_value_subst : forall n (v : value n) m k (sigma : fin n -> value m) (xi : fin m -> fin k),
    ren_value xi (subst_value sigma v) = subst_value (fun i => ren_value xi (sigma i)) v.
Proof. intros. destruct (ren_subst_lem n) as [H1 H2]. apply H1. Qed.

Lemma ren_comp_subst : forall n (c : comp n) m k (sigma : fin n -> value m) (xi : fin m -> fin k),
    ren_comp xi (subst_comp sigma c) = subst_comp (fun i => ren_value xi (sigma i)) c.
Proof. intros. destruct (ren_subst_lem n) as [H1 H2]. apply H2. Qed.

Lemma upSubst_upSubst : forall n m k (sigma : fin n -> value m) (tau : fin m -> value k),
    forall i, subst_value (up_value_value tau) ((up_value_value sigma) i) =
              (up_value_value (fun i => subst_value tau (sigma i))) i.
Proof.
  intros n m k sigma tau i. destruct i as [j|]; cbn.
  - unfold funcomp; cbn. rewrite subst_value_ren.
    transitivity (subst_value (fun i => ren_value shift (tau i)) (sigma j)).
    + apply subst_value_ext. intro i. unfold funcomp. cbn. reflexivity.
    + symmetry. apply ren_value_subst.
  - reflexivity.
Qed.

Lemma subst_subst_lem : forall n,
  (forall (v : value n) (m k : nat) (sigma : fin n -> value m) (tau : fin m -> value k),
      subst_value tau (subst_value sigma v) = subst_value (fun i => subst_value tau (sigma i)) v)
  /\ (forall (c : comp n) (m k : nat) (sigma : fin n -> value m) (tau : fin m -> value k),
      subst_comp tau (subst_comp sigma c) = subst_comp (fun i => subst_value tau (sigma i)) c).
Proof.
  apply mutind_val_comp.
  - intros n f m k sigma tau. cbn. reflexivity.
  - intros n m k sigma tau. reflexivity.
  - intros n v IH1 v0 IH2 m k sigma tau. cbn. f_equal; [apply IH1 | apply IH2].
  - intros n b v IH m k sigma tau. cbn. f_equal. apply IH.
  - intros n c IH m k sigma tau. cbn. f_equal. apply IH.
  - intros n m k sigma tau. reflexivity.
  - intros n v IH m k sigma tau. cbn. f_equal. apply IH.
  - intros n c IH m k sigma tau. cbn. f_equal.
    rewrite IH. apply subst_comp_ext. intro i. apply upSubst_upSubst.
  - intros n c IH v IHv m k sigma tau. cbn. f_equal; [apply IH | apply IHv].
  - intros n c IH c0 IH0 m k sigma tau. cbn. f_equal; [apply IH | apply IH0].
  - intros n v IH m k sigma tau. cbn. f_equal. apply IH.
  - intros n c IH c0 IH0 m k sigma tau. cbn. f_equal. apply IH.
    rewrite IH0. apply subst_comp_ext. intro i. apply upSubst_upSubst.
  - intros n b c IH m k sigma tau. cbn. f_equal. apply IH.
  - intros n v IH m k sigma tau. cbn. f_equal. apply IH.
  - intros n v IH c IHc c0 IH0 m k sigma tau. cbn. f_equal. apply IH.
    rewrite IHc. apply subst_comp_ext. intro i. apply upSubst_upSubst.
    rewrite IH0. apply subst_comp_ext. intro i. apply upSubst_upSubst.
  - intros n v IH c IHc m k sigma tau. cbn. f_equal. apply IH.
    rewrite IHc. apply subst_comp_ext. intro i. rewrite upSubst_upSubst.
    apply pointwise_upSubst. intro j. apply upSubst_upSubst.
Qed.

Lemma subst_value_subst : forall n (v : value n) m k (sigma : fin n -> value m) (tau : fin m -> value k),
    subst_value tau (subst_value sigma v) = subst_value (fun i => subst_value tau (sigma i)) v.
Proof. intros. destruct (subst_subst_lem n) as [H1 H2]. apply H1. Qed.

Lemma subst_comp_subst : forall n (c : comp n) m k (sigma : fin n -> value m) (tau : fin m -> value k),
    subst_comp tau (subst_comp sigma c) = subst_comp (fun i => subst_value tau (sigma i)) c.
Proof. intros. destruct (subst_subst_lem n) as [H1 H2]. apply H2. Qed.

(* ===== Parallel reduction ===== *)

Inductive par : forall n, comp n -> comp n -> Prop :=
| parCu n : par n cu cu
| parForce n (c c' : comp n) : par n c c' -> par n (force (thunk c)) c'
| parForceCong n (v v' : value n) : parv n v v' -> par n (force v) (force v')
| parLambda n (c c' : comp (S n)) : par (S n) c c' -> par n (lambda c) (lambda c')
| parAppCong n (c c' : comp n) (v v' : value n) :
    par n c c' -> parv n v v' -> par n (app c v) (app c' v')
| parAppRed n (c c' : comp (S n)) (v v' : value n) :
    par (S n) c c' -> parv n v v' -> par n (app (lambda c) v) (c'[v'..])
| parTupleCong n (c1 c1' c2 c2' : comp n) :
    par n c1 c1' -> par n c2 c2' -> par n (tuple c1 c2) (tuple c1' c2')
| parRetCong n (v v' : value n) : parv n v v' -> par n (ret v) (ret v')
| parLetinCong n (c1 c1' : comp n) (c2 c2' : comp (S n)) :
    par n c1 c1' -> par (S n) c2 c2' -> par n (letin c1 c2) (letin c1' c2')
| parLetinRed n (v v' : value n) (c c' : comp (S n)) :
    parv n v v' -> par (S n) c c' -> par n (letin (ret v) c) (c'[v'..])
| parProjCong n b (c c' : comp n) : par n c c' -> par n (proj b c) (proj b c')
| parProjRedTrue n (c1 c1' c2 c2' : comp n) :
    par n c1 c1' -> par n c2 c2' ->
    par n (proj true (tuple c1 c2)) c1'
| parProjRedFalse n (c1 c1' c2 c2' : comp n) :
    par n c1 c1' -> par n c2 c2' ->
    par n (proj false (tuple c1 c2)) c2' 
| parCaseZCong n (v v' : value n) : parv n v v' -> par n (caseZ v) (caseZ v')
| parCaseSCong n (v v' : value n) (c1 c1' c2 c2' : comp (S n)) :
    parv n v v' -> par (S n) c1 c1' -> par (S n) c2 c2' ->
    par n (caseS v c1 c2) (caseS v' c1' c2')
| parCaseSRedTrue n (v v' : value n) (c1 c1' c2 c2' : comp (S n)) :
    parv n v v' -> par (S n) c1 c1' -> par (S n) c2 c2' ->
    par n (caseS (inj true v) c1 c2) (c1'[v'..])
| parCaseSRedFalse n (v v' : value n) (c1 c1' c2 c2' : comp (S n)) :
    parv n v v' -> par (S n) c1 c1' -> par (S n) c2 c2' ->
    par n (caseS (inj false v) c1 c2) (c2'[v'..])
| parCasePCong n (v v' : value n) (c c' : comp (S (S n))) :
    parv n v v' -> par (S (S n)) c c' -> par n (caseP v c) (caseP v' c')
| parCasePRed n (v1 v1' v2 v2' : value n) (c c' : comp (S (S n))) :
    parv n v1 v1' -> parv n v2 v2' -> par (S (S n)) c c' ->
    par n (caseP (pair v1 v2) c) (c'[v2',v1'..])
with parv : forall n, value n -> value n -> Prop :=
| parVar n (i : fin n) : parv n (var_value i) (var_value i)
| parU n : parv n u u
| parPairCong n (v1 v1' v2 v2' : value n) :
    parv n v1 v1' -> parv n v2 v2' -> parv n (pair v1 v2) (pair v1' v2')
| parInjCong n b (v v' : value n) : parv n v v' -> parv n (inj b v) (inj b v')
| parThunkCong n (c c' : comp n) : par n c c' -> parv n (thunk c) (thunk c').

Scheme par_ind_2 := Induction for par Sort Prop
  with parv_ind_2 := Induction for parv Sort Prop.

Combined Scheme mutind_par from par_ind_2, parv_ind_2.

Lemma ren_subst_single : forall k (c : comp (S k)) m (xi : fin k -> fin m) (v : value k),
    ren_comp xi (c[v..]) = (ren_comp (upRen_value_value xi) c)[(ren_value xi v)..].
Proof.
  intros k c m xi v. rewrite ren_comp_subst.
  transitivity (subst_comp (fun i => ((ren_value xi v)..) ((upRen_value_value xi) i)) c).
  - apply subst_comp_ext. intro i. destruct i as [j|]; cbn.
    + unfold funcomp; cbn. reflexivity.
    + reflexivity.
  - symmetry. apply subst_comp_ren.
Qed.

Lemma ren_subst_double : forall k (c : comp (S (S k))) m (xi : fin k -> fin m) (v1 v2 : value k),
    ren_comp xi (c[v2,v1..]) = (ren_comp (upRen_value_value (upRen_value_value xi)) c)[(ren_value xi v2),(ren_value xi v1)..].
Proof.
  intros k c m xi v1 v2. rewrite ren_comp_subst.
  transitivity (subst_comp
    (fun i => ((ren_value xi v2),(ren_value xi v1)..) ((upRen_value_value (upRen_value_value xi)) i)) c).
  - apply subst_comp_ext. intro i. destruct i as [j|]; cbn.
    + destruct j as [j'|]; cbn.
      * unfold funcomp; cbn. reflexivity.
      * reflexivity.
    + reflexivity.
  - symmetry. apply subst_comp_ren.
Qed.

Lemma par_refl_lem : forall n,
  (forall (v : value n), parv n v v) /\ (forall (c : comp n), par n c c).
Proof.
  apply mutind_val_comp.
  - intros n f. apply parVar.
  - intros n. apply parU.
  - intros n v IH v0 IH0. apply parPairCong; assumption.
  - intros n b v IH. apply parInjCong; assumption.
  - intros n c IH. apply parThunkCong; assumption.
  - intros n. apply parCu.
  - intros n v IH. apply parForceCong; assumption.
  - intros n c IH. apply parLambda; assumption.
  - intros n c IH v IHv. apply parAppCong; assumption.
  - intros n c IH c0 IH0. apply parTupleCong; assumption.
  - intros n v IH. apply parRetCong; assumption.
  - intros n c IH c0 IH0. apply parLetinCong; assumption.
  - intros n b c IH. apply parProjCong; assumption.
  - intros n v IH. apply parCaseZCong; assumption.
  - intros n v IH c IHc c0 IH0. apply parCaseSCong; assumption.
  - intros n v IH c IHc. apply parCasePCong; assumption.
Qed.

Lemma par_refl : forall n (c : comp n), par n c c.
Proof. intros. destruct (par_refl_lem n) as [H1 H2]. apply H2. Qed.

Lemma parv_refl : forall n (v : value n), parv n v v.
Proof. intros. destruct (par_refl_lem n) as [H1 H2]. apply H1. Qed.

Lemma par_ren_lem :
  (forall (n : nat) (c c' : comp n) (p : par n c c') (m : nat) (xi : fin n -> fin m),
      par m (ren_comp xi c) (ren_comp xi c'))
  /\ (forall (n : nat) (v v' : value n) (p : parv n v v') (m : nat) (xi : fin n -> fin m),
      parv m (ren_value xi v) (ren_value xi v')).
Proof.
  apply mutind_par.
  - intros n m xi. apply parCu.
  - intros n c c' p IH m xi. cbn [ren_comp ren_value]. apply parForce. apply (IH m xi).
  - intros n v v' p IH m xi. cbn [ren_comp ren_value]. apply parForceCong. apply (IH m xi).
  - intros n c c' p IH m xi. cbn [ren_comp ren_value]. apply parLambda.
    apply (IH (S m) (upRen_value_value xi)).
  - intros n c c' v v' p IH p0 IH0 m xi. cbn [ren_comp ren_value]. apply parAppCong.
    + apply (IH m xi).
    + apply (IH0 m xi).
  - intros n c c' v v' p IH p0 IH0 m xi. cbn [ren_comp ren_value].
    rewrite ren_subst_single. apply parAppRed.
    + apply (IH (S m) (upRen_value_value xi)).
    + apply (IH0 m xi).
  - intros n c1 c1' c2 c2' p IH p0 IH0 m xi. cbn [ren_comp ren_value]. apply parTupleCong.
    + apply (IH m xi). + apply (IH0 m xi).
  - intros n v v' p IH m xi. cbn [ren_comp ren_value]. apply parRetCong. apply (IH m xi).
  - intros n c1 c1' c2 c2' p IH p0 IH0 m xi. cbn [ren_comp ren_value]. apply parLetinCong.
    + apply (IH m xi).
    + apply (IH0 (S m) (upRen_value_value xi)).
  - intros n v v' c c' p IH p0 IH0 m xi. cbn [ren_comp ren_value].
    rewrite ren_subst_single. apply parLetinRed.
    + apply (IH m xi).
    + apply (IH0 (S m) (upRen_value_value xi)).
  - intros n b c c' p IH m xi. cbn [ren_comp ren_value]. apply parProjCong. apply (IH m xi).
  - intros n c1 c1' c2 c2' p IH p0 IH0 m xi. cbn [ren_comp ren_value].
    apply (parProjRedTrue m (ren_comp xi c1) (ren_comp xi c1') (ren_comp xi c2) (ren_comp xi c2')).
    + apply (IH m xi). + apply (IH0 m xi).
  - intros n c1 c1' c2 c2' p IH p0 IH0 m xi. cbn [ren_comp ren_value].
    apply (parProjRedFalse m (ren_comp xi c1) (ren_comp xi c1') (ren_comp xi c2) (ren_comp xi c2')).
    + apply (IH m xi). + apply (IH0 m xi).
  - intros n v v' p IH m xi. cbn [ren_comp ren_value]. apply parCaseZCong. apply (IH m xi).
  - intros n v v' c1 c1' c2 c2' p IH p0 IH0 p1 IH1 m xi. cbn [ren_comp ren_value].
    apply parCaseSCong.
    + apply (IH m xi).
    + apply (IH0 (S m) (upRen_value_value xi)).
    + apply (IH1 (S m) (upRen_value_value xi)).
  - intros n v v' c1 c1' c2 c2' p IH p0 IH0 p1 IH1 m xi. cbn [ren_comp ren_value].
    rewrite ren_subst_single. cbn [ren_comp ren_value].
    apply (parCaseSRedTrue m (ren_value xi v) (ren_value xi v')
             (ren_comp (upRen_value_value xi) c1) (ren_comp (upRen_value_value xi) c1')
             (ren_comp (upRen_value_value xi) c2) (ren_comp (upRen_value_value xi) c2')).
    + apply (IH m xi).
    + apply (IH0 (S m) (upRen_value_value xi)).
    + apply (IH1 (S m) (upRen_value_value xi)).
  - intros n v v' c1 c1' c2 c2' p IH p0 IH0 p1 IH1 m xi. cbn [ren_comp ren_value].
    rewrite ren_subst_single. cbn [ren_comp ren_value].
    apply (parCaseSRedFalse m (ren_value xi v) (ren_value xi v')
             (ren_comp (upRen_value_value xi) c1) (ren_comp (upRen_value_value xi) c1')
             (ren_comp (upRen_value_value xi) c2) (ren_comp (upRen_value_value xi) c2')).
    + apply (IH m xi).
    + apply (IH0 (S m) (upRen_value_value xi)).
    + apply (IH1 (S m) (upRen_value_value xi)).
  - intros n v v' c c' p IH p0 IH0 m xi. cbn [ren_comp ren_value]. apply parCasePCong.
    + apply (IH m xi).
    + apply (IH0 (S (S m)) (upRen_value_value (upRen_value_value xi))).
  - intros n v1 v1' v2 v2' c c' p IH p0 IH0 p1 IH1 m xi. cbn [ren_comp ren_value].
    rewrite ren_subst_double. apply parCasePRed.
    + apply (IH m xi).
    + apply (IH0 m xi).
    + apply (IH1 (S (S m)) (upRen_value_value (upRen_value_value xi))).
  - intros n i m xi. cbn [ren_comp ren_value]. apply parVar.
  - intros n m xi. cbn [ren_comp ren_value]. apply parU.
  - intros n v1 v1' v2 v2' p IH p0 IH0 m xi. cbn [ren_comp ren_value]. apply parPairCong.
    + apply (IH m xi). + apply (IH0 m xi).
  - intros n b v v' p IH m xi. cbn [ren_comp ren_value]. apply parInjCong. apply (IH m xi).
  - intros n c c' p IH m xi. cbn [ren_comp ren_value]. apply parThunkCong. apply (IH m xi).
Qed.

Lemma par_ren : forall n (c c' : comp n) m (xi : fin n -> fin m),
    par n c c' -> par m (ren_comp xi c) (ren_comp xi c').
Proof. intros. destruct par_ren_lem as [H1 H2]. apply (H1 n c c' H m xi). Qed.

Lemma parv_ren : forall n (v v' : value n) m (xi : fin n -> fin m),
    parv n v v' -> parv m (ren_value xi v) (ren_value xi v').
Proof. intros. destruct par_ren_lem as [H1 H2]. apply (H2 n v v' H m xi). Qed.

Lemma subst_ids_lem : forall n,
  (forall (v : value n), subst_value (ids) v = v)
  /\ (forall (c : comp n), subst_comp (ids) c = c).
Proof.
  apply mutind_val_comp.
  - intros n f. cbn. reflexivity.
  - intros n. reflexivity.
  - intros n v IH v0 IH0. cbn. f_equal; assumption.
  - intros n b v IH. cbn. f_equal. assumption.
  - intros n c IH. cbn. f_equal. assumption.
  - intros n. reflexivity.
  - intros n v IH. cbn. f_equal. assumption.
  - intros n c IH. cbn. f_equal.
    transitivity (subst_comp (ids) c).
    + apply subst_comp_ext. intro i. destruct i as [j|]; cbn.
      * unfold funcomp; cbn. reflexivity.
      * reflexivity.
    + apply IH.
  - intros n c IH v IHv. cbn. f_equal; assumption.
  - intros n c IH c0 IH0. cbn. f_equal; assumption.
  - intros n v IH. cbn. f_equal. assumption.
  - intros n c IH c0 IH0. cbn. f_equal.
    + assumption.
    + transitivity (subst_comp (ids) c0).
      * apply subst_comp_ext. intro i. destruct i as [j|]; cbn.
        -- unfold funcomp; cbn. reflexivity.
        -- reflexivity.
      * apply IH0.
  - intros n b c IH. cbn. f_equal. assumption.
  - intros n v IH. cbn. f_equal. assumption.
  - intros n v IH c IHc c0 IH0. cbn. f_equal.
    + assumption.
    + transitivity (subst_comp (ids) c).
      * apply subst_comp_ext. intro i. destruct i as [j|]; cbn.
        -- unfold funcomp; cbn. reflexivity.
        -- reflexivity.
      * apply IHc.
    + transitivity (subst_comp (ids) c0).
      * apply subst_comp_ext. intro i. destruct i as [j|]; cbn.
        -- unfold funcomp; cbn. reflexivity.
        -- reflexivity.
      * apply IH0.
  - intros n v IH c IHc. cbn. f_equal.
    + assumption.
    + transitivity (subst_comp (ids) c).
      * apply subst_comp_ext. intro i. destruct i as [j|]; cbn.
        -- destruct j as [j'|]; cbn.
           ++ unfold funcomp; cbn. reflexivity.
           ++ reflexivity.
        -- reflexivity.
      * apply IHc.
Qed.

Lemma subst_value_ids : forall n (v : value n), subst_value (ids) v = v.
Proof. intros. destruct (subst_ids_lem n) as [H1 H2]. apply H1. Qed.

Lemma subst_comp_ids : forall n (c : comp n), subst_comp (ids) c = c.
Proof. intros. destruct (subst_ids_lem n) as [H1 H2]. apply H2. Qed.

Lemma subst_comp_scons : forall n (c : comp (S n)) m (v : value n) (tau : fin n -> value m),
    (c[v..])[tau] = (c[up_value_value tau])[(v[tau])..].
Proof.
  intros n c m v tau. rewrite subst_comp_subst. rewrite subst_comp_subst.
  apply subst_comp_ext. intro i. destruct i as [j|]; cbn.
  - unfold funcomp. rewrite subst_value_ren.
    change (tau j = subst_value (ids) (tau j)).
    rewrite subst_value_ids. reflexivity.
  - reflexivity.
Qed.

Lemma subst_comp_scons2 : forall n (c : comp (S (S n))) m (v1 v2 : value n) (tau : fin n -> value m),
    (c[v2,v1..])[tau] = (c[up_value_value (up_value_value tau)])[(v2[tau],v1[tau]..)].
Proof.
  intros n c m v1 v2 tau. rewrite subst_comp_subst. rewrite subst_comp_subst.
  apply subst_comp_ext. intro i. destruct i as [j|]; cbn.
  - destruct j as [j'|]; cbn.
    + unfold funcomp. rewrite subst_value_ren. rewrite subst_value_ren.
      change (tau j' = subst_value (ids) (tau j')).
      rewrite subst_value_ids. reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma pointwise_par_up : forall n m (sigma tau : fin n -> value m),
    (forall (i : fin n), parv m (sigma i) (tau i)) ->
    forall (i : fin (S n)), parv (S m) ((up_value_value sigma) i) ((up_value_value tau) i).
Proof.
  intros n m sigma tau H i. destruct i as [j|]; cbn.
  - apply parv_ren with (n := m) (m := S m) (xi := shift). apply H.
  - apply parVar.
Qed.
Arguments pointwise_par_up {n} {m} {sigma} {tau} _.

Lemma par_subst_lem :
  (forall (n : nat) (c c' : comp n) (p : par n c c') (m : nat)
          (sigma tau : fin n -> value m),
      (forall (i : fin n), parv m (sigma i) (tau i)) -> par m (c[sigma]) (c'[tau]))
  /\ (forall (n : nat) (v v' : value n) (p : parv n v v') (m : nat)
          (sigma tau : fin n -> value m),
      (forall (i : fin n), parv m (sigma i) (tau i)) -> parv m (v[sigma]) (v'[tau])).
Proof.
  apply mutind_par.
  - intros n m sigma tau H. cbn. apply parCu.
  - intros n c c' p IH m sigma tau H. cbn [subst_comp subst_value]. apply parForce.
    apply (IH m sigma tau H).
  - intros n v v' p IH m sigma tau H. cbn [subst_comp subst_value]. apply parForceCong.
    apply (IH m sigma tau H).
  - intros n c c' p IH m sigma tau H. cbn [subst_comp subst_value]. apply parLambda.
    apply (IH (S m) (up_value_value sigma) (up_value_value tau) (pointwise_par_up H)).
  - intros n c c' v v' p IH p0 IH0 m sigma tau H. cbn [subst_comp subst_value].
    apply parAppCong. + apply (IH m sigma tau H). + apply (IH0 m sigma tau H).
  - intros n c c' v v' p IH p0 IH0 m sigma tau H. cbn [subst_comp subst_value].
    rewrite subst_comp_scons. apply parAppRed.
    + apply (IH (S m) (up_value_value sigma) (up_value_value tau) (pointwise_par_up H)).
    + apply (IH0 m sigma tau H).
  - intros n c1 c1' c2 c2' p IH p0 IH0 m sigma tau H. cbn [subst_comp subst_value].
    apply parTupleCong. + apply (IH m sigma tau H). + apply (IH0 m sigma tau H).
  - intros n v v' p IH m sigma tau H. cbn [subst_comp subst_value]. apply parRetCong.
    apply (IH m sigma tau H).
  - intros n c1 c1' c2 c2' p IH p0 IH0 m sigma tau H. cbn [subst_comp subst_value].
    apply parLetinCong.
    + apply (IH m sigma tau H).
    + apply (IH0 (S m) (up_value_value sigma) (up_value_value tau) (pointwise_par_up H)).
  - intros n v v' c c' p IH p0 IH0 m sigma tau H. cbn [subst_comp subst_value].
    rewrite subst_comp_scons. apply parLetinRed.
    + apply (IH m sigma tau H).
    + apply (IH0 (S m) (up_value_value sigma) (up_value_value tau) (pointwise_par_up H)).
  - intros n b c c' p IH m sigma tau H. cbn [subst_comp subst_value]. apply parProjCong.
    apply (IH m sigma tau H).
  - intros n c1 c1' c2 c2' p IH p0 IH0 m sigma tau H. cbn [subst_comp subst_value].
    apply (parProjRedTrue m (c1[sigma]) (c1'[tau]) (c2[sigma]) (c2'[tau])).
    + apply (IH m sigma tau H). + apply (IH0 m sigma tau H).
  - intros n c1 c1' c2 c2' p IH p0 IH0 m sigma tau H. cbn [subst_comp subst_value].
    apply (parProjRedFalse m (c1[sigma]) (c1'[tau]) (c2[sigma]) (c2'[tau])).
    + apply (IH m sigma tau H). + apply (IH0 m sigma tau H).
  - intros n v v' p IH m sigma tau H. cbn [subst_comp subst_value]. apply parCaseZCong.
    apply (IH m sigma tau H).
  - intros n v v' c1 c1' c2 c2' p IH p0 IH0 p1 IH1 m sigma tau H.
    cbn [subst_comp subst_value]. apply parCaseSCong.
    + apply (IH m sigma tau H).
    + apply (IH0 (S m) (up_value_value sigma) (up_value_value tau) (pointwise_par_up H)).
    + apply (IH1 (S m) (up_value_value sigma) (up_value_value tau) (pointwise_par_up H)).
  - intros n v v' c1 c1' c2 c2' p IH p0 IH0 p1 IH1 m sigma tau H.
    cbn [subst_comp subst_value]. rewrite subst_comp_scons.
    apply (parCaseSRedTrue m (v[sigma]) (v'[tau])
             (c1[up_value_value sigma]) (c1'[up_value_value tau])
             (c2[up_value_value sigma]) (c2'[up_value_value tau])).
    + apply (IH m sigma tau H).
    + apply (IH0 (S m) (up_value_value sigma) (up_value_value tau) (pointwise_par_up H)).
    + apply (IH1 (S m) (up_value_value sigma) (up_value_value tau) (pointwise_par_up H)).
  - intros n v v' c1 c1' c2 c2' p IH p0 IH0 p1 IH1 m sigma tau H.
    cbn [subst_comp subst_value]. rewrite subst_comp_scons.
    apply (parCaseSRedFalse m (v[sigma]) (v'[tau])
             (c1[up_value_value sigma]) (c1'[up_value_value tau])
             (c2[up_value_value sigma]) (c2'[up_value_value tau])).
    + apply (IH m sigma tau H).
    + apply (IH0 (S m) (up_value_value sigma) (up_value_value tau) (pointwise_par_up H)).
    + apply (IH1 (S m) (up_value_value sigma) (up_value_value tau) (pointwise_par_up H)).
  - intros n v v' c c' p IH p0 IH0 m sigma tau H. cbn [subst_comp subst_value].
    apply parCasePCong.
    + apply (IH m sigma tau H).
    + apply (IH0 (S (S m)) (up_value_value (up_value_value sigma))
                              (up_value_value (up_value_value tau))
                              (pointwise_par_up (pointwise_par_up H))).
  - intros n v1 v1' v2 v2' c c' p IH p0 IH0 p1 IH1 m sigma tau H.
    cbn [subst_comp subst_value]. rewrite subst_comp_scons2. apply parCasePRed.
    + apply (IH m sigma tau H).
    + apply (IH0 m sigma tau H).
    + apply (IH1 (S (S m)) (up_value_value (up_value_value sigma))
                              (up_value_value (up_value_value tau))
                              (pointwise_par_up (pointwise_par_up H))).
  - intros n i m sigma tau H. cbn [subst_comp subst_value]. apply H.
  - intros n m sigma tau H. cbn [subst_comp subst_value]. apply parU.
  - intros n v1 v1' v2 v2' p IH p0 IH0 m sigma tau H. cbn [subst_comp subst_value].
    apply parPairCong. + apply (IH m sigma tau H). + apply (IH0 m sigma tau H).
  - intros n b v v' p IH m sigma tau H. cbn [subst_comp subst_value]. apply parInjCong.
    apply (IH m sigma tau H).
  - intros n c c' p IH m sigma tau H. cbn [subst_comp subst_value]. apply parThunkCong.
    apply (IH m sigma tau H).
Qed.

Lemma par_subst : forall n (c c' : comp n) m (sigma tau : fin n -> value m),
    par n c c' -> (forall (i : fin n), parv m (sigma i) (tau i)) ->
    par m (c[sigma]) (c'[tau]).
Proof. intros. destruct par_subst_lem as [H1 H2]. apply (H1 n c c' H m sigma tau H0). Qed.

Lemma parv_subst : forall n (v v' : value n) m (sigma tau : fin n -> value m),
    parv n v v' -> (forall (i : fin n), parv m (sigma i) (tau i)) ->
    parv m (v[sigma]) (v'[tau]).
Proof. intros. destruct par_subst_lem as [H1 H2]. apply (H2 n v v' H m sigma tau H0). Qed.

Fixpoint dev_comp {n : nat} (c : comp n) {struct c} : comp n :=
  match c with
  | cu => cu
  | force v =>
      match v with
      | thunk c0 => dev_comp c0
      | _ => force (dev_value v)
      end
  | lambda c0 => lambda (dev_comp c0)
  | app c0 v =>
      match c0 with
      | lambda b => (dev_comp b)[(dev_value v)..]
      | _ => app (dev_comp c0) (dev_value v)
      end
  | tuple c1 c2 => tuple (dev_comp c1) (dev_comp c2)
  | ret v => ret (dev_value v)
  | letin c1 c2 =>
      match c1 with
      | ret v => (dev_comp c2)[(dev_value v)..]
      | _ => letin (dev_comp c1) (dev_comp c2)
      end
  | proj b c0 =>
      match c0 with
      | tuple c1 c2 => (if b then dev_comp c1 else dev_comp c2)
      | _ => proj b (dev_comp c0)
      end
  | caseZ v => caseZ (dev_value v)
  | caseS v c1 c2 =>
      match v with
      | inj b v0 => ((if b then dev_comp c1 else dev_comp c2)[(dev_value v0)..])
      | _ => caseS (dev_value v) (dev_comp c1) (dev_comp c2)
      end
  | caseP v c0 =>
      match v with
      | pair v1 v2 => (dev_comp c0)[(dev_value v2),(dev_value v1)..]
      | _ => caseP (dev_value v) (dev_comp c0)
      end
  end
with dev_value {n : nat} (v : value n) {struct v} : value n :=
  match v with
  | var_value i => var_value i
  | u => u
  | pair v1 v2 => pair (dev_value v1) (dev_value v2)
  | inj b v0 => inj b (dev_value v0)
  | thunk c => thunk (dev_comp c)
  end.


(* Injection of existT equalities over nat indices (axiom-free, uses decidable
   equality of the index type). *)
Ltac injT :=
  repeat match goal with
  | H : existT _ _ _ = existT _ _ _ |- _ =>
      apply (inj_pair2_eq_dec _ Nat.eq_dec) in H; subst; clear H
  end.

Lemma par_lambda_src_inv : forall n (b : comp (S n)) (c' : comp n),
    par n (lambda b) c' -> exists b', c' = lambda b' /\ par (S n) b b'.
Proof. intros n b c' H. inversion H. subst. injT. eauto. Qed.
Arguments par_lambda_src_inv {n} {b} {c'} _.

Lemma par_tuple_src_inv : forall n (c1 c2 c' : comp n),
    par n (tuple c1 c2) c' ->
    exists c1' c2', c' = tuple c1' c2' /\ par n c1 c1' /\ par n c2 c2'.
Proof. intros n c1 c2 c' H. inversion H. subst. injT. eauto. Qed.
Arguments par_tuple_src_inv {n} {c1} {c2} {c'} _.

Lemma par_ret_src_inv : forall n (v : value n) (c' : comp n),
    par n (ret v) c' -> exists v', c' = ret v' /\ parv n v v'.
Proof. intros n v c' H. inversion H. subst. injT. eauto. Qed.
Arguments par_ret_src_inv {n} {v} {c'} _.

Lemma parv_thunk_src_inv : forall n (c : comp n) (v' : value n),
    parv n (thunk c) v' -> exists c', v' = thunk c' /\ par n c c'.
Proof. intros n c v' H. inversion H. subst. injT. eauto. Qed.
Arguments parv_thunk_src_inv {n} {c} {v'} _.

Lemma parv_inj_src_inv : forall n b (v : value n) (v' : value n),
    parv n (inj b v) v' -> exists v'', v' = inj b v'' /\ parv n v v''.
Proof. intros n b v v' H. inversion H. subst. injT. eauto. Qed.
Arguments parv_inj_src_inv {n} {b} {v} {v'} _.

Lemma parv_pair_src_inv : forall n (v1 v2 v' : value n),
    parv n (pair v1 v2) v' ->
    exists v1' v2', v' = pair v1' v2' /\ parv n v1 v1' /\ parv n v2 v2'.
Proof. intros n v1 v2 v' H. inversion H. subst. injT. eauto. Qed.
Arguments parv_pair_src_inv {n} {v1} {v2} {v'} _.

(* ===== Generic consequences of the diamond property ===== *)

Section GenericStar.
Context {X : Type}.

Lemma star_trans_gen (R : X -> X -> Prop) :
  forall x y z, star R x y -> star R y z -> star R x z.
Proof.
  intros x y z H. induction H as [x | x x' y Hxx' Hx'y IH]; intro H2.
  - exact H2.
  - eapply starStep; [exact Hxx' | apply IH; exact H2].
Qed.

Lemma star_strip (R : X -> X -> Prop) (D : diamond R) :
  forall x z, star R x z -> forall y, R x y -> exists w, star R y w /\ star R z w.
Proof.
  intros x z H. induction H as [x | x z1 z Hxz1 Hz1z IH]; intros y Hxy.
  - exists y. split. apply starRefl. eapply starStep; [exact Hxy | apply starRefl].
  - destruct (D x y z1 Hxy Hxz1) as [w0 Hyw0 Hz1w0].
    destruct (IH w0 Hz1w0) as [w Hw0w]. destruct Hw0w as [Hw0w' Hzw].
    exists w. split.
    + eapply starStep; [exact Hyw0 | exact Hw0w'].
    + exact Hzw.
Qed.

Lemma diamond_star (R : X -> X -> Prop) (D : diamond R) : diamond (star R).
Proof.
  intros x y z Hxy. revert z.
  induction Hxy as [x | x y1 y Hxy1 Hy1y IH]; intros z Hxz.
  - exists z.
    + exact Hxz.
    + apply starRefl.
  - destruct (star_strip R D x z Hxz y1 Hxy1) as [w0 Hw0].
    destruct Hw0 as [Hy1w0 Hzw0].
    destruct (IH w0 Hy1w0) as [w Hyw' Hw0w].
    exists w.
    + exact Hyw'.
    + eapply star_trans_gen.
      * exact Hzw0.
      * exact Hw0w.
Qed.

End GenericStar.

(* ===== Complete development simulates parallel reduction ===== *)

Lemma dev_sim_lem :
  (forall (n : nat) (c c' : comp n) (p : par n c c'), par n c' (dev_comp c))
  /\ (forall (n : nat) (v v' : value n) (p : parv n v v'), parv n v' (dev_value v)).
Proof.
  apply mutind_par.
  - intros n. cbn [dev_comp]. apply parCu.
  - intros n c c' p IH. cbn [dev_comp]. apply IH.
  - intros n v v' p IH. destruct v as [i| |v1 v2|bb vv|cc].
    + cbn [dev_comp]. apply parForceCong. apply IH.
    + cbn [dev_comp]. apply parForceCong. apply IH.
    + cbn [dev_comp]. apply parForceCong. apply IH.
    + cbn [dev_comp]. apply parForceCong. apply IH.
    + destruct (parv_thunk_src_inv p) as [e He]. destruct He as [Ev Hpe]. subst v'.
      cbn [dev_value] in IH.
      destruct (parv_thunk_src_inv IH) as [e' He']. destruct He' as [E2 H2].
      injection E2 as E2'. subst e'.
      cbn [dev_comp]. apply parForce. apply H2.
  - intros n c c' p IH. cbn [dev_comp]. apply parLambda. apply IH.
  - intros n c c' v v' p IH p0 IH0.
    destruct c as [| fv | lb | ac av | tc1 tc2 | rv | lc1 lc2 | pb pc | zv | sv sc1 sc2 | pv pc2].
    + cbn [dev_comp]. apply parAppCong. apply IH. apply IH0.
    + cbn [dev_comp]. apply parAppCong. apply IH. apply IH0.
    + destruct (par_lambda_src_inv p) as [bA HbA]. destruct HbA as [Ec' HbA].
      subst c'. cbn [dev_comp] in IH.
      destruct (par_lambda_src_inv IH) as [bB HB]. destruct HB as [E2 H2].
      injection E2 as E2'. subst bB.
      cbn [dev_comp]. apply parAppRed. apply H2. apply IH0.
    + cbn [dev_comp]. apply parAppCong. apply IH. apply IH0.
    + cbn [dev_comp]. apply parAppCong. apply IH. apply IH0.
    + cbn [dev_comp]. apply parAppCong. apply IH. apply IH0.
    + cbn [dev_comp]. apply parAppCong. apply IH. apply IH0.
    + cbn [dev_comp]. apply parAppCong. apply IH. apply IH0.
    + cbn [dev_comp]. apply parAppCong. apply IH. apply IH0.
    + cbn [dev_comp]. apply parAppCong. apply IH. apply IH0.
    + cbn [dev_comp]. apply parAppCong. apply IH. apply IH0.
  - intros n c c' v v' p IH p0 IH0. cbn [dev_comp].
    apply par_subst.
    + apply IH.
    + intro i. destruct i as [j|]; cbn.
      * apply parVar.
      * apply IH0.
  - intros n c1 c1' c2 c2' p IH p0 IH0. cbn [dev_comp]. apply parTupleCong.
    apply IH. apply IH0.
  - intros n v v' p IH. cbn [dev_comp]. apply parRetCong. apply IH.
  - intros n c1 c1' c2 c2' p IH p0 IH0.
    destruct c1 as [| fv | lb | ac av | tc1 tc2 | rv | lc1 lc2 | pb pc | zv | sv sc1 sc2 | pv pc2].
    + cbn [dev_comp]. apply parLetinCong. apply IH. apply IH0.
    + cbn [dev_comp]. apply parLetinCong. apply IH. apply IH0.
    + cbn [dev_comp]. apply parLetinCong. apply IH. apply IH0.
    + cbn [dev_comp]. apply parLetinCong. apply IH. apply IH0.
    + cbn [dev_comp]. apply parLetinCong. apply IH. apply IH0.
    + destruct (par_ret_src_inv p) as [vA HvA]. destruct HvA as [Ec1' HvA].
      subst c1'. cbn [dev_comp] in IH.
      destruct (par_ret_src_inv IH) as [vB HB]. destruct HB as [E2 H2].
      injection E2 as E2'. subst vB.
      cbn [dev_comp]. apply parLetinRed. apply H2. apply IH0.
    + cbn [dev_comp]. apply parLetinCong. apply IH. apply IH0.
    + cbn [dev_comp]. apply parLetinCong. apply IH. apply IH0.
    + cbn [dev_comp]. apply parLetinCong. apply IH. apply IH0.
    + cbn [dev_comp]. apply parLetinCong. apply IH. apply IH0.
    + cbn [dev_comp]. apply parLetinCong. apply IH. apply IH0.
  - intros n v v' c c' p IH p0 IH0. cbn [dev_comp].
    apply par_subst.
    + apply IH0.
    + intro i. destruct i as [j|]; cbn.
      * apply parVar.
      * apply IH.
  - intros n b c c' p IH.
    destruct c as [| fv | lb | ac av | tc1 tc2 | rv | lc1 lc2 | pb pc | zv | sv sc1 sc2 | pv pc2].
    + cbn [dev_comp]. apply parProjCong. apply IH.
    + cbn [dev_comp]. apply parProjCong. apply IH.
    + cbn [dev_comp]. apply parProjCong. apply IH.
    + cbn [dev_comp]. apply parProjCong. apply IH.
    + destruct (par_tuple_src_inv p) as [c1A Hc]. destruct Hc as [c2A Hc].
      destruct Hc as [Ec' H12]. destruct H12 as [H1 H2]. subst c'.
      cbn [dev_comp] in IH.
      destruct (par_tuple_src_inv IH) as [c1B Hc]. destruct Hc as [c2B Hc].
      destruct Hc as [E2 H12]. destruct H12 as [H1' H2'].
      injection E2 as E1 E2'. subst c1B. subst c2B.
      cbn [dev_comp]. destruct b.
      * apply (parProjRedTrue n c1A (dev_comp tc1) c2A (dev_comp tc2)). apply H1'. apply H2'.
      * apply (parProjRedFalse n c1A (dev_comp tc1) c2A (dev_comp tc2)). apply H1'. apply H2'.
    + cbn [dev_comp]. apply parProjCong. apply IH.
    + cbn [dev_comp]. apply parProjCong. apply IH.
    + cbn [dev_comp]. apply parProjCong. apply IH.
    + cbn [dev_comp]. apply parProjCong. apply IH.
    + cbn [dev_comp]. apply parProjCong. apply IH.
    + cbn [dev_comp]. apply parProjCong. apply IH.
  - intros n c1 c1' c2 c2' p IH p0 IH0. cbn [dev_comp]. apply IH.
  - intros n c1 c1' c2 c2' p IH p0 IH0. cbn [dev_comp]. apply IH0.
  - intros n v v' p IH. cbn [dev_comp]. apply parCaseZCong. apply IH.
  - intros n v v' c1 c1' c2 c2' p IH p0 IH0 p1 IH1.
    destruct v as [i| |v1 v2|bb vv|cc].
    + cbn [dev_comp]. apply parCaseSCong. apply IH. apply IH0. apply IH1.
    + cbn [dev_comp]. apply parCaseSCong. apply IH. apply IH0. apply IH1.
    + cbn [dev_comp]. apply parCaseSCong. apply IH. apply IH0. apply IH1.
    + destruct (parv_inj_src_inv p) as [vA Hv]. destruct Hv as [Ev' Hv]. subst v'.
      cbn [dev_value] in IH.
      destruct (parv_inj_src_inv IH) as [vB HB]. destruct HB as [E2 H2].
      injection E2 as E2'. subst vB.
      cbn [dev_comp]. destruct bb.
      * apply (parCaseSRedTrue n vA (dev_value vv) c1' (dev_comp c1) c2' (dev_comp c2)).
        apply H2. apply IH0. apply IH1.
      * apply (parCaseSRedFalse n vA (dev_value vv) c1' (dev_comp c1) c2' (dev_comp c2)).
        apply H2. apply IH0. apply IH1.
    + cbn [dev_comp]. apply parCaseSCong. apply IH. apply IH0. apply IH1.
  - intros n v v' c1 c1' c2 c2' p IH p0 IH0 p1 IH1. cbn [dev_comp].
    apply par_subst.
    + apply IH0.
    + intro i. destruct i as [j|]; cbn.
      * apply parVar.
      * apply IH.
  - intros n v v' c1 c1' c2 c2' p IH p0 IH0 p1 IH1. cbn [dev_comp].
    apply par_subst.
    + apply IH1.
    + intro i. destruct i as [j|]; cbn.
      * apply parVar.
      * apply IH.
  - intros n v v' c c' p IH p0 IH0.
    destruct v as [i| |v1 v2|bb vv|cc].
    + cbn [dev_comp]. apply parCasePCong. apply IH. apply IH0.
    + cbn [dev_comp]. apply parCasePCong. apply IH. apply IH0.
    + destruct (parv_pair_src_inv p) as [v1A Hv]. destruct Hv as [v2A Hv].
      destruct Hv as [Ev' H12]. destruct H12 as [H1 H2]. subst v'.
      cbn [dev_value] in IH.
      destruct (parv_pair_src_inv IH) as [v1B Hv]. destruct Hv as [v2B Hv].
      destruct Hv as [E2 H12]. destruct H12 as [H1' H2'].
      injection E2 as E1 E2'. subst v1B. subst v2B.
      cbn [dev_comp].
      apply (parCasePRed n v1A (dev_value v1) v2A (dev_value v2) c' (dev_comp c)).
      apply H1'. apply H2'. apply IH0.
    + cbn [dev_comp]. apply parCasePCong. apply IH. apply IH0.
    + cbn [dev_comp]. apply parCasePCong. apply IH. apply IH0.
  - intros n v1 v1' v2 v2' c c' p IH p0 IH0 p1 IH1. cbn [dev_comp].
    apply par_subst.
    + apply IH1.
    + intro i. destruct i as [j|]; cbn.
      * destruct j as [j'|]; cbn.
        -- apply parVar.
        -- apply IH.
      * apply IH0.
  - intros n i. cbn [dev_value]. apply parVar.
  - intros n. cbn [dev_value]. apply parU.
  - intros n v1 v1' v2 v2' p IH p0 IH0. cbn [dev_value]. apply parPairCong. apply IH. apply IH0.
  - intros n b v v' p IH. cbn [dev_value]. apply parInjCong. apply IH.
  - intros n c c' p IH. cbn [dev_value]. apply parThunkCong. apply IH.
Qed.

Lemma dev_sim_comp : forall (n : nat) (c c' : comp n), par n c c' -> par n c' (dev_comp c).
Proof. intros. destruct dev_sim_lem as [H1 H2]. apply (H1 n c c' H). Qed.

Lemma dev_sim_value : forall (n : nat) (v v' : value n), parv n v v' -> parv n v' (dev_value v).
Proof. intros. destruct dev_sim_lem as [H1 H2]. apply (H2 n v v' H). Qed.

(* ===== Diamond of parallel reduction ===== *)

Lemma par_diamond_lem :
  (forall (n : nat) (c a b : comp n), par n c a -> par n c b -> joinable (par n) a b)
  /\ (forall (n : nat) (v a b : value n), parv n v a -> parv n v b -> joinable (parv n) a b).
Proof.
  split.
  - intros n c a b H1 H2. exists (dev_comp c).
    + apply dev_sim_comp. exact H1.
    + apply dev_sim_comp. exact H2.
  - intros n v a b H1 H2. exists (dev_value v).
    + apply dev_sim_value. exact H1.
    + apply dev_sim_value. exact H2.
Qed.

Lemma par_diamond (n : nat) : diamond (par n).
Proof. intros c a b H1 H2. destruct par_diamond_lem as [H H']. apply (H n c a b H1 H2). Qed.

Lemma parv_diamond (n : nat) : diamond (parv n).
Proof. intros v a b H1 H2. destruct par_diamond_lem as [H H']. apply (H' n v a b H1 H2). Qed.

(* ===== pstep is included in par ===== *)

Lemma pstep_par : forall (n : nat) (c c' : comp n), c ≽ c' -> par n c c'.
Proof.
  intros n c c' H. induction H.
  - apply parForce. apply par_refl.
  - rewrite <- H. apply parAppRed. apply par_refl. apply parv_refl.
  - rewrite H. destruct b; cbn.
    + apply (parProjRedTrue n c1 c1 c2 c2). apply par_refl. apply par_refl.
    + apply (parProjRedFalse n c1 c1 c2 c2). apply par_refl. apply par_refl.
  - rewrite <- H. cbn. apply parLetinRed. apply parv_refl. apply par_refl.
  - rewrite <- H. destruct b; cbn.
    + apply (parCaseSRedTrue n v v c1 c1 c2 c2). apply parv_refl. apply par_refl. apply par_refl.
    + apply (parCaseSRedFalse n v v c1 c1 c2 c2). apply parv_refl. apply par_refl. apply par_refl.
  - rewrite <- H. cbn. apply parCasePRed. apply parv_refl. apply parv_refl. apply par_refl.
Qed.

(* ===== Lifting one-step congruences to reflexive-transitive closure ===== *)

Lemma star_map_comp {n m : nat} (f : comp n -> comp m)
  (Hf : forall (a b : comp n), a ↪ b -> f a ↪ f b) :
  forall (a b : comp n), a ↪* b -> f a ↪* f b.
Proof.
  intros a b H. induction H as [a | a a' b Ha Hrest IH].
  - apply starRefl.
  - eapply starStep; [apply Hf; exact Ha | exact IH].
Qed.

Lemma star_map_value {n m : nat} (f : value n -> value m)
  (Hf : forall (a b : value n), a ↪ᵥ b -> f a ↪ᵥ f b) :
  forall (a b : value n), a ↪ᵥ* b -> f a ↪ᵥ* f b.
Proof.
  intros a b H. induction H as [a | a a' b Ha Hrest IH].
  - apply starRefl.
  - eapply starStep; [apply Hf; exact Ha | exact IH].
Qed.

Lemma star_map_val_comp {n m : nat} (f : value n -> comp m)
  (Hf : forall (a b : value n), a ↪ᵥ b -> f a ↪ f b) :
  forall (a b : value n), a ↪ᵥ* b -> f a ↪* f b.
Proof.
  intros a b H. induction H as [a | a a' b Ha Hrest IH].
  - apply starRefl.
  - eapply starStep; [apply Hf; exact Ha | exact IH].
Qed.

Lemma star_map_comp_val {n m : nat} (f : comp n -> value m)
  (Hf : forall (a b : comp n), a ↪ b -> f a ↪ᵥ f b) :
  forall (a b : comp n), a ↪* b -> f a ↪ᵥ* f b.
Proof.
  intros a b H. induction H as [a | a a' b Ha Hrest IH].
  - apply starRefl.
  - eapply starStep; [apply Hf; exact Ha | exact IH].
Qed.

Lemma star_sstep_lambda n (c c' : comp (S n)) : c ↪* c' -> lambda c ↪* lambda c'.
Proof. intros H. exact (star_map_comp (n:=S n) (m:=n) (fun x => lambda x)
        (fun a b s => sstepLambda s) c c' H). Qed.

Lemma star_sstep_force n (v v' : value n) : v ↪ᵥ* v' -> force v ↪* force v'.
Proof. intros H. exact (star_map_val_comp (n:=n) (m:=n) (fun x => x !)
        (fun a b s => sstepForce s) v v' H). Qed.

Lemma star_sstep_appL n (c c' : comp n) (v : value n) : c ↪* c' -> app c v ↪* app c' v.
Proof. intros H. exact (star_map_comp (n:=n) (m:=n) (fun x => app x v)
        (fun a b s => sstepAppL v s) c c' H). Qed.

Lemma star_sstep_appR n (c : comp n) (v v' : value n) : v ↪ᵥ* v' -> app c v ↪* app c v'.
Proof. intros H. exact (star_map_val_comp (n:=n) (m:=n) (fun x => app c x)
        (fun a b s => sstepAppR c s) v v' H). Qed.

Lemma star_sstep_tupleL n (c1 c1' c2 : comp n) : c1 ↪* c1' -> tuple c1 c2 ↪* tuple c1' c2.
Proof. intros H. exact (star_map_comp (n:=n) (m:=n) (fun x => tuple x c2)
        (fun a b s => sstepTupleL c2 s) c1 c1' H). Qed.

Lemma star_sstep_tupleR n (c1 c2 c2' : comp n) : c2 ↪* c2' -> tuple c1 c2 ↪* tuple c1 c2'.
Proof. intros H. exact (star_map_comp (n:=n) (m:=n) (fun x => tuple c1 x)
        (fun a b s => sstepTupleR c1 s) c2 c2' H). Qed.

Lemma star_sstep_ret n (v v' : value n) : v ↪ᵥ* v' -> ret v ↪* ret v'.
Proof. intros H. exact (star_map_val_comp (n:=n) (m:=n) (fun x => ret x)
        (fun a b s => sstepRet s) v v' H). Qed.

Lemma star_sstep_letinL n (c1 c1' : comp n) (c2 : comp (S n)) :
  c1 ↪* c1' -> letin c1 c2 ↪* letin c1' c2.
Proof. intros H. exact (star_map_comp (n:=n) (m:=n) (fun x => letin x c2)
        (fun a b s => sstepLetinL c2 s) c1 c1' H). Qed.

Lemma star_sstep_letinR n (c1 : comp n) (c2 c2' : comp (S n)) :
  c2 ↪* c2' -> letin c1 c2 ↪* letin c1 c2'.
Proof. intros H. exact (star_map_comp (n:=S n) (m:=n) (fun x => letin c1 x)
        (fun a b s => sstepLetinR c1 s) c2 c2' H). Qed.

Lemma star_sstep_proj n b (c c' : comp n) : c ↪* c' -> proj b c ↪* proj b c'.
Proof. intros H. exact (star_map_comp (n:=n) (m:=n) (fun x => proj b x)
        (fun a b' s => sstepProj b s) c c' H). Qed.

Lemma star_sstep_caseZ n (v v' : value n) : v ↪ᵥ* v' -> caseZ v ↪* caseZ v'.
Proof. intros H. exact (star_map_val_comp (n:=n) (m:=n) (fun x => caseZ x)
        (fun a b s => sstepCaseZ s) v v' H). Qed.

Lemma star_sstep_caseSV n (v v' : value n) (c1 c2 : comp (S n)) :
  v ↪ᵥ* v' -> caseS v c1 c2 ↪* caseS v' c1 c2.
Proof. intros H. exact (star_map_val_comp (n:=n) (m:=n) (fun x => caseS x c1 c2)
        (fun a b s => sstepCaseSV c1 c2 s) v v' H). Qed.

Lemma star_sstep_caseSL n (v : value n) (c1 c1' c2 : comp (S n)) :
  c1 ↪* c1' -> caseS v c1 c2 ↪* caseS v c1' c2.
Proof. intros H. exact (star_map_comp (n:=S n) (m:=n) (fun x => caseS v x c2)
        (fun a b s => sstepCaseSL v c2 s) c1 c1' H). Qed.

Lemma star_sstep_caseSR n (v : value n) (c1 c2 c2' : comp (S n)) :
  c2 ↪* c2' -> caseS v c1 c2 ↪* caseS v c1 c2'.
Proof. intros H. exact (star_map_comp (n:=S n) (m:=n) (fun x => caseS v c1 x)
        (fun a b s => sstepCaseSR v c1 s) c2 c2' H). Qed.

Lemma star_sstep_casePV n (v v' : value n) (c : comp (S (S n))) :
  v ↪ᵥ* v' -> caseP v c ↪* caseP v' c.
Proof. intros H. exact (star_map_val_comp (n:=n) (m:=n) (fun x => caseP x c)
        (fun a b s => sstepCasePV c s) v v' H). Qed.

Lemma star_sstep_casePC n (v : value n) (c c' : comp (S (S n))) :
  c ↪* c' -> caseP v c ↪* caseP v c'.
Proof. intros H. exact (star_map_comp (n:=S (S n)) (m:=n) (fun x => caseP v x)
        (fun a b s => sstepCasePC v s) c c' H). Qed.

Lemma star_sstep_value_pairL n (v1 v1' v2 : value n) :
  v1 ↪ᵥ* v1' -> pair v1 v2 ↪ᵥ* pair v1' v2.
Proof. intros H. exact (star_map_value (n:=n) (m:=n) (fun x => pair x v2)
        (fun a b s => sstepValuePairL v2 s) v1 v1' H). Qed.

Lemma star_sstep_value_pairR n (v1 v2 v2' : value n) :
  v2 ↪ᵥ* v2' -> pair v1 v2 ↪ᵥ* pair v1 v2'.
Proof. intros H. exact (star_map_value (n:=n) (m:=n) (fun x => pair v1 x)
        (fun a b s => sstepValuePairR v1 s) v2 v2' H). Qed.

Lemma star_sstep_value_inj n b (v v' : value n) : v ↪ᵥ* v' -> inj b v ↪ᵥ* inj b v'.
Proof. intros H. exact (star_map_value (n:=n) (m:=n) (fun x => inj b x)
        (fun a b' s => sstepValueInj b s) v v' H). Qed.

Lemma star_sstep_value_thunk n (c c' : comp n) : c ↪* c' -> thunk c ↪ᵥ* thunk c'.
Proof. intros H. exact (star_map_comp_val (n:=n) (m:=n) (fun x => thunk x)
        (fun a b s => sstepValueThunk s) c c' H). Qed.

(* ===== par is included in the reflexive-transitive closure of sstep ===== *)

Lemma par_to_sstep_lem :
  (forall (n : nat) (c c' : comp n), par n c c' -> c ↪* c')
  /\ (forall (n : nat) (v v' : value n), parv n v v' -> v ↪ᵥ* v').
Proof.
  apply mutind_par.
  - intros n. apply starRefl.
  - intros n c c' p IH. eapply starStep.
    exact (sstepPrimitive (pstepForce c)). exact IH.
  - intros n v v' p IH. apply star_sstep_force. exact IH.
  - intros n c c' p IH. apply star_sstep_lambda. exact IH.
  - intros n c c' v v' p IH p0 IH0.
    eapply star_trans_gen. apply star_sstep_appL. exact IH.
    apply star_sstep_appR. exact IH0.
  - intros n c c' v v' p IH p0 IH0.
    eapply star_trans_gen. apply star_sstep_appL. apply star_sstep_lambda. exact IH.
    eapply star_trans_gen. apply star_sstep_appR. exact IH0.
    eapply starStep. apply sstepPrimitive. eapply pstepApp. reflexivity. apply starRefl.
  - intros n c1 c1' c2 c2' p IH p0 IH0.
    eapply star_trans_gen. apply star_sstep_tupleL. exact IH.
    apply star_sstep_tupleR. exact IH0.
  - intros n v v' p IH. apply star_sstep_ret. exact IH.
  - intros n c1 c1' c2 c2' p IH p0 IH0.
    eapply star_trans_gen. apply star_sstep_letinL. exact IH.
    apply star_sstep_letinR. exact IH0.
  - intros n v v' c c' p IH p0 IH0.
    eapply star_trans_gen. apply star_sstep_letinL. apply star_sstep_ret. exact IH.
    eapply star_trans_gen. apply star_sstep_letinR. exact IH0.
    eapply starStep. apply sstepPrimitive. eapply pstepLetin. reflexivity. apply starRefl.
  - intros n b c c' p IH. apply star_sstep_proj. exact IH.
  - intros n c1 c1' c2 c2' p IH p0 IH0.
    eapply star_trans_gen. apply star_sstep_proj. apply star_sstep_tupleL. exact IH.
    eapply star_trans_gen. apply star_sstep_proj. apply star_sstep_tupleR. exact IH0.
    eapply starStep. apply sstepPrimitive. eapply pstepProj. reflexivity. apply starRefl.
  - intros n c1 c1' c2 c2' p IH p0 IH0.
    eapply star_trans_gen. apply star_sstep_proj. apply star_sstep_tupleL. exact IH.
    eapply star_trans_gen. apply star_sstep_proj. apply star_sstep_tupleR. exact IH0.
    eapply starStep. apply sstepPrimitive. eapply pstepProj. reflexivity. apply starRefl.
  - intros n v v' p IH. apply star_sstep_caseZ. exact IH.
  - intros n v v' c1 c1' c2 c2' p IH p0 IH0 p1 IH1.
    eapply star_trans_gen. apply star_sstep_caseSV. exact IH.
    eapply star_trans_gen. apply star_sstep_caseSL. exact IH0.
    apply star_sstep_caseSR. exact IH1.
  - intros n v v' c1 c1' c2 c2' p IH p0 IH0 p1 IH1.
    eapply star_trans_gen. apply star_sstep_caseSV. apply star_sstep_value_inj. exact IH.
    eapply star_trans_gen. apply star_sstep_caseSL. exact IH0.
    eapply star_trans_gen. apply star_sstep_caseSR. exact IH1.
    eapply starStep.
    apply sstepPrimitive. eapply pstepCaseS. reflexivity. apply starRefl.
  - intros n v v' c1 c1' c2 c2' p IH p0 IH0 p1 IH1.
    eapply star_trans_gen. apply star_sstep_caseSV. apply star_sstep_value_inj. exact IH.
    eapply star_trans_gen. apply star_sstep_caseSL. exact IH0.
    eapply star_trans_gen. apply star_sstep_caseSR. exact IH1.
    eapply starStep.
    apply sstepPrimitive. eapply pstepCaseS. reflexivity. apply starRefl.
  - intros n v v' c c' p IH p0 IH0.
    eapply star_trans_gen. apply star_sstep_casePV. exact IH.
    apply star_sstep_casePC. exact IH0.
  - intros n v1 v1' v2 v2' c c' p IH p0 IH0 p1 IH1.
    eapply star_trans_gen.
    apply star_sstep_casePV.
    eapply star_trans_gen. apply star_sstep_value_pairL. exact IH.
    apply star_sstep_value_pairR. exact IH0.
    eapply star_trans_gen. apply star_sstep_casePC. exact IH1.
    eapply starStep.
    apply sstepPrimitive. eapply pstepCaseP. reflexivity. apply starRefl.
  - intros n i. apply starRefl.
  - intros n. apply starRefl.
  - intros n v1 v1' v2 v2' p IH p0 IH0.
    eapply star_trans_gen. apply star_sstep_value_pairL. exact IH.
    apply star_sstep_value_pairR. exact IH0.
  - intros n b v v' p IH. apply star_sstep_value_inj. exact IH.
  - intros n c c' p IH. apply star_sstep_value_thunk. exact IH.
Qed.

Lemma par_to_sstep : forall (n : nat) (c c' : comp n), par n c c' -> c ↪* c'.
Proof. intros. destruct par_to_sstep_lem as [H1 H2]. apply (H1 n c c' H). Qed.

Lemma parv_to_sstep : forall (n : nat) (v v' : value n), parv n v v' -> v ↪ᵥ* v'.
Proof. intros. destruct par_to_sstep_lem as [H1 H2]. apply (H2 n v v' H). Qed.

(* ===== sstep is included in par ===== *)

Lemma sstep_to_par_lem : forall n,
  (forall (c c' : comp n), c ↪ c' -> par n c c')
  /\ (forall (v v' : value n), v ↪ᵥ v' -> parv n v v').
Proof.
  apply mutind_sstep.
  - intros n v1 v1' v2 s IH. apply parPairCong. apply IH. apply parv_refl.
  - intros n v1 v2 v2' s IH. apply parPairCong. apply parv_refl. apply IH.
  - intros n b v v' s IH. apply parInjCong. apply IH.
  - intros n c c' s IH. apply parThunkCong. apply IH.
  - intros n v v' s IH. apply parForceCong. apply IH.
  - intros n c c' s IH. apply parLambda. apply IH.
  - intros n c c' v s IH. apply parAppCong. apply IH. apply parv_refl.
  - intros n c v v' s IH. apply parAppCong. apply par_refl. apply IH.
  - intros n c1 c1' c2 s IH. apply parTupleCong. apply IH. apply par_refl.
  - intros n c1 c2 c2' s IH. apply parTupleCong. apply par_refl. apply IH.
  - intros n v v' s IH. apply parRetCong. apply IH.
  - intros n c1 c1' c2 s IH. apply parLetinCong. apply IH. apply par_refl.
  - intros n c1 c2 c2' s IH. apply parLetinCong. apply par_refl. apply IH.
  - intros n c c' b s IH. apply parProjCong. apply IH.
  - intros n v v' s IH. apply parCaseZCong. apply IH.
  - intros n v v' c1 c2 s IH. apply parCaseSCong. apply IH. apply par_refl. apply par_refl.
  - intros n v c1 c1' c2 s IH. apply parCaseSCong. apply parv_refl. apply IH. apply par_refl.
  - intros n v c1 c2 c2' s IH. apply parCaseSCong. apply parv_refl. apply par_refl. apply IH.
  - intros n v v' c s IH. apply parCasePCong. apply IH. apply par_refl.
  - intros n v c c' s IH. apply parCasePCong. apply parv_refl. apply IH.
  - intros n c c' p. apply pstep_par. exact p.
Qed.

Lemma sstep_to_par : forall (n : nat) (c c' : comp n), c ↪ c' -> par n c c'.
Proof. intros. destruct (sstep_to_par_lem n) as [H1 H2]. apply (H1 c c' H). Qed.

Lemma sstep_value_to_par : forall (n : nat) (v v' : value n), v ↪ᵥ v' -> parv n v v'.
Proof. intros. destruct (sstep_to_par_lem n) as [H1 H2]. apply (H2 v v' H). Qed.

(* ===== Confluence of sstep and sstep_value ===== *)

Lemma sstep_star_to_par n (c c' : comp n) : c ↪* c' -> star (par n) c c'.
Proof.
  intros H. induction H as [c | c c1 c' Hs Hrest IH].
  - apply starRefl.
  - eapply starStep; [apply sstep_to_par; exact Hs | exact IH].
Qed.

Lemma sstep_value_star_to_par n (v v' : value n) : v ↪ᵥ* v' -> star (parv n) v v'.
Proof.
  intros H. induction H as [v | v v1 v' Hs Hrest IH].
  - apply starRefl.
  - eapply starStep; [apply sstep_value_to_par; exact Hs | exact IH].
Qed.

Lemma par_star_to_sstep n (c c' : comp n) : star (par n) c c' -> c ↪* c'.
Proof.
  intros H. induction H as [c | c c1 c' Hp Hrest IH].
  - apply starRefl.
  - eapply star_trans_gen; [apply par_to_sstep; exact Hp | exact IH].
Qed.

Lemma parv_star_to_sstep n (v v' : value n) : star (parv n) v v' -> v ↪ᵥ* v'.
Proof.
  intros H. induction H as [v | v v1 v' Hp Hrest IH].
  - apply starRefl.
  - eapply star_trans_gen; [apply parv_to_sstep; exact Hp | exact IH].
Qed.

Theorem confluence n:
   confluent (@sstep n) /\ confluent (@sstep_value n).
Proof.
  split.
  - intros x y z Hxy Hxz.
    pose proof (sstep_star_to_par n x y Hxy) as Hy.
    pose proof (sstep_star_to_par n x z Hxz) as Hz.
    destruct (diamond_star (par n) (par_diamond n) x y z Hy Hz) as [w Hwy Hwz].
    exists w.
    + apply par_star_to_sstep. exact Hwy.
    + apply par_star_to_sstep. exact Hwz.
  - intros x y z Hxy Hxz.
    pose proof (sstep_value_star_to_par n x y Hxy) as Hy.
    pose proof (sstep_value_star_to_par n x z Hxz) as Hz.
    destruct (diamond_star (parv n) (parv_diamond n) x y z Hy Hz) as [w Hwy Hwz].
    exists w.
    + apply parv_star_to_sstep. exact Hwy.
    + apply parv_star_to_sstep. exact Hwz.
Qed.
