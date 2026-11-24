From Mctt.Algorithmic.Typing Require Import Definitions.

From Mctt.Core Require Import Base.

From Mctt.Frontend Require Import Elaborator.
From Stdlib Require Import Lia PeanoNat Arith.Wf_nat.

Import Domain_Notations.

(* Context and type formation for declarative derivations. *)
Local Hint Constructors wf_ctx wf_exp wf_sub : mctt_wf.

Local Lemma typing_contexts :
  (forall Γ A M, {{ Γ ⊢ M : A }} -> {{ ⊢ Γ }}) /\
  (forall Γ Δ σ, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}).
Proof.
  assert (H : (forall Γ, {{ ⊢ Γ }} -> {{ ⊢ Γ }}) /\
              (forall Γ A M, {{ Γ ⊢ M : A }} -> {{ ⊢ Γ }}) /\
              (forall Γ Δ σ, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }})).
  {
    apply syntactic_wf_mut_ind'; intros;
      repeat match goal with H : _ /\ _ |- _ => destruct H end;
      try match goal with H : wf_ctx (_ :: _) |- _ => inversion H; subst end;
      eauto with mctt_wf.
  }
  exact (proj2 H).
Qed.

Local Lemma typing_context Γ A M :
  {{ Γ ⊢ M : A }} -> {{ ⊢ Γ }}.
Proof. apply typing_contexts. Qed.

Local Lemma lookup_type Γ x A :
  {{ #x : A ∈ Γ }} -> {{ ⊢ Γ }} -> exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
  induction 1; intros HΓ; inversion HΓ; subst.
  - exists i. eapply wf_exp_subtyp.
    + eapply wf_exp_sub; eauto with mctt_wf.
    + now constructor.
    + eapply wf_subtyp_refl.
      * now constructor.
      * eapply wf_exp_eq_typ_sub. now constructor.
  - destruct (IHctx_lookup ltac:(assumption)) as [j Hj].
    exists j. eapply wf_exp_subtyp.
    + eapply wf_exp_sub; eauto with mctt_wf.
    + now constructor.
    + eapply wf_subtyp_refl.
      * now constructor.
      * eapply wf_exp_eq_typ_sub. now constructor.
Qed.

Local Lemma type_cumulativity Γ A i j :
  {{ Γ ⊢ A : Type@i }} -> i <= j -> {{ Γ ⊢ A : Type@j }}.
Proof.
  intros H Hij. destruct (Nat.eq_dec i j) as [-> | Hne]; [exact H |].
  pose proof (typing_context _ _ _ H).
  eapply wf_exp_subtyp; eauto using wf_typ, wf_subtyp_univ.
  apply wf_subtyp_univ; [assumption | lia].
Qed.

Local Lemma type_substitution Γ Δ σ A i :
  {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ A : Type@i }} -> {{ Γ ⊢ A[σ] : Type@i }}.
Proof.
  intros Hσ HA.
  pose proof (proj1 (proj2 typing_contexts _ _ _ Hσ)) as HΓ.
  eapply wf_exp_subtyp.
  - eapply wf_exp_sub; eassumption.
  - now constructor.
  - eapply wf_subtyp_refl; eauto using wf_typ, wf_exp_eq_typ_sub.
Qed.

Local Lemma convert_term Γ M A B i :
  {{ Γ ⊢ M : A }} ->
  {{ Γ ⊢ B : Type@i }} ->
  {{ Γ ⊢ A ≈ B : Type@i }} ->
  {{ Γ ⊢ M : B }}.
Proof. eauto using wf_exp_subtyp, wf_subtyp_refl. Qed.

Local Lemma typing_identity_extension Γ A M i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  {{ Γ ⊢s Id,,M : Γ, A }}.
Proof.
  intros HA HM. pose proof (typing_context _ _ _ HA).
  eapply wf_sub_extend; eauto using wf_sub_id.
  eapply convert_term.
  - exact HM.
  - eapply type_substitution; eauto using wf_sub_id.
  - apply wf_exp_eq_sym, wf_exp_eq_sub_id. exact HA.
Qed.

Local Lemma subtyping_nf_reflexive A : {{ ⊢anf A ⊆ A }}.
Proof.
  induction A; first [apply asnf_refl; [exact I | reflexivity] |
    apply asnf_univ; lia | now apply asnf_pi | now apply asnf_sigma].
Qed.

Local Lemma subtyping_nf_transitive A B C :
  {{ ⊢anf A ⊆ B }} -> {{ ⊢anf B ⊆ C }} -> {{ ⊢anf A ⊆ C }}.
Proof.
  intros HAB. revert C.
  induction HAB; intros C HBC; subst; try assumption;
    inversion HBC; subst; try contradiction;
    constructor; eauto; lia.
Qed.

(* Evaluation and readback are single-valued. *)
Local Lemma evaluation_fst_deterministic m a b :
  eval_fst m a -> eval_fst m b -> a = b.
Proof. intros H K; inversion H; inversion K; congruence. Qed.

Local Ltac reconcile_evaluation :=
  repeat multimatch goal with
  | IH : forall y, ?R y -> ?x = y, H : ?R ?z |- _ =>
      tryif constr_eq x z then fail
      else let E := fresh in
        pose proof (IH _ H) as E;
        first [is_var z; subst z | is_var x; subst x | progress (injection E; intros; subst)]
  | H : eval_fst ?m ?x, K : eval_fst ?m ?y |- _ =>
      tryif constr_eq x y then fail
      else let E := fresh in
        pose proof (evaluation_fst_deterministic _ _ _ H K) as E;
        first [is_var y; subst y | is_var x; subst x | progress (injection E; intros; subst)]
  end.

Local Lemma evaluation_deterministic :
  (forall M ρ m, eval_exp M ρ m -> forall m', eval_exp M ρ m' -> m = m') /\
  (forall A MZ MS m ρ r, eval_natrec A MZ MS m ρ r ->
     forall r', eval_natrec A MZ MS m ρ r' -> r = r') /\
  (forall m n r, eval_app m n r -> forall r', eval_app m n r' -> r = r') /\
  (forall m r, eval_snd m r -> forall r', eval_snd m r' -> r = r') /\
  (forall a B BR m1 m2 n ρ r, eval_eqrec a B BR m1 m2 n ρ r ->
     forall r', eval_eqrec a B BR m1 m2 n ρ r' -> r = r') /\
  (forall σ ρ ρ', eval_sub σ ρ ρ' ->
     forall ρ'', eval_sub σ ρ ρ'' -> ρ' = ρ'').
Proof.
  apply eval_mut_ind; intros;
    match goal with
    | H : eval_exp _ _ _ |- _ => is_var m'; inversion H; subst
    | H : eval_natrec _ _ _ _ _ _ |- _ => inversion H; subst
    | H : eval_app _ _ _ |- _ => inversion H; subst
    | H : eval_snd _ _ |- _ => inversion H; subst
    | H : eval_eqrec _ _ _ _ _ _ _ _ |- _ => inversion H; subst
    | H : eval_sub _ _ _ |- _ => inversion H; subst
    end;
    reconcile_evaluation; reflexivity.
Qed.

Local Lemma eval_exp_deterministic :
  forall M ρ m, eval_exp M ρ m -> forall m', eval_exp M ρ m' -> m = m'.
Proof. exact (proj1 evaluation_deterministic). Qed.

Local Lemma eval_app_deterministic :
  forall m n r, eval_app m n r -> forall r', eval_app m n r' -> r = r'.
Proof. exact (proj1 (proj2 (proj2 evaluation_deterministic))). Qed.

Local Lemma eval_snd_deterministic :
  forall m r, eval_snd m r -> forall r', eval_snd m r' -> r = r'.
Proof. exact (proj1 (proj2 (proj2 (proj2 evaluation_deterministic)))). Qed.

Local Ltac reconcile_values :=
  repeat first
    [ progress reconcile_evaluation
    | multimatch goal with
      | H : eval_exp ?M ?ρ ?x, K : eval_exp ?M ?ρ ?y |- _ =>
          tryif constr_eq x y then fail
          else let E := fresh in
            pose proof (eval_exp_deterministic _ _ _ H _ K) as E;
            first [is_var y; subst y | is_var x; subst x]
      | H : eval_app ?m ?n ?x, K : eval_app ?m ?n ?y |- _ =>
          tryif constr_eq x y then fail
          else let E := fresh in
            pose proof (eval_app_deterministic _ _ _ H _ K) as E;
            first [is_var y; subst y | is_var x; subst x]
      | H : eval_snd ?m ?x, K : eval_snd ?m ?y |- _ =>
          tryif constr_eq x y then fail
          else let E := fresh in
            pose proof (eval_snd_deterministic _ _ H _ K) as E;
            first [is_var y; subst y | is_var x; subst x]
      end ].

Local Lemma readback_deterministic :
  (forall s m M, read_nf s m M -> forall M', read_nf s m M' -> M = M') /\
  (forall s m M, read_ne s m M -> forall M', read_ne s m M' -> M = M') /\
  (forall s a A, read_typ s a A -> forall A', read_typ s a A' -> A = A').
Proof.
  apply read_mut_ind; intros.
  all:
    match goal with
    | H : read_nf _ _ ?out |- _ = ?out => inversion H; subst
    | H : read_ne _ _ ?out |- _ = ?out => inversion H; subst
    | H : read_typ _ _ ?out |- _ = ?out => inversion H; subst
    end.
  all: reconcile_values.
  all: reflexivity.
Qed.

Local Lemma initial_env_deterministic Γ ρ :
  initial_env Γ ρ -> forall ρ', initial_env Γ ρ' -> ρ = ρ'.
Proof.
  induction 1; intros ρ' Henv; inversion Henv; subst;
    reconcile_values; reflexivity.
Qed.

Local Lemma nbe_ty_deterministic Γ A B C :
  nbe_ty Γ A B -> nbe_ty Γ A C -> B = C.
Proof.
  intros H K. destruct H. inversion K; subst.
  match goal with
  | H : initial_env ?Γ ?ρ, K : initial_env ?Γ ?ρ' |- _ =>
      tryif constr_eq ρ ρ' then fail
      else pose proof (initial_env_deterministic _ _ H _ K); subst ρ'
  end.
  reconcile_values. eapply (proj2 (proj2 readback_deterministic)); eassumption.
Qed.

Local Lemma expression_equality_reflexive Γ M A :
  {{ Γ ⊢ M : A }} -> {{ Γ ⊢ M ≈ M : A }}.
Proof.
  intro H. pose proof (wf_exp_eq_sub_id _ _ _ H) as Hid.
  exact (wf_exp_eq_trans _ _ _ _ _ (wf_exp_eq_sym _ _ _ _ Hid) Hid).
Qed.

Local Lemma substitution_equality_reflexive Γ Δ σ :
  {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢s σ ≈ σ : Δ }}.
Proof.
  induction 1; eauto using wf_sub_eq_id, wf_sub_eq_weaken,
    wf_sub_eq_compose_cong, wf_sub_eq_extend_cong, wf_sub_eq_subtyp,
    expression_equality_reflexive.
Qed.

Local Lemma convert_equality Γ M N A B i :
  {{ Γ ⊢ M ≈ N : A }} ->
  {{ Γ ⊢ B : Type@i }} ->
  {{ Γ ⊢ A ≈ B : Type@i }} ->
  {{ Γ ⊢ M ≈ N : B }}.
Proof. eauto using wf_exp_eq_subtyp, wf_subtyp_refl. Qed.

Local Lemma type_equality_universe_sub Γ Δ σ i M N :
  {{ Γ ⊢s σ : Δ }} ->
  {{ Γ ⊢ M ≈ N : Type@i[σ] }} ->
  {{ Γ ⊢ M ≈ N : Type@i }}.
Proof.
  intros Hσ H.
  pose proof (proj1 (proj2 typing_contexts _ _ _ Hσ)) as HΓ.
  eapply convert_equality; eauto using wf_typ, wf_exp_eq_typ_sub.
Qed.

Local Lemma type_substitution_congruence Γ Δ σ τ A B i :
  {{ Γ ⊢s σ : Δ }} ->
  {{ Γ ⊢s σ ≈ τ : Δ }} ->
  {{ Δ ⊢ A ≈ B : Type@i }} ->
  {{ Γ ⊢ A[σ] ≈ B[τ] : Type@i }}.
Proof.
  intros. eapply type_equality_universe_sub; eauto using wf_exp_eq_sub_cong.
Qed.

Local Lemma type_substitution_composition Γ Δ Θ τ σ A i :
  {{ Γ ⊢s τ : Δ }} ->
  {{ Δ ⊢s σ : Θ }} ->
  {{ Θ ⊢ A : Type@i }} ->
  {{ Γ ⊢ A[σ∘τ] ≈ A[σ][τ] : Type@i }}.
Proof.
  intros. eapply (type_equality_universe_sub Γ Θ {{{ σ∘τ }}});
    eauto using wf_sub_compose, wf_exp_eq_sub_compose.
Qed.

Local Lemma type_weakening_cancel Γ Δ σ A M i B j :
  {{ Γ ⊢s σ : Δ }} ->
  {{ Δ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A[σ] }} ->
  {{ Δ ⊢ B : Type@j }} ->
  {{ Γ ⊢ B[Wk][σ,,M] ≈ B[σ] : Type@j }}.
Proof.
  intros Hσ HA HM HB.
  pose proof (proj2 (proj2 typing_contexts _ _ _ Hσ)) as HΔ.
  assert (Hw : {{ Δ, A ⊢s Wk : Δ }}) by eauto with mctt_wf.
  assert (He : {{ Γ ⊢s σ,,M : Δ, A }}) by eauto using wf_sub_extend.
  eapply wf_exp_eq_trans.
  - apply wf_exp_eq_sym. eapply type_substitution_composition; eassumption.
  - eapply type_substitution_congruence.
    + eapply wf_sub_compose; eassumption.
    + exact (wf_sub_eq_p_extend _ _ _ _ _ _ Hσ HA HM).
    + apply expression_equality_reflexive. exact HB.
Qed.

Local Lemma nat_case_substitution Γ M :
  {{ Γ ⊢ M : ℕ }} -> {{ Γ ⊢s Id,,M : Γ, ℕ }}.
Proof.
  intro HM. apply typing_identity_extension with (i := 0).
  - apply wf_nat. exact (typing_context _ _ _ HM).
  - exact HM.
Qed.

Local Lemma weaken_type Γ A B i j :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ B : Type@j }} ->
  {{ Γ, B ⊢ A[Wk] : Type@i }}.
Proof.
  intros HA HB. pose proof (typing_context _ _ _ HB).
  eapply type_substitution; eauto using wf_sub_weaken, wf_ctx_extend.
Qed.

Local Lemma step_case_substitution Γ A i :
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Γ, ℕ, A ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }}.
Proof.
  intro HA.
  pose proof (typing_context _ _ _ HA) as HΓN.
  assert (HΓ : {{ ⊢ Γ }}) by (inversion HΓN; assumption).
  assert (HΓNA : {{ ⊢ Γ, ℕ, A }}) by eauto using wf_ctx_extend.
  assert (Hw1 : {{ Γ, ℕ ⊢s Wk : Γ }}) by now constructor.
  assert (Hw2 : {{ Γ, ℕ, A ⊢s Wk : Γ, ℕ }}) by now constructor.
  assert (Hw : {{ Γ, ℕ, A ⊢s Wk∘Wk : Γ }}) by eauto using wf_sub_compose.
  assert (Hn : {{ Γ ⊢ ℕ : Type@0 }}) by now constructor.
  eapply (wf_sub_extend _ _ _ 0); try eassumption.
  apply (convert_term _ _ a_nat _ 0).
  - apply wf_succ. apply (convert_term _ _ {{{ ℕ[Wk][Wk] }}} _ 0).
    + apply wf_vlookup; [exact HΓNA | first [apply here | apply there, here]].
    + now constructor.
    + eapply wf_exp_eq_trans.
      * apply wf_exp_eq_sym. eapply type_substitution_composition; eassumption.
      * eapply wf_exp_eq_nat_sub. exact Hw.
  - eapply type_substitution; eassumption.
  - apply wf_exp_eq_sym. eapply wf_exp_eq_nat_sub. exact Hw.
Qed.

Local Lemma eqrec_context Γ A i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A, A[Wk] ⊢ Eq A[Wk∘Wk] #1 #0 : Type@i }}.
Proof.
  intro HA.
  pose proof (typing_context _ _ _ HA) as HΓ.
  assert (HAw : {{ Γ, A ⊢ A[Wk] : Type@i }}) by eauto using weaken_type.
  assert (HΓA : {{ ⊢ Γ, A }}) by eauto using wf_ctx_extend.
  assert (HΓAA : {{ ⊢ Γ, A, A[Wk] }}) by eauto using wf_ctx_extend.
  assert (Hw1 : {{ Γ, A ⊢s Wk : Γ }}) by now constructor.
  assert (Hw2 : {{ Γ, A, A[Wk] ⊢s Wk : Γ, A }}) by now constructor.
  assert (Hw : {{ Γ, A, A[Wk] ⊢s Wk∘Wk : Γ }}) by eauto using wf_sub_compose.
  assert (HAww : {{ Γ, A, A[Wk] ⊢ A[Wk∘Wk] : Type@i }})
    by eauto using type_substitution.
  assert (HE : {{ Γ, A, A[Wk] ⊢ A[Wk][Wk] ≈ A[Wk∘Wk] : Type@i }})
    by (apply wf_exp_eq_sym; eapply type_substitution_composition; eassumption).
  apply wf_eq with (i := i); [exact HAww | | ];
    apply (convert_term _ _ {{{ A[Wk][Wk] }}} _ i);
    try assumption;
    (apply wf_vlookup; [exact HΓAA | first [apply here | apply there, here]]).
Qed.

Local Lemma eqrec_case_substitution Γ A M N P i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  {{ Γ ⊢ N : A }} ->
  {{ Γ ⊢ P : Eq A M N }} ->
  {{ Γ ⊢s Id,,M,,N,,P : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
Proof.
  intros HA HM HN HP.
  pose proof (typing_context _ _ _ HA) as HΓ.
  assert (HΓA : {{ ⊢ Γ, A }}) by eauto using wf_ctx_extend.
  assert (HAw : {{ Γ, A ⊢ A[Wk] : Type@i }}) by eauto using weaken_type.
  assert (HΓAA : {{ ⊢ Γ, A, A[Wk] }}) by eauto using wf_ctx_extend.
  assert (Hid : {{ Γ ⊢s Id : Γ }}) by now constructor.
  assert (HM' : {{ Γ ⊢ M : A[Id] }}) by
    (eapply convert_term; [exact HM | eapply type_substitution; eassumption |
      apply wf_exp_eq_sym, wf_exp_eq_sub_id; exact HA]).
  assert (Hσ : {{ Γ ⊢s Id,,M : Γ, A }}) by eauto using wf_sub_extend.
  assert (HE1 : {{ Γ ⊢ A[Wk][Id,,M] ≈ A : Type@i }}).
  {
    eapply wf_exp_eq_trans.
    - exact (type_weakening_cancel _ _ _ _ _ _ _ _ Hid HA HM' HA).
    - apply wf_exp_eq_sub_id. exact HA.
  }
  assert (Hs1 : {{ Γ ⊢ A[Wk][Id,,M] : Type@i }})
    by (eapply type_substitution; eassumption).
  assert (HN' : {{ Γ ⊢ N : A[Wk][Id,,M] }})
    by eauto using convert_term, wf_exp_eq_sym.
  assert (Hτ : {{ Γ ⊢s Id,,M,,N : Γ, A, A[Wk] }}) by eauto using wf_sub_extend.
  assert (Hw1 : {{ Γ, A ⊢s Wk : Γ }}) by now constructor.
  assert (Hw2 : {{ Γ, A, A[Wk] ⊢s Wk : Γ, A }}) by now constructor.
  assert (Hw : {{ Γ, A, A[Wk] ⊢s Wk∘Wk : Γ }}) by eauto using wf_sub_compose.
  assert (HAww : {{ Γ, A, A[Wk] ⊢ A[Wk∘Wk] : Type@i }})
    by eauto using type_substitution.
  assert (HEw : {{ Γ, A, A[Wk] ⊢ A[Wk∘Wk] ≈ A[Wk][Wk] : Type@i }})
    by (eapply type_substitution_composition; eassumption).
  assert (HE2 : {{ Γ ⊢ A[Wk∘Wk][Id,,M,,N] ≈ A : Type@i }}).
  {
    eapply wf_exp_eq_trans.
    - eapply type_substitution_congruence;
        eauto using substitution_equality_reflexive.
    - eapply wf_exp_eq_trans; [ | exact HE1 ].
      exact (type_weakening_cancel _ _ _ _ _ _ _ _ Hσ HAw HN' HAw).
  }
  assert (Hs2 : {{ Γ ⊢ A[Wk∘Wk][Id,,M,,N] : Type@i }})
    by eauto using type_substitution.
  assert (H1 : {{ Γ, A, A[Wk] ⊢ #1 : A[Wk∘Wk] }}).
  {
    apply (convert_term _ _ {{{ A[Wk][Wk] }}} _ i); try assumption.
    - (apply wf_vlookup; [exact HΓAA | first [apply here | apply there, here]]).
    - apply wf_exp_eq_sym. exact HEw.
  }
  assert (H0 : {{ Γ, A, A[Wk] ⊢ #0 : A[Wk∘Wk] }}).
  {
    apply (convert_term _ _ {{{ A[Wk][Wk] }}} _ i); try assumption.
    - (apply wf_vlookup; [exact HΓAA | first [apply here | apply there, here]]).
    - apply wf_exp_eq_sym. exact HEw.
  }
  assert (HM1 : {{ Γ ⊢ #1[Id,,M,,N] ≈ M : A }}).
  {
    eapply wf_exp_eq_trans.
    - eapply convert_equality; [ | exact HA | exact HE1 ].
      eapply wf_exp_eq_var_S_sub; try eassumption. constructor.
    - eapply convert_equality; [ | exact HA | apply wf_exp_eq_sub_id; exact HA ].
      exact (wf_exp_eq_var_0_sub _ _ _ _ _ _ Hid HA HM').
  }
  assert (HN0 : {{ Γ ⊢ #0[Id,,M,,N] ≈ N : A }}).
  {
    eapply convert_equality; [ | exact HA | exact HE1 ].
    exact (wf_exp_eq_var_0_sub _ _ _ _ _ _ Hσ HAw HN').
  }
  pose proof (eqrec_context _ _ _ HA) as HEq.
  apply (wf_sub_extend _ _ _ i); try assumption.
  eapply convert_term.
  - exact HP.
  - eapply type_substitution; eassumption.
  - apply wf_exp_eq_sym.
    eapply wf_exp_eq_trans.
    + eapply wf_exp_eq_eq_sub; eassumption.
    + apply wf_exp_eq_eq_cong.
      * exact HE2.
      * eapply convert_equality; [exact HM1 | exact Hs2 | now apply wf_exp_eq_sym].
      * eapply convert_equality; [exact HN0 | exact Hs2 | now apply wf_exp_eq_sym].
Qed.

Local Lemma type_of_typing Γ A M :
  {{ Γ ⊢ M : A }} -> exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
  induction 1.
  - eexists. now apply wf_typ.
  - eexists. now apply wf_typ.
  - exists 0. now apply wf_nat.
  - exact IHwf_exp.
  - exists i. eapply type_substitution; [now apply nat_case_substitution | eassumption].
  - exists (S i). apply wf_typ. eauto using typing_context.
  - destruct IHwf_exp2 as [j HB].
    exists (Nat.max i j). apply wf_pi; [ | ]; eapply type_cumulativity; try eassumption; lia.
  - exists i. eapply type_substitution; [eapply typing_identity_extension | ]; eassumption.
  - exists (S i). apply wf_typ. eauto using typing_context.
  - exists i. now apply wf_sigma.
  - now exists i.
  - exists i. eapply type_substitution;
    [eapply typing_identity_extension; [eassumption | eapply wf_fst; eassumption] | eassumption].
  - eapply lookup_type; eassumption.
  - exists (S i). apply wf_typ. eauto using typing_context.
  - exists i. now apply wf_eq.
  - exists j. eapply type_substitution; [eapply eqrec_case_substitution | ]; eassumption.
  - destruct IHwf_exp as [i HA]. exists i. eapply type_substitution; eassumption.
  - now exists i.
Qed.

Local Lemma subtype_from_typed_reflexivity Γ A i :
  {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ A ⊆ A }}.
Proof. eauto using expression_equality_reflexive, wf_subtyp_refl. Qed.

(* Substitution and narrowing for dependent binders. *)
Local Lemma lifted_substitution Γ Δ σ A i :
  {{ Γ ⊢s σ : Δ }} ->
  {{ Δ ⊢ A : Type@i }} ->
  {{ Γ, A[σ] ⊢s q σ : Δ, A }}.
Proof.
  intros Hσ HA.
  pose proof (proj1 (proj2 typing_contexts _ _ _ Hσ)) as HΓ.
  assert (HAs : {{ Γ ⊢ A[σ] : Type@i }}) by eauto using type_substitution.
  assert (HΓA : {{ ⊢ Γ, A[σ] }}) by eauto using wf_ctx_extend.
  assert (Hw : {{ Γ, A[σ] ⊢s Wk : Γ }}) by now constructor.
  assert (Hτ : {{ Γ, A[σ] ⊢s σ∘Wk : Δ }}) by eauto using wf_sub_compose.
  change {{ Γ, A[σ] ⊢s (σ∘Wk),,#0 : Δ, A }}. eapply wf_sub_extend; [exact Hτ | exact HA |].
  apply (convert_term _ _ {{{ A[σ][Wk] }}} _ i).
  - apply wf_vlookup; [exact HΓA | apply here].
  - eauto using type_substitution.
  - apply wf_exp_eq_sym. eauto using type_substitution_composition.
Qed.

Local Lemma subtyping_under_substitution Γ A B :
  {{ Γ ⊢ A ⊆ B }} ->
  forall Δ σ, {{ Δ ⊢s σ : Γ }} -> {{ Δ ⊢ A[σ] ⊆ B[σ] }}.
Proof.
  induction 1; intros Θ σ Hσ.
  - apply wf_subtyp_refl with (i := i).
    + eauto using type_substitution.
    + eapply type_substitution_congruence;
        eauto using substitution_equality_reflexive.
  - eauto using wf_subtyp_trans.
  - pose proof (proj1 (proj2 typing_contexts _ _ _ Hσ)) as HΘ.
    eapply wf_subtyp_trans with (M' := a_typ i).
    + eauto using wf_subtyp_refl, wf_exp_eq_typ_sub, wf_typ.
    + eapply wf_subtyp_trans with (M' := a_typ j).
      * now apply wf_subtyp_univ.
      * apply wf_subtyp_refl with (i := S j).
        -- eauto using wf_typ, type_substitution.
        -- eapply wf_exp_eq_sym, wf_exp_eq_typ_sub; exact Hσ.
  - assert (HA : {{ Θ ⊢ A[σ] : Type@i }}) by eauto using type_substitution.
    assert (HA' : {{ Θ ⊢ A'[σ] : Type@i }}) by eauto using type_substitution.
    assert (Hq : {{ Θ, A[σ] ⊢s q σ : Γ, A }}) by eauto using lifted_substitution.
    assert (Hq' : {{ Θ, A'[σ] ⊢s q σ : Γ, A' }}) by eauto using lifted_substitution.
    assert (HB : {{ Θ, A[σ] ⊢ B[q σ] : Type@i }}) by eauto using type_substitution.
    assert (HB' : {{ Θ, A'[σ] ⊢ B'[q σ] : Type@i }}) by eauto using type_substitution.
    eapply wf_subtyp_trans with (M' := {{{ Π A[σ] B[q σ] }}}).
    + eauto using wf_subtyp_refl, wf_pi, wf_exp_eq_pi_sub.
    + eapply wf_subtyp_trans with (M' := {{{ Π A'[σ] B'[q σ] }}}).
      * eapply wf_subtyp_pi; try eassumption.
        -- eapply type_substitution_congruence;
             eauto using substitution_equality_reflexive.
        -- now apply IHwf_subtyp.
      * eauto 7 using wf_subtyp_refl, wf_pi, wf_exp_eq_pi_sub,
          wf_exp_eq_sym, type_substitution.
  - assert (HA : {{ Θ ⊢ A[σ] : Type@i }}) by eauto using type_substitution.
    assert (HA' : {{ Θ ⊢ A'[σ] : Type@i }}) by eauto using type_substitution.
    assert (Hq : {{ Θ, A[σ] ⊢s q σ : Γ, A }}) by eauto using lifted_substitution.
    assert (Hq' : {{ Θ, A'[σ] ⊢s q σ : Γ, A' }}) by eauto using lifted_substitution.
    assert (HB : {{ Θ, A[σ] ⊢ B[q σ] : Type@i }}) by eauto using type_substitution.
    assert (HB' : {{ Θ, A'[σ] ⊢ B'[q σ] : Type@i }}) by eauto using type_substitution.
    eapply wf_subtyp_trans with (M' := {{{ Σ A[σ] B[q σ] }}}).
    + eauto using wf_subtyp_refl, wf_sigma, wf_exp_eq_sigma_sub.
    + eapply wf_subtyp_trans with (M' := {{{ Σ A'[σ] B'[q σ] }}}).
      * eapply wf_subtyp_sigma; try eassumption.
        -- eapply type_substitution_congruence;
             eauto using substitution_equality_reflexive.
        -- now apply IHwf_subtyp.
      * eauto 7 using wf_subtyp_refl, wf_sigma, wf_exp_eq_sigma_sub,
          wf_exp_eq_sym, type_substitution.
Qed.

Local Lemma context_subtyping_reflexive Γ :
  {{ ⊢ Γ }} -> {{ ⊢ Γ ⊆ Γ }}.
Proof.
  induction 1; eauto using wf_ctx_sub_empty, wf_ctx_sub_extend,
    subtype_from_typed_reflexivity.
Qed.

Local Lemma subtyping_right_type Γ A B :
  {{ Γ ⊢ A ⊆ B }} -> exists i, {{ Γ ⊢ B : Type@i }}.
Proof. induction 1; eauto using wf_typ, wf_pi, wf_sigma. Qed.

Local Lemma cumulatively_extend_context Γ Δ A i :
  {{ ⊢ Γ ⊆ Δ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Δ ⊢ A : Type@i }} ->
  {{ ⊢ Γ, A ⊆ Δ, A }}.
Proof. eauto using wf_ctx_sub_extend, subtype_from_typed_reflexivity. Qed.

Local Lemma narrowed_lookup Γ Δ x A :
  {{ ⊢ Γ }} ->
  {{ ⊢ Γ ⊆ Δ }} ->
  {{ #x : A ∈ Δ }} ->
  exists B, {{ #x : B ∈ Γ }} /\ {{ Γ ⊢ B ⊆ A }}.
Proof.
  intros HΓ Hsub Hx. revert Γ HΓ Hsub.
  induction Hx; intros Θ HΘ Hsub; inversion Hsub; subst.
  - eexists. split; [apply here |].
    eapply subtyping_under_substitution; [eassumption | now apply wf_sub_weaken].
  - assert (Htail : wf_ctx Γ0) by (inversion HΘ; assumption).
    destruct (IHHx _ Htail ltac:(eassumption)) as [C [HC HCA]].
    eexists. split; [eapply there; exact HC |].
    eapply subtyping_under_substitution; [exact HCA | now apply wf_sub_weaken].
Qed.

Local Lemma narrowed_variable Γ Δ A x :
  {{ ⊢ Γ }} ->
  {{ ⊢ Γ ⊆ Δ }} ->
  {{ #x : A ∈ Δ }} ->
  {{ Γ ⊢ #x : A }}.
Proof.
  intros HΓ Hsub Hx.
  destruct (narrowed_lookup _ _ _ _ HΓ Hsub Hx) as [B [HB HBA]].
  destruct (subtyping_right_type _ _ _ HBA) as [i HA].
  eauto using wf_exp_subtyp, wf_vlookup.
Qed.

Local Lemma narrowed_variable_weaken Γ Δ A B B' x :
  {{ ⊢ Γ, B' }} ->
  {{ ⊢ Γ, B' ⊆ Δ, B }} ->
  {{ #x : A ∈ Δ }} ->
  {{ Γ, B' ⊢ #x[Wk] ≈ #(S x) : A[Wk] }}.
Proof.
  intros HΓB Hsub Hx.
  assert (HΓ : {{ ⊢ Γ }}) by (inversion HΓB; assumption).
  assert (HΓΔ : {{ ⊢ Γ ⊆ Δ }}) by (inversion Hsub; assumption).
  destruct (narrowed_lookup _ _ _ _ HΓ HΓΔ Hx) as [C [HC HCA]].
  assert (Hw : {{ Γ, B' ⊢s Wk : Γ }}) by now constructor.
  pose proof (subtyping_under_substitution _ _ _ HCA _ _ Hw) as HCAw.
  destruct (subtyping_right_type _ _ _ HCAw) as [i HA].
  eauto using wf_exp_eq_subtyp, wf_exp_eq_var_weaken.
Qed.

Local Lemma narrowed_weakening Γ Δ A :
  {{ ⊢ Γ }} -> {{ ⊢ Δ, A }} -> {{ ⊢ Γ ⊆ Δ, A }} -> {{ Γ ⊢s Wk : Δ }}.
Proof.
  intros HΓ HΔ Hsub. inversion Hsub; inversion HΔ; subst.
  eauto using wf_sub_weaken, wf_sub_subtyp.
Qed.

Local Hint Resolve wf_ctx_extend cumulatively_extend_context wf_nat weaken_type
  eqrec_context typing_context : mctt_narrow.

Local Ltac constructor_data proof source target :=
  lazymatch proof with
  | ?head ?arg =>
      let partial := constructor_data head source target in
      let ty := type of arg in
      let sort := type of ty in
      lazymatch sort with
      | Prop => partial
      | _ =>
          lazymatch arg with
          | source => constr:(partial target)
          | _ => constr:(partial arg)
          end
      end
  | _ => proof
  end.

Local Lemma narrowing :
  (forall Γ A M, {{ Γ ⊢ M : A }} ->
     forall Δ, {{ ⊢ Δ }} -> {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ M : A }}) /\
  (forall Γ A M N, {{ Γ ⊢ M ≈ N : A }} ->
     forall Δ, {{ ⊢ Δ }} -> {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ M ≈ N : A }}) /\
  (forall Γ Ξ σ, {{ Γ ⊢s σ : Ξ }} ->
     forall Δ, {{ ⊢ Δ }} -> {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢s σ : Ξ }}) /\
  (forall Γ Ξ σ τ, {{ Γ ⊢s σ ≈ τ : Ξ }} ->
     forall Δ, {{ ⊢ Δ }} -> {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢s σ ≈ τ : Ξ }}) /\
  (forall Γ A B, {{ Γ ⊢ A ⊆ B }} ->
     forall Δ, {{ ⊢ Δ }} -> {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ A ⊆ B }}).
Proof.
  assert (H :
    (forall Γ, {{ ⊢ Γ }} -> True) /\
    (forall Γ Δ, {{ ⊢ Γ ⊆ Δ }} -> True) /\
    (forall Γ A M, {{ Γ ⊢ M : A }} ->
       forall Δ, {{ ⊢ Δ }} -> {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ M : A }}) /\
    (forall Γ A M N, {{ Γ ⊢ M ≈ N : A }} ->
       forall Δ, {{ ⊢ Δ }} -> {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ M ≈ N : A }}) /\
    (forall Γ Ξ σ, {{ Γ ⊢s σ : Ξ }} ->
       forall Δ, {{ ⊢ Δ }} -> {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢s σ : Ξ }}) /\
    (forall Γ Ξ σ τ, {{ Γ ⊢s σ ≈ τ : Ξ }} ->
       forall Δ, {{ ⊢ Δ }} -> {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢s σ ≈ τ : Ξ }}) /\
    (forall Γ A B, {{ Γ ⊢ A ⊆ B }} ->
       forall Δ, {{ ⊢ Δ }} -> {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ A ⊆ B }})).
  {
    eapply (syntactic_wf_mut_ind
      (fun _ _ => True)
      (fun _ _ _ => True)
      (fun Γ A M original => let old := original in
        forall Δ, {{ ⊢ Δ }} -> {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ M : A }})
      (fun Γ A M N original => let old := original in
        forall Δ, {{ ⊢ Δ }} -> {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ M ≈ N : A }})
      (fun Γ Ξ σ original => let old := original in
        forall Δ, {{ ⊢ Δ }} -> {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢s σ : Ξ }})
      (fun Γ Ξ σ τ original => let old := original in
        forall Δ, {{ ⊢ Δ }} -> {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢s σ ≈ τ : Ξ }})
      (fun Γ A B original => let old := original in
        forall Δ, {{ ⊢ Δ }} -> {{ ⊢ Δ ⊆ Γ }} -> {{ Δ ⊢ A ⊆ B }}));
      intros; try exact I.
    all: try solve [eauto 7 using narrowed_variable, narrowed_variable_weaken,
      expression_equality_reflexive, wf_sub_id, wf_sub_subtyp, narrowed_weakening,
      substitution_equality_reflexive].
    all: try solve [
      match goal with
      | old := wf_exp_eq_var_weaken _ _ _ _ _ _,
        H : wf_ctx_sub ?Δ _ |- _ =>
          destruct Δ; [inversion H | eauto using narrowed_variable_weaken]
      end].
    all: lazymatch goal with
    | Hsub : wf_ctx_sub ?target ?source, old := ?proof |- _ =>
        let ctor := constructor_data proof source target in
        apply ctor
    end.
    all: try match goal with
    | HA : wf_exp (a_nat :: ?Γ) (a_typ ?i) ?A,
      Hsub : wf_ctx_sub ?Δ ?Γ, HΔ : wf_ctx ?Δ |- _ =>
        let HΓ := fresh in
        assert (HΓ : wf_ctx Γ) by (pose proof (typing_context _ _ _ HA) as Hext; inversion Hext; assumption);
        let HNat := fresh in
        assert (HNat : wf_ctx_sub (a_nat :: Δ) (a_nat :: Γ))
          by eauto using cumulatively_extend_context, wf_nat;
        let HN := fresh in
        assert (HN : wf_ctx (a_nat :: Δ)) by eauto with mctt_narrow;
        let HAm := fresh in
        assert (HAm : wf_exp (a_nat :: Δ) (a_typ i) A) by eauto
    end.
    all: try solve [eauto 9 with mctt_narrow].
    all: match goal with
    | HA : wf_exp ?Γ (a_typ ?i) ?A,
      Hsub : wf_ctx_sub ?Δ ?Γ, HΔ : wf_ctx ?Δ |- _ =>
        let HA' := fresh in
        assert (HA' : wf_exp Δ (a_typ i) A) by eauto;
        pose proof (weaken_type _ _ _ _ _ HA HA);
        pose proof (weaken_type _ _ _ _ _ HA' HA');
        pose proof (eqrec_context _ _ _ HA);
        pose proof (eqrec_context _ _ _ HA')
    end.
    all: eauto 12 with mctt_narrow.
  }
  tauto.
Qed.

(* Soundness of normal-form comparison and the reduction of typing
   soundness to type-preserving readback. *)
Local Lemma type_former_components Γ T M :
  {{ Γ ⊢ M : T }} ->
  match M with
  | a_pi A B | a_sigma A B =>
      exists i, {{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@i }}
  | _ => True
  end.
Proof. induction 1; simpl; eauto. Qed.

Local Lemma normal_subtyping_sound Γ A B i j :
  {{ ⊢anf A ⊆ B }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ B : Type@j }} ->
  {{ Γ ⊢ A ⊆ B }}.
Proof.
  intros H. revert Γ i j.
  induction H; intros Γ k l HA HB; subst.
  - eauto using subtype_from_typed_reflexivity.
  - destruct (Nat.eq_dec i j) as [-> | Hne].
    + eauto using subtype_from_typed_reflexivity.
    + apply wf_subtyp_univ; [eauto using typing_context | lia].
  - destruct (type_former_components _ _ _ HA) as [i [HD HC]].
    destruct (type_former_components _ _ _ HB) as [j [HD' HC']].
    assert (Hnew : {{ Γ ⊢ A' : Type@(Nat.max i j) }})
      by eauto using type_cumulativity, Nat.le_max_l.
    apply wf_subtyp_pi with (i := Nat.max i j);
      eauto using expression_equality_reflexive, type_cumulativity,
        Nat.le_max_l, Nat.le_max_r.
  - destruct (type_former_components _ _ _ HA) as [i [HD HC]].
    destruct (type_former_components _ _ _ HB) as [j [HD' HC']].
    assert (Hnew : {{ Γ ⊢ A' : Type@(Nat.max i j) }})
      by eauto using type_cumulativity, Nat.le_max_l.
    apply wf_subtyp_sigma with (i := Nat.max i j);
      eauto using expression_equality_reflexive, type_cumulativity,
        Nat.le_max_l, Nat.le_max_r.
Qed.

Local Lemma type_readback_is_universe_readback Γ A B i :
  nbe_ty Γ A B -> nbe Γ A (a_typ i) B.
Proof.
  destruct 1; eauto using nbe_run, eval_exp_typ, read_nf_type.
Qed.

Local Definition readback_preserves_typing :=
  forall Γ A M N,
    {{ Γ ⊢ M : A }} ->
    nbe Γ M A N ->
    {{ Γ ⊢ N : A }} /\ {{ Γ ⊢ M ≈ N : A }}.

Local Lemma type_readback_preserves_typing :
  readback_preserves_typing ->
  forall Γ A B i,
    {{ Γ ⊢ A : Type@i }} ->
    nbe_ty Γ A B ->
    {{ Γ ⊢ B : Type@i }} /\ {{ Γ ⊢ A ≈ B : Type@i }}.
Proof. intros H Γ A B i HA Hn; eauto using type_readback_is_universe_readback. Qed.

Local Lemma algorithm_subtyping_sound_from_readback :
  readback_preserves_typing ->
  forall Γ A B i j,
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ B : Type@j }} ->
    {{ Γ ⊢a A ⊆ B }} ->
    {{ Γ ⊢ A ⊆ B }}.
Proof.
  intros H Γ A B i j HA HB Hsub. destruct Hsub.
  destruct (type_readback_preserves_typing H _ _ _ _ HA H0) as [HA' HEA].
  destruct (type_readback_preserves_typing H _ _ _ _ HB H1) as [HB' HEB].
  eapply wf_subtyp_trans.
  - exact (wf_subtyp_refl _ _ _ _ HA' HEA).
  - eapply wf_subtyp_trans.
    + exact (normal_subtyping_sound _ _ _ _ _ H2 HA' HB').
    + eapply wf_subtyp_refl; [exact HB | now apply wf_exp_eq_sym].
Qed.

Local Lemma eqrec_refl_substitution Γ A i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢s Id,,#0,,refl A[Wk] #0 : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
Proof.
  intro HA.
  pose proof (typing_context _ _ _ HA) as HΓ.
  assert (HΓA : {{ ⊢ Γ, A }}) by eauto using wf_ctx_extend.
  assert (HAw : {{ Γ, A ⊢ A[Wk] : Type@i }}) by eauto using weaken_type.
  assert (HΓAA : {{ ⊢ Γ, A, A[Wk] }}) by eauto using wf_ctx_extend.
  assert (Hv : {{ Γ, A ⊢ #0 : A[Wk] }}) by (apply wf_vlookup; [assumption | apply here]).
  assert (Hid : {{ Γ, A ⊢s Id : Γ, A }}) by now constructor.
  assert (Hv' : {{ Γ, A ⊢ #0 : A[Wk][Id] }}) by
    (eapply convert_term; [exact Hv | eapply type_substitution; eassumption |
      apply wf_exp_eq_sym, wf_exp_eq_sub_id; exact HAw]).
  assert (Hσ : {{ Γ, A ⊢s Id,,#0 : Γ, A, A[Wk] }}) by eauto using wf_sub_extend.
  assert (Hw1 : {{ Γ, A ⊢s Wk : Γ }}) by now constructor.
  assert (Hw2 : {{ Γ, A, A[Wk] ⊢s Wk : Γ, A }}) by now constructor.
  assert (Hw : {{ Γ, A, A[Wk] ⊢s Wk∘Wk : Γ }}) by eauto using wf_sub_compose.
  assert (HAww : {{ Γ, A, A[Wk] ⊢ A[Wk∘Wk] : Type@i }})
    by eauto using type_substitution.
  assert (HEw : {{ Γ, A, A[Wk] ⊢ A[Wk∘Wk] ≈ A[Wk][Wk] : Type@i }})
    by (eapply type_substitution_composition; eassumption).
  assert (HE : {{ Γ, A ⊢ A[Wk∘Wk][Id,,#0] ≈ A[Wk] : Type@i }}).
  {
    eapply wf_exp_eq_trans.
    - eapply type_substitution_congruence;
        eauto using substitution_equality_reflexive.
    - eapply wf_exp_eq_trans.
      + exact (type_weakening_cancel _ _ _ _ _ _ _ _ Hid HAw Hv' HAw).
      + apply wf_exp_eq_sub_id. exact HAw.
  }
  assert (Hs : {{ Γ, A ⊢ A[Wk∘Wk][Id,,#0] : Type@i }})
    by eauto using type_substitution.
  assert (H1 : {{ Γ, A, A[Wk] ⊢ #1 : A[Wk∘Wk] }}).
  {
    apply (convert_term _ _ {{{ A[Wk][Wk] }}} _ i); try assumption.
    - apply wf_vlookup; [exact HΓAA | apply there, here].
    - apply wf_exp_eq_sym. exact HEw.
  }
  assert (H0 : {{ Γ, A, A[Wk] ⊢ #0 : A[Wk∘Wk] }}).
  {
    apply (convert_term _ _ {{{ A[Wk][Wk] }}} _ i); try assumption.
    - apply wf_vlookup; [exact HΓAA | apply here].
    - apply wf_exp_eq_sym. exact HEw.
  }
  assert (He1 : {{ Γ, A ⊢ #1[Id,,#0] ≈ #0 : A[Wk] }}).
  {
    eapply wf_exp_eq_trans with (M' := {{{ #0[Id] }}}).
    - eapply convert_equality; [ | exact HAw | apply wf_exp_eq_sub_id; exact HAw ].
      exact (wf_exp_eq_var_S_sub _ _ _ _ _ _ _ _ Hid HAw Hv' (here A Γ)).
    - apply wf_exp_eq_sub_id. exact Hv.
  }
  assert (He0 : {{ Γ, A ⊢ #0[Id,,#0] ≈ #0 : A[Wk] }}).
  {
    eapply convert_equality; [ | exact HAw | apply wf_exp_eq_sub_id; exact HAw ].
    exact (wf_exp_eq_var_0_sub _ _ _ _ _ _ Hid HAw Hv').
  }
  pose proof (eqrec_context _ _ _ HA) as HEq.
  apply (wf_sub_extend _ _ _ i); try assumption.
  eapply convert_term.
  - eapply wf_refl; eassumption.
  - eapply type_substitution; eassumption.
  - apply wf_exp_eq_sym.
    eapply wf_exp_eq_trans.
    + eapply wf_exp_eq_eq_sub; eassumption.
    + apply wf_exp_eq_eq_cong.
      * exact HE.
      * eapply convert_equality; [exact He1 | exact Hs | now apply wf_exp_eq_sym].
      * eapply convert_equality; [exact He0 | exact Hs | now apply wf_exp_eq_sym].
Qed.

Local Lemma equality_cumulativity Γ A B i j :
  {{ Γ ⊢ A ≈ B : Type@i }} ->
  {{ ⊢ Γ }} ->
  i <= j ->
  {{ Γ ⊢ A ≈ B : Type@j }}.
Proof.
  intros H HΓ Hij. destruct (Nat.eq_dec i j) as [-> | Hne]; [exact H |].
  eapply wf_exp_eq_subtyp.
  - exact H.
  - now apply wf_typ.
  - apply wf_subtyp_univ; [assumption | lia].
Qed.

Local Lemma change_binder Γ A B C M i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ B : Type@i }} ->
  {{ Γ ⊢ A ≈ B : Type@i }} ->
  {{ Γ, A ⊢ M : C }} ->
  {{ Γ, B ⊢ M : C }}.
Proof.
  intros HA HB HE HM.
  pose proof (typing_context _ _ _ HA).
  apply (proj1 narrowing _ _ _ HM);
    eauto using wf_ctx_extend, wf_ctx_sub_extend, wf_subtyp_refl,
      wf_exp_eq_sym, context_subtyping_reflexive.
Qed.

Local Lemma term_at_normalized_type :
  readback_preserves_typing ->
  forall Γ M A B, {{ Γ ⊢ M : A }} -> nbe_ty Γ A B -> {{ Γ ⊢ M : B }}.
Proof.
  intros H Γ M A B HM Hn.
  destruct (type_of_typing _ _ _ HM) as [i HA].
  destruct (type_readback_preserves_typing H _ _ _ _ HA Hn) as [HB HE].
  eauto using convert_term.
Qed.

Local Lemma algorithm_sound_from_readback :
  readback_preserves_typing ->
  (forall Γ A M, {{ Γ ⊢a M ⟸ A }} -> {{ ⊢ Γ }} ->
     (exists i, {{ Γ ⊢ A : Type@i }}) -> {{ Γ ⊢ M : A }}) /\
  (forall Γ A M, {{ Γ ⊢a M ⟹ A }} -> {{ ⊢ Γ }} -> {{ Γ ⊢ M : A }}).
Proof.
  intro Hread. apply alg_type_mut_ind.
  - intros Γ A M B _ IH Hsub HΓ [j HB].
    pose proof (IH HΓ) as HM.
    destruct (type_of_typing _ _ _ HM) as [i HA].
    eapply wf_exp_subtyp; [exact HM | exact HB |].
    eapply algorithm_subtyping_sound_from_readback; eassumption.
  - intros. now apply wf_typ.
  - intros. now apply wf_nat.
  - intros. now apply wf_zero.
  - intros Γ M _ IH HΓ. apply wf_succ, IH; eauto using wf_nat.
  - intros Γ i A MZ MS M B _ IHA _ IHmz _ IHms _ IHm Hn HΓ.
    assert (HΓN : {{ ⊢ Γ, ℕ }}) by eauto using wf_ctx_extend, wf_nat.
    assert (HA : {{ Γ, ℕ ⊢ A : Type@i }}) by now apply IHA.
    assert (HΓNA : {{ ⊢ Γ, ℕ, A }}) by eauto using wf_ctx_extend.
    assert (Hz : {{ Γ ⊢ zero : ℕ }}) by now apply wf_zero.
    eapply term_at_normalized_type; [exact Hread | | exact Hn].
    eapply wf_natrec; [exact HA | apply IHmz | apply IHms | apply IHm];
      eauto using wf_nat, type_substitution, nat_case_substitution,
        step_case_substitution.
  - intros Γ i A j B _ IHA _ IHB HΓ.
    pose proof (IHA HΓ) as HA.
    assert (HΓA : {{ ⊢ Γ, A }}) by eauto using wf_ctx_extend.
    eapply wf_pi; eapply type_cumulativity;
      eauto using Nat.le_max_l, Nat.le_max_r.
  - intros Γ i A B M C _ IHA _ IHM Hn HΓ.
    pose proof (IHA HΓ) as HA.
    assert (HΓA : {{ ⊢ Γ, A }}) by eauto using wf_ctx_extend.
    pose proof (IHM HΓA) as HM.
    destruct (type_of_typing _ _ _ HM) as [j HB].
    destruct (type_readback_preserves_typing Hread _ _ _ _ HA Hn) as [HC HE].
    apply (convert_term _ _ {{{ Π A B }}} _ (Nat.max i j)).
    + eapply wf_fn; eassumption.
    + eapply wf_pi.
      * eauto using type_cumulativity, Nat.le_max_l.
      * eapply type_cumulativity; [ | apply Nat.le_max_r].
        exact (change_binder _ _ _ _ _ _ HA HC HE HB).
    + eapply wf_exp_eq_pi_cong;
        eauto using type_cumulativity, equality_cumulativity,
          expression_equality_reflexive, Nat.le_max_l, Nat.le_max_r.
  - intros Γ A B M N C _ IHM _ IHN Hn HΓ.
    pose proof (IHM HΓ) as HM.
    destruct (type_of_typing _ _ _ HM) as [i Hpi].
    destruct (type_former_components _ _ _ Hpi) as [j [HA HB]].
    eapply term_at_normalized_type; [exact Hread | | exact Hn].
    eapply wf_app; [exact HA | exact HB | exact HM |].
    apply IHN; eauto.
  - intros Γ i A j B _ IHA _ IHB HΓ.
    pose proof (IHA HΓ) as HA.
    assert (HΓA : {{ ⊢ Γ, A }}) by eauto using wf_ctx_extend.
    eapply wf_sigma; eapply type_cumulativity;
      eauto using Nat.le_max_l, Nat.le_max_r.
  - intros Γ i A j B M N A' C _ IHA _ IHB _ IHM _ IHN HnA HnB HΓ.
    pose proof (IHA HΓ) as HA.
    assert (HΓA : {{ ⊢ Γ, A }}) by eauto using wf_ctx_extend.
    pose proof (IHB HΓA) as HB.
    assert (HM : {{ Γ ⊢ M : A }}) by (apply IHM; eauto).
    assert (HN : {{ Γ ⊢ N : B[Id,,M] }}) by
      (apply IHN; eauto using type_substitution, typing_identity_extension).
    destruct (type_readback_preserves_typing Hread _ _ _ _ HA HnA) as [HA' HEA].
    destruct (type_readback_preserves_typing Hread _ _ _ _ HB HnB) as [HC HEB].
    apply (convert_term _ _ {{{ Σ A B }}} _ (Nat.max i j)).
    + apply wf_pair with (i := Nat.max i j);
        eauto using type_cumulativity, Nat.le_max_l, Nat.le_max_r.
    + eapply wf_sigma.
      * eauto using type_cumulativity, Nat.le_max_l.
      * eapply type_cumulativity; [ | apply Nat.le_max_r].
        exact (change_binder _ _ _ _ _ _ HA HA' HEA HC).
    + eapply wf_exp_eq_sigma_cong;
        eauto using type_cumulativity, equality_cumulativity,
          Nat.le_max_l, Nat.le_max_r.
  - intros Γ A B M _ IHM HΓ.
    pose proof (IHM HΓ) as HM.
    destruct (type_of_typing _ _ _ HM) as [i Hsigma].
    destruct (type_former_components _ _ _ Hsigma) as [j [HA HB]].
    eapply wf_fst; eassumption.
  - intros Γ A B M C _ IHM Hn HΓ.
    pose proof (IHM HΓ) as HM.
    destruct (type_of_typing _ _ _ HM) as [i Hsigma].
    destruct (type_former_components _ _ _ Hsigma) as [j [HA HB]].
    eapply term_at_normalized_type; [exact Hread | | exact Hn].
    eapply wf_snd; eassumption.
  - intros Γ i A M N _ IHA _ IHM _ IHN HΓ.
    pose proof (IHA HΓ) as HA.
    apply wf_eq with (i := i); [exact HA | apply IHM | apply IHN]; eauto.
  - intros Γ i A M C N _ IHA _ IHM HnA HnM HΓ.
    pose proof (IHA HΓ) as HA.
    assert (HM : {{ Γ ⊢ M : A }}) by (apply IHM; eauto).
    destruct (type_readback_preserves_typing Hread _ _ _ _ HA HnA) as [HC HEC].
    destruct (Hread _ _ _ _ HM HnM) as [HN HEN].
    apply (convert_term _ _ {{{ Eq A M M }}} _ i).
    + eauto using wf_refl.
    + apply wf_eq with (i := i); eauto using convert_term.
    + now apply wf_exp_eq_eq_cong.
  - intros Γ i A M1 M2 j B BR N C _ IHA _ IHM1 _ IHM2 _ IHB _ IHBR _ IHN Hn HΓ.
    pose proof (IHA HΓ) as HA.
    assert (HΓA : {{ ⊢ Γ, A }}) by eauto using wf_ctx_extend.
    assert (HAw : {{ Γ, A ⊢ A[Wk] : Type@i }}) by eauto using weaken_type.
    assert (HΓAA : {{ ⊢ Γ, A, A[Wk] }}) by eauto using wf_ctx_extend.
    assert (HΓEq : {{ ⊢ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }})
      by eauto using wf_ctx_extend, eqrec_context.
    pose proof (IHB HΓEq) as HB.
    assert (HM1 : {{ Γ ⊢ M1 : A }}) by (apply IHM1; eauto).
    assert (HM2 : {{ Γ ⊢ M2 : A }}) by (apply IHM2; eauto).
    eapply term_at_normalized_type; [exact Hread | | exact Hn].
    eapply wf_eqrec; [exact HA | exact HM1 | exact HM2 | exact HB | apply IHBR | apply IHN];
      eauto using wf_eq, type_substitution, eqrec_refl_substitution.
  - intros x A Γ B Hx Hn HΓ.
    eapply term_at_normalized_type; [exact Hread | | exact Hn].
    now apply wf_vlookup.
Qed.

(* Scoping prevents neutral variables from reducing to values supplied
   by the default environment. *)
Local Fixpoint scoped_exp (M : exp) (n : nat) : Prop :=
  match M with
  | a_typ _ | a_nat | a_zero => True
  | a_succ M | a_fst M | a_snd M => scoped_exp M n
  | a_natrec A MZ MS M =>
      scoped_exp A (S n) /\ scoped_exp MZ n /\
      scoped_exp MS (S (S n)) /\ scoped_exp M n
  | a_pi A B | a_fn A B | a_sigma A B =>
      scoped_exp A n /\ scoped_exp B (S n)
  | a_app M N | a_refl M N => scoped_exp M n /\ scoped_exp N n
  | a_pair M A N B =>
      scoped_exp M n /\ scoped_exp A n /\ scoped_exp N n /\ scoped_exp B (S n)
  | a_eq A M N => scoped_exp A n /\ scoped_exp M n /\ scoped_exp N n
  | a_eqrec A B BR M1 M2 N =>
      scoped_exp A n /\ scoped_exp B (S (S (S n))) /\ scoped_exp BR (S n) /\
      scoped_exp M1 n /\ scoped_exp M2 n /\ scoped_exp N n
  | a_var x => x < n
  | a_sub M σ => exists m, scoped_sub σ n m /\ scoped_exp M m
  end
with scoped_sub (σ : sub) (n m : nat) : Prop :=
  match σ with
  | a_id => n = m
  | a_weaken => n = S m
  | a_compose σ τ => exists k, scoped_sub τ n k /\ scoped_sub σ k m
  | a_extend σ M => exists k, m = S k /\ scoped_sub σ n k /\ scoped_exp M n
  end.

Local Lemma lookup_in_bounds Γ x A :
  {{ #x : A ∈ Γ }} -> x < length Γ.
Proof. induction 1; simpl; lia. Qed.

Local Lemma subtyping_context_length Γ Δ :
  {{ ⊢ Γ ⊆ Δ }} -> length Γ = length Δ.
Proof. induction 1; simpl; congruence. Qed.

Local Lemma typing_scoped :
  (forall Γ A M, {{ Γ ⊢ M : A }} -> scoped_exp M (length Γ)) /\
  (forall Γ Δ σ, {{ Γ ⊢s σ : Δ }} -> scoped_sub σ (length Γ) (length Δ)).
Proof.
  assert (H : (forall Γ, {{ ⊢ Γ }} -> True) /\
    (forall Γ A M, {{ Γ ⊢ M : A }} -> scoped_exp M (length Γ)) /\
    (forall Γ Δ σ, {{ Γ ⊢s σ : Δ }} -> scoped_sub σ (length Γ) (length Δ))).
  {
    apply syntactic_wf_mut_ind'; intros; cbn in *;
      eauto 9 using lookup_in_bounds.
    match goal with
    | H : wf_ctx_sub ?Γ ?Δ |- _ =>
      rewrite <- (subtyping_context_length _ _ H); assumption
    end.
  }
  exact (proj2 H).
Qed.

Local Lemma initial_env_variable Γ ρ x :
  initial_env Γ ρ ->
  x < length Γ ->
  exists a, ρ x = d_neut a (d_var (length Γ - x - 1)).
Proof.
  intro H. revert x.
  induction H; intros x Hx; cbn in *; [lia |].
  destruct x as [|x].
  - exists a. f_equal. f_equal. lia.
  - apply IHinitial_env; simpl in Hx; lia.
Qed.

Local Lemma neutral_evaluation Γ ρ :
  initial_env Γ ρ ->
  forall M d, scoped_exp M (length Γ) ->
    (exists N : ne, M = ne_to_exp N) ->
    eval_exp M ρ d -> exists a k, d = d_neut a k.
Proof.
  intros Hρ M d HM [N ->] He.
  revert d HM He.
  induction N; intros d HM He; cbn in HM.
  - inversion He; subst.
    destruct HM as [_ [_ [_ Hscrutinee]]].
    match goal with
    | H : eval_exp (ne_to_exp N) ρ ?d |- _ =>
      destruct (IHN _ Hscrutinee H) as [a [k ->]]
    end.
    match goal with H : eval_natrec _ _ _ _ _ _ |- _ => inversion H; subst end.
    eauto.
  - inversion He; subst.
    destruct HM as [Hfunction _].
    match goal with
    | H : eval_exp (ne_to_exp N) ρ ?d |- _ =>
      destruct (IHN _ Hfunction H) as [a [k ->]]
    end.
    match goal with H : eval_app _ _ _ |- _ => inversion H; subst end.
    eauto.
  - inversion He; subst.
    match goal with
    | H : eval_exp (ne_to_exp N) ρ ?d |- _ =>
      destruct (IHN _ HM H) as [a [k ->]]
    end.
    match goal with H : eval_fst _ _ |- _ => inversion H; subst end.
    eauto.
  - inversion He; subst.
    match goal with
    | H : eval_exp (ne_to_exp N) ρ ?d |- _ =>
      destruct (IHN _ HM H) as [a [k ->]]
    end.
    match goal with H : eval_snd _ _ |- _ => inversion H; subst end.
    eauto.
  - inversion He; subst. destruct (initial_env_variable _ _ _ Hρ HM) as [a ->].
    eauto.
  - inversion He; subst.
    destruct HM as [_ [_ [_ [_ [_ Hscrutinee]]]]].
    match goal with
    | H : eval_exp (ne_to_exp N) ρ ?d |- _ =>
      destruct (IHN _ Hscrutinee H) as [a_neutral [k ->]]
    end.
    match goal with H : eval_eqrec _ _ _ _ _ _ _ _ |- _ => inversion H; subst end.
    eauto.
Qed.

Local Definition normal_type_head (A : nf) :=
  match A with
  | nf_typ _ => 0
  | nf_pi _ _ => 1
  | nf_sigma _ _ => 2
  | _ => 3
  end.

Local Lemma normalization_preserves_normal_type_head Γ A B :
  scoped_exp (nf_to_exp A) (length Γ) ->
  nbe_ty Γ A B ->
  normal_type_head A = normal_type_head B.
Proof.
  intros Hsc Hn. inversion Hn; subst.
  destruct A; cbn in *;
    match goal with
    | H : eval_exp (ne_to_exp ?N) ?ρ _, Hρ : initial_env _ ?ρ |- _ =>
        destruct (neutral_evaluation _ _ Hρ _ _ Hsc
          ltac:(exists N; reflexivity) H) as [a [k ->]]
    | H : eval_exp _ _ _ |- _ => inversion H; subst
    end;
    match goal with H : read_typ _ _ _ |- _ => inversion H; subst end;
    reflexivity.
Qed.

(* Completeness reduces to existence and adequacy of normalization. *)
Local Definition readback_total :=
  forall Γ A M, {{ Γ ⊢ M : A }} -> exists N, nbe Γ M A N.

Local Definition declarative_subtyping_is_algorithmic :=
  forall Γ A B, {{ Γ ⊢ A ⊆ B }} -> {{ Γ ⊢a A ⊆ B }}.

Local Lemma type_readback_total :
  readback_total ->
  forall Γ A i, {{ Γ ⊢ A : Type@i }} -> exists B, nbe_ty Γ A B.
Proof.
  intros H Γ A i HA. destruct (H _ _ _ HA) as [B HB].
  inversion HB; subst.
  match goal with
  | H : eval_exp (a_typ _) _ _ |- _ => inversion H; subst
  end.
  match goal with
  | H : read_nf _ _ _ |- _ => inversion H; subst
  end.
  eauto using nbe_ty_run.
Qed.

Local Lemma normalized_type_lower_bound :
  readback_preserves_typing -> readback_total ->
  forall Γ A i, {{ Γ ⊢ A : Type@i }} ->
    exists B, nbe_ty Γ A B /\ {{ Γ ⊢ B ⊆ A }}.
Proof.
  intros Hp Ht Γ A i HA.
  destruct (type_readback_total Ht _ _ _ HA) as [B Hn].
  destruct (type_readback_preserves_typing Hp _ _ _ _ HA Hn) as [_ HE].
  eauto using wf_subtyp_refl, wf_exp_eq_sym.
Qed.

Local Lemma normalizes_universe Γ i A :
  nbe_ty Γ (a_typ i) A -> A = nf_typ i.
Proof.
  intro H. inversion H; subst.
  match goal with H : eval_exp _ _ _ |- _ => inversion H; subst end.
  match goal with H : read_typ _ _ _ |- _ => inversion H; reflexivity end.
Qed.

Local Lemma normalizes_pi Γ A B N :
  nbe_ty Γ (a_pi A B) N ->
  exists C D, N = nf_pi C D /\ nbe_ty Γ A C /\ nbe_ty (A :: Γ) B D.
Proof.
  intro H. inversion H; subst.
  match goal with H : eval_exp _ _ _ |- _ => inversion H; subst end.
  match goal with H : read_typ _ _ _ |- _ => inversion H; subst end.
  eauto 8 using nbe_ty_run, initial_env_cons.
Qed.

Local Lemma normalizes_sigma Γ A B N :
  nbe_ty Γ (a_sigma A B) N ->
  exists C D, N = nf_sigma C D /\ nbe_ty Γ A C /\ nbe_ty (A :: Γ) B D.
Proof.
  intro H. inversion H; subst.
  match goal with H : eval_exp _ _ _ |- _ => inversion H; subst end.
  match goal with H : read_typ _ _ _ |- _ => inversion H; subst end.
  eauto 8 using nbe_ty_run, initial_env_cons.
Qed.

Local Lemma normal_subtype_universe Γ (A : nf) i j :
  declarative_subtyping_is_algorithmic ->
  {{ Γ ⊢ A : Type@j }} ->
  {{ Γ ⊢ A ⊆ Type@i }} ->
  exists k, A = nf_typ k /\ k <= i.
Proof.
  intros Hsub HA H.
  pose proof (Hsub _ _ _ H) as Halg.
  inversion Halg as [Γ' A' B' N P HN HP HNP]; subst.
  apply normalizes_universe in HP. subst P.
  inversion HNP; subst; cbn in *; try contradiction.
  pose proof (normalization_preserves_normal_type_head _ _ _
    (proj1 typing_scoped _ _ _ HA) HN) as Hhead.
  destruct A; cbn in Hhead; try discriminate.
  apply normalizes_universe in HN. inversion HN; subst.
  eauto.
Qed.

Local Lemma compare_codomain_from_normalization :
  readback_preserves_typing ->
  forall Γ A B C D i j X Y Z,
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ, A ⊢ B : Type@i }} ->
    {{ Γ ⊢ C : Type@j }} ->
    {{ Γ, C ⊢ D : Type@j }} ->
    nbe_ty Γ A X -> nbe_ty Γ C X ->
    nbe_ty (A :: Γ) B Y -> nbe_ty (C :: Γ) D Z ->
    {{ ⊢anf Z ⊆ Y }} ->
    exists k,
      {{ Γ ⊢ A : Type@k }} /\
      {{ Γ ⊢ C : Type@k }} /\
      {{ Γ ⊢ A ≈ C : Type@k }} /\
      {{ Γ, C ⊢ D ⊆ B }}.
Proof.
  intros Hp Γ A B C D i j X Y Z HA HB HC HD HAX HCX HBY HDZ HZY.
  pose proof (typing_context _ _ _ HA) as HΓ.
  destruct (type_readback_preserves_typing Hp _ _ _ _ HA HAX) as [HX HEA].
  destruct (type_readback_preserves_typing Hp _ _ _ _ HC HCX) as [_ HEC].
  destruct (type_readback_preserves_typing Hp _ _ _ _ HB HBY) as [HY HEB].
  destruct (type_readback_preserves_typing Hp _ _ _ _ HD HDZ) as [HZ HED].
  exists (Nat.max i j).
  assert (HA' : {{ Γ ⊢ A : Type@(Nat.max i j) }})
    by eauto using type_cumulativity, Nat.le_max_l.
  assert (HC' : {{ Γ ⊢ C : Type@(Nat.max i j) }})
    by eauto using type_cumulativity, Nat.le_max_r.
  assert (HE : {{ Γ ⊢ A ≈ C : Type@(Nat.max i j) }}).
  {
    eapply wf_exp_eq_trans with (M' := nf_to_exp X).
    - eauto using equality_cumulativity, Nat.le_max_l.
    - apply wf_exp_eq_sym. eauto using equality_cumulativity, Nat.le_max_r.
  }
  do 3 (split; [assumption |]).
  assert (HΓC : {{ ⊢ Γ, C }}) by eauto using wf_ctx_extend.
  assert (HΓCA : {{ ⊢ Γ, C ⊆ Γ, A }}) by
    eauto using wf_ctx_sub_extend, wf_subtyp_refl, wf_exp_eq_sym,
      context_subtyping_reflexive.
  pose proof (proj1 narrowing _ _ _ HY _ HΓC HΓCA) as HY'.
  pose proof (proj1 narrowing _ _ _ HB _ HΓC HΓCA) as HB'.
  pose proof (proj1 (proj2 narrowing) _ _ _ _ HEB _ HΓC HΓCA) as HEB'.
  eapply wf_subtyp_trans with (M' := nf_to_exp Z).
  - eauto using wf_subtyp_refl.
  - eapply wf_subtyp_trans with (M' := nf_to_exp Y).
    + eauto using normal_subtyping_sound.
    + eauto using wf_subtyp_refl, wf_exp_eq_sym.
Qed.

Local Lemma normal_subtype_pi_components :
  readback_preserves_typing ->
  declarative_subtyping_is_algorithmic ->
  forall Γ (F : nf) A B i j,
    {{ Γ ⊢ F : Type@j }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ, A ⊢ B : Type@i }} ->
    {{ Γ ⊢ F ⊆ Π A B }} ->
    exists C D : nf, F = nf_pi C D /\ exists k,
      {{ Γ ⊢ A : Type@k }} /\
      {{ Γ ⊢ C : Type@k }} /\
      {{ Γ ⊢ A ≈ C : Type@k }} /\
      {{ Γ, ^(nf_to_exp C) ⊢ D ⊆ B }}.
Proof.
  intros Hp Hcomp Γ F A B i j HF HA HB H.
  pose proof (Hcomp _ _ _ H) as Halg.
  inversion Halg as [Γ' A' B' N P HN HP HNP]; subst.
  destruct (normalizes_pi _ _ _ _ HP) as [X [Y [-> [HAX HBY]]]].
  inversion HNP; subst; cbn in *; try contradiction.
  pose proof (normalization_preserves_normal_type_head _ _ _
    (proj1 typing_scoped _ _ _ HF) HN) as Hhead.
  destruct F; cbn in Hhead; try discriminate.
  destruct (type_former_components _ _ _ HF) as [l [HC HD]].
  destruct (normalizes_pi _ _ _ _ HN) as [X' [Z [Heq [HCX HDZ]]]].
  inversion Heq; subst.
  exists F1, F2. split; [reflexivity |].
  eapply compare_codomain_from_normalization; eassumption.
Qed.

Local Lemma normal_subtype_sigma_components :
  readback_preserves_typing ->
  declarative_subtyping_is_algorithmic ->
  forall Γ (F : nf) A B i j,
    {{ Γ ⊢ F : Type@j }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ, A ⊢ B : Type@i }} ->
    {{ Γ ⊢ F ⊆ Σ A B }} ->
    exists C D : nf, F = nf_sigma C D /\ exists k,
      {{ Γ ⊢ A : Type@k }} /\
      {{ Γ ⊢ C : Type@k }} /\
      {{ Γ ⊢ A ≈ C : Type@k }} /\
      {{ Γ, ^(nf_to_exp C) ⊢ D ⊆ B }}.
Proof.
  intros Hp Hcomp Γ F A B i j HF HA HB H.
  pose proof (Hcomp _ _ _ H) as Halg.
  inversion Halg as [Γ' A' B' N P HN HP HNP]; subst.
  destruct (normalizes_sigma _ _ _ _ HP) as [X [Y [-> [HAX HBY]]]].
  inversion HNP; subst; cbn in *; try contradiction.
  pose proof (normalization_preserves_normal_type_head _ _ _
    (proj1 typing_scoped _ _ _ HF) HN) as Hhead.
  destruct F; cbn in Hhead; try discriminate.
  destruct (type_former_components _ _ _ HF) as [l [HC HD]].
  destruct (normalizes_sigma _ _ _ _ HN) as [X' [Z [Heq [HCX HDZ]]]].
  inversion Heq; subst.
  exists F1, F2. split; [reflexivity |].
  eapply compare_codomain_from_normalization; eassumption.
Qed.

Local Lemma check_from_subtype :
  declarative_subtyping_is_algorithmic ->
  forall Γ M A B,
    (exists F, {{ Γ ⊢a M ⟹ F }} /\ {{ Γ ⊢ F ⊆ A }}) ->
    {{ Γ ⊢ A ⊆ B }} ->
    {{ Γ ⊢a M ⟸ B }}.
Proof.
  intros Hcomp Γ M A B [F [HF HFA]] HAB.
  exact (atc_ati _ _ _ _ HF (Hcomp _ _ _ (wf_subtyp_trans _ _ _ _ HFA HAB))).
Qed.

Local Lemma check_from_inferred_type :
  declarative_subtyping_is_algorithmic ->
  forall Γ M A,
    {{ Γ ⊢ M : A }} ->
    (exists F, {{ Γ ⊢a M ⟹ F }} /\ {{ Γ ⊢ F ⊆ A }}) ->
    {{ Γ ⊢a M ⟸ A }}.
Proof.
  intros Hcomp Γ M A HM Hex.
  destruct (type_of_typing _ _ _ HM) as [i HA].
  eauto using check_from_subtype, subtype_from_typed_reflexivity.
Qed.

Local Lemma inference_at_universe :
  readback_preserves_typing ->
  declarative_subtyping_is_algorithmic ->
  forall Γ A i,
    {{ ⊢ Γ }} ->
    (exists F, {{ Γ ⊢a A ⟹ F }} /\ {{ Γ ⊢ F ⊆ Type@i }}) ->
    exists j, {{ Γ ⊢a A ⟹ Type@j }} /\ j <= i.
Proof.
  intros Hp Hcomp Γ A i HΓ [F [HF Hsub]].
  pose proof (proj2 (algorithm_sound_from_readback Hp) _ _ _ HF HΓ) as HA.
  destruct (type_of_typing _ _ _ HA) as [k HFt].
  destruct (normal_subtype_universe _ _ _ _ Hcomp HFt Hsub) as [j [-> Hle]].
  eauto.
Qed.

Local Lemma subtyping_universes Γ i j :
  {{ ⊢ Γ }} -> i <= j -> {{ Γ ⊢ Type@i ⊆ Type@j }}.
Proof.
  intros HΓ Hij. destruct (Nat.eq_dec i j) as [-> | Hne].
  - eauto using wf_typ, subtype_from_typed_reflexivity.
  - apply wf_subtyp_univ; [assumption | lia].
Qed.

Local Lemma normalize_smaller_type :
  readback_preserves_typing -> readback_total ->
  forall Γ C A i,
    {{ Γ ⊢ C : Type@i }} ->
    {{ Γ ⊢ C ⊆ A }} ->
    exists R, nbe_ty Γ C R /\ {{ Γ ⊢ R ⊆ A }}.
Proof.
  intros Hp Ht Γ C A i HC Hsub.
  destruct (normalized_type_lower_bound Hp Ht _ _ _ HC) as [R [HR HRC]].
  eauto using wf_subtyp_trans.
Qed.

Local Lemma algorithm_inference_complete_from_normalization :
  readback_preserves_typing -> readback_total -> declarative_subtyping_is_algorithmic ->
  forall Γ M A, {{ Γ ⊢ M : A }} -> user_exp M ->
    exists F, {{ Γ ⊢a M ⟹ F }} /\ {{ Γ ⊢ F ⊆ A }}.
Proof.
  intros Hp Ht Hcomp Γ M A Htyping.
  induction Htyping as
    [Γ i HΓ
    |Γ HΓ
    |Γ HΓ
    |Γ M HM IHM
    |Γ i A MZ MS M HA IHA HMZ IHMZ HMS IHMS HM IHM
    |Γ i A B HA IHA HB IHB
    |Γ i A B M HA IHA HM IHM
    |Γ i A B M N HA IHA HB IHB HM IHM HN IHN
    |Γ i A B HA IHA HB IHB
    |Γ i A B M N HA IHA HB IHB HM IHM HN IHN
    |Γ i A B M HA IHA HB IHB HM IHM
    |Γ i A B M HA IHA HB IHB HM IHM
    |Γ x A HΓ Hx
    |Γ i A M N HA IHA HM IHM HN IHN
    |Γ i A M HA IHA HM IHM
    |Γ i A M1 M2 j B BR N HA IHA HM1 IHM1 HM2 IHM2 HB IHB HBR IHBR HN IHN
    |Γ Δ σ A M Hσ HM IHM
    |Γ A M i B HM IHM HB IHB Hsub];
    intro Hu.
  1-17: inversion Hu; subst.
  - exists (nf_typ (S i)). split; [constructor | now apply subtyping_universes].
  - exists (nf_typ 0). split; [constructor | now apply subtyping_universes].
  - exists nf_nat. split; [constructor | eauto using wf_nat, subtype_from_typed_reflexivity].
  - exists nf_nat. split.
    + apply ati_succ. eauto using check_from_inferred_type.
    + eauto using wf_nat, subtype_from_typed_reflexivity, typing_context.
  - assert (HΓN : {{ ⊢ Γ, ℕ }}) by eauto using typing_context.
    destruct (inference_at_universe Hp Hcomp _ _ _ HΓN (IHA ltac:(assumption)))
      as [j [HAt Hle]].
    assert (HAresult : {{ Γ ⊢ A[Id,,M] : Type@i }})
      by eauto using type_substitution, nat_case_substitution.
    destruct (normalized_type_lower_bound Hp Ht _ _ _ HAresult) as [R [HR Hsub]].
    exists R. split; [ | exact Hsub].
    eapply ati_natrec; eauto using check_from_inferred_type.
  - pose proof (typing_context _ _ _ HA) as HΓ.
    pose proof (typing_context _ _ _ HB) as HΓA.
    destruct (inference_at_universe Hp Hcomp _ _ _ HΓ (IHA ltac:(assumption)))
      as [k [HAt Hk]].
    destruct (inference_at_universe Hp Hcomp _ _ _ HΓA (IHB ltac:(assumption)))
      as [l [HBt Hl]].
    exists (nf_typ (Nat.max k l)). split; [now apply ati_pi |].
    apply subtyping_universes; [assumption | lia].
  - pose proof (typing_context _ _ _ HA) as HΓ.
    pose proof (typing_context _ _ _ HM) as HΓA.
    destruct (inference_at_universe Hp Hcomp _ _ _ HΓ (IHA ltac:(assumption)))
      as [j [HAt _]].
    destruct (IHM ltac:(assumption)) as [F [HMF HFB]].
    destruct (type_readback_total Ht _ _ _ HA) as [C Hn].
    destruct (type_readback_preserves_typing Hp _ _ _ _ HA Hn) as [HC HE].
    pose proof (proj2 (algorithm_sound_from_readback Hp) _ _ _ HMF HΓA) as HMF'.
    destruct (type_of_typing _ _ _ HMF') as [k HF].
    destruct (type_of_typing _ _ _ HM) as [l HB].
    exists (nf_pi C F). split; [eauto using ati_fn |].
    apply wf_subtyp_pi with (i := Nat.max i (Nat.max k l)).
    + eapply type_cumulativity; [exact HC | lia].
    + eapply type_cumulativity; [exact HA | lia].
    + apply wf_exp_eq_sym. eapply equality_cumulativity; [exact HE | exact HΓ | lia].
    + eapply type_cumulativity.
      * exact (change_binder _ _ _ _ _ _ HA HC HE HF).
      * lia.
    + eapply type_cumulativity; [exact HB | lia].
    + exact HFB.
  - pose proof (typing_context _ _ _ HA) as HΓ.
    destruct (IHM ltac:(assumption)) as [F [HMF HFsub]].
    pose proof (proj2 (algorithm_sound_from_readback Hp) _ _ _ HMF HΓ) as HMF'.
    destruct (type_of_typing _ _ _ HMF') as [j HF].
    destruct (normal_subtype_pi_components Hp Hcomp _ _ _ _ _ _ HF HA HB HFsub)
      as [C [D [-> [k [HAk [HC [HE HDB]]]]]]].
    assert (HNC : {{ Γ ⊢ N : C }}) by (eapply convert_term; eassumption).
    assert (Hσ : {{ Γ ⊢s Id,,N : Γ, ^(nf_to_exp C) }}) by eauto using typing_identity_extension.
    pose proof (subtyping_under_substitution _ _ _ HDB _ _ Hσ) as Hsub.
    destruct (type_former_components _ _ _ HF) as [l [HC' HD]].
    assert (HDR : {{ Γ ⊢ D[Id,,N] : Type@l }}) by eauto using type_substitution.
    destruct (normalize_smaller_type Hp Ht _ _ _ _ HDR Hsub) as [R [HR HRsub]].
    exists R. split; [ | exact HRsub].
    eapply ati_app; [exact HMF | | exact HR].
    eapply check_from_subtype; [exact Hcomp | eauto | eauto using wf_subtyp_refl].
  - pose proof (typing_context _ _ _ HA) as HΓ.
    pose proof (typing_context _ _ _ HB) as HΓA.
    destruct (inference_at_universe Hp Hcomp _ _ _ HΓ (IHA ltac:(assumption)))
      as [k [HAt Hk]].
    destruct (inference_at_universe Hp Hcomp _ _ _ HΓA (IHB ltac:(assumption)))
      as [l [HBt Hl]].
    exists (nf_typ (Nat.max k l)). split; [now apply ati_sigma |].
    apply subtyping_universes; [assumption | lia].
  - pose proof (typing_context _ _ _ HA) as HΓ.
    pose proof (typing_context _ _ _ HB) as HΓA.
    destruct (inference_at_universe Hp Hcomp _ _ _ HΓ (IHA ltac:(assumption)))
      as [k [HAt Hk]].
    destruct (inference_at_universe Hp Hcomp _ _ _ HΓA (IHB ltac:(assumption)))
      as [l [HBt Hl]].
    destruct (type_readback_total Ht _ _ _ HA) as [C HnC].
    destruct (type_readback_total Ht _ _ _ HB) as [D HnD].
    destruct (type_readback_preserves_typing Hp _ _ _ _ HA HnC) as [HC HEA].
    destruct (type_readback_preserves_typing Hp _ _ _ _ HB HnD) as [HD HEB].
    exists (nf_sigma C D). split.
    + eapply ati_pair; eauto using check_from_inferred_type.
    + eapply wf_subtyp_refl.
      * eapply wf_sigma; eassumption.
      * apply wf_exp_eq_sym. eapply wf_exp_eq_sigma_cong; eassumption.
  - pose proof (typing_context _ _ _ HA) as HΓ.
    destruct (IHM ltac:(assumption)) as [F [HMF HFsub]].
    pose proof (proj2 (algorithm_sound_from_readback Hp) _ _ _ HMF HΓ) as HMF'.
    destruct (type_of_typing _ _ _ HMF') as [j HF].
    destruct (normal_subtype_sigma_components Hp Hcomp _ _ _ _ _ _ HF HA HB HFsub)
      as [C [D [-> [k [HAk [HC [HE HDB]]]]]]].
    exists C. split; [eauto using ati_fst |].
    eauto using wf_subtyp_refl, wf_exp_eq_sym.
  - pose proof (typing_context _ _ _ HA) as HΓ.
    destruct (IHM ltac:(assumption)) as [F [HMF HFsub]].
    pose proof (proj2 (algorithm_sound_from_readback Hp) _ _ _ HMF HΓ) as HMF'.
    destruct (type_of_typing _ _ _ HMF') as [j HF].
    destruct (normal_subtype_sigma_components Hp Hcomp _ _ _ _ _ _ HF HA HB HFsub)
      as [C [D [-> [k [HAk [HC [HE HDB]]]]]]].
    destruct (type_former_components _ _ _ HF) as [l [HC' HD]].
    assert (Hfst : {{ Γ ⊢ fst M : C }}) by eauto using wf_fst.
    assert (Hσ : {{ Γ ⊢s Id,,fst M : Γ, ^(nf_to_exp C) }}) by eauto using typing_identity_extension.
    pose proof (subtyping_under_substitution _ _ _ HDB _ _ Hσ) as Hsub.
    assert (HDR : {{ Γ ⊢ D[Id,,fst M] : Type@l }}) by eauto using type_substitution.
    destruct (normalize_smaller_type Hp Ht _ _ _ _ HDR Hsub) as [R [HR HRsub]].
    exists R. split; [eauto using ati_snd | exact HRsub].
  - destruct (lookup_type _ _ _ Hx HΓ) as [i HA].
    destruct (normalized_type_lower_bound Hp Ht _ _ _ HA) as [R [HR Hsub]].
    exists R. split; [eauto using ati_vlookup | exact Hsub].
  - pose proof (typing_context _ _ _ HA) as HΓ.
    destruct (inference_at_universe Hp Hcomp _ _ _ HΓ (IHA ltac:(assumption)))
      as [j [HAt Hle]].
    exists (nf_typ j). split.
    + eapply ati_eq; [exact HAt | | ]; eauto using check_from_inferred_type.
    + now apply subtyping_universes.
  - pose proof (typing_context _ _ _ HA) as HΓ.
    destruct (inference_at_universe Hp Hcomp _ _ _ HΓ (IHA ltac:(assumption)))
      as [j [HAt _]].
    destruct (type_readback_total Ht _ _ _ HA) as [C HnC].
    destruct (type_readback_preserves_typing Hp _ _ _ _ HA HnC) as [HC HEC].
    destruct (Ht _ _ _ HM) as [N HnN].
    destruct (Hp _ _ _ _ HM HnN) as [HN HEN].
    exists (nf_eq C N N). split.
    + eapply ati_refl; eauto using check_from_inferred_type.
    + eapply wf_subtyp_refl.
      * eapply wf_eq; eassumption.
      * apply wf_exp_eq_sym. now apply wf_exp_eq_eq_cong.
  - pose proof (typing_context _ _ _ HA) as HΓ.
    pose proof (typing_context _ _ _ HB) as HΓEq.
    destruct (inference_at_universe Hp Hcomp _ _ _ HΓ (IHA ltac:(assumption)))
      as [k [HAt _]].
    destruct (inference_at_universe Hp Hcomp _ _ _ HΓEq (IHB ltac:(assumption)))
      as [l [HBt _]].
    assert (Hresult : {{ Γ ⊢ B[Id,,M1,,M2,,N] : Type@j }})
      by eauto using type_substitution, eqrec_case_substitution.
    destruct (normalized_type_lower_bound Hp Ht _ _ _ Hresult) as [R [HR Hsub]].
    exists R. split; [ | exact Hsub].
    eapply ati_eqrec; eauto using check_from_inferred_type.
  - destruct (IHM Hu) as [F [HF HFsub]].
    exists F. split; eauto using wf_subtyp_trans.
Qed.

Local Lemma algorithm_complete_from_normalization :
  readback_preserves_typing -> readback_total -> declarative_subtyping_is_algorithmic ->
  forall Γ A M, user_exp M -> {{ Γ ⊢ M : A }} -> {{ Γ ⊢a M ⟸ A }}.
Proof.
  eauto using check_from_inferred_type, algorithm_inference_complete_from_normalization.
Qed.

(* Shared readbacks for declarative type equality suffice for totality
   and for completeness of algorithmic subtyping. *)
Local Definition type_equality_has_common_readback :=
  forall Γ A B i, {{ Γ ⊢ A ≈ B : Type@i }} ->
    exists R, nbe_ty Γ A R /\ nbe_ty Γ B R.

Local Lemma readback_total_from_type_equality :
  type_equality_has_common_readback -> readback_total.
Proof.
  intros Heq Γ A M HM.
  destruct (type_of_typing _ _ _ HM) as [i HA].
  assert (HE : {{ Γ ⊢ Eq A M M : Type@i }}) by eauto using wf_eq.
  destruct (Heq _ _ _ _ (expression_equality_reflexive _ _ _ HE)) as [R [HR _]].
  inversion HR; subst.
  match goal with H : eval_exp _ _ _ |- _ => inversion H; subst end.
  match goal with H : read_typ _ _ _ |- _ => inversion H; subst end.
  eauto using nbe_run.
Qed.

Local Lemma algorithmic_subtyping_transitive Γ A B C :
  {{ Γ ⊢a A ⊆ B }} -> {{ Γ ⊢a B ⊆ C }} -> {{ Γ ⊢a A ⊆ C }}.
Proof.
  intros H K.
  inversion H as [Γ' A' B' NA NB HNA HNB Hsub]; subst.
  inversion K as [Γ' B' C' NB' NC HNB' HNC Hsub']; subst.
  pose proof (nbe_ty_deterministic _ _ _ _ HNB HNB') as ->.
  eauto using alg_subtyp_run, subtyping_nf_transitive.
Qed.

Local Ltac reconcile_type_readbacks :=
  repeat multimatch goal with
  | H : nbe_ty ?Γ ?A ?X, K : nbe_ty ?Γ ?A ?Y |- _ =>
      tryif constr_eq X Y then fail
      else let E := fresh in
        pose proof (nbe_ty_deterministic _ _ _ _ H K) as E;
        first [is_var X; subst X | is_var Y; subst Y]
  end.

Local Lemma subtyping_complete_from_type_readback :
  type_equality_has_common_readback -> declarative_subtyping_is_algorithmic.
Proof.
  intros Heq Γ A B Hsub.
  pose proof (readback_total_from_type_equality Heq) as Htotal.
  induction Hsub as
    [Γ i A B HB He
    |Γ A B C HAB IH1 HBC IH2
    |Γ i j HΓ Hlt
    |Γ i A A' B B' HA HA' He HB HB' Hsub IH
    |Γ i A A' B B' HA HA' He HB HB' Hsub IH].
  - destruct (Heq _ _ _ _ He) as [R [HA HnB]].
    eauto using alg_subtyp_run, subtyping_nf_reflexive.
  - eauto using algorithmic_subtyping_transitive.
  - destruct (type_readback_total Htotal _ _ _ (wf_typ Γ i HΓ)) as [R HR].
    destruct (type_readback_total Htotal _ _ _ (wf_typ Γ j HΓ)) as [S HS].
    pose proof (normalizes_universe _ _ _ HR) as ->.
    pose proof (normalizes_universe _ _ _ HS) as ->.
    eapply alg_subtyp_run; try eassumption.
    apply asnf_univ. lia.
  - assert (Hform : {{ Γ ⊢ Π A B ≈ Π A' B : Type@i }})
      by eauto using wf_exp_eq_pi_cong, expression_equality_reflexive.
    destruct (Heq _ _ _ _ Hform) as [R [HR HR']].
    destruct (normalizes_pi _ _ _ _ HR') as [X [Y [-> [HX HY]]]].
    destruct (type_readback_total Htotal _ _ _ (wf_pi _ _ _ _ HA' HB')) as [S HS].
    destruct (normalizes_pi _ _ _ _ HS) as [X' [Z [-> [HX' HZ]]]].
    inversion IH; subst. reconcile_type_readbacks.
    eapply alg_subtyp_run; [exact HR | exact HS |].
    now apply asnf_pi.
  - assert (Hform : {{ Γ ⊢ Σ A B ≈ Σ A' B : Type@i }})
      by eauto using wf_exp_eq_sigma_cong, expression_equality_reflexive.
    destruct (Heq _ _ _ _ Hform) as [R [HR HR']].
    destruct (normalizes_sigma _ _ _ _ HR') as [X [Y [-> [HX HY]]]].
    destruct (type_readback_total Htotal _ _ _ (wf_sigma _ _ _ _ HA' HB')) as [S HS].
    destruct (normalizes_sigma _ _ _ _ HS) as [X' [Z [-> [HX' HZ]]]].
    inversion IH; subst. reconcile_type_readbacks.
    eapply alg_subtyp_run; [exact HR | exact HS |].
    now apply asnf_sigma.
Qed.

Local Lemma algorithm_complete_from_readback :
  readback_preserves_typing ->
  type_equality_has_common_readback ->
  forall Γ A M, user_exp M -> {{ Γ ⊢ M : A }} -> {{ Γ ⊢a M ⟸ A }}.
Proof.
  intros Hp Heq.
  apply algorithm_complete_from_normalization;
    eauto using readback_total_from_type_equality, subtyping_complete_from_type_readback.
Qed.

From Stdlib Require Import Arith.Wf_nat.
(* Semantic relations for a universe layer. Readback agreement quantifies
   over the level at which the values are quoted. *)

Local Definition value_relation := domain -> domain -> Prop.

Local Definition relations_agree (R S : value_relation) :=
  forall x y, R x y <-> S x y.

Local Definition neutrals_agree (x y : domain_ne) :=
  forall s, exists N, read_ne s x N /\ read_ne s y N.

Local Definition neutral_values_agree : value_relation :=
  fun x y => exists a b m n,
    x = d_neut a m /\ y = d_neut b n /\ neutrals_agree m n.

Inductive natural_values_agree : value_relation :=
| natural_values_zero : natural_values_agree d_zero d_zero
| natural_values_succ x y :
    natural_values_agree x y ->
    natural_values_agree (d_succ x) (d_succ y)
| natural_values_neutral x y :
    neutral_values_agree x y -> natural_values_agree x y.

Local Definition function_values_agree
    (R : value_relation) (S : domain -> domain -> value_relation) : value_relation :=
  fun f g => forall x y, R x y ->
    exists u v, eval_app f x u /\ eval_app g y v /\ S x y u v.

Local Definition pair_values_agree
    (R : value_relation) (S : domain -> domain -> value_relation) : value_relation :=
  fun p qv => exists x y u v,
    eval_fst p x /\ eval_fst qv y /\ eval_snd p u /\ eval_snd qv v /\
    R x y /\ S x y u v.

Local Definition equality_values_agree
    (R : value_relation) (m n : domain) : value_relation :=
  fun p qv => neutral_values_agree p qv \/
    exists x y, p = d_refl x /\ qv = d_refl y /\
      R x y /\ R x m /\ R x n.

Local Definition universe_family := nat -> domain -> domain -> value_relation -> Prop.

Local Definition universe_values_agree (U : universe_family) i : value_relation :=
  fun a b => exists R, U i a b R.

Inductive universe_layer (U : universe_family) (i : nat)
  : domain -> domain -> value_relation -> Prop :=
| layer_universe j R :
    j < i ->
    relations_agree R (universe_values_agree U j) ->
    universe_layer U i (d_univ j) (d_univ j) R
| layer_natural R :
    relations_agree R natural_values_agree ->
    universe_layer U i d_nat d_nat R
| layer_function a a' ρ ρ' B B' R S T :
    universe_layer U i a a' R ->
    (forall x y, R x y -> exists b b',
      eval_exp B (extend_env ρ x) b /\ eval_exp B' (extend_env ρ' y) b') ->
    (forall x y b b', R x y ->
      eval_exp B (extend_env ρ x) b ->
      eval_exp B' (extend_env ρ' y) b' ->
      universe_layer U i b b' (S x y)) ->
    relations_agree T (function_values_agree R S) ->
    universe_layer U i (d_pi a ρ B) (d_pi a' ρ' B') T
| layer_pair a a' ρ ρ' B B' R S T :
    universe_layer U i a a' R ->
    (forall x y, R x y -> exists b b',
      eval_exp B (extend_env ρ x) b /\ eval_exp B' (extend_env ρ' y) b') ->
    (forall x y b b', R x y ->
      eval_exp B (extend_env ρ x) b ->
      eval_exp B' (extend_env ρ' y) b' ->
      universe_layer U i b b' (S x y)) ->
    relations_agree T (pair_values_agree R S) ->
    universe_layer U i (d_sigma a ρ B) (d_sigma a' ρ' B') T
| layer_equality a a' m n m' n' R S :
    universe_layer U i a a' R ->
    R m m' ->
    R n n' ->
    relations_agree S (equality_values_agree R m n) ->
    universe_layer U i (d_eq a m n) (d_eq a' m' n') S
| layer_neutral a a' n n' R :
    neutrals_agree n n' ->
    relations_agree R neutral_values_agree ->
    universe_layer U i (d_neut a n) (d_neut a' n') R.

Local Definition type_quotes_agree (a b : domain) :=
  forall s, exists A, read_typ s a A /\ read_typ s b A.

Local Definition value_quotes_agree (a b : domain) (R : value_relation) :=
  forall x y, R x y ->
    forall s, exists X, read_nf s (d_dom a x) X /\ read_nf s (d_dom b y) X.

Local Definition reflects_neutrals (a b : domain) (R : value_relation) :=
  forall m n, neutrals_agree m n -> R (d_neut a m) (d_neut b n).

Local Definition layer_readback a b R :=
  type_quotes_agree a b /\ value_quotes_agree a b R /\ reflects_neutrals a b R.

Local Lemma related_variable n : neutrals_agree (d_var n) (d_var n).
Proof. intro s. eexists. split; apply read_ne_var. Qed.

Local Lemma related_neutral_application a b m n x y :
  neutrals_agree m n ->
  (forall s, exists X, read_nf s (d_dom a x) X /\ read_nf s (d_dom b y) X) ->
  neutrals_agree (d_app m (d_dom a x)) (d_app n (d_dom b y)).
Proof.
  intros Hne Hval s.
  destruct (Hne s) as [N [Hl Hr]]. destruct (Hval s) as [X [Hx Hy]].
  exists (ne_app N X). auto using read_ne_app.
Qed.

Local Lemma related_neutral_fst m n :
  neutrals_agree m n -> neutrals_agree (d_fst m) (d_fst n).
Proof.
  intros H s. destruct (H s) as [N [Hl Hr]].
  exists (ne_fst N). auto using read_ne_fst.
Qed.

Local Lemma related_neutral_snd m n :
  neutrals_agree m n -> neutrals_agree (d_snd m) (d_snd n).
Proof.
  intros H s. destruct (H s) as [N [Hl Hr]].
  exists (ne_snd N). auto using read_ne_snd.
Qed.

Local Lemma natural_values_readback : value_quotes_agree d_nat d_nat natural_values_agree.
Proof.
  intros x y H.
  induction H as [|x y H0 IH|x y [a [b [m [n [-> [-> Hne]]]]]]]; intro s.
  - exists nf_zero. auto using read_nf_zero.
  - destruct (IH s) as [N [Hl Hr]].
    exists (nf_succ N). auto using read_nf_succ.
  - destruct (Hne s) as [N [Hl Hr]].
    exists (nf_neut N). eauto using read_nf_nat_neut.
Qed.

Local Lemma layer_relation_conversion U i a b R S :
  universe_layer U i a b R ->
  relations_agree R S ->
  universe_layer U i a b S.
Proof.
  intros H HS. destruct H;
    first [eapply layer_universe | eapply layer_natural | eapply layer_function |
      eapply layer_pair | eapply layer_equality | eapply layer_neutral];
    try eassumption.
  all: intros x y; specialize (HS x y).
  all: match goal with Hrel : relations_agree _ _ |- _ =>
    specialize (Hrel x y); tauto
  end.
Qed.

Local Lemma universe_layer_readback U i :
  (forall j a b R, j < i -> U j a b R -> type_quotes_agree a b) ->
  (forall j a b m n, j < i -> neutrals_agree m n ->
     exists R, U j (d_neut a m) (d_neut b n) R) ->
  forall a b R, universe_layer U i a b R -> layer_readback a b R.
Proof.
  intros HU Hneutral a b R H.
  induction H as
    [j R Hj Hrel
    |R Hrel
    |a a' ρ ρ' B B' R S T Hdom IHdom Htotal Hcod IHcod Hrel
    |a a' ρ ρ' B B' R S T Hdom IHdom Htotal Hcod IHcod Hrel
    |a a' m n m' n' R S Hdom IHdom Hm Hn Hrel
    |a a' m n R Hne Hrel].
  - repeat split.
    + intro s. exists (nf_typ j). auto using read_typ_univ.
    + intros x y Hxy s. apply Hrel in Hxy.
      destruct Hxy as [S HS].
      destruct (HU _ _ _ _ Hj HS s) as [N [Hl Hr]].
      exists N. auto using read_nf_type.
    + intros m n Hne. apply Hrel. now apply Hneutral.
  - repeat split.
    + intro s. exists nf_nat. auto using read_typ_nat.
    + intros x y Hxy. apply natural_values_readback.
      now apply Hrel.
    + intros m n Hne. apply Hrel, natural_values_neutral.
      exists d_nat, d_nat, m, n. auto.
  - destruct IHdom as [Hty [Hval Hreflect]].
    assert (Hfresh : forall s, R (d_neut a (d_var s)) (d_neut a' (d_var s)))
      by (intro s; apply Hreflect, related_variable).
    repeat split.
    + intro s.
      destruct (Hty s) as [A [HA HA']].
      destruct (Htotal _ _ (Hfresh s)) as [b [b' [Hb Hb']]].
      destruct (IHcod _ _ _ _ (Hfresh s) Hb Hb') as [HtyB _].
      destruct (HtyB (Datatypes.S s)) as [C [HC HC']].
      exists (nf_pi A C). eauto using read_typ_pi.
    + intros f g Hfg s. apply Hrel in Hfg.
      destruct (Hty s) as [A [HA HA']].
      destruct (Htotal _ _ (Hfresh s)) as [b [b' [Hb Hb']]].
      destruct (Hfg _ _ (Hfresh s)) as [u [v [Hu [Hv Huv]]]].
      destruct (IHcod _ _ _ _ (Hfresh s) Hb Hb') as [_ [HvalB _]].
      destruct (HvalB _ _ Huv (Datatypes.S s)) as [M [HM HM']].
      exists (nf_fn A M). eauto using read_nf_fn.
    + intros m n Hne. apply Hrel.
      intros x y Hxy.
      destruct (Htotal _ _ Hxy) as [b [b' [Hb Hb']]].
      exists (d_neut b (d_app m (d_dom a x))),
        (d_neut b' (d_app n (d_dom a' y))).
      split; [now apply eval_app_neut |].
      split; [now apply eval_app_neut |].
      destruct (IHcod _ _ _ _ Hxy Hb Hb') as [_ [_ HreflectB]].
      apply HreflectB, related_neutral_application; auto.
  - destruct IHdom as [Hty [Hval Hreflect]].
    assert (Hfresh : forall s, R (d_neut a (d_var s)) (d_neut a' (d_var s)))
      by (intro s; apply Hreflect, related_variable).
    repeat split.
    + intro s.
      destruct (Hty s) as [A [HA HA']].
      destruct (Htotal _ _ (Hfresh s)) as [b [b' [Hb Hb']]].
      destruct (IHcod _ _ _ _ (Hfresh s) Hb Hb') as [HtyB _].
      destruct (HtyB (Datatypes.S s)) as [C [HC HC']].
      exists (nf_sigma A C). eauto using read_typ_sigma.
    + intros p qv Hpq s. apply Hrel in Hpq.
      destruct Hpq as [x [y [u [v [Hx [Hy [Hu [Hv [Hxy Huv]]]]]]]]].
      destruct (Hty s) as [A [HA HA']].
      destruct (Htotal _ _ (Hfresh s)) as [b [b' [Hb Hb']]].
      destruct (IHcod _ _ _ _ (Hfresh s) Hb Hb') as [HtyB _].
      destruct (HtyB (Datatypes.S s)) as [C [HC HC']].
      destruct (Htotal _ _ Hxy) as [c [c' [Hc Hc']]].
      destruct (IHcod _ _ _ _ Hxy Hc Hc') as [_ [HvalB _]].
      destruct (Hval _ _ Hxy s) as [M [HM HM']].
      destruct (HvalB _ _ Huv s) as [N [HN HN']].
      exists (nf_pair M A N C). eauto using read_nf_sigma.
    + intros m n Hne. apply Hrel.
      assert (Hxy : R (d_neut a (d_fst m)) (d_neut a' (d_fst n)))
        by (apply Hreflect, related_neutral_fst; exact Hne).
      destruct (Htotal _ _ Hxy) as [b [b' [Hb Hb']]].
      exists (d_neut a (d_fst m)), (d_neut a' (d_fst n)),
        (d_neut b (d_snd m)), (d_neut b' (d_snd n)).
      repeat split; auto using eval_fst_neut, eval_snd_neut.
      destruct (IHcod _ _ _ _ Hxy Hb Hb') as [_ [_ HreflectB]].
      apply HreflectB, related_neutral_snd. exact Hne.
  - destruct IHdom as [Hty [Hval Hreflect]].
    repeat split.
    + intro s.
      destruct (Hty s) as [A [HA HA']].
      destruct (Hval _ _ Hm s) as [M [HM HM']].
      destruct (Hval _ _ Hn s) as [N [HN HN']].
      exists (nf_eq A M N). eauto using read_typ_eq.
    + intros p qv Hpq s. apply Hrel in Hpq.
      destruct Hpq as [[c [c' [k [k' [-> [-> Hne]]]]]] | [x [y [-> [-> [Hxy _]]]]]].
      * destruct (Hne s) as [N [Hl Hr]].
        exists (nf_neut N). eauto using read_nf_eq_neut.
      * destruct (Hty s) as [A [HA HA']].
        destruct (Hval _ _ Hxy s) as [N [HN HN']].
        exists (nf_refl A N). eauto using read_nf_refl.
    + intros k k' Hne. apply Hrel. left.
      exists (d_eq a m n), (d_eq a' m' n'), k, k'. auto.
  - repeat split.
    + intro s. destruct (Hne s) as [N [Hl Hr]].
      exists (nf_neut N). eauto using read_typ_neut.
    + intros x y Hxy s. apply Hrel in Hxy.
      destruct Hxy as [c [c' [k [k' [-> [-> Hk]]]]]].
      destruct (Hk s) as [N [Hl Hr]].
      exists (nf_neut N). eauto using read_nf_neut.
    + intros k k' Hk. apply Hrel.
      exists (d_neut a m), (d_neut a' n), k, k'. auto.
Qed.

Local Fixpoint lower_universes (i : nat) : universe_family :=
  match i with
  | 0 => fun _ _ _ _ => False
  | S smaller => fun j =>
      if Nat.eq_dec j smaller then universe_layer (lower_universes smaller) smaller
      else lower_universes smaller j
  end.

Local Definition semantic_type i := universe_layer (lower_universes i) i.

Local Lemma lower_universes_lookup i j a b R :
  j < i -> (lower_universes i j a b R <-> semantic_type j a b R).
Proof.
  induction i as [|i IH]; intro Hj; [lia |].
  cbn [lower_universes]. destruct (Nat.eq_dec j i) as [-> | Hne].
  - try unfold relations_agree; intros; reflexivity.
  - apply IH. lia.
Qed.

Local Lemma semantic_type_readback i a b R :
  semantic_type i a b R -> layer_readback a b R.
Proof.
  revert a b R. induction i using lt_wf_ind.
  intros a b R Hlayer. apply (universe_layer_readback (lower_universes i) i).
  - intros j x y S Hj HS.
    apply lower_universes_lookup in HS; [ | exact Hj ].
    exact (proj1 (H j Hj _ _ _ HS)).
  - intros j x y m n Hj Hne.
    exists neutral_values_agree. apply lower_universes_lookup; [exact Hj |].
    apply layer_neutral; [exact Hne | unfold relations_agree; intros; reflexivity].
  - exact Hlayer.
Qed.

Local Lemma layer_monotone U V i j :
  i <= j ->
  (forall k a b R, k < i -> (U k a b R <-> V k a b R)) ->
  forall a b R, universe_layer U i a b R -> universe_layer V j a b R.
Proof.
  intros Hij HUV a b R H.
  induction H as
    [k R Hk Hrel
    |R Hrel
    |a a' ρ ρ' B B' R S T HA IHA Htotal Hcod IHcod Hrel
    |a a' ρ ρ' B B' R S T HA IHA Htotal Hcod IHcod Hrel
    |a a' m n m' n' R S HA IHA Hm Hn Hrel
    |a a' m n R Hne Hrel].
  - apply layer_universe; [lia |].
    intros x y. specialize (Hrel x y). unfold universe_values_agree in *.
    split; intro Hxy.
    + apply Hrel in Hxy. destruct Hxy as [S HS].
      exists S. apply HUV; assumption.
    + apply Hrel. destruct Hxy as [S HS].
      exists S. apply HUV; assumption.
  - now apply layer_natural.
  - eapply layer_function; eassumption.
  - eapply layer_pair; eassumption.
  - eapply layer_equality; eassumption.
  - now apply layer_neutral.
Qed.

Local Lemma semantic_type_cumulative i j a b R :
  i <= j -> semantic_type i a b R -> semantic_type j a b R.
Proof.
  intros Hle H. eapply layer_monotone; try eassumption.
  intros k x y S Hk. rewrite !lower_universes_lookup by lia. reflexivity.
Qed.

Local Lemma agreement_symmetric R S :
  relations_agree R S -> relations_agree S R.
Proof. intros H x y. specialize (H x y). tauto. Qed.

Local Lemma agreement_transitive R S T :
  relations_agree R S -> relations_agree S T -> relations_agree R T.
Proof. intros H K x y. specialize (H x y). specialize (K x y). tauto. Qed.

Local Lemma function_relation_congruence R R' S S' :
  relations_agree R R' ->
  (forall x y, R x y -> relations_agree (S x y) (S' x y)) ->
  relations_agree (function_values_agree R S) (function_values_agree R' S').
Proof.
  intros Hdom Hcod f g. split; intros Hfg x y Hxy.
  - assert (Hxy' : R x y) by (apply Hdom; exact Hxy).
    destruct (Hfg _ _ Hxy') as [u [v [Hu [Hv Huv]]]].
    exists u, v. split; [exact Hu |]. split; [exact Hv |].
    apply (Hcod _ _ Hxy'). exact Huv.
  - assert (Hxy' : R' x y) by (apply Hdom; exact Hxy).
    destruct (Hfg _ _ Hxy') as [u [v [Hu [Hv Huv]]]].
    exists u, v. split; [exact Hu |]. split; [exact Hv |].
    apply (Hcod _ _ Hxy). exact Huv.
Qed.

Local Lemma pair_relation_congruence R R' S S' :
  relations_agree R R' ->
  (forall x y, R x y -> relations_agree (S x y) (S' x y)) ->
  relations_agree (pair_values_agree R S) (pair_values_agree R' S').
Proof.
  intros Hdom Hcod p qv. split;
    intros [x [y [u [v [Hx [Hy [Hu [Hv [Hxy Huv]]]]]]]]];
    exists x, y, u, v; repeat split; try assumption.
  - now apply Hdom.
  - now apply (Hcod _ _ Hxy).
  - now apply Hdom.
  - apply (Hcod x y ltac:(now apply Hdom)). exact Huv.
Qed.

Local Lemma equality_relation_congruence R R' m n :
  relations_agree R R' ->
  relations_agree (equality_values_agree R m n) (equality_values_agree R' m n).
Proof.
  intros Heq p qv. split;
    intros [Hne | [x [y [-> [-> [Hxy [Hxm Hxn]]]]]]];
    try (left; exact Hne);
    right; exists x, y; repeat split; try reflexivity; now apply Heq.
Qed.

Local Lemma layers_agree_on_left U i a b R :
  universe_layer U i a b R ->
  forall c S, universe_layer U i a c S -> relations_agree R S.
Proof.
  intro H. induction H as
    [k R Hk Hrel
    |R Hrel
    |a b ρ ρ' B B' R S T HA IHA Htotal Hcod IHcod Hrel
    |a b ρ ρ' B B' R S T HA IHA Htotal Hcod IHcod Hrel
    |a b m n m' n' R S HA IHA Hm Hn Hrel
    |a b m n R Hne Hrel]; intros c P HP; inversion HP; subst; clear HP.
  all: eapply agreement_transitive; [exact Hrel |].
  all: eapply agreement_transitive; [ | apply agreement_symmetric; eassumption].
  - try unfold relations_agree; intros; reflexivity.
  - try unfold relations_agree; intros; reflexivity.
  - apply function_relation_congruence.
    + eapply IHA; eassumption.
    + intros x y Hxy.
      assert (HR' : R0 x y) by (apply (IHA _ _ ltac:(eassumption)); assumption).
      destruct (Htotal _ _ Hxy) as [u [v [Hu Hv]]].
      match goal with
      | H : forall x y, R0 x y -> exists u v, eval_exp B (extend_env ρ x) u /\ _ |- _ =>
          destruct (H _ _ HR') as [u' [w [Hu' Hw]]]
      end.
      reconcile_values.
      eapply IHcod; try eassumption.
      eauto.
  - apply pair_relation_congruence.
    + eapply IHA; eassumption.
    + intros x y Hxy.
      assert (HR' : R0 x y) by (apply (IHA _ _ ltac:(eassumption)); assumption).
      destruct (Htotal _ _ Hxy) as [u [v [Hu Hv]]].
      match goal with
      | H : forall x y, R0 x y -> exists u v, eval_exp B (extend_env ρ x) u /\ _ |- _ =>
          destruct (H _ _ HR') as [u' [w [Hu' Hw]]]
      end.
      reconcile_values.
      eapply IHcod; try eassumption.
      eauto.
  - apply equality_relation_congruence. eapply IHA; eassumption.
  - try unfold relations_agree; intros; reflexivity.
Qed.

Local Definition partial_equivalence {V : Type} (R : V -> V -> Prop) :=
  (forall x y, R x y -> R y x) /\
  (forall x y z, R x y -> R y z -> R x z).

Local Lemma per_left {V : Type} (R : V -> V -> Prop) x y :
  partial_equivalence R -> R x y -> R x x.
Proof. intros [Hsym Htrans] H. eauto. Qed.

Local Lemma per_right {V : Type} (R : V -> V -> Prop) x y :
  partial_equivalence R -> R x y -> R y y.
Proof. intros [Hsym Htrans] H. eauto. Qed.

Local Lemma per_agreement R S :
  relations_agree R S -> partial_equivalence S -> partial_equivalence R.
Proof.
  intros Heq [Hsym Htrans]. split.
  - intros x y H. now apply Heq, Hsym, Heq.
  - intros x y z Hxy Hyz. apply Heq. apply (Htrans x y z); now apply Heq.
Qed.

Local Lemma neutrals_agree_symmetric m n :
  neutrals_agree m n -> neutrals_agree n m.
Proof. intros H s. destruct (H s) as [N [? ?]]. eauto. Qed.

Local Lemma neutrals_agree_transitive m n k :
  neutrals_agree m n -> neutrals_agree n k -> neutrals_agree m k.
Proof.
  intros H K s.
  destruct (H s) as [N [Hm Hn]]. destruct (K s) as [N' [Hn' Hk]].
  replace N' with N in Hk.
  - eauto.
  - eapply (proj1 (proj2 readback_deterministic)); eassumption.
Qed.

Local Lemma neutral_values_per : partial_equivalence neutral_values_agree.
Proof.
  split.
  - intros x y [a [b [m [n [-> [-> Hne]]]]]].
    exists b, a, n, m. auto using neutrals_agree_symmetric.
  - intros x y z [a [b [m [n [-> [-> Hmn]]]]]]
       [b' [c [n' [k [E [-> Hnk]]]]]].
    inversion E; subst.
    exists a, c, m, k. eauto using neutrals_agree_transitive.
Qed.

Local Ltac eliminate_impossible_neutral :=
  match goal with
  | H : neutral_values_agree d_zero _ |- _ =>
      destruct H as [? [? [? [? [E _]]]]]; discriminate E
  | H : neutral_values_agree _ d_zero |- _ =>
      destruct H as [? [? [? [? [_ [E _]]]]]]; discriminate E
  | H : neutral_values_agree (d_succ _) _ |- _ =>
      destruct H as [? [? [? [? [E _]]]]]; discriminate E
  | H : neutral_values_agree _ (d_succ _) |- _ =>
      destruct H as [? [? [? [? [_ [E _]]]]]]; discriminate E
  | H : neutral_values_agree (d_refl _) _ |- _ =>
      destruct H as [? [? [? [? [E _]]]]]; discriminate E
  | H : neutral_values_agree _ (d_refl _) |- _ =>
      destruct H as [? [? [? [? [_ [E _]]]]]]; discriminate E
  end.

Local Lemma natural_values_per : partial_equivalence natural_values_agree.
Proof.
  destruct neutral_values_per as [Hsym Htrans]. split.
  - intros x y H. induction H; eauto using natural_values_zero,
      natural_values_succ, natural_values_neutral.
  - intros x y z H. revert z. induction H; intros z K; inversion K; subst;
      try eliminate_impossible_neutral;
      eauto using natural_values_zero, natural_values_succ, natural_values_neutral.
Qed.

Local Lemma equality_values_per R m n :
  partial_equivalence R -> partial_equivalence (equality_values_agree R m n).
Proof.
  intros [Hsym Htrans]. destruct neutral_values_per as [Hns Hnt]. split.
  - intros p qv [Hne | [x [y [-> [-> [Hxy [Hxm Hxn]]]]]]].
    + left. auto.
    + right. exists y, x. repeat split; eauto.
  - intros p qv t H K.
    destruct H as [Hne | [x [y [-> [-> [Hxy [Hxm Hxn]]]]]]];
      destruct K as [Hne' | [y' [z [E [-> [Hyz _]]]]]]; subst;
      try eliminate_impossible_neutral.
    + left. eauto.
    + inversion E; subst. right. exists x, z. repeat split; eauto.
Qed.

Local Lemma codomains_agree_on_left U i ρ ρ' B B' R S :
  (forall x y, R x y -> exists b b',
    eval_exp B (extend_env ρ x) b /\ eval_exp B' (extend_env ρ' y) b') ->
  (forall x y b b', R x y ->
    eval_exp B (extend_env ρ x) b ->
    eval_exp B' (extend_env ρ' y) b' ->
    universe_layer U i b b' (S x y)) ->
  forall x y z, R x y -> R x z -> relations_agree (S x y) (S x z).
Proof.
  intros Htotal Hcod x y z Hxy Hxz.
  destruct (Htotal _ _ Hxy) as [b [c [Hb Hc]]].
  destruct (Htotal _ _ Hxz) as [b' [d [Hb' Hd]]].
  reconcile_values.
  eapply layers_agree_on_left; eauto.
Qed.

Local Lemma codomains_agree_on_right U i ρ ρ' B B' R S :
  (forall x y, R x y -> exists b b',
    eval_exp B (extend_env ρ x) b /\ eval_exp B' (extend_env ρ' y) b') ->
  (forall x y b b', R x y ->
    eval_exp B (extend_env ρ x) b ->
    eval_exp B' (extend_env ρ' y) b' ->
    forall c T, universe_layer U i c b' T -> relations_agree (S x y) T) ->
  (forall x y b b', R x y ->
    eval_exp B (extend_env ρ x) b ->
    eval_exp B' (extend_env ρ' y) b' ->
    universe_layer U i b b' (S x y)) ->
  forall x y z, R x z -> R y z -> relations_agree (S x z) (S y z).
Proof.
  intros Htotal IHcod Hcod x y z Hxz Hyz.
  destruct (Htotal _ _ Hxz) as [b [c [Hb Hc]]].
  destruct (Htotal _ _ Hyz) as [b' [d [Hb' Hd]]].
  reconcile_values.
  eapply IHcod; eauto.
Qed.

Local Lemma per_family_agreement (R : value_relation) (S : domain -> domain -> value_relation) :
  partial_equivalence R ->
  (forall x y z, R x y -> R x z -> relations_agree (S x y) (S x z)) ->
  (forall x y z, R x z -> R y z -> relations_agree (S x z) (S y z)) ->
  forall x y z w, R x y -> R z w -> R x z -> relations_agree (S x y) (S z w).
Proof.
  intros HR Hl Hr x y z w Hxy Hzw Hxz.
  assert (Hxw : R x w) by (eapply (proj2 HR); eassumption).
  eapply agreement_transitive; [eapply Hl | eapply Hr]; eassumption.
Qed.

Local Lemma function_values_per R S :
  partial_equivalence R ->
  (forall x y, R x y -> partial_equivalence (S x y)) ->
  (forall x y z w, R x y -> R z w -> R x z -> relations_agree (S x y) (S z w)) ->
  partial_equivalence (function_values_agree R S).
Proof.
  intros HR HS Hstable. split.
  - intros f g Hfg x y Hxy.
    assert (Hyx : R y x) by (apply (proj1 HR); exact Hxy).
    destruct (Hfg _ _ Hyx) as [u [v [Hu [Hv Huv]]]].
    exists v, u. split; [exact Hv |]. split; [exact Hu |].
    apply (proj1 (HS _ _ Hxy)).
    apply (Hstable _ _ _ _ Hyx Hxy Hyx). exact Huv.
  - intros f g h Hfg Hgh x z Hxz.
    pose proof (per_left _ _ _ HR Hxz) as Hxx.
    destruct (Hfg _ _ Hxx) as [u [v [Hu [Hv Huv]]]].
    destruct (Hgh _ _ Hxz) as [v' [w [Hv' [Hw Hvw]]]].
    reconcile_values.
    exists u, w. split; [exact Hu |]. split; [exact Hw |].
    eapply (proj2 (HS _ _ Hxz)); [ | exact Hvw].
    apply (Hstable _ _ _ _ Hxx Hxz Hxx). exact Huv.
Qed.

Local Lemma pair_values_per R S :
  partial_equivalence R ->
  (forall x y, R x y -> partial_equivalence (S x y)) ->
  (forall x y z w, R x y -> R z w -> R x z -> relations_agree (S x y) (S z w)) ->
  partial_equivalence (pair_values_agree R S).
Proof.
  intros HR HS Hstable. split.
  - intros p qv [x [y [u [v [Hx [Hy [Hu [Hv [Hxy Huv]]]]]]]]].
    assert (Hyx : R y x) by (apply (proj1 HR); exact Hxy).
    exists y, x, v, u. repeat split; try assumption.
    apply (proj1 (HS _ _ Hyx)).
    apply (Hstable _ _ _ _ Hxy Hyx Hxy). exact Huv.
  - intros p qv t [x [y [u [v [Hx [Hy [Hu [Hv [Hxy Huv]]]]]]]]]
      [y' [z [v' [w [Hy' [Hz [Hv' [Hw [Hyz Hvw]]]]]]]]].
    reconcile_values.
    assert (Hxz : R x z) by (eapply (proj2 HR); eassumption).
    exists x, z, u, w. repeat split; try assumption.
    eapply (proj2 (HS _ _ Hxz)).
    + apply (Hstable _ _ _ _ Hxy Hxz (per_left _ _ _ HR Hxy)). exact Huv.
    + apply (Hstable _ _ _ _ Hyz Hxz (proj1 HR _ _ Hxy)). exact Hvw.
Qed.

Local Lemma equality_values_change_endpoints R m n m' n' :
  partial_equivalence R ->
  R m m' -> R n n' ->
  relations_agree (equality_values_agree R m n) (equality_values_agree R m' n').
Proof.
  intros [Hsym Htrans] Hm Hn p qv. split;
    intros [Hne | [x [y [-> [-> [Hxy [Hxm Hxn]]]]]]];
    try (left; exact Hne);
    right; exists x, y; repeat split; eauto.
Qed.

Local Lemma layers_agree_on_right_and_per U i :
  (forall j, j < i -> partial_equivalence (universe_values_agree U j)) ->
  forall a b R, universe_layer U i a b R ->
    partial_equivalence R /\
    (forall c S, universe_layer U i c b S -> relations_agree R S).
Proof.
  intros HU a b R H.
  induction H as
    [k R Hk Hrel
    |R Hrel
    |a b ρ ρ' B B' R S T HA IHA Htotal Hcod IHcod Hrel
    |a b ρ ρ' B B' R S T HA IHA Htotal Hcod IHcod Hrel
    |a b m n m' n' R S HA IHA Hm Hn Hrel
    |a b m n R Hne Hrel].
  - split.
    + eauto using per_agreement.
    + intros c P HP. inversion HP; subst.
      eapply agreement_transitive; [exact Hrel |].
      apply agreement_symmetric. assumption.
  - split.
    + eauto using per_agreement, natural_values_per.
    + intros c P HP. inversion HP; subst.
      eapply agreement_transitive; [exact Hrel |].
      apply agreement_symmetric. assumption.
  - destruct IHA as [HR HRcoh].
    split.
    + apply (per_agreement _ _ Hrel), function_values_per.
      * exact HR.
      * intros x y Hxy.
        destruct (Htotal _ _ Hxy) as [u [v [Hu Hv]]].
        exact (proj1 (IHcod _ _ _ _ Hxy Hu Hv)).
      * apply per_family_agreement; [assumption | |].
        -- eapply codomains_agree_on_left; eassumption.
        -- eapply codomains_agree_on_right; [exact Htotal | | exact Hcod].
           intros x y u v Hxy Hx Hy. apply (proj2 (IHcod _ _ _ _ Hxy Hx Hy)).
    + intros c P HP. inversion HP; subst; clear HP.
      eapply agreement_transitive; [exact Hrel |].
      eapply agreement_transitive; [ | apply agreement_symmetric; eassumption].
      apply function_relation_congruence.
      * eapply HRcoh; eassumption.
      * intros x y Hxy.
        assert (HR' : R0 x y) by (apply (HRcoh _ _ ltac:(eassumption)); assumption).
        destruct (Htotal _ _ Hxy) as [u [v [Hu Hv]]].
        match goal with
        | H : forall x y, R0 x y -> exists u v, _ /\ eval_exp B' (extend_env ρ' y) v |- _ =>
            destruct (H _ _ HR') as [w [v' [Hw Hv']]]
        end.
        reconcile_values.
        eapply (proj2 (IHcod _ _ _ _ Hxy Hu ltac:(eassumption))).
        eauto.
  - destruct IHA as [HR HRcoh].
    split.
    + apply (per_agreement _ _ Hrel), pair_values_per.
      * exact HR.
      * intros x y Hxy.
        destruct (Htotal _ _ Hxy) as [u [v [Hu Hv]]].
        exact (proj1 (IHcod _ _ _ _ Hxy Hu Hv)).
      * apply per_family_agreement; [assumption | |].
        -- eapply codomains_agree_on_left; eassumption.
        -- eapply codomains_agree_on_right; [exact Htotal | | exact Hcod].
           intros x y u v Hxy Hx Hy. apply (proj2 (IHcod _ _ _ _ Hxy Hx Hy)).
    + intros c P HP. inversion HP; subst; clear HP.
      eapply agreement_transitive; [exact Hrel |].
      eapply agreement_transitive; [ | apply agreement_symmetric; eassumption].
      apply pair_relation_congruence.
      * eapply HRcoh; eassumption.
      * intros x y Hxy.
        assert (HR' : R0 x y) by (apply (HRcoh _ _ ltac:(eassumption)); assumption).
        destruct (Htotal _ _ Hxy) as [u [v [Hu Hv]]].
        match goal with
        | H : forall x y, R0 x y -> exists u v, _ /\ eval_exp B' (extend_env ρ' y) v |- _ =>
            destruct (H _ _ HR') as [w [v' [Hw Hv']]]
        end.
        reconcile_values.
        eapply (proj2 (IHcod _ _ _ _ Hxy Hu ltac:(eassumption))).
        eauto.
  - destruct IHA as [HR HRcoh].
    split.
    + eauto using per_agreement, equality_values_per.
    + intros c P HP. inversion HP; subst; clear HP.
      eapply agreement_transitive; [exact Hrel |].
      eapply agreement_transitive; [ | apply agreement_symmetric; eassumption].
      assert (Heq : relations_agree R R0) by (eapply HRcoh; eassumption).
      eapply agreement_transitive; [ | apply equality_relation_congruence; exact Heq ].
      apply equality_values_change_endpoints; [assumption | |];
        (eapply (proj2 HR); [eassumption | apply (proj1 HR), Heq; eassumption]).
  - split.
    + eauto using per_agreement, neutral_values_per.
    + intros c P HP. inversion HP; subst.
      eapply agreement_transitive; [exact Hrel |].
      apply agreement_symmetric. assumption.
Qed.

Local Lemma layer_per U i :
  (forall j, j < i -> partial_equivalence (universe_values_agree U j)) ->
  forall a b R, universe_layer U i a b R -> partial_equivalence R.
Proof.
  intros H a b R HT. exact (proj1 (layers_agree_on_right_and_per _ _ H _ _ _ HT)).
Qed.

Local Lemma layers_agree_on_right U i :
  (forall j, j < i -> partial_equivalence (universe_values_agree U j)) ->
  forall a b c R S, universe_layer U i a b R ->
    universe_layer U i c b S -> relations_agree R S.
Proof.
  intros H a b c R S HT HT'.
  exact (proj2 (layers_agree_on_right_and_per _ _ H _ _ _ HT) _ _ HT').
Qed.

Local Lemma layer_codomain_per_family U i a b ρ ρ' B B' R S :
  (forall j, j < i -> partial_equivalence (universe_values_agree U j)) ->
  universe_layer U i a b R ->
  (forall x y, R x y -> exists b b',
    eval_exp B (extend_env ρ x) b /\ eval_exp B' (extend_env ρ' y) b') ->
  (forall x y b b', R x y ->
    eval_exp B (extend_env ρ x) b ->
    eval_exp B' (extend_env ρ' y) b' ->
    universe_layer U i b b' (S x y)) ->
  forall x y z w, R x y -> R z w -> R x z -> relations_agree (S x y) (S z w).
Proof.
  intros H HA Htotal Hcod. apply per_family_agreement.
  - eauto using layer_per.
  - eapply codomains_agree_on_left; eassumption.
  - eapply codomains_agree_on_right; [exact Htotal | | exact Hcod].
    intros x y u v Hxy Hx Hy c T HT.
    eapply layers_agree_on_right; [exact H | apply Hcod; eassumption | exact HT].
Qed.

Local Lemma layer_symmetric U i :
  (forall j, j < i -> partial_equivalence (universe_values_agree U j)) ->
  forall a b R, universe_layer U i a b R -> universe_layer U i b a R.
Proof.
  intros HU a b R H.
  induction H as
    [k R Hk Hrel
    |R Hrel
    |a b ρ ρ' B B' R S T HA IHA Htotal Hcod IHcod Hrel
    |a b ρ ρ' B B' R S T HA IHA Htotal Hcod IHcod Hrel
    |a b m n m' n' R S HA IHA Hm Hn Hrel
    |a b m n R Hne Hrel].
  - now apply layer_universe.
  - now apply layer_natural.
  - pose proof (layer_per _ _ HU _ _ _ HA) as [Hsym Htrans].
    eapply layer_function with (R := R) (S := fun x y => S y x).
    + exact IHA.
    + intros x y Hxy. destruct (Htotal _ _ (Hsym _ _ Hxy)) as [u [v [Hu Hv]]].
      exists v, u. auto.
    + intros x y v u Hxy Hv Hu. eauto.
    + eapply agreement_transitive; [exact Hrel |].
      apply function_relation_congruence; [intros x y; reflexivity |].
      intros x y Hxy.
      eapply layer_codomain_per_family; try eassumption; eauto.
  - pose proof (layer_per _ _ HU _ _ _ HA) as [Hsym Htrans].
    eapply layer_pair with (R := R) (S := fun x y => S y x).
    + exact IHA.
    + intros x y Hxy. destruct (Htotal _ _ (Hsym _ _ Hxy)) as [u [v [Hu Hv]]].
      exists v, u. auto.
    + intros x y v u Hxy Hv Hu. eauto.
    + eapply agreement_transitive; [exact Hrel |].
      apply pair_relation_congruence; [intros x y; reflexivity |].
      intros x y Hxy.
      eapply layer_codomain_per_family; try eassumption; eauto.
  - pose proof (layer_per _ _ HU _ _ _ HA) as HR.
    eapply layer_equality; [exact IHA | apply (proj1 HR); exact Hm |
      apply (proj1 HR); exact Hn |].
    eapply agreement_transitive; [exact Hrel |].
    eauto using equality_values_change_endpoints.
  - auto using layer_neutral, neutrals_agree_symmetric.
Qed.

Local Lemma layer_transitive U i :
  (forall j, j < i -> partial_equivalence (universe_values_agree U j)) ->
  forall a b R, universe_layer U i a b R ->
  forall c S, universe_layer U i b c S -> universe_layer U i a c R.
Proof.
  intros HU a b R H.
  induction H as
    [k R Hk Hrel
    |R Hrel
    |a b ρ ρ' B B' R S T HA IHA Htotal Hcod IHcod Hrel
    |a b ρ ρ' B B' R S T HA IHA Htotal Hcod IHcod Hrel
    |a b m n m' n' R S HA IHA Hm Hn Hrel
    |a b m n R Hne Hrel]; intros c P HP.
  - inversion HP; subst. now apply layer_universe.
  - inversion HP; subst. now apply layer_natural.
  - inversion HP as [ | |a0 c0 θ0 θ C0 C Q V W Hdom Ht Hc Hr | | |]; subst.
    assert (HRQ : relations_agree R Q)
      by (eapply layers_agree_on_left; [apply layer_symmetric; eassumption | exact Hdom]).
    pose proof (layer_per _ _ HU _ _ _ HA) as HR.
    eapply layer_function with (R := R) (S := S).
    + eapply IHA; eassumption.
    + intros x y Hxy.
      assert (Hyy : Q y y) by (apply HRQ; exact (per_right _ _ _ HR Hxy)).
      destruct (Htotal _ _ Hxy) as [u [v [Hu Hv]]].
      destruct (Ht _ _ Hyy) as [v' [w [Hv' Hw]]].
      eauto.
    + intros x y u w Hxy Hu Hw.
      assert (Hyy : Q y y) by (apply HRQ; exact (per_right _ _ _ HR Hxy)).
      destruct (Htotal _ _ Hxy) as [u' [v [Hu' Hv]]].
      refine (IHcod x y u v Hxy Hu Hv _ _ _).
      eapply Hc; eassumption.
    + exact Hrel.
  - inversion HP as [ | | |a0 c0 θ0 θ C0 C Q V W Hdom Ht Hc Hr | |]; subst.
    assert (HRQ : relations_agree R Q)
      by (eapply layers_agree_on_left; [apply layer_symmetric; eassumption | exact Hdom]).
    pose proof (layer_per _ _ HU _ _ _ HA) as HR.
    eapply layer_pair with (R := R) (S := S).
    + eapply IHA; eassumption.
    + intros x y Hxy.
      assert (Hyy : Q y y) by (apply HRQ; exact (per_right _ _ _ HR Hxy)).
      destruct (Htotal _ _ Hxy) as [u [v [Hu Hv]]].
      destruct (Ht _ _ Hyy) as [v' [w [Hv' Hw]]].
      eauto.
    + intros x y u w Hxy Hu Hw.
      assert (Hyy : Q y y) by (apply HRQ; exact (per_right _ _ _ HR Hxy)).
      destruct (Htotal _ _ Hxy) as [u' [v [Hu' Hv]]].
      refine (IHcod x y u v Hxy Hu Hv _ _ _).
      eapply Hc; eassumption.
    + exact Hrel.
  - inversion HP as [ | | | |a0 c0 u0 v0 u v Q W Hdom Hu Hv Hr |]; subst.
    assert (HRQ : relations_agree R Q)
      by (eapply layers_agree_on_left; [apply layer_symmetric; eassumption | exact Hdom]).
    pose proof (layer_per _ _ HU _ _ _ HA) as HR.
    eapply layer_equality with (R := R).
    + eapply IHA; eassumption.
    + eapply (proj2 HR); [exact Hm | now apply HRQ].
    + eapply (proj2 HR); [exact Hn | now apply HRQ].
    + exact Hrel.
  - inversion HP; subst. eauto using layer_neutral, neutrals_agree_transitive.
Qed.

Local Lemma semantic_universe_per i :
  partial_equivalence (fun a b => exists R, semantic_type i a b R).
Proof.
  induction i using lt_wf_ind.
  assert (Hlower : forall j, j < i ->
    partial_equivalence (universe_values_agree (lower_universes i) j)).
  {
    intros j Hj. eapply per_agreement; [ | apply H; exact Hj].
    intros a b. unfold universe_values_agree. setoid_rewrite lower_universes_lookup; auto; reflexivity.
  }
  split.
  - intros a b [R Hlayer]. exists R.
    exact (layer_symmetric _ _ Hlower _ _ _ Hlayer).
  - intros a b c [R HA] [S HB]. exists R.
    exact (layer_transitive _ _ Hlower _ _ _ HA _ _ HB).
Qed.

Local Lemma lower_values_per i j :
  j < i -> partial_equivalence (universe_values_agree (lower_universes i) j).
Proof.
  intro Hj. eapply per_agreement; [ | apply semantic_universe_per with (i := j)].
  intros a b. unfold universe_values_agree. setoid_rewrite lower_universes_lookup; auto; reflexivity.
Qed.

Local Lemma semantic_value_per i a b R :
  semantic_type i a b R -> partial_equivalence R.
Proof. exact (layer_per _ _ (lower_values_per i) a b R). Qed.

Local Lemma semantic_type_sym i a b R :
  semantic_type i a b R -> semantic_type i b a R.
Proof. exact (layer_symmetric _ _ (lower_values_per i) a b R). Qed.

Local Lemma semantic_type_trans i a b c R S :
  semantic_type i a b R ->
  semantic_type i b c S ->
  semantic_type i a c R.
Proof. intros H K. exact (layer_transitive _ _ (lower_values_per i) _ _ _ H _ _ K). Qed.

Local Lemma semantic_types_agree_on_left i j a b c R S :
  semantic_type i a b R ->
  semantic_type j a c S ->
  relations_agree R S.
Proof.
  intros HA HB.
  refine (layers_agree_on_left (lower_universes (Nat.max i j)) (Nat.max i j)
    a b R _ c S _).
  - exact (semantic_type_cumulative _ _ _ _ _ (Nat.le_max_l _ _) HA).
  - exact (semantic_type_cumulative _ _ _ _ _ (Nat.le_max_r _ _) HB).
Qed.

Local Lemma semantic_types_agree_on_right i j a b c R S :
  semantic_type i a b R ->
  semantic_type j c b S ->
  relations_agree R S.
Proof. eauto using semantic_types_agree_on_left, semantic_type_sym. Qed.

Local Definition closure_evaluations i ρ ρ' B B' x y b b' T :=
  eval_exp B (extend_env ρ x) b /\
  eval_exp B' (extend_env ρ' y) b' /\ semantic_type i b b' T.

Local Definition closure_relation i ρ ρ' B B' x y u v :=
  exists b b' T, closure_evaluations i ρ ρ' B B' x y b b' T /\ T u v.

Local Lemma closure_relation_agrees i ρ ρ' B B' x y b b' T :
  closure_evaluations i ρ ρ' B B' x y b b' T ->
  relations_agree T (closure_relation i ρ ρ' B B' x y).
Proof.
  intros [Hb [Hb' HT]] u v. split.
  - intro H. exists b, b', T. repeat split; assumption.
  - intros [c [c' [R [[Hc [Hc' HR]] Huv]]]].
    reconcile_values.
    apply (semantic_types_agree_on_left _ _ _ _ _ _ _ HT HR). exact Huv.
Qed.

Local Lemma semantic_closure_total i ρ ρ' B B' R :
  (forall x y, R x y ->
    exists b b' T, closure_evaluations i ρ ρ' B B' x y b b' T) ->
  forall x y, R x y -> exists b b',
    eval_exp B (extend_env ρ x) b /\ eval_exp B' (extend_env ρ' y) b'.
Proof.
  intros H x y Hxy.
  destruct (H _ _ Hxy) as [b [b' [T [Hb [Hb' HT]]]]]. eauto.
Qed.

Local Lemma semantic_closure_codomain i ρ ρ' B B' R :
  (forall x y, R x y ->
    exists b b' T, closure_evaluations i ρ ρ' B B' x y b b' T) ->
  forall x y b b', R x y ->
    eval_exp B (extend_env ρ x) b ->
    eval_exp B' (extend_env ρ' y) b' ->
    semantic_type i b b' (closure_relation i ρ ρ' B B' x y).
Proof.
  intros H x y b b' Hxy Hb Hb'.
  destruct (H _ _ Hxy) as [c [c' [T [Hc [Hc' HT]]]]].
  reconcile_values.
  eapply layer_relation_conversion; [exact HT |].
  eapply closure_relation_agrees. repeat split; eassumption.
Qed.

Local Lemma semantic_pi i a a' ρ ρ' B B' R :
  semantic_type i a a' R ->
  (forall x y, R x y ->
    exists b b' T, closure_evaluations i ρ ρ' B B' x y b b' T) ->
  semantic_type i (d_pi a ρ B) (d_pi a' ρ' B')
    (function_values_agree R (closure_relation i ρ ρ' B B')).
Proof.
  intros Hdom Hcod.
  eapply layer_function with (R := R) (S := closure_relation i ρ ρ' B B').
  - exact Hdom.
  - exact (semantic_closure_total _ _ _ _ _ _ Hcod).
  - exact (semantic_closure_codomain _ _ _ _ _ _ Hcod).
  - unfold relations_agree. reflexivity.
Qed.

Local Lemma semantic_sigma i a a' ρ ρ' B B' R :
  semantic_type i a a' R ->
  (forall x y, R x y ->
    exists b b' T, closure_evaluations i ρ ρ' B B' x y b b' T) ->
  semantic_type i (d_sigma a ρ B) (d_sigma a' ρ' B')
    (pair_values_agree R (closure_relation i ρ ρ' B B')).
Proof.
  intros Hdom Hcod.
  eapply layer_pair with (R := R) (S := closure_relation i ρ ρ' B B').
  - exact Hdom.
  - exact (semantic_closure_total _ _ _ _ _ _ Hcod).
  - exact (semantic_closure_codomain _ _ _ _ _ _ Hcod).
  - unfold relations_agree. reflexivity.
Qed.

(* Related environments interpret each dependent context entry. *)
Inductive related_environments : ctx -> env -> env -> Prop :=
| related_empty ρ ρ' : related_environments nil ρ ρ'
| related_extension Γ A ρ ρ' i a b R :
    related_environments Γ (drop_env ρ) (drop_env ρ') ->
    eval_exp A (drop_env ρ) a ->
    eval_exp A (drop_env ρ') b ->
    semantic_type i a b R ->
    R (ρ 0) (ρ' 0) ->
    related_environments (A :: Γ) ρ ρ'.

Local Lemma environments_extend Γ A ρ ρ' i a b R x y :
  related_environments Γ ρ ρ' ->
  eval_exp A ρ a -> eval_exp A ρ' b ->
  semantic_type i a b R -> R x y ->
  related_environments (A :: Γ) (extend_env ρ x) (extend_env ρ' y).
Proof. intros; econstructor; cbn; eassumption. Qed.

Local Lemma environments_per Γ : partial_equivalence (related_environments Γ).
Proof.
  induction Γ as [|A Γ [Hsym Htrans]].
  - split; intros; apply related_empty.
  - split.
    + intros ρ ρ' H.
      inversion H as [| Γ0 A0 η0 η1 i a b R Hr Ha Hb HT Hr0]; subst.
      eapply related_extension with (i := i) (R := R).
      * now apply Hsym.
      * exact Hb.
      * exact Ha.
      * exact (semantic_type_sym _ _ _ _ HT).
      * apply (proj1 (semantic_value_per _ _ _ _ HT)). exact Hr0.
    + intros ρ ρ' ρ'' H K.
      inversion H as [| Γ0 A0 η0 η1 i a b R Hr Ha Hb HT Hρ]; subst.
      inversion K as [| Γ0 A0 η0 η1 j b' c S Hr' Hb' Hc HS Hρ']; subst.
      reconcile_values.
      pose proof (semantic_types_agree_on_left _ _ _ _ _ _ _
        (semantic_type_sym _ _ _ _ HT) HS) as HE.
      eapply related_extension with (i := Nat.max i j) (R := R);
        try solve [eassumption | eauto].
      * eapply semantic_type_trans.
        -- eapply semantic_type_cumulative; [ | exact HT]. lia.
        -- eapply semantic_type_cumulative; [ | exact HS]. lia.
      * eapply (proj2 (semantic_value_per _ _ _ _ HT)); [exact Hρ |].
        now apply HE.
Qed.

Local Definition interpreted_term Γ A M N :=
  exists i, forall ρ ρ', related_environments Γ ρ ρ' ->
    exists a b R m n,
      eval_exp A ρ a /\ eval_exp A ρ' b /\ semantic_type i a b R /\
      eval_exp M ρ m /\ eval_exp N ρ' n /\ R m n.

Local Definition interpreted_type Γ i A B :=
  forall ρ ρ', related_environments Γ ρ ρ' ->
    exists a b R, eval_exp A ρ a /\ eval_exp B ρ' b /\ semantic_type i a b R.

Local Definition interpreted_substitution Γ Δ σ τ :=
  forall ρ ρ', related_environments Γ ρ ρ' ->
    exists η η', eval_sub σ ρ η /\ eval_sub τ ρ' η' /\
      related_environments Δ η η'.

Local Definition interpreted_subtyping Γ A B :=
  exists i, forall ρ ρ', related_environments Γ ρ ρ' ->
    exists a b c d R S,
      eval_exp A ρ a /\ eval_exp A ρ' b /\ semantic_type i a b R /\
      eval_exp B ρ c /\ eval_exp B ρ' d /\ semantic_type i c d S /\
      (forall x y, R x y -> S x y).

Local Lemma interpreted_types_as_terms Γ i A B :
  interpreted_type Γ i A B -> interpreted_term Γ (a_typ i) A B.
Proof.
  intro H. exists (S i). intros ρ ρ' Hρ.
  destruct (H _ _ Hρ) as [a [b [R [Ha [Hb Hab]]]]].
  exists (d_univ i), (d_univ i),
    (universe_values_agree (lower_universes (S i)) i), a, b.
  repeat split; auto using eval_exp_typ.
  - apply layer_universe; [lia | unfold relations_agree; reflexivity].
  - exists R. apply lower_universes_lookup; [lia | assumption].
Qed.

Local Lemma interpreted_terms_as_types Γ i A B :
  interpreted_term Γ (a_typ i) A B -> interpreted_type Γ i A B.
Proof.
  intros [j H] ρ ρ' Hρ.
  destruct (H _ _ Hρ) as [a [b [R [m [n [Ha [Hb [Hty [Hm [Hn Hmn]]]]]]]]]].
  inversion Ha; inversion Hb; subst.
  inversion Hty; subst.
  match goal with H : relations_agree R _ |- _ => apply H in Hmn end.
  destruct Hmn as [S HS]. apply lower_universes_lookup in HS; [ | assumption ].
  exists m, n, S. repeat split; assumption.
Qed.

Local Lemma initial_related_context Γ :
  (exists ρ, initial_env Γ ρ /\ related_environments Γ ρ ρ) ->
  forall A i, interpreted_type Γ i A A ->
  exists ρ, initial_env (A :: Γ) ρ /\ related_environments (A :: Γ) ρ ρ.
Proof.
  intros [ρ [Hinit Hρ]] A i H.
  destruct (H _ _ Hρ) as [a [b [R [Ha [Hb Hab]]]]].
  pose proof (eval_exp_deterministic _ _ _ Ha _ Hb). subst b.
  exists (extend_env ρ (d_neut a (d_var (length Γ)))). split.
  - now apply initial_env_cons.
  - eapply environments_extend; try eassumption.
    apply (proj2 (proj2 (semantic_type_readback _ _ _ _ Hab))).
    apply related_variable.
Qed.

Local Lemma shared_readback_of_interpreted_types Γ i A B :
  (exists ρ, initial_env Γ ρ /\ related_environments Γ ρ ρ) ->
  interpreted_type Γ i A B ->
  exists N, nbe_ty Γ A N /\ nbe_ty Γ B N.
Proof.
  intros [ρ [Hinit Hρ]] H.
  destruct (H _ _ Hρ) as [a [b [R [Ha [Hb Hab]]]]].
  destruct (proj1 (semantic_type_readback _ _ _ _ Hab) (length Γ))
    as [N [HN HN']].
  exists N. split; eauto using nbe_ty_run.
Qed.

Inductive interpreted_context : ctx -> Prop :=
| interpreted_empty : interpreted_context nil
| interpreted_extension Γ A i :
    interpreted_context Γ ->
    interpreted_type Γ i A A ->
    interpreted_context (A :: Γ).

Local Lemma interpreted_context_has_environment Γ :
  interpreted_context Γ ->
  exists ρ, initial_env Γ ρ /\ related_environments Γ ρ ρ.
Proof.
  induction 1.
  - exists empty_env. split; constructor.
  - eauto using initial_related_context.
Qed.

Local Lemma interpreted_lookup Γ x A :
  ctx_lookup x A Γ ->
  interpreted_context Γ ->
  interpreted_term Γ A (a_var x) (a_var x).
Proof.
  induction 1 as [A Γ | n A Γ B Hx IH]; intro HΓ.
  - inversion HΓ as [|Γ' A' i HΓ' HA]; subst. exists i.
    intros ρ ρ' Hρ. inversion Hρ as [| Γ0 A0 η0 η1 j a b R Hr Ha Hb Hty Hvar]; subst.
    destruct (HA _ _ Hr) as [c [d [S [Hc [Hd HS]]]]].
    reconcile_values.
    exists a, b, S, (ρ 0), (ρ' 0).
    repeat split; try assumption; try apply eval_exp_var.
    + eapply eval_exp_sub; [apply eval_sub_weaken | exact Ha].
    + eapply eval_exp_sub; [apply eval_sub_weaken | exact Hb].
    + apply (semantic_types_agree_on_left _ _ _ _ _ _ _ Hty HS). exact Hvar.
  - inversion HΓ as [|Γ0 B0 level Htail HB]; subst.
    destruct (IH Htail) as [i H].
    exists i. intros ρ ρ' Hρ.
    inversion Hρ as [|Γ0 B0 e0 e1 j c d T Hdrop Hc Hd HD Hval]; subst.
    destruct (H _ _ Hdrop) as [a [b [R [m [v [Ha [Hb [HT [Hm [Hv Hmv]]]]]]]]]].
    inversion Hm; inversion Hv; subst.
    exists a, b, R, (ρ (S n)), (ρ' (S n)).
    repeat split; try assumption; try apply eval_exp_var;
      (eapply eval_exp_sub; [apply eval_sub_weaken | eassumption]).
Qed.

Local Lemma interpreted_equality_sym Γ A M N :
  interpreted_term Γ A M N -> interpreted_term Γ A N M.
Proof.
  intros [i H]. exists i. intros ρ ρ' Hρ.
  destruct (H _ _ (proj1 (environments_per Γ) _ _ Hρ)) as
    [b [a [R [n [m [Hb [Ha [Hty [Hn [Hm Hnm]]]]]]]]]].
  exists a, b, R, m, n. repeat split; try assumption.
  - now apply semantic_type_sym.
  - apply (proj1 (semantic_value_per _ _ _ _ Hty)). assumption.
Qed.

Local Lemma interpreted_equality_trans Γ A M N P :
  interpreted_term Γ A M N ->
  interpreted_term Γ A N P ->
  interpreted_term Γ A M P.
Proof.
  intros [i H] [j K]. exists j.
  intros ρ ρ' Hρ.
  destruct (H _ _ (per_left _ _ _ (environments_per Γ) Hρ)) as
    [a [a' [R [m [n [Ha [Ha' [Hty [Hm [Hn Hmn]]]]]]]]]].
  destruct (K _ _ Hρ) as
    [c [b [T [n' [p [Hc [Hb [HT [Hn' [Hp Hnp]]]]]]]]]].
  pose proof (eval_exp_deterministic _ _ _ Ha _ Hc). subst a.
  pose proof (eval_exp_deterministic _ _ _ Hn _ Hn'). subst n'.
  exists c, b, T, m, p. repeat split; try assumption.
  eapply (proj2 (semantic_value_per _ _ _ _ HT)); [ | exact Hnp].
  apply (semantic_types_agree_on_left _ _ _ _ _ _ _ Hty HT). exact Hmn.
Qed.

Local Lemma interpreted_term_subtyping Γ A B M N :
  interpreted_subtyping Γ A B ->
  interpreted_term Γ A M N ->
  interpreted_term Γ B M N.
Proof.
  intros [i HS] [j H]. exists i.
  intros ρ ρ' Hρ.
  destruct (HS _ _ Hρ) as [a [b [c [d [R [T [Ha [Hb [HR [Hc [Hd [HT Hsub]]]]]]]]]]]].
  destruct (H _ _ Hρ) as [a' [b' [S [m [n [Ha' [Hb' [HV [Hm [Hn Hmn]]]]]]]]]].
  reconcile_values.
  exists c, d, T, m, n. repeat split; try assumption.
  apply Hsub.
  match goal with
  | HR : semantic_type i ?x _ R, HV : semantic_type j ?x _ S |- _ =>
      apply (semantic_types_agree_on_left _ _ _ _ _ _ _ HV HR)
  end.
  exact Hmn.
Qed.

Local Lemma interpreted_term_substitution Γ Δ A M N σ τ :
  interpreted_term Δ A M N ->
  interpreted_substitution Γ Δ σ τ ->
  interpreted_term Γ (a_sub A σ) (a_sub M σ) (a_sub N τ).
Proof.
  intros [i H] Hσ. exists i. intros ρ ρ' Hρ.
  destruct (Hσ _ _ Hρ) as [η [η' [Hη [Hη' HΔ]]]].
  destruct (H _ _ HΔ) as [a [b [R [m [n [Ha [Hb [HR [Hm [Hn Hmn]]]]]]]]]].
  (* The type of the right term is evaluated using the left substitution. *)
  assert (Hcross : related_environments Γ ρ' ρ')
    by (eapply per_right; [apply environments_per | exact Hρ]).
  destruct (Hσ _ _ Hcross) as [θ [θ' [Hθ [Hθ' Hθr]]]].
  unfold interpreted_substitution in Hσ.
  assert (Hτ : η' = θ') by (eapply (proj2 (proj2 (proj2 (proj2 (proj2 evaluation_deterministic))))); eassumption).
  subst θ'.
  assert (Hηθ : related_environments Δ η θ)
    by (eapply (proj2 (environments_per Δ)); [exact HΔ | apply (proj1 (environments_per Δ)); exact Hθr]).
  destruct (H _ _ Hηθ) as [a' [c [S [m' [v [Ha' [Hc [HV [Hm' [Hv Hmv]]]]]]]]]].
  reconcile_values.
  exists a, c, S, m, n. repeat split; try eassumption;
    try solve [eapply eval_exp_sub; eassumption].
  apply (semantic_types_agree_on_left _ _ _ _ _ _ _ HR HV). exact Hmn.
Qed.

Local Lemma semantic_universe i j :
  i < j ->
  semantic_type j (d_univ i) (d_univ i) (fun a b => exists R, semantic_type i a b R).
Proof.
  intro Hij. apply layer_universe; [exact Hij |].
  intros a b. unfold universe_values_agree. setoid_rewrite lower_universes_lookup; auto; reflexivity.
Qed.

Local Lemma interpreted_subtyping_reflexive Γ i A B :
  interpreted_type Γ i A B ->
  interpreted_subtyping Γ A B.
Proof.
  intro H. exists i. intros ρ ρ' Hρ.
  destruct (H _ _ Hρ) as [a [d [R [Ha [Hd HR]]]]].
  destruct (H _ _ (per_left _ _ _ (environments_per Γ) Hρ))
    as [a' [c [T [Ha' [Hc HT]]]]].
  destruct (H _ _ (per_right _ _ _ (environments_per Γ) Hρ))
    as [b [d' [S [Hb [Hd' HS]]]]].
  reconcile_values.
  exists a, b, c, d, R, T. repeat split; try eassumption.
  - eapply semantic_type_trans; [exact HR | apply semantic_type_sym; exact HS].
  - eapply semantic_type_trans; [apply semantic_type_sym; exact HT | exact HR].
  - apply (semantic_types_agree_on_left _ _ _ _ _ _ _ HR HT).
Qed.

Local Lemma interpreted_subtyping_transitive Γ A B C :
  interpreted_subtyping Γ A B ->
  interpreted_subtyping Γ B C ->
  interpreted_subtyping Γ A C.
Proof.
  intros [i H] [j K]. exists (Nat.max i j).
  intros ρ ρ' Hρ.
  destruct (H _ _ Hρ) as [a [b [c [d [R [S [Ha [Hb [HR [Hc [Hd [HS Hsub]]]]]]]]]]]].
  destruct (K _ _ Hρ) as [c' [d' [u [v [T [U [Hc' [Hd' [HT [Hu [Hv [HU Hsub']]]]]]]]]]]].
  reconcile_values.
  exists a, b, u, v, R, U. repeat split; try eassumption.
  - eapply semantic_type_cumulative; [ | exact HR]. lia.
  - eapply semantic_type_cumulative; [ | exact HU]. lia.
  - intros x y Hxy. apply Hsub'.
    apply (semantic_types_agree_on_left _ _ _ _ _ _ _ HS HT).
    now apply Hsub.
Qed.

Local Lemma interpreted_subtyping_universes Γ i j :
  i < j ->
  interpreted_subtyping Γ (a_typ i) (a_typ j).
Proof.
  intro Hij. exists (S j). intros ρ ρ' Hρ.
  exists (d_univ i), (d_univ i), (d_univ j), (d_univ j),
    (fun a b => exists R, semantic_type i a b R),
    (fun a b => exists R, semantic_type j a b R).
  repeat split; try apply eval_exp_typ; try (apply semantic_universe; lia).
  intros x y [R HR]. exists R. eauto using semantic_type_cumulative, Nat.lt_le_incl.
Qed.

Local Lemma interpreted_context_inclusion Γ Δ A B :
  (forall ρ ρ', related_environments Γ ρ ρ' -> related_environments Δ ρ ρ') ->
  interpreted_subtyping Γ A B ->
  forall ρ ρ', related_environments (A :: Γ) ρ ρ' ->
    related_environments (B :: Δ) ρ ρ'.
Proof.
  intros Htail [i H] ρ ρ' Hρ.
  inversion Hρ as [|Γ0 A0 e0 e1 j a b R Hr Ha Hb HR Hr0]; subst.
  destruct (H _ _ Hr) as
    [a' [b' [c [d [S [T [Ha' [Hb' [HS [Hc [Hd [HT Hsub]]]]]]]]]]]].
  reconcile_values.
  eapply related_extension; [now apply Htail | exact Hc | exact Hd | exact HT |].
  apply Hsub. apply (semantic_types_agree_on_left _ _ _ _ _ _ _ HR HS). exact Hr0.
Qed.

Local Lemma interpreted_universe_constructor Γ i :
  interpreted_term Γ (a_typ (S i)) (a_typ i) (a_typ i).
Proof.
  apply interpreted_types_as_terms. intros ρ ρ' Hρ.
  exists (d_univ i), (d_univ i), (fun a b => exists R, semantic_type i a b R).
  repeat split; auto using eval_exp_typ, semantic_universe, Nat.lt_succ_diag_r.
Qed.

Local Lemma interpreted_natural_constructor Γ :
  interpreted_term Γ (a_typ 0) a_nat a_nat.
Proof.
  apply interpreted_types_as_terms. intros ρ ρ' Hρ.
  exists d_nat, d_nat, natural_values_agree. repeat split; try apply eval_exp_nat.
  apply layer_natural. unfold relations_agree. reflexivity.
Qed.

Local Lemma interpreted_zero_constructor Γ :
  interpreted_term Γ a_nat a_zero a_zero.
Proof.
  exists 0. intros ρ ρ' Hρ.
  exists d_nat, d_nat, natural_values_agree, d_zero, d_zero.
  repeat split; try apply eval_exp_nat; try apply eval_exp_zero; try apply natural_values_zero.
  apply layer_natural. unfold relations_agree. reflexivity.
Qed.

Local Lemma interpreted_successor_constructor Γ M N :
  interpreted_term Γ a_nat M N ->
  interpreted_term Γ a_nat (a_succ M) (a_succ N).
Proof.
  intros [i H]. exists i. intros ρ ρ' Hρ.
  destruct (H _ _ Hρ) as [a [b [R [m [n [Ha [Hb [HR [Hm [Hn Hmn]]]]]]]]]].
  inversion Ha; inversion Hb; subst.
  exists d_nat, d_nat, R, (d_succ m), (d_succ n).
  repeat split; try eassumption; try (now apply eval_exp_succ).
  inversion HR; subst.
  match goal with HE : relations_agree R natural_values_agree |- _ =>
    apply HE, natural_values_succ, HE; exact Hmn
  end.
Qed.

Local Lemma interpreted_type_left Γ i A B :
  interpreted_type Γ i A B ->
  interpreted_type Γ i A A.
Proof.
  intros H ρ ρ' Hρ.
  destruct (H _ _ Hρ) as [a [b [R [Ha [Hb HR]]]]].
  destruct (H _ _ (per_right _ _ _ (environments_per Γ) Hρ))
    as [c [b' [T [Hc [Hb' HT]]]]].
  reconcile_values.
  exists a, c, R. repeat split; try eassumption.
  eapply semantic_type_trans; [exact HR | exact (semantic_type_sym _ _ _ _ HT)].
Qed.

Local Lemma interpreted_dependent_type Γ i A A' B B' :
  interpreted_type Γ i A A' ->
  interpreted_type (A :: Γ) i B B' ->
  interpreted_type Γ i (a_pi A B) (a_pi A' B') /\
  interpreted_type Γ i (a_sigma A B) (a_sigma A' B').
Proof.
  intros Hdom Hcod.
  assert (H : forall ρ ρ', related_environments Γ ρ ρ' ->
    exists a a' R,
      eval_exp A ρ a /\ eval_exp A' ρ' a' /\ semantic_type i a a' R /\
      (forall x y, R x y -> exists b b' T, closure_evaluations i ρ ρ' B B' x y b b' T)).
  {
    intros ρ ρ' Hρ.
    destruct (Hdom _ _ Hρ) as [a [a' [R [Ha [Ha' HR]]]]].
    destruct (interpreted_type_left _ _ _ _ Hdom _ _ Hρ)
      as [c [c' [S [Hc [Hc' HS]]]]].
    reconcile_values.
    exists a, a', R. repeat split; try eassumption.
    intros x y Hxy.
    assert (HSxy : S x y)
      by (apply (semantic_types_agree_on_left _ _ _ _ _ _ _ HR HS); exact Hxy).
    pose proof (environments_extend _ _ _ _ _ _ _ _ _ _ Hρ ltac:(eassumption)
      Hc' HS HSxy) as Hxyρ.
    destruct (Hcod _ _ Hxyρ) as [b [b' [T [Hb [Hb' HT]]]]].
    exists b, b', T. repeat split; eassumption.
  }
  split; intros ρ ρ' Hρ;
    destruct (H _ _ Hρ) as [a [a' [R [Ha [Ha' [HR Hcod']]]]]].
  - exists (d_pi a ρ B), (d_pi a' ρ' B'),
      (function_values_agree R (closure_relation i ρ ρ' B B')).
    repeat split; auto using eval_exp_pi, semantic_pi.
  - exists (d_sigma a ρ B), (d_sigma a' ρ' B'),
      (pair_values_agree R (closure_relation i ρ ρ' B B')).
    repeat split; auto using eval_exp_sigma, semantic_sigma.
Qed.

Local Lemma interpreted_lambda Γ i A A' B M M' :
  interpreted_type Γ i A A ->
  interpreted_term (A :: Γ) B M M' ->
  interpreted_term Γ (a_pi A B) (a_fn A M) (a_fn A' M').
Proof.
  intros Hdom [j Hbody]. exists (Nat.max i j). intros ρ ρ' Hρ.
  destruct (Hdom _ _ Hρ) as [a [a' [R [Ha [Ha' HR]]]]].
  assert (Hbody' : forall x y, R x y -> exists b b' T m m',
    closure_evaluations (Nat.max i j) ρ ρ' B B x y b b' T /\
    eval_exp M (extend_env ρ x) m /\ eval_exp M' (extend_env ρ' y) m' /\ T m m').
  {
    intros x y Hxy.
    pose proof (environments_extend _ _ _ _ _ _ _ _ _ _ Hρ Ha Ha' HR Hxy) as Hρxy.
    destruct (Hbody _ _ Hρxy) as (b & b' & T & m & m' & Hb & Hb' & HT & Hm & Hm' & Hmm').
    exists b, b', T, m, m'.
    repeat split; try assumption.
    eapply semantic_type_cumulative; [ | exact HT]. lia.
  }
  exists (d_pi a ρ B), (d_pi a' ρ' B),
    (function_values_agree R (closure_relation (Nat.max i j) ρ ρ' B B)),
    (d_fn ρ M), (d_fn ρ' M').
  repeat split; try (now apply eval_exp_pi); try apply eval_exp_fn.
  - apply semantic_pi; [eapply semantic_type_cumulative; [ | exact HR]; lia |].
    intros x y Hxy. destruct (Hbody' _ _ Hxy) as (b & b' & T & m & m' & HT & _).
    exists b, b', T. exact HT.
  - intros x y Hxy.
    destruct (Hbody' _ _ Hxy) as (b & b' & T & m & m' & HT & Hm & Hm' & Hmm').
    exists m, m'. repeat split; auto using eval_app_fn.
    exists b, b', T. split; assumption.
Qed.

Local Lemma interpreted_equality_type Γ i A A' M M' N N' :
  interpreted_type Γ i A A' ->
  interpreted_term Γ A M M' ->
  interpreted_term Γ A N N' ->
  interpreted_type Γ i (a_eq A M N) (a_eq A' M' N').
Proof.
  intros HA [j HM] [k HN] ρ ρ' Hρ.
  destruct (HA _ _ Hρ) as [a [a' [R [Ha [Ha' HR]]]]].
  destruct (HM _ _ Hρ) as (b & b' & S & m & m' & Hb & Hb' & HS & Hm & Hm' & Hmm').
  destruct (HN _ _ Hρ) as (c & c' & T & n & n' & Hc & Hc' & HT & Hn & Hn' & Hnn').
  reconcile_values.
  exists (d_eq a m n), (d_eq a' m' n'), (equality_values_agree R m n).
  repeat split; try (now apply eval_exp_eq).
  eapply layer_equality with (R := R); [exact HR | | | unfold relations_agree; reflexivity].
  - apply (semantic_types_agree_on_left _ _ _ _ _ _ _ HS HR). exact Hmm'.
  - apply (semantic_types_agree_on_left _ _ _ _ _ _ _ HT HR). exact Hnn'.
Qed.

Local Lemma equality_contexts :
  (forall Γ A M N, wf_exp_eq Γ A M N -> wf_ctx Γ) /\
  (forall Γ Δ σ τ, wf_sub_eq Γ Δ σ τ -> wf_ctx Γ /\ wf_ctx Δ).
Proof.
  assert (H :
    (forall Γ, wf_ctx Γ -> wf_ctx Γ) /\
    (forall Γ Δ, wf_ctx_sub Γ Δ -> wf_ctx Γ /\ wf_ctx Δ) /\
    (forall Γ A M, wf_exp Γ A M -> wf_ctx Γ) /\
    (forall Γ A M N, wf_exp_eq Γ A M N -> wf_ctx Γ) /\
    (forall Γ Δ σ, wf_sub Γ Δ σ -> wf_ctx Γ /\ wf_ctx Δ) /\
    (forall Γ Δ σ τ, wf_sub_eq Γ Δ σ τ -> wf_ctx Γ /\ wf_ctx Δ) /\
    (forall Γ A B, wf_subtyp Γ A B -> wf_ctx Γ)).
  {
    apply syntactic_wf_mut_ind; intros;
      repeat match goal with Hpair : _ /\ _ |- _ => destruct Hpair end;
      try match goal with
      | Hext : wf_ctx (_ :: _) |- _ => inversion Hext; subst
      end;
      eauto with mctt_wf.
  }
  tauto.
Qed.

Local Lemma shared_type_readback_from_interpretation :
  (forall Γ, wf_ctx Γ -> interpreted_context Γ) ->
  (forall Γ A M N, wf_exp_eq Γ A M N -> interpreted_term Γ A M N) ->
  type_equality_has_common_readback.
Proof.
  intros Hctx Heq Γ A B i H.
  eapply shared_readback_of_interpreted_types.
  - apply interpreted_context_has_environment, Hctx.
    exact (proj1 equality_contexts _ _ _ _ H).
  - apply (interpreted_terms_as_types _ i). eauto.
Qed.

(* Compatibility of the interpretation with explicit substitutions. *)

Local Definition evaluation_preserved (M N : exp) :=
  forall ρ d, eval_exp M ρ d -> eval_exp N ρ d.

Local Lemma evaluation_preserved_refl M : evaluation_preserved M M.
Proof. intros ρ d H. exact H. Qed.

Local Lemma interpreted_by_evaluation Γ A B M N M' N' :
  interpreted_term Γ A M N ->
  evaluation_preserved A B ->
  evaluation_preserved M M' ->
  evaluation_preserved N N' ->
  interpreted_term Γ B M' N'.
Proof.
  intros [i H] Htype Hleft Hright. exists i. intros ρ ρ' Hρ.
  destruct (H _ _ Hρ) as (a & b & R & m & n & Ha & Hb & HR & Hm & Hn & Hmn).
  exists a, b, R, m, n. repeat split; auto.
Qed.

Local Lemma interpreted_type_sym Γ i A B :
  interpreted_type Γ i A B -> interpreted_type Γ i B A.
Proof.
  intros H ρ ρ' Hρ.
  destruct (H _ _ (proj1 (environments_per Γ) _ _ Hρ)) as
    (b & a & R & Hb & Ha & HR).
  exists a, b, R. repeat split; try assumption.
  exact (semantic_type_sym _ _ _ _ HR).
Qed.

Local Lemma interpreted_term_left Γ A M N :
  interpreted_term Γ A M N -> interpreted_term Γ A M M.
Proof.
  intro H. eapply interpreted_equality_trans.
  - exact H.
  - now apply interpreted_equality_sym.
Qed.

Local Lemma interpreted_substitution_id Γ :
  interpreted_substitution Γ Γ a_id a_id.
Proof.
  intros ρ ρ' Hρ. exists ρ, ρ'. repeat split; auto using eval_sub_id.
Qed.

Local Lemma interpreted_substitution_weaken Γ A :
  interpreted_substitution (A :: Γ) Γ a_weaken a_weaken.
Proof.
  intros ρ ρ' Hρ. inversion Hρ; subst.
  exists (drop_env ρ), (drop_env ρ'). repeat split; auto using eval_sub_weaken.
Qed.

Local Lemma eval_sub_deterministic σ ρ η η' :
  eval_sub σ ρ η -> eval_sub σ ρ η' -> η = η'.
Proof.
  intro H. exact (proj2 (proj2 (proj2 (proj2 (proj2 evaluation_deterministic)))) σ ρ η H η').
Qed.

Local Lemma interpreted_substitution_sym Γ Δ σ τ :
  interpreted_substitution Γ Δ σ τ ->
  interpreted_substitution Γ Δ τ σ.
Proof.
  intros H ρ ρ' Hρ.
  destruct (H _ _ (proj1 (environments_per Γ) _ _ Hρ)) as
    (η' & η & Hη' & Hη & HΔ).
  exists η, η'. repeat split; try assumption.
  now apply (proj1 (environments_per Δ)).
Qed.

Local Lemma interpreted_substitution_trans Γ Δ σ τ θ :
  interpreted_substitution Γ Δ σ τ ->
  interpreted_substitution Γ Δ τ θ ->
  interpreted_substitution Γ Δ σ θ.
Proof.
  intros H K ρ ρ' Hρ.
  destruct (H _ _ (per_left _ _ _ (environments_per Γ) Hρ)) as
    (η & ηmid & Hη & Hmid & HΔ).
  destruct (K _ _ Hρ) as (ηmid' & η' & Hmid' & Hη' & HΔ').
  pose proof (eval_sub_deterministic _ _ _ _ Hmid Hmid'). subst ηmid'.
  exists η, η'. repeat split; try assumption.
  exact (proj2 (environments_per Δ) _ _ _ HΔ HΔ').
Qed.

Local Lemma interpreted_substitution_compose Γ Δ Θ σ σ' τ τ' :
  interpreted_substitution Γ Δ τ τ' ->
  interpreted_substitution Δ Θ σ σ' ->
  interpreted_substitution Γ Θ (a_compose σ τ) (a_compose σ' τ').
Proof.
  intros H K ρ ρ' Hρ.
  destruct (H _ _ Hρ) as (η & η' & Hη & Hη' & HΔ).
  destruct (K _ _ HΔ) as (ξ & ξ' & Hξ & Hξ' & HΘ).
  exists ξ, ξ'. repeat split; eauto using eval_sub_compose.
Qed.

Local Lemma invert_eval_substitution ρ M σ m :
  eval_exp (a_sub M σ) ρ m -> exists η, eval_sub σ ρ η /\ eval_exp M η m.
Proof. intro H. inversion H; subst; eauto. Qed.

Local Lemma interpreted_substitution_extend Γ Δ A i σ σ' M M' :
  interpreted_substitution Γ Δ σ σ' ->
  interpreted_type Δ i A A ->
  interpreted_term Γ (a_sub A σ) M M' ->
  interpreted_substitution Γ (A :: Δ) (a_extend σ M) (a_extend σ' M').
Proof.
  intros Hσ HA [j HM] ρ ρ' Hρ.
  destruct (Hσ _ _ Hρ) as (η & η' & Hη & Hη' & HΔ).
  destruct (HA _ _ HΔ) as (a & b & R & Ha & Hb & HR).
  destruct (HM _ _ Hρ) as (c & d & T & m & n & Hc & Hd & HT & Hm & Hn & Hmn).
  destruct (invert_eval_substitution _ _ _ _ Hc) as (θ & Hep & Heu).
  pose proof (eval_sub_deterministic _ _ _ _ Hη Hep). subst θ.
  pose proof (eval_exp_deterministic _ _ _ Ha _ Heu). subst c.
  assert (Hrelated : R m n).
  { apply (semantic_types_agree_on_left _ _ _ _ _ _ _ HT HR). exact Hmn. }
  exists (extend_env η m), (extend_env η' n). repeat split.
  - now apply eval_sub_extend.
  - now apply eval_sub_extend.
  - exact (environments_extend _ _ _ _ _ _ _ _ _ _ HΔ Ha Hb HR Hrelated).
Qed.

Local Lemma interpreted_substitution_widen Γ Δ Θ σ σ' :
  interpreted_substitution Γ Δ σ σ' ->
  (forall ρ ρ', related_environments Δ ρ ρ' -> related_environments Θ ρ ρ') ->
  interpreted_substitution Γ Θ σ σ'.
Proof.
  intros H Hsub ρ ρ' Hρ.
  destruct (H _ _ Hρ) as (η & η' & Hη & Hη' & HΔ).
  exists η, η'. repeat split; auto.
Qed.

Local Lemma eval_sub_lift σ ρ η x :
  eval_sub σ ρ η ->
  eval_sub (Syntax.q σ) (extend_env ρ x) (extend_env η x).
Proof.
  intro H. apply eval_sub_extend.
  - eapply eval_sub_compose; [apply eval_sub_weaken | exact H].
  - apply eval_exp_var.
Qed.

Local Lemma interpreted_substitutions_by_evaluation Γ Δ σ τ σ' τ' :
  interpreted_substitution Γ Δ σ τ ->
  (forall ρ η, eval_sub σ ρ η -> eval_sub σ' ρ η) ->
  (forall ρ η, eval_sub τ ρ η -> eval_sub τ' ρ η) ->
  interpreted_substitution Γ Δ σ' τ'.
Proof.
  intros H Hl Hr ρ ρ' Hρ.
  destruct (H _ _ Hρ) as (η & η' & Hη & Hη' & HΔ).
  exists η, η'. repeat split; auto.
Qed.

Local Lemma interpreted_substitution_right_identity Γ Δ σ :
  interpreted_substitution Γ Δ σ σ ->
  interpreted_substitution Γ Δ (a_compose a_id σ) σ.
Proof.
  intro H. eapply interpreted_substitutions_by_evaluation; [exact H | | auto].
  intros. eauto using eval_sub_compose, eval_sub_id.
Qed.

Local Lemma interpreted_substitution_left_identity Γ Δ σ :
  interpreted_substitution Γ Δ σ σ ->
  interpreted_substitution Γ Δ (a_compose σ a_id) σ.
Proof.
  intro H. eapply interpreted_substitutions_by_evaluation; [exact H | | auto].
  intros. eauto using eval_sub_compose, eval_sub_id.
Qed.

Local Lemma interpreted_substitution_assoc Γ Δ Θ Ξ σ τ θ :
  interpreted_substitution Γ Δ θ θ ->
  interpreted_substitution Δ Θ τ τ ->
  interpreted_substitution Θ Ξ σ σ ->
  interpreted_substitution Γ Ξ
    (a_compose (a_compose σ τ) θ) (a_compose σ (a_compose τ θ)).
Proof.
  intros Hθ Hτ Hσ ρ ρ' Hρ.
  destruct (Hθ _ _ Hρ) as (η & η' & Hη & Hη' & HΔ).
  destruct (Hτ _ _ HΔ) as (ξ & ξ' & Hξ & Hξ' & HΘ).
  destruct (Hσ _ _ HΘ) as (ω & ω' & Hω & Hω' & HΞ).
  exists ω, ω'. repeat split; eauto 8 using eval_sub_compose.
Qed.

Local Lemma interpreted_substitution_project Γ Δ A σ M :
  interpreted_substitution Γ (A :: Δ) (a_extend σ M) (a_extend σ M) ->
  interpreted_substitution Γ Δ (a_compose a_weaken (a_extend σ M)) σ.
Proof.
  intros H ρ ρ' Hρ.
  destruct (H _ _ Hρ) as (η & η' & Hη & Hη' & HΔ).
  inversion Hη; inversion Hη'; subst.
  inversion HΔ; subst.
  eexists _, _. split.
  - eapply eval_sub_compose; [exact Hη | apply eval_sub_weaken].
  - split; cbn; eassumption.
Qed.

Local Lemma interpreted_substitution_eta Γ Δ A σ :
  interpreted_substitution Γ (A :: Δ) σ σ ->
  interpreted_substitution Γ (A :: Δ) σ
    (a_extend (a_compose a_weaken σ) (a_sub (a_var 0) σ)).
Proof.
  intros H ρ ρ' Hρ.
  destruct (H _ _ Hρ) as (η & η' & Hη & Hη' & HΔ).
  exists η, (extend_env (drop_env η') (η' 0)).
  split; [exact Hη |].
  split.
  - apply eval_sub_extend.
    + eapply eval_sub_compose; [exact Hη' | apply eval_sub_weaken].
    + eapply eval_exp_sub; [exact Hη' | apply eval_exp_var].
  - inversion HΔ; subst. econstructor; cbn; eassumption.
Qed.

Local Lemma interpreted_dependent_subtyping Γ i A A' B B' :
  interpreted_type Γ i A A' ->
  interpreted_subtyping (A' :: Γ) B B' ->
  interpreted_subtyping Γ (a_pi A B) (a_pi A' B') /\
  interpreted_subtyping Γ (a_sigma A B) (a_sigma A' B').
Proof.
  intros Hdom [j Hcod].
  set (k := Nat.max i j).
  assert (H : forall ρ ρ', related_environments Γ ρ ρ' ->
    exists a a' c c' R T,
      eval_exp A ρ a /\ eval_exp A ρ' a' /\ semantic_type k a a' R /\
      eval_exp A' ρ c /\ eval_exp A' ρ' c' /\ semantic_type k c c' T /\
      relations_agree R T /\
      (forall x y, R x y -> exists b b' d d' S V,
        closure_evaluations k ρ ρ' B B x y b b' S /\
        closure_evaluations k ρ ρ' B' B' x y d d' V /\
        (forall m n, S m n -> V m n))).
  {
    intros ρ ρ' Hρ.
    destruct (Hdom _ _ Hρ) as (u & v & P & Hu & Hv & HP).
    destruct (interpreted_type_left _ _ _ _ Hdom _ _ Hρ) as
      (a & a' & R & Ha & Ha' & HR).
    destruct (interpreted_type_left _ _ _ _ (interpreted_type_sym _ _ _ _ Hdom) _ _ Hρ) as
      (c & c' & T & Hc & Hc' & HT).
    pose proof (eval_exp_deterministic _ _ _ Hu _ Ha). subst u.
    pose proof (eval_exp_deterministic _ _ _ Hv _ Hc'). subst v.
    assert (HRT : relations_agree R T).
    {
      eapply agreement_transitive.
      - exact (semantic_types_agree_on_left _ _ _ _ _ _ _ HR HP).
      - exact (semantic_types_agree_on_right _ _ _ _ _ _ _ HP HT).
    }
    exists a, a', c, c', R, T.
    repeat (first [assumption | solve [apply (semantic_type_cumulative i k); [unfold k; lia | assumption]] | split]).
    intros x y Hxy.
    assert (HTxy : T x y) by (now apply HRT).
    pose proof (environments_extend _ _ _ _ _ _ _ _ _ _ Hρ Hc Hc' HT HTxy) as Hρxy.
    destruct (Hcod _ _ Hρxy) as (b & b' & d & d' & S & V & Hb & Hb' & HS & Hd & Hd' & HV & Hsub).
    exists b, b', d, d', S, V. repeat split; try assumption;
      (apply (semantic_type_cumulative j k); [unfold k; lia | assumption]).
  }
  split; exists k; intros ρ ρ' Hρ;
    destruct (H _ _ Hρ) as (a & a' & c & c' & R & T & Ha & Ha' & HR & Hc & Hc' & HT & HRT & Hfam);
    assert (Hleft : forall x y, R x y -> exists b b' S, closure_evaluations k ρ ρ' B B x y b b' S)
      by (intros x y Hxy; destruct (Hfam _ _ Hxy) as (b & b' & d & d' & S & V & HS & _); exists b, b', S; exact HS);
    assert (Hright : forall x y, T x y -> exists d d' V, closure_evaluations k ρ ρ' B' B' x y d d' V)
      by (intros x y Hxy; apply HRT in Hxy; destruct (Hfam _ _ Hxy) as (b & b' & d & d' & S & V & _ & HV & _); exists d, d', V; exact HV);
    assert (Hincl : forall x y, R x y -> forall m n,
      closure_relation k ρ ρ' B B x y m n -> closure_relation k ρ ρ' B' B' x y m n)
      by (intros x y Hxy m n Hmn; destruct (Hfam _ _ Hxy) as (b & b' & d & d' & S & V & HS & HV & Hsub);
        apply (closure_relation_agrees _ _ _ _ _ _ _ _ _ _ HV), Hsub;
        now apply (closure_relation_agrees _ _ _ _ _ _ _ _ _ _ HS)).
  - exists (d_pi a ρ B), (d_pi a' ρ' B), (d_pi c ρ B'), (d_pi c' ρ' B'),
      (function_values_agree R (closure_relation k ρ ρ' B B)),
      (function_values_agree T (closure_relation k ρ ρ' B' B')).
    repeat split; try (now apply eval_exp_pi); try (now apply semantic_pi).
    intros f g Hfg x y Hxy. apply HRT in Hxy.
    destruct (Hfg _ _ Hxy) as (m & n & Hm & Hn & Hmn).
    exists m, n. repeat split; auto.
  - exists (d_sigma a ρ B), (d_sigma a' ρ' B), (d_sigma c ρ B'), (d_sigma c' ρ' B'),
      (pair_values_agree R (closure_relation k ρ ρ' B B)),
      (pair_values_agree T (closure_relation k ρ ρ' B' B')).
    repeat split; try (now apply eval_exp_sigma); try (now apply semantic_sigma).
    intros f g (x & y & u & v & Hx & Hy & Hu & Hv & Hxy & Huv).
    exists x, y, u, v. repeat split; auto.
    now apply HRT.
Qed.

Local Lemma interpreted_value_at Γ A M N i ρ ρ' a b R :
  interpreted_term Γ A M N ->
  related_environments Γ ρ ρ' ->
  eval_exp A ρ a -> semantic_type i a b R ->
  exists m n, eval_exp M ρ m /\ eval_exp N ρ' n /\ R m n.
Proof.
  intros [j H] Hρ Ha HT.
  destruct (H _ _ Hρ) as (c & d & S & m & n & Hc & Hd & HS & Hm & Hn & Hmn).
  pose proof (eval_exp_deterministic _ _ _ Ha _ Hc). subst c.
  exists m, n. repeat split; try assumption.
  now apply (semantic_types_agree_on_left _ _ _ _ _ _ _ HS HT).
Qed.

Local Lemma invert_eval_pi ρ A B p :
  eval_exp (a_pi A B) ρ p -> exists a, p = d_pi a ρ B /\ eval_exp A ρ a.
Proof. intro H. inversion H; subst; eauto. Qed.

Local Lemma invert_eval_sigma ρ A B p :
  eval_exp (a_sigma A B) ρ p -> exists a, p = d_sigma a ρ B /\ eval_exp A ρ a.
Proof. intro H. inversion H; subst; eauto. Qed.

Local Lemma semantic_pi_inversion i a b ρ ρ' B B' T :
  semantic_type i (d_pi a ρ B) (d_pi b ρ' B') T ->
  exists R S,
    semantic_type i a b R /\
    (forall x y, R x y -> exists u v,
      eval_exp B (extend_env ρ x) u /\ eval_exp B' (extend_env ρ' y) v) /\
    (forall x y u v, R x y ->
      eval_exp B (extend_env ρ x) u -> eval_exp B' (extend_env ρ' y) v ->
      semantic_type i u v (S x y)) /\
    relations_agree T (function_values_agree R S).
Proof. intro H. inversion H; subst; eauto 10. Qed.

Local Lemma semantic_sigma_inversion i a b ρ ρ' B B' T :
  semantic_type i (d_sigma a ρ B) (d_sigma b ρ' B') T ->
  exists R S,
    semantic_type i a b R /\
    (forall x y, R x y -> exists u v,
      eval_exp B (extend_env ρ x) u /\ eval_exp B' (extend_env ρ' y) v) /\
    (forall x y u v, R x y ->
      eval_exp B (extend_env ρ x) u -> eval_exp B' (extend_env ρ' y) v ->
      semantic_type i u v (S x y)) /\
    relations_agree T (pair_values_agree R S).
Proof. intro H. inversion H; subst; eauto 10. Qed.

Local Lemma eval_at_argument ρ M m B a :
  eval_exp M ρ m -> eval_exp B (extend_env ρ m) a ->
  eval_exp (a_sub B (a_extend a_id M)) ρ a.
Proof.
  intros HM HB. eapply eval_exp_sub; [ | exact HB].
  now apply eval_sub_extend; [apply eval_sub_id | ].
Qed.

Local Lemma interpreted_application Γ A B M M' N N' :
  interpreted_term Γ (a_pi A B) M M' ->
  interpreted_term Γ A N N' ->
  interpreted_term Γ (a_sub B (a_extend a_id N)) (a_app M N) (a_app M' N').
Proof.
  intros [i HM] HN. exists i. intros ρ ρ' Hρ.
  destruct (HM _ _ Hρ) as (p & qv & T & f & g & Hp & Hq & HT & Hf & Hg & Hfg).
  destruct (invert_eval_pi _ _ _ _ Hp) as (a & -> & Ha).
  destruct (invert_eval_pi _ _ _ _ Hq) as (b & -> & Hb).
  destruct (semantic_pi_inversion _ _ _ _ _ _ _ _ HT) as (R & S & HR & Htotal & Hcod & Hrel).
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _ HN Hρ Ha HR) as
    (x & y & Hx & Hy & Hxy).
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _ HN
    (per_right _ _ _ (environments_per Γ) Hρ) Hb
    (semantic_type_sym _ _ _ _ HR)) as (z & y' & Hz & Hy' & Hzy).
  pose proof (eval_exp_deterministic _ _ _ Hy _ Hy'). subst y'.
  pose proof (semantic_value_per _ _ _ _ HR) as [Hsym Htrans].
  assert (Hxz : R x z) by (eapply Htrans; [exact Hxy | now apply Hsym]).
  apply Hrel in Hfg.
  destruct (Hfg _ _ Hxy) as (m & n & Hm & Hn & Hmn).
  destruct (Htotal _ _ Hxz) as (u & v & Hu & Hv).
  exists u, v, (S x z), m, n. repeat split.
  - now apply eval_at_argument with (m := x).
  - now apply eval_at_argument with (m := z).
  - now apply Hcod.
  - eauto using eval_exp_app.
  - eauto using eval_exp_app.
  - apply (codomains_agree_on_left _ _ _ _ _ _ _ _ Htotal Hcod _ _ _ Hxy Hxz).
    exact Hmn.
Qed.

Local Lemma interpreted_pair Γ i A A' B B' M M' N N' :
  interpreted_type Γ i A A ->
  interpreted_type (A :: Γ) i B B ->
  interpreted_term Γ A M M' ->
  interpreted_term Γ (a_sub B (a_extend a_id M)) N N' ->
  interpreted_term Γ (a_sigma A B) (a_pair M A N B) (a_pair M' A' N' B').
Proof.
  intros HA HB HM HN. exists i. intros ρ ρ' Hρ.
  destruct (proj2 (interpreted_dependent_type _ _ _ _ _ _ HA HB) _ _ Hρ) as
    (p & qv & T & Hp & Hq & HT).
  destruct (invert_eval_sigma _ _ _ _ Hp) as (a & -> & Ha).
  destruct (invert_eval_sigma _ _ _ _ Hq) as (b & -> & Hb).
  destruct (semantic_sigma_inversion _ _ _ _ _ _ _ _ HT) as
    (R & S & HR & Htotal & Hcod & Hrel).
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _ HM Hρ Ha HR) as
    (x & y & Hx & Hy & Hxy).
  destruct (Htotal _ _ Hxy) as (u & v & Hu & Hv).
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _ HN Hρ
    (eval_at_argument _ _ _ _ _ Hx Hu) (Hcod _ _ _ _ Hxy Hu Hv)) as
    (m & n & Hm & Hn & Hmn).
  exists (d_sigma a ρ B), (d_sigma b ρ' B), T, (d_pair x m), (d_pair y n).
  repeat split; try assumption; try (now apply eval_exp_pair).
  apply Hrel. exists x, y, m, n. repeat split; auto using eval_fst_pair, eval_snd_pair.
Qed.

Local Lemma interpreted_fst Γ A B M N :
  interpreted_term Γ (a_sigma A B) M N ->
  interpreted_term Γ A (a_fst M) (a_fst N).
Proof.
  intros [i H]. exists i. intros ρ ρ' Hρ.
  destruct (H _ _ Hρ) as (p & qv & T & m & n & Hp & Hq & HT & Hm & Hn & Hmn).
  destruct (invert_eval_sigma _ _ _ _ Hp) as (a & -> & Ha).
  destruct (invert_eval_sigma _ _ _ _ Hq) as (b & -> & Hb).
  destruct (semantic_sigma_inversion _ _ _ _ _ _ _ _ HT) as
    (R & S & HR & Htotal & Hcod & Hrel).
  apply Hrel in Hmn.
  destruct Hmn as (x & y & u & v & Hx & Hy & Hu & Hv & Hxy & Huv).
  exists a, b, R, x, y. repeat split; eauto using eval_exp_fst.
Qed.

Local Lemma interpreted_snd Γ A B M N :
  interpreted_term Γ (a_sigma A B) M N ->
  interpreted_term Γ (a_sub B (a_extend a_id (a_fst M))) (a_snd M) (a_snd N).
Proof.
  intro H. destruct H as [i H]. exists i. intros ρ ρ' Hρ.
  destruct (H _ _ Hρ) as (p & qv & T & m & n & Hp & Hq & HT & Hm & Hn & Hmn).
  destruct (invert_eval_sigma _ _ _ _ Hp) as (a & -> & Ha).
  destruct (invert_eval_sigma _ _ _ _ Hq) as (b & -> & Hb).
  destruct (semantic_sigma_inversion _ _ _ _ _ _ _ _ HT) as
    (R & S & HR & Htotal & Hcod & Hrel).
  apply Hrel in Hmn.
  destruct Hmn as (x & y & u & v & Hx & Hy & Hu & Hv & Hxy & Huv).
  assert (Hfst : interpreted_term Γ A (a_fst M) (a_fst N)).
  { apply interpreted_fst with (B := B). now exists i. }
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _ Hfst
    (per_right _ _ _ (environments_per Γ) Hρ) Hb
    (semantic_type_sym _ _ _ _ HR)) as (z & y' & Hz & Hy' & Hzy).
  assert (Hy0 : eval_exp (a_fst N) ρ' y) by eauto using eval_exp_fst.
  pose proof (eval_exp_deterministic _ _ _ Hy0 _ Hy'). subst y'.
  pose proof (semantic_value_per _ _ _ _ HR) as [Hsym Htrans].
  assert (Hxz : R x z) by (eapply Htrans; [exact Hxy | now apply Hsym]).
  destruct (Htotal _ _ Hxz) as (s & t & Hs & Ht).
  exists s, t, (S x z), u, v. repeat split.
  - eapply eval_at_argument; [ | exact Hs]. eauto using eval_exp_fst.
  - now apply eval_at_argument with (m := z).
  - now apply Hcod.
  - eauto using eval_exp_snd.
  - eauto using eval_exp_snd.
  - apply (codomains_agree_on_left _ _ _ _ _ _ _ _ Htotal Hcod _ _ _ Hxy Hxz).
    exact Huv.
Qed.

(* The recursion argument determines the codomain of a natural recursor. *)

Local Definition natural_motive i ρ ρ' A A' :=
  forall x y, natural_values_agree x y ->
    exists a a' R, closure_evaluations i ρ ρ' A A' x y a a' R.

Local Definition natural_step i ρ ρ' A A' MS MS' :=
  forall x y a a' R m n,
    natural_values_agree x y ->
    closure_evaluations i ρ ρ' A A' x y a a' R ->
    R m n ->
    exists b b' S u v,
      closure_evaluations i ρ ρ' A A' (d_succ x) (d_succ y) b b' S /\
      eval_exp MS (extend_env (extend_env ρ x) m) u /\
      eval_exp MS' (extend_env (extend_env ρ' y) n) v /\
      S u v.

Local Lemma semantic_natural i : semantic_type i d_nat d_nat natural_values_agree.
Proof. apply layer_natural. unfold relations_agree. reflexivity. Qed.

Local Lemma related_natural_environment Γ ρ ρ' x y :
  related_environments Γ ρ ρ' ->
  natural_values_agree x y ->
  related_environments (a_nat :: Γ) (extend_env ρ x) (extend_env ρ' y).
Proof.
  intros Hρ Hxy.
  exact (environments_extend _ _ _ _ _ _ _ _ _ _ Hρ
    (eval_exp_nat ρ) (eval_exp_nat ρ') (semantic_natural 0) Hxy).
Qed.

Local Lemma natural_related_fresh s :
  natural_values_agree (d_neut d_nat (d_var s)) (d_neut d_nat (d_var s)).
Proof.
  apply natural_values_neutral. exists d_nat, d_nat, (d_var s), (d_var s).
  repeat split. apply related_variable.
Qed.

Local Lemma interpreted_natural_motive Γ i A A' ρ ρ' :
  interpreted_type (a_nat :: Γ) i A A' ->
  related_environments Γ ρ ρ' ->
  natural_motive i ρ ρ' A A'.
Proof.
  intros H Hρ x y Hxy.
  exact (H _ _ (related_natural_environment _ _ _ _ _ Hρ Hxy)).
Qed.

Local Lemma eval_natural_step_type ρ x m A b :
  eval_exp A (extend_env ρ (d_succ x)) b ->
  eval_exp
    (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1))))
    (extend_env (extend_env ρ x) m) b.
Proof.
  intro H. eapply eval_exp_sub; [ | exact H].
  apply eval_sub_extend.
  - eapply eval_sub_compose; apply eval_sub_weaken.
  - apply eval_exp_succ, eval_exp_var.
Qed.

Local Lemma interpreted_natural_step Γ i A A' MS MS' ρ ρ' :
  interpreted_type (a_nat :: Γ) i A A' ->
  interpreted_term (A :: a_nat :: Γ)
    (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) MS MS' ->
  related_environments Γ ρ ρ' ->
  natural_step i ρ ρ' A A' MS MS'.
Proof.
  intros Hmot Hstep Hρ x y a a' R m n Hxy (Ha & Ha' & HR) Hmn.
  pose proof (related_natural_environment _ _ _ _ _ Hρ Hxy) as Hρxy.
  destruct (interpreted_type_left _ _ _ _ Hmot _ _ Hρxy) as
    (c & d & T & Hc & Hd & HT).
  pose proof (eval_exp_deterministic _ _ _ Ha _ Hc). subst c.
  assert (HTmn : T m n)
    by (apply (semantic_types_agree_on_left _ _ _ _ _ _ _ HR HT); exact Hmn).
  pose proof (environments_extend _ _ _ _ _ _ _ _ _ _ Hρxy Ha Hd HT HTmn) as Hρmn.
  destruct (interpreted_natural_motive _ _ _ _ _ _ Hmot Hρ _ _
    (natural_values_succ _ _ Hxy)) as (b & b' & S & Hb & Hb' & HS).
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _ Hstep Hρmn
    (eval_natural_step_type _ _ _ _ _ Hb) HS) as (u & v & Hu & Hv & Huv).
  exists b, b', S, u, v. repeat split; assumption.
Qed.

Local Lemma natural_neutral_recursion_readback i ρ ρ' A A' MS MS' mz mz' k k' bz bz' R :
  natural_motive i ρ ρ' A A' ->
  natural_step i ρ ρ' A A' MS MS' ->
  closure_evaluations i ρ ρ' A A' d_zero d_zero bz bz' R ->
  R mz mz' ->
  neutrals_agree k k' ->
  neutrals_agree (d_natrec ρ A mz MS k) (d_natrec ρ' A' mz' MS' k').
Proof.
  intros Hmot Hstep Hzero Hmz Hkk' s.
  set (x := d_neut d_nat (d_var s)).
  assert (Hxx : natural_values_agree x x) by apply natural_related_fresh.
  destruct (Hmot _ _ Hxx) as (a & a' & T & Ha & Ha' & HT).
  destruct (semantic_type_readback _ _ _ _ HT) as (Hnty & Hnval & Hreflect).
  destruct (Hnty (S s)) as (A0 & HA & HA').
  destruct Hzero as (Hbz & Hbz' & HR).
  destruct (proj1 (proj2 (semantic_type_readback _ _ _ _ HR)) _ _ Hmz s)
    as (NZ & HNZ & HNZ').
  assert (Hyy : T (d_neut a (d_var (S s))) (d_neut a' (d_var (S s)))).
  { apply Hreflect, related_variable. }
  destruct (Hstep _ _ _ _ _ _ _ Hxx (conj Ha (conj Ha' HT)) Hyy)
    as (b & b' & V & u & v & (Hb & Hb' & HV) & Hu & Hv & Huv).
  destruct (proj1 (proj2 (semantic_type_readback _ _ _ _ HV)) _ _ Huv (S (S s)))
    as (NS & HNS & HNS').
  destruct (Hkk' s) as (NM & HNM & HNM').
  exists (ne_natrec A0 NZ NS NM).
  split; eapply read_ne_natrec; eassumption.
Qed.

Local Lemma interpreted_natural_recursion_values i ρ ρ' A A' MZ MZ' MS MS' bz bz' R mz mz' :
  natural_motive i ρ ρ' A A' ->
  natural_step i ρ ρ' A A' MS MS' ->
  closure_evaluations i ρ ρ' A A' d_zero d_zero bz bz' R ->
  eval_exp MZ ρ mz -> eval_exp MZ' ρ' mz' ->
  R mz mz' ->
  forall x y, natural_values_agree x y ->
    exists a a' T m n,
      closure_evaluations i ρ ρ' A A' x y a a' T /\
      eval_natrec A MZ MS x ρ m /\ eval_natrec A' MZ' MS' y ρ' n /\ T m n.
Proof.
  intros Hmot Hstep Hzero Hmz Hmz' Hrel x y Hxy.
  induction Hxy as [|x y Hxy IH|x y [c [c' [k [k' [-> [-> Hkk']]]]]]].
  - exists bz, bz', R, mz, mz'. split; [exact Hzero |].
    repeat split; auto using eval_natrec_zero.
  - destruct IH as (a & a' & S & m & n & Ha & Hm & Hn & Hmn).
    destruct (Hstep _ _ _ _ _ _ _ Hxy Ha Hmn) as
      (b & b' & T & u & v & Hb & Hu & Hv & Huv).
    exists b, b', T, u, v. split; [exact Hb |].
    repeat split; try assumption.
    + eapply eval_natrec_succ; eassumption.
    + eapply eval_natrec_succ; eassumption.
  - assert (Hxy : natural_values_agree (d_neut c k) (d_neut c' k')).
    { apply natural_values_neutral. exists c, c', k, k'. auto. }
    destruct (Hmot _ _ Hxy) as (a & a' & T & Ha & Ha' & HT).
    exists a, a', T, (d_neut a (d_natrec ρ A mz MS k)),
      (d_neut a' (d_natrec ρ' A' mz' MS' k')).
    repeat split; try assumption; try (now apply eval_natrec_neut).
    apply (proj2 (proj2 (semantic_type_readback _ _ _ _ HT))).
    eapply natural_neutral_recursion_readback; eassumption.
Qed.

Local Lemma interpreted_natural_recursion Γ i A A' MZ MZ' MS MS' M M' :
  interpreted_type (a_nat :: Γ) i A A' ->
  interpreted_term Γ (a_sub A (a_extend a_id a_zero)) MZ MZ' ->
  interpreted_term (A :: a_nat :: Γ)
    (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) MS MS' ->
  interpreted_term Γ a_nat M M' ->
  interpreted_term Γ (a_sub A (a_extend a_id M))
    (a_natrec A MZ MS M) (a_natrec A' MZ' MS' M').
Proof.
  intros HA HZ HS HM. exists i. intros ρ ρ' Hρ.
  pose proof (interpreted_natural_motive _ _ _ _ _ _ HA Hρ) as Hmot.
  pose proof (interpreted_natural_step _ _ _ _ _ _ _ _ HA HS Hρ) as Hstep.
  destruct (Hmot _ _ natural_values_zero) as (bz & bz' & R & Hbz & Hbz' & HR).
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _ HZ Hρ
    (eval_at_argument _ _ _ _ _ (eval_exp_zero ρ) Hbz) HR)
    as (mz & mz' & Hmz & Hmz' & Hmzz).
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _ HM Hρ
    (eval_exp_nat ρ) (semantic_natural 0)) as (x & y & Hx & Hy & Hxy).
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _ HM
    (per_right _ _ _ (environments_per Γ) Hρ) (eval_exp_nat ρ') (semantic_natural 0))
    as (z & y' & Hz & Hy' & Hzy).
  pose proof (eval_exp_deterministic _ _ _ Hy _ Hy'). subst y'.
  assert (Hxz : natural_values_agree x z).
  { eapply (proj2 natural_values_per); [exact Hxy | apply (proj1 natural_values_per); exact Hzy]. }
  destruct (interpreted_natural_recursion_values _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hmot Hstep (conj Hbz (conj Hbz' HR)) Hmz Hmz' Hmzz _ _ Hxy) as
    (a & a' & T & m & n & (Ha & Ha' & HT) & Hm & Hn & Hmn).
  destruct (interpreted_natural_motive _ _ _ _ _ _ (interpreted_type_left _ _ _ _ HA) Hρ _ _ Hxz)
    as (b & b' & S & Hb & Hb' & HSem).
  pose proof (eval_exp_deterministic _ _ _ Ha _ Hb). subst b.
  exists a, b', S, m, n. repeat split.
  - now apply eval_at_argument with (m := x).
  - now apply eval_at_argument with (m := z).
  - exact HSem.
  - eauto using eval_exp_natrec.
  - eauto using eval_exp_natrec.
  - now apply (semantic_types_agree_on_left _ _ _ _ _ _ _ HT HSem).
Qed.

Local Lemma evaluate_composed_substitution ρ M σ τ m :
  eval_exp (a_sub M (a_compose σ τ)) ρ m ->
  eval_exp (a_sub (a_sub M σ) τ) ρ m.
Proof.
  intro H. destruct (invert_eval_substitution _ _ _ _ H) as (η & Hsub & HM).
  inversion Hsub; subst.
  eapply eval_exp_sub; [eassumption |].
  eapply eval_exp_sub; eassumption.
Qed.

Local Lemma interpreted_term_identity_eq Γ A M :
  interpreted_term Γ A M M -> interpreted_term Γ A (a_sub M a_id) M.
Proof.
  intro H. eapply interpreted_by_evaluation; [exact H | apply evaluation_preserved_refl | | apply evaluation_preserved_refl].
  intros ρ m HM. eapply eval_exp_sub; [apply eval_sub_id | exact HM].
Qed.

Local Lemma interpreted_term_composition_eq Γ Δ Ξ A M σ τ :
  interpreted_substitution Γ Δ τ τ ->
  interpreted_substitution Δ Ξ σ σ ->
  interpreted_term Ξ A M M ->
  interpreted_term Γ (a_sub A (a_compose σ τ))
    (a_sub M (a_compose σ τ)) (a_sub (a_sub M σ) τ).
Proof.
  intros Hτ Hσ HM.
  eapply interpreted_by_evaluation.
  - eapply interpreted_term_substitution; [exact HM |].
    exact (interpreted_substitution_compose _ _ _ _ _ _ _ Hτ Hσ).
  - apply evaluation_preserved_refl.
  - apply evaluation_preserved_refl.
  - exact (fun ρ m => evaluate_composed_substitution ρ M σ τ m).
Qed.

Local Lemma interpreted_substitution_extend_compose Γ Δ Ξ A i σ τ M :
  interpreted_substitution Δ Ξ σ σ ->
  interpreted_type Ξ i A A ->
  interpreted_term Δ (a_sub A σ) M M ->
  interpreted_substitution Γ Δ τ τ ->
  interpreted_substitution Γ (A :: Ξ)
    (a_compose (a_extend σ M) τ) (a_extend (a_compose σ τ) (a_sub M τ)).
Proof.
  intros Hσ HA HM Hτ. eapply interpreted_substitutions_by_evaluation.
  - apply interpreted_substitution_compose with (Δ := Δ).
    + exact Hτ.
    + exact (interpreted_substitution_extend _ _ _ _ _ _ _ _ Hσ HA HM).
  - auto.
  - intros ρ ρ' H.
    inversion H as [ | | |? ? ? η ξ Hη Hext]; subst.
    inversion Hext; subst.
    apply eval_sub_extend.
    + eapply eval_sub_compose; eassumption.
    + eapply eval_exp_sub; eassumption.
Qed.

Local Lemma substituted_zero_variable ρ σ η M m :
  eval_sub σ ρ η -> eval_exp M ρ m ->
  eval_exp (a_sub (a_var 0) (a_extend σ M)) ρ m.
Proof.
  intros Hσ HM. eapply eval_exp_sub.
  - exact (eval_sub_extend _ _ _ _ _ Hσ HM).
  - apply eval_exp_var.
Qed.

Local Lemma interpreted_variable_zero_eq Γ Δ A σ M :
  interpreted_substitution Γ Δ σ σ ->
  interpreted_term Γ (a_sub A σ) M M ->
  interpreted_term Γ (a_sub A σ) (a_sub (a_var 0) (a_extend σ M)) M.
Proof.
  intros Hσ [i H]. exists i. intros ρ ρ' Hρ.
  destruct (H _ _ Hρ) as (a & b & R & m & n & Ha & Hb & HR & Hm & Hn & Hmn).
  destruct (Hσ _ _ Hρ) as (η & η' & Hη & Hη' & HΔ).
  exists a, b, R, m, n. repeat split; eauto using substituted_zero_variable.
Qed.

Local Lemma interpreted_variable_succ_eq Γ Δ A B σ M x :
  interpreted_substitution Γ Δ σ σ ->
  interpreted_term Γ (a_sub A σ) M M ->
  interpreted_term Δ B (a_var x) (a_var x) ->
  interpreted_term Γ (a_sub B σ)
    (a_sub (a_var (S x)) (a_extend σ M)) (a_sub (a_var x) σ).
Proof.
  intros Hσ [j HM] [i HV]. exists i. intros ρ ρ' Hρ.
  destruct (Hσ _ _ Hρ) as (η & η' & Hη & Hη' & HΔ).
  destruct (HV _ _ HΔ) as (a & b & R & n & n' & Ha & Hb & HR & Hn & Hn' & Hnn).
  destruct (HM _ _ Hρ) as (c & d & S & m & m' & Hc & Hd & HS & Hm & Hm' & Hmm).
  inversion Hn; subst.
  exists a, b, R, (η x), n'. repeat split; try assumption.
  - eapply eval_exp_sub; [exact Hη | exact Ha].
  - eapply eval_exp_sub; [exact Hη' | exact Hb].
  - eapply eval_exp_sub; [exact (eval_sub_extend _ _ _ _ _ Hη Hm) |
      exact (eval_exp_var (Datatypes.S x) (extend_env η m))].
  - eapply eval_exp_sub; [exact Hη' | exact Hn'].
Qed.

Local Lemma interpreted_variable_weaken_eq Γ B A x :
  interpreted_term (B :: Γ) (a_sub A a_weaken) (a_var (S x)) (a_var (S x)) ->
  interpreted_term (B :: Γ) (a_sub A a_weaken)
    (a_sub (a_var x) a_weaken) (a_var (S x)).
Proof.
  intro H. eapply interpreted_by_evaluation; [exact H | apply evaluation_preserved_refl | | apply evaluation_preserved_refl].
  intros ρ m Hm. inversion Hm; subst.
  eapply eval_exp_sub; [apply eval_sub_weaken | exact (eval_exp_var x (drop_env ρ))].
Qed.

Local Lemma eval_sub_universe ρ σ i d :
  eval_exp (a_sub (a_typ i) σ) ρ d -> eval_exp (a_typ i) ρ d.
Proof.
  intro H.
  destruct (invert_eval_substitution _ _ _ _ H) as (η & Hσ & HE).
  inversion HE; subst; apply eval_exp_typ.
Qed.

Local Lemma eval_sub_naturals ρ σ d :
  eval_exp (a_sub a_nat σ) ρ d -> eval_exp a_nat ρ d.
Proof.
  intro H.
  destruct (invert_eval_substitution _ _ _ _ H) as (η & Hσ & HE).
  inversion HE; subst; apply eval_exp_nat.
Qed.

Local Lemma eval_sub_zero_value ρ σ d :
  eval_exp (a_sub a_zero σ) ρ d -> eval_exp a_zero ρ d.
Proof.
  intro H.
  destruct (invert_eval_substitution _ _ _ _ H) as (η & Hσ & HE).
  inversion HE; subst; apply eval_exp_zero.
Qed.

Local Lemma interpreted_substitution_universe_eq Γ Δ σ i :
  interpreted_substitution Γ Δ σ σ ->
  interpreted_term Γ (a_typ (S i)) (a_sub (a_typ i) σ) (a_typ i).
Proof.
  intro Hσ. eapply interpreted_by_evaluation.
  - exact (interpreted_term_substitution _ _ _ _ _ _ _
      (interpreted_universe_constructor Δ i) Hσ).
  - intros ρ d HE; eapply eval_sub_universe; exact HE.
  - apply evaluation_preserved_refl.
  - intros ρ d HE; eapply eval_sub_universe; exact HE.
Qed.

Local Lemma interpreted_substitution_naturals_eq Γ Δ σ :
  interpreted_substitution Γ Δ σ σ ->
  interpreted_term Γ (a_typ 0) (a_sub a_nat σ) a_nat.
Proof.
  intro Hσ. eapply interpreted_by_evaluation.
  - exact (interpreted_term_substitution _ _ _ _ _ _ _
      (interpreted_natural_constructor Δ) Hσ).
  - intros ρ d HE; eapply eval_sub_universe; exact HE.
  - apply evaluation_preserved_refl.
  - intros ρ d HE; eapply eval_sub_naturals; exact HE.
Qed.

Local Lemma interpreted_substitution_zero_eq Γ Δ σ :
  interpreted_substitution Γ Δ σ σ ->
  interpreted_term Γ a_nat (a_sub a_zero σ) a_zero.
Proof.
  intro Hσ. eapply interpreted_by_evaluation.
  - exact (interpreted_term_substitution _ _ _ _ _ _ _
      (interpreted_zero_constructor Δ) Hσ).
  - intros ρ d HE; eapply eval_sub_naturals; exact HE.
  - apply evaluation_preserved_refl.
  - intros ρ d HE; eapply eval_sub_zero_value; exact HE.
Qed.

Local Lemma interpreted_substitution_successor_eq Γ Δ σ M :
  interpreted_substitution Γ Δ σ σ ->
  interpreted_term Δ a_nat M M ->
  interpreted_term Γ a_nat (a_sub (a_succ M) σ) (a_succ (a_sub M σ)).
Proof.
  intros Hσ HM. eapply interpreted_by_evaluation.
  - exact (interpreted_term_substitution _ _ _ _ _ _ _ (interpreted_successor_constructor _ _ _ HM) Hσ).
  - intros ρ d HE; eapply eval_sub_naturals; exact HE.
  - apply evaluation_preserved_refl.
  - intros ρ d H. destruct (invert_eval_substitution _ _ _ _ H) as (η & Hη & HE).
    inversion HE; subst. eauto using eval_exp_sub, eval_exp_succ.
Qed.

Local Lemma interpreted_refl Γ A A' M N :
  interpreted_term Γ A M N ->
  interpreted_term Γ (a_eq A M M) (a_refl A M) (a_refl A' N).
Proof.
  intros [i HM]. exists i. intros ρ ρ' Hρ.
  destruct (HM _ _ Hρ) as (a & b & R & x & y & Ha & Hb & HR & Hx & Hy & Hxy).
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _ (ex_intro _ i HM)
    (per_right _ _ _ (environments_per Γ) Hρ) Hb (semantic_type_sym _ _ _ _ HR))
    as (z & y' & Hz & Hy' & Hzy).
  pose proof (eval_exp_deterministic _ _ _ Hy _ Hy'). subst y'.
  pose proof (semantic_value_per _ _ _ _ HR) as [Hsym Htrans].
  assert (Hxz : R x z) by (eapply Htrans; [exact Hxy | now apply Hsym]).
  exists (d_eq a x x), (d_eq b z z), (equality_values_agree R x x), (d_refl x), (d_refl y).
  repeat split; try (now apply eval_exp_eq); try (now apply eval_exp_refl).
  - eapply layer_equality with (R := R); [exact HR | exact Hxz | exact Hxz |].
    unfold relations_agree. reflexivity.
  - right. exists x, y. repeat split; auto.
    all: eapply (per_left R); [now apply (semantic_value_per i a b) | exact Hxy].
Qed.

Local Lemma interpreted_function_eta Γ A B M :
  interpreted_term Γ (a_pi A B) M M ->
  interpreted_term Γ (a_pi A B) M (a_fn A (a_app (a_sub M a_weaken) (a_var 0))).
Proof.
  intros [i H]. exists i. intros ρ ρ' Hρ.
  destruct (H _ _ Hρ) as (p & qv & T & m & n & Hp & Hq & HT & Hm & Hn & Hmn).
  destruct (invert_eval_pi _ _ _ _ Hp) as (a & -> & Ha).
  destruct (invert_eval_pi _ _ _ _ Hq) as (b & -> & Hb).
  destruct (semantic_pi_inversion _ _ _ _ _ _ _ _ HT) as
    (R & S & HR & Htotal & Hcod & Hrel).
  exists (d_pi a ρ B), (d_pi b ρ' B), T, m, (d_fn ρ' (a_app (a_sub M a_weaken) (a_var 0))).
  repeat split; try assumption; try apply eval_exp_fn.
  apply Hrel in Hmn. apply Hrel.
  intros x y Hxy. destruct (Hmn _ _ Hxy) as (u & v & Hu & Hv & Huv).
  exists u, v. repeat split; try assumption.
  apply eval_app_fn. eapply eval_exp_app; [ | apply eval_exp_var | exact Hv].
  eapply eval_exp_sub; [apply eval_sub_weaken | exact Hn].
Qed.

Local Lemma interpreted_pair_eta Γ A B M :
  interpreted_term Γ (a_sigma A B) M M ->
  interpreted_term Γ (a_sigma A B) M (a_pair (a_fst M) A (a_snd M) B).
Proof.
  intros [i H]. exists i. intros ρ ρ' Hρ.
  destruct (H _ _ Hρ) as (p & qv & T & m & n & Hp & Hq & HT & Hm & Hn & Hmn).
  destruct (invert_eval_sigma _ _ _ _ Hp) as (a & -> & Ha).
  destruct (invert_eval_sigma _ _ _ _ Hq) as (b & -> & Hb).
  destruct (semantic_sigma_inversion _ _ _ _ _ _ _ _ HT) as
    (R & S & HR & Htotal & Hcod & Hrel).
  apply Hrel in Hmn.
  destruct Hmn as (x & y & u & v & Hx & Hy & Hu & Hv & Hxy & Huv).
  exists (d_sigma a ρ B), (d_sigma b ρ' B), T, m, (d_pair y v).
  repeat split; try assumption.
  - apply eval_exp_pair; eauto using eval_exp_fst, eval_exp_snd.
  - apply Hrel. exists x, y, u, v. repeat split; auto using eval_fst_pair, eval_snd_pair.
Qed.

Local Lemma eval_function_beta A M N :
  evaluation_preserved (a_app (a_fn A M) N) (a_sub M (a_extend a_id N)).
Proof.
  intros ρ d H. inversion H; subst.
  match goal with K : eval_exp (a_fn _ _) _ _ |- _ => inversion K; subst end.
  match goal with K : eval_app _ _ _ |- _ => inversion K; subst end.
  eapply eval_at_argument; eassumption.
Qed.

Local Lemma eval_fst_beta A B M N :
  evaluation_preserved (a_fst (a_pair M A N B)) M.
Proof.
  intros ρ d H. inversion H; subst.
  match goal with K : eval_exp (a_pair _ _ _ _) _ _ |- _ => inversion K; subst end.
  match goal with K : eval_fst _ _ |- _ => inversion K; subst end.
  assumption.
Qed.

Local Lemma eval_snd_beta A B M N :
  evaluation_preserved (a_snd (a_pair M A N B)) N.
Proof.
  intros ρ d H. inversion H; subst.
  match goal with K : eval_exp (a_pair _ _ _ _) _ _ |- _ => inversion K; subst end.
  match goal with K : eval_snd _ _ |- _ => inversion K; subst end.
  assumption.
Qed.

Local Lemma eval_natural_beta_zero A MZ MS :
  evaluation_preserved (a_natrec A MZ MS a_zero) MZ.
Proof.
  intros ρ d H. inversion H; subst.
  match goal with K : eval_exp a_zero _ _ |- _ => inversion K; subst end.
  match goal with K : eval_natrec _ _ _ _ _ _ |- _ => inversion K; subst end.
  assumption.
Qed.

Local Lemma eval_natural_beta_succ A MZ MS M :
  evaluation_preserved (a_natrec A MZ MS (a_succ M))
    (a_sub MS (a_extend (a_extend a_id M) (a_natrec A MZ MS M))).
Proof.
  intros ρ d H. inversion H; subst.
  match goal with K : eval_exp (a_succ _) _ _ |- _ => inversion K; subst end.
  match goal with K : eval_natrec _ _ _ (d_succ _) _ _ |- _ => inversion K; subst end.
  eapply eval_exp_sub.
  - eapply eval_sub_extend; [eauto using eval_sub_extend, eval_sub_id |].
    eauto using eval_exp_natrec.
  - eassumption.
Qed.

(* The motive of equality elimination has three dependent binders. *)

Local Definition equation_context (Γ : ctx) (A : typ) : ctx :=
  a_eq (a_sub A (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0)
  :: a_sub A a_weaken :: A :: Γ.

Local Definition equation_environment ρ x y p :=
  extend_env (extend_env (extend_env ρ x) y) p.

Local Lemma eval_equation_context_last ρ A a x y :
  eval_exp A ρ a ->
  eval_exp
    (a_eq (a_sub A (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0))
    (extend_env (extend_env ρ x) y) (d_eq a x y).
Proof.
  intro H. apply eval_exp_eq; [ | apply eval_exp_var | apply eval_exp_var].
  eapply eval_exp_sub; [ | exact H].
  eapply eval_sub_compose; apply eval_sub_weaken.
Qed.

Local Lemma semantic_equality i a a' x x' y y' R :
  semantic_type i a a' R -> R x x' -> R y y' ->
  semantic_type i (d_eq a x y) (d_eq a' x' y') (equality_values_agree R x y).
Proof.
  intros. eapply layer_equality; try eassumption.
  unfold relations_agree. reflexivity.
Qed.

Local Lemma related_equation_environment Γ A i ρ ρ' a a' R x x' y y' p p' :
  related_environments Γ ρ ρ' ->
  eval_exp A ρ a -> eval_exp A ρ' a' -> semantic_type i a a' R ->
  R x x' -> R y y' -> equality_values_agree R x y p p' ->
  related_environments (equation_context Γ A)
    (equation_environment ρ x y p) (equation_environment ρ' x' y' p').
Proof.
  intros Hρ Ha Ha' HR Hx Hy Hp.
  assert (Hone : related_environments (A :: Γ) (extend_env ρ x) (extend_env ρ' x'))
    by (eapply environments_extend; eassumption).
  assert (Htwo : related_environments (a_sub A a_weaken :: A :: Γ)
    (extend_env (extend_env ρ x) y) (extend_env (extend_env ρ' x') y')).
  {
    eapply environments_extend; [exact Hone | | | exact HR | exact Hy];
      (eapply eval_exp_sub; [apply eval_sub_weaken | eassumption]).
  }
  unfold equation_context, equation_environment.
  eapply environments_extend; [exact Htwo | | | | exact Hp].
  - exact (eval_equation_context_last _ _ _ _ _ Ha).
  - exact (eval_equation_context_last _ _ _ _ _ Ha').
  - exact (semantic_equality _ _ _ _ _ _ _ _ HR Hx Hy).
Qed.

Local Definition equation_motive i ρ ρ' R B B' :=
  forall x x' y y' p p',
    R x x' -> R y y' -> equality_values_agree R x y p p' ->
    exists b b' S,
      eval_exp B (equation_environment ρ x y p) b /\
      eval_exp B' (equation_environment ρ' x' y' p') b' /\ semantic_type i b b' S.

Local Lemma interpreted_equation_motive Γ i j A B B' ρ ρ' a a' R :
  interpreted_type Γ i A A ->
  interpreted_type (equation_context Γ A) j B B' ->
  related_environments Γ ρ ρ' ->
  eval_exp A ρ a -> semantic_type i a a' R ->
  equation_motive j ρ ρ' R B B'.
Proof.
  intros HA HB Hρ Ha HR x x' y y' p p' Hxx Hyy Hpp.
  destruct (HA _ _ Hρ) as (c & d & T & Hc & Hd & HT).
  pose proof (eval_exp_deterministic _ _ _ Ha _ Hc). subst c.
  pose proof (semantic_types_agree_on_left _ _ _ _ _ _ _ HR HT) as HE.
  apply HB.
  eapply related_equation_environment; [exact Hρ | exact Ha | exact Hd | exact HT | | |].
  - now apply HE.
  - now apply HE.
  - now apply (equality_relation_congruence _ _ _ _ HE).
Qed.

Local Definition equation_refl_type A B :=
  a_sub B (a_extend (a_extend a_id (a_var 0)) (a_refl (a_sub A a_weaken) (a_var 0))).

Local Definition equation_refl_case i ρ ρ' R B B' BR BR' :=
  forall x x', R x x' ->
  exists b b' S m m',
    eval_exp B (equation_environment ρ x x (d_refl x)) b /\
    eval_exp B' (equation_environment ρ' x' x' (d_refl x')) b' /\
    semantic_type i b b' S /\
    eval_exp BR (extend_env ρ x) m /\ eval_exp BR' (extend_env ρ' x') m' /\ S m m'.

Local Lemma eval_equation_refl_type ρ A B x b :
  eval_exp B (equation_environment ρ x x (d_refl x)) b ->
  eval_exp (equation_refl_type A B) (extend_env ρ x) b.
Proof.
  intro H. eapply eval_exp_sub; [ | exact H].
  apply eval_sub_extend.
  - apply eval_sub_extend; [apply eval_sub_id | apply eval_exp_var].
  - apply eval_exp_refl, eval_exp_var.
Qed.

Local Lemma interpreted_equation_refl_case Γ A i j B B' BR BR' ρ ρ' a a' R :
  interpreted_type Γ i A A ->
  interpreted_type (equation_context Γ A) j B B' ->
  interpreted_term (A :: Γ) (equation_refl_type A B) BR BR' ->
  related_environments Γ ρ ρ' ->
  eval_exp A ρ a -> semantic_type i a a' R ->
  equation_refl_case j ρ ρ' R B B' BR BR'.
Proof.
  intros HA HB HRB Hρ Ha HR x x' Hxx.
  pose proof (per_left _ _ _ (semantic_value_per _ _ _ _ HR) Hxx) as Hx.
  assert (Hpp : equality_values_agree R x x (d_refl x) (d_refl x')).
  { right. exists x, x'. auto. }
  destruct (interpreted_equation_motive _ _ _ _ _ _ _ _ _ _ _
    HA HB Hρ Ha HR _ _ _ _ _ _ Hxx Hxx Hpp) as (b & b' & S & Hb & Hb' & HS).
  destruct (HA _ _ Hρ) as (c & d & T & Hc & Hd & HT).
  pose proof (eval_exp_deterministic _ _ _ Ha _ Hc). subst c.
  assert (HTxx : T x x')
    by (apply (semantic_types_agree_on_left _ _ _ _ _ _ _ HR HT); exact Hxx).
  pose proof (environments_extend _ _ _ _ _ _ _ _ _ _ Hρ Ha Hd HT HTxx) as Henv.
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _ HRB Henv
    (eval_equation_refl_type _ _ _ _ _ Hb) HS) as (m & m' & Hm & Hm' & Hmm).
  exists b, b', S, m, m'. repeat split; assumption.
Qed.

Local Lemma neutral_equation_readback i j ρ ρ' a a' R x x' y y' B B' BR BR' k k' :
  semantic_type i a a' R -> R x x' -> R y y' ->
  equation_motive j ρ ρ' R B B' ->
  equation_refl_case j ρ ρ' R B B' BR BR' ->
  neutrals_agree k k' ->
  neutrals_agree (d_eqrec ρ a B BR x y k) (d_eqrec ρ' a' B' BR' x' y' k').
Proof.
  intros HR Hxx Hyy Hmot Hstep Hkk' s.
  destruct (semantic_type_readback _ _ _ _ HR) as (Hty & Hval & Href).
  destruct (Hty s) as (A & HA & HA').
  destruct (Hval _ _ Hxx s) as (M1 & HM1 & HM1').
  destruct (Hval _ _ Hyy s) as (M2 & HM2 & HM2').
  set (u := d_neut a (d_var s)).
  set (u' := d_neut a' (d_var s)).
  set (v := d_neut a (d_var (S s))).
  set (v' := d_neut a' (d_var (S s))).
  set (p := d_neut (d_eq a u v) (d_var (S (S s)))).
  set (p' := d_neut (d_eq a' u' v') (d_var (S (S s)))).
  assert (Huu : R u u') by (apply Href, related_variable).
  assert (Hvv : R v v') by (apply Href, related_variable).
  assert (Hpp : equality_values_agree R u v p p').
  { left. exists (d_eq a u v), (d_eq a' u' v'), (d_var (S (S s))), (d_var (S (S s))).
    repeat split. apply related_variable. }
  destruct (Hmot _ _ _ _ _ _ Huu Hvv Hpp) as (b & b' & S0 & Hb & Hb' & HS).
  destruct (proj1 (semantic_type_readback _ _ _ _ HS) (S (S (S s)))) as (C & HC & HC').
  destruct (Hstep _ _ Huu) as (c & c' & T & m & m' & Hc & Hc' & HT & Hm & Hm' & Hmm').
  destruct (proj1 (proj2 (semantic_type_readback _ _ _ _ HT)) _ _ Hmm' (S s))
    as (D & HD & HD').
  destruct (Hkk' s) as (N & HN & HN').
  exists (ne_eqrec A C D M1 M2 N).
  split; eapply read_ne_eqrec; eassumption.
Qed.

Local Lemma related_equation_recursion_values i j Γ A ρ ρ' a a' R B B' BR BR'
    x x' y y' p p' b b' T :
  interpreted_type (equation_context Γ A) j B B ->
  equation_motive j ρ ρ' R B B' ->
  related_environments Γ ρ ρ ->
  eval_exp A ρ a -> semantic_type i a a' R ->
  R x x' -> R y y' -> equality_values_agree R x y p p' ->
  eval_exp B (equation_environment ρ x y p) b ->
  eval_exp B' (equation_environment ρ' x' y' p') b' -> semantic_type j b b' T ->
  equation_refl_case j ρ ρ' R B B' BR BR' ->
  exists m m',
    eval_eqrec a B BR x y p ρ m /\
    eval_eqrec a' B' BR' x' y' p' ρ' m' /\ T m m'.
Proof.
  intros Hmot Hfamily Hρ Ha HR Hxx Hyy Hpp Hb Hb' HT Hstep.
  destruct Hpp as [(c & c' & k & k' & -> & -> & Hne) | (u & u' & -> & -> & Huu & Hux & Huy)].
  - exists (d_neut b (d_eqrec ρ a B BR x y k)),
      (d_neut b' (d_eqrec ρ' a' B' BR' x' y' k')).
    repeat split; try now apply eval_eqrec_neut.
    apply (proj2 (proj2 (semantic_type_readback _ _ _ _ HT))).
    eapply neutral_equation_readback; eassumption.
  - destruct (Hstep _ _ Huu) as (c & c' & S & m & m' & Hc & Hc' & HS & Hm & Hm' & Hmm').
    pose proof (semantic_value_per _ _ _ _ HR) as [Hsym Htrans].
    pose proof (per_left _ _ _ (conj Hsym Htrans) Huu) as Hurel.
    assert (HRaa : semantic_type i a a R).
    { eapply semantic_type_trans; [exact HR | exact (semantic_type_sym _ _ _ _ HR)]. }
    assert (Hctx : related_environments (equation_context Γ A)
      (equation_environment ρ x y (d_refl u)) (equation_environment ρ u u (d_refl u))).
    {
      eapply related_equation_environment; [exact Hρ | exact Ha | exact Ha | exact HRaa | | |].
      - now apply Hsym.
      - now apply Hsym.
      - right. exists u, u. auto.
    }
    destruct (Hmot _ _ Hctx) as
      (d & d' & V & Hd & Hd' & HV).
    pose proof (eval_exp_deterministic _ _ _ Hb _ Hd). subst d.
    pose proof (eval_exp_deterministic _ _ _ Hc _ Hd'). subst d'.
    exists m, m'. repeat split; auto using eval_eqrec_refl.
    apply (semantic_types_agree_on_left _ _ _ _ _ _ _ HV HT).
    now apply (semantic_types_agree_on_left _ _ _ _ _ _ _ HS (semantic_type_sym _ _ _ _ HV)).
Qed.

Local Definition equation_result_type B M N P :=
  a_sub B (a_extend (a_extend (a_extend a_id M) N) P).

Local Lemma eval_equation_result_type ρ B M N P x y p b :
  eval_exp M ρ x -> eval_exp N ρ y -> eval_exp P ρ p ->
  eval_exp B (equation_environment ρ x y p) b ->
  eval_exp (equation_result_type B M N P) ρ b.
Proof.
  intros. unfold equation_result_type. eapply eval_exp_sub; [ | eassumption].
  do 3 (apply eval_sub_extend; [ | eassumption]). apply eval_sub_id.
Qed.

Local Lemma interpreted_equality_recursion Γ i j A A' B B' BR BR' M1 M1' M2 M2' P P' :
  interpreted_type Γ i A A' ->
  interpreted_term Γ A M1 M1' ->
  interpreted_term Γ A M2 M2' ->
  interpreted_type (equation_context Γ A) j B B' ->
  interpreted_term (A :: Γ) (equation_refl_type A B) BR BR' ->
  interpreted_term Γ (a_eq A M1 M2) P P' ->
  interpreted_term Γ (equation_result_type B M1 M2 P)
    (a_eqrec A B BR M1 M2 P) (a_eqrec A' B' BR' M1' M2' P').
Proof.
  intros HA HM1 HM2 HB HBR HP.
  pose proof (interpreted_type_left _ _ _ _ HA) as HAA.
  exists j. intros ρ ρ' Hρ.
  destruct (HA _ _ Hρ) as (a & a' & R & Ha & Ha' & HR).
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _ HM1 Hρ Ha HR) as (x & x' & Hx & Hx' & Hxx).
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _ HM2 Hρ Ha HR) as (y & y' & Hy & Hy' & Hyy).
  pose proof (eval_exp_eq _ _ _ _ _ _ _ Ha Hx Hy) as HE.
  pose proof (semantic_equality _ _ _ _ _ _ _ _ HR Hxx Hyy) as HSEM.
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _ HP Hρ HE HSEM) as (p & p' & Hp & Hp' & Hpp).
  pose proof (interpreted_equation_motive _ _ _ _ _ _ _ _ _ _ _ HAA HB Hρ Ha HR) as Hfam.
  pose proof (interpreted_equation_refl_case _ _ _ _ _ _ _ _ _ _ _ _ _ HAA HB HBR Hρ Ha HR) as Hstep.
  destruct (Hfam _ _ _ _ _ _ Hxx Hyy Hpp) as (b & b' & T & Hb & Hb' & HT).
  destruct (related_equation_recursion_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (interpreted_type_left _ _ _ _ HB) Hfam (per_left _ _ _ (environments_per Γ) Hρ) Ha HR Hxx Hyy Hpp Hb Hb' HT Hstep) as (m & m' & Hm & Hm' & Hmm').
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _
    (interpreted_term_left _ _ _ _ HM1) Hρ Ha HR) as (u & x0 & Hu & Hx0 & Hux).
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _
    (interpreted_term_left _ _ _ _ HM2) Hρ Ha HR) as (v & y0 & Hv & Hy0 & Hvy).
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _
    (interpreted_term_left _ _ _ _ HP) Hρ HE HSEM) as (w & p0 & Hw & Hp0 & Hwp).
  pose proof (eval_exp_deterministic _ _ _ Hx _ Hu). subst u.
  pose proof (eval_exp_deterministic _ _ _ Hy _ Hv). subst v.
  pose proof (eval_exp_deterministic _ _ _ Hp _ Hw). subst w.
  destruct (interpreted_equation_motive _ _ _ _ _ _ _ _ _ _ _
    HAA (interpreted_type_left _ _ _ _ HB) Hρ Ha HR _ _ _ _ _ _ Hux Hvy Hwp)
    as (c & c' & S & Hc & Hc' & HS).
  pose proof (eval_exp_deterministic _ _ _ Hb _ Hc). subst c.
  exists b, c', S, m, m'. repeat split; try assumption.
  - eapply eval_equation_result_type; eassumption.
  - eapply eval_equation_result_type; eassumption.
  - eapply eval_exp_eqrec; eassumption.
  - eapply eval_exp_eqrec; eassumption.
  - now apply (semantic_types_agree_on_left _ _ _ _ _ _ _ HT HS).
Qed.

Local Lemma eval_equation_beta A B BR M :
  evaluation_preserved (a_eqrec A B BR M M (a_refl A M))
    (a_sub BR (a_extend a_id M)).
Proof.
  intros ρ d H. inversion H; subst.
  match goal with K : eval_exp (a_refl _ _) _ _ |- _ => inversion K; subst end.
  match goal with K : eval_eqrec _ _ _ _ _ _ _ _ |- _ => inversion K; subst end.
  eapply eval_at_argument; eassumption.
Qed.

Local Lemma interpreted_explicit_substitution_eq Γ Δ A B M N σ :
  interpreted_substitution Γ Δ σ σ ->
  interpreted_term Δ A M M ->
  evaluation_preserved (a_sub A σ) B ->
  evaluation_preserved (a_sub M σ) N ->
  interpreted_term Γ B (a_sub M σ) N.
Proof.
  intros Hσ HM Htype Hexpr. eapply interpreted_by_evaluation.
  - exact (interpreted_term_substitution _ _ _ _ _ _ _ HM Hσ).
  - exact Htype.
  - apply evaluation_preserved_refl.
  - exact Hexpr.
Qed.

Local Lemma eval_substitution_codomain ρ η σ B N n d :
  eval_sub σ ρ η ->
  eval_exp N ρ n ->
  eval_exp B (extend_env η n) d ->
  eval_exp (a_sub B (a_extend σ N)) ρ d.
Proof.
  intros. eapply eval_exp_sub; [ | eassumption].
  eapply eval_sub_extend; eassumption.
Qed.

Local Lemma eval_distribute_app M N σ :
  evaluation_preserved (a_sub (a_app M N) σ) (a_app (a_sub M σ) (a_sub N σ)).
Proof.
  intros ρ d H. destruct (invert_eval_substitution _ _ _ _ H) as (η & Hσ & HE).
  inversion HE; subst. eauto 6 using eval_exp_sub, eval_exp_app.
Qed.

Local Lemma eval_distribute_fst M σ :
  evaluation_preserved (a_sub (a_fst M) σ) (a_fst (a_sub M σ)).
Proof.
  intros ρ d H. destruct (invert_eval_substitution _ _ _ _ H) as (η & Hσ & HE).
  inversion HE; subst. eauto using eval_exp_sub, eval_exp_fst.
Qed.

Local Lemma eval_distribute_snd M σ :
  evaluation_preserved (a_sub (a_snd M) σ) (a_snd (a_sub M σ)).
Proof.
  intros ρ d H. destruct (invert_eval_substitution _ _ _ _ H) as (η & Hσ & HE).
  inversion HE; subst. eauto using eval_exp_sub, eval_exp_snd.
Qed.

Local Lemma eval_distribute_pair A B M N σ :
  evaluation_preserved (a_sub (a_pair M A N B) σ)
    (a_pair (a_sub M σ) (a_sub A σ) (a_sub N σ) (a_sub B (Syntax.q σ))).
Proof.
  intros ρ d H. destruct (invert_eval_substitution _ _ _ _ H) as (η & Hσ & HE).
  inversion HE; subst. eauto using eval_exp_sub, eval_exp_pair.
Qed.

Local Lemma eval_distribute_equality A M N σ :
  evaluation_preserved (a_sub (a_eq A M N) σ)
    (a_eq (a_sub A σ) (a_sub M σ) (a_sub N σ)).
Proof.
  intros ρ d H. destruct (invert_eval_substitution _ _ _ _ H) as (η & Hσ & HE).
  inversion HE; subst. eauto 7 using eval_exp_sub, eval_exp_eq.
Qed.

Local Lemma eval_distribute_refl A M σ :
  evaluation_preserved (a_sub (a_refl A M) σ) (a_refl (a_sub A σ) (a_sub M σ)).
Proof.
  intros ρ d H. destruct (invert_eval_substitution _ _ _ _ H) as (η & Hσ & HE).
  inversion HE; subst. eauto using eval_exp_sub, eval_exp_refl.
Qed.

Local Lemma eval_distribute_argument_type B M N σ :
  evaluation_preserved (a_sub M σ) N ->
  evaluation_preserved (a_sub (a_sub B (a_extend a_id M)) σ) (a_sub B (a_extend σ N)).
Proof.
  intros Harg ρ d H.
  destruct (invert_eval_substitution _ _ _ _ H) as (η & Hη & Htype).
  destruct (invert_eval_substitution _ _ _ _ Htype) as (ξ & Hξ & HB).
  inversion Hξ; subst.
  match goal with HI : eval_sub a_id _ _ |- _ => inversion HI; subst end.
  eapply eval_substitution_codomain; [exact Hη | | exact HB].
  apply Harg. eapply eval_exp_sub; eassumption.
Qed.

Local Lemma interpreted_dependent_substitution Γ Δ i σ A B :
  interpreted_substitution Γ Δ σ σ ->
  interpreted_type Δ i A A ->
  interpreted_type (A :: Δ) i B B ->
  interpreted_type Γ i (a_sub (a_pi A B) σ) (a_pi (a_sub A σ) (a_sub B (Syntax.q σ))) /\
  interpreted_type Γ i (a_sub (a_sigma A B) σ) (a_sigma (a_sub A σ) (a_sub B (Syntax.q σ))).
Proof.
  intros Hσ HA HB.
  assert (H : forall ρ ρ', related_environments Γ ρ ρ' ->
    exists η η' a b R,
      eval_sub σ ρ η /\ eval_sub σ ρ' η' /\ eval_exp A η a /\ eval_exp A η' b /\
      semantic_type i a b R /\
      (forall x y, R x y ->
        exists u v T, closure_evaluations i η ρ' B (a_sub B (Syntax.q σ)) x y u v T)).
  {
    intros ρ ρ' Hρ.
    destruct (Hσ _ _ Hρ) as (η & η' & Hη & Hη' & HΔ).
    destruct (HA _ _ HΔ) as (a & b & R & Ha & Hb & HR).
    exists η, η', a, b, R. repeat split; try assumption.
    intros x y Hxy.
    destruct (HB _ _ (environments_extend _ _ _ _ _ _ _ _ _ _ HΔ Ha Hb HR Hxy)) as
      (u & v & T & Hu & Hv & HT).
    exists u, v, T. repeat split; try assumption.
    eapply eval_exp_sub; [apply eval_sub_lift; exact Hη' | exact Hv].
  }
  split; intros ρ ρ' Hρ;
    destruct (H _ _ Hρ) as (η & η' & a & b & R & Hη & Hη' & Ha & Hb & HR & Hcod).
  - exists (d_pi a η B), (d_pi b ρ' (a_sub B (Syntax.q σ))),
      (function_values_agree R (closure_relation i η ρ' B (a_sub B (Syntax.q σ)))).
    repeat split; try (now apply semantic_pi).
    + eapply eval_exp_sub; [exact Hη | now apply eval_exp_pi].
    + apply eval_exp_pi. eapply eval_exp_sub; eassumption.
  - exists (d_sigma a η B), (d_sigma b ρ' (a_sub B (Syntax.q σ))),
      (pair_values_agree R (closure_relation i η ρ' B (a_sub B (Syntax.q σ)))).
    repeat split; try (now apply semantic_sigma).
    + eapply eval_exp_sub; [exact Hη | now apply eval_exp_sigma].
    + apply eval_exp_sigma. eapply eval_exp_sub; eassumption.
Qed.

Local Lemma interpreted_function_substitution_eq Γ Δ A B M σ :
  interpreted_substitution Γ Δ σ σ ->
  interpreted_term Δ (a_pi A B) (a_fn A M) (a_fn A M) ->
  interpreted_term Γ (a_sub (a_pi A B) σ)
    (a_sub (a_fn A M) σ) (a_fn (a_sub A σ) (a_sub M (Syntax.q σ))).
Proof.
  intros Hσ [i HM]. exists i. intros ρ ρ' Hρ.
  destruct (Hσ _ _ Hρ) as (η & η' & Hη & Hη' & HΔ).
  destruct (HM _ _ HΔ) as (p & qv & T & m & n & Hp & Hq & HT & Hm & Hn & Hmn).
  destruct (invert_eval_pi _ _ _ _ Hp) as (a & -> & Ha).
  destruct (invert_eval_pi _ _ _ _ Hq) as (b & -> & Hb).
  destruct (semantic_pi_inversion _ _ _ _ _ _ _ _ HT) as
    (R & S & HR & Htotal & Hcod & Hrel).
  inversion Hn; subst.
  exists (d_pi a η B), (d_pi b η' B), T, m, (d_fn ρ' (a_sub M (Syntax.q σ))).
  repeat split; try assumption; try (now apply eval_exp_fn); try solve [eapply eval_exp_sub; eassumption].
  apply Hrel in Hmn. apply Hrel. intros x y Hxy.
  destruct (Hmn _ _ Hxy) as (u & v & Hu & Hv & Huv).
  exists u, v. repeat split; try assumption.
  apply eval_app_fn. eapply eval_exp_sub; [exact (eval_sub_lift _ _ _ _ Hη') |].
  inversion Hv; subst. assumption.
Qed.

Local Lemma eval_lifted_expression σ ρ η x B b :
  eval_sub σ ρ η ->
  eval_exp B (extend_env η x) b ->
  eval_exp (a_sub B (Syntax.q σ)) (extend_env ρ x) b.
Proof.
  intros Hσ HB. eapply eval_exp_sub; [exact (eval_sub_lift _ _ _ _ Hσ) | exact HB].
Qed.

Local Lemma eval_lifted_expression_back σ ρ η x B b :
  eval_sub σ ρ η ->
  eval_exp (a_sub B (Syntax.q σ)) (extend_env ρ x) b ->
  eval_exp B (extend_env η x) b.
Proof.
  intros Hσ HB.
  destruct (invert_eval_substitution _ _ _ _ HB) as (θ & Hθ & H).
  pose proof (eval_sub_deterministic _ _ _ _ (eval_sub_lift _ _ _ x Hσ) Hθ).
  now subst θ.
Qed.

Local Lemma interpreted_recursion_substitution Γ Δ i σ A MZ MS M :
  interpreted_substitution Γ Δ σ σ ->
  interpreted_type (a_nat :: Δ) i A A ->
  interpreted_term Δ (a_sub A (a_extend a_id a_zero)) MZ MZ ->
  interpreted_term (A :: a_nat :: Δ)
    (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) MS MS ->
  interpreted_term Δ a_nat M M ->
  interpreted_term Γ (a_sub A (a_extend σ (a_sub M σ)))
    (a_sub (a_natrec A MZ MS M) σ)
    (a_natrec (a_sub A (Syntax.q σ)) (a_sub MZ σ)
      (a_sub MS (Syntax.q (Syntax.q σ))) (a_sub M σ)).
Proof.
  intros Hσ HA HZ HS HM. exists i. intros ρ ρ' Hρ.
  destruct (Hσ _ _ Hρ) as (η & η' & Hη & Hη' & HΔ).
  pose proof (interpreted_natural_motive _ _ _ _ _ _ HA HΔ) as Hmot.
  pose proof (interpreted_natural_step _ _ _ _ _ _ _ _ HA HS HΔ) as Hstep.
  set (A' := a_sub A (Syntax.q σ)).
  set (MS' := a_sub MS (Syntax.q (Syntax.q σ))).
  assert (Hmot' : natural_motive i η ρ' A A').
  {
    intros x y Hxy.
    destruct (Hmot _ _ Hxy) as (a & a' & R & Ha & Ha' & HR).
    exists a, a', R. repeat split; try assumption.
    eapply eval_lifted_expression; eassumption.
  }
  assert (Hstep' : natural_step i η ρ' A A' MS MS').
  {
    intros x y a a' R m n Hxy (Ha & Ha' & HR) Hmn.
    assert (Haraw : eval_exp A (extend_env η' y) a') by
      (eapply eval_lifted_expression_back; eassumption).
    destruct (Hstep _ _ _ _ _ _ _ Hxy (conj Ha (conj Haraw HR)) Hmn) as
      (b & b' & S & u & v & (Hb & Hb' & HT) & Hu & Hv & Huv).
    exists b, b', S, u, v. repeat split; try assumption.
    - eapply eval_lifted_expression; eassumption.
    - eapply eval_lifted_expression; [exact (eval_sub_lift _ _ _ _ Hη') | exact Hv].
  }
  destruct (Hmot _ _ natural_values_zero) as (bz & bz' & Z & Hbz & Hbz' & HZsem).
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _ HZ HΔ
    (eval_at_argument _ _ _ _ _ (eval_exp_zero η) Hbz) HZsem)
    as (mz & mz' & Hmz & Hmz' & Hmzz).
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _ HM HΔ
    (eval_exp_nat η) (semantic_natural 0)) as (x & y & Hx & Hy & Hxy).
  assert (HZr : eval_exp (a_sub MZ σ) ρ' mz') by (eapply eval_exp_sub; eassumption).
  assert (HBZr : eval_exp A' (extend_env ρ' d_zero) bz') by
    (eapply eval_lifted_expression; eassumption).
  destruct (interpreted_natural_recursion_values _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Hmot' Hstep' (conj Hbz (conj HBZr HZsem)) Hmz HZr Hmzz _ _ Hxy) as
    (a & a' & R & m & n & (Ha & Ha' & HR) & Hm & Hn & Hmn).
  assert (Haraw : eval_exp A (extend_env η' y) a')
    by (eapply eval_lifted_expression_back; eassumption).
  exists a, a', R, m, n. repeat split; try assumption.
  - eapply eval_substitution_codomain; [exact Hη | | exact Ha].
    eapply eval_exp_sub; eassumption.
  - eapply eval_substitution_codomain; [exact Hη' | | exact Haraw].
    eapply eval_exp_sub; eassumption.
  - eapply eval_exp_sub; [exact Hη | eapply eval_exp_natrec; eassumption].
  - eapply eval_exp_natrec; [eapply eval_exp_sub; eassumption | exact Hn].
Qed.

Local Lemma eval_equation_lifted σ ρ η B x y p b :
  eval_sub σ ρ η ->
  eval_exp B (equation_environment η x y p) b ->
  eval_exp (a_sub B (Syntax.q (Syntax.q (Syntax.q σ)))) (equation_environment ρ x y p) b.
Proof.
  intros Hσ HB. unfold equation_environment in *.
  eapply eval_lifted_expression; [apply eval_sub_lift, eval_sub_lift; exact Hσ | exact HB].
Qed.

Local Lemma eval_equation_substituted_type σ ρ η B M1 M2 P x y p b :
  eval_sub σ ρ η -> eval_exp M1 η x -> eval_exp M2 η y -> eval_exp P η p ->
  eval_exp B (equation_environment η x y p) b ->
  eval_exp (a_sub B (a_extend (a_extend (a_extend σ (a_sub M1 σ)) (a_sub M2 σ)) (a_sub P σ))) ρ b.
Proof.
  intros Hσ H1 H2 HP HB.
  eapply eval_exp_sub; [ | exact HB].
  do 3 (eapply eval_sub_extend; [ | eapply eval_exp_sub; eassumption]).
  exact Hσ.
Qed.

Local Lemma interpreted_equation_substitution Γ Δ i j σ A B BR M1 M2 P :
  interpreted_substitution Γ Δ σ σ ->
  interpreted_type Δ i A A ->
  interpreted_term Δ A M1 M1 ->
  interpreted_term Δ A M2 M2 ->
  interpreted_type (equation_context Δ A) j B B ->
  interpreted_term (A :: Δ) (equation_refl_type A B) BR BR ->
  interpreted_term Δ (a_eq A M1 M2) P P ->
  interpreted_term Γ (a_sub B (a_extend (a_extend (a_extend σ (a_sub M1 σ)) (a_sub M2 σ)) (a_sub P σ)))
    (a_sub (a_eqrec A B BR M1 M2 P) σ)
    (a_eqrec (a_sub A σ) (a_sub B (Syntax.q (Syntax.q (Syntax.q σ))))
      (a_sub BR (Syntax.q σ)) (a_sub M1 σ) (a_sub M2 σ) (a_sub P σ)).
Proof.
  intros Hσ HA HM1 HM2 HB HBR HP. exists j. intros ρ ρ' Hρ.
  destruct (Hσ _ _ Hρ) as (η & η' & Hη & Hη' & HΔ).
  destruct (HA _ _ HΔ) as (a & a' & R & Ha & Ha' & HR).
  pose proof (interpreted_equation_motive _ _ _ _ _ _ _ _ _ _ _
    HA HB HΔ Ha HR) as Hfam.
  pose proof (interpreted_equation_refl_case _ _ _ _ _ _ _ _ _ _ _ _ _
    HA HB HBR HΔ Ha HR) as Hstep.
  set (B' := a_sub B (Syntax.q (Syntax.q (Syntax.q σ)))).
  set (BR' := a_sub BR (Syntax.q σ)).
  assert (Hfam' : equation_motive j η ρ' R B B').
  {
    intros x x' y y' p p' Hxx Hyy Hpp.
    destruct (Hfam _ _ _ _ _ _ Hxx Hyy Hpp) as (b & b' & T & Hb & Hb' & HT).
    exists b, b', T. repeat split; try assumption.
    eapply eval_equation_lifted; eassumption.
  }
  assert (Hstep' : equation_refl_case j η ρ' R B B' BR BR').
  {
    intros x y Hxy.
    destruct (Hstep _ _ Hxy) as (b & b' & T & m & n & Hb & Hb' & HT & Hm & Hn & Hmn).
    exists b, b', T, m, n. repeat split; try assumption.
    - eapply eval_equation_lifted; eassumption.
    - eapply eval_lifted_expression; eassumption.
  }
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _ HM1 HΔ Ha HR) as (x & x' & Hx & Hx' & Hxx).
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _ HM2 HΔ Ha HR) as (y & y' & Hy & Hy' & Hyy).
  pose proof (eval_exp_eq _ _ _ _ _ _ _ Ha Hx Hy) as HE.
  pose proof (semantic_equality _ _ _ _ _ _ _ _ HR Hxx Hyy) as HSEM.
  destruct (interpreted_value_at _ _ _ _ _ _ _ _ _ _ HP HΔ HE HSEM) as (p & p' & Hp & Hp' & Hpp).
  destruct (Hfam _ _ _ _ _ _ Hxx Hyy Hpp) as (b & b' & T & Hb & Hb' & HT).
  assert (Hb'new : eval_exp B' (equation_environment ρ' x' y' p') b')
    by (eapply eval_equation_lifted; eassumption).
  destruct (related_equation_recursion_values _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HB Hfam' (per_left _ _ _ (environments_per Δ) HΔ) Ha HR Hxx Hyy Hpp Hb Hb'new HT Hstep')
    as (m & m' & Hm & Hm' & Hmm').
  exists b, b', T, m, m'. repeat split; try assumption.
  - eapply eval_equation_substituted_type; eassumption.
  - eapply eval_equation_substituted_type; eassumption.
  - eapply eval_exp_sub; [exact Hη | eapply eval_exp_eqrec; eassumption].
  - eapply eval_exp_eqrec;
      try (eapply eval_exp_sub; eassumption); exact Hm'.
Qed.

Local Lemma eval_replace_argument_type B M N :
  evaluation_preserved M N ->
  evaluation_preserved (a_sub B (a_extend a_id M)) (a_sub B (a_extend a_id N)).
Proof.
  intros H ρ d E.
  destruct (invert_eval_substitution _ _ _ _ E) as (η & Hη & HB).
  inversion Hη; subst.
  match goal with HI : eval_sub a_id _ _ |- _ => inversion HI; subst end.
  eapply eval_at_argument; [eapply H; eassumption | exact HB].
Qed.

Local Lemma interpreted_pi_type Γ i A A' B B' :
  interpreted_type Γ i A A' -> interpreted_type (A :: Γ) i B B' ->
  interpreted_type Γ i (a_pi A B) (a_pi A' B').
Proof. intros H K. exact (proj1 (interpreted_dependent_type _ _ _ _ _ _ H K)). Qed.

Local Lemma interpreted_pi_type_substitution Γ Δ i σ A B :
  interpreted_substitution Γ Δ σ σ ->
  interpreted_type Δ i A A -> interpreted_type (A :: Δ) i B B ->
  interpreted_type Γ i (a_sub (a_pi A B) σ)
    (a_pi (a_sub A σ) (a_sub B (Syntax.q σ))).
Proof. intros H K L. exact (proj1 (interpreted_dependent_substitution _ _ _ _ _ _ H K L)). Qed.

Local Lemma interpreted_pi_subtyping Γ i A A' B B' :
  interpreted_type Γ i A A' ->
  interpreted_subtyping (A' :: Γ) B B' ->
  interpreted_subtyping Γ (a_pi A B) (a_pi A' B').
Proof. intros H K. exact (proj1 (interpreted_dependent_subtyping _ _ _ _ _ _ H K)). Qed.

Local Lemma interpreted_sigma_type Γ i A A' B B' :
  interpreted_type Γ i A A' -> interpreted_type (A :: Γ) i B B' ->
  interpreted_type Γ i (a_sigma A B) (a_sigma A' B').
Proof. intros H K. exact (proj2 (interpreted_dependent_type _ _ _ _ _ _ H K)). Qed.

Local Lemma interpreted_sigma_type_substitution Γ Δ i σ A B :
  interpreted_substitution Γ Δ σ σ ->
  interpreted_type Δ i A A -> interpreted_type (A :: Δ) i B B ->
  interpreted_type Γ i (a_sub (a_sigma A B) σ)
    (a_sigma (a_sub A σ) (a_sub B (Syntax.q σ))).
Proof. intros H K L. exact (proj2 (interpreted_dependent_substitution _ _ _ _ _ _ H K L)). Qed.

Local Lemma interpreted_sigma_subtyping Γ i A A' B B' :
  interpreted_type Γ i A A' ->
  interpreted_subtyping (A' :: Γ) B B' ->
  interpreted_subtyping Γ (a_sigma A B) (a_sigma A' B').
Proof. intros H K. exact (proj2 (interpreted_dependent_subtyping _ _ _ _ _ _ H K)). Qed.

Local Ltac interpreted_type_assumption :=
  first [eassumption | solve [eapply interpreted_terms_as_types; eassumption] |
    eapply interpreted_type_left; eapply interpreted_terms_as_types; eassumption].

Local Ltac interpreted_type_constructor derive :=
  apply interpreted_types_as_terms;
  derive;
  interpreted_type_assumption.

Local Ltac interpreted_beta derive rule :=
  eapply interpreted_by_evaluation;
    [ | apply evaluation_preserved_refl | apply evaluation_preserved_refl | apply rule];
  derive.

Local Ltac declarative_constructor derivation :=
  lazymatch derivation with
  | ?f ?arg => declarative_constructor f
  | _ => derivation
  end.

Local Ltac interpret_self_lambda :=
  match goal with |- interpreted_term _ (a_pi ?A _) _ _ =>
    eapply interpreted_lambda with (A' := A); interpreted_type_assumption
  end.

Local Ltac interpret_self_pair :=
  match goal with |- interpreted_term _ (a_sigma ?A ?B) _ _ =>
    eapply interpreted_pair with (A' := A) (B' := B); interpreted_type_assumption
  end.

Local Ltac interpret_declarative_rule head :=
  lazymatch head with
  | wf_ctx_empty => apply interpreted_empty
  | wf_ctx_extend => eapply interpreted_extension; interpreted_type_assumption
  | wf_ctx_sub_empty => intros; apply related_empty
  | wf_ctx_sub_extend => eapply interpreted_context_inclusion; eassumption
  | wf_typ => apply interpreted_universe_constructor
  | wf_nat => apply interpreted_natural_constructor
  | wf_zero => apply interpreted_zero_constructor
  | wf_succ => now apply interpreted_successor_constructor
  | wf_natrec => eapply interpreted_natural_recursion; interpreted_type_assumption
  | wf_pi => interpreted_type_constructor ltac:(eapply interpreted_pi_type)
  | wf_fn => eapply interpreted_lambda; interpreted_type_assumption
  | wf_app => eapply interpreted_application; eassumption
  | wf_sigma => interpreted_type_constructor ltac:(eapply interpreted_sigma_type)
  | wf_pair => eapply interpreted_pair; interpreted_type_assumption
  | wf_fst => eapply interpreted_fst; eassumption
  | wf_snd => eapply interpreted_snd; eassumption
  | wf_vlookup => eapply interpreted_lookup; eassumption
  | wf_eq => apply interpreted_types_as_terms; eapply interpreted_equality_type; interpreted_type_assumption
  | wf_refl => now apply interpreted_refl
  | wf_eqrec => eapply interpreted_equality_recursion; interpreted_type_assumption
  | wf_exp_sub => eapply interpreted_term_substitution; eassumption
  | wf_exp_subtyp => eapply interpreted_term_subtyping; eassumption
  | wf_exp_eq_typ_sub => eapply interpreted_substitution_universe_eq; eassumption
  | wf_exp_eq_nat_sub => eapply interpreted_substitution_naturals_eq; eassumption
  | wf_exp_eq_zero_sub => eapply interpreted_substitution_zero_eq; eassumption
  | wf_exp_eq_succ_sub => eapply interpreted_substitution_successor_eq; eassumption
  | wf_exp_eq_succ_cong => now apply interpreted_successor_constructor
  | wf_exp_eq_natrec_cong => eapply interpreted_natural_recursion; interpreted_type_assumption
  | wf_exp_eq_natrec_sub => eapply interpreted_recursion_substitution; interpreted_type_assumption
  | wf_exp_eq_nat_beta_zero =>
      interpreted_beta ltac:(eapply interpreted_natural_recursion;
        first [interpreted_type_assumption | apply interpreted_zero_constructor]) eval_natural_beta_zero
  | wf_exp_eq_nat_beta_succ =>
      interpreted_beta ltac:(eapply interpreted_natural_recursion;
        first [interpreted_type_assumption | now apply interpreted_successor_constructor]) eval_natural_beta_succ
  | wf_exp_eq_pi_sub => interpreted_type_constructor ltac:(eapply interpreted_pi_type_substitution)
  | wf_exp_eq_pi_cong => interpreted_type_constructor ltac:(eapply interpreted_pi_type)
  | wf_exp_eq_fn_cong => eapply interpreted_lambda; interpreted_type_assumption
  | wf_exp_eq_fn_sub =>
      eapply interpreted_function_substitution_eq; [eassumption | eapply interpreted_lambda; interpreted_type_assumption]
  | wf_exp_eq_app_cong => eapply interpreted_application; eassumption
  | wf_exp_eq_app_sub =>
      eapply interpreted_explicit_substitution_eq;
        [eassumption | eapply interpreted_application; eassumption |
          apply eval_distribute_argument_type, evaluation_preserved_refl | apply eval_distribute_app]
  | wf_exp_eq_pi_beta =>
      interpreted_beta ltac:(eapply interpreted_application;
        [interpret_self_lambda | eassumption]) eval_function_beta
  | wf_exp_eq_pi_eta => now apply interpreted_function_eta
  | wf_exp_eq_sigma_sub => interpreted_type_constructor ltac:(eapply interpreted_sigma_type_substitution)
  | wf_exp_eq_sigma_cong => interpreted_type_constructor ltac:(eapply interpreted_sigma_type)
  | wf_exp_eq_pair_cong => eapply interpreted_pair; interpreted_type_assumption
  | wf_exp_eq_pair_sub =>
      eapply interpreted_explicit_substitution_eq;
        [eassumption | eapply interpreted_pair; interpreted_type_assumption |
          apply evaluation_preserved_refl | apply eval_distribute_pair]
  | wf_exp_eq_fst_cong => eapply interpreted_fst; eassumption
  | wf_exp_eq_fst_sub =>
      eapply interpreted_explicit_substitution_eq;
        [eassumption | eapply interpreted_fst; eassumption |
          apply evaluation_preserved_refl | apply eval_distribute_fst]
  | wf_exp_eq_snd_cong => eapply interpreted_snd; eassumption
  | wf_exp_eq_snd_sub =>
      eapply interpreted_explicit_substitution_eq;
        [eassumption | eapply interpreted_snd; eassumption |
          apply eval_distribute_argument_type, eval_distribute_fst | apply eval_distribute_snd]
  | wf_exp_eq_fst_beta =>
      interpreted_beta ltac:(eapply interpreted_fst; interpret_self_pair) eval_fst_beta
  | wf_exp_eq_snd_beta =>
      eapply interpreted_by_evaluation;
        [ | apply eval_replace_argument_type, eval_fst_beta |
          apply evaluation_preserved_refl | apply eval_snd_beta];
      eapply interpreted_snd; interpret_self_pair
  | wf_exp_eq_sigma_eta => now apply interpreted_pair_eta
  | wf_exp_eq_eq_sub =>
      eapply interpreted_explicit_substitution_eq;
        [eassumption | apply interpreted_types_as_terms; eapply interpreted_equality_type;
          interpreted_type_assumption | intros ρ d HE; eapply eval_sub_universe; exact HE | apply eval_distribute_equality]
  | wf_exp_eq_refl_sub =>
      eapply interpreted_explicit_substitution_eq;
        [eassumption | apply interpreted_refl; eassumption | apply evaluation_preserved_refl | apply eval_distribute_refl]
  | wf_exp_eq_eqrec_sub => eapply interpreted_equation_substitution; interpreted_type_assumption
  | wf_exp_eq_eq_cong => apply interpreted_types_as_terms; eapply interpreted_equality_type; interpreted_type_assumption
  | wf_exp_eq_refl_cong => now apply interpreted_refl
  | wf_exp_eq_eqrec_cong => eapply interpreted_equality_recursion; interpreted_type_assumption
  | wf_exp_eq_eqrec_beta =>
      interpreted_beta ltac:(eapply interpreted_equality_recursion;
        first [interpreted_type_assumption | now apply interpreted_refl]) eval_equation_beta
  | wf_exp_eq_var => eapply interpreted_lookup; eassumption
  | wf_exp_eq_var_0_sub => eapply interpreted_variable_zero_eq; eassumption
  | wf_exp_eq_var_S_sub =>
      eapply interpreted_variable_succ_eq; [eassumption | eassumption | eapply interpreted_lookup; eassumption]
  | wf_exp_eq_var_weaken =>
      apply interpreted_variable_weaken_eq;
      eapply interpreted_lookup; [now apply there | assumption]
  | wf_exp_eq_sub_cong => eapply interpreted_term_substitution; eassumption
  | wf_exp_eq_sub_id => now apply interpreted_term_identity_eq
  | wf_exp_eq_sub_compose => eapply interpreted_term_composition_eq; eassumption
  | wf_exp_eq_subtyp => eapply interpreted_term_subtyping; eassumption
  | wf_exp_eq_sym => now apply interpreted_equality_sym
  | wf_exp_eq_trans => eapply interpreted_equality_trans; eassumption
  | wf_sub_id => split; [assumption | apply interpreted_substitution_id]
  | wf_sub_weaken => split; [solve [match goal with H : interpreted_context (_ :: _) |- _ => inversion H; assumption end] |
      apply interpreted_substitution_weaken]
  | wf_sub_compose => split; [assumption | eapply interpreted_substitution_compose; eassumption]
  | wf_sub_extend => split; [eapply interpreted_extension; interpreted_type_assumption |
      eapply interpreted_substitution_extend; interpreted_type_assumption]
  | wf_sub_subtyp => split; [assumption | eapply interpreted_substitution_widen; eassumption]
  | wf_sub_eq_id => apply interpreted_substitution_id
  | wf_sub_eq_weaken => apply interpreted_substitution_weaken
  | wf_sub_eq_compose_cong => eapply interpreted_substitution_compose; eassumption
  | wf_sub_eq_extend_cong => eapply interpreted_substitution_extend; interpreted_type_assumption
  | wf_sub_eq_id_compose_right => now apply interpreted_substitution_right_identity
  | wf_sub_eq_id_compose_left => now apply interpreted_substitution_left_identity
  | wf_sub_eq_compose_assoc => eapply interpreted_substitution_assoc; eassumption
  | wf_sub_eq_extend_compose => eapply interpreted_substitution_extend_compose; interpreted_type_assumption
  | wf_sub_eq_p_extend => eapply interpreted_substitution_project;
      eapply interpreted_substitution_extend; interpreted_type_assumption
  | wf_sub_eq_extend => now apply interpreted_substitution_eta
  | wf_sub_eq_sym => now apply interpreted_substitution_sym
  | wf_sub_eq_trans => eapply interpreted_substitution_trans; eassumption
  | wf_sub_eq_subtyp => eapply interpreted_substitution_widen; eassumption
  | wf_subtyp_refl => eapply interpreted_subtyping_reflexive; interpreted_type_assumption
  | wf_subtyp_trans => eapply interpreted_subtyping_transitive; eassumption
  | wf_subtyp_univ => now apply interpreted_subtyping_universes
  | wf_subtyp_pi => eapply interpreted_pi_subtyping; interpreted_type_assumption
  | wf_subtyp_sigma => eapply interpreted_sigma_subtyping; interpreted_type_assumption
  end.

Local Lemma declarative_interpretation :
  (forall Γ, wf_ctx Γ -> interpreted_context Γ) /\
  (forall Γ Δ, wf_ctx_sub Γ Δ ->
    forall ρ ρ', related_environments Γ ρ ρ' -> related_environments Δ ρ ρ') /\
  (forall Γ A M, wf_exp Γ A M -> interpreted_term Γ A M M) /\
  (forall Γ A M N, wf_exp_eq Γ A M N -> interpreted_term Γ A M N) /\
  (forall Γ Δ σ, wf_sub Γ Δ σ ->
    interpreted_context Δ /\ interpreted_substitution Γ Δ σ σ) /\
  (forall Γ Δ σ τ, wf_sub_eq Γ Δ σ τ -> interpreted_substitution Γ Δ σ τ) /\
  (forall Γ A B, wf_subtyp Γ A B -> interpreted_subtyping Γ A B).
Proof.
  eapply (syntactic_wf_mut_ind
    (fun Γ d => let origin := d in interpreted_context Γ)
    (fun Γ Δ d => let origin := d in
      forall ρ ρ', related_environments Γ ρ ρ' -> related_environments Δ ρ ρ')
    (fun Γ A M d => let origin := d in interpreted_term Γ A M M)
    (fun Γ A M N d => let origin := d in interpreted_term Γ A M N)
    (fun Γ Δ σ d => let origin := d in interpreted_context Δ /\ interpreted_substitution Γ Δ σ σ)
    (fun Γ Δ σ τ d => let origin := d in interpreted_substitution Γ Δ σ τ)
    (fun Γ A B d => let origin := d in interpreted_subtyping Γ A B)).
  all: intros.
  all: repeat match goal with H : (let _ := _ in _) |- _ => progress cbv zeta in H end.
  all: repeat match goal with H : interpreted_context _ /\ interpreted_substitution _ _ _ _ |- _ => destruct H end.
  all: match goal with origin := ?rule |- _ =>
    let head := declarative_constructor rule in interpret_declarative_rule head
  end.
Qed.

Local Lemma equal_types_have_shared_readback : type_equality_has_common_readback.
Proof.
  destruct declarative_interpretation as [Hctx [_ [_ [Heq _]]]].
  exact (shared_type_readback_from_interpretation Hctx Heq).
Qed.

Local Lemma declarative_readback_total : readback_total.
Proof. exact (readback_total_from_type_equality equal_types_have_shared_readback). Qed.

(* Substitution equations for reconstructing typed readback. *)

Local Lemma substitution_source Γ Δ σ :
  {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Γ }}.
Proof. intro H. exact (proj1 (proj2 typing_contexts _ _ _ H)). Qed.

Local Lemma substitution_target Γ Δ σ :
  {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Δ }}.
Proof. intro H. exact (proj2 (proj2 typing_contexts _ _ _ H)). Qed.

Local Lemma equality_under_substitution Γ Δ σ A M N :
  {{ Γ ⊢s σ : Δ }} ->
  {{ Δ ⊢ M ≈ N : A }} ->
  {{ Γ ⊢ M[σ] ≈ N[σ] : A[σ] }}.
Proof. eauto using wf_exp_eq_sub_cong, substitution_equality_reflexive. Qed.

Local Lemma type_substitution_equality_same_body Γ Δ σ τ A i :
  {{ Γ ⊢s σ : Δ }} ->
  {{ Γ ⊢s σ ≈ τ : Δ }} ->
  {{ Δ ⊢ A : Type@i }} ->
  {{ Γ ⊢ A[σ] ≈ A[τ] : Type@i }}.
Proof. eauto using type_substitution_congruence, expression_equality_reflexive. Qed.

Local Lemma last_variable_after_lifting Γ Δ σ A i :
  {{ Γ ⊢s σ : Δ }} ->
  {{ Δ ⊢ A : Type@i }} ->
  {{ Γ, A[σ] ⊢ #0 : A[σ∘Wk] }}.
Proof.
  intros Hσ HA.
  assert (HAs : {{ Γ ⊢ A[σ] : Type@i }}) by eauto using type_substitution.
  assert (HC : {{ ⊢ Γ, A[σ] }}) by eauto using wf_ctx_extend, substitution_source.
  assert (Hwk : {{ Γ, A[σ] ⊢s Wk : Γ }}) by now apply wf_sub_weaken.
  apply (convert_term _ _ {{{ A[σ][Wk] }}} _ i).
  - apply wf_vlookup; [exact HC | apply here].
  - eapply type_substitution; [ | exact HA].
    eapply wf_sub_compose; eassumption.
  - apply wf_exp_eq_sym. eapply type_substitution_composition; eassumption.
Qed.

Local Lemma lift_composition Γ Δ Θ σ τ A i :
  {{ Γ ⊢s σ : Δ }} ->
  {{ Δ ⊢ A : Type@i }} ->
  {{ Θ ⊢s τ : Γ, A[σ] }} ->
  {{ Θ ⊢s (q σ)∘τ ≈ (σ∘(Wk∘τ)),,#0[τ] : Δ, A }}.
Proof.
  intros Hσ HA Hτ.
  assert (Hw : {{ Γ, A[σ] ⊢s Wk : Γ }})
    by eauto using wf_sub_weaken, substitution_target.
  assert (HS : {{ Γ, A[σ] ⊢s σ∘Wk : Δ }}) by eauto using wf_sub_compose.
  assert (Hlast : {{ Γ, A[σ] ⊢ #0 : A[σ∘Wk] }}) by eauto using last_variable_after_lifting.
  assert (Htail : {{ Θ ⊢s (σ∘Wk)∘τ : Δ }}) by eauto using wf_sub_compose.
  assert (Hty : {{ Θ ⊢ A[(σ∘Wk)∘τ] : Type@i }}) by eauto using type_substitution.
  assert (HM : {{ Θ ⊢ #0[τ] : A[(σ∘Wk)∘τ] }}).
  {
    eapply convert_term.
    - exact (wf_exp_sub _ _ _ _ _ Hτ Hlast).
    - exact Hty.
    - apply wf_exp_eq_sym. eapply type_substitution_composition; eassumption.
  }
  change {{ Θ ⊢s ((σ∘Wk),,#0)∘τ ≈ (σ∘(Wk∘τ)),,#0[τ] : Δ, A }}.
  eapply wf_sub_eq_trans.
  - exact (wf_sub_eq_extend_compose _ _ _ _ _ _ _ _ HS HA Hlast Hτ).
  - eapply wf_sub_eq_extend_cong.
    + exact (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ Hσ Hw Hτ).
    + exact HA.
    + now apply expression_equality_reflexive.
Qed.

Local Lemma lift_at_argument Γ Δ σ A M i :
  {{ Γ ⊢s σ : Δ }} ->
  {{ Δ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A[σ] }} ->
  {{ Γ ⊢s (q σ)∘(Id,,M) ≈ σ,,M : Δ, A }}.
Proof.
  intros Hσ HA HM.
  assert (HΓ : {{ ⊢ Γ }}) by eauto using substitution_source.
  assert (Hid : {{ Γ ⊢s Id : Γ }}) by now apply wf_sub_id.
  assert (HAs : {{ Γ ⊢ A[σ] : Type@i }}) by eauto using type_substitution.
  assert (Ht : {{ Γ ⊢s Id,,M : Γ, A[σ] }}) by eauto using typing_identity_extension.
  assert (HMi : {{ Γ ⊢ M : A[σ][Id] }}).
  {
    eapply convert_term; [exact HM | |].
    - eapply type_substitution; eassumption.
    - apply wf_exp_eq_sym, wf_exp_eq_sub_id. exact HAs.
  }
  assert (Hw : {{ Γ, A[σ] ⊢s Wk : Γ }}) by eauto using wf_sub_weaken, substitution_target.
  assert (Htail : {{ Γ ⊢s σ∘(Wk∘(Id,,M)) : Δ }}) by eauto using wf_sub_compose.
  assert (Htail_eq : {{ Γ ⊢s σ∘(Wk∘(Id,,M)) ≈ σ : Δ }}).
  {
    eapply wf_sub_eq_trans with (σ' := {{{ σ∘Id }}}).
    - eapply wf_sub_eq_compose_cong.
      + exact (wf_sub_eq_p_extend _ _ _ _ _ _ Hid HAs HMi).
      + now apply substitution_equality_reflexive.
    - now apply wf_sub_eq_id_compose_left.
  }
  eapply wf_sub_eq_trans.
  - exact (lift_composition _ _ _ _ _ _ _ Hσ HA Ht).
  - eapply wf_sub_eq_extend_cong; [exact Htail_eq | exact HA |].
    eapply convert_equality.
    + exact (wf_exp_eq_var_0_sub _ _ _ _ _ _ Hid HAs HMi).
    + eapply type_substitution; eassumption.
    + eapply wf_exp_eq_trans.
      * apply wf_exp_eq_sub_id. exact HAs.
      * apply wf_exp_eq_sym.
        eapply type_substitution_equality_same_body; eassumption.
Qed.

Local Lemma type_lift_at_argument Γ Δ σ A B M i j :
  {{ Γ ⊢s σ : Δ }} ->
  {{ Δ ⊢ A : Type@i }} ->
  {{ Δ, A ⊢ B : Type@j }} ->
  {{ Γ ⊢ M : A[σ] }} ->
  {{ Γ ⊢ B[q σ][Id,,M] ≈ B[σ,,M] : Type@j }}.
Proof.
  intros Hσ HA HB HM.
  assert (HAs : {{ Γ ⊢ A[σ] : Type@i }}) by eauto using type_substitution.
  assert (Hq : {{ Γ, A[σ] ⊢s q σ : Δ, A }}) by eauto using lifted_substitution.
  assert (Ht : {{ Γ ⊢s Id,,M : Γ, A[σ] }}) by eauto using typing_identity_extension.
  eapply wf_exp_eq_trans.
  - apply wf_exp_eq_sym. eapply type_substitution_composition; eassumption.
  - eapply type_substitution_equality_same_body.
    + eapply wf_sub_compose; eassumption.
    + exact (lift_at_argument _ _ _ _ _ _ Hσ HA HM).
    + exact HB.
Qed.

Local Lemma identity_with_last_variable Γ A i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢s Wk,,#0 ≈ Id : Γ, A }}.
Proof.
  intro HA.
  assert (HΓA : {{ ⊢ Γ, A }}) by eauto using wf_ctx_extend, typing_context.
  assert (Hw : {{ Γ, A ⊢s Wk : Γ }}) by now apply wf_sub_weaken.
  assert (Hid : {{ Γ, A ⊢s Id : Γ, A }}) by now apply wf_sub_id.
  assert (Hhead : {{ Γ, A ⊢ #0 : A[Wk] }}) by (apply wf_vlookup; [assumption | apply here]).
  pose proof (wf_sub_eq_id_compose_left _ _ _ Hw) as Hw_eq.
  eapply wf_sub_eq_trans.
  - apply wf_sub_eq_sym.
    eapply wf_sub_eq_extend_cong; [exact Hw_eq | exact HA |].
    eapply convert_equality.
    + apply wf_exp_eq_sub_id. exact Hhead.
    + eapply type_substitution; [eapply wf_sub_compose; eassumption | exact HA].
    + apply wf_exp_eq_sym.
      eapply type_substitution_equality_same_body; [eapply wf_sub_compose; eassumption | exact Hw_eq | exact HA].
  - apply wf_sub_eq_sym. exact (wf_sub_eq_extend _ _ _ _ Hid).
Qed.

Local Lemma eta_codomain Γ A B i j :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@j }} ->
  {{ Γ, A ⊢ B[q Wk][Id,,#0] ≈ B : Type@j }}.
Proof.
  intros HA HB.
  assert (HΓA : {{ ⊢ Γ, A }}) by eauto using wf_ctx_extend, typing_context.
  assert (Hw : {{ Γ, A ⊢s Wk : Γ }}) by now apply wf_sub_weaken.
  assert (Hhead : {{ Γ, A ⊢ #0 : A[Wk] }}) by (apply wf_vlookup; [assumption | apply here]).
  eapply wf_exp_eq_trans with (M' := {{{ B[Wk,,#0] }}}).
  - exact (type_lift_at_argument _ _ _ _ _ _ _ _ Hw HA HB Hhead).
  - eapply wf_exp_eq_trans with (M' := {{{ B[Id] }}}).
    + eapply type_substitution_equality_same_body.
      * exact (wf_sub_extend _ _ _ _ _ _ Hw HA Hhead).
      * exact (identity_with_last_variable _ _ _ HA).
      * exact HB.
    + apply wf_exp_eq_sub_id. exact HB.
Qed.

Local Lemma eta_body_typing Γ A B F i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ F : Π A B }} ->
  {{ Γ, A ⊢ F[Wk] #0 : B }}.
Proof.
  intros HA HB HF.
  assert (HΓA : {{ ⊢ Γ, A }}) by eauto using wf_ctx_extend, typing_context.
  assert (Hw : {{ Γ, A ⊢s Wk : Γ }}) by now apply wf_sub_weaken.
  assert (HAw : {{ Γ, A ⊢ A[Wk] : Type@i }}) by eauto using type_substitution.
  assert (Hqw : {{ Γ, A, A[Wk] ⊢s q Wk : Γ, A }})
    by eauto using lifted_substitution.
  assert (HBq : {{ Γ, A, A[Wk] ⊢ B[q Wk] : Type@i }})
    by eauto using type_substitution.
  assert (HFw : {{ Γ, A ⊢ F[Wk] : Π A[Wk] B[q Wk] }}).
  {
    eapply convert_term.
    - exact (wf_exp_sub _ _ _ _ _ Hw HF).
    - exact (wf_pi _ _ _ _ HAw HBq).
    - exact (wf_exp_eq_pi_sub _ _ _ _ _ _ Hw HA HB).
  }
  eapply convert_term; [ | exact HB | exact (eta_codomain _ _ _ _ _ HA HB)].
  eapply wf_app with (i := i); try eassumption.
  apply wf_vlookup; [exact HΓA | apply here].
Qed.

Local Lemma identity_argument_equality Γ A M N i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M ≈ N : A }} ->
  {{ Γ ⊢s Id,,M ≈ Id,,N : Γ, A }}.
Proof.
  intros HA HMN.
  pose proof (typing_context _ _ _ HA) as HΓ.
  assert (Hid : {{ Γ ⊢s Id : Γ }}) by now apply wf_sub_id.
  eapply wf_sub_eq_extend_cong; [now apply wf_sub_eq_id | exact HA |].
  eapply convert_equality.
  - exact HMN.
  - eapply type_substitution; eassumption.
  - apply wf_exp_eq_sym, wf_exp_eq_sub_id. exact HA.
Qed.

Local Lemma reconstruct_readback_lambda Γ A A' B F N i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ A' : Type@i }} ->
  {{ Γ ⊢ A ≈ A' : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ F : Π A B }} ->
  {{ Γ, A ⊢ N : B }} ->
  {{ Γ, A ⊢ F[Wk] #0 ≈ N : B }} ->
  {{ Γ ⊢ λ A' N : Π A B }} /\ {{ Γ ⊢ F ≈ λ A' N : Π A B }}.
Proof.
  intros HA HA' HAA' HB HF HN HE.
  split.
  - eapply convert_term with (A := {{{ Π A' B }}}).
    + apply wf_fn with (i := i); [exact HA' |].
      exact (change_binder _ _ _ _ _ _ HA HA' HAA' HN).
    + exact (wf_pi _ _ _ _ HA HB).
    + apply wf_exp_eq_sym, wf_exp_eq_pi_cong with (i := i);
        auto using expression_equality_reflexive.
  - eapply wf_exp_eq_trans with (M' := {{{ λ A (F[Wk] #0) }}}).
    + exact (wf_exp_eq_pi_eta _ _ _ _ _ HA HB HF).
    + exact (wf_exp_eq_fn_cong _ _ _ _ _ _ _ HA HAA' HE).
Qed.

Local Lemma reconstruct_readback_pair Γ A A' B B' P M N i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ A' : Type@i }} ->
  {{ Γ ⊢ A ≈ A' : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ, A ⊢ B' : Type@i }} ->
  {{ Γ, A ⊢ B ≈ B' : Type@i }} ->
  {{ Γ ⊢ P : Σ A B }} ->
  {{ Γ ⊢ M : A }} ->
  {{ Γ ⊢ fst P ≈ M : A }} ->
  {{ Γ ⊢ N : B[Id,,fst P] }} ->
  {{ Γ ⊢ snd P ≈ N : B[Id,,fst P] }} ->
  {{ Γ ⊢ ⟨ M : A' ; N : B' ⟩ : Σ A B }} /\
  {{ Γ ⊢ P ≈ ⟨ M : A' ; N : B' ⟩ : Σ A B }}.
Proof.
  intros HA HA' HAA' HB HB' HBB' HP HM Hfst HN Hsnd.
  assert (HfstT : {{ Γ ⊢ fst P : A }}) by eauto using wf_fst.
  assert (Hσ : {{ Γ ⊢s Id,,fst P : Γ, A }}) by eauto using typing_identity_extension.
  assert (Hσ' : {{ Γ ⊢s Id,,M : Γ, A }}) by eauto using typing_identity_extension.
  assert (HM' : {{ Γ ⊢ M : A' }}) by eauto using convert_term.
  assert (HB'N : {{ Γ ⊢ B'[Id,,M] : Type@i }}) by eauto using type_substitution.
  assert (HB'new : {{ Γ, A' ⊢ B' : Type@i }}) by
    exact (change_binder _ _ _ _ _ _ HA HA' HAA' HB').
  assert (HNN : {{ Γ ⊢ N : B'[Id,,M] }}).
  {
    eapply convert_term; [exact HN | exact HB'N |].
    eapply type_substitution_congruence; [exact Hσ | | exact HBB'].
    exact (identity_argument_equality _ _ _ _ _ HA Hfst).
  }
  split.
  - eapply convert_term with (A := {{{ Σ A' B' }}}).
    + exact (wf_pair _ _ _ _ _ _ HA' HB'new HM' HNN).
    + exact (wf_sigma _ _ _ _ HA HB).
    + apply wf_exp_eq_sym. exact (wf_exp_eq_sigma_cong _ _ _ _ _ _ HA HAA' HBB').
  - eapply wf_exp_eq_trans with (M' := {{{ ⟨ fst P : A ; snd P : B ⟩ }}}).
    + exact (wf_exp_eq_sigma_eta _ _ _ _ _ HA HB HP).
    + exact (wf_exp_eq_pair_cong _ _ _ _ _ _ _ _ _ _ HA HAA' HBB' Hfst Hsnd).
Qed.

Local Lemma reconstruct_readback_refl Γ A A' M N i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ A' : Type@i }} ->
  {{ Γ ⊢ A ≈ A' : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  {{ Γ ⊢ N : A }} ->
  {{ Γ ⊢ M ≈ N : A }} ->
  {{ Γ ⊢ refl A' N : Eq A M M }} /\
  {{ Γ ⊢ refl A M ≈ refl A' N : Eq A M M }}.
Proof.
  intros HA HA' HE HM HN HMN.
  split.
  - eapply convert_term with (A := {{{ Eq A' N N }}}).
    + apply wf_refl with (i := i); [exact HA' | eauto using convert_term].
    + now apply wf_eq with (i := i).
    + apply wf_exp_eq_sym. exact (wf_exp_eq_eq_cong _ _ _ _ _ _ _ _ HE HMN HMN).
  - exact (wf_exp_eq_refl_cong _ _ _ _ _ _ HE HMN).
Qed.

(* Context extensions keep the levels of existing semantic variables. *)

Inductive context_weakening : ctx -> ctx -> sub -> Prop :=
| context_weakening_id Γ :
    {{ ⊢ Γ }} -> context_weakening Γ Γ a_id
| context_weakening_step Γ Δ σ A i :
    context_weakening Γ Δ σ ->
    {{ Δ ⊢ A : Type@i }} ->
    context_weakening Γ (A :: Δ) (a_compose σ a_weaken).

Local Lemma context_weakening_typed Γ Δ σ :
  context_weakening Γ Δ σ -> {{ Δ ⊢s σ : Γ }}.
Proof.
  induction 1.
  - now apply wf_sub_id.
  - eapply wf_sub_compose; [ | eassumption].
    eauto using wf_sub_weaken, wf_ctx_extend, typing_context.
Qed.

Local Lemma context_weakening_length Γ Δ σ :
  context_weakening Γ Δ σ -> length Γ <= length Δ.
Proof. induction 1; simpl; lia. Qed.

Local Lemma context_weakening_compose Γ Δ Θ σ τ :
  context_weakening Γ Δ σ ->
  context_weakening Δ Θ τ ->
  exists ω, context_weakening Γ Θ ω /\ {{ Θ ⊢s σ∘τ ≈ ω : Γ }}.
Proof.
  intros Hσ Hτ. induction Hτ as [Δ HΔ | Δ Θ τ A i Hτ IH HA].
  - exists σ. split; [exact Hσ |].
    apply wf_sub_eq_id_compose_left. exact (context_weakening_typed _ _ _ Hσ).
  - destruct (IH Hσ) as (ω & Hω & HE).
    exists (a_compose ω a_weaken). split.
    + eapply context_weakening_step; eassumption.
    + assert (Hw : {{ Θ, A ⊢s Wk : Θ }}) by eauto using wf_sub_weaken, wf_ctx_extend, typing_context.
      eapply wf_sub_eq_trans with (σ' := {{{ (σ∘τ)∘Wk }}}).
      * apply wf_sub_eq_sym.
        exact (wf_sub_eq_compose_assoc _ _ _ _ _ _ _
          (context_weakening_typed _ _ _ Hσ) (context_weakening_typed _ _ _ Hτ) Hw).
      * eapply wf_sub_eq_compose_cong; [ | exact HE].
        apply wf_sub_eq_weaken. exact (substitution_source _ _ _ Hw).
Qed.

Local Lemma reconstruct_weakened_variable Γ Δ σ x A :
  context_weakening Γ Δ σ ->
  ctx_lookup x A Γ ->
  exists B i,
    ctx_lookup (x + (length Δ - length Γ)) B Δ /\
    {{ Δ ⊢ A[σ] : Type@i }} /\
    {{ Δ ⊢ B : Type@i }} /\
    {{ Δ ⊢ A[σ] ≈ B : Type@i }} /\
    {{ Δ ⊢ #x[σ] ≈ #(x + (length Δ - length Γ)) : A[σ] }}.
Proof.
  intros HW Hlookup.
  induction HW as [Γ HΓ | Γ Δ σ C j HW IH HC].
  - destruct (lookup_type _ _ _ Hlookup HΓ) as [i HA].
    assert (Hid : {{ Γ ⊢s Id : Γ }}) by now apply wf_sub_id.
    assert (HAid : {{ Γ ⊢ A[Id] : Type@i }}) by eauto using type_substitution.
    assert (HV : {{ Γ ⊢ #x : A }}) by eauto using wf_vlookup.
    rewrite Nat.sub_diag, Nat.add_0_r.
    exists A, i. repeat split; try assumption.
    + apply wf_exp_eq_sub_id. exact HA.
    + eapply convert_equality; [apply wf_exp_eq_sub_id; exact HV | exact HAid |].
      apply wf_exp_eq_sym, wf_exp_eq_sub_id. exact HA.
  - destruct (IH Hlookup) as (B & i & HB & HAσ & HBty & HEty & HE).
    assert (HΔC : {{ ⊢ Δ, C }}) by eauto using wf_ctx_extend, typing_context.
    assert (Hw : {{ Δ, C ⊢s Wk : Δ }}) by now apply wf_sub_weaken.
    pose proof (context_weakening_typed _ _ _ HW) as Hσ.
    pose proof (context_weakening_length _ _ _ HW) as Hle.
    pose proof (substitution_target _ _ _ Hσ) as HΓ.
    destruct (lookup_type _ _ _ Hlookup HΓ) as [k HA].
    (* Both levels are available, so the comparison can take place at their maximum. *)
    set (o := x + (length Δ - length Γ)).
    change (ctx_lookup o B Δ) in HB.
    assert (Hshift : x + (S (length Δ) - length Γ) = S o) by (unfold o; lia).
    change (length (C :: Δ)) with (S (length Δ)).
    rewrite Hshift.
    assert (HAmax : {{ Γ ⊢ A : Type@(Nat.max i k) }}) by eauto using type_cumulativity, Nat.le_max_r.
    assert (HAσmax : {{ Δ ⊢ A[σ] : Type@(Nat.max i k) }}) by eauto using type_cumulativity, Nat.le_max_l.
    assert (HBmax : {{ Δ ⊢ B : Type@(Nat.max i k) }}) by eauto using type_cumulativity, Nat.le_max_l.
    assert (Hcomp : {{ Δ, C ⊢s σ∘Wk : Γ }}) by eauto using wf_sub_compose.
    assert (HNew : {{ Δ, C ⊢ A[σ∘Wk] : Type@(Nat.max i k) }}) by eauto using type_substitution.
    assert (Hcomp_eq : {{ Δ, C ⊢ A[σ∘Wk] ≈ A[σ][Wk] : Type@(Nat.max i k) }})
      by eauto using type_substitution_composition.
    assert (HNew_eq : {{ Δ, C ⊢ A[σ∘Wk] ≈ B[Wk] : Type@(Nat.max i k) }}).
    {
      eapply wf_exp_eq_trans; [exact Hcomp_eq |].
      eapply type_substitution_congruence; [exact Hw | now apply wf_sub_eq_weaken |].
      eapply equality_cumulativity; eauto using substitution_source, Nat.le_max_l.
    }
    exists {{{ B[Wk] }}}, (Nat.max i k). repeat split; try assumption.
    + now apply there.
    + eauto using type_substitution.
    + eapply wf_exp_eq_trans with (M' := {{{ #x[σ][Wk] }}}).
      * exact (wf_exp_eq_sub_compose _ _ _ _ _ _ _ Hw Hσ (wf_vlookup _ _ _ HΓ Hlookup)).
      * eapply wf_exp_eq_trans with (M' := {{{ #o[Wk] }}}).
        -- eapply convert_equality; [exact (equality_under_substitution _ _ _ _ _ _ Hw HE) | exact HNew |].
           now apply wf_exp_eq_sym.
        -- eapply convert_equality; [exact (wf_exp_eq_var_weaken _ _ _ _ HΔC HB) | exact HNew |].
           exact (wf_exp_eq_sym _ _ _ _ HNew_eq).
Qed.

Local Lemma readback_of_weakened_variable Γ Δ σ x A :
  context_weakening Γ Δ σ ->
  ctx_lookup x A Γ ->
  exists n,
    read_ne (length Δ) (d_var (length Γ - x - 1)) n /\
    {{ Δ ⊢ ^(ne_to_exp n) : A[σ] }} /\
    {{ Δ ⊢ #x[σ] ≈ ^(ne_to_exp n) : A[σ] }}.
Proof.
  intros HW HL.
  destruct (reconstruct_weakened_variable _ _ _ _ _ HW HL) as
    (B & i & HB & HA & HT & HEty & HE).
  pose proof (context_weakening_length _ _ _ HW) as Hlen.
  pose proof (lookup_in_bounds _ _ _ HL) as Hx.
  exists (ne_var (x + (length Δ - length Γ))). cbn. repeat split; try assumption.
  - replace (x + (length Δ - length Γ)) with (length Δ - (length Γ - x - 1) - 1) by lia.
    apply read_ne_var.
  - eapply convert_term with (A := B); [ | exact HA | exact (wf_exp_eq_sym _ _ _ _ HEty)].
    apply wf_vlookup; [ | exact HB].
    eauto using substitution_source, context_weakening_typed.
Qed.

Local Lemma reconstruct_readback_natural_recursion Γ A A' MZ MZ' MS MS' M M' i :
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Γ, ℕ ⊢ A' : Type@i }} ->
  {{ Γ, ℕ ⊢ A ≈ A' : Type@i }} ->
  {{ Γ ⊢ MZ' : A[Id,,zero] }} ->
  {{ Γ ⊢ MZ ≈ MZ' : A[Id,,zero] }} ->
  {{ Γ, ℕ, A ⊢ MS' : A[Wk∘Wk,,succ #1] }} ->
  {{ Γ, ℕ, A ⊢ MS ≈ MS' : A[Wk∘Wk,,succ #1] }} ->
  {{ Γ ⊢ M : ℕ }} ->
  {{ Γ ⊢ M' : ℕ }} ->
  {{ Γ ⊢ M ≈ M' : ℕ }} ->
  {{ Γ ⊢ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }} /\
  {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end
      ≈ rec M' return A' | zero -> MZ' | succ -> MS' end : A[Id,,M] }}.
Proof.
  intros HA HA' HE HMZ EMZ HMS EMS HM HM' EM.
  pose proof (typing_context _ _ _ HM) as HΓ.
  assert (HNat : {{ Γ ⊢ ℕ : Type@0 }}) by now apply wf_nat.
  assert (H0 : {{ Γ ⊢s Id,,zero : Γ, ℕ }}) by eauto using nat_case_substitution, wf_zero.
  assert (HS : {{ Γ, ℕ, A' ⊢s Wk∘Wk,,succ #1 : Γ, ℕ }})
    by exact (step_case_substitution _ _ _ HA').
  assert (H0T : {{ Γ ⊢ A'[Id,,zero] : Type@i }}) by eauto using type_substitution.
  assert (HST : {{ Γ, ℕ, A' ⊢ A'[Wk∘Wk,,succ #1] : Type@i }}) by eauto using type_substitution.
  assert (HMZ' : {{ Γ ⊢ MZ' : A'[Id,,zero] }}).
  {
    eapply convert_term; [exact HMZ | exact H0T |].
    eapply type_substitution_congruence; eauto using substitution_equality_reflexive.
  }
  assert (HMS' : {{ Γ, ℕ, A' ⊢ MS' : A'[Wk∘Wk,,succ #1] }}).
  {
    eapply convert_term with (A := {{{ A[Wk∘Wk,,succ #1] }}}).
    - exact (change_binder _ _ _ _ _ _ HA HA' HE HMS).
    - exact HST.
    - eapply type_substitution_congruence; eauto using substitution_equality_reflexive.
  }
  split.
  - eapply convert_term with (A := {{{ A'[Id,,M'] }}}).
    + exact (wf_natrec _ _ _ _ _ _ HA' HMZ' HMS' HM').
    + eapply type_substitution; eauto using nat_case_substitution.
    + apply wf_exp_eq_sym.
      eapply type_substitution_congruence.
      * now apply nat_case_substitution.
      * exact (identity_argument_equality _ _ _ _ _ HNat EM).
      * exact HE.
  - exact (wf_exp_eq_natrec_cong _ _ _ _ _ _ _ _ _ _ HA HE EMZ EMS EM).
Qed.

Local Lemma equation_indices_substitution Γ Δ σ A M N i :
  {{ Γ ⊢s σ : Δ }} ->
  {{ Δ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A[σ] }} ->
  {{ Γ ⊢ N : A[σ] }} ->
  {{ Γ ⊢s σ,,M,,N : Δ, A, A[Wk] }} /\
  {{ Γ ⊢ (Eq A[Wk∘Wk] #1 #0)[σ,,M,,N] ≈ Eq A[σ] M N : Type@i }}.
Proof.
  intros Hσ HA HM HN.
  assert (HΔA : {{ ⊢ Δ, A }}) by eauto using substitution_target, wf_ctx_extend.
  assert (HAw : {{ Δ, A ⊢ A[Wk] : Type@i }}) by eauto using weaken_type.
  assert (HΔAA : {{ ⊢ Δ, A, A[Wk] }}) by eauto using wf_ctx_extend.
  assert (HS : {{ Γ ⊢s σ,,M : Δ, A }}) by eauto using wf_sub_extend.
  assert (HAs : {{ Γ ⊢ A[σ] : Type@i }}) by eauto using type_substitution.
  assert (HE : {{ Γ ⊢ A[Wk][σ,,M] ≈ A[σ] : Type@i }}) by eauto using type_weakening_cancel.
  assert (HN' : {{ Γ ⊢ N : A[Wk][σ,,M] }}).
  {
    eapply convert_term; [exact HN | eauto using type_substitution |].
    now apply wf_exp_eq_sym.
  }
  assert (HT : {{ Γ ⊢s σ,,M,,N : Δ, A, A[Wk] }}) by eauto using wf_sub_extend.
  split; [exact HT |].
  assert (Hwk1 : {{ Δ, A ⊢s Wk : Δ }}) by now apply wf_sub_weaken.
  assert (Hwk2 : {{ Δ, A, A[Wk] ⊢s Wk : Δ, A }}) by now apply wf_sub_weaken.
  assert (Hww : {{ Δ, A, A[Wk] ⊢s Wk∘Wk : Δ }}) by eauto using wf_sub_compose.
  assert (HAAww : {{ Δ, A, A[Wk] ⊢ A[Wk∘Wk] : Type@i }}) by eauto using type_substitution.
  assert (Hwc : {{ Δ, A, A[Wk] ⊢ A[Wk∘Wk] ≈ A[Wk][Wk] : Type@i }})
    by eauto using type_substitution_composition.
  assert (H1 : {{ Δ, A, A[Wk] ⊢ #1 : A[Wk∘Wk] }}).
  {
    eapply convert_term with (A := {{{ A[Wk][Wk] }}}).
    - apply wf_vlookup; [exact HΔAA | apply there, here].
    - exact HAAww.
    - exact (wf_exp_eq_sym _ _ _ _ Hwc).
  }
  assert (H0 : {{ Δ, A, A[Wk] ⊢ #0 : A[Wk∘Wk] }}).
  {
    eapply convert_term with (A := {{{ A[Wk][Wk] }}}).
    - apply wf_vlookup; [exact HΔAA | apply here].
    - exact HAAww.
    - exact (wf_exp_eq_sym _ _ _ _ Hwc).
  }
  assert (HAt : {{ Γ ⊢ A[Wk∘Wk][σ,,M,,N] : Type@i }}) by eauto using type_substitution.
  assert (HAt_eq : {{ Γ ⊢ A[Wk∘Wk][σ,,M,,N] ≈ A[σ] : Type@i }}).
  {
    eapply wf_exp_eq_trans.
    - eapply type_substitution_congruence; [exact HT | now apply substitution_equality_reflexive | exact Hwc].
    - eapply wf_exp_eq_trans; [ | exact HE].
      exact (type_weakening_cancel _ _ _ _ _ _ _ _ HS HAw HN' HAw).
  }
  assert (Hidx1 : {{ Γ ⊢ #1[σ,,M,,N] ≈ M : A[σ] }}).
  {
    eapply wf_exp_eq_trans with (M' := {{{ #0[σ,,M] }}}).
    - eapply convert_equality; [ | exact HAs | exact HE].
      exact (wf_exp_eq_var_S_sub _ _ _ _ _ _ _ _ HS HAw HN' (here A Δ)).
    - exact (wf_exp_eq_var_0_sub _ _ _ _ _ _ Hσ HA HM).
  }
  assert (Hidx0 : {{ Γ ⊢ #0[σ,,M,,N] ≈ N : A[σ] }}).
  {
    eapply convert_equality; [ | exact HAs | exact HE].
    exact (wf_exp_eq_var_0_sub _ _ _ _ _ _ HS HAw HN').
  }
  eapply wf_exp_eq_trans.
  - exact (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HT HAAww H1 H0).
  - apply wf_exp_eq_eq_cong; [exact HAt_eq | | ];
      (eapply convert_equality; [eassumption | exact HAt | now apply wf_exp_eq_sym]).
Qed.

Local Lemma equation_identity_indices Γ A M N i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  {{ Γ ⊢ N : A }} ->
  {{ Γ ⊢s Id,,M,,N : Γ, A, A[Wk] }} /\
  {{ Γ ⊢ (Eq A[Wk∘Wk] #1 #0)[Id,,M,,N] ≈ Eq A M N : Type@i }}.
Proof.
  intros HA HM HN.
  assert (Hid : {{ Γ ⊢s Id : Γ }}) by eauto using wf_sub_id, typing_context.
  assert (HAi : {{ Γ ⊢ A[Id] : Type@i }}) by eauto using type_substitution.
  assert (HE : {{ Γ ⊢ A[Id] ≈ A : Type@i }}) by now apply wf_exp_eq_sub_id.
  assert (HMi : {{ Γ ⊢ M : A[Id] }}) by eauto using convert_term, wf_exp_eq_sym.
  assert (HNi : {{ Γ ⊢ N : A[Id] }}) by eauto using convert_term, wf_exp_eq_sym.
  destruct (equation_indices_substitution _ _ _ _ _ _ _ Hid HA HMi HNi) as [HS HEq].
  split; [exact HS |].
  eapply wf_exp_eq_trans; [exact HEq |].
  apply wf_exp_eq_eq_cong; [exact HE | | ];
    (apply expression_equality_reflexive; assumption).
Qed.

Local Lemma equation_reflexive_indices Γ A i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢s Id,,#0 : Γ, A, A[Wk] }} /\
  {{ Γ, A ⊢ (Eq A[Wk∘Wk] #1 #0)[Id,,#0] ≈ Eq A[Wk] #0 #0 : Type@i }}.
Proof.
  intro HA.
  assert (HΓA : {{ ⊢ Γ, A }}) by eauto using wf_ctx_extend, typing_context.
  assert (Hw : {{ Γ, A ⊢s Wk : Γ }}) by now apply wf_sub_weaken.
  assert (Hid : {{ Γ, A ⊢s Id : Γ, A }}) by now apply wf_sub_id.
  assert (Hhead : {{ Γ, A ⊢ #0 : A[Wk] }}) by (apply wf_vlookup; [assumption | apply here]).
  assert (HAw : {{ Γ, A ⊢ A[Wk] : Type@i }}) by eauto using type_substitution.
  assert (HS : {{ Γ, A ⊢s Id,,#0 : Γ, A, A[Wk] }}) by eauto using typing_identity_extension.
  split; [exact HS |].
  destruct (equation_indices_substitution _ _ _ _ _ _ _ Hw HA Hhead Hhead) as [HT HE].
  eapply wf_exp_eq_trans; [ | exact HE].
  eapply type_substitution_equality_same_body; [exact HS | | eauto using eqrec_context].
  eapply wf_sub_eq_extend_cong.
  - apply wf_sub_eq_sym. exact (identity_with_last_variable _ _ _ HA).
  - exact HAw.
  - apply expression_equality_reflexive. eapply convert_term.
    + exact Hhead.
    + eapply type_substitution; eassumption.
    + apply wf_exp_eq_sym, wf_exp_eq_sub_id. exact HAw.
Qed.

Local Lemma declaration_change_context Γ A A' i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ A' : Type@i }} ->
  {{ Γ ⊢ A ≈ A' : Type@i }} ->
  {{ ⊢ Γ, A' ⊆ Γ, A }}.
Proof.
  intros HA HA' HE.
  eapply wf_ctx_sub_extend with (i := i); try assumption.
  - eauto using context_subtyping_reflexive, typing_context.
  - eauto using wf_subtyp_refl, wf_exp_eq_sym.
Qed.

Local Lemma equality_type_components Γ T M :
  wf_exp Γ T M ->
  match M with
  | a_eq A P Q => exists i, wf_exp Γ (a_typ i) A /\ wf_exp Γ A P /\ wf_exp Γ A Q
  | _ => True
  end.
Proof. induction 1; simpl; eauto. Qed.

Local Lemma equation_context_change Γ A A' i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ A' : Type@i }} ->
  {{ Γ ⊢ A ≈ A' : Type@i }} ->
  wf_ctx_sub (equation_context Γ A') (equation_context Γ A).
Proof.
  intros HA HA' HE.
  pose proof (declaration_change_context _ _ _ _ HA HA' HE) as Hsub.
  assert (HΓA : {{ ⊢ Γ, A }}) by eauto using wf_ctx_extend, typing_context.
  assert (HΓA' : {{ ⊢ Γ, A' }}) by eauto using wf_ctx_extend, typing_context.
  assert (Hw : {{ Γ, A' ⊢s Wk : Γ }}) by now apply wf_sub_weaken.
  assert (HAw : {{ Γ, A ⊢ A[Wk] : Type@i }}) by eauto using weaken_type.
  assert (HAw_new : {{ Γ, A' ⊢ A[Wk] : Type@i }}) by eauto using type_substitution.
  assert (HAw' : {{ Γ, A' ⊢ A'[Wk] : Type@i }}) by eauto using type_substitution.
  assert (HEw : {{ Γ, A' ⊢ A'[Wk] ≈ A[Wk] : Type@i }})
    by eauto using type_substitution_congruence, wf_exp_eq_sym, substitution_equality_reflexive.
  assert (Hsub2 : {{ ⊢ Γ, A', A'[Wk] ⊆ Γ, A, A[Wk] }})
    by eauto using wf_ctx_sub_extend, wf_subtyp_refl.
  assert (HΓAA' : {{ ⊢ Γ, A', A'[Wk] }}) by eauto using wf_ctx_extend.
  assert (Hw2 : {{ Γ, A', A'[Wk] ⊢s Wk : Γ, A' }}) by now apply wf_sub_weaken.
  assert (Hww : {{ Γ, A', A'[Wk] ⊢s Wk∘Wk : Γ }}) by eauto using wf_sub_compose.
  assert (HEww : {{ Γ, A', A'[Wk] ⊢ A'[Wk∘Wk] ≈ A[Wk∘Wk] : Type@i }})
    by eauto using type_substitution_congruence, wf_exp_eq_sym, substitution_equality_reflexive.
  pose proof (eqrec_context _ _ _ HA) as HOld.
  pose proof (eqrec_context _ _ _ HA') as HNew.
  pose proof (proj1 narrowing _ _ _ HOld _ HΓAA' Hsub2) as HOldNew.
  destruct (equality_type_components _ _ _ HNew) as (k & HT & H1 & H0).
  unfold equation_context.
  eapply wf_ctx_sub_extend with (i := i); try assumption.
  eapply wf_subtyp_refl; [exact HOldNew |].
  exact (wf_exp_eq_eq_cong _ _ _ _ _ _ _ _ HEww
    (expression_equality_reflexive _ _ _ H1) (expression_equality_reflexive _ _ _ H0)).
Qed.

Local Lemma equation_identity_congruence Γ A M M' N N' P P' i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  {{ Γ ⊢ N : A }} ->
  {{ Γ ⊢ M ≈ M' : A }} ->
  {{ Γ ⊢ N ≈ N' : A }} ->
  {{ Γ ⊢ P ≈ P' : Eq A M N }} ->
  {{ Γ ⊢s Id,,M,,N,,P ≈ Id,,M',,N',,P' : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
Proof.
  intros HA HM HN EM EN EP.
  assert (Hid : {{ Γ ⊢s Id : Γ }}) by eauto using wf_sub_id, typing_context.
  assert (Hs : {{ Γ ⊢s Id,,M : Γ, A }}) by eauto using typing_identity_extension.
  assert (HAw : {{ Γ, A ⊢ A[Wk] : Type@i }}) by eauto using weaken_type.
  assert (HMi : {{ Γ ⊢ M : A[Id] }}).
  {
    eapply convert_term; [exact HM | eauto using type_substitution |].
    apply wf_exp_eq_sym, wf_exp_eq_sub_id. exact HA.
  }
  assert (HE : {{ Γ ⊢ A[Wk][Id,,M] ≈ A : Type@i }}).
  {
    eapply wf_exp_eq_trans.
    - exact (type_weakening_cancel _ _ _ _ _ _ _ _ Hid HA HMi HA).
    - apply wf_exp_eq_sub_id. exact HA.
  }
  destruct (equation_identity_indices _ _ _ _ _ HA HM HN) as [Hθ HEθ].
  eapply wf_sub_eq_extend_cong; [ | exact (eqrec_context _ _ _ HA) |].
  - eapply wf_sub_eq_extend_cong; [exact (identity_argument_equality _ _ _ _ _ HA EM) | exact HAw |].
    eapply convert_equality; [exact EN | eauto using type_substitution | now apply wf_exp_eq_sym].
  - eapply convert_equality; [exact EP | eauto using type_substitution, eqrec_context | now apply wf_exp_eq_sym].
Qed.

Local Lemma equation_reflexive_congruence Γ A A' i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ A' : Type@i }} ->
  {{ Γ ⊢ A ≈ A' : Type@i }} ->
  {{ Γ, A' ⊢s Id,,#0,,refl A[Wk] #0 ≈ Id,,#0,,refl A'[Wk] #0
        : Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }}.
Proof.
  intros HA HA' HE.
  assert (HΓA' : {{ ⊢ Γ, A' }}) by eauto using wf_ctx_extend, typing_context.
  assert (Hw : {{ Γ, A' ⊢s Wk : Γ }}) by now apply wf_sub_weaken.
  assert (Hsub : {{ ⊢ Γ, A' ⊆ Γ, A }}) by eauto using declaration_change_context.
  destruct (equation_reflexive_indices _ _ _ HA) as [Hs HEq].
  pose proof (proj1 (proj2 (proj2 narrowing)) _ _ _ Hs _ HΓA' Hsub) as Hsn.
  pose proof (proj1 (proj2 narrowing) _ _ _ _ HEq _ HΓA' Hsub) as HEn.
  assert (HAw : {{ Γ, A' ⊢ A[Wk] : Type@i }}) by eauto using type_substitution.
  assert (HAw' : {{ Γ, A' ⊢ A'[Wk] : Type@i }}) by eauto using type_substitution.
  assert (HEw : {{ Γ, A' ⊢ A[Wk] ≈ A'[Wk] : Type@i }})
    by eauto using type_substitution_congruence, substitution_equality_reflexive.
  assert (H0 : {{ Γ, A' ⊢ #0 : A'[Wk] }}) by (apply wf_vlookup; [assumption | apply here]).
  assert (H0' : {{ Γ, A' ⊢ #0 : A[Wk] }}) by eauto using convert_term, wf_exp_eq_sym.
  eapply wf_sub_eq_extend_cong;
    [now apply substitution_equality_reflexive | exact (eqrec_context _ _ _ HA) |].
  eapply convert_equality.
  - exact (wf_exp_eq_refl_cong _ _ _ _ _ _ HEw (expression_equality_reflexive _ _ _ H0')).
  - eapply type_substitution; [exact Hsn | exact (eqrec_context _ _ _ HA)].
  - now apply wf_exp_eq_sym.
Qed.

Local Lemma equation_context_wellformed Γ A i :
  {{ Γ ⊢ A : Type@i }} ->
  wf_ctx (equation_context Γ A).
Proof.
  intro HA. unfold equation_context.
  apply wf_ctx_extend with (i := i).
  - apply wf_ctx_extend with (i := i).
    + eauto using wf_ctx_extend, typing_context.
    + eauto using weaken_type.
  - exact (eqrec_context _ _ _ HA).
Qed.

Local Lemma reconstruct_readback_equation_recursion
    Γ A A' B B' BR BR' M1 M1' M2 M2' P P' i j :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ A' : Type@i }} ->
  {{ Γ ⊢ A ≈ A' : Type@i }} ->
  {{ Γ ⊢ M1 : A }} ->
  {{ Γ ⊢ M1' : A }} ->
  {{ Γ ⊢ M1 ≈ M1' : A }} ->
  {{ Γ ⊢ M2 : A }} ->
  {{ Γ ⊢ M2' : A }} ->
  {{ Γ ⊢ M2 ≈ M2' : A }} ->
  wf_exp (equation_context Γ A) (a_typ j) B ->
  wf_exp (equation_context Γ A) (a_typ j) B' ->
  wf_exp_eq (equation_context Γ A) (a_typ j) B B' ->
  wf_exp (A :: Γ) (equation_refl_type A B) BR' ->
  wf_exp_eq (A :: Γ) (equation_refl_type A B) BR BR' ->
  {{ Γ ⊢ P : Eq A M1 M2 }} ->
  {{ Γ ⊢ P' : Eq A M1 M2 }} ->
  {{ Γ ⊢ P ≈ P' : Eq A M1 M2 }} ->
  wf_exp Γ (equation_result_type B M1 M2 P) (a_eqrec A' B' BR' M1' M2' P') /\
  wf_exp_eq Γ (equation_result_type B M1 M2 P)
    (a_eqrec A B BR M1 M2 P) (a_eqrec A' B' BR' M1' M2' P').
Proof.
  intros HA HA' EA HM1 HM1' EM1 HM2 HM2' EM2 HB HB' EB HBR' EBR HP HP' EP.
  assert (HMA1 : {{ Γ ⊢ M1' : A' }}) by eauto using convert_term.
  assert (HMA2 : {{ Γ ⊢ M2' : A' }}) by eauto using convert_term.
  assert (HPA : {{ Γ ⊢ P' : Eq A' M1' M2' }}).
  {
    eapply convert_term; [exact HP' | |].
    - exact (wf_eq _ _ _ _ _ HA' HMA1 HMA2).
    - exact (wf_exp_eq_eq_cong _ _ _ _ _ _ _ _ EA EM1 EM2).
  }
  pose proof (equation_context_wellformed _ _ _ HA') as HC.
  pose proof (equation_context_change _ _ _ _ HA HA' EA) as HSub.
  pose proof (proj1 narrowing _ _ _ HB' _ HC HSub) as HB'new.
  assert (HΓA' : {{ ⊢ Γ, A' }}) by eauto using wf_ctx_extend, typing_context.
  pose proof (declaration_change_context _ _ _ _ HA HA' EA) as HSubA.
  pose proof (proj1 narrowing _ _ _ HBR' _ HΓA' HSubA) as HBR'old.
  pose proof (eqrec_refl_substitution _ _ _ HA) as HSold.
  pose proof (proj1 (proj2 (proj2 narrowing)) _ _ _ HSold _ HΓA' HSubA) as HS.
  pose proof (eqrec_refl_substitution _ _ _ HA') as HSnew.
  pose proof (equation_reflexive_congruence _ _ _ _ HA HA' EA) as HSeq.
  assert (HBR'new : wf_exp (A' :: Γ) (equation_refl_type A' B') BR').
  {
    eapply convert_term.
    - exact HBR'old.
    - exact (type_substitution _ _ _ _ _ HSnew HB'new).
    - exact (type_substitution_congruence _ _ _ _ _ _ _ HS HSeq EB).
  }
  pose proof (eqrec_case_substitution _ _ _ _ _ _ HA HM1 HM2 HP) as HPsub.
  split.
  - eapply convert_term with (A := equation_result_type B' M1' M2' P').
    + eapply wf_eqrec; eassumption.
    + exact (type_substitution _ _ _ _ _ HPsub HB).
    + apply wf_exp_eq_sym.
      eapply type_substitution_congruence.
      * exact HPsub.
      * exact (equation_identity_congruence _ _ _ _ _ _ _ _ _ HA HM1 HM2 EM1 EM2 EP).
      * exact EB.
  - eapply wf_exp_eq_eqrec_cong; eassumption.
Qed.

Local Lemma reconstruct_readback_application Γ A B F F' M M' i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ F' : Π A B }} ->
  {{ Γ ⊢ F ≈ F' : Π A B }} ->
  {{ Γ ⊢ M : A }} ->
  {{ Γ ⊢ M' : A }} ->
  {{ Γ ⊢ M ≈ M' : A }} ->
  {{ Γ ⊢ F' M' : B[Id,,M] }} /\
  {{ Γ ⊢ F M ≈ F' M' : B[Id,,M] }}.
Proof.
  intros HA HB HF' EF HM HM' EM.
  assert (Hid : {{ Γ ⊢s Id,,M : Γ, A }}) by eauto using typing_identity_extension.
  split.
  - eapply convert_term with (A := {{{ B[Id,,M'] }}}).
    + exact (wf_app _ _ _ _ _ _ HA HB HF' HM').
    + exact (type_substitution _ _ _ _ _ Hid HB).
    + apply wf_exp_eq_sym.
      eapply type_substitution_equality_same_body;
        eauto using identity_argument_equality.
  - exact (wf_exp_eq_app_cong _ _ _ _ _ _ _ _ HA HB EF EM).
Qed.

Local Lemma reconstruct_readback_first Γ A B P P' i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ P' : Σ A B }} ->
  {{ Γ ⊢ P ≈ P' : Σ A B }} ->
  {{ Γ ⊢ fst P' : A }} /\ {{ Γ ⊢ fst P ≈ fst P' : A }}.
Proof. intros. split; eauto using wf_fst, wf_exp_eq_fst_cong. Qed.

Local Lemma reconstruct_readback_second Γ A B P P' i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ P : Σ A B }} ->
  {{ Γ ⊢ P' : Σ A B }} ->
  {{ Γ ⊢ P ≈ P' : Σ A B }} ->
  {{ Γ ⊢ snd P' : B[Id,,fst P] }} /\
  {{ Γ ⊢ snd P ≈ snd P' : B[Id,,fst P] }}.
Proof.
  intros HA HB HP HP' EP.
  assert (Hfst : {{ Γ ⊢ fst P : A }}) by eauto using wf_fst.
  assert (Efst : {{ Γ ⊢ fst P ≈ fst P' : A }}) by eauto using wf_exp_eq_fst_cong.
  assert (HS : {{ Γ ⊢s Id,,fst P : Γ, A }}) by eauto using typing_identity_extension.
  split.
  - eapply convert_term with (A := {{{ B[Id,,fst P'] }}}).
    + exact (wf_snd _ _ _ _ _ HA HB HP').
    + eauto using type_substitution.
    + apply wf_exp_eq_sym.
      eapply type_substitution_equality_same_body;
        eauto using identity_argument_equality.
  - exact (wf_exp_eq_snd_cong _ _ _ _ _ _ HA HB EP).
Qed.

(* A typed quotation is valid at every extension of the current context. *)

Local Definition typed_readback {D W : Type}
    (read : nat -> D -> W -> Prop) (embed : W -> exp) Γ A M (d : D) :=
  forall Δ σ, context_weakening Γ Δ σ ->
    exists w,
      read (length Δ) d w /\
      wf_exp Δ (a_sub A σ) (embed w) /\
      wf_exp_eq Δ (a_sub A σ) (a_sub M σ) (embed w).

Local Definition typed_value_readback Γ A M a m :=
  typed_readback read_nf nf_to_exp Γ A M (d_dom a m).

Local Definition typed_type_readback Γ i A a :=
  typed_readback read_typ nf_to_exp Γ (a_typ i) A a.

Local Definition typed_neutral_readback Γ A M n :=
  typed_readback read_ne ne_to_exp Γ A M n.

Local Lemma typed_readback_here D W (read : nat -> D -> W -> Prop) embed Γ A M d i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  typed_readback read embed Γ A M d ->
  exists w, read (length Γ) d w /\ wf_exp Γ A (embed w) /\ wf_exp_eq Γ A M (embed w).
Proof.
  intros HA HM H.
  pose proof (typing_context _ _ _ HA) as HΓ.
  destruct (H _ _ (context_weakening_id _ HΓ)) as (w & Hw & HT & HE).
  assert (HAE : {{ Γ ⊢ A[Id] ≈ A : Type@i }}) by now apply wf_exp_eq_sub_id.
  exists w. repeat split; try assumption.
  - exact (convert_term _ _ _ _ _ HT HA HAE).
  - eapply wf_exp_eq_trans.
    + apply wf_exp_eq_sym, wf_exp_eq_sub_id. exact HM.
    + exact (convert_equality _ _ _ _ _ _ HE HA HAE).
Qed.

Local Lemma typed_readback_type_conversion D W (read : nat -> D -> W -> Prop) embed Γ A B M d i :
  {{ Γ ⊢ B : Type@i }} ->
  {{ Γ ⊢ A ≈ B : Type@i }} ->
  typed_readback read embed Γ A M d ->
  typed_readback read embed Γ B M d.
Proof.
  intros HB HE H Δ σ HW.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  destruct (H _ _ HW) as (w & Hw & HT & EQ).
  pose proof (type_substitution _ _ _ _ _ HS HB) as HTw.
  pose proof (type_substitution_congruence _ _ _ _ _ _ _ HS (substitution_equality_reflexive _ _ _ HS) HE) as HEw.
  exists w. repeat split; eauto using convert_term, convert_equality.
Qed.

Local Lemma typed_readback_expression_conversion D W (read : nat -> D -> W -> Prop) embed Γ A M N d :
  {{ Γ ⊢ N ≈ M : A }} ->
  typed_readback read embed Γ A M d ->
  typed_readback read embed Γ A N d.
Proof.
  intros HE H Δ σ HW.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  destruct (H _ _ HW) as (w & Hw & HT & EQ).
  exists w. repeat split; try assumption.
  eapply wf_exp_eq_trans; [exact (equality_under_substitution _ _ _ _ _ _ HS HE) | exact EQ].
Qed.

Local Lemma typed_readback_weakening D W (read : nat -> D -> W -> Prop) embed Γ Δ σ A M d i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  context_weakening Γ Δ σ ->
  typed_readback read embed Γ A M d ->
  typed_readback read embed Δ {{{ A[σ] }}} {{{ M[σ] }}} d.
Proof.
  intros HA HM Hσ H Θ τ Hτ.
  destruct (context_weakening_compose _ _ _ _ _ Hσ Hτ) as (ω & Hω & HE).
  destruct (H _ _ Hω) as (w & Hw & HT & HQ).
  pose proof (context_weakening_typed _ _ _ Hσ) as Hs.
  pose proof (context_weakening_typed _ _ _ Hτ) as Ht.
  assert (Hst : {{ Θ ⊢s σ∘τ : Γ }}) by eauto using wf_sub_compose.
  assert (HAst : {{ Θ ⊢ A[σ][τ] : Type@i }}) by eauto using type_substitution.
  pose proof (type_substitution_composition _ _ _ _ _ _ _ Ht Hs HA) as HAc.
  pose proof (type_substitution_equality_same_body _ _ _ _ _ _ Hst HE HA) as HAw.
  assert (HAE : {{ Θ ⊢ A[ω] ≈ A[σ][τ] : Type@i }})
    by (eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; exact HAw | exact HAc]).
  exists w. repeat split; try assumption.
  - exact (convert_term _ _ _ _ _ HT HAst HAE).
  - eapply wf_exp_eq_trans with (M' := {{{ M[σ∘τ] }}}).
    + eapply convert_equality; [ | exact HAst | exact HAc].
      apply wf_exp_eq_sym. exact (wf_exp_eq_sub_compose _ _ _ _ _ _ _ Ht Hs HM).
    + eapply wf_exp_eq_trans with (M' := {{{ M[ω] }}}).
      * eapply convert_equality; [ | exact HAst | exact HAc].
        exact (wf_exp_eq_sub_cong _ _ _ _ _ _ _ (expression_equality_reflexive _ _ _ HM) HE).
      * exact (convert_equality _ _ _ _ _ _ HQ HAst HAE).
Qed.

Local Lemma shared_type_readback_transport Γ A i a b j R :
  semantic_type j a b R ->
  typed_type_readback Γ i A a ->
  typed_type_readback Γ i A b.
Proof.
  intros HT H Δ σ HW.
  destruct (H _ _ HW) as (w & Hw & HTw & HE).
  destruct (proj1 (semantic_type_readback _ _ _ _ HT) (length Δ)) as (w' & Hw' & HR).
  pose proof (proj2 (proj2 readback_deterministic) _ _ _ Hw _ Hw'). subst w'.
  exists w. repeat split; assumption.
Qed.

Local Lemma typed_readback_universe Γ A a i :
  typed_type_readback Γ i A a -> typed_value_readback Γ (a_typ i) A (d_univ i) a.
Proof.
  intros H Δ σ HW. destruct (H _ _ HW) as (w & Hw & HT & HE).
  exists w. repeat split; auto using read_nf_type.
Qed.

Local Lemma typed_readback_reflected_variable Γ A x :
  ctx_lookup x A Γ ->
  typed_neutral_readback Γ A (a_var x) (d_var (length Γ - x - 1)).
Proof. intros H Δ σ HW. exact (readback_of_weakened_variable _ _ _ _ _ HW H). Qed.

Local Lemma typed_type_readback_here Γ i A a :
  {{ Γ ⊢ A : Type@i }} ->
  typed_type_readback Γ i A a ->
  exists W, read_typ (length Γ) a W /\
    {{ Γ ⊢ ^(nf_to_exp W) : Type@i }} /\ {{ Γ ⊢ A ≈ ^(nf_to_exp W) : Type@i }}.
Proof.
  intros HA H.
  exact (typed_readback_here _ _ _ _ _ _ _ _ _
    (wf_typ _ _ (typing_context _ _ _ HA)) HA H).
Qed.

Local Lemma typed_type_readback_at_extension Γ Δ σ i A a :
  context_weakening Γ Δ σ ->
  typed_type_readback Γ i A a ->
  exists W, read_typ (length Δ) a W /\
    {{ Δ ⊢ ^(nf_to_exp W) : Type@i }} /\ {{ Δ ⊢ A[σ] ≈ ^(nf_to_exp W) : Type@i }}.
Proof.
  intros HW H.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  destruct (H _ _ HW) as (W & HR & HT & HE).
  assert (HTyp : {{ Δ ⊢ Type@i : Type@(S i) }}) by eauto using wf_typ, substitution_source.
  exists W. split; [exact HR |].
  split.
  - exact (convert_term _ _ _ _ _ HT HTyp (wf_exp_eq_typ_sub _ _ _ _ HS)).
  - exact (type_equality_universe_sub _ _ _ _ _ _ HS HE).
Qed.

Local Lemma typed_type_readback_binder Γ A B i a ρ C :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  typed_type_readback Γ i A a ->
  (forall Δ σ, context_weakening Γ Δ σ ->
    exists b, eval_exp C (extend_env ρ (d_neut a (d_var (length Δ)))) b /\
      typed_type_readback (a_sub A σ :: Δ) i (a_sub B (Syntax.q σ)) b) ->
  typed_type_readback Γ i (a_pi A B) (d_pi a ρ C) /\
  typed_type_readback Γ i (a_sigma A B) (d_sigma a ρ C).
Proof.
  intros HA HB Hdom Hcod.
  assert (H : forall Δ σ, context_weakening Γ Δ σ ->
    exists a0 b0 b,
      read_typ (length Δ) a a0 /\
      eval_exp C (extend_env ρ (d_neut a (d_var (length Δ)))) b /\
      read_typ (S (length Δ)) b b0 /\
      {{ Δ ⊢ A[σ] : Type@i }} /\
      {{ Δ ⊢ ^(nf_to_exp a0) : Type@i }} /\
      {{ Δ ⊢ A[σ] ≈ ^(nf_to_exp a0) : Type@i }} /\
      {{ Δ, A[σ] ⊢ B[q σ] ≈ ^(nf_to_exp b0) : Type@i }} /\
      wf_exp (nf_to_exp a0 :: Δ) (a_typ i) (nf_to_exp b0)).
  {
    intros Δ σ HW.
    pose proof (context_weakening_typed _ _ _ HW) as HS.
    pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
    pose proof (lifted_substitution _ _ _ _ _ HS HA) as Hq.
    pose proof (type_substitution _ _ _ _ _ Hq HB) as HBq.
    destruct (typed_type_readback_at_extension _ _ _ _ _ _ HW Hdom) as (a0 & HRA & HA0 & HAE).
    destruct (Hcod _ _ HW) as (b & Hb & Hread).
    destruct (typed_type_readback_here _ _ _ _ HBq Hread) as (b0 & HRB & HB0 & HBE).
    exists a0, b0, b. repeat split; try assumption.
    exact (change_binder _ _ _ _ _ _ HAs HA0 HAE HB0).
  }
  split; intros Δ σ HW;
    pose proof (context_weakening_typed _ _ _ HW) as HS;
    destruct (H _ _ HW) as (na & nb & b & HRA & Hb & HRB & HAs & HNA & HEA & HEB & HNB);
    pose proof (substitution_target _ _ _ HS) as HΓ;
    pose proof (wf_typ Γ i HΓ) as HTyp;
    pose proof (type_substitution _ _ _ _ _ HS HTyp) as HST;
    pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_typ_sub _ _ _ i HS)) as HSTeq.
  - exists (nf_pi na nb). repeat split; cbn.
    + eapply read_typ_pi; eassumption.
    + eapply convert_term; [exact (wf_pi _ _ _ _ HNA HNB) | exact HST | exact HSTeq].
    + eapply convert_equality; [ | exact HST | exact HSTeq].
      eapply wf_exp_eq_trans.
      * exact (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA HB).
      * exact (wf_exp_eq_pi_cong _ _ _ _ _ _ HAs HEA HEB).
  - exists (nf_sigma na nb). repeat split; cbn.
    + eapply read_typ_sigma; eassumption.
    + eapply convert_term; [exact (wf_sigma _ _ _ _ HNA HNB) | exact HST | exact HSTeq].
    + eapply convert_equality; [ | exact HST | exact HSTeq].
      eapply wf_exp_eq_trans.
      * exact (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB).
      * exact (wf_exp_eq_sigma_cong _ _ _ _ _ _ HAs HEA HEB).
Qed.

Local Lemma typed_value_readback_function Γ A B F i a ρ C f :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ F : Π A B }} ->
  typed_type_readback Γ i A a ->
  (forall Δ σ, context_weakening Γ Δ σ ->
    exists b m,
      eval_exp C (extend_env ρ (d_neut a (d_var (length Δ)))) b /\
      eval_app f (d_neut a (d_var (length Δ))) m /\
      typed_value_readback (a_sub A σ :: Δ) (a_sub B (Syntax.q σ))
        (a_app (a_sub (a_sub F σ) a_weaken) (a_var 0)) b m) ->
  typed_value_readback Γ {{{ Π A B }}} F (d_pi a ρ C) f.
Proof.
  intros HA HB HF HD HC Δ σ HW.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (type_substitution _ _ _ _ _ HQ HB) as HBq.
  pose proof (wf_exp_sub _ _ _ _ _ HS HF) as HFsub.
  pose proof (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA HB) as HEQ.
  assert (HFT : {{ Δ ⊢ F[σ] : Π A[σ] B[q σ] }}).
  { exact (convert_term _ _ _ _ _ HFsub (wf_pi _ _ _ _ HAs HBq) HEQ). }
  pose proof (eta_body_typing _ _ _ _ _ HAs HBq HFT) as Hbody.
  destruct (HC _ _ HW) as (b & m & Hb & Hm & Hread).
  destruct (typed_readback_here _ _ _ _ _ _ _ _ _ HBq Hbody Hread)
    as (w & HR & HWty & HWeq).
  destruct (typed_type_readback_at_extension _ _ _ _ _ _ HW HD) as (u & HU & HUty & HUeq).
  destruct (reconstruct_readback_lambda _ _ _ _ _ _ _ HAs HUty HUeq HBq HFT HWty HWeq)
    as (HT & HE).
  assert (HAold : {{ Δ ⊢ (Π A B)[σ] : Type@i }}) by eauto using type_substitution, wf_pi.
  pose proof (wf_exp_eq_sym _ _ _ _ HEQ) as Hback.
  exists (nf_fn u w). repeat split; cbn.
  - eapply read_nf_fn; eassumption.
  - exact (convert_term _ _ _ _ _ HT HAold Hback).
  - exact (convert_equality _ _ _ _ _ _ HE HAold Hback).
Qed.

Local Lemma typed_type_readback_equality Γ A M N i a m n :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  {{ Γ ⊢ N : A }} ->
  typed_type_readback Γ i A a ->
  typed_value_readback Γ A M a m ->
  typed_value_readback Γ A N a n ->
  typed_type_readback Γ i {{{ Eq A M N }}} (d_eq a m n).
Proof.
  intros HA HM HN HAr HMr HNr Δ σ HW.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  destruct (typed_type_readback_at_extension _ _ _ _ _ _ HW HAr) as (A0 & HRA & HA0 & HEA).
  destruct (HMr _ _ HW) as (M0 & HRM & HM0 & HEM).
  destruct (HNr _ _ HW) as (N0 & HRN & HN0 & HEN).
  pose proof (convert_term _ _ _ _ _ HM0 HA0 HEA) as HM'.
  pose proof (convert_term _ _ _ _ _ HN0 HA0 HEA) as HN'.
  assert (HTyp : {{ Γ ⊢ Type@i : Type@(S i) }}) by eauto using wf_typ, substitution_target.
  pose proof (type_substitution _ _ _ _ _ HS HTyp) as HST.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_typ_sub _ _ _ i HS)) as HSTeq.
  exists (nf_eq A0 M0 N0). repeat split; cbn.
  - eapply read_typ_eq; eassumption.
  - eapply convert_term; [exact (wf_eq _ _ _ _ _ HA0 HM' HN') | exact HST | exact HSTeq].
  - eapply convert_equality; [ | exact HST | exact HSTeq].
    eapply wf_exp_eq_trans.
    + exact (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HS HA HM HN).
    + exact (wf_exp_eq_eq_cong _ _ _ _ _ _ _ _ HEA HEM HEN).
Qed.

Local Lemma typed_value_readback_sigma Γ A B P i a ρ C p :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ P : Σ A B }} ->
  typed_type_readback Γ i A a ->
  (forall Δ σ, context_weakening Γ Δ σ ->
    exists b b' m n,
      eval_exp C (extend_env ρ (d_neut a (d_var (length Δ)))) b /\
      typed_type_readback (a_sub A σ :: Δ) i (a_sub B (Syntax.q σ)) b /\
      eval_fst p m /\ eval_snd p n /\ eval_exp C (extend_env ρ m) b' /\
      typed_value_readback Δ (a_sub A σ) (a_fst (a_sub P σ)) a m /\
      typed_value_readback Δ
        (a_sub (a_sub B (Syntax.q σ)) (a_extend a_id (a_fst (a_sub P σ))))
        (a_snd (a_sub P σ)) b' n) ->
  typed_value_readback Γ {{{ Σ A B }}} P (d_sigma a ρ C) p.
Proof.
  intros HA HB HP HD HC Δ σ HW.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (type_substitution _ _ _ _ _ HQ HB) as HBq.
  pose proof (wf_exp_sub _ _ _ _ _ HS HP) as HPsub.
  pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB) as HEQ.
  assert (HPtyped : {{ Δ ⊢ P[σ] : Σ A[σ] B[q σ] }}).
  { exact (convert_term _ _ _ _ _ HPsub (wf_sigma _ _ _ _ HAs HBq) HEQ). }
  pose proof (wf_fst _ _ _ _ _ HAs HBq HPtyped) as HF.
  pose proof (wf_snd _ _ _ _ _ HAs HBq HPtyped) as HSn.
  pose proof (typing_identity_extension _ _ _ _ HAs HF) as HSinst.
  pose proof (type_substitution _ _ _ _ _ HSinst HBq) as HSnty.
  destruct (HC _ _ HW) as (b & b' & m & n & Hb & HBT & Hm & Hn & Hb' & HMR & HNR).
  destruct (typed_readback_here _ _ _ _ _ _ _ _ _ HAs HF HMR) as (M0 & HM & HMT & HME).
  destruct (typed_readback_here _ _ _ _ _ _ _ _ _ HSnty HSn HNR) as (N0 & HN & HNT & HNE).
  destruct (typed_type_readback_here _ _ _ _ HBq HBT) as (B0 & HBR & HBT0 & HBE).
  destruct (typed_type_readback_at_extension _ _ _ _ _ _ HW HD) as (A0 & HAR & HAT0 & HAE).
  destruct (reconstruct_readback_pair _ _ _ _ _ _ _ _ _
    HAs HAT0 HAE HBq HBT0 HBE HPtyped HMT HME HNT HNE) as (HT & HE).
  assert (HAold : {{ Δ ⊢ (Σ A B)[σ] : Type@i }}) by eauto using type_substitution, wf_sigma.
  pose proof (wf_exp_eq_sym _ _ _ _ HEQ) as Hback.
  exists (nf_pair M0 A0 N0 B0). repeat split; cbn.
  - eapply read_nf_sigma; eassumption.
  - exact (convert_term _ _ _ _ _ HT HAold Hback).
  - exact (convert_equality _ _ _ _ _ _ HE HAold Hback).
Qed.

Inductive atomic_type_code : domain -> Prop :=
| atomic_universe i : atomic_type_code (d_univ i)
| atomic_natural : atomic_type_code d_nat
| atomic_equality a m n : atomic_type_code (d_eq a m n)
| atomic_neutral a k : atomic_type_code (d_neut a k).

Local Lemma typed_readback_atomic_reflection Γ A M a a' k :
  atomic_type_code a ->
  typed_neutral_readback Γ A M k ->
  typed_value_readback Γ A M a (d_neut a' k).
Proof.
  intros Ha H Δ σ HW.
  destruct (H _ _ HW) as (n & Hn & HT & HE).
  exists (nf_neut n). cbn. repeat split; try assumption.
  destruct Ha; eauto using read_nf_type, read_typ_neut, read_nf_nat_neut,
    read_nf_eq_neut, read_nf_neut.
Qed.

Local Lemma typed_type_readback_neutral Γ M i a k :
  typed_neutral_readback Γ (a_typ i) M k ->
  typed_type_readback Γ i M (d_neut a k).
Proof.
  intros H Δ σ HW.
  destruct (H _ _ HW) as (n & Hn & HT & HE).
  exists (nf_neut n). cbn. repeat split; eauto using read_typ_neut.
Qed.

Local Lemma argument_substitution_composition Γ Δ σ A M i :
  {{ Γ ⊢s σ : Δ }} ->
  {{ Δ ⊢ A : Type@i }} ->
  {{ Δ ⊢ M : A }} ->
  {{ Γ ⊢s (Id,,M)∘σ ≈ σ,,M[σ] : Δ, A }}.
Proof.
  intros Hσ HA HM.
  assert (HΔ : {{ ⊢ Δ }}) by eauto using substitution_target.
  assert (Hid : {{ Δ ⊢s Id : Δ }}) by now apply wf_sub_id.
  assert (HMi : {{ Δ ⊢ M : A[Id] }}).
  {
    eapply convert_term; [exact HM | eauto using type_substitution |].
    apply wf_exp_eq_sym, wf_exp_eq_sub_id. exact HA.
  }
  assert (Htail : {{ Γ ⊢s Id∘σ : Δ }}) by eauto using wf_sub_compose.
  assert (HAis : {{ Γ ⊢ A[Id∘σ] : Type@i }}) by eauto using type_substitution.
  assert (HMs : {{ Γ ⊢ M[σ] : A[Id∘σ] }}).
  {
    eapply convert_term.
    - exact (wf_exp_sub _ _ _ _ _ Hσ HM).
    - exact HAis.
    - apply wf_exp_eq_sym.
      eapply type_substitution_equality_same_body;
        eauto using wf_sub_eq_id_compose_right.
  }
  eapply wf_sub_eq_trans with (σ' := {{{ (Id∘σ),,M[σ] }}}).
  - exact (wf_sub_eq_extend_compose _ _ _ _ _ _ _ _ Hid HA HMi Hσ).
  - eapply wf_sub_eq_extend_cong; [now apply wf_sub_eq_id_compose_right | exact HA |].
    now apply expression_equality_reflexive.
Qed.

Local Lemma type_argument_substitution_composition Γ Δ σ A B M i j :
  {{ Γ ⊢s σ : Δ }} ->
  {{ Δ ⊢ A : Type@i }} ->
  {{ Δ, A ⊢ B : Type@j }} ->
  {{ Δ ⊢ M : A }} ->
  {{ Γ ⊢ B[Id,,M][σ] ≈ B[σ,,M[σ]] : Type@j }}.
Proof.
  intros Hσ HA HB HM.
  assert (HS : {{ Δ ⊢s Id,,M : Δ, A }}) by eauto using typing_identity_extension.
  assert (Hcomp : {{ Γ ⊢s (Id,,M)∘σ : Δ, A }}) by eauto using wf_sub_compose.
  eapply wf_exp_eq_trans with (M' := {{{ B[(Id,,M)∘σ] }}}).
  - apply wf_exp_eq_sym. exact (type_substitution_composition _ _ _ _ _ _ _ Hσ HS HB).
  - eapply type_substitution_equality_same_body; [exact Hcomp | | exact HB].
    exact (argument_substitution_composition _ _ _ _ _ _ Hσ HA HM).
Qed.

Local Lemma typed_neutral_readback_app Γ A B F M i a f m :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ F : Π A B }} ->
  {{ Γ ⊢ M : A }} ->
  typed_neutral_readback Γ {{{ Π A B }}} F f ->
  typed_value_readback Γ A M a m ->
  typed_neutral_readback Γ {{{ B[Id,,M] }}} {{{ F M }}} (d_app f (d_dom a m)).
Proof.
  intros HA HB HF HM HRF HRM Δ σ HW.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  destruct (HRF _ _ HW) as (f0 & Hf & HFty & HFeq).
  destruct (HRM _ _ HW) as (m0 & Hm & HMty & HMeq).
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (type_substitution _ _ _ _ _ HQ HB) as HBq.
  pose proof (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA HB) as HPE.
  pose proof (wf_pi _ _ _ _ HAs HBq) as HPT.
  pose proof (convert_term _ _ _ _ _ HFty HPT HPE) as HF0.
  pose proof (convert_equality _ _ _ _ _ _ HFeq HPT HPE) as HE0.
  pose proof (wf_exp_sub _ _ _ _ _ HS HM) as HMs.
  destruct (reconstruct_readback_application _ _ _ _ _ _ _ _
    HAs HBq HF0 HE0 HMs HMty HMeq) as (HApp & EApp).
  pose proof (type_lift_at_argument _ _ _ _ _ _ _ _ HS HA HB HMs) as HEarg.
  assert (HBol : {{ Γ ⊢ B[Id,,M] : Type@i }}) by eauto using type_substitution, typing_identity_extension.
  pose proof (type_substitution _ _ _ _ _ HS HBol) as HBT.
  pose proof (type_argument_substitution_composition _ _ _ _ _ _ _ _ HS HA HB HM) as HBE.
  assert (HEapp : {{ Δ ⊢ B[q σ][Id,,M[σ]] ≈ B[Id,,M][σ] : Type@i }}).
  { eapply wf_exp_eq_trans; [exact HEarg | now apply wf_exp_eq_sym]. }
  exists (ne_app f0 m0). cbn. repeat split.
  - exact (read_ne_app _ _ _ _ _ Hf Hm).
  - exact (convert_term _ _ _ _ _ HApp HBT HEapp).
  - eapply wf_exp_eq_trans with (M' := {{{ F[σ] M[σ] }}}).
    + eapply convert_equality; [exact (wf_exp_eq_app_sub _ _ _ _ _ _ _ _ HS HA HB HF HM) | exact HBT |].
      exact (wf_exp_eq_sym _ _ _ _ HBE).
    + exact (convert_equality _ _ _ _ _ _ EApp HBT HEapp).
Qed.

Local Lemma typed_neutral_readback_fst Γ A B P i p :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ P : Σ A B }} ->
  typed_neutral_readback Γ {{{ Σ A B }}} P p ->
  typed_neutral_readback Γ A {{{ fst P }}} (d_fst p).
Proof.
  intros HA HB HP HR Δ σ HW.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (type_substitution _ _ _ _ _ HQ HB) as HBq.
  pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB) as HPE.
  pose proof (wf_sigma _ _ _ _ HAs HBq) as HPT.
  destruct (HR _ _ HW) as (p0 & Hp & HT & HE).
  pose proof (convert_term _ _ _ _ _ HT HPT HPE) as HP0.
  pose proof (convert_equality _ _ _ _ _ _ HE HPT HPE) as HE0.
  destruct (reconstruct_readback_first _ _ _ _ _ _ HAs HBq HP0 HE0) as (Hfst & HEfst).
  exists (ne_fst p0). cbn. repeat split; try assumption.
  - exact (read_ne_fst _ _ _ Hp).
  - eapply wf_exp_eq_trans.
    + exact (wf_exp_eq_fst_sub _ _ _ _ _ _ _ HS HA HB HP).
    + exact HEfst.
Qed.

Local Lemma typed_neutral_readback_snd Γ A B P i p :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ P : Σ A B }} ->
  typed_neutral_readback Γ {{{ Σ A B }}} P p ->
  typed_neutral_readback Γ {{{ B[Id,,fst P] }}} {{{ snd P }}} (d_snd p).
Proof.
  intros HA HB HP HR Δ σ HW.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (type_substitution _ _ _ _ _ HQ HB) as HBq.
  pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB) as HPE.
  pose proof (wf_sigma _ _ _ _ HAs HBq) as HPT.
  destruct (HR _ _ HW) as (p0 & Hp & HT & HE).
  pose proof (convert_term _ _ _ _ _ HT HPT HPE) as HP0.
  pose proof (convert_equality _ _ _ _ _ _ HE HPT HPE) as HE0.
  pose proof (wf_exp_sub _ _ _ _ _ HS HP) as HPs.
  pose proof (convert_term _ _ _ _ _ HPs HPT HPE) as HPsc.
  destruct (reconstruct_readback_second _ _ _ _ _ _ HAs HBq HPsc HP0 HE0) as (Hsnd & HEsnd).
  pose proof (wf_fst _ _ _ _ _ HA HB HP) as Hfst.
  pose proof (wf_fst _ _ _ _ _ HAs HBq HPsc) as HFstSub.
  pose proof (wf_exp_eq_fst_sub _ _ _ _ _ _ _ HS HA HB HP) as EFstSub.
  assert (HOldType : {{ Γ ⊢ B[Id,,fst P] : Type@i }}) by eauto using type_substitution, typing_identity_extension.
  pose proof (type_substitution _ _ _ _ _ HS HOldType) as HBT.
  pose proof (type_argument_substitution_composition _ _ _ _ _ _ _ _ HS HA HB Hfst) as HBE.
  pose proof (type_lift_at_argument _ _ _ _ _ _ _ _ HS HA HB HFstSub) as HLift.
  assert (HSt : {{ Δ ⊢s σ,,(fst P)[σ] : Γ, A }})
    by eauto using wf_sub_extend, wf_exp_sub.
  assert (HSTe : {{ Δ ⊢s σ,,(fst P)[σ] ≈ σ,,fst P[σ] : Γ, A }})
    by eauto using wf_sub_eq_extend_cong, substitution_equality_reflexive.
  pose proof (type_substitution_equality_same_body _ _ _ _ _ _ HSt HSTe HB) as HBE'.
  assert (Hty_snd : {{ Δ ⊢ B[σ,,fst P[σ]] ≈ B[Id,,fst P][σ] : Type@i }})
    by (apply wf_exp_eq_sym; eapply wf_exp_eq_trans; eassumption).
  assert (HEq : {{ Δ ⊢ B[q σ][Id,,fst P[σ]] ≈ B[Id,,fst P][σ] : Type@i }})
    by (eapply wf_exp_eq_trans; [exact HLift | exact Hty_snd]).
  exists (ne_snd p0). cbn. repeat split.
  - exact (read_ne_snd _ _ _ Hp).
  - exact (convert_term _ _ _ _ _ Hsnd HBT HEq).
  - eapply wf_exp_eq_trans with (M' := {{{ snd P[σ] }}}).
    + exact (convert_equality _ _ _ _ _ _ (wf_exp_eq_snd_sub _ _ _ _ _ _ _ HS HA HB HP) HBT Hty_snd).
    + exact (convert_equality _ _ _ _ _ _ HEsnd HBT HEq).
Qed.

Local Lemma initial_environment_of_prefix Γ Δ σ η :
  context_weakening Γ Δ σ ->
  initial_env Δ η ->
  exists ρ, initial_env Γ ρ /\ eval_sub σ η ρ.
Proof.
  intros HW. revert η.
  induction HW as [Γ HΓ |Γ Δ σ A i HW IH HA]; intros η Hη.
  - exists η. split; [exact Hη | apply eval_sub_id].
  - inversion Hη as [ | Δ0 ρ A0 a Hρ He]; subst.
    destruct (IH _ Hρ) as (ηold & Hold & Hσ).
    exists ηold. split; [exact Hold |].
    eapply eval_sub_compose; [apply eval_sub_weaken | exact Hσ].
Qed.

Local Lemma typed_readback_subtyping D W (read : nat -> D -> W -> Prop) embed Γ A B M d i :
  {{ Γ ⊢ B : Type@i }} ->
  {{ Γ ⊢ A ⊆ B }} ->
  typed_readback read embed Γ A M d ->
  typed_readback read embed Γ B M d.
Proof.
  intros HB Hsub H Δ σ HW.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  pose proof (type_substitution _ _ _ _ _ HS HB) as HBT.
  pose proof (subtyping_under_substitution _ _ _ Hsub _ _ HS) as Hsubw.
  destruct (H _ _ HW) as (w & HR & HT & HE).
  exists w. repeat split; try assumption.
  - exact (wf_exp_subtyp _ _ _ _ _ HT HBT Hsubw).
  - exact (wf_exp_eq_subtyp _ _ _ _ _ _ HE HBT Hsubw).
Qed.

Local Lemma typed_readback_observation Γ A M a m N :
  {{ Γ ⊢ M : A }} ->
  typed_value_readback Γ A M a m ->
  read_nf (length Γ) (d_dom a m) N ->
  {{ Γ ⊢ N : A }} /\ {{ Γ ⊢ M ≈ N : A }}.
Proof.
  intros HM HR HN.
  destruct (type_of_typing _ _ _ HM) as [i HA].
  destruct (typed_readback_here _ _ _ _ _ _ _ _ _ HA HM HR) as (W & Hw & HT & HE).
  pose proof (proj1 readback_deterministic _ _ _ HN _ Hw). subst W.
  split; assumption.
Qed.

Local Lemma nbe_evaluation_readback Γ A M N ρ a m :
  nbe Γ M A N ->
  initial_env Γ ρ ->
  eval_exp A ρ a ->
  eval_exp M ρ m ->
  read_nf (length Γ) (d_dom a m) N.
Proof.
  intros HN Hρ HA HM.
  inversion HN as [Γ0 η A0 b M0 n W Hη HB Hm HR]; subst.
  pose proof (initial_env_deterministic _ _ Hρ _ Hη). subst η.
  pose proof (eval_exp_deterministic _ _ _ HA _ HB). subst b.
  pose proof (eval_exp_deterministic _ _ _ HM _ Hm). subst n.
  exact HR.
Qed.

Local Definition initialized_typed_readback :=
  forall Γ A M ρ a m,
    wf_exp Γ A M -> initial_env Γ ρ ->
    eval_exp A ρ a -> eval_exp M ρ m -> typed_value_readback Γ A M a m.

Local Lemma initialized_typed_readback_equivalent :
  initialized_typed_readback <-> readback_preserves_typing.
Proof.
  split.
  - intros H Γ A M N HM HN.
    inversion HN as [Γ0 ρ A0 a M0 m W Hρ HA Hm HR]; subst.
    eapply typed_readback_observation; [exact HM | | exact HR].
    exact (H _ _ _ _ _ _ HM Hρ HA Hm).
  - intros H Γ A M ρ a m HM Hρ HA Hm Δ σ HW.
    pose proof (context_weakening_typed _ _ _ HW) as HS.
    pose proof (substitution_source _ _ _ HS) as HΔ.
    pose proof (proj1 declarative_interpretation _ HΔ) as HD.
    destruct (interpreted_context_has_environment _ HD) as (η & Hη & _).
    destruct (initial_environment_of_prefix _ _ _ _ HW Hη) as (ρ0 & Hρ0 & Hσ).
    pose proof (initial_env_deterministic _ _ Hρ _ Hρ0). subst ρ0.
    pose proof (wf_exp_sub _ _ _ _ _ HS HM) as HMs.
    destruct (declarative_readback_total _ _ _ HMs) as (w & Hnb).
    destruct (H _ _ _ _ HMs Hnb) as [HT HE].
    exists w. repeat split; try assumption.
    eapply nbe_evaluation_readback; [exact Hnb | exact Hη | | ];
      (eapply eval_exp_sub; eassumption).
Qed.

Local Lemma typed_type_readback_universe_constructor Γ i :
  typed_type_readback Γ (S i) (a_typ i) (d_univ i).
Proof.
  intros Δ σ HW.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  pose proof (substitution_source _ _ _ HS) as HΔ.
  pose proof (substitution_target _ _ _ HS) as HΓ.
  pose proof (type_substitution _ _ _ _ _ HS (wf_typ Γ (S i) HΓ)) as HT.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_typ_sub _ _ _ (S i) HS)) as HE.
  exists (nf_typ i). cbn. repeat split.
  - apply read_typ_univ.
  - exact (convert_term _ _ _ _ _ (wf_typ Δ i HΔ) HT HE).
  - exact (convert_equality _ _ _ _ _ _ (wf_exp_eq_typ_sub _ _ _ i HS) HT HE).
Qed.

Local Lemma typed_type_readback_natural_constructor Γ :
  typed_type_readback Γ 0 a_nat d_nat.
Proof.
  intros Δ σ HW.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  pose proof (substitution_source _ _ _ HS) as HΔ.
  pose proof (substitution_target _ _ _ HS) as HΓ.
  pose proof (type_substitution _ _ _ _ _ HS (wf_typ Γ 0 HΓ)) as HT.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_typ_sub _ _ _ 0 HS)) as HE.
  exists nf_nat. cbn. repeat split.
  - apply read_typ_nat.
  - exact (convert_term _ _ _ _ _ (wf_nat Δ HΔ) HT HE).
  - exact (convert_equality _ _ _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS) HT HE).
Qed.

Local Lemma typed_value_readback_zero_constructor Γ :
  typed_value_readback Γ a_nat a_zero d_nat d_zero.
Proof.
  intros Δ σ HW.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  pose proof (substitution_source _ _ _ HS) as HΔ.
  pose proof (substitution_target _ _ _ HS) as HΓ.
  pose proof (type_substitution _ _ _ _ _ HS (wf_nat Γ HΓ)) as HT.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS)) as HE.
  exists nf_zero. cbn. repeat split.
  - apply read_nf_zero.
  - exact (convert_term _ _ _ _ _ (wf_zero Δ HΔ) HT HE).
  - exact (convert_equality _ _ _ _ _ _ (wf_exp_eq_zero_sub _ _ _ HS) HT HE).
Qed.

Local Lemma typed_value_readback_successor Γ M m :
  {{ Γ ⊢ M : ℕ }} ->
  typed_value_readback Γ a_nat M d_nat m ->
  typed_value_readback Γ a_nat (a_succ M) d_nat (d_succ m).
Proof.
  intros HM HR Δ σ HW.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  pose proof (substitution_source _ _ _ HS) as HΔ.
  pose proof (substitution_target _ _ _ HS) as HΓ.
  pose proof (type_substitution _ _ _ _ _ HS (wf_nat Γ HΓ)) as HT.
  pose proof (wf_exp_eq_nat_sub _ _ _ HS) as HE.
  pose proof (wf_exp_eq_sym _ _ _ _ HE) as HE'.
  destruct (HR _ _ HW) as (w & Hw & HTw & HEw).
  pose proof (convert_term _ _ _ _ _ HTw (wf_nat Δ HΔ) HE) as HN.
  pose proof (convert_equality _ _ _ _ _ _ HEw (wf_nat Δ HΔ) HE) as EN.
  exists (nf_succ w). cbn. repeat split.
  - now apply read_nf_succ.
  - exact (convert_term _ _ _ _ _ (wf_succ _ _ HN) HT HE').
  - eapply convert_equality; [ | exact HT | exact HE'].
    eapply wf_exp_eq_trans.
    + exact (wf_exp_eq_succ_sub _ _ _ _ HS HM).
    + now apply wf_exp_eq_succ_cong.
Qed.

Local Lemma typed_value_readback_reflexivity Γ A M i a m :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  typed_type_readback Γ i A a ->
  typed_value_readback Γ A M a m ->
  typed_value_readback Γ {{{ Eq A M M }}} {{{ refl A M }}} (d_eq a m m) (d_refl m).
Proof.
  intros HA HM HAr HMr Δ σ HW.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (wf_exp_sub _ _ _ _ _ HS HM) as HMs.
  destruct (typed_type_readback_at_extension _ _ _ _ _ _ HW HAr) as (A0 & HRA & HA0 & HEA).
  destruct (HMr _ _ HW) as (M0 & HRM & HM0 & HEM).
  destruct (reconstruct_readback_refl _ _ _ _ _ _ HAs HA0 HEA HMs HM0 HEM) as (HT & HE).
  pose proof (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HS HA HM HM) as HEold.
  pose proof (type_substitution _ _ _ _ _ HS (wf_eq _ _ _ _ _ HA HM HM)) as HTold.
  pose proof (wf_exp_eq_sym _ _ _ _ HEold) as HBack.
  exists (nf_refl A0 M0). cbn. repeat split.
  - eapply read_nf_refl; eassumption.
  - exact (convert_term _ _ _ _ _ HT HTold HBack).
  - eapply wf_exp_eq_trans with (M' := {{{ refl A[σ] M[σ] }}}).
    + exact (wf_exp_eq_refl_sub _ _ _ _ _ _ HS HA HM).
    + exact (convert_equality _ _ _ _ _ _ HE HTold HBack).
Qed.


(* Syntactic substitutions paired with semantic environments. The
   realization relation supplies the witnesses for variables. *)

Local Definition term_realization := ctx -> typ -> exp -> domain -> domain -> Prop.

Local Definition realizes_environment (R : term_realization) Δ Γ σ (ρ : env) :=
  wf_sub Δ Γ σ /\
  forall x A, ctx_lookup x A Γ ->
    exists a, eval_exp A ρ a /\ R Δ (a_sub A σ) (a_sub (a_var x) σ) a (ρ x).

Local Definition realization_type_conversion (R : term_realization) :=
  forall Γ A B M a m i,
    wf_exp Γ (a_typ i) B -> wf_exp_eq Γ (a_typ i) A B ->
    R Γ A M a m -> R Γ B M a m.

Local Definition realization_term_conversion (R : term_realization) :=
  forall Γ A M N a m,
    wf_exp Γ A N -> wf_exp_eq Γ A N M -> R Γ A M a m -> R Γ A N a m.

Local Definition realization_weakening (R : term_realization) :=
  forall Γ Δ σ A M a m i,
    context_weakening Γ Δ σ -> wf_exp Γ (a_typ i) A -> wf_exp Γ A M ->
    R Γ A M a m -> R Δ (a_sub A σ) (a_sub M σ) a m.

Local Lemma realized_environment_empty R Δ σ ρ :
  wf_sub Δ nil σ -> realizes_environment R Δ nil σ ρ.
Proof. intro H. split; [exact H | intros x A Hx; inversion Hx]. Qed.

Local Lemma realized_environment_extend R Δ Γ σ ρ A M a m i :
  realization_type_conversion R ->
  realization_term_conversion R ->
  realizes_environment R Δ Γ σ ρ ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Δ ⊢ M : A[σ] }} ->
  eval_exp A ρ a ->
  R Δ (a_sub A σ) M a m ->
  realizes_environment R Δ (A :: Γ) (a_extend σ M) (extend_env ρ m).
Proof.
  intros Rtype Rterm [HS HR] HA HM Ha Hm.
  assert (HExt : {{ Δ ⊢s σ,,M : Γ, A }}) by eauto using wf_sub_extend.
  pose proof (substitution_target _ _ _ HS) as HΓ.
  assert (HAw : {{ Γ, A ⊢ A[Wk] : Type@i }}) by eauto using weaken_type.
  split; [exact HExt |].
  intros x B HL. inversion HL as [A0 Γ0 |n B0 Γ0 A0 Hlookup]; subst.
  - exists a. split.
    + eapply eval_exp_sub; [apply eval_sub_weaken | exact Ha].
    + assert (HT : {{ Δ ⊢ A[Wk][σ,,M] : Type@i }}) by eauto using type_substitution.
      pose proof (type_weakening_cancel _ _ _ _ _ _ _ _ HS HA HM HA) as HE.
      pose proof (wf_exp_eq_sym _ _ _ _ HE) as HE'.
      pose proof (wf_exp_eq_var_0_sub _ _ _ _ _ _ HS HA HM) as EM.
      cbn.
      eapply Rterm.
      * exact (wf_exp_sub _ _ _ _ _ HExt (wf_vlookup _ _ _ (substitution_target _ _ _ HExt) (here A Γ))).
      * exact (convert_equality _ _ _ _ _ _ EM HT HE').
      * exact (Rtype _ _ _ _ _ _ _ HT HE' Hm).
  - destruct (HR _ _ Hlookup) as (b & Hb & Hv).
    destruct (lookup_type _ _ _ Hlookup HΓ) as [j HB].
    assert (HBw : {{ Γ, A ⊢ B0[Wk] : Type@j }}) by eauto using weaken_type.
    assert (HT : {{ Δ ⊢ B0[Wk][σ,,M] : Type@j }}) by eauto using type_substitution.
    pose proof (type_weakening_cancel _ _ _ _ _ _ _ _ HS HA HM HB) as HE.
    pose proof (wf_exp_eq_sym _ _ _ _ HE) as HE'.
    pose proof (wf_exp_eq_var_S_sub _ _ _ _ _ _ _ _ HS HA HM Hlookup) as EM.
    exists b. split.
    + eapply eval_exp_sub; [apply eval_sub_weaken | exact Hb].
    + cbn. eapply Rterm.
      * exact (wf_exp_sub _ _ _ _ _ HExt (wf_vlookup _ _ _ (substitution_target _ _ _ HExt) (there _ _ _ _ Hlookup))).
      * exact (convert_equality _ _ _ _ _ _ EM HT HE').
      * exact (Rtype _ _ _ _ _ _ _ HT HE' Hv).
Qed.

Local Lemma realized_environment_substitution_conversion R Δ Γ σ τ ρ :
  realization_type_conversion R ->
  realization_term_conversion R ->
  realizes_environment R Δ Γ σ ρ ->
  {{ Δ ⊢s τ : Γ }} ->
  {{ Δ ⊢s σ ≈ τ : Γ }} ->
  realizes_environment R Δ Γ τ ρ.
Proof.
  intros Rtype Rterm [HS HR] HT HE. split; [exact HT |].
  intros x A HL.
  destruct (HR _ _ HL) as (a & Ha & Hreal).
  pose proof (substitution_target _ _ _ HS) as HΓ.
  destruct (lookup_type _ _ _ HL HΓ) as [i HA].
  pose proof (type_substitution _ _ _ _ _ HT HA) as HAτ.
  pose proof (type_substitution_equality_same_body _ _ _ _ _ _ HS HE HA) as HEA.
  pose proof (wf_vlookup _ _ _ HΓ HL) as Hvar.
  pose proof (wf_exp_eq_sub_cong _ _ _ _ _ _ _ (expression_equality_reflexive _ _ _ Hvar) HE) as Evar.
  exists a. split; [exact Ha |].
  eapply Rterm.
  - exact (wf_exp_sub _ _ _ _ _ HT Hvar).
  - apply wf_exp_eq_sym. exact (convert_equality _ _ _ _ _ _ Evar HAτ HEA).
  - exact (Rtype _ _ _ _ _ _ _ HAτ HEA Hreal).
Qed.

Local Lemma realized_environment_weaken R Δ Θ Γ σ τ ρ :
  realization_type_conversion R ->
  realization_term_conversion R ->
  realization_weakening R ->
  realizes_environment R Δ Γ σ ρ ->
  context_weakening Δ Θ τ ->
  realizes_environment R Θ Γ (a_compose σ τ) ρ.
Proof.
  intros Rtype Rterm Rweak [HS HR] HW.
  pose proof (context_weakening_typed _ _ _ HW) as HT.
  pose proof (wf_sub_compose _ _ _ _ _ HT HS) as HST.
  split; [exact HST |].
  intros x A HL.
  destruct (HR _ _ HL) as (a & Ha & Hreal).
  pose proof (substitution_target _ _ _ HS) as HΓ.
  destruct (lookup_type _ _ _ HL HΓ) as [i HA].
  pose proof (type_substitution _ _ _ _ _ HST HA) as HAS.
  pose proof (type_substitution_composition _ _ _ _ _ _ _ HT HS HA) as HEA.
  pose proof (wf_exp_eq_sym _ _ _ _ HEA) as HEAr.
  pose proof (wf_vlookup _ _ _ HΓ HL) as Hvar.
  pose proof (wf_exp_eq_sub_compose _ _ _ _ _ _ _ HT HS Hvar) as Evar.
  exists a. split; [exact Ha |].
  eapply Rterm; [exact (wf_exp_sub _ _ _ _ _ HST Hvar) | exact Evar |].
  exact (Rtype _ _ _ _ _ _ _ HAS HEAr (Rweak _ _ _ _ _ _ _ _ HW
    (type_substitution _ _ _ _ _ HS HA) (wf_exp_sub _ _ _ _ _ HS Hvar) Hreal)).
Qed.

Local Lemma realized_environment_drop R Δ Γ σ ρ B :
  realization_type_conversion R ->
  realization_term_conversion R ->
  realizes_environment R Δ (B :: Γ) σ ρ ->
  realizes_environment R Δ Γ (a_compose a_weaken σ) (drop_env ρ).
Proof.
  intros Rtype Rterm [HS HR].
  pose proof (substitution_target _ _ _ HS) as HC.
  assert (Hw : {{ Γ, B ⊢s Wk : Γ }}) by now apply wf_sub_weaken.
  pose proof (wf_sub_compose _ _ _ _ _ HS Hw) as HST.
  split; [exact HST |].
  intros x A HL.
  destruct (HR _ _ (there _ _ _ _ HL)) as (a & Ha & Hreal).
  destruct (invert_eval_substitution _ _ _ _ Ha) as (η & Hη & Haf).
  inversion Hη; subst.
  pose proof (substitution_target _ _ _ Hw) as HΓ.
  destruct (lookup_type _ _ _ HL HΓ) as [i HA].
  pose proof (type_substitution _ _ _ _ _ HST HA) as HT.
  pose proof (type_substitution_composition _ _ _ _ _ _ _ HS Hw HA) as HEA.
  pose proof (wf_exp_eq_sym _ _ _ _ HEA) as HEAr.
  pose proof (wf_vlookup _ _ _ HΓ HL) as Hvar.
  pose proof (wf_exp_eq_sub_compose _ _ _ _ _ _ _ HS Hw Hvar) as Evar.
  pose proof (wf_exp_eq_var_weaken _ _ _ _ HC HL) as Evarw.
  pose proof (equality_under_substitution _ _ _ _ _ _ HS Evarw) as Evarws.
  exists a. split; [exact Haf |].
  cbn. eapply Rterm.
  - exact (wf_exp_sub _ _ _ _ _ HST Hvar).
  - eapply wf_exp_eq_trans; [exact Evar |].
    exact (convert_equality _ _ _ _ _ _ Evarws HT HEAr).
  - exact (Rtype _ _ _ _ _ _ _ HT HEAr Hreal).
Qed.

Local Lemma realized_environment_compose_action
    R Γ Δ Θ σ τ M A a m i :
  realization_type_conversion R ->
  realization_term_conversion R ->
  {{ Θ ⊢s τ : Δ }} ->
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  R Θ (a_sub A (a_compose σ τ)) (a_sub M (a_compose σ τ)) a m ->
  R Θ (a_sub (a_sub A σ) τ) (a_sub (a_sub M σ) τ) a m.
Proof.
  intros Rtype Rterm HT HS HA HM HR.
  assert (Hty : {{ Θ ⊢ A[σ][τ] : Type@i }}) by eauto using type_substitution.
  pose proof (type_substitution_composition _ _ _ _ _ _ _ HT HS HA) as HE.
  pose proof (wf_exp_eq_sub_compose _ _ _ _ _ _ _ HT HS HM) as EM.
  eapply Rterm.
  - exact (wf_exp_sub _ _ _ _ _ HT (wf_exp_sub _ _ _ _ _ HS HM)).
  - exact (wf_exp_eq_sym _ _ _ _ (convert_equality _ _ _ _ _ _ EM Hty HE)).
  - exact (Rtype _ _ _ _ _ _ _ Hty HE HR).
Qed.

(* Calculations in an extended context may use any substitution
   judgmentally equal to the projection onto the original context. *)

Local Definition weakening_between Γ Δ σ :=
  exists τ, context_weakening Γ Δ τ /\ wf_sub Δ Γ σ /\ wf_sub_eq Δ Γ σ τ.

Local Lemma weakening_between_canonical Γ Δ σ :
  context_weakening Γ Δ σ -> weakening_between Γ Δ σ.
Proof.
  intro H. exists σ. split; [exact H |].
  pose proof (context_weakening_typed _ _ _ H) as HS.
  split; [exact HS | now apply substitution_equality_reflexive].
Qed.

Local Lemma weakening_between_typed Γ Δ σ :
  weakening_between Γ Δ σ -> wf_sub Δ Γ σ.
Proof. intros (τ & Hτ & HS & HE). exact HS. Qed.

Local Lemma weakening_between_composition Γ Δ Θ σ τ :
  weakening_between Γ Δ σ ->
  weakening_between Δ Θ τ ->
  weakening_between Γ Θ (a_compose σ τ).
Proof.
  intros (σ' & Hσ' & HS & ES) (τ' & Hτ' & HT & ET).
  destruct (context_weakening_compose _ _ _ _ _ Hσ' Hτ') as (ω & HW & HE).
  exists ω. repeat split; try assumption.
  - exact (wf_sub_compose _ _ _ _ _ HT HS).
  - eapply wf_sub_eq_trans; [ | exact HE].
    eapply wf_sub_eq_compose_cong; eassumption.
Qed.

Local Lemma typed_readback_under_weakening D W (read : nat -> D -> W -> Prop) embed Γ Δ σ A M d i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  weakening_between Γ Δ σ ->
  typed_readback read embed Γ A M d ->
  typed_readback read embed Δ {{{ A[σ] }}} {{{ M[σ] }}} d.
Proof.
  intros HA HM (τ & HW & HS & HE) H.
  pose proof (typed_readback_weakening _ _ _ _ _ _ _ _ _ _ _ HA HM HW H) as HT.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (type_substitution_equality_same_body _ _ _ _ _ _ HS HE HA) as HEA.
  pose proof (wf_exp_eq_sub_cong _ _ _ _ _ _ _ (expression_equality_reflexive _ _ _ HM) HE) as HEM.
  eapply typed_readback_expression_conversion; [exact HEM |].
  exact (typed_readback_type_conversion _ _ _ _ _ _ _ _ _ _ HAs (wf_exp_eq_sym _ _ _ _ HEA) HT).
Qed.

(* Candidates retain a syntactic typing judgment and the action of a
   semantic value under elimination in each extension. *)

Local Definition value_candidate := exp -> domain -> Prop.

Local Definition candidates_equivalent (R S : value_candidate) :=
  forall M m, R M m <-> S M m.

Local Definition domain_candidate := ctx -> sub -> value_candidate.

Local Definition codomain_candidate := ctx -> sub -> exp -> domain -> value_candidate.

Local Definition candidate_universe :=
  nat -> ctx -> typ -> domain -> value_candidate -> Prop.

Inductive natural_candidate (Γ : ctx) : value_candidate :=
| candidate_zero M :
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ M ≈ zero : ℕ }} ->
    natural_candidate Γ M d_zero
| candidate_successor M N n :
    {{ Γ ⊢ M : ℕ }} ->
    {{ Γ ⊢ M ≈ succ N : ℕ }} ->
    natural_candidate Γ N n ->
    natural_candidate Γ M (d_succ n)
| candidate_neutral M a k :
    {{ Γ ⊢ M : ℕ }} ->
    typed_neutral_readback Γ a_nat M k ->
    natural_candidate Γ M (d_neut a k).

Local Lemma natural_candidate_typed Γ M m :
  natural_candidate Γ M m -> {{ Γ ⊢ M : ℕ }}.
Proof. destruct 1; assumption. Qed.

Local Lemma natural_candidate_quotes Γ M m :
  natural_candidate Γ M m -> typed_value_readback Γ a_nat M d_nat m.
Proof.
  induction 1 as [M HM HE | M N n HM HE Hn IH |M a k HM Hk].
  - eapply typed_readback_expression_conversion; [exact HE |].
    exact (typed_value_readback_zero_constructor Γ).
  - eapply typed_readback_expression_conversion; [exact HE |].
    eapply typed_value_readback_successor; eauto using natural_candidate_typed.
  - eapply typed_readback_atomic_reflection; [apply atomic_natural | exact Hk].
Qed.

Local Definition neutral_candidate Γ A : value_candidate :=
  fun M m => wf_exp Γ A M /\ exists tag k,
    m = d_neut tag k /\ typed_neutral_readback Γ A M k.

Local Definition equation_candidate Γ A P Q (R : value_candidate) : value_candidate :=
  fun M m => wf_exp Γ (a_eq A P Q) M /\
    ((exists tag k, m = d_neut tag k /\ typed_neutral_readback Γ (a_eq A P Q) M k) \/
     (exists N n, m = d_refl n /\ R N n /\
       wf_exp_eq Γ A N P /\ wf_exp_eq Γ A N Q /\
       wf_exp_eq Γ (a_eq A P Q) M (a_refl A N))).

Local Definition function_candidate Γ A B ρ C
    (R : domain_candidate) (S : codomain_candidate) : value_candidate :=
  fun F f =>
    wf_exp Γ (a_pi A B) F /\
    forall Δ σ, weakening_between Γ Δ σ ->
    forall N n, R Δ σ N n ->
    exists b r, eval_exp C (extend_env ρ n) b /\ eval_app f n r /\
      S Δ σ N n (a_app (a_sub F σ) N) r.

Local Definition sigma_candidate Γ A B ρ C
    (R : domain_candidate) (S : codomain_candidate) : value_candidate :=
  fun P p =>
    wf_exp Γ (a_sigma A B) P /\
    forall Δ σ, weakening_between Γ Δ σ ->
    exists x y b,
      eval_fst p x /\ eval_snd p y /\ eval_exp C (extend_env ρ x) b /\
      R Δ σ (a_fst (a_sub P σ)) x /\ S Δ σ (a_fst (a_sub P σ)) x (a_snd (a_sub P σ)) y.

Local Definition universe_candidate (U : candidate_universe) j Γ : value_candidate :=
  fun M m => exists R, U j Γ M m R.

Local Lemma typed_type_readback_remove_identity Γ i A a :
  {{ Γ ⊢ A : Type@i }} ->
  typed_type_readback Γ i {{{ A[Id] }}} a ->
  typed_type_readback Γ i A a.
Proof.
  intros HA H. eapply typed_readback_expression_conversion; [ | exact H].
  apply wf_exp_eq_sym, wf_exp_eq_sub_id. exact HA.
Qed.

Local Lemma typed_type_readback_raise Γ i j A a :
  {{ ⊢ Γ }} -> i <= j ->
  typed_type_readback Γ i A a -> typed_type_readback Γ j A a.
Proof.
  intros HΓ Hle H.
  eapply typed_readback_subtyping; [exact (wf_typ Γ j HΓ) | | exact H].
  exact (subtyping_universes _ _ _ HΓ Hle).
Qed.

Local Lemma last_variable_quotation_after_lift Γ Δ σ A i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Δ, A[σ] ⊢ #0 : A[σ∘Wk] }} /\
  typed_neutral_readback (a_sub A σ :: Δ) (a_sub A (a_compose σ a_weaken))
    (a_var 0) (d_var (length Δ)).
Proof.
  intros HS HA.
  split; [exact (last_variable_after_lifting _ _ _ _ _ HS HA) |].
  assert (HAs : {{ Δ ⊢ A[σ] : Type@i }}) by eauto using type_substitution.
  assert (HΔA : {{ ⊢ Δ, A[σ] }}) by eauto using wf_ctx_extend, substitution_source.
  assert (Hw : {{ Δ, A[σ] ⊢s Wk : Δ }}) by now apply wf_sub_weaken.
  assert (HLong : {{ Δ, A[σ] ⊢ A[σ∘Wk] : Type@i }})
    by eauto using type_substitution, wf_sub_compose.
  pose proof (type_substitution_composition _ _ _ _ _ _ _ Hw HS HA) as HE.
  pose proof (typed_readback_reflected_variable _ _ _ (here (a_sub A σ) Δ)) as H.
  assert (E : length (a_sub A σ :: Δ) - 0 - 1 = length Δ) by (change (S (length Δ) - 0 - 1 = length Δ); lia).
  rewrite E in H.
  exact (typed_readback_type_conversion _ _ _ _ _ _ _ _ _ _ HLong (wf_exp_eq_sym _ _ _ _ HE) H).
Qed.

Local Lemma apply_substituted_function Γ Δ σ A B F N i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ F : Π A B }} ->
  {{ Δ ⊢ N : A[σ] }} ->
  {{ Δ ⊢ B[σ,,N] : Type@i }} /\ {{ Δ ⊢ F[σ] N : B[σ,,N] }}.
Proof.
  intros HS HA HB HF HN.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (type_substitution _ _ _ _ _ HQ HB) as HBq.
  pose proof (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA HB) as HE.
  pose proof (wf_pi _ _ _ _ HAs HBq) as HP.
  pose proof (convert_term _ _ _ _ _ (wf_exp_sub _ _ _ _ _ HS HF) HP HE) as HFs.
  assert (HNsub : {{ Δ ⊢s σ,,N : Γ, A }}) by eauto using wf_sub_extend.
  pose proof (type_substitution _ _ _ _ _ HNsub HB) as HBT.
  split; [exact HBT |].
  exact (convert_term _ _ _ _ _ (wf_app _ _ _ _ _ _ HAs HBq HFs HN)
    HBT (type_lift_at_argument _ _ _ _ _ _ _ _ HS HA HB HN)).
Qed.

Local Lemma application_under_iterated_weakening Γ Δ Θ σ τ A B F N i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Θ ⊢s τ : Δ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ F : Π A B }} ->
  {{ Θ ⊢ N : A[σ∘τ] }} ->
  {{ Θ ⊢ F[σ][τ] N ≈ F[σ∘τ] N : B[σ∘τ,,N] }}.
Proof.
  intros HS HT HA HB HF HN.
  pose proof (wf_sub_compose _ _ _ _ _ HT HS) as HST.
  pose proof (type_substitution _ _ _ _ _ HST HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HST HA) as HQ.
  pose proof (type_substitution _ _ _ _ _ HQ HB) as HBq.
  pose proof (wf_exp_eq_pi_sub _ _ _ _ _ _ HST HA HB) as HE.
  pose proof (wf_pi _ _ _ _ HAs HBq) as HP.
  pose proof (wf_exp_eq_sub_compose _ _ _ _ _ _ _ HT HS HF) as EF.
  pose proof (convert_equality _ _ _ _ _ _ EF HP HE) as EFs.
  destruct (apply_substituted_function _ _ _ _ _ _ _ _ HST HA HB HF HN) as [HBs HFs].
  eapply convert_equality; [ | exact HBs | exact (type_lift_at_argument _ _ _ _ _ _ _ _ HST HA HB HN)].
  eapply wf_exp_eq_app_cong; [exact HAs | exact HBq | now apply wf_exp_eq_sym |].
  now apply expression_equality_reflexive.
Qed.

Local Lemma typed_equation_value_reindex Γ A P M a x y u :
  typed_value_readback Γ A P (d_eq a x x) M ->
  typed_value_readback Γ A P (d_eq a y u) M.
Proof.
  intros H Δ σ HW.
  destruct (H _ _ HW) as (w & Hread & HT & HE).
  exists w. repeat split; try assumption.
  inversion Hread; subst; eauto using read_nf_refl, read_nf_eq_neut.
Qed.

Local Lemma neutral_application_under_weakening Γ Δ σ A B F N i a k n :
  weakening_between Γ Δ σ ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ F : Π A B }} ->
  {{ Δ ⊢ N : A[σ] }} ->
  typed_neutral_readback Γ {{{ Π A B }}} F k ->
  typed_value_readback Δ {{{ A[σ] }}} N a n ->
  {{ Δ ⊢ F[σ] N : B[σ,,N] }} /\
  typed_neutral_readback Δ {{{ B[σ,,N] }}} {{{ F[σ] N }}} (d_app k (d_dom a n)).
Proof.
  intros HW HA HB HF HN HR Harg.
  pose proof (weakening_between_typed _ _ _ HW) as HS.
  destruct (apply_substituted_function _ _ _ _ _ _ _ _ HS HA HB HF HN) as [HBT HApp].
  split; [exact HApp |].
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (type_substitution _ _ _ _ _ HQ HB) as HBq.
  pose proof (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA HB) as HPE.
  pose proof (wf_pi _ _ _ _ HAs HBq) as HT.
  pose proof (typed_readback_under_weakening _ _ _ _ _ _ _ _ _ _ _
    (wf_pi _ _ _ _ HA HB) HF HW HR) as HRS.
  pose proof (typed_readback_type_conversion _ _ _ _ _ _ _ _ _ _ HT HPE HRS) as HRef.
  pose proof (convert_term _ _ _ _ _ (wf_exp_sub _ _ _ _ _ HS HF) HT HPE) as HFσ.
  pose proof (typed_neutral_readback_app _ _ _ _ _ _ _ _ _
    HAs HBq HFσ HN HRef Harg) as Hobs.
  exact (typed_readback_type_conversion _ _ _ _ _ _ _ _ _ _ HBT
    (type_lift_at_argument _ _ _ _ _ _ _ _ HS HA HB HN) Hobs).
Qed.

Local Lemma substituted_pair_components Γ Δ σ A B P i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ P : Σ A B }} ->
  {{ Δ ⊢ fst P[σ] : A[σ] }} /\
  {{ Δ ⊢ B[σ,,fst P[σ]] : Type@i }} /\
  {{ Δ ⊢ snd P[σ] : B[σ,,fst P[σ]] }}.
Proof.
  intros HS HA HB HP.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (type_substitution _ _ _ _ _ HQ HB) as HBq.
  pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB) as HPE.
  pose proof (wf_sigma _ _ _ _ HAs HBq) as HT.
  pose proof (convert_term _ _ _ _ _ (wf_exp_sub _ _ _ _ _ HS HP) HT HPE) as HPσ.
  pose proof (wf_fst _ _ _ _ _ HAs HBq HPσ) as HF.
  pose proof (wf_snd _ _ _ _ _ HAs HBq HPσ) as HSn.
  assert (Hsub : {{ Δ ⊢s σ,,fst P[σ] : Γ, A }}) by eauto using wf_sub_extend.
  pose proof (type_substitution _ _ _ _ _ Hsub HB) as HBT.
  split; [exact HF | split; [exact HBT |]].
  exact (convert_term _ _ _ _ _ HSn HBT (type_lift_at_argument _ _ _ _ _ _ _ _ HS HA HB HF)).
Qed.

Local Lemma neutral_pair_projections_under_weakening Γ Δ σ A B P i k :
  weakening_between Γ Δ σ ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ P : Σ A B }} ->
  typed_neutral_readback Γ {{{ Σ A B }}} P k ->
  typed_neutral_readback Δ {{{ A[σ] }}} {{{ fst P[σ] }}} (d_fst k) /\
  typed_neutral_readback Δ {{{ B[σ,,fst P[σ]] }}} {{{ snd P[σ] }}} (d_snd k).
Proof.
  intros HW HA HB HP HR.
  pose proof (weakening_between_typed _ _ _ HW) as HS.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (type_substitution _ _ _ _ _ HQ HB) as HBq.
  pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB) as HPE.
  pose proof (wf_sigma _ _ _ _ HAs HBq) as HT.
  pose proof (typed_readback_under_weakening _ _ _ _ _ _ _ _ _ _ _
    (wf_sigma _ _ _ _ HA HB) HP HW HR) as HRS.
  pose proof (typed_readback_type_conversion _ _ _ _ _ _ _ _ _ _ HT HPE HRS) as HRef.
  pose proof (convert_term _ _ _ _ _ (wf_exp_sub _ _ _ _ _ HS HP) HT HPE) as HPσ.
  split.
  - exact (typed_neutral_readback_fst _ _ _ _ _ _ HAs HBq HPσ HRef).
  - destruct (substituted_pair_components _ _ _ _ _ _ _ HS HA HB HP) as (HF & HBT & _).
    pose proof (typed_neutral_readback_snd _ _ _ _ _ _ HAs HBq HPσ HRef) as Hobs.
    exact (typed_readback_type_conversion _ _ _ _ _ _ _ _ _ _ HBT
      (type_lift_at_argument _ _ _ _ _ _ _ _ HS HA HB HF) Hobs).
Qed.

Local Lemma candidate_agreement_sym R S :
  candidates_equivalent R S -> candidates_equivalent S R.
Proof. intros H M m. specialize (H M m). tauto. Qed.

Local Lemma candidate_agreement_trans R S T :
  candidates_equivalent R S -> candidates_equivalent S T -> candidates_equivalent R T.
Proof. intros H K M m. specialize (H M m). specialize (K M m). tauto. Qed.

Local Lemma neutral_candidate_covariance Γ A B i :
  {{ Γ ⊢ B : Type@i }} ->
  {{ Γ ⊢ A ≈ B : Type@i }} ->
  forall M m, neutral_candidate Γ A M m -> neutral_candidate Γ B M m.
Proof.
  intros HB HE M m (HT & a & k & -> & HR).
  split; [exact (convert_term _ _ _ _ _ HT HB HE) |].
  exists a, k. split; [reflexivity |].
  exact (typed_readback_type_conversion _ _ _ _ _ _ _ _ _ _ HB HE HR).
Qed.

Local Lemma equation_candidate_covariance Γ A A' P P' Q Q' i R S :
  {{ Γ ⊢ A' : Type@i }} ->
  {{ Γ ⊢ A ≈ A' : Type@i }} ->
  {{ Γ ⊢ P' : A' }} ->
  {{ Γ ⊢ Q' : A' }} ->
  {{ Γ ⊢ P ≈ P' : A }} ->
  {{ Γ ⊢ Q ≈ Q' : A }} ->
  (forall M m, R M m -> wf_exp Γ A M) ->
  candidates_equivalent R S ->
  forall M m, equation_candidate Γ A P Q R M m ->
    equation_candidate Γ A' P' Q' S M m.
Proof.
  intros HA' EA HP' HQ' EP EQ HR HE M m [HM H].
  pose proof (wf_eq _ _ _ _ _ HA' HP' HQ') as HT.
  pose proof (wf_exp_eq_eq_cong _ _ _ _ _ _ _ _ EA EP EQ) as ET.
  split; [exact (convert_term _ _ _ _ _ HM HT ET) |].
  destruct H as [(a & k & -> & Hnr) | (N & n & -> & HN & ENP & ENQ & EM)].
  - left. exists a, k. split; [reflexivity |].
    exact (typed_readback_type_conversion _ _ _ _ _ _ _ _ _ _ HT ET Hnr).
  - right. exists N, n.
    assert (HNP : {{ Γ ⊢ N ≈ P' : A }}) by exact (wf_exp_eq_trans _ _ _ _ _ ENP EP).
    assert (HNQ : {{ Γ ⊢ N ≈ Q' : A }}) by exact (wf_exp_eq_trans _ _ _ _ _ ENQ EQ).
    split; [reflexivity | split; [now apply HE |]].
    split; [exact (convert_equality _ _ _ _ _ _ HNP HA' EA) |].
    split; [exact (convert_equality _ _ _ _ _ _ HNQ HA' EA) |].
    eapply wf_exp_eq_trans.
    + exact (convert_equality _ _ _ _ _ _ EM HT ET).
    + eapply convert_equality; [ | exact HT | exact (wf_exp_eq_eq_cong _ _ _ _ _ _ _ _ EA HNP HNQ)].
      exact (wf_exp_eq_refl_cong _ _ _ _ _ _ EA
        (expression_equality_reflexive _ _ _ (HR _ _ HN))).
Qed.

Local Lemma function_candidate_agreement Γ A A' B B' i ρ C R R' S S' :
  {{ Γ ⊢ Π A B : Type@i }} ->
  {{ Γ ⊢ Π A' B' : Type@i }} ->
  {{ Γ ⊢ Π A B ≈ Π A' B' : Type@i }} ->
  (forall Δ σ, weakening_between Γ Δ σ -> candidates_equivalent (R Δ σ) (R' Δ σ)) ->
  (forall Δ σ, weakening_between Γ Δ σ -> forall N n b,
    R Δ σ N n -> eval_exp C (extend_env ρ n) b ->
    candidates_equivalent (S Δ σ N n) (S' Δ σ N n)) ->
  candidates_equivalent (function_candidate Γ A B ρ C R S) (function_candidate Γ A' B' ρ C R' S').
Proof.
  intros HT HT' ET HD HC F f. split; intros [HF H].
  - split; [exact (convert_term _ _ _ _ _ HF HT' ET) |].
    intros Δ σ HW N n HN. apply (HD _ _ HW) in HN.
    destruct (H _ _ HW _ _ HN) as (b & r & Hb & Hr & HS).
    exists b, r. repeat split; try assumption.
    apply (HC _ _ HW _ _ _ HN Hb). exact HS.
  - split; [exact (convert_term _ _ _ _ _ HF HT (wf_exp_eq_sym _ _ _ _ ET)) |].
    intros Δ σ HW N n HN.
    assert (HN' : R' Δ σ N n) by now apply (HD _ _ HW).
    destruct (H _ _ HW _ _ HN') as (b & r & Hb & Hr & HS).
    exists b, r. repeat split; try assumption.
    apply (HC _ _ HW _ _ _ HN Hb). exact HS.
Qed.

Local Lemma sigma_candidate_agreement Γ A A' B B' i ρ C R R' S S' :
  {{ Γ ⊢ Σ A B : Type@i }} ->
  {{ Γ ⊢ Σ A' B' : Type@i }} ->
  {{ Γ ⊢ Σ A B ≈ Σ A' B' : Type@i }} ->
  (forall Δ σ, weakening_between Γ Δ σ -> candidates_equivalent (R Δ σ) (R' Δ σ)) ->
  (forall Δ σ, weakening_between Γ Δ σ -> forall N n b,
    R Δ σ N n -> eval_exp C (extend_env ρ n) b ->
    candidates_equivalent (S Δ σ N n) (S' Δ σ N n)) ->
  candidates_equivalent (sigma_candidate Γ A B ρ C R S) (sigma_candidate Γ A' B' ρ C R' S').
Proof.
  intros HT HT' ET HD HC P p. split; intros [HP H].
  - split; [exact (convert_term _ _ _ _ _ HP HT' ET) |].
    intros Δ σ HW. destruct (H _ _ HW) as (x & y & b & Hx & Hy & Hb & HRx & HSy).
    exists x, y, b. repeat split; try assumption.
    + now apply (HD _ _ HW).
    + now apply (HC _ _ HW _ _ _ HRx Hb).
  - split; [exact (convert_term _ _ _ _ _ HP HT (wf_exp_eq_sym _ _ _ _ ET)) |].
    intros Δ σ HW. destruct (H _ _ HW) as (x & y & b & Hx & Hy & Hb & HRx & HSy).
    apply (HD _ _ HW) in HRx.
    exists x, y, b. repeat split; try assumption.
    now apply (HC _ _ HW _ _ _ HRx Hb).
Qed.

Local Lemma substituted_application_equality Γ Δ σ A B F G N i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ F ≈ G : Π A B }} ->
  {{ Δ ⊢ N : A[σ] }} ->
  {{ Δ ⊢ F[σ] N ≈ G[σ] N : B[σ,,N] }}.
Proof.
  intros HS HA HB EF HN.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (type_substitution _ _ _ _ _ HQ HB) as HBq.
  pose proof (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA HB) as HE.
  pose proof (convert_equality _ _ _ _ _ _ (equality_under_substitution _ _ _ _ _ _ HS EF)
    (wf_pi _ _ _ _ HAs HBq) HE) as EFs.
  pose proof (wf_exp_eq_app_cong _ _ _ _ _ _ _ _ HAs HBq EFs
    (expression_equality_reflexive _ _ _ HN)) as EApp.
  assert (HSN : {{ Δ ⊢s σ,,N : Γ, A }}) by eauto using wf_sub_extend.
  exact (convert_equality _ _ _ _ _ _ EApp (type_substitution _ _ _ _ _ HSN HB)
    (type_lift_at_argument _ _ _ _ _ _ _ _ HS HA HB HN)).
Qed.

Local Lemma substituted_pair_equality Γ Δ σ A B P Q i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ P : Σ A B }} ->
  {{ Γ ⊢ Q : Σ A B }} ->
  {{ Γ ⊢ P ≈ Q : Σ A B }} ->
  {{ Δ ⊢ fst P[σ] ≈ fst Q[σ] : A[σ] }} /\
  {{ Δ ⊢ B[σ,,fst P[σ]] ≈ B[σ,,fst Q[σ]] : Type@i }} /\
  {{ Δ ⊢ snd P[σ] ≈ snd Q[σ] : B[σ,,fst P[σ]] }}.
Proof.
  intros HS HA HB HP HQ EP.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HL.
  pose proof (type_substitution _ _ _ _ _ HL HB) as HBl.
  pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB) as HE.
  pose proof (convert_equality _ _ _ _ _ _ (equality_under_substitution _ _ _ _ _ _ HS EP)
    (wf_sigma _ _ _ _ HAs HBl) HE) as EPs.
  pose proof (wf_exp_eq_fst_cong _ _ _ _ _ _ HAs HBl EPs) as EF.
  destruct (substituted_pair_components _ _ _ _ _ _ _ HS HA HB HP) as (HF & HBp & _).
  destruct (substituted_pair_components _ _ _ _ _ _ _ HS HA HB HQ) as (HF' & HBq & _).
  assert (HSP : {{ Δ ⊢s σ,,fst P[σ] : Γ, A }}) by eauto using wf_sub_extend.
  assert (Eσ : {{ Δ ⊢s σ,,fst P[σ] ≈ σ,,fst Q[σ] : Γ, A }}) by
    eauto using wf_sub_eq_extend_cong, substitution_equality_reflexive.
  repeat split.
  - exact EF.
  - exact (type_substitution_equality_same_body _ _ _ _ _ _ HSP Eσ HB).
  - exact (convert_equality _ _ _ _ _ _
      (wf_exp_eq_snd_cong _ _ _ _ _ _ HAs HBl EPs) HBp
      (type_lift_at_argument _ _ _ _ _ _ _ _ HS HA HB HF)).
Qed.

Local Lemma natural_candidate_expression_conversion Γ M N m :
  {{ Γ ⊢ N : ℕ }} ->
  {{ Γ ⊢ N ≈ M : ℕ }} ->
  natural_candidate Γ M m -> natural_candidate Γ N m.
Proof.
  intros HN E H.
  destruct H as [M HM EM | M P p HM EM HP | M a k HM HR].
  - apply candidate_zero; [exact HN | exact (wf_exp_eq_trans _ _ _ _ _ E EM)].
  - eapply candidate_successor; [exact HN | exact (wf_exp_eq_trans _ _ _ _ _ E EM) | exact HP].
  - eapply candidate_neutral; [exact HN |].
    exact (typed_readback_expression_conversion _ _ _ _ _ _ _ _ _ E HR).
Qed.

Local Lemma typed_neutral_readback_agreement Γ A M k k' :
  neutrals_agree k k' ->
  typed_neutral_readback Γ A M k ->
  typed_neutral_readback Γ A M k'.
Proof.
  intros Hne H Δ σ HW.
  destruct (H _ _ HW) as (w & Hw & HT & HE).
  destruct (Hne (length Δ)) as (w' & Hw' & HR).
  pose proof (proj1 (proj2 readback_deterministic) _ _ _ Hw _ Hw') as E. subst w'.
  exists w. auto.
Qed.

Local Lemma natural_candidate_semantic_transport Γ m n :
  natural_values_agree m n ->
  forall M, natural_candidate Γ M m -> natural_candidate Γ M n.
Proof.
  induction 1 as [ |m n H IH |m n H]; intros M HM.
  - exact HM.
  - inversion HM; subst. eapply candidate_successor; try eassumption. now apply IH.
  - destruct H as (a & b & k & k' & -> & -> & Hne).
    inversion HM; subst. apply candidate_neutral; [assumption |].
    eapply typed_neutral_readback_agreement; eassumption.
Qed.

Local Lemma lifted_substitution_at_argument Γ Δ Θ σ τ A N i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Θ ⊢s τ : Δ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Θ ⊢ N : A[σ][τ] }} ->
  {{ Θ ⊢s (q σ)∘(τ,,N) ≈ (σ∘τ),,N : Γ, A }}.
Proof.
  intros HS HT HA HN.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (wf_sub_extend _ _ _ _ _ _ HT HAs HN) as HTN.
  pose proof (wf_sub_eq_p_extend _ _ _ _ _ _ HT HAs HN) as EW.
  pose proof (wf_sub_eq_compose_cong _ _ _ _ _ _ _ EW
    (substitution_equality_reflexive _ _ _ HS)) as ES.
  pose proof (wf_sub_weaken _ _ (substitution_target _ _ _ HTN)) as HW.
  pose proof (wf_sub_compose _ _ _ _ _ HTN HW) as HTW.
  pose proof (wf_sub_compose _ _ _ _ _ HTW HS) as Htail.
  pose proof (type_substitution _ _ _ _ _ Htail HA) as HTailA.
  pose proof (type_substitution _ _ _ _ _ (wf_sub_compose _ _ _ _ _ HT HS) HA) as HAT.
  pose proof (type_substitution_equality_same_body _ _ _ _ _ _ Htail ES HA) as EStem.
  pose proof (type_substitution_composition _ _ _ _ _ _ _ HT HS HA) as EST.
  eapply wf_sub_eq_trans.
  - exact (lift_composition _ _ _ _ _ _ _ HS HA HTN).
  - eapply wf_sub_eq_extend_cong; [exact ES | exact HA |].
    eapply convert_equality; [exact (wf_exp_eq_var_0_sub _ _ _ _ _ _ HT HAs HN) | exact HTailA |].
    apply wf_exp_eq_sym.
    exact (wf_exp_eq_trans _ _ _ _ _ EStem EST).
Qed.

Local Lemma type_lifted_substitution_at_argument Γ Δ Θ σ τ A B N i j :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Θ ⊢s τ : Δ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@j }} ->
  {{ Θ ⊢ N : A[σ][τ] }} ->
  {{ Θ ⊢ B[q σ][τ,,N] ≈ B[σ∘τ,,N] : Type@j }}.
Proof.
  intros HS HT HA HB HN.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (wf_sub_extend _ _ _ _ _ _ HT (type_substitution _ _ _ _ _ HS HA) HN) as HTN.
  pose proof (wf_sub_compose _ _ _ _ _ HTN HQ) as HC.
  eapply wf_exp_eq_trans.
  - apply wf_exp_eq_sym. exact (type_substitution_composition _ _ _ _ _ _ _ HTN HQ HB).
  - exact (type_substitution_equality_same_body _ _ _ _ _ _ HC
      (lifted_substitution_at_argument _ _ _ _ _ _ _ _ HS HT HA HN) HB).
Qed.

Local Lemma natural_candidate_weakening Γ Δ σ M m :
  weakening_between Γ Δ σ ->
  natural_candidate Γ M m ->
  natural_candidate Δ (a_sub M σ) m.
Proof.
  intros HW HR.
  pose proof (weakening_between_typed _ _ _ HW) as HS.
  pose proof (wf_nat _ (substitution_source _ _ _ HS)) as HN.
  pose proof (wf_exp_eq_nat_sub _ _ _ HS) as EN.
  induction HR as [M HM EM | M P p HM EM HP IH | M a k HM Hk].
  - apply candidate_zero.
    + exact (convert_term _ _ _ _ _ (wf_exp_sub _ _ _ _ _ HS HM) HN EN).
    + eapply wf_exp_eq_trans; [ | exact (wf_exp_eq_zero_sub _ _ _ HS)].
      exact (convert_equality _ _ _ _ _ _
        (equality_under_substitution _ _ _ _ _ _ HS EM) HN EN).
  - eapply candidate_successor with (N := a_sub P σ).
    + exact (convert_term _ _ _ _ _ (wf_exp_sub _ _ _ _ _ HS HM) HN EN).
    + eapply wf_exp_eq_trans; [ | exact (wf_exp_eq_succ_sub _ _ _ _ HS
        (natural_candidate_typed _ _ _ HP))].
      exact (convert_equality _ _ _ _ _ _
        (equality_under_substitution _ _ _ _ _ _ HS EM) HN EN).
    + exact IH.
  - apply candidate_neutral.
    + exact (convert_term _ _ _ _ _ (wf_exp_sub _ _ _ _ _ HS HM) HN EN).
    + eapply typed_readback_type_conversion; [exact HN | exact EN |].
      exact (typed_readback_under_weakening _ _ _ _ _ _ _ _ _ _ _
        (wf_nat _ (substitution_target _ _ _ HS)) HM HW Hk).
Qed.

Local Lemma neutral_candidate_weakening Γ Δ σ A M m i :
  {{ Γ ⊢ A : Type@i }} ->
  weakening_between Γ Δ σ ->
  neutral_candidate Γ A M m -> neutral_candidate Δ (a_sub A σ) (a_sub M σ) m.
Proof.
  intros HA HW (HM & a & k & -> & Hne).
  split.
  - exact (wf_exp_sub _ _ _ _ _ (weakening_between_typed _ _ _ HW) HM).
  - exists a, k. split; [reflexivity |].
    exact (typed_readback_under_weakening _ _ _ _ _ _ _ _ _ _ _ HA HM HW Hne).
Qed.

Local Lemma equation_candidate_weakening Γ Δ σ A P Q i R S :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ P : A }} ->
  {{ Γ ⊢ Q : A }} ->
  weakening_between Γ Δ σ ->
  (forall M m, R M m -> {{ Γ ⊢ M : A }}) ->
  (forall M m, R M m -> S (a_sub M σ) m) ->
  forall M m, equation_candidate Γ A P Q R M m ->
    equation_candidate Δ (a_sub A σ) (a_sub P σ) (a_sub Q σ) S (a_sub M σ) m.
Proof.
  intros HA HP HQ HW HR Hmem M m (HM & H).
  pose proof (weakening_between_typed _ _ _ HW) as Hσ.
  pose proof (type_substitution _ _ _ _ _ Hσ HA) as HAs.
  pose proof (wf_eq _ _ _ _ _ HA HP HQ) as HEq.
  pose proof (wf_eq _ _ _ _ _ HAs
    (wf_exp_sub _ _ _ _ _ Hσ HP) (wf_exp_sub _ _ _ _ _ Hσ HQ)) as HT.
  pose proof (wf_exp_eq_eq_sub _ _ _ _ _ _ _ Hσ HA HP HQ) as ET.
  split; [exact (convert_term _ _ _ _ _ (wf_exp_sub _ _ _ _ _ Hσ HM) HT ET) |].
  destruct H as [(a & k & -> & Hne) | (N & n & -> & HN & EP & EQ & EM)].
  - left. exists a, k. split; [reflexivity |].
    eapply typed_readback_type_conversion; [exact HT | exact ET |].
    exact (typed_readback_under_weakening _ _ _ _ _ _ _ _ _ _ _ HEq HM HW Hne).
  - right. exists (a_sub N σ), n. split; [reflexivity |].
    split; [exact (Hmem _ _ HN) |].
    pose proof (equality_under_substitution _ _ _ _ _ _ Hσ EP) as EPs.
    pose proof (equality_under_substitution _ _ _ _ _ _ Hσ EQ) as EQs.
    split; [exact EPs | split; [exact EQs |]].
    eapply wf_exp_eq_trans.
    + exact (convert_equality _ _ _ _ _ _
        (equality_under_substitution _ _ _ _ _ _ Hσ EM) HT ET).
    + eapply convert_equality.
      * exact (wf_exp_eq_refl_sub _ _ _ _ _ _ Hσ HA (HR _ _ HN)).
      * exact HT.
      * eapply wf_exp_eq_trans.
        -- exact (wf_exp_eq_eq_sub _ _ _ _ _ _ _ Hσ HA (HR _ _ HN) (HR _ _ HN)).
        -- exact (wf_exp_eq_eq_cong _ _ _ _ _ _ _ _
            (expression_equality_reflexive _ _ _ HAs) EPs EQs).
Qed.

Local Lemma pair_projections_under_iterated_weakening Γ Δ Θ σ τ A B P i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Θ ⊢s τ : Δ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ P : Σ A B }} ->
  {{ Θ ⊢ fst P[σ][τ] : A[σ∘τ] }} /\
  {{ Θ ⊢ fst P[σ][τ] ≈ fst P[σ∘τ] : A[σ∘τ] }} /\
  {{ Θ ⊢ snd P[σ][τ] : B[σ∘τ,,fst P[σ][τ]] }} /\
  {{ Θ ⊢ snd P[σ][τ] ≈ snd P[σ∘τ] : B[σ∘τ,,fst P[σ][τ]] }}.
Proof.
  intros Hσ Hτ HA HB HP.
  pose proof (wf_sub_compose _ _ _ _ _ Hτ Hσ) as HS.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (type_substitution _ _ _ _ _ (lifted_substitution _ _ _ _ _ HS HA) HB) as HBs.
  pose proof (wf_sigma _ _ _ _ HAs HBs) as HT.
  pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB) as Eσ.
  pose proof (type_substitution_composition _ _ _ _ _ _ _ Hτ Hσ
    (wf_sigma _ _ _ _ HA HB)) as EST.
  pose proof (wf_exp_eq_trans _ _ _ _ _ (wf_exp_eq_sym _ _ _ _ EST) Eσ) as ET.
  pose proof (convert_term _ _ _ _ _ (wf_exp_sub _ _ _ _ _ Hτ
    (wf_exp_sub _ _ _ _ _ Hσ HP)) HT ET) as HP'.
  pose proof (wf_fst _ _ _ _ _ HAs HBs HP') as HF.
  pose proof (wf_snd _ _ _ _ _ HAs HBs HP') as HSn.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_sub_compose _ _ _ _ _ _ _ Hτ Hσ HP)) as EP.
  pose proof (convert_equality _ _ _ _ _ _ EP HT Eσ) as EP'.
  pose proof (wf_exp_eq_fst_cong _ _ _ _ _ _ HAs HBs EP') as EF.
  pose proof (wf_exp_eq_snd_cong _ _ _ _ _ _ HAs HBs EP') as ESn.
  pose proof (type_lift_at_argument _ _ _ _ _ _ _ _ HS HA HB HF) as EL.
  pose proof (type_substitution _ _ _ _ _ (wf_sub_extend _ _ _ _ _ _ HS HA HF) HB) as HC.
  repeat split; try assumption.
  - exact (convert_term _ _ _ _ _ HSn HC EL).
  - exact (convert_equality _ _ _ _ _ _ ESn HC EL).
Qed.

Local Lemma substituted_lambda_application Γ Δ σ A B M N i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ, A ⊢ M : B }} ->
  {{ Δ ⊢ N : A[σ] }} ->
  {{ Δ ⊢ (λ A M)[σ] N ≈ M[σ,,N] : B[σ,,N] }}.
Proof.
  intros HS HA HB HM HN.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (type_substitution _ _ _ _ _ HQ HB) as HBq.
  pose proof (wf_exp_sub _ _ _ _ _ HQ HM) as HMq.
  pose proof (wf_pi _ _ _ _ HAs HBq) as HP.
  pose proof (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA HB) as EP.
  pose proof (convert_equality _ _ _ _ _ _
    (wf_exp_eq_fn_sub _ _ _ _ _ _ _ HS HA HM) HP EP) as EF.
  pose proof (wf_exp_eq_app_cong _ _ _ _ _ _ _ _ HAs HBq EF
    (expression_equality_reflexive _ _ _ HN)) as Eapp.
  pose proof (wf_exp_eq_pi_beta _ _ _ _ _ _ HAs HBq HMq HN) as Ebeta.
  pose proof (type_lift_at_argument _ _ _ _ _ _ _ _ HS HA HB HN) as EL.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HN) as HSN.
  pose proof (type_substitution _ _ _ _ _ HSN HB) as HT.
  eapply wf_exp_eq_trans.
  - exact (convert_equality _ _ _ _ _ _ (wf_exp_eq_trans _ _ _ _ _ Eapp Ebeta) HT EL).
  - pose proof (typing_identity_extension _ _ _ _ HAs HN) as Hext.
    pose proof (wf_sub_compose _ _ _ _ _ Hext HQ) as HC.
    pose proof (lift_at_argument _ _ _ _ _ _ HS HA HN) as Eσ.
    pose proof (type_substitution_equality_same_body _ _ _ _ _ _ HC Eσ HB) as Ecod.
    eapply wf_exp_eq_trans.
    + exact (convert_equality _ _ _ _ _ _
        (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_sub_compose _ _ _ _ _ _ _ Hext HQ HM)) HT Ecod).
    + exact (convert_equality _ _ _ _ _ _
        (wf_exp_eq_sub_cong _ _ _ _ _ _ _
          (expression_equality_reflexive _ _ _ HM) Eσ) HT Ecod).
Qed.

Local Lemma nominal_projection_typing Γ Δ σ A B P i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ P : Σ A B }} ->
  {{ Δ ⊢ (fst P)[σ] ≈ fst P[σ][Id] : A[σ] }} /\
  {{ Δ ⊢ (snd P)[σ] ≈ snd P[σ][Id] : B[Id,,fst P][σ] }}.
Proof.
  intros HS HA HB HP.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (type_substitution _ _ _ _ _ (lifted_substitution _ _ _ _ _ HS HA) HB) as HBs.
  pose proof (wf_sigma _ _ _ _ HAs HBs) as HT.
  pose proof (wf_exp_sub _ _ _ _ _ HS HP) as HPs.
  pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB) as ET.
  pose proof (convert_equality _ _ _ _ _ _
    (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_sub_id _ _ _ HPs)) HT ET) as EP.
  pose proof (wf_exp_eq_fst_sub _ _ _ _ _ _ _ HS HA HB HP) as EF.
  split.
  - exact (wf_exp_eq_trans _ _ _ _ _ EF (wf_exp_eq_fst_cong _ _ _ _ _ _ HAs HBs EP)).
  - pose proof (wf_fst _ _ _ _ _ HA HB HP) as HF.
    pose proof (substituted_pair_components _ _ _ _ _ _ _ HS HA HB HP) as (HFs & HBp & _).
    pose proof (wf_exp_sub _ _ _ _ _ HS HF) as HFsub.
    pose proof (type_lift_at_argument _ _ _ _ _ _ _ _ HS HA HB HFs) as EL.
    pose proof (type_argument_substitution_composition _ _ _ _ _ _ _ _ HS HA HB HF) as EB.
    pose proof (type_substitution _ _ _ _ _
      (typing_identity_extension _ _ _ _ HA HF) HB) as HOut.
    pose proof (type_substitution _ _ _ _ _ HS HOut) as HFinal.
    pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HFsub) as HSN.
    pose proof (wf_sub_eq_extend_cong _ _ _ _ _ _ _ _ (substitution_equality_reflexive _ _ _ HS) HA EF) as ESN.
    pose proof (type_substitution_equality_same_body _ _ _ _ _ _ HSN ESN HB) as ECode.
    pose proof (wf_exp_eq_snd_sub _ _ _ _ _ _ _ HS HA HB HP) as ESub.
    pose proof (convert_equality _ _ _ _ _ _ (wf_exp_eq_snd_cong _ _ _ _ _ _ HAs HBs EP) HBp EL) as ESnd.
    eapply convert_equality; [exact (wf_exp_eq_trans _ _ _ _ _ ESub ESnd) | exact HFinal |].
    apply wf_exp_eq_sym. exact (wf_exp_eq_trans _ _ _ _ _ EB ECode).
Qed.

Local Lemma substituted_pair_beta Γ Δ σ A B M N i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  {{ Γ ⊢ N : B[Id,,M] }} ->
  let P := a_sub (a_pair M A N B) σ in
  wf_exp Δ (a_sub A σ) (a_fst P) /\
  wf_exp_eq Δ (a_sub A σ) (a_fst P) (a_sub M σ) /\
  wf_exp Δ (a_sub B (a_extend σ (a_fst P))) (a_snd P) /\
  wf_exp_eq Δ (a_sub B (a_extend σ (a_fst P))) (a_snd P) (a_sub N σ).
Proof.
  intros HS HA HB HM HN P.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (type_substitution _ _ _ _ _ (lifted_substitution _ _ _ _ _ HS HA) HB) as HBs.
  pose proof (wf_exp_sub _ _ _ _ _ HS HM) as HMs.
  pose proof (type_argument_substitution_composition _ _ _ _ _ _ _ _ HS HA HB HM) as Earg.
  pose proof (type_lift_at_argument _ _ _ _ _ _ _ _ HS HA HB HMs) as ELift.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HMs) as HSM.
  pose proof (type_substitution _ _ _ _ _ HSM HB) as HBm.
  pose proof (typing_identity_extension _ _ _ _ HAs HMs) as HId.
  pose proof (type_substitution _ _ _ _ _ HId HBs) as HNm.
  pose proof (wf_exp_eq_trans _ _ _ _ _ Earg (wf_exp_eq_sym _ _ _ _ ELift)) as Etype.
  pose proof (convert_term _ _ _ _ _ (wf_exp_sub _ _ _ _ _ HS HN) HNm Etype) as HNs.
  pose proof (wf_pair _ _ _ _ _ _ HA HB HM HN) as HP.
  pose proof (wf_sigma _ _ _ _ HAs HBs) as HT.
  pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB) as EΣ.
  pose proof (convert_equality _ _ _ _ _ _
    (wf_exp_eq_pair_sub _ _ _ _ _ _ _ _ HS HA HB HM HN) HT EΣ) as EP.
  pose proof (convert_term _ _ _ _ _ (wf_exp_sub _ _ _ _ _ HS HP) HT EΣ) as HPs.
  pose proof (wf_fst _ _ _ _ _ HAs HBs HPs) as HF.
  pose proof (wf_snd _ _ _ _ _ HAs HBs HPs) as HSn.
  pose proof (wf_exp_eq_fst_cong _ _ _ _ _ _ HAs HBs EP) as EF.
  pose proof (wf_exp_eq_fst_beta _ _ _ _ _ _ HAs HBs HMs HNs) as EFβ.
  pose proof (wf_exp_eq_trans _ _ _ _ _ EF EFβ) as EFirst.
  pose proof (type_lift_at_argument _ _ _ _ _ _ _ _ HS HA HB HF) as EFarg.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HF) as HSF.
  pose proof (type_substitution _ _ _ _ _ HSF HB) as HTF.
  pose proof (wf_sub_eq_extend_cong _ _ _ _ _ _ _ _
    (substitution_equality_reflexive _ _ _ HS) HA EF) as ESub.
  pose proof (type_substitution_equality_same_body _ _ _ _ _ _ HSF ESub HB) as EBody.
  pose proof (wf_exp_eq_snd_cong _ _ _ _ _ _ HAs HBs EP) as ESn.
  pose proof (wf_exp_eq_snd_beta _ _ _ _ _ _ HAs HBs HMs HNs) as ESβ.
  pose proof (wf_sub_eq_extend_cong _ _ _ _ _ _ _ _
    (substitution_equality_reflexive _ _ _ HS) HA EFirst) as ESub'.
  pose proof (type_substitution_equality_same_body _ _ _ _ _ _ HSF ESub' HB) as EBody'.
  repeat split.
  - exact HF.
  - exact EFirst.
  - exact (convert_term _ _ _ _ _ HSn HTF EFarg).
  - eapply wf_exp_eq_trans.
    + exact (convert_equality _ _ _ _ _ _ ESn HTF EFarg).
    + exact (convert_equality _ _ _ _ _ _ ESβ HTF
        (wf_exp_eq_trans _ _ _ _ _ ELift (wf_exp_eq_sym _ _ _ _ EBody'))).
Qed.

Local Lemma pair_beta_under_iterated_weakening Γ Δ Θ σ τ A B M N i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Θ ⊢s τ : Δ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  {{ Γ ⊢ N : B[Id,,M] }} ->
  let P := a_sub (a_sub (a_pair M A N B) σ) τ in
  wf_exp Θ (a_sub A (a_compose σ τ)) (a_fst P) /\
  wf_exp_eq Θ (a_sub A (a_compose σ τ)) (a_fst P) (a_sub M (a_compose σ τ)) /\
  wf_exp Θ (a_sub B (a_extend (a_compose σ τ) (a_fst P))) (a_snd P) /\
  wf_exp_eq Θ (a_sub B (a_extend (a_compose σ τ) (a_fst P))) (a_snd P) (a_sub N (a_compose σ τ)).
Proof.
  intros Hσ Hτ HA HB HM HN P.
  pose proof (wf_pair _ _ _ _ _ _ HA HB HM HN) as HP.
  pose proof (wf_sub_compose _ _ _ _ _ Hτ Hσ) as HS.
  destruct (pair_projections_under_iterated_weakening _ _ _ _ _ _ _ _ _
    Hσ Hτ HA HB HP) as (HF & EF & HSnd & ESn).
  destruct (substituted_pair_beta _ _ _ _ _ _ _ _ HS HA HB HM HN) as (_ & EFβ & _ & ESβ).
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HF) as HSF.
  pose proof (type_substitution _ _ _ _ _ HSF HB) as HBS.
  pose proof (wf_sub_eq_extend_cong _ _ _ _ _ _ _ _
    (substitution_equality_reflexive _ _ _ HS) HA EF) as ESub.
  pose proof (type_substitution_equality_same_body _ _ _ _ _ _ HSF ESub HB) as ET.
  repeat split; try assumption.
  - exact (wf_exp_eq_trans _ _ _ _ _ EF EFβ).
  - exact (wf_exp_eq_trans _ _ _ _ _ ESn
      (convert_equality _ _ _ _ _ _ ESβ HBS (wf_exp_eq_sym _ _ _ _ ET))).
Qed.

(* The lifted substitution for a natural-number binder uses the
   judgmental equality between substituted and unsubstituted naturals. *)

Local Lemma lift_natural_substitution Γ Δ σ :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ, ℕ ⊢s q σ : Γ, ℕ }}.
Proof.
  intro Hσ.
  pose proof (wf_nat Γ (substitution_target _ _ _ Hσ)) as HN.
  pose proof (wf_nat Δ (substitution_source _ _ _ Hσ)) as HND.
  pose proof (type_substitution _ _ _ _ _ Hσ HN) as HNs.
  pose proof (wf_exp_eq_nat_sub _ _ _ Hσ) as EN.
  pose proof (wf_ctx_extend Δ 0 a_nat (substitution_source _ _ _ Hσ) HND) as HΔ.
  exact (proj1 (proj2 (proj2 narrowing)) _ _ _
    (lifted_substitution _ _ _ _ _ Hσ HN) _ HΔ
    (declaration_change_context _ _ _ _ HNs HND EN)).
Qed.

Local Lemma natural_argument_substitution Γ Δ σ N :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ ⊢ N : ℕ }} ->
  {{ Δ ⊢s σ,,N : Γ, ℕ }}.
Proof.
  intros Hσ HN.
  pose proof (wf_nat Γ (substitution_target _ _ _ Hσ)) as HT.
  eapply wf_sub_extend; [exact Hσ | exact HT |].
  exact (convert_term _ _ _ _ _ HN
    (type_substitution _ _ _ _ _ Hσ HT)
    (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ Hσ))).
Qed.

Local Lemma lift_natural_at_argument Γ Δ Θ σ τ N :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Θ ⊢s τ : Δ }} ->
  {{ Θ ⊢ N : ℕ }} ->
  {{ Θ ⊢s (q σ)∘(τ,,N) ≈ (σ∘τ),,N : Γ, ℕ }}.
Proof.
  intros Hσ Hτ HN.
  pose proof (wf_nat Γ (substitution_target _ _ _ Hσ)) as HT.
  pose proof (type_substitution _ _ _ _ _ Hσ HT) as HTσ.
  pose proof (type_substitution _ _ _ _ _ Hτ HTσ) as HTστ.
  pose proof (type_substitution_congruence _ _ _ _ _ _ _ Hτ
    (substitution_equality_reflexive _ _ _ Hτ) (wf_exp_eq_nat_sub _ _ _ Hσ)) as E.
  pose proof (wf_exp_eq_trans _ _ _ _ _ E (wf_exp_eq_nat_sub _ _ _ Hτ)) as EN.
  exact (lifted_substitution_at_argument _ _ _ _ _ _ _ _ Hσ Hτ HT
    (convert_term _ _ _ _ _ HN HTστ (wf_exp_eq_sym _ _ _ _ EN))).
Qed.

Local Lemma natural_type_lift_at_argument Γ Δ Θ σ τ A N i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Θ ⊢s τ : Δ }} ->
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Θ ⊢ N : ℕ }} ->
  {{ Θ ⊢ A[q σ][τ,,N] ≈ A[σ∘τ,,N] : Type@i }}.
Proof.
  intros Hσ Hτ HA HN.
  pose proof (lift_natural_substitution _ _ _ Hσ) as HQ.
  pose proof (natural_argument_substitution _ _ _ _ Hτ HN) as HτN.
  pose proof (wf_sub_compose _ _ _ _ _ HτN HQ) as HC.
  eapply wf_exp_eq_trans.
  - exact (wf_exp_eq_sym _ _ _ _
      (type_substitution_composition _ _ _ _ _ _ _ HτN HQ HA)).
  - exact (type_substitution_equality_same_body _ _ _ _ _ _ HC
      (lift_natural_at_argument _ _ _ _ _ _ Hσ Hτ HN) HA).
Qed.

Local Lemma natural_substituted_zero_type Γ Δ σ A i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Δ ⊢ A[Id,,zero][σ] ≈ A[q σ][Id,,zero] : Type@i }}.
Proof.
  intros Hσ HA.
  pose proof (substitution_source _ _ _ Hσ) as HΔ.
  pose proof (substitution_target _ _ _ Hσ) as HΓ.
  pose proof (wf_zero Δ HΔ) as H0.
  pose proof (wf_sub_id Δ HΔ) as HI.
  pose proof (natural_type_lift_at_argument _ _ _ _ _ _ _ _ Hσ HI HA H0) as Elift.
  pose proof (wf_nat Γ HΓ) as HN.
  pose proof (wf_zero Γ HΓ) as HZ0.
  pose proof (type_argument_substitution_composition _ _ _ _ _ _ _ _ Hσ HN HA HZ0) as Earg.
  pose proof (wf_sub_eq_sym _ _ _ _ (wf_sub_eq_id_compose_left _ _ _ Hσ)) as Ebase.
  pose proof (wf_sub_eq_extend_cong _ _ _ _ _ _ _ _ Ebase HN
    (convert_equality _ _ _ _ _ _ (wf_exp_eq_zero_sub _ _ _ Hσ)
      (type_substitution _ _ _ _ _ Hσ HN)
      (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ Hσ)))) as Eargs.
  pose proof (natural_argument_substitution _ _ _ _ Hσ
    (convert_term _ _ _ _ _ (wf_exp_sub _ _ _ _ _ Hσ HZ0) (wf_nat Δ HΔ)
      (wf_exp_eq_nat_sub _ _ _ Hσ))) as Hargs.
  pose proof (type_substitution_equality_same_body _ _ _ _ _ _ Hargs Eargs HA) as E.
  exact (wf_exp_eq_trans _ _ _ _ _ Earg
    (wf_exp_eq_trans _ _ _ _ _ E (wf_exp_eq_sym _ _ _ _ Elift))).
Qed.

Local Lemma natural_substituted_zero_case Γ Δ σ A MZ i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Γ ⊢ MZ : A[Id,,zero] }} ->
  {{ Δ ⊢ MZ[σ] : A[q σ][Id,,zero] }}.
Proof.
  intros HS HA HZ.
  pose proof (type_substitution _ _ _ _ _ (lift_natural_substitution _ _ _ HS) HA) as HA'.
  pose proof (substitution_source _ _ _ HS) as HΔ.
  eapply convert_term.
  - exact (wf_exp_sub _ _ _ _ _ HS HZ).
  - exact (type_substitution _ _ _ _ _ (nat_case_substitution _ _ (wf_zero _ HΔ)) HA').
  - exact (natural_substituted_zero_type _ _ _ _ _ HS HA).
Qed.

Local Lemma natural_term_from_substituted_type Γ Δ σ M :
  {{ Γ ⊢s σ : Δ }} ->
  {{ Γ ⊢ M : ℕ[σ] }} ->
  {{ Γ ⊢ M : ℕ }}.
Proof.
  intros HS HM.
  exact (convert_term _ _ _ _ _ HM (wf_nat _ (substitution_source _ _ _ HS))
    (wf_exp_eq_nat_sub _ _ _ HS)).
Qed.

Local Lemma natural_equality_from_substituted_type Γ Δ σ M N :
  {{ Γ ⊢s σ : Δ }} ->
  {{ Γ ⊢ M ≈ N : ℕ[σ] }} ->
  {{ Γ ⊢ M ≈ N : ℕ }}.
Proof.
  intros HS HE.
  exact (convert_equality _ _ _ _ _ _ HE (wf_nat _ (substitution_source _ _ _ HS))
    (wf_exp_eq_nat_sub _ _ _ HS)).
Qed.

Local Lemma lift_natural_head Γ Δ σ :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ, ℕ ⊢ #0[q σ] ≈ #0 : ℕ }}.
Proof.
  intros HS.
  pose proof (lift_natural_substitution _ _ _ HS) as HQ.
  pose proof (substitution_source _ _ _ HQ) as HD.
  pose proof (wf_sub_weaken _ _ HD) as HW.
  pose proof (wf_sub_compose _ _ _ _ _ HW HS) as HT.
  pose proof (wf_nat Γ (substitution_target _ _ _ HS)) as HNat.
  assert (Hv : {{ Δ, ℕ ⊢ #0 : ℕ }})
    by (eapply natural_term_from_substituted_type; [exact HW | apply wf_vlookup; [exact HD | constructor]]).
  pose proof (convert_term _ _ _ _ _ Hv (type_substitution _ _ _ _ _ HT HNat)
    (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HT))) as Hv'.
  eapply natural_equality_from_substituted_type; [exact HT |].
  exact (wf_exp_eq_var_0_sub _ _ _ _ _ _ HT HNat Hv').
Qed.

Local Lemma lift_natural_tail Γ Δ σ :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ, ℕ ⊢s Wk∘q σ ≈ σ∘Wk : Γ }}.
Proof.
  intro HS.
  pose proof (lift_natural_substitution _ _ _ HS) as HQ.
  pose proof (substitution_source _ _ _ HQ) as HD.
  pose proof (wf_sub_weaken _ _ HD) as HW.
  pose proof (wf_sub_compose _ _ _ _ _ HW HS) as HT.
  pose proof (wf_nat Γ (substitution_target _ _ _ HS)) as HNat.
  assert (Hv : {{ Δ, ℕ ⊢ #0 : ℕ }})
    by (eapply natural_term_from_substituted_type; [exact HW | apply wf_vlookup; [exact HD | constructor]]).
  pose proof (convert_term _ _ _ _ _ Hv (type_substitution _ _ _ _ _ HT HNat)
    (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HT))) as Hv'.
  exact (wf_sub_eq_p_extend _ _ _ _ _ _ HT HNat Hv').
Qed.

Local Definition natural_step_substitution :=
  a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)).

Local Lemma natural_variable_one Γ A i :
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Γ, ℕ, A ⊢ #1 : ℕ }}.
Proof.
  intro HA.
  pose proof (typing_context _ _ _ HA) as HΓN.
  pose proof (wf_ctx_extend _ _ _ HΓN HA) as HC.
  pose proof (wf_sub_weaken _ _ HΓN) as H1.
  pose proof (wf_sub_weaken _ _ HC) as H2.
  pose proof (wf_sub_compose _ _ _ _ _ H2 H1) as HW.
  pose proof (wf_nat Γ (substitution_target _ _ _ H1)) as HN.
  pose proof (type_substitution_composition _ _ _ _ _ _ _ H2 H1 HN) as E.
  eapply natural_term_from_substituted_type; [exact HW |].
  eapply convert_term.
  - apply wf_vlookup; [exact HC | apply there, here].
  - exact (type_substitution _ _ _ _ _ HW HN).
  - exact (wf_exp_eq_sym _ _ _ _ E).
Qed.

Local Lemma lifted_substitution_tail Γ Δ σ A i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Δ, A[σ] ⊢s Wk∘q σ ≈ σ∘Wk : Γ }}.
Proof.
  intros HS HA.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (wf_sub_weaken _ _ (substitution_source _ _ _ HQ)) as HW.
  exact (wf_sub_eq_p_extend _ _ _ _ _ _
    (wf_sub_compose _ _ _ _ _ HW HS) HA
    (last_variable_after_lifting _ _ _ _ _ HS HA)).
Qed.

Local Lemma natural_step_lift_tail Γ Δ σ A i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Δ, ℕ, A[q σ] ⊢s (Wk∘Wk)∘q (q σ) ≈ σ∘(Wk∘Wk) : Γ }}.
Proof.
  intros HS HA.
  pose proof (lift_natural_substitution _ _ _ HS) as HQ.
  pose proof (lifted_substitution _ _ _ _ _ HQ HA) as HQQ.
  pose proof (wf_sub_weaken _ _ (substitution_target _ _ _ HQ)) as H1.
  pose proof (wf_sub_weaken _ _ (substitution_target _ _ _ HQQ)) as H2.
  pose proof (wf_sub_weaken _ _ (substitution_source _ _ _ HQ)) as H3.
  pose proof (wf_sub_weaken _ _ (substitution_source _ _ _ HQQ)) as H4.
  eapply wf_sub_eq_trans.
  - exact (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ H1 H2 HQQ).
  - eapply wf_sub_eq_trans.
    + exact (wf_sub_eq_compose_cong _ _ _ _ _ _ _
        (lifted_substitution_tail _ _ _ _ _ HQ HA) (substitution_equality_reflexive _ _ _ H1)).
    + eapply wf_sub_eq_trans.
      * exact (wf_sub_eq_sym _ _ _ _ (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ H1 HQ H4)).
      * eapply wf_sub_eq_trans.
        -- exact (wf_sub_eq_compose_cong _ _ _ _ _ _ _
             (substitution_equality_reflexive _ _ _ H4) (lift_natural_tail _ _ _ HS)).
        -- exact (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ HS H3 H4).
Qed.

Local Lemma natural_step_lift_variable Γ Δ σ A i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Δ, ℕ, A[q σ] ⊢ #1[q (q σ)] ≈ #1 : ℕ }}.
Proof.
  intros HS HA.
  pose proof (lift_natural_substitution _ _ _ HS) as HQ.
  pose proof (lifted_substitution _ _ _ _ _ HQ HA) as HQQ.
  pose proof (wf_sub_weaken _ _ (substitution_target _ _ _ HQ)) as H1.
  pose proof (wf_sub_weaken _ _ (substitution_source _ _ _ HQ)) as H3.
  pose proof (wf_sub_weaken _ _ (substitution_source _ _ _ HQQ)) as H4.
  pose proof (wf_sub_compose _ _ _ _ _ H4 HQ) as HT.
  pose proof (wf_sub_compose _ _ _ _ _ HT H1) as HU.
  pose proof (wf_nat Γ (substitution_target _ _ _ HS)) as HN.
  pose proof (wf_nat _ (substitution_source _ _ _ HQQ)) as HN'.
  pose proof (wf_vlookup _ _ _ (substitution_target _ _ _ HQ) (here a_nat Γ)) as HV.
  eapply wf_exp_eq_trans.
  - eapply convert_equality.
    + exact (wf_exp_eq_var_S_sub _ _ _ _ _ _ _ _ HT HA
        (last_variable_after_lifting _ _ _ _ _ HQ HA) (here a_nat Γ)).
    + exact HN'.
    + eapply wf_exp_eq_trans.
      * exact (wf_exp_eq_sym _ _ _ _
          (type_substitution_composition _ _ _ _ _ _ _ HT H1 HN)).
      * exact (wf_exp_eq_nat_sub _ _ _ HU).
  - eapply wf_exp_eq_trans.
    + eapply convert_equality.
      * exact (wf_exp_eq_sub_compose _ _ _ _ _ _ _ H4 HQ HV).
      * exact HN'.
      * eapply wf_exp_eq_trans.
        -- exact (wf_exp_eq_sym _ _ _ _
             (type_substitution_composition _ _ _ _ _ _ _ HT H1 HN)).
        -- exact (wf_exp_eq_nat_sub _ _ _ HU).
    + eapply wf_exp_eq_trans.
      * exact (natural_equality_from_substituted_type _ _ _ _ _ H4
          (equality_under_substitution _ _ _ _ _ _ H4 (lift_natural_head _ _ _ HS))).
      * eapply convert_equality.
        -- apply wf_exp_eq_var_weaken; [exact (substitution_source _ _ _ HQQ) | apply here].
        -- exact HN'.
        -- eapply wf_exp_eq_trans.
           ++ exact (wf_exp_eq_sym _ _ _ _
                (type_substitution_composition _ _ _ _ _ _ _ H4 H3
                  (wf_nat Δ (substitution_source _ _ _ HS)))).
           ++ exact (wf_exp_eq_nat_sub _ _ _ (wf_sub_compose _ _ _ _ _ H4 H3)).
Qed.

Local Lemma natural_step_lift_composition Γ Δ σ A i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Δ, ℕ, A[q σ] ⊢s ^natural_step_substitution∘q (q σ)
    ≈ (q σ)∘^natural_step_substitution : Γ, ℕ }}.
Proof.
  intros HS HA.
  pose proof (lift_natural_substitution _ _ _ HS) as HQ.
  pose proof (type_substitution _ _ _ _ _ HQ HA) as HA'.
  pose proof (lifted_substitution _ _ _ _ _ HQ HA) as HQQ.
  pose proof (wf_sub_weaken _ _ (substitution_target _ _ _ HQ)) as H1.
  pose proof (wf_sub_weaken _ _ (substitution_target _ _ _ HQQ)) as H2.
  pose proof (wf_sub_weaken _ _ (substitution_source _ _ _ HQ)) as H3.
  pose proof (wf_sub_weaken _ _ (substitution_source _ _ _ HQQ)) as H4.
  pose proof (wf_sub_compose _ _ _ _ _ H2 H1) as H12.
  pose proof (wf_sub_compose _ _ _ _ _ H4 H3) as H34.
  pose proof (wf_sub_compose _ _ _ _ _ HQQ H12) as HT.
  pose proof (wf_nat Γ (substitution_target _ _ _ HS)) as HN.
  pose proof (natural_variable_one _ _ _ HA) as HV.
  pose proof (wf_succ _ _ HV) as HVs.
  pose proof (convert_term _ _ _ _ _ HVs (type_substitution _ _ _ _ _ H12 HN)
    (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ H12))) as HVs'.
  unfold natural_step_substitution.
  eapply wf_sub_eq_trans.
  - exact (wf_sub_eq_extend_compose _ _ _ _ _ _ _ _ H12 HN HVs' HQQ).
  - eapply wf_sub_eq_trans.
    + eapply wf_sub_eq_extend_cong.
      * exact (natural_step_lift_tail _ _ _ _ _ HS HA).
      * exact HN.
      * eapply convert_equality.
        -- exact (wf_exp_eq_trans _ _ _ _ _
             (wf_exp_eq_succ_sub _ _ _ _ HQQ HV)
             (wf_exp_eq_succ_cong _ _ _ (natural_step_lift_variable _ _ _ _ _ HS HA))).
        -- exact (type_substitution _ _ _ _ _ HT HN).
        -- exact (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HT)).
    + exact (wf_sub_eq_sym _ _ _ _ (lift_natural_at_argument _ _ _ _ _ _
        HS H34 (wf_succ _ _ (natural_variable_one _ _ _ HA')))).
Qed.

Local Lemma natural_substituted_step_type Γ Δ σ A i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Δ, ℕ, A[q σ] ⊢ A[Wk∘Wk,,succ #1][q (q σ)] ≈ A[q σ][Wk∘Wk,,succ #1] : Type@i }}.
Proof.
  intros HS HA.
  pose proof (lift_natural_substitution _ _ _ HS) as HQ.
  pose proof (type_substitution _ _ _ _ _ HQ HA) as HA'.
  pose proof (lifted_substitution _ _ _ _ _ HQ HA) as HQQ.
  pose proof (step_case_substitution _ _ _ HA) as HT.
  pose proof (step_case_substitution _ _ _ HA') as HT'.
  pose proof (type_substitution_composition _ _ _ _ _ _ _ HQQ HT HA) as E1.
  pose proof (type_substitution_composition _ _ _ _ _ _ _ HT' HQ HA) as E2.
  pose proof (type_substitution_equality_same_body _ _ _ _ _ _
    (wf_sub_compose _ _ _ _ _ HQQ HT) (natural_step_lift_composition _ _ _ _ _ HS HA) HA) as E.
  exact (wf_exp_eq_trans _ _ _ _ _ (wf_exp_eq_sym _ _ _ _ E1) (wf_exp_eq_trans _ _ _ _ _ E E2)).
Qed.

Local Lemma natural_substituted_step_case Γ Δ σ A MS i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
  {{ Δ, ℕ, A[q σ] ⊢ MS[q (q σ)] : A[q σ][Wk∘Wk,,succ #1] }}.
Proof.
  intros HS HA HM.
  pose proof (lift_natural_substitution _ _ _ HS) as HQ.
  pose proof (type_substitution _ _ _ _ _ HQ HA) as HA'.
  eapply convert_term.
  - exact (wf_exp_sub _ _ _ _ _ (lifted_substitution _ _ _ _ _ HQ HA) HM).
  - exact (type_substitution _ _ _ _ _ (step_case_substitution _ _ _ HA') HA').
  - exact (natural_substituted_step_type _ _ _ _ _ HS HA).
Qed.

Local Lemma natural_argument_equality Γ Δ σ τ N N' :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ ⊢s σ ≈ τ : Γ }} ->
  {{ Δ ⊢ N ≈ N' : ℕ }} ->
  {{ Δ ⊢s σ,,N ≈ τ,,N' : Γ, ℕ }}.
Proof.
  intros HS E EN.
  pose proof (wf_nat Γ (substitution_target _ _ _ HS)) as HN.
  eapply wf_sub_eq_extend_cong; [exact E | exact HN |].
  exact (convert_equality _ _ _ _ _ _ EN (type_substitution _ _ _ _ _ HS HN)
    (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS))).
Qed.

Local Lemma natural_motive_instance Γ Δ σ A N i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Δ ⊢ N : ℕ }} ->
  {{ Δ ⊢ A[q σ][Id,,N] ≈ A[σ,,N] : Type@i }}.
Proof.
  intros HS HA HN.
  pose proof (wf_sub_id Δ (substitution_source _ _ _ HS)) as HI.
  pose proof (wf_sub_compose _ _ _ _ _ HI HS) as Hc.
  eapply wf_exp_eq_trans.
  - exact (natural_type_lift_at_argument _ _ _ _ _ _ _ _ HS HI HA HN).
  - eapply type_substitution_equality_same_body; [exact (natural_argument_substitution _ _ _ _ Hc HN) | | exact HA].
    eapply natural_argument_equality.
    + exact Hc.
    + exact (wf_sub_eq_id_compose_left _ _ _ HS).
    + exact (expression_equality_reflexive _ _ _ HN).
Qed.

Local Lemma cancel_two_substitution_extensions Γ Δ σ A B M N i j :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@j }} ->
  {{ Δ ⊢ M : A[σ] }} ->
  {{ Δ ⊢ N : B[σ,,M] }} ->
  {{ Δ ⊢s (Wk∘Wk)∘(σ,,M,,N) ≈ σ : Γ }}.
Proof.
  intros HS HA HB HM HN.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HM) as HSM.
  pose proof (wf_sub_extend _ _ _ _ _ _ HSM HB HN) as HSMN.
  pose proof (wf_sub_weaken _ _ (substitution_target _ _ _ HSM)) as H1.
  pose proof (wf_sub_weaken _ _ (substitution_target _ _ _ HSMN)) as H2.
  eapply wf_sub_eq_trans.
  - exact (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ H1 H2 HSMN).
  - eapply wf_sub_eq_trans.
    + exact (wf_sub_eq_compose_cong _ _ _ _ _ _ _ (wf_sub_eq_p_extend _ _ _ _ _ _ HSM HB HN)
        (substitution_equality_reflexive _ _ _ H1)).
    + exact (wf_sub_eq_p_extend _ _ _ _ _ _ HS HA HM).
Qed.

Local Lemma natural_step_at_argument Γ Δ σ A N R i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Δ ⊢ N : ℕ }} ->
  {{ Δ ⊢ R : A[σ,,N] }} ->
  {{ Δ ⊢s ^natural_step_substitution∘(σ,,N,,R) ≈ σ,,succ N : Γ, ℕ }}.
Proof.
  intros HS HA HN HR.
  pose proof (wf_nat Γ (substitution_target _ _ _ HS)) as HNat.
  pose proof (wf_nat Δ (substitution_source _ _ _ HS)) as HNat'.
  pose proof (convert_term _ _ _ _ _ HN (type_substitution _ _ _ _ _ HS HNat)
    (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS))) as HN'.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HNat HN') as HSN.
  pose proof (wf_sub_extend _ _ _ _ _ _ HSN HA HR) as HSNR.
  pose proof (wf_sub_weaken _ _ (substitution_target _ _ _ HSN)) as HW1.
  pose proof (wf_sub_weaken _ _ (substitution_target _ _ _ HSNR)) as HW2.
  pose proof (wf_sub_compose _ _ _ _ _ HW2 HW1) as HW.
  pose proof (wf_sub_compose _ _ _ _ _ HSNR HW) as Ht.
  pose proof (wf_succ _ _ (natural_variable_one _ _ _ HA)) as Hs.
  pose proof (convert_term _ _ _ _ _ Hs (type_substitution _ _ _ _ _ HW HNat)
    (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HW))) as Hs'.
  assert (E1 : {{ Δ ⊢ #1[σ,,N,,R] ≈ N : ℕ }}).
  {
    eapply wf_exp_eq_trans.
    - eapply convert_equality.
      + exact (wf_exp_eq_var_S_sub _ _ _ _ _ _ _ _ HSN HA HR (here a_nat Γ)).
      + exact HNat'.
      + eapply wf_exp_eq_trans.
        * exact (type_weakening_cancel _ _ _ _ _ _ _ _ HS HNat HN' HNat).
        * exact (wf_exp_eq_nat_sub _ _ _ HS).
    - exact (natural_equality_from_substituted_type _ _ _ _ _ HS
        (wf_exp_eq_var_0_sub _ _ _ _ _ _ HS HNat HN')).
  }
  unfold natural_step_substitution.
  eapply wf_sub_eq_trans.
  - exact (wf_sub_eq_extend_compose _ _ _ _ _ _ _ _ HW HNat Hs' HSNR).
  - eapply natural_argument_equality; [exact Ht | |].
    + exact (cancel_two_substitution_extensions _ _ _ _ _ _ _ _ _ HS HNat HA HN' HR).
    + exact (wf_exp_eq_trans _ _ _ _ _
        (wf_exp_eq_succ_sub _ _ _ _ HSNR (natural_variable_one _ _ _ HA))
        (wf_exp_eq_succ_cong _ _ _ E1)).
Qed.

Local Lemma natural_step_type_at_argument Γ Δ σ A N R i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Δ ⊢ N : ℕ }} ->
  {{ Δ ⊢ R : A[σ,,N] }} ->
  {{ Δ ⊢ A[^natural_step_substitution][σ,,N,,R] ≈ A[σ,,succ N] : Type@i }}.
Proof.
  intros HS HA HN HR.
  pose proof (wf_sub_extend _ _ _ _ _ _ (natural_argument_substitution _ _ _ _ HS HN) HA HR) as HT.
  pose proof (step_case_substitution _ _ _ HA) as HStep.
  eapply wf_exp_eq_trans.
  - exact (wf_exp_eq_sym _ _ _ _
      (type_substitution_composition _ _ _ _ _ _ _ HT HStep HA)).
  - exact (type_substitution_equality_same_body _ _ _ _ _ _
      (wf_sub_compose _ _ _ _ _ HT HStep) (natural_step_at_argument _ _ _ _ _ _ _ HS HA HN HR) HA).
Qed.

Local Lemma natural_lift_at_identity Γ Δ σ N :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Δ ⊢ N : ℕ }} ->
  {{ Δ ⊢s (q σ)∘(Id,,N) ≈ σ,,N : Γ, ℕ }}.
Proof.
  intros HS HN.
  pose proof (wf_sub_id Δ (substitution_source _ _ _ HS)) as HI.
  pose proof (wf_sub_compose _ _ _ _ _ HI HS) as HC.
  eapply wf_sub_eq_trans.
  - exact (lift_natural_at_argument _ _ _ _ _ _ HS HI HN).
  - apply natural_argument_equality; [exact HC | exact (wf_sub_eq_id_compose_left _ _ _ HS) |].
    exact (expression_equality_reflexive _ _ _ HN).
Qed.

Local Lemma natural_step_lift_at_identity Γ Δ σ A N R i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Δ ⊢ N : ℕ }} ->
  {{ Δ ⊢ R : A[q σ][Id,,N] }} ->
  {{ Δ ⊢s q (q σ)∘(Id,,N,,R) ≈ σ,,N,,R : Γ, ℕ, A }}.
Proof.
  intros HS HA HN HR.
  pose proof (wf_sub_id Δ (substitution_source _ _ _ HS)) as HI.
  pose proof (natural_argument_substitution _ _ _ _ HI HN) as HIN.
  pose proof (lift_natural_substitution _ _ _ HS) as HQ.
  pose proof (wf_sub_compose _ _ _ _ _ HIN HQ) as HCI.
  pose proof (type_substitution_composition _ _ _ _ _ _ _ HIN HQ HA) as EC.
  pose proof (type_substitution _ _ _ _ _ HCI HA) as HC.
  pose proof (convert_term _ _ _ _ _ HR HC (wf_exp_eq_sym _ _ _ _ EC)) as HR'.
  eapply wf_sub_eq_trans.
  - exact (lifted_substitution_at_argument _ _ _ _ _ _ _ _ HQ HIN HA HR).
  - eapply wf_sub_eq_extend_cong.
    + exact (natural_lift_at_identity _ _ _ _ HS HN).
    + exact HA.
    + exact (expression_equality_reflexive _ _ _ HR').
Qed.

Local Lemma substitution_composition_reindex Γ Δ Θ σ τ ν A M i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Θ ⊢s τ : Δ }} ->
  {{ Θ ⊢s ν : Γ }} ->
  {{ Θ ⊢s σ∘τ ≈ ν : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  {{ Θ ⊢ M[σ][τ] ≈ M[ν] : A[ν] }}.
Proof.
  intros HS HT HN ES HA HM.
  pose proof (type_substitution _ _ _ _ _ HN HA) as HAn.
  pose proof (type_substitution_equality_same_body _ _ _ _ _ _
    (wf_sub_compose _ _ _ _ _ HT HS) ES HA) as EA.
  eapply wf_exp_eq_trans.
  - exact (convert_equality _ _ _ _ _ _
      (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_sub_compose _ _ _ _ _ _ _ HT HS HM)) HAn EA).
  - exact (convert_equality _ _ _ _ _ _
      (wf_exp_eq_sub_cong _ _ _ _ _ _ _
        (expression_equality_reflexive _ _ _ HM) ES) HAn EA).
Qed.

Local Definition natural_recursion_at σ A MZ MS N :=
  a_natrec (a_sub A (Syntax.q σ)) (a_sub MZ σ)
    (a_sub MS (Syntax.q (Syntax.q σ))) N.

Local Lemma natural_recursion_at_typing Γ Δ σ A MZ MS N i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Γ ⊢ MZ : A[Id,,zero] }} ->
  {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
  {{ Δ ⊢ N : ℕ }} ->
  wf_exp Δ (a_sub A (a_extend σ N)) (natural_recursion_at σ A MZ MS N).
Proof.
  intros HS HA HZ HStep HN.
  pose proof (type_substitution _ _ _ _ _ (lift_natural_substitution _ _ _ HS) HA) as HA'.
  pose proof (natural_substituted_zero_case _ _ _ _ _ _ HS HA HZ) as HZ'.
  pose proof (natural_substituted_step_case _ _ _ _ _ _ HS HA HStep) as HStep'.
  eapply convert_term.
  - exact (wf_natrec _ _ _ _ _ _ HA' HZ' HStep' HN).
  - exact (type_substitution _ _ _ _ _ (natural_argument_substitution _ _ _ _ HS HN) HA).
  - exact (natural_motive_instance _ _ _ _ _ _ HS HA HN).
Qed.

Local Lemma natural_recursion_at_argument_congruence Γ Δ σ A MZ MS N N' i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Γ ⊢ MZ : A[Id,,zero] }} ->
  {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
  {{ Δ ⊢ N : ℕ }} ->
  {{ Δ ⊢ N ≈ N' : ℕ }} ->
  wf_exp_eq Δ (a_sub A (a_extend σ N))
    (natural_recursion_at σ A MZ MS N) (natural_recursion_at σ A MZ MS N').
Proof.
  intros HS HA HZ HStep HN EN.
  pose proof (type_substitution _ _ _ _ _ (lift_natural_substitution _ _ _ HS) HA) as HA'.
  pose proof (natural_substituted_zero_case _ _ _ _ _ _ HS HA HZ) as HZ'.
  pose proof (natural_substituted_step_case _ _ _ _ _ _ HS HA HStep) as HStep'.
  eapply convert_equality.
  - exact (wf_exp_eq_natrec_cong _ _ _ _ _ _ _ _ _ _ HA'
      (expression_equality_reflexive _ _ _ HA')
      (expression_equality_reflexive _ _ _ HZ') (expression_equality_reflexive _ _ _ HStep') EN).
  - exact (type_substitution _ _ _ _ _ (natural_argument_substitution _ _ _ _ HS HN) HA).
  - exact (natural_motive_instance _ _ _ _ _ _ HS HA HN).
Qed.

Local Lemma natural_recursion_at_zero Γ Δ σ A MZ MS i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Γ ⊢ MZ : A[Id,,zero] }} ->
  {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
  wf_exp_eq Δ (a_sub A (a_extend σ a_zero))
    (natural_recursion_at σ A MZ MS a_zero) (a_sub MZ σ).
Proof.
  intros HS HA HZ HStep.
  pose proof (wf_zero Δ (substitution_source _ _ _ HS)) as H0.
  pose proof (type_substitution _ _ _ _ _ (lift_natural_substitution _ _ _ HS) HA) as HA'.
  eapply convert_equality.
  - exact (wf_exp_eq_nat_beta_zero _ _ _ _ _ HA'
      (natural_substituted_zero_case _ _ _ _ _ _ HS HA HZ)
      (natural_substituted_step_case _ _ _ _ _ _ HS HA HStep)).
  - exact (type_substitution _ _ _ _ _ (natural_argument_substitution _ _ _ _ HS H0) HA).
  - exact (natural_motive_instance _ _ _ _ _ _ HS HA H0).
Qed.

Local Lemma natural_recursion_at_successor Γ Δ σ A MZ MS N i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Γ ⊢ MZ : A[Id,,zero] }} ->
  {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
  {{ Δ ⊢ N : ℕ }} ->
  let R := natural_recursion_at σ A MZ MS N in
  wf_exp_eq Δ (a_sub A (a_extend σ (a_succ N)))
    (natural_recursion_at σ A MZ MS (a_succ N)) (a_sub MS (a_extend (a_extend σ N) R)).
Proof.
  intros HS HA HZ HStep HN R.
  pose proof (lift_natural_substitution _ _ _ HS) as HQ.
  pose proof (type_substitution _ _ _ _ _ HQ HA) as HA'.
  pose proof (natural_substituted_zero_case _ _ _ _ _ _ HS HA HZ) as HZ'.
  pose proof (natural_substituted_step_case _ _ _ _ _ _ HS HA HStep) as HStep'.
  pose proof (wf_natrec _ _ _ _ _ _ HA' HZ' HStep' HN) as HR0.
  change {{ Δ ⊢ R : A[q σ][Id,,N] }} in HR0.
  pose proof (natural_recursion_at_typing _ _ _ _ _ _ _ _ HS HA HZ HStep HN) as HR.
  change {{ Δ ⊢ R : A[σ,,N] }} in HR.
  pose proof (natural_argument_substitution _ _ _ _
    (wf_sub_id Δ (substitution_source _ _ _ HS)) HN) as HIN.
  pose proof (wf_sub_extend _ _ _ _ _ _ HIN HA' HR0) as HINR.
  pose proof (natural_argument_substitution _ _ _ _ HS HN) as HSN.
  pose proof (wf_sub_extend _ _ _ _ _ _ HSN HA HR) as HSNR.
  pose proof (wf_succ _ _ HN) as Hs.
  pose proof (type_substitution _ _ _ _ _ (natural_argument_substitution _ _ _ _ HS Hs) HA) as HB.
  pose proof (natural_step_lift_at_identity _ _ _ _ _ _ _ HS HA HN HR0) as ES.
  eapply wf_exp_eq_trans.
  - exact (convert_equality _ _ _ _ _ _
      (wf_exp_eq_nat_beta_succ _ _ _ _ _ _ HA' HZ' HStep' HN) HB
      (natural_motive_instance _ _ _ _ _ _ HS HA Hs)).
  - eapply convert_equality; [| exact HB | exact (natural_step_type_at_argument _ _ _ _ _ _ _ HS HA HN HR)].
    eapply substitution_composition_reindex.
    + exact (lifted_substitution _ _ _ _ _ HQ HA).
    + exact HINR.
    + exact HSNR.
    + exact ES.
    + exact (type_substitution _ _ _ _ _ (step_case_substitution _ _ _ HA) HA).
    + exact HStep.
Qed.

Local Lemma weakening_of_last_binder Γ A i :
  {{ Γ ⊢ A : Type@i }} ->
  weakening_between Γ (A :: Γ) a_weaken.
Proof.
  intro HA.
  pose proof (typing_context _ _ _ HA) as HΓ.
  exists (a_compose a_id a_weaken).
  split; [exact (context_weakening_step _ _ _ _ _ (context_weakening_id _ HΓ) HA) |].
  pose proof (wf_sub_weaken _ _ (wf_ctx_extend _ _ _ HΓ HA)) as HW.
  split; [exact HW | apply wf_sub_eq_sym, wf_sub_eq_id_compose_right; exact HW].
Qed.

Local Lemma lifted_substitution_head Γ Δ σ A i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Δ, A[σ] ⊢ #0[q σ] ≈ #0 : A[σ][Wk] }}.
Proof.
  intros HS HA.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (wf_sub_weaken _ _ (substitution_source _ _ _ HQ)) as HW.
  pose proof (wf_sub_compose _ _ _ _ _ HW HS) as HST.
  eapply convert_equality.
  - exact (wf_exp_eq_var_0_sub _ _ _ _ _ _ HST HA
      (last_variable_after_lifting _ _ _ _ _ HS HA)).
  - exact (type_substitution _ _ _ _ _ HW (type_substitution _ _ _ _ _ HS HA)).
  - exact (type_substitution_composition _ _ _ _ _ _ _ HW HS HA).
Qed.

Local Lemma compose_lifted_substitutions Γ Δ Θ σ τ A i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Θ ⊢s τ : Δ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Θ, A[σ][τ] ⊢s q σ∘q τ ≈ q (σ∘τ) : Γ, A }}.
Proof.
  intros HS HT HA.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HT HAs) as HQ.
  pose proof (wf_sub_weaken _ _ (substitution_target _ _ _ HQ)) as H1.
  pose proof (wf_sub_weaken _ _ (substitution_source _ _ _ HQ)) as H2.
  pose proof (wf_sub_compose _ _ _ _ _ HQ H1) as HP.
  pose proof (wf_sub_compose _ _ _ _ _ HP HS) as HC.
  pose proof (type_substitution _ _ _ _ _ HC HA) as HCt.
  pose proof (wf_sub_compose _ _ _ _ _ HT HS) as HST.
  pose proof (wf_sub_compose _ _ _ _ _ H2 HST) as HSTw.
  assert (E : {{ Θ, A[σ][τ] ⊢s σ∘(Wk∘q τ) ≈ (σ∘τ)∘Wk : Γ }}).
  {
    eapply wf_sub_eq_trans.
    - exact (wf_sub_eq_compose_cong _ _ _ _ _ _ _
        (lifted_substitution_tail _ _ _ _ _ HT HAs) (substitution_equality_reflexive _ _ _ HS)).
    - exact (wf_sub_eq_sym _ _ _ _ (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ HS HT H2)).
  }
  pose proof (type_substitution_equality_same_body _ _ _ _ _ _ HC E HA) as EC.
  pose proof (type_substitution_composition _ _ _ _ _ _ _ HT HS HA) as E1.
  assert (E2 : {{ Θ, A[σ][τ] ⊢ A[(σ∘τ)∘Wk] ≈ A[σ][τ][Wk] : Type@i }}).
  {
    eapply wf_exp_eq_trans.
    - exact (type_substitution_composition _ _ _ _ _ _ _ H2 HST HA).
    - exact (type_substitution_congruence _ _ _ _ _ _ _ H2
        (substitution_equality_reflexive _ _ _ H2) E1).
  }
  eapply wf_sub_eq_trans.
  - exact (lift_composition _ _ _ _ _ _ _ HS HA HQ).
  - change (wf_sub_eq (a_sub (a_sub A σ) τ :: Θ) (A :: Γ)
      (a_extend (a_compose σ (a_compose a_weaken (Syntax.q τ))) (a_sub (a_var 0) (Syntax.q τ)))
      (a_extend (a_compose (a_compose σ τ) a_weaken) (a_var 0))).
    eapply wf_sub_eq_extend_cong; [exact E | exact HA |].
    exact (convert_equality _ _ _ _ _ _ (lifted_substitution_head _ _ _ _ _ HT HAs)
      HCt (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_trans _ _ _ _ _ EC E2))).
Qed.

Local Lemma compose_lifted_natural_substitutions Γ Δ Θ σ τ :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Θ ⊢s τ : Δ }} ->
  {{ Θ, ℕ ⊢s q σ∘q τ ≈ q (σ∘τ) : Γ, ℕ }}.
Proof.
  intros HS HT.
  pose proof (wf_nat Γ (substitution_target _ _ _ HS)) as HA.
  pose proof (wf_nat Δ (substitution_source _ _ _ HS)) as HAs.
  pose proof (lift_natural_substitution _ _ _ HT) as HQ.
  pose proof (substitution_source _ _ _ HQ) as HC.
  pose proof (wf_nat _ (substitution_source _ _ _ HT)) as HΘN.
  pose proof (substitution_target _ _ _ HQ) as HD.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HSubA.
  assert (HSub : {{ ⊢ Δ, ℕ ⊆ Δ, ℕ[σ] }})
    by exact (declaration_change_context _ _ _ _
      HSubA HAs (wf_exp_eq_nat_sub _ _ _ HS)).
  pose proof (wf_sub_subtyp _ _ _ _ HQ
    (wf_ctx_extend _ _ _ (substitution_source _ _ _ HS) HSubA) HSub) as HQ'.
  pose proof (wf_sub_weaken _ _ HD) as H1.
  pose proof (wf_sub_weaken _ _ HC) as H2.
  pose proof (wf_sub_compose _ _ _ _ _ HQ H1) as HP.
  pose proof (wf_sub_compose _ _ _ _ _ HP HS) as HW.
  assert (E : {{ Θ, ℕ ⊢s σ∘(Wk∘q τ) ≈ (σ∘τ)∘Wk : Γ }}).
  {
    eapply wf_sub_eq_trans.
    - exact (wf_sub_eq_compose_cong _ _ _ _ _ _ _
        (lift_natural_tail _ _ _ HT) (substitution_equality_reflexive _ _ _ HS)).
    - exact (wf_sub_eq_sym _ _ _ _ (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ HS HT H2)).
  }
  eapply wf_sub_eq_trans.
  - exact (lift_composition _ _ _ _ _ _ _ HS HA HQ').
  - change (wf_sub_eq (a_nat :: Θ) (a_nat :: Γ)
      (a_extend (a_compose σ (a_compose a_weaken (Syntax.q τ))) (a_sub (a_var 0) (Syntax.q τ)))
      (a_extend (a_compose (a_compose σ τ) a_weaken) (a_var 0))).
    eapply natural_argument_equality; [exact HW | exact E | exact (lift_natural_head _ _ _ HT)].
Qed.

Local Lemma eval_natural_argument_inversion A N ρ n a :
  eval_exp N ρ n ->
  eval_exp (a_sub A (a_extend a_id N)) ρ a ->
  eval_exp A (extend_env ρ n) a.
Proof.
  intros HN HA.
  destruct (invert_eval_substitution _ _ _ _ HA) as (η & Hη & H).
  inversion Hη; subst.
  match goal with Hid : eval_sub a_id _ _ |- _ => inversion Hid; subst end.
  reconcile_values. assumption.
Qed.

Local Lemma natural_step_argument_inversion A ρ n m b :
  eval_exp (a_sub A natural_step_substitution) (extend_env (extend_env ρ n) m) b ->
  eval_exp A (extend_env ρ (d_succ n)) b.
Proof.
  intro H.
  destruct (invert_eval_substitution _ _ _ _ H) as (η & Hη & H').
  assert (E : eval_sub natural_step_substitution (extend_env (extend_env ρ n) m)
    (extend_env ρ (d_succ n))).
  { unfold natural_step_substitution.
    apply eval_sub_extend.
    - eapply eval_sub_compose; apply eval_sub_weaken.
    - apply eval_exp_succ, eval_exp_var. }
  pose proof (eval_sub_deterministic _ _ _ _ Hη E) as Eη. now subst η.
Qed.

Local Lemma natural_motive_congruence Γ Δ σ A N N' i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Δ ⊢ N : ℕ }} ->
  {{ Δ ⊢ N ≈ N' : ℕ }} ->
  {{ Δ ⊢ A[σ,,N] ≈ A[σ,,N'] : Type@i }}.
Proof.
  intros HS HA HN EN.
  eapply type_substitution_equality_same_body.
  - exact (natural_argument_substitution _ _ _ _ HS HN).
  - exact (natural_argument_equality _ _ _ _ _ _ HS
      (substitution_equality_reflexive _ _ _ HS) EN).
  - exact HA.
Qed.

(* The semantic certificate on a candidate member lets a dependent
   candidate apply its closure to the arguments admitted by the PER. *)

Local Definition semantic_member (a m : domain) :=
  exists i Q, semantic_type i a a Q /\ Q m m.

Local Definition certified_candidate a (R : value_candidate) : value_candidate :=
  fun M m => semantic_member a m /\ R M m.

Local Lemma semantic_member_in_relation i a b Q m :
  semantic_type i a b Q -> semantic_member a m -> Q m m.
Proof.
  intros HQ (j & R & HR & Hm).
  exact (proj1 (semantic_types_agree_on_left _ _ _ _ _ _ _ HR HQ _ _) Hm).
Qed.

Local Lemma semantic_member_left i a b Q m n :
  semantic_type i a b Q -> Q m n -> semantic_member a m.
Proof.
  intros HQ H.
  exists i, Q. split.
  - exact (semantic_type_trans _ _ _ _ _ _ HQ (semantic_type_sym _ _ _ _ HQ)).
  - exact (per_left _ _ _ (semantic_value_per _ _ _ _ HQ) H).
Qed.

Local Lemma semantic_member_right i a b Q m n :
  semantic_type i a b Q -> Q m n -> semantic_member b n.
Proof.
  intros HQ H.
  apply semantic_member_left with (i := i) (b := a) (Q := Q) (n := m).
  - exact (semantic_type_sym _ _ _ _ HQ).
  - exact (proj1 (semantic_value_per _ _ _ _ HQ) _ _ H).
Qed.

Local Lemma semantic_member_neutral i a Q k :
  semantic_type i a a Q -> neutrals_agree k k -> semantic_member a (d_neut a k).
Proof.
  intros HQ H.
  exists i, Q. split; [exact HQ |].
  exact (proj2 (proj2 (semantic_type_readback _ _ _ _ HQ)) _ _ H).
Qed.

Local Lemma semantic_member_quotes a m :
  semantic_member a m ->
  forall s, exists N, read_nf s (d_dom a m) N /\ read_nf s (d_dom a m) N.
Proof.
  intros (i & Q & HQ & Hm).
  exact (proj1 (proj2 (semantic_type_readback _ _ _ _ HQ)) _ _ Hm).
Qed.

Inductive certified_realization_layer (U : candidate_universe) (i : nat)
    : ctx -> typ -> domain -> value_candidate -> Prop :=
| certify_universe Γ j R :
    wf_ctx Γ -> j < i ->
    candidates_equivalent R (certified_candidate (d_univ j) (universe_candidate U j Γ)) ->
    certified_realization_layer U i Γ (a_typ j) (d_univ j) R
| certify_natural Γ R :
    wf_ctx Γ ->
    candidates_equivalent R (certified_candidate d_nat (natural_candidate Γ)) ->
    certified_realization_layer U i Γ a_nat d_nat R
| certify_neutral Γ A a k R :
    wf_exp Γ (a_typ i) A ->
    typed_type_readback Γ i A (d_neut a k) ->
    neutrals_agree k k ->
    candidates_equivalent R (certified_candidate (d_neut a k) (neutral_candidate Γ A)) ->
    certified_realization_layer U i Γ A (d_neut a k) R
| certify_equation Γ A P Q a p qv R S :
    certified_realization_layer U i Γ A a R ->
    R P p -> R Q qv ->
    candidates_equivalent S (certified_candidate (d_eq a p qv) (equation_candidate Γ A P Q R)) ->
    certified_realization_layer U i Γ (a_eq A P Q) (d_eq a p qv) S
| certify_function Γ A B a ρ C R S T :
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    (forall Δ σ, weakening_between Γ Δ σ ->
      certified_realization_layer U i Δ (a_sub A σ) a (R Δ σ)) ->
    (forall Δ σ, weakening_between Γ Δ σ ->
      forall N n, R Δ σ N n -> exists b, eval_exp C (extend_env ρ n) b) ->
    (forall Δ σ, weakening_between Γ Δ σ ->
      forall N n b, R Δ σ N n -> eval_exp C (extend_env ρ n) b ->
      certified_realization_layer U i Δ (a_sub B (a_extend σ N)) b (S Δ σ N n)) ->
    (exists Q, semantic_type i (d_pi a ρ C) (d_pi a ρ C) Q) ->
    candidates_equivalent T (certified_candidate (d_pi a ρ C) (function_candidate Γ A B ρ C R S)) ->
    certified_realization_layer U i Γ (a_pi A B) (d_pi a ρ C) T
| certify_sigma Γ A B a ρ C R S T :
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    (forall Δ σ, weakening_between Γ Δ σ ->
      certified_realization_layer U i Δ (a_sub A σ) a (R Δ σ)) ->
    (forall Δ σ, weakening_between Γ Δ σ ->
      forall N n, R Δ σ N n -> exists b, eval_exp C (extend_env ρ n) b) ->
    (forall Δ σ, weakening_between Γ Δ σ ->
      forall N n b, R Δ σ N n -> eval_exp C (extend_env ρ n) b ->
      certified_realization_layer U i Δ (a_sub B (a_extend σ N)) b (S Δ σ N n)) ->
    (exists Q, semantic_type i (d_sigma a ρ C) (d_sigma a ρ C) Q) ->
    candidates_equivalent T (certified_candidate (d_sigma a ρ C) (sigma_candidate Γ A B ρ C R S)) ->
    certified_realization_layer U i Γ (a_sigma A B) (d_sigma a ρ C) T
| certify_conversion Γ A B a R :
    certified_realization_layer U i Γ A a R ->
    wf_exp Γ (a_typ i) B -> wf_exp_eq Γ (a_typ i) A B ->
    certified_realization_layer U i Γ B a R.

Local Lemma certified_realization_layer_typing U i :
  (forall j Γ A a R, j < i -> U j Γ A a R -> wf_exp Γ (a_typ j) A) ->
  forall Γ A a R, certified_realization_layer U i Γ A a R ->
    wf_exp Γ (a_typ i) A /\ (forall M m, R M m -> wf_exp Γ A M).
Proof.
  intros Hlower Γ A a R H.
  induction H as
    [Γ j R HΓ Hj HE
    |Γ R HΓ HE
    |Γ A a k R HA HR Hne HE
    |Γ A P Q a p qv R S HG IHG HP HQ HE
    |Γ A B a ρ C R S T HA HB HD IHD Htot HC IHC Hsem HE
    |Γ A B a ρ C R S T HA HB HD IHD Htot HC IHC Hsem HE
    |Γ A B a R HG IHG HB HE].
  - split.
    + eapply type_cumulativity; [exact (wf_typ Γ j HΓ) | lia].
    + intros M m HM. apply HE in HM.
      destruct HM as [_ [R' HL]]. exact (Hlower _ _ _ _ _ Hj HL).
  - split.
    + eapply type_cumulativity; [exact (wf_nat Γ HΓ) | lia].
    + intros M m HM. apply HE in HM. exact (natural_candidate_typed _ _ _ (proj2 HM)).
  - split; [exact HA |].
    intros M m HM. apply HE in HM. exact (proj1 (proj2 HM)).
  - destruct IHG as [HA HM].
    split.
    + exact (wf_eq _ _ _ _ _ HA (HM _ _ HP) (HM _ _ HQ)).
    + intros M m H. apply HE in H. exact (proj1 (proj2 H)).
  - split; [exact (wf_pi _ _ _ _ HA HB) |].
    intros M m H. apply HE in H. exact (proj1 (proj2 H)).
  - split; [exact (wf_sigma _ _ _ _ HA HB) |].
    intros M m H. apply HE in H. exact (proj1 (proj2 H)).
  - split; [exact HB |].
    intros M m H. exact (convert_term _ _ _ _ _ (proj2 IHG _ _ H) HB HE).
Qed.


Local Lemma certified_layer_member U i Γ A a R :
  certified_realization_layer U i Γ A a R ->
  forall M m, R M m -> semantic_member a m.
Proof.
  induction 1; intros M m HM; try now (lazymatch goal with
    | HE : candidates_equivalent _ (certified_candidate _ _) |- _ =>
      exact (proj1 (proj1 (HE _ _) HM))
    end).
  now apply IHcertified_realization_layer with (M := M).
Qed.

Local Lemma certified_layer_semantic_type U i Γ A a R :
  certified_realization_layer U i Γ A a R ->
  exists Q, semantic_type i a a Q.
Proof.
  induction 1 as [Γ j R HΓ Hj HE | Γ R HΓ HE | Γ A a k R HA HR Hk HE |
    Γ A P T a p t R S HG IH HP HT HE |
    Γ A B a ρ C R S T HA HB HD IHD Htot HC IHC Hsem HE |
    Γ A B a ρ C R S T HA HB HD IHD Htot HC IHC Hsem HE |
    Γ A B a R HG IH HB HE].
  - eexists. exact (semantic_universe _ _ Hj).
  - eexists. exact (semantic_natural i).
  - exists neutral_values_agree. apply layer_neutral; [exact Hk | intros x y; reflexivity].
  - destruct IH as [Q HQ].
    exists (equality_values_agree Q p t).
    apply layer_equality with (R := Q); [exact HQ | | | intros x y; reflexivity].
    + exact (semantic_member_in_relation _ _ _ _ _ HQ (certified_layer_member _ _ _ _ _ _ HG _ _ HP)).
    + exact (semantic_member_in_relation _ _ _ _ _ HQ (certified_layer_member _ _ _ _ _ _ HG _ _ HT)).
  - exact Hsem.
  - exact Hsem.
  - exact IH.
Qed.

Local Lemma semantic_member_reflection i a k :
  (exists Q, semantic_type i a a Q) ->
  neutrals_agree k k ->
  semantic_member a (d_neut a k).
Proof. intros [Q HQ] H. exact (semantic_member_neutral _ _ _ _ HQ H). Qed.

Local Definition certified_observation Γ i A a (R : value_candidate) :=
  typed_type_readback Γ i A a /\
  (forall M m, R M m -> typed_value_readback Γ A M a m) /\
  (forall M k, wf_exp Γ A M -> typed_neutral_readback Γ A M k -> neutrals_agree k k -> R M (d_neut a k)).

Local Lemma certified_fresh_binder Γ Δ σ A i a (R : domain_candidate) :
  {{ Γ ⊢ A : Type@i }} ->
  context_weakening Γ Δ σ ->
  (forall Θ τ, weakening_between Γ Θ τ ->
    certified_observation Θ i (a_sub A τ) a (R Θ τ)) ->
  weakening_between Γ (a_sub A σ :: Δ) (a_compose σ a_weaken) /\
  {{ Δ, A[σ] ⊢ #0 : A[σ∘Wk] }} /\
  R {{{ Δ, A[σ] }}} (a_compose σ a_weaken)
    (a_var 0) (d_neut a (d_var (length Δ))).
Proof.
  intros HA HW HObs.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (weakening_between_canonical _ _ _
    (context_weakening_step _ _ _ _ _ HW HAs)) as HW'.
  destruct (last_variable_quotation_after_lift _ _ _ _ _ HS HA) as [H0 HR].
  split; [exact HW' | split; [exact H0 |]].
  exact (proj2 (proj2 (HObs _ _ HW')) _ _ H0 HR (related_variable (length Δ))).
Qed.

Local Lemma certified_binder_observations Γ A B i a ρ C (R : domain_candidate) (S : codomain_candidate) :
  {{ Γ ⊢ A : Type@i }} ->
  (forall Δ σ, weakening_between Γ Δ σ ->
    certified_observation Δ i (a_sub A σ) a (R Δ σ)) ->
  (forall Δ σ, weakening_between Γ Δ σ ->
    forall N n, R Δ σ N n -> exists b, eval_exp C (extend_env ρ n) b) ->
  (forall Δ σ, weakening_between Γ Δ σ ->
    forall N n b, R Δ σ N n -> eval_exp C (extend_env ρ n) b ->
    certified_observation Δ i (a_sub B (a_extend σ N)) b (S Δ σ N n)) ->
  typed_type_readback Γ i A a /\
  (forall Δ σ, context_weakening Γ Δ σ ->
    exists b, eval_exp C (extend_env ρ (d_neut a (d_var (length Δ)))) b /\
      typed_type_readback (a_sub A σ :: Δ) i (a_sub B (Syntax.q σ)) b).
Proof.
  intros HA HD Htotal HC.
  pose proof (typing_context _ _ _ HA) as HΓ.
  split.
  - eapply typed_type_readback_remove_identity; [exact HA |].
    exact (proj1 (HD _ _ (weakening_between_canonical _ _ _ (context_weakening_id _ HΓ)))).
  - intros Δ σ HW.
    destruct (certified_fresh_binder _ _ _ _ _ _ _ HA HW HD) as (HW' & H0 & HR).
    destruct (Htotal _ _ HW' _ _ HR) as (b & Hb).
    exists b. split; [exact Hb | exact (proj1 (HC _ _ HW' _ _ _ HR Hb))].
Qed.

Local Lemma certified_realization_layer_observes U i :
  (forall j Γ A a R, j < i -> U j Γ A a R -> wf_exp Γ (a_typ j) A) ->
  (forall j Γ A a R, j < i -> U j Γ A a R -> typed_type_readback Γ j A a) ->
  (forall j Γ A k, j < i -> wf_exp Γ (a_typ j) A ->
    typed_neutral_readback Γ (a_typ j) A k -> neutrals_agree k k ->
    exists R, U j Γ A (d_neut (d_univ j) k) R) ->
  forall Γ A a R, certified_realization_layer U i Γ A a R ->
    certified_observation Γ i A a R.
Proof.
  intros HlowT HlowR HlowN Γ A a R H.
  induction H as
    [Γ j R HΓ Hj HE
    |Γ R HΓ HE
    |Γ A a k R HA HR Hk HE
    |Γ A P Q a p qv R S HG IHG HP HQ HE
    |Γ A B a ρ C R S T HA HB HD IHD Htot HC IHC Hsem HE
    |Γ A B a ρ C R S T HA HB HD IHD Htot HC IHC Hsem HE
    |Γ A B a R HG IHG HB HE].
  - split.
    + eapply typed_type_readback_raise; [exact HΓ | | apply typed_type_readback_universe_constructor]. lia.
    + split.
      * intros M m HM. apply HE in HM. destruct HM as [_ [T HT]].
        apply typed_readback_universe. eapply HlowR; eassumption.
      * intros M k HM Hk Hkk. apply HE. split.
        -- exact (semantic_member_neutral _ _ _ _ (semantic_universe _ _ Hj) Hkk).
        -- exact (HlowN _ _ _ _ Hj HM Hk Hkk).
  - split.
    + apply (typed_type_readback_raise Γ 0 i); [exact HΓ | lia | apply typed_type_readback_natural_constructor].
    + split.
      * intros M m HM. apply HE in HM. exact (natural_candidate_quotes _ _ _ (proj2 HM)).
      * intros M k HM Hk Hkk. apply HE. split.
        -- exact (semantic_member_neutral _ _ _ _ (semantic_natural i) Hkk).
        -- now apply candidate_neutral.
  - split; [exact HR |]. split.
    + intros M m HM. apply HE in HM.
      destruct HM as (_ & HT & tag & n & -> & Hnr).
      eapply typed_readback_atomic_reflection; [apply atomic_neutral | exact Hnr].
    + intros M n HM Hn Hnn. apply HE. split.
      * eapply semantic_member_reflection with (i := i); [| exact Hnn].
        exists neutral_values_agree. apply layer_neutral; [exact Hk | intros x y; reflexivity].
      * split; [exact HM |].
        exists (d_neut a k), n. auto.
  - destruct IHG as (HAr & HVal & HReflect).
    destruct (certified_realization_layer_typing _ _ HlowT _ _ _ _ HG) as [HA HTyp].
    pose proof (HTyp _ _ HP) as HPT.
    pose proof (HTyp _ _ HQ) as HQT.
    pose proof (wf_eq _ _ _ _ _ HA HPT HQT) as HResult.
    split.
    + eapply typed_type_readback_equality; eauto.
    + split.
      * intros M m HM. apply HE in HM.
        destruct HM as [_ [HM [(tag & n & -> & Hnr) | (N & n & -> & HN & ENP & ENQ & EM)]]].
        -- eapply typed_readback_atomic_reflection; [apply atomic_equality | exact Hnr].
        -- pose proof (typed_value_readback_reflexivity _ _ _ _ _ _
             HA (HTyp _ _ HN) HAr (HVal _ _ HN)) as HRefl.
           pose proof (typed_equation_value_reindex _ _ _ _ _ _ p qv HRefl) as Hindexed.
           eapply typed_readback_expression_conversion; [exact EM |].
           eapply typed_readback_type_conversion; [exact HResult | | exact Hindexed].
           exact (wf_exp_eq_eq_cong _ _ _ _ _ _ _ _
             (expression_equality_reflexive _ _ _ HA) ENP ENQ).
      * intros M n HM Hn Hnn. apply HE. split.
        -- eapply semantic_member_reflection with (i := i); [| exact Hnn].
           eapply certified_layer_semantic_type.
           exact (certify_equation _ _ _ _ _ _ _ _ _ _ _ HG HP HQ HE).
        -- split; [exact HM | left]. exists (d_eq a p qv), n. auto.
  - destruct (certified_binder_observations _ _ _ _ _ _ _ _ _ HA IHD Htot IHC) as [HAr HBr].
    split.
    + exact (proj1 (typed_type_readback_binder _ _ _ _ _ _ _ HA HB HAr HBr)).
    + split.
      * intros F f HF. apply HE in HF. destruct HF as [_ [HF HAction]].
        apply (typed_value_readback_function _ _ _ _ _ _ _ _ _ HA HB HF HAr).
        intros Δ σ HW.
        pose proof (context_weakening_typed _ _ _ HW) as HS.
        pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
        assert (Hw : wf_sub (a_sub A σ :: Δ) Δ a_weaken) by
          eauto using wf_sub_weaken, wf_ctx_extend, typing_context.
        destruct (certified_fresh_binder _ _ _ _ _ _ _ HA HW IHD) as (HW' & H0 & HR).
        destruct (HAction _ _ HW' _ _ HR) as (b & r & Hb & HApp & HRb).
        exists b, r. split; [exact Hb | split; [exact HApp |]].
        eapply typed_readback_expression_conversion.
        -- exact (application_under_iterated_weakening _ _ _ _ _ _ _ _ _ _ HS Hw HA HB HF H0).
        -- exact (proj1 (proj2 (IHC _ _ HW' _ _ _ HR Hb)) _ _ HRb).
      * intros F k HF Hk Hkk. apply HE. split; [exact (semantic_member_reflection _ _ _ Hsem Hkk) |].
        split; [exact HF |].
        intros Δ σ HW N n HN.
        pose proof (certified_realization_layer_typing _ _ HlowT _ _ _ _ (HD _ _ HW)) as Htyped.
        pose proof (proj2 Htyped _ _ HN) as HNty.
        pose proof (proj1 (proj2 (IHD _ _ HW)) _ _ HN) as HNread.
        destruct (Htot _ _ HW _ _ HN) as (b & Hb).
        destruct (neutral_application_under_weakening _ _ _ _ _ _ _ _ _ _ _ HW HA HB HF HNty Hk HNread)
          as (HApp & HAppread).
        exists b, (d_neut b (d_app k (d_dom a n))).
        split; [exact Hb | split; [now apply eval_app_neut |]].
        eapply (proj2 (proj2 (IHC _ _ HW _ _ _ HN Hb))); [exact HApp | exact HAppread |].
        eapply related_neutral_application; [exact Hkk |].
        exact (semantic_member_quotes _ _
          (certified_layer_member _ _ _ _ _ _ (HD _ _ HW) _ _ HN)).
  - destruct (certified_binder_observations _ _ _ _ _ _ _ _ _ HA IHD Htot IHC) as [HAr HBr].
    split.
    + exact (proj2 (typed_type_readback_binder _ _ _ _ _ _ _ HA HB HAr HBr)).
    + split.
      * intros P p HP. apply HE in HP. destruct HP as [_ [HP HAction]].
        apply (typed_value_readback_sigma _ _ _ _ _ _ _ _ _ HA HB HP HAr).
        intros Δ σ HW.
        pose proof (context_weakening_typed _ _ _ HW) as HS.
        pose proof (weakening_between_canonical _ _ _ HW) as HWeak.
        destruct (HBr _ _ HW) as (b & Hb & HRb).
        destruct (HAction _ _ HWeak) as (x & y & b' & Hx & Hy & Hb' & HRx & HRy).
        destruct (substituted_pair_components _ _ _ _ _ _ _ HS HA HB HP) as (HF & HBT & HSn).
        pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
        pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
        pose proof (type_substitution _ _ _ _ _ HQ HB) as HBq.
        pose proof (typing_identity_extension _ _ _ _ HAs HF) as HInst.
        pose proof (type_substitution _ _ _ _ _ HInst HBq) as Hty.
        pose proof (type_lift_at_argument _ _ _ _ _ _ _ _ HS HA HB HF) as Htyeq.
        exists b, b', x, y. repeat split; try assumption.
        -- exact (proj1 (proj2 (IHD _ _ HWeak)) _ _ HRx).
        -- eapply typed_readback_type_conversion; [exact Hty | exact (wf_exp_eq_sym _ _ _ _ Htyeq) |].
           exact (proj1 (proj2 (IHC _ _ HWeak _ _ _ HRx Hb')) _ _ HRy).
      * intros P k HP Hk Hkk. apply HE. split; [exact (semantic_member_reflection _ _ _ Hsem Hkk) |].
        split; [exact HP |].
        intros Δ σ HW.
        pose proof (weakening_between_typed _ _ _ HW) as HS.
        destruct (substituted_pair_components _ _ _ _ _ _ _ HS HA HB HP) as (HF & HBT & HSn).
        destruct (neutral_pair_projections_under_weakening _ _ _ _ _ _ _ _ HW HA HB HP Hk)
          as [HFR HSR].
        assert (HRx : R Δ σ (a_fst (a_sub P σ)) (d_neut a (d_fst k))).
        { exact (proj2 (proj2 (IHD _ _ HW)) _ _ HF HFR (related_neutral_fst _ _ Hkk)). }
        destruct (Htot _ _ HW _ _ HRx) as (b & Hb).
        exists (d_neut a (d_fst k)), (d_neut b (d_snd k)), b.
        repeat split; try assumption; try (now apply eval_fst_neut); try (now apply eval_snd_neut).
        exact (proj2 (proj2 (IHC _ _ HW _ _ _ HRx Hb)) _ _ HSn HSR (related_neutral_snd _ _ Hkk)).
  - destruct IHG as (HT & HR & HN).
    pose proof (proj1 (certified_realization_layer_typing _ _ HlowT _ _ _ _ HG)) as HA.
    pose proof (wf_exp_eq_sym _ _ _ _ HE) as HE'.
    split.
    + eapply typed_readback_expression_conversion; eassumption.
    + split.
      * intros M m HM.
        exact (typed_readback_type_conversion _ _ _ _ _ _ _ _ _ _ HB HE (HR _ _ HM)).
      * intros M k HM Hk Hkk. apply HN.
        -- exact (convert_term _ _ _ _ _ HM HA HE').
        -- exact (typed_readback_type_conversion _ _ _ _ _ _ _ _ _ _ HA HE' Hk).
        -- exact Hkk.
Qed.


Local Fixpoint lower_certified_realizations (i : nat) : candidate_universe :=
  match i with
  | 0 => fun _ _ _ _ _ => False
  | S j => fun k =>
    if Nat.eq_dec k j then certified_realization_layer (lower_certified_realizations j) j
    else lower_certified_realizations j k
  end.

Local Definition certified_type i := certified_realization_layer (lower_certified_realizations i) i.

Local Lemma lower_certified_realization_lookup i j Γ A a R :
  j < i -> (lower_certified_realizations i j Γ A a R <-> certified_type j Γ A a R).
Proof.
  induction i as [|i IH]; intro H; [lia |].
  cbn [lower_certified_realizations]. destruct (Nat.eq_dec j i) as [-> | Hne].
  - reflexivity.
  - apply IH. lia.
Qed.

Local Lemma certified_type_properties i Γ A a R :
  certified_type i Γ A a R ->
  (wf_exp Γ (a_typ i) A /\ (forall M m, R M m -> wf_exp Γ A M)) /\
  certified_observation Γ i A a R.
Proof.
  revert Γ A a R. induction i using lt_wf_ind.
  intros Γ A a R HG.
  assert (HL : forall j Δ B b T, j < i -> lower_certified_realizations i j Δ B b T ->
    (wf_exp Δ (a_typ j) B /\ (forall M m, T M m -> wf_exp Δ B M)) /\
    certified_observation Δ j B b T).
  {
    intros j Δ B b T Hj Hlow.
    apply (H j Hj).
    apply (lower_certified_realization_lookup _ _ _ _ _ _ Hj). exact Hlow.
  }
  assert (Htype : forall j Δ B b T, j < i -> lower_certified_realizations i j Δ B b T ->
    wf_exp Δ (a_typ j) B).
  { intros. exact (proj1 (proj1 (HL _ _ _ _ _ ltac:(eassumption) ltac:(eassumption)))). }
  split.
  - exact (certified_realization_layer_typing _ _ Htype _ _ _ _ HG).
  - eapply certified_realization_layer_observes.
    + exact Htype.
    + intros j Δ B b T Hj Hr. exact (proj1 (proj2 (HL _ _ _ _ _ Hj Hr))).
    + intros j Δ B k Hj HB Hk Hkk.
      exists (certified_candidate (d_neut (d_univ j) k) (neutral_candidate Δ B)).
      apply (lower_certified_realization_lookup _ _ _ _ _ _ Hj).
      apply certify_neutral; [exact HB | now apply typed_type_readback_neutral | exact Hkk |].
      unfold candidates_equivalent. reflexivity.
    + exact HG.
Qed.

Local Lemma certified_type_readback i Γ A a R :
  certified_type i Γ A a R -> typed_type_readback Γ i A a.
Proof. intro H. exact (proj1 (proj2 (certified_type_properties _ _ _ _ _ H))). Qed.

Local Lemma certified_term_readback i Γ A a R M m :
  certified_type i Γ A a R -> R M m -> typed_value_readback Γ A M a m.
Proof. intros H HR. exact (proj1 (proj2 (proj2 (certified_type_properties _ _ _ _ _ H))) _ _ HR). Qed.

Local Lemma certified_reflection i Γ A a R M k :
  certified_type i Γ A a R ->
  wf_exp Γ A M -> typed_neutral_readback Γ A M k -> neutrals_agree k k ->
  R M (d_neut a k).
Proof. intro H. exact (proj2 (proj2 (proj2 (certified_type_properties _ _ _ _ _ H))) _ _). Qed.

Local Lemma certified_type_conversion i Γ A B a R :
  certified_type i Γ A a R ->
  {{ Γ ⊢ B : Type@i }} -> {{ Γ ⊢ A ≈ B : Type@i }} ->
  certified_type i Γ B a R.
Proof. intros. eapply certify_conversion; eassumption. Qed.

Local Lemma certified_types_with_same_code Γ A A' a i j R S :
  certified_type i Γ A a R -> certified_type j Γ A' a S ->
  {{ Γ ⊢ A ≈ A' : Type@(Nat.max i j) }}.
Proof.
  intros HA HA'.
  destruct (certified_type_properties _ _ _ _ _ HA) as ([HAt _] & HAr & _).
  destruct (certified_type_properties _ _ _ _ _ HA') as ([HA't _] & HA'r & _).
  destruct (typed_type_readback_here _ _ _ _ HAt HAr) as (w & Hw & HT & HE).
  destruct (typed_type_readback_here _ _ _ _ HA't HA'r) as (u & Hu & HT' & HE').
  pose proof (proj2 (proj2 readback_deterministic) _ _ _ Hw _ Hu). subst u.
  pose proof (typing_context _ _ _ HAt) as HΓ.
  eapply wf_exp_eq_trans.
  - eapply equality_cumulativity; [exact HE | exact HΓ | apply Nat.le_max_l].
  - apply wf_exp_eq_sym.
    eapply equality_cumulativity; [exact HE' | exact HΓ | apply Nat.le_max_r].
Qed.

Inductive certified_realization_head (U : candidate_universe) (i : nat)
    : ctx -> typ -> domain -> value_candidate -> Prop :=
| certified_head_universe Γ j R :
    wf_ctx Γ -> j < i ->
    candidates_equivalent R (certified_candidate (d_univ j) (universe_candidate U j Γ)) ->
    certified_realization_head U i Γ (a_typ j) (d_univ j) R
| certified_head_natural Γ R :
    wf_ctx Γ ->
    candidates_equivalent R (certified_candidate d_nat (natural_candidate Γ)) ->
    certified_realization_head U i Γ a_nat d_nat R
| certified_head_neutral Γ A a k R :
    wf_exp Γ (a_typ i) A ->
    typed_type_readback Γ i A (d_neut a k) ->
    neutrals_agree k k ->
    candidates_equivalent R (certified_candidate (d_neut a k) (neutral_candidate Γ A)) ->
    certified_realization_head U i Γ A (d_neut a k) R
| certified_head_equation Γ A P Q a p qv R S :
    certified_realization_layer U i Γ A a R ->
    R P p -> R Q qv ->
    candidates_equivalent S (certified_candidate (d_eq a p qv) (equation_candidate Γ A P Q R)) ->
    certified_realization_head U i Γ (a_eq A P Q) (d_eq a p qv) S
| certified_head_function Γ A B a ρ C R S T :
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    (forall Δ σ, weakening_between Γ Δ σ ->
      certified_realization_layer U i Δ (a_sub A σ) a (R Δ σ)) ->
    (forall Δ σ, weakening_between Γ Δ σ ->
      forall N n, R Δ σ N n -> exists b, eval_exp C (extend_env ρ n) b) ->
    (forall Δ σ, weakening_between Γ Δ σ ->
      forall N n b, R Δ σ N n -> eval_exp C (extend_env ρ n) b ->
      certified_realization_layer U i Δ (a_sub B (a_extend σ N)) b (S Δ σ N n)) ->
    (exists Q, semantic_type i (d_pi a ρ C) (d_pi a ρ C) Q) ->
    candidates_equivalent T (certified_candidate (d_pi a ρ C) (function_candidate Γ A B ρ C R S)) ->
    certified_realization_head U i Γ (a_pi A B) (d_pi a ρ C) T
| certified_head_sigma Γ A B a ρ C R S T :
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    (forall Δ σ, weakening_between Γ Δ σ ->
      certified_realization_layer U i Δ (a_sub A σ) a (R Δ σ)) ->
    (forall Δ σ, weakening_between Γ Δ σ ->
      forall N n, R Δ σ N n -> exists b, eval_exp C (extend_env ρ n) b) ->
    (forall Δ σ, weakening_between Γ Δ σ ->
      forall N n b, R Δ σ N n -> eval_exp C (extend_env ρ n) b ->
      certified_realization_layer U i Δ (a_sub B (a_extend σ N)) b (S Δ σ N n)) ->
    (exists Q, semantic_type i (d_sigma a ρ C) (d_sigma a ρ C) Q) ->
    candidates_equivalent T (certified_candidate (d_sigma a ρ C) (sigma_candidate Γ A B ρ C R S)) ->
    certified_realization_head U i Γ (a_sigma A B) (d_sigma a ρ C) T.

Local Lemma certified_realization_layer_expose_head U i Γ A a R :
  certified_realization_layer U i Γ A a R ->
  exists B, certified_realization_head U i Γ B a R.
Proof.
  intro H.
  induction H as
    [Γ j R HΓ Hj HE
    |Γ R HΓ HE
    |Γ A a k R HA HR Hk HE
    |Γ A P Q a p qv R S HG IHG HP HQ HE
    |Γ A B a ρ C R S T HA HB HD IHD Htot HC IHC Hsem HE
    |Γ A B a ρ C R S T HA HB HD IHD Htot HC IHC Hsem HE
    |Γ A B a R HG IHG HB HE].
  - exists (a_typ j). exact (certified_head_universe _ _ _ _ _ HΓ Hj HE).
  - exists a_nat. exact (certified_head_natural _ _ _ _ HΓ HE).
  - exists A. exact (certified_head_neutral _ _ _ _ _ _ _ HA HR Hk HE).
  - exists (a_eq A P Q). exact (certified_head_equation _ _ _ _ _ _ _ _ _ _ _ HG HP HQ HE).
  - exists (a_pi A B). exact (certified_head_function _ _ _ _ _ _ _ _ _ _ _ HA HB HD Htot HC Hsem HE).
  - exists (a_sigma A B). exact (certified_head_sigma _ _ _ _ _ _ _ _ _ _ _ HA HB HD Htot HC Hsem HE).
  - exact IHG.
Qed.

Local Lemma certified_realization_head_as_layer U i Γ A a R :
  certified_realization_head U i Γ A a R -> certified_realization_layer U i Γ A a R.
Proof.
  destruct 1; first [eapply certify_universe | eapply certify_natural | eapply certify_neutral |
    eapply certify_equation | eapply certify_function | eapply certify_sigma];
    eassumption.
Qed.


Local Lemma certified_candidate_agreement a R S :
  candidates_equivalent R S ->
  candidates_equivalent (certified_candidate a R) (certified_candidate a S).
Proof.
  intros H M m.
  specialize (H M m). unfold certified_candidate. tauto.
Qed.

Local Lemma certified_realization_layer_change_candidate U i Γ A a R S :
  certified_realization_layer U i Γ A a R ->
  candidates_equivalent R S ->
  certified_realization_layer U i Γ A a S.
Proof.
  intros H HE.
  induction H as
    [Γ j R HΓ Hj EQ
    |Γ R HΓ EQ
    |Γ A a k R HA HR Hk EQ
    |Γ A P Q a p qv R T HG IHG HP HQ EQ
    |Γ A B a ρ C R T V HA HB HD IHD Htot HC IHC Hsem EQ
    |Γ A B a ρ C R T V HA HB HD IHD Htot HC IHC Hsem EQ
    |Γ A B a R HG IHG HB EQ].
  all: first [eapply certify_universe | eapply certify_natural | eapply certify_neutral |
    eapply certify_equation | eapply certify_function | eapply certify_sigma |
    eapply certify_conversion].
  all: try (solve [eassumption | apply IHG; exact HE]).
  all: exact (candidate_agreement_trans _ _ _ (candidate_agreement_sym _ _ HE) EQ).
Qed.

Local Lemma certified_realization_layer_raise U V i j :
  i <= j ->
  (forall k Γ A a R, k < i -> (U k Γ A a R <-> V k Γ A a R)) ->
  forall Γ A a R, certified_realization_layer U i Γ A a R -> certified_realization_layer V j Γ A a R.
Proof.
  intros Hle HUV Γ A a R H.
  induction H as
    [Γ k R HΓ Hk HE
    |Γ R HΓ HE
    |Γ A a n R HA HR Hn HE
    |Γ A P Q a p qv R S H IHH HP HQ HE
    |Γ A B a ρ C R S T HA HB HD IHD Htot HC IHC Hsem HE
    |Γ A B a ρ C R S T HA HB HD IHD Htot HC IHC Hsem HE
    |Γ A B a R H IHH HB HE].
  - eapply certify_universe; [exact HΓ | lia |].
    intros M m. specialize (HE M m). unfold universe_candidate in *.
    split; intro HM.
    + apply HE in HM. destruct HM as [HG [S HS]]. split; [exact HG | exists S; now apply HUV].
    + apply HE. destruct HM as [HG [S HS]]. split; [exact HG | exists S; now apply HUV].
  - now apply certify_natural.
  - eapply certify_neutral; [eauto using type_cumulativity | | exact Hn | exact HE].
    eapply typed_type_readback_raise; eauto using typing_context.
  - eapply certify_equation; eassumption.
  - eapply certify_function; eauto using type_cumulativity.
    destruct Hsem as [Q HQ]. exists Q. exact (semantic_type_cumulative _ _ _ _ _ Hle HQ).
  - eapply certify_sigma; eauto using type_cumulativity.
    destruct Hsem as [Q HQ]. exists Q. exact (semantic_type_cumulative _ _ _ _ _ Hle HQ).
  - eapply certify_conversion.
    + exact IHH.
    + eauto using type_cumulativity.
    + eapply equality_cumulativity; eauto using typing_context.
Qed.

Local Lemma certified_type_raise i j Γ A a R :
  i <= j -> certified_type i Γ A a R -> certified_type j Γ A a R.
Proof.
  intros Hle H.
  eapply certified_realization_layer_raise; try eassumption.
  intros k Δ B b S Hk.
  rewrite !lower_certified_realization_lookup by lia. reflexivity.
Qed.

Local Lemma certified_same_level_code_equality Γ A B a i R S :
  certified_type i Γ A a R -> certified_type i Γ B a S ->
  {{ Γ ⊢ A ≈ B : Type@i }}.
Proof.
  intros H H'.
  pose proof (certified_types_with_same_code _ _ _ _ _ _ _ _ H H') as E.
  now rewrite Nat.max_id in E.
Qed.

Local Lemma certified_members_same_value Γ A B a i R S M N m :
  certified_type i Γ A a R ->
  certified_type i Γ B a S ->
  R M m -> S N m ->
  {{ Γ ⊢ M ≈ N : A }}.
Proof.
  intros HT HT' HM HN.
  destruct (proj1 (certified_type_properties _ _ _ _ _ HT)) as [HA Htyped].
  destruct (proj1 (certified_type_properties _ _ _ _ _ HT')) as [HB Htyped'].
  pose proof (certified_same_level_code_equality _ _ _ _ _ _ _ HT HT') as Htypes.
  destruct (typed_readback_here _ _ _ _ _ _ _ _ _
    HA (Htyped _ _ HM) (certified_term_readback _ _ _ _ _ _ _ HT HM))
    as (w & Hw & HTw & HEM).
  destruct (typed_readback_here _ _ _ _ _ _ _ _ _
    HB (Htyped' _ _ HN) (certified_term_readback _ _ _ _ _ _ _ HT' HN))
    as (u & Hu & HTu & HEN).
  pose proof (proj1 readback_deterministic _ _ _ Hw _ Hu). subst u.
  eapply wf_exp_eq_trans; [exact HEM |].
  apply wf_exp_eq_sym.
  exact (convert_equality _ _ _ _ _ _ HEN HA (wf_exp_eq_sym _ _ _ _ Htypes)).
Qed.


Local Lemma certified_universe_view i Γ A j R :
  certified_type i Γ A (d_univ j) R ->
  candidates_equivalent R (certified_candidate (d_univ j) (universe_candidate (lower_certified_realizations i) j Γ)).
Proof.
  intro H.
  destruct (certified_realization_layer_expose_head _ _ _ _ _ _ H) as (B & HB).
  inversion HB; subst. assumption.
Qed.

Local Lemma certified_natural_view i Γ A R :
  certified_type i Γ A d_nat R ->
  candidates_equivalent R (certified_candidate d_nat (natural_candidate Γ)).
Proof.
  intro H.
  destruct (certified_realization_layer_expose_head _ _ _ _ _ _ H) as (B & HB).
  inversion HB; subst. assumption.
Qed.

Local Lemma certified_neutral_view i Γ A a k R :
  certified_type i Γ A (d_neut a k) R ->
  exists B, {{ Γ ⊢ B : Type@i }} /\
    certified_type i Γ B (d_neut a k) R /\ candidates_equivalent R (certified_candidate (d_neut a k) (neutral_candidate Γ B)).
Proof.
  intro H.
  destruct (certified_realization_layer_expose_head _ _ _ _ _ _ H) as (B & HB).
  pose proof (certified_realization_head_as_layer _ _ _ _ _ _ HB) as HT.
  inversion HB; subst. exists B. repeat (first [assumption | split]).
Qed.

Local Lemma certified_equation_view i Γ A a m n S :
  certified_type i Γ A (d_eq a m n) S ->
  exists B P Q R,
    certified_type i Γ B a R /\ R P m /\ R Q n /\
    certified_type i Γ (a_eq B P Q) (d_eq a m n) S /\
    candidates_equivalent S (certified_candidate (d_eq a m n) (equation_candidate Γ B P Q R)).
Proof.
  intro H.
  destruct (certified_realization_layer_expose_head _ _ _ _ _ _ H) as (B & HB).
  pose proof (certified_realization_head_as_layer _ _ _ _ _ _ HB) as HT.
  inversion HB; subst.
  do 4 eexists. repeat (first [eassumption | split]).
Qed.

Local Lemma certified_function_view i Γ A a ρ C T :
  certified_type i Γ A (d_pi a ρ C) T ->
  exists P Q R S,
    wf_exp Γ (a_typ i) P /\ wf_exp (P :: Γ) (a_typ i) Q /\
    certified_type i Γ (a_pi P Q) (d_pi a ρ C) T /\
    (forall Δ σ, weakening_between Γ Δ σ -> certified_type i Δ (a_sub P σ) a (R Δ σ)) /\
    (forall Δ σ, weakening_between Γ Δ σ ->
      forall N n, R Δ σ N n -> exists b, eval_exp C (extend_env ρ n) b) /\
    (forall Δ σ, weakening_between Γ Δ σ ->
      forall N n b, R Δ σ N n -> eval_exp C (extend_env ρ n) b ->
      certified_type i Δ (a_sub Q (a_extend σ N)) b (S Δ σ N n)) /\
    candidates_equivalent T (certified_candidate (d_pi a ρ C) (function_candidate Γ P Q ρ C R S)).
Proof.
  intro H.
  destruct (certified_realization_layer_expose_head _ _ _ _ _ _ H) as (B & HB).
  pose proof (certified_realization_head_as_layer _ _ _ _ _ _ HB) as HT.
  inversion HB; subst.
  do 4 eexists. repeat (first [eassumption | split]).
Qed.

Local Lemma certified_sigma_view i Γ A a ρ C T :
  certified_type i Γ A (d_sigma a ρ C) T ->
  exists P Q R S,
    wf_exp Γ (a_typ i) P /\ wf_exp (P :: Γ) (a_typ i) Q /\
    certified_type i Γ (a_sigma P Q) (d_sigma a ρ C) T /\
    (forall Δ σ, weakening_between Γ Δ σ -> certified_type i Δ (a_sub P σ) a (R Δ σ)) /\
    (forall Δ σ, weakening_between Γ Δ σ ->
      forall N n, R Δ σ N n -> exists b, eval_exp C (extend_env ρ n) b) /\
    (forall Δ σ, weakening_between Γ Δ σ ->
      forall N n b, R Δ σ N n -> eval_exp C (extend_env ρ n) b ->
      certified_type i Δ (a_sub Q (a_extend σ N)) b (S Δ σ N n)) /\
    candidates_equivalent T (certified_candidate (d_sigma a ρ C) (sigma_candidate Γ P Q ρ C R S)).
Proof.
  intro H.
  destruct (certified_realization_layer_expose_head _ _ _ _ _ _ H) as (B & HB).
  pose proof (certified_realization_head_as_layer _ _ _ _ _ _ HB) as HT.
  inversion HB; subst.
  do 4 eexists. repeat (first [eassumption | split]).
Qed.


Local Lemma certified_candidates_with_same_code i Γ A a R :
  certified_type i Γ A a R ->
  forall B S, certified_type i Γ B a S -> candidates_equivalent R S.
Proof.
  intro H. pose proof H as Hleft. revert Hleft.
  induction H as
    [Γ j R HΓ Hj HE
    |Γ R HΓ HE
    |Γ A a k R HA HR Hk HE
    |Γ A P Q a p qv R S HG IHG HP HQ HE
    |Γ A B a ρ C R S T HA HB HD IHD Htot HC IHC Hsem HE
    |Γ A B a ρ C R S T HA HB HD IHD Htot HC IHC Hsem HE
    |Γ A B a R HG IHG HB HE];
    intros Hleft Z V Hright.
  - eapply candidate_agreement_trans; [exact HE |].
    apply candidate_agreement_sym. exact (certified_universe_view _ _ _ _ _ Hright).
  - eapply candidate_agreement_trans; [exact HE |].
    apply candidate_agreement_sym. exact (certified_natural_view _ _ _ _ Hright).
  - destruct (certified_neutral_view _ _ _ _ _ _ Hright) as (A' & HA' & Hright' & HE').
    pose proof (certified_same_level_code_equality _ _ _ _ _ _ _ Hleft Hright') as EA.
    eapply candidate_agreement_trans; [exact HE |].
    eapply candidate_agreement_trans; [ | exact (candidate_agreement_sym _ _ HE')].
    apply certified_candidate_agreement.
    intros M m. split.
    + exact (neutral_candidate_covariance _ _ _ _ HA' EA _ _).
    + exact (neutral_candidate_covariance _ _ _ _ HA (wf_exp_eq_sym _ _ _ _ EA) _ _).
  - destruct (certified_equation_view _ _ _ _ _ _ _ Hright) as
      (A' & P' & Q' & T & HGA' & HP' & HQ' & Hright' & HE').
    pose proof (IHG HG _ _ HGA') as ERel.
    pose proof (certified_same_level_code_equality _ _ _ _ _ _ _ HG HGA') as EA.
    destruct (proj1 (certified_type_properties _ _ _ _ _ HG)) as [HA HT].
    destruct (proj1 (certified_type_properties _ _ _ _ _ HGA')) as [HA' HT'].
    eapply candidate_agreement_trans; [exact HE |].
    eapply candidate_agreement_trans; [ | exact (candidate_agreement_sym _ _ HE')].
    apply certified_candidate_agreement.
    intros M m. split.
    + eapply equation_candidate_covariance; try eassumption; try solve [eauto].
      * exact (certified_members_same_value _ _ _ _ _ _ _ _ _ _ HG HGA' HP HP').
      * exact (certified_members_same_value _ _ _ _ _ _ _ _ _ _ HG HGA' HQ HQ').
    + eapply equation_candidate_covariance; try eassumption;
        try solve [now apply wf_exp_eq_sym | now apply candidate_agreement_sym | eauto].
      * exact (certified_members_same_value _ _ _ _ _ _ _ _ _ _ HGA' HG HP' HP).
      * exact (certified_members_same_value _ _ _ _ _ _ _ _ _ _ HGA' HG HQ' HQ).
  - destruct (certified_function_view _ _ _ _ _ _ _ Hright) as
      (A' & B' & R' & S' & HA' & HB' & Hright' & HD' & Htot' & HC' & HE').
    eapply candidate_agreement_trans; [exact HE |].
    eapply candidate_agreement_trans; [ | exact (candidate_agreement_sym _ _ HE')].
    apply certified_candidate_agreement.
    apply function_candidate_agreement with (i := i).
    + exact (wf_pi _ _ _ _ HA HB).
    + exact (wf_pi _ _ _ _ HA' HB').
    + exact (certified_same_level_code_equality _ _ _ _ _ _ _ Hleft Hright').
    + intros Δ σ HW. exact (IHD _ _ HW (HD _ _ HW) _ _ (HD' _ _ HW)).
    + intros Δ σ HW N n b HN Hb.
      assert (HN' : R' Δ σ N n) by
        (apply (IHD _ _ HW (HD _ _ HW) _ _ (HD' _ _ HW)); exact HN).
      exact (IHC _ _ HW _ _ _ HN Hb (HC _ _ HW _ _ _ HN Hb) _ _ (HC' _ _ HW _ _ _ HN' Hb)).
  - destruct (certified_sigma_view _ _ _ _ _ _ _ Hright) as
      (A' & B' & R' & S' & HA' & HB' & Hright' & HD' & Htot' & HC' & HE').
    eapply candidate_agreement_trans; [exact HE |].
    eapply candidate_agreement_trans; [ | exact (candidate_agreement_sym _ _ HE')].
    apply certified_candidate_agreement.
    apply sigma_candidate_agreement with (i := i).
    + exact (wf_sigma _ _ _ _ HA HB).
    + exact (wf_sigma _ _ _ _ HA' HB').
    + exact (certified_same_level_code_equality _ _ _ _ _ _ _ Hleft Hright').
    + intros Δ σ HW. exact (IHD _ _ HW (HD _ _ HW) _ _ (HD' _ _ HW)).
    + intros Δ σ HW N n b HN Hb.
      assert (HN' : R' Δ σ N n) by
        (apply (IHD _ _ HW (HD _ _ HW) _ _ (HD' _ _ HW)); exact HN).
      exact (IHC _ _ HW _ _ _ HN Hb (HC _ _ HW _ _ _ HN Hb) _ _ (HC' _ _ HW _ _ _ HN' Hb)).
  - exact (IHG HG _ _ Hright).
Qed.

Local Definition candidate_correspondence (Q : value_relation) (R S : value_candidate) :=
  forall M m n, Q m n -> (R M m <-> S M n).

Local Lemma certified_type_canonical i Γ A a :
  (exists R, certified_type i Γ A a R) ->
  certified_type i Γ A a (fun M m => exists R, certified_type i Γ A a R /\ R M m).
Proof.
  intros (R & HG).
  eapply certified_realization_layer_change_candidate; [exact HG |].
  intros M m. split.
  - intro HM. exists R. now split.
  - intros (S & HS & HM). now apply (certified_candidates_with_same_code _ _ _ _ _ HG _ _ HS).
Qed.

Local Lemma certified_member_of_canonical i Γ A a R M m :
  certified_type i Γ A a R ->
  (R M m <-> exists S, certified_type i Γ A a S /\ S M m).
Proof.
  intros H. split.
  - intro Hm. exists R. auto.
  - intros (S & HS & Hm). now apply (certified_candidates_with_same_code _ _ _ _ _ H _ _ HS).
Qed.

Local Lemma certified_codomain_canonical i Γ A ρ C n b R :
  eval_exp C (extend_env ρ n) b ->
  certified_type i Γ A b R ->
  candidates_equivalent R
    (fun M m => exists b' S, eval_exp C (extend_env ρ n) b' /\
      certified_type i Γ A b' S /\ S M m).
Proof.
  intros Hb HR M m. split.
  - intro HM. exists b, R. auto.
  - intros (b' & S & Hb' & HS & HM).
    pose proof (eval_exp_deterministic _ _ _ Hb _ Hb') as E. subst b'.
    now apply (certified_candidates_with_same_code _ _ _ _ _ HR _ _ HS).
Qed.

Local Lemma certified_dependence_transport Γ A B i a a' ρ ρ' C C' R S Q L :
  semantic_type i a a' Q ->
  (forall x y, Q x y -> exists b b',
    eval_exp C (extend_env ρ x) b /\ eval_exp C' (extend_env ρ' y) b') ->
  (forall x y b b', Q x y ->
    eval_exp C (extend_env ρ x) b ->
    eval_exp C' (extend_env ρ' y) b' ->
    semantic_type i b b' (L x y)) ->
  (forall Δ σ, weakening_between Γ Δ σ ->
    exists R', certified_type i Δ (a_sub A σ) a' R' /\
      candidate_correspondence Q (R Δ σ) R') ->
  (forall Δ σ, weakening_between Γ Δ σ ->
    forall N n b, R Δ σ N n -> eval_exp C (extend_env ρ n) b ->
    forall b' T, semantic_type i b b' T ->
    exists S', certified_type i Δ (a_sub B (a_extend σ N)) b' S' /\
      candidate_correspondence T (S Δ σ N n) S') ->
  exists R' : domain_candidate, exists S' : codomain_candidate,
    (forall Δ σ, weakening_between Γ Δ σ -> certified_type i Δ (a_sub A σ) a' (R' Δ σ)) /\
    (forall Δ σ, weakening_between Γ Δ σ ->
      forall N n, R' Δ σ N n -> exists b, eval_exp C' (extend_env ρ' n) b) /\
    (forall Δ σ, weakening_between Γ Δ σ ->
      forall N n b, R' Δ σ N n -> eval_exp C' (extend_env ρ' n) b ->
      certified_type i Δ (a_sub B (a_extend σ N)) b (S' Δ σ N n)) /\
    (forall Δ σ, weakening_between Γ Δ σ -> candidate_correspondence Q (R Δ σ) (R' Δ σ)) /\
    (forall Δ σ, weakening_between Γ Δ σ ->
      forall N n n' b b', R Δ σ N n ->
      Q n n' -> eval_exp C (extend_env ρ n) b -> eval_exp C' (extend_env ρ' n') b' ->
      candidate_correspondence (L n n') (S Δ σ N n) (S' Δ σ N n')).
Proof.
  intros HQ Htotal HL HD HC.
  set (R' := fun Δ σ M m =>
    exists T, certified_type i Δ (a_sub A σ) a' T /\ T M m).
  set (S' := fun Δ σ N n M m =>
    exists b T, eval_exp C' (extend_env ρ' n) b /\
      certified_type i Δ (a_sub B (a_extend σ N)) b T /\ T M m).
  assert (HR' : forall Δ σ, weakening_between Γ Δ σ -> certified_type i Δ (a_sub A σ) a' (R' Δ σ)).
  {
    intros Δ σ HW. destruct (HD _ _ HW) as (T & HT & _).
    apply certified_type_canonical. now exists T.
  }
  assert (HD' : forall Δ σ, weakening_between Γ Δ σ ->
    candidate_correspondence Q (R Δ σ) (R' Δ σ)).
  {
    intros Δ σ HW M m n Hmn.
    destruct (HD _ _ HW) as (T & HT & HE).
    specialize (HE M m n Hmn).
    pose proof (certified_member_of_canonical _ _ _ _ _ M n HT) as Hcan.
    fold (R' Δ σ M n) in Hcan. tauto.
  }
  assert (Hn : forall Δ σ, weakening_between Γ Δ σ -> forall N n,
    R' Δ σ N n -> Q n n /\ R Δ σ N n).
  {
    intros Δ σ HW N n HN.
    pose proof (certified_layer_member _ _ _ _ _ _ (HR' _ _ HW) _ _ HN) as Hmem.
    pose proof (semantic_member_in_relation _ _ _ _ _ (semantic_type_sym _ _ _ _ HQ) Hmem) as Hnn.
    split; [exact Hnn | now apply (HD' _ _ HW _ _ _ Hnn)].
  }
  exists R', S'. split; [exact HR' |].
  split.
  - intros Δ σ HW N n HN. destruct (Hn _ _ HW _ _ HN) as [Hnn _].
    destruct (Htotal _ _ Hnn) as (b & b' & _ & Hb'). now exists b'.
  - split.
    + intros Δ σ HW N n b' HN Hb'.
      destruct (Hn _ _ HW _ _ HN) as [Hnn HR].
      destruct (Htotal _ _ Hnn) as (b & b0 & Hb & _).
      destruct (HC _ _ HW _ _ _ HR Hb _ _ (HL _ _ _ _ Hnn Hb Hb')) as (T & HT & _).
      exact (certified_realization_layer_change_candidate _ _ _ _ _ _ _ HT
        (certified_codomain_canonical _ _ _ _ _ _ _ _ Hb' HT)).
    + split; [exact HD' |].
      intros Δ σ HW N n n' b b' HR Hnn' Hb Hb' M m m' Hmm'.
      destruct (HC _ _ HW _ _ _ HR Hb _ _ (HL _ _ _ _ Hnn' Hb Hb')) as (T & HT & HE).
      specialize (HE M m m' Hmm').
      pose proof (certified_codomain_canonical _ _ _ _ _ _ _ _ Hb' HT M m') as Hcan.
      fold (S' Δ σ N n' M m') in Hcan. tauto.
Qed.

Local Lemma certified_correspondence a b Q i R S :
  semantic_type i a b Q ->
  candidate_correspondence Q R S ->
  candidate_correspondence Q (certified_candidate a R) (certified_candidate b S).
Proof.
  intros HQ H M m n Hmn.
  specialize (H M m n Hmn).
  pose proof (semantic_member_left _ _ _ _ _ _ HQ Hmn) as HL.
  pose proof (semantic_member_right _ _ _ _ _ _ HQ Hmn) as HR.
  unfold certified_candidate. tauto.
Qed.

Local Lemma function_candidate_semantic_correspondence Γ A B ρ ρ' C C' R S R' S' Q L :
  (forall Δ σ, weakening_between Γ Δ σ ->
    forall N n, R Δ σ N n -> Q n n) ->
  (forall Δ σ, weakening_between Γ Δ σ ->
    forall N n, R' Δ σ N n -> Q n n) ->
  (forall Δ σ, weakening_between Γ Δ σ -> candidate_correspondence Q (R Δ σ) (R' Δ σ)) ->
  (forall x y, Q x y -> exists b b',
    eval_exp C (extend_env ρ x) b /\ eval_exp C' (extend_env ρ' y) b') ->
  (forall Δ σ, weakening_between Γ Δ σ ->
    forall N n n' b b', R Δ σ N n ->
    Q n n' -> eval_exp C (extend_env ρ n) b -> eval_exp C' (extend_env ρ' n') b' ->
    candidate_correspondence (L n n') (S Δ σ N n) (S' Δ σ N n')) ->
  candidate_correspondence (function_values_agree Q L)
    (function_candidate Γ A B ρ C R S) (function_candidate Γ A B ρ' C' R' S').
Proof.
  intros HV HV' HD Htotal HC F f f' Hf.
  split; intros [HF HA]; split; [exact HF | | exact HF |].
  - intros Δ σ HW N n HN.
    pose proof (HV' _ _ HW _ _ HN) as Hnn.
    pose proof (proj2 (HD _ _ HW _ _ _ Hnn) HN) as HNr.
    destruct (HA _ _ HW _ _ HNr) as (b & x & Hb & Hx & HS).
    destruct (Htotal _ _ Hnn) as (b0 & b' & _ & Hb').
    destruct (Hf _ _ Hnn) as (u & v & Hu & Hv & Huv).
    pose proof (eval_app_deterministic _ _ _ Hx _ Hu) as E. subst u.
    exists b', v. repeat split; try assumption.
    exact (proj1 (HC _ _ HW _ _ _ _ _ HNr Hnn Hb Hb' _ _ _ Huv) HS).
  - intros Δ σ HW N n HN.
    pose proof (HV _ _ HW _ _ HN) as Hnn.
    pose proof (proj1 (HD _ _ HW _ _ _ Hnn) HN) as HNr.
    destruct (HA _ _ HW _ _ HNr) as (b' & y & Hb' & Hy & HS).
    destruct (Htotal _ _ Hnn) as (b & b0 & Hb & _).
    destruct (Hf _ _ Hnn) as (u & v & Hu & Hv & Huv).
    pose proof (eval_app_deterministic _ _ _ Hy _ Hv) as E. subst v.
    exists b, u. repeat split; try assumption.
    exact (proj2 (HC _ _ HW _ _ _ _ _ HN Hnn Hb Hb' _ _ _ Huv) HS).
Qed.

Local Lemma sigma_candidate_semantic_correspondence Γ A B ρ ρ' C C' R S R' S' Q L :
  (forall Δ σ, weakening_between Γ Δ σ -> candidate_correspondence Q (R Δ σ) (R' Δ σ)) ->
  (forall x y, Q x y -> exists b b',
    eval_exp C (extend_env ρ x) b /\ eval_exp C' (extend_env ρ' y) b') ->
  (forall Δ σ, weakening_between Γ Δ σ ->
    forall N n n' b b', R Δ σ N n ->
    Q n n' -> eval_exp C (extend_env ρ n) b -> eval_exp C' (extend_env ρ' n') b' ->
    candidate_correspondence (L n n') (S Δ σ N n) (S' Δ σ N n')) ->
  candidate_correspondence (pair_values_agree Q L)
    (sigma_candidate Γ A B ρ C R S) (sigma_candidate Γ A B ρ' C' R' S').
Proof.
  intros HD Htotal HC P p p' (x & x' & y & y' & Hx & Hx' & Hy & Hy' & Hxx' & Hyy').
  split; intros [HP H]; split; [exact HP | | exact HP |].
  - intros Δ σ HW.
    destruct (H _ _ HW) as (u & v & b & Hu & Hv & Hb & HR & HS).
    pose proof (evaluation_fst_deterministic _ _ _ Hu Hx) as Ex. subst u.
    pose proof (eval_snd_deterministic _ _ Hv _ Hy) as Ey. subst v.
    destruct (Htotal _ _ Hxx') as (b0 & b' & _ & Hb').
    exists x', y', b'. repeat split; try assumption.
    + exact (proj1 (HD _ _ HW _ _ _ Hxx') HR).
    + exact (proj1 (HC _ _ HW _ _ _ _ _ HR Hxx' Hb Hb' _ _ _ Hyy') HS).
  - intros Δ σ HW.
    destruct (H _ _ HW) as (u & v & b' & Hu & Hv & Hb' & HR & HS).
    pose proof (evaluation_fst_deterministic _ _ _ Hu Hx') as Ex. subst u.
    pose proof (eval_snd_deterministic _ _ Hv _ Hy') as Ey. subst v.
    destruct (Htotal _ _ Hxx') as (b & b0 & Hb & _).
    pose proof (proj2 (HD _ _ HW _ _ _ Hxx') HR) as HNr.
    exists x, y, b. repeat split; try assumption.
    exact (proj2 (HC _ _ HW _ _ _ _ _ HNr Hxx' Hb Hb' _ _ _ Hyy') HS).
Qed.

Local Lemma natural_candidate_semantic_correspondence Γ :
  candidate_correspondence natural_values_agree (natural_candidate Γ) (natural_candidate Γ).
Proof.
  intros M m n H.
  split; intro HM; eapply natural_candidate_semantic_transport; try eassumption.
  exact (proj1 natural_values_per _ _ H).
Qed.

Local Lemma neutral_candidate_semantic_correspondence Γ A :
  candidate_correspondence neutral_values_agree (neutral_candidate Γ A) (neutral_candidate Γ A).
Proof.
  intros M m n (a & b & k & k' & -> & -> & Hkk').
  split; intros (HM & tag & l & HE & Hne).
  - injection HE as <- <-.
    split; [exact HM | exists b, k'; split; [reflexivity |]].
    exact (typed_neutral_readback_agreement _ _ _ _ _ Hkk' Hne).
  - injection HE as <- <-.
    split; [exact HM | exists a, k; split; [reflexivity |]].
    eapply typed_neutral_readback_agreement; [ | exact Hne].
    intro s. destruct (Hkk' s) as (N & Hl & Hr). exists N. auto.
Qed.

Local Lemma equation_candidate_semantic_correspondence Γ A P T R S Q p t :
  candidate_correspondence Q R S ->
  candidate_correspondence (equality_values_agree Q p t)
    (equation_candidate Γ A P T R) (equation_candidate Γ A P T S).
Proof.
  intros HE M m n Hrel.
  destruct Hrel as [Hne | (x & y & -> & -> & Hxy & _)].
  - destruct Hne as (a & b & k & k' & -> & -> & Hkk').
    split; intros (HM & [(tag & l & E & Hnr) | (N & z & E & _)]);
      try discriminate E; injection E as <- <-; split; [exact HM | | exact HM |].
    + left. exists b, k'. split; [reflexivity |].
      exact (typed_neutral_readback_agreement _ _ _ _ _ Hkk' Hnr).
    + left. exists a, k. split; [reflexivity |].
      eapply typed_neutral_readback_agreement; [ | exact Hnr].
      intro s. destruct (Hkk' s) as (N & Hl & Hr). exists N. auto.
  - split; intros (HM & [(tag & l & E & _) | (N & z & E & HN & ENP & ENT & EM)]);
      try discriminate E; injection E as <-; split; [exact HM | | exact HM |].
    + right. exists N, y. repeat split; try assumption. exact (proj1 (HE _ _ _ Hxy) HN).
    + right. exists N, x. repeat split; try assumption. exact (proj2 (HE _ _ _ Hxy) HN).
Qed.

Local Lemma candidate_correspondence_extensional Q R S R' S' :
  candidates_equivalent R R' ->
  candidates_equivalent S S' ->
  candidate_correspondence Q R' S' ->
  candidate_correspondence Q R S.
Proof.
  intros EL ER H M m n HQ. specialize (H M m n HQ).
  specialize (EL M m). specialize (ER M n). tauto.
Qed.

Local Lemma candidate_correspondence_relation Q L R S :
  relations_agree Q L ->
  candidate_correspondence L R S ->
  candidate_correspondence Q R S.
Proof. intros E H M m n HQ. apply H. now apply E. Qed.

Local Lemma semantic_universe_target i j b Q :
  semantic_type i (d_univ j) b Q ->
  b = d_univ j /\ relations_agree Q (fun m n => exists L, semantic_type j m n L).
Proof.
  intro H. inversion H; subst. split; [reflexivity |].
  exact (semantic_types_agree_on_left _ _ _ _ _ _ _ H (semantic_universe j i ltac:(lia))).
Qed.

Local Lemma semantic_natural_target i b Q :
  semantic_type i d_nat b Q ->
  b = d_nat /\ relations_agree Q natural_values_agree.
Proof. inversion 1; subst. auto. Qed.

Local Lemma semantic_neutral_target i a k b Q :
  semantic_type i (d_neut a k) b Q ->
  exists a' k', b = d_neut a' k' /\ neutrals_agree k k' /\ relations_agree Q neutral_values_agree.
Proof. inversion 1; subst. eauto. Qed.

Local Lemma semantic_equation_target i a p t b Q :
  semantic_type i (d_eq a p t) b Q ->
  exists a' p' t' L, b = d_eq a' p' t' /\
    semantic_type i a a' L /\ L p p' /\ L t t' /\ relations_agree Q (equality_values_agree L p t).
Proof.
  inversion 1; subst. do 4 eexists. split; [reflexivity |].
  repeat first [eassumption | split].
Qed.

Local Lemma semantic_function_target i a ρ C b Q :
  semantic_type i (d_pi a ρ C) b Q ->
  exists a' ρ' C', b = d_pi a' ρ' C'.
Proof. inversion 1; subst. eauto. Qed.

Local Lemma semantic_pair_target i a ρ C b Q :
  semantic_type i (d_sigma a ρ C) b Q ->
  exists a' ρ' C', b = d_sigma a' ρ' C'.
Proof. inversion 1; subst. eauto. Qed.

Local Lemma certified_type_transport i Γ A a R :
  certified_type i Γ A a R ->
  forall b Q, semantic_type i a b Q ->
    exists S, certified_type i Γ A b S /\ candidate_correspondence Q R S.
Proof.
  revert Γ A a R. induction i using lt_wf_ind.
  intros Γ A a R HG.
  induction HG as
    [Γ j R HΓ Hj HE
    |Γ R HΓ HE
    |Γ A a k R HA HR Hk HE
    |Γ A P T a p t R S HG IHG HP HT HE
    |Γ A B a ρ C R S T HA HB HD IHD Htot HC IHC Hsem HE
    |Γ A B a ρ C R S T HA HB HD IHD Htot HC IHC Hsem HE
    |Γ A B a R HG IHG HB HE]; intros z V HV.
  - destruct (semantic_universe_target _ _ _ _ HV) as (-> & EV).
    exists R. split; [exact (certify_universe _ _ _ _ _ HΓ Hj HE) |].
    eapply candidate_correspondence_extensional; [exact HE | exact HE |].
    eapply certified_correspondence; [exact HV |].
    intros M m n HVmn. apply EV in HVmn. destruct HVmn as (Q & HQ).
    unfold universe_candidate. split; intros (S & HS).
    + apply (proj1 (lower_certified_realization_lookup _ _ _ _ _ _ Hj)) in HS.
      destruct (H j Hj _ _ _ _ HS _ _ HQ) as (T & HT & _).
      exists T. now apply (proj2 (lower_certified_realization_lookup _ _ _ _ _ _ Hj)).
    + apply (proj1 (lower_certified_realization_lookup _ _ _ _ _ _ Hj)) in HS.
      destruct (H j Hj _ _ _ _ HS _ _ (semantic_type_sym _ _ _ _ HQ)) as (T & HT & _).
      exists T. now apply (proj2 (lower_certified_realization_lookup _ _ _ _ _ _ Hj)).
  - destruct (semantic_natural_target _ _ _ HV) as (-> & EV).
    exists R. split; [exact (certify_natural _ _ _ _ HΓ HE) |].
    eapply candidate_correspondence_extensional; [exact HE | exact HE |].
    eapply certified_correspondence; [exact HV |].
    eapply candidate_correspondence_relation; [exact EV | apply natural_candidate_semantic_correspondence].
  - destruct (semantic_neutral_target _ _ _ _ _ HV) as (a' & k' & -> & Hkk' & EV).
    exists (certified_candidate (d_neut a' k') (neutral_candidate Γ A)). split.
    + eapply certify_neutral; [exact HA | | | intros M m; reflexivity].
      * exact (shared_type_readback_transport _ _ _ _ _ _ _ HV HR).
      * intro s. destruct (Hkk' s) as (N & _ & HN). now exists N.
    + eapply candidate_correspondence_extensional; [exact HE | intros M m; reflexivity |].
      eapply certified_correspondence; [exact HV |].
      eapply candidate_correspondence_relation; [exact EV | apply neutral_candidate_semantic_correspondence].
  - destruct (semantic_equation_target _ _ _ _ _ _ HV) as (a' & p' & t' & Q & -> & HQ & Hpp' & Htt' & EV).
    destruct (IHG _ _ HQ) as (R' & HD' & HDRel).
    exists (certified_candidate (d_eq a' p' t') (equation_candidate Γ A P T R')). split.
    + eapply certify_equation; [exact HD' | | | intros M m; reflexivity].
      * exact (proj1 (HDRel _ _ _ Hpp') HP).
      * exact (proj1 (HDRel _ _ _ Htt') HT).
    + eapply candidate_correspondence_extensional; [exact HE | intros M m; reflexivity |].
      eapply certified_correspondence; [exact HV |].
      eapply candidate_correspondence_relation; [exact EV |].
      now apply equation_candidate_semantic_correspondence.
  - destruct (semantic_function_target _ _ _ _ _ _ HV) as (a' & ρ' & C' & ->).
    destruct (semantic_pi_inversion _ _ _ _ _ _ _ _ HV) as (Q & L & HQ & Htotal & HL & EV).
    destruct (certified_dependence_transport Γ A B i a a' ρ ρ' C C' R S Q L
      HQ Htotal HL (fun Δ σ HW => IHD Δ σ HW a' Q HQ) IHC) as (R' & S' & HD' & Htot' & HC' & HDR & HCR).
    exists (certified_candidate (d_pi a' ρ' C') (function_candidate Γ A B ρ' C' R' S')). split.
    + eapply certify_function; try eassumption.
      * exists V. exact (semantic_type_trans _ _ _ _ _ _ (semantic_type_sym _ _ _ _ HV) HV).
      * intros M m. reflexivity.
    + eapply candidate_correspondence_extensional; [exact HE | intros M m; reflexivity |].
      eapply certified_correspondence; [exact HV |].
      eapply candidate_correspondence_relation; [exact EV |].
      eapply function_candidate_semantic_correspondence; try eassumption.
      * intros Δ σ HW N n HN.
        exact (semantic_member_in_relation _ _ _ _ _ HQ
          (certified_layer_member _ _ _ _ _ _ (HD _ _ HW) _ _ HN)).
      * intros Δ σ HW N n HN.
        exact (semantic_member_in_relation _ _ _ _ _ (semantic_type_sym _ _ _ _ HQ)
          (certified_layer_member _ _ _ _ _ _ (HD' _ _ HW) _ _ HN)).
  - destruct (semantic_pair_target _ _ _ _ _ _ HV) as (a' & ρ' & C' & ->).
    destruct (semantic_sigma_inversion _ _ _ _ _ _ _ _ HV) as (Q & L & HQ & Htotal & HL & EV).
    destruct (certified_dependence_transport Γ A B i a a' ρ ρ' C C' R S Q L
      HQ Htotal HL (fun Δ σ HW => IHD Δ σ HW a' Q HQ) IHC) as (R' & S' & HD' & Htot' & HC' & HDR & HCR).
    exists (certified_candidate (d_sigma a' ρ' C') (sigma_candidate Γ A B ρ' C' R' S')). split.
    + eapply certify_sigma; try eassumption.
      * exists V. exact (semantic_type_trans _ _ _ _ _ _ (semantic_type_sym _ _ _ _ HV) HV).
      * intros M m. reflexivity.
    + eapply candidate_correspondence_extensional; [exact HE | intros M m; reflexivity |].
      eapply certified_correspondence; [exact HV |].
      eapply candidate_correspondence_relation; [exact EV |].
      eapply sigma_candidate_semantic_correspondence; eassumption.
  - destruct (IHG _ _ HV) as (S & HS & Hrel).
    exists S. split; [exact (certified_type_conversion _ _ _ _ _ _ HS HB HE) | exact Hrel].
Qed.
Local Lemma certified_candidate_expression_conversion i Γ A a R :
  certified_type i Γ A a R ->
  forall M N m, {{ Γ ⊢ N : A }} -> {{ Γ ⊢ N ≈ M : A }} -> R M m -> R N m.
Proof.
  intro H. pose proof H as Hreal. revert Hreal.
  induction H as
    [Γ j R HΓ Hj HE
    |Γ R HΓ HE
    |Γ A a k R HA HR Hk HE
    |Γ A P Q a p qv R S HG IHG HP HQ HE
    |Γ A B a ρ C R S T HA HB HD IHD Htot HC IHC Hsem HE
    |Γ A B a ρ C R S T HA HB HD IHD Htot HC IHC Hsem HE
    |Γ A B a R HG IHG HB HE];
    intros Hreal M N m HN EN HM.
  - apply HE in HM. apply HE. destruct HM as [Hgood HM]. split; [exact Hgood |].
    destruct HM as (S & HS). exists S.
    apply (proj1 (lower_certified_realization_lookup _ _ _ _ _ _ Hj)) in HS.
    apply (proj2 (lower_certified_realization_lookup _ _ _ _ _ _ Hj)).
    exact (certified_type_conversion _ _ _ _ _ _ HS HN (wf_exp_eq_sym _ _ _ _ EN)).
  - apply HE in HM. apply HE. split; [exact (proj1 HM) |].
    exact (natural_candidate_expression_conversion _ _ _ _ HN EN (proj2 HM)).
  - apply HE in HM. apply HE. destruct HM as [Hgood HM]. split; [exact Hgood |].
    destruct HM as (_ & tag & k' & -> & Hk').
    split; [exact HN | exists tag, k'; split; [reflexivity |]].
    exact (typed_readback_expression_conversion _ _ _ _ _ _ _ _ _ EN Hk').
  - apply HE in HM. apply HE. destruct HM as [Hgood HM]. split; [exact Hgood |].
    split; [exact HN |].
    destruct HM as (_ & [(tag & k & -> & Hk) | (T & n & -> & HT & ETP & ETQ & EM)]).
    + left. exists tag, k. split; [reflexivity |].
      exact (typed_readback_expression_conversion _ _ _ _ _ _ _ _ _ EN Hk).
    + right. exists T, n. repeat split; try assumption.
      exact (wf_exp_eq_trans _ _ _ _ _ EN EM).
  - apply HE in HM. apply HE. destruct HM as [Hgood HM]. split; [exact Hgood |].
    destruct HM as (_ & H).
    split; [exact HN |].
    intros Δ σ HW P p HP.
    destruct (H _ _ HW _ _ HP) as (b & m' & Hb & Hm' & Hout).
    pose proof (weakening_between_typed _ _ _ HW) as HS.
    pose proof (proj2 (proj1 (certified_type_properties _ _ _ _ _ (HD _ _ HW))) _ _ HP) as HPt.
    pose proof (proj2 (apply_substituted_function _ _ _ _ _ _ _ _ HS HA HB HN HPt)) as Houtt.
    pose proof (substituted_application_equality _ _ _ _ _ _ _ _ _
      HS HA HB EN HPt) as Eout.
    exists b, m'. split; [exact Hb | split; [exact Hm' |]].
    exact (IHC _ _ HW _ _ _ HP Hb (HC _ _ HW _ _ _ HP Hb) _ _ _ Houtt Eout Hout).
  - apply HE in HM. apply HE. destruct HM as [Hgood HM]. split; [exact Hgood |].
    destruct HM as (HM & H).
    split; [exact HN |].
    intros Δ σ HW.
    destruct (H _ _ HW) as (x & y & b & Hx & Hy & Hb & HR & HS).
    pose proof (weakening_between_typed _ _ _ HW) as Hσ.
    destruct (substituted_pair_components _ _ _ _ _ _ _ Hσ HA HB HN) as (HF & HT & HSn).
    destruct (substituted_pair_components _ _ _ _ _ _ _ Hσ HA HB HM) as (_ & HT' & _).
    destruct (substituted_pair_equality _ _ _ _ _ _ _ _
      Hσ HA HB HN HM EN) as (EF & ET & ESn).
    pose proof (IHD _ _ HW (HD _ _ HW) _ _ _ HF EF HR) as HR'.
    pose proof (HC _ _ HW _ _ _ HR Hb) as HGold.
    pose proof (HC _ _ HW _ _ _ HR' Hb) as HGnew.
    pose proof (certified_type_conversion _ _ _ _ _ _ HGold HT (wf_exp_eq_sym _ _ _ _ ET)) as HGcast.
    pose proof (certified_candidates_with_same_code _ _ _ _ _ HGcast _ _ HGnew) as HCand.
    exists x, y, b. repeat split; try assumption.
    apply HCand.
    exact (IHC _ _ HW _ _ _ HR Hb HGold _ _ _
      (convert_term _ _ _ _ _ HSn HT' ET)
      (convert_equality _ _ _ _ _ _ ESn HT' ET) HS).
  - destruct (proj1 (certified_type_properties _ _ _ _ _ HG)) as [HA _].
    pose proof (wf_exp_eq_sym _ _ _ _ HE) as HE'.
    apply (IHG HG M N m); [eapply convert_term | eapply convert_equality | exact HM]; eassumption.
Qed.


Local Lemma reindex_certified_binder_domain i Γ Δ σ A a R :
  {{ Γ ⊢ A : Type@i }} ->
  weakening_between Γ Δ σ ->
  (forall Θ τ, weakening_between Γ Θ τ ->
    certified_type i Θ (a_sub A τ) a (R Θ τ)) ->
  forall Θ τ, weakening_between Δ Θ τ ->
    certified_type i Θ (a_sub (a_sub A σ) τ) a (R Θ (a_compose σ τ)).
Proof.
  intros HA HW HD Θ τ HT.
  pose proof (weakening_between_typed _ _ _ HW) as Hσ.
  pose proof (weakening_between_typed _ _ _ HT) as Hτ.
  eapply certified_type_conversion.
  - exact (HD _ _ (weakening_between_composition _ _ _ _ _ HW HT)).
  - exact (type_substitution _ _ _ _ _ Hτ (type_substitution _ _ _ _ _ Hσ HA)).
  - exact (type_substitution_composition _ _ _ _ _ _ _ Hτ Hσ HA).
Qed.

Local Lemma reindex_certified_binder_codomain i Γ Δ σ A B a ρ C R S :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  weakening_between Γ Δ σ ->
  (forall Θ τ, weakening_between Γ Θ τ ->
    certified_type i Θ (a_sub A τ) a (R Θ τ)) ->
  (forall Θ τ, weakening_between Γ Θ τ -> forall N n b,
    R Θ τ N n -> eval_exp C (extend_env ρ n) b ->
    certified_type i Θ (a_sub B (a_extend τ N)) b (S Θ τ N n)) ->
  forall Θ τ, weakening_between Δ Θ τ -> forall N n b,
    R Θ (a_compose σ τ) N n -> eval_exp C (extend_env ρ n) b ->
    certified_type i Θ (a_sub (a_sub B (Syntax.q σ)) (a_extend τ N)) b
      (S Θ (a_compose σ τ) N n).
Proof.
  intros HA HB HW HD HC Θ τ HT N n b HR Hb.
  pose proof (weakening_between_composition _ _ _ _ _ HW HT) as Hcomp.
  pose proof (weakening_between_typed _ _ _ HW) as Hσ.
  pose proof (weakening_between_typed _ _ _ HT) as Hτ.
  pose proof (reindex_certified_binder_domain _ _ _ _ _ _ _ HA HW HD _ _ HT) as HD'.
  pose proof (proj2 (proj1 (certified_type_properties _ _ _ _ _ HD')) _ _ HR) as HN.
  pose proof (type_substitution _ _ _ _ _ Hσ HA) as HAs.
  pose proof (wf_sub_extend _ _ _ _ _ _ Hτ HAs HN) as HτN.
  pose proof (lifted_substitution _ _ _ _ _ Hσ HA) as HQ.
  pose proof (type_substitution _ _ _ _ _ HτN (type_substitution _ _ _ _ _ HQ HB)) as HB'.
  exact (certified_type_conversion _ _ _ _ _ _ (HC _ _ Hcomp _ _ _ HR Hb) HB'
    (wf_exp_eq_sym _ _ _ _ (type_lifted_substitution_at_argument _ _ _ _ _ _ _ _ _ _
      Hσ Hτ HA HB HN))).
Qed.

Local Lemma certified_function_candidate_weakening Γ Δ σ A B a ρ C i R S :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  weakening_between Γ Δ σ ->
  (forall Θ τ, weakening_between Γ Θ τ ->
    certified_type i Θ (a_sub A τ) a (R Θ τ)) ->
  (forall Θ τ, weakening_between Γ Θ τ -> forall N n b,
    R Θ τ N n -> eval_exp C (extend_env ρ n) b ->
    certified_type i Θ (a_sub B (a_extend τ N)) b (S Θ τ N n)) ->
  forall F f,
    function_candidate Γ A B ρ C R S F f ->
    function_candidate Δ (a_sub A σ) (a_sub B (Syntax.q σ)) ρ C
      (fun Θ τ => R Θ (a_compose σ τ))
      (fun Θ τ => S Θ (a_compose σ τ))
      (a_sub F σ) f.
Proof.
  intros HA HB HW HD HC F f (HF & H).
  pose proof (weakening_between_typed _ _ _ HW) as Hσ.
  pose proof (type_substitution _ _ _ _ _ Hσ HA) as HAs.
  pose proof (type_substitution _ _ _ _ _ (lifted_substitution _ _ _ _ _ Hσ HA) HB) as HBs.
  pose proof (convert_term _ _ _ _ _ (wf_exp_sub _ _ _ _ _ Hσ HF)
    (wf_pi _ _ _ _ HAs HBs) (wf_exp_eq_pi_sub _ _ _ _ _ _ Hσ HA HB)) as HFσ.
  split; [exact HFσ |].
  intros Θ τ HT N n HR.
  pose proof (weakening_between_composition _ _ _ _ _ HW HT) as Hcomp.
  pose proof (weakening_between_typed _ _ _ HT) as Hτ.
  pose proof (proj2 (proj1 (certified_type_properties _ _ _ _ _ (HD _ _ Hcomp))) _ _ HR) as HN.
  destruct (H _ _ Hcomp _ _ HR) as (b & r & Hb & Happ & Hmem).
  pose proof (reindex_certified_binder_domain _ _ _ _ _ _ _ HA HW HD _ _ HT) as HD'.
  pose proof (proj2 (proj1 (certified_type_properties _ _ _ _ _ HD')) _ _ HR) as HN'.
  pose proof (reindex_certified_binder_codomain _ _ _ _ _ _ _ _ _ _ _ HA HB HW HD HC
    _ _ HT _ _ _ HR Hb) as HCod'.
  destruct (apply_substituted_function _ _ _ _ _ _ _ _ Hτ HAs HBs HFσ HN') as (HB' & HApp').
  pose proof (application_under_iterated_weakening _ _ _ _ _ _ _ _ _ _ Hσ Hτ HA HB HF HN) as Eapp.
  pose proof (wf_exp_eq_sym _ _ _ _ (type_lifted_substitution_at_argument _ _ _ _ _ _ _ _ _ _
    Hσ Hτ HA HB HN')) as EB.
  exists b, r. split; [exact Hb | split; [exact Happ |]].
  exact (certified_candidate_expression_conversion _ _ _ _ _ HCod' _ _ _ HApp'
    (convert_equality _ _ _ _ _ _ Eapp HB' EB) Hmem).
Qed.


Local Lemma certified_sigma_candidate_weakening Γ Δ σ A B a ρ C i R S :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  weakening_between Γ Δ σ ->
  (forall Θ τ, weakening_between Γ Θ τ ->
    certified_type i Θ (a_sub A τ) a (R Θ τ)) ->
  (forall Θ τ, weakening_between Γ Θ τ -> forall N n b,
    R Θ τ N n -> eval_exp C (extend_env ρ n) b ->
    certified_type i Θ (a_sub B (a_extend τ N)) b (S Θ τ N n)) ->
  forall P p,
    sigma_candidate Γ A B ρ C R S P p ->
    sigma_candidate Δ (a_sub A σ) (a_sub B (Syntax.q σ)) ρ C
      (fun Θ τ => R Θ (a_compose σ τ))
      (fun Θ τ => S Θ (a_compose σ τ))
      (a_sub P σ) p.
Proof.
  intros HA HB HW HD HC P p (HP & H).
  pose proof (weakening_between_typed _ _ _ HW) as Hσ.
  pose proof (type_substitution _ _ _ _ _ Hσ HA) as HAs.
  pose proof (type_substitution _ _ _ _ _ (lifted_substitution _ _ _ _ _ Hσ HA) HB) as HBs.
  pose proof (convert_term _ _ _ _ _ (wf_exp_sub _ _ _ _ _ Hσ HP)
    (wf_sigma _ _ _ _ HAs HBs) (wf_exp_eq_sigma_sub _ _ _ _ _ _ Hσ HA HB)) as HPσ.
  split; [exact HPσ |].
  intros Θ τ HT.
  pose proof (weakening_between_composition _ _ _ _ _ HW HT) as Hcomp.
  pose proof (weakening_between_typed _ _ _ HT) as Hτ.
  destruct (H _ _ Hcomp) as (x & y & b & Hx & Hy & Hb & HR & HS).
  destruct (pair_projections_under_iterated_weakening _ _ _ _ _ _ _ _ _
    Hσ Hτ HA HB HP) as (HF & EF & HSn & ESn).
  pose proof (certified_candidate_expression_conversion _ _ _ _ _ (HD _ _ Hcomp)
    _ _ _ HF EF HR) as HR'.
  pose proof (HC _ _ Hcomp _ _ _ HR Hb) as HG.
  pose proof (HC _ _ Hcomp _ _ _ HR' Hb) as HG'.
  pose proof (certified_candidates_with_same_code _ _ _ _ _ HG _ _ HG') as EqS.
  pose proof (proj1 (EqS _ _) HS) as HS'.
  exists x, y, b. repeat split; try assumption.
  exact (certified_candidate_expression_conversion _ _ _ _ _ HG' _ _ _ HSn ESn HS').
Qed.

Local Lemma certified_type_weakening i Γ A a R :
  certified_type i Γ A a R ->
  forall Δ σ, weakening_between Γ Δ σ ->
    exists S, certified_type i Δ (a_sub A σ) a S /\
      (forall M m, R M m -> S (a_sub M σ) m).
Proof.
  revert Γ A a R. induction i using lt_wf_ind.
  intros Γ A a R HG.
  induction HG as
    [Γ j R HΓ Hj HE
    |Γ R HΓ HE
    |Γ A a k R HA HR Hk HE
    |Γ A P Q a p qv R S HG IHG HP HQ HE
    |Γ A B a ρ C R S T HA HB HD IHD Htot HC IHC Hsem HE
    |Γ A B a ρ C R S T HA HB HD IHD Htot HC IHC Hsem HE
    |Γ A B a R HG IHG HB HE];
    intros Δ σ HW;
    pose proof (weakening_between_typed _ _ _ HW) as Hσ;
    pose proof (substitution_source _ _ _ Hσ) as HΔ.
  - exists (certified_candidate (d_univ j) (universe_candidate (lower_certified_realizations i) j Δ)). split.
    + pose proof (type_cumulativity _ _ (S j) i (wf_typ _ j HΓ) ltac:(lia)) as HU.
      eapply certified_type_conversion.
      * apply certify_universe; [exact HΔ | exact Hj | intros M m; reflexivity].
      * exact (type_substitution _ _ _ _ _ Hσ HU).
      * exact (equality_cumulativity _ _ _ (S j) i
          (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_typ_sub _ _ _ j Hσ)) HΔ ltac:(lia)).
    + intros M m HM. apply HE in HM.
      destruct HM as (Hgood & S & HS). split; [exact Hgood |].
      apply (proj1 (lower_certified_realization_lookup _ _ _ _ _ _ Hj)) in HS.
      destruct (H _ Hj _ _ _ _ HS _ _ HW) as (T & HT & _).
      exists T. now apply (proj2 (lower_certified_realization_lookup _ _ _ _ _ _ Hj)).
  - exists (certified_candidate d_nat (natural_candidate Δ)). split.
    + eapply certified_type_conversion.
      * apply certify_natural; [exact HΔ | intros M m; reflexivity].
      * exact (type_cumulativity _ _ _ _
          (type_substitution _ _ _ _ _ Hσ (wf_nat _ HΓ)) (Nat.le_0_l i)).
      * exact (equality_cumulativity _ _ _ 0 i
          (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ Hσ)) HΔ (Nat.le_0_l i)).
    + intros M m HM. apply HE in HM. split; [exact (proj1 HM) |].
      exact (natural_candidate_weakening _ _ _ _ _ HW (proj2 HM)).
  - exists (certified_candidate (d_neut a k) (neutral_candidate Δ (a_sub A σ))). split.
    + eapply certify_neutral.
      * exact (type_substitution _ _ _ _ _ Hσ HA).
      * eapply typed_readback_type_conversion.
        -- exact (wf_typ _ _ HΔ).
        -- exact (wf_exp_eq_typ_sub _ _ _ _ Hσ).
        -- exact (typed_readback_under_weakening _ _ _ _ _ _ _ _ _ _ _
            (wf_typ _ _ (typing_context _ _ _ HA)) HA HW HR).
      * exact Hk.
      * intros M m. reflexivity.
    + intros M m HM. apply HE in HM. split; [exact (proj1 HM) |].
      exact (neutral_candidate_weakening _ _ _ _ _ _ _ HA HW (proj2 HM)).
  - destruct (IHG _ _ HW) as (R' & HD & Hmem).
    destruct (proj1 (certified_type_properties _ _ _ _ _ HG)) as [HA HTyped].
    pose proof (HTyped _ _ HP) as HPt.
    pose proof (HTyped _ _ HQ) as HQt.
    pose proof (wf_eq _ _ _ _ _ HA HPt HQt) as HT.
    pose proof (wf_exp_eq_eq_sub _ _ _ _ _ _ _ Hσ HA HPt HQt) as ET.
    exists (certified_candidate (d_eq a p qv) (equation_candidate Δ (a_sub A σ) (a_sub P σ) (a_sub Q σ) R')). split.
    + eapply certified_type_conversion.
      * eapply certify_equation; [exact HD | exact (Hmem _ _ HP) | exact (Hmem _ _ HQ) |].
        intros M m. reflexivity.
      * exact (type_substitution _ _ _ _ _ Hσ HT).
      * exact (wf_exp_eq_sym _ _ _ _ ET).
    + intros M m HM. apply HE in HM. split; [exact (proj1 HM) |].
      exact (equation_candidate_weakening _ _ _ _ _ _ _ _ _ HA HPt HQt HW HTyped Hmem
        _ _ (proj2 HM)).
  - pose (R' := fun Θ τ => R Θ (a_compose σ τ)).
    pose (S' := fun Θ τ => S Θ (a_compose σ τ)).
    pose proof (type_substitution _ _ _ _ _ Hσ HA) as HAs.
    pose proof (type_substitution _ _ _ _ _ (lifted_substitution _ _ _ _ _ Hσ HA) HB) as HBs.
    exists (certified_candidate (d_pi a ρ C) (function_candidate Δ (a_sub A σ) (a_sub B (Syntax.q σ)) ρ C R' S')). split.
    + eapply certified_type_conversion.
      * eapply certify_function with (R := R') (S := S').
        -- exact HAs.
        -- exact HBs.
        -- exact (reindex_certified_binder_domain _ _ _ _ _ _ _ HA HW HD).
        -- intros Θ τ Hτ N n HR. exact (Htot _ _
             (weakening_between_composition _ _ _ _ _ HW Hτ) _ _ HR).
        -- exact (reindex_certified_binder_codomain _ _ _ _ _ _ _ _ _ _ _ HA HB HW HD HC).
        -- exact Hsem.
        -- intros M m. reflexivity.
      * exact (type_substitution _ _ _ _ _ Hσ (wf_pi _ _ _ _ HA HB)).
      * exact (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_pi_sub _ _ _ _ _ _ Hσ HA HB)).
    + intros M m HM. apply HE in HM. split; [exact (proj1 HM) |].
      exact (certified_function_candidate_weakening _ _ _ _ _ _ _ _ _ _ _ HA HB HW HD HC _ _
        (proj2 HM)).
  - pose (R' := fun Θ τ => R Θ (a_compose σ τ)).
    pose (S' := fun Θ τ => S Θ (a_compose σ τ)).
    pose proof (type_substitution _ _ _ _ _ Hσ HA) as HAs.
    pose proof (type_substitution _ _ _ _ _ (lifted_substitution _ _ _ _ _ Hσ HA) HB) as HBs.
    exists (certified_candidate (d_sigma a ρ C) (sigma_candidate Δ (a_sub A σ) (a_sub B (Syntax.q σ)) ρ C R' S')). split.
    + eapply certified_type_conversion.
      * eapply certify_sigma with (R := R') (S := S').
        -- exact HAs.
        -- exact HBs.
        -- exact (reindex_certified_binder_domain _ _ _ _ _ _ _ HA HW HD).
        -- intros Θ τ Hτ N n HR. exact (Htot _ _
             (weakening_between_composition _ _ _ _ _ HW Hτ) _ _ HR).
        -- exact (reindex_certified_binder_codomain _ _ _ _ _ _ _ _ _ _ _ HA HB HW HD HC).
        -- exact Hsem.
        -- intros M m. reflexivity.
      * exact (type_substitution _ _ _ _ _ Hσ (wf_sigma _ _ _ _ HA HB)).
      * exact (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_sigma_sub _ _ _ _ _ _ Hσ HA HB)).
    + intros M m HM. apply HE in HM. split; [exact (proj1 HM) |].
      exact (certified_sigma_candidate_weakening _ _ _ _ _ _ _ _ _ _ _ HA HB HW HD HC _ _
        (proj2 HM)).
  - destruct (IHG _ _ HW) as (S & HS & Hmem).
    exists S. split; [| exact Hmem].
    exact (certified_type_conversion _ _ _ _ _ _ HS
      (type_substitution _ _ _ _ _ Hσ HB)
      (type_substitution_congruence _ _ _ _ _ _ _ Hσ
        (substitution_equality_reflexive _ _ _ Hσ) HE)).
Qed.

Local Definition has_certified_realization Γ A M a m :=
  exists i R, certified_type i Γ A a R /\ R M m.

Local Definition uniform_certified_realization : term_realization :=
  fun Γ A M a m => forall Δ σ, context_weakening Γ Δ σ ->
    has_certified_realization Δ (a_sub A σ) (a_sub M σ) a m.

Local Lemma has_certified_realization_typing Γ A M a m :
  has_certified_realization Γ A M a m -> {{ Γ ⊢ M : A }}.
Proof.
  intros (i & R & HG & HM).
  exact (proj2 (proj1 (certified_type_properties _ _ _ _ _ HG)) _ _ HM).
Qed.

Local Lemma has_certified_realization_type_conversion :
  realization_type_conversion has_certified_realization.
Proof.
  intros Γ A B M a m j HB HE (i & R & HG & HM).
  pose proof (proj1 (proj1 (certified_type_properties _ _ _ _ _ HG))) as HA.
  pose proof (typing_context _ _ _ HA) as HΓ.
  exists (Nat.max i j), R. split; [| exact HM].
  eapply certified_type_conversion with (A := A).
  - exact (certified_type_raise _ _ _ _ _ _ (Nat.le_max_l _ _) HG).
  - exact (type_cumulativity _ _ _ _ HB (Nat.le_max_r _ _)).
  - exact (equality_cumulativity _ _ _ _ _ HE HΓ (Nat.le_max_r _ _)).
Qed.

Local Lemma has_certified_realization_term_conversion :
  realization_term_conversion has_certified_realization.
Proof.
  intros Γ A M N a m HN EN (i & R & HG & HM).
  exists i, R. split; [exact HG |].
  exact (certified_candidate_expression_conversion _ _ _ _ _ HG _ _ _ HN EN HM).
Qed.

Local Lemma uniform_certified_realization_at_identity Γ A M a m i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  uniform_certified_realization Γ A M a m -> has_certified_realization Γ A M a m.
Proof.
  intros HA HM H.
  specialize (H _ _ (context_weakening_id _ (typing_context _ _ _ HA))).
  pose proof (wf_exp_eq_sub_id _ _ _ HA) as EA.
  eapply has_certified_realization_term_conversion; [exact HM | |].
  - apply wf_exp_eq_sym, wf_exp_eq_sub_id. exact HM.
  - exact (has_certified_realization_type_conversion _ _ _ _ _ _ _ HA EA H).
Qed.

Local Lemma uniform_certified_realization_readback Γ A M a m :
  uniform_certified_realization Γ A M a m -> typed_value_readback Γ A M a m.
Proof.
  intros H Δ σ HW.
  destruct (H _ _ HW) as (i & R & HG & HM).
  destruct (proj1 (certified_type_properties _ _ _ _ _ HG)) as (HA & HT).
  eapply typed_readback_here; [exact HA | exact (HT _ _ HM) |].
  exact (certified_term_readback _ _ _ _ _ _ _ HG HM).
Qed.

Local Lemma uniform_certified_realization_type_conversion :
  realization_type_conversion uniform_certified_realization.
Proof.
  intros Γ A B M a m i HB HE H Δ σ HW.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  eapply has_certified_realization_type_conversion.
  - exact (type_substitution _ _ _ _ _ HS HB).
  - exact (type_substitution_congruence _ _ _ _ _ _ _ HS
      (substitution_equality_reflexive _ _ _ HS) HE).
  - exact (H _ _ HW).
Qed.

Local Lemma uniform_certified_realization_term_conversion :
  realization_term_conversion uniform_certified_realization.
Proof.
  intros Γ A M N a m HN EN H Δ σ HW.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  eapply has_certified_realization_term_conversion.
  - exact (wf_exp_sub _ _ _ _ _ HS HN).
  - exact (equality_under_substitution _ _ _ _ _ _ HS EN).
  - exact (H _ _ HW).
Qed.

Local Lemma uniform_certified_realization_under_weakening :
  realization_weakening uniform_certified_realization.
Proof.
  intros Γ Δ σ A M a m i Hσ HA HM H Θ τ Hτ.
  destruct (context_weakening_compose _ _ _ _ _ Hσ Hτ) as (ω & Hω & HE).
  pose proof (context_weakening_typed _ _ _ Hσ) as HS.
  pose proof (context_weakening_typed _ _ _ Hτ) as HT.
  pose proof (wf_sub_compose _ _ _ _ _ HT HS) as HST.
  pose proof (type_substitution _ _ _ _ _ HST HA) as HAsc.
  pose proof (type_substitution_equality_same_body _ _ _ _ _ _ HST HE HA) as EAc.
  pose proof (wf_exp_eq_sub_cong _ _ _ _ _ _ _
    (expression_equality_reflexive _ _ _ HM) HE) as EMc.
  eapply realized_environment_compose_action; try eassumption;
    try exact has_certified_realization_type_conversion; try exact has_certified_realization_term_conversion.
  eapply has_certified_realization_term_conversion.
  - exact (wf_exp_sub _ _ _ _ _ HST HM).
  - exact EMc.
  - exact (has_certified_realization_type_conversion _ _ _ _ _ _ _ HAsc
      (wf_exp_eq_sym _ _ _ _ EAc) (H _ _ Hω)).
Qed.

Local Lemma nominal_certified_realization_under_weakening Γ Δ σ A M a m i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  weakening_between Γ Δ σ ->
  uniform_certified_realization Γ A M a m ->
  has_certified_realization Δ (a_sub A σ) (a_sub M σ) a m.
Proof.
  intros HA HM (τ & Hτ & HS & HE) H.
  pose proof (context_weakening_typed _ _ _ Hτ) as HT.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAt.
  pose proof (type_substitution_equality_same_body _ _ _ _ _ _ HS HE HA) as HEA.
  pose proof (wf_exp_eq_sub_cong _ _ _ _ _ _ _
    (expression_equality_reflexive _ _ _ HM) HE) as HEM.
  eapply has_certified_realization_term_conversion.
  - exact (wf_exp_sub _ _ _ _ _ HS HM).
  - exact HEM.
  - exact (has_certified_realization_type_conversion _ _ _ _ _ _ _ HAt
      (wf_exp_eq_sym _ _ _ _ HEA) (H _ _ Hτ)).
Qed.

Local Lemma certified_type_of_universe_member Γ M m i j R :
  certified_type j Γ (a_typ i) (d_univ i) R ->
  R M m ->
  exists S, certified_type i Γ M m S.
Proof.
  intros HG HM.
  pose proof (certified_universe_view _ _ _ _ _ HG M m) as Hview.
  apply Hview in HM.
  destruct (certified_realization_layer_expose_head _ _ _ _ _ _ HG) as (B & HB).
  inversion HB; subst.
  destruct HM as (_ & S & HS).
  exists S. now apply lower_certified_realization_lookup in HS.
Qed.

Local Lemma uniform_certified_realization_type_witness Γ Δ σ A i a :
  {{ Γ ⊢ A : Type@i }} ->
  weakening_between Γ Δ σ ->
  uniform_certified_realization Γ (a_typ i) A (d_univ i) a ->
  exists R, certified_type i Δ (a_sub A σ) a R.
Proof.
  intros HA HW H.
  assert (HU : {{ Γ ⊢ Type@i : Type@(S i) }}) by eauto using wf_typ, typing_context.
  destruct (nominal_certified_realization_under_weakening _ _ _ _ _ _ _ _ HU HA HW H)
    as (j & R & HG & HR).
  pose proof (weakening_between_typed _ _ _ HW) as HS.
  pose proof (wf_typ Δ i (substitution_source _ _ _ HS)) as HT.
  pose proof (wf_exp_eq_typ_sub _ _ _ i HS) as HE.
  destruct (has_certified_realization_type_conversion _ _ _ _ _ _ _ HT HE
    (ex_intro _ j (ex_intro _ R (conj HG HR)))) as (k & S & HG' & HR').
  exact (certified_type_of_universe_member _ _ _ _ _ _ HG' HR').
Qed.

Local Lemma uniform_certified_realization_reflection Γ A M i a k :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  uniform_certified_realization Γ (a_typ i) A (d_univ i) a ->
  typed_neutral_readback Γ A M k ->
  neutrals_agree k k ->
  uniform_certified_realization Γ A M a (d_neut a k).
Proof.
  intros HA HM Htype Hne Hkk Δ σ HW.
  destruct (uniform_certified_realization_type_witness _ _ _ _ _ _ HA
      (weakening_between_canonical _ _ _ HW) Htype) as (R & HG).
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  exists i, R. split; [exact HG |].
  eapply certified_reflection; [exact HG | exact (wf_exp_sub _ _ _ _ _ HS HM) | | exact Hkk].
  eapply typed_readback_weakening; [exact HA | exact HM | exact HW | exact Hne].
Qed.

Local Definition certifies_typed_term Γ A M :=
  forall Δ σ ρ, realizes_environment uniform_certified_realization Δ Γ σ ρ ->
    exists a m, eval_exp A ρ a /\ eval_exp M ρ m /\
      uniform_certified_realization Δ (a_sub A σ) (a_sub M σ) a m.

Local Definition uniform_certified_typing_interpretation :=
  forall Γ A M, wf_exp Γ A M -> certifies_typed_term Γ A M.

Local Lemma uniform_certified_initial_environment :
  uniform_certified_typing_interpretation ->
  forall Γ ρ, wf_ctx Γ -> initial_env Γ ρ ->
    realizes_environment uniform_certified_realization Γ Γ a_id ρ.
Proof.
  intros Hfund Γ ρ HΓ Hρ.
  revert HΓ.
  induction Hρ as [|Γ ρ A a Hρ IH Ha]; intro Hctx.
  - apply realized_environment_empty. now apply wf_sub_id.
  - inversion Hctx as [| Γ' A' i HΓ HA]; subst.
    pose proof (IH HΓ) as Henv.
    assert (Hσ : {{ Γ, A ⊢s Wk : Γ }}) by now apply wf_sub_weaken.
    assert (Hid : {{ Γ, A ⊢s Id : Γ, A }}) by now apply wf_sub_id.
    pose proof (wf_sub_eq_id_compose_right _ _ _ Hσ) as Eσ.
    pose proof (context_weakening_step _ _ _ _ _ (context_weakening_id Γ HΓ) HA) as HW.
    pose proof (realized_environment_weaken _ _ _ _ _ _ _
      uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
      uniform_certified_realization_under_weakening Henv HW) as Henv_w.
    assert (Eσw : {{ Γ, A ⊢s Id∘(Id∘Wk) ≈ Wk : Γ }}) by
      (eapply wf_sub_eq_trans; [apply wf_sub_eq_id_compose_right;
        exact (context_weakening_typed _ _ _ HW) | exact Eσ]).
    pose proof (realized_environment_substitution_conversion _ _ _ _ _ _
      uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
      Henv_w Hσ Eσw) as Henv_σ.
    destruct (Hfund _ _ _ HA _ _ _ Henv_σ) as (u & a' & Hu & Ha' & Htype).
    pose proof (eval_exp_deterministic _ _ _ Ha _ Ha'). subst a'.
    inversion Hu; subst.
    pose proof (type_substitution _ _ _ _ _ Hσ HA) as HAw.
    pose proof (uniform_certified_realization_type_conversion _ _ _ _ _ _ _
      (wf_typ _ _ Hctx) (wf_exp_eq_typ_sub _ _ _ _ Hσ) Htype) as Htype_w.
    assert (Hv : {{ Γ, A ⊢ #0 : A[Wk] }}) by eauto using wf_vlookup, here.
    pose proof (typed_readback_reflected_variable _ _ _ (here A Γ)) as Hne.
    cbn in Hne. rewrite Nat.sub_0_r in Hne.
    pose proof (uniform_certified_realization_reflection _ _ _ _ _ _ HAw Hv Htype_w Hne (related_variable (length Γ))) as Hvar.
    pose proof (realized_environment_extend _ _ _ _ _ _ _ _ _ _
      uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
      Henv_σ HA Hv Ha Hvar) as Hext.
    exact (realized_environment_substitution_conversion _ _ _ _ _ _
      uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
      Hext Hid (identity_with_last_variable _ _ _ HA)).
Qed.

Local Lemma uniform_certified_typing_interpretation_implies_readback :
  uniform_certified_typing_interpretation -> readback_preserves_typing.
Proof.
  intros Hfund. apply initialized_typed_readback_equivalent.
  intros Γ A M ρ a m HM Hρ Ha Hm.
  pose proof (typing_context _ _ _ HM) as HΓ.
  pose proof (uniform_certified_initial_environment Hfund _ _ HΓ Hρ) as Henv.
  destruct (Hfund _ _ _ HM _ _ _ Henv) as (a' & m' & Ha' & Hm' & H).
  pose proof (eval_exp_deterministic _ _ _ Ha _ Ha') as Ea. subst a'.
  pose proof (eval_exp_deterministic _ _ _ Hm _ Hm') as Em. subst m'.
  destruct (type_of_typing _ _ _ HM) as (i & HA).
  pose proof (uniform_certified_realization_type_conversion _ _ _ _ _ _ _ HA
    (wf_exp_eq_sub_id _ _ _ HA) H) as Hcast.
  apply uniform_certified_realization_readback.
  exact (uniform_certified_realization_term_conversion _ _ _ _ _ _ HM
    (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_sub_id _ _ _ HM)) Hcast).
Qed.

Local Definition certifies_typed_substitution Γ Δ σ :=
  forall Θ τ ρ, realizes_environment uniform_certified_realization Θ Γ τ ρ ->
    exists η, eval_sub σ ρ η /\
      realizes_environment uniform_certified_realization Θ Δ (a_compose σ τ) η.

Local Lemma uniform_certified_variable_case Γ A x :
  ctx_lookup x A Γ -> certifies_typed_term Γ A (a_var x).
Proof.
  intros HL Δ σ ρ [_ HR].
  destruct (HR _ _ HL) as (a & Ha & Hv).
  exists a, (ρ x). repeat split; auto using eval_exp_var.
Qed.

Local Lemma uniform_certified_substitution_case Γ Δ A M σ :
  {{ Δ ⊢ M : A }} ->
  {{ Γ ⊢s σ : Δ }} ->
  certifies_typed_term Δ A M ->
  certifies_typed_substitution Γ Δ σ ->
  certifies_typed_term Γ (a_sub A σ) (a_sub M σ).
Proof.
  intros HM HS Hterm Hsub Θ τ ρ Hρ.
  destruct (Hsub _ _ _ Hρ) as (η & Hη & Henv).
  destruct (Hterm _ _ _ Henv) as (a & m & Ha & Hm & H).
  exists a, m. repeat split; try (eapply eval_exp_sub; eassumption).
  destruct (type_of_typing _ _ _ HM) as [i HA].
  exact (realized_environment_compose_action _ _ _ _ _ _ _ _ _ _ _
    uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
    (proj1 Hρ) HS HA HM H).
Qed.

Local Lemma uniform_certified_identity_substitution Γ :
  certifies_typed_substitution Γ Γ a_id.
Proof.
  intros Θ τ ρ Hρ.
  pose proof (proj1 Hρ) as HS.
  pose proof (substitution_target _ _ _ HS) as HΓ.
  exists ρ. split; [apply eval_sub_id |].
  eapply realized_environment_substitution_conversion;
    try exact uniform_certified_realization_type_conversion;
    try exact uniform_certified_realization_term_conversion;
    try exact Hρ.
  - exact (wf_sub_compose _ _ _ _ _ HS (wf_sub_id _ HΓ)).
  - apply wf_sub_eq_sym, wf_sub_eq_id_compose_right. exact HS.
Qed.

Local Lemma uniform_certified_weakening_substitution Γ A :
  certifies_typed_substitution (A :: Γ) Γ a_weaken.
Proof.
  intros Θ τ ρ Hρ.
  exists (drop_env ρ). split; [apply eval_sub_weaken |].
  exact (realized_environment_drop _ _ _ _ _ _
    uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion Hρ).
Qed.

Local Lemma uniform_certified_composition_substitution Γ Δ Θ σ τ :
  {{ Γ ⊢s τ : Δ }} ->
  {{ Δ ⊢s σ : Θ }} ->
  certifies_typed_substitution Γ Δ τ ->
  certifies_typed_substitution Δ Θ σ ->
  certifies_typed_substitution Γ Θ (a_compose σ τ).
Proof.
  intros HT HS Hτ Hσ Ξ υ ρ Hρ.
  destruct (Hτ _ _ _ Hρ) as (η & Hη & Henv).
  destruct (Hσ _ _ _ Henv) as (ω & Hω & Henv').
  exists ω. split; [eapply eval_sub_compose; eassumption |].
  pose proof (proj1 Hρ) as HU.
  eapply realized_environment_substitution_conversion;
    try exact uniform_certified_realization_type_conversion;
    try exact uniform_certified_realization_term_conversion;
    try exact Henv'.
  - exact (wf_sub_compose _ _ _ _ _ HU (wf_sub_compose _ _ _ _ _ HT HS)).
  - apply wf_sub_eq_sym. exact (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ HS HT HU).
Qed.

Local Lemma certified_type_as_universe_member Γ M m i R :
  certified_type i Γ M m R -> has_certified_realization Γ (a_typ i) M (d_univ i) m.
Proof.
  intro HG.
  pose proof (proj1 (proj1 (certified_type_properties _ _ _ _ _ HG))) as HM.
  exists (S i), (certified_candidate (d_univ i) (universe_candidate (lower_certified_realizations (S i)) i Γ)).
  split.
  - apply certify_universe; [eauto using typing_context | lia | intros N n; reflexivity].
  - split.
    + exists (S i), (fun b b' => exists Q, semantic_type i b b' Q). split.
      * apply semantic_universe. lia.
      * exact (certified_layer_semantic_type _ _ _ _ _ _ HG).
    + exists R. apply lower_certified_realization_lookup; [lia | exact HG].
Qed.

Local Lemma uniform_certified_typing_of_universe Γ j :
  {{ ⊢ Γ }} ->
  uniform_certified_realization Γ (a_typ (S j)) (a_typ j) (d_univ (S j)) (d_univ j).
Proof.
  intros HΓ Δ σ HW.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  pose proof (substitution_source _ _ _ HS) as HΔ.
  assert (HG : certified_type (S j) Δ (a_typ j) (d_univ j)
    (certified_candidate (d_univ j) (universe_candidate (lower_certified_realizations (S j)) j Δ))) by
    (apply certify_universe; [exact HΔ | lia | intros N n; reflexivity]).
  assert (HT : {{ Δ ⊢ Type@(S j)[σ] : Type@(S (S j)) }}) by
    eauto using type_substitution, wf_typ.
  eapply has_certified_realization_term_conversion.
  - exact (wf_exp_sub _ _ _ _ _ HS (wf_typ _ _ HΓ)).
  - exact (convert_equality _ _ _ _ _ _
      (wf_exp_eq_typ_sub _ _ _ j HS) HT
      (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_typ_sub _ _ _ (S j) HS))).
  - eapply has_certified_realization_type_conversion.
    + exact HT.
    + exact (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_typ_sub _ _ _ (S j) HS)).
    + exact (certified_type_as_universe_member _ _ _ _ _ HG).
Qed.

Local Lemma uniform_certified_typing_of_natural Γ :
  {{ ⊢ Γ }} ->
  uniform_certified_realization Γ (a_typ 0) a_nat (d_univ 0) d_nat.
Proof.
  intros HΓ Δ σ HW.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  pose proof (substitution_source _ _ _ HS) as HΔ.
  assert (HG : certified_type 0 Δ a_nat d_nat (certified_candidate d_nat (natural_candidate Δ))) by
    (apply certify_natural; [exact HΔ | intros M m; reflexivity]).
  assert (HT : {{ Δ ⊢ Type@0[σ] : Type@1 }}) by eauto using type_substitution, wf_typ.
  eapply has_certified_realization_term_conversion.
  - exact (wf_exp_sub _ _ _ _ _ HS (wf_nat _ HΓ)).
  - exact (convert_equality _ _ _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS) HT
      (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_typ_sub _ _ _ 0 HS))).
  - eapply has_certified_realization_type_conversion.
    + exact HT.
    + exact (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_typ_sub _ _ _ 0 HS)).
    + exact (certified_type_as_universe_member _ _ _ _ _ HG).
Qed.

Local Lemma uniform_certified_typing_of_zero Γ :
  {{ ⊢ Γ }} ->
  uniform_certified_realization Γ a_nat a_zero d_nat d_zero.
Proof.
  intros HΓ Δ σ HW.
  pose proof (context_weakening_typed _ _ _ HW) as HS.
  pose proof (substitution_source _ _ _ HS) as HΔ.
  assert (HT : {{ Δ ⊢ ℕ[σ] : Type@0 }}) by eauto using type_substitution, wf_nat.
  assert (HG : has_certified_realization Δ a_nat a_zero d_nat d_zero).
  {
    exists 0, (certified_candidate d_nat (natural_candidate Δ)). split.
    - apply certify_natural; [exact HΔ | intros M m; reflexivity].
    - split.
      + exists 0, natural_values_agree. split; [apply semantic_natural | apply natural_values_zero].
      + apply candidate_zero; eauto using wf_zero, expression_equality_reflexive.
  }
  eapply has_certified_realization_term_conversion.
  - exact (wf_exp_sub _ _ _ _ _ HS (wf_zero _ HΓ)).
  - exact (convert_equality _ _ _ _ _ _ (wf_exp_eq_zero_sub _ _ _ HS) HT
      (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS))).
  - exact (has_certified_realization_type_conversion _ _ _ _ _ _ _ HT
      (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS)) HG).
Qed.

Local Lemma uniform_certified_extension_substitution Γ Δ σ A M i :
  {{ Γ ⊢s σ : Δ }} ->
  {{ Δ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A[σ] }} ->
  certifies_typed_substitution Γ Δ σ ->
  certifies_typed_term Γ (a_sub A σ) M ->
  certifies_typed_substitution Γ (A :: Δ) (a_extend σ M).
Proof.
  intros HS HA HM Hsub Hterm Θ τ ρ Hρ.
  pose proof (proj1 Hρ) as HT.
  destruct (Hsub _ _ _ Hρ) as (η & Hη & Henv).
  destruct (Hterm _ _ _ Hρ) as (a & m & Ha & Hm & H).
  destruct (invert_eval_substitution _ _ _ _ Ha) as (η' & Hη' & Ha').
  pose proof (eval_sub_deterministic _ _ _ _ Hη Hη'). subst η'.
  pose proof (proj1 Henv) as HST.
  pose proof (type_substitution _ _ _ _ _ HST HA) as HAt.
  pose proof (wf_exp_eq_sym _ _ _ _ (type_substitution_composition _ _ _ _ _ _ _ HT HS HA)) as EAt.
  pose proof (convert_term _ _ _ _ _ (wf_exp_sub _ _ _ _ _ HT HM) HAt EAt) as HMt.
  pose proof (uniform_certified_realization_type_conversion _ _ _ _ _ _ _ HAt EAt H) as HMreal.
  exists (extend_env η m). split; [eapply eval_sub_extend; eassumption |].
  pose proof (realized_environment_extend _ _ _ _ _ _ _ _ _ _
    uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
    Henv HA HMt Ha' HMreal) as Hext.
  eapply realized_environment_substitution_conversion;
    try exact uniform_certified_realization_type_conversion;
    try exact uniform_certified_realization_term_conversion;
    try exact Hext.
  - exact (wf_sub_compose _ _ _ _ _ HT (wf_sub_extend _ _ _ _ _ _ HS HA HM)).
  - apply wf_sub_eq_sym.
    exact (wf_sub_eq_extend_compose _ _ _ _ _ _ _ _ HS HA HM HT).
Qed.


Local Lemma nominal_certified_member_of_same_code Γ A B a M m i R :
  has_certified_realization Γ A M a m -> certified_type i Γ B a R -> R M m.
Proof.
  intros (j & S & HG & HM) HH.
  pose proof (certified_type_raise _ _ _ _ _ _ (Nat.le_max_l j i) HG) as HGl.
  pose proof (certified_type_raise _ _ _ _ _ _ (Nat.le_max_r j i) HH) as HGr.
  now apply (certified_candidates_with_same_code _ _ _ _ _ HGl _ _ HGr).
Qed.


Local Definition certifies_typed_term_at_substitution Γ A M :=
  forall Δ σ ρ, realizes_environment uniform_certified_realization Δ Γ σ ρ ->
    exists a m, eval_exp A ρ a /\ eval_exp M ρ m /\
      has_certified_realization Δ (a_sub A σ) (a_sub M σ) a m.

Local Lemma substituted_certified_realization_lifts_to_uniform Γ A M :
  {{ Γ ⊢ M : A }} ->
  certifies_typed_term_at_substitution Γ A M ->
  certifies_typed_term Γ A M.
Proof.
  intros HM Hnom Δ σ ρ Hρ.
  destruct (Hnom _ _ _ Hρ) as (a & m & Ha & Hm & _).
  exists a, m. split; [exact Ha | split; [exact Hm |]].
  intros Θ τ HW.
  pose proof (realized_environment_weaken _ _ _ _ _ _ _
    uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
    uniform_certified_realization_under_weakening Hρ HW) as Hρ'.
  destruct (Hnom _ _ _ Hρ') as (a' & m' & Ha' & Hm' & H).
  pose proof (eval_exp_deterministic _ _ _ Ha _ Ha') as Ea. subst a'.
  pose proof (eval_exp_deterministic _ _ _ Hm _ Hm') as Em. subst m'.
  destruct (type_of_typing _ _ _ HM) as (i & HA).
  exact (realized_environment_compose_action _ _ _ _ _ _ _ _ _ _ _
    has_certified_realization_type_conversion has_certified_realization_term_conversion
    (context_weakening_typed _ _ _ HW) (proj1 Hρ) HA HM H).
Qed.


Local Lemma nominal_certified_realization_is_uniform Γ A M a m :
  has_certified_realization Γ A M a m -> uniform_certified_realization Γ A M a m.
Proof.
  intros (i & R & HG & HM) Δ σ HW.
  destruct (certified_type_weakening _ _ _ _ _ HG _ _
    (weakening_between_canonical _ _ _ HW)) as (S & HS & Hmem).
  exists i, S. split; [exact HS | exact (Hmem _ _ HM)].
Qed.

Local Lemma certified_environment_weakening_between Γ Δ Θ σ τ ρ :
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  weakening_between Δ Θ τ ->
  realizes_environment uniform_certified_realization Θ Γ (a_compose σ τ) ρ.
Proof.
  intros Hρ (ω & Hω & Hτ & Eτ).
  pose proof (proj1 Hρ) as Hσ.
  pose proof (realized_environment_weaken _ _ _ _ _ _ _
    uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
    uniform_certified_realization_under_weakening Hρ Hω) as Hρ'.
  eapply realized_environment_substitution_conversion;
    try exact uniform_certified_realization_type_conversion;
    try exact uniform_certified_realization_term_conversion;
    try exact Hρ'.
  - exact (wf_sub_compose _ _ _ _ _ Hτ Hσ).
  - exact (wf_sub_eq_compose_cong _ _ _ _ _ _ _ (wf_sub_eq_sym _ _ _ _ Eτ)
      (substitution_equality_reflexive _ _ _ Hσ)).
Qed.

Local Lemma nominal_certified_universe_realization Γ Δ σ ρ A i a :
  {{ Γ ⊢ A : Type@i }} ->
  certifies_typed_term Γ (a_typ i) A ->
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  eval_exp A ρ a ->
  exists R, certified_type i Δ (a_sub A σ) a R.
Proof.
  intros HA HC Hρ Ha.
  destruct (HC _ _ _ Hρ) as (t & b & Ht & Hb & H).
  pose proof (eval_exp_deterministic _ _ _ Ha _ Hb) as E. subst b.
  inversion Ht; subst t.
  pose proof (proj1 Hρ) as Hσ.
  pose proof (wf_typ Δ i (substitution_source _ _ _ Hσ)) as HU.
  pose proof (uniform_certified_realization_type_conversion _ _ _ _ _ _ _
    HU (wf_exp_eq_typ_sub _ _ _ _ Hσ) H) as HU'.
  destruct (uniform_certified_realization_at_identity _ _ _ _ _ _ HU
    (type_substitution _ _ _ _ _ Hσ HA) HU') as (j & R & HG & HR).
  exact (certified_type_of_universe_member _ _ _ _ _ _ HG HR).
Qed.


Local Lemma semantic_environment_from_lookup Γ ρ :
  (forall x A, ctx_lookup x A Γ ->
    exists a, eval_exp A ρ a /\ semantic_member a (ρ x)) ->
  related_environments Γ ρ ρ.
Proof.
  revert ρ. induction Γ as [|A Γ IH]; intros ρ HR.
  - apply related_empty.
  - destruct (HR _ _ (here A Γ)) as (a & Ha & j & Q & HQ & H0).
    destruct (invert_eval_substitution _ _ _ _ Ha) as (η & Hη & HA).
    inversion Hη; subst.
    eapply related_extension; [| exact HA | exact HA | exact HQ | exact H0].
    apply IH. intros x B HL.
    destruct (HR _ _ (there _ _ _ _ HL)) as (b & Hb & HS).
    destruct (invert_eval_substitution _ _ _ _ Hb) as (η & Hη' & HB).
    inversion Hη'; subst. exists b. now split.
Qed.

Local Lemma certified_environment_semantic Γ Δ σ ρ :
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  related_environments Γ ρ ρ.
Proof.
  intros (HS & HR).
  apply semantic_environment_from_lookup.
  intros x A HL.
  destruct (HR _ _ HL) as (a & Ha & Hmember).
  pose proof (substitution_source _ _ _ HS) as HΔ.
  destruct (Hmember _ _ (context_weakening_id _ HΔ)) as (j & R & HG & HM).
  exists a. split; [exact Ha |].
  exact (certified_layer_member _ _ _ _ _ _ HG _ _ HM).
Qed.

Local Lemma certified_evaluated_member Γ A M ρ a m :
  {{ Γ ⊢ M : A }} ->
  related_environments Γ ρ ρ ->
  eval_exp A ρ a ->
  eval_exp M ρ m ->
  semantic_member a m.
Proof.
  intros HM Hρ Ha Hm.
  pose proof (proj1 (proj2 (proj2 declarative_interpretation)) _ _ _ HM) as HF.
  destruct HF as [i H].
  destruct (H _ _ Hρ) as (a' & b & Q & m' & n & Ha' & Hb & HQ & Hm' & Hn & Hr).
  reconcile_values.
  exists i, Q. now split.
Qed.

Local Lemma nominal_certified_code_conversion Γ A B a b M m n j k Q :
  {{ Γ ⊢ B : Type@j }} ->
  {{ Γ ⊢ A ≈ B : Type@j }} ->
  semantic_type k a b Q ->
  Q m n ->
  has_certified_realization Γ A M a m ->
  has_certified_realization Γ B M b n.
Proof.
  intros HB EAB HQ Hmn (i & R & HG & HM).
  set (l := Nat.max i (Nat.max j k)).
  assert (Hil : i <= l) by (unfold l; lia).
  assert (Hjl : j <= l) by (unfold l; lia).
  assert (Hkl : k <= l) by (unfold l; lia).
  pose proof (certified_type_raise _ _ _ _ _ _ Hil HG) as HGl.
  pose proof (semantic_type_cumulative _ _ _ _ _ Hkl HQ) as HQl.
  destruct (certified_type_transport _ _ _ _ _ HGl _ _ HQl) as (S & HS & HE).
  exists l, S. split.
  - exact (certified_type_conversion _ _ _ _ _ _ HS
      (type_cumulativity _ _ _ _ HB Hjl)
      (equality_cumulativity _ _ _ _ _ EAB (typing_context _ _ _ HB) Hjl)).
  - exact (proj1 (HE M m n Hmn) HM).
Qed.

Local Lemma certified_subtyping_by_type_equality Γ Δ σ ρ A B M i a m :
  {{ Γ ⊢ B : Type@i }} ->
  {{ Γ ⊢ A ≈ B : Type@i }} ->
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  eval_exp A ρ a ->
  has_certified_realization Δ (a_sub A σ) M a m ->
  exists b, eval_exp B ρ b /\ has_certified_realization Δ (a_sub B σ) M b m.
Proof.
  intros HB EAB Hρ Ha (j & R & HG & HM).
  pose proof (certified_environment_semantic _ _ _ _ Hρ) as Hrho.
  pose proof (proj1 (proj2 (proj2 (proj2 declarative_interpretation))) _ _ _ _ EAB) as Hinterp.
  destruct (interpreted_terms_as_types _ _ _ _ Hinterp _ _ Hrho) as (a' & b & Q & Ha' & Hb & HQ).
  pose proof (eval_exp_deterministic _ _ _ Ha _ Ha') as E. subst a'.
  pose proof (proj1 Hρ) as HS.
  pose proof (type_substitution _ _ _ _ _ HS HB) as HBT.
  pose proof (type_substitution_congruence _ _ _ _ _ _ _ HS
    (substitution_equality_reflexive _ _ _ HS) EAB) as EBT.
  pose proof (semantic_member_in_relation _ _ _ _ _ HQ
    (certified_layer_member _ _ _ _ _ _ HG _ _ HM)) as Hm.
  exists b. split; [exact Hb |].
  exact (nominal_certified_code_conversion _ _ _ _ _ _ _ _ _ _ _
    HBT EBT HQ Hm (ex_intro _ j (ex_intro _ R (conj HG HM)))).
Qed.

Local Lemma semantic_type_of_evaluated_type Γ A i ρ a :
  {{ Γ ⊢ A : Type@i }} ->
  related_environments Γ ρ ρ ->
  eval_exp A ρ a ->
  exists Q, semantic_type i a a Q.
Proof.
  intros HA Hρ Ha.
  pose proof (proj1 (proj2 (proj2 declarative_interpretation)) _ _ _ HA) as H.
  destruct (interpreted_terms_as_types _ _ _ _ H _ _ Hρ)
    as (a' & b & Q & Ha' & Hb & HQ).
  reconcile_values. now exists Q.
Qed.

Local Lemma certified_inhabitant_of_supertype Γ A B ρ a b m :
  wf_subtyp Γ A B ->
  related_environments Γ ρ ρ ->
  eval_exp A ρ a ->
  eval_exp B ρ b ->
  semantic_member a m ->
  semantic_member b m.
Proof.
  intros Hsub Hρ Ha Hb HM.
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 declarative_interpretation)))))
    _ _ _ Hsub) as (i & H).
  destruct (H _ _ Hρ)
    as (a' & a'' & b' & b'' & Q & T & Ha' & Ha'' & HQ & Hb' & Hb'' & HT & HQT).
  reconcile_values.
  exists i, T. split; [exact HT |].
  apply HQT. exact (semantic_member_in_relation _ _ _ _ _ HQ HM).
Qed.
Local Lemma nominal_certified_realization_application Γ Δ A B F N i σ a ρ C f n :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ F : Π A B }} ->
  {{ Γ ⊢ N : A }} ->
  has_certified_realization Δ (a_sub (a_pi A B) σ) (a_sub F σ) (d_pi a ρ C) f ->
  has_certified_realization Δ (a_sub A σ) (a_sub N σ) a n ->
  (forall b, eval_exp C (extend_env ρ n) b ->
    exists j R, certified_type j Δ (a_sub B (a_extend σ (a_sub N σ))) b R) ->
  exists b r, eval_exp C (extend_env ρ n) b /\ eval_app f n r /\
    has_certified_realization Δ (a_sub (a_sub B (a_extend a_id N)) σ) (a_sub (a_app F N) σ) b r.
Proof.
  intros Hσ HA HB HF HN (j & S & HG & HS) Harg Hcod.
  destruct (certified_function_view _ _ _ _ _ _ _ HG)
    as (A' & B' & R & T & HA' & HB' & HG' & HD & _ & HC & HE).
  apply HE in HS. destruct HS as (_ & HF' & H).
  pose proof (substitution_source _ _ _ Hσ) as HΔ.
  pose proof (weakening_between_canonical _ _ _ (context_weakening_id Δ HΔ)) as HW.
  pose proof (nominal_certified_member_of_same_code _ _ _ _ _ _ _ _ Harg (HD _ _ HW)) as Hn.
  destruct (H _ _ HW _ _ Hn) as (b & r & Hb & Hr & Hres).
  pose proof (HC _ _ HW _ _ _ Hn Hb) as HBres.
  destruct (Hcod _ Hb) as (k & V & Hresult).
  pose proof (proj1 (proj1 (certified_type_properties _ _ _ _ _ Hresult))) as HT.
  pose proof (certified_types_with_same_code _ _ _ _ _ _ _ _ HBres Hresult) as Etype.
  assert (Hres' : has_certified_realization Δ {{{ B'[Id,,N[σ]] }}} {{{ F[σ][Id] N[σ] }}} b r) by
    (exists j, (T Δ a_id (a_sub N σ) n); now split).
  pose proof (has_certified_realization_type_conversion _ _ _ _ _ _ _
    (type_cumulativity _ _ _ _ HT (Nat.le_max_r j k)) Etype Hres') as Hcast.
  pose proof (type_substitution _ _ _ _ _ Hσ HA) as HAs.
  pose proof (type_substitution _ _ _ _ _ (lifted_substitution _ _ _ _ _ Hσ HA) HB) as HBs.
  pose proof (wf_pi _ _ _ _ HAs HBs) as HPi.
  pose proof (wf_exp_eq_pi_sub _ _ _ _ _ _ Hσ HA HB) as EPi.
  pose proof (wf_exp_sub _ _ _ _ _ Hσ HF) as HFs.
  pose proof (wf_exp_sub _ _ _ _ _ Hσ HN) as HNs.
  pose proof (convert_equality _ _ _ _ _ _
    (wf_exp_eq_sub_id _ _ _ HFs) HPi EPi) as EF.
  pose proof (type_substitution _ _ _ _ _ (wf_sub_extend _ _ _ _ _ _ Hσ HA HNs) HB) as HTi.
  pose proof (convert_equality _ _ _ _ _ _
    (wf_exp_eq_app_cong _ _ _ _ _ _ _ _ HAs HBs EF
      (expression_equality_reflexive _ _ _ HNs)) HTi
    (type_lift_at_argument _ _ _ _ _ _ _ _ Hσ HA HB HNs)) as Eapp.
  pose proof (wf_exp_eq_app_sub _ _ _ _ _ _ _ _ Hσ HA HB HF HN) as Esub.
  pose proof (type_argument_substitution_composition _ _ _ _ _ _ _ _ Hσ HA HB HN) as Eres.
  pose proof (type_substitution _ _ _ _ _
    (typing_identity_extension _ _ _ _ HA HN) HB) as HTapp.
  pose proof (type_substitution _ _ _ _ _ Hσ HTapp) as HTs.
  exists b, r. split; [exact Hb | split; [exact Hr |]].
  eapply has_certified_realization_term_conversion.
  - exact (wf_exp_sub _ _ _ _ _ Hσ (wf_app _ _ _ _ _ _ HA HB HF HN)).
  - eapply convert_equality; [ | exact HTs | exact (wf_exp_eq_sym _ _ _ _ Eres)].
    exact (wf_exp_eq_trans _ _ _ _ _ Esub (wf_exp_eq_sym _ _ _ _ Eapp)).
  - exact (has_certified_realization_type_conversion _ _ _ _ _ _ _ HTs
      (wf_exp_eq_sym _ _ _ _ Eres) Hcast).
Qed.


Local Lemma uniform_certified_application_case Γ A B F N i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ F : Π A B }} ->
  {{ Γ ⊢ N : A }} ->
  certifies_typed_term (A :: Γ) (a_typ i) B ->
  certifies_typed_term Γ (a_pi A B) F ->
  certifies_typed_term Γ A N ->
  certifies_typed_term Γ (a_sub B (a_extend a_id N)) (a_app F N).
Proof.
  intros HA HB HF HN Hcod Hfun Harg.
  apply substituted_certified_realization_lifts_to_uniform; [exact (wf_app _ _ _ _ _ _ HA HB HF HN) |].
  intros Δ σ ρ Hρ.
  pose proof (proj1 Hρ) as Hσ.
  destruct (Hfun _ _ _ Hρ) as (t & f & Ht & Hf & HFreal).
  destruct (Harg _ _ _ Hρ) as (a & n & Ha & Hn & HNreal).
  assert (Et : t = d_pi a ρ B) by
    (eapply eval_exp_deterministic; [exact Ht | now apply eval_exp_pi]).
  subst t.
  pose proof (type_substitution _ _ _ _ _ Hσ HA) as HAs.
  pose proof (type_substitution _ _ _ _ _ Hσ (wf_pi _ _ _ _ HA HB)) as HPs.
  pose proof (wf_exp_sub _ _ _ _ _ Hσ HN) as HNs.
  pose proof (uniform_certified_realization_at_identity _ _ _ _ _ _ HPs
    (wf_exp_sub _ _ _ _ _ Hσ HF) HFreal) as HFnom.
  pose proof (uniform_certified_realization_at_identity _ _ _ _ _ _ HAs HNs HNreal) as HNnom.
  assert (Hcodomain : forall b, eval_exp B (extend_env ρ n) b ->
    exists j R, certified_type j Δ (a_sub B (a_extend σ (a_sub N σ))) b R).
  {
    intros b Hb.
    pose proof (realized_environment_extend _ _ _ _ _ _ _ _ _ _
      uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
      Hρ HA HNs Ha HNreal) as Hρ'.
    destruct (Hcod _ _ _ Hρ') as (u & b' & Hu & Hb' & HBr).
    pose proof (eval_exp_deterministic _ _ _ Hb _ Hb') as Eb. subst b'.
    inversion Hu; subst u.
    pose proof (proj1 Hρ') as HSN.
    pose proof (wf_typ _ i (substitution_source _ _ _ HSN)) as HUi.
    pose proof (uniform_certified_realization_type_conversion _ _ _ _ _ _ _ HUi
      (wf_exp_eq_typ_sub _ _ _ _ HSN) HBr) as HBr'.
    pose proof (type_substitution _ _ _ _ _ HSN HB) as HBt.
    destruct (uniform_certified_realization_at_identity _ _ _ _ _ _ HUi HBt HBr')
      as (j & R & HG & HR).
    exists i. exact (certified_type_of_universe_member _ _ _ _ _ _ HG HR).
  }
  destruct (nominal_certified_realization_application _ _ _ _ _ _ _ _ _ _ _ _ _
    Hσ HA HB HF HN HFnom HNnom Hcodomain) as (b & r & Hb & Hr & Hreal).
  exists b, r. split.
  - eapply eval_exp_sub; [eapply eval_sub_extend; [apply eval_sub_id | exact Hn] | exact Hb].
  - split; [eapply eval_exp_app; eassumption | exact Hreal].
Qed.


Local Lemma certified_binder_families Γ Δ σ ρ A B i a :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  certifies_typed_term Γ (a_typ i) A ->
  certifies_typed_term (A :: Γ) (a_typ i) B ->
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  eval_exp A ρ a ->
  exists R : domain_candidate, exists S : codomain_candidate,
    (forall Θ τ, weakening_between Δ Θ τ ->
      certified_type i Θ (a_sub (a_sub A σ) τ) a (R Θ τ)) /\
    (forall Θ τ, weakening_between Δ Θ τ ->
      forall N n, R Θ τ N n -> exists b, eval_exp B (extend_env ρ n) b) /\
    (forall Θ τ, weakening_between Δ Θ τ -> forall N n b,
      R Θ τ N n -> eval_exp B (extend_env ρ n) b ->
      certified_type i Θ (a_sub (a_sub B (Syntax.q σ)) (a_extend τ N)) b (S Θ τ N n)).
Proof.
  intros HA HB HAr HBr Hρ Ha.
  pose proof (proj1 Hρ) as Hσ.
  set (R := fun Θ τ N n =>
    exists R, certified_type i Θ (a_sub (a_sub A σ) τ) a R /\ R N n).
  set (S := fun Θ τ N n M m =>
    exists b T, eval_exp B (extend_env ρ n) b /\
      certified_type i Θ (a_sub (a_sub B (Syntax.q σ)) (a_extend τ N)) b T /\ T M m).
  exists R, S. split.
  - intros Θ τ HW. unfold R. apply certified_type_canonical.
    pose proof (weakening_between_typed _ _ _ HW) as Hτ.
    pose proof (certified_environment_weakening_between _ _ _ _ _ _ Hρ HW) as Hρ'.
    destruct (nominal_certified_universe_realization _ _ _ _ _ _ _ HA HAr Hρ' Ha) as (T & HT).
    exists T. eapply certified_type_conversion; [exact HT | |].
    + exact (type_substitution _ _ _ _ _ Hτ (type_substitution _ _ _ _ _ Hσ HA)).
    + exact (type_substitution_composition _ _ _ _ _ _ _ Hτ Hσ HA).
  - assert (Hcod : forall Θ τ, weakening_between Δ Θ τ -> forall N n,
      R Θ τ N n -> exists b T, eval_exp B (extend_env ρ n) b /\
        certified_type i Θ (a_sub (a_sub B (Syntax.q σ)) (a_extend τ N)) b T).
    {
      intros Θ τ HW N n (T & HT & HN).
      pose proof (weakening_between_typed _ _ _ HW) as Hτ.
      pose proof (certified_environment_weakening_between _ _ _ _ _ _ Hρ HW) as Hρ'.
      pose proof (wf_sub_compose _ _ _ _ _ Hτ Hσ) as HST.
      pose proof (type_substitution _ _ _ _ _ HST HA) as HAt.
      pose proof (type_substitution_composition _ _ _ _ _ _ _ Hτ Hσ HA) as EAt.
      pose proof (proj2 (proj1 (certified_type_properties _ _ _ _ _ HT)) _ _ HN) as HNt.
      pose proof (convert_term _ _ _ _ _ HNt HAt (wf_exp_eq_sym _ _ _ _ EAt)) as HN'.
      assert (HR : has_certified_realization Θ (a_sub A (a_compose σ τ)) N a n).
      {
        exists i, T. split; [| exact HN].
        exact (certified_type_conversion _ _ _ _ _ _ HT HAt (wf_exp_eq_sym _ _ _ _ EAt)).
      }
      pose proof (realized_environment_extend _ _ _ _ _ _ _ _ _ _
        uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
        Hρ' HA HN' Ha (nominal_certified_realization_is_uniform _ _ _ _ _ HR)) as Hρ''.
      destruct (HBr _ _ _ Hρ'') as (u & b & Hu & Hb & HBreal).
      destruct (nominal_certified_universe_realization _ _ _ _ _ _ _ HB HBr Hρ'' Hb) as (V & HV).
      exists b, V. split; [exact Hb |].
      pose proof (type_substitution _ _ _ _ _ Hσ HA) as HAs.
      pose proof (lifted_substitution _ _ _ _ _ Hσ HA) as HQ.
      pose proof (wf_sub_extend _ _ _ _ _ _ Hτ HAs HNt) as HTN.
      eapply certified_type_conversion; [exact HV | |].
      - exact (type_substitution _ _ _ _ _ HTN (type_substitution _ _ _ _ _ HQ HB)).
      - apply wf_exp_eq_sym.
        exact (type_lifted_substitution_at_argument _ _ _ _ _ _ _ _ _ _
          Hσ Hτ HA HB HNt).
    }
    split.
    + intros Θ τ HW N n HR. destruct (Hcod _ _ HW _ _ HR) as (b & T & Hb & _).
      now exists b.
    + intros Θ τ HW N n b HR Hb.
      destruct (Hcod _ _ HW _ _ HR) as (b' & T & Hb' & HT).
      pose proof (eval_exp_deterministic _ _ _ Hb _ Hb') as E. subst b'.
      eapply certified_realization_layer_change_candidate; [exact HT |].
      intros M m. split.
      * intro HM. exists b, T. auto.
      * intros (b' & V & Hb'' & HV & HM).
        pose proof (eval_exp_deterministic _ _ _ Hb _ Hb'') as E. subst b'.
        now apply (certified_candidates_with_same_code _ _ _ _ _ HV _ _ HT).
Qed.

Local Lemma substituted_certified_universe_member Γ Δ σ A B b i R :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Δ ⊢ B ≈ A[σ] : Type@i }} ->
  certified_type i Δ B b R ->
  has_certified_realization Δ (a_sub (a_typ i) σ) (a_sub A σ) (d_univ i) b.
Proof.
  intros HS HA EA HG.
  pose proof (certified_type_conversion _ _ _ _ _ _ HG
    (type_substitution _ _ _ _ _ HS HA) EA) as H.
  eapply has_certified_realization_type_conversion.
  - apply type_substitution with (Δ := Γ); [exact HS |].
    exact (wf_typ _ _ (typing_context _ _ _ HA)).
  - apply wf_exp_eq_sym. exact (wf_exp_eq_typ_sub _ _ _ _ HS).
  - exact (certified_type_as_universe_member _ _ _ _ _ H).
Qed.

Local Lemma uniform_certified_dependent_type_formation Γ A B i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  certifies_typed_term Γ (a_typ i) A ->
  certifies_typed_term (A :: Γ) (a_typ i) B ->
  certifies_typed_term Γ (a_typ i) (a_pi A B) /\
  certifies_typed_term Γ (a_typ i) (a_sigma A B).
Proof.
  intros HA HB HAr HBr.
  split; apply substituted_certified_realization_lifts_to_uniform;
    [exact (wf_pi _ _ _ _ HA HB) | | exact (wf_sigma _ _ _ _ HA HB) |].
  all: intros Δ σ ρ Hρ;
    destruct (HAr _ _ _ Hρ) as (u & a & Hu & Ha & Hreal);
    pose proof (proj1 Hρ) as HS;
    pose proof (type_substitution _ _ _ _ _ HS HA) as HAs;
    pose proof (type_substitution _ _ _ _ _ (lifted_substitution _ _ _ _ _ HS HA) HB) as HBs;
    destruct (certified_binder_families _ _ _ _ _ _ _ _ HA HB HAr HBr Hρ Ha)
      as (R & S & HD & HT & HC).
  - pose proof (eval_exp_pi _ _ _ B Ha) as Hcode.
    pose proof (semantic_type_of_evaluated_type _ _ _ _ _ (wf_pi _ _ _ _ HA HB)
      (certified_environment_semantic _ _ _ _ Hρ) Hcode) as Hsem.
    exists (d_univ i), (d_pi a ρ B).
    split; [apply eval_exp_typ | split; [exact Hcode |]].
    eapply substituted_certified_universe_member.
    + exact HS.
    + exact (wf_pi _ _ _ _ HA HB).
    + apply wf_exp_eq_sym. exact (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA HB).
    + eapply certify_function with (R := R) (S := S); try eassumption.
      intros M m. reflexivity.
  - pose proof (eval_exp_sigma _ _ _ B Ha) as Hcode.
    pose proof (semantic_type_of_evaluated_type _ _ _ _ _ (wf_sigma _ _ _ _ HA HB)
      (certified_environment_semantic _ _ _ _ Hρ) Hcode) as Hsem.
    exists (d_univ i), (d_sigma a ρ B).
    split; [apply eval_exp_typ | split; [exact Hcode |]].
    eapply substituted_certified_universe_member.
    + exact HS.
    + exact (wf_sigma _ _ _ _ HA HB).
    + apply wf_exp_eq_sym. exact (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB).
    + eapply certify_sigma with (R := R) (S := S); try eassumption.
      intros M m. reflexivity.
Qed.


Local Lemma uniform_certified_equality_type_case Γ A P Q i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ P : A }} -> {{ Γ ⊢ Q : A }} ->
  certifies_typed_term Γ (a_typ i) A ->
  certifies_typed_term Γ A P -> certifies_typed_term Γ A Q ->
  certifies_typed_term Γ (a_typ i) (a_eq A P Q).
Proof.
  intros HA HP HQ HAr HPr HQr.
  apply substituted_certified_realization_lifts_to_uniform; [exact (wf_eq _ _ _ _ _ HA HP HQ) |].
  intros Δ σ ρ Hρ.
  pose proof (proj1 Hρ) as HS.
  destruct (HPr _ _ _ Hρ) as (a & p & Ha & Hp & Hpreal).
  destruct (HQr _ _ _ Hρ) as (a' & n & Ha' & Hn & Hnreal).
  pose proof (eval_exp_deterministic _ _ _ Ha _ Ha') as E. subst a'.
  destruct (nominal_certified_universe_realization _ _ _ _ _ _ _ HA HAr Hρ Ha) as (R & HG).
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (uniform_certified_realization_at_identity _ _ _ _ _ _ HAs
    (wf_exp_sub _ _ _ _ _ HS HP) Hpreal) as HPnom.
  pose proof (uniform_certified_realization_at_identity _ _ _ _ _ _ HAs
    (wf_exp_sub _ _ _ _ _ HS HQ) Hnreal) as HQnom.
  pose proof (nominal_certified_member_of_same_code _ _ _ _ _ _ _ _ HPnom HG) as HPm.
  pose proof (nominal_certified_member_of_same_code _ _ _ _ _ _ _ _ HQnom HG) as HQm.
  exists (d_univ i), (d_eq a p n).
  split; [apply eval_exp_typ | split; [eapply eval_exp_eq; eassumption |]].
  eapply substituted_certified_universe_member.
  - exact HS.
  - exact (wf_eq _ _ _ _ _ HA HP HQ).
  - apply wf_exp_eq_sym. exact (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HS HA HP HQ).
  - eapply certify_equation; [exact HG | exact HPm | exact HQm |].
    intros M m. reflexivity.
Qed.

Local Lemma uniform_certified_reflexivity_case Γ A M i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  certifies_typed_term Γ (a_typ i) A ->
  certifies_typed_term Γ A M ->
  certifies_typed_term Γ (a_eq A M M) (a_refl A M).
Proof.
  intros HA HM HAr HMr.
  apply substituted_certified_realization_lifts_to_uniform; [exact (wf_refl _ _ _ _ HA HM) |].
  intros Δ σ ρ Hρ.
  pose proof (proj1 Hρ) as HS.
  destruct (HMr _ _ _ Hρ) as (a & m & Ha & Hm & Hreal).
  destruct (nominal_certified_universe_realization _ _ _ _ _ _ _ HA HAr Hρ Ha) as (R & HG).
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (wf_exp_sub _ _ _ _ _ HS HM) as HMs.
  pose proof (uniform_certified_realization_at_identity _ _ _ _ _ _ HAs HMs Hreal) as Hnom.
  pose proof (nominal_certified_member_of_same_code _ _ _ _ _ _ _ _ Hnom HG) as HMm.
  pose proof (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HS HA HM HM) as ET.
  pose proof (type_substitution _ _ _ _ _ HS (wf_eq _ _ _ _ _ HA HM HM)) as HT.
  assert (HRefl : has_certified_realization Δ (a_eq (a_sub A σ) (a_sub M σ) (a_sub M σ))
    (a_refl (a_sub A σ) (a_sub M σ)) (d_eq a m m) (d_refl m)).
  {
    exists i, (certified_candidate (d_eq a m m) (equation_candidate Δ (a_sub A σ) (a_sub M σ) (a_sub M σ) R)). split.
    - eapply certify_equation; [exact HG | exact HMm | exact HMm | intros N n; reflexivity].
    - split.
      + eapply certified_evaluated_member.
        * exact (wf_refl _ _ _ _ HA HM).
        * exact (certified_environment_semantic _ _ _ _ Hρ).
        * eapply eval_exp_eq; eassumption.
        * now apply eval_exp_refl.
      + split; [exact (wf_refl _ _ _ _ HAs HMs) | right].
        exists (a_sub M σ), m. repeat split; eauto using expression_equality_reflexive, wf_refl.
  }
  exists (d_eq a m m), (d_refl m).
  split; [eapply eval_exp_eq; eassumption | split; [now apply eval_exp_refl |]].
  eapply has_certified_realization_term_conversion.
  - exact (wf_exp_sub _ _ _ _ _ HS (wf_refl _ _ _ _ HA HM)).
  - exact (wf_exp_eq_refl_sub _ _ _ _ _ _ HS HA HM).
  - exact (has_certified_realization_type_conversion _ _ _ _ _ _ _ HT (wf_exp_eq_sym _ _ _ _ ET) HRefl).
Qed.

Local Lemma uniform_certified_successor_case Γ M :
  {{ Γ ⊢ M : ℕ }} ->
  certifies_typed_term Γ a_nat M ->
  certifies_typed_term Γ a_nat (a_succ M).
Proof.
  intros HM HMr.
  apply substituted_certified_realization_lifts_to_uniform; [now apply wf_succ |].
  intros Δ σ ρ Hρ.
  pose proof (proj1 Hρ) as HS.
  destruct (HMr _ _ _ Hρ) as (a & m & Ha & Hm & Hreal).
  inversion Ha; subst a.
  pose proof (wf_nat _ (typing_context _ _ _ HM)) as HN.
  pose proof (type_substitution _ _ _ _ _ HS HN) as HNs.
  pose proof (wf_exp_sub _ _ _ _ _ HS HM) as HMs.
  pose proof (uniform_certified_realization_at_identity _ _ _ _ _ _ HNs HMs Hreal) as Hnom.
  pose proof (substitution_source _ _ _ HS) as HΔ.
  assert (HG : certified_type 0 Δ a_nat d_nat (certified_candidate d_nat (natural_candidate Δ))) by
    (apply certify_natural; [exact HΔ | intros N n; reflexivity]).
  pose proof (nominal_certified_member_of_same_code _ _ _ _ _ _ _ _ Hnom HG) as HC.
  assert (HSucc : has_certified_realization Δ a_nat (a_succ (a_sub M σ)) d_nat (d_succ m)).
  {
    exists 0, (certified_candidate d_nat (natural_candidate Δ)). split; [exact HG |].
    split.
    { eapply certified_evaluated_member.
      - exact (wf_succ _ _ HM).
      - exact (certified_environment_semantic _ _ _ _ Hρ).
      - apply eval_exp_nat.
      - now apply eval_exp_succ. }
    pose proof (wf_succ _ _ (natural_candidate_typed _ _ _ (proj2 HC))) as HT.
    eapply candidate_successor with (N := a_sub M σ);
      eauto using expression_equality_reflexive.
    exact (proj2 HC).
  }
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS)) as E.
  exists d_nat, (d_succ m). split; [apply eval_exp_nat | split; [now apply eval_exp_succ |]].
  eapply has_certified_realization_term_conversion.
  - exact (wf_exp_sub _ _ _ _ _ HS (wf_succ _ _ HM)).
  - exact (convert_equality _ _ _ _ _ _ (wf_exp_eq_succ_sub _ _ _ _ HS HM) HNs E).
  - exact (has_certified_realization_type_conversion _ _ _ _ _ _ _ HNs E HSucc).
Qed.


Local Lemma certified_environment_bind_argument Γ Δ Θ σ τ ρ A i a T N n :
  {{ Γ ⊢ A : Type@i }} ->
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  weakening_between Δ Θ τ ->
  eval_exp A ρ a ->
  certified_type i Θ (a_sub (a_sub A σ) τ) a T ->
  T N n ->
  realizes_environment uniform_certified_realization Θ (A :: Γ)
    (a_extend (a_compose σ τ) N) (extend_env ρ n).
Proof.
  intros HA Hρ HW Ha HG HN.
  pose proof (proj1 Hρ) as Hσ.
  pose proof (weakening_between_typed _ _ _ HW) as Hτ.
  pose proof (certified_environment_weakening_between _ _ _ _ _ _ Hρ HW) as Hρ'.
  pose proof (type_substitution _ _ _ _ _ (proj1 Hρ') HA) as HAt.
  pose proof (wf_exp_eq_sym _ _ _ _
    (type_substitution_composition _ _ _ _ _ _ _ Hτ Hσ HA)) as EAt.
  pose proof (certified_type_conversion _ _ _ _ _ _ HG HAt EAt) as HG'.
  assert (HR : has_certified_realization Θ (a_sub A (a_compose σ τ)) N a n) by
    (exists i, T; now split).
  exact (realized_environment_extend _ _ _ _ _ _ _ _ _ _
    uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
    Hρ' HA (has_certified_realization_typing _ _ _ _ _ HR) Ha (nominal_certified_realization_is_uniform _ _ _ _ _ HR)).
Qed.

Local Lemma uniform_certified_lambda_case Γ A B M i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ, A ⊢ M : B }} ->
  certifies_typed_term Γ (a_typ i) A ->
  certifies_typed_term (A :: Γ) (a_typ i) B ->
  certifies_typed_term (A :: Γ) B M ->
  certifies_typed_term Γ (a_pi A B) (a_fn A M).
Proof.
  intros HA HB HM HAr HBr HMr.
  pose proof (wf_fn _ _ _ _ _ HA HM) as HF.
  apply substituted_certified_realization_lifts_to_uniform; [exact HF |].
  intros Δ σ ρ Hρ.
  pose proof (proj1 Hρ) as Hσ.
  destruct (HAr _ _ _ Hρ) as (t & a & Ht & Ha & _).
  destruct (certified_binder_families _ _ _ _ _ _ _ _ HA HB HAr HBr Hρ Ha)
    as (R & S & HD & HT & HC).
  pose proof (type_substitution _ _ _ _ _ Hσ HA) as HAs.
  pose proof (type_substitution _ _ _ _ _ (lifted_substitution _ _ _ _ _ Hσ HA) HB) as HBs.
  pose proof (wf_pi _ _ _ _ HAs HBs) as Hpi.
  pose proof (wf_exp_eq_pi_sub _ _ _ _ _ _ Hσ HA HB) as Epi.
  pose proof (convert_term _ _ _ _ _ (wf_exp_sub _ _ _ _ _ Hσ HF) Hpi Epi) as HFσ.
  pose proof (eval_exp_pi _ _ _ B Ha) as Hcode.
  pose proof (certified_environment_semantic _ _ _ _ Hρ) as HEnv.
  pose proof (semantic_type_of_evaluated_type _ _ _ _ _ (wf_pi _ _ _ _ HA HB) HEnv Hcode) as Hsem.
  exists (d_pi a ρ B), (d_fn ρ M).
  split; [now apply eval_exp_pi | split; [apply eval_exp_fn |]].
  assert (HG : has_certified_realization Δ (a_pi (a_sub A σ) (a_sub B (Syntax.q σ)))
    (a_sub (a_fn A M) σ) (d_pi a ρ B) (d_fn ρ M)).
  {
    exists i, (certified_candidate (d_pi a ρ B) (function_candidate Δ (a_sub A σ) (a_sub B (Syntax.q σ)) ρ B R S)).
    split.
    - eapply certify_function; try eassumption. intros N n. reflexivity.
    - split.
      { exact (certified_evaluated_member _ _ _ _ _ _ HF HEnv Hcode (eval_exp_fn _ _ _)). }
      split; [exact HFσ |].
      intros Θ τ HW N n HR.
      pose proof (weakening_between_typed _ _ _ HW) as Hτ.
      pose proof (certified_environment_bind_argument _ _ _ _ _ _ _ _ _ _ _ _
        HA Hρ HW Ha (HD _ _ HW) HR) as Hρ'.
      destruct (HMr _ _ _ Hρ') as (b & m & Hb & Hm & Hbody).
      pose proof (proj1 Hρ') as HσN.
      pose proof (type_substitution _ _ _ _ _ HσN HB) as HB'.
      pose proof (wf_exp_sub _ _ _ _ _ HσN HM) as HM'.
      pose proof (uniform_certified_realization_at_identity _ _ _ _ _ _ HB' HM' Hbody) as Hbody'.
      pose proof (HC _ _ HW _ _ _ HR Hb) as Hcod.
      pose proof (nominal_certified_member_of_same_code _ _ _ _ _ _ _ _ Hbody' Hcod) as Hres.
      pose proof (proj2 (proj1 (certified_type_properties _ _ _ _ _ (HD _ _ HW))) _ _ HR) as HN.
      pose proof (type_substitution_composition _ _ _ _ _ _ _ Hτ Hσ HA) as EAs.
      pose proof (wf_sub_compose _ _ _ _ _ Hτ Hσ) as Hστ.
      pose proof (type_substitution _ _ _ _ _ Hστ HA) as HAn.
      pose proof (convert_term _ _ _ _ _ HN HAn (wf_exp_eq_sym _ _ _ _ EAs)) as HN'.
      pose proof (application_under_iterated_weakening _ _ _ _ _ _ _ _ _ _ Hσ Hτ HA HB HF HN') as Eapp.
      pose proof (substituted_lambda_application _ _ _ _ _ _ _ _ Hστ HA HB HM HN') as Eβ.
      destruct (apply_substituted_function _ _ _ _ _ _ _ _ Hτ HAs HBs HFσ HN) as (HBq & HApp).
      pose proof (wf_exp_eq_sym _ _ _ _ (type_lifted_substitution_at_argument _ _ _ _ _ _ _ _ _ _
        Hσ Hτ HA HB HN)) as EB.
      exists b, m. split; [exact Hb | split; [now apply eval_app_fn |]].
      exact (certified_candidate_expression_conversion _ _ _ _ _ Hcod _ _ _ HApp
        (convert_equality _ _ _ _ _ _ (wf_exp_eq_trans _ _ _ _ _ Eapp Eβ) HBq EB) Hres).
  }
  exact (has_certified_realization_type_conversion _ _ _ _ _ _ _
    (type_substitution _ _ _ _ _ Hσ (wf_pi _ _ _ _ HA HB)) (wf_exp_eq_sym _ _ _ _ Epi) HG).
Qed.


Local Lemma uniform_certified_projections Γ A B P i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ P : Σ A B }} ->
  certifies_typed_term Γ (a_typ i) A ->
  certifies_typed_term (A :: Γ) (a_typ i) B ->
  certifies_typed_term Γ (a_sigma A B) P ->
  certifies_typed_term Γ A (a_fst P) /\
  certifies_typed_term Γ (a_sub B (a_extend a_id (a_fst P))) (a_snd P).
Proof.
  intros HA HB HP HAr HBr HPr.
  pose proof (wf_fst _ _ _ _ _ HA HB HP) as HF.
  pose proof (wf_snd _ _ _ _ _ HA HB HP) as HSn.
  assert (Hcomponents : forall Δ σ ρ, realizes_environment uniform_certified_realization Δ Γ σ ρ ->
    exists a b x y,
      eval_exp A ρ a /\
      eval_exp (a_sub B (a_extend a_id (a_fst P))) ρ b /\
      eval_exp (a_fst P) ρ x /\ eval_exp (a_snd P) ρ y /\
      has_certified_realization Δ (a_sub A σ) (a_sub (a_fst P) σ) a x /\
      has_certified_realization Δ (a_sub (a_sub B (a_extend a_id (a_fst P))) σ) (a_sub (a_snd P) σ) b y).
  {
    intros Δ σ ρ Hρ.
    pose proof (proj1 Hρ) as Hσ.
    destruct (HPr _ _ _ Hρ) as (t & p & Ht & Hp & HPuniform).
    destruct (invert_eval_sigma _ _ _ _ Ht) as (a & -> & Ha).
    pose proof (type_substitution _ _ _ _ _ Hσ (wf_sigma _ _ _ _ HA HB)) as HΣ.
    destruct (uniform_certified_realization_at_identity _ _ _ _ _ _ HΣ
      (wf_exp_sub _ _ _ _ _ Hσ HP) HPuniform) as (j & T & HG & HPmem).
    destruct (certified_sigma_view _ _ _ _ _ _ _ HG)
      as (A' & B' & R & S & HA' & HB' & HG' & HD & Htot & HC & HE).
    apply HE in HPmem. destruct HPmem as [_ [_ H]].
    pose proof (context_weakening_id _ (substitution_source _ _ _ Hσ)) as HW.
    pose proof (weakening_between_canonical _ _ _ HW) as HW'.
    destruct (H _ _ HW') as (x & y & b & Hx & Hy & Hb & HR & HS).
    destruct (nominal_projection_typing _ _ _ _ _ _ _ Hσ HA HB HP) as (EF & ESn).
    pose proof (HD _ _ HW') as HDF.
    pose proof (HC _ _ HW' _ _ _ HR Hb) as HCS.
    destruct (nominal_certified_universe_realization _ _ _ _ _ _ _ HA HAr Hρ Ha) as (R' & HDA).
    pose proof (certified_types_with_same_code _ _ _ _ _ _ _ _ HDF HDA) as EAF.
    pose proof (type_substitution _ _ _ _ _ Hσ HA) as HAs.
    assert (HF0 : has_certified_realization Δ (a_sub A' a_id) {{{ fst P[σ][Id] }}} a x) by
      (exists j, (R Δ a_id); now split).
    assert (HFreal : has_certified_realization Δ (a_sub A σ) (a_sub (a_fst P) σ) a x).
    {
      eapply has_certified_realization_term_conversion.
      - exact (wf_exp_sub _ _ _ _ _ Hσ HF).
      - exact EF.
      - exact (has_certified_realization_type_conversion _ _ _ _ _ _ _
          (type_cumulativity _ _ _ _ HAs (Nat.le_max_r j i)) EAF HF0).
    }
    pose proof (nominal_certified_realization_is_uniform _ _ _ _ _ HFreal) as HFuniform.
    pose proof (wf_exp_sub _ _ _ _ _ Hσ HF) as HFσ.
    pose proof (realized_environment_extend _ _ _ _ _ _ _ _ _ _
      uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
      Hρ HA HFσ Ha HFuniform) as Hρ'.
    destruct (nominal_certified_universe_realization _ _ _ _ _ _ _ HB HBr Hρ' Hb) as (V & HGB).
    pose proof (certified_types_with_same_code _ _ _ _ _ _ _ _ HCS HGB) as EBS.
    pose proof (type_argument_substitution_composition _ _ _ _ _ _ _ _ Hσ HA HB HF) as EB.
    pose proof (type_substitution _ _ _ _ _ (proj1 Hρ') HB) as HBσ.
    pose proof (type_substitution _ _ _ _ _
      (typing_identity_extension _ _ _ _ HA HF) HB) as HT.
    pose proof (type_substitution _ _ _ _ _ Hσ HT) as HTσ.
    assert (HS0 : has_certified_realization Δ {{{ B'[Id,,fst P[σ][Id]] }}} {{{ snd P[σ][Id] }}} b y) by
      (exists j, (S Δ a_id {{{ fst P[σ][Id] }}} x); now split).
    pose proof (has_certified_realization_type_conversion _ _ _ _ _ _ _
      (type_cumulativity _ _ _ _ HBσ (Nat.le_max_r j i)) EBS HS0) as HS1.
    exists a, b, x, y. repeat split; try assumption.
    - eapply eval_exp_sub; [eapply eval_sub_extend; [apply eval_sub_id |] | exact Hb].
      eapply eval_exp_fst; eassumption.
    - eapply eval_exp_fst; eassumption.
    - eapply eval_exp_snd; eassumption.
    - eapply has_certified_realization_term_conversion.
      + exact (wf_exp_sub _ _ _ _ _ Hσ HSn).
      + exact ESn.
      + exact (has_certified_realization_type_conversion _ _ _ _ _ _ _ HTσ (wf_exp_eq_sym _ _ _ _ EB) HS1).
  }
  split.
  - apply substituted_certified_realization_lifts_to_uniform; [exact HF |].
    intros Δ σ ρ Hρ. destruct (Hcomponents _ _ _ Hρ) as (a & b & x & y & Ha & _ & Hx & _ & HR & _).
    exists a, x. auto.
  - apply substituted_certified_realization_lifts_to_uniform; [exact HSn |].
    intros Δ σ ρ Hρ. destruct (Hcomponents _ _ _ Hρ) as (a & b & x & y & _ & Hb & _ & Hy & _ & HR).
    exists b, y. auto.
Qed.

Local Lemma uniform_certified_universe_cumulativity Γ A i j :
  i <= j ->
  {{ Γ ⊢ A : Type@i }} ->
  certifies_typed_term Γ (a_typ i) A ->
  certifies_typed_term Γ (a_typ j) A.
Proof.
  intros Hle HA HAr.
  pose proof (type_cumulativity _ _ _ _ HA Hle) as HAj.
  apply substituted_certified_realization_lifts_to_uniform; [exact HAj |].
  intros Δ σ ρ Hρ.
  destruct (HAr _ _ _ Hρ) as (u & a & Hu & Ha & _).
  destruct (nominal_certified_universe_realization _ _ _ _ _ _ _ HA HAr Hρ Ha) as (R & HG).
  exists (d_univ j), a. split; [apply eval_exp_typ | split; [exact Ha |]].
  eapply substituted_certified_universe_member.
  - exact (proj1 Hρ).
  - exact HAj.
  - apply expression_equality_reflexive. exact (type_substitution _ _ _ _ _ (proj1 Hρ) HAj).
  - exact (certified_type_raise _ _ _ _ _ _ Hle HG).
Qed.

Local Lemma uniform_certified_universe_case Γ i :
  {{ ⊢ Γ }} ->
  certifies_typed_term Γ (a_typ (S i)) (a_typ i).
Proof.
  intros HΓ Δ σ ρ Hρ.
  pose proof (proj1 Hρ) as HS.
  pose proof (substitution_source _ _ _ HS) as HΔ.
  pose proof (wf_exp_eq_typ_sub _ _ _ (S i) HS) as ET.
  pose proof (wf_exp_eq_sym _ _ _ _ ET) as ET'.
  pose proof (type_substitution _ _ _ _ _ HS (wf_typ _ (S i) HΓ)) as HT.
  pose proof (wf_exp_sub _ _ _ _ _ HS (wf_typ _ i HΓ)) as HM.
  exists (d_univ (S i)), (d_univ i). split; [apply eval_exp_typ | split; [apply eval_exp_typ |]].
  eapply uniform_certified_realization_term_conversion.
  - exact HM.
  - exact (convert_equality _ _ _ _ _ _ (wf_exp_eq_typ_sub _ _ _ i HS) HT ET').
  - exact (uniform_certified_realization_type_conversion _ _ _ _ _ _ _ HT ET'
      (uniform_certified_typing_of_universe _ _ HΔ)).
Qed.

Local Lemma uniform_certified_natural_case Γ :
  {{ ⊢ Γ }} ->
  certifies_typed_term Γ (a_typ 0) a_nat.
Proof.
  intros HΓ Δ σ ρ Hρ.
  pose proof (proj1 Hρ) as HS.
  pose proof (substitution_source _ _ _ HS) as HΔ.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_typ_sub _ _ _ 0 HS)) as ET.
  pose proof (type_substitution _ _ _ _ _ HS (wf_typ _ 0 HΓ)) as HT.
  exists (d_univ 0), d_nat. split; [apply eval_exp_typ | split; [apply eval_exp_nat |]].
  eapply uniform_certified_realization_term_conversion.
  - exact (wf_exp_sub _ _ _ _ _ HS (wf_nat _ HΓ)).
  - exact (convert_equality _ _ _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS) HT ET).
  - exact (uniform_certified_realization_type_conversion _ _ _ _ _ _ _ HT ET
      (uniform_certified_typing_of_natural _ HΔ)).
Qed.

Local Lemma uniform_certified_zero_case Γ :
  {{ ⊢ Γ }} ->
  certifies_typed_term Γ a_nat a_zero.
Proof.
  intros HΓ Δ σ ρ Hρ.
  pose proof (proj1 Hρ) as HS.
  pose proof (substitution_source _ _ _ HS) as HΔ.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS)) as ET.
  pose proof (type_substitution _ _ _ _ _ HS (wf_nat _ HΓ)) as HT.
  exists d_nat, d_zero. split; [apply eval_exp_nat | split; [apply eval_exp_zero |]].
  eapply uniform_certified_realization_term_conversion.
  - exact (wf_exp_sub _ _ _ _ _ HS (wf_zero _ HΓ)).
  - exact (convert_equality _ _ _ _ _ _ (wf_exp_eq_zero_sub _ _ _ HS) HT ET).
  - exact (uniform_certified_realization_type_conversion _ _ _ _ _ _ _ HT ET
      (uniform_certified_typing_of_zero _ HΔ)).
Qed.


Local Lemma uniform_certified_pair_case Γ A B M N i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  {{ Γ ⊢ N : B[Id,,M] }} ->
  certifies_typed_term Γ (a_typ i) A ->
  certifies_typed_term (A :: Γ) (a_typ i) B ->
  certifies_typed_term Γ A M ->
  certifies_typed_term Γ (a_sub B (a_extend a_id M)) N ->
  certifies_typed_term Γ (a_sigma A B) (a_pair M A N B).
Proof.
  intros HA HB HM HN HAr HBr HMr HNr.
  pose proof (wf_pair _ _ _ _ _ _ HA HB HM HN) as HP.
  pose proof (type_substitution _ _ _ _ _ (typing_identity_extension _ _ _ _ HA HM) HB) as HBT.
  apply substituted_certified_realization_lifts_to_uniform; [exact HP |].
  intros Δ σ ρ Hρ.
  pose proof (proj1 Hρ) as Hσ.
  destruct (HMr _ _ _ Hρ) as (a & x & Ha & Hx & _).
  destruct (HNr _ _ _ Hρ) as (b & y & HOut & Hy & _).
  assert (HBody : eval_exp B (extend_env ρ x) b).
  {
    destruct (invert_eval_substitution _ _ _ _ HOut) as (η & Hη & HE).
    inversion Hη; subst.
    match goal with Hid : eval_sub a_id _ _ |- _ => inversion Hid; subst end.
    reconcile_values. assumption.
  }
  destruct (certified_binder_families _ _ _ _ _ _ _ _ HA HB HAr HBr Hρ Ha)
    as (R & S & HD & HT & HC).
  pose proof (type_substitution _ _ _ _ _ Hσ HA) as HAs.
  pose proof (type_substitution _ _ _ _ _ (lifted_substitution _ _ _ _ _ Hσ HA) HB) as HBs.
  pose proof (wf_sigma _ _ _ _ HAs HBs) as HΣ.
  pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ Hσ HA HB) as EΣ.
  pose proof (convert_term _ _ _ _ _ (wf_exp_sub _ _ _ _ _ Hσ HP) HΣ EΣ) as HPσ.
  pose proof (eval_exp_sigma _ _ _ B Ha) as Hcode.
  pose proof (certified_environment_semantic _ _ _ _ Hρ) as HEnv.
  pose proof (semantic_type_of_evaluated_type _ _ _ _ _ (wf_sigma _ _ _ _ HA HB) HEnv Hcode) as Hsem.
  exists (d_sigma a ρ B), (d_pair x y).
  split; [now apply eval_exp_sigma | split; [now apply eval_exp_pair |]].
  assert (HG : has_certified_realization Δ (a_sigma (a_sub A σ) (a_sub B (Syntax.q σ)))
    (a_sub (a_pair M A N B) σ) (d_sigma a ρ B) (d_pair x y)).
  {
    exists i, (certified_candidate (d_sigma a ρ B) (sigma_candidate Δ (a_sub A σ) (a_sub B (Syntax.q σ)) ρ B R S)).
    split.
    - eapply certify_sigma with (R := R) (S := S); try eassumption. intros P p. reflexivity.
    - split.
      { eapply certified_evaluated_member; [exact HP | exact HEnv | exact Hcode | now apply eval_exp_pair]. }
      split; [exact HPσ |].
      intros Θ τ HW.
      pose proof (weakening_between_typed _ _ _ HW) as Hτ.
      pose proof (certified_environment_weakening_between _ _ _ _ _ _ Hρ HW) as Hρ'.
      pose proof (proj1 Hρ') as HS.
      destruct (HMr _ _ _ Hρ') as (a' & x' & Ha' & Hx' & HMr').
      destruct (HNr _ _ _ Hρ') as (b' & y' & Hb' & Hy' & HNr').
      pose proof (eval_exp_deterministic _ _ _ Ha _ Ha') as Ea. subst a'.
      pose proof (eval_exp_deterministic _ _ _ Hx _ Hx') as Ex. subst x'.
      pose proof (eval_exp_deterministic _ _ _ HOut _ Hb') as Eb. subst b'.
      pose proof (eval_exp_deterministic _ _ _ Hy _ Hy') as Ey. subst y'.
      destruct (pair_beta_under_iterated_weakening _ _ _ _ _ _ _ _ _ _
        Hσ Hτ HA HB HM HN) as (HF & EF & HSnd & ESnd).
      pose proof (type_substitution _ _ _ _ _ HS HA) as HDomain.
      pose proof (uniform_certified_realization_at_identity _ _ _ _ _ _ HDomain
        (wf_exp_sub _ _ _ _ _ HS HM) HMr') as HMnom.
      pose proof (nominal_certified_member_of_same_code _ _ _ _ _ _ _ _ HMnom (HD _ _ HW)) as HMmem.
      pose proof (type_substitution _ _ _ _ _ Hτ HAs) as HFType.
      pose proof (type_substitution_composition _ _ _ _ _ _ _ Hτ Hσ HA) as EType.
      pose proof (convert_term _ _ _ _ _ HF HFType EType) as HF'.
      pose proof (certified_candidate_expression_conversion _ _ _ _ _ (HD _ _ HW)
        _ _ _ HF' (convert_equality _ _ _ _ _ _ EF HFType EType) HMmem) as HX.
      pose proof (HC _ _ HW _ _ _ HX HBody) as HCS.
      pose proof (uniform_certified_realization_at_identity _ _ _ _ _ _
        (type_substitution _ _ _ _ _ HS HBT) (wf_exp_sub _ _ _ _ _ HS HN) HNr') as HNnom.
      pose proof (nominal_certified_member_of_same_code _ _ _ _ _ _ _ _ HNnom HCS) as HNmem.
      pose proof (wf_exp_eq_sym _ _ _ _
        (type_lifted_substitution_at_argument _ _ _ _ _ _ _ _ _ _ Hσ Hτ HA HB HF')) as EBody.
      pose proof (proj1 (proj1 (certified_type_properties _ _ _ _ _ HCS))) as HCSt.
      exists x, y, b. repeat split; auto using eval_fst_pair, eval_snd_pair.
      exact (certified_candidate_expression_conversion _ _ _ _ _ HCS _ _ _
        (convert_term _ _ _ _ _ HSnd HCSt EBody)
        (convert_equality _ _ _ _ _ _ ESnd HCSt EBody) HNmem).
  }
  exact (has_certified_realization_type_conversion _ _ _ _ _ _ _
    (type_substitution _ _ _ _ _ Hσ (wf_sigma _ _ _ _ HA HB)) (wf_exp_eq_sym _ _ _ _ EΣ) HG).
Qed.


Local Definition certified_subsumption Γ A B :=
  forall Δ σ ρ a M m,
    realizes_environment uniform_certified_realization Δ Γ σ ρ ->
    eval_exp A ρ a ->
    has_certified_realization Δ (a_sub A σ) M a m ->
    exists b, eval_exp B ρ b /\ has_certified_realization Δ (a_sub B σ) M b m.

Local Lemma certified_subsumption_trans Γ A B C :
  certified_subsumption Γ A B -> certified_subsumption Γ B C ->
  certified_subsumption Γ A C.
Proof.
  intros H K Δ σ ρ a M m Hρ Ha Hm.
  destruct (H _ _ _ _ _ _ Hρ Ha Hm) as (b & Hb & Hmb).
  exact (K _ _ _ _ _ _ Hρ Hb Hmb).
Qed.

Local Lemma certified_universe_subsumption Γ i j :
  i <= j -> certified_subsumption Γ (a_typ i) (a_typ j).
Proof.
  intros Hij Δ σ ρ a M m Hρ Ha Hmem.
  inversion Ha; subst a.
  pose proof (proj1 Hρ) as HS.
  pose proof (substitution_source _ _ _ HS) as HΔ.
  destruct (has_certified_realization_type_conversion _ _ _ _ _ _ _
     (wf_typ Δ i HΔ) (wf_exp_eq_typ_sub _ _ _ i HS) Hmem) as (k & R & HT & HM).
  destruct (certified_type_of_universe_member _ _ _ _ _ _ HT HM) as (S & H).
  pose proof (certified_type_raise _ _ _ _ _ _ Hij H) as H'.
  pose proof (certified_type_as_universe_member _ _ _ _ _ H') as Hmem'.
  exists (d_univ j). split; [apply eval_exp_typ |].
  eapply has_certified_realization_type_conversion;
    [| exact (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_typ_sub _ _ _ j HS)) | exact Hmem'].
  exact (type_substitution _ _ _ _ _ HS (wf_typ _ j (substitution_target _ _ _ HS))).
Qed.

Local Lemma certified_equal_types_agree_on_candidates i Γ A B a b Q R S :
  certified_type i Γ A a R -> certified_type i Γ B b S ->
  {{ Γ ⊢ A ≈ B : Type@i }} ->
  semantic_type i a b Q ->
  candidates_equivalent R S.
Proof.
  intros HL HR EA HQ M m.
  pose proof (proj1 (proj1 (certified_type_properties _ _ _ _ _ HL))) as HA.
  pose proof (proj1 (proj1 (certified_type_properties _ _ _ _ _ HR))) as HB.
  split; intro HM.
  - pose proof (semantic_member_in_relation _ _ _ _ _ HQ
      (certified_layer_member _ _ _ _ _ _ HL _ _ HM)) as Hrel.
    eapply nominal_certified_member_of_same_code; [| exact HR].
    exact (nominal_certified_code_conversion _ _ _ _ _ _ _ _ _ _ _
      HB EA HQ Hrel (ex_intro _ i (ex_intro _ R (conj HL HM)))).
  - pose proof (semantic_type_sym _ _ _ _ HQ) as HQ'.
    pose proof (semantic_member_in_relation _ _ _ _ _ HQ'
      (certified_layer_member _ _ _ _ _ _ HR _ _ HM)) as Hrel.
    eapply nominal_certified_member_of_same_code; [| exact HL].
    exact (nominal_certified_code_conversion _ _ _ _ _ _ _ _ _ _ _
      HA (wf_exp_eq_sym _ _ _ _ EA) HQ' Hrel (ex_intro _ i (ex_intro _ S (conj HR HM)))).
Qed.

Local Lemma certified_dependent_candidate_subsumption
    Γ Δ σ ρ A A' B B' i a a' R R' S S' :
  {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ A' : Type@i }} ->
  {{ Γ ⊢ A ≈ A' : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  eval_exp A ρ a -> eval_exp A' ρ a' ->
  certified_subsumption (A' :: Γ) B B' ->
  (forall Θ τ, weakening_between Δ Θ τ ->
    certified_type i Θ (a_sub (a_sub A σ) τ) a (R Θ τ)) ->
  (forall Θ τ, weakening_between Δ Θ τ ->
    certified_type i Θ (a_sub (a_sub A' σ) τ) a' (R' Θ τ)) ->
  (forall Θ τ, weakening_between Δ Θ τ -> forall N n b,
    R Θ τ N n -> eval_exp B (extend_env ρ n) b ->
    certified_type i Θ (a_sub (a_sub B (Syntax.q σ)) (a_extend τ N)) b (S Θ τ N n)) ->
  (forall Θ τ, weakening_between Δ Θ τ -> forall N n b,
    R' Θ τ N n -> eval_exp B' (extend_env ρ n) b ->
    certified_type i Θ (a_sub (a_sub B' (Syntax.q σ)) (a_extend τ N)) b (S' Θ τ N n)) ->
  (forall Θ τ, weakening_between Δ Θ τ -> candidates_equivalent (R Θ τ) (R' Θ τ)) /\
  (forall Θ τ, weakening_between Δ Θ τ -> forall N n b M m,
    R Θ τ N n -> eval_exp B (extend_env ρ n) b -> S Θ τ N n M m ->
    exists b', eval_exp B' (extend_env ρ n) b' /\ S' Θ τ N n M m).
Proof.
  intros HA HA' E HB Hρ Ha Ha' Hsub HD HD' HC HC'.
  pose proof (proj1 Hρ) as HS.
  pose proof (proj1 (proj2 (proj2 (proj2 declarative_interpretation))) _ _ _ _ E) as Hsem.
  destruct (interpreted_terms_as_types _ _ _ _ Hsem _ _
    (certified_environment_semantic _ _ _ _ Hρ)) as (x & y & Q & Hx & Hy & HQ).
  reconcile_values.
  assert (HDA : forall Θ τ, weakening_between Δ Θ τ -> candidates_equivalent (R Θ τ) (R' Θ τ)).
  {
    intros Θ τ HW.
    pose proof (weakening_between_typed _ _ _ HW) as HT.
    pose proof (type_substitution_congruence _ _ _ _ _ _ _ HS
      (substitution_equality_reflexive _ _ _ HS) E) as E0.
    pose proof (type_substitution_congruence _ _ _ _ _ _ _ HT
      (substitution_equality_reflexive _ _ _ HT) E0) as E1.
    exact (certified_equal_types_agree_on_candidates _ _ _ _ _ _ _ _ _
      (HD _ _ HW) (HD' _ _ HW) E1 HQ).
  }
  split; [exact HDA |].
  intros Θ τ HW N n b M m HN Hb HM.
  pose proof (proj1 (HDA _ _ HW _ _) HN) as HN'.
  pose proof (weakening_between_typed _ _ _ HW) as HT.
  pose proof (certified_environment_bind_argument _ _ _ _ _ _ _ _ _ _ _ _
    HA' Hρ HW Ha' (HD' _ _ HW) HN') as Hρ'.
  pose proof (HC _ _ HW _ _ _ HN Hb) as HCode.
  pose proof (proj2 (proj1 (certified_type_properties _ _ _ _ _ (HD _ _ HW))) _ _ HN) as HNst.
  pose proof (wf_sub_compose _ _ _ _ _ HT HS) as HST.
  pose proof (type_substitution _ _ _ _ _ HST HA) as HAn.
  pose proof (type_substitution_composition _ _ _ _ _ _ _ HT HS HA) as EDom.
  pose proof (convert_term _ _ _ _ _ HNst HAn (wf_exp_eq_sym _ _ _ _ EDom)) as HNn.
  pose proof (wf_sub_extend _ _ _ _ _ _ HST HA HNn) as HSTN.
  pose proof (type_substitution _ _ _ _ _ HSTN HB) as HBn.
  pose proof (type_lifted_substitution_at_argument _ _ _ _ _ _ _ _ _ _
    HS HT HA HB HNst) as ECod.
  pose proof (certified_type_conversion _ _ _ _ _ _ HCode HBn ECod) as HCn.
  destruct (Hsub _ _ _ _ _ _ Hρ' Hb (ex_intro _ i (ex_intro _ _ (conj HCn HM))))
    as (b' & Hb' & HResult).
  exists b'. split; [exact Hb' |].
  exact (nominal_certified_member_of_same_code _ _ _ _ _ _ _ _ HResult (HC' _ _ HW _ _ _ HN' Hb')).
Qed.

Local Lemma certified_dependent_subsumption Γ i A A' B B' :
  {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ A' : Type@i }} ->
  {{ Γ ⊢ A ≈ A' : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} -> {{ Γ, A' ⊢ B' : Type@i }} ->
  {{ Γ, A' ⊢ B ⊆ B' }} ->
  certifies_typed_term Γ (a_typ i) A ->
  certifies_typed_term Γ (a_typ i) A' ->
  certifies_typed_term (A :: Γ) (a_typ i) B ->
  certifies_typed_term (A' :: Γ) (a_typ i) B' ->
  certified_subsumption (A' :: Γ) B B' ->
  certified_subsumption Γ (a_pi A B) (a_pi A' B') /\
  certified_subsumption Γ (a_sigma A B) (a_sigma A' B').
Proof.
  intros HA HA' EA HB HB' HSub HAr HAr' HBr HBr' Hsub.
  split.
  all: intros Δ σ ρ c F f Hρ Hc HF;
    pose proof (proj1 Hρ) as Hσ;
    pose proof (certified_environment_semantic _ _ _ _ Hρ) as HEnv;
    destruct (HAr _ _ _ Hρ) as (u & a & Hu & Ha & _);
    destruct (HAr' _ _ _ Hρ) as (u' & a' & Hu' & Ha' & _);
    destruct (certified_binder_families _ _ _ _ _ _ _ _ HA HB HAr HBr Hρ Ha)
      as (R & S & HD & HT & HC);
    destruct (certified_binder_families _ _ _ _ _ _ _ _ HA' HB' HAr' HBr' Hρ Ha')
      as (R' & S' & HD' & HT' & HC');
    destruct (certified_dependent_candidate_subsumption _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      HA HA' EA HB Hρ Ha Ha' Hsub HD HD' HC HC') as (HDA & HCA);
    pose proof (type_substitution _ _ _ _ _ Hσ HA) as HAs;
    pose proof (type_substitution _ _ _ _ _ Hσ HA') as HAs';
    pose proof (type_substitution _ _ _ _ _ (lifted_substitution _ _ _ _ _ Hσ HA) HB) as HBs;
    pose proof (type_substitution _ _ _ _ _ (lifted_substitution _ _ _ _ _ Hσ HA') HB') as HBs'.
  - pose proof (eval_exp_pi _ _ _ B Ha) as HLeft.
    pose proof (eval_exp_pi _ _ _ B' Ha') as HRight.
    pose proof (eval_exp_deterministic _ _ _ HLeft _ Hc) as Ec; subst c.
    pose proof (semantic_type_of_evaluated_type _ _ _ _ _ (wf_pi _ _ _ _ HA HB) HEnv HLeft) as HV.
    pose proof (semantic_type_of_evaluated_type _ _ _ _ _ (wf_pi _ _ _ _ HA' HB') HEnv HRight) as HV'.
    pose proof (wf_subtyp_pi _ _ _ _ _ _ HA HA' EA HB HB' HSub) as HS.
    pose proof (wf_exp_eq_pi_sub _ _ _ _ _ _ Hσ HA' HB') as ES.
    pose proof (type_substitution _ _ _ _ _ Hσ (wf_pi _ _ _ _ HA' HB')) as HTR.
    assert (Hsrc : certified_type i Δ (a_pi (a_sub A σ) (a_sub B (Syntax.q σ)))
      (d_pi a ρ B) (certified_candidate (d_pi a ρ B) (function_candidate Δ (a_sub A σ) (a_sub B (Syntax.q σ)) ρ B R S))).
    { eapply certify_function with (R := R) (S := S); try eassumption. intros M m. reflexivity. }
    destruct (nominal_certified_member_of_same_code _ _ _ _ _ _ _ _ HF Hsrc) as [Hgood [HFt HAct]].
    pose proof (certified_inhabitant_of_supertype _ _ _ _ _ _ _ HS HEnv HLeft HRight Hgood) as Hgood'.
    pose proof (wf_exp_subtyp _ _ _ _ _ (has_certified_realization_typing _ _ _ _ _ HF) HTR
      (subtyping_under_substitution _ _ _ HS _ _ Hσ)) as HFsub.
    pose proof (convert_term _ _ _ _ _ HFsub (wf_pi _ _ _ _ HAs' HBs') ES) as HFsub'.
    exists (d_pi a' ρ B'). split; [exact HRight |].
    eapply has_certified_realization_type_conversion; [exact HTR | exact (wf_exp_eq_sym _ _ _ _ ES) |].
    exists i, (certified_candidate (d_pi a' ρ B')
      (function_candidate Δ (a_sub A' σ) (a_sub B' (Syntax.q σ)) ρ B' R' S')).
    split.
    + eapply certify_function with (R := R') (S := S'); try eassumption. intros M m. reflexivity.
    + split; [exact Hgood' | split; [exact HFsub' |]].
      intros Θ τ HW N n HN.
      pose proof (proj2 (HDA _ _ HW _ _) HN) as HN0.
      destruct (HAct _ _ HW _ _ HN0) as (b & r & Hb & Hr & HrR).
      destruct (HCA _ _ HW _ _ _ _ _ HN0 Hb HrR) as (b' & Hb' & Hnew).
      exists b', r. repeat split; assumption.
  - pose proof (eval_exp_sigma _ _ _ B Ha) as HLeft.
    pose proof (eval_exp_sigma _ _ _ B' Ha') as HRight.
    pose proof (eval_exp_deterministic _ _ _ HLeft _ Hc) as Ec; subst c.
    pose proof (semantic_type_of_evaluated_type _ _ _ _ _ (wf_sigma _ _ _ _ HA HB) HEnv HLeft) as HV.
    pose proof (semantic_type_of_evaluated_type _ _ _ _ _ (wf_sigma _ _ _ _ HA' HB') HEnv HRight) as HV'.
    pose proof (wf_subtyp_sigma _ _ _ _ _ _ HA HA' EA HB HB' HSub) as HS.
    pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ Hσ HA' HB') as ES.
    pose proof (type_substitution _ _ _ _ _ Hσ (wf_sigma _ _ _ _ HA' HB')) as HTR.
    assert (Hsrc : certified_type i Δ (a_sigma (a_sub A σ) (a_sub B (Syntax.q σ)))
      (d_sigma a ρ B) (certified_candidate (d_sigma a ρ B) (sigma_candidate Δ (a_sub A σ) (a_sub B (Syntax.q σ)) ρ B R S))).
    { eapply certify_sigma with (R := R) (S := S); try eassumption. intros M m. reflexivity. }
    destruct (nominal_certified_member_of_same_code _ _ _ _ _ _ _ _ HF Hsrc) as [Hgood [HFt HAct]].
    pose proof (certified_inhabitant_of_supertype _ _ _ _ _ _ _ HS HEnv HLeft HRight Hgood) as Hgood'.
    pose proof (wf_exp_subtyp _ _ _ _ _ (has_certified_realization_typing _ _ _ _ _ HF) HTR
      (subtyping_under_substitution _ _ _ HS _ _ Hσ)) as HFsub.
    pose proof (convert_term _ _ _ _ _ HFsub (wf_sigma _ _ _ _ HAs' HBs') ES) as HFsub'.
    exists (d_sigma a' ρ B'). split; [exact HRight |].
    eapply has_certified_realization_type_conversion; [exact HTR | exact (wf_exp_eq_sym _ _ _ _ ES) |].
    exists i, (certified_candidate (d_sigma a' ρ B')
      (sigma_candidate Δ (a_sub A' σ) (a_sub B' (Syntax.q σ)) ρ B' R' S')).
    split.
    + eapply certify_sigma with (R := R') (S := S'); try eassumption. intros M m. reflexivity.
    + split; [exact Hgood' | split; [exact HFsub' |]].
      intros Θ τ HW.
      destruct (HAct _ _ HW) as (x & y & b & Hx & Hy & Hb & HNx & HSx).
      destruct (HCA _ _ HW _ _ _ _ _ HNx Hb HSx) as (b' & Hb' & Hnew).
      exists x, y, b'. repeat split; try assumption. now apply (HDA _ _ HW _ _).
Qed.

Local Lemma certified_natural_predecessor n :
  semantic_member d_nat (d_succ n) -> semantic_member d_nat n.
Proof.
  intro H.
  pose proof (semantic_member_in_relation _ _ _ _ _ (semantic_natural 0) H) as HS.
  inversion HS; subst.
  - exists 0, natural_values_agree. split; [exact (semantic_natural 0) | assumption].
  - match goal with Hbad : neutral_values_agree _ _ |- _ =>
      destruct Hbad as (? & ? & ? & ? & E & _); discriminate E end.
Qed.

Local Lemma certified_natural_neutral a k :
  semantic_member d_nat (d_neut a k) -> neutrals_agree k k.
Proof.
  intro H.
  pose proof (semantic_member_in_relation _ _ _ _ _ (semantic_natural 0) H) as Hne.
  inversion Hne; subst.
  match goal with H0 : neutral_values_agree _ _ |- _ =>
    destruct H0 as (? & ? & ? & ? & E & E' & Hk); inversion E; inversion E'; subst; exact Hk
  end.
Qed.

Local Lemma certified_natrec_neutral_agreement Γ Δ σ ρ A MZ MS i a k bz mz :
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Γ ⊢ MZ : A[Id,,zero] }} ->
  {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  eval_exp A (extend_env ρ d_zero) bz ->
  eval_exp MZ ρ mz ->
  semantic_member d_nat (d_neut a k) ->
  neutrals_agree (d_natrec ρ A mz MS k) (d_natrec ρ A mz MS k).
Proof.
  intros HA HZ HStep Hρ Hbz Hmz Hn.
  pose proof (certified_environment_semantic _ _ _ _ Hρ) as HEnv.
  pose proof (proj1 (proj2 (proj2 declarative_interpretation)) _ _ _ HA) as H0.
  pose proof (interpreted_terms_as_types _ _ _ _ H0) as HMot.
  pose proof (proj1 (proj2 (proj2 declarative_interpretation)) _ _ _ HStep) as HS.
  pose proof (interpreted_natural_motive _ _ _ _ _ _ HMot HEnv) as HM.
  pose proof (interpreted_natural_step _ _ _ _ _ _ _ _ HMot HS HEnv) as HStepS.
  destruct (HM _ _ natural_values_zero) as (b & b' & Q & Hb & Hb' & HQ).
  reconcile_values.
  eapply natural_neutral_recursion_readback; [exact HM | exact HStepS | | |].
  - repeat split; eassumption.
  - eapply semantic_member_in_relation; [exact HQ |].
    exact (certified_evaluated_member _ _ _ _ _ _ HZ HEnv
      (eval_at_argument _ _ _ _ _ (eval_exp_zero ρ) Hbz) Hmz).
  - exact (certified_natural_neutral _ _ Hn).
Qed.
Local Lemma certified_environment_fresh_binder Γ Δ σ ρ A B a i R :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Δ ⊢ B : Type@i }} ->
  {{ Δ ⊢ A[σ] ≈ B : Type@i }} ->
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  eval_exp A ρ a ->
  certified_type i Δ (a_sub A σ) a R ->
  realizes_environment uniform_certified_realization (B :: Δ) (A :: Γ) (Syntax.q σ)
    (extend_env ρ (d_neut a (d_var (length Δ)))).
Proof.
  intros HA HB EB Hρ Ha HG.
  pose proof (proj1 Hρ) as HS.
  pose proof (weakening_of_last_binder _ _ _ HB) as HW.
  pose proof (weakening_between_typed _ _ _ HW) as HT.
  pose proof (certified_environment_weakening_between _ _ _ _ _ _ Hρ HW) as Hρw.
  pose proof (certified_type_conversion _ _ _ _ _ _ HG HB EB) as HGB.
  destruct (certified_type_weakening _ _ _ _ _ HGB _ _ HW) as (T & HTy & _).
  pose proof (wf_sub_compose _ _ _ _ _ HT HS) as HST.
  pose proof (type_substitution _ _ _ _ _ HST HA) as HAw.
  assert (E : {{ Δ, B ⊢ B[Wk] ≈ A[σ∘Wk] : Type@i }}).
  {
    eapply wf_exp_eq_trans.
    - exact (type_substitution_congruence _ _ _ _ _ _ _ HT
        (substitution_equality_reflexive _ _ _ HT) (wf_exp_eq_sym _ _ _ _ EB)).
    - exact (wf_exp_eq_sym _ _ _ _
        (type_substitution_composition _ _ _ _ _ _ _ HT HS HA)).
  }
  pose proof (certified_type_conversion _ _ _ _ _ _ HTy HAw E) as HGw.
  pose proof (wf_vlookup _ _ _ (substitution_source _ _ _ HT) (here B Δ)) as Hv.
  pose proof (convert_term _ _ _ _ _ Hv HAw E) as Hv'.
  pose proof (typed_readback_reflected_variable _ _ _ (here B Δ)) as Hne.
  cbn in Hne. rewrite Nat.sub_0_r in Hne.
  pose proof (typed_readback_type_conversion _ _ _ _ _ _ _ _ _ _ HAw E Hne) as Hne'.
  pose proof (certified_reflection _ _ _ _ _ _ _ HGw Hv' Hne' (related_variable (length Δ))) as Hval.
  assert (Hnom : has_certified_realization (B :: Δ) (a_sub A (a_compose σ a_weaken))
    (a_var 0) a (d_neut a (d_var (length Δ)))) by (exists i, T; now split).
  exact (realized_environment_extend _ _ _ _ _ _ _ _ _ _
    uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
    Hρw HA Hv' Ha (nominal_certified_realization_is_uniform _ _ _ _ _ Hnom)).
Qed.


Local Lemma certified_environment_lift_natural Γ Δ σ ρ :
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  realizes_environment uniform_certified_realization (a_nat :: Δ) (a_nat :: Γ) (Syntax.q σ)
    (extend_env ρ (d_neut d_nat (d_var (length Δ)))).
Proof.
  intro Hρ.
  pose proof (proj1 Hρ) as HS.
  pose proof (substitution_source _ _ _ HS) as HΔ.
  pose proof (wf_nat Γ (substitution_target _ _ _ HS)) as HA.
  pose proof (wf_nat Δ HΔ) as HB.
  pose proof (wf_exp_eq_nat_sub _ _ _ HS) as EB.
  assert (HG : certified_type 0 Δ a_nat d_nat (certified_candidate d_nat (natural_candidate Δ))).
  { apply certify_natural; [exact HΔ | intros M m; reflexivity]. }
  pose proof (certified_type_conversion _ _ _ _ _ _ HG
    (type_substitution _ _ _ _ _ HS HA) (wf_exp_eq_sym _ _ _ _ EB)) as HG'.
  exact (certified_environment_fresh_binder _ _ _ _ _ _ _ _ _ HA HB EB Hρ
    (eval_exp_nat ρ) HG').
Qed.

Local Lemma certified_environment_lift_natural_composition Γ Δ Θ σ τ ρ :
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  weakening_between Δ Θ τ ->
  realizes_environment uniform_certified_realization (a_nat :: Θ) (a_nat :: Γ)
    (a_compose (Syntax.q σ) (Syntax.q τ)) (extend_env ρ (d_neut d_nat (d_var (length Θ)))).
Proof.
  intros Hρ HW.
  pose proof (proj1 Hρ) as HS.
  pose proof (weakening_between_typed _ _ _ HW) as HT.
  pose proof (certified_environment_weakening_between _ _ _ _ _ _ Hρ HW) as Hρ'.
  eapply realized_environment_substitution_conversion.
  - exact uniform_certified_realization_type_conversion.
  - exact uniform_certified_realization_term_conversion.
  - exact (certified_environment_lift_natural _ _ _ _ Hρ').
  - exact (wf_sub_compose _ _ _ _ _
      (lift_natural_substitution _ _ _ HT) (lift_natural_substitution _ _ _ HS)).
  - exact (wf_sub_eq_sym _ _ _ _ (compose_lifted_natural_substitutions _ _ _ _ _ HS HT)).
Qed.


Local Lemma certified_readback_from_nested_substitution Γ Δ Θ σ τ A M a m i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Θ ⊢s τ : Δ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  uniform_certified_realization Θ (a_sub A (a_compose σ τ)) (a_sub M (a_compose σ τ)) a m ->
  typed_value_readback Θ (a_sub (a_sub A σ) τ) (a_sub (a_sub M σ) τ) a m.
Proof.
  intros HS HT HA HM HR.
  exact (uniform_certified_realization_readback _ _ _ _ _
    (realized_environment_compose_action _ _ _ _ _ _ _ _ _ _ _
      uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
      HT HS HA HM HR)).
Qed.

Local Lemma typed_certified_neutral_natural_recursion Γ Δ σ ρ A MZ MS N i bz mz k :
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Γ ⊢ MZ : A[Id,,zero] }} ->
  {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
  {{ Δ ⊢ N : ℕ }} ->
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  certifies_typed_term (a_nat :: Γ) (a_typ i) A ->
  certifies_typed_term (A :: a_nat :: Γ) (a_sub A natural_step_substitution) MS ->
  eval_exp A (extend_env ρ d_zero) bz ->
  typed_value_readback Δ (a_sub (a_sub A (a_extend a_id a_zero)) σ) (a_sub MZ σ) bz mz ->
  typed_neutral_readback Δ a_nat N k ->
  typed_neutral_readback Δ (a_sub A (a_extend σ N)) (natural_recursion_at σ A MZ MS N)
    (d_natrec ρ A mz MS k).
Proof.
  intros HA HZ HStep HN Hρ HAr HStepR Hbz HZR HNR Θ τ HW.
  pose proof (proj1 Hρ) as HS.
  pose proof (context_weakening_typed _ _ _ HW) as HT.
  pose proof (weakening_between_canonical _ _ _ HW) as HW'.
  pose proof (substitution_source _ _ _ HS) as HΔ.
  pose proof (substitution_source _ _ _ HT) as HΘ.
  pose proof (lift_natural_substitution _ _ _ HS) as HQ.
  pose proof (lift_natural_substitution _ _ _ HT) as HQ'.
  pose proof (type_substitution _ _ _ _ _ HQ HA) as HAq.
  pose proof (type_substitution _ _ _ _ _ HQ' HAq) as HAqq.
  pose proof (lifted_substitution _ _ _ _ _ HQ HA) as HQQ.
  pose proof (lifted_substitution _ _ _ _ _ HQ' HAq) as HQQ'.
  pose proof (natural_substituted_zero_case _ _ _ _ _ _ HS HA HZ) as HZq.
  pose proof (natural_substituted_step_case _ _ _ _ _ _ HS HA HStep) as HStepq.
  pose proof (natural_substituted_zero_case _ _ _ _ _ _ HT HAq HZq) as HZqq.
  pose proof (natural_substituted_step_case _ _ _ _ _ _ HT HAq HStepq) as HStepqq.

  pose proof (certified_environment_lift_natural_composition _ _ _ _ _ _ Hρ HW') as HρN.
  destruct (HAr _ _ _ HρN) as (u & a & Hu & Ha & _).
  destruct (nominal_certified_universe_realization _ _ _ _ _ _ _ HA HAr HρN Ha) as (R & HAt).
  pose proof (type_substitution_composition _ _ _ _ _ _ _ HQ' HQ HA) as EAt.
  pose proof (certified_type_conversion _ _ _ _ _ _ HAt HAqq EAt) as HG.
  destruct (typed_type_readback_here _ _ _ _ HAqq (certified_type_readback _ _ _ _ _ HG))
    as (Av & HAv & HAvt & HAvE).

  pose proof (certified_environment_fresh_binder _ _ _ _ _ _ _ _ _
    HA HAqq EAt HρN Ha HAt) as HρA0.
  assert (HρA : realizes_environment uniform_certified_realization
      (a_sub (a_sub A (Syntax.q σ)) (Syntax.q τ) :: a_nat :: Θ)
      (A :: a_nat :: Γ) (a_compose (Syntax.q (Syntax.q σ)) (Syntax.q (Syntax.q τ)))
      (extend_env (extend_env ρ (d_neut d_nat (d_var (length Θ))))
        (d_neut a (d_var (S (length Θ)))))).
  {
    eapply realized_environment_substitution_conversion;
      [exact uniform_certified_realization_type_conversion | exact uniform_certified_realization_term_conversion | |
        exact (wf_sub_compose _ _ _ _ _ HQQ' HQQ) |].
    - exact HρA0.
    - exact (wf_sub_eq_sym _ _ _ _ (compose_lifted_substitutions _ _ _ _ _ _ _ HQ HQ' HA)).
  }
  destruct (HStepR _ _ _ HρA) as (b & r & Hb & Hr & HR).
  pose proof (natural_step_argument_inversion _ _ _ _ _ Hb) as Hb'.
  pose proof (type_substitution _ _ _ _ _ (step_case_substitution _ _ _ HA) HA) as HStepT.
  pose proof (certified_readback_from_nested_substitution _ _ _ _ _ _ _ _ _ _
    HQQ HQQ' HStepT HStep HR) as HStepR0.
  pose proof (type_substitution _ _ _ _ _ (step_case_substitution _ _ _ HAqq) HAqq) as HStepT'.
  assert (EStep : {{ Θ, ℕ, A[q σ][q τ] ⊢
      A[Wk∘Wk,,succ #1][q (q σ)][q (q τ)] ≈ A[q σ][q τ][Wk∘Wk,,succ #1] : Type@i }}).
  {
    eapply wf_exp_eq_trans.
    - exact (type_substitution_congruence _ _ _ _ _ _ _ HQQ'
        (substitution_equality_reflexive _ _ _ HQQ') (natural_substituted_step_type _ _ _ _ _ HS HA)).
    - exact (natural_substituted_step_type _ _ _ _ _ HT HAq).
  }
  pose proof (typed_readback_type_conversion _ _ _ _ _ _ _ _ _ _ HStepT' EStep HStepR0) as HStepR'.
  destruct (typed_readback_here _ _ _ _ _ _ _ _ _ HStepT' HStepqq HStepR')
    as (MSv & HMSv & HMSvt & HMSvE).

  pose proof (type_substitution _ _ _ _ _
    (nat_case_substitution _ _
      (wf_zero _ (substitution_target _ _ _ HS))) HA) as HZT.
  pose proof (typed_readback_under_weakening _ _ _ _ _ _ _ _ _ _ _
    (type_substitution _ _ _ _ _ HS HZT) (wf_exp_sub _ _ _ _ _ HS HZ) HW' HZR) as HZR0.
  pose proof (type_substitution _ _ _ _ _
    (nat_case_substitution _ _ (wf_zero _ HΘ)) HAqq) as HZT'.
  assert (EZ : {{ Θ ⊢ A[Id,,zero][σ][τ] ≈ A[q σ][q τ][Id,,zero] : Type@i }}).
  {
    eapply wf_exp_eq_trans.
    - exact (type_substitution_congruence _ _ _ _ _ _ _ HT
        (substitution_equality_reflexive _ _ _ HT) (natural_substituted_zero_type _ _ _ _ _ HS HA)).
    - exact (natural_substituted_zero_type _ _ _ _ _ HT HAq).
  }
  pose proof (typed_readback_type_conversion _ _ _ _ _ _ _ _ _ _ HZT' EZ HZR0) as HZR'.
  destruct (typed_readback_here _ _ _ _ _ _ _ _ _ HZT' HZqq HZR')
    as (MZv & HMZv & HMZvt & HMZvE).

  pose proof (natural_term_from_substituted_type _ _ _ _ HT (wf_exp_sub _ _ _ _ _ HT HN)) as HN'.
  pose proof (wf_nat Θ HΘ) as HNat.
  pose proof (typed_readback_under_weakening _ _ _ _ _ _ _ _ _ _ _
    (wf_nat Δ HΔ) HN HW' HNR) as HNR0.
  pose proof (typed_readback_type_conversion _ _ _ _ _ _ _ _ _ _
    HNat (wf_exp_eq_nat_sub _ _ _ HT) HNR0) as HNR'.
  destruct (typed_readback_here _ _ _ _ _ _ _ _ _ HNat HN' HNR') as (Nv & HNv & HNvt & HNvE).
  destruct (reconstruct_readback_natural_recursion _ _ _ _ _ _ _ _ _ _
    HAqq HAvt HAvE HMZvt HMZvE HMSvt HMSvE HN' HNvt HNvE) as (Hres & Eres).

  pose proof (type_substitution _ _ _ _ _ (natural_argument_substitution _ _ _ _ HS HN) HA) as HOut.
  pose proof (type_substitution _ _ _ _ _ HT HOut) as HOut'.
  pose proof (type_argument_substitution_composition _ _ _ _ _ _ _ _ HT (wf_nat Δ HΔ) HAq HN) as EArg.
  pose proof (natural_motive_instance _ _ _ _ _ _ HS HA HN) as EOrig.
  pose proof (type_substitution_congruence _ _ _ _ _ _ _ HT
    (substitution_equality_reflexive _ _ _ HT) EOrig) as EOrig'.
  pose proof (wf_exp_eq_trans _ _ _ _ _ (wf_exp_eq_sym _ _ _ _ EArg) EOrig') as EOut.
  pose proof (natural_motive_instance _ _ _ _ _ _ HT HAq HN') as ECurrent.
  pose proof (wf_exp_eq_trans _ _ _ _ _ ECurrent EOut) as EResult.
  exists (ne_natrec Av MZv MSv Nv). repeat split.
  - eapply read_ne_natrec; try eassumption.
  - exact (convert_term _ _ _ _ _ Hres HOut' EResult).
  - eapply wf_exp_eq_trans.
    + exact (convert_equality _ _ _ _ _ _
        (wf_exp_eq_natrec_sub _ _ _ _ _ _ _ _ HT HAq HZq HStepq HN) HOut' EOut).
    + exact (convert_equality _ _ _ _ _ _ Eres HOut' EResult).
Qed.

Local Lemma certified_environment_natural_argument Γ Δ σ ρ N n :
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  natural_candidate Δ N n -> semantic_member d_nat n ->
  realizes_environment uniform_certified_realization Δ (a_nat :: Γ) (a_extend σ N) (extend_env ρ n).
Proof.
  intros Hρ HN Hgood.
  pose proof (proj1 Hρ) as HS.
  pose proof (substitution_source _ _ _ HS) as HΔ.
  pose proof (wf_nat Γ (substitution_target _ _ _ HS)) as HNat.
  pose proof (type_substitution _ _ _ _ _ HS HNat) as HT.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS)) as ET.
  assert (HG : certified_type 0 Δ a_nat d_nat (certified_candidate d_nat (natural_candidate Δ))).
  { apply certify_natural; [exact HΔ | intros M m; reflexivity]. }
  pose proof (certified_type_conversion _ _ _ _ _ _ HG HT ET) as HGT.
  assert (Hnom : has_certified_realization Δ (a_sub a_nat σ) N d_nat n) by
    (exists 0, (certified_candidate d_nat (natural_candidate Δ)); now split).
  exact (realized_environment_extend _ _ _ _ _ _ _ _ _ _
    uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
    Hρ HNat (has_certified_realization_typing _ _ _ _ _ Hnom) (eval_exp_nat ρ)
    (nominal_certified_realization_is_uniform _ _ _ _ _ Hnom)).
Qed.


Local Lemma certified_natural_recursion_values Γ Δ σ ρ A MZ MS i bz mz :
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Γ ⊢ MZ : A[Id,,zero] }} ->
  {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  certifies_typed_term (a_nat :: Γ) (a_typ i) A ->
  certifies_typed_term (A :: a_nat :: Γ) (a_sub A natural_step_substitution) MS ->
  eval_exp A (extend_env ρ d_zero) bz ->
  eval_exp MZ ρ mz ->
  uniform_certified_realization Δ (a_sub (a_sub A (a_extend a_id a_zero)) σ) (a_sub MZ σ) bz mz ->
  forall N n, natural_candidate Δ N n -> semantic_member d_nat n ->
    exists b r R, eval_exp A (extend_env ρ n) b /\ eval_natrec A MZ MS n ρ r /\
      certified_type i Δ (a_sub A (a_extend σ N)) b R /\
      R (natural_recursion_at σ A MZ MS N) r.
Proof.
  intros HA HZ HStep Hρ HAr HStepR Hbz Hmz HZR N n HN.
  pose proof (proj1 Hρ) as HS.
  pose proof (substitution_source _ _ _ HS) as HΔ.
  pose proof (substitution_target _ _ _ HS) as HΓ.
  pose proof HN as HN0. revert HN0.
  induction HN as [N HN E | N P p HN E HP IH | N a k HN HNe]; intros HN0 Hgood;
    pose proof (certified_environment_natural_argument _ _ _ _ _ _ Hρ HN0 Hgood) as HρN;
    destruct (HAr _ _ _ HρN) as (u & b & Hu & Hb & _);
    destruct (nominal_certified_universe_realization _ _ _ _ _ _ _ HA HAr HρN Hb) as (R & HG);
    pose proof (natural_recursion_at_typing _ _ _ _ _ _ _ _ HS HA HZ HStep HN) as HR;
    pose proof (type_substitution _ _ _ _ _ (proj1 HρN) HA) as HB.
  - pose proof (eval_exp_deterministic _ _ _ Hbz _ Hb) as Eb. subst b.
    pose proof (type_substitution _ _ _ _ _ (nat_case_substitution _ _ (wf_zero _ HΓ)) HA) as HZT.
    pose proof (uniform_certified_realization_at_identity _ _ _ _ _ _
      (type_substitution _ _ _ _ _ HS HZT) (wf_exp_sub _ _ _ _ _ HS HZ) HZR) as HZnom.
    pose proof (nominal_certified_member_of_same_code _ _ _ _ _ _ _ _ HZnom HG) as HZmem.
    pose proof (natural_motive_congruence _ _ _ _ _ _ _ HS HA HN E) as EArg.
    pose proof (natural_recursion_at_argument_congruence _ _ _ _ _ _ _ _ _
      HS HA HZ HStep HN E) as ERec.
    exists bz, mz, R. repeat split; try assumption.
    + now apply eval_natrec_zero.
    + eapply certified_candidate_expression_conversion; [exact HG | exact HR | | exact HZmem].
      exact (wf_exp_eq_trans _ _ _ _ _ ERec
        (convert_equality _ _ _ _ _ _
          (natural_recursion_at_zero _ _ _ _ _ _ _ HS HA HZ HStep) HB (wf_exp_eq_sym _ _ _ _ EArg))).
  - pose proof (certified_natural_predecessor _ Hgood) as Hpred.
    destruct (IH HP Hpred) as (bp & rp & T & Hbp & Hrec & HT & Hmem).
    pose proof (certified_environment_natural_argument _ _ _ _ _ _ Hρ HP Hpred) as HρP.
    assert (Hpast : has_certified_realization Δ (a_sub A (a_extend σ P))
      (natural_recursion_at σ A MZ MS P) bp rp) by (exists i, T; now split).
    pose proof (realized_environment_extend _ _ _ _ _ _ _ _ _ _
      uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
      HρP HA (has_certified_realization_typing _ _ _ _ _ Hpast) Hbp
      (nominal_certified_realization_is_uniform _ _ _ _ _ Hpast)) as HρStep.
    destruct (HStepR _ _ _ HρStep) as (bs & r & Hbs & Hr & HrR).
    pose proof (natural_step_argument_inversion _ _ _ _ _ Hbs) as Hbs'.
    pose proof (eval_exp_deterministic _ _ _ Hb _ Hbs') as Eb. subst bs.
    pose proof (type_substitution _ _ _ _ _ (step_case_substitution _ _ _ HA) HA) as HStepT.
    pose proof (uniform_certified_realization_at_identity _ _ _ _ _ _
      (type_substitution _ _ _ _ _ (proj1 HρStep) HStepT)
      (wf_exp_sub _ _ _ _ _ (proj1 HρStep) HStep) HrR) as HStepNom.
    pose proof (nominal_certified_member_of_same_code _ _ _ _ _ _ _ _ HStepNom HG) as HStepMem.
    pose proof (natural_motive_congruence _ _ _ _ _ _ _ HS HA HN E) as EArg.
    pose proof (natural_recursion_at_argument_congruence _ _ _ _ _ _ _ _ _
      HS HA HZ HStep HN E) as ERec.
    exists b, r, R. repeat split; try assumption.
    + exact (eval_natrec_succ _ _ _ _ _ _ _ Hrec Hr).
    + eapply certified_candidate_expression_conversion; [exact HG | exact HR | | exact HStepMem].
      exact (wf_exp_eq_trans _ _ _ _ _ ERec
        (convert_equality _ _ _ _ _ _
          (natural_recursion_at_successor _ _ _ _ _ _ _ _
            HS HA HZ HStep (natural_candidate_typed _ _ _ HP)) HB (wf_exp_eq_sym _ _ _ _ EArg))).
  - exists b, (d_neut b (d_natrec ρ A mz MS k)), R. repeat split; try assumption.
    + exact (eval_natrec_neut _ _ _ _ _ _ _ _ Hmz Hb).
    + eapply certified_reflection; [exact HG | exact HR | |].
      * exact (typed_certified_neutral_natural_recursion _ _ _ _ _ _ _ _ _ _ _ _
          HA HZ HStep HN Hρ HAr HStepR Hbz (uniform_certified_realization_readback _ _ _ _ _ HZR) HNe).
      * eapply certified_natrec_neutral_agreement; eassumption.

Qed.

Local Lemma uniform_certified_natural_elimination Γ A MZ MS M i :
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Γ ⊢ MZ : A[Id,,zero] }} ->
  {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
  {{ Γ ⊢ M : ℕ }} ->
  certifies_typed_term (a_nat :: Γ) (a_typ i) A ->
  certifies_typed_term Γ (a_sub A (a_extend a_id a_zero)) MZ ->
  certifies_typed_term (A :: a_nat :: Γ) (a_sub A natural_step_substitution) MS ->
  certifies_typed_term Γ a_nat M ->
  certifies_typed_term Γ (a_sub A (a_extend a_id M)) (a_natrec A MZ MS M).
Proof.
  intros HA HZ HStep HM HAr HZr HStepR HMr.
  apply substituted_certified_realization_lifts_to_uniform;
    [exact (wf_natrec _ _ _ _ _ _ HA HZ HStep HM) |].
  intros Δ σ ρ Hρ.
  pose proof (proj1 Hρ) as HS.
  pose proof (substitution_source _ _ _ HS) as HΔ.
  pose proof (substitution_target _ _ _ HS) as HΓ.
  destruct (HMr _ _ _ Hρ) as (nT & n & HnT & Hn & HMr').
  inversion HnT; subst nT.
  pose proof (wf_nat Γ HΓ) as HNat.
  pose proof (type_substitution _ _ _ _ _ HS HNat) as HNat'.
  pose proof (wf_exp_sub _ _ _ _ _ HS HM) as HM'.
  pose proof (uniform_certified_realization_at_identity _ _ _ _ _ _ HNat' HM' HMr') as HMnom.
  assert (HG : certified_type 0 Δ a_nat d_nat (certified_candidate d_nat (natural_candidate Δ))).
  { apply certify_natural; [exact HΔ | intros P p; reflexivity]. }
  pose proof (nominal_certified_member_of_same_code _ _ _ _ _ _ _ _ HMnom HG) as HN.
  destruct (HZr _ _ _ Hρ) as (bz & mz & Hbz & Hmz & Hz).
  pose proof (eval_natural_argument_inversion _ _ _ _ _ (eval_exp_zero ρ) Hbz) as Hbz'.
  destruct (certified_natural_recursion_values _ _ _ _ _ _ _ _ _ _
    HA HZ HStep Hρ HAr HStepR Hbz' Hmz Hz _ _ (proj2 HN) (proj1 HN)) as (b & r & R & Hb & Hr & HR & Hrec).
  exists b, r. repeat split.
  - exact (eval_at_argument _ _ _ _ _ Hn Hb).
  - exact (eval_exp_natrec _ _ _ _ _ _ _ Hn Hr).
  - pose proof (natural_candidate_typed _ _ _ (proj2 HN)) as HNtyped.
    pose proof (type_substitution _ _ _ _ _ (natural_argument_substitution _ _ _ _ HS HNtyped)
      HA) as HResT.
    pose proof (type_substitution _ _ _ _ _ (nat_case_substitution _ _ HM) HA) as HT.
    pose proof (type_substitution _ _ _ _ _ HS HT) as HT'.
    pose proof (type_argument_substitution_composition _ _ _ _ _ _ _ _ HS HNat HA HM) as E.
    assert (Hrecnom : has_certified_realization Δ (a_sub A (a_extend σ (a_sub M σ)))
      (natural_recursion_at σ A MZ MS (a_sub M σ)) b r) by (exists i, R; now split).
    eapply has_certified_realization_term_conversion.
    + exact (wf_exp_sub _ _ _ _ _ HS (wf_natrec _ _ _ _ _ _ HA HZ HStep HM)).
    + exact (convert_equality _ _ _ _ _ _
        (wf_exp_eq_natrec_sub _ _ _ _ _ _ _ _ HS HA HZ HStep HM) HT'
        (wf_exp_eq_sym _ _ _ _ E)).
    + exact (has_certified_realization_type_conversion _ _ _ _ _ _ _ HT'
        (wf_exp_eq_sym _ _ _ _ E) Hrecnom).
Qed.


Local Definition certified_context_subsumption Γ Δ :=
  forall Θ σ ρ, realizes_environment uniform_certified_realization Θ Γ σ ρ ->
    realizes_environment uniform_certified_realization Θ Δ σ ρ.

Local Lemma certified_extend_context_subsumption Γ Δ A B i :
  {{ ⊢ Γ ⊆ Δ }} ->
  {{ Γ ⊢ A : Type@i }} -> {{ Δ ⊢ B : Type@i }} ->
  {{ Γ ⊢ A ⊆ B }} ->
  certified_context_subsumption Γ Δ ->
  certified_subsumption Γ A B ->
  certified_context_subsumption (A :: Γ) (B :: Δ).
Proof.
  intros Hsub HA HB HAB HTail HHead Θ σ ρ Hρ.
  pose proof (proj1 Hρ) as Hσ.
  pose proof (typing_context _ _ _ HB) as HΔ0.
  pose proof (wf_ctx_extend Δ i B HΔ0 HB) as HΔ.
  pose proof (wf_sub_subtyp _ _ _ _ Hσ HΔ
    (wf_ctx_sub_extend _ _ _ _ _ Hsub HA HB HAB)) as Hσ'.
  pose proof (realized_environment_drop _ _ _ _ _ _
    uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion Hρ) as HρΓ.
  pose proof (HTail _ _ _ HρΓ) as HρΔ.
  pose proof (wf_sub_weaken _ _ (substitution_target _ _ _ Hσ)) as HWΓ.
  pose proof (wf_sub_weaken _ _ HΔ) as HWΔ.
  split; [exact Hσ' |].
  intros x T Hx. inversion Hx as [ | y T' Δ' B' HY]; subst.
  - destruct ((proj2 Hρ) _ _ (here A Γ)) as (a & Ha & H0).
    destruct (invert_eval_substitution _ _ _ _ Ha) as (η & Hη & Ha').
    inversion Hη; subst.
    pose proof (type_substitution _ _ _ _ _ HWΓ HA) as HAw.
    pose proof (type_substitution _ _ _ _ _ Hσ HAw) as HAT.
    pose proof (wf_exp_sub _ _ _ _ _ Hσ
      (wf_vlookup _ _ _ (substitution_target _ _ _ Hσ) (here A Γ))) as H0t.
    pose proof (uniform_certified_realization_at_identity _ _ _ _ _ _ HAT H0t H0) as H0n.
    pose proof (type_substitution _ _ _ _ _ (proj1 HρΓ) HA) as HAtail.
    pose proof (wf_exp_eq_sym _ _ _ _
      (type_substitution_composition _ _ _ _ _ _ _ Hσ HWΓ HA)) as EA.
    pose proof (has_certified_realization_type_conversion _ _ _ _ _ _ _ HAtail EA H0n) as H0n'.
    destruct (HHead _ _ _ _ _ _ HρΓ Ha' H0n') as (b & Hb & Hbc).
    pose proof (type_substitution _ _ _ _ _ Hσ' (type_substitution _ _ _ _ _ HWΔ HB)) as HBw.
    pose proof (type_substitution_composition _ _ _ _ _ _ _ Hσ' HWΔ HB) as EB.
    exists b. split.
    + exact (eval_exp_sub _ _ _ _ _ (eval_sub_weaken ρ) Hb).
    + exact (nominal_certified_realization_is_uniform _ _ _ _ _
        (has_certified_realization_type_conversion _ _ _ _ _ _ _ HBw EB Hbc)).
  - destruct ((proj2 HρΔ) _ _ HY) as (b & Hb & Hv).
    pose proof (wf_vlookup _ _ _ HΔ0 HY) as HV.
    destruct (lookup_type _ _ _ HY HΔ0) as (k & HTy).
    pose proof (type_substitution _ _ _ _ _ HWΔ HTy) as HWTy.
    pose proof (type_substitution _ _ _ _ _ Hσ' HWTy) as HTy'.
    pose proof (type_substitution_composition _ _ _ _ _ _ _ Hσ' HWΔ HTy) as ET.
    pose proof (wf_exp_eq_sub_compose _ _ _ _ _ _ _ Hσ' HWΔ HV) as EC.
    pose proof (equality_under_substitution _ _ _ _ _ _ Hσ'
      (wf_exp_eq_var_weaken _ _ _ _ HΔ HY)) as EV.
    exists b. split.
    + exact (eval_exp_sub _ _ _ _ _ (eval_sub_weaken ρ) Hb).
    + eapply uniform_certified_realization_term_conversion.
      * exact (wf_exp_sub _ _ _ _ _ Hσ'
           (wf_vlookup _ _ _ HΔ (there _ _ _ _ HY))).
      * apply wf_exp_eq_sym. exact (wf_exp_eq_trans _ _ _ _ _
           (convert_equality _ _ _ _ _ _ EC HTy' ET) EV).
      * exact (uniform_certified_realization_type_conversion _ _ _ _ _ _ _ HTy' ET Hv).
Qed.

Local Lemma certified_term_by_subsumption Γ A B M i :
  {{ Γ ⊢ M : A }} -> {{ Γ ⊢ B : Type@i }} -> {{ Γ ⊢ A ⊆ B }} ->
  certifies_typed_term Γ A M ->
  certified_subsumption Γ A B ->
  certifies_typed_term Γ B M.
Proof.
  intros HM HB Hsub HM' Hcast.
  apply substituted_certified_realization_lifts_to_uniform;
    [exact (wf_exp_subtyp _ _ _ _ _ HM HB Hsub) |].
  intros Δ σ ρ Hρ.
  pose proof (proj1 Hρ) as HS.
  destruct (HM' _ _ _ Hρ) as (a & m & Ha & Hm & Hreal).
  destruct (type_of_typing _ _ _ HM) as (j & HA).
  pose proof (uniform_certified_realization_at_identity _ _ _ _ _ _
    (type_substitution _ _ _ _ _ HS HA) (wf_exp_sub _ _ _ _ _ HS HM) Hreal) as Hnom.
  destruct (Hcast _ _ _ _ _ _ Hρ Ha Hnom) as (b & Hb & Hnom').
  exists b, m. repeat split; assumption.
Qed.

Local Lemma certified_substitution_by_subsumption Γ Δ Ξ σ :
  certifies_typed_substitution Γ Δ σ ->
  certified_context_subsumption Δ Ξ ->
  certifies_typed_substitution Γ Ξ σ.
Proof.
  intros HS Hsub Θ τ ρ Hρ.
  destruct (HS _ _ _ Hρ) as (η & Hη & Henv).
  exists η. split; [exact Hη | now apply Hsub].
Qed.
Local Lemma uniform_certified_conversion_at_same_code Γ A B M i :
  {{ Γ ⊢ B : Type@i }} ->
  {{ Γ ⊢ A ≈ B : Type@i }} ->
  (forall ρ a, eval_exp A ρ a -> eval_exp B ρ a) ->
  certifies_typed_term Γ A M ->
  certifies_typed_term Γ B M.
Proof.
  intros HB EAB Heval H Δ σ ρ Hρ.
  destruct (H _ _ _ Hρ) as (a & m & Ha & Hm & Hmreal).
  pose proof (proj1 Hρ) as Hσ.
  exists a, m. split; [exact (Heval _ _ Ha) | split; [exact Hm |]].
  eapply uniform_certified_realization_type_conversion.
  - exact (type_substitution _ _ _ _ _ Hσ HB).
  - exact (type_substitution_congruence _ _ _ _ _ _ _ Hσ
      (substitution_equality_reflexive _ _ _ Hσ) EAB).
  - exact Hmreal.
Qed.

Local Lemma certified_type_under_substitution Γ Δ σ A i :
  {{ Γ ⊢s σ : Δ }} ->
  {{ Δ ⊢ A : Type@i }} ->
  certifies_typed_substitution Γ Δ σ ->
  certifies_typed_term Δ (a_typ i) A ->
  certifies_typed_term Γ (a_typ i) (a_sub A σ).
Proof.
  intros Hσ HA Hsub HAreal.
  eapply uniform_certified_conversion_at_same_code.
  - exact (wf_typ _ i (substitution_source _ _ _ Hσ)).
  - exact (wf_exp_eq_typ_sub _ _ _ i Hσ).
  - intros ρ a He.
    destruct (invert_eval_substitution _ _ _ _ He) as (η & Hη & Hu).
    inversion Hu; subst. apply eval_exp_typ.
  - exact (uniform_certified_substitution_case _ _ _ _ _ HA Hσ HAreal Hsub).
Qed.

Local Lemma certified_identity_extension Γ A M i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  certifies_typed_term Γ A M ->
  certifies_typed_substitution Γ (A :: Γ) (a_extend a_id M).
Proof.
  intros HA HM Hreal.
  pose proof (typing_context _ _ _ HA) as HΓ.
  pose proof (wf_sub_id Γ HΓ) as HId.
  pose proof (type_substitution _ _ _ _ _ HId HA) as HAI.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_sub_id _ _ _ HA)) as EAI.
  eapply uniform_certified_extension_substitution.
  - exact HId.
  - exact HA.
  - exact (convert_term _ _ _ _ _ HM HAI EAI).
  - apply uniform_certified_identity_substitution.
  - eapply uniform_certified_conversion_at_same_code.
    + exact HAI.
    + exact EAI.
    + intros ρ a He. eapply eval_exp_sub; [apply eval_sub_id | exact He].
    + exact Hreal.
Qed.

Local Definition certified_type_formation Γ A :=
  exists i, wf_exp Γ (a_typ i) A /\ certifies_typed_term Γ (a_typ i) A.

Local Fixpoint certified_context_formation (Γ : ctx) : Prop :=
  match Γ with
  | nil => True
  | cons A Γ' => certified_context_formation Γ' /\ certified_type_formation Γ' A
  end.

Local Lemma certified_context_extend Γ A i :
  {{ Γ ⊢ A : Type@i }} ->
  certifies_typed_term Γ (a_typ i) A ->
  certified_context_formation Γ ->
  certified_context_formation (A :: Γ).
Proof. intros HA HAr HC. split; [exact HC | exists i; now split]. Qed.

Local Lemma certified_context_lookup Γ :
  certified_context_formation Γ ->
  forall x A, ctx_lookup x A Γ -> certified_type_formation Γ A.
Proof.
  induction Γ as [|B Γ IH]; intros HC x T HL; [inversion HL |].
  destruct HC as (HC & i & HB & HBr).
  pose proof (typing_context _ _ _ HB) as HΓ.
  pose proof (wf_ctx_extend _ _ _ HΓ HB) as Hctx.
  pose proof (wf_sub_weaken _ _ Hctx) as HW.
  inversion HL as [|y T0 Γ0 A0 HL']; subst.
  - exists i. split.
    + exact (type_substitution _ _ _ _ _ HW HB).
    + exact (certified_type_under_substitution _ _ _ _ _ HW HB
        (uniform_certified_weakening_substitution _ _) HBr).
  - destruct (IH HC _ _ HL') as (j & HT & HTr).
    exists j. split.
    + exact (type_substitution _ _ _ _ _ HW HT).
    + exact (certified_type_under_substitution _ _ _ _ _ HW HT
        (uniform_certified_weakening_substitution _ _) HTr).
Qed.

Local Definition certified_typing Γ A M :=
  certifies_typed_term Γ A M /\ certified_type_formation Γ A.

Local Lemma certified_dependent_type_after_argument Γ A B M i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  {{ Γ ⊢ M : A }} ->
  certifies_typed_term (A :: Γ) (a_typ i) B ->
  certifies_typed_term Γ A M ->
  certified_type_formation Γ (a_sub B (a_extend a_id M)).
Proof.
  intros HA HB HM HBr HMr.
  pose proof (typing_identity_extension _ _ _ _ HA HM) as Hσ.
  exists i. split; [exact (type_substitution _ _ _ _ _ Hσ HB) |].
  exact (certified_type_under_substitution _ _ _ _ _ Hσ HB
    (certified_identity_extension _ _ _ _ HA HM HMr) HBr).
Qed.

Local Definition certifies_equation_elimination :=
  forall Γ i A M1 M2 j B BR P,
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M1 : A }} ->
    {{ Γ ⊢ M2 : A }} ->
    {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B : Type@j }} ->
    {{ Γ, A ⊢ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Γ ⊢ P : Eq A M1 M2 }} ->
    certifies_typed_term Γ (a_typ i) A ->
    certifies_typed_term Γ A M1 ->
    certifies_typed_term Γ A M2 ->
    certifies_typed_term (equation_context Γ A) (a_typ j) B ->
    certifies_typed_term (A :: Γ) (equation_refl_type A B) BR ->
    certifies_typed_term Γ (a_eq A M1 M2) P ->
    certified_typing Γ (equation_result_type B M1 M2 P)
      (a_eqrec A B BR M1 M2 P).

Local Lemma certified_universe_formation Γ i :
  {{ ⊢ Γ }} -> certified_type_formation Γ (a_typ i).
Proof.
  intro HΓ. exists (S i). split; [now apply wf_typ | now apply uniform_certified_universe_case].
Qed.

Local Lemma certified_dependent_formation Γ A B i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A ⊢ B : Type@i }} ->
  certifies_typed_term Γ (a_typ i) A ->
  certifies_typed_term (A :: Γ) (a_typ i) B ->
  certified_type_formation Γ (a_pi A B) /\ certified_type_formation Γ (a_sigma A B).
Proof.
  intros HA HB HAr HBr.
  destruct (uniform_certified_dependent_type_formation _ _ _ _ HA HB HAr HBr) as [HP HS].
  split; exists i; split; eauto using wf_pi, wf_sigma.
Qed.

Local Lemma uniform_certified_typing_from_equation_elimination :
  certifies_equation_elimination -> uniform_certified_typing_interpretation.
Proof.
  intro Heq.
  assert (H :
    (forall Γ, wf_ctx Γ -> certified_context_formation Γ) /\
    (forall Γ Δ, wf_ctx_sub Γ Δ -> certified_context_subsumption Γ Δ) /\
    (forall Γ A M, wf_exp Γ A M -> certified_typing Γ A M) /\
    (forall Γ A M N, wf_exp_eq Γ A M N -> True) /\
    (forall Γ Δ σ, wf_sub Γ Δ σ -> certifies_typed_substitution Γ Δ σ) /\
    (forall Γ Δ σ τ, wf_sub_eq Γ Δ σ τ -> True) /\
    (forall Γ A B, wf_subtyp Γ A B -> certified_subsumption Γ A B)).
  {
    apply syntactic_wf_mut_ind; try solve [intros; exact I].
    - intros Γ i A HΓ HC HA [HAreal _].
      exact (certified_context_extend _ _ _ HA HAreal HC).
    - intros Θ σ ρ H. exact H.
    - intros Γ Δ i A B HS Htail HA _ HB _ HAB Hhead.
      exact (certified_extend_context_subsumption _ _ _ _ _ HS HA HB HAB Htail Hhead).
    - intros Γ i HΓ _. split.
      + exact (uniform_certified_universe_case _ _ HΓ).
      + exact (certified_universe_formation _ _ HΓ).
    - intros Γ HΓ _. split.
      + exact (uniform_certified_natural_case _ HΓ).
      + exact (certified_universe_formation _ _ HΓ).
    - intros Γ HΓ _. split.
      + exact (uniform_certified_zero_case _ HΓ).
      + exists 0. split; [exact (wf_nat _ HΓ) | exact (uniform_certified_natural_case _ HΓ)].
    - intros Γ M HM [HMreal HT]. split; [now apply uniform_certified_successor_case | exact HT].
    - intros Γ i A MZ MS M HA [HAr _] HZ [HZr _] HS [HSr _] HM [HMr _].
      split.
      + exact (uniform_certified_natural_elimination _ _ _ _ _ _ HA HZ HS HM HAr HZr HSr HMr).
      + exact (certified_dependent_type_after_argument _ _ _ _ _
          (type_cumulativity _ _ _ _ (wf_nat _ (typing_context _ _ _ HM)) (Nat.le_0_l i))
          HA HM HAr HMr).
    - intros Γ i A B HA [HAr HT] HB [HBr _]. split; [| exact HT].
      exact (proj1 (uniform_certified_dependent_type_formation _ _ _ _ HA HB HAr HBr)).
    - intros Γ i A B M HA [HAr _] HM [HMr (j & HB & HBr)].
      pose proof (type_cumulativity _ _ _ _ HA (Nat.le_max_l i j)) as HAk.
      pose proof (type_cumulativity _ _ _ _ HB (Nat.le_max_r i j)) as HBk.
      pose proof (uniform_certified_universe_cumulativity _ _ _ _ (Nat.le_max_l i j) HA HAr) as HArk.
      pose proof (uniform_certified_universe_cumulativity _ _ _ _ (Nat.le_max_r i j) HB HBr) as HBrk.
      split.
      + exact (uniform_certified_lambda_case _ _ _ _ _ HAk HBk HM HArk HBrk HMr).
      + exact (proj1 (certified_dependent_formation _ _ _ _ HAk HBk HArk HBrk)).
    - intros Γ i A B F N HA [HAr _] HB [HBr _] HF [HFr _] HN [HNr _].
      split.
      + exact (uniform_certified_application_case _ _ _ _ _ _ HA HB HF HN HBr HFr HNr).
      + exact (certified_dependent_type_after_argument _ _ _ _ _ HA HB HN HBr HNr).
    - intros Γ i A B HA [HAr HT] HB [HBr _]. split; [| exact HT].
      exact (proj2 (uniform_certified_dependent_type_formation _ _ _ _ HA HB HAr HBr)).
    - intros Γ i A B M N HA [HAr _] HB [HBr _] HM [HMr _] HN [HNr _].
      split.
      + exact (uniform_certified_pair_case _ _ _ _ _ _ HA HB HM HN HAr HBr HMr HNr).
      + exact (proj2 (certified_dependent_formation _ _ _ _ HA HB HAr HBr)).
    - intros Γ i A B P HA [HAr _] HB [HBr _] HP [HPr _].
      split.
      + exact (proj1 (uniform_certified_projections _ _ _ _ _ HA HB HP HAr HBr HPr)).
      + exists i. now split.
    - intros Γ i A B P HA [HAr _] HB [HBr _] HP [HPr _].
      destruct (uniform_certified_projections _ _ _ _ _ HA HB HP HAr HBr HPr) as [HF HSn].
      split; [exact HSn |].
      exact (certified_dependent_type_after_argument _ _ _ _ _ HA HB
        (wf_fst _ _ _ _ _ HA HB HP) HBr HF).
    - intros Γ x A HΓ HC HL.
      split; [now apply uniform_certified_variable_case | exact (certified_context_lookup _ HC _ _ HL)].
    - intros Γ i A M N HA [HAr HT] HM [HMr _] HN [HNr _].
      split; [exact (uniform_certified_equality_type_case _ _ _ _ _ HA HM HN HAr HMr HNr) | exact HT].
    - intros Γ i A M HA [HAr _] HM [HMr _]. split.
      + exact (uniform_certified_reflexivity_case _ _ _ _ HA HM HAr HMr).
      + exists i. split.
        * exact (wf_eq _ _ _ _ _ HA HM HM).
        * exact (uniform_certified_equality_type_case _ _ _ _ _ HA HM HM HAr HMr HMr).
    - intros Γ i A M1 M2 j B BR P HA [HAr _] HM1 [HM1r _] HM2 [HM2r _]
        HB [HBr _] HBR [HBRr _] HP [HPr _].
      exact (Heq _ _ _ _ _ _ _ _ _ HA HM1 HM2 HB HBR HP HAr HM1r HM2r HBr HBRr HPr).
    - intros Γ Δ σ A M HS HSreal HM [HMreal (i & HA & HAreal)].
      split.
      + exact (uniform_certified_substitution_case _ _ _ _ _ HM HS HMreal HSreal).
      + exists i. split.
        * exact (type_substitution _ _ _ _ _ HS HA).
        * exact (certified_type_under_substitution _ _ _ _ _ HS HA HSreal HAreal).
    - intros Γ A M i B HM [HMreal _] HB [HBreal _] Hsubtype IHsub. split.
      + exact (certified_term_by_subsumption _ _ _ _ _ HM HB Hsubtype HMreal IHsub).
      + exists i. now split.
    - intros. apply uniform_certified_identity_substitution.
    - intros. apply uniform_certified_weakening_substitution.
    - intros Γ Δ τ Θ σ HT HTr HS HSr.
      exact (uniform_certified_composition_substitution _ _ _ _ _ HT HS HTr HSr).
    - intros Γ Δ σ i A M HS HSr HA _ HM [HMr _].
      exact (uniform_certified_extension_substitution _ _ _ _ _ _ HS HA HM HSr HMr).
    - intros Γ Δ σ Ξ Hσ Hσr HΞ HΞr HΔΞ IHsub.
      exact (certified_substitution_by_subsumption _ _ _ _ Hσr IHsub).
    - intros Γ i A B HB _ HE _. intros Θ σ ρ a M m Hρ Ha Hmem.
      exact (certified_subtyping_by_type_equality _ _ _ _ _ _ _ _ _ _
        HB HE Hρ Ha Hmem).
    - intros Γ A B C HAB IHAB HBC IHBC.
      exact (certified_subsumption_trans _ _ _ _ IHAB IHBC).
    - intros Γ i j HΓ _ Hij. apply certified_universe_subsumption. lia.
    - intros Γ i A A' B B' HA [HAr _] HA' [HAr' _] EA _
        HB [HBr _] HB' [HBr' _] Hsub IHsub.
      exact (proj1 (certified_dependent_subsumption _ _ _ _ _ _
        HA HA' EA HB HB' Hsub HAr HAr' HBr HBr' IHsub)).
    - intros Γ i A A' B B' HA [HAr _] HA' [HAr' _] EA _
        HB [HBr _] HB' [HBr' _] Hsub IHsub.
      exact (proj2 (certified_dependent_subsumption _ _ _ _ _ _
        HA HA' EA HB HB' Hsub HAr HAr' HBr HBr' IHsub)).
  }
  intros Γ A M HM. exact (proj1 (proj1 (proj2 (proj2 H)) _ _ _ HM)).
Qed.


Local Definition equation_indices_type A :=
  a_eq (a_sub A (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0).

Local Definition equation_reflexive_substitution A :=
  a_extend (a_extend a_id (a_var 0)) (a_refl (a_sub A a_weaken) (a_var 0)).

Local Definition equation_argument_substitution σ M N P :=
  a_extend (a_extend (a_extend σ M) N) P.

Local Lemma lift_substitution_over_equal_declaration Γ Δ σ A B i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} -> {{ Δ ⊢ B : Type@i }} ->
  {{ Δ ⊢ A[σ] ≈ B : Type@i }} ->
  {{ Δ, B ⊢s q σ : Γ, A }}.
Proof.
  intros HS HA HB EB.
  exact (proj1 (proj2 (proj2 narrowing)) _ _ _
    (lifted_substitution _ _ _ _ _ HS HA) _
    (wf_ctx_extend _ _ _ (substitution_source _ _ _ HS) HB)
    (declaration_change_context _ _ _ _
      (type_substitution _ _ _ _ _ HS HA) HB EB)).
Qed.

Local Lemma weaken_type_under_lifted_substitution Γ Δ σ A i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Δ, A[σ] ⊢ A[Wk][q σ] ≈ A[σ][Wk] : Type@i }}.
Proof.
  intros HS HA.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (wf_sub_weaken _ _ (substitution_target _ _ _ HQ)) as H1.
  pose proof (wf_sub_weaken _ _ (substitution_source _ _ _ HQ)) as H2.
  pose proof (wf_sub_compose _ _ _ _ _ HQ H1) as HT.
  eapply wf_exp_eq_trans.
  - exact (wf_exp_eq_sym _ _ _ _
      (type_substitution_composition _ _ _ _ _ _ _ HQ H1 HA)).
  - eapply wf_exp_eq_trans.
    + exact (type_substitution_equality_same_body _ _ _ _ _ _ HT
        (lifted_substitution_tail _ _ _ _ _ HS HA) HA).
    + exact (type_substitution_composition _ _ _ _ _ _ _ H2 HS HA).
Qed.

Local Lemma equation_double_lift Γ Δ σ A i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Δ, A[σ], A[σ][Wk] ⊢s q (q σ) : Γ, A, A[Wk] }}.
Proof.
  intros HS HA.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  eapply lift_substitution_over_equal_declaration; [exact HQ | | |].
  - exact (weaken_type _ _ _ _ _ HA HA).
  - exact (weaken_type _ _ _ _ _
      (type_substitution _ _ _ _ _ HS HA) (type_substitution _ _ _ _ _ HS HA)).
  - exact (weaken_type_under_lifted_substitution _ _ _ _ _ HS HA).
Qed.

Local Lemma equation_second_variable_typing Γ A i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A, A[Wk] ⊢ #1 : A[Wk∘Wk] }} /\
  {{ Γ, A, A[Wk] ⊢ #0 : A[Wk∘Wk] }}.
Proof.
  intro HA.
  destruct (equality_type_components _ _ _ (eqrec_context _ _ _ HA))
    as (j & Hj & H1 & H0).
  exact (conj H1 H0).
Qed.

Local Lemma equation_double_lift_agreement Γ Δ σ A i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Δ, A[σ], A[σ][Wk] ⊢s q (q σ) ≈ (σ∘(Wk∘Wk)),,#1,,#0 : Γ, A, A[Wk] }}.
Proof.
  intros HS HA.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (equation_double_lift _ _ _ _ _ HS HA) as HQQ.
  pose proof (wf_sub_weaken _ _ (substitution_source _ _ _ HQ)) as H1.
  pose proof (wf_sub_weaken _ _ (substitution_source _ _ _ HQQ)) as H2.
  pose proof (wf_sub_compose _ _ _ _ _ H2 H1) as HW.
  pose proof (wf_sub_compose _ _ _ _ _ HW HS) as Hσw.
  pose proof (wf_sub_compose _ _ _ _ _ H2 HQ) as HWQ.
  pose proof (weaken_type _ _ _ _ _ HA HA) as HAw.
  pose proof (type_substitution _ _ _ _ _ Hσw HA) as HAw2.
  pose proof (type_substitution _ _ _ _ _ HW HAs) as HAs2.
  pose proof (type_substitution_composition _ _ _ _ _ _ _ HW HS HA) as EAw2.
  destruct (equation_second_variable_typing _ _ _ HAs) as [Hx Hy].
  pose proof (convert_term _ _ _ _ _ Hx HAw2 (wf_exp_eq_sym _ _ _ _ EAw2)) as Hx'.
  pose proof (convert_term _ _ _ _ _ Hy HAw2 (wf_exp_eq_sym _ _ _ _ EAw2)) as Hy'.
  assert (E : {{ Δ, A[σ], A[σ][Wk] ⊢s q σ∘Wk ≈ (σ∘(Wk∘Wk)),,#1 : Γ, A }}).
  {
    eapply wf_sub_eq_trans.
    - exact (lift_composition _ _ _ _ _ _ _ HS HA H2).
    - eapply wf_sub_eq_extend_cong; [exact (substitution_equality_reflexive _ _ _ Hσw) | exact HA |].
      eapply convert_equality.
      + exact (wf_exp_eq_var_weaken _ _ _ _ (substitution_source _ _ _ H2) (here (a_sub A σ) Δ)).
      + exact HAw2.
      + eapply wf_exp_eq_trans.
        * exact (wf_exp_eq_sym _ _ _ _
            (type_substitution_composition _ _ _ _ _ _ _ H2 H1 HAs)).
        * exact (wf_exp_eq_sym _ _ _ _ EAw2).
  }
  pose proof (type_substitution _ _ _ _ _ HWQ HAw) as HLast.
  assert (ELast : {{ Δ, A[σ], A[σ][Wk] ⊢ A[Wk][q σ∘Wk] ≈ A[σ∘(Wk∘Wk)] : Type@i }}).
  {
    eapply wf_exp_eq_trans.
    - exact (type_substitution_equality_same_body _ _ _ _ _ _ HWQ E HAw).
    - exact (type_weakening_cancel _ _ _ _ _ _ _ _ Hσw HA Hx' HA).
  }
  change {{ Δ, A[σ], A[σ][Wk] ⊢s (q σ∘Wk),,#0 ≈ (σ∘(Wk∘Wk)),,#1,,#0 : Γ, A, A[Wk] }}.
  eapply wf_sub_eq_extend_cong; [exact E | exact HAw |].
  apply expression_equality_reflexive.
  exact (convert_term _ _ _ _ _ Hy' HLast (wf_exp_eq_sym _ _ _ _ ELast)).
Qed.

Local Lemma equation_indices_under_double_lift Γ Δ σ A i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  wf_exp_eq (a_sub (a_sub A σ) a_weaken :: a_sub A σ :: Δ) (a_typ i)
    (a_sub (equation_indices_type A) (Syntax.q (Syntax.q σ)))
    (equation_indices_type (a_sub A σ)).
Proof.
  intros HS HA.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (equation_double_lift _ _ _ _ _ HS HA) as HQQ.
  pose proof (wf_sub_weaken _ _ (substitution_source _ _ _ HQ)) as H1.
  pose proof (wf_sub_weaken _ _ (substitution_source _ _ _ HQQ)) as H2.
  pose proof (wf_sub_compose _ _ _ _ _ H2 H1) as HW.
  pose proof (wf_sub_compose _ _ _ _ _ HW HS) as Hσw.
  pose proof (type_substitution _ _ _ _ _ Hσw HA) as HAw.
  pose proof (type_substitution_composition _ _ _ _ _ _ _ HW HS HA) as EAw.
  destruct (equation_second_variable_typing _ _ _ HAs) as [Hx Hy].
  pose proof (convert_term _ _ _ _ _ Hx HAw (wf_exp_eq_sym _ _ _ _ EAw)) as Hx'.
  pose proof (convert_term _ _ _ _ _ Hy HAw (wf_exp_eq_sym _ _ _ _ EAw)) as Hy'.
  destruct (equation_indices_substitution _ _ _ _ _ _ _ Hσw HA Hx' Hy') as (HArg & EArg).
  eapply wf_exp_eq_trans.
  - exact (type_substitution_equality_same_body _ _ _ _ _ _ HQQ
      (equation_double_lift_agreement _ _ _ _ _ HS HA) (eqrec_context _ _ _ HA)).
  - eapply wf_exp_eq_trans; [exact EArg |].
    exact (wf_exp_eq_eq_cong _ _ _ _ _ _ _ _ EAw
      (expression_equality_reflexive _ _ _ Hx')
      (expression_equality_reflexive _ _ _ Hy')).
Qed.

Local Lemma equation_triple_lift Γ Δ σ A i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  wf_sub (equation_context Δ (a_sub A σ)) (equation_context Γ A) (Syntax.q (Syntax.q (Syntax.q σ))).
Proof.
  intros HS HA.
  unfold equation_context.
  eapply lift_substitution_over_equal_declaration.
  - exact (equation_double_lift _ _ _ _ _ HS HA).
  - exact (eqrec_context _ _ _ HA).
  - exact (eqrec_context _ _ _ (type_substitution _ _ _ _ _ HS HA)).
  - exact (equation_indices_under_double_lift _ _ _ _ _ HS HA).
Qed.

Local Lemma extend_after_composition Γ Δ Θ σ τ ν A M N i :
  {{ Δ ⊢s σ : Γ }} -> {{ Θ ⊢s τ : Δ }} ->
  {{ Θ ⊢s σ∘τ ≈ ν : Γ }} ->
  {{ Γ ⊢ A : Type@i }} -> {{ Δ ⊢ M : A[σ] }} ->
  {{ Θ ⊢ A[ν] : Type@i }} -> {{ Θ ⊢ M[τ] ≈ N : A[ν] }} ->
  {{ Θ ⊢s (σ,,M)∘τ ≈ ν,,N : Γ, A }}.
Proof.
  intros HS HT E HA HM HAn EM.
  pose proof (wf_sub_compose _ _ _ _ _ HT HS) as HC.
  pose proof (type_substitution_equality_same_body _ _ _ _ _ _ HC E HA) as EAn.
  eapply wf_sub_eq_trans.
  - exact (wf_sub_eq_extend_compose _ _ _ _ _ _ _ _ HS HA HM HT).
  - eapply wf_sub_eq_extend_cong; [exact E | exact HA |].
    exact (convert_equality _ _ _ _ _ _ EM (type_substitution _ _ _ _ _ HC HA)
      (wf_exp_eq_sym _ _ _ _ EAn)).
Qed.

Local Lemma equation_arguments_typed Γ Δ σ A M N P i :
  {{ Δ ⊢s σ : Γ }} -> {{ Γ ⊢ A : Type@i }} ->
  {{ Δ ⊢ M : A[σ] }} -> {{ Δ ⊢ N : A[σ] }} ->
  {{ Δ ⊢ P : Eq A[σ] M N }} ->
  wf_sub Δ (equation_context Γ A) (equation_argument_substitution σ M N P).
Proof.
  intros HS HA HM HN HP.
  destruct (equation_indices_substitution _ _ _ _ _ _ _ HS HA HM HN) as (HT & ET).
  pose proof (eqrec_context _ _ _ HA) as HEq.
  unfold equation_context, equation_argument_substitution.
  eapply wf_sub_extend; [exact HT | exact HEq |].
  exact (convert_term _ _ _ _ _ HP (type_substitution _ _ _ _ _ HT HEq) (wf_exp_eq_sym _ _ _ _ ET)).
Qed.

Local Lemma equation_arguments_congruent Γ Δ σ τ A M M' N N' P P' i :
  {{ Δ ⊢s σ : Γ }} -> {{ Δ ⊢s σ ≈ τ : Γ }} -> {{ Γ ⊢ A : Type@i }} ->
  {{ Δ ⊢ M : A[σ] }} -> {{ Δ ⊢ N : A[σ] }} ->
  {{ Δ ⊢ M ≈ M' : A[σ] }} -> {{ Δ ⊢ N ≈ N' : A[σ] }} ->
  {{ Δ ⊢ P ≈ P' : Eq A[σ] M N }} ->
  wf_sub_eq Δ (equation_context Γ A)
    (equation_argument_substitution σ M N P) (equation_argument_substitution τ M' N' P').
Proof.
  intros HS E HA HM HN EM EN EP.
  pose proof (weaken_type _ _ _ _ _ HA HA) as HAw.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HM) as HSM.
  pose proof (type_weakening_cancel _ _ _ _ _ _ _ _ HS HA HM HA) as EAw.
  destruct (equation_indices_substitution _ _ _ _ _ _ _ HS HA HM HN) as (HT & ET).
  unfold equation_context, equation_argument_substitution.
  eapply wf_sub_eq_extend_cong; [ | exact (eqrec_context _ _ _ HA) |].
  - eapply wf_sub_eq_extend_cong;
      [exact (wf_sub_eq_extend_cong _ _ _ _ _ _ _ _ E HA EM) | exact HAw |].
    exact (convert_equality _ _ _ _ _ _ EN (type_substitution _ _ _ _ _ HSM HAw)
      (wf_exp_eq_sym _ _ _ _ EAw)).
  - exact (convert_equality _ _ _ _ _ _ EP
      (type_substitution _ _ _ _ _ HT (eqrec_context _ _ _ HA))
      (wf_exp_eq_sym _ _ _ _ ET)).
Qed.

Local Lemma lift_at_equal_declaration_argument Γ Δ Θ σ τ A B N i :
  {{ Δ ⊢s σ : Γ }} -> {{ Θ ⊢s τ : Δ }} ->
  {{ Γ ⊢ A : Type@i }} -> {{ Δ ⊢ B : Type@i }} ->
  {{ Δ ⊢ A[σ] ≈ B : Type@i }} ->
  {{ Θ ⊢ N : B[τ] }} ->
  {{ Θ ⊢s q σ∘(τ,,N) ≈ (σ∘τ),,N : Γ, A }}.
Proof.
  intros HS HT HA HB E HN.
  eapply lifted_substitution_at_argument; [exact HS | exact HT | exact HA |].
  pose proof (type_substitution_congruence _ _ _ _ _ _ _ HT
    (substitution_equality_reflexive _ _ _ HT) E) as ET.
  exact (convert_term _ _ _ _ _ HN
    (type_substitution _ _ _ _ _ HT (type_substitution _ _ _ _ _ HS HA))
    (wf_exp_eq_sym _ _ _ _ ET)).
Qed.

Local Lemma equation_lift_at_arguments Γ Δ Θ σ τ A M N P i :
  {{ Δ ⊢s σ : Γ }} -> {{ Θ ⊢s τ : Δ }} -> {{ Γ ⊢ A : Type@i }} ->
  {{ Θ ⊢ M : A[σ][τ] }} -> {{ Θ ⊢ N : A[σ][τ] }} ->
  {{ Θ ⊢ P : Eq A[σ][τ] M N }} ->
  wf_sub_eq Θ (equation_context Γ A)
    (a_compose (Syntax.q (Syntax.q (Syntax.q σ))) (equation_argument_substitution τ M N P))
    (equation_argument_substitution (a_compose σ τ) M N P).
Proof.
  intros HS HT HA HM HN HP.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (equation_double_lift _ _ _ _ _ HS HA) as HQQ.
  pose proof (wf_sub_compose _ _ _ _ _ HT HS) as HST.
  pose proof (wf_sub_extend _ _ _ _ _ _ HT HAs HM) as HTM.
  destruct (equation_indices_substitution _ _ _ _ _ _ _ HT HAs HM HN) as (HTMN & EP).
  pose proof (eqrec_context _ _ _ HA) as HEq.
  pose proof (eqrec_context _ _ _ HAs) as HEqs.
  pose proof (weaken_type _ _ _ _ _ HA HA) as HAw.
  pose proof (weaken_type _ _ _ _ _ HAs HAs) as HAsw.
  pose proof (type_weakening_cancel _ _ _ _ _ _ _ _ HT HAs HM HAs) as EN.
  pose proof (convert_term _ _ _ _ _ HN (type_substitution _ _ _ _ _ HTM HAsw)
    (wf_exp_eq_sym _ _ _ _ EN)) as HNs.
  pose proof (convert_term _ _ _ _ _ HP (type_substitution _ _ _ _ _ HTMN HEqs)
    (wf_exp_eq_sym _ _ _ _ EP)) as HPs.
  pose proof (lifted_substitution_at_argument _ _ _ _ _ _ _ _ HS HT HA HM) as EM.
  assert (EN' : {{ Θ ⊢s q (q σ)∘(τ,,M,,N) ≈ (σ∘τ),,M,,N : Γ, A, A[Wk] }}).
  {
    eapply wf_sub_eq_trans.
    - exact (lift_at_equal_declaration_argument _ _ _ _ _ _ _ _ _
        HQ HTM HAw HAsw (weaken_type_under_lifted_substitution _ _ _ _ _ HS HA) HNs).
    - eapply wf_sub_eq_extend_cong; [exact EM | exact HAw |].
      apply expression_equality_reflexive.
      pose proof (type_substitution_congruence _ _ _ _ _ _ _ HTM
        (substitution_equality_reflexive _ _ _ HTM)
        (weaken_type_under_lifted_substitution _ _ _ _ _ HS HA)) as EN0.
      pose proof (type_substitution_composition _ _ _ _ _ _ _ HTM HQ HAw) as EN1.
      exact (convert_term _ _ _ _ _ HNs
        (type_substitution _ _ _ _ _ (wf_sub_compose _ _ _ _ _ HTM HQ) HAw)
        (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_trans _ _ _ _ _ EN1 EN0))).
  }
  unfold equation_context, equation_argument_substitution.
  eapply wf_sub_eq_trans.
  - exact (lift_at_equal_declaration_argument _ _ _ _ _ _ _ _ _
      HQQ HTMN HEq HEqs (equation_indices_under_double_lift _ _ _ _ _ HS HA) HPs).
  - eapply wf_sub_eq_extend_cong; [exact EN' | exact HEq |].
    apply expression_equality_reflexive.
    pose proof (type_substitution_congruence _ _ _ _ _ _ _ HTMN
      (substitution_equality_reflexive _ _ _ HTMN)
      (equation_indices_under_double_lift _ _ _ _ _ HS HA)) as EP0.
    pose proof (type_substitution_composition _ _ _ _ _ _ _ HTMN HQQ HEq) as EP1.
    exact (convert_term _ _ _ _ _ HPs
      (type_substitution _ _ _ _ _ (wf_sub_compose _ _ _ _ _ HTMN HQQ) HEq)
      (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_trans _ _ _ _ _ EP1 EP0))).
Qed.

Local Lemma equation_reflexive_after_argument Γ Δ σ A N i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  {{ Δ ⊢ N : A[σ] }} ->
  wf_sub_eq Δ (equation_context Γ A)
    (a_compose (equation_reflexive_substitution A) (a_extend σ N))
    (equation_argument_substitution σ N N (a_refl (a_sub A σ) N)).
Proof.
  intros HS HA HN.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HN) as Hθ.
  pose proof (substitution_target _ _ _ Hθ) as HC.
  pose proof (wf_sub_id _ HC) as HI.
  pose proof (wf_sub_weaken _ _ HC) as HW.
  pose proof (type_substitution _ _ _ _ _ HW HA) as HAw.
  pose proof (wf_vlookup _ _ _ HC (here A Γ)) as H0.
  pose proof (type_substitution _ _ _ _ _ Hθ HAw) as HAt.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (type_weakening_cancel _ _ _ _ _ _ _ _ HS HA HN HA) as EAt.
  pose proof (wf_exp_eq_var_0_sub _ _ _ _ _ _ HS HA HN) as E0.
  pose proof (convert_equality _ _ _ _ _ _ E0 HAt (wf_exp_eq_sym _ _ _ _ EAt)) as E0'.
  pose proof (convert_term _ _ _ _ _ H0 (type_substitution _ _ _ _ _ HI HAw)
    (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_sub_id _ _ _ HAw))) as H0'.
  destruct (equation_reflexive_indices _ _ _ HA) as (HId0 & EIdx).
  pose proof (eqrec_context _ _ _ HA) as HIdx.
  pose proof (wf_refl _ _ _ _ HAw H0) as HRefl.
  pose proof (convert_term _ _ _ _ _ HRefl (type_substitution _ _ _ _ _ HId0 HIdx)
    (wf_exp_eq_sym _ _ _ _ EIdx)) as HRefl'.
  destruct (equation_indices_substitution _ _ _ _ _ _ _ HS HA HN HN) as (HθN & EθN).
  assert (Eθ : {{ Δ ⊢s (Id,,#0)∘(σ,,N) ≈ σ,,N,,N : Γ, A, A[Wk] }}).
  {
    eapply extend_after_composition; [exact HI | exact Hθ | | exact HAw | exact H0' | exact HAt | exact E0'].
    exact (wf_sub_eq_id_compose_right _ _ _ Hθ).
  }
  pose proof (wf_exp_eq_eq_sub _ _ _ _ _ _ _ Hθ HAw H0 H0) as ESub.
  pose proof (wf_exp_eq_eq_cong _ _ _ _ _ _ _ _ EAt E0' E0') as ETo.
  pose proof (wf_eq _ _ _ _ _ HAs HN HN) as HGoalTy.
  assert (EProof : {{ Δ ⊢ (refl A[Wk] #0)[σ,,N] ≈ refl A[σ] N : Eq A[σ] N N }}).
  {
    eapply wf_exp_eq_trans.
    - exact (convert_equality _ _ _ _ _ _
        (wf_exp_eq_refl_sub _ _ _ _ _ _ Hθ HAw H0) HGoalTy (wf_exp_eq_trans _ _ _ _ _ ESub ETo)).
    - exact (convert_equality _ _ _ _ _ _
        (wf_exp_eq_refl_cong _ _ _ _ _ _ EAt E0') HGoalTy ETo).
  }
  unfold equation_reflexive_substitution, equation_argument_substitution, equation_context.
  eapply extend_after_composition; [exact HId0 | exact Hθ | exact Eθ | exact HIdx | exact HRefl' | |].
  - exact (type_substitution _ _ _ _ _ HθN HIdx).
  - exact (convert_equality _ _ _ _ _ _ EProof (type_substitution _ _ _ _ _ HθN HIdx)
      (wf_exp_eq_sym _ _ _ _ EθN)).
Qed.

Local Lemma equation_reflexive_type_after_argument Γ Δ σ A B N i j :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  wf_exp (equation_context Γ A) (a_typ j) B ->
  {{ Δ ⊢ N : A[σ] }} ->
  wf_exp_eq Δ (a_typ j) (a_sub (equation_refl_type A B) (a_extend σ N))
    (a_sub B (equation_argument_substitution σ N N (a_refl (a_sub A σ) N))).
Proof.
  intros HS HA HB HN.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HN) as Hθ.
  pose proof (eqrec_refl_substitution _ _ _ HA) as HT.
  change (wf_exp_eq Δ (a_typ j)
    (a_sub (a_sub B (equation_reflexive_substitution A)) (a_extend σ N))
    (a_sub B (equation_argument_substitution σ N N (a_refl (a_sub A σ) N)))).
  eapply wf_exp_eq_trans.
  - exact (wf_exp_eq_sym _ _ _ _
      (type_substitution_composition _ _ _ _ _ _ _ Hθ HT HB)).
  - exact (type_substitution_equality_same_body _ _ _ _ _ _
      (wf_sub_compose _ _ _ _ _ Hθ HT) (equation_reflexive_after_argument _ _ _ _ _ _ HS HA HN) HB).
Qed.

Local Lemma equation_reflexive_substitution_as_extension Γ A i :
  {{ Γ ⊢ A : Type@i }} ->
  wf_sub_eq (A :: Γ) (equation_context Γ A)
    (equation_reflexive_substitution A)
    (equation_argument_substitution a_weaken (a_var 0) (a_var 0)
      (a_refl (a_sub A a_weaken) (a_var 0))).
Proof.
  intro HA.
  pose proof (eqrec_refl_substitution _ _ _ HA) as HR.
  pose proof (substitution_source _ _ _ HR) as HC.
  pose proof (wf_sub_id _ HC) as HI.
  pose proof (wf_sub_weaken _ _ HC) as HW.
  pose proof (type_substitution _ _ _ _ _ HW HA) as HAw.
  pose proof (wf_vlookup _ _ _ HC (here A Γ)) as H0.
  pose proof (convert_term _ _ _ _ _ H0 (type_substitution _ _ _ _ _ HI HAw)
    (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_sub_id _ _ _ HAw))) as H0'.
  destruct (equation_reflexive_indices _ _ _ HA) as (HId0 & EIdx).
  pose proof (eqrec_context _ _ _ HA) as HIdx.
  pose proof (convert_term _ _ _ _ _ (wf_refl _ _ _ _ HAw H0)
    (type_substitution _ _ _ _ _ HId0 HIdx) (wf_exp_eq_sym _ _ _ _ EIdx)) as HRefl.
  unfold equation_reflexive_substitution, equation_argument_substitution, equation_context.
  eapply wf_sub_eq_extend_cong; [| exact HIdx | exact (expression_equality_reflexive _ _ _ HRefl)].
  exact (wf_sub_eq_extend_cong _ _ _ _ _ _ _ _
    (wf_sub_eq_sym _ _ _ _ (identity_with_last_variable _ _ _ HA)) HAw
    (expression_equality_reflexive _ _ _ H0')).
Qed.

Local Lemma equation_reflexive_lift_composition Γ Δ σ A i :
  {{ Δ ⊢s σ : Γ }} ->
  {{ Γ ⊢ A : Type@i }} ->
  wf_sub_eq (a_sub A σ :: Δ) (equation_context Γ A)
    (a_compose (equation_reflexive_substitution A) (Syntax.q σ))
    (a_compose (Syntax.q (Syntax.q (Syntax.q σ))) (equation_reflexive_substitution (a_sub A σ))).
Proof.
  intros HS HA.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (substitution_source _ _ _ HQ) as HC.
  pose proof (wf_sub_weaken _ _ HC) as HW.
  pose proof (wf_sub_compose _ _ _ _ _ HW HS) as HSW.
  pose proof (type_substitution _ _ _ _ _ HW HAs) as HAsw.
  pose proof (last_variable_after_lifting _ _ _ _ _ HS HA) as H0.
  pose proof (wf_vlookup _ _ _ HC (here (a_sub A σ) Δ)) as H0s.
  pose proof (type_substitution_composition _ _ _ _ _ _ _ HW HS HA) as ET.
  eapply wf_sub_eq_trans.
  - exact (equation_reflexive_after_argument _ _ _ _ _ _ HSW HA H0).
  - eapply wf_sub_eq_trans.
    + apply equation_arguments_congruent with (i := i);
        try (exact HSW || exact HA || exact H0 || exact (substitution_equality_reflexive _ _ _ HSW) ||
          exact (expression_equality_reflexive _ _ _ H0)).
      exact (wf_exp_eq_refl_cong _ _ _ _ _ _ ET (expression_equality_reflexive _ _ _ H0)).
    + apply wf_sub_eq_sym. eapply wf_sub_eq_trans.
      * exact (wf_sub_eq_compose_cong _ _ _ _ _ _ _
          (equation_reflexive_substitution_as_extension _ _ _ HAs)
          (substitution_equality_reflexive _ _ _ (equation_triple_lift _ _ _ _ _ HS HA))).
      * exact (equation_lift_at_arguments _ _ _ _ _ _ _ _ _ _
          HS HW HA H0s H0s (wf_refl _ _ _ _ HAsw H0s)).
Qed.

Local Lemma equation_reflexive_type_under_lift Γ Δ σ A B i j :
  {{ Δ ⊢s σ : Γ }} -> {{ Γ ⊢ A : Type@i }} ->
  wf_exp (equation_context Γ A) (a_typ j) B ->
  wf_exp_eq (a_sub A σ :: Δ) (a_typ j)
    (a_sub (equation_refl_type A B) (Syntax.q σ))
    (equation_refl_type (a_sub A σ) (a_sub B (Syntax.q (Syntax.q (Syntax.q σ))))).
Proof.
  intros HS HA HB.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (equation_triple_lift _ _ _ _ _ HS HA) as HQQQ.
  pose proof (eqrec_refl_substitution _ _ _ HA) as HR.
  pose proof (eqrec_refl_substitution _ _ _ HAs) as HR'.
  eapply wf_exp_eq_trans.
  - exact (wf_exp_eq_sym _ _ _ _
      (type_substitution_composition _ _ _ _ _ _ _ HQ HR HB)).
  - eapply wf_exp_eq_trans.
    + exact (type_substitution_equality_same_body _ _ _ _ _ _
        (wf_sub_compose _ _ _ _ _ HQ HR) (equation_reflexive_lift_composition _ _ _ _ _ HS HA) HB).
    + exact (type_substitution_composition _ _ _ _ _ _ _ HR' HQQQ HB).
Qed.

Local Lemma equation_reflexive_case_under_lift Γ Δ σ A B BR i j :
  {{ Δ ⊢s σ : Γ }} -> {{ Γ ⊢ A : Type@i }} ->
  wf_exp (equation_context Γ A) (a_typ j) B ->
  wf_exp (A :: Γ) (equation_refl_type A B) BR ->
  wf_exp (a_sub A σ :: Δ)
    (equation_refl_type (a_sub A σ) (a_sub B (Syntax.q (Syntax.q (Syntax.q σ)))))
    (a_sub BR (Syntax.q σ)).
Proof.
  intros HS HA HB HBR.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  eapply convert_term.
  - exact (wf_exp_sub _ _ _ _ _ (lifted_substitution _ _ _ _ _ HS HA) HBR).
  - exact (type_substitution _ _ _ _ _ (eqrec_refl_substitution _ _ _ HAs)
      (type_substitution _ _ _ _ _ (equation_triple_lift _ _ _ _ _ HS HA) HB)).
  - exact (equation_reflexive_type_under_lift _ _ _ _ _ _ _ HS HA HB).
Qed.

Local Lemma compose_lifts_over_equal_declarations Γ Δ Θ σ τ A B C i :
  {{ Δ ⊢s σ : Γ }} -> {{ Θ ⊢s τ : Δ }} ->
  {{ Γ ⊢ A : Type@i }} -> {{ Δ ⊢ B : Type@i }} -> {{ Θ ⊢ C : Type@i }} ->
  {{ Δ ⊢ A[σ] ≈ B : Type@i }} -> {{ Θ ⊢ B[τ] ≈ C : Type@i }} ->
  {{ Θ, C ⊢s q σ∘q τ ≈ q (σ∘τ) : Γ, A }}.
Proof.
  intros HS HT HA HB HC E1 E2.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (type_substitution _ _ _ _ _ HT HAs) as HAστ.
  pose proof (type_substitution_congruence _ _ _ _ _ _ _ HT
    (substitution_equality_reflexive _ _ _ HT) E1) as E1'.
  pose proof (wf_exp_eq_trans _ _ _ _ _ E1' E2) as E.
  pose proof (wf_ctx_extend _ _ _ (substitution_source _ _ _ HT) HC) as Hctx.
  exact (proj1 (proj2 (proj2 (proj2 narrowing))) _ _ _ _
    (compose_lifted_substitutions _ _ _ _ _ _ _ HS HT HA) _ Hctx
    (declaration_change_context _ _ _ _ HAστ HC E)).
Qed.

Local Lemma certified_equation_environment Γ Δ σ ρ A i a M N P x y p :
  {{ Γ ⊢ A : Type@i }} ->
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  eval_exp A ρ a ->
  has_certified_realization Δ (a_sub A σ) M a x ->
  has_certified_realization Δ (a_sub A σ) N a y ->
  has_certified_realization Δ (a_eq (a_sub A σ) M N) P (d_eq a x y) p ->
  realizes_environment uniform_certified_realization Δ (equation_context Γ A)
    (equation_argument_substitution σ M N P) (equation_environment ρ x y p).
Proof.
  intros HA Hρ Ha HM HN HP.
  pose proof (proj1 Hρ) as HS.
  pose proof (has_certified_realization_typing _ _ _ _ _ HM) as HMt.
  pose proof (has_certified_realization_typing _ _ _ _ _ HN) as HNt.
  pose proof (realized_environment_extend _ _ _ _ _ _ _ _ _ _
    uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
    Hρ HA HMt Ha (nominal_certified_realization_is_uniform _ _ _ _ _ HM)) as Hρ1.
  pose proof (weaken_type _ _ _ _ _ HA HA) as HAw.
  pose proof (type_substitution _ _ _ _ _ (proj1 Hρ1) HAw) as HAw1.
  pose proof (type_weakening_cancel _ _ _ _ _ _ _ _ HS HA HMt HA) as EAw.
  pose proof (has_certified_realization_type_conversion _ _ _ _ _ _ _ HAw1
    (wf_exp_eq_sym _ _ _ _ EAw) HN) as HN'.
  pose proof (eval_exp_sub _ _ _ _ _ (eval_sub_weaken (extend_env ρ x)) Ha) as Ha'.
  pose proof (realized_environment_extend _ _ _ _ _ _ _ _ _ _
    uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
    Hρ1 HAw (has_certified_realization_typing _ _ _ _ _ HN') Ha'
    (nominal_certified_realization_is_uniform _ _ _ _ _ HN')) as Hρ2.
  destruct (equation_indices_substitution _ _ _ _ _ _ _ HS HA HMt HNt) as (HIdx & EIdx).
  pose proof (eqrec_context _ _ _ HA) as HEq.
  pose proof (has_certified_realization_type_conversion _ _ _ _ _ _ _
    (type_substitution _ _ _ _ _ HIdx HEq) (wf_exp_eq_sym _ _ _ _ EIdx) HP) as HP'.
  exact (realized_environment_extend _ _ _ _ _ _ _ _ _ _
    uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
    Hρ2 HEq (has_certified_realization_typing _ _ _ _ _ HP')
    (eval_equation_context_last _ _ _ _ _ Ha) (nominal_certified_realization_is_uniform _ _ _ _ _ HP')).
Qed.

Local Lemma equation_result_substitution_composition Γ Δ σ A M N P i :
  {{ Δ ⊢s σ : Γ }} -> {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} -> {{ Γ ⊢ N : A }} -> {{ Γ ⊢ P : Eq A M N }} ->
  wf_sub_eq Δ (equation_context Γ A)
    (a_compose (equation_argument_substitution a_id M N P) σ)
    (equation_argument_substitution σ (a_sub M σ) (a_sub N σ) (a_sub P σ)).
Proof.
  intros HS HA HM HN HP.
  pose proof (wf_sub_id _ (substitution_target _ _ _ HS)) as HI.
  pose proof (type_substitution _ _ _ _ _ HI HA) as HAI.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_sub_id _ _ _ HA)) as EAI.
  pose proof (convert_term _ _ _ _ _ HM HAI EAI) as HMi.
  pose proof (wf_sub_extend _ _ _ _ _ _ HI HA HMi) as HIm.
  pose proof (weaken_type _ _ _ _ _ HA HA) as HAw.
  pose proof (type_substitution _ _ _ _ _ HIm HAw) as HAwI.
  pose proof (type_weakening_cancel _ _ _ _ _ _ _ _ HI HA HMi HA) as EAwI.
  pose proof (wf_exp_eq_trans _ _ _ _ _ EAwI (wf_exp_eq_sub_id _ _ _ HA)) as EAI'.
  pose proof (convert_term _ _ _ _ _ HN HAwI (wf_exp_eq_sym _ _ _ _ EAI')) as HNi.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (wf_exp_sub _ _ _ _ _ HS HM) as HM'.
  pose proof (wf_exp_sub _ _ _ _ _ HS HN) as HN'.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HM') as HSm.
  pose proof (type_substitution _ _ _ _ _ HSm HAw) as HAwS.
  pose proof (type_weakening_cancel _ _ _ _ _ _ _ _ HS HA HM' HA) as EAwS.
  pose proof (convert_term _ _ _ _ _ HN' HAwS (wf_exp_eq_sym _ _ _ _ EAwS)) as HNs.
  pose proof (extend_after_composition _ _ _ _ _ _ _ _ _ _ HI HS
    (wf_sub_eq_id_compose_right _ _ _ HS) HA HMi HAs (expression_equality_reflexive _ _ _ HM')) as Em.
  pose proof (extend_after_composition _ _ _ _ _ _ _ _ _ _ HIm HS Em HAw HNi
    HAwS (expression_equality_reflexive _ _ _ HNs)) as En.
  destruct (equation_identity_indices _ _ _ _ _ HA HM HN) as (HIdmn & EIdmn).
  destruct (equation_indices_substitution _ _ _ _ _ _ _ HS HA HM' HN') as (HSmn & ESmn).
  pose proof (eqrec_context _ _ _ HA) as HEq.
  pose proof (convert_term _ _ _ _ _ HP (type_substitution _ _ _ _ _ HIdmn HEq)
    (wf_exp_eq_sym _ _ _ _ EIdmn)) as HPi.
  pose proof (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HS HA HM HN) as EP.
  pose proof (convert_term _ _ _ _ _ (wf_exp_sub _ _ _ _ _ HS HP)
    (type_substitution _ _ _ _ _ HSmn HEq)
    (wf_exp_eq_trans _ _ _ _ _ EP (wf_exp_eq_sym _ _ _ _ ESmn))) as HPs.
  unfold equation_argument_substitution, equation_context.
  exact (extend_after_composition _ _ _ _ _ _ _ _ _ _ HIdmn HS En HEq HPi
    (type_substitution _ _ _ _ _ HSmn HEq) (expression_equality_reflexive _ _ _ HPs)).
Qed.

Local Lemma equation_result_type_composition Γ Δ σ A B M N P i j :
  {{ Δ ⊢s σ : Γ }} -> {{ Γ ⊢ A : Type@i }} ->
  wf_exp (equation_context Γ A) (a_typ j) B ->
  {{ Γ ⊢ M : A }} -> {{ Γ ⊢ N : A }} -> {{ Γ ⊢ P : Eq A M N }} ->
  wf_exp_eq Δ (a_typ j) (a_sub (equation_result_type B M N P) σ)
    (a_sub B (equation_argument_substitution σ (a_sub M σ) (a_sub N σ) (a_sub P σ))).
Proof.
  intros HS HA HB HM HN HP.
  pose proof (eqrec_case_substitution _ _ _ _ _ _ HA HM HN HP) as HArg.
  eapply wf_exp_eq_trans.
  - exact (wf_exp_eq_sym _ _ _ _
      (type_substitution_composition _ _ _ _ _ _ _ HS HArg HB)).
  - exact (type_substitution_equality_same_body _ _ _ _ _ _
      (wf_sub_compose _ _ _ _ _ HS HArg) (equation_result_substitution_composition _ _ _ _ _ _ _ _
        HS HA HM HN HP) HB).
Qed.

Local Lemma equation_lift_at_identity_arguments Γ Δ σ A M N P i :
  {{ Δ ⊢s σ : Γ }} -> {{ Γ ⊢ A : Type@i }} ->
  {{ Δ ⊢ M : A[σ] }} -> {{ Δ ⊢ N : A[σ] }} -> {{ Δ ⊢ P : Eq A[σ] M N }} ->
  wf_sub_eq Δ (equation_context Γ A)
    (a_compose (Syntax.q (Syntax.q (Syntax.q σ))) (equation_argument_substitution a_id M N P))
    (equation_argument_substitution σ M N P).
Proof.
  intros HS HA HM HN HP.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (wf_sub_id Δ (substitution_source _ _ _ HS)) as HI.
  pose proof (type_substitution _ _ _ _ _ HI HAs) as HAI.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_sub_id _ _ _ HAs)) as EAI.
  pose proof (convert_term _ _ _ _ _ HM HAI EAI) as HMI.
  pose proof (convert_term _ _ _ _ _ HN HAI EAI) as HNI.
  pose proof (expression_equality_reflexive _ _ _ HM) as EM.
  pose proof (expression_equality_reflexive _ _ _ HN) as EN.
  pose proof (convert_term _ _ _ _ _ HP (wf_eq _ _ _ _ _ HAI HMI HNI)
    (wf_exp_eq_eq_cong _ _ _ _ _ _ _ _ EAI EM EN)) as HPI.
  pose proof (wf_sub_compose _ _ _ _ _ HI HS) as HC.
  pose proof (wf_sub_eq_id_compose_left _ _ _ HS) as EC.
  pose proof (type_substitution_equality_same_body _ _ _ _ _ _ HC EC HA) as EAT.
  pose proof (type_substitution _ _ _ _ _ HC HA) as HAT.
  pose proof (convert_term _ _ _ _ _ HM HAT (wf_exp_eq_sym _ _ _ _ EAT)) as HM0.
  pose proof (convert_term _ _ _ _ _ HN HAT (wf_exp_eq_sym _ _ _ _ EAT)) as HN0.
  pose proof (convert_term _ _ _ _ _ HP (wf_eq _ _ _ _ _ HAT HM0 HN0)
    (wf_exp_eq_eq_cong _ _ _ _ _ _ _ _ (wf_exp_eq_sym _ _ _ _ EAT) EM EN)) as HP0.
  eapply wf_sub_eq_trans.
  - exact (equation_lift_at_arguments _ _ _ _ _ _ _ _ _ _ HS HI HA HMI HNI HPI).
  - exact (equation_arguments_congruent _ _ _ _ _ _ _ _ _ _ _ _ HC EC HA HM0 HN0
      (expression_equality_reflexive _ _ _ HM0)
      (expression_equality_reflexive _ _ _ HN0)
      (expression_equality_reflexive _ _ _ HP0)).
Qed.

Local Lemma equation_motive_instance Γ Δ σ A B M N P i j :
  {{ Δ ⊢s σ : Γ }} -> {{ Γ ⊢ A : Type@i }} ->
  wf_exp (equation_context Γ A) (a_typ j) B ->
  {{ Δ ⊢ M : A[σ] }} -> {{ Δ ⊢ N : A[σ] }} -> {{ Δ ⊢ P : Eq A[σ] M N }} ->
  wf_exp_eq Δ (a_typ j)
    (equation_result_type (a_sub B (Syntax.q (Syntax.q (Syntax.q σ)))) M N P)
    (a_sub B (equation_argument_substitution σ M N P)).
Proof.
  intros HS HA HB HM HN HP.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (equation_triple_lift _ _ _ _ _ HS HA) as HQ.
  pose proof (eqrec_case_substitution _ _ _ _ _ _ HAs HM HN HP) as HArg.
  eapply wf_exp_eq_trans.
  - exact (wf_exp_eq_sym _ _ _ _
      (type_substitution_composition _ _ _ _ _ _ _ HArg HQ HB)).
  - exact (type_substitution_equality_same_body _ _ _ _ _ _
      (wf_sub_compose _ _ _ _ _ HArg HQ) (equation_lift_at_identity_arguments _ _ _ _ _ _ _ _
        HS HA HM HN HP) HB).
Qed.

Local Definition equation_recursion_at σ A B BR M N P :=
  a_eqrec (a_sub A σ) (a_sub B (Syntax.q (Syntax.q (Syntax.q σ))))
    (a_sub BR (Syntax.q σ)) M N P.

Local Lemma equation_recursion_at_typing Γ Δ σ A B BR M N P i j :
  {{ Δ ⊢s σ : Γ }} -> {{ Γ ⊢ A : Type@i }} ->
  wf_exp (equation_context Γ A) (a_typ j) B ->
  wf_exp (A :: Γ) (equation_refl_type A B) BR ->
  {{ Δ ⊢ M : A[σ] }} -> {{ Δ ⊢ N : A[σ] }} -> {{ Δ ⊢ P : Eq A[σ] M N }} ->
  wf_exp Δ (a_sub B (equation_argument_substitution σ M N P))
    (equation_recursion_at σ A B BR M N P).
Proof.
  intros HS HA HB HBR HM HN HP.
  eapply convert_term.
  - exact (wf_eqrec _ _ _ _ _ _ _ _ _
      (type_substitution _ _ _ _ _ HS HA) HM HN
      (type_substitution _ _ _ _ _ (equation_triple_lift _ _ _ _ _ HS HA) HB)
      (equation_reflexive_case_under_lift _ _ _ _ _ _ _ _ HS HA HB HBR) HP).
  - exact (type_substitution _ _ _ _ _ (equation_arguments_typed _ _ _ _ _ _ _ _ HS HA HM HN HP) HB).
  - exact (equation_motive_instance _ _ _ _ _ _ _ _ _ _ HS HA HB HM HN HP).
Qed.

Local Lemma equation_recursion_at_congruence Γ Δ σ A B BR M M' N N' P P' i j :
  {{ Δ ⊢s σ : Γ }} -> {{ Γ ⊢ A : Type@i }} ->
  wf_exp (equation_context Γ A) (a_typ j) B ->
  wf_exp (A :: Γ) (equation_refl_type A B) BR ->
  {{ Δ ⊢ M : A[σ] }} -> {{ Δ ⊢ N : A[σ] }} -> {{ Δ ⊢ P : Eq A[σ] M N }} ->
  {{ Δ ⊢ M ≈ M' : A[σ] }} -> {{ Δ ⊢ N ≈ N' : A[σ] }} -> {{ Δ ⊢ P ≈ P' : Eq A[σ] M N }} ->
  wf_exp_eq Δ (a_sub B (equation_argument_substitution σ M N P))
    (equation_recursion_at σ A B BR M N P) (equation_recursion_at σ A B BR M' N' P').
Proof.
  intros HS HA HB HBR HM HN HP EM EN EP.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (type_substitution _ _ _ _ _ (equation_triple_lift _ _ _ _ _ HS HA) HB) as HBs.
  pose proof (equation_reflexive_case_under_lift _ _ _ _ _ _ _ _ HS HA HB HBR) as HBRs.
  eapply convert_equality.
  - unfold equation_recursion_at.
    exact (wf_exp_eq_eqrec_cong _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      HAs HM HN (expression_equality_reflexive _ _ _ HAs) EM EN
      (expression_equality_reflexive _ _ _ HBs) (expression_equality_reflexive _ _ _ HBRs) EP).
  - exact (type_substitution _ _ _ _ _ (equation_arguments_typed _ _ _ _ _ _ _ _ HS HA HM HN HP) HB).
  - exact (equation_motive_instance _ _ _ _ _ _ _ _ _ _ HS HA HB HM HN HP).
Qed.

Local Lemma equation_recursion_at_reflexivity Γ Δ σ A B BR N i j :
  {{ Δ ⊢s σ : Γ }} -> {{ Γ ⊢ A : Type@i }} ->
  wf_exp (equation_context Γ A) (a_typ j) B ->
  wf_exp (A :: Γ) (equation_refl_type A B) BR ->
  {{ Δ ⊢ N : A[σ] }} ->
  wf_exp_eq Δ (a_sub B (equation_argument_substitution σ N N (a_refl (a_sub A σ) N)))
    (equation_recursion_at σ A B BR N N (a_refl (a_sub A σ) N)) (a_sub BR (a_extend σ N)).
Proof.
  intros HS HA HB HBR HN.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (equation_triple_lift _ _ _ _ _ HS HA) as HQQQ.
  pose proof (type_substitution _ _ _ _ _ HQQQ HB) as HBs.
  pose proof (equation_reflexive_case_under_lift _ _ _ _ _ _ _ _ HS HA HB HBR) as HBRs.
  pose proof (wf_refl _ _ _ _ HAs HN) as HP.
  pose proof (type_substitution _ _ _ _ _
    (equation_arguments_typed _ _ _ _ _ _ _ _ HS HA HN HN HP) HB) as HOut.
  pose proof (equation_motive_instance _ _ _ _ _ _ _ _ _ _ HS HA HB HN HN HP) as EOut.
  pose proof (typing_identity_extension _ _ _ _ HAs HN) as HIdN.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HN) as HSN.
  pose proof (lift_at_argument _ _ _ _ _ _ HS HA HN) as ES.
  pose proof (type_substitution _ _ _ _ _ (eqrec_refl_substitution _ _ _ HA) HB) as HClause.
  eapply wf_exp_eq_trans.
  - exact (convert_equality _ _ _ _ _ _
      (wf_exp_eq_eqrec_beta _ _ _ _ _ _ _ HAs HN HBs HBRs) HOut EOut).
  - eapply convert_equality.
    + exact (substitution_composition_reindex _ _ _ _ _ _ _ _ _
        HQ HIdN HSN ES HClause HBR).
    + exact HOut.
    + exact (equation_reflexive_type_after_argument _ _ _ _ _ _ _ _ HS HA HB HN).
Qed.

Local Lemma certified_equation_inputs Γ Δ σ ρ A M N P i :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} -> {{ Γ ⊢ N : A }} -> {{ Γ ⊢ P : Eq A M N }} ->
  certifies_typed_term Γ (a_typ i) A ->
  certifies_typed_term Γ A M -> certifies_typed_term Γ A N ->
  certifies_typed_term Γ (a_eq A M N) P ->
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  exists a x y p R, eval_exp A ρ a /\ eval_exp M ρ x /\ eval_exp N ρ y /\ eval_exp P ρ p /\
    certified_type i Δ (a_sub A σ) a R /\
    R (a_sub M σ) x /\ R (a_sub N σ) y /\
    certified_candidate (d_eq a x y)
      (equation_candidate Δ (a_sub A σ) (a_sub M σ) (a_sub N σ) R) (a_sub P σ) p /\
    realizes_environment uniform_certified_realization Δ (equation_context Γ A)
      (equation_argument_substitution σ (a_sub M σ) (a_sub N σ) (a_sub P σ))
      (equation_environment ρ x y p).
Proof.
  intros HA HM HN HP HAr HMr HNr HPr Hρ.
  pose proof (proj1 Hρ) as HS.
  destruct (HMr _ _ _ Hρ) as (a & x & Ha & Hx & HMr').
  destruct (HNr _ _ _ Hρ) as (a' & y & Ha' & Hy & HNr').
  destruct (HPr _ _ _ Hρ) as (eq & p & Heq & Hp & HPr').
  pose proof (eval_exp_deterministic _ _ _ Ha _ Ha') as Ea. subst a'.
  assert (HE : eval_exp (a_eq A M N) ρ (d_eq a x y)) by (eapply eval_exp_eq; eassumption).
  pose proof (eval_exp_deterministic _ _ _ HE _ Heq) as E. subst eq.
  destruct (nominal_certified_universe_realization _ _ _ _ _ _ _ HA HAr Hρ Ha) as (R & HG).
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (wf_exp_sub _ _ _ _ _ HS HM) as HM'.
  pose proof (wf_exp_sub _ _ _ _ _ HS HN) as HN'.
  pose proof (uniform_certified_realization_at_identity _ _ _ _ _ _ HAs HM' HMr') as HNomM.
  pose proof (uniform_certified_realization_at_identity _ _ _ _ _ _ HAs HN' HNr') as HNomN.
  pose proof (nominal_certified_member_of_same_code _ _ _ _ _ _ _ _ HNomM HG) as HMemM.
  pose proof (nominal_certified_member_of_same_code _ _ _ _ _ _ _ _ HNomN HG) as HMemN.
  pose proof (type_substitution _ _ _ _ _ HS (wf_eq _ _ _ _ _ HA HM HN)) as HT.
  pose proof (uniform_certified_realization_at_identity _ _ _ _ _ _ HT
    (wf_exp_sub _ _ _ _ _ HS HP) HPr') as HNomP.
  pose proof (has_certified_realization_type_conversion _ _ _ _ _ _ _
    (wf_eq _ _ _ _ _ HAs HM' HN') (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HS HA HM HN) HNomP) as HNomP'.
  assert (HGP : certified_type i Δ (a_eq (a_sub A σ) (a_sub M σ) (a_sub N σ)) (d_eq a x y)
    (certified_candidate (d_eq a x y) (equation_candidate Δ (a_sub A σ) (a_sub M σ) (a_sub N σ) R))).
  { eapply certify_equation; [exact HG | exact HMemM | exact HMemN | intros U v; reflexivity]. }
  pose proof (nominal_certified_member_of_same_code _ _ _ _ _ _ _ _ HNomP' HGP) as HMemP.
  pose proof (certified_equation_environment _ _ _ _ _ _ _ _ _ _ _ _ _
    HA Hρ Ha HNomM HNomN HNomP') as HCurrent.
  exists a, x, y, p, R. repeat first [assumption | split].
Qed.

Local Lemma certified_equation_result_formation Γ A B M N P i j :
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M : A }} -> {{ Γ ⊢ N : A }} -> {{ Γ ⊢ P : Eq A M N }} ->
  wf_exp (equation_context Γ A) (a_typ j) B ->
  certifies_typed_term Γ (a_typ i) A ->
  certifies_typed_term Γ A M -> certifies_typed_term Γ A N ->
  certifies_typed_term Γ (a_eq A M N) P ->
  certifies_typed_term (equation_context Γ A) (a_typ j) B ->
  certified_type_formation Γ (equation_result_type B M N P).
Proof.
  intros HA HM HN HP HB HAr HMr HNr HPr HBr.
  pose proof (type_substitution _ _ _ _ _ (eqrec_case_substitution _ _ _ _ _ _ HA HM HN HP) HB) as HT.
  exists j. split; [exact HT |].
  apply substituted_certified_realization_lifts_to_uniform; [exact HT |].
  intros Δ σ ρ Hρ.
  destruct (certified_equation_inputs _ _ _ _ _ _ _ _ _ HA HM HN HP HAr HMr HNr HPr Hρ)
    as (a & x & y & p & R & Ha & Hx & Hy & Hp & HG & HRx & HRy & HRp & Hρ').
  destruct (HBr _ _ _ Hρ') as (t & b & Ht & Hb & _).
  destruct (nominal_certified_universe_realization _ _ _ _ _ _ _ HB HBr Hρ' Hb) as (S & Hgb).
  exists (d_univ j), b. split; [apply eval_exp_typ | split; [eapply eval_equation_result_type; eassumption |]].
  eapply substituted_certified_universe_member; [exact (proj1 Hρ) | exact HT | | exact Hgb].
  exact (wf_exp_eq_sym _ _ _ _ (equation_result_type_composition _ _ _ _ _ _ _ _ _ _ (proj1 Hρ) HA HB HM HN HP)).
Qed.

Local Lemma eval_equation_reflexive_type_inversion A B ρ x b :
  eval_exp (equation_refl_type A B) (extend_env ρ x) b ->
  eval_exp B (equation_environment ρ x x (d_refl x)) b.
Proof.
  intro H.
  destruct (invert_eval_substitution _ _ _ _ H) as (η & Hη & HE).
  assert (Hsub : eval_sub (equation_reflexive_substitution A) (extend_env ρ x)
      (equation_environment ρ x x (d_refl x))).
  {
    unfold equation_reflexive_substitution, equation_environment.
    apply eval_sub_extend.
    - apply eval_sub_extend; [apply eval_sub_id | apply eval_exp_var].
    - apply eval_exp_refl, eval_exp_var.
  }
  pose proof (eval_sub_deterministic _ _ _ _ Hη Hsub). now subst η.
Qed.

Local Lemma certified_equation_reflexive_compatibility Γ Δ σ ρ A B i j a x y w X Y W R b b' :
  {{ Γ ⊢ A : Type@i }} ->
  wf_exp (equation_context Γ A) (a_typ j) B ->
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  eval_exp A ρ a ->
  certified_type i Δ (a_sub A σ) a R ->
  R X x -> R Y y -> R W w ->
  semantic_member (d_eq a x y) (d_refl w) ->
  eval_exp B (equation_environment ρ w w (d_refl w)) b ->
  eval_exp B (equation_environment ρ x y (d_refl w)) b' ->
  exists Q, semantic_type j b b' Q.
Proof.
  intros HA HB Hρ Ha HG HX HY HW HP Hb Hb'.
  destruct (certified_layer_semantic_type _ _ _ _ _ _ HG) as (D & HD).
  pose proof (semantic_member_in_relation _ _ _ _ _ HD
    (certified_layer_member _ _ _ _ _ _ HG _ _ HX)) as Hxx.
  pose proof (semantic_member_in_relation _ _ _ _ _ HD
    (certified_layer_member _ _ _ _ _ _ HG _ _ HY)) as Hyy.
  pose proof (semantic_member_in_relation _ _ _ _ _ HD
    (certified_layer_member _ _ _ _ _ _ HG _ _ HW)) as Hww.
  pose proof (semantic_member_in_relation _ _ _ _ _
    (semantic_equality _ _ _ _ _ _ _ _ HD Hxx Hyy) HP) as HE.
  assert (Hwx : D w x /\ D w y).
  {
    destruct HE as [(tag & tag' & k & k' & E & _) | (u & v & E & E' & _ & H1 & H2)].
    - discriminate E.
    - injection E as <-. now split.
  }
  destruct Hwx as [Hwx Hwy].
  assert (Href : equality_values_agree D w w (d_refl w) (d_refl w)).
  { right. exists w, w. repeat split; assumption || reflexivity. }
  pose proof (related_equation_environment _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (certified_environment_semantic _ _ _ _ Hρ) Ha Ha HD Hwx Hwy Href) as HEnv.
  pose proof (proj1 (proj2 (proj2 declarative_interpretation)) _ _ _ HB) as H.
  destruct (interpreted_terms_as_types _ _ _ _ H _ _ HEnv)
    as (c & c' & Q & Hc & Hc' & HQ).
  reconcile_values. now exists Q.
Qed.

Local Lemma certified_equation_reflexive_recursion Γ Δ σ ρ A B BR i j a x y w b X Y P W R :
  {{ Γ ⊢ A : Type@i }} ->
  wf_exp (equation_context Γ A) (a_typ j) B ->
  wf_exp (A :: Γ) (equation_refl_type A B) BR ->
  certifies_typed_term (A :: Γ) (equation_refl_type A B) BR ->
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  eval_exp A ρ a ->
  eval_exp B (equation_environment ρ x y (d_refl w)) b ->
  certified_type i Δ (a_sub A σ) a R ->
  R X x -> R Y y -> R W w ->
  {{ Δ ⊢ W ≈ X : A[σ] }} -> {{ Δ ⊢ W ≈ Y : A[σ] }} ->
  {{ Δ ⊢ P : Eq A[σ] X Y }} ->
  {{ Δ ⊢ P ≈ refl A[σ] W : Eq A[σ] X Y }} ->
  semantic_member (d_eq a x y) (d_refl w) ->
  exists r, eval_exp BR (extend_env ρ w) r /\
    has_certified_realization Δ (a_sub B (equation_argument_substitution σ X Y P))
      (equation_recursion_at σ A B BR X Y P) b r.
Proof.
  intros HA HB HBR HBRr Hρ Ha Hb HG HX HY HW EX EY HP EP Hsem.
  pose proof (proj1 Hρ) as HS.
  pose proof (proj2 (proj1 (certified_type_properties _ _ _ _ _ HG))) as HT.
  pose proof (HT _ _ HX) as HXt.
  pose proof (HT _ _ HY) as HYt.
  pose proof (HT _ _ HW) as HWt.
  assert (HNW : has_certified_realization Δ (a_sub A σ) W a w) by
    (exists i, R; now split).
  pose proof (realized_environment_extend _ _ _ _ _ _ _ _ _ _
    uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
    Hρ HA HWt Ha (nominal_certified_realization_is_uniform _ _ _ _ _ HNW)) as HρW.
  destruct (HBRr _ _ _ HρW) as (b0 & r & Hb0 & Hr & HCR).
  pose proof (eval_equation_reflexive_type_inversion _ _ _ _ _ Hb0) as Heb0.
  destruct (certified_equation_reflexive_compatibility _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HA HB Hρ Ha HG HX HY HW Hsem Heb0 Hb) as (Q & HQ).
  pose proof (type_substitution _ _ _ _ _ (eqrec_refl_substitution _ _ _ HA) HB) as HTBR.
  pose proof (uniform_certified_realization_at_identity _ _ _ _ _ _
    (type_substitution _ _ _ _ _ (proj1 HρW) HTBR)
    (wf_exp_sub _ _ _ _ _ (proj1 HρW) HBR) HCR) as HNR.
  destruct HNR as (k & S & HSr & HRr).
  pose proof (semantic_member_in_relation _ _ _ _ _ HQ
    (certified_layer_member _ _ _ _ _ _ HSr _ _ HRr)) as Hrr.
  pose proof (equation_arguments_typed _ _ _ _ _ _ _ _ HS HA HXt HYt HP) as HARG.
  pose proof (equation_arguments_congruent _ _ _ _ _ _ _ _ _ _ _ _ HS
    (substitution_equality_reflexive _ _ _ HS) HA HXt HYt
    (wf_exp_eq_sym _ _ _ _ EX) (wf_exp_eq_sym _ _ _ _ EY) EP) as EA.
  pose proof (type_substitution_equality_same_body _ _ _ _ _ _ HARG EA HB) as E.
  pose proof (equation_reflexive_type_after_argument _ _ _ _ _ _ _ _ HS HA HB HWt) as EOut.
  pose proof (type_substitution _ _ _ _ _ HARG HB) as HOut.
  pose proof (nominal_certified_code_conversion _ _ _ _ _ _ _ _ _ _ _
    HOut (wf_exp_eq_trans _ _ _ _ _ EOut (wf_exp_eq_sym _ _ _ _ E))
    HQ Hrr (ex_intro _ k (ex_intro _ S (conj HSr HRr)))) as Hres.
  exists r. split; [exact Hr |].
  eapply has_certified_realization_term_conversion.
  - exact (equation_recursion_at_typing _ _ _ _ _ _ _ _ _ _ _ HS HA HB HBR HXt HYt HP).
  - eapply wf_exp_eq_trans.
    + exact (equation_recursion_at_congruence _ _ _ _ _ _ _ _ _ _ _ _ _ _
        HS HA HB HBR HXt HYt HP (wf_exp_eq_sym _ _ _ _ EX) (wf_exp_eq_sym _ _ _ _ EY) EP).
    + exact (convert_equality _ _ _ _ _ _
        (equation_recursion_at_reflexivity _ _ _ _ _ _ _ _ _ HS HA HB HBR HWt)
        HOut (wf_exp_eq_sym _ _ _ _ E)).
  - exact Hres.
Qed.

Local Lemma certified_equation_indices Γ A i a R :
  {{ Γ ⊢ A : Type@i }} ->
  certified_type i Γ A a R ->
  exists T, certified_type i (a_sub A a_weaken :: A :: Γ) (equation_indices_type A)
    (d_eq a (d_neut a (d_var (length Γ))) (d_neut a (d_var (S (length Γ))))) T.
Proof.
  intros HA HG.
  pose proof (weaken_type _ _ _ _ _ HA HA) as HAw.
  pose proof (weakening_of_last_binder _ _ _ HA) as H1.
  pose proof (weakening_of_last_binder _ _ _ HAw) as H2.
  pose proof (weakening_between_composition _ _ _ _ _ H1 H2) as HW.
  destruct (certified_type_weakening _ _ _ _ _ HG _ _ HW) as (T & HT & _).
  pose proof (weakening_between_typed _ _ _ H1) as Hσ.
  pose proof (weakening_between_typed _ _ _ H2) as Hτ.
  pose proof (weakening_between_typed _ _ _ HW) as HS.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAt.
  pose proof (wf_exp_eq_sym _ _ _ _
    (type_substitution_composition _ _ _ _ _ _ _ Hτ Hσ HA)) as E.
  pose proof (typed_readback_reflected_variable _ _ _
    (there 0 _ _ (a_sub A a_weaken) (here A Γ))) as Hx.
  pose proof (typed_readback_reflected_variable _ _ _
    (here (a_sub A a_weaken) (A :: Γ))) as Hy.
  assert (Ex : length (a_sub A a_weaken :: A :: Γ) - 1 - 1 = length Γ) by (cbn; lia).
  assert (Ey : length (a_sub A a_weaken :: A :: Γ) - 0 - 1 = S (length Γ)) by (cbn; lia).
  rewrite Ex in Hx. rewrite Ey in Hy.
  destruct (equation_second_variable_typing _ _ _ HA) as [HxT HyT].
  pose proof (typed_readback_type_conversion _ _ _ _ _ _ _ _ _ _ HAt E Hx) as Hx'.
  pose proof (typed_readback_type_conversion _ _ _ _ _ _ _ _ _ _ HAt E Hy) as Hy'.
  pose proof (certified_reflection _ _ _ _ _ _ _ HT HxT Hx' (related_variable (length Γ))) as HX.
  pose proof (certified_reflection _ _ _ _ _ _ _ HT HyT Hy' (related_variable (S (length Γ)))) as HY.
  unfold equation_indices_type.
  eexists. eapply certify_equation; [exact HT | exact HX | exact HY | intros M m; reflexivity].
Qed.

Local Lemma certified_lifted_equation_environments Γ Δ Θ σ τ ρ A a i R :
  {{ Γ ⊢ A : Type@i }} ->
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  certified_type i Δ (a_sub A σ) a R ->
  eval_exp A ρ a ->
  weakening_between Δ Θ τ ->
  let C := a_sub (a_sub A σ) τ in
  let x := d_neut a (d_var (length Θ)) in
  let y := d_neut a (d_var (S (length Θ))) in
  let p := d_neut (d_eq a x y) (d_var (S (S (length Θ)))) in
  realizes_environment uniform_certified_realization (C :: Θ) (A :: Γ)
    (a_compose (Syntax.q σ) (Syntax.q τ)) (extend_env ρ x) /\
  realizes_environment uniform_certified_realization (equation_context Θ C) (equation_context Γ A)
    (a_compose (Syntax.q (Syntax.q (Syntax.q σ))) (Syntax.q (Syntax.q (Syntax.q τ))))
    (equation_environment ρ x y p).
Proof.
  intros HA Hρ HG Ha HW C x y p.
  pose proof (proj1 Hρ) as HS.
  pose proof (weakening_between_typed _ _ _ HW) as HT.
  pose proof (certified_environment_weakening_between _ _ _ _ _ _ Hρ HW) as Hρ0.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (type_substitution _ _ _ _ _ HT HAs) as HC.
  pose proof (type_substitution_composition _ _ _ _ _ _ _ HT HS HA) as EC.
  destruct (certified_type_weakening _ _ _ _ _ HG _ _ HW) as (T & HCg & _).
  pose proof (certified_type_conversion _ _ _ _ _ _ HCg
    (type_substitution _ _ _ _ _ (proj1 Hρ0) HA) (wf_exp_eq_sym _ _ _ _ EC)) as HBase.
  pose proof (certified_environment_fresh_binder _ _ _ _ _ _ _ _ _
    HA HC EC Hρ0 Ha HBase) as HρA.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (lifted_substitution _ _ _ _ _ HT HAs) as HQ'.
  pose proof (wf_sub_compose _ _ _ _ _ HQ' HQ) as Hqcomp.
  pose proof (realized_environment_substitution_conversion _ _ _ _ _ _
    uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
    HρA Hqcomp (wf_sub_eq_sym _ _ _ _
      (compose_lifted_substitutions _ _ _ _ _ _ _ HS HT HA))) as Hρ1.
  split; [exact Hρ1 |].

  pose proof (weaken_type _ _ _ _ _ HA HA) as HAw.
  pose proof (weaken_type _ _ _ _ _ HAs HAs) as HAsw.
  pose proof (weaken_type _ _ _ _ _ HC HC) as HCw.
  pose proof (weaken_type_under_lifted_substitution _ _ _ _ _ HS HA) as E0.
  pose proof (weaken_type_under_lifted_substitution _ _ _ _ _ HT HAs) as E1.
  pose proof (type_substitution_congruence _ _ _ _ _ _ _ HQ'
    (substitution_equality_reflexive _ _ _ HQ') E0) as E0'.
  pose proof (type_substitution_composition _ _ _ _ _ _ _ HQ' HQ HAw) as Eβ.
  pose proof (wf_exp_eq_trans _ _ _ _ _ Eβ (wf_exp_eq_trans _ _ _ _ _ E0' E1)) as E2.
  destruct (certified_type_weakening _ _ _ _ _ HCg _ _ (weakening_of_last_binder _ _ _ HC))
    as (W & HCwg & _).
  pose proof (certified_type_conversion _ _ _ _ _ _ HCwg
    (type_substitution _ _ _ _ _ Hqcomp HAw) (wf_exp_eq_sym _ _ _ _ E2)) as HAwreal.
  pose proof (eval_exp_sub _ _ _ _ _ (eval_sub_weaken (extend_env ρ x)) Ha) as Haw.
  pose proof (certified_environment_fresh_binder _ _ _ _ _ _ _ _ _
    HAw HCw E2 Hρ1 Haw HAwreal) as HρA2.
  pose proof (equation_double_lift _ _ _ _ _ HS HA) as HQQ.
  pose proof (equation_double_lift _ _ _ _ _ HT HAs) as HQQ'.
  pose proof (wf_sub_compose _ _ _ _ _ HQQ' HQQ) as Hqqcomp.
  pose proof (realized_environment_substitution_conversion _ _ _ _ _ _
    uniform_certified_realization_type_conversion uniform_certified_realization_term_conversion
    HρA2 Hqqcomp (wf_sub_eq_sym _ _ _ _
      (compose_lifts_over_equal_declarations _ _ _ _ _ _ _ _ _
        HQ HQ' HAw HAsw HCw E0 E1))) as Hρ2.

  pose proof (eqrec_context _ _ _ HA) as HEq.
  pose proof (eqrec_context _ _ _ HAs) as HEqs.
  pose proof (eqrec_context _ _ _ HC) as HEqt.
  pose proof (equation_indices_under_double_lift _ _ _ _ _ HS HA) as E0e.
  pose proof (equation_indices_under_double_lift _ _ _ _ _ HT HAs) as E1e.
  pose proof (type_substitution_congruence _ _ _ _ _ _ _ HQQ'
    (substitution_equality_reflexive _ _ _ HQQ') E0e) as E0e'.
  pose proof (wf_exp_eq_trans _ _ _ _ _
    (type_substitution_composition _ _ _ _ _ _ _ HQQ' HQQ HEq)
    (wf_exp_eq_trans _ _ _ _ _ E0e' E1e)) as E2e.
  destruct (certified_equation_indices _ _ _ _ _ HC HCg) as (V & HInd).
  pose proof (certified_type_conversion _ _ _ _ _ _ HInd
    (type_substitution _ _ _ _ _ Hqqcomp HEq) (wf_exp_eq_sym _ _ _ _ E2e)) as HEqr.
  pose proof (eval_equation_context_last _ _ _ x y Ha) as Heq.
  pose proof (certified_environment_fresh_binder _ _ _ _ _ _ _ _ _
    HEq HEqt E2e Hρ2 Heq HEqr) as HρA3.
  pose proof (equation_triple_lift _ _ _ _ _ HS HA) as HQQQ.
  pose proof (equation_triple_lift _ _ _ _ _ HT HAs) as HQQQ'.
  eapply realized_environment_substitution_conversion;
    [exact uniform_certified_realization_type_conversion | exact uniform_certified_realization_term_conversion | |
      exact (wf_sub_compose _ _ _ _ _ HQQQ' HQQQ) |].
  - exact HρA3.
  - exact (wf_sub_eq_sym _ _ _ _ (compose_lifts_over_equal_declarations _ _ _ _ _ _ _ _ _
      HQQ HQQ' HEq HEqs HEqt E0e E1e)).
Qed.

Local Lemma typed_certified_neutral_equation_recursion
    Γ Δ σ ρ A B BR X Y P i j a x y R k :
  {{ Γ ⊢ A : Type@i }} ->
  wf_exp (equation_context Γ A) (a_typ j) B ->
  wf_exp (A :: Γ) (equation_refl_type A B) BR ->
  certifies_typed_term (equation_context Γ A) (a_typ j) B ->
  certifies_typed_term (A :: Γ) (equation_refl_type A B) BR ->
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  eval_exp A ρ a ->
  certified_type i Δ (a_sub A σ) a R -> R X x -> R Y y ->
  {{ Δ ⊢ P : Eq A[σ] X Y }} ->
  typed_neutral_readback Δ (a_eq (a_sub A σ) X Y) P k ->
  typed_neutral_readback Δ (a_sub B (equation_argument_substitution σ X Y P))
    (equation_recursion_at σ A B BR X Y P) (d_eqrec ρ a B BR x y k).
Proof.
  intros HA HB HBR HBr HBRr Hρ Ha HG HX HY HP Hne Θ τ HW.
  pose proof (proj1 Hρ) as HS.
  pose proof (context_weakening_typed _ _ _ HW) as HT.
  pose proof (weakening_between_canonical _ _ _ HW) as HW'.
  pose proof (type_substitution _ _ _ _ _ HS HA) as HAs.
  pose proof (type_substitution _ _ _ _ _ HT HAs) as HA0.
  pose proof (lifted_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (lifted_substitution _ _ _ _ _ HT HAs) as HQ'.
  pose proof (equation_triple_lift _ _ _ _ _ HS HA) as HQQQ.
  pose proof (equation_triple_lift _ _ _ _ _ HT HAs) as HQQQ'.
  pose proof (type_substitution _ _ _ _ _ HQQQ HB) as HBs.
  pose proof (type_substitution _ _ _ _ _ HQQQ' HBs) as HB0.
  pose proof (equation_reflexive_case_under_lift _ _ _ _ _ _ _ _ HS HA HB HBR) as HBRs.
  pose proof (equation_reflexive_case_under_lift _ _ _ _ _ _ _ _ HT HAs HBs HBRs) as HBR0.
  destruct (certified_lifted_equation_environments _ _ _ _ _ _ _ _ _ _
    HA Hρ HG Ha HW') as (HρR & HρB).

  destruct (HBr _ _ _ HρB) as (u & c & Hu & Hc & _).
  destruct (nominal_certified_universe_realization _ _ _ _ _ _ _ HB HBr HρB Hc) as (S & HC).
  pose proof (certified_type_conversion _ _ _ _ _ _ HC HB0
    (type_substitution_composition _ _ _ _ _ _ _ HQQQ' HQQQ HB)) as HC0.
  destruct (typed_type_readback_here _ _ _ _ HB0 (certified_type_readback _ _ _ _ _ HC0))
    as (Bv & HBv & HBvt & HBvE).

  destruct (HBRr _ _ _ HρR) as (b & r & Hb & Hr & HR).
  pose proof (eval_equation_reflexive_type_inversion _ _ _ _ _ Hb) as Hb'.
  pose proof (type_substitution _ _ _ _ _ (eqrec_refl_substitution _ _ _ HA) HB) as HClause.
  pose proof (certified_readback_from_nested_substitution _ _ _ _ _ _ _ _ _ _
    HQ HQ' HClause HBR HR) as HR0.
  pose proof (type_substitution _ _ _ _ _ (eqrec_refl_substitution _ _ _ HA0) HB0) as HClause0.
  pose proof (type_substitution_congruence _ _ _ _ _ _ _ HQ'
    (substitution_equality_reflexive _ _ _ HQ') (equation_reflexive_type_under_lift _ _ _ _ _ _ _ HS HA HB)) as EClause1.
  pose proof (equation_reflexive_type_under_lift _ _ _ _ _ _ _ HT HAs HBs) as EClause2.
  pose proof (typed_readback_type_conversion _ _ _ _ _ _ _ _ _ _ HClause0
    (wf_exp_eq_trans _ _ _ _ _ EClause1 EClause2) HR0) as HR'.
  destruct (typed_readback_here _ _ _ _ _ _ _ _ _ HClause0 HBR0 HR')
    as (BRv & HBRv & HBRvt & HBRvE).

  destruct (typed_type_readback_at_extension _ _ _ _ _ _ HW (certified_type_readback _ _ _ _ _ HG))
    as (Av & HAv & HAvt & HAvE).
  pose proof (proj2 (proj1 (certified_type_properties _ _ _ _ _ HG))) as HAt.
  pose proof (HAt _ _ HX) as HXt.
  pose proof (HAt _ _ HY) as HYt.
  pose proof (wf_exp_sub _ _ _ _ _ HT HXt) as HX0.
  pose proof (wf_exp_sub _ _ _ _ _ HT HYt) as HY0.
  destruct ((certified_term_readback _ _ _ _ _ _ _ HG HX) _ _ HW) as (Xv & HXv & HXvt & HXvE).
  destruct ((certified_term_readback _ _ _ _ _ _ _ HG HY) _ _ HW) as (Yv & HYv & HYvt & HYvE).
  destruct (Hne _ _ HW) as (Pv & HPv & HPvt & HPvE).
  pose proof (wf_eq _ _ _ _ _ HA0 HX0 HY0) as HEq.
  pose proof (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HT HAs HXt HYt) as EEq.
  pose proof (convert_term _ _ _ _ _ (wf_exp_sub _ _ _ _ _ HT HP) HEq EEq) as HP0.
  pose proof (convert_term _ _ _ _ _ HPvt HEq EEq) as HPvt'.
  pose proof (convert_equality _ _ _ _ _ _ HPvE HEq EEq) as HPvE'.
  destruct (reconstruct_readback_equation_recursion _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HA0 HAvt HAvE HX0 HXvt HXvE HY0 HYvt HYvE HB0 HBvt HBvE HBRvt HBRvE
    HP0 HPvt' HPvE') as (Hres & Eres).

  pose proof (type_substitution _ _ _ _ _ (equation_arguments_typed _ _ _ _ _ _ _ _ HS HA HXt HYt HP) HB) as HOut.
  pose proof (type_substitution _ _ _ _ _ HT HOut) as HOut'.
  pose proof (equation_result_type_composition _ _ _ _ _ _ _ _ _ _ HT HAs HBs HXt HYt HP) as EArgs.
  pose proof (type_substitution_congruence _ _ _ _ _ _ _ HT
    (substitution_equality_reflexive _ _ _ HT)
    (equation_motive_instance _ _ _ _ _ _ _ _ _ _ HS HA HB HXt HYt HP)) as EOrig.
  pose proof (wf_exp_eq_trans _ _ _ _ _ (wf_exp_eq_sym _ _ _ _ EArgs) EOrig) as EOut.
  pose proof (equation_motive_instance _ _ _ _ _ _ _ _ _ _ HT HAs HBs HX0 HY0 HP0) as ENow.
  pose proof (wf_exp_eq_trans _ _ _ _ _ ENow EOut) as EFinal.
  exists (ne_eqrec Av Bv BRv Xv Yv Pv). repeat split.
  - eapply read_ne_eqrec; eassumption.
  - exact (convert_term _ _ _ _ _ Hres HOut' EFinal).
  - eapply wf_exp_eq_trans.
    + eapply convert_equality; [| exact HOut' | exact EOut].
      unfold equation_recursion_at. eapply wf_exp_eq_eqrec_sub; eassumption.
    + exact (convert_equality _ _ _ _ _ _ Eres HOut' EFinal).
Qed.

Local Lemma certified_eqrec_neutral_agreement Γ Δ σ ρ A B BR i j a x y X Y R tag k :
  {{ Γ ⊢ A : Type@i }} ->
  wf_exp (equation_context Γ A) (a_typ j) B ->
  wf_exp (A :: Γ) (equation_refl_type A B) BR ->
  realizes_environment uniform_certified_realization Δ Γ σ ρ ->
  eval_exp A ρ a ->
  certified_type i Δ (a_sub A σ) a R ->
  R X x -> R Y y ->
  semantic_member (d_eq a x y) (d_neut tag k) ->
  neutrals_agree (d_eqrec ρ a B BR x y k) (d_eqrec ρ a B BR x y k).
Proof.
  intros HA HB HBR Hρ Ha HG HX HY Hmem.
  pose proof (certified_environment_semantic _ _ _ _ Hρ) as HEnv.
  destruct (certified_layer_semantic_type _ _ _ _ _ _ HG) as (D & HD).
  pose proof (semantic_member_in_relation _ _ _ _ _ HD
    (certified_layer_member _ _ _ _ _ _ HG _ _ HX)) as Hxx.
  pose proof (semantic_member_in_relation _ _ _ _ _ HD
    (certified_layer_member _ _ _ _ _ _ HG _ _ HY)) as Hyy.
  pose proof (semantic_member_in_relation _ _ _ _ _
    (semantic_equality _ _ _ _ _ _ _ _ HD Hxx Hyy) Hmem) as HE.
  assert (Hkk : neutrals_agree k k).
  {
    destruct HE as [(t & t' & k' & k'' & E & E' & Hne) | (u & v & E & _)].
    - inversion E; inversion E'; now subst.
    - discriminate E.
  }
  pose proof (proj1 (proj2 (proj2 declarative_interpretation)) _ _ _ HA) as HsemA.
  pose proof (proj1 (proj2 (proj2 declarative_interpretation)) _ _ _ HB) as HsemB.
  pose proof (proj1 (proj2 (proj2 declarative_interpretation)) _ _ _ HBR) as HsemBR.
  pose proof (interpreted_terms_as_types _ _ _ _ HsemA) as HAI.
  pose proof (interpreted_terms_as_types _ _ _ _ HsemB) as HBI.
  exact (neutral_equation_readback _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HD Hxx Hyy
    (interpreted_equation_motive _ _ _ _ _ _ _ _ _ _ _ HAI HBI HEnv Ha HD)
    (interpreted_equation_refl_case _ _ _ _ _ _ _ _ _ _ _ _ _ HAI HBI HsemBR HEnv Ha HD)
    Hkk).
Qed.

Local Lemma uniform_certified_equation_elimination : certifies_equation_elimination.
Proof.
  intros Γ i A M1 M2 j B BR P HA HM1 HM2 HB HBR HP HAr HM1r HM2r HBr HBRr HPr.
  pose proof (wf_eqrec _ _ _ _ _ _ _ _ _ HA HM1 HM2 HB HBR HP) as Hrec.
  split.
  - apply substituted_certified_realization_lifts_to_uniform; [exact Hrec |].
    intros Δ σ ρ Hρ.
    pose proof (proj1 Hρ) as HS.
    destruct (certified_equation_inputs _ _ _ _ _ _ _ _ _ HA HM1 HM2 HP HAr HM1r HM2r HPr Hρ)
      as (a & x & y & p & R & Ha & Hx & Hy & Hp & HG & HRx & HRy & HRp & HρP).
    destruct (HBr _ _ _ HρP) as (u & b & Hu & Hb & _).
    destruct (nominal_certified_universe_realization _ _ _ _ _ _ _ HB HBr HρP Hb) as (S & HGout).
    pose proof (wf_exp_sub _ _ _ _ _ HS HM1) as HX.
    pose proof (wf_exp_sub _ _ _ _ _ HS HM2) as HY.
    destruct HRp as (Hgood & HPtyped & HView).
    pose proof (type_substitution _ _ _ _ _ (eqrec_case_substitution _ _ _ _ _ _ HA HM1 HM2 HP) HB) as HRT.
    pose proof (type_substitution _ _ _ _ _ HS HRT) as HRT'.
    pose proof (equation_result_type_composition _ _ _ _ _ _ _ _ _ _ HS HA HB HM1 HM2 HP) as ER.
    pose proof (wf_exp_eq_eqrec_sub _ _ _ _ _ _ _ _ _ _ _ HS HA HM1 HM2 HB HBR HP) as ERaw.
    assert (Hfinish : forall r,
      eval_eqrec a B BR x y p ρ r ->
      has_certified_realization Δ
        (a_sub B (equation_argument_substitution σ (a_sub M1 σ) (a_sub M2 σ) (a_sub P σ)))
        (equation_recursion_at σ A B BR (a_sub M1 σ) (a_sub M2 σ) (a_sub P σ)) b r ->
      exists b' m, eval_exp (equation_result_type B M1 M2 P) ρ b' /\
        eval_exp (a_eqrec A B BR M1 M2 P) ρ m /\
        has_certified_realization Δ (a_sub (equation_result_type B M1 M2 P) σ)
          (a_sub (a_eqrec A B BR M1 M2 P) σ) b' m).
    {
      intros r Hr Hnom.
      exists b, r. split; [eapply eval_equation_result_type; eassumption |].
      split; [eapply eval_exp_eqrec; eassumption |].
      eapply has_certified_realization_term_conversion.
      - exact (wf_exp_sub _ _ _ _ _ HS Hrec).
      - exact (convert_equality _ _ _ _ _ _ ERaw HRT' (wf_exp_eq_sym _ _ _ _ ER)).
      - exact (has_certified_realization_type_conversion _ _ _ _ _ _ _
          HRT' (wf_exp_eq_sym _ _ _ _ ER) Hnom).
    }
    destruct HView as [(tag & k & -> & Hne) | (W & w & -> & HRw & EX & EY & EP)].
    + eapply Hfinish with (r := d_neut b (d_eqrec ρ a B BR x y k)).
      * now apply eval_eqrec_neut.
      * exists j, S. split; [exact HGout |].
        eapply certified_reflection; [exact HGout | | |].
        -- exact (equation_recursion_at_typing _ _ _ _ _ _ _ _ _ _ _ HS HA HB HBR HX HY HPtyped).
        -- exact (typed_certified_neutral_equation_recursion _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             HA HB HBR HBr HBRr Hρ Ha HG HRx HRy HPtyped Hne).
        -- exact (certified_eqrec_neutral_agreement _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
             HA HB HBR Hρ Ha HG HRx HRy Hgood).
    + destruct (certified_equation_reflexive_recursion _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        HA HB HBR HBRr Hρ Ha Hb HG HRx HRy HRw EX EY HPtyped EP Hgood)
        as (r & Hr & Hnom).
      eapply Hfinish with (r := r); [apply eval_eqrec_refl; exact Hr | exact Hnom].
  - exact (certified_equation_result_formation _ _ _ _ _ _ _ _
      HA HM1 HM2 HP HB HAr HM1r HM2r HPr HBr).
Qed.

Local Lemma certified_typing_interpretation : uniform_certified_typing_interpretation.
Proof.
  exact (uniform_certified_typing_from_equation_elimination uniform_certified_equation_elimination).
Qed.

Local Lemma certified_readback_preserves_typing : readback_preserves_typing.
Proof.
  exact (uniform_certified_typing_interpretation_implies_readback certified_typing_interpretation).
Qed.

Theorem alg_type_check_sound : forall {Γ i A M},
    {{ Γ ⊢a M ⟸ A }} ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A }}.
Proof.
  intros Γ i A M HM HΓ HA.
  exact (proj1 (algorithm_sound_from_readback certified_readback_preserves_typing)
    _ _ _ HM HΓ (ex_intro _ i HA)).
Qed.

Theorem alg_type_check_complete : forall {Γ A M},
    user_exp M ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢a M ⟸ A }}.
Proof.
  exact (algorithm_complete_from_readback certified_readback_preserves_typing equal_types_have_shared_readback).
Qed.
