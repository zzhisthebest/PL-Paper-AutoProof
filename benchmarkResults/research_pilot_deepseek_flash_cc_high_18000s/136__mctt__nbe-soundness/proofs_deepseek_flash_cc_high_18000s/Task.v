From Coq Require Import Arith Lia List.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export NbE.
Import Domain_Notations.
Arguments wf_nat {_} _.
Arguments wf_zero {_} _.
Arguments wf_sub_id {_} _.
Arguments wf_sub_eq_id {_} _.

Arguments wf_ctx_extend {_ _ _} _ _.
Arguments wf_ctx_sub_extend {_ _ _ _ _} _ _ _ _.
Arguments wf_typ {_ _} _.
Arguments wf_succ {_ _} _.
Arguments wf_natrec {_ _ _ _ _ _} _ _ _ _.
Arguments wf_pi {_ _ _ _} _ _.
Arguments wf_fn {_ _ _ _ _} _ _.
Arguments wf_app {_ _ _ _ _ _} _ _ _ _.
Arguments wf_sigma {_ _ _ _} _ _.
Arguments wf_pair {_ _ _ _ _ _} _ _ _ _.
Arguments wf_fst {_ _ _ _ _} _ _ _.
Arguments wf_snd {_ _ _ _ _} _ _ _.
Arguments wf_vlookup {_ _ _} _ _.
Arguments wf_eq {_ _ _ _ _} _ _ _.
Arguments wf_refl {_ _ _ _} _ _.
Arguments wf_eqrec {_ _ _ _ _ _ _ _ _} _ _ _ _ _ _.
Arguments wf_exp_sub {_ _ _ _ _} _ _.
Arguments wf_exp_subtyp {_ _ _ _ _} _ _ _.
Arguments wf_sub_weaken {_ _} _.
Arguments wf_sub_compose {_ _ _ _ _} _ _.
Arguments wf_sub_extend {_ _ _ _ _ _} _ _ _.
Arguments wf_sub_subtyp {_ _ _ _} _ _ _.
Arguments wf_exp_eq_typ_sub {_ _ _ _} _.
Arguments wf_exp_eq_nat_sub {_ _ _} _.
Arguments wf_exp_eq_zero_sub {_ _ _} _.
Arguments wf_exp_eq_succ_sub {_ _ _ _} _ _.
Arguments wf_exp_eq_succ_cong {_ _ _} _.
Arguments wf_exp_eq_natrec_cong {_ _ _ _ _ _ _ _ _ _} _ _ _ _ _.
Arguments wf_exp_eq_natrec_sub {_ _ _ _ _ _ _ _} _ _ _ _ _.
Arguments wf_exp_eq_nat_beta_zero {_ _ _ _ _} _ _ _.
Arguments wf_exp_eq_nat_beta_succ {_ _ _ _ _ _} _ _ _ _.
Arguments wf_exp_eq_pi_sub {_ _ _ _ _ _} _ _ _.
Arguments wf_exp_eq_pi_cong {_ _ _ _ _ _} _ _ _.
Arguments wf_exp_eq_fn_cong {_ _ _ _ _ _ _} _ _ _.
Arguments wf_exp_eq_fn_sub {_ _ _ _ _ _ _} _ _ _.
Arguments wf_exp_eq_app_cong {_ _ _ _ _ _ _ _} _ _ _ _.
Arguments wf_exp_eq_app_sub {_ _ _ _ _ _ _ _} _ _ _ _ _.
Arguments wf_exp_eq_pi_beta {_ _ _ _ _ _} _ _ _ _.
Arguments wf_exp_eq_pi_eta {_ _ _ _ _} _ _ _.
Arguments wf_exp_eq_sigma_sub {_ _ _ _ _ _} _ _ _.
Arguments wf_exp_eq_sigma_cong {_ _ _ _ _ _} _ _ _.
Arguments wf_exp_eq_pair_cong {_ _ _ _ _ _ _ _ _ _} _ _ _ _ _.
Arguments wf_exp_eq_pair_sub {_ _ _ _ _ _ _ _} _ _ _ _ _.
Arguments wf_exp_eq_fst_cong {_ _ _ _ _ _} _ _ _.
Arguments wf_exp_eq_fst_sub {_ _ _ _ _ _ _} _ _ _ _.
Arguments wf_exp_eq_snd_cong {_ _ _ _ _ _} _ _ _.
Arguments wf_exp_eq_snd_sub {_ _ _ _ _ _ _} _ _ _ _.
Arguments wf_exp_eq_fst_beta {_ _ _ _ _ _} _ _ _ _.
Arguments wf_exp_eq_snd_beta {_ _ _ _ _ _} _ _ _ _.
Arguments wf_exp_eq_sigma_eta {_ _ _ _ _} _ _ _.
Arguments wf_exp_eq_eq_sub {_ _ _ _ _ _ _} _ _ _ _.
Arguments wf_exp_eq_refl_sub {_ _ _ _ _ _} _ _ _.
Arguments wf_exp_eq_eqrec_sub {_ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _.
Arguments wf_exp_eq_eq_cong {_ _ _ _ _ _ _ _} _ _ _.
Arguments wf_exp_eq_refl_cong {_ _ _ _ _ _} _ _.
Arguments wf_exp_eq_eqrec_cong {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _} _ _ _ _ _ _ _ _ _.
Arguments wf_exp_eq_eqrec_beta {_ _ _ _ _ _ _} _ _ _ _.
Arguments wf_exp_eq_var {_ _ _} _ _.
Arguments wf_exp_eq_var_0_sub {_ _ _ _ _ _} _ _ _.
Arguments wf_exp_eq_var_S_sub {_ _ _ _ _ _ _ _} _ _ _ _.
Arguments wf_exp_eq_var_weaken {_ _ _ _} _ _.
Arguments wf_exp_eq_sub_cong {_ _ _ _ _ _ _} _ _.
Arguments wf_exp_eq_sub_id {_ _ _} _.
Arguments wf_exp_eq_sub_compose {_ _ _ _ _ _ _} _ _ _.
Arguments wf_exp_eq_subtyp {_ _ _ _ _ _} _ _ _.
Arguments wf_exp_eq_sym {_ _ _ _} _.
Arguments wf_exp_eq_trans {_ _ _ _ _} _ _.
Arguments wf_sub_eq_weaken {_ _} _.
Arguments wf_sub_eq_compose_cong {_ _ _ _ _ _ _} _ _.
Arguments wf_sub_eq_extend_cong {_ _ _ _ _ _ _ _} _ _ _.
Arguments wf_sub_eq_id_compose_right {_ _ _} _.
Arguments wf_sub_eq_id_compose_left {_ _ _} _.
Arguments wf_sub_eq_compose_assoc {_ _ _ _ _ _ _} _ _ _.
Arguments wf_sub_eq_extend_compose {_ _ _ _ _ _ _ _} _ _ _ _.
Arguments wf_sub_eq_p_extend {_ _ _ _ _ _} _ _ _.
Arguments wf_sub_eq_extend {_ _ _ _} _.
Arguments wf_sub_eq_sym {_ _ _ _} _.
Arguments wf_sub_eq_trans {_ _ _ _ _} _ _.
Arguments wf_sub_eq_subtyp {_ _ _ _ _} _ _ _.
Arguments wf_subtyp_refl {_ _ _ _} _ _.
Arguments wf_subtyp_trans {_ _ _ _} _ _.
Arguments wf_subtyp_univ {_ _ _} _.
Arguments wf_subtyp_pi {_ _ _ _ _ _} _ _ _ _ _ _.
Arguments wf_subtyp_sigma {_ _ _ _ _ _} _ _ _ _ _ _.

(* Arguments omitted: we use explicit forms where needed. *)

Lemma wf_ctx_sub_wf_l : forall Γ Δ, {{ ⊢ Γ ⊆ Δ }} -> {{ ⊢ Γ }}
with wf_ctx_sub_wf_r : forall Γ Δ, {{ ⊢ Γ ⊆ Δ }} -> {{ ⊢ Δ }}.
Proof.
  - intros Γ Δ H. induction H; eauto using wf_ctx_extend, wf_ctx_empty.
  - intros Γ Δ H. induction H; eauto using wf_ctx_extend, wf_ctx_empty.
Qed.

Lemma wf_sub_wf_ctx_l : forall Γ Δ σ, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Γ }}.
Proof. intros Γ Δ σ H. induction H; eauto using wf_ctx_empty, wf_ctx_extend. Qed.

Lemma wf_sub_wf_ctx_r : forall Γ Δ σ, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Δ }}.
Proof. intros Γ Δ σ H. induction H; eauto using wf_ctx_extend, wf_ctx_empty, wf_ctx_sub_wf_r.
  inversion H; eauto.
Qed.

Lemma wf_exp_wf_ctx : forall Γ A M, {{ Γ ⊢ M : A }} -> {{ ⊢ Γ }}.
Proof. intros Γ A M H. induction H; eauto using wf_sub_wf_ctx_l, wf_ctx_extend, wf_sub_wf_ctx_r. Qed.

Lemma wf_exp_eq_refl : forall Γ A M, {{ Γ ⊢ M : A }} -> {{ Γ ⊢ M ≈ M : A }}.
Proof. intros Γ A M H.
  pose proof (wf_exp_eq_sub_id H) as H1.
  pose proof (wf_exp_eq_sym H1) as H2.
  eapply wf_exp_eq_trans; eassumption. Qed.
Arguments wf_exp_eq_refl {_ _ _} _.

Lemma wf_exp_typing_conv : forall Γ A A' M i,
  {{ Γ ⊢ M : A }} -> {{ Γ ⊢ A' : Type@i }} -> {{ Γ ⊢ A ≈ A' : Type@i }} -> {{ Γ ⊢ M : A' }}.
Proof. intros. refine (@wf_exp_subtyp Γ A M i A' _ _ _); [assumption|assumption|].
  refine (@wf_subtyp_refl Γ i A' A _ _); assumption. Qed.

Lemma wf_exp_typing_conv_sym : forall Γ A A' M i,
  {{ Γ ⊢ M : A }} -> {{ Γ ⊢ A' : Type@i }} -> {{ Γ ⊢ A' ≈ A : Type@i }} -> {{ Γ ⊢ M : A' }}.
Proof. intros Γ A A' M i H H0 H1. refine (@wf_exp_typing_conv Γ A A' M i H H0 _).
  eapply wf_exp_eq_sym; exact H1. Qed.

Lemma wf_exp_eq_conv_type : forall Γ A A' M M' i,
  {{ Γ ⊢ M ≈ M' : A }} -> {{ Γ ⊢ A' : Type@i }} -> {{ Γ ⊢ A ≈ A' : Type@i }} -> {{ Γ ⊢ M ≈ M' : A' }}.
Proof. intros. refine (@wf_exp_eq_subtyp Γ A M M' i A' _ _ _); [assumption|assumption|].
  refine (@wf_subtyp_refl Γ i A' A _ _); assumption. Qed.

Lemma wf_exp_eq_conv_type_sym : forall Γ A A' M M' i,
  {{ Γ ⊢ M ≈ M' : A }} -> {{ Γ ⊢ A' : Type@i }} -> {{ Γ ⊢ A' ≈ A : Type@i }} -> {{ Γ ⊢ M ≈ M' : A' }}.
Proof. intros Γ A A' M M' i H H0 H1. refine (@wf_exp_eq_conv_type Γ A A' M M' i H H0 _).
  eapply wf_exp_eq_sym; exact H1. Qed.

Lemma wf_exp_typing_le : forall Γ A i j, {{ Γ ⊢ A : Type@i }} -> i <= j -> {{ Γ ⊢ A : Type@j }}.
Proof.
  intros Γ A i j H Hij.
  assert (Hcases : i < j \/ i = j) by lia. destruct Hcases as [Hlt|Heq].
  - refine (@wf_exp_subtyp Γ (a_typ i) A (S j) (a_typ j) H _ _).
    + eapply wf_typ. eapply wf_exp_wf_ctx in H. exact H.
    + refine (@wf_subtyp_univ Γ i j _ Hlt). eapply wf_exp_wf_ctx in H. exact H.
  - subst j. exact H.
Qed.

(* Typing of a context entry *)
Lemma wf_exp_weaken_ty : forall Γ B A i, {{ ⊢ Γ, B }} -> {{ Γ ⊢ A : Type@i }} -> {{ Γ, B ⊢ A[Wk] : Type@i }}.
Proof.
  intros Γ B A i Hctx HA.
  pose proof (wf_sub_weaken (A:=B) (Γ:=Γ) Hctx) as Hwk.
  pose proof (wf_exp_sub Hwk HA) as Hsub.
  (* Hsub : Γ, B ⊢ A[Wk] : (Type@i)[Wk] *)
  eapply wf_exp_typing_conv with (A := a_sub (a_typ i) a_weaken).
  - exact Hsub.
  - eapply wf_typ. eapply wf_sub_wf_ctx_l in Hwk. exact Hwk.
  - eapply wf_exp_eq_typ_sub. exact Hwk.
Qed.

Lemma wf_ctx_lookup_ty : forall Γ x A, {{ ⊢ Γ }} -> {{ #x : A ∈ Γ }} -> exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
  intros Γ x A Hwf Hlk. revert Hwf. induction Hlk as [A0 Γ0 | n A0 Γ0 B0 Hlk IH]; intros Hwf.
  - (* here *)
    inversion Hwf as [| Γ' j A' w wA Hty]; subst.
    exists j. eapply wf_exp_weaken_ty; eassumption.
  - (* there *)
    inversion Hwf as [| Γ' j A' w wA Hty]; subst.
    destruct (IH w) as [i Hi].
    exists i. eapply wf_exp_weaken_ty; eassumption.
Qed.

Lemma wf_exp_sub_wf_ty : forall Γ Δ σ A i, {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ A : Type@i }} -> {{ Γ ⊢ A[σ] : Type@i }}.
Proof.
  intros Γ Δ σ A i Hσ HA.
  pose proof (wf_exp_sub Hσ HA) as Hsub.
  eapply wf_exp_typing_conv with (A := a_sub (a_typ i) σ).
  - exact Hsub.
  - eapply wf_typ. eapply wf_sub_wf_ctx_l in Hσ. exact Hσ.
  - eapply wf_exp_eq_typ_sub. exact Hσ.
Qed.
Arguments wf_exp_sub_wf_ty {_ _ _ _ _} _ _.

Lemma wf_exp_conv_nat_Id : forall Γ M, {{ ⊢ Γ }} -> {{ Γ ⊢ M : ℕ }} -> {{ Γ ⊢ M : ℕ[Id] }}.
Proof.
  intros Γ M Hctx HM.
  pose proof (wf_sub_id Hctx) as HId.
  pose proof (wf_exp_sub_wf_ty HId (wf_nat Hctx)) as Hty.
  eapply wf_exp_typing_conv_sym.
  - exact HM.
  - exact Hty.
  - eapply wf_exp_eq_nat_sub. exact HId.
Qed.
Arguments wf_exp_conv_nat_Id {_ _} _ _.

Lemma wf_sub_Id_V_nat : forall Γ M, {{ ⊢ Γ }} -> {{ Γ ⊢ M : ℕ }} -> {{ Γ ⊢s Id,,M : Γ, ℕ }}.
Proof.
  intros Γ M Hctx HM.
  eapply wf_sub_extend.
  - eapply wf_sub_id. exact Hctx.
  - eapply wf_nat. exact Hctx.
  - eapply wf_exp_conv_nat_Id; assumption.
Qed.



Lemma wf_sub_Id_V_term : forall Γ A M i, {{ ⊢ Γ }} -> {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ M : A }} -> {{ Γ ⊢s Id,,M : Γ, A }}.
Proof.
  intros Γ A M i Hctx HA HM.
  pose proof (wf_sub_id Hctx) as HId.
  pose proof (wf_exp_sub_wf_ty HId HA) as HAId.  (* Γ ⊢ A[Id] : Type@i *)
  pose proof (@wf_exp_eq_sub_id Γ (a_typ i) A HA) as Heq. (* Γ ⊢ A[Id] ≈ A : Type@i *)
  assert (HM' : {{ Γ ⊢ M : A[Id] }}).
  { eapply wf_exp_typing_conv_sym; [exact HM|exact HAId|exact Heq]. }
  eapply wf_sub_extend.
  - exact HId.
  - exact HA.
  - exact HM'.
Qed.
Arguments wf_sub_Id_V_term {_ _ _ _} _ _ _.


(* Equality of substituted types at the same universe *)
Lemma wf_exp_eq_ty_sub_cong : forall Γ Δ A σ σ' i,
  {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ A : Type@i }} -> {{ Γ ⊢s σ ≈ σ' : Δ }} ->
  {{ Γ ⊢ A[σ] ≈ A[σ'] : Type@i }}.
Proof.
  intros Γ Δ A σ σ' i Hσ HA Hseq.
  pose proof (wf_exp_eq_sub_cong (wf_exp_eq_refl HA) Hseq) as Heq.
  (* Heq : Γ ⊢ A[σ] ≈ A[σ'] : (Type@i)[σ] *)
  eapply wf_exp_eq_conv_type with (A := a_sub (a_typ i) σ).
  - exact Heq.
  - eapply wf_typ. eapply wf_sub_wf_ctx_l in Hσ. exact Hσ.
  - eapply wf_exp_eq_typ_sub. exact Hσ.
Qed.
Arguments wf_exp_eq_ty_sub_cong {_ _ _ _ _ _} _ _ _.

(* Substitution composition as an equality of types at their universe *)
Lemma wf_exp_eq_sub_compose_ty : forall Γ Γ' Γ'' A σ τ i,
  {{ Γ ⊢s τ : Γ' }} -> {{ Γ' ⊢s σ : Γ'' }} -> {{ Γ'' ⊢ A : Type@i }} ->
  {{ Γ ⊢ (A[σ])[τ] ≈ A[σ∘τ] : Type@i }}.
Proof.
  intros Γ Γ' Γ'' A σ τ i Hτ Hσ HA.
  pose proof (wf_exp_eq_sub_compose Hτ Hσ HA) as Heq.
  (* Heq : Γ ⊢ A[σ∘τ] ≈ A[σ][τ] : (Type@i)[σ∘τ] *)
  eapply wf_exp_eq_conv_type with (A := a_sub (a_typ i) (a_compose σ τ)).
  - eapply wf_exp_eq_sym. exact Heq.
  - eapply wf_typ. eapply wf_sub_wf_ctx_l in Hτ. exact Hτ.
  - eapply wf_exp_eq_typ_sub. eapply wf_sub_compose; eassumption.
Qed.
Arguments wf_exp_eq_sub_compose_ty {_ _ _ _ _ _ _} _ _ _.

(* Auxiliary facts for the eqrec type-well-formedness case *)
Lemma wf_ctx_extend2 : forall Γ A B, {{ ⊢ Γ }} -> {{ Γ ⊢ A : Type@0 }} -> {{ Γ ⊢ B : Type@0 }} -> {{ ⊢ Γ, A }}.
Proof. intros. eapply wf_ctx_extend; eassumption. Qed.

Lemma wf_weaken_sub : forall Γ A, {{ ⊢ Γ, A }} -> {{ Γ, A ⊢s Wk : Γ }}.
Proof. intros. eapply wf_sub_weaken. assumption. Qed.

Arguments wf_ctx_sub_wf_l {_ _} _.
Arguments wf_ctx_sub_wf_r {_ _} _.
Arguments wf_sub_wf_ctx_l {_ _ _} _.
Arguments wf_sub_wf_ctx_r {_ _ _} _.
Arguments wf_exp_wf_ctx {_ _ _} _.
Arguments wf_exp_typing_conv {_ _ _ _ _} _ _ _.
Arguments wf_exp_typing_conv_sym {_ _ _ _ _} _ _ _.
Arguments wf_exp_eq_conv_type {_ _ _ _ _ _} _ _ _.
Arguments wf_exp_eq_conv_type_sym {_ _ _ _ _ _} _ _ _.
Arguments wf_exp_typing_le {_ _ _ _} _ _.
Arguments wf_exp_weaken_ty {_ _ _ _} _ _.
Arguments wf_ctx_lookup_ty {_ _ _} _ _.
Arguments wf_ctx_extend2 {_ _ _} _ _ _.
Arguments wf_weaken_sub {_ _} _.


Lemma wf_sub_compose_assoc2 : forall Γ1 Γ2 Γ3 Γ4 (τ : sub) (σ : sub) (υ : sub),
  {{ Γ1 ⊢s τ : Γ2 }} -> {{ Γ2 ⊢s σ : Γ3 }} -> {{ Γ3 ⊢s υ : Γ4 }} ->
  {{ Γ1 ⊢s (υ∘σ)∘τ ≈ υ∘(σ∘τ) : Γ4 }}.
Proof.
  intros. eapply wf_sub_eq_compose_assoc; eassumption.
Qed.
Arguments wf_sub_compose_assoc2 {_ _ _ _ _ _ _} _ _ _.

Lemma wf_exp_ty_eqrec_aux : forall Γ A M1 M2 N i j B,
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M1 : A }} ->
  {{ Γ ⊢ M2 : A }} ->
  {{ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ⊢ B : Type@j }} ->
  {{ Γ ⊢ N : Eq A M1 M2 }} ->
  exists k, {{ Γ ⊢ B[Id,,M1,,M2,,N] : Type@k }}.
Proof.
  intros Γ A M1 M2 N i j B hA hM1 hM2 hB hN.
  pose proof (wf_exp_wf_ctx hA) as Hctx.
  pose proof (wf_ctx_extend Hctx hA) as HΓA.
  pose proof (wf_exp_sub_wf_ty (Γ:=Γ) (Δ:=Γ) (σ:=a_id) (A:=A) (i:=i) (wf_sub_id Hctx) hA) as hAId.
  pose proof (wf_exp_eq_sub_id (Γ:=Γ) (A:=a_typ i) (M:=A) hA) as eqAId.
  assert (hM1' : {{ Γ ⊢ M1 : A[Id] }}).
  { eapply wf_exp_typing_conv_sym; [exact hM1|exact hAId|exact eqAId]. }
  pose proof (wf_sub_Id_V_term (Γ:=Γ) (A:=A) (M:=M1) (i:=i) Hctx hA hM1) as ds1.
  pose proof (wf_exp_weaken_ty (B:=A) (A:=A) (i:=i) HΓA hA) as hAw.
  pose proof (wf_exp_eq_sub_compose_ty (Γ:=Γ) (Γ':=(cons A Γ)) (Γ'':=Γ) (A:=A)
                (σ:=a_weaken) (τ:=a_extend a_id M1) (i:=i) ds1 (wf_sub_weaken HΓA) hA) as eq1.
  pose proof (@wf_sub_compose Γ (cons A Γ) (a_extend a_id M1) Γ a_weaken
                ds1 (wf_sub_weaken HΓA)) as dsWk1.
  pose proof (@wf_sub_eq_p_extend Γ Γ a_id i A M1 (wf_sub_id Hctx) hA hM1') as eqWk1.
  pose proof (wf_exp_eq_ty_sub_cong (Γ:=Γ) (Δ:=Γ) (A:=A)
                (σ:=a_compose a_weaken (a_extend a_id M1)) (σ':=a_id) (i:=i)
                dsWk1 hA eqWk1) as eq2.
  pose proof (wf_exp_eq_trans (Γ:=Γ) (A:=a_typ i)
                (M:=(a_sub (a_sub A a_weaken) (a_extend a_id M1)))
                (M':=a_sub A (a_compose a_weaken (a_extend a_id M1)))
                (M'':=a_sub A a_id) eq1 eq2) as eq12.
  pose proof (wf_exp_eq_trans (Γ:=Γ) (A:=a_typ i)
                (M:=(a_sub (a_sub A a_weaken) (a_extend a_id M1)))
                (M':=a_sub A a_id) (M'':=A) eq12 eqAId) as eqM2.
  pose proof (wf_exp_sub_wf_ty (Γ:=Γ) (Δ:=(cons A Γ)) (σ:=a_extend a_id M1) (A:=a_sub A a_weaken) (i:=i) ds1 hAw) as hTyM2.
  assert (hM2' : {{ Γ ⊢ M2 : (A[Wk])[Id,,M1] }}).
  { eapply wf_exp_typing_conv_sym; [exact hM2|exact hTyM2|exact eqM2]. }
  pose proof (wf_sub_extend (Γ:=Γ) (Δ:=(cons A Γ)) (σ:=a_extend a_id M1) (A:=a_sub A a_weaken) (M:=M2) (i:=i) ds1 hAw hM2') as ds2.
  (* === the Eq entry === *)
  pose proof (wf_ctx_extend HΓA hAw) as HΔ3.
  pose proof (@wf_sub_compose (cons (a_sub A a_weaken) (cons A Γ)) (cons A Γ) a_weaken Γ a_weaken
                (wf_sub_weaken HΔ3) (wf_sub_weaken HΓA)) as dsWkWk.
  pose proof (wf_exp_sub_wf_ty (Γ:=(cons (a_sub A a_weaken) (cons A Γ))) (Δ:=Γ)
                (σ:=a_compose a_weaken a_weaken) (A:=A) (i:=i) dsWkWk hA) as hAw2.
  (* lookups *)
  pose proof (@here A Γ) as lkhere.
  pose proof (@there 0 (a_sub A a_weaken) (cons A Γ) (a_sub A a_weaken) lkhere) as lk1.
  pose proof (@here (a_sub A a_weaken) (cons A Γ)) as lk0.
  pose proof (wf_vlookup (Γ:=(cons (a_sub A a_weaken) (cons A Γ))) (x:=1) (A:=(a_sub (a_sub A a_weaken) a_weaken)) HΔ3 lk1) as h1raw.
  pose proof (wf_vlookup (Γ:=(cons (a_sub A a_weaken) (cons A Γ))) (x:=0) (A:=(a_sub (a_sub A a_weaken) a_weaken)) HΔ3 lk0) as h0raw.
  (* equality of lookup types with A[Wk∘Wk] *)
  pose proof (wf_exp_eq_sub_compose_ty (Γ:=(cons (a_sub A a_weaken) (cons A Γ))) (Γ':=(cons A Γ)) (Γ'':=Γ)
                (A:=A) (σ:=a_weaken) (τ:=a_weaken) (i:=i) (wf_sub_weaken HΔ3) (wf_sub_weaken HΓA) hA) as eqWkWk1.
  assert (h1 : {{ Γ, A, A[Wk] ⊢ #1 : A[Wk∘Wk] }}).
  { eapply wf_exp_typing_conv; [exact h1raw|exact hAw2|exact eqWkWk1]. }
  assert (h0 : {{ Γ, A, A[Wk] ⊢ #0 : A[Wk∘Wk] }}).
  { eapply wf_exp_typing_conv; [exact h0raw|exact hAw2|exact eqWkWk1]. }
  pose proof (wf_eq (Γ:=(cons (a_sub A a_weaken) (cons A Γ))) (i:=i)
                (A:=a_sub A (a_compose a_weaken a_weaken)) (M:=a_var 1) (N:=a_var 0)
                hAw2 h1 h0) as hE.
  (* === substitution equality (Wk o Wk) o ds2 = Id === *)
  pose proof (@wf_sub_compose_assoc2 Γ (cons (a_sub A a_weaken) (cons A Γ)) (cons A Γ) Γ
                (a_extend (a_extend a_id M1) M2) a_weaken a_weaken
                ds2 (wf_sub_weaken HΔ3) (wf_sub_weaken HΓA)) as assoc1.
  pose proof (@wf_sub_eq_p_extend Γ (cons A Γ) (a_extend a_id M1) i (a_sub A a_weaken) M2
                ds1 hAw hM2') as eqWkds2.
  pose proof (@wf_sub_eq_weaken A Γ HΓA) as eqWkWkA.
  pose proof (@wf_sub_eq_compose_cong Γ (cons A Γ)
                (a_compose a_weaken (a_extend (a_extend a_id M1) M2)) (a_extend a_id M1)
                Γ a_weaken a_weaken eqWkds2 eqWkWkA) as cong2.
  pose proof (@wf_sub_eq_trans Γ Γ
                (a_compose (a_compose a_weaken a_weaken) (a_extend (a_extend a_id M1) M2))
                (a_compose a_weaken (a_compose a_weaken (a_extend (a_extend a_id M1) M2)))
                (a_compose a_weaken (a_extend a_id M1)) assoc1 cong2) as step1.
  pose proof (@wf_sub_eq_trans Γ Γ
                (a_compose (a_compose a_weaken a_weaken) (a_extend (a_extend a_id M1) M2))
                (a_compose a_weaken (a_extend a_id M1)) a_id step1 eqWk1) as eqAssoc.
  (* === type equality A0[ds2] = A === *)
  pose proof (wf_exp_eq_sub_compose_ty (Γ:=Γ) (Γ':=(cons (a_sub A a_weaken) (cons A Γ))) (Γ'':=Γ)
                (A:=A) (σ:=a_compose a_weaken a_weaken) (τ:=a_extend (a_extend a_id M1) M2) (i:=i)
                ds2 dsWkWk hA) as eqA0a.
  pose proof (@wf_sub_compose Γ (cons (a_sub A a_weaken) (cons A Γ)) (a_extend (a_extend a_id M1) M2) Γ (a_compose a_weaken a_weaken) ds2 dsWkWk) as dsComp.
  pose proof (wf_exp_eq_ty_sub_cong (Γ:=Γ) (Δ:=Γ) (A:=A)
                (σ:=a_compose (a_compose a_weaken a_weaken) (a_extend (a_extend a_id M1) M2))
                (σ':=a_id) (i:=i) dsComp hA eqAssoc) as eqAIdSub.
  pose proof (wf_exp_eq_trans (Γ:=Γ) (A:=a_typ i)
                (M:=a_sub (a_sub A (a_compose a_weaken a_weaken)) (a_extend (a_extend a_id M1) M2))
                (M':=a_sub A (a_compose (a_compose a_weaken a_weaken) (a_extend (a_extend a_id M1) M2)))
                (M'':=a_sub A a_id) eqA0a eqAIdSub) as eqA0ab.
  pose proof (wf_exp_eq_trans (Γ:=Γ) (A:=a_typ i)
                (M:=a_sub (a_sub A (a_compose a_weaken a_weaken)) (a_extend (a_extend a_id M1) M2))
                (M':=a_sub A a_id) (M'':=A) eqA0ab eqAId) as eqA0.
  (* === term equalities === *)
  pose proof (@wf_exp_eq_var_0_sub Γ (cons A Γ) (a_extend a_id M1) i (a_sub A a_weaken) M2
                ds1 hAw hM2') as e0raw.
  pose proof (wf_exp_eq_conv_type (Γ:=Γ) (A:=a_sub (a_sub A a_weaken) (a_extend a_id M1))
                (A':=A) (M:=a_sub (a_var 0) (a_extend (a_extend a_id M1) M2)) (M':=M2) (i:=i)
                e0raw hA eqM2) as e0.
  pose proof (@wf_exp_eq_var_0_sub Γ Γ a_id i A M1 (wf_sub_id Hctx) hA hM1') as eq0M1.
  pose proof (wf_exp_eq_conv_type_sym (Γ:=Γ) (A:=a_sub A a_id)
                (A':=a_sub (a_sub A a_weaken) (a_extend a_id M1))
                (M:=a_sub (a_var 0) (a_extend a_id M1)) (M':=M1) (i:=i) eq0M1 hTyM2 eq12) as eq0M1'.
  pose proof (@wf_exp_eq_var_S_sub Γ (cons A Γ) (a_extend a_id M1) i (a_sub A a_weaken) M2 0 (a_sub A a_weaken)
                ds1 hAw hM2' lkhere) as e1raw.
  pose proof (wf_exp_eq_trans (Γ:=Γ) (A:=a_sub (a_sub A a_weaken) (a_extend a_id M1))
                (M:=a_sub (a_var 1) (a_extend (a_extend a_id M1) M2))
                (M':=a_sub (a_var 0) (a_extend a_id M1)) (M'':=M1) e1raw eq0M1') as e1mid.
  pose proof (wf_exp_eq_conv_type (Γ:=Γ) (A:=a_sub (a_sub A a_weaken) (a_extend a_id M1))
                (A':=A) (M:=a_sub (a_var 1) (a_extend (a_extend a_id M1) M2)) (M':=M1) (i:=i)
                e1mid hA eqM2) as e1.
  pose proof (wf_exp_eq_eq_cong (Γ:=Γ) (i:=i) (A:=A)
                (A':=a_sub (a_sub A (a_compose a_weaken a_weaken)) (a_extend (a_extend a_id M1) M2))
                (M:=M1) (M':=a_sub (a_var 1) (a_extend (a_extend a_id M1) M2))
                (N:=M2) (N':=a_sub (a_var 0) (a_extend (a_extend a_id M1) M2))
                (wf_exp_eq_sym eqA0) (wf_exp_eq_sym e1) (wf_exp_eq_sym e0)) as eqEq_rev.
  pose proof (wf_exp_eq_sym eqEq_rev) as eqEq.
  pose proof (@wf_exp_eq_eq_sub Γ (cons (a_sub A a_weaken) (cons A Γ))
                (a_extend (a_extend a_id M1) M2) i
                (a_sub A (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0)
                ds2 hAw2 h1 h0) as eq_sub.
  pose proof (wf_exp_eq_trans (Γ:=Γ) (A:=a_typ i)
                (M:=a_sub (a_eq (a_sub A (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0)) (a_extend (a_extend a_id M1) M2))
                (M':=a_eq (a_sub (a_sub A (a_compose a_weaken a_weaken)) (a_extend (a_extend a_id M1) M2))
                          (a_sub (a_var 1) (a_extend (a_extend a_id M1) M2))
                          (a_sub (a_var 0) (a_extend (a_extend a_id M1) M2)))
                (M'':=a_eq A M1 M2) eq_sub eqEq) as eqE.
  pose proof (wf_exp_sub_wf_ty (Γ:=Γ) (Δ:=(cons (a_sub A a_weaken) (cons A Γ)))
                (σ:=a_extend (a_extend a_id M1) M2) (A:=a_eq (a_sub A (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0)) (i:=i)
                ds2 hE) as hEsub.
  assert (hN' : wf_exp Γ
            (a_sub (a_eq (a_sub A (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0))
                   (a_extend (a_extend a_id M1) M2)) N).
  { eapply wf_exp_typing_conv_sym; [exact hN|exact hEsub|exact eqE]. }
  pose proof (@wf_sub_extend Γ (cons (a_sub A a_weaken) (cons A Γ)) (a_extend (a_extend a_id M1) M2) i
                (a_eq (a_sub A (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0)) N ds2 hE hN') as ds3.
  exists j.
  refine (@wf_exp_sub_wf_ty Γ
            (cons (a_eq (a_sub A (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0))
                  (cons (a_sub A a_weaken) (cons A Γ)))
            (a_extend (a_extend (a_extend a_id M1) M2) N) B j ds3 hB).
Qed.
Arguments wf_exp_ty_eqrec_aux {_ _ _ _ _ _ _ _} _ _ _ _ _.

Lemma wf_exp_ty_wf : forall Γ A M, {{ Γ ⊢ M : A }} -> exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
  intros Γ A M H. induction H; try (eauto 6 using wf_typ, wf_nat, wf_pi, wf_sigma, wf_ctx_lookup_ty, wf_exp_sub_wf_ty; fail).
  - (* natrec *) eexists. eapply wf_exp_sub_wf_ty.
    + eapply wf_sub_Id_V_nat; [eapply wf_exp_wf_ctx; eassumption|eassumption].
    + eassumption.
  - (* fn *) destruct IHwf_exp2 as [j HB].
    exists (Nat.max i j). eapply wf_pi.
    + eapply wf_exp_typing_le; [eassumption|apply Nat.le_max_l].
    + eapply wf_exp_typing_le; [exact HB|apply Nat.le_max_r].
  - (* app *) eexists. eapply wf_exp_sub_wf_ty.
    + eapply wf_sub_Id_V_term.
      * eapply wf_exp_wf_ctx; eassumption.
      * eassumption.
      * eassumption.
    + eassumption.
  - (* snd *) eexists. eapply wf_exp_sub_wf_ty.
    + eapply wf_sub_Id_V_term.
      * eapply wf_exp_wf_ctx; eassumption.
      * eassumption.
      * eapply wf_fst; eassumption.
    + eassumption.
  - (* refl *) eexists. eapply wf_eq; eassumption.
  - (* eqrec *) eapply wf_exp_ty_eqrec_aux; eassumption.
  - (* sub *) destruct IHwf_exp as [k HA]. exists k. eapply wf_exp_sub_wf_ty; [eassumption|exact HA].
Qed.


(* Evaluation inversion lemmas *)
Lemma eval_fn_inv : forall A M ρ m, eval_exp (a_fn A M) ρ m -> m = d_fn ρ M.
Proof. intros. inversion H. reflexivity. Qed.
Lemma eval_nat_inv : forall ρ m, eval_exp a_nat ρ m -> m = d_nat.
Proof. intros. inversion H. reflexivity. Qed.
Lemma eval_typ_inv : forall i ρ m, eval_exp (a_typ i) ρ m -> m = d_univ i.
Proof. intros. inversion H. reflexivity. Qed.
Lemma eval_zero_inv : forall ρ m, eval_exp a_zero ρ m -> m = d_zero.
Proof. intros. inversion H. reflexivity. Qed.
Lemma eval_var_inv : forall x ρ m, eval_exp (a_var x) ρ m -> m = ρ x.
Proof. intros. inversion H. reflexivity. Qed.
Lemma eval_succ_inv : forall M ρ m, eval_exp (a_succ M) ρ m -> exists m', m = d_succ m' /\ eval_exp M ρ m'.
Proof. intros. inversion H. subst. eexists _; split; try reflexivity; eassumption. Qed.
Lemma eval_pair_inv : forall M A N B ρ m, eval_exp (a_pair M A N B) ρ m -> exists a b, m = d_pair a b /\ eval_exp M ρ a /\ eval_exp N ρ b.
Proof. intros. inversion H. subst. eexists _, _; repeat split; try reflexivity; eassumption. Qed.
Lemma eval_pi_inv : forall A B ρ m, eval_exp (a_pi A B) ρ m -> exists a, m = d_pi a ρ B /\ eval_exp A ρ a.
Proof. intros. inversion H. subst. eexists _; split; try reflexivity; eassumption. Qed.
Lemma eval_sigma_inv : forall A B ρ m, eval_exp (a_sigma A B) ρ m -> exists a, m = d_sigma a ρ B /\ eval_exp A ρ a.
Proof. intros. inversion H. subst. eexists _; split; try reflexivity; eassumption. Qed.
Lemma eval_refl_inv : forall A M ρ m, eval_exp (a_refl A M) ρ m -> exists m1, m = d_refl m1 /\ eval_exp M ρ m1.
Proof. intros. inversion H. subst. eexists _; split; try reflexivity; eassumption. Qed.
Lemma eval_sub_inv : forall M σ ρ m, eval_exp (a_sub M σ) ρ m -> exists ρ', eval_sub σ ρ ρ' /\ eval_exp M ρ' m.
Proof. intros. inversion H. subst. eexists _; split; eassumption. Qed.
Arguments eval_fn_inv {_ _ _ _} _.
Arguments eval_nat_inv {_ _} _.
Arguments eval_typ_inv {_ _ _} _.
Arguments eval_zero_inv {_ _} _.
Arguments eval_var_inv {_ _ _} _.
Arguments eval_succ_inv {_ _ _} _.
Arguments eval_pair_inv {_ _ _ _ _ _} _.
Arguments eval_pi_inv {_ _ _ _} _.
Arguments eval_sigma_inv {_ _ _ _} _.
Arguments eval_refl_inv {_ _ _ _} _.
Arguments eval_sub_inv {_ _ _ _} _.


(* Realizability of a term at a syntactic type, relative to a world context Γ
   with environment ρ, and a substitution σ from Γ into the term's context Δ
   evaluated as ρσ. *)
Fixpoint Real (Γ : ctx) (ρ : env) (Δ : ctx) (A : typ) (σ : sub) (ρσ : env) (M : exp) (m : domain) {struct A} : Prop :=
  (exists (a : domain) (W : nf),
      eval_exp A ρσ a /\
      eval_exp M ρσ m /\
      read_nf (length Γ) (d_dom a m) W /\
      wf_exp_eq Γ (a_sub A σ) (a_sub M σ) W)
  /\
  match A with
  | a_pi A0 B =>
      forall (N : exp) (n : domain),
        wf_exp Δ A0 N ->
        Real Γ ρ Δ A0 σ ρσ N n ->
        exists (a0 r : domain),
          eval_exp A0 ρσ a0 /\
          eval_app m n r /\
          Real Γ ρ (cons A0 Δ) B (a_compose (a_extend a_id N) σ) (extend_env ρσ n)
               (a_app (a_sub M a_weaken) (a_var 0)) r
  | a_sigma A0 B =>
      (exists r1, eval_fst m r1 /\ Real Γ ρ Δ A0 σ ρσ (a_fst M) r1 /\
         (exists r2, eval_snd m r2 /\
            Real Γ ρ (cons A0 Δ) B (a_compose (a_extend a_id (a_fst M)) σ)
                 (extend_env ρσ r1) (a_snd (a_sub M a_weaken)) r2))
  | _ => True
  end.

Definition SubReal (Γ : ctx) (ρ : env) (Δ : ctx) (σ : sub) (ρσ : env) : Prop :=
  forall (x : nat) (A : typ), ctx_lookup x A Δ ->
    Real Γ ρ Δ A σ ρσ (a_var x) (ρσ x).

Definition RealEnv (Γ : ctx) (ρ : env) : Prop :=
  forall (x : nat) (A : typ), ctx_lookup x A Γ ->
    Real Γ ρ Γ A a_id ρ (a_var x) (ρ x).

Arguments Real {_ _ _ _ _ _ _} _.
Arguments SubReal {_ _ _ _} _.
Arguments RealEnv {_ _}.

Lemma Real_typ : forall Γ ρ Δ σ ρσ i,
  wf_sub Γ Δ σ -> eval_sub σ ρ ρσ ->
  @Real Γ ρ Δ (a_typ (S i)) σ ρσ (a_typ i) (d_univ i).
Proof.
  intros Γ ρ Δ σ ρσ i Hσ Hσe.
  simpl. split.
  - exists (d_univ (S i)), (nf_typ i). repeat split.
    + eapply eval_exp_typ.
    + eapply eval_exp_typ.
    + eapply read_nf_type. eapply read_typ_univ.
    + (* equality *)
      refine (@wf_exp_eq_conv_type Γ (a_typ (S i)) (a_sub (a_typ (S i)) σ)
                (a_sub (a_typ i) σ) (a_typ i) (S (S i)) _ _ _).
      * eapply wf_exp_eq_typ_sub. exact Hσ.
      * eapply wf_exp_sub_wf_ty.
        -- exact Hσ.
        -- eapply wf_typ. pose proof (wf_sub_wf_ctx_r Hσ) as HΔ. exact HΔ.
      * eapply wf_exp_eq_sym. eapply wf_exp_eq_typ_sub. exact Hσ.
  - exact I.
Qed.

Lemma Real_nat : forall Γ ρ Δ σ ρσ,
  wf_sub Γ Δ σ -> eval_sub σ ρ ρσ ->
  @Real Γ ρ Δ (a_typ 0) σ ρσ a_nat d_nat.
Proof.
  intros Γ ρ Δ σ ρσ Hσ Hσe. simpl. split.
  - exists (d_univ 0), nf_nat. repeat split.
    + eapply eval_exp_typ.
    + eapply eval_exp_nat.
    + eapply read_nf_type. eapply read_typ_nat.
    + refine (@wf_exp_eq_conv_type_sym Γ (a_typ 0) (a_sub (a_typ 0) σ) (a_sub a_nat σ) a_nat (S 0) _ _ _).
      * eapply wf_exp_eq_nat_sub. exact Hσ.
      * eapply wf_exp_sub_wf_ty; [exact Hσ|eapply wf_typ; pose proof (wf_sub_wf_ctx_r Hσ) as HΔ; exact HΔ].
      * eapply wf_exp_eq_typ_sub. exact Hσ.
  - exact I.
Qed.

Lemma typing_nat_sub : forall Γ Δ σ, wf_sub Γ Δ σ -> wf_exp Γ (a_typ 0) (a_sub a_nat σ).
Proof.
  intros. eapply wf_exp_sub_wf_ty.
  - exact H.
  - eapply wf_nat. pose proof (wf_sub_wf_ctx_r H) as HΔ. exact HΔ.
Qed.
Arguments typing_nat_sub {_ _ _} _.

Lemma conv_nat_eq : forall Γ Δ σ M M',
  wf_sub Γ Δ σ -> wf_exp_eq Γ a_nat M M' -> wf_exp_eq Γ (a_sub a_nat σ) M M'.
Proof.
  intros. refine (@wf_exp_eq_conv_type_sym Γ a_nat (a_sub a_nat σ) M M' 0 _ _ _).
  - exact H0.
  - eapply typing_nat_sub. exact H.
  - eapply wf_exp_eq_nat_sub. exact H.
Qed.
Arguments conv_nat_eq {_ _ _ _ _} _ _.

Lemma conv_nat_eq_inv : forall Γ Δ σ M M',
  wf_sub Γ Δ σ -> wf_exp_eq Γ (a_sub a_nat σ) M M' -> wf_exp_eq Γ a_nat M M'.
Proof.
  intros. refine (@wf_exp_eq_conv_type Γ (a_sub a_nat σ) a_nat M M' 0 _ _ _).
  - exact H0.
  - eapply wf_nat. pose proof (wf_sub_wf_ctx_l H) as HΓ. exact HΓ.
  - eapply wf_exp_eq_nat_sub. exact H.
Qed.
Arguments conv_nat_eq_inv {_ _ _ _ _} _ _.

Lemma Real_zero : forall Γ ρ Δ σ ρσ,
  wf_sub Γ Δ σ -> eval_sub σ ρ ρσ ->
  @Real Γ ρ Δ a_nat σ ρσ a_zero d_zero.
Proof.
  intros Γ ρ Δ σ ρσ Hσ Hσe. simpl. split.
  - exists d_nat, nf_zero. repeat split.
    + eapply eval_exp_nat.
    + eapply eval_exp_zero.
    + eapply read_nf_zero.
    + eapply conv_nat_eq.
      * exact Hσ.
      * eapply wf_exp_eq_zero_sub. exact Hσ.
  - exact I.
Qed.

Lemma Real_succ : forall Γ ρ Δ σ ρσ M m,
  wf_sub Γ Δ σ -> wf_exp Δ a_nat M ->
  @Real Γ ρ Δ a_nat σ ρσ M m ->
  @Real Γ ρ Δ a_nat σ ρσ (a_succ M) (d_succ m).
Proof.
  intros Γ ρ Δ σ ρσ M m Hσ HMty HR. simpl in *. split.
  - destruct HR as [[a [W [Ha [HM [Hread Heq]]]]] _].
    pose proof (eval_nat_inv Ha) as Ha'. subst a.
    exists d_nat, (nf_succ W). repeat split.
    + eapply eval_exp_nat.
    + eapply eval_exp_succ. exact HM.
    + eapply read_nf_succ. exact Hread.
    + (* equality: (succ M)[σ] ≈ succ W : a_nat[σ] *)
      eapply wf_exp_eq_trans.
      * eapply conv_nat_eq.
        -- exact Hσ.
        -- eapply wf_exp_eq_succ_sub; [exact Hσ|exact HMty].
      * eapply conv_nat_eq.
        -- exact Hσ.
        -- eapply wf_exp_eq_succ_cong. eapply conv_nat_eq_inv; [exact Hσ|exact Heq].
  - exact I.
Qed.

(* Realization of a type expression at the universe, from its readback. *)
Lemma Real_ty : forall Γ ρ Δ σ ρσ A i a W,
  wf_sub Γ Δ σ ->
  eval_exp A ρσ a ->
  read_typ (length Γ) a W ->
  wf_exp_eq Γ (a_sub (a_typ i) σ) (a_sub A σ) W ->
  @Real Γ ρ Δ (a_typ i) σ ρσ A a.
Proof.
  intros Γ ρ Δ σ ρσ A i a W Hσ Ha Hrt Heq. simpl. split.
  - exists (d_univ i), W. repeat split.
    + eapply eval_exp_typ.
    + exact Ha.
    + eapply read_nf_type. exact Hrt.
    + exact Heq.
  - exact I.
Qed.
Arguments Real_ty {_ _ _ _ _ _ _ _ _} _ _ _ _.

(* Readback of a single neutral variable at atomic type codes. *)

Lemma read_ne_var_nat : forall s x,
  exists M, {{ Rne !x in s ↘ M }} /\ {{ Rnf ⇓ ℕ (⇑ ℕ !x) in s ↘ ⇑ M }}.
Proof.
  intros. eexists. split.
  - eapply read_ne_var.
  - eapply read_nf_nat_neut. eapply read_ne_var.
Qed.

Lemma read_ne_var_univ : forall s i x,
  exists M, {{ Rne !x in s ↘ M }} /\
            {{ Rnf ⇓ 𝕌@i (⇑ 𝕌@i !x) in s ↘ ⇑ M }}.
Proof.
  intros. eexists. split.
  - eapply read_ne_var.
  - eapply read_nf_type. eapply read_typ_neut. eapply read_ne_var.
Qed.

(* Transport of the conclusion component of Real along substitution
   equality, with the two substitutions evaluating to the same environment. *)

Lemma Real_concl_inv : forall Γ ρ Δ A σ ρσ M m,
  @Real Γ ρ Δ A σ ρσ M m ->
  exists a W, eval_exp A ρσ a /\ eval_exp M ρσ m /\
     read_nf (length Γ) (d_dom a m) W /\
     wf_exp_eq Γ (a_sub A σ) (a_sub M σ) W.
Proof.
  intros Γ ρ Δ A σ ρσ M m HR.
  destruct A; simpl in HR; try (destruct HR as [HC _]);
    destruct HC as [a [W [Ha [Hev [Hread Heq]]]]];
    exists a, W; repeat split; assumption.
Qed.

Lemma Real_concl_sub_eq : forall Γ ρ Δ A σ σ' ρσ M m,
  wf_sub Γ Δ σ -> wf_sub Γ Δ σ' ->
  wf_sub_eq Γ Δ σ σ' ->
  eval_sub σ ρ ρσ -> eval_sub σ' ρ ρσ ->
  wf_exp Δ A M ->
  @Real Γ ρ Δ A σ ρσ M m ->
  exists a W, eval_exp A ρσ a /\ eval_exp M ρσ m /\
     read_nf (length Γ) (d_dom a m) W /\
     wf_exp_eq Γ (a_sub A σ') (a_sub M σ') W.
Proof.
  intros Γ ρ Δ A σ σ' ρσ M m Hσ Hσ' Hseq Hρ Hρ' Hty HR.
  destruct (Real_concl_inv _ _ _ _ _ _ _ _ HR)
    as [a [W [Ha [Hev [Hread Heq]]]]].
  exists a, W; repeat split; try assumption.
  destruct (wf_exp_ty_wf Δ A M Hty) as [i HA].
  pose proof (wf_exp_sub_wf_ty Hσ' HA) as HA'.
  pose proof (wf_exp_eq_ty_sub_cong Hσ HA Hseq) as HeqA.
  pose proof (wf_exp_eq_sub_cong (wf_exp_eq_refl Hty) Hseq) as HeqM.
  pose proof (wf_exp_eq_sym HeqM) as HeqMsym.
  pose proof (wf_exp_eq_trans HeqMsym Heq) as Htrans.
  eapply (@wf_exp_eq_conv_type Γ (a_sub A σ) (a_sub A σ') (a_sub M σ') W i).
  - exact Htrans.
  - exact HA'.
  - exact HeqA.
Qed.

(* Equality of the extended-composed substitutions, and its evaluation. *)

Lemma wf_sub_eq_extend_compose : forall Γ Δ A0 N i σ σ',
  wf_sub Γ Δ σ -> wf_sub Γ Δ σ' -> wf_sub_eq Γ Δ σ σ' ->
  wf_exp Δ (a_typ i) A0 -> wf_exp Δ A0 N ->
  wf_sub_eq Γ (cons A0 Δ)
    (a_compose (a_extend a_id N) σ)
    (a_compose (a_extend a_id N) σ').
Proof.
  intros Γ Δ A0 N i σ σ' Hσ Hσ' Hseq HA0 HN.
  pose proof (wf_sub_wf_ctx_r Hσ) as HΔ.
  pose proof (wf_sub_id HΔ) as Hid.
  pose proof (wf_sub_eq_id HΔ) as Hseqid.
  pose proof (wf_exp_eq_refl HN) as HNrefl.
  pose proof (wf_exp_eq_sub_id HA0) as HA0id.
  pose proof (wf_exp_sub_wf_ty Hid HA0) as HA0idty.
  pose proof (wf_exp_eq_conv_type_sym HNrefl HA0idty HA0id) as HNconv.
  pose proof (wf_sub_eq_extend_cong Hseqid HA0 HNconv) as Hext.
  pose proof (@wf_sub_eq_compose_cong Γ Δ σ σ' (cons A0 Δ)
                (a_extend a_id N) (a_extend a_id N)
                Hseq Hext) as Hcomp.
  exact Hcomp.
Qed.

Lemma eval_sub_extend_compose : forall (Γ Δ : ctx) (A0 N : typ) (σ : sub) (ρ ρσ : env) (n : domain),
  @eval_sub σ ρ ρσ -> eval_exp N ρσ n ->
  @eval_sub (a_compose (a_extend a_id N) σ) ρ (extend_env ρσ n).
Proof.
  intros Γ Δ A0 N σ ρ ρσ n Hσ HN.
  eapply eval_sub_compose.
  - exact Hσ.
  - eapply eval_sub_extend.
    + eapply eval_sub_id.
    + exact HN.
Qed.

(* Initial-environment constructors, used for the context realization. *)
Lemma initial_env_empty : initial_env nil empty_env.
Proof. eapply initial_env_nil. Qed.

Lemma initial_env_cons' : forall Γ ρ A a,
  initial_env Γ ρ -> eval_exp A ρ a ->
  initial_env (cons A Γ) (extend_env ρ (d_neut a (d_var (length Γ)))).
Proof.
  intros. eapply initial_env_cons; eassumption.
Qed.

(* Universe cumulativity preserves realizability. *)

Lemma subtyp_typ_sub_self : forall Γ Δ σ i,
  wf_sub Γ Δ σ -> wf_subtyp Γ (a_sub (a_typ i) σ) (a_typ i).
Proof.
  intros Γ Δ σ i Hσ.
  pose proof (wf_sub_wf_ctx_l Hσ) as HΓ.
  pose proof (@wf_typ Γ i HΓ) as HtyA.
  pose proof (@wf_exp_eq_typ_sub Γ Δ σ i Hσ) as Heq.
  refine (@wf_subtyp_refl Γ (S i) (a_typ i) (a_sub (a_typ i) σ) HtyA Heq).
Qed.

Lemma subtyp_typ_self_sub : forall Γ Δ σ j,
  wf_sub Γ Δ σ -> wf_subtyp Γ (a_typ j) (a_sub (a_typ j) σ).
Proof.
  intros Γ Δ σ j Hσ.
  pose proof (wf_sub_wf_ctx_l Hσ) as HΓ.
  pose proof (wf_sub_wf_ctx_r Hσ) as HΔ.
  pose proof (@wf_typ Γ j HΓ) as HtyA.
  pose proof (@wf_exp_sub Γ Δ σ (a_typ (S j)) (a_typ j) Hσ (@wf_typ Δ j HΔ)) as HtyAsub.
  pose proof (@wf_exp_eq_typ_sub Γ Δ σ j Hσ) as Heq. (* Γ ⊢ (a_typ j)[σ] ≈ a_typ j : Type@(S j) *)
  pose proof (@wf_typ Γ (S j) HΓ) as HtySj.
  refine (@wf_subtyp_refl Γ (S j) (a_sub (a_typ j) σ) (a_typ j) _ _).
  - refine (@wf_exp_typing_conv Γ (a_sub (a_typ (S j)) σ) (a_typ (S j))
              (a_sub (a_typ j) σ) (S (S j)) HtyAsub HtySj
              (@wf_exp_eq_typ_sub Γ Δ σ (S j) Hσ)).
  - eapply wf_exp_eq_sym. exact Heq.
Qed.

Lemma subtyp_typ_sub_le : forall Γ Δ σ i j,
  wf_sub Γ Δ σ -> i <= j ->
  wf_subtyp Γ (a_sub (a_typ i) σ) (a_sub (a_typ j) σ).
Proof.
  intros Γ Δ σ i j Hσ Hij.
  assert (Hcases : i < j \/ i = j) by lia.
  destruct Hcases as [Hlt|Heq].
  - (* i < j *)
    refine (@wf_subtyp_trans Γ (a_sub (a_typ i) σ) (a_typ i)
              (a_sub (a_typ j) σ) _ _).
    + eapply subtyp_typ_sub_self. exact Hσ.
    + refine (@wf_subtyp_trans Γ (a_typ i) (a_typ j)
                (a_sub (a_typ j) σ) _ _).
      * refine (@wf_subtyp_univ Γ i j _ _).
        -- eapply wf_sub_wf_ctx_l. exact Hσ.
        -- exact Hlt.
      * eapply subtyp_typ_self_sub. exact Hσ.
  - subst j.
    pose proof (wf_sub_wf_ctx_l Hσ) as HΓ.
    pose proof (wf_sub_wf_ctx_r Hσ) as HΔ.
    pose proof (@wf_typ Δ i HΔ) as HtyAi.
    pose proof (@wf_exp_sub Γ Δ σ (a_typ (S i)) (a_typ i) Hσ HtyAi) as HtyAsub.
    pose proof (@wf_typ Γ (S i) HΓ) as HtySi.
    pose proof (wf_exp_typing_conv (A:=a_sub (a_typ (S i)) σ) (A':=a_typ (S i))
                  (M:=a_sub (a_typ i) σ) (i:=S (S i)) HtyAsub HtySi
                  (@wf_exp_eq_typ_sub Γ Δ σ (S i) Hσ)) as Htyconv.
    pose proof (wf_exp_eq_refl Htyconv) as Heq.
    refine (@wf_subtyp_refl Γ (S i) (a_sub (a_typ i) σ) (a_sub (a_typ i) σ) Htyconv Heq).
Qed.

Lemma read_nf_univ_inv : forall s m W i,
  read_nf s (d_dom (d_univ i) m) W -> read_typ s m W.
Proof.
  intros s m W i H. inversion H. assumption.
Qed.

Lemma Real_typ_le : forall Γ ρ Δ σ ρσ M m i j,
  wf_sub Γ Δ σ -> i <= j ->
  @Real Γ ρ Δ (a_typ i) σ ρσ M m ->
  @Real Γ ρ Δ (a_typ j) σ ρσ M m.
Proof.
  intros Γ ρ Δ σ ρσ M m i j Hσ Hij HR.
  pose proof (wf_sub_wf_ctx_l Hσ) as HΓ.
  pose proof (wf_sub_wf_ctx_r Hσ) as HΔ.
  simpl in HR. destruct HR as [[a [W [Ha [Hev [Hread Heq]]]]] _].
  pose proof (eval_typ_inv Ha) as Ea. subst a.
  pose proof (read_nf_univ_inv (length Γ) m W i Hread) as Hrtyp.
  simpl. split.
  - exists (d_univ j), W. repeat split.
    + eapply eval_exp_typ.
    + exact Hev.
    + eapply read_nf_type. exact Hrtyp.
    + pose proof (@wf_typ Δ j HΔ) as HtyAj.
      pose proof (@wf_exp_sub Γ Δ σ (a_typ (S j)) (a_typ j) Hσ HtyAj) as HtyAjsub.
      pose proof (@wf_typ Γ (S j) HΓ) as HtySj.
      pose proof (wf_exp_typing_conv (A:=a_sub (a_typ (S j)) σ) (A':=a_typ (S j))
                    (M:=a_sub (a_typ j) σ) (i:=S (S j)) HtyAjsub HtySj
                    (@wf_exp_eq_typ_sub Γ Δ σ (S j) Hσ)) as Htyconv.
      eapply wf_exp_eq_subtyp.
      * exact Heq.
      * exact Htyconv.
      * eapply subtyp_typ_sub_le. exact Hσ. exact Hij.
  - exact I.
Qed.

(* Substitution instance: a realizer at A0 under (tau o sigma) yields one
   at A0[tau] under sigma for the substituted term. *)
Lemma Real_sub_compose : forall Γ ρ Δ Δ0 A0 τ σ ρσ ρτσ M0 m i,
  wf_sub Γ Δ σ -> wf_sub Δ Δ0 τ ->
  eval_sub σ ρ ρσ -> eval_sub τ ρσ ρτσ ->
  wf_exp Δ0 (a_typ i) A0 -> wf_exp Δ0 A0 M0 ->
  @Real Γ ρ Δ0 A0 (a_compose τ σ) ρτσ M0 m ->
  @Real Γ ρ Δ (a_sub A0 τ) σ ρσ (a_sub M0 τ) m.
Proof.
  intros Γ ρ Δ Δ0 A0 τ σ ρσ ρτσ M0 m i Hσ Hτ Hσe Hτe HA0 HM0 HR.
  pose proof (Real_concl_inv _ _ _ _ _ _ _ _ HR) as HC.
  destruct HC as [a [W [Ha [HM [Hread Heq]]]]].
  pose proof (wf_sub_wf_ctx_l Hσ) as HΓ.
  pose proof (@wf_sub_compose Γ Δ σ Δ0 τ Hσ Hτ) as Hcomp.
  simpl. split.
  - exists a, W. repeat split.
    + eapply eval_exp_sub; eassumption.
    + eapply eval_exp_sub; eassumption.
    + exact Hread.
    + (* type & term composition equalities *)
      pose proof (@wf_exp_eq_sub_compose Γ Δ σ Δ0 τ (a_typ i) A0 Hσ Hτ HA0) as eqAraw.
      pose proof (@wf_typ Γ i HΓ) as HtyUi.
      pose proof (@wf_exp_eq_typ_sub Γ Δ0 (a_compose τ σ) i Hcomp) as HtyUs.
      pose proof (@wf_exp_eq_conv_type Γ (a_sub (a_typ i) (a_compose τ σ)) (a_typ i)
                    (a_sub A0 (a_compose τ σ)) (a_sub (a_sub A0 τ) σ) (S i)
                    eqAraw HtyUi HtyUs) as eqA.
      pose proof (@wf_exp_sub_wf_ty Δ Δ0 τ A0 i Hτ HA0) as HtyAtau.
      pose proof (@wf_exp_sub_wf_ty Γ Δ σ (a_sub A0 τ) i Hσ HtyAtau) as HtyA'.
      pose proof (@wf_exp_eq_sub_compose Γ Δ σ Δ0 τ A0 M0 Hσ Hτ HM0) as eqMraw.
      pose proof (@wf_exp_eq_conv_type Γ (a_sub A0 (a_compose τ σ))
                    (a_sub (a_sub A0 τ) σ) (a_sub M0 (a_compose τ σ))
                    (a_sub (a_sub M0 τ) σ) i eqMraw HtyA' eqA) as eqM.
      pose proof (@wf_exp_eq_conv_type Γ (a_sub A0 (a_compose τ σ))
                    (a_sub (a_sub A0 τ) σ) (a_sub M0 (a_compose τ σ))
                    W i Heq HtyA' eqA) as Heq'.
      eapply wf_exp_eq_trans.
      * eapply wf_exp_eq_sym. exact eqM.
      * exact Heq'.
  - exact I.
Qed.

(* ================================================================== *)
(* Target theorem.                                                    *)
(* ================================================================== *)
Theorem soundness : forall {Γ M A},
    {{ Γ ⊢ M : A }} ->
    exists W, nbe Γ M A W /\ {{ Γ ⊢ M ≈ W : A }}.
Proof.
  intros Γ M A H.
