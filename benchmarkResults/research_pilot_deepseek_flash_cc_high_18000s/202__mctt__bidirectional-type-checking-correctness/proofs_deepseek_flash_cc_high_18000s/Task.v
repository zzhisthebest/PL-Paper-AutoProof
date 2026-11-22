From Mctt.Algorithmic.Typing Require Import Definitions.

From Mctt.Core Require Import Base.

From Mctt.Frontend Require Import Elaborator.

From Stdlib Require Import Lia PeanoNat.

Import Domain_Notations.

(* ============================================================ *)
(* Basic evaluation / readback determinism                      *)
(* ============================================================ *)

Lemma eval_fst_det : forall m r, eval_fst m r -> forall r', eval_fst m r' -> r = r'.
Proof.
  intros m r H. induction H; intros r' H'; inversion H'; reflexivity.
Qed.

Lemma eval_det :
  (forall e ρ d, eval_exp e ρ d -> forall d', eval_exp e ρ d' -> d = d') /\
  (forall A MZ MS m ρ r, eval_natrec A MZ MS m ρ r -> forall r', eval_natrec A MZ MS m ρ r' -> r = r') /\
  (forall m n r, eval_app m n r -> forall r', eval_app m n r' -> r = r') /\
  (forall m r, eval_snd m r -> forall r', eval_snd m r' -> r = r') /\
  (forall a B BR m1 m2 n ρ r, eval_eqrec a B BR m1 m2 n ρ r -> forall r', eval_eqrec a B BR m1 m2 n ρ r' -> r = r') /\
  (forall σ ρ ρσ, eval_sub σ ρ ρσ -> forall ρσ', eval_sub σ ρ ρσ' -> ρσ = ρσ').
Proof.
  apply (eval_mut_ind
    (fun e ρ d _ => forall d', eval_exp e ρ d' -> d = d')
    (fun A MZ MS m ρ r _ => forall r', eval_natrec A MZ MS m ρ r' -> r = r')
    (fun m n r _ => forall r', eval_app m n r' -> r = r')
    (fun m r _ => forall r', eval_snd m r' -> r = r')
    (fun a B BR m1 m2 n ρ r _ => forall r', eval_eqrec a B BR m1 m2 n ρ r' -> r = r')
    (fun σ ρ ρσ _ => forall ρσ', eval_sub σ ρ ρσ' -> ρσ = ρσ')).
  all: intros; try match goal with
    | H : ?R ?c |- ?lhs = ?c =>
        inversion H; subst;
        repeat match goal with
          | IH2 : forall y, ?R2 y -> ?a2 = ?b2, H2 : ?R2 ?c2 |- _ =>
              let E := fresh in pose proof (IH2 c2 H2) as E; clear IH2; rewrite E in *; clear E
        end; subst; try reflexivity; try assumption; try congruence
    end.
  all: try solve [eapply eval_fst_det; eassumption].
Qed.

Definition eval_exp_fun := proj1 eval_det.
Definition eval_natrec_fun := proj1 (proj2 eval_det).
Definition eval_app_fun := proj1 (proj2 (proj2 eval_det)).
Definition eval_snd_fun := proj1 (proj2 (proj2 (proj2 eval_det))).
Definition eval_eqrec_fun := proj1 (proj2 (proj2 (proj2 (proj2 eval_det)))).
Definition eval_sub_fun := proj2 (proj2 (proj2 (proj2 (proj2 eval_det)))).

Lemma read_det :
  (forall s m W, read_nf s m W -> forall W', read_nf s m W' -> W = W') /\
  (forall s m W, read_ne s m W -> forall W', read_ne s m W' -> W = W') /\
  (forall s m W, read_typ s m W -> forall W', read_typ s m W' -> W = W').
Proof.
  apply (read_mut_ind
    (fun s m W _ => forall W', read_nf s m W' -> W = W')
    (fun s m W _ => forall W', read_ne s m W' -> W = W')
    (fun s m W _ => forall W', read_typ s m W' -> W = W')).
  all: intros; try match goal with
    | H : ?R ?c |- ?lhs = ?c =>
        inversion H; subst;
        repeat match goal with
          | IH2 : forall y, ?R2 y -> ?a2 = ?b2, H2 : ?R2 ?c2 |- _ =>
              let E := fresh in pose proof (IH2 c2 H2) as E; clear IH2; clear H2; rewrite E in *; clear E
          | H1 : eval_exp ?e ?r ?d, H2 : eval_exp ?e ?r ?d2 |- _ =>
              let E := fresh in pose proof (eval_exp_fun e r d H1 d2 H2) as E; clear H1; clear H2; rewrite E in *; clear E
          | H1 : eval_natrec ?A ?MZ ?MS ?m ?r ?d, H2 : eval_natrec ?A ?MZ ?MS ?m ?r ?d2 |- _ =>
              let E := fresh in pose proof (eval_natrec_fun A MZ MS m r d H1 d2 H2) as E; clear H1; clear H2; rewrite E in *; clear E
          | H1 : eval_app ?m ?n ?d, H2 : eval_app ?m ?n ?d2 |- _ =>
              let E := fresh in pose proof (eval_app_fun m n d H1 d2 H2) as E; clear H1; clear H2; rewrite E in *; clear E
          | H1 : eval_snd ?m ?d, H2 : eval_snd ?m ?d2 |- _ =>
              let E := fresh in pose proof (eval_snd_fun m d H1 d2 H2) as E; clear H1; clear H2; rewrite E in *; clear E
          | H1 : eval_eqrec ?a ?B ?BR ?m1 ?m2 ?n ?r ?d, H2 : eval_eqrec ?a ?B ?BR ?m1 ?m2 ?n ?r ?d2 |- _ =>
              let E := fresh in pose proof (eval_eqrec_fun a B BR m1 m2 n r d H1 d2 H2) as E; clear H1; clear H2; rewrite E in *; clear E
          | H1 : eval_sub ?s ?r ?d, H2 : eval_sub ?s ?r ?d2 |- _ =>
              let E := fresh in pose proof (eval_sub_fun s r d H1 d2 H2) as E; clear H1; clear H2; rewrite E in *; clear E
          | H1 : eval_fst ?m ?d, H2 : eval_fst ?m ?d2 |- _ =>
              let E := fresh in pose proof (eval_fst_det m d H1 d2 H2) as E; clear H1; clear H2; rewrite E in *; clear E
        end; subst; try reflexivity; try assumption; try congruence
    end.
Qed.

Lemma initial_env_det : forall Γ ρ1, initial_env Γ ρ1 -> forall ρ2, initial_env Γ ρ2 -> ρ1 = ρ2.
Proof.
  intros Γ. induction Γ as [| A Γ IH]; intros ρ1 H1 ρ2 H2; inversion H1; inversion H2; subst.
  - reflexivity.
  - assert (Hρ : ρ = ρ0) by (eapply IH; eassumption). subst ρ0.
    assert (Ha : a = a0) by (eapply eval_exp_fun; eassumption). subst a0.
    reflexivity.
Qed.

Lemma nbe_ty_det : forall Γ A W, nbe_ty Γ A W -> forall W', nbe_ty Γ A W' -> W = W'.
Proof.
  intros Γ A W H. intros W' H'. inversion H; inversion H'; subst.
  assert (Hρ : ρ = ρ0) by (eapply initial_env_det; eassumption). subst ρ0.
  assert (Hm : m = m0) by (eapply eval_exp_fun; eassumption). subst m0.
  exact (proj2 (proj2 (read_det)) _ _ _ H2 _ H8).
Qed.

Lemma nbe_det : forall Γ M A W, nbe Γ M A W -> forall W', nbe Γ M A W' -> W = W'.
Proof.
  intros Γ M A W H. intros W' H'. inversion H; inversion H'; subst.
  assert (Hρ : ρ = ρ0) by (eapply initial_env_det; eassumption). subst ρ0.
  assert (Ha : a = a0) by (eapply eval_exp_fun; eassumption). subst a0.
  assert (Hm : m = m0) by (eapply eval_exp_fun; eassumption). subst m0.
  exact (proj1 (read_det) (length Γ) (d_dom a m) W H3 W' H11).
Qed.

(* ============================================================ *)
(* Basic context/typing facts                                   *)
(* ============================================================ *)

Lemma wf_ctx_prefix : forall {Γ A}, {{ ⊢ Γ, A }} -> {{ ⊢ Γ }}.
Proof. intros. inversion H. assumption. Qed.

Lemma wf_all_ctx :
  (forall Γ, {{ ⊢ Γ }} -> {{ ⊢ Γ }}) /\
  (forall Γ A M, {{ Γ ⊢ M : A }} -> {{ ⊢ Γ }}) /\
  (forall Γ Δ σ, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Γ }}).
Proof.
  apply (syntactic_wf_mut_ind'
    (fun Γ _ => {{ ⊢ Γ }})
    (fun Γ A M _ => {{ ⊢ Γ }})
    (fun Γ Δ σ _ => {{ ⊢ Γ }})).
  - exact wf_ctx_empty.
  - intros Γ i A w IH w0 IH0. apply wf_ctx_extend with (i:=i); [exact IH | exact w0].
  - intros; assumption.
  - intros; assumption.
  - intros; assumption.
  - intros; assumption.
  - intros Γ i A MZ MS M w IH w0 IH0 w1 IH1 w2 IH2. apply wf_ctx_prefix in IH. exact IH.
  - intros; assumption.
  - intros; assumption.
  - intros; assumption.
  - intros; assumption.
  - intros; assumption.
  - intros; assumption.
  - intros; assumption.
  - intros; assumption.
  - intros; assumption.
  - intros; assumption.
  - intros; assumption.
  - intros; assumption.
  - intros; assumption.
  - intros; assumption.
  - intros; assumption.
  - intros; assumption.
  - intros; assumption.
  - intros; assumption.
Qed.

Lemma wf_exp_ctx : forall Γ A M, {{ Γ ⊢ M : A }} -> {{ ⊢ Γ }}.
Proof. intros. exact (proj1 (proj2 wf_all_ctx) Γ A M H). Qed.

Lemma wf_sub_ctx : forall Γ Δ σ, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Γ }}.
Proof. intros. exact (proj2 (proj2 wf_all_ctx) Γ Δ σ H). Qed.





(* ============================================================ *)
(* Reflexivity of expression and substitution equality          *)
(* ============================================================ *)

Lemma wf_eq_refl_all :
  (forall Γ, {{ ⊢ Γ }} -> True) /\
  (forall Γ Δ, {{ ⊢ Γ ⊆ Δ }} -> True) /\
  (forall Γ A M, {{ Γ ⊢ M : A }} -> {{ Γ ⊢ M ≈ M : A }}) /\
  (forall Γ A M M', {{ Γ ⊢ M ≈ M' : A }} -> True) /\
  (forall Γ Δ σ, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢s σ ≈ σ : Δ }}) /\
  (forall Γ Δ σ σ', {{ Γ ⊢s σ ≈ σ' : Δ }} -> True) /\
  (forall Γ A A', {{ Γ ⊢ A ⊆ A' }} -> True).
Proof.
  apply (syntactic_wf_mut_ind
    (fun _ _ => True)
    (fun _ _ _ => True)
    (fun Γ A M _ => {{ Γ ⊢ M ≈ M : A }})
    (fun _ _ _ _ _ => True)
    (fun Γ Δ σ _ => {{ Γ ⊢s σ ≈ σ : Δ }})
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ => True)).
  all: try exact I.
  all: intros.
  all: try solve
    [ eapply wf_exp_eq_trans with (M' := a_sub (a_typ _) a_id);
      [ eapply wf_exp_eq_sym; eapply wf_exp_eq_typ_sub; apply wf_sub_id; eauto
      | eapply wf_exp_eq_typ_sub; apply wf_sub_id; eauto ]
    | eapply wf_exp_eq_trans with (M' := a_sub a_nat a_id);
      [ eapply wf_exp_eq_sym; eapply wf_exp_eq_nat_sub; apply wf_sub_id; eauto
      | eapply wf_exp_eq_nat_sub; apply wf_sub_id; eauto ]
    | eapply wf_exp_eq_trans with (M' := a_sub a_zero a_id);
      [ eapply wf_exp_eq_sym; eapply wf_exp_eq_zero_sub; apply wf_sub_id; eauto
      | eapply wf_exp_eq_zero_sub; apply wf_sub_id; eauto ]
    | eapply wf_exp_eq_var; eauto
    | eapply wf_sub_eq_id; eauto
    | eapply wf_sub_eq_weaken; eauto
    | eapply wf_sub_eq_compose_cong; eauto
    | eapply wf_sub_eq_extend_cong; eauto
    | eapply wf_sub_eq_subtyp; eauto
    | econstructor; eauto ].
Qed.


Lemma wf_exp_eq_refl : forall Γ A M, {{ Γ ⊢ M : A }} -> {{ Γ ⊢ M ≈ M : A }}.
Proof. intros. exact (proj1 (proj2 (proj2 wf_eq_refl_all)) Γ A M H). Qed.

Lemma wf_sub_eq_refl : forall Γ Δ σ, {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢s σ ≈ σ : Δ }}.
Proof. intros. exact (proj1 (proj2 (proj2 (proj2 (proj2 wf_eq_refl_all)))) Γ Δ σ H). Qed.

(* ============================================================ *)
(* Substitution helpers for universes and general types         *)
(* ============================================================ *)

Lemma wf_subst_type : forall Γ Δ σ A i,
  {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ A : Type@i }} -> {{ Γ ⊢ A[σ] : Type@i }}.
Proof.
  intros Γ Δ σ A i Hσ HA. apply wf_sub_ctx in Hσ as Hwf.
  eapply wf_exp_subtyp.
  - eapply wf_exp_sub; [exact Hσ | exact HA].
  - apply wf_typ. exact Hwf.
  - apply wf_subtyp_refl with (i := S i).
    + apply wf_typ. exact Hwf.
    + eapply wf_exp_eq_typ_sub. exact Hσ.
Qed.

Lemma wf_exp_eq_univ_retype : forall Γ Δ σ i M M',
  {{ Γ ⊢s σ : Δ }} ->
  {{ Γ ⊢ M ≈ M' : (Type@i)[σ] }} ->
  {{ Γ ⊢ M ≈ M' : Type@i }}.
Proof.
  intros Γ Δ σ i M M' Hσ Heq. apply wf_sub_ctx in Hσ as Hwf.
  eapply wf_exp_eq_subtyp; [exact Heq| |].
  - apply wf_typ. exact Hwf.
  - apply wf_subtyp_refl with (i := S i).
    + apply wf_typ. exact Hwf.
    + eapply wf_exp_eq_typ_sub. exact Hσ.
Qed.

Lemma wf_exp_eq_sub_cong_univ : forall Γ Δ σ σ' A i,
  {{ Γ ⊢s σ : Δ }} -> {{ Γ ⊢s σ' : Δ }} ->
  {{ Γ ⊢s σ ≈ σ' : Δ }} ->
  {{ Δ ⊢ A : Type@i }} ->
  {{ Γ ⊢ A[σ] ≈ A[σ'] : Type@i }}.
Proof.
  intros Γ Δ σ σ' A i Hσ Hσ' Hseq HA.
  eapply wf_exp_eq_univ_retype; [exact Hσ|].
  eapply wf_exp_eq_sub_cong.
  - apply wf_exp_eq_refl. exact HA.
  - exact Hseq.
Qed.

Lemma wf_exp_eq_sub_compose_univ : forall Γ Γ' Γ'' τ σ A i,
  {{ Γ ⊢s τ : Γ' }} -> {{ Γ' ⊢s σ : Γ'' }} ->
  {{ Γ'' ⊢ A : Type@i }} ->
  {{ Γ ⊢ (A[σ ∘ τ]) ≈ (A[σ])[τ] : Type@i }}.
Proof.
  intros Γ Γ' Γ'' τ σ A i Hτ Hσ HA.
  eapply wf_exp_eq_univ_retype with (Δ:=Γ'') (σ:=a_compose σ τ).
  - apply wf_sub_compose with (Γ2 := Γ'); eassumption.
  - eapply wf_exp_eq_sub_compose with (Γ:=Γ) (Γ':=Γ') (Γ'':=Γ'') (τ:=τ) (σ:=σ) (A:=a_typ i) (M:=A); [exact Hτ|exact Hσ|exact HA].
Qed.

Lemma wf_exp_eq_sub_id_univ : forall Γ A i,
  {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ (A[Id]) ≈ A : Type@i }}.
Proof. intros. apply wf_exp_eq_sub_id. exact H. Qed.

Lemma wf_exp_conv : forall Γ A A' M i,
  {{ Γ ⊢ M : A }} -> {{ Γ ⊢ A ≈ A' : Type@i }} ->
  {{ Γ ⊢ A' : Type@i }} -> {{ Γ ⊢ M : A' }}.
Proof.
  intros Γ A A' M i HM Heq HA'.
  eapply wf_exp_subtyp; [exact HM|exact HA'|].
  eapply wf_subtyp_refl; [exact HA'|exact Heq].
Qed.

Lemma wf_sub_extend_id_self : forall Γ A M i,
  {{ Γ ⊢ M : A }} -> {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢s (Id ,, M) : Γ, A }}.
Proof.
  intros Γ A M i HM HA. apply wf_exp_ctx in HM as Hwf.
  assert (Hid : {{ Γ ⊢s Id : Γ }}) by (apply wf_sub_id; exact Hwf).
  assert (HAid : {{ Γ ⊢ (A[Id]) : Type@i }})
    by (eapply wf_subst_type; [exact Hid|exact HA]).
  assert (Heq : {{ Γ ⊢ (A[Id]) ≈ A : Type@i }})
    by (apply wf_exp_eq_sub_id; exact HA).
  assert (HM' : {{ Γ ⊢ M : (A[Id]) }})
    by (eapply wf_exp_conv; [exact HM | apply wf_exp_eq_sym; exact Heq | exact HAid]).
  eapply wf_sub_extend; [exact Hid|exact HA|exact HM'].
Qed.




Lemma wf_exp_eq_conv : forall Γ A A' M M' i,
  {{ Γ ⊢ M ≈ M' : A }} -> {{ Γ ⊢ A ≈ A' : Type@i }} ->
  {{ Γ ⊢ A' : Type@i }} -> {{ Γ ⊢ M ≈ M' : A' }}.
Proof.
  intros Γ A A' M M' i Heq HAeq HA'.
  eapply wf_exp_eq_subtyp; [exact Heq|exact HA'|].
  apply wf_subtyp_refl with (i := i); [exact HA'|exact HAeq].
Qed.



Lemma sub_wk_extend_id_self_approx : forall Γ A M i,
  {{ Γ ⊢ M : A }} -> {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ (A[Wk])[Id ,, M] ≈ A : Type@i }}.
Proof.
  intros Γ A M i HM HA. apply wf_exp_ctx in HM as Hwf.
  assert (Hid : {{ Γ ⊢s Id : Γ }}) by (apply wf_sub_id; exact Hwf).
  assert (HAid_ty : {{ Γ ⊢ (A[Id]) : Type@i }})
    by (eapply wf_subst_type; [exact Hid|exact HA]).
  assert (HAid_eq : {{ Γ ⊢ (A[Id]) ≈ A : Type@i }})
    by (apply wf_exp_eq_sub_id; exact HA).
  assert (HMId : {{ Γ ⊢ M : (A[Id]) }})
    by (eapply wf_exp_conv; [exact HM|apply wf_exp_eq_sym; exact HAid_eq|exact HAid_ty]).
  assert (Hσ1 : {{ Γ ⊢s (Id ,, M) : Γ, A }})
    by (eapply wf_sub_extend; [exact Hid|exact HA|exact HMId]).
  assert (HctxA : {{ ⊢ Γ, A }}) by (apply wf_ctx_extend with (i:=i); [exact Hwf|exact HA]).
  assert (HWk : {{ Γ, A ⊢s Wk : Γ }}) by (apply wf_sub_weaken; exact HctxA).
  assert (Hcomp : {{ Γ ⊢ (A[Wk ∘ (Id ,, M)]) ≈ (A[Wk])[Id ,, M] : Type@i }})
    by (eapply wf_exp_eq_sub_compose_univ with (Γ:=Γ) (Γ':=(A :: Γ)%list) (Γ'':=Γ)
          (τ:=a_extend a_id M) (σ:=a_weaken) (A:=A) (i:=i); eassumption).
  assert (Hsubeq : {{ Γ ⊢s (Wk ∘ (Id ,, M)) ≈ Id : Γ }})
    by (eapply wf_sub_eq_p_extend; [exact Hid|exact HA|exact HMId]).
  assert (Hcong : {{ Γ ⊢ (A[Wk ∘ (Id ,, M)]) ≈ (A[Id]) : Type@i }}).
  { eapply wf_exp_eq_sub_cong_univ with
      (Δ:=Γ) (σ:=a_compose a_weaken (a_extend a_id M)) (σ':=a_id).
    - eapply wf_sub_compose with (Γ2 := (A :: Γ)%list); eassumption.
    - exact Hid.
    - exact Hsubeq.
    - exact HA. }
  eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; exact Hcomp|].
  eapply wf_exp_eq_trans; [exact Hcong|exact HAid_eq].
Qed.


Lemma sub_wk_extend_approx : forall Γ Δ σ A M i,
  {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ A : Type@i }} -> {{ Γ ⊢ M : A[σ] }} ->
  {{ Γ ⊢ (A[Wk])[σ ,, M] ≈ A[σ] : Type@i }}.
Proof.
  intros Γ Δ σ A M i Hσ HA HM.
  assert (HσM : {{ Γ ⊢s (σ ,, M) : Δ, A }})
    by (eapply wf_sub_extend; eassumption).
  assert (HctxΔ : {{ ⊢ Δ }}) by (apply wf_exp_ctx in HA; exact HA).
  assert (HctxΔA : {{ ⊢ Δ, A }}) by (apply wf_ctx_extend with (i:=i); assumption).
  assert (HWk : {{ Δ, A ⊢s Wk : Δ }}) by (apply wf_sub_weaken; exact HctxΔA).
  assert (Hcomp : {{ Γ ⊢ (A[Wk ∘ (σ ,, M)]) ≈ (A[Wk])[σ ,, M] : Type@i }})
    by (eapply wf_exp_eq_sub_compose_univ with (Γ:=Γ) (Γ':=(A :: Δ)%list) (Γ'':=Δ)
          (τ:=a_extend σ M) (σ:=a_weaken) (A:=A) (i:=i); eassumption).
  assert (Hsubeq : {{ Γ ⊢s (Wk ∘ (σ ,, M)) ≈ σ : Δ }})
    by (eapply wf_sub_eq_p_extend; [exact Hσ|exact HA|exact HM]).
  assert (Hcong : {{ Γ ⊢ (A[Wk ∘ (σ ,, M)]) ≈ A[σ] : Type@i }}).
  { eapply wf_exp_eq_sub_cong_univ with
      (Δ:=Δ) (σ:=a_compose a_weaken (a_extend σ M)) (σ':=σ).
    - eapply wf_sub_compose with (Γ2 := (A :: Δ)%list); eassumption.
    - exact Hσ.
    - exact Hsubeq.
    - exact HA. }
  eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; exact Hcomp|exact Hcong].
Qed.

Lemma sub_double_wk_extend_approx : forall Γ A M1 M2 i,
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M1 : (A[Id]) }} ->
  {{ Γ ⊢ M2 : ((A[Wk])[Id ,, M1]) }} ->
  {{ Γ ⊢ (A[Wk ∘ Wk])[(Id ,, M1) ,, M2] ≈ A : Type@i }}.
Proof.
  intros Γ A M1 M2 i HA HM1 HM2.
  apply wf_exp_ctx in HA as Hwf.
  assert (Hid : {{ Γ ⊢s Id : Γ }}) by (apply wf_sub_id; exact Hwf).
  assert (HAid : {{ Γ ⊢ (A[Id]) : Type@i }}) by (eapply wf_subst_type; eassumption).
  assert (Hσ1 : {{ Γ ⊢s (Id ,, M1) : Γ, A }}) by (eapply wf_sub_extend; eassumption).
  assert (Hctx1 : {{ ⊢ Γ, A }}) by (apply wf_ctx_extend with (i:=i); assumption).
  assert (HWk1 : {{ Γ, A ⊢s Wk : Γ }}) by (apply wf_sub_weaken; exact Hctx1).
  assert (HAwk : {{ Γ, A ⊢ (A[Wk]) : Type@i }}) by (eapply wf_subst_type; eassumption).
  assert (Hctx2 : {{ ⊢ Γ, A, A[Wk] }}) by (apply wf_ctx_extend with (i:=i); assumption).
  assert (HWk2 : {{ Γ, A, A[Wk] ⊢s Wk : Γ, A }}) by (apply wf_sub_weaken; exact Hctx2).
  assert (Hσ2 : {{ Γ ⊢s ((Id ,, M1) ,, M2) : Γ, A, A[Wk] }})
    by (eapply wf_sub_extend; eassumption).
  assert (HWW : {{ Γ, A, A[Wk] ⊢s (Wk ∘ Wk) : Γ }}).
  { eapply wf_sub_compose with (Γ1:=(a_sub A a_weaken :: A :: Γ)%list)
      (Γ2:=(A :: Γ)%list) (Γ3:=Γ)
      (σ2:=a_weaken) (σ1:=a_weaken); assumption. }
  assert (Hcomp : {{ Γ ⊢ (A[(Wk ∘ Wk) ∘ ((Id ,, M1) ,, M2)]) ≈ (A[Wk ∘ Wk])[(Id ,, M1) ,, M2] : Type@i }})
    by (eapply wf_exp_eq_sub_compose_univ with
          (Γ:=Γ) (Γ':=(a_sub A a_weaken :: A :: Γ)%list) (Γ'':=Γ)
          (τ:=a_extend (a_extend a_id M1) M2) (σ:=a_compose a_weaken a_weaken)
          (A:=A) (i:=i); eassumption).
  assert (Hsubeq1 : {{ Γ ⊢s (Wk ∘ (Id ,, M1)) ≈ Id : Γ }})
    by (eapply wf_sub_eq_p_extend; [exact Hid|exact HA|exact HM1]).
  assert (Hsubeq2 : {{ Γ ⊢s (Wk ∘ ((Id ,, M1) ,, M2)) ≈ (Id ,, M1) : Γ, A }})
    by (eapply wf_sub_eq_p_extend; [exact Hσ1|exact HAwk|exact HM2]).
  assert (Hcompose_cong : {{ Γ ⊢s (Wk ∘ (Wk ∘ ((Id ,, M1) ,, M2))) ≈ (Wk ∘ (Id ,, M1)) : Γ }}).
  { eapply wf_sub_eq_compose_cong with
      (Γ:=Γ) (Γ':=(A :: Γ)%list)
      (τ:=a_compose a_weaken (a_extend (a_extend a_id M1) M2))
      (τ':=a_extend a_id M1)
      (Γ'':=Γ) (σ:=a_weaken) (σ':=a_weaken).
    - exact Hsubeq2.
    - eapply wf_sub_eq_refl. exact HWk1. }
  assert (Hassoc : {{ Γ ⊢s ((Wk ∘ Wk) ∘ ((Id ,, M1) ,, M2)) ≈ (Wk ∘ (Wk ∘ ((Id ,, M1) ,, M2))) : Γ }}).
  { eapply wf_sub_eq_compose_assoc with
      (Γ':=(A :: Γ)%list) (Γ:=Γ) (σ:=a_weaken)
      (Γ'':=(a_sub A a_weaken :: A :: Γ)%list) (σ':=a_weaken)
      (Γ''':=Γ) (σ'':=a_extend (a_extend a_id M1) M2).
    - exact HWk1.
    - exact HWk2.
    - exact Hσ2. }
  assert (Hsubeq : {{ Γ ⊢s ((Wk ∘ Wk) ∘ ((Id ,, M1) ,, M2)) ≈ Id : Γ }}).
  { eapply wf_sub_eq_trans; [exact Hassoc|].
    eapply wf_sub_eq_trans; [exact Hcompose_cong|exact Hsubeq1]. }
  assert (HWWσ : {{ Γ ⊢s (((Wk ∘ Wk) ∘ ((Id ,, M1) ,, M2))) : Γ }}).
  { eapply wf_sub_compose with
      (Γ1:=Γ) (Γ2:=(a_sub A a_weaken :: A :: Γ)%list) (Γ3:=Γ)
      (σ2:=a_extend (a_extend a_id M1) M2)
      (σ1:=a_compose a_weaken a_weaken); assumption. }
  assert (Hcong : {{ Γ ⊢ (A[(Wk ∘ Wk) ∘ ((Id ,, M1) ,, M2)]) ≈ (A[Id]) : Type@i }}).
  { eapply wf_exp_eq_sub_cong_univ with
      (Δ:=Γ) (σ:=a_compose (a_compose a_weaken a_weaken) (a_extend (a_extend a_id M1) M2))
      (σ':=a_id).
    - exact HWWσ.
    - exact Hid.
    - exact Hsubeq.
    - exact HA. }
  assert (HId : {{ Γ ⊢ (A[Id]) ≈ A : Type@i }}) by (apply wf_exp_eq_sub_id_univ; exact HA).
  eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; exact Hcomp|].
  eapply wf_exp_eq_trans; [exact Hcong|exact HId].
Qed.

Lemma eqrec_ctx_typing : forall Γ A i,
  {{ Γ ⊢ A : Type@i }} ->
  ({{ Γ, A, A[Wk] ⊢ (A[Wk ∘ Wk]) : Type@i }} /\
   {{ Γ, A, A[Wk] ⊢ #1 : (A[Wk ∘ Wk]) }} /\
   {{ Γ, A, A[Wk] ⊢ #0 : (A[Wk ∘ Wk]) }} /\
   {{ Γ, A, A[Wk] ⊢ Eq (A[Wk ∘ Wk]) #1 #0 : Type@i }}).
Proof.
  intros Γ A i HA. pose proof (wf_exp_ctx _ _ _ HA) as Hwf.
  assert (Hctx1 : {{ ⊢ Γ, A }}) by (apply wf_ctx_extend with (i:=i); [exact Hwf|exact HA]).
  assert (HWk1 : {{ Γ, A ⊢s Wk : Γ }}) by (apply wf_sub_weaken; exact Hctx1).
  assert (HAwk : {{ Γ, A ⊢ (A[Wk]) : Type@i }}) by (eapply wf_subst_type; eassumption).
  assert (Hctx2 : {{ ⊢ Γ, A, A[Wk] }}) by (apply wf_ctx_extend with (i:=i); [exact Hctx1|exact HAwk]).
  assert (HWk2 : {{ Γ, A, A[Wk] ⊢s Wk : Γ, A }}) by (apply wf_sub_weaken; exact Hctx2).
  assert (HWW : {{ Γ, A, A[Wk] ⊢s (Wk ∘ Wk) : Γ }}).
  { eapply wf_sub_compose with (Γ1:=(a_sub A a_weaken :: A :: Γ)%list)
      (Γ2:=(A :: Γ)%list) (Γ3:=Γ)
      (σ2:=a_weaken) (σ1:=a_weaken); assumption. }
  assert (HAc : {{ Γ, A, A[Wk] ⊢ (A[Wk ∘ Wk]) : Type@i }})
    by (eapply wf_subst_type; eassumption).
  assert (HL : {{ Γ, A, A[Wk] ⊢ ((A[Wk])[Wk]) : Type@i }})
    by (eapply wf_subst_type; eassumption).
  assert (Happrox : {{ Γ, A, A[Wk] ⊢ (A[Wk ∘ Wk]) ≈ (A[Wk])[Wk] : Type@i }}).
  { eapply wf_exp_eq_sub_compose_univ with
      (Γ:=(a_sub A a_weaken :: A :: Γ)%list) (Γ':=(A :: Γ)%list) (Γ'':=Γ)
      (τ:=a_weaken) (σ:=a_weaken) (A:=A) (i:=i); eassumption. }
  assert (Hlk0 : {{ #0 : (A[Wk])[Wk] ∈ Γ, A, A[Wk] }}) by apply here.
  assert (Hlk1 : {{ #1 : (A[Wk])[Wk] ∈ Γ, A, A[Wk] }}) by (apply there; apply here).
  assert (HM1 : {{ Γ, A, A[Wk] ⊢ #1 : ((A[Wk])[Wk]) }})
    by (apply wf_vlookup; assumption).
  assert (HM0 : {{ Γ, A, A[Wk] ⊢ #0 : ((A[Wk])[Wk]) }})
    by (apply wf_vlookup; assumption).
  assert (HM1' : {{ Γ, A, A[Wk] ⊢ #1 : (A[Wk ∘ Wk]) }})
    by (eapply wf_exp_conv; [exact HM1|apply wf_exp_eq_sym; exact Happrox|exact HAc]).
  assert (HM0' : {{ Γ, A, A[Wk] ⊢ #0 : (A[Wk ∘ Wk]) }})
    by (eapply wf_exp_conv; [exact HM0|apply wf_exp_eq_sym; exact Happrox|exact HAc]).
  assert (HC : {{ Γ, A, A[Wk] ⊢ Eq (A[Wk ∘ Wk]) #1 #0 : Type@i }})
    by (apply wf_eq; assumption).
  repeat split; assumption.
Qed.

Lemma eqrec_ctx_sub_approx : forall Γ A M1 M2 i,
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M1 : (A[Id]) }} ->
  {{ Γ ⊢ M2 : ((A[Wk])[Id ,, M1]) }} ->
  {{ Γ ⊢ (Eq (A[Wk ∘ Wk]) #1 #0)[(Id ,, M1) ,, M2] ≈ Eq A M1 M2 : Type@i }}.
Proof.
  intros Γ A M1 M2 i HA HM1 HM2.
  pose proof (wf_exp_ctx _ _ _ HA) as Hwf.
  assert (Hid : {{ Γ ⊢s Id : Γ }}) by (apply wf_sub_id; exact Hwf).
  assert (Hctx1 : {{ ⊢ Γ, A }}) by (apply wf_ctx_extend with (i:=i); [exact Hwf|exact HA]).
  assert (HWk1 : {{ Γ, A ⊢s Wk : Γ }}) by (apply wf_sub_weaken; exact Hctx1).
  assert (HAwk : {{ Γ, A ⊢ (A[Wk]) : Type@i }}) by (eapply wf_subst_type; eassumption).
  assert (Hctx2 : {{ ⊢ Γ, A, A[Wk] }}) by (apply wf_ctx_extend with (i:=i); [exact Hctx1|exact HAwk]).
  assert (HWk2 : {{ Γ, A, A[Wk] ⊢s Wk : Γ, A }}) by (apply wf_sub_weaken; exact Hctx2).
  assert (Hσ1 : {{ Γ ⊢s (Id ,, M1) : Γ, A }}) by (eapply wf_sub_extend; eassumption).
  assert (Hσ2 : {{ Γ ⊢s ((Id ,, M1) ,, M2) : Γ, A, A[Wk] }})
    by (eapply wf_sub_extend; eassumption).
  destruct (eqrec_ctx_typing Γ A i HA) as [HAc [HMc [HNc HC]]].
  assert (E1 : {{ Γ ⊢ (A[Wk ∘ Wk])[(Id ,, M1) ,, M2] ≈ A : Type@i }})
    by (eapply sub_double_wk_extend_approx; eassumption).
  assert (HL1 : {{ Γ ⊢ ((A[Wk])[Id ,, M1]) : Type@i }})
    by (eapply wf_subst_type; eassumption).
  assert (HAid : {{ Γ ⊢ (A[Id]) : Type@i }}) by (eapply wf_subst_type; eassumption).
  assert (HAid_eq : {{ Γ ⊢ (A[Id]) ≈ A : Type@i }}) by (apply wf_exp_eq_sub_id_univ; exact HA).
  assert (HEawk : {{ Γ ⊢ ((A[Wk])[Id ,, M1]) ≈ (A[Id]) : Type@i }})
    by (eapply sub_wk_extend_approx; eassumption).
  assert (HAc_sub : {{ Γ ⊢ (A[Wk ∘ Wk])[(Id ,, M1) ,, M2] : Type@i }})
    by (eapply wf_subst_type; eassumption).
  assert (HL1_Ac : {{ Γ ⊢ ((A[Wk])[Id ,, M1]) ≈ (A[Wk ∘ Wk])[(Id ,, M1) ,, M2] : Type@i }}).
  { eapply wf_exp_eq_trans; [|apply wf_exp_eq_sym; exact E1].
    eapply wf_exp_eq_trans; [exact HEawk|exact HAid_eq]. }
  assert (HAid_Ac : {{ Γ ⊢ (A[Id]) ≈ (A[Wk ∘ Wk])[(Id ,, M1) ,, M2] : Type@i }}).
  { eapply wf_exp_eq_trans; [exact HAid_eq|apply wf_exp_eq_sym; exact E1]. }
  assert (HvarS : {{ Γ ⊢ #1[(Id ,, M1) ,, M2] ≈ #0[Id ,, M1] : ((A[Wk])[Id ,, M1]) }}).
  { eapply wf_exp_eq_var_S_sub.
    - exact Hσ1.
    - exact HAwk.
    - exact HM2.
    - apply here. }
  assert (Hvar0M1 : {{ Γ ⊢ #0[Id ,, M1] ≈ M1 : (A[Id]) }}).
  { eapply wf_exp_eq_var_0_sub; [exact Hid|exact HA|exact HM1]. }
  assert (Hvar0M2 : {{ Γ ⊢ #0[(Id ,, M1) ,, M2] ≈ M2 : ((A[Wk])[Id ,, M1]) }}).
  { eapply wf_exp_eq_var_0_sub; [exact Hσ1|exact HAwk|exact HM2]. }
  assert (E2 : {{ Γ ⊢ #1[(Id ,, M1) ,, M2] ≈ M1 : (A[Wk ∘ Wk])[(Id ,, M1) ,, M2] }}).
  { eapply wf_exp_eq_trans.
    - eapply wf_exp_eq_conv; [exact HvarS|exact HL1_Ac|exact HAc_sub].
    - eapply wf_exp_eq_conv; [exact Hvar0M1|exact HAid_Ac|exact HAc_sub]. }
  assert (E3 : {{ Γ ⊢ #0[(Id ,, M1) ,, M2] ≈ M2 : (A[Wk ∘ Wk])[(Id ,, M1) ,, M2] }}).
  { eapply wf_exp_eq_conv; [exact Hvar0M2|exact HL1_Ac|exact HAc_sub]. }
  assert (Heqsub : {{ Γ ⊢ (Eq (A[Wk ∘ Wk]) #1 #0)[(Id ,, M1) ,, M2]
      ≈ Eq (A[Wk ∘ Wk])[(Id ,, M1) ,, M2] (#1[(Id ,, M1) ,, M2]) (#0[(Id ,, M1) ,, M2]) : Type@i }}).
  { eapply wf_exp_eq_eq_sub; [exact Hσ2|exact HAc|exact HMc|exact HNc]. }
  assert (Heqcong : {{ Γ ⊢ Eq (A[Wk ∘ Wk])[(Id ,, M1) ,, M2]
        (#1[(Id ,, M1) ,, M2]) (#0[(Id ,, M1) ,, M2])
      ≈ Eq A M1 M2 : Type@i }}).
  { eapply wf_exp_eq_eq_cong; [exact E1|exact E2|exact E3]. }
  eapply wf_exp_eq_trans; [exact Heqsub|exact Heqcong].
Qed.

Lemma wf_eqrec_subst : forall Γ A M1 M2 N B i j,
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ M1 : (A[Id]) }} ->
  {{ Γ ⊢ M2 : ((A[Wk])[Id ,, M1]) }} ->
  {{ Γ ⊢ N : Eq A M1 M2 }} ->
  {{ Γ, A, A[Wk], Eq (A[Wk ∘ Wk]) #1 #0 ⊢ B : Type@j }} ->
  {{ Γ ⊢ B[((Id ,, M1) ,, M2) ,, N] : Type@j }}.
Proof.
  intros Γ A M1 M2 N B i j HA HM1 HM2 HN HB.
  pose proof (wf_exp_ctx _ _ _ HA) as Hwf.
  assert (Hid : {{ Γ ⊢s Id : Γ }}) by (apply wf_sub_id; exact Hwf).
  assert (Hctx1 : {{ ⊢ Γ, A }}) by (apply wf_ctx_extend with (i:=i); [exact Hwf|exact HA]).
  assert (HWk1 : {{ Γ, A ⊢s Wk : Γ }}) by (apply wf_sub_weaken; exact Hctx1).
  assert (HAwk : {{ Γ, A ⊢ (A[Wk]) : Type@i }}) by (eapply wf_subst_type; eassumption).
  assert (Hctx2 : {{ ⊢ Γ, A, A[Wk] }}) by (apply wf_ctx_extend with (i:=i); [exact Hctx1|exact HAwk]).
  assert (HWk2 : {{ Γ, A, A[Wk] ⊢s Wk : Γ, A }}) by (apply wf_sub_weaken; exact Hctx2).
  assert (Hσ1 : {{ Γ ⊢s (Id ,, M1) : Γ, A }}) by (eapply wf_sub_extend; eassumption).
  assert (Hσ2 : {{ Γ ⊢s ((Id ,, M1) ,, M2) : Γ, A, A[Wk] }})
    by (eapply wf_sub_extend; eassumption).
  destruct (eqrec_ctx_typing Γ A i HA) as [HAc [HMc [HNc HC]]].
  assert (Hsub : {{ Γ ⊢ (Eq (A[Wk ∘ Wk]) #1 #0)[(Id ,, M1) ,, M2] ≈ Eq A M1 M2 : Type@i }})
    by (eapply eqrec_ctx_sub_approx; eassumption).
  assert (Hsub_ty : {{ Γ ⊢ (Eq (A[Wk ∘ Wk]) #1 #0)[(Id ,, M1) ,, M2] : Type@i }})
    by (eapply wf_subst_type; eassumption).
  assert (HN' : {{ Γ ⊢ N : (Eq (A[Wk ∘ Wk]) #1 #0)[(Id ,, M1) ,, M2] }})
    by (eapply wf_exp_conv; [exact HN|apply wf_exp_eq_sym; exact Hsub|exact Hsub_ty]).
  assert (Hσ3 : {{ Γ ⊢s (((Id ,, M1) ,, M2) ,, N) : Γ, A, A[Wk], Eq (A[Wk ∘ Wk]) #1 #0 }})
    by (eapply wf_sub_extend; [exact Hσ2|exact HC|exact HN']).
  eapply wf_subst_type; [exact Hσ3|exact HB].
Qed.


(* ============================================================ *)
(* Environment arithmetic and initial-environment facts         *)
(* ============================================================ *)

Lemma drop_env_extend : forall (ρ : env) v, drop_env (extend_env ρ v) = ρ.
Proof. intros. reflexivity. Qed.

Lemma extend_env_zero : forall (ρ : env) v, extend_env ρ v 0 = v.
Proof. intros. reflexivity. Qed.

Lemma extend_env_succ : forall (ρ : env) v n, extend_env ρ v (S n) = ρ n.
Proof. intros. reflexivity. Qed.

Lemma initial_env_drop : forall A Γ ρ, initial_env (A :: Γ) ρ ->
  initial_env Γ (drop_env ρ).
Proof.
  intros A Γ ρ H. inversion H; subst.
  rewrite drop_env_extend. assumption.
Qed.

Lemma initial_env_head : forall A Γ ρ, initial_env (A :: Γ) ρ ->
  exists a, ρ 0 = d_neut a (d_var (length Γ)) /\ eval_exp A (drop_env ρ) a.
Proof.
  intros A Γ ρ H. inversion H; subst.
  exists a. split.
  - rewrite extend_env_zero. reflexivity.
  - rewrite drop_env_extend. exact H4.
Qed.

Lemma initial_env_extend : forall Γ ρ a, initial_env Γ ρ ->
  forall A, eval_exp A ρ a ->
  initial_env (A :: Γ) (extend_env ρ (d_neut a (d_var (length Γ)))).
Proof.
  intros. apply initial_env_cons; assumption.
Qed.


Lemma eval_exp_subst : forall M σ ρ ρσ m,
  eval_sub σ ρ ρσ -> eval_exp M ρσ m -> eval_exp (a_sub M σ) ρ m.
Proof. intros. eapply eval_exp_sub; eassumption. Qed.

Lemma eval_exp_sub_inv : forall M σ ρ m,
  eval_exp (a_sub M σ) ρ m -> exists ρσ, eval_sub σ ρ ρσ /\ eval_exp M ρσ m.
Proof. intros. inversion H; subst. eauto. Qed.

Lemma eval_sub_id_env : forall ρ, eval_sub a_id ρ ρ.
Proof. apply eval_sub_id. Qed.

Lemma eval_sub_weaken_env : forall ρ, eval_sub a_weaken ρ (drop_env ρ).
Proof. intros. apply eval_sub_weaken. Qed.

Lemma eval_sub_extend_env : forall σ ρ ρσ M m,
  eval_sub σ ρ ρσ -> eval_exp M ρ m ->
  eval_sub (a_extend σ M) ρ (extend_env ρσ m).
Proof. intros. eapply eval_sub_extend; eassumption. Qed.

Lemma eval_sub_compose_env : forall σ τ ρ ρτ ρτσ,
  eval_sub τ ρ ρτ -> eval_sub σ ρτ ρτσ ->
  eval_sub (a_compose σ τ) ρ ρτσ.
Proof. intros. eapply eval_sub_compose; eassumption. Qed.


Lemma wf_exp_cumul : forall Γ A i j, i <= j -> {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ A : Type@j }}.
Proof.
  intros Γ A i j Hle HA.
  destruct (Nat.lt_ge_cases i j) as [Hlt|Hge].
  - pose proof (wf_exp_ctx _ _ _ HA) as Hwf.
    eapply wf_exp_subtyp; [exact HA| |].
    + apply wf_typ. exact Hwf.
    + apply wf_subtyp_univ; [exact Hwf|exact Hlt].
  - assert (i = j) by lia. subst. exact HA.
Qed.

(* ============================================================ *)
(* Presupposition: lookup types and typing of types             *)
(* ============================================================ *)

Lemma ctx_lookup_type : forall Γ x A, {{ #x : A ∈ Γ }} ->
  {{ ⊢ Γ }} -> exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
  intros Γ x A Hlk. induction Hlk as [A0 Γ0 | n0 A0 Γ0 B Hn IH]; intros Hwf.
  - inversion Hwf; subst.
    exists i.
    eapply wf_exp_subtyp.
    + eapply wf_exp_sub; [apply wf_sub_weaken; exact Hwf | exact H2].
    + apply wf_typ. exact Hwf.
    + apply wf_subtyp_refl with (i := S i).
      * apply wf_typ. exact Hwf.
      * eapply wf_exp_eq_typ_sub. apply wf_sub_weaken. exact Hwf.
  - inversion Hwf; subst.
    destruct (IH H1) as [j Hj].
    exists j.
    eapply wf_exp_subtyp.
    + eapply wf_exp_sub; [apply wf_sub_weaken; exact Hwf | exact Hj].
    + apply wf_typ. exact Hwf.
    + apply wf_subtyp_refl with (i := S j).
      * apply wf_typ. exact Hwf.
      * eapply wf_exp_eq_typ_sub. apply wf_sub_weaken. exact Hwf.
Qed.


Lemma wf_exp_type : forall Γ A M, {{ Γ ⊢ M : A }} -> exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
  apply (wf_exp_ind (fun Γ A M => exists i, {{ Γ ⊢ A : Type@i }})).
  - intros Γ i Hwf. eexists. apply wf_typ. exact Hwf.
  - intros Γ Hwf. eexists. apply wf_typ. exact Hwf.
  - intros Γ Hwf. eexists. apply wf_nat. exact Hwf.
  - intros Γ M HM IHM. exact IHM.
  - intros Γ i A MZ MS M HA IHA HMZ IHMZ HMS IHMS HM IHM.
    pose proof (wf_exp_ctx _ _ _ HM) as Hwf.
    assert (Hnat : {{ Γ ⊢ ℕ : Type@0 }}) by (apply wf_nat; exact Hwf).
    assert (Hσ : {{ Γ ⊢s (Id ,, M) : Γ, ℕ }}) by (eapply wf_sub_extend_id_self; eassumption).
    exists i. eapply wf_subst_type; [exact Hσ|exact HA].
  - intros Γ i A B HA IHA HB IHB.
    eexists. apply wf_typ. pose proof (wf_exp_ctx _ _ _ HA). exact H.
  - intros Γ i A B M HA IHA HM IHM.
    destruct IHM as [j HB].
    assert (HcumA : {{ Γ ⊢ A : Type@(S (max i j)) }})
      by (eapply wf_exp_cumul; [|exact HA]; lia).
    assert (HcumB : {{ Γ, A ⊢ B : Type@(S (max i j)) }})
      by (eapply wf_exp_cumul; [|exact HB]; lia).
    exists (S (max i j)). apply wf_pi with (i:=S (max i j)); assumption.
  - intros Γ i A B M N HA IHA HB IHB HM IHM HN IHN.
    assert (Hσ : {{ Γ ⊢s (Id ,, N) : Γ, A }}) by (eapply wf_sub_extend_id_self; eassumption).
    exists i. eapply wf_subst_type; [exact Hσ|exact HB].
  - intros Γ i A B HA IHA HB IHB.
    eexists. apply wf_typ. pose proof (wf_exp_ctx _ _ _ HA). exact H.
  - intros Γ i A B M N HA IHA HB IHB HM IHM HN IHN.
    exists i. apply wf_sigma with (i:=i); assumption.
  - intros Γ i A B M HA IHA HB IHB HM IHM.
    exists i. exact HA.
  - intros Γ i A B M HA IHA HB IHB HM IHM.
    assert (HMf : {{ Γ ⊢ fst M : A }}) by (eapply wf_fst; eassumption).
    assert (Hσ : {{ Γ ⊢s (Id ,, fst M) : Γ, A }}) by (eapply wf_sub_extend_id_self; eassumption).
    exists i. eapply wf_subst_type; [exact Hσ|exact HB].
  - intros Γ x A Hwf Hlk. eapply ctx_lookup_type; eassumption.
  - intros Γ i A M N HA IHA HM IHM HN IHN.
    eexists. apply wf_typ. pose proof (wf_exp_ctx _ _ _ HA). exact H.
  - intros Γ i A M HA IHA HM IHM.
    exists i. apply wf_eq; assumption.
  - intros Γ i A M1 M2 j B BR N HA IHA HM1 IHM1 HM2 IHM2 HB IHB HBR IHBR HN IHN.
    pose proof (wf_exp_ctx _ _ _ HA) as Hwf.
    assert (Hid : {{ Γ ⊢s Id : Γ }}) by (apply wf_sub_id; exact Hwf).
    assert (HAid_ty : {{ Γ ⊢ (A[Id]) : Type@i }}) by (eapply wf_subst_type; eassumption).
    assert (HAid_eq : {{ Γ ⊢ (A[Id]) ≈ A : Type@i }}) by (apply wf_exp_eq_sub_id_univ; exact HA).
    assert (HM1' : {{ Γ ⊢ M1 : (A[Id]) }})
      by (eapply wf_exp_conv; [exact HM1|apply wf_exp_eq_sym; exact HAid_eq|exact HAid_ty]).
    assert (Hctx1 : {{ ⊢ Γ, A }}) by (apply wf_ctx_extend with (i:=i); [exact Hwf|exact HA]).
    assert (HWk1 : {{ Γ, A ⊢s Wk : Γ }}) by (apply wf_sub_weaken; exact Hctx1).
    assert (HAwk : {{ Γ, A ⊢ (A[Wk]) : Type@i }}) by (eapply wf_subst_type; eassumption).
    assert (Hσ1 : {{ Γ ⊢s (Id ,, M1) : Γ, A }}) by (eapply wf_sub_extend; eassumption).
    assert (HL1_ty : {{ Γ ⊢ ((A[Wk])[Id ,, M1]) : Type@i }}) by (eapply wf_subst_type; eassumption).
    assert (HEawk : {{ Γ ⊢ ((A[Wk])[Id ,, M1]) ≈ A : Type@i }}).
    { eapply wf_exp_eq_trans; [eapply sub_wk_extend_approx; eassumption|exact HAid_eq]. }
    assert (HM2' : {{ Γ ⊢ M2 : ((A[Wk])[Id ,, M1]) }})
      by (eapply wf_exp_conv; [exact HM2|apply wf_exp_eq_sym; exact HEawk|exact HL1_ty]).
    exists j. eapply wf_eqrec_subst with (Γ:=Γ) (A:=A) (M1:=M1) (M2:=M2) (N:=N) (B:=B) (i:=i) (j:=j); eassumption.
  - intros Γ Δ σ A M Hσ HM IHM.
    destruct IHM as [i Hi]. exists i. eapply wf_subst_type; [exact Hσ|exact Hi].
  - intros Γ A M i A' HM IHM HA' IHA' Hsub.
    exists i. exact HA'.
Qed.



Lemma wf_subtyp_refl' : forall Γ A i,
  {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ A ⊆ A }}.
Proof.
  intros. apply wf_subtyp_refl with (i:=i); [exact H|apply wf_exp_eq_refl; exact H].
Qed.

Lemma wf_subtyp_of_eq : forall Γ A A' i,
  {{ Γ ⊢ A ≈ A' : Type@i }} -> {{ Γ ⊢ A' : Type@i }} ->
  {{ Γ ⊢ A ⊆ A' }}.
Proof.
  intros. apply wf_subtyp_refl with (i:=i); assumption.
Qed.


Lemma eval_sub_id_initial : forall Γ ρ, initial_env Γ ρ -> eval_sub a_id ρ ρ.
Proof. intros. apply eval_sub_id. Qed.

Lemma eval_sub_extend_initial : forall Γ ρ M m,
  initial_env Γ ρ -> eval_exp M ρ m ->
  eval_sub (a_extend a_id M) ρ (extend_env ρ m).
Proof. intros. eapply eval_sub_extend; [apply eval_sub_id|exact H0]. Qed.

Lemma eval_sub_weaken_initial : forall A Γ ρ,
  initial_env (A :: Γ) ρ -> eval_sub a_weaken ρ (drop_env ρ).
Proof. intros. apply eval_sub_weaken. Qed.





Lemma wf_sub_tgt : forall Γ Δ σ, {{ Γ ⊢s σ : Δ }} -> {{ ⊢ Δ }}.
Proof.
  intros Γ Δ σ H. induction H.
  - exact H.
  - apply wf_ctx_prefix in H. exact H.
  - assumption.
  - eapply wf_ctx_extend; eassumption.
  - exact H0.
Qed.


Lemma wf_ctx_eq_refl : forall Γ, {{ ⊢ Γ }} -> {{ ⊢ Γ ≈ Γ }}.
Proof.
  intros Γ H. induction H as [| Γ i A Hwf HA IH].
  - apply wf_ctx_eq_empty.
  - eapply wf_ctx_eq_extend; try eassumption.
    all: apply wf_exp_eq_refl; assumption.
Qed.


Lemma wf_ctx_eq_sym : forall Γ Δ, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Δ ≈ Γ }}.
Proof.
  intros Γ Δ H.
  induction H as [| Γ0 Δ0 i A0 A0' Heq IH HA HA' HAΔ HAΔ' HeqΓ HeqΔ].
  - apply wf_ctx_eq_empty.
  - eapply wf_ctx_eq_extend with (Γ:=Δ0) (Δ:=Γ0) (i:=i) (A:=A0') (A':=A0).
    + exact IH.
    + exact HAΔ'.
    + exact HAΔ.
    + exact HA'.
    + exact HA.
    + apply wf_exp_eq_sym. exact HeqΔ.
    + apply wf_exp_eq_sym. exact HeqΓ.
Qed.


Lemma wf_subtyp_univ_le : forall Γ i j,
  {{ ⊢ Γ }} -> i <= j -> {{ Γ ⊢ Type@i ⊆ Type@j }}.
Proof.
  intros Γ i j Hwf Hle.
  destruct (Nat.lt_ge_cases i j) as [Hlt|Hge].
  - apply wf_subtyp_univ; assumption.
  - assert (i = j) by lia. subst.
    apply wf_subtyp_refl with (i:=S j).
    + apply wf_typ. exact Hwf.
    + apply wf_exp_eq_refl. apply wf_typ. exact Hwf.
Qed.

(* ============================================================ *)
(* Algorithmic normal-form subtyping: reflexivity               *)
(* ============================================================ *)

Lemma alg_subtyping_nf_refl : forall A, {{ ⊢anf A ⊆ A }}.
Proof.
  intro A. induction A.
  - apply asnf_univ. lia.
  - apply asnf_refl; [simpl; auto|reflexivity].
  - apply asnf_refl; [simpl; auto|reflexivity].
  - apply asnf_refl; [simpl; auto|reflexivity].
  - apply asnf_pi; [reflexivity|exact IHA2].
  - apply asnf_refl; [simpl; auto|reflexivity].
  - apply asnf_sigma; [reflexivity|exact IHA2].
  - apply asnf_refl; [simpl; auto|reflexivity].
  - apply asnf_refl; [simpl; auto|reflexivity].
  - apply asnf_refl; [simpl; auto|reflexivity].
  - apply asnf_refl; [simpl; auto|reflexivity].
Qed.


(* ============================================================ *)
(* Semantic realizability on domain values (fuel-indexed, cumulative) *)
(* ============================================================ *)

Fixpoint ST (n : nat) (a : domain) {struct n} : Prop :=
  match n with
  | O => True
  | S n' =>
    ST n' a /\
    match a with
    | d_univ _ => True
    | d_nat => True
    | d_pi a0 ρ B =>
        ST n' a0 /\
        (forall v, VT n' a0 v -> exists b, eval_exp B (extend_env ρ v) b /\ ST n' b)
    | d_sigma a0 ρ B =>
        ST n' a0 /\
        (forall v, VT n' a0 v -> exists b, eval_exp B (extend_env ρ v) b /\ ST n' b)
    | d_eq a m1 m2 => ST n' a /\ VT n' a m1 /\ VT n' a m2
    | d_neut _ _ => True
    | _ => False
    end
  end
with VT (n : nat) (a v : domain) {struct n} : Prop :=
  match n with
  | O => True
  | S n' =>
    VT n' a v /\
    match a with
    | d_univ _ =>
        ST n' v /\
        match v with
        | d_univ _ => True
        | d_nat => True
        | d_pi a0 ρ B =>
            ST n' a0 /\
            (forall v0, VT n' a0 v0 -> exists b, eval_exp B (extend_env ρ v0) b /\ ST n' b)
        | d_sigma a0 ρ B =>
            ST n' a0 /\
            (forall v0, VT n' a0 v0 -> exists b, eval_exp B (extend_env ρ v0) b /\ ST n' b)
        | d_eq a m1 m2 => ST n' a /\ VT n' a m1 /\ VT n' a m2
        | d_neut _ _ => True
        | _ => False
        end
    | d_nat => v = d_zero \/ (exists m, v = d_succ m) \/ (exists ty w, v = d_neut ty w)
    | d_pi a0 ρ B =>
        forall v0, VT n' a0 v0 ->
          exists r b, eval_exp B (extend_env ρ v0) b /\ eval_app v v0 r /\ VT n' b r
    | d_sigma a0 ρ B =>
        (exists v1 v2 b, v = d_pair v1 v2 /\ VT n' a0 v1 /\
                         eval_exp B (extend_env ρ v1) b /\ VT n' b v2)
        \/ (exists ty w, v = d_neut ty w)
    | d_eq a m1 m2 =>
        (exists m, v = d_refl m /\ VT n' a m) \/ (exists ty w, v = d_neut ty w)
    | d_neut _ _ => exists ty w, v = d_neut ty w
    | _ => False
    end
  end
with EQT (n : nat) (a b : domain) {struct n} : Prop :=
  match n with
  | O => True
  | S n' =>
    EQT n' a b /\
    match a, b with
    | d_univ i, d_univ j => i = j
    | d_nat, d_nat => True
    | d_pi a0 ρ B, d_pi a0' ρ' B' =>
        EQT n' a0 a0' /\
        (forall v v', EQV n' a0 v v' ->
           exists b b', eval_exp B (extend_env ρ v) b /\
                        eval_exp B' (extend_env ρ' v') b' /\ EQT n' b b')
    | d_sigma a0 ρ B, d_sigma a0' ρ' B' =>
        EQT n' a0 a0' /\
        (forall v v', EQV n' a0 v v' ->
           exists b b', eval_exp B (extend_env ρ v) b /\
                        eval_exp B' (extend_env ρ' v') b' /\ EQT n' b b')
    | d_eq a m1 m2, d_eq a' m1' m2' =>
        EQT n' a a' /\ EQV n' a m1 m1' /\ EQV n' a m2 m2'
    | d_neut _ _, d_neut _ _ => True
    | _, _ => False
    end
  end
with EQV (n : nat) (a v w : domain) {struct n} : Prop :=
  match n with
  | O => True
  | S n' =>
    EQV n' a v w /\
    match a with
    | d_univ _ =>
        EQT n' v w /\
        match v, w with
        | d_univ i, d_univ j => i = j
        | d_nat, d_nat => True
        | d_pi a0 ρ B, d_pi a0' ρ' B' =>
            EQT n' a0 a0' /\
            (forall u u', EQV n' a0 u u' ->
               exists b b', eval_exp B (extend_env ρ u) b /\
                            eval_exp B' (extend_env ρ' u') b' /\ EQT n' b b')
        | d_sigma a0 ρ B, d_sigma a0' ρ' B' =>
            EQT n' a0 a0' /\
            (forall u u', EQV n' a0 u u' ->
               exists b b', eval_exp B (extend_env ρ u) b /\
                            eval_exp B' (extend_env ρ' u') b' /\ EQT n' b b')
        | d_eq a m1 m2, d_eq a' m1' m2' =>
            EQT n' a a' /\ EQV n' a m1 m1' /\ EQV n' a m2 m2'
        | d_neut _ _, d_neut _ _ => True
        | _, _ => False
        end
    | d_nat =>
        (v = d_zero /\ w = d_zero) \/
        (exists m m', v = d_succ m /\ w = d_succ m' /\ EQV n' d_nat m m') \/
        (exists ty1 ty2 v' w', v = d_neut ty1 v' /\ w = d_neut ty2 w')
    | d_pi a0 ρ B =>
        (forall v0 v0', EQV n' a0 v0 v0' ->
           exists r r' b b', eval_exp B (extend_env ρ v0) b /\
                             eval_exp B (extend_env ρ v0') b' /\
                             eval_app v v0 r /\ eval_app w v0' r' /\ EQV n' b r r')
    | d_sigma a0 ρ B =>
        (exists v1 v2, v = d_pair v1 v2) /\ (exists w1 w2, w = d_pair w1 w2)
        \/ (exists ty1 ty2 v' w', v = d_neut ty1 v' /\ w = d_neut ty2 w')
    | d_eq a m1 m2 =>
        (exists m, v = d_refl m /\ w = d_refl m)
        \/ (exists ty1 ty2 v' w', v = d_neut ty1 v' /\ w = d_neut ty2 w')
    | d_neut _ _ => exists ty1 ty2 v' w', v = d_neut ty1 v' /\ w = d_neut ty2 w'
    | _ => False
    end
  end.

Lemma ST_down1 : forall n a, ST (S n) a -> ST n a.
Proof. intros. exact (proj1 H). Qed.
Lemma VT_down1 : forall n a v, VT (S n) a v -> VT n a v.
Proof. intros. exact (proj1 H). Qed.
Lemma EQT_down1 : forall n a b, EQT (S n) a b -> EQT n a b.
Proof. intros. exact (proj1 H). Qed.
Lemma EQV_down1 : forall n a v w, EQV (S n) a v w -> EQV n a v w.
Proof. intros. exact (proj1 H). Qed.

Lemma ST_down : forall n m a, m <= n -> ST n a -> ST m a.
Proof.
  intros n m a Hle. induction Hle as [| n Hle IH]; intros H.
  - exact H.
  - apply IH. apply ST_down1. exact H.
Qed.
Lemma VT_down : forall n m a v, m <= n -> VT n a v -> VT m a v.
Proof.
  intros n m a v Hle. induction Hle as [| n Hle IH]; intros H.
  - exact H.
  - apply IH. apply VT_down1. exact H.
Qed.
Lemma EQT_down : forall n m a b, m <= n -> EQT n a b -> EQT m a b.
Proof. intros n m a b Hle. induction Hle as [| n Hle IH]; intros H.
  - exact H. - apply IH. apply EQT_down1. exact H. Qed.
Lemma EQV_down : forall n m a v w, m <= n -> EQV n a v w -> EQV m a v w.
Proof. intros n m a v w Hle. induction Hle as [| n Hle IH]; intros H.
  - exact H. - apply IH. apply EQV_down1. exact H. Qed.

Lemma ST_univ : forall n i, ST n (d_univ i).
Proof. induction n; simpl; auto. Qed.
Lemma ST_nat_ty : forall n, ST n d_nat.
Proof. induction n; simpl; auto. Qed.
Lemma ST_neutral_val : forall n a w, ST n (d_neut a w).
Proof. induction n; simpl; auto. Qed.

Lemma VT_neutral : forall n a w, ST n a -> VT n a (d_neut a w).
Proof.
  induction n as [| n IH]; intros a w HST.
  - exact I.
  - destruct HST as [HSTn Hcl].
    split; [exact (IH a w HSTn)|].
    destruct a as [i| | |m|a0 e B|e M|a0 e B|v1 v2|a1 m1 m2|m|ty ww]; simpl in *.
    + split; [apply ST_neutral_val|]. exact I.
    + right; right; exists d_nat, w; reflexivity.
    + exfalso; exact Hcl.
    + exfalso; exact Hcl.
    + destruct Hcl as [Ha0 Hfam]. intros v0 HV0.
      destruct (Hfam v0 HV0) as [b [Hb HSTb]].
      exists (d_neut b (d_app w (d_dom a0 v0))), b.
      split; [exact Hb|]. split.
      * eapply eval_app_neut. exact Hb.
      * apply IH. exact HSTb.
    + exfalso; exact Hcl.
    + destruct Hcl as [Ha0 Hfam]. right. exists (d_sigma a0 e B), w. reflexivity.
    + exfalso; exact Hcl.
    + destruct Hcl as [Ha Hm1 Hm2]. right. exists (d_eq a1 m1 m2), w. reflexivity.
    + exfalso; exact Hcl.
    + exists (d_neut ty ww), w. reflexivity.
Qed.


(* ============================================================ *)
(* Realizing environments                                       *)
(* ============================================================ *)

Inductive Renv (n : nat) : ctx -> env -> Prop :=
| Renv_nil : Renv n nil empty_env
| Renv_cons : forall Γ ρ A a b,
    Renv n Γ ρ ->
    eval_exp A ρ b ->
    VT n b a ->
    Renv n (A :: Γ) (extend_env ρ a).

Lemma Renv_down : forall n Γ ρ, Renv (S n) Γ ρ -> Renv n Γ ρ.
Proof.
  intros n Γ ρ H. induction H as [| Γ ρ A a b HR IH He HVT].
  - apply Renv_nil.
  - eapply Renv_cons.
    + exact IH.
    + exact He.
    + apply VT_down1. exact HVT.
Qed.

Lemma Renv_lookup : forall Γ x A, ctx_lookup x A Γ -> forall n ρ,
  Renv n Γ ρ -> exists b, eval_exp A ρ b /\ VT n b (ρ x).
Proof.
  intros Γ x A Hlk. induction Hlk as [A0 Γ0 | n0 A0 Γ0 B Hn IH]; intros n ρ HR.
  - inversion HR; subst.
    exists b. split.
    + eapply eval_exp_sub.
      * apply eval_sub_weaken.
      * exact H2.
    + exact H4.
  - inversion HR; subst.
    destruct (IH _ _ H1) as [b' [Hb HVT]].
    exists b'. split.
    + eapply eval_exp_sub.
      * apply eval_sub_weaken.
      * exact Hb.
    + exact HVT.
Qed.


(* ============================================================ *)
(* Weakening (level shift) of normal forms / neutral forms      *)
(* ============================================================ *)

Fixpoint wk_nf (s : nat) (W : nf) {struct W} : nf :=
  match W with
  | nf_typ i => nf_typ i
  | nf_nat => nf_nat
  | nf_zero => nf_zero
  | nf_succ M => nf_succ (wk_nf s M)
  | nf_pi A B => nf_pi (wk_nf s A) (wk_nf (S s) B)
  | nf_fn A M => nf_fn (wk_nf s A) (wk_nf (S s) M)
  | nf_sigma A B => nf_sigma (wk_nf s A) (wk_nf (S s) B)
  | nf_pair M A N B => nf_pair (wk_nf s M) (wk_nf s A) (wk_nf s N) (wk_nf (S s) B)
  | nf_eq A M N => nf_eq (wk_nf s A) (wk_nf s M) (wk_nf s N)
  | nf_refl A M => nf_refl (wk_nf s A) (wk_nf s M)
  | nf_neut N => nf_neut (wk_ne s N)
  end
with wk_ne (s : nat) (N : ne) {struct N} : ne :=
  match N with
  | ne_var x => ne_var (S s - x - 1)
  | ne_app M N => ne_app (wk_ne s M) (wk_nf s N)
  | ne_fst M => ne_fst (wk_ne s M)
  | ne_snd M => ne_snd (wk_ne s M)
  | ne_natrec A MZ MS M =>
      ne_natrec (wk_nf (S s) A) (wk_nf s MZ) (wk_nf (S (S s)) MS) (wk_ne s M)
  | ne_eqrec A B BR M M' N =>
      ne_eqrec (wk_nf s A) (wk_nf (S (S (S s))) B) (wk_nf (S s) BR)
               (wk_nf s M) (wk_nf s M') (wk_ne s N)
  end.


(* ============================================================ *)
(* Decomposition of nbe_ty                                      *)
(* ============================================================ *)

Lemma nbe_ty_typ : forall Γ i W, nbe_ty Γ (a_typ i) W -> W = nf_typ i.
Proof.
  intros Γ i W H. inversion H; subst.
  match goal with Hm : eval_exp (a_typ i) ?ρ ?m |- _ =>
    let E := fresh in
    assert (E : m = d_univ i) by (inversion Hm; reflexivity); subst m
  end.
  match goal with Hr : read_typ (length Γ) (d_univ i) W |- _ => inversion Hr; reflexivity end.
Qed.

Lemma nbe_ty_nat : forall Γ W, nbe_ty Γ a_nat W -> W = nf_nat.
Proof.
  intros Γ W H. inversion H; subst.
  match goal with Hm : eval_exp a_nat ?ρ ?m |- _ =>
    let E := fresh in
    assert (E : m = d_nat) by (inversion Hm; reflexivity); subst m
  end.
  match goal with Hr : read_typ (length Γ) d_nat W |- _ => inversion Hr; reflexivity end.
Qed.

Lemma nbe_ty_pi : forall Γ A0 A1 W,
  nbe_ty Γ (a_pi A0 A1) W ->
  exists W0 W1, W = nf_pi W0 W1 /\ nbe_ty Γ A0 W0 /\ nbe_ty (A0::Γ) A1 W1.
Proof.
  intros Γ A0 A1 W H. inversion H; subst.
  inversion H1; subst.
  inversion H2; subst.
  match goal with
  | Ha : read_typ (length Γ) a ?A |- _ =>
    match goal with
    | Hb : eval_exp A1 (extend_env ρ (d_neut a (d_var (length Γ)))) ?b |- _ =>
      match goal with
      | HB : read_typ (S (length Γ)) b ?B' |- _ =>
          exists A, B'; split; [reflexivity|]; split;
          [ eapply nbe_ty_run; [exact H0 | exact H7 | exact Ha]
          | eapply nbe_ty_run;
            [ eapply initial_env_cons; [exact H0 | exact H7]
            | exact Hb | exact HB ] ]
      end
    end
  end.
Qed.

Lemma nbe_ty_sigma : forall Γ A0 A1 W,
  nbe_ty Γ (a_sigma A0 A1) W ->
  exists W0 W1, W = nf_sigma W0 W1 /\ nbe_ty Γ A0 W0 /\ nbe_ty (A0::Γ) A1 W1.
Proof.
  intros Γ A0 A1 W H. inversion H; subst.
  inversion H1; subst.
  inversion H2; subst.
  match goal with
  | Ha : read_typ (length Γ) a ?A |- _ =>
    match goal with
    | Hb : eval_exp A1 (extend_env ρ (d_neut a (d_var (length Γ)))) ?b |- _ =>
      match goal with
      | HB : read_typ (S (length Γ)) b ?B' |- _ =>
          exists A, B'; split; [reflexivity|]; split;
          [ eapply nbe_ty_run; [exact H0 | exact H7 | exact Ha]
          | eapply nbe_ty_run;
            [ eapply initial_env_cons; [exact H0 | exact H7]
            | exact Hb | exact HB ] ]
      end
    end
  end.
Qed.

Lemma nbe_ty_eq : forall Γ A0 M1 M2 W,
  nbe_ty Γ (a_eq A0 M1 M2) W ->
  exists W0 W1 W2, W = nf_eq W0 W1 W2 /\ nbe_ty Γ A0 W0 /\ nbe Γ M1 A0 W1 /\ nbe Γ M2 A0 W2.
Proof.
  intros Γ A0 M1 M2 W H. inversion H; subst.
  inversion H1; subst.
  inversion H2; subst.
  exists A, M0, M3. split; [reflexivity|]. split.
  - eapply nbe_ty_run; [exact H0 | exact H6 | exact H8].
  - split.
    + eapply nbe_run; [exact H0 | exact H6 | exact H9 | exact H12].
    + eapply nbe_run; [exact H0 | exact H6 | exact H10 | exact H13].
Qed.


Lemma nbe_ty_nbe : forall Γ M i W, nbe_ty Γ M W <-> nbe Γ M (a_typ i) W.
Proof.
  intros Γ M i W. split.
  - intros H. inversion H; subst.
    match goal with
    | He : eval_exp M ?ρ ?m |- _ =>
      match goal with Hr : read_typ (length Γ) m W |- _ =>
        eapply nbe_run;
        [ exact H0
        | constructor
        | exact He
        | eapply read_nf_type; exact Hr ]
      end
    end.
  - intros H. inversion H; subst.
    inversion H3; subst.
    all: try (exact (nbe_ty_run Γ ρ M m W H0 H2 H8)).
    all: try (match goal with He : eval_exp (a_typ _) _ _ |- _ => inversion He end).
Qed.



Lemma alg_subtyping_nf_trans : forall A B C,
  {{ ⊢anf A ⊆ B }} -> {{ ⊢anf B ⊆ C }} -> {{ ⊢anf A ⊆ C }}.
Proof.
  intros A B C H1 H2. revert C H2. induction H1; intros C' H2.
  all: inversion H2; subst.
  all: try (eapply asnf_refl; [eassumption|reflexivity]).
  all: try (eapply asnf_univ; lia).
  all: try (eapply asnf_pi; [reflexivity| ]).
  all: try (eapply asnf_sigma; [reflexivity| ]).
  all: try (match goal with IH : forall X, alg_subtyping_nf ?B' X -> alg_subtyping_nf ?B X |- _ =>
               eapply IH; eassumption end).
  all: try (exfalso; match goal with H : not_univ_pi_sigma ?X |- _ =>
    unfold not_univ_pi_sigma in H; destruct X; simpl in H; try discriminate; exact H end).
Qed.

Lemma alg_subtyping_trans : forall Γ A B C,
  alg_subtyping Γ A B -> alg_subtyping Γ B C -> alg_subtyping Γ A C.
Proof.
  intros Γ A B C H1 H2. inversion H1; subst. inversion H2; subst.
  assert (B' = A'0) by (eapply nbe_ty_det; [exact H0 | exact H4]). subst A'0.
  eapply alg_subtyp_run; [exact H | exact H5 |].
  eapply alg_subtyping_nf_trans; [exact H3 | exact H6].
Qed.


(* ============================================================ *)
(* Initial environments: variables and out-of-range values      *)
(* ============================================================ *)

Lemma initial_env_beyond : forall Γ ρ, initial_env Γ ρ ->
  forall x, length Γ <= x -> ρ x = d_zero.
Proof.
  intros Γ. induction Γ as [| A Γ IH]; intros ρ H x Hx; inversion H; subst.
  - simpl in *. reflexivity.
  - destruct x as [| x]; [simpl in Hx; lia|].
    cbn. apply (IH ρ0 H2 x). simpl in Hx. lia.
Qed.

Lemma initial_env_lookup : forall Γ ρ, initial_env Γ ρ ->
  forall x, x < length Γ ->
  exists b, ρ x = d_neut b (d_var (length Γ - x - 1)).
Proof.
  intros Γ. induction Γ as [| A Γ IH]; intros ρ H x Hx; inversion H; subst.
  - simpl in Hx; lia.
  - destruct x as [| x].
    + exists a. cbn. replace (length Γ - 0) with (length Γ) by lia. reflexivity.
    + assert (Hx' : x < length Γ) by (simpl in Hx; lia).
      destruct (IH ρ0 H2 x Hx') as [b Hb].
      exists b. cbn. rewrite Hb.
      replace (S (length Γ) - S x - 1) with (length Γ - x - 1) by lia.
      reflexivity.
Qed.


Lemma nbe_ty_var : forall Γ x W, nbe_ty Γ (a_var x) W -> W = nf_neut (ne_var x).
Proof.
  intros Γ x W H. inversion H; subst.
  match goal with H : initial_env Γ _ |- _ => rename H into Hie end.
  match goal with H : eval_exp (a_var x) _ _ |- _ => rename H into Hev end.
  match goal with H : read_typ (length Γ) _ W |- _ => rename H into Hrt end.
  inversion Hev; subst.
  destruct (Nat.lt_ge_cases x (length Γ)) as [Hlt|Hge].
  - destruct (initial_env_lookup Γ ρ Hie x Hlt) as [b Hb].
    rewrite Hb in Hrt. inversion Hrt; subst.
    match goal with Hn : read_ne (length Γ) (d_var (length Γ - x - 1)) ?B |- _ =>
      rename Hn into Hn0
    end.
    inversion Hn0; subst.
    replace (length Γ - (length Γ - x - 1) - 1) with x by lia. reflexivity.
  - rewrite (initial_env_beyond Γ ρ Hie x Hge) in Hrt. inversion Hrt.
Qed.

Lemma nbe_ty_var_run : forall Γ x, x < length Γ ->
  forall ρ, initial_env Γ ρ ->
  nbe_ty Γ (a_var x) (nf_neut (ne_var x)).
Proof.
  intros Γ x Hx ρ Hρ.
  destruct (initial_env_lookup Γ ρ Hρ x Hx) as [b Hb].
  assert (Hrt : read_typ (length Γ) (d_neut b (d_var (length Γ - x - 1)))
                  (nf_neut (ne_var x))).
  { eapply read_typ_neut.
    replace (ne_var x) with (ne_var (length Γ - (length Γ - x - 1) - 1))
      by (f_equal; lia).
    apply read_ne_var. }
  eapply nbe_ty_run.
  - exact Hρ.
  - apply eval_exp_var.
  - rewrite Hb. exact Hrt.
Qed.


Lemma wf_pi_typing_inv : forall Γ A B T,
  {{ Γ ⊢ Π A B : T }} ->
  exists i j, {{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@j }}.
Proof.
  intros Γ A B T H. remember (a_pi A B) as M eqn:E. revert A B E.
  induction H; intros A0 B0 E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - inversion E; subst. exists i, i. split; assumption.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - exact (IHwf_exp1 A0 B0 E).
Qed.

Lemma wf_sigma_typing_inv : forall Γ A B T,
  {{ Γ ⊢ Σ A B : T }} ->
  exists i j, {{ Γ ⊢ A : Type@i }} /\ {{ Γ, A ⊢ B : Type@j }}.
Proof.
  intros Γ A B T H. remember (a_sigma A B) as M eqn:E. revert A B E.
  induction H; intros A0 B0 E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - inversion E; subst. exists i, i. split; assumption.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - discriminate E.
  - exact (IHwf_exp1 A0 B0 E).
Qed.

Lemma asnf_sound : forall A B,
  {{ ⊢anf A ⊆ B }} ->
  forall Γ,
  (exists i, {{ Γ ⊢ A : Type@i }}) ->
  (exists j, {{ Γ ⊢ B : Type@j }}) ->
  {{ Γ ⊢ A ⊆ B }}.
Proof.
  intros A B H. induction H as [A A' Hn Heq | i j Hle | A B A' B' Heq Hsub IH | A B A' B' Heq Hsub IH];
    intros Γ [iu Hu] [ju Hv].
  - subst A'. apply wf_subtyp_refl' with (i := iu). exact Hu.
  - pose proof (wf_exp_ctx _ _ _ Hu) as Hwf.
    destruct (Nat.lt_ge_cases i j) as [Hlt|Hge].
    + apply wf_subtyp_univ; assumption.
    + assert (i = j) by lia. subst j.
      apply wf_subtyp_refl with (i := S i).
      * apply wf_typ. exact Hwf.
      * apply wf_exp_eq_refl. apply wf_typ. exact Hwf.
  - subst A'.
    destruct (wf_pi_typing_inv Γ A B (a_typ iu) Hu) as [i1 [i2 [HA1 HB1]]].
    destruct (wf_pi_typing_inv Γ A B' (a_typ ju) Hv) as [j1 [j2 [HA2 HB2]]].
    set (u := Nat.max (Nat.max i1 i2) (Nat.max j1 j2)).
    set (ΓA := cons (A : exp) Γ).
    assert (Hi1 : {{ Γ ⊢ A : Type@u }}) by (eapply wf_exp_cumul; [|exact HA1]; unfold u; lia).
    assert (Hj1 : {{ Γ ⊢ A : Type@u }}) by (eapply wf_exp_cumul; [|exact HA2]; unfold u; lia).
    assert (Hi2 : {{ ΓA ⊢ B : Type@u }}) by (eapply wf_exp_cumul; [|exact HB1]; unfold u; lia).
    assert (Hj2 : {{ ΓA ⊢ B' : Type@u }}) by (eapply wf_exp_cumul; [|exact HB2]; unfold u; lia).
    eapply wf_subtyp_pi.
    + exact Hi1.
    + exact Hj1.
    + apply wf_exp_eq_refl. exact Hi1.
    + exact Hi2.
    + exact Hj2.
    + apply IH with (Γ := ΓA). exists u. exact Hi2. exists u. exact Hj2.
  - subst A'.
    destruct (wf_sigma_typing_inv Γ A B (a_typ iu) Hu) as [i1 [i2 [HA1 HB1]]].
    destruct (wf_sigma_typing_inv Γ A B' (a_typ ju) Hv) as [j1 [j2 [HA2 HB2]]].
    set (u := Nat.max (Nat.max i1 i2) (Nat.max j1 j2)).
    set (ΓA := cons (A : exp) Γ).
    assert (Hi1 : {{ Γ ⊢ A : Type@u }}) by (eapply wf_exp_cumul; [|exact HA1]; unfold u; lia).
    assert (Hj1 : {{ Γ ⊢ A : Type@u }}) by (eapply wf_exp_cumul; [|exact HA2]; unfold u; lia).
    assert (Hi2 : {{ ΓA ⊢ B : Type@u }}) by (eapply wf_exp_cumul; [|exact HB1]; unfold u; lia).
    assert (Hj2 : {{ ΓA ⊢ B' : Type@u }}) by (eapply wf_exp_cumul; [|exact HB2]; unfold u; lia).
    eapply wf_subtyp_sigma.
    + exact Hi1.
    + exact Hj1.
    + apply wf_exp_eq_refl. exact Hi1.
    + exact Hi2.
    + exact Hj2.
    + apply IH with (Γ := ΓA). exists u. exact Hi2. exists u. exact Hj2.
Qed.

Lemma alg_subtyping_sound :
  (forall Γ A W i,
      nbe_ty Γ A W ->
      {{ Γ ⊢ A : Type@i }} ->
      {{ Γ ⊢ W : Type@i }} /\ {{ Γ ⊢ A ≈ W : Type@i }}) ->
  forall Γ A B,
    alg_subtyping Γ A B ->
    (exists i, {{ Γ ⊢ A : Type@i }}) ->
    (exists j, {{ Γ ⊢ B : Type@j }}) ->
    {{ Γ ⊢ A ⊆ B }}.
Proof.
  intros S Γ A B H [i HA] [j HB].
  inversion H as [Γ0 A0 B0 A' B' Hnba Hnbb Hnf]; subst.
  destruct (S Γ A A' i Hnba HA) as [HA' HeqA].
  destruct (S Γ B B' j Hnbb HB) as [HB' HeqB].
  assert (Hsub : {{ Γ ⊢ A' ⊆ B' }}).
  { eapply asnf_sound; [exact Hnf | exists i; exact HA' | exists j; exact HB']. }
  assert (HAA' : {{ Γ ⊢ A ⊆ A' }}).
  { apply wf_subtyp_refl with (i := i); assumption. }
  assert (HB'B : {{ Γ ⊢ B' ⊆ B }}).
  { apply wf_subtyp_refl with (i := j); [exact HB | apply wf_exp_eq_sym; exact HeqB]. }
  eapply wf_subtyp_trans; [exact HAA'|].
  eapply wf_subtyp_trans; [exact Hsub|exact HB'B].
Qed.

Lemma wf_ctx_eq_prefix : forall Γ A Δ A',
  {{ ⊢ Γ, A ≈ Δ, A' }} -> {{ ⊢ Γ ≈ Δ }}.
Proof.
  intros Γ A Δ A' H. inversion H; subst. assumption.
Qed.

Lemma wf_ctx_eq_ctx : forall Γ Δ, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Γ }} /\ {{ ⊢ Δ }}.
Proof.
  intros Γ Δ H. induction H as [| Γ Δ i A A' Hctx IH HA HA' HA0 HA0' Heq Heq'] using wf_ctx_eq_ind.
  - split; apply wf_ctx_empty.
  - destruct IH as [HwfΓ HwfΔ].
    split.
    + eapply wf_ctx_extend; eassumption.
    + eapply wf_ctx_extend; eassumption.
Qed.

Lemma wf_ctx_eq_extend_same : forall Γ Δ A i,
  {{ ⊢ Γ ≈ Δ }} -> {{ Γ ⊢ A : Type@i }} -> {{ Δ ⊢ A : Type@i }} ->
  {{ ⊢ Γ, A ≈ Δ, A }}.
Proof.
  intros Γ Δ A i Hctx HA HA'.
  eapply wf_ctx_eq_extend; try exact Hctx; try exact HA; try exact HA'.
  - apply wf_exp_eq_refl. exact HA.
  - apply wf_exp_eq_refl. exact HA'.
Qed.

Lemma wf_ctx_eq_lookup : forall Γ Δ, {{ ⊢ Γ ≈ Δ }} ->
  forall x A, {{ #x : A ∈ Γ }} ->
  exists A', {{ #x : A' ∈ Δ }} /\
    (exists i, {{ Δ ⊢ A : Type@i }} /\ {{ Δ ⊢ A' : Type@i }} /\
               {{ Δ ⊢ A ≈ A' : Type@i }}).
Proof.
  intros Γ Δ Hctx. induction Hctx as [| Γ0 Δ0 i A0 A0' Hpre IH HA0 HA0' HB0 HB0' HeqΓ HeqΔ] using wf_ctx_eq_ind;
    intros x A Hlk.
  - inversion Hlk.
  - destruct x as [| x].
    + (* here *) inversion Hlk; subst.
      exists (a_sub A0' a_weaken).
      split.
      * apply here.
      * (* Δ0,A0' well formed *)
        assert (HwfΔA : {{ ⊢ Δ0, A0' }}).
        { eapply wf_ctx_extend; [ | exact HB0'].
          eapply wf_exp_ctx. exact HB0'. }
        assert (HWk : {{ Δ0, A0' ⊢s Wk : Δ0 }}) by (apply wf_sub_weaken; exact HwfΔA).
        assert (HtyA : {{ Δ0, A0' ⊢ A0[Wk] : Type@i }}) by (eapply wf_subst_type; eassumption).
        assert (HtyA' : {{ Δ0, A0' ⊢ A0'[Wk] : Type@i }}) by (eapply wf_subst_type; eassumption).
        exists i. split; [exact HtyA|]. split; [exact HtyA'|].
        eapply wf_exp_eq_univ_retype with (σ := a_weaken) (Δ := Δ0);
          [ exact HWk
          | eapply wf_exp_eq_sub_cong; [exact HeqΔ | apply wf_sub_eq_refl; exact HWk] ].
    + (* there *) inversion Hlk; subst.
      destruct (IH x A1 H2) as [A' [Hlk' [j [Hty [Hty' Heq]]]]].
      exists (a_sub A' a_weaken).
      split.
      * apply there. exact Hlk'.
      * assert (HwfΔB : {{ ⊢ Δ0, A0' }}).
        { eapply wf_ctx_extend; [ | exact HB0'].
          eapply wf_exp_ctx. exact HB0'. }
        assert (HWk : {{ Δ0, A0' ⊢s Wk : Δ0 }}) by (apply wf_sub_weaken; exact HwfΔB).
        assert (HtyW : {{ Δ0, A0' ⊢ A1[Wk] : Type@j }}) by (eapply wf_subst_type; eassumption).
        assert (HtyW' : {{ Δ0, A0' ⊢ A'[Wk] : Type@j }}) by (eapply wf_subst_type; eassumption).
        exists j. split; [exact HtyW|]. split; [exact HtyW'|].
        eapply wf_exp_eq_univ_retype with (σ := a_weaken) (Δ := Δ0);
          [ exact HWk
          | eapply wf_exp_eq_sub_cong; [exact Heq | apply wf_sub_eq_refl; exact HWk] ].
Qed.

Lemma wf_exp_eq_raise_univ : forall Γ A A' i u,
  {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ A ≈ A' : Type@i }} -> i <= u ->
  {{ Γ ⊢ A ≈ A' : Type@u }}.
Proof.
  intros Γ A A' i u HA Heq Hle.
  pose proof (wf_exp_ctx _ _ _ HA) as Hwf.
  eapply wf_exp_eq_subtyp.
  - exact Heq.
  - apply wf_typ. exact Hwf.
  - apply wf_subtyp_univ_le; assumption.
Qed.

Lemma wf_natrec_zero_ty : forall Γ A i,
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Γ ⊢ A[Id,,zero] : Type@i }}.
Proof.
  intros Γ A i HA. pose proof (wf_exp_ctx _ _ _ HA) as Hwf.
  assert (HwfΓ : {{ ⊢ Γ }}) by (eapply wf_ctx_prefix; exact Hwf).
  assert (Hnat : {{ Γ ⊢ ℕ : Type@0 }}) by (apply wf_nat; exact HwfΓ).
  assert (Hzero : {{ Γ ⊢ zero : ℕ }}) by (apply wf_zero; exact HwfΓ).
  assert (Hσ : {{ Γ ⊢s (Id ,, zero) : Γ, ℕ }}) by (eapply wf_sub_extend_id_self; eassumption).
  eapply wf_subst_type; eassumption.
Qed.

Lemma wf_natrec_scrut_ty : forall Γ A M i,
  {{ Γ, ℕ ⊢ A : Type@i }} -> {{ Γ ⊢ M : ℕ }} ->
  {{ Γ ⊢ A[Id,,M] : Type@i }}.
Proof.
  intros Γ A M i HA HM.
  assert (HwfΓ : {{ ⊢ Γ }}) by (eapply wf_exp_ctx; exact HM).
  assert (Hnat : {{ Γ ⊢ ℕ : Type@0 }}) by (apply wf_nat; exact HwfΓ).
  assert (Hσ : {{ Γ ⊢s (Id ,, M) : Γ, ℕ }}) by (eapply wf_sub_extend_id_self; eassumption).
  eapply wf_subst_type; eassumption.
Qed.

Lemma wf_app_cod_ty : forall Γ A B N i,
  {{ Γ ⊢ A : Type@i }} -> {{ Γ, A ⊢ B : Type@i }} -> {{ Γ ⊢ N : A }} ->
  {{ Γ ⊢ B[Id,,N] : Type@i }}.
Proof.
  intros Γ A B N i HA HB HN.
  assert (Hσ : {{ Γ ⊢s (Id ,, N) : Γ, A }}) by (eapply wf_sub_extend_id_self; eassumption).
  eapply wf_subst_type; eassumption.
Qed.

Lemma wf_natrec_step_ty : forall Γ A i,
  {{ Γ, ℕ ⊢ A : Type@i }} ->
  {{ Γ, ℕ, A ⊢ A[Wk∘Wk,,succ #1] : Type@i }}.
Proof.
  intros Γ A i HA. pose proof (wf_exp_ctx _ _ _ HA) as HwfN.
  assert (Hctx1 : {{ ⊢ Γ, ℕ }}) by assumption.
  assert (Hctx2 : {{ ⊢ Γ, ℕ, A }}) by (eapply wf_ctx_extend; eassumption).
  assert (HWk1 : {{ Γ, ℕ ⊢s Wk : Γ }}) by (apply wf_sub_weaken; exact Hctx1).
  assert (HWk2 : {{ Γ, ℕ, A ⊢s Wk : Γ, ℕ }}) by (apply wf_sub_weaken; exact Hctx2).
  assert (HWW : {{ Γ, ℕ, A ⊢s (Wk ∘ Wk) : Γ }})
    by (eapply wf_sub_compose with (Γ2 := (a_nat :: Γ)%list); eassumption).
  (* variable #1 has (ℕ[Wk])[Wk], convert to ℕ *)
  assert (HwfΓ : {{ ⊢ Γ }}) by (eapply wf_ctx_prefix; eassumption).
  assert (Hnat : {{ Γ ⊢ ℕ : Type@0 }}) by (apply wf_nat; exact HwfΓ).
  assert (Hlk1 : {{ #1 : (ℕ[Wk])[Wk] ∈ Γ, ℕ, A }}) by (apply there; apply here).
  assert (Hv1 : {{ Γ, ℕ, A ⊢ #1 : (ℕ[Wk])[Wk] }}) by (apply wf_vlookup; eassumption).
  assert (Hcomp0 : {{ Γ, ℕ, A ⊢ ℕ[Wk∘Wk] ≈ ℕ[Wk][Wk] : (Type@0)[Wk∘Wk] }}).
  { eapply wf_exp_eq_sub_compose; eassumption. }
  assert (HcompT : {{ Γ, ℕ, A ⊢ ℕ[Wk∘Wk] ≈ ℕ[Wk][Wk] : Type@0 }}).
  { eapply wf_exp_eq_univ_retype; [exact HWW|exact Hcomp0]. }
  assert (HnatSub : {{ Γ, ℕ, A ⊢ ℕ[Wk∘Wk] ≈ ℕ : Type@0 }})
    by (eapply wf_exp_eq_nat_sub; exact HWW).
  assert (Heq1 : {{ Γ, ℕ, A ⊢ ℕ[Wk][Wk] ≈ ℕ : Type@0 }}).
  { eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; exact HcompT|exact HnatSub]. }
  assert (Hsucc : {{ Γ, ℕ, A ⊢ succ #1 : ℕ }}).
  { apply wf_succ. eapply wf_exp_conv; [exact Hv1|exact Heq1|apply wf_nat; exact Hctx2]. }
  assert (Hσ : {{ Γ, ℕ, A ⊢s (Wk ∘ Wk ,, succ #1) : Γ, ℕ }}).
  { eapply wf_sub_extend; [exact HWW|exact Hnat|].
    eapply wf_exp_conv; [exact Hsucc|apply wf_exp_eq_sym; eapply wf_exp_eq_nat_sub; exact HWW|eapply wf_subst_type; [exact HWW|exact Hnat]]. }
  eapply wf_subst_type; eassumption.
Qed.

Lemma BranchTy_proved : forall Γ A i j B,
  {{ Γ ⊢ A : Type@i }} ->
  {{ Γ, A, A[Wk], Eq (A[Wk∘Wk]) #1 #0 ⊢ B : Type@j }} ->
  {{ Γ, A ⊢ B[Id,,#0,,refl A[Wk] #0] : Type@j }}.
Proof.
  intros Γ A i j B HA HB.
  pose proof (wf_exp_ctx _ _ _ HA) as Hwf.
  assert (Hctx1 : {{ ⊢ Γ, A }}) by (eapply wf_ctx_extend; [exact Hwf|exact HA]).
  destruct (eqrec_ctx_typing Γ A i HA) as [HWWty [HMc [HNc HEqty]]].
  assert (Hctx2 : {{ ⊢ Γ, A, A[Wk] }}) by (eapply wf_exp_ctx; exact HWWty).
  assert (HWk1 : {{ Γ, A ⊢s Wk : Γ }}) by (apply wf_sub_weaken; exact Hctx1).
  assert (HWk2 : {{ Γ, A, A[Wk] ⊢s Wk : Γ, A }}) by (apply wf_sub_weaken; exact Hctx2).
  assert (HWk1_ty : {{ Γ, A ⊢ A[Wk] : Type@i }})
    by (eapply wf_subst_type; [exact HWk1|exact HA]).
  assert (HId1 : {{ Γ, A ⊢s Id : Γ, A }}) by (apply wf_sub_id; exact Hctx1).
  assert (Hlk0 : {{ #0 : A[Wk] ∈ Γ, A }}) by apply here.
  assert (Hv0 : {{ Γ, A ⊢ #0 : A[Wk] }}) by (apply wf_vlookup; eassumption).
  assert (HId0_ty : {{ Γ, A ⊢ (A[Wk])[Id] : Type@i }})
    by (eapply wf_subst_type; [exact HId1|exact HWk1_ty]).
  assert (Hid0_eq : {{ Γ, A ⊢ (A[Wk])[Id] ≈ A[Wk] : Type@i }})
    by (apply wf_exp_eq_sub_id_univ; exact HWk1_ty).
  assert (Hv0' : {{ Γ, A ⊢ #0 : (A[Wk])[Id] }}).
  { eapply wf_exp_conv; [exact Hv0|apply wf_exp_eq_sym; exact Hid0_eq|exact HId0_ty]. }
  assert (Hσ1 : {{ Γ, A ⊢s (Id ,, #0) : Γ, A, A[Wk] }})
    by (eapply wf_sub_extend; [exact HId1|exact HWk1_ty|exact Hv0']).
  assert (HQty : {{ Γ, A ⊢ (Eq (A[Wk∘Wk]) #1 #0)[Id,,#0] : Type@i }})
    by (eapply wf_subst_type; [exact Hσ1|exact HEqty]).
  assert (Hrefl : {{ Γ, A ⊢ refl A[Wk] #0 : Eq (A[Wk]) #0 #0 }})
    by (eapply wf_refl; [exact HWk1_ty|exact Hv0]).
  (* substitution composition facts *)
  assert (HWW : {{ Γ, A, A[Wk] ⊢s (Wk ∘ Wk) : Γ }})
    by (eapply wf_sub_compose with (Γ2 := (A :: Γ)%list); eassumption).
  assert (HWkWk : {{ Γ, A, A[Wk] ⊢s Wk : Γ, A }}) by exact HWk2.
  assert (Hcomp1 : {{ Γ, A, A[Wk] ⊢ A[Wk∘Wk] ≈ (A[Wk])[Wk] : (Type@i)[Wk∘Wk] }}).
  { eapply wf_exp_eq_sub_compose; [exact HWk2|exact HWk1|exact HA]. }
  assert (e1 : {{ Γ, A, A[Wk] ⊢ A[Wk∘Wk] ≈ (A[Wk])[Wk] : Type@i }}).
  { eapply wf_exp_eq_univ_retype; [exact HWW|exact Hcomp1]. }
  (* σ1-congruence *)
  assert (e2raw : {{ Γ, A ⊢ (A[Wk∘Wk])[Id,,#0] ≈ ((A[Wk])[Wk])[Id,,#0] : (Type@i)[Id,,#0] }}).
  { eapply wf_exp_eq_sub_cong; [exact e1|apply wf_sub_eq_refl; exact Hσ1]. }
  assert (e2 : {{ Γ, A ⊢ (A[Wk∘Wk])[Id,,#0] ≈ ((A[Wk])[Wk])[Id,,#0] : Type@i }}).
  { eapply wf_exp_eq_univ_retype; [exact Hσ1|exact e2raw]. }
  assert (HWkσ1 : {{ Γ, A ⊢s (Wk ∘ (Id,,#0)) : Γ, A }})
    by (eapply wf_sub_compose with (Γ2 := (a_sub A a_weaken :: A :: Γ)%list); [exact Hσ1|exact HWk2]).
  assert (e3raw : {{ Γ, A ⊢ (A[Wk])[Wk∘(Id,,#0)] ≈ ((A[Wk])[Wk])[Id,,#0] : (Type@i)[Wk∘(Id,,#0)] }}).
  { eapply wf_exp_eq_sub_compose; [exact Hσ1|exact HWk2|exact HWk1_ty]. }
  assert (e3 : {{ Γ, A ⊢ ((A[Wk])[Wk])[Id,,#0] ≈ (A[Wk])[Wk∘(Id,,#0)] : Type@i }}).
  { eapply wf_exp_eq_univ_retype; [exact HWkσ1|apply wf_exp_eq_sym; exact e3raw]. }
  assert (Hseq1 : {{ Γ, A ⊢s (Wk ∘ (Id,,#0)) ≈ Id : Γ, A }}).
  { eapply wf_sub_eq_p_extend; [exact HId1|exact HWk1_ty|exact Hv0']. }
  assert (e4 : {{ Γ, A ⊢ (A[Wk])[Wk∘(Id,,#0)] ≈ (A[Wk])[Id] : Type@i }}).
  { eapply wf_exp_eq_sub_cong_univ; [exact HWkσ1|exact HId1|exact Hseq1|exact HWk1_ty]. }
  assert (e5 : {{ Γ, A ⊢ (A[Wk])[Id] ≈ A[Wk] : Type@i }})
    by (apply wf_exp_eq_sub_id_univ; exact HWk1_ty).
  assert (Acomp : {{ Γ, A ⊢ (A[Wk∘Wk])[Id,,#0] ≈ A[Wk] : Type@i }}).
  { eapply wf_exp_eq_trans; [exact e2|].
    eapply wf_exp_eq_trans; [exact e3|].
    eapply wf_exp_eq_trans; [exact e4|exact e5]. }
  (* component equalities *)
  assert (H1s : {{ Γ, A ⊢ #1[Id,,#0] ≈ #0[Id] : (A[Wk])[Id] }}).
  { eapply wf_exp_eq_var_S_sub; [exact HId1|exact HWk1_ty|exact Hv0'|apply here]. }
  assert (H0id : {{ Γ, A ⊢ #0[Id] ≈ #0 : (A[Wk])[Id] }})
    by (apply wf_exp_eq_sub_id; exact Hv0').
  assert (H1raw : {{ Γ, A ⊢ #1[Id,,#0] ≈ #0 : (A[Wk])[Id] }})
    by (eapply wf_exp_eq_trans; [exact H1s|exact H0id]).
  assert (HT2 : {{ Γ, A ⊢ (A[Wk∘Wk])[Id,,#0] : Type@i }})
    by (eapply wf_subst_type; [exact Hσ1|exact HWWty]).
  assert (T1T2 : {{ Γ, A ⊢ (A[Wk])[Id] ≈ (A[Wk∘Wk])[Id,,#0] : Type@i }})
    by (eapply wf_exp_eq_trans; [exact e5|apply wf_exp_eq_sym; exact Acomp]).
  assert (M1comp : {{ Γ, A ⊢ #1[Id,,#0] ≈ #0 : (A[Wk∘Wk])[Id,,#0] }})
    by (eapply wf_exp_eq_conv; [exact H1raw|exact T1T2|exact HT2]).
  assert (H0sub : {{ Γ, A ⊢ #0[Id,,#0] ≈ #0 : (A[Wk])[Id] }})
    by (eapply wf_exp_eq_var_0_sub; [exact HId1|exact HWk1_ty|exact Hv0']).
  assert (M2comp : {{ Γ, A ⊢ #0[Id,,#0] ≈ #0 : (A[Wk∘Wk])[Id,,#0] }})
    by (eapply wf_exp_eq_conv; [exact H0sub|exact T1T2|exact HT2]).
  assert (Heqsub : {{ Γ, A ⊢ (Eq (A[Wk∘Wk]) #1 #0)[Id,,#0]
        ≈ Eq ((A[Wk∘Wk])[Id,,#0]) (#1[Id,,#0]) (#0[Id,,#0]) : Type@i }}).
  { eapply wf_exp_eq_eq_sub; [exact Hσ1|exact HWWty|exact HMc|exact HNc]. }
  assert (Heqcong : {{ Γ, A ⊢ Eq ((A[Wk∘Wk])[Id,,#0]) (#1[Id,,#0]) (#0[Id,,#0])
        ≈ Eq (A[Wk]) #0 #0 : Type@i }}).
  { eapply wf_exp_eq_eq_cong; [exact Acomp|exact M1comp|exact M2comp]. }
  assert (EQeq : {{ Γ, A ⊢ (Eq (A[Wk∘Wk]) #1 #0)[Id,,#0] ≈ Eq (A[Wk]) #0 #0 : Type@i }})
    by (eapply wf_exp_eq_trans; [exact Heqsub|exact Heqcong]).
  assert (HreflQ : {{ Γ, A ⊢ refl A[Wk] #0 : (Eq (A[Wk∘Wk]) #1 #0)[Id,,#0] }})
    by (eapply wf_exp_conv; [exact Hrefl|apply wf_exp_eq_sym; exact EQeq|exact HQty]).
  assert (Hσ2 : {{ Γ, A ⊢s ((Id ,, #0) ,, refl A[Wk] #0)
                     : Γ, A, A[Wk], Eq (A[Wk∘Wk]) #1 #0 }}).
  { eapply wf_sub_extend; [exact Hσ1|exact HEqty|exact HreflQ]. }
  eapply wf_subst_type; [exact Hσ2|exact HB].
Qed.

Lemma wf_ctx_eq_vlookup : forall Γ Δ, {{ ⊢ Γ ≈ Δ }} ->
  forall x A, {{ #x : A ∈ Γ }} ->
  exists A', {{ #x : A' ∈ Δ }} /\ {{ Δ ⊢ #x : A }}.
Proof.
  intros Γ Δ Hctx x A Hlk.
  destruct (wf_ctx_eq_lookup Γ Δ Hctx x A Hlk) as [A' [Hlk' [i [HA [HA' Heq]]]]].
  exists A'. split; [exact Hlk'|].
  destruct (wf_ctx_eq_ctx Γ Δ Hctx) as [HwfΓ HwfΔ].
  assert (Hv : {{ Δ ⊢ #x : A' }}) by (apply wf_vlookup; assumption).
  eapply wf_exp_conv; [exact Hv|apply wf_exp_eq_sym; exact Heq|exact HA].
Qed.

Lemma wf_ctx_eq_wf_typ : forall Γ Δ i, {{ ⊢ Γ ≈ Δ }} ->
  {{ Γ ⊢ Type@i : Type@(S i) }} -> {{ Δ ⊢ Type@i : Type@(S i) }}.
Proof.
  intros Γ Δ i Hctx H. destruct (wf_ctx_eq_ctx Γ Δ Hctx) as [HwfΓ HwfΔ].
  apply wf_typ. exact HwfΔ.
Qed.

Lemma wf_ctx_eq_wf_nat : forall Γ Δ, {{ ⊢ Γ ≈ Δ }} ->
  {{ Γ ⊢ ℕ : Type@0 }} -> {{ Δ ⊢ ℕ : Type@0 }}.
Proof.
  intros Γ Δ Hctx H. destruct (wf_ctx_eq_ctx Γ Δ Hctx) as [HwfΓ HwfΔ].
  apply wf_nat. exact HwfΔ.
Qed.

Lemma wf_ctx_eq_wf_zero : forall Γ Δ, {{ ⊢ Γ ≈ Δ }} ->
  {{ Γ ⊢ zero : ℕ }} -> {{ Δ ⊢ zero : ℕ }}.
Proof.
  intros Γ Δ Hctx H. destruct (wf_ctx_eq_ctx Γ Δ Hctx) as [HwfΓ HwfΔ].
  apply wf_zero. exact HwfΔ.
Qed.

Lemma wf_ctx_eq_ctx_sub_l : forall Γ Δ, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Γ ⊆ Δ }}.
Proof.
  intros Γ Δ H. induction H as [| Γ Δ i A A' Hpre IH HA HA' HA0 HA0' Heq Heq'] using wf_ctx_eq_ind.
  - apply wf_ctx_sub_empty.
  - eapply wf_ctx_sub_extend; [exact IH|exact HA|exact HA0'|].
    eapply wf_subtyp_of_eq; [exact Heq|exact HA'].
Qed.

Lemma wf_ctx_eq_ctx_sub_r : forall Γ Δ, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Δ ⊆ Γ }}.
Proof.
  intros Γ Δ H. apply wf_ctx_eq_ctx_sub_l. apply wf_ctx_eq_sym. exact H.
Qed.

Lemma ctx_eq_transport_all :
  (forall Γ (H : {{ ⊢ Γ }}), forall Δ, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Δ }}) /\
  (forall Γ Δ (H : {{ ⊢ Γ ⊆ Δ }}), True) /\
  (forall Γ A M (H : {{ Γ ⊢ M : A }}), forall Δ, {{ ⊢ Γ ≈ Δ }} -> {{ Δ ⊢ M : A }}) /\
  (forall Γ A M M' (H : {{ Γ ⊢ M ≈ M' : A }}), forall Δ, {{ ⊢ Γ ≈ Δ }} -> {{ Δ ⊢ M ≈ M' : A }}) /\
  (forall Γ Δ' σ (H : {{ Γ ⊢s σ : Δ' }}), forall Δ, {{ ⊢ Γ ≈ Δ }} -> {{ Δ ⊢s σ : Δ' }}) /\
  (forall Γ Δ' σ σ' (H : {{ Γ ⊢s σ ≈ σ' : Δ' }}), forall Δ, {{ ⊢ Γ ≈ Δ }} -> {{ Δ ⊢s σ ≈ σ' : Δ' }}) /\
  (forall Γ A A' (H : {{ Γ ⊢ A ⊆ A' }}), forall Δ, {{ ⊢ Γ ≈ Δ }} -> {{ Δ ⊢ A ⊆ A' }}).
Proof.
  apply (syntactic_wf_mut_ind
    (fun Γ (_ : {{ ⊢ Γ }}) => forall Δ, {{ ⊢ Γ ≈ Δ }} -> {{ ⊢ Δ }})
    (fun Γ Δ (H : {{ ⊢ Γ ⊆ Δ }}) => True)
    (fun Γ A M (_ : {{ Γ ⊢ M : A }}) => forall Δ, {{ ⊢ Γ ≈ Δ }} -> {{ Δ ⊢ M : A }})
    (fun Γ A M M' (_ : {{ Γ ⊢ M ≈ M' : A }}) => forall Δ, {{ ⊢ Γ ≈ Δ }} -> {{ Δ ⊢ M ≈ M' : A }})
    (fun Γ Δ' σ (_ : {{ Γ ⊢s σ : Δ' }}) => forall Δ, {{ ⊢ Γ ≈ Δ }} -> {{ Δ ⊢s σ : Δ' }})
    (fun Γ Δ' σ σ' (_ : {{ Γ ⊢s σ ≈ σ' : Δ' }}) => forall Δ, {{ ⊢ Γ ≈ Δ }} -> {{ Δ ⊢s σ ≈ σ' : Δ' }})
    (fun Γ A A' (_ : {{ Γ ⊢ A ⊆ A' }}) => forall Δ, {{ ⊢ Γ ≈ Δ }} -> {{ Δ ⊢ A ⊆ A' }})).
  - (* ctx empty *) intros Δ HΔ. inversion HΔ. apply wf_ctx_empty.
  - (* ctx extend *) intros Γ i A Hwf IH HA IHA Δ HΔ. inversion HΔ; subst.
    eapply wf_ctx_extend; [ eapply IH; eassumption | eassumption ].
  - (* ctx_sub empty *) intros. exact I.
  - (* ctx_sub extend *) intros. exact I.
  - (* typ *) intros Γ i Hwf IH Δ HΔ. apply wf_typ. eapply IH; eassumption.
  - (* nat *) intros Γ Hwf IH Δ HΔ. apply wf_nat. eapply IH; eassumption.
  - (* zero *) intros Γ Hwf IH Δ HΔ. apply wf_zero. eapply IH; eassumption.
  - (* succ *) intros Γ M HM IHM Δ HΔ. apply wf_succ. eapply IHM; eassumption.
  - (* natrec *) intros Γ i A MZ MS M HA IHA HMZ IHMZ HMS IHMS HM IHM Δ HΔ.
    destruct (wf_ctx_eq_ctx Γ Δ HΔ) as [HwfΓ HwfΔ].
    assert (HnatΓ : {{ Γ ⊢ ℕ : Type@0 }}) by (apply wf_nat; exact HwfΓ).
    assert (HnatΔ : {{ Δ ⊢ ℕ : Type@0 }}) by (apply wf_nat; exact HwfΔ).
    assert (HctxN : {{ ⊢ Γ, ℕ ≈ Δ, ℕ }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    pose proof (IHA _ HctxN) as HAΔ.
    assert (HctxNA : {{ ⊢ Γ, ℕ, A ≈ Δ, ℕ, A }})
      by (eapply wf_ctx_eq_extend_same; [exact HctxN|exact HA|exact HAΔ]).
    pose proof (IHMZ _ HΔ) as HMZΔ.
    pose proof (IHMS _ HctxNA) as HMSΔ.
    pose proof (IHM _ HΔ) as HMΔ.
    eapply wf_natrec; eassumption.
  - (* pi *) intros Γ i A B HA IHA HB IHB Δ HΔ.
    destruct (wf_ctx_eq_ctx Γ Δ HΔ) as [HwfΓ HwfΔ].
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    pose proof (IHB _ HctxA) as HBΔ.
    eapply wf_pi; eassumption.
  - (* fn *) intros Γ i A B M HA IHA HM IHM Δ HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    pose proof (IHM _ HctxA) as HMΔ.
    eapply wf_fn; eassumption.
  - (* app *) intros Γ i A B M N HA IHA HB IHB HM IHM HN IHN Δ HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    pose proof (IHB _ HctxA) as HBΔ.
    pose proof (IHM _ HΔ) as HMΔ.
    pose proof (IHN _ HΔ) as HNΔ.
    eapply wf_app; eassumption.
  - (* sigma *) intros Γ i A B HA IHA HB IHB Δ HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    pose proof (IHB _ HctxA) as HBΔ.
    eapply wf_sigma; eassumption.
  - (* pair *) intros Γ i A B M N HA IHA HB IHB HM IHM HN IHN Δ HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    pose proof (IHB _ HctxA) as HBΔ.
    pose proof (IHM _ HΔ) as HMΔ.
    pose proof (IHN _ HΔ) as HNΔ.
    eapply wf_pair; eassumption.
  - (* fst *) intros Γ i A B M HA IHA HB IHB HM IHM Δ HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    pose proof (IHB _ HctxA) as HBΔ.
    pose proof (IHM _ HΔ) as HMΔ.
    eapply wf_fst; eassumption.
  - (* snd *) intros Γ i A B M HA IHA HB IHB HM IHM Δ HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    pose proof (IHB _ HctxA) as HBΔ.
    pose proof (IHM _ HΔ) as HMΔ.
    eapply wf_snd; eassumption.
  - (* vlookup *) intros Γ x A Hwf IH Hlk Δ HΔ.
    destruct (wf_ctx_eq_vlookup Γ Δ HΔ x A Hlk) as [A' [Hlk' Htyp]].
    exact Htyp.
  - (* eq *) intros Γ i A M N HA IHA HM IHM HN IHN Δ HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    pose proof (IHM _ HΔ) as HMΔ.
    pose proof (IHN _ HΔ) as HNΔ.
    eapply wf_eq; eassumption.
  - (* refl *) intros Γ i A M HA IHA HM IHM Δ HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    pose proof (IHM _ HΔ) as HMΔ.
    eapply wf_refl; eassumption.
  - (* eqrec *) intros Γ i A M1 M2 j B BR N HA IHA HM1 IHM1 HM2 IHM2 HB IHB HBR IHBR HN IHN Δ HΔ.
    destruct (wf_ctx_eq_ctx Γ Δ HΔ) as [HwfΓ HwfΔ].
    pose proof (IHA _ HΔ) as HAΔ.
    pose proof (IHM1 _ HΔ) as HM1Δ.
    pose proof (IHM2 _ HΔ) as HM2Δ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    pose proof (IHBR _ HctxA) as HBRΔ.
    destruct (wf_ctx_eq_ctx (A :: Γ) (A :: Δ) HctxA) as [HwfΓA HwfΔA].
    assert (HAwkΓ : {{ Γ, A ⊢ A[Wk] : Type@i }}).
    { eapply wf_subst_type; [apply wf_sub_weaken; exact HwfΓA|exact HA]. }
    assert (HAwkΔ : {{ Δ, A ⊢ A[Wk] : Type@i }}).
    { eapply wf_subst_type; [apply wf_sub_weaken; exact HwfΔA|exact HAΔ]. }
    assert (Hctx2 : {{ ⊢ Γ, A, A[Wk] ≈ Δ, A, A[Wk] }})
      by (eapply wf_ctx_eq_extend_same; eassumption).
    destruct (eqrec_ctx_typing Γ A i HA) as [_ [_ [_ HEqΓ]]].
    destruct (eqrec_ctx_typing Δ A i HAΔ) as [_ [_ [_ HEqΔ]]].
    assert (HctxE : {{ ⊢ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ≈ Δ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }})
      by (eapply wf_ctx_eq_extend_same; eassumption).
    pose proof (IHB _ HctxE) as HBΔ.
    pose proof (IHN _ HΔ) as HNΔ.
    eapply wf_eqrec; eassumption.
  - (* exp_sub *) intros Γ Δ0 σ A M Hσ IHσ HM IHM Δ HΔ.
    pose proof (IHσ _ HΔ) as HσΔ.
    eapply wf_exp_sub; eassumption.
  - (* exp_subtyp *) intros Γ A M i A' HM IHM HA' IHA' Hsub IHsub Δ HΔ.
    pose proof (IHM _ HΔ) as HMΔ.
    pose proof (IHA' _ HΔ) as HA'Δ.
    pose proof (IHsub _ HΔ) as HsubΔ.
    eapply wf_exp_subtyp; eassumption.
  - (* exp_eq typ_sub *) intros Γ Δ σ i Hσ IHσ Δ0 HΔ. eapply wf_exp_eq_typ_sub. eapply IHσ; exact HΔ.
  - (* nat_sub *) intros Γ Δ σ Hσ IHσ Δ0 HΔ. eapply wf_exp_eq_nat_sub. eapply IHσ; exact HΔ.
  - (* zero_sub *) intros Γ Δ σ Hσ IHσ Δ0 HΔ. eapply wf_exp_eq_zero_sub. eapply IHσ; exact HΔ.
  - (* succ_sub *) intros Γ Δ σ M Hσ IHσ HM IHM Δ0 HΔ.
    eapply wf_exp_eq_succ_sub; [eapply IHσ; exact HΔ|exact HM].
  - (* succ_cong *) intros Γ M M' HM IHM Δ0 HΔ.
    eapply wf_exp_eq_succ_cong; eapply IHM; exact HΔ.
  - (* natrec_cong *) intros Γ i A A' MZ MZ' MS MS' M M' HA IHA HAeq IHAeq HMZ IHMZ HMSeq IHMSeq HM IHM Δ0 HΔ.
    destruct (wf_ctx_eq_ctx Γ Δ0 HΔ) as [HwfΓ HwfΔ].
    assert (HnatΓ : {{ Γ ⊢ ℕ : Type@0 }}) by (apply wf_nat; exact HwfΓ).
    assert (HnatΔ : {{ Δ0 ⊢ ℕ : Type@0 }}) by (apply wf_nat; exact HwfΔ).
    assert (HctxN : {{ ⊢ Γ, ℕ ≈ Δ0, ℕ }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    pose proof (IHA _ HctxN) as HAΔ.
    assert (HctxNA : {{ ⊢ Γ, ℕ, A ≈ Δ0, ℕ, A }})
      by (eapply wf_ctx_eq_extend_same; [exact HctxN|exact HA|exact HAΔ]).
    eapply wf_exp_eq_natrec_cong;
      [ eapply IHA; exact HctxN
      | eapply IHAeq; exact HctxN
      | eapply IHMZ; exact HΔ
      | eapply IHMSeq; exact HctxNA
      | eapply IHM; exact HΔ ].
  - (* natrec_sub *) intros Γ Δ σ i A MZ MS M Hσ IHσ HA IHA HMZ IHMZ HMS IHMS HM IHM Δ0 HΔ.
    eapply wf_exp_eq_natrec_sub; [eapply IHσ; exact HΔ|exact HA|exact HMZ|exact HMS|exact HM].
  - (* nat_beta_zero *) intros Γ i A MZ MS HA IHA HMZ IHMZ HMS IHMS Δ0 HΔ.
    destruct (wf_ctx_eq_ctx Γ Δ0 HΔ) as [HwfΓ HwfΔ].
    assert (HnatΓ : {{ Γ ⊢ ℕ : Type@0 }}) by (apply wf_nat; exact HwfΓ).
    assert (HnatΔ : {{ Δ0 ⊢ ℕ : Type@0 }}) by (apply wf_nat; exact HwfΔ).
    assert (HctxN : {{ ⊢ Γ, ℕ ≈ Δ0, ℕ }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    pose proof (IHA _ HctxN) as HAΔ.
    assert (HctxNA : {{ ⊢ Γ, ℕ, A ≈ Δ0, ℕ, A }})
      by (eapply wf_ctx_eq_extend_same; [exact HctxN|exact HA|exact HAΔ]).
    eapply wf_exp_eq_nat_beta_zero;
      [ eapply IHA; exact HctxN
      | eapply IHMZ; exact HΔ
      | eapply IHMS; exact HctxNA ].
  - (* nat_beta_succ *) intros Γ i A MZ MS M HA IHA HMZ IHMZ HMS IHMS HM IHM Δ0 HΔ.
    destruct (wf_ctx_eq_ctx Γ Δ0 HΔ) as [HwfΓ HwfΔ].
    assert (HnatΓ : {{ Γ ⊢ ℕ : Type@0 }}) by (apply wf_nat; exact HwfΓ).
    assert (HnatΔ : {{ Δ0 ⊢ ℕ : Type@0 }}) by (apply wf_nat; exact HwfΔ).
    assert (HctxN : {{ ⊢ Γ, ℕ ≈ Δ0, ℕ }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    pose proof (IHA _ HctxN) as HAΔ.
    assert (HctxNA : {{ ⊢ Γ, ℕ, A ≈ Δ0, ℕ, A }})
      by (eapply wf_ctx_eq_extend_same; [exact HctxN|exact HA|exact HAΔ]).
    eapply wf_exp_eq_nat_beta_succ;
      [ eapply IHA; exact HctxN
      | eapply IHMZ; exact HΔ
      | eapply IHMS; exact HctxNA
      | eapply IHM; exact HΔ ].
  - (* pi_sub *) intros Γ Δ σ i A B Hσ IHσ HA IHA HB IHB Δ0 HΔ.
    eapply wf_exp_eq_pi_sub; [eapply IHσ; exact HΔ|exact HA|exact HB].
  - (* pi_cong *) intros Γ i A A' B B' HA IHA HAeq IHAeq HBeq IHBeq Δ0 HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ0, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    eapply wf_exp_eq_pi_cong;
      [ eapply IHA; exact HΔ
      | eapply IHAeq; exact HΔ
      | eapply IHBeq; exact HctxA ].
  - (* fn_cong *) intros Γ i A A' B M M' HA IHA HAeq IHAeq HMeq IHMeq Δ0 HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ0, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    eapply wf_exp_eq_fn_cong;
      [ eapply IHA; exact HΔ
      | eapply IHAeq; exact HΔ
      | eapply IHMeq; exact HctxA ].
  - (* fn_sub *) intros Γ Δ σ i A B M Hσ IHσ HA IHA HM IHM Δ0 HΔ.
    eapply wf_exp_eq_fn_sub; [eapply IHσ; exact HΔ|exact HA|exact HM].
  - (* app_cong *) intros Γ i A B M M' N N' HA IHA HB IHB HMeq IHMeq HNeq IHNeq Δ0 HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ0, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    eapply wf_exp_eq_app_cong;
      [ eapply IHA; exact HΔ
      | eapply IHB; exact HctxA
      | eapply IHMeq; exact HΔ
      | eapply IHNeq; exact HΔ ].
  - (* app_sub *) intros Γ Δ σ i A B M N Hσ IHσ HA IHA HB IHB HM IHM HN IHN Δ0 HΔ.
    eapply wf_exp_eq_app_sub; [eapply IHσ; exact HΔ|exact HA|exact HB|exact HM|exact HN].
  - (* pi_beta *) intros Γ i A B M N HA IHA HB IHB HM IHM HN IHN Δ0 HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ0, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    eapply wf_exp_eq_pi_beta;
      [ eapply IHA; exact HΔ
      | eapply IHB; exact HctxA
      | eapply IHM; exact HctxA
      | eapply IHN; exact HΔ ].
  - (* pi_eta *) intros Γ i A B M HA IHA HB IHB HM IHM Δ0 HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ0, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    eapply wf_exp_eq_pi_eta;
      [ eapply IHA; exact HΔ
      | eapply IHB; exact HctxA
      | eapply IHM; exact HΔ ].
  - (* sigma_sub *) intros Γ Δ σ i A B Hσ IHσ HA IHA HB IHB Δ0 HΔ.
    eapply wf_exp_eq_sigma_sub; [eapply IHσ; exact HΔ|exact HA|exact HB].
  - (* sigma_cong *) intros Γ i A A' B B' HA IHA HAeq IHAeq HBeq IHBeq Δ0 HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ0, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    eapply wf_exp_eq_sigma_cong;
      [ eapply IHA; exact HΔ
      | eapply IHAeq; exact HΔ
      | eapply IHBeq; exact HctxA ].
  - (* pair_cong *) intros Γ i A A' B B' M M' N N' HA IHA HAeq IHAeq HBeq IHBeq HMeq IHMeq HNeq IHNeq Δ0 HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ0, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    eapply wf_exp_eq_pair_cong;
      [ eapply IHA; exact HΔ
      | eapply IHAeq; exact HΔ
      | eapply IHBeq; exact HctxA
      | eapply IHMeq; exact HΔ
      | eapply IHNeq; exact HΔ ].
  - (* pair_sub *) intros Γ Δ σ i A B M N Hσ IHσ HA IHA HB IHB HM IHM HN IHN Δ0 HΔ.
    eapply wf_exp_eq_pair_sub; [eapply IHσ; exact HΔ|exact HA|exact HB|exact HM|exact HN].
  - (* fst_cong *) intros Γ i A B M M' HA IHA HB IHB HMeq IHMeq Δ0 HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ0, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    eapply wf_exp_eq_fst_cong;
      [ eapply IHA; exact HΔ
      | eapply IHB; exact HctxA
      | eapply IHMeq; exact HΔ ].
  - (* fst_sub *) intros Γ Δ σ i A B M Hσ IHσ HA IHA HB IHB HM IHM Δ0 HΔ.
    eapply wf_exp_eq_fst_sub; [eapply IHσ; exact HΔ|exact HA|exact HB|exact HM].
  - (* snd_cong *) intros Γ i A B M M' HA IHA HB IHB HMeq IHMeq Δ0 HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ0, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    eapply wf_exp_eq_snd_cong;
      [ eapply IHA; exact HΔ
      | eapply IHB; exact HctxA
      | eapply IHMeq; exact HΔ ].
  - (* snd_sub *) intros Γ Δ σ i A B M Hσ IHσ HA IHA HB IHB HM IHM Δ0 HΔ.
    eapply wf_exp_eq_snd_sub; [eapply IHσ; exact HΔ|exact HA|exact HB|exact HM].
  - (* fst_beta *) intros Γ i A B M N HA IHA HB IHB HM IHM HN IHN Δ0 HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ0, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    eapply wf_exp_eq_fst_beta;
      [ eapply IHA; exact HΔ
      | eapply IHB; exact HctxA
      | eapply IHM; exact HΔ
      | eapply IHN; exact HΔ ].
  - (* snd_beta *) intros Γ i A B M N HA IHA HB IHB HM IHM HN IHN Δ0 HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ0, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    eapply wf_exp_eq_snd_beta;
      [ eapply IHA; exact HΔ
      | eapply IHB; exact HctxA
      | eapply IHM; exact HΔ
      | eapply IHN; exact HΔ ].
  - (* sigma_eta *) intros Γ i A B M HA IHA HB IHB HM IHM Δ0 HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ0, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    eapply wf_exp_eq_sigma_eta;
      [ eapply IHA; exact HΔ
      | eapply IHB; exact HctxA
      | eapply IHM; exact HΔ ].
  - (* eq_sub *) intros Γ Δ σ i A M N Hσ IHσ HA IHA HM IHM HN IHN Δ0 HΔ.
    eapply wf_exp_eq_eq_sub; [eapply IHσ; exact HΔ|exact HA|exact HM|exact HN].
  - (* refl_sub *) intros Γ Δ σ i A M Hσ IHσ HA IHA HM IHM Δ0 HΔ.
    eapply wf_exp_eq_refl_sub; [eapply IHσ; exact HΔ|exact HA|exact HM].
  - (* eqrec_sub *) intros Γ Δ σ i A M1 M2 j B BR N Hσ IHσ HA IHA HM1 IHM1 HM2 IHM2 HB IHB HBR IHBR HN IHN Δ0 HΔ.
    eapply wf_exp_eq_eqrec_sub; [eapply IHσ; exact HΔ|exact HA|exact HM1|exact HM2|exact HB|exact HBR|exact HN].
  - (* eq_cong *) intros Γ i A A' M M' N N' HAeq IHAeq HMeq IHMeq HNeq IHNeq Δ0 HΔ.
    eapply wf_exp_eq_eq_cong;
      [ eapply IHAeq; exact HΔ
      | eapply IHMeq; exact HΔ
      | eapply IHNeq; exact HΔ ].
  - (* refl_cong *) intros Γ i A A' M M' HAeq IHAeq HMeq IHMeq Δ0 HΔ.
    eapply wf_exp_eq_refl_cong;
      [ eapply IHAeq; exact HΔ
      | eapply IHMeq; exact HΔ ].
  - (* eqrec_cong *) intros Γ i A M1 M2 j B BR N A' M1' M2' B' BR' N' HA IHA HM1 IHM1 HM2 IHM2 HAeq IHAeq HM1eq IHM1eq HM2eq IHM2eq HBeq IHBeq HBReq IHBReq HNeq IHNeq Δ0 HΔ.
    destruct (wf_ctx_eq_ctx Γ Δ0 HΔ) as [HwfΓ HwfΔ].
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ0, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    destruct (wf_ctx_eq_ctx (A :: Γ) (A :: Δ0) HctxA) as [HwfΓA HwfΔA].
    assert (HAwkΓ : {{ Γ, A ⊢ A[Wk] : Type@i }}).
    { eapply wf_subst_type; [apply wf_sub_weaken; exact HwfΓA|exact HA]. }
    assert (HAwkΔ : {{ Δ0, A ⊢ A[Wk] : Type@i }}).
    { eapply wf_subst_type; [apply wf_sub_weaken; exact HwfΔA|exact HAΔ]. }
    assert (Hctx2 : {{ ⊢ Γ, A, A[Wk] ≈ Δ0, A, A[Wk] }})
      by (eapply wf_ctx_eq_extend_same; eassumption).
    destruct (eqrec_ctx_typing Γ A i HA) as [_ [_ [_ HEqΓ]]].
    destruct (eqrec_ctx_typing Δ0 A i HAΔ) as [_ [_ [_ HEqΔ]]].
    assert (HctxE : {{ ⊢ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ≈ Δ0, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }})
      by (eapply wf_ctx_eq_extend_same; eassumption).
    eapply wf_exp_eq_eqrec_cong;
      [ eapply IHA; exact HΔ
      | eapply IHM1; exact HΔ
      | eapply IHM2; exact HΔ
      | eapply IHAeq; exact HΔ
      | eapply IHM1eq; exact HΔ
      | eapply IHM2eq; exact HΔ
      | eapply IHBeq; exact HctxE
      | eapply IHBReq; exact HctxA
      | eapply IHNeq; exact HΔ ].
  - (* eqrec_beta *) intros Γ i A M j B BR HA IHA HM IHM HB IHB HBR IHBR Δ0 HΔ.
    destruct (wf_ctx_eq_ctx Γ Δ0 HΔ) as [HwfΓ HwfΔ].
    pose proof (IHA _ HΔ) as HAΔ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ0, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    destruct (wf_ctx_eq_ctx (A :: Γ) (A :: Δ0) HctxA) as [HwfΓA HwfΔA].
    assert (HAwkΓ : {{ Γ, A ⊢ A[Wk] : Type@i }}).
    { eapply wf_subst_type; [apply wf_sub_weaken; exact HwfΓA|exact HA]. }
    assert (HAwkΔ : {{ Δ0, A ⊢ A[Wk] : Type@i }}).
    { eapply wf_subst_type; [apply wf_sub_weaken; exact HwfΔA|exact HAΔ]. }
    assert (Hctx2 : {{ ⊢ Γ, A, A[Wk] ≈ Δ0, A, A[Wk] }})
      by (eapply wf_ctx_eq_extend_same; eassumption).
    destruct (eqrec_ctx_typing Γ A i HA) as [_ [_ [_ HEqΓ]]].
    destruct (eqrec_ctx_typing Δ0 A i HAΔ) as [_ [_ [_ HEqΔ]]].
    assert (HctxE : {{ ⊢ Γ, A, A[Wk], Eq A[Wk∘Wk] #1 #0 ≈ Δ0, A, A[Wk], Eq A[Wk∘Wk] #1 #0 }})
      by (eapply wf_ctx_eq_extend_same; eassumption).
    eapply wf_exp_eq_eqrec_beta;
      [ eapply IHA; exact HΔ
      | eapply IHM; exact HΔ
      | eapply IHB; exact HctxE
      | eapply IHBR; exact HctxA ].
  - (* exp_eq var *) intros Γ x A Hwf IH Hlk Δ0 HΔ.
    destruct (wf_ctx_eq_vlookup Γ Δ0 HΔ x A Hlk) as [A' [Hlk' Htyp]].
    apply wf_exp_eq_refl. exact Htyp.
  - (* var_0_sub *) intros Γ Δ σ i A M Hσ IHσ HA IHA HM IHM Δ0 HΔ.
    eapply wf_exp_eq_var_0_sub; [eapply IHσ; exact HΔ|exact HA|eapply IHM; exact HΔ].
  - (* var_S_sub *) intros Γ Δ σ i A M x B Hσ IHσ HA IHA HM IHM Hlk Δ0 HΔ.
    eapply wf_exp_eq_var_S_sub; [eapply IHσ; exact HΔ|exact HA|eapply IHM; exact HΔ|exact Hlk].
  - (* var_weaken *) intros B Γ x A HwfB IH Hlk Δ0 HΔ.
    destruct Δ0 as [| A' Δ0'].
    + inversion HΔ.
    + inversion HΔ as [| Γ0 Δ0 i0 A0 A0' Hpre HA0 HA0' HA00 HA00' Heq Heq']; subst.
      destruct (wf_ctx_eq_lookup Γ Δ0' Hpre x A Hlk) as [A'' [Hlk' [i [HAt [HA't HeqA]]]]].
      destruct (wf_ctx_eq_ctx Γ Δ0' Hpre) as [HwfΓ HwfΔ].
      assert (HwfΔA : {{ ⊢ Δ0', A' }})
        by (eapply wf_ctx_extend; [exact HwfΔ|exact HA00']).
      assert (HWk : {{ Δ0', A' ⊢s Wk : Δ0' }}) by (apply wf_sub_weaken; exact HwfΔA).
      assert (HeqW : {{ Δ0', A' ⊢ A''[Wk] ≈ A[Wk] : Type@i }}).
      { eapply wf_exp_eq_univ_retype with (σ := a_weaken) (Δ := Δ0').
        - exact HWk.
        - eapply wf_exp_eq_sub_cong; [apply wf_exp_eq_sym; exact HeqA|apply wf_sub_eq_refl; exact HWk]. }
      assert (HtyW : {{ Δ0', A' ⊢ A[Wk] : Type@i }}) by (eapply wf_subst_type; [exact HWk|exact HAt]).
      assert (HvarEq : {{ Δ0', A' ⊢ #x[Wk] ≈ #(S x) : A''[Wk] }})
        by (eapply wf_exp_eq_var_weaken; [exact HwfΔA|exact Hlk']).
      eapply wf_exp_eq_conv; [exact HvarEq|exact HeqW|exact HtyW].
  - (* sub_cong *) intros Δ Γ A M M' σ σ' HMeq IHMeq Hseq IHseq Δ0 HΔ.
    eapply wf_exp_eq_sub_cong; [exact HMeq|eapply IHseq; exact HΔ].
  - (* sub_id *) intros Γ A M HM IHM Δ0 HΔ.
    eapply wf_exp_eq_sub_id. eapply IHM; exact HΔ.
  - (* sub_compose *) intros Γ Γ' Γ'' τ σ A M Hτ IHτ Hσ IHσ HM IHM Δ0 HΔ.
    eapply wf_exp_eq_sub_compose; [eapply IHτ; exact HΔ|exact Hσ|exact HM].
  - (* subtyp *) intros Γ A M M' i A' HMeq IHMeq HA' IHA' Hsub IHsub Δ0 HΔ.
    eapply wf_exp_eq_subtyp; [eapply IHMeq; exact HΔ|eapply IHA'; exact HΔ|eapply IHsub; exact HΔ].
  - (* sym *) intros Γ A M M' HMeq IHMeq Δ0 HΔ.
    apply wf_exp_eq_sym. eapply IHMeq; exact HΔ.
  - (* trans *) intros Γ A M M' M'' HMeq IHMeq HMeq' IHMeq' Δ0 HΔ.
    eapply wf_exp_eq_trans; [eapply IHMeq; exact HΔ|eapply IHMeq'; exact HΔ].
  - (* sub_id *) intros Γ Hwf IH Δ0 HΔ.
    destruct (wf_ctx_eq_ctx Γ Δ0 HΔ) as [HwfΓ HwfΔ].
    assert (Hctxsub : {{ ⊢ Δ0 ⊆ Γ }}) by (apply wf_ctx_eq_ctx_sub_r; exact HΔ).
    assert (Hid : {{ Δ0 ⊢s Id : Δ0 }}) by (apply wf_sub_id; exact HwfΔ).
    eapply wf_sub_subtyp; [exact Hid|exact HwfΓ|exact Hctxsub].
  - (* sub_weaken *) intros A Γ HwfA IH Δ0 HΔ.
    destruct Δ0 as [| B Δ0'].
    + inversion HΔ.
    + inversion HΔ as [| Γ0 Δ0 i0 A0 A0' Hpre HA0 HA0' HA00 HA00' Heq Heq']; subst.
      assert (HwfΔ : {{ ⊢ Δ0', B }}) by (eapply wf_ctx_extend; [ eapply wf_ctx_eq_ctx; exact Hpre | exact HA00']).
      assert (HWk : {{ Δ0', B ⊢s Wk : Δ0' }}) by (apply wf_sub_weaken; exact HwfΔ).
      assert (Hctxsub : {{ ⊢ Δ0' ⊆ Γ }}) by (apply wf_ctx_eq_ctx_sub_r; exact Hpre).
      assert (HwfΓ : {{ ⊢ Γ }}) by (destruct (wf_ctx_eq_ctx Γ Δ0' Hpre) as [H _]; exact H).
      eapply wf_sub_subtyp; [exact HWk|exact HwfΓ|exact Hctxsub].
  - (* sub_compose *) intros Γ1 Γ2 σ2 Γ3 σ1 Hσ2 IHσ2 Hσ1 IHσ1 Δ0 HΔ.
    eapply wf_sub_compose; [eapply IHσ2; exact HΔ|exact Hσ1].
  - (* sub_extend *) intros Γ Δ σ i A M Hσ IHσ HA IHA HM IHM Δ0 HΔ.
    eapply wf_sub_extend; [eapply IHσ; exact HΔ|exact HA|eapply IHM; exact HΔ].
  - (* sub_subtyp *) intros Γ Δ σ Δ' Hσ IHσ HwfΔ' IHwf Hsub IHsub Δ0 HΔ.
    eapply wf_sub_subtyp; [eapply IHσ; exact HΔ|exact HwfΔ'|exact Hsub].
  - (* sub_eq_id *) intros Γ Hwf IH Δ0 HΔ.
    destruct (wf_ctx_eq_ctx Γ Δ0 HΔ) as [HwfΓ HwfΔ].
    assert (Hctxsub : {{ ⊢ Δ0 ⊆ Γ }}) by (apply wf_ctx_eq_ctx_sub_r; exact HΔ).
    assert (Hid : {{ Δ0 ⊢s Id ≈ Id : Δ0 }}) by (apply wf_sub_eq_id; exact HwfΔ).
    eapply wf_sub_eq_subtyp; [exact Hid|exact HwfΓ|exact Hctxsub].
  - (* sub_eq_weaken *) intros A Γ HwfA IH Δ0 HΔ.
    destruct Δ0 as [| B Δ0'].
    + inversion HΔ.
    + inversion HΔ as [| Γ0 Δ0 i0 A0 A0' Hpre HA0 HA0' HA00 HA00' Heq Heq']; subst.
      assert (HwfΔ : {{ ⊢ Δ0', B }}) by (eapply wf_ctx_extend; [ eapply wf_ctx_eq_ctx; exact Hpre | exact HA00']).
      assert (HWk : {{ Δ0', B ⊢s Wk ≈ Wk : Δ0' }}) by (apply wf_sub_eq_weaken; exact HwfΔ).
      assert (Hctxsub : {{ ⊢ Δ0' ⊆ Γ }}) by (apply wf_ctx_eq_ctx_sub_r; exact Hpre).
      assert (HwfΓ : {{ ⊢ Γ }}) by (destruct (wf_ctx_eq_ctx Γ Δ0' Hpre) as [H _]; exact H).
      eapply wf_sub_eq_subtyp; [exact HWk|exact HwfΓ|exact Hctxsub].
  - (* sub_eq_compose_cong *) intros Γ Γ' τ τ' Γ'' σ σ' Hτ IHτ Hσ IHσ Δ0 HΔ.
    eapply wf_sub_eq_compose_cong; [eapply IHτ; exact HΔ|exact Hσ].
  - (* sub_eq_extend_cong *) intros Γ Δ σ σ' i A M M' Hseq IHseq HA IHA HMeq IHMeq Δ0 HΔ.
    eapply wf_sub_eq_extend_cong; [eapply IHseq; exact HΔ|exact HA|eapply IHMeq; exact HΔ].
  - (* sub_eq_id_compose_right *) intros Γ Δ σ Hσ IHσ Δ0 HΔ.
    eapply wf_sub_eq_id_compose_right; eapply IHσ; exact HΔ.
  - (* sub_eq_id_compose_left *) intros Γ Δ σ Hσ IHσ Δ0 HΔ.
    eapply wf_sub_eq_id_compose_left; eapply IHσ; exact HΔ.
  - (* sub_eq_compose_assoc *) intros Γ' Γ σ Γ'' σ' Γ''' σ'' Hσ IHσ Hσ' IHσ' Hσ'' IHσ'' Δ0 HΔ.
    eapply wf_sub_eq_compose_assoc; [exact Hσ|exact Hσ'|eapply IHσ''; exact HΔ].
  - (* sub_eq_extend_compose *) intros Γ' Γ'' σ i A M Γ τ Hσ IHσ HA IHA HM IHM Hτ IHτ Δ0 HΔ.
    eapply wf_sub_eq_extend_compose; [exact Hσ|exact HA|exact HM|eapply IHτ; exact HΔ].
  - (* sub_eq_p_extend *) intros Γ' Γ σ i A M Hσ IHσ HA IHA HM IHM Δ0 HΔ.
    eapply wf_sub_eq_p_extend; [eapply IHσ; exact HΔ|exact HA|eapply IHM; exact HΔ].
  - (* sub_eq_extend *) intros Γ' A Γ σ Hσ IHσ Δ0 HΔ.
    eapply wf_sub_eq_extend; eapply IHσ; exact HΔ.
  - (* sub_eq_sym *) intros Γ Δ σ σ' Hseq IHseq Δ0 HΔ.
    apply wf_sub_eq_sym. eapply IHseq; exact HΔ.
  - (* sub_eq_trans *) intros Γ Δ σ σ' σ'' Hseq IHseq Hseq' IHseq' Δ0 HΔ.
    eapply wf_sub_eq_trans; [eapply IHseq; exact HΔ|eapply IHseq'; exact HΔ].
  - (* sub_eq_subtyp *) intros Γ Δ σ σ' Δ' Hseq IHseq HwfΔ' IHwf Hsub IHsub Δ0 HΔ.
    eapply wf_sub_eq_subtyp; [eapply IHseq; exact HΔ|exact HwfΔ'|exact Hsub].
  - (* subtyp_refl *) intros Γ i M' M HM' IHM' HMeq IHMeq Δ0 HΔ.
    eapply wf_subtyp_refl; [eapply IHM'; exact HΔ|eapply IHMeq; exact HΔ].
  - (* subtyp_trans *) intros Γ M M' M'' Hsub IHsub Hsub' IHsub' Δ0 HΔ.
    eapply wf_subtyp_trans; [eapply IHsub; exact HΔ|eapply IHsub'; exact HΔ].
  - (* subtyp_univ *) intros Γ i j Hwf IH Hlt Δ0 HΔ.
    eapply wf_subtyp_univ; [eapply IH; exact HΔ|exact Hlt].
  - (* subtyp_pi *) intros Γ i A A' B B' HA IHA HA' IHA' HAeq IHAeq HB IHB HB' IHB' Hsub IHsub Δ0 HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    pose proof (IHA' _ HΔ) as HA'Δ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ0, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    assert (HctxA' : {{ ⊢ Γ, A' ≈ Δ0, A' }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    eapply wf_subtyp_pi;
      [ eapply IHA; exact HΔ
      | eapply IHA'; exact HΔ
      | eapply IHAeq; exact HΔ
      | eapply IHB; exact HctxA
      | eapply IHB'; exact HctxA'
      | eapply IHsub; exact HctxA' ].
  - (* subtyp_sigma *) intros Γ i A A' B B' HA IHA HA' IHA' HAeq IHAeq HB IHB HB' IHB' Hsub IHsub Δ0 HΔ.
    pose proof (IHA _ HΔ) as HAΔ.
    pose proof (IHA' _ HΔ) as HA'Δ.
    assert (HctxA : {{ ⊢ Γ, A ≈ Δ0, A }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    assert (HctxA' : {{ ⊢ Γ, A' ≈ Δ0, A' }}) by (eapply wf_ctx_eq_extend_same; eassumption).
    eapply wf_subtyp_sigma;
      [ eapply IHA; exact HΔ
      | eapply IHA'; exact HΔ
      | eapply IHAeq; exact HΔ
      | eapply IHB; exact HctxA
      | eapply IHB'; exact HctxA'
      | eapply IHsub; exact HctxA' ].

Qed.

Lemma CtxConvTy_strong : forall Γ A C i,
  {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ C : Type@i }} ->
  {{ Γ ⊢ A ≈ C : Type@i }} ->
  forall B j, {{ Γ, A ⊢ B : Type@j }} -> {{ Γ, C ⊢ B : Type@j }}.
Proof.
  intros Γ A C i HA HC Heq B j HB.
  assert (HwfΓ : {{ ⊢ Γ }}) by (eapply wf_exp_ctx; exact HA).
  assert (HctxEq : {{ ⊢ Γ, A ≈ Γ, C }}).
  { eapply wf_ctx_eq_extend; [ apply wf_ctx_eq_refl; exact HwfΓ | exact HA | exact HC | exact HA | exact HC | exact Heq | exact Heq ]. }
  exact (proj1 (proj2 (proj2 ctx_eq_transport_all)) (cons A Γ) (a_typ j) B HB (cons C Γ) HctxEq).
Qed.

Section Reduction.
Hypothesis NTS : forall Γ A W i,
  nbe_ty Γ A W -> {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ W : Type@i }} /\ {{ Γ ⊢ A ≈ W : Type@i }}.
Hypothesis NTmS : forall Γ M A W,
  nbe Γ M A W -> {{ Γ ⊢ M : A }} ->
  {{ Γ ⊢ W : A }} /\ {{ Γ ⊢ M ≈ W : A }}.
Lemma infer_check_sound :
  (forall Γ A M, alg_type_check Γ A M ->
     forall i, {{ ⊢ Γ }} -> {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ M : A }}) /\
  (forall Γ A M, alg_type_infer Γ A M ->
     {{ ⊢ Γ }} -> exists i, {{ Γ ⊢ M : A }} /\ {{ Γ ⊢ A : Type@i }}).
Proof.
  apply (alg_type_mut_ind
    (fun Γ A M _ => forall i, {{ ⊢ Γ }} -> {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ M : A }})
    (fun Γ A M _ => {{ ⊢ Γ }} -> exists i, {{ Γ ⊢ M : A }} /\ {{ Γ ⊢ A : Type@i }})).
  - (* atc_ati *) intros Γ A M B0 a IH a0 i Hwf HB.
    destruct (IH Hwf) as [j [HM HA]].
    assert (Hsub : {{ Γ ⊢ A ⊆ B0 }}).
    { eapply alg_subtyping_sound; [exact NTS | exact a0 | exists j; exact HA | exists i; exact HB]. }
    eapply wf_exp_subtyp; [exact HM | exact HB | exact Hsub].
  - (* ati_typ *) intros Γ i Hwf. exists (S (S i)). split.
    + apply wf_typ. exact Hwf.
    + apply wf_typ. exact Hwf.
  - (* ati_nat *) intros Γ Hwf. exists 1. split.
    + apply wf_nat. exact Hwf.
    + apply wf_typ. exact Hwf.
  - (* ati_zero *) intros Γ Hwf. exists 0. split.
    + apply wf_zero. exact Hwf.
    + apply wf_nat. exact Hwf.
  - (* ati_succ *) intros Γ M a IH Hwf.
    pose proof (IH 0 Hwf (@wf_nat Γ Hwf)) as HM.
    exists 0. split.
    + apply wf_succ. exact HM.
    + apply wf_nat. exact Hwf.
  - (* ati_natrec *) intros Γ i A MZ MS M B a IHA a0 IHMZ a1 IHMS a2 IHM n Hwf.
    assert (Hnat : {{ Γ ⊢ ℕ : Type@0 }}) by (apply wf_nat; exact Hwf).
    assert (HctxN : {{ ⊢ Γ, ℕ }}) by (eapply wf_ctx_extend; eassumption).
    destruct (IHA HctxN) as [iA [HA HATy]].
    assert (HMZty : {{ Γ ⊢ A[Id,,zero] : Type@i }}) by (eapply wf_natrec_zero_ty; exact HA).
    pose proof (IHMZ i Hwf HMZty) as HMZ.
    assert (HMSty : {{ Γ, ℕ, A ⊢ A[Wk∘Wk,,succ #1] : Type@i }})
      by (eapply wf_natrec_step_ty; exact HA).
    assert (Hctx2 : {{ ⊢ Γ, ℕ, A }}) by (eapply wf_ctx_extend; [exact HctxN|exact HA]).
    pose proof (IHMS i Hctx2 HMSty) as HMS.
    pose proof (IHM 0 Hwf Hnat) as HM.
    assert (Hrec : {{ Γ ⊢ rec M return A | zero -> MZ | succ -> MS end : A[Id,,M] }})
      by (eapply wf_natrec; eassumption).
    assert (HAscrut : {{ Γ ⊢ A[Id,,M] : Type@i }}) by (eapply wf_natrec_scrut_ty; eassumption).
    destruct (NTS Γ (a_sub A (a_extend a_id M)) B i n HAscrut) as [HB HBeq].
    exists i. split.
    + eapply wf_exp_conv; [exact Hrec|exact HBeq|exact HB].
    + exact HB.
  - (* ati_pi *) intros Γ i A j B a IHA a0 IHB Hwf.
    destruct (IHA Hwf) as [iA [HA HATy]].
    assert (HctxA : {{ ⊢ Γ, A }}) by (eapply wf_ctx_extend; [exact Hwf|exact HA]).
    destruct (IHB HctxA) as [iB [HB HBTy]].
    set (u := Nat.max i j).
    assert (HAu : {{ Γ ⊢ A : Type@u }}) by (eapply wf_exp_cumul; [|exact HA]; unfold u; lia).
    assert (HBu : {{ Γ, A ⊢ B : Type@u }}) by (eapply wf_exp_cumul; [|exact HB]; unfold u; lia).
    exists (S u). split.
    + apply wf_pi with (i := u); assumption.
    + apply wf_typ. exact Hwf.
  - (* ati_fn *) intros Γ i A B M C a IHA a0 IHM n Hwf.
    destruct (IHA Hwf) as [iA [HA HATy]].
    destruct (NTS Γ A C i n HA) as [HC HeqAC].
    assert (HctxA : {{ ⊢ Γ, A }}) by (eapply wf_ctx_extend; [exact Hwf|exact HA]).
    destruct (IHM HctxA) as [j [HM HBTy]].
    set (ΓC := cons (C : exp) Γ).
    assert (HBC : {{ ΓC ⊢ B : Type@j }}) by (exact (CtxConvTy_strong Γ A C i HA HC HeqAC (B : exp) j HBTy)).
    set (u := Nat.max i j).
    assert (HAu : {{ Γ ⊢ A : Type@u }}) by (eapply wf_exp_cumul; [|exact HA]; unfold u; lia).
    assert (HCu : {{ Γ ⊢ C : Type@u }}) by (eapply wf_exp_cumul; [|exact HC]; unfold u; lia).
    assert (HBuA : {{ Γ, A ⊢ B : Type@u }}) by (eapply wf_exp_cumul; [|exact HBTy]; unfold u; lia).
    assert (HBuC : {{ ΓC ⊢ B : Type@u }}) by (eapply wf_exp_cumul; [|exact HBC]; unfold u; lia).
    assert (Hty : {{ Γ ⊢ Π C B : Type@u }}) by (eapply wf_pi; eassumption).
    assert (Hlam : {{ Γ ⊢ λ A M : Π A B }}) by (eapply wf_fn; [exact HA|exact HM]).
    assert (HeqACu : {{ Γ ⊢ A ≈ C : Type@u }})
      by (eapply wf_exp_eq_raise_univ; [exact HA|exact HeqAC|unfold u; lia]).
    assert (HeqPi : {{ Γ ⊢ Π A B ≈ Π C B : Type@u }}).
    { eapply wf_exp_eq_pi_cong; [exact HAu|exact HeqACu|apply wf_exp_eq_refl; exact HBuA]. }
    exists u. split.
    + eapply wf_exp_conv; [exact Hlam|exact HeqPi|exact Hty].
    + exact Hty.
  - (* ati_app *) intros Γ A B M N C a IHM a0 IHN n Hwf.
    destruct (IHM Hwf) as [j [HM HPiTy]].
    destruct (wf_pi_typing_inv Γ A B (a_typ j) HPiTy) as [iA [iB [HA HB]]].
    pose proof (IHN iA Hwf HA) as HN.
    set (u := Nat.max iA iB).
    set (ΓA := cons (A : exp) Γ).
    assert (HAu : {{ Γ ⊢ A : Type@u }}) by (eapply wf_exp_cumul; [|exact HA]; unfold u; lia).
    assert (HBu : {{ ΓA ⊢ B : Type@u }}) by (eapply wf_exp_cumul; [|exact HB]; unfold u; lia).
    assert (Happ : {{ Γ ⊢ M N : B[Id,,N] }}) by (eapply wf_app; eassumption).
    assert (Hcod : {{ Γ ⊢ B[Id,,N] : Type@u }}) by (eapply wf_app_cod_ty; eassumption).
    destruct (NTS Γ (a_sub B (a_extend a_id N)) C u n Hcod) as [HC HCe].
    exists u. split.
    + eapply wf_exp_conv; [exact Happ|exact HCe|exact HC].
    + exact HC.
  - (* ati_sigma *) intros Γ i A j B a IHA a0 IHB Hwf.
    destruct (IHA Hwf) as [iA [HA HATy]].
    assert (HctxA : {{ ⊢ Γ, A }}) by (eapply wf_ctx_extend; [exact Hwf|exact HA]).
    destruct (IHB HctxA) as [iB [HB HBTy]].
    set (u := Nat.max i j).
    assert (HAu : {{ Γ ⊢ A : Type@u }}) by (eapply wf_exp_cumul; [|exact HA]; unfold u; lia).
    assert (HBu : {{ Γ, A ⊢ B : Type@u }}) by (eapply wf_exp_cumul; [|exact HB]; unfold u; lia).
    exists (S u). split.
    + apply wf_sigma with (i := u); assumption.
    + apply wf_typ. exact Hwf.
  - (* ati_pair *) intros Γ i A j B M1 M2 A' C a IHA a0 IHB a1 IHM1 a2 IHM2 n n0 Hwf.
    destruct (IHA Hwf) as [iA [HA HATy]].
    assert (HctxA : {{ ⊢ Γ, A }}) by (eapply wf_ctx_extend; [exact Hwf|exact HA]).
    destruct (IHB HctxA) as [jB [HB HBTy]].
    set (u := Nat.max i j).
    assert (HAu : {{ Γ ⊢ A : Type@u }}) by (eapply wf_exp_cumul; [|exact HA]; unfold u; lia).
    assert (HBu : {{ Γ, A ⊢ B : Type@u }}) by (eapply wf_exp_cumul; [|exact HB]; unfold u; lia).
    pose proof (IHM1 u Hwf HAu) as HM1.
    assert (HBsub : {{ Γ ⊢ B[Id,,M1] : Type@u }}) by (eapply wf_app_cod_ty; eassumption).
    pose proof (IHM2 u Hwf HBsub) as HM2.
    destruct (NTS Γ A A' i n HA) as [HA' HeqAA'].
    destruct (NTS _ B C j n0 HB) as [HC HeqBC].
    assert (Hpair : {{ Γ ⊢ ⟨ M1 : A ; M2 : B ⟩ : Σ A B }}) by (eapply wf_pair; eassumption).
    assert (HA'u : {{ Γ ⊢ A' : Type@u }}) by (eapply wf_exp_cumul; [|exact HA']; unfold u; lia).
    set (ΓA' := cons (A' : exp) Γ).
    assert (HC_A' : {{ ΓA' ⊢ C : Type@j }}) by (exact (CtxConvTy_strong Γ A (A' : exp) i HA HA' HeqAA' (C : exp) j HC)).
    assert (HCu : {{ ΓA' ⊢ C : Type@u }}) by (eapply wf_exp_cumul; [|exact HC_A']; unfold u; lia).
    assert (Hty : {{ Γ ⊢ Σ A' C : Type@u }}) by (eapply wf_sigma; eassumption).
    assert (HeqAA'u : {{ Γ ⊢ A ≈ A' : Type@u }})
      by (eapply wf_exp_eq_raise_univ; [exact HA|exact HeqAA'|unfold u; lia]).
    assert (HeqBCu : {{ Γ, A ⊢ B ≈ C : Type@u }})
      by (eapply wf_exp_eq_raise_univ; [exact HB|exact HeqBC|unfold u; lia]).
    assert (HeqSig : {{ Γ ⊢ Σ A B ≈ Σ A' C : Type@u }}).
    { eapply wf_exp_eq_sigma_cong; [exact HAu|exact HeqAA'u|exact HeqBCu]. }
    exists u. split.
    + eapply wf_exp_conv; [exact Hpair|exact HeqSig|exact Hty].
    + exact Hty.
  - (* ati_fst *) intros Γ A B M a IHM Hwf.
    destruct (IHM Hwf) as [j [HM HSigTy]].
    destruct (wf_sigma_typing_inv Γ A B (a_typ j) HSigTy) as [iA [iB [HA HB]]].
    set (u := Nat.max iA iB).
    set (ΓA := cons (A : exp) Γ).
    assert (HAu : {{ Γ ⊢ A : Type@u }}) by (eapply wf_exp_cumul; [|exact HA]; unfold u; lia).
    assert (HBu : {{ ΓA ⊢ B : Type@u }}) by (eapply wf_exp_cumul; [|exact HB]; unfold u; lia).
    assert (Hfst : {{ Γ ⊢ fst M : A }}) by (eapply wf_fst; eassumption).
    exists iA. split; [exact Hfst|exact HA].
  - (* ati_snd *) intros Γ A B M C a IHM n Hwf.
    destruct (IHM Hwf) as [j [HM HSigTy]].
    destruct (wf_sigma_typing_inv Γ A B (a_typ j) HSigTy) as [iA [iB [HA HB]]].
    set (u := Nat.max iA iB).
    set (ΓA := cons (A : exp) Γ).
    assert (HAu : {{ Γ ⊢ A : Type@u }}) by (eapply wf_exp_cumul; [|exact HA]; unfold u; lia).
    assert (HBu : {{ ΓA ⊢ B : Type@u }}) by (eapply wf_exp_cumul; [|exact HB]; unfold u; lia).
    assert (Hfst : {{ Γ ⊢ fst M : A }}) by (eapply wf_fst; eassumption).
    assert (Hσ : {{ Γ ⊢s (Id ,, fst M) : ΓA }}) by (eapply wf_sub_extend_id_self; eassumption).
    assert (Hcod : {{ Γ ⊢ B[Id,,fst M] : Type@iB }}) by (eapply wf_subst_type; eassumption).
    destruct (NTS Γ (a_sub B (a_extend a_id (a_fst M))) C iB n Hcod) as [HC HCe].
    assert (Hsnd : {{ Γ ⊢ snd M : B[Id,,fst M] }}) by (eapply wf_snd with (i:=u); [exact HAu|exact HBu|exact HM]).
    exists iB. split.
    + eapply wf_exp_conv; [exact Hsnd|exact HCe|exact HC].
    + exact HC.
  - (* ati_eq *) intros Γ i A M1 M2 a IHA a0 IHM1 a1 IHM2 Hwf.
    destruct (IHA Hwf) as [iA [HA HATy]].
    pose proof (IHM1 i Hwf HA) as HM1.
    pose proof (IHM2 i Hwf HA) as HM2.
    assert (Heq : {{ Γ ⊢ Eq A M1 M2 : Type@i }}) by (eapply wf_eq; eassumption).
    exists iA. split.
    + exact Heq.
    + exact HATy.
  - (* ati_refl *) intros Γ i A M C N a IHA a0 IHM n n0 Hwf.
    destruct (IHA Hwf) as [iA [HA HATy]].
    pose proof (IHM i Hwf HA) as HM.
    destruct (NTS Γ A C i n HA) as [HC HeqAC].
    destruct (NTmS Γ M A N n0 HM) as [HN HeqMN].
    assert (HNC : {{ Γ ⊢ N : C }}) by (eapply wf_exp_conv; [exact HN|exact HeqAC|exact HC]).
    assert (HeqTy : {{ Γ ⊢ Eq A M M ≈ Eq C N N : Type@i }})
      by (eapply wf_exp_eq_eq_cong; eassumption).
    assert (Hty : {{ Γ ⊢ Eq C N N : Type@i }}) by (eapply wf_eq; eassumption).
    assert (Hrefl : {{ Γ ⊢ refl A M : Eq A M M }}) by (eapply wf_refl; eassumption).
    exists i. split.
    + eapply wf_exp_conv; [exact Hrefl|exact HeqTy|exact Hty].
    + exact Hty.
  - (* ati_eqrec *) intros Γ i A M1 M2 j B BR N C a IHA a0 IHM1 a1 IHM2 a2 IHB a3 IHBR a4 IHN n Hwf.
    destruct (IHA Hwf) as [iA [HA HATy]].
    pose proof (IHM1 i Hwf HA) as HM1.
    pose proof (IHM2 i Hwf HA) as HM2.
    assert (Hctx1 : {{ ⊢ Γ, A }}) by (eapply wf_ctx_extend; [exact Hwf|exact HA]).
    destruct (eqrec_ctx_typing Γ A i HA) as [HWWty [HMc [HNc HEqty]]].
    assert (Hctx2 : {{ ⊢ Γ, A, A[Wk] }}) by (eapply wf_exp_ctx; exact HWWty).
    assert (HctxE : {{ ⊢ Γ, A, A[Wk], Eq (A[Wk∘Wk]) #1 #0 }})
      by (eapply wf_ctx_extend; [exact Hctx2|exact HEqty]).
    destruct (IHB HctxE) as [jB [HB HBTy]].
    assert (HBRty : {{ Γ, A ⊢ B[Id,,#0,,refl A[Wk] #0] : Type@j }})
      by (eapply BranchTy_proved; eassumption).
    pose proof (IHBR j Hctx1 HBRty) as HBR.
    assert (HNty : {{ Γ ⊢ Eq A M1 M2 : Type@i }}) by (eapply wf_eq; eassumption).
    pose proof (IHN i Hwf HNty) as HN.
    assert (Hterm : {{ Γ ⊢ eqrec N as Eq A M1 M2 return B | refl -> BR end
                        : B[Id,,M1,,M2,,N] }}) by (eapply wf_eqrec; eassumption).
    (* type of the result via wf_eqrec_subst *)
    assert (HM1' : {{ Γ ⊢ M1 : A[Id] }})
      by (eapply wf_exp_conv; [exact HM1|apply wf_exp_eq_sym; apply wf_exp_eq_sub_id_univ; exact HA|eapply wf_subst_type; [apply wf_sub_id; exact Hwf|exact HA]]).
    assert (HAwk : {{ Γ, A ⊢ A[Wk] : Type@i }})
      by (eapply wf_subst_type; [apply wf_sub_weaken; exact Hctx1|exact HA]).
    assert (HAwk_sub_ty : {{ Γ ⊢ (A[Wk])[Id,,M1] : Type@i }}).
    { eapply wf_subst_type.
      - eapply wf_sub_extend_id_self; [exact HM1|exact HA].
      - exact HAwk. }
    assert (HAid : {{ Γ ⊢ A[Id] ≈ A : Type@i }}) by (apply wf_exp_eq_sub_id_univ; exact HA).
    assert (Hwk : {{ Γ ⊢ (A[Wk])[Id,,M1] ≈ A[Id] : Type@i }})
      by (eapply sub_wk_extend_approx; [apply wf_sub_id; exact Hwf|exact HA|exact HM1']).
    assert (Heq2 : {{ Γ ⊢ A ≈ (A[Wk])[Id,,M1] : Type@i }})
      by (eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; exact HAid|apply wf_exp_eq_sym; exact Hwk]).
    assert (HM2' : {{ Γ ⊢ M2 : ((A[Wk])[Id,,M1]) }})
      by (eapply wf_exp_conv; [exact HM2|exact Heq2|exact HAwk_sub_ty]).
    assert (Hresty : {{ Γ ⊢ B[Id,,M1,,M2,,N] : Type@j }})
      by (eapply wf_eqrec_subst with (A:=A) (M1:=M1) (M2:=M2) (N:=N) (B:=B) (i:=i) (j:=j); eassumption).
    destruct (NTS Γ (a_sub B (a_extend (a_extend (a_extend a_id M1) M2) N)) C j n Hresty) as [HC HCe].
    exists j. split.
    + eapply wf_exp_conv; [exact Hterm|exact HCe|exact HC].
    + exact HC.
  - (* ati_vlookup *) intros x A Γ B c n Hwf.
    destruct (ctx_lookup_type Γ x A c Hwf) as [i HA].
    destruct (NTS Γ A B i n HA) as [HB Heq].
    exists i. split.
    + eapply wf_exp_conv; [eapply wf_vlookup; eassumption|exact Heq|exact HB].
    + exact HB.
Qed.
End Reduction.

(* The substitution-realizing environment relation used by the intended
   adequacy proof.  It is only a Definition: no axiom is introduced. *)
Definition Rsub (Γ Δ : ctx) (σ : sub) (ρ : env) : Prop :=
  forall x A, {{ #x : A ∈ Δ }} ->
    exists i a WA W,
      {{ Δ ⊢ A : Type@i }} /\
      {{ Γ ⊢ A[σ] : Type@i }} /\
      eval_exp A ρ a /\
      read_typ (length Γ) a WA /\
      {{ Γ ⊢ WA : Type@i }} /\
      {{ Γ ⊢ A[σ] ≈ WA : Type@i }} /\
      read_nf (length Γ) (d_dom a (ρ x)) W /\
      {{ Γ ⊢ #x[σ] ≈ W : A[σ] }}.

Lemma check_complete_from_infer :
  (forall (M : exp), user_exp M ->
     forall Γ A, {{ Γ ⊢ M : A }} ->
       exists B : nf, alg_type_infer Γ B M /\ {{ Γ ⊢ B ⊆ A }}) ->
  (forall Γ A B, {{ Γ ⊢ A ⊆ B }} -> alg_subtyping Γ A B) ->
  forall (M : exp), user_exp M ->
     forall Γ A, {{ Γ ⊢ M : A }} -> alg_type_check Γ A M.
Proof.
  intros HInfer HSub M Hu Γ A HM.
  destruct (HInfer M Hu Γ A HM) as [B [Hinf Hsub]].
  eapply atc_ati.
  - exact Hinf.
  - eapply HSub. exact Hsub.
Qed.

Definition RsubFundamentalStmt : Prop :=
  (forall Γ Δ σ ρ,
      {{ Γ ⊢s σ : Δ }} -> Rsub Γ Δ σ ρ ->
      forall A i, {{ Δ ⊢ A : Type@i }} ->
        exists a WA, eval_exp A ρ a /\ read_typ (length Γ) a WA /\
          {{ Γ ⊢ A[σ] ≈ WA : Type@i }})
  /\
  (forall Γ Δ σ ρ,
      {{ Γ ⊢s σ : Δ }} -> Rsub Γ Δ σ ρ ->
      forall A M, {{ Δ ⊢ M : A }} ->
        exists a m W, eval_exp A ρ a /\ eval_exp M ρ m /\
          read_nf (length Γ) (d_dom a m) W /\
          {{ Γ ⊢ M[σ] ≈ W : A[σ] }})
  /\
  (forall Δ ρ, {{ ⊢ Δ }} -> initial_env Δ ρ -> Rsub Δ Δ a_id ρ).

Definition InferCompleteUserStmt : Prop :=
  forall (M : exp), user_exp M ->
    forall Γ A, {{ Γ ⊢ M : A }} ->
      exists B : nf, alg_type_infer Γ B M /\ {{ Γ ⊢ B ⊆ A }}.

(* ============================================================ *)
(* Canonical typing shapes for user expressions                 *)
(* ============================================================ *)

Inductive user_shape : ctx -> exp -> typ -> Prop :=
| us_typ : forall Γ i, {{ ⊢ Γ }} -> user_shape Γ (a_typ i) (a_typ (S i))
| us_nat : forall Γ, {{ ⊢ Γ }} -> user_shape Γ a_nat (a_typ 0)
| us_zero : forall Γ, {{ ⊢ Γ }} -> user_shape Γ a_zero a_nat
| us_succ : forall Γ M, {{ Γ ⊢ M : ℕ }} -> user_shape Γ (a_succ M) a_nat
| us_natrec : forall Γ i A MZ MS M,
    {{ Γ, ℕ ⊢ A : Type@i }} ->
    {{ Γ ⊢ MZ : A[Id,,zero] }} ->
    {{ Γ, ℕ, A ⊢ MS : A[Wk∘Wk,,succ #1] }} ->
    {{ Γ ⊢ M : ℕ }} ->
    user_shape Γ (a_natrec A MZ MS M) (a_sub A (a_extend a_id M))
| us_pi : forall Γ i A B,
    {{ Γ ⊢ A : Type@i }} -> {{ Γ, A ⊢ B : Type@i }} ->
    user_shape Γ (a_pi A B) (a_typ i)
| us_fn : forall Γ i A B M,
    {{ Γ ⊢ A : Type@i }} -> {{ Γ, A ⊢ M : B }} ->
    user_shape Γ (a_fn A M) (a_pi A B)
| us_app : forall Γ i A B M N,
    {{ Γ ⊢ A : Type@i }} -> {{ Γ, A ⊢ B : Type@i }} ->
    {{ Γ ⊢ M : Π A B }} -> {{ Γ ⊢ N : A }} ->
    user_shape Γ (a_app M N) (a_sub B (a_extend a_id N))
| us_sigma : forall Γ i A B,
    {{ Γ ⊢ A : Type@i }} -> {{ Γ, A ⊢ B : Type@i }} ->
    user_shape Γ (a_sigma A B) (a_typ i)
| us_pair : forall Γ i A B M N,
    {{ Γ ⊢ A : Type@i }} -> {{ Γ, A ⊢ B : Type@i }} ->
    {{ Γ ⊢ M : A }} -> {{ Γ ⊢ N : B[Id,,M] }} ->
    user_shape Γ (a_pair M A N B) (a_sigma A B)
| us_fst : forall Γ i A B M,
    {{ Γ ⊢ A : Type@i }} -> {{ Γ, A ⊢ B : Type@i }} ->
    {{ Γ ⊢ M : Σ A B }} -> user_shape Γ (a_fst M) A
| us_snd : forall Γ i A B M,
    {{ Γ ⊢ A : Type@i }} -> {{ Γ, A ⊢ B : Type@i }} ->
    {{ Γ ⊢ M : Σ A B }} -> user_shape Γ (a_snd M) (a_sub B (a_extend a_id (a_fst M)))
| us_eq : forall Γ i A M N,
    {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ M : A }} -> {{ Γ ⊢ N : A }} ->
    user_shape Γ (a_eq A M N) (a_typ i)
| us_refl : forall Γ i A M,
    {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ M : A }} ->
    user_shape Γ (a_refl A M) (a_eq A M M)
| us_eqrec : forall Γ i A M1 M2 j B BR N,
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M1 : A }} -> {{ Γ ⊢ M2 : A }} ->
    {{ Γ, A, A[Wk], Eq (A[Wk∘Wk]) #1 #0 ⊢ B : Type@j }} ->
    {{ Γ, A ⊢ BR : B[Id,,#0,,refl A[Wk] #0] }} ->
    {{ Γ ⊢ N : Eq A M1 M2 }} ->
    user_shape Γ (a_eqrec A B BR M1 M2 N) (a_sub B (a_extend (a_extend (a_extend a_id M1) M2) N))
| us_var : forall Γ x A,
    {{ ⊢ Γ }} -> {{ #x : A ∈ Γ }} -> user_shape Γ (a_var x) A.

Lemma user_shape_typing : forall Γ M A,
  user_shape Γ M A -> {{ Γ ⊢ M : A }}.
Proof.
  intros Γ M A H. induction H; econstructor; eassumption.
Qed.

Lemma user_shape_type : forall Γ M A,
  user_shape Γ M A -> exists i, {{ Γ ⊢ A : Type@i }}.
Proof.
  intros. eapply wf_exp_type. eapply user_shape_typing. exact H.
Qed.

Lemma user_shape_subtyp_refl : forall Γ M A,
  user_shape Γ M A -> {{ Γ ⊢ A ⊆ A }}.
Proof.
  intros. destruct (user_shape_type _ _ _ H) as [i Hi].
  apply wf_subtyp_refl' with (i:=i). exact Hi.
Qed.


Lemma user_exp_sub_false : forall M0 σ, user_exp (a_sub M0 σ) -> False.
Proof. intros. inversion H. Qed.

Lemma user_typing_shape : forall Γ A M,
  user_exp M -> {{ Γ ⊢ M : A }} ->
  exists A0, user_shape Γ M A0 /\ {{ Γ ⊢ A0 ⊆ A }}.
Proof.
  intros Γ A M Hu Hty. revert Hu.
  induction Hty using wf_exp_ind.
  all: intros Hu.
  all: try (eexists; split; [econstructor; eassumption|eapply user_shape_subtyp_refl; econstructor; eassumption]).
  - exfalso. eapply user_exp_sub_false; eassumption.
  - match goal with
    | Hfun : (user_exp _ -> _) |- _ =>
        destruct (Hfun Hu) as [A0 [Hs HB]];
        exists A0; split; [exact Hs|eapply wf_subtyp_trans; eassumption]
    end.
Qed.


(* ============================================================ *)
(* Substitution preservation of declarative subtyping           *)
(* ============================================================ *)

Lemma wf_exp_eq_sub_type_univ : forall Γ Δ σ A A' i,
  {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ A ≈ A' : Type@i }} ->
  {{ Γ ⊢ A[σ] ≈ A'[σ] : Type@i }}.
Proof.
  intros Γ Δ σ A A' i Hσ Heq.
  assert (Hraw : {{ Γ ⊢ A[σ] ≈ A'[σ] : (Type@i)[σ] }})
    by (eapply wf_exp_eq_sub_cong; [exact Heq|apply wf_sub_eq_refl; exact Hσ]).
  eapply wf_exp_eq_univ_retype with (i:=i); [exact Hσ|exact Hraw].
Qed.

Lemma wf_subtyp_eq_left : forall Γ A A' B i,
  {{ Γ ⊢ A ≈ A' : Type@i }} -> {{ Γ ⊢ A' : Type@i }} ->
  {{ Γ ⊢ A' ⊆ B }} -> {{ Γ ⊢ A ⊆ B }}.
Proof.
  intros Γ A A' B i Heq HA' Hsub.
  eapply wf_subtyp_trans; [eapply wf_subtyp_of_eq; eassumption|exact Hsub].
Qed.

Lemma wf_subtyp_eq_right : forall Γ A B B' i,
  {{ Γ ⊢ A ⊆ B }} -> {{ Γ ⊢ B ≈ B' : Type@i }} ->
  {{ Γ ⊢ B' : Type@i }} -> {{ Γ ⊢ A ⊆ B' }}.
Proof.
  intros Γ A B B' i Hsub Heq HB'.
  eapply wf_subtyp_trans; [exact Hsub|eapply wf_subtyp_of_eq; eassumption].
Qed.

Lemma wf_sub_q : forall Γ Δ σ A i,
  {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ A : Type@i }} ->
  {{ Γ, A[σ] ⊢s q σ : Δ, A }}.
Proof.
  intros Γ Δ σ A i Hσ HA.
  apply wf_sub_ctx in Hσ as HwfΓ.
  assert (HAσ : {{ Γ ⊢ A[σ] : Type@i }})
    by (eapply wf_subst_type; eassumption).
  assert (HctxΓA : {{ ⊢ Γ, A[σ] }})
    by (eapply wf_ctx_extend; eassumption).
  assert (HWk : {{ Γ, A[σ] ⊢s Wk : Γ }})
    by (apply wf_sub_weaken; exact HctxΓA).
  assert (HσWk : {{ Γ, A[σ] ⊢s σ∘Wk : Δ }})
    by (eapply wf_sub_compose; eassumption).
  assert (HAσWk : {{ Γ, A[σ] ⊢ A[σ∘Wk] : Type@i }})
    by (eapply wf_subst_type; eassumption).
  pose proof (here (a_sub A σ) Γ) as Hlk.
  assert (Hvar : {{ Γ, A[σ] ⊢ #0 : (A[σ])[Wk] }})
    by (eapply wf_vlookup; eassumption).
  assert (Hcomp : {{ Γ, A[σ] ⊢ A[σ∘Wk] ≈ (A[σ])[Wk] : Type@i }})
    by (eapply wf_exp_eq_sub_compose_univ with
          (Γ := (a_sub A σ :: Γ)%list) (Γ':=Γ) (Γ'':=Δ)
          (τ:=a_weaken) (σ:=σ) (A:=A) (i:=i); eassumption).
  assert (Hvar' : {{ Γ, A[σ] ⊢ #0 : A[σ∘Wk] }})
    by (eapply wf_exp_conv;
        [exact Hvar|apply wf_exp_eq_sym; exact Hcomp|exact HAσWk]).
  eapply wf_sub_extend; [exact HσWk|exact HA|exact Hvar'].
Qed.

Lemma wf_subtyp_subst : forall Γ Δ σ A A',
  {{ Γ ⊢s σ : Δ }} -> {{ Δ ⊢ A ⊆ A' }} -> {{ Γ ⊢ A[σ] ⊆ A'[σ] }}.
Proof.
  intros Γ Δ σ A A' Hσ Hsub.
  revert Γ σ Hσ.
  induction Hsub as
    [ Δ0 i M' M HM' HMeq
    | Δ0 M M' M'' Hsub1 IH1 Hsub2 IH2
    | Δ0 i j Hwf Hlt
    | Δ0 i A A' B B' HA HA' HAeq HB HB' HsubB IHB
    | Δ0 i A A' B B' HA HA' HAeq HB HB' HsubB IHB ];
    intros Γ0 σ0 Hσ0.
  - (* refl *)
    assert (HtyM' : {{ Γ0 ⊢ M'[σ0] : Type@i }})
      by (eapply wf_subst_type; eassumption).
    assert (Heq : {{ Γ0 ⊢ M[σ0] ≈ M'[σ0] : Type@i }})
      by (eapply wf_exp_eq_sub_type_univ; eassumption).
    eapply wf_subtyp_refl with (i:=i); [exact HtyM'|exact Heq].
  - (* trans *) eapply wf_subtyp_trans; [eapply IH1; exact Hσ0|eapply IH2; exact Hσ0].
  - (* univ *)
    apply wf_sub_ctx in Hσ0 as HwfΓ.
    assert (Hi : {{ Γ0 ⊢ Type@i[σ0] ≈ Type@i : Type@(S i) }})
      by (eapply wf_exp_eq_typ_sub; exact Hσ0).
    assert (Hj : {{ Γ0 ⊢ Type@j[σ0] ≈ Type@j : Type@(S j) }})
      by (eapply wf_exp_eq_typ_sub; exact Hσ0).
    assert (Htyj : {{ Γ0 ⊢ Type@j[σ0] : Type@(S j) }})
      by (eapply wf_subst_type; [exact Hσ0|apply wf_typ; exact Hwf]).
    eapply wf_subtyp_trans.
    + eapply wf_subtyp_of_eq. { exact Hi. } { apply wf_typ. exact HwfΓ. }
    + eapply wf_subtyp_trans.
      * eapply wf_subtyp_univ; eassumption.
      * eapply wf_subtyp_of_eq. { apply wf_exp_eq_sym. exact Hj. } { exact Htyj. }
  - (* pi *)
    assert (HAσ : {{ Γ0 ⊢ A[σ0] : Type@i }}) by (eapply wf_subst_type; eassumption).
    assert (HA'σ : {{ Γ0 ⊢ A'[σ0] : Type@i }}) by (eapply wf_subst_type; eassumption).
    assert (HAeqσ : {{ Γ0 ⊢ A[σ0] ≈ A'[σ0] : Type@i }})
      by (eapply wf_exp_eq_sub_type_univ; eassumption).
    assert (HqA : {{ Γ0, A[σ0] ⊢s q σ0 : Δ0, A }}) by (eapply wf_sub_q; eassumption).
    assert (HqA' : {{ Γ0, A'[σ0] ⊢s q σ0 : Δ0, A' }}) by (eapply wf_sub_q; eassumption).
    assert (HBq : {{ Γ0, A[σ0] ⊢ B[q σ0] : Type@i }}) by (eapply wf_subst_type; eassumption).
    assert (HB'q : {{ Γ0, A'[σ0] ⊢ B'[q σ0] : Type@i }}) by (eapply wf_subst_type; eassumption).
    assert (Hsubq : {{ Γ0, A'[σ0] ⊢ B[q σ0] ⊆ B'[q σ0] }}) by (eapply IHB; exact HqA').
    assert (Hpi : {{ Γ0 ⊢ Π A[σ0] B[q σ0] ⊆ Π A'[σ0] B'[q σ0] }})
      by (eapply wf_subtyp_pi; eassumption).
    assert (HtyPi : {{ Γ0 ⊢ Π A[σ0] B[q σ0] : Type@i }})
      by (eapply wf_pi; eassumption).
    assert (HtyPi' : {{ Γ0 ⊢ (Π A' B')[σ0] : Type@i }})
      by (eapply wf_subst_type; [exact Hσ0|eapply wf_pi; eassumption]).
    assert (HX : {{ Γ0 ⊢ (Π A B)[σ0] ≈ Π A[σ0] B[q σ0] : Type@i }})
      by (eapply wf_exp_eq_pi_sub; eassumption).
    assert (HY : {{ Γ0 ⊢ (Π A' B')[σ0] ≈ Π A'[σ0] B'[q σ0] : Type@i }})
      by (eapply wf_exp_eq_pi_sub; eassumption).
    assert (Hright : {{ Γ0 ⊢ Π A[σ0] B[q σ0] ⊆ (Π A' B')[σ0] }})
      by (eapply wf_subtyp_eq_right;
          [exact Hpi|apply wf_exp_eq_sym; exact HY|exact HtyPi']).
    eapply wf_subtyp_trans.
    + eapply wf_subtyp_of_eq; [exact HX|exact HtyPi].
    + exact Hright.
  - (* sigma *)
    assert (HAσ : {{ Γ0 ⊢ A[σ0] : Type@i }}) by (eapply wf_subst_type; eassumption).
    assert (HA'σ : {{ Γ0 ⊢ A'[σ0] : Type@i }}) by (eapply wf_subst_type; eassumption).
    assert (HAeqσ : {{ Γ0 ⊢ A[σ0] ≈ A'[σ0] : Type@i }})
      by (eapply wf_exp_eq_sub_type_univ; eassumption).
    assert (HqA : {{ Γ0, A[σ0] ⊢s q σ0 : Δ0, A }}) by (eapply wf_sub_q; eassumption).
    assert (HqA' : {{ Γ0, A'[σ0] ⊢s q σ0 : Δ0, A' }}) by (eapply wf_sub_q; eassumption).
    assert (HBq : {{ Γ0, A[σ0] ⊢ B[q σ0] : Type@i }}) by (eapply wf_subst_type; eassumption).
    assert (HB'q : {{ Γ0, A'[σ0] ⊢ B'[q σ0] : Type@i }}) by (eapply wf_subst_type; eassumption).
    assert (Hsubq : {{ Γ0, A'[σ0] ⊢ B[q σ0] ⊆ B'[q σ0] }}) by (eapply IHB; exact HqA').
    assert (Hsig : {{ Γ0 ⊢ Σ A[σ0] B[q σ0] ⊆ Σ A'[σ0] B'[q σ0] }})
      by (eapply wf_subtyp_sigma; eassumption).
    assert (HtySig : {{ Γ0 ⊢ Σ A[σ0] B[q σ0] : Type@i }})
      by (eapply wf_sigma; eassumption).
    assert (HtySig' : {{ Γ0 ⊢ (Σ A' B')[σ0] : Type@i }})
      by (eapply wf_subst_type; [exact Hσ0|eapply wf_sigma; eassumption]).
    assert (HX : {{ Γ0 ⊢ (Σ A B)[σ0] ≈ Σ A[σ0] B[q σ0] : Type@i }})
      by (eapply wf_exp_eq_sigma_sub; eassumption).
    assert (HY : {{ Γ0 ⊢ (Σ A' B')[σ0] ≈ Σ A'[σ0] B'[q σ0] : Type@i }})
      by (eapply wf_exp_eq_sigma_sub; eassumption).
    assert (Hright : {{ Γ0 ⊢ Σ A[σ0] B[q σ0] ⊆ (Σ A' B')[σ0] }})
      by (eapply wf_subtyp_eq_right;
          [exact Hsig|apply wf_exp_eq_sym; exact HY|exact HtySig']).
    eapply wf_subtyp_trans.
    + eapply wf_subtyp_of_eq; [exact HX|exact HtySig].
    + exact Hright.
Qed.

Section SubtypingCompleteness.

(* Semantic-normalization hypotheses, as permitted by the task. *)
Hypothesis NTS : forall Γ A W i,
  nbe_ty Γ A W -> {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ W : Type@i }} /\ {{ Γ ⊢ A ≈ W : Type@i }}.
Hypothesis NTmS : forall Γ M A W,
  nbe Γ M A W -> {{ Γ ⊢ M : A }} ->
  {{ Γ ⊢ W : A }} /\ {{ Γ ⊢ M ≈ W : A }}.
Hypothesis TyEx : forall Γ A i,
  {{ Γ ⊢ A : Type@i }} -> exists W, nbe_ty Γ A W.

(* Canonicity/readback hypotheses.  These say that the normal form
   produced by NbE is well defined on convertible types and is stable
   under replacement of a context head by a convertible type. *)
Hypothesis NbeEq : forall Γ M N i W,
  {{ Γ ⊢ M ≈ N : Type@i }} ->
  nbe_ty Γ N W -> nbe_ty Γ M W.
Hypothesis CtxNbe : forall Γ A A' i C W,
  {{ Γ ⊢ A ≈ A' : Type@i }} ->
  nbe_ty (A :: Γ) C W -> nbe_ty (A' :: Γ) C W.

(* Strengthened induction invariant: both endpoints have readbacks and
   the readback normal forms are related algorithmically.  The extra
   endpoint readback data is what makes the transitivity case go
   through without presupposition of the intermediate type. *)
Definition SubCompletePred (Γ : ctx) (A B : typ)
    (H : {{ Γ ⊢ A ⊆ B }}) : Prop :=
  (exists WA, nbe_ty Γ A WA) /\
  (exists WB, nbe_ty Γ B WB) /\
  (forall WA WB, nbe_ty Γ A WA -> nbe_ty Γ B WB ->
     {{ ⊢anf WA ⊆ WB }}).

Lemma wf_subtyp_complete_core :
  forall Γ A B (H : {{ Γ ⊢ A ⊆ B }}), SubCompletePred Γ A B H.
Proof.
  apply (wf_subtyp_mut_ind
    (fun _ _ => True)
    (fun _ _ _ => True)
    (fun _ _ _ _ => True)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ => True)
    (fun _ _ _ _ _ => True)
    SubCompletePred).
  all: try solve [intros; exact I].
  - (* wf_subtyp_refl *)
    intros Γ0 i M' M HM' _ HMeq _.
    unfold SubCompletePred.
    destruct (TyEx Γ0 M' i HM') as [WB HWB].
    assert (HWA : nbe_ty Γ0 M WB) by (eapply NbeEq; eassumption).
    split.
    + exists WB. exact HWA.
    + split.
      * exists WB. exact HWB.
      * intros WA WB' HWA' HWB'.
        assert (E : WA = WB')
          by (eapply nbe_ty_det; [exact HWA'|eapply NbeEq; eassumption]).
        subst WB'. apply alg_subtyping_nf_refl.
  - (* wf_subtyp_trans *)
    intros Γ0 M M' M'' H1 IH1 H2 IH2.
    unfold SubCompletePred in *.
    destruct IH1 as [[W1 HW1] [[Wm HWm] Hrel1]].
    destruct IH2 as [[Wm' HWm'] [[W2 HW2] Hrel2]].
    assert (E : Wm = Wm') by (eapply nbe_ty_det; [exact HWm|exact HWm']).
    subst Wm'.
    split.
    + exists W1. exact HW1.
    + split.
      * exists W2. exact HW2.
      * intros WA WB HWA HWB.
        eapply alg_subtyping_nf_trans.
        -- eapply Hrel1; [exact HWA|exact HWm].
        -- eapply Hrel2; [exact HWm'|exact HWB].
  - (* wf_subtyp_univ *)
    intros Γ0 i j Hwf _ Hlt.
    unfold SubCompletePred.
    split.
    + destruct (TyEx Γ0 (a_typ i) (S i) (wf_typ Γ0 i Hwf)) as [W HW].
      exists W. exact HW.
    + split.
      * destruct (TyEx Γ0 (a_typ j) (S j) (wf_typ Γ0 j Hwf)) as [W HW].
        exists W. exact HW.
      * intros WA WB HWA HWB.
        pose proof (nbe_ty_typ Γ0 i WA HWA) as E1. subst WA.
        pose proof (nbe_ty_typ Γ0 j WB HWB) as E2. subst WB.
        apply asnf_univ. lia.
  - (* wf_subtyp_pi *)
    intros Γ0 i A0 A' B0 B' HA _ HA' _ HAeq _ HB _ HB' _ HsubB IHB.
    unfold SubCompletePred in *.
    destruct IHB as [[Wl HWl] [[Wr HWr] Hrel]].
    split.
    + destruct (TyEx Γ0 (a_pi A0 B0) i (wf_pi Γ0 i A0 B0 HA HB)) as [W HW].
      exists W. exact HW.
    + split.
      * destruct (TyEx Γ0 (a_pi A' B') i (wf_pi Γ0 i A' B' HA' HB')) as [W HW].
        exists W. exact HW.
      * intros WA WB HWA HWB.
        destruct (nbe_ty_pi Γ0 A0 B0 WA HWA) as
            [WA0 [WA1 [E1 [HWA0 HWA1]]]]. subst WA.
        destruct (nbe_ty_pi Γ0 A' B' WB HWB) as
            [WB0 [WB1 [E2 [HWB0 HWB1]]]]. subst WB.
        assert (HA0eq : WA0 = WB0).
        { eapply nbe_ty_det.
          - exact HWA0.
          - eapply NbeEq; eassumption. }
        apply asnf_pi; [exact HA0eq|].
        eapply Hrel.
        -- eapply CtxNbe; [exact HAeq|exact HWA1].
        -- exact HWB1.
  - (* wf_subtyp_sigma *)
    intros Γ0 i A0 A' B0 B' HA _ HA' _ HAeq _ HB _ HB' _ HsubB IHB.
    unfold SubCompletePred in *.
    destruct IHB as [[Wl HWl] [[Wr HWr] Hrel]].
    split.
    + destruct (TyEx Γ0 (a_sigma A0 B0) i (wf_sigma Γ0 i A0 B0 HA HB)) as [W HW].
      exists W. exact HW.
    + split.
      * destruct (TyEx Γ0 (a_sigma A' B') i (wf_sigma Γ0 i A' B' HA' HB')) as [W HW].
        exists W. exact HW.
      * intros WA WB HWA HWB.
        destruct (nbe_ty_sigma Γ0 A0 B0 WA HWA) as
            [WA0 [WA1 [E1 [HWA0 HWA1]]]]. subst WA.
        destruct (nbe_ty_sigma Γ0 A' B' WB HWB) as
            [WB0 [WB1 [E2 [HWB0 HWB1]]]]. subst WB.
        assert (HA0eq : WA0 = WB0).
        { eapply nbe_ty_det.
          - exact HWA0.
          - eapply NbeEq; eassumption. }
        apply asnf_sigma; [exact HA0eq|].
        eapply Hrel.
        -- eapply CtxNbe; [exact HAeq|exact HWA1].
        -- exact HWB1.
Qed.

(* The nf-level form: the algorithmic normal-form relation is complete
   for declarative subtyping between the readback normal forms. *)
Lemma alg_subtyping_nf_complete : forall Γ A B WA WB,
  nbe_ty Γ A WA -> nbe_ty Γ B WB ->
  {{ Γ ⊢ A ⊆ B }} -> {{ ⊢anf WA ⊆ WB }}.
Proof.
  intros Γ A B WA WB HWA HWB H.
  destruct (wf_subtyp_complete_core Γ A B H) as [_ [_ Hrel]].
  eapply Hrel; eassumption.
Qed.

(* Special case where the nf endpoints are stable under readback. *)
Lemma alg_subtyping_nf_complete_self : forall Γ (A B : nf),
  nbe_ty Γ A A -> nbe_ty Γ B B ->
  {{ Γ ⊢ A ⊆ B }} -> {{ ⊢anf A ⊆ B }}.
Proof.
  intros Γ A B HAA HBB H.
  eapply alg_subtyping_nf_complete; eassumption.
Qed.

(* Requested step 1: endpoint transport of declarative subtyping over
   the equalities supplied by NTS.  Note that this needs syntactic
   typing of the two endpoints; the final SubComplete proof below does
   not need this lemma and hence does not need that presupposition. *)
Lemma subtyping_endpoint_transport : forall Γ A B (A' B' : nf) i j,
  {{ Γ ⊢ A ⊆ B }} ->
  {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ B : Type@j }} ->
  nbe_ty Γ A A' -> nbe_ty Γ B B' ->
  {{ Γ ⊢ A' ⊆ B' }}.
Proof.
  intros Γ A B A' B' i j Hsub HA HB Hnba Hnbb.
  destruct (NTS Γ A A' i Hnba HA) as [HA' HeqA].
  destruct (NTS Γ B B' j Hnbb HB) as [HB' HeqB].
  assert (HAB' : {{ Γ ⊢ A ⊆ B' }}).
  { eapply wf_subtyp_eq_right with (A := A) (B := B) (B' := B') (i := j).
    - exact Hsub.
    - exact HeqB.
    - exact HB'. }
  eapply wf_subtyp_eq_left with (A := A') (A' := A) (B := B') (i := i).
  - apply wf_exp_eq_sym. exact HeqA.
  - exact HA.
  - exact HAB'.
Qed.

Theorem SubComplete : forall Γ A B,
  {{ Γ ⊢ A ⊆ B }} -> alg_subtyping Γ A B.
Proof.
  intros Γ A B H.
  destruct (wf_subtyp_complete_core Γ A B H) as
      [[WA HWA] [[WB HWB] Hrel]].
  eapply alg_subtyp_run.
  - exact HWA.
  - exact HWB.
  - eapply Hrel; [exact HWA|exact HWB].
Qed.

End SubtypingCompleteness.

Print Assumptions SubComplete.

(* ============================================================ *)
(* Completeness of user-expression inference (conditional)      *)
(* ============================================================ *)

Definition nf_head (B : nf) : nat :=
  match B with
  | nf_typ _ => 0
  | nf_nat => 1
  | nf_pi _ _ => 2
  | nf_sigma _ _ => 3
  | nf_eq _ _ _ => 4
  | nf_neut _ => 5
  | _ => 6
  end.

(* --- scoping of expressions --------------------------------- *)
(* scoped_exp n M : all free de Bruijn variables of M are < n.
   The a_sub case is deliberately permissive: substitutions are never
   part of a normal form, so only the wf_exp_sub rule needs it, where
   the goal is trivially True.                                    *)

Fixpoint scoped_exp (n : nat) (M : exp) : Prop :=
  match M with
  | a_typ _ => True
  | a_nat => True
  | a_zero => True
  | a_succ M => scoped_exp n M
  | a_natrec A MZ MS M =>
      scoped_exp (S n) A /\ scoped_exp n MZ /\
      scoped_exp (S (S n)) MS /\ scoped_exp n M
  | a_pi A B => scoped_exp n A /\ scoped_exp (S n) B
  | a_fn A M => scoped_exp n A /\ scoped_exp (S n) M
  | a_app M N => scoped_exp n M /\ scoped_exp n N
  | a_sigma A B => scoped_exp n A /\ scoped_exp (S n) B
  | a_pair M A N B =>
      scoped_exp n M /\ scoped_exp n A /\
      scoped_exp n N /\ scoped_exp (S n) B
  | a_fst M => scoped_exp n M
  | a_snd M => scoped_exp n M
  | a_eq A M N => scoped_exp n A /\ scoped_exp n M /\ scoped_exp n N
  | a_refl A M => scoped_exp n A /\ scoped_exp n M
  | a_eqrec A B BR M1 M2 N =>
      scoped_exp n A /\ scoped_exp (S (S (S n))) B /\
      scoped_exp (S n) BR /\ scoped_exp n M1 /\
      scoped_exp n M2 /\ scoped_exp n N
  | a_var x => x < n
  | a_sub _ _ => True
  end.

Lemma ctx_lookup_bound : forall Γ x A,
  {{ #x : A ∈ Γ }} -> x < length Γ.
Proof.
  intros Γ x A H. induction H as [B Γ0 | n A0 B Γ0 Hlk IH].
  - simpl. lia.
  - simpl. lia.
Qed.

Lemma wf_exp_scoped : forall Γ M A,
  {{ Γ ⊢ M : A }} -> scoped_exp (length Γ) M.
Proof.
  intros Γ M A H. induction H using wf_exp_ind.
  - simpl. exact I.
  - simpl. exact I.
  - simpl. exact I.
  - simpl. assumption.
  - simpl. repeat split; assumption.
  - simpl. split; assumption.
  - simpl. split; assumption.
  - simpl. split; assumption.
  - simpl. split; assumption.
  - simpl. repeat split; assumption.
  - simpl. assumption.
  - simpl. assumption.
  - simpl. eapply ctx_lookup_bound; eassumption.
  - simpl. repeat split; assumption.
  - simpl. split; assumption.
  - simpl. repeat split; assumption.
  - simpl. exact I.
  - simpl. assumption.
Qed.

(* --- evaluation of a scoped neutral normal form -------------- *)

Lemma eval_natrec_neut_dom : forall A MZ MS (a : domain) w ρ r,
  eval_natrec A MZ MS (d_neut a w) ρ r -> exists a' w', r = d_neut a' w'.
Proof. intros. inversion H; subst; try discriminate; eauto. Qed.

Lemma eval_app_neut_dom : forall (a : domain) w n r,
  eval_app (d_neut a w) n r -> exists b w', r = d_neut b w'.
Proof. intros. inversion H; subst; try discriminate; eauto. Qed.

Lemma eval_fst_neut_dom : forall (a : domain) w r,
  eval_fst (d_neut a w) r -> exists b w', r = d_neut b w'.
Proof. intros. inversion H; subst; try discriminate; eauto. Qed.

Lemma eval_snd_neut_dom : forall (a : domain) w r,
  eval_snd (d_neut a w) r -> exists b w', r = d_neut b w'.
Proof. intros. inversion H; subst; try discriminate; eauto. Qed.

Lemma eval_eqrec_neut_dom : forall (a : domain) B BR m1 m2 (c : domain) n ρ r,
  eval_eqrec a B BR m1 m2 (d_neut c n) ρ r -> exists b w', r = d_neut b w'.
Proof. intros. inversion H; subst; try discriminate; eauto. Qed.

Lemma eval_ne_initial : forall Γ (ne : ne) ρ mdom,
  scoped_exp (length Γ) (ne_to_exp ne) -> initial_env Γ ρ ->
  eval_exp (ne_to_exp ne) ρ mdom -> exists a w, mdom = d_neut a w.
Proof.
  intros Γ ne. induction ne as
    [ A MZ MS mne IH
    | mne IH Nnf
    | mne IH
    | mne IH
    | x
    | A B BR M1 M2 mne IH ]; intros ρ mdom Hsc Hie Hev.
  - (* ne_natrec *)
    simpl in Hsc.
    destruct Hsc as [HA [HMZ [HMS HM]]].
    inversion Hev; subst.
    match goal with He : eval_exp (ne_to_exp mne) _ _ |- _ =>
      destruct (IH _ _ HM Hie He) as [a [w Hw]] end.
    subst.
    match goal with Hn : eval_natrec _ _ _ (d_neut _ _) _ _ |- _ =>
      eapply eval_natrec_neut_dom; exact Hn end.
  - (* ne_app *)
    simpl in Hsc. destruct Hsc as [HM _].
    inversion Hev; subst.
    match goal with He : eval_exp (ne_to_exp mne) _ _ |- _ =>
      destruct (IH _ _ HM Hie He) as [a [w Hw]] end.
    subst.
    match goal with Ha : eval_app (d_neut _ _) _ _ |- _ =>
      eapply eval_app_neut_dom; exact Ha end.
  - (* ne_fst *)
    simpl in Hsc.
    inversion Hev; subst.
    match goal with He : eval_exp (ne_to_exp mne) _ _ |- _ =>
      destruct (IH _ _ Hsc Hie He) as [a [w Hw]] end.
    subst.
    match goal with Hf : eval_fst (d_neut _ _) _ |- _ =>
      eapply eval_fst_neut_dom; exact Hf end.
  - (* ne_snd *)
    simpl in Hsc.
    inversion Hev; subst.
    match goal with He : eval_exp (ne_to_exp mne) _ _ |- _ =>
      destruct (IH _ _ Hsc Hie He) as [a [w Hw]] end.
    subst.
    match goal with Hf : eval_snd (d_neut _ _) _ |- _ =>
      eapply eval_snd_neut_dom; exact Hf end.
  - (* ne_var *)
    simpl in Hsc.
    inversion Hev; subst.
    destruct (initial_env_lookup Γ ρ Hie x Hsc) as [b Hb].
    eexists; eexists; exact Hb.
  - (* ne_eqrec *)
    simpl in Hsc.
    destruct Hsc as [HA [HB [HBR [HM1 [HM2 HM]]]]].
    inversion Hev; subst.
    lazymatch goal with He : eval_exp (ne_to_exp mne) _ _ |- _ =>
      destruct (IH _ _ HM Hie He) as [da [dw Hw]] end.
    subst.
    match goal with Hn : eval_eqrec _ _ _ _ _ (d_neut _ _) _ _ |- _ =>
      eapply eval_eqrec_neut_dom; exact Hn end.
Qed.

(* --- head preservation for normal forms ---------------------- *)

Lemma nbe_ty_nf_head_scoped : forall Γ (B : nf) W,
  scoped_exp (length Γ) B -> nbe_ty Γ B W -> nf_head B = nf_head W.
Proof.
  intros Γ B W Hsc Hn.
  destruct B as [i| | |M0|A0 B0|A0 M0|A0 B0|M0 A0 N0 B0|A0 M0 N0|A0 M0|ne].
  - (* nf_typ *) simpl in *. apply nbe_ty_typ in Hn. subst. reflexivity.
  - (* nf_nat *) simpl in *. apply nbe_ty_nat in Hn. subst. reflexivity.
  - (* nf_zero *)
    simpl in *. inversion Hn; subst.
    match goal with He : eval_exp a_zero _ _ |- _ => inversion He; subst end.
    match goal with Hr : read_typ _ d_zero _ |- _ => inversion Hr end.
  - (* nf_succ *)
    simpl in *. inversion Hn; subst.
    match goal with He : eval_exp (a_succ _) _ _ |- _ => inversion He; subst end.
    match goal with Hr : read_typ _ (d_succ _) _ |- _ => inversion Hr end.
  - (* nf_pi *) simpl in *. apply nbe_ty_pi in Hn.
    destruct Hn as [W0 [W1 [Heq _]]]. subst. reflexivity.
  - (* nf_fn *)
    simpl in *. inversion Hn; subst.
    match goal with He : eval_exp (a_fn _ _) _ _ |- _ => inversion He; subst end.
    match goal with Hr : read_typ _ (d_fn _ _) _ |- _ => inversion Hr end.
  - (* nf_sigma *) simpl in *. apply nbe_ty_sigma in Hn.
    destruct Hn as [W0 [W1 [Heq _]]]. subst. reflexivity.
  - (* nf_pair *)
    simpl in *. inversion Hn; subst.
    match goal with He : eval_exp (a_pair _ _ _ _) _ _ |- _ => inversion He; subst end.
    match goal with Hr : read_typ _ (d_pair _ _) _ |- _ => inversion Hr end.
  - (* nf_eq *) simpl in *. apply nbe_ty_eq in Hn.
    destruct Hn as [W0 [W1 [W2 [Heq _]]]]. subst. reflexivity.
  - (* nf_refl *)
    simpl in *. inversion Hn; subst.
    match goal with He : eval_exp (a_refl _ _) _ _ |- _ => inversion He; subst end.
    match goal with Hr : read_typ _ (d_refl _) _ |- _ => inversion Hr end.
  - (* nf_neut *)
    simpl in *. inversion Hn; subst.
    match goal with Hie : initial_env Γ _ |- _ =>
      match goal with He : eval_exp (ne_to_exp ne) _ _ |- _ =>
        destruct (eval_ne_initial Γ ne _ _ Hsc Hie He) as [a [w Hw]] end end.
    subst.
    match goal with Hr : read_typ _ (d_neut _ _) _ |- _ =>
      inversion Hr; subst; reflexivity end.
Qed.

Lemma nf_head_zero : forall (B : nf), nf_head B = 0 -> exists i, B = nf_typ i.
Proof.
  intros B. destruct B; simpl; intros H; try discriminate; eauto.
Qed.

Lemma nbe_ty_nf_head : forall Γ (B : nf) W j,
  {{ ⊢ Γ }} -> {{ Γ ⊢ B : Type@j }} ->
  nbe_ty Γ B W -> nf_head B = nf_head W.
Proof.
  intros Γ B W j Hwf HBty Hn.
  eapply nbe_ty_nf_head_scoped.
  - exact (wf_exp_scoped Γ B (a_typ j) HBty).
  - exact Hn.
Qed.

Section InferCompleteSection.

Hypothesis NTS : forall Γ A W i,
  nbe_ty Γ A W -> {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ W : Type@i }} /\ {{ Γ ⊢ A ≈ W : Type@i }}.
Hypothesis NTmS : forall Γ M A W,
  nbe Γ M A W -> {{ Γ ⊢ M : A }} ->
  {{ Γ ⊢ W : A }} /\ {{ Γ ⊢ M ≈ W : A }}.
Hypothesis TyEx : forall Γ A i, {{ Γ ⊢ A : Type@i }} -> exists W, nbe_ty Γ A W.
Hypothesis TmEx : forall Γ M A, {{ Γ ⊢ M : A }} -> exists W, nbe Γ M A W.
Hypothesis SubComplete : forall Γ A B, {{ Γ ⊢ A ⊆ B }} -> alg_subtyping Γ A B.
Hypothesis InferUniv : forall Γ M B i,
  alg_type_infer Γ B M -> {{ Γ ⊢ M : Type@i }} -> exists j, B = nf_typ j.

Lemma atc_of_ati : forall Γ B M T,
  alg_type_infer Γ B M -> {{ Γ ⊢ B ⊆ T }} -> alg_type_check Γ T M.
Proof.
  intros. eapply atc_ati; [ exact H | eapply SubComplete; exact H0 ].
Qed.

Lemma alg_infer_sound : forall Γ B M,
  alg_type_infer Γ B M -> {{ ⊢ Γ }} ->
  exists i, {{ Γ ⊢ M : B }} /\ {{ Γ ⊢ B : Type@i }}.
Proof.
  intros. exact (proj2 (infer_check_sound NTS NTmS) Γ B M H H0).
Qed.

Lemma subtyp_nbe_ty : forall Γ T W i,
  nbe_ty Γ T W -> {{ Γ ⊢ T : Type@i }} -> {{ Γ ⊢ W ⊆ T }}.
Proof.
  intros Γ T W i Hn HT.
  destruct (NTS Γ T W i Hn HT) as [HW Heq].
  eapply wf_subtyp_refl with (M := W) (M' := T) (i := i).
  - exact HT.
  - apply wf_exp_eq_sym. exact Heq.
Qed.

Lemma alg_subtyping_nf_typ_le : forall A B i j,
  {{ ⊢anf A ⊆ B }} -> A = nf_typ i -> B = nf_typ j -> i <= j.
Proof.
  intros A B i j H.
  induction H as
    [ A0 A0' Hn Heq
    | i0 j0 Hle
    | A0 B0 A0' B0' Heq Hsub IH
    | A0 B0 A0' B0' Heq Hsub IH ]; intros HA HB.
  - subst A0'. subst A0. simpl in Hn. destruct Hn.
  - inversion HA. inversion HB. subst. assumption.
  - inversion HA.
  - inversion HA.
Qed.

Lemma alg_subtyping_typ_typ_le : forall Γ i j,
  alg_subtyping Γ (a_typ i) (a_typ j) -> i <= j.
Proof.
  intros Γ i j H.
  inversion H; subst.
  match goal with
  | Hna : nbe_ty Γ (a_typ i) ?A' |- _ =>
      apply nbe_ty_typ in Hna; subst A'
  end.
  match goal with
  | Hnb : nbe_ty Γ (a_typ j) ?B' |- _ =>
      apply nbe_ty_typ in Hnb; subst B'
  end.
  eapply alg_subtyping_nf_typ_le; [ eassumption | reflexivity | reflexivity ].
Qed.

Lemma wf_subtyp_univ_level : forall Γ i j,
  {{ Γ ⊢ Type@i ⊆ Type@j }} -> i <= j.
Proof.
  intros. eapply alg_subtyping_typ_typ_le. eapply SubComplete. exact H.
Qed.

Lemma common_nbe_eq : forall Γ A B W i j u,
  nbe_ty Γ A W -> nbe_ty Γ B W ->
  {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ B : Type@j }} ->
  i <= u -> j <= u -> {{ Γ ⊢ A ≈ B : Type@u }}.
Proof.
  intros Γ A B W i j u HA HB HTA HTB Hiu Hju.
  destruct (NTS Γ A W i HA HTA) as [_ HeqA].
  destruct (NTS Γ B W j HB HTB) as [_ HeqB].
  assert (HeqAu : {{ Γ ⊢ A ≈ W : Type@u }})
    by (eapply wf_exp_eq_raise_univ; [ exact HTA | exact HeqA | exact Hiu ]).
  assert (HeqBu : {{ Γ ⊢ B ≈ W : Type@u }})
    by (eapply wf_exp_eq_raise_univ; [ exact HTB | exact HeqB | exact Hju ]).
  eapply wf_exp_eq_trans; [ exact HeqAu | apply wf_exp_eq_sym; exact HeqBu ].
Qed.

Lemma common_nbe_subtyp : forall Γ A B W i j,
  nbe_ty Γ A W -> nbe_ty Γ B W ->
  {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ B : Type@j }} -> {{ Γ ⊢ A ⊆ B }}.
Proof.
  intros Γ A B W i j HA HB HTA HTB.
  set (u := Nat.max i j).
  assert (Hiu : i <= u) by (unfold u; lia).
  assert (Hju : j <= u) by (unfold u; lia).
  assert (HTBu : {{ Γ ⊢ B : Type@u }}) by (eapply wf_exp_cumul; [ exact Hju | exact HTB ]).
  assert (Heq : {{ Γ ⊢ A ≈ B : Type@u }})
    by (eapply common_nbe_eq; [ exact HA | exact HB | exact HTA | exact HTB | exact Hiu | exact Hju ]).
  eapply wf_subtyp_of_eq; [ exact Heq | exact HTBu ].
Qed.

Lemma asnf_sigma_inv : forall A X Y,
  {{ ⊢anf A ⊆ Σ X Y }} ->
  exists A2, A = nf_sigma X A2 /\ {{ ⊢anf A2 ⊆ Y }}.
Proof.
  intros A X Y H. inversion H; subst.
  - match goal with Hn : not_univ_pi_sigma ?Z |- _ => simpl in Hn; destruct Hn end.
  - eexists. split; [ reflexivity | eassumption ].
Qed.

Lemma asnf_pi_inv : forall A X Y,
  {{ ⊢anf A ⊆ Π X Y }} ->
  exists A2, A = nf_pi X A2 /\ {{ ⊢anf A2 ⊆ Y }}.
Proof.
  intros A X Y H. inversion H; subst.
  - match goal with Hn : not_univ_pi_sigma ?Z |- _ => simpl in Hn; destruct Hn end.
  - eexists. split; [ reflexivity | eassumption ].
Qed.

Lemma nbe_ty_nf_pi : forall Γ (B : nf) X Y j,
  {{ ⊢ Γ }} -> {{ Γ ⊢ B : Type@j }} ->
  nbe_ty Γ B (nf_pi X Y) -> exists B1 B2, B = nf_pi B1 B2.
Proof.
  intros Γ B X Y j Hwf HBty Hn.
  pose proof (nbe_ty_nf_head Γ B (nf_pi X Y) j Hwf HBty Hn) as Hh.
  destruct B as [i| | |M0|B0 C0|A0 M0|B0 C0|M0 A0 N0 C0|A0 M0 N0|A0 M0|ne];
    simpl in Hh; try discriminate.
  - exists B0, C0. reflexivity.
Qed.

Lemma nbe_ty_nf_sigma : forall Γ (B : nf) X Y j,
  {{ ⊢ Γ }} -> {{ Γ ⊢ B : Type@j }} ->
  nbe_ty Γ B (nf_sigma X Y) -> exists B1 B2, B = nf_sigma B1 B2.
Proof.
  intros Γ B X Y j Hwf HBty Hn.
  pose proof (nbe_ty_nf_head Γ B (nf_sigma X Y) j Hwf HBty Hn) as Hh.
  destruct B as [i| | |M0|B0 C0|A0 M0|B0 C0|M0 A0 N0 C0|A0 M0 N0|A0 M0|ne];
    simpl in Hh; try discriminate.
  - exists B0, C0. reflexivity.
Qed.

Lemma alg_infer_pi_decomp : forall Γ (B : nf) M T1 T2,
  {{ ⊢ Γ }} -> alg_type_infer Γ B M -> {{ Γ ⊢ B ⊆ Π T1 T2 }} ->
  exists B1 B2 W1 W2 V2,
    B = nf_pi B1 B2 /\
    nbe_ty Γ B1 W1 /\ nbe_ty Γ T1 W1 /\
    nbe_ty ((B1 : exp) :: Γ) B2 W2 /\ nbe_ty (T1 :: Γ) T2 V2 /\
    {{ ⊢anf W2 ⊆ V2 }}.
Proof.
  intros Γ B M T1 T2 Hwf Hinf Hsub.
  destruct (alg_infer_sound Γ B M Hinf Hwf) as [jB [HMB HBTy]].
  pose proof (SubComplete _ _ _ Hsub) as Ha.
  inversion Ha as [Γ0 A B0 A' B' Hna Hnb Hnf]; subst.
  destruct (nbe_ty_pi Γ T1 T2 B' Hnb) as [V1 [V2 [HB' [HT1V1 HT2V2]]]]; subst B'.
  destruct (asnf_pi_inv A' V1 V2 Hnf) as [A2 [HA' Hasnf]]; subst A'.
  destruct (nbe_ty_nf_pi Γ B V1 A2 jB Hwf HBTy Hna) as [B1 [B2 HB]]; subst B.
  destruct (nbe_ty_pi Γ B1 B2 (nf_pi V1 A2) Hna) as [W1 [W2 [Heq [HnB1 HnB2]]]].
  injection Heq as HV HW; subst.
  exists B1, B2, W1, W2, V2. split; [ reflexivity | ].
  split; [ exact HnB1 | ]. split; [ exact HT1V1 | ].
  split; [ exact HnB2 | ]. split; [ exact HT2V2 | exact Hasnf ].
Qed.

Lemma alg_infer_sigma_decomp : forall Γ (B : nf) M T1 T2,
  {{ ⊢ Γ }} -> alg_type_infer Γ B M -> {{ Γ ⊢ B ⊆ Σ T1 T2 }} ->
  exists B1 B2 W1 W2 V2,
    B = nf_sigma B1 B2 /\
    nbe_ty Γ B1 W1 /\ nbe_ty Γ T1 W1 /\
    nbe_ty ((B1 : exp) :: Γ) B2 W2 /\ nbe_ty (T1 :: Γ) T2 V2 /\
    {{ ⊢anf W2 ⊆ V2 }}.
Proof.
  intros Γ B M T1 T2 Hwf Hinf Hsub.
  destruct (alg_infer_sound Γ B M Hinf Hwf) as [jB [HMB HBTy]].
  pose proof (SubComplete _ _ _ Hsub) as Ha.
  inversion Ha as [Γ0 A B0 A' B' Hna Hnb Hnf]; subst.
  destruct (nbe_ty_sigma Γ T1 T2 B' Hnb) as [V1 [V2 [HB' [HT1V1 HT2V2]]]]; subst B'.
  destruct (asnf_sigma_inv A' V1 V2 Hnf) as [A2 [HA' Hasnf]]; subst A'.
  destruct (nbe_ty_nf_sigma Γ B V1 A2 jB Hwf HBTy Hna) as [B1 [B2 HB]]; subst B.
  destruct (nbe_ty_sigma Γ B1 B2 (nf_sigma V1 A2) Hna) as [W1 [W2 [Heq [HnB1 HnB2]]]].
  injection Heq as HV HW; subst.
  exists B1, B2, W1, W2, V2. split; [ reflexivity | ].
  split; [ exact HnB1 | ]. split; [ exact HT1V1 | ].
  split; [ exact HnB2 | ]. split; [ exact HT2V2 | exact Hasnf ].
Qed.

Lemma subtyp_second_transport : forall Γ (B1 T1 B2 T2 : typ) i j W2 V2,
  {{ Γ ⊢ B1 ≈ T1 : Type@i }} ->
  {{ Γ ⊢ B1 : Type@i }} -> {{ Γ ⊢ T1 : Type@i }} ->
  {{ Γ, B1 ⊢ B2 : Type@j }} -> {{ Γ, T1 ⊢ T2 : Type@j }} ->
  nbe_ty ((B1 : exp) :: Γ) B2 W2 -> nbe_ty (T1 :: Γ) T2 V2 ->
  {{ ⊢anf W2 ⊆ V2 }} ->
  {{ Γ, T1 ⊢ B2 ⊆ T2 }}.
Proof.
  intros Γ B1 T1 B2 T2 i j W2 V2 Heq HB1 HT1 HB2 HT2 HnB2 HnT2 Hasnf.
  destruct (NTS _ _ _ j HnB2 HB2) as [HW2 HeqB2].
  destruct (NTS _ _ _ j HnT2 HT2) as [HV2 HeqT2].
  assert (HctxEq : {{ ⊢ Γ, B1 ≈ Γ, T1 }}).
  { eapply wf_ctx_eq_extend.
    - apply wf_ctx_eq_refl. eapply wf_exp_ctx. exact HB1.
    - exact HB1. - exact HT1. - exact HB1. - exact HT1.
    - exact Heq. - exact Heq. }
  assert (HW2' : {{ Γ, T1 ⊢ W2 : Type@j }}).
  { exact (proj1 (proj2 (proj2 ctx_eq_transport_all)) _ _ _ HW2 _ HctxEq). }
  assert (HeqB2' : {{ Γ, T1 ⊢ B2 ≈ W2 : Type@j }}).
  { exact (proj1 (proj2 (proj2 (proj2 ctx_eq_transport_all))) _ _ _ _ HeqB2 _ HctxEq). }
  assert (HWV : {{ Γ, T1 ⊢ W2 ⊆ V2 }}).
  { eapply asnf_sound; [ exact Hasnf | exists j; exact HW2' | exists j; exact HV2 ]. }
  eapply wf_subtyp_trans; [ | eapply wf_subtyp_trans; [ exact HWV | ] ].
  - eapply wf_subtyp_of_eq; [ exact HeqB2' | exact HW2' ].
  - eapply wf_subtyp_of_eq; [ apply wf_exp_eq_sym; exact HeqT2 | exact HT2 ].
Qed.

Lemma InferCompleteUserStmt_conditional : InferCompleteUserStmt.
Proof.
  unfold InferCompleteUserStmt.
  intros M Hu.
  induction Hu as
    [ i
    |
    |
    | Mn HuMn IHMn
    | An MZn MSn Mn HuAn IHA HuMZn IHMZ HuMSn IHMS HuMn IHM
    | An Bn HuAn IHA HuBn IHB
    | An Mn HuAn IHA HuMn IHM
    | Mn Nn HuMn IHM HuNn IHN
    | An Bn HuAn IHA HuBn IHB
    | Mn An Nn Bn HuMn IHM HuAn IHA HuNn IHN HuBn IHB
    | Mn HuMn IHM
    | Mn HuMn IHM
    | An M1 M2 HuAn IHA HuM1 IHM1 HuM2 IHM2
    | An Mn HuAn IHA HuMn IHM
    | An Bn BRn M1 M2 Nn HuAn IHA HuBn IHB HuBRn IHBR HuM1 IHM1 HuM2 IHM2 HuNn IHN
    | x ].
  all: intros Γ A HM.
  - (* BRtyp *)
    destruct (user_typing_shape Γ A (a_typ i) (user_exp_typ i) HM) as [T0 [Hs Hsub]].
    inversion Hs; subst; clear Hs.
    exists (nf_typ (S i)). split.
    + apply ati_typ.
    + exact Hsub.
  - (* BRnat *)
    destruct (user_typing_shape Γ A a_nat user_exp_nat HM) as [T0 [Hs Hsub]].
    inversion Hs; subst; clear Hs.
    exists (nf_typ 0). split.
    + apply ati_nat.
    + exact Hsub.
  - (* BRzero *)
    destruct (user_typing_shape Γ A a_zero user_exp_zero HM) as [T0 [Hs Hsub]].
    inversion Hs; subst; clear Hs.
    exists nf_nat. split.
    + apply ati_zero.
    + exact Hsub.
  - (* BRsucc *)
    destruct (user_typing_shape Γ A (a_succ Mn) (user_exp_succ Mn HuMn) HM) as [T0 [Hs Hsub]].
    inversion Hs; subst; clear Hs.
    assert (Hmn : {{ Γ ⊢ Mn : ℕ }}) by assumption.
    destruct (IHMn Γ a_nat Hmn) as [B [Hinf HsubB]].
    assert (Hchk : alg_type_check Γ a_nat Mn) by (eapply atc_of_ati; [ exact Hinf | exact HsubB ]).
    exists nf_nat. split.
    + apply ati_succ. exact Hchk.
    + exact Hsub.
  - (* BRnatrec *)
    destruct (user_typing_shape Γ A (a_natrec An MZn MSn Mn)
      (user_exp_natrec An MZn MSn Mn HuAn HuMZn HuMSn HuMn) HM) as [T0 [Hs Hsub]].
    destruct (user_shape_type _ _ _ Hs) as [k0 HT0ty].
    inversion Hs; subst; clear Hs.
    assert (HAnTy : {{ Γ, ℕ ⊢ An : Type@i }}) by assumption.
    assert (HMZTy : {{ Γ ⊢ MZn : An[Id,,zero] }}) by assumption.
    assert (HMSTy : {{ Γ, ℕ, An ⊢ MSn : An[Wk∘Wk,,succ #1] }}) by assumption.
    assert (HMTy : {{ Γ ⊢ Mn : ℕ }}) by assumption.
    destruct (IHA (a_nat :: Γ)%list (a_typ i) HAnTy) as [BA [HinfA HsubA]].
    destruct (InferUniv (a_nat :: Γ)%list An BA i HinfA HAnTy) as [j HBA]. subst BA.
    destruct (IHMZ Γ (a_sub An (a_extend a_id a_zero)) HMZTy) as [BMZ [HinfMZ HsubMZ]].
    destruct (IHMS (An :: a_nat :: Γ)%list
      (a_sub An (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) HMSTy)
      as [BMS [HinfMS HsubMS]].
    destruct (IHM Γ a_nat HMTy) as [BM [HinfM HsubM]].
    destruct (TyEx _ _ k0 HT0ty) as [B HB].
    exists B. split.
    + eapply ati_natrec.
      * exact HinfA.
      * eapply atc_of_ati; [ exact HinfMZ | exact HsubMZ ].
      * eapply atc_of_ati; [ exact HinfMS | exact HsubMS ].
      * eapply atc_of_ati; [ exact HinfM | exact HsubM ].
      * exact HB.
    + eapply wf_subtyp_trans; [ | exact Hsub ].
      eapply subtyp_nbe_ty; [ exact HB | exact HT0ty ].
  - (* BRpi *)
    destruct (user_typing_shape Γ A (a_pi An Bn) (user_exp_pi An Bn HuAn HuBn) HM) as [T0 [Hs Hsub]].
    inversion Hs; subst; clear Hs.
    assert (HAnTy : {{ Γ ⊢ An : Type@i }}) by assumption.
    assert (HBnTy : {{ Γ, An ⊢ Bn : Type@i }}) by assumption.
    destruct (IHA Γ (a_typ i) HAnTy) as [BA [HinfA HsubA]].
    destruct (InferUniv Γ An BA i HinfA HAnTy) as [k HBA]. subst BA.
    destruct (IHB (An :: Γ)%list (a_typ i) HBnTy) as [BB [HinfB HsubB]].
    destruct (InferUniv (An :: Γ)%list Bn BB i HinfB HBnTy) as [l HBB]. subst BB.
    assert (Hkle : k <= i) by (eapply alg_subtyping_typ_typ_le; eapply SubComplete; exact HsubA).
    assert (Hlle : l <= i) by (eapply alg_subtyping_typ_typ_le; eapply SubComplete; exact HsubB).
    exists (nf_typ (Nat.max k l)). split.
    + eapply ati_pi; [ exact HinfA | exact HinfB ].
    + assert (HwfΓ : {{ ⊢ Γ }}) by (eapply wf_exp_ctx; exact HM).
      eapply wf_subtyp_trans; [ | exact Hsub ].
      eapply wf_subtyp_univ_le; [ exact HwfΓ | lia ].
  - (* BRfn *)
    destruct (user_typing_shape Γ A (a_fn An Mn) (user_exp_fn An Mn HuAn HuMn) HM) as [T0 [Hs Hsub]].
    inversion Hs; subst; clear Hs.
    assert (HAnTy : {{ Γ ⊢ An : Type@i }}) by assumption.
    assert (HMty : {{ Γ, An ⊢ Mn : B }}) by assumption.
    destruct (IHA Γ (a_typ i) HAnTy) as [BA [HinfA HsubA]].
    destruct (InferUniv Γ An BA i HinfA HAnTy) as [k HBA]. subst BA.
    destruct (IHM (An :: Γ)%list B HMty) as [BM [HinfM HsubM]].
    destruct (TyEx Γ An i HAnTy) as [C HC].
    destruct (NTS Γ An C i HC HAnTy) as [HCty HeqAC].
    destruct (wf_exp_type (An :: Γ)%list B Mn HMty) as [jB HBty].
    assert (HwfΓ : {{ ⊢ Γ }}) by (eapply wf_exp_ctx; exact HM).
    assert (HctxA : {{ ⊢ Γ, An }}) by (eapply wf_ctx_extend; [ exact HwfΓ | exact HAnTy ]).
    destruct (alg_infer_sound (An :: Γ)%list BM Mn HinfM HctxA) as [j [HMnBM HBMty]].
    set (u := Nat.max i (Nat.max j jB)).
    assert (Hiu : i <= u) by (unfold u; lia).
    assert (Hju : j <= u) by (unfold u; lia).
    assert (HjBu : jB <= u) by (unfold u; lia).
    assert (HAnu : {{ Γ ⊢ An : Type@u }}) by (eapply wf_exp_cumul; [ exact Hiu | exact HAnTy ]).
    assert (HCu : {{ Γ ⊢ C : Type@u }}) by (eapply wf_exp_cumul; [ exact Hiu | exact HCty ]).
    assert (HAnCu : {{ Γ ⊢ An ≈ C : Type@u }})
      by (eapply wf_exp_eq_raise_univ; [ exact HAnTy | exact HeqAC | exact Hiu ]).
    assert (HCAnu : {{ Γ ⊢ C ≈ An : Type@u }}) by (apply wf_exp_eq_sym; exact HAnCu).
    assert (HBMu : {{ Γ, An ⊢ BM : Type@u }})
      by (eapply wf_exp_cumul; [ exact Hju | exact HBMty ]).
    assert (HBu : {{ Γ, An ⊢ B : Type@u }})
      by (eapply wf_exp_cumul; [ exact HjBu | exact HBty ]).
    set (Ce := (C : exp)).
    assert (HCBM : {{ Γ, Ce ⊢ BM : Type@u }}).
    { eapply wf_exp_cumul; [ exact Hju | ].
      eapply CtxConvTy_strong with (A := An) (C := C) (i := i);
        [ exact HAnTy | exact HCty | exact HeqAC | exact HBMty ]. }
    exists (nf_pi C BM). split.
    + eapply ati_fn; [ exact HinfA | exact HinfM | exact HC ].
    + eapply wf_subtyp_trans; [ | exact Hsub ].
      eapply wf_subtyp_pi.
      * exact HCu.
      * exact HAnu.
      * exact HCAnu.
      * exact HCBM.
      * exact HBu.
      * exact HsubM.
  - (* BRapp *)
    destruct (user_typing_shape Γ A (a_app Mn Nn) (user_exp_app Mn Nn HuMn HuNn) HM) as [T0 [Hs Hsub]].
    destruct (user_shape_type _ _ _ Hs) as [k0 HT0ty].
    inversion Hs; subst; clear Hs.
    match goal with
    | HAnTy : wf_exp Γ (a_typ ?iA) ?XA |- _ =>
      match goal with
      | HBnTy : wf_exp (cons XA Γ) (a_typ ?iB) ?XB |- _ =>
        match goal with
        | HMty : wf_exp Γ (a_pi XA XB) Mn |- _ =>
          match goal with
          | HNty : wf_exp Γ XA Nn |- _ =>
            assert (HwfΓ : {{ ⊢ Γ }}) by (eapply wf_exp_ctx; exact HM);
            destruct (IHM Γ (a_pi XA XB) HMty) as [BM [HinfM HsubM]];
            destruct (alg_infer_pi_decomp Γ BM Mn XA XB HwfΓ HinfM HsubM) as
              [B1 [B2 [W1 [W2 [V2 [HBM [HnB1 [HnT1 [HnB2 [HnT2 Hasnf]]]]]]]]]];
            destruct (alg_infer_sound Γ BM Mn HinfM HwfΓ) as [jM [HMnBM HBMty]];
            subst BM;
            destruct (wf_pi_typing_inv Γ B1 B2 (a_typ jM) HBMty) as [iB1 [iB2 [HB1ty HB2ty]]];
            set (u1 := Nat.max iB1 iA);
            assert (Hu1iB : iB1 <= u1) by (unfold u1; lia);
            assert (Hu1i : iA <= u1) by (unfold u1; lia);
            assert (HB1XA : {{ Γ ⊢ B1 ≈ XA : Type@u1 }})
              by (eapply common_nbe_eq; [ exact HnB1 | exact HnT1 | exact HB1ty | exact HAnTy | exact Hu1iB | exact Hu1i ]);
            assert (HB1u : {{ Γ ⊢ B1 : Type@u1 }}) by (eapply wf_exp_cumul; [ exact Hu1iB | exact HB1ty ]);
            assert (HXAu : {{ Γ ⊢ XA : Type@u1 }}) by (eapply wf_exp_cumul; [ exact Hu1i | exact HAnTy ]);
            assert (HNnB1 : {{ Γ ⊢ Nn : B1 }})
              by (eapply wf_exp_conv; [ exact HNty | apply wf_exp_eq_sym; exact HB1XA | exact HB1u ]);
            destruct (IHN Γ B1 HNnB1) as [BN [HinfN HsubN]];
            assert (HchkN : alg_type_check Γ B1 Nn) by (eapply atc_of_ati; [ exact HinfN | exact HsubN ]);
            set (B1e := (B1 : exp));
            assert (HσB1 : {{ Γ ⊢s Id,,Nn : Γ, B1e }})
              by (eapply wf_sub_extend_id_self; [ exact HNnB1 | exact HB1ty ]);
            assert (HB2sigty : {{ Γ ⊢ B2[Id,,Nn] : Type@iB2 }})
              by (eapply wf_subst_type; [ exact HσB1 | exact HB2ty ]);
            destruct (TyEx Γ (a_sub B2 (a_extend a_id Nn)) iB2 HB2sigty) as [CC HCC];
            exists CC; split;
            [ eapply ati_app; [ exact HinfM | exact HchkN | exact HCC ]
            | set (u2 := Nat.max iB2 iB);
              assert (Hu2iB : iB2 <= u2) by (unfold u2; lia);
              assert (Hu2i : iB <= u2) by (unfold u2; lia);
              assert (HB2u : {{ Γ, B1e ⊢ B2 : Type@u2 }})
                by (eapply wf_exp_cumul; [ exact Hu2iB | exact HB2ty ]);
              assert (HXBu : {{ Γ, XA ⊢ XB : Type@u2 }})
                by (eapply wf_exp_cumul; [ exact Hu2i | exact HBnTy ]);
              assert (Hsub2 : {{ Γ, XA ⊢ B2 ⊆ XB }})
                by (eapply subtyp_second_transport;
                      [ exact HB1XA | exact HB1u | exact HXAu | exact HB2u | exact HXBu | exact HnB2 | exact HnT2 | exact Hasnf ]);
              assert (HσXA : {{ Γ ⊢s Id,,Nn : Γ, XA }})
                by (eapply wf_sub_extend_id_self; [ exact HNty | exact HAnTy ]);
              assert (Hsub2sig : {{ Γ ⊢ B2[Id,,Nn] ⊆ XB[Id,,Nn] }})
                by (eapply wf_subtyp_subst; [ exact HσXA | exact Hsub2 ]);
              eapply wf_subtyp_trans; [ | exact Hsub ];
              eapply wf_subtyp_trans; [ | exact Hsub2sig ];
              eapply wf_subtyp_of_eq;
              [ destruct (NTS Γ (a_sub B2 (a_extend a_id Nn)) CC iB2 HCC HB2sigty) as [_ HeqC];
                apply wf_exp_eq_sym; exact HeqC
              | exact HB2sigty ] ]
          end
        end
      end
    end.
  - (* BRsigma *)
    destruct (user_typing_shape Γ A (a_sigma An Bn) (user_exp_sigma An Bn HuAn HuBn) HM) as [T0 [Hs Hsub]].
    inversion Hs; subst; clear Hs.
    assert (HAnTy : {{ Γ ⊢ An : Type@i }}) by assumption.
    assert (HBnTy : {{ Γ, An ⊢ Bn : Type@i }}) by assumption.
    destruct (IHA Γ (a_typ i) HAnTy) as [BA [HinfA HsubA]].
    destruct (InferUniv Γ An BA i HinfA HAnTy) as [k HBA]. subst BA.
    destruct (IHB (An :: Γ)%list (a_typ i) HBnTy) as [BB [HinfB HsubB]].
    destruct (InferUniv (An :: Γ)%list Bn BB i HinfB HBnTy) as [l HBB]. subst BB.
    assert (Hkle : k <= i) by (eapply alg_subtyping_typ_typ_le; eapply SubComplete; exact HsubA).
    assert (Hlle : l <= i) by (eapply alg_subtyping_typ_typ_le; eapply SubComplete; exact HsubB).
    exists (nf_typ (Nat.max k l)). split.
    + eapply ati_sigma; [ exact HinfA | exact HinfB ].
    + assert (HwfΓ : {{ ⊢ Γ }}) by (eapply wf_exp_ctx; exact HM).
      eapply wf_subtyp_trans; [ | exact Hsub ].
      eapply wf_subtyp_univ_le; [ exact HwfΓ | lia ].
  - (* BRpair *)
    destruct (user_typing_shape Γ A (a_pair Mn An Nn Bn)
      (user_exp_pair Mn An Nn Bn HuMn HuAn HuNn HuBn) HM) as [T0 [Hs Hsub]].
    inversion Hs; subst; clear Hs.
    assert (HAnTy : {{ Γ ⊢ An : Type@i }}) by assumption.
    assert (HBnTy : {{ Γ, An ⊢ Bn : Type@i }}) by assumption.
    assert (HMty : {{ Γ ⊢ Mn : An }}) by assumption.
    assert (HNty : {{ Γ ⊢ Nn : Bn[Id,,Mn] }}) by assumption.
    destruct (IHA Γ (a_typ i) HAnTy) as [BA [HinfA HsubA]].
    destruct (InferUniv Γ An BA i HinfA HAnTy) as [k HBA]. subst BA.
    destruct (IHB (An :: Γ)%list (a_typ i) HBnTy) as [BB [HinfB HsubB]].
    destruct (InferUniv (An :: Γ)%list Bn BB i HinfB HBnTy) as [l HBB]. subst BB.
    destruct (IHM Γ An HMty) as [BM [HinfM HsubM]].
    destruct (IHN Γ (a_sub Bn (a_extend a_id Mn)) HNty) as [BN [HinfN HsubN]].
    assert (HchkM : alg_type_check Γ An Mn) by (eapply atc_of_ati; [ exact HinfM | exact HsubM ]).
    assert (HchkN : alg_type_check Γ (a_sub Bn (a_extend a_id Mn)) Nn)
      by (eapply atc_of_ati; [ exact HinfN | exact HsubN ]).
    destruct (TyEx Γ An i HAnTy) as [A' HA'].
    destruct (TyEx (An :: Γ)%list Bn i HBnTy) as [C HCty].
    destruct (NTS Γ An A' i HA' HAnTy) as [HA'ty HeqAA'].
    destruct (NTS (An :: Γ)%list Bn C i HCty HBnTy) as [HCty' HeqBC].
    set (A'e := (A' : exp)).
    assert (HC_A' : {{ Γ, A'e ⊢ C : Type@i }}).
    { eapply CtxConvTy_strong with (A := An) (C := A') (i := i);
        [ exact HAnTy | exact HA'ty | exact HeqAA' | exact HCty' ]. }
    assert (HCA' : {{ Γ, An ⊢ C ⊆ Bn }})
      by (eapply wf_subtyp_of_eq; [ apply wf_exp_eq_sym; exact HeqBC | exact HBnTy ]).
    exists (nf_sigma A' C). split.
    + eapply ati_pair; [ exact HinfA | exact HinfB | exact HchkM | exact HchkN | exact HA' | exact HCty ].
    + eapply wf_subtyp_trans; [ | exact Hsub ].
      eapply wf_subtyp_sigma.
      * exact HA'ty.
      * exact HAnTy.
      * apply wf_exp_eq_sym. exact HeqAA'.
      * exact HC_A'.
      * exact HBnTy.
      * exact HCA'.
  - (* BRfst *)
    destruct (user_typing_shape Γ A (a_fst Mn) (user_exp_fst Mn HuMn) HM) as [T0 [Hs Hsub]].
    inversion Hs; subst; clear Hs.
    assert (HDomTy : {{ Γ ⊢ T0 : Type@i }}) by assumption.
    assert (HCodTy : {{ Γ, T0 ⊢ B : Type@i }}) by assumption.
    assert (HMty : {{ Γ ⊢ Mn : Σ T0 B }}) by assumption.
    assert (HwfΓ : {{ ⊢ Γ }}) by (eapply wf_exp_ctx; exact HM).
    destruct (IHM Γ (a_sigma T0 B) HMty) as [BM [HinfM HsubM]].
    destruct (alg_infer_sigma_decomp Γ BM Mn T0 B HwfΓ HinfM HsubM) as
      [B1 [B2 [W1 [W2 [V2 [HBM [HnB1 [HnT1 [HnB2 [HnT2 Hasnf]]]]]]]]]].
    destruct (alg_infer_sound Γ BM Mn HinfM HwfΓ) as [jM [HMnBM HBMty]].
    subst BM.
    destruct (wf_sigma_typing_inv Γ B1 B2 (a_typ jM) HBMty) as [iB1 [iB2 [HB1ty HB2ty]]].
    exists B1. split.
    + eapply ati_fst. exact HinfM.
    + eapply wf_subtyp_trans; [ | exact Hsub ].
      eapply common_nbe_subtyp; [ exact HnB1 | exact HnT1 | exact HB1ty | exact HDomTy ].
  - (* BRsnd *)
    destruct (user_typing_shape Γ A (a_snd Mn) (user_exp_snd Mn HuMn) HM) as [T0 [Hs Hsub]].
    destruct (user_shape_type _ _ _ Hs) as [k0 HT0ty].
    inversion Hs; subst; clear Hs.
    match goal with
    | HDomTy : wf_exp Γ (a_typ ?iA) ?XA |- _ =>
      match goal with
      | HCodTy : wf_exp (cons XA Γ) (a_typ ?iB) ?XB |- _ =>
        match goal with
        | HMty : wf_exp Γ (a_sigma XA XB) Mn |- _ =>
            assert (HwfΓ : {{ ⊢ Γ }}) by (eapply wf_exp_ctx; exact HM);
            destruct (IHM Γ (a_sigma XA XB) HMty) as [BM [HinfM HsubM]];
            destruct (alg_infer_sigma_decomp Γ BM Mn XA XB HwfΓ HinfM HsubM) as
              [B1 [B2 [W1 [W2 [V2 [HBM [HnB1 [HnT1 [HnB2 [HnT2 Hasnf]]]]]]]]]];
            destruct (alg_infer_sound Γ BM Mn HinfM HwfΓ) as [jM [HMnBM HBMty]];
            subst BM;
            destruct (wf_sigma_typing_inv Γ B1 B2 (a_typ jM) HBMty) as [iB1 [iB2 [HB1ty HB2ty]]];
            set (u1 := Nat.max iB1 iA);
            assert (Hu1iB : iB1 <= u1) by (unfold u1; lia);
            assert (Hu1i : iA <= u1) by (unfold u1; lia);
            assert (HB1XA : {{ Γ ⊢ B1 ≈ XA : Type@u1 }})
              by (eapply common_nbe_eq; [ exact HnB1 | exact HnT1 | exact HB1ty | exact HDomTy | exact Hu1iB | exact Hu1i ]);
            assert (HB1u : {{ Γ ⊢ B1 : Type@u1 }}) by (eapply wf_exp_cumul; [ exact Hu1iB | exact HB1ty ]);
            assert (HXAu : {{ Γ ⊢ XA : Type@u1 }}) by (eapply wf_exp_cumul; [ exact Hu1i | exact HDomTy ]);
            assert (HfstXA : {{ Γ ⊢ fst Mn : XA }}) by (eapply wf_fst; [ exact HDomTy | exact HCodTy | exact HMty ]);
            assert (HfstB1 : {{ Γ ⊢ fst Mn : B1 }})
              by (eapply wf_exp_conv; [ exact HfstXA | apply wf_exp_eq_sym; exact HB1XA | exact HB1u ]);
            set (B1e := (B1 : exp));
            assert (HσB1 : {{ Γ ⊢s Id,,fst Mn : Γ, B1e }})
              by (eapply wf_sub_extend_id_self; [ exact HfstB1 | exact HB1ty ]);
            assert (HB2sigty : {{ Γ ⊢ B2[Id,,fst Mn] : Type@iB2 }})
              by (eapply wf_subst_type; [ exact HσB1 | exact HB2ty ]);
            destruct (TyEx Γ (a_sub B2 (a_extend a_id (a_fst Mn))) iB2 HB2sigty) as [CC HCC];
            exists CC; split;
            [ eapply ati_snd; [ exact HinfM | exact HCC ]
            | set (u2 := Nat.max iB2 iB);
              assert (Hu2iB : iB2 <= u2) by (unfold u2; lia);
              assert (Hu2i : iB <= u2) by (unfold u2; lia);
              assert (HB2u : {{ Γ, B1e ⊢ B2 : Type@u2 }})
                by (eapply wf_exp_cumul; [ exact Hu2iB | exact HB2ty ]);
              assert (HXBu : {{ Γ, XA ⊢ XB : Type@u2 }})
                by (eapply wf_exp_cumul; [ exact Hu2i | exact HCodTy ]);
              assert (Hsub2 : {{ Γ, XA ⊢ B2 ⊆ XB }})
                by (eapply subtyp_second_transport;
                      [ exact HB1XA | exact HB1u | exact HXAu | exact HB2u | exact HXBu | exact HnB2 | exact HnT2 | exact Hasnf ]);
              assert (HσXA : {{ Γ ⊢s Id,,fst Mn : Γ, XA }})
                by (eapply wf_sub_extend_id_self; [ exact HfstXA | exact HDomTy ]);
              assert (Hsub2sig : {{ Γ ⊢ B2[Id,,fst Mn] ⊆ XB[Id,,fst Mn] }})
                by (eapply wf_subtyp_subst; [ exact HσXA | exact Hsub2 ]);
              eapply wf_subtyp_trans; [ | exact Hsub ];
              eapply wf_subtyp_trans; [ | exact Hsub2sig ];
              eapply wf_subtyp_of_eq;
              [ destruct (NTS Γ (a_sub B2 (a_extend a_id (a_fst Mn))) CC iB2 HCC HB2sigty) as [_ HeqC];
                apply wf_exp_eq_sym; exact HeqC
              | exact HB2sigty ] ]
        end
      end
    end.
  - (* BReq *)
    destruct (user_typing_shape Γ A (a_eq An M1 M2) (user_exp_eq An M1 M2 HuAn HuM1 HuM2) HM) as [T0 [Hs Hsub]].
    inversion Hs; subst; clear Hs.
    assert (HAnTy : {{ Γ ⊢ An : Type@i }}) by assumption.
    assert (HM1ty : {{ Γ ⊢ M1 : An }}) by assumption.
    assert (HM2ty : {{ Γ ⊢ M2 : An }}) by assumption.
    destruct (IHA Γ (a_typ i) HAnTy) as [BA [HinfA HsubA]].
    destruct (InferUniv Γ An BA i HinfA HAnTy) as [k HBA]. subst BA.
    assert (Hkle : k <= i) by (eapply alg_subtyping_typ_typ_le; eapply SubComplete; exact HsubA).
    destruct (IHM1 Γ An HM1ty) as [B1 [Hinf1 Hsub1]].
    destruct (IHM2 Γ An HM2ty) as [B2 [Hinf2 Hsub2]].
    exists (nf_typ k). split.
    + eapply ati_eq;
        [ exact HinfA
        | eapply atc_of_ati; [ exact Hinf1 | exact Hsub1 ]
        | eapply atc_of_ati; [ exact Hinf2 | exact Hsub2 ] ].
    + assert (HwfΓ : {{ ⊢ Γ }}) by (eapply wf_exp_ctx; exact HM).
      eapply wf_subtyp_trans; [ | exact Hsub ].
      eapply wf_subtyp_univ_le; [ exact HwfΓ | exact Hkle ].
  - (* BRrefl *)
    destruct (user_typing_shape Γ A (a_refl An Mn) (user_exp_refl An Mn HuAn HuMn) HM) as [T0 [Hs Hsub]].
    inversion Hs; subst; clear Hs.
    assert (HAnTy : {{ Γ ⊢ An : Type@i }}) by assumption.
    assert (HMty : {{ Γ ⊢ Mn : An }}) by assumption.
    destruct (IHA Γ (a_typ i) HAnTy) as [BA [HinfA HsubA]].
    destruct (InferUniv Γ An BA i HinfA HAnTy) as [k HBA]. subst BA.
    destruct (IHM Γ An HMty) as [BM [HinfM HsubM]].
    assert (HchkM : alg_type_check Γ An Mn) by (eapply atc_of_ati; [ exact HinfM | exact HsubM ]).
    destruct (TyEx Γ An i HAnTy) as [C HC].
    destruct (NTS Γ An C i HC HAnTy) as [_ HeqAC].
    destruct (TmEx Γ Mn An HMty) as [N HN].
    destruct (NTmS Γ Mn An N HN HMty) as [_ HeqMN].
    exists (nf_eq C N N). split.
    + eapply ati_refl; [ exact HinfA | exact HchkM | exact HC | exact HN ].
    + eapply wf_subtyp_trans; [ | exact Hsub ].
      assert (HEqTy : {{ Γ ⊢ Eq An Mn Mn : Type@i }})
        by (eapply wf_eq; [ exact HAnTy | exact HMty | exact HMty ]).
      assert (HeqEq : {{ Γ ⊢ Eq An Mn Mn ≈ Eq C N N : Type@i }})
        by (eapply wf_exp_eq_eq_cong; [ exact HeqAC | exact HeqMN | exact HeqMN ]).
      eapply wf_subtyp_of_eq; [ apply wf_exp_eq_sym; exact HeqEq | exact HEqTy ].
  - (* BReqrec *)
    destruct (user_typing_shape Γ A (a_eqrec An Bn BRn M1 M2 Nn)
      (user_exp_eqrec An Bn BRn M1 M2 Nn HuAn HuBn HuBRn HuM1 HuM2 HuNn) HM) as [T0 [Hs Hsub]].
    destruct (user_shape_type _ _ _ Hs) as [k0 HT0ty].
    inversion Hs; subst; clear Hs.
    set (CtxB := (a_eq (a_sub An (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0)
                   :: a_sub An a_weaken :: An :: Γ)%list).
    assert (HAnTy : {{ Γ ⊢ An : Type@i }}) by assumption.
    assert (HM1ty : {{ Γ ⊢ M1 : An }}) by assumption.
    assert (HM2ty : {{ Γ ⊢ M2 : An }}) by assumption.
    assert (HBnTy : {{ CtxB ⊢ Bn : Type@j }}) by (unfold CtxB; assumption).
    assert (HBRty : {{ Γ, An ⊢ BRn : Bn[Id,,#0,,refl An[Wk] #0] }}) by assumption.
    assert (HNty : {{ Γ ⊢ Nn : Eq An M1 M2 }}) by assumption.
    destruct (IHA Γ (a_typ i) HAnTy) as [BA [HinfA HsubA]].
    destruct (InferUniv Γ An BA i HinfA HAnTy) as [k HBA]. subst BA.
    destruct (IHM1 Γ An HM1ty) as [B1 [Hinf1 Hsub1]].
    destruct (IHM2 Γ An HM2ty) as [B2 [Hinf2 Hsub2]].
    destruct (IHB CtxB (a_typ j) HBnTy) as [BB [HinfB HsubB]].
    destruct (InferUniv CtxB Bn BB j HinfB HBnTy) as [l HBB]. subst BB.
    destruct (IHBR (An :: Γ)%list
      (a_sub Bn (a_extend (a_extend a_id (a_var 0)) (a_refl (a_sub An a_weaken) (a_var 0)))) HBRty)
      as [BBR [HinfBR HsubBR]].
    destruct (IHN Γ (a_eq An M1 M2) HNty) as [BN [HinfN HsubN]].
    destruct (TyEx _ _ k0 HT0ty) as [C HC].
    exists C. split.
    + eapply ati_eqrec.
      * exact HinfA.
      * eapply atc_of_ati; [ exact Hinf1 | exact Hsub1 ].
      * eapply atc_of_ati; [ exact Hinf2 | exact Hsub2 ].
      * unfold CtxB. exact HinfB.
      * eapply atc_of_ati; [ exact HinfBR | exact HsubBR ].
      * eapply atc_of_ati; [ exact HinfN | exact HsubN ].
      * exact HC.
    + eapply wf_subtyp_trans; [ | exact Hsub ].
      eapply subtyp_nbe_ty; [ exact HC | exact HT0ty ].
  - (* BRvar *)
    destruct (user_typing_shape Γ A (a_var x) (user_exp_vlookup x) HM) as [T0 [Hs Hsub]].
    inversion Hs; subst; clear Hs.
    assert (HwfΓ : {{ ⊢ Γ }}) by assumption.
    assert (Hlk : {{ # x : T0 ∈ Γ }}) by assumption.
    destruct (ctx_lookup_type Γ x T0 Hlk HwfΓ) as [i HT0ty].
    destruct (TyEx _ _ i HT0ty) as [B HB].
    exists B. split.
    + eapply ati_vlookup; [ exact Hlk | exact HB ].
    + eapply wf_subtyp_trans; [ | exact Hsub ].
      eapply subtyp_nbe_ty; [ exact HB | exact HT0ty ].
Qed.

End InferCompleteSection.

(* ============================================================ *)
(* Universe canonicity and its relation to InferUniv            *)
(* ============================================================ *)

(* Precise missing canonicity principle: if a term M has type T and
   is itself typed at a universe, then the normal form of T is a
   universe.  This is the standard canonicity/uniqueness of typing at
   universes and is not derivable from nbe soundness, existence of
   normal forms, or subtyping completeness. *)
Definition NbeUniverseCanon : Prop :=
  forall Γ (T : typ) (W : nf) (M : typ) i,
    nbe_ty Γ T W -> {{ Γ ⊢ M : T }} -> {{ Γ ⊢ M : Type@i }} ->
    exists j, W = nf_typ j.

Section InferUnivFromCanon.
Hypothesis NTS : forall Γ A W i,
  nbe_ty Γ A W -> {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ W : Type@i }} /\ {{ Γ ⊢ A ≈ W : Type@i }}.
Hypothesis NTmS : forall Γ M A W,
  nbe Γ M A W -> {{ Γ ⊢ M : A }} ->
  {{ Γ ⊢ W : A }} /\ {{ Γ ⊢ M ≈ W : A }}.
Hypothesis TyEx : forall Γ A i, {{ Γ ⊢ A : Type@i }} -> exists W, nbe_ty Γ A W.
Hypothesis Canon : NbeUniverseCanon.

Lemma InferUniv_of_canon : forall Γ M B i,
  alg_type_infer Γ B M -> {{ Γ ⊢ M : Type@i }} -> exists j, B = nf_typ j.
Proof.
  intros Γ M B i Hinf HM.
  assert (Hwf : {{ ⊢ Γ }}) by (eapply wf_exp_ctx; exact HM).
  destruct (proj2 (infer_check_sound NTS NTmS) Γ B M Hinf Hwf) as [j [HMB HBTy]].
  destruct (TyEx Γ B j HBTy) as [W HW].
  destruct (Canon Γ B W M i HW HMB HM) as [k Hk]. subst W.
  assert (Hh : nf_head B = nf_head (nf_typ k)).
  { eapply nbe_ty_nf_head; [ exact Hwf | exact HBTy | exact HW ]. }
  simpl in Hh.
  exact (nf_head_zero B Hh).
Qed.

End InferUnivFromCanon.

(* The same completeness result, with InferUniv replaced by the
   explicit canonicity principle above. *)
Section InferCompleteFromCanon.
Hypothesis NTS : forall Γ A W i,
  nbe_ty Γ A W -> {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ W : Type@i }} /\ {{ Γ ⊢ A ≈ W : Type@i }}.
Hypothesis NTmS : forall Γ M A W,
  nbe Γ M A W -> {{ Γ ⊢ M : A }} ->
  {{ Γ ⊢ W : A }} /\ {{ Γ ⊢ M ≈ W : A }}.
Hypothesis TyEx : forall Γ A i, {{ Γ ⊢ A : Type@i }} -> exists W, nbe_ty Γ A W.
Hypothesis TmEx : forall Γ M A, {{ Γ ⊢ M : A }} -> exists W, nbe Γ M A W.
Hypothesis SubComplete : forall Γ A B, {{ Γ ⊢ A ⊆ B }} -> alg_subtyping Γ A B.
Hypothesis Canon : NbeUniverseCanon.

Lemma InferCompleteUserStmt_of_canon : InferCompleteUserStmt.
Proof.
  exact (InferCompleteUserStmt_conditional NTS NTmS TyEx TmEx SubComplete
           (InferUniv_of_canon NTS NTmS TyEx Canon)).
Qed.

End InferCompleteFromCanon.

Print Assumptions InferCompleteUserStmt_conditional.
Print Assumptions InferCompleteUserStmt_of_canon.

Section FinalAssembly.
Hypothesis NTS : forall Γ A W i,
  nbe_ty Γ A W -> {{ Γ ⊢ A : Type@i }} ->
  {{ Γ ⊢ W : Type@i }} /\ {{ Γ ⊢ A ≈ W : Type@i }}.
Hypothesis NTmS : forall Γ M A W,
  nbe Γ M A W -> {{ Γ ⊢ M : A }} ->
  {{ Γ ⊢ W : A }} /\ {{ Γ ⊢ M ≈ W : A }}.
Hypothesis TyEx : forall Γ A i,
  {{ Γ ⊢ A : Type@i }} -> exists W, nbe_ty Γ A W.
Hypothesis TmEx : forall Γ M A,
  {{ Γ ⊢ M : A }} -> exists W, nbe Γ M A W.
Hypothesis NbeEq : forall Γ M N i W,
  {{ Γ ⊢ M ≈ N : Type@i }} -> nbe_ty Γ N W -> nbe_ty Γ M W.
Hypothesis CtxNbe : forall Γ A A' i C W,
  {{ Γ ⊢ A ≈ A' : Type@i }} ->
  nbe_ty (A :: Γ) C W -> nbe_ty (A' :: Γ) C W.

Theorem sound_of_sem : forall {Γ i A M},
  {{ Γ ⊢a M ⟸ A }} -> {{ ⊢ Γ }} -> {{ Γ ⊢ A : Type@i }} -> {{ Γ ⊢ M : A }}.
Proof.
  intros Γ0 i0 A0 M0 H Hwf HA.
  exact (proj1 (infer_check_sound NTS NTmS) Γ0 A0 M0 H i0 Hwf HA).
Qed.

Theorem complete_of_sem :
  NbeUniverseCanon ->
  forall {Γ A M}, user_exp M -> {{ Γ ⊢ M : A }} -> {{ Γ ⊢a M ⟸ A }}.
Proof.
  intros Hcanon Γ0 A0 M0 Hu HM.
  eapply check_complete_from_infer.
  - eapply InferCompleteUserStmt_of_canon.
    + exact NTS.
    + exact NTmS.
    + exact TyEx.
    + exact TmEx.
    + eapply SubComplete; [exact TyEx|exact NbeEq|exact CtxNbe].
    + exact Hcanon.
  - eapply SubComplete; [exact TyEx|exact NbeEq|exact CtxNbe].
  - exact Hu.
  - exact HM.
Qed.
End FinalAssembly.


(* ============================================================ *)
(* Targets                                                      *)
(* ============================================================ *)

Theorem alg_type_check_sound : forall {Γ i A M},
    {{ Γ ⊢a M ⟸ A }} ->
    {{ ⊢ Γ }} ->
    {{ Γ ⊢ A : Type@i }} ->
    {{ Γ ⊢ M : A }}.
Admitted.

Theorem alg_type_check_complete : forall {Γ A M},
    user_exp M ->
    {{ Γ ⊢ M : A }} ->
    {{ Γ ⊢a M ⟸ A }}.
Admitted.
